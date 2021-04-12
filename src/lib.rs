use std::{
	fmt::Debug,
	hint::unreachable_unchecked,
	mem::{replace, MaybeUninit},
	ptr::{copy, copy_nonoverlapping, null_mut},
};

const B: u8 = 4;

#[derive(Debug)]
// FIXME remove the requirement that K: Debug, V: Debug
pub struct BTree<K, V>
where
	K: Ord,
	K: Debug,
	V: Debug,
{
	root: Node<K, V>,
}

// FIXME remove the requirement that K: Debug, V: Debug
impl<K, V> BTree<K, V>
where
	K: Ord,
	K: Debug,
	V: Debug,
	K: Copy,
{
	pub fn new() -> Self { Self { root: Node::new() } }

	pub fn insert(&mut self, key: K, value: V) -> Option<V> {
		match self.root.insert(key, value) {
			NodeInsertResult::Split {
				new_node,
				bubble: (key, value),
			} => {
				let old_root = replace(&mut self.root, Node::new());
				self.root.keys[0] = MaybeUninit::new(key);
				self.root.values[0] = MaybeUninit::new(value);
				self.root.children[0] = MaybeUninit::new(Box::into_raw(Box::new(old_root)));
				self.root.children[1] = MaybeUninit::new(Box::into_raw(new_node));
				self.root.len = 1;
				None
			}
			NodeInsertResult::Existed(v) => Some(v),
			NodeInsertResult::Ok => None,
		}
	}

	pub fn remove(&mut self, key: K) -> Option<V> {
		match self.root.remove(key) {
			NodeRemoveResult::NotThere => None,
			NodeRemoveResult::Removed(value) => Some(value),
			NodeRemoveResult::Merged(value) => {
				if self.root.len() == 0 {
					// Switch root

					let new_root_ptr = unsafe { self.root.children.get_unchecked(0).assume_init() };
					let new_root_box = unsafe { Box::from_raw(new_root_ptr) };
					self.root = *new_root_box;
				}
				Some(value)
			}
		}
	}
}

// FIXME remove the requirement that K: Debug, V: Debug
pub struct Node<K, V>
where
	K: Ord,
	K: Debug,
	V: Debug,
{
	len: u8,
	keys: [MaybeUninit<K>; (B - 1) as usize],
	values: [MaybeUninit<V>; (B - 1) as usize],
	children: [MaybeUninit<*mut Node<K, V>>; B as usize],
}

impl<K, V> std::fmt::Debug for Node<K, V>
where
	K: Ord,
	K: std::fmt::Debug,
	V: std::fmt::Debug,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let children = self
			.children
			.iter()
			.take(if self.len == 0 {
				0
			}
			else {
				self.len as usize + 1
			})
			.enumerate()
			.take_while(|(_, p)| !unsafe { p.assume_init().is_null() })
			.map(|(n, p)| (n, unsafe { (*p).assume_init().as_ref().unwrap() }))
			.map(|(_, p)| p)
			.collect::<Vec<_>>();
		f.debug_struct("Node")
			.field("len", &self.len)
			.field("keys", &unsafe {
				&*(&self.keys[..self.len as usize] as *const _ as *const [K])
			})
			.field("values", &unsafe {
				&*(&self.values[..self.len as usize] as *const _ as *const [V])
			})
			.field("children", &children)
			.finish()
	}
}

#[must_use]
#[derive(Debug)]
// FIXME remove the requirement that K: Debug, V: Debug
pub enum NodeInsertResult<K, V>
where
	K: Ord,
	K: Debug,
	V: Debug,
{
	Split {
		new_node: Box<Node<K, V>>,
		bubble: (K, V),
	},
	Existed(V),
	Ok,
}

#[must_use]
#[derive(Debug)]
// FIXME remove the requirement that K: Debug, V: Debug
pub enum NodeRemoveResult<V>
where
	V: Debug,
{
	NotThere,
	Removed(V),
	Merged(V),
}

// FIXME remove the requirement that K: Debug, V: Debug
impl<K, V> Node<K, V>
where
	K: Ord,
	K: Debug,
	V: Debug,
{
	#[inline(never)]
	pub fn new() -> Self {
		Self {
			len: 0,
			keys: unsafe { MaybeUninit::uninit().assume_init() },
			values: unsafe { MaybeUninit::uninit().assume_init() },
			children: [MaybeUninit::new(null_mut()); B as usize],
		}
	}

	pub fn insert(&mut self, key: K, value: V) -> NodeInsertResult<K, V> {
		let keys_valid = unsafe {
			&mut *(self.keys.get_unchecked_mut(..self.len as usize) as *mut _ as *mut [K])
		};

		let greater_index = match keys_valid.binary_search(&key) {
			Ok(index) => {
				// Key exists already - swap value and return

				let value_in_array = unsafe { self.values.get_unchecked_mut(index) };
				let old_value_maybeuninit = replace(value_in_array, MaybeUninit::new(value));
				let old_value = unsafe { old_value_maybeuninit.assume_init() };

				return NodeInsertResult::Existed(old_value);
			}
			Err(index) => index,
		};

		let child_link = unsafe { self.children.get_unchecked_mut(greater_index).assume_init() };

		match unsafe { child_link.as_mut() } {
			None => {
				// We are a leaf node - insert and bubble back up

				if self.len < (B - 1) {
					// Add to node

					unsafe { self.insert_at_index_unchecked_leaf(key, value, greater_index) };

					NodeInsertResult::Ok
				}
				else {
					let (new_node, bubble) =
						unsafe { self.split_leaf_node_unchecked(key, value, greater_index) };
					NodeInsertResult::Split { new_node, bubble }
				}
			}
			Some(child) => {
				// We have a child - recurse

				match child.insert(key, value) {
					NodeInsertResult::Split { new_node, bubble } => {
						// Insert the bubbled-up node into this node

						if self.len < (B - 1) {
							// Add to node

							unsafe {
								self.insert_at_index_unchecked_internal(
									new_node,
									bubble,
									greater_index,
								)
							};
							NodeInsertResult::Ok
						}
						else {
							let (new_node, bubble) = unsafe {
								self.split_internal_node_unchecked(new_node, bubble, greater_index)
							};
							NodeInsertResult::Split { new_node, bubble }
						}
					}
					NodeInsertResult::Existed(v) => NodeInsertResult::Existed(v),
					NodeInsertResult::Ok => NodeInsertResult::Ok,
				}
			}
		}
	}

	pub fn remove(&mut self, key: K) -> NodeRemoveResult<V> {
		let keys_valid = unsafe {
			&mut *(self.keys.get_unchecked_mut(..self.len as usize) as *mut _ as *mut [K])
		};

		match keys_valid.binary_search(&key) {
			Ok(index) => {
				let left_child_link =
					unsafe { self.children.get_unchecked_mut(index).assume_init() };
				match unsafe { left_child_link.as_mut() } {
					None => {
						// We are a leaf node - simply remove the item
						let (_, value) = unsafe { self.remove_at_index_unchecked_leaf(index) };
						NodeRemoveResult::Removed(value)
					}
					Some(child) => {
						// We are not a leaf node

						// Get pointers to the key and value to pass into the recursion
						let indexed_key_ptr =
							unsafe { self.keys.get_unchecked_mut(index).as_mut_ptr() };
						let indexed_value_ptr =
							unsafe { self.values.get_unchecked_mut(index).as_mut_ptr() };

						// Read out the value for returning
						let value = unsafe { indexed_value_ptr.read() };

						// Replace value with new value from leaf node
						unsafe { child.swap_with_left_leaf(indexed_key_ptr, indexed_value_ptr) };

						// Unroll recursion - rebalancing along the way
						match unsafe { self.rebalance(index) } {
							false => NodeRemoveResult::Removed(value),
							true => NodeRemoveResult::Merged(value),
						}
					}
				}
			}
			Err(index) => {
				// Have not yet found the key
				let child_link = unsafe { self.children.get_unchecked_mut(index).assume_init() };
				match unsafe { child_link.as_mut() } {
					None => NodeRemoveResult::NotThere,
					Some(child) => match child.remove(key) {
						NodeRemoveResult::NotThere => NodeRemoveResult::NotThere,
						NodeRemoveResult::Removed(value) => {
							match unsafe { self.rebalance(index) } {
								false => NodeRemoveResult::Removed(value),
								true => NodeRemoveResult::Merged(value),
							}
						}

						NodeRemoveResult::Merged(value) => match unsafe { self.rebalance(index) } {
							false => NodeRemoveResult::Removed(value),
							true => NodeRemoveResult::Merged(value),
						},
					},
				}
			}
		}
	}

	fn len(&self) -> u8 { self.len }

	// Insert an element into the leaf node at an index
	// Makes the assumption that the node has enough capacity for the new element
	unsafe fn insert_at_index_unchecked_leaf(&mut self, key: K, value: V, index: usize) {
		debug_assert!(index <= self.len as usize);

		let copy_len = self.len as usize - index;

		// Copy keys forward
		let keys_ptr = self.keys.as_mut_ptr();
		let copy_src = keys_ptr.add(index);
		let copy_dst = keys_ptr.add(index + 1);
		copy(copy_src, copy_dst, copy_len);

		// Copy values forward
		let values_ptr = self.values.as_mut_ptr();
		let copy_src = values_ptr.add(index);
		let copy_dst = values_ptr.add(index + 1);
		copy(copy_src, copy_dst, copy_len);

		// Insert new key / value
		*self.keys.get_unchecked_mut(index) = MaybeUninit::new(key);
		*self.values.get_unchecked_mut(index) = MaybeUninit::new(value);

		self.len += 1;
	}

	unsafe fn split_leaf_node_unchecked(
		&mut self,
		key: K,
		value: V,
		index: usize,
	) -> (Box<Node<K, V>>, (K, V)) {
		debug_assert!(self.len > 0);

		// Split node

		// Create pivot while also accounting for the to-be-inserted element
		// Left bias because the bubble will be picked from the left node
		let (insert_left, pivot) = if index as u8 <= self.len / 2 {
			// New element goes to the left of the pivot
			(true, self.len / 2)
		}
		else {
			// New element goes to the right of the pivot
			(false, self.len / 2 + 1)
		};

		let new_len = self.len - pivot;

		// Create our right node
		let mut new_node = Self {
			len: new_len,
			keys: MaybeUninit::uninit().assume_init(),
			values: MaybeUninit::uninit().assume_init(),
			children: [MaybeUninit::new(null_mut()); B as usize],
		};

		// Copy half of keys
		let copy_src = self.keys.as_ptr().add(pivot as usize);
		let copy_dst = new_node.keys.as_mut_ptr();
		copy_nonoverlapping(copy_src, copy_dst, new_len as usize);

		// Copy half of values
		let copy_src = self.values.as_ptr().add(pivot as usize);
		let copy_dst = new_node.values.as_mut_ptr();
		copy_nonoverlapping(copy_src, copy_dst, new_len as usize);

		// Update length
		self.len = pivot;

		// Insert new element - now we're sure that whichever node has room
		if insert_left {
			self.insert_at_index_unchecked_leaf(key, value, index);
		}
		else {
			new_node.insert_at_index_unchecked_leaf(key, value, index - pivot as usize);
		}

		// Decrement left node length since we are about to remove the bubble
		let new_left_len = self.len - 1;

		let bubble_key = self
			.keys
			.get_unchecked(new_left_len as usize)
			.as_ptr()
			.read();
		let bubble_value = self
			.values
			.get_unchecked(new_left_len as usize)
			.as_ptr()
			.read();

		self.len = new_left_len;

		(Box::new(new_node), (bubble_key, bubble_value))
	}

	// Insert a bubbled-up element into the internal node at an index
	// Makes the assumption that the node has enough capacity for the new element
	unsafe fn insert_at_index_unchecked_internal(
		&mut self,
		new_node: Box<Node<K, V>>,
		(key, value): (K, V),
		index: usize,
	) {
		debug_assert!(index <= self.len as usize);

		let copy_len = self.len as usize - index;

		// Copy keys forward
		let keys_ptr = self.keys.as_mut_ptr();
		let copy_src = keys_ptr.add(index);
		let copy_dst = keys_ptr.add(index + 1);
		copy(copy_src, copy_dst, copy_len);

		// Copy keys forward
		let values_ptr = self.keys.as_mut_ptr();
		let copy_src = values_ptr.add(index);
		let copy_dst = values_ptr.add(index + 1);
		copy(copy_src, copy_dst, copy_len);

		// Copy children forward
		let children_ptr = self.keys.as_mut_ptr();
		let copy_src = children_ptr.add(index + 1);
		let copy_dst = children_ptr.add(index + 2);
		copy(copy_src, copy_dst, copy_len);

		// Insert new key / value / child
		*self.keys.get_unchecked_mut(index) = MaybeUninit::new(key);
		*self.values.get_unchecked_mut(index) = MaybeUninit::new(value);
		*self.children.get_unchecked_mut(index + 1) = MaybeUninit::new(Box::into_raw(new_node));

		self.len += 1;
	}

	unsafe fn split_internal_node_unchecked(
		&mut self,
		new_right_node: Box<Node<K, V>>,
		bubble: (K, V),
		index: usize,
	) -> (Box<Node<K, V>>, (K, V)) {
		// Split node

		// Create pivot while also accounting for the to-be-inserted element
		// Left bias because the bubble will be picked from the left node
		let (insert_left, pivot) = if index as u8 <= self.len / 2 {
			// New element goes to the left of the pivot
			(true, self.len / 2)
		}
		else {
			// New element goes to the right of the pivot
			(false, self.len / 2 + 1)
		};

		let new_len = self.len - pivot;

		// Create our right node
		let mut new_node = Self {
			len: new_len,
			keys: MaybeUninit::uninit().assume_init(),
			values: MaybeUninit::uninit().assume_init(),
			children: MaybeUninit::uninit().assume_init(),
		};

		// Copy half of keys
		let src = self.keys.as_ptr().add(pivot as usize);
		let dest = new_node.keys.as_mut_ptr();
		copy_nonoverlapping(src, dest, new_len as usize);

		// Copy half of values
		let src = self.values.as_ptr().add(pivot as usize);
		let dest = new_node.values.as_mut_ptr();
		copy_nonoverlapping(src, dest, new_len as usize);

		// Insert new element - now we're sure that whichever node has room
		// Insert bubbled-up key and value only - we will handle the new right node later
		if insert_left {
			let copy_len = self.len - pivot;
			let src = self.children.get_unchecked(pivot as usize + 1).as_ptr();
			let dest = new_node.children.get_unchecked_mut(1).as_mut_ptr();

			// Copy child values to the right node - leave a space at the start for later transfer from the left node
			copy_nonoverlapping(src, dest, copy_len as usize);

			// Update length
			self.len = pivot;

			self.insert_at_index_unchecked_internal(new_right_node, bubble, index);

			// Move child from end of left node to start of right node
			*new_node.children.get_unchecked_mut(0).as_mut_ptr() =
				*self.children.get_unchecked(pivot as usize).as_ptr();
		}
		else {
			let copy_len = self.len - pivot + 1;
			let src = self.children.get_unchecked(pivot as usize).as_ptr();
			let dest = new_node.children.get_unchecked_mut(0).as_mut_ptr();

			// Copy child values to the right node
			copy_nonoverlapping(src, dest, copy_len as usize);

			// Update length
			self.len = pivot;

			new_node.insert_at_index_unchecked_internal(
				new_right_node,
				bubble,
				index - pivot as usize,
			);
		}

		// Decrement left node length since we are about to remove the bubble
		let new_left_len = self.len - 1;

		let bubble_key = self
			.keys
			.get_unchecked(new_left_len as usize)
			.as_ptr()
			.read();
		let bubble_value = self
			.values
			.get_unchecked(new_left_len as usize)
			.as_ptr()
			.read();

		self.len = new_left_len;

		(Box::new(new_node), (bubble_key, bubble_value))
	}

	unsafe fn swap_with_left_leaf(&mut self, key_hole: *mut K, value_hole: *mut V) {
		let len = self.len() as usize;
		let rightmost_child = self.children.get_unchecked_mut(len).assume_init();
		match rightmost_child.as_mut() {
			None => {
				// We are a leaf node
				// Replace the key and value of the ancestor node
				let (key, value, _) = self.remove_last();
				*key_hole = key;
				*value_hole = value;
			}
			Some(child) => {
				// We are an internal node - recurse
				child.swap_with_left_leaf(key_hole, value_hole);
				self.rebalance(len);
			}
		}
	}

	unsafe fn remove_at_index_unchecked_leaf(&mut self, index: usize) -> (K, V) {
		debug_assert!(index <= self.len as usize);

		let removed_key = self.keys.get_unchecked(index).as_ptr().read();
		let removed_value = self.values.get_unchecked(index).as_ptr().read();

		let copy_len = self.len as usize - index - 1;

		// Copy keys backwards
		let keys_ptr = self.keys.as_mut_ptr();
		let copy_src = keys_ptr.add(index + 1);
		let copy_dst = keys_ptr.add(index);
		copy(copy_src, copy_dst, copy_len);

		// Copy values backwards
		let values_ptr = self.values.as_mut_ptr();
		let copy_src = values_ptr.add(index + 1);
		let copy_dst = values_ptr.add(index);
		copy(copy_src, copy_dst, copy_len);

		self.len -= 1;

		(removed_key, removed_value)
	}

	unsafe fn remove_at_index_unchecked_internal(
		&mut self,
		index: usize,
	) -> (K, V, Box<Node<K, V>>) {
		debug_assert!(index <= self.len as usize);

		let removed_key = self.keys.get_unchecked(index).as_ptr().read();
		let removed_value = self.values.get_unchecked(index).as_ptr().read();
		let removed_child = self.children.get_unchecked(index + 1).assume_init();

		let copy_len = self.len as usize - index - 1;

		// Copy keys backwards
		let keys_ptr = self.keys.as_mut_ptr();
		let copy_src = keys_ptr.add(index + 1);
		let copy_dst = keys_ptr.add(index);
		copy(copy_src, copy_dst, copy_len);

		// Copy values backwards
		let values_ptr = self.values.as_mut_ptr();
		let copy_src = values_ptr.add(index + 1);
		let copy_dst = values_ptr.add(index);
		copy(copy_src, copy_dst, copy_len);

		// Copy keys backwards
		let children_ptr = self.keys.as_mut_ptr();
		let copy_src = children_ptr.add(index + 2);
		let copy_dst = children_ptr.add(index + 1);
		copy(copy_src, copy_dst, copy_len);

		self.len -= 1;

		(removed_key, removed_value, Box::from_raw(removed_child))
	}

	unsafe fn remove_last(&mut self) -> (K, V, Box<Node<K, V>>) {
		let len = self.len() as usize;

		let removed_key = self.keys.get_unchecked(len - 1).as_ptr().read();
		let removed_value = self.values.get_unchecked(len - 1).as_ptr().read();
		let removed_child = self.children.get_unchecked(len).assume_init();

		self.len -= 1;

		(removed_key, removed_value, Box::from_raw(removed_child))
	}

	unsafe fn remove_first(&mut self) -> (K, V, Box<Node<K, V>>) {
		let removed_key = self.keys.get_unchecked(0).as_ptr().read();
		let removed_value = self.values.get_unchecked(0).as_ptr().read();
		let removed_child = self.children.get_unchecked(0).assume_init();

		let copy_len = self.len as usize - 1;

		// Copy keys backwards
		let keys_ptr = self.keys.as_mut_ptr();
		let copy_src = keys_ptr.add(1);
		let copy_dst = keys_ptr.add(0);
		copy(copy_src, copy_dst, copy_len);

		// Copy values backwards
		let values_ptr = self.values.as_mut_ptr();
		let copy_src = values_ptr.add(1);
		let copy_dst = values_ptr.add(0);
		copy(copy_src, copy_dst, copy_len);

		// Copy children backwards
		let children_ptr = self.children.as_mut_ptr();
		let copy_src = children_ptr.add(1);
		let copy_dst = children_ptr.add(0);
		copy(copy_src, copy_dst, copy_len + 1);

		self.len -= 1;

		(removed_key, removed_value, Box::from_raw(removed_child))
	}

	unsafe fn insert_first(&mut self, key: K, value: V, child: Box<Node<K, V>>) {
		let copy_len = self.len as usize;

		// Copy keys forward
		let keys_ptr = self.keys.as_mut_ptr();
		let copy_src = keys_ptr.add(0);
		let copy_dst = keys_ptr.add(1);
		copy(copy_src, copy_dst, copy_len);

		// Copy values forward
		let values_ptr = self.values.as_mut_ptr();
		let copy_src = values_ptr.add(0);
		let copy_dst = values_ptr.add(1);
		copy(copy_src, copy_dst, copy_len);

		// Copy children forward
		let children_ptr = self.children.as_mut_ptr();
		let copy_src = children_ptr.add(0);
		let copy_dst = children_ptr.add(1);
		copy(copy_src, copy_dst, copy_len + 1);

		// Insert new key / value / child
		*self.keys.get_unchecked_mut(0).as_mut_ptr() = key;
		*self.values.get_unchecked_mut(0).as_mut_ptr() = value;
		*self.children.get_unchecked_mut(0).as_mut_ptr() = Box::into_raw(child);

		self.len += 1;
	}

	unsafe fn rebalance(&mut self, child_index: usize) -> bool {
		let child_link = self
			.children
			.get_unchecked_mut(child_index as usize)
			.assume_init();
		let child = match child_link.as_mut() {
			None => unreachable_unchecked(),
			Some(child) => child,
		};

		let child_len = child.len();
		if child_len >= B / 2 - 1 {
			// No rebalancing needed - early exit
			return false;
		}

		let (selected_sibling_index, pivot_index, left_sibling) = match child_index {
			0 => (child_index + 1, child_index, false),
			_ => (child_index - 1, child_index - 1, true),
		};

		let sibling_link = self
			.children
			.get_unchecked_mut(selected_sibling_index as usize)
			.assume_init();
		let sibling = match sibling_link.as_mut() {
			None => unreachable_unchecked(),
			Some(sibling) => sibling,
		};

		let sibling_len = sibling.len();
		if sibling_len >= B / 2 {
			// Do rotation

			// Copy key / value out of parent
			let parent_key = self.keys.get_unchecked(pivot_index).as_ptr().read();
			let parent_value = self.values.get_unchecked(pivot_index).as_ptr().read();

			let (sibling_key, sibling_value) = match left_sibling {
				true => {
					let (key, value, node) = sibling.remove_last();
					child.insert_first(parent_key, parent_value, node);
					(key, value)
				}
				false => {
					let (key, value, node) = sibling.remove_first();
					child.insert_at_index_unchecked_internal(
						node,
						(parent_key, parent_value),
						child_len as usize,
					);
					(key, value)
				}
			};

			*self.keys.get_unchecked_mut(pivot_index) = MaybeUninit::new(sibling_key);
			*self.values.get_unchecked_mut(pivot_index) = MaybeUninit::new(sibling_value);

			false
		}
		else {
			// Do merge
			let (mut left_node, key, value, mut right_node) = match left_sibling {
				true => {
					let (key, value, child) = self.remove_at_index_unchecked_internal(pivot_index);
					(sibling, key, value, child)
				}
				false => {
					let (key, value, sibling) =
						self.remove_at_index_unchecked_internal(pivot_index);
					(child, key, value, sibling)
				}
			};

			let left_len = left_node.len() as usize;
			let right_len = right_node.len() as usize;

			// Copy orphaned key and value into the left node
			*left_node.keys.get_unchecked_mut(left_len).as_mut_ptr() = key;
			*left_node.values.get_unchecked_mut(left_len).as_mut_ptr() = value;

			// Copy keys from right node
			let copy_src = right_node.keys.get_unchecked(0).as_ptr();
			let copy_dst = left_node.keys.get_unchecked_mut(left_len + 1).as_mut_ptr();
			copy_nonoverlapping(copy_src, copy_dst, right_len);

			// Copy values from right node
			let copy_src = right_node.values.get_unchecked(0).as_ptr();
			let copy_dst = left_node
				.values
				.get_unchecked_mut(left_len + 1)
				.as_mut_ptr();
			copy_nonoverlapping(copy_src, copy_dst, right_len);

			// Copy children from right node
			let copy_src = right_node.children.get_unchecked(0).as_ptr();
			let copy_dst = left_node
				.children
				.get_unchecked_mut(left_len + 1)
				.as_mut_ptr();
			copy_nonoverlapping(copy_src, copy_dst, right_len + 1);

			// Set lengths
			left_node.len = (left_len + 1 + right_len) as u8;
			right_node.len = 0;
			true
		}
	}
}

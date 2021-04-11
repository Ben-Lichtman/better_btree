use std::{
	hint::unreachable_unchecked,
	mem::{replace, MaybeUninit},
	ptr::{copy, copy_nonoverlapping, null_mut, read},
};

use std::fmt::Debug;

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
						let value = unsafe { self.remove_at_index_unchecked_leaf(index) };
						NodeRemoveResult::Removed(value)
					}
					Some(child) => {
						// We are not a leaf node
						todo!("The rest of the fucking recursion")
					}
				}
			}
			Err(index) => {
				// Have not yet found the key
				let child_link = unsafe { self.children.get_unchecked_mut(index).assume_init() };
				match unsafe { child_link.as_mut() } {
					None => return NodeRemoveResult::NotThere,
					Some(child) => match child.remove(key) {
						NodeRemoveResult::NotThere => NodeRemoveResult::NotThere,
						NodeRemoveResult::Removed(value) => {
							unsafe { self.rebalance(index) };
							NodeRemoveResult::Removed(value)
						}
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

		let copy_src = self.keys.as_ptr().add(index);
		let copy_dst = self.keys.as_mut_ptr().add(index + 1);

		// Copy keys forward
		copy(copy_src, copy_dst, copy_len);
		// Insert new key
		*self.keys.get_unchecked_mut(index) = MaybeUninit::new(key);

		let copy_src = self.values.as_ptr().add(index);
		let copy_dst = self.values.as_mut_ptr().add(index + 1);

		// Copy values forward
		copy(copy_src, copy_dst, copy_len);
		// Insert new value
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
		let src = self.keys.as_ptr().offset(pivot as isize);
		let dest = new_node.keys.as_mut_ptr();
		copy_nonoverlapping(src, dest, new_len as usize);

		// Copy half of values
		let src = self.values.as_ptr().offset(pivot as isize);
		let dest = new_node.values.as_mut_ptr();
		copy_nonoverlapping(src, dest, new_len as usize);

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

		let bubble_key = read(self.keys.get_unchecked(new_left_len as usize)).assume_init();
		let bubble_value = read(self.values.get_unchecked(new_left_len as usize)).assume_init();

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

		let copy_src = self.keys.as_ptr().add(index);
		let copy_dst = self.keys.as_mut_ptr().add(index + 1);

		// Copy keys forward
		copy(copy_src, copy_dst, copy_len);
		// Insert new key
		*self.keys.get_unchecked_mut(index) = MaybeUninit::new(key);

		let copy_src = self.values.as_ptr().add(index);
		let copy_dst = self.values.as_mut_ptr().add(index + 1);

		// Copy values forward
		copy(copy_src, copy_dst, copy_len);
		// Insert new value
		*self.values.get_unchecked_mut(index) = MaybeUninit::new(value);

		// Copy length must be at least 1 since we are always copying the rightmost pointer
		let copy_src = self.children.as_ptr().add(index + 1);
		let copy_dst = self.children.as_mut_ptr().add(index + 2);

		// Copy children forward
		copy(copy_src, copy_dst, copy_len);
		// Insert new child
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
		let src = self.keys.as_ptr().offset(pivot as isize);
		let dest = new_node.keys.as_mut_ptr();
		copy_nonoverlapping(src, dest, new_len as usize);

		// Copy half of values
		let src = self.values.as_ptr().offset(pivot as isize);
		let dest = new_node.values.as_mut_ptr();
		copy_nonoverlapping(src, dest, new_len as usize);

		// Insert new element - now we're sure that whichever node has room
		// Insert bubbled-up key and value only - we will handle the new right node later
		if insert_left {
			let copy_len = self.len - pivot;
			let src = self.children.as_ptr().add(pivot as usize + 1);
			let dest = new_node.children.as_mut_ptr().add(1);

			// Copy child values to the right node - leave a space at the start for later transfer from the left node
			copy_nonoverlapping(src, dest, copy_len as usize);

			// Update length
			self.len = pivot;

			self.insert_at_index_unchecked_internal(new_right_node, bubble, index);

			// Move child from end of left node to start of right node
			*new_node.children.as_mut_ptr() = *self.children.as_ptr().add(pivot as usize);
		}
		else {
			let copy_len = self.len - pivot + 1;
			let src = self.children.as_ptr().add(pivot as usize);
			let dest = new_node.children.as_mut_ptr();

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

		let bubble_key = read(self.keys.get_unchecked(new_left_len as usize)).assume_init();
		let bubble_value = read(self.values.get_unchecked(new_left_len as usize)).assume_init();

		self.len = new_left_len;

		(Box::new(new_node), (bubble_key, bubble_value))
	}

	unsafe fn remove_at_index_unchecked_leaf(&mut self, index: usize) -> V {
		debug_assert!(index <= self.len as usize);

		let removed_value = self.values.get_unchecked(index).as_ptr().read();

		let copy_len = self.len as usize - index - 1;

		let copy_src = self.keys.as_ptr().add(index + 1);
		let copy_dst = self.keys.as_mut_ptr().add(index);

		// Copy keys backwards
		copy(copy_src, copy_dst, copy_len);

		let copy_src = self.values.as_ptr().add(index + 1);
		let copy_dst = self.values.as_mut_ptr().add(index);

		// Copy values backwards
		copy(copy_src, copy_dst, copy_len);

		self.len -= 1;

		removed_value
	}

	unsafe fn remove_last(&mut self) -> (V, *mut Node<K, V>) {
		let index = self.len() as usize;

		let removed_value = self.values.get_unchecked(index).as_ptr().read();
		let removed_child = self.children.get_unchecked(index + 1).as_ptr().read();

		self.len -= 1;

		(removed_value, removed_child)
	}

	unsafe fn remove_first(&mut self) -> (V, *mut Node<K, V>) {
		let removed_value = self.values.get_unchecked(0).as_ptr().read();
		let removed_child = self.children.get_unchecked(0).as_ptr().read();

		let copy_len = self.len as usize - 1;

		let copy_src = self.keys.as_ptr().add(1);
		let copy_dst = self.keys.as_mut_ptr().add(0);

		// Copy keys backwards
		copy(copy_src, copy_dst, copy_len);

		let copy_src = self.values.as_ptr().add(1);
		let copy_dst = self.values.as_mut_ptr().add(0);

		// Copy values backwards
		copy(copy_src, copy_dst, copy_len);

		let copy_src = self.children.as_ptr().add(1);
		let copy_dst = self.children.as_mut_ptr().add(0);

		// Copy children backwards
		copy(copy_src, copy_dst, copy_len);

		self.len -= 1;

		(removed_value, removed_child)
	}

	unsafe fn rebalance(&mut self, child_index: usize) {
		let child_link = self.children.get_unchecked_mut(child_index).assume_init();
		let child = match child_link.as_mut() {
			None => unreachable_unchecked(),
			Some(child) => child,
		};

		let child_len = child.len();
		if child_len >= B / 2 {
			// No rebalancing needed - early exit
			return;
		}

		let (selected_sibling_index, left_sibling) = match child_index {
			0 => (child_index + 1, false),
			_ => (child_index - 1, true),
		};

		let sibling_link = self
			.children
			.get_unchecked_mut(selected_sibling_index)
			.assume_init();
		let sibling = match sibling_link.as_mut() {
			None => unreachable_unchecked(),
			Some(sibling) => sibling,
		};

		let sibling_len = sibling.len();
		if sibling_len >= B / 2 {
			// Do rotation
			if left_sibling {
				todo!()
			}
			else {
				todo!()
			}
		}
		else {
			// Do merge
			if left_sibling {
				todo!()
			}
			else {
				todo!()
			}
		}
	}
}

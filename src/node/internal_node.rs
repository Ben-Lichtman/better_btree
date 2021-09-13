use crate::{
	node::{
		leaf_node::LeafNode, marker, search, uninit_array, NodeInsertResult, NodeRebalanceResult,
		NodeRef, NodeRemoveResult,
	},
	B,
};
use core::{
	fmt::Debug,
	mem::{replace, MaybeUninit},
	ptr::{copy, copy_nonoverlapping, drop_in_place},
};

// SAFETY: len should always be >= 1
// SAFETY: children must always be initialised in the range [0..self.data.len + 1)
// SAFETY: struct is #[repr(C)] to ensure that LeafNode may be soundly transmuted into an InternalNode
#[repr(C)]
pub struct InternalNode<K, V> {
	data: LeafNode<K, V>,
	children: [MaybeUninit<NodeRef<K, V, marker::Owned, marker::LeafOrInternal>>; B as usize],
}

impl<K, V> InternalNode<K, V> {
	pub fn new() -> Self {
		Self {
			data: LeafNode::new_for_internal(),
			children: uninit_array(),
		}
	}

	pub fn len(&self) -> usize { self.data.len() }

	pub fn insert(&mut self, key: K, value: V) -> NodeInsertResult<K, V>
	where
		K: Ord,
	{
		let index = search(&key, self.data.valid_keys());

		match index {
			Ok(index) => {
				// Key exists already - swap value and return

				// SAFETY: index must be within the valid array subslice since it is always < self.len
				let value_in_array = unsafe { self.data.values_mut().get_unchecked_mut(index) };
				// SAFETY: this value comes from the valid subslice of the array and therefore is valid
				let old_value_maybeuninit = replace(value_in_array, MaybeUninit::new(value));
				let old_value = unsafe { old_value_maybeuninit.assume_init() };

				NodeInsertResult::Existed(old_value)
			}
			Err(index) => {
				// SAFETY: index must be within the valid array subslice since it is always < self.len + 1
				let child = unsafe {
					self.children
						.get_unchecked_mut(index)
						.assume_init_mut()
						.as_mut()
				};
				let child_result = match child.is_internal() {
					false => {
						// SAFETY: we have just checked the type of the child ref so typecasting is sound
						unsafe { child.into_leaf().insert(key, value) }
					}
					true => {
						// SAFETY: we have just checked the type of the child ref so typecasting is sound
						unsafe { child.into_internal().insert(key, value) }
					}
				};

				let (bubble, new_node) = match child_result {
					NodeInsertResult::Existed(x) => return NodeInsertResult::Existed(x),
					NodeInsertResult::Ok => return NodeInsertResult::Ok,
					NodeInsertResult::SplitLeaf { bubble, new_node } => {
						(bubble, new_node.into_type_erased())
					}

					NodeInsertResult::SplitInternal { bubble, new_node } => {
						(bubble, new_node.into_type_erased())
					}
				};

				if self.len() != B as usize - 1 {
					// SAFETY: binary search guarantees index <= self.len
					unsafe { self.insert_unchecked_right(index, bubble, new_node) };
					NodeInsertResult::Ok
				}
				else {
					let (bubble, new_node) = if index <= (B as usize - 1) / 2 {
						// SAFETY: node is full
						// SAFETY: index is on the left half of the node
						unsafe { self.split_left_unchecked(bubble, new_node, index) }
					}
					else {
						// SAFETY: node is full
						// SAFETY: index is on the right half of the node
						unsafe { self.split_right_unchecked(bubble, new_node, index) }
					};
					NodeInsertResult::SplitInternal { bubble, new_node }
				}
			}
		}
	}

	pub fn remove(&mut self, key: &K) -> NodeRemoveResult<K, V>
	where
		K: Ord,
	{
		let index = search(key, self.data.valid_keys());

		match index {
			Ok(index) => {
				// SAFETY: index must be within the valid array subslice since it is always < self.len
				let indexed_key_ptr = unsafe {
					self.data
						.keys_mut()
						.get_unchecked_mut(index)
						.assume_init_mut()
				} as *mut K;
				// SAFETY: index must be within the valid array subslice since it is always < self.len
				let indexed_value_ptr = unsafe {
					self.data
						.values_mut()
						.get_unchecked_mut(index)
						.assume_init_mut()
				} as *mut V;

				// SAFETY: sound since we will be overwriting this key with a key from a leaf node
				let key = unsafe { indexed_key_ptr.read() };

				// SAFETY: sound since we will be overwriting this value with a value from a leaf node
				let value = unsafe { indexed_value_ptr.read() };

				// SAFETY: index must be within the valid array subslice since it is always < self.len
				let left_child =
					unsafe { self.children.get_unchecked_mut(index).assume_init_mut() };

				match left_child.is_internal() {
					// SAFETY: we have just checked the type of the child ref so typecasting is sound
					false => unsafe {
						left_child
							.as_mut()
							.into_leaf()
							.swap_with_left_leaf(indexed_key_ptr, indexed_value_ptr)
					},
					// SAFETY: we have just checked the type of the child ref so typecasting is sound
					true => unsafe {
						left_child
							.as_mut()
							.into_internal()
							.swap_with_left_leaf(indexed_key_ptr, indexed_value_ptr)
					},
				}

				// SAFETY: index is < self.len therefore this is sound
				match unsafe { self.rebalance(index) } {
					NodeRebalanceResult::None => NodeRemoveResult::Removed(key, value),
					NodeRebalanceResult::Rotated => NodeRemoveResult::Removed(key, value),
					NodeRebalanceResult::Merged => NodeRemoveResult::Merged(key, value),
				}
			}
			Err(index) => {
				// SAFETY: index must be within the valid array subslice since it is always < self.len + 1
				let child = unsafe {
					self.children
						.get_unchecked_mut(index)
						.assume_init_mut()
						.as_mut()
				};
				match child.is_internal() {
					false => {
						let mut child = unsafe { child.into_leaf() };
						match child.remove(key) {
							NodeRemoveResult::NotThere => NodeRemoveResult::NotThere,
							NodeRemoveResult::Removed(k, v) | NodeRemoveResult::Merged(k, v) => {
								// SAFETY: index is < self.len therefore this is sound
								match unsafe { self.rebalance(index) } {
									NodeRebalanceResult::None | NodeRebalanceResult::Rotated => {
										NodeRemoveResult::Removed(k, v)
									}
									NodeRebalanceResult::Merged => NodeRemoveResult::Merged(k, v),
								}
							}
						}
					}
					true => {
						let mut child = unsafe { child.into_internal() };
						match child.remove(key) {
							NodeRemoveResult::NotThere => NodeRemoveResult::NotThere,
							NodeRemoveResult::Removed(k, v) | NodeRemoveResult::Merged(k, v) => {
								// SAFETY: index is < self.len therefore this is sound
								match unsafe { self.rebalance(index) } {
									NodeRebalanceResult::None | NodeRebalanceResult::Rotated => {
										NodeRemoveResult::Removed(k, v)
									}
									NodeRebalanceResult::Merged => NodeRemoveResult::Merged(k, v),
								}
							}
						}
					}
				}
			}
		}
	}

	pub fn children(
		&self,
	) -> &[MaybeUninit<NodeRef<K, V, marker::Owned, marker::LeafOrInternal>>; B as usize] {
		&self.children
	}

	pub fn children_mut(
		&mut self,
	) -> &mut [MaybeUninit<NodeRef<K, V, marker::Owned, marker::LeafOrInternal>>; B as usize] {
		&mut self.children
	}

	pub fn valid_children(&self) -> &[NodeRef<K, V, marker::Owned, marker::LeafOrInternal>] {
		let len = self.len();
		debug_assert!(len != 0);
		// SAFETY: self.children is always valid in range [0..self.len + 1)
		unsafe { &*(self.children.get_unchecked(0..len + 1) as *const _ as *const _) }
	}

	pub fn valid_children_mut(
		&mut self,
	) -> &mut [NodeRef<K, V, marker::Owned, marker::LeafOrInternal>] {
		let len = self.len();
		debug_assert!(len != 0);
		// SAFETY: self.children is always valid in range [0..self.len + 1)
		unsafe { &mut *(self.children.get_unchecked_mut(0..len + 1) as *mut _ as *mut _) }
	}

	// SAFETY: node must be completely full
	// SAFETY: index must be <= (B - 1) / 2
	pub unsafe fn split_left_unchecked(
		&mut self,
		bubble: (K, V),
		bubbled_right_node: NodeRef<K, V, marker::Owned, marker::LeafOrInternal>,
		index: usize,
	) -> ((K, V), NodeRef<K, V, marker::Owned, marker::InternalNode>)
	where
		K: Ord,
	{
		debug_assert!(self.len() == B as usize - 1);
		debug_assert!(index <= (B as usize - 1) / 2);

		// Create new right node
		let mut right_node = Self::new();

		let pivot = (B as usize - 1) / 2;

		let right_len = B as usize - 1 - pivot;

		// Copy half of keys
		let src = self.data.keys().as_ptr().add(pivot);
		let dest = right_node.data.keys_mut().as_mut_ptr();
		copy_nonoverlapping(src, dest, right_len);

		// Copy half of values
		let src = self.data.values().as_ptr().add(pivot);
		let dest = right_node.data.values_mut().as_mut_ptr();
		copy_nonoverlapping(src, dest, right_len);

		// Copy half of child values to the right node - leaving a space on the left side for later copying from the left node
		let copy_len = B as usize - 1 - pivot;
		let src = self.children.as_ptr().add(pivot + 1);
		let dest = right_node.children.as_mut_ptr().add(1);
		copy_nonoverlapping(src, dest, copy_len);

		self.data.set_len(pivot);

		self.insert_unchecked_right(index, bubble, bubbled_right_node);

		let ((bubble_key, bubble_value), orphan_node) = self.remove_unchecked_right(pivot);

		// Move child from end of right side of left node to left side of right node
		*right_node.children.get_unchecked_mut(0).as_mut_ptr() = orphan_node;

		right_node.data.set_len(right_len);

		let right_node = NodeRef::from_boxed_internal(Box::new(right_node));
		((bubble_key, bubble_value), right_node)
	}

	// SAFETY: node must be completely full
	// SAFETY: index must be < (B - 1)
	// SAFETY: index must be > (B - 1) / 2
	pub unsafe fn split_right_unchecked(
		&mut self,
		bubble: (K, V),
		bubbled_right_node: NodeRef<K, V, marker::Owned, marker::LeafOrInternal>,
		index: usize,
	) -> ((K, V), NodeRef<K, V, marker::Owned, marker::InternalNode>)
	where
		K: Ord,
	{
		debug_assert!(self.len() == B as usize - 1);
		debug_assert!(index < B as usize);
		debug_assert!(index >= (B as usize - 1) / 2);

		// Create new right node
		let mut right_node = Self::new();

		let pivot = (B as usize - 1) / 2 + 1;

		let right_len = B as usize - 1 - pivot;

		// Copy half of keys
		let src = self.data.keys().as_ptr().add(pivot);
		let dest = right_node.data.keys_mut().as_mut_ptr();
		copy_nonoverlapping(src, dest, right_len);

		// Copy half of values
		let src = self.data.values().as_ptr().add(pivot);
		let dest = right_node.data.values_mut().as_mut_ptr();
		copy_nonoverlapping(src, dest, right_len);

		// Copy half of child values to the right node
		let copy_len = B as usize - pivot;
		let src = self.children.as_ptr().add(pivot);
		let dest = right_node.children.as_mut_ptr();
		copy_nonoverlapping(src, dest, copy_len);

		right_node.data.set_len(right_len);

		right_node.insert_unchecked_right(index - pivot, bubble, bubbled_right_node);

		let bubble_key = self.data.keys().get_unchecked(pivot - 1).as_ptr().read();
		let bubble_value = self.data.values().get_unchecked(pivot - 1).as_ptr().read();

		self.data.set_len(pivot - 1);

		let right_node = NodeRef::from_boxed_internal(Box::new(right_node));
		((bubble_key, bubble_value), right_node)
	}

	pub unsafe fn swap_with_left_leaf(&mut self, key_hole: *mut K, value_hole: *mut V) {
		let len = self.len();
		let rightmost_child = (&mut *self.children.get_unchecked_mut(len).as_mut_ptr()).as_mut();

		match rightmost_child.is_internal() {
			false => rightmost_child
				.into_leaf()
				.swap_with_left_leaf(key_hole, value_hole),
			true => rightmost_child
				.into_internal()
				.swap_with_left_leaf(key_hole, value_hole),
		}

		self.rebalance(len);
	}

	// SAFETY: child_index must be <= self.len + 1
	pub unsafe fn rebalance(&mut self, child_index: usize) -> NodeRebalanceResult {
		debug_assert!(child_index <= self.len() + 1);

		let child = (&mut *self.children.get_unchecked_mut(child_index).as_mut_ptr()).as_mut();

		if child.len() >= (B as usize - 1) / 2 {
			// No rebalancing needed - early exit
			return NodeRebalanceResult::None;
		}

		let children_are_internal = child.is_internal();

		let (pivot_index, selected_sibling_index, child_is_left) = match child_index {
			0 => (child_index, child_index + 1, true),
			_ => (child_index - 1, child_index - 1, false),
		};

		let sibling = (&mut *self
			.children
			.get_unchecked_mut(selected_sibling_index)
			.as_mut_ptr())
			.as_mut();

		let sibling_len = sibling.len();

		if sibling_len > B as usize / 2 {
			// Do rotation
			match (children_are_internal, child_is_left) {
				(false, false) => self.rotate_right_leaf(pivot_index),
				(false, true) => self.rotate_left_leaf(pivot_index),
				(true, false) => self.rotate_right_internal(pivot_index),
				(true, true) => self.rotate_left_internal(pivot_index),
			}
			NodeRebalanceResult::Rotated
		}
		else {
			// Do merge
			match children_are_internal {
				false => self.merge_leaf(pivot_index),
				true => self.merge_internal(pivot_index),
			}
			NodeRebalanceResult::Merged
		}
	}

	// SAFETY: pivot_index must be < self.len
	// SAFETY: the children of this node must be internal nodes
	pub unsafe fn rotate_left_internal(&mut self, pivot_index: usize) {
		debug_assert!(pivot_index < self.len());

		let mut child = (&mut *self.children.get_unchecked_mut(pivot_index).as_mut_ptr())
			.as_mut()
			.into_internal();
		let mut sibling = (&mut *self
			.children
			.get_unchecked_mut(pivot_index + 1)
			.as_mut_ptr())
			.as_mut()
			.into_internal();

		let child_len = child.len();

		// Copy key / value out of parent
		let parent_key = self.data.keys().get_unchecked(pivot_index).as_ptr().read();
		let parent_value = self
			.data
			.values()
			.get_unchecked(pivot_index)
			.as_ptr()
			.read();

		// Remove from the left side of the sibling node
		let ((sibling_key, sibling_value), sibling_child) = sibling.remove_unchecked_left(0);

		// Add to the right side of the child node
		child.insert_unchecked_right(child_len, (parent_key, parent_value), sibling_child);

		// Copy key / value in to replace the ones copied out earlier
		*self.data.keys_mut().get_unchecked_mut(pivot_index) = MaybeUninit::new(sibling_key);
		*self.data.values_mut().get_unchecked_mut(pivot_index) = MaybeUninit::new(sibling_value);
	}

	// SAFETY: pivot_index must be < self.len
	// SAFETY: the children of this node must be internal nodes
	pub unsafe fn rotate_right_internal(&mut self, pivot_index: usize) {
		debug_assert!(pivot_index < self.len());

		let mut child = (&mut *self
			.children
			.get_unchecked_mut(pivot_index + 1)
			.as_mut_ptr())
			.as_mut()
			.into_internal();
		let mut sibling = (&mut *self.children.get_unchecked_mut(pivot_index).as_mut_ptr())
			.as_mut()
			.into_internal();

		let sibling_len = sibling.len();

		// Copy key / value out of parent
		let parent_key = self.data.keys().get_unchecked(pivot_index).as_ptr().read();
		let parent_value = self
			.data
			.values()
			.get_unchecked(pivot_index)
			.as_ptr()
			.read();

		// Remove from the right side of the sibling node
		let ((sibling_key, sibling_value), sibling_child) =
			sibling.remove_unchecked_right(sibling_len - 1);

		// Add to the right side of the child node
		child.insert_unchecked_left(0, (parent_key, parent_value), sibling_child);

		// Copy key / value in to replace the ones copied out earlier
		*self.data.keys_mut().get_unchecked_mut(pivot_index) = MaybeUninit::new(sibling_key);
		*self.data.values_mut().get_unchecked_mut(pivot_index) = MaybeUninit::new(sibling_value);
	}

	// SAFETY: pivot_index must be < self.len
	// SAFETY: the children of this node must be leaf nodes
	pub unsafe fn rotate_left_leaf(&mut self, pivot_index: usize) {
		debug_assert!(pivot_index < self.len());

		let mut child = (&mut *self.children.get_unchecked_mut(pivot_index).as_mut_ptr())
			.as_mut()
			.into_leaf();
		let mut sibling = (&mut *self
			.children
			.get_unchecked_mut(pivot_index + 1)
			.as_mut_ptr())
			.as_mut()
			.into_leaf();

		let child_len = child.len();

		// Copy key / value out of parent
		let parent_key = self.data.keys().get_unchecked(pivot_index).as_ptr().read();
		let parent_value = self
			.data
			.values()
			.get_unchecked(pivot_index)
			.as_ptr()
			.read();

		// Remove from the left side of the sibling node
		let (sibling_key, sibling_value) = sibling.remove_unchecked(0);

		// Add to the right side of the child node
		child.insert_unchecked(child_len, (parent_key, parent_value));

		// Copy key / value in to replace the ones copied out earlier
		*self.data.keys_mut().get_unchecked_mut(pivot_index) = MaybeUninit::new(sibling_key);
		*self.data.values_mut().get_unchecked_mut(pivot_index) = MaybeUninit::new(sibling_value);
	}

	// SAFETY: pivot_index must be < self.len
	// SAFETY: the children of this node must be leaf nodes
	pub unsafe fn rotate_right_leaf(&mut self, pivot_index: usize) {
		debug_assert!(pivot_index < self.len());

		let mut child = (&mut *self
			.children
			.get_unchecked_mut(pivot_index + 1)
			.as_mut_ptr())
			.as_mut()
			.into_leaf();
		let mut sibling = (&mut *self.children.get_unchecked_mut(pivot_index).as_mut_ptr())
			.as_mut()
			.into_leaf();

		let sibling_len = sibling.len();

		// Copy key / value out of parent
		let parent_key = self.data.keys().get_unchecked(pivot_index).as_ptr().read();
		let parent_value = self
			.data
			.values()
			.get_unchecked(pivot_index)
			.as_ptr()
			.read();

		// Remove from the right side of the sibling node
		let (sibling_key, sibling_value) = sibling.remove_unchecked(sibling_len - 1);

		// Add to the right side of the child node
		child.insert_unchecked(0, (parent_key, parent_value));

		// Copy key / value in to replace the ones copied out earlier
		*self.data.keys_mut().get_unchecked_mut(pivot_index) = MaybeUninit::new(sibling_key);
		*self.data.values_mut().get_unchecked_mut(pivot_index) = MaybeUninit::new(sibling_value);
	}

	// SAFETY: pivot_index must be < self.len
	// SAFETY: the children of this node must be internal nodes
	pub unsafe fn merge_internal(&mut self, pivot_index: usize) {
		debug_assert!(pivot_index < self.len());

		let mut left_node = (&mut *self.children.get_unchecked_mut(pivot_index).as_mut_ptr())
			.as_mut()
			.into_internal();

		let ((parent_key, parent_value), right_node) = self.remove_unchecked_right(pivot_index);

		let mut right_node = right_node.into_internal().into_boxed_internal();

		let left_len = left_node.len();
		let right_len = right_node.len();

		// Copy orphaned key and value into the left node
		*left_node
			.data
			.keys_mut()
			.get_unchecked_mut(left_len)
			.as_mut_ptr() = parent_key;
		*left_node
			.data
			.values_mut()
			.get_unchecked_mut(left_len)
			.as_mut_ptr() = parent_value;

		// Copy keys from right node to left node
		let copy_src = right_node.data.keys().get_unchecked(0).as_ptr();
		let copy_dst = left_node
			.data
			.keys_mut()
			.get_unchecked_mut(left_len + 1)
			.as_mut_ptr();
		copy_nonoverlapping(copy_src, copy_dst, right_len);

		// Copy values from right node to left node
		let copy_src = right_node.data.values().get_unchecked(0).as_ptr();
		let copy_dst = left_node
			.data
			.values_mut()
			.get_unchecked_mut(left_len + 1)
			.as_mut_ptr();
		copy_nonoverlapping(copy_src, copy_dst, right_len);

		// Copy children from right node to left node
		let copy_src = right_node.children.get_unchecked(0).as_ptr();
		let copy_dst = left_node
			.children
			.get_unchecked_mut(left_len + 1)
			.as_mut_ptr();
		copy_nonoverlapping(copy_src, copy_dst, right_len + 1);

		// Set node lengths
		left_node.data.set_len(left_len + right_len + 1);
		right_node.data.set_len(0);
	}

	// SAFETY: pivot_index must be < self.len
	// SAFETY: the children of this node must be leaf nodes
	pub unsafe fn merge_leaf(&mut self, pivot_index: usize) {
		debug_assert!(pivot_index < self.len());

		let mut left_node = (&mut *self.children.get_unchecked_mut(pivot_index).as_mut_ptr())
			.as_mut()
			.into_leaf();

		let ((parent_key, parent_value), right_node) = self.remove_unchecked_right(pivot_index);

		let mut right_node = right_node.into_leaf().into_boxed_leaf();

		let left_len = left_node.len();
		let right_len = right_node.len();

		// Copy orphaned key and value into the left node
		*left_node
			.keys_mut()
			.get_unchecked_mut(left_len)
			.as_mut_ptr() = parent_key;
		*left_node
			.values_mut()
			.get_unchecked_mut(left_len)
			.as_mut_ptr() = parent_value;

		// Copy keys from right node to left node
		let copy_src = right_node.keys().get_unchecked(0).as_ptr();
		let copy_dst = left_node
			.keys_mut()
			.get_unchecked_mut(left_len + 1)
			.as_mut_ptr();
		copy_nonoverlapping(copy_src, copy_dst, right_len);

		// Copy values from right node to left node
		let copy_src = right_node.values().get_unchecked(0).as_ptr();
		let copy_dst = left_node
			.values_mut()
			.get_unchecked_mut(left_len + 1)
			.as_mut_ptr();
		copy_nonoverlapping(copy_src, copy_dst, right_len);

		// Set node lengths
		left_node.set_len(left_len + right_len + 1);
		right_node.set_len(0);
	}

	// SAFETY: index must be <= self.len
	// SAFETY: self.len must be < B - 1
	pub unsafe fn insert_unchecked_left(
		&mut self,
		index: usize,
		(key, value): (K, V),
		child: NodeRef<K, V, marker::Owned, marker::LeafOrInternal>,
	) {
		debug_assert!(index <= self.len());
		debug_assert!(self.len() < B as usize - 1);

		let copy_len = self.len() + 1 - index;

		// copy children forward
		let keys_ptr = self.children.as_mut_ptr();
		let copy_src = keys_ptr.add(index);
		let copy_dst = keys_ptr.add(index + 1);
		copy(copy_src, copy_dst, copy_len);

		// Insert new key / value
		*self.children.get_unchecked_mut(index) = MaybeUninit::new(child);

		self.data.insert_unchecked(index, (key, value))
	}

	// SAFETY: index must be <= self.len
	// SAFETY: self.len must be > 0
	pub unsafe fn insert_unchecked_right(
		&mut self,
		index: usize,
		(key, value): (K, V),
		child: NodeRef<K, V, marker::Owned, marker::LeafOrInternal>,
	) {
		debug_assert!(index <= self.len());
		debug_assert!(self.len() < B as usize - 1);

		let copy_len = self.len() - index;

		// copy children forward
		let keys_ptr = self.children.as_mut_ptr();
		let copy_src = keys_ptr.add(index + 1);
		let copy_dst = keys_ptr.add(index + 2);
		copy(copy_src, copy_dst, copy_len);

		// Insert new key / value
		*self.children.get_unchecked_mut(index + 1) = MaybeUninit::new(child);

		self.data.insert_unchecked(index, (key, value))
	}

	// SAFETY: index must be < self.len
	// SAFETY: self.len must be > 0
	pub unsafe fn remove_unchecked_left(
		&mut self,
		index: usize,
	) -> ((K, V), NodeRef<K, V, marker::Owned, marker::LeafOrInternal>) {
		debug_assert!(index < self.len());

		// copy child out of the array
		let child = self.children.get_unchecked(index).as_ptr().read();

		let copy_len = self.len() - index;

		// copy children backwards from removal spot
		let keys_ptr = self.children.as_mut_ptr();
		let copy_src = keys_ptr.add(index + 1);
		let copy_dst = keys_ptr.add(index);
		copy(copy_src, copy_dst, copy_len);

		let (key, value) = self.data.remove_unchecked(index);
		((key, value), child)
	}

	// SAFETY: index must be < self.len
	// SAFETY: self.len must be > 0
	pub unsafe fn remove_unchecked_right(
		&mut self,
		index: usize,
	) -> ((K, V), NodeRef<K, V, marker::Owned, marker::LeafOrInternal>) {
		debug_assert!(index < self.len());

		// copy child out of the array
		let child = self.children.get_unchecked(index + 1).as_ptr().read();

		let copy_len = self.len() - index - 1;

		// copy children backwards from removal spot
		let keys_ptr = self.children.as_mut_ptr();
		let copy_src = keys_ptr.add(index + 2);
		let copy_dst = keys_ptr.add(index + 1);

		copy(copy_src, copy_dst, copy_len);

		let (key, value) = self.data.remove_unchecked(index);
		((key, value), child)
	}
}

impl<K, V> Debug for InternalNode<K, V>
where
	K: Debug,
	V: Debug,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let children = self
			.valid_children()
			.iter()
			.map(|c| c.as_ref())
			.collect::<Vec<_>>();
		f.debug_struct("InternalNode")
			.field("len", &self.len())
			// Taking the valid array subslice
			.field("keys", &self.data.valid_keys())
			// Taking the valid array subslice
			.field("values", &self.data.valid_values())
			.field("children", &children)
			.finish()
	}
}

impl<K, V> Drop for InternalNode<K, V> {
	fn drop(&mut self) {
		// drop internal data
		unsafe { drop_in_place(&mut self.data) }
		// drop children
		if self.len() != 0 {
			for child in self.valid_children_mut() {
				let is_internal = child.is_internal();

				let child = child as *mut NodeRef<K, V, marker::Owned, marker::LeafOrInternal>;

				let copied_out = unsafe {
					(child as *mut NodeRef<K, V, marker::Owned, marker::LeafOrInternal>).read()
				};

				match is_internal {
					// SAFETY: we have already checked to make sure that the variant is correct
					false => unsafe {
						copied_out.into_leaf().into_boxed_leaf();
					},
					// SAFETY: we have already checked to make sure that the variant is correct
					true => unsafe {
						copied_out.into_internal().into_boxed_internal();
					},
				};
			}
		}
	}
}

impl<K, V> Clone for InternalNode<K, V>
where
	K: Clone,
	V: Clone,
{
	fn clone(&self) -> Self {
		let len = self.len() as usize;
		let data = self.data.clone();
		let mut children = uninit_array();
		// SAFETY: we know self.values is valid in the range [0..len + 1)
		// SAFETY: since we are cloning, the cloned array must also be valid in the same range
		unsafe {
			children
				.get_unchecked_mut(0..len + 1)
				.iter_mut()
				.zip(self.children.get_unchecked(0..len + 1).iter())
				.for_each(|(dest, src)| {
					dest.write(src.assume_init_ref().clone());
				})
		}

		Self { data, children }
	}
}

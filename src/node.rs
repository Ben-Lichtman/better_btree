pub mod internal_node;
pub mod leaf_node;

use crate::node_ref::{marker, NodeRef};
use internal_node::InternalNode;
use leaf_node::LeafNode;
use std::{
	cmp::Ordering,
	fmt::Debug,
	mem::{replace, ManuallyDrop, MaybeUninit},
	ops::Deref,
};

pub enum NodeInsertResult<K, V> {
	SplitLeaf {
		bubble: (K, V),
		new_node: NodeRef<K, V, marker::Owned, marker::LeafNode>,
	},
	SplitInternal {
		bubble: (K, V),
		new_node: NodeRef<K, V, marker::Owned, marker::InternalNode>,
	},
	Existed(V),
	Ok,
}

pub enum NodeRemoveResult<K, V> {
	NotThere,
	Removed(K, V),
	Merged(K, V),
}

pub enum NodeRebalanceResult {
	None,
	Merged,
	Rotated,
}

// This should later be replaced with MaybeUnint::uninit_array() when stabilised
#[inline(always)]
fn uninit_array<T, const LEN: usize>() -> [MaybeUninit<T>; LEN] {
	// SAFETY: An uninitialized `[MaybeUninit<_>; LEN]` is valid.
	unsafe { MaybeUninit::<[MaybeUninit<T>; LEN]>::uninit().assume_init() }
}

const LINEAR_SEARCH: bool = false;

fn search<K: Ord>(needle: &K, haystack: &[K]) -> Result<usize, usize> {
	if LINEAR_SEARCH {
		for (n, key) in haystack.iter().enumerate() {
			match key.cmp(needle) {
				Ordering::Greater => return Err(n),
				Ordering::Equal => return Ok(n),
				Ordering::Less => (),
			}
		}
		Err(haystack.len())
	}
	else {
		haystack.binary_search(needle)
	}
}

#[repr(C)]
pub union RootNode<K, V> {
	leaf: ManuallyDrop<LeafNode<K, V>>,
	internal: ManuallyDrop<InternalNode<K, V>>,
}

impl<K, V> RootNode<K, V> {
	pub fn new() -> Self {
		RootNode {
			leaf: ManuallyDrop::new(LeafNode::new()),
		}
	}

	pub fn is_internal(&self) -> bool {
		// SAFETY: both variants are repr(c) and may be soundly transmuted between each other
		unsafe { self.leaf.is_internal() }
	}

	pub fn len(&self) -> usize {
		// SAFETY: both variants are repr(c) and may be soundly transmuted between each other
		unsafe { self.leaf.len() }
	}

	pub fn insert(&mut self, key: K, value: V) -> Option<V>
	where
		K: Ord,
	{
		let is_internal = self.is_internal();

		let result = match is_internal {
			// SAFETY: we have already checked to make sure that the variant is correct
			false => unsafe { self.leaf.insert(key, value) },
			// SAFETY: we have already checked to make sure that the variant is correct
			true => unsafe { self.internal.insert(key, value) },
		};

		let (bubble, new_node) = match result {
			NodeInsertResult::Existed(old) => return Some(old),
			NodeInsertResult::Ok => return None,
			NodeInsertResult::SplitLeaf { bubble, new_node } => {
				(bubble, new_node.into_type_erased())
			}
			NodeInsertResult::SplitInternal { bubble, new_node } => {
				(bubble, new_node.into_type_erased())
			}
		};

		// We have split - replace the root with a new root

		let old_root_owned = match is_internal {
			false => {
				let old_root = replace(
					self,
					RootNode {
						internal: ManuallyDrop::new(InternalNode::new()),
					},
				);
				// SAFETY: we have already checked to make sure that this is a leaf node
				let old_root_leaf = unsafe { old_root.destructure_leaf() };
				let boxed = Box::new(old_root_leaf);
				NodeRef::from_boxed_leaf(boxed).into_type_erased()
			}
			true => {
				let old_root = replace(
					self,
					RootNode {
						internal: ManuallyDrop::new(InternalNode::new()),
					},
				);
				// SAFETY: we have already checked to make sure that this is an internal node
				let old_root_internal = unsafe { old_root.destructure_internal() };
				let boxed = Box::new(old_root_internal);
				NodeRef::from_boxed_internal(boxed).into_type_erased()
			}
		};

		// SAFETY: root is currently a completely empty InternalNode - we are not corrupting any existing information
		unsafe {
			*self.internal.children_mut().get_unchecked_mut(0) = MaybeUninit::new(old_root_owned);
		}

		// SAFETY: function will leave child[0] untouched and insert key/value + child[1] then increment len to 1
		unsafe {
			self.internal.insert_unchecked_right(0, bubble, new_node);
		}

		None
	}

	pub fn remove(&mut self, key: &K) -> Option<V>
	where
		K: Ord,
	{
		let is_internal = self.is_internal();

		let result = match is_internal {
			// SAFETY: we have already checked to make sure that the variant is correct
			false => unsafe { self.leaf.remove(key) },
			// SAFETY: we have already checked to make sure that the variant is correct
			true => unsafe { self.internal.remove(key) },
		};

		let (_, value) = match result {
			NodeRemoveResult::NotThere => return None,
			NodeRemoveResult::Removed(_, value) => return Some(value),
			NodeRemoveResult::Merged(key, value) => (key, value),
		};

		if is_internal && self.len() == 0 {
			let new_root = unsafe { self.internal.children().get_unchecked(0).as_ptr().read() };
			match new_root.is_internal() {
				false => {
					// SAFETY: we have already checked to make sure that the variant is correct
					let new_root_leaf = unsafe { new_root.into_leaf().into_boxed_leaf() };

					// Move the node out of the box and into the root node
					*self = RootNode {
						leaf: ManuallyDrop::new(*new_root_leaf),
					};
				}
				true => {
					// SAFETY: we have already checked to make sure that the variant is correct
					let new_root_internal =
						unsafe { new_root.into_internal().into_boxed_internal() };

					// Move the node out of the box and into the root node
					*self = RootNode {
						internal: ManuallyDrop::new(*new_root_internal),
					};
				}
			}
		}

		Some(value)
	}

	// SAFETY: this node must be a leaf node
	unsafe fn destructure_leaf(self) -> LeafNode<K, V> {
		debug_assert!(!self.is_internal());

		// Prevent self from having drop called on it
		let nodrop = ManuallyDrop::new(self);

		(nodrop.leaf.deref() as *const LeafNode<_, _>).read()
	}

	// SAFETY: this node must be a leaf node
	unsafe fn destructure_internal(self) -> InternalNode<K, V> {
		debug_assert!(self.is_internal());

		// Prevent self from having drop called on it
		let nodrop = ManuallyDrop::new(self);

		(nodrop.internal.deref() as *const InternalNode<_, _>).read()
	}
}

impl<K, V> Debug for RootNode<K, V>
where
	K: Debug,
	V: Debug,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let is_internal = self.is_internal();

		match is_internal {
			// SAFETY: we have already checked to make sure that the variant is correct
			false => unsafe { self.leaf.deref().fmt(f) },
			// SAFETY: we have already checked to make sure that the variant is correct
			true => unsafe { self.internal.deref().fmt(f) },
		}
	}
}

impl<K, V> Drop for RootNode<K, V> {
	fn drop(&mut self) {
		let is_internal = self.is_internal();

		match is_internal {
			// SAFETY: we have already checked to make sure that the variant is correct
			false => unsafe {
				ManuallyDrop::drop(&mut self.leaf);
			},
			// SAFETY: we have already checked to make sure that the variant is correct
			true => unsafe {
				ManuallyDrop::drop(&mut self.internal);
			},
		};
	}
}

impl<K, V> Clone for RootNode<K, V>
where
	K: Clone,
	V: Clone,
{
	fn clone(&self) -> Self {
		let is_internal = self.is_internal();

		match is_internal {
			// SAFETY: we have already checked to make sure that the variant is correct
			false => Self {
				leaf: unsafe { self.leaf.clone() },
			},
			// SAFETY: we have already checked to make sure that the variant is correct
			true => Self {
				internal: unsafe { self.internal.clone() },
			},
		}
	}
}

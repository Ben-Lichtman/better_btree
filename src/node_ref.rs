pub mod marker;

use crate::node::{internal_node::InternalNode, leaf_node::LeafNode};
use core::{
	fmt::Debug,
	marker::PhantomData,
	ops::{Deref, DerefMut},
	ptr::NonNull,
};

// Type erased immutably borrowed pointer type which points to either a leaf or internal node
pub struct NodeRef<K, V, BorrowType, NodeKind> {
	pointer: NonNull<InternalNode<K, V>>,
	_phantom: PhantomData<(BorrowType, NodeKind)>,
}
impl<'a, K, V, Type> Copy for NodeRef<K, V, marker::Immut<'a>, Type> {}
impl<'a, K, V, Type> Clone for NodeRef<K, V, marker::Immut<'a>, Type> {
	fn clone(&self) -> Self { *self }
}

impl<'a, K, V> Clone for NodeRef<K, V, marker::Owned, marker::LeafNode>
where
	K: Clone,
	V: Clone,
{
	fn clone(&self) -> Self { self.deref().clone() }
}

impl<'a, K, V> Clone for NodeRef<K, V, marker::Owned, marker::InternalNode>
where
	K: Clone,
	V: Clone,
{
	fn clone(&self) -> Self { self.deref().clone() }
}

impl<'a, K, V> Clone for NodeRef<K, V, marker::Owned, marker::LeafOrInternal>
where
	K: Clone,
	V: Clone,
{
	fn clone(&self) -> Self {
		let is_internal = self.is_internal();

		match is_internal {
			false => {
				// SAFETY: we have already checked to make sure that the variant is correct
				let noderef = unsafe { self.as_ref().into_leaf() };
				let clone = noderef.deref().clone();
				NodeRef::from_boxed_leaf(Box::new(clone)).into_type_erased()
			}
			true => {
				// SAFETY: we have already checked to make sure that the variant is correct
				let noderef = unsafe { self.as_ref().into_internal() };
				let clone = noderef.deref().clone();
				NodeRef::from_boxed_internal(Box::new(clone)).into_type_erased()
			}
		}
	}
}

impl<K, V> Debug for NodeRef<K, V, marker::Immut<'_>, marker::LeafOrInternal>
where
	K: Debug,
	V: Debug,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let is_internal = self.is_internal();

		match is_internal {
			false => {
				// SAFETY: we have already checked to make sure that the variant is correct
				let noderef = unsafe { self.into_leaf() };
				noderef.fmt(f)
			}
			true => {
				// SAFETY: we have already checked to make sure that the variant is correct
				let noderef = unsafe { self.into_internal() };
				noderef.fmt(f)
			}
		}
	}
}

impl<K, V, BorrowType, Type> NodeRef<K, V, BorrowType, Type> {
	// SAFETY: while this may not actually point to a leaf node, we cast the internal pointer to a leafnode pointer for the sake of accessing the is_internal boolean. This is sound because of the repr(C) data layout of InternalNode
	pub fn is_internal(&self) -> bool {
		unsafe { self.pointer.cast::<LeafNode<K, V>>().as_ref().is_internal() }
	}

	// SAFETY: while this may not actually point to a leaf node, we cast the internal pointer to a leafnode pointer for the sake of accessing the len integer. This is sound because of the repr(C) data layout of InternalNode
	pub fn len(&self) -> usize { unsafe { self.pointer.cast::<LeafNode<K, V>>().as_ref().len() } }
}

// A type erased reference that may be either a leaf or internal node
impl<K, V, BorrowType: marker::BorrowType> NodeRef<K, V, BorrowType, marker::LeafOrInternal> {
	// SAFETY: caller must ensure that this reference actually refers to an internal node
	pub unsafe fn into_internal(self) -> NodeRef<K, V, BorrowType, marker::InternalNode> {
		NodeRef {
			pointer: self.pointer,
			_phantom: PhantomData,
		}
	}

	// SAFETY: caller must ensure that this reference actually refers to a leaf node
	pub unsafe fn into_leaf(self) -> NodeRef<K, V, BorrowType, marker::LeafNode> {
		NodeRef {
			pointer: self.pointer,
			_phantom: PhantomData,
		}
	}
}

impl<K, V, BorrowType: marker::BorrowType> NodeRef<K, V, BorrowType, marker::LeafNode> {
	pub fn into_type_erased(self) -> NodeRef<K, V, BorrowType, marker::LeafOrInternal> {
		NodeRef {
			pointer: self.pointer,
			_phantom: PhantomData,
		}
	}
}

impl<K, V, BorrowType: marker::BorrowType> NodeRef<K, V, BorrowType, marker::InternalNode> {
	pub fn into_type_erased(self) -> NodeRef<K, V, BorrowType, marker::LeafOrInternal> {
		NodeRef {
			pointer: self.pointer,
			_phantom: PhantomData,
		}
	}
}

impl<K, V> NodeRef<K, V, marker::Owned, marker::LeafNode> {
	pub fn from_boxed_leaf(node: Box<LeafNode<K, V>>) -> Self {
		let pointer = NonNull::from(Box::leak(node)).cast();
		Self {
			pointer,
			_phantom: PhantomData,
		}
	}

	// SAFETY: caller asserts that the internal pointer actually points to a leaf node
	pub unsafe fn into_boxed_leaf(self) -> Box<LeafNode<K, V>> {
		Box::from_raw(self.pointer.as_ptr() as _)
	}
}

impl<K, V> NodeRef<K, V, marker::Owned, marker::InternalNode> {
	pub fn from_boxed_internal(node: Box<InternalNode<K, V>>) -> Self {
		let pointer = NonNull::from(Box::leak(node)).cast();
		Self {
			pointer,
			_phantom: PhantomData,
		}
	}

	// SAFETY: caller asserts that the internal pointer actually points to an internal node
	pub unsafe fn into_boxed_internal(self) -> Box<InternalNode<K, V>> {
		Box::from_raw(self.pointer.as_ptr() as _)
	}
}

impl<K, V, Type> NodeRef<K, V, marker::Owned, Type> {
	pub fn as_ref(&self) -> NodeRef<K, V, marker::Immut<'_>, Type> {
		let pointer = self.pointer;
		NodeRef {
			pointer,
			_phantom: PhantomData,
		}
	}

	pub fn as_mut(&mut self) -> NodeRef<K, V, marker::Mut<'_>, Type> {
		let pointer = self.pointer;
		NodeRef {
			pointer,
			_phantom: PhantomData,
		}
	}
}

impl<'a, K, V> From<&LeafNode<K, V>> for NodeRef<K, V, marker::Immut<'a>, marker::LeafNode> {
	fn from(input: &LeafNode<K, V>) -> Self {
		let pointer = NonNull::from(input).cast();
		Self {
			pointer,
			_phantom: PhantomData,
		}
	}
}

impl<'a, K, V> From<&mut LeafNode<K, V>> for NodeRef<K, V, marker::Mut<'a>, marker::LeafNode> {
	fn from(input: &mut LeafNode<K, V>) -> Self {
		let pointer = NonNull::from(input).cast();
		Self {
			pointer,
			_phantom: PhantomData,
		}
	}
}

impl<'a, K, V> From<&mut LeafNode<K, V>> for NodeRef<K, V, marker::Immut<'a>, marker::LeafNode> {
	fn from(input: &mut LeafNode<K, V>) -> Self {
		let pointer = NonNull::from(input).cast();
		Self {
			pointer,
			_phantom: PhantomData,
		}
	}
}

impl<'a, K, V> From<&LeafNode<K, V>> for NodeRef<K, V, marker::Immut<'a>, marker::InternalNode> {
	fn from(input: &LeafNode<K, V>) -> Self {
		let pointer = NonNull::from(input).cast();
		Self {
			pointer,
			_phantom: PhantomData,
		}
	}
}

impl<'a, K, V> From<&mut LeafNode<K, V>> for NodeRef<K, V, marker::Mut<'a>, marker::InternalNode> {
	fn from(input: &mut LeafNode<K, V>) -> Self {
		let pointer = NonNull::from(input).cast();
		Self {
			pointer,
			_phantom: PhantomData,
		}
	}
}

impl<'a, K, V> From<&mut LeafNode<K, V>>
	for NodeRef<K, V, marker::Immut<'a>, marker::InternalNode>
{
	fn from(input: &mut LeafNode<K, V>) -> Self {
		let pointer = NonNull::from(input).cast();
		Self {
			pointer,
			_phantom: PhantomData,
		}
	}
}

impl<'a, K, V> Deref for NodeRef<K, V, marker::Immut<'a>, marker::LeafNode> {
	type Target = LeafNode<K, V>;

	// SAFETY: This pointer will always point to a valid leaf node as as invariant
	fn deref(&self) -> &Self::Target { unsafe { self.pointer.cast().as_ref() } }
}

impl<'a, K, V> Deref for NodeRef<K, V, marker::Immut<'a>, marker::InternalNode> {
	type Target = InternalNode<K, V>;

	// SAFETY: This pointer will always point to a valid internal node as as invariant
	fn deref(&self) -> &Self::Target { unsafe { self.pointer.cast().as_ref() } }
}

impl<'a, K, V> Deref for NodeRef<K, V, marker::Mut<'a>, marker::LeafNode> {
	type Target = LeafNode<K, V>;

	// SAFETY: This pointer will always point to a valid leaf node as as invariant
	fn deref(&self) -> &Self::Target { unsafe { self.pointer.cast().as_ref() } }
}

impl<'a, K, V> Deref for NodeRef<K, V, marker::Mut<'a>, marker::InternalNode> {
	type Target = InternalNode<K, V>;

	// SAFETY: This pointer will always point to a valid internal node as as invariant
	fn deref(&self) -> &Self::Target { unsafe { self.pointer.cast().as_ref() } }
}

impl<'a, K, V> DerefMut for NodeRef<K, V, marker::Mut<'a>, marker::LeafNode> {
	// SAFETY: This pointer will always point to a valid leaf node as as invariant
	fn deref_mut(&mut self) -> &mut Self::Target { unsafe { self.pointer.cast().as_mut() } }
}

impl<'a, K, V> DerefMut for NodeRef<K, V, marker::Mut<'a>, marker::InternalNode> {
	// SAFETY: This pointer will always point to a valid internal node as as invariant
	fn deref_mut(&mut self) -> &mut Self::Target { unsafe { self.pointer.cast().as_mut() } }
}

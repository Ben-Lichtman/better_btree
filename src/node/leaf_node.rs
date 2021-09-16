use crate::{
	node::{marker, search, uninit_array, NodeInsertResult, NodeRef, NodeRemoveResult},
	B,
};
use core::{
	fmt::Debug,
	mem::{replace, MaybeUninit},
	ptr::{copy, copy_nonoverlapping, drop_in_place},
};

// SAFETY: keys and values must always be initialised in the range [0..self.len)
// SAFETY: if is_internal is true, this node may be safely transmuted into an InternalNode
pub struct LeafNode<K, V> {
	len: u8,
	is_internal: bool,
	keys: [MaybeUninit<K>; (B - 1) as usize],
	values: [MaybeUninit<V>; (B - 1) as usize],
}

impl<K, V> LeafNode<K, V> {
	pub fn new() -> Self {
		Self {
			len: 0,
			is_internal: false,
			keys: uninit_array(),
			values: uninit_array(),
		}
	}

	pub fn new_for_internal() -> Self {
		Self {
			len: 0,
			is_internal: true,
			keys: uninit_array(),
			values: uninit_array(),
		}
	}

	pub fn is_internal(&self) -> bool { self.is_internal }

	pub fn len(&self) -> usize { self.len as usize }

	pub fn insert(&mut self, key: K, value: V) -> NodeInsertResult<K, V>
	where
		K: Ord,
	{
		let index = search(&key, self.valid_keys());

		match index {
			Ok(index) => {
				// Key exists already - swap value and return

				// SAFETY: index must be within the valid array subslice since it is always < self.len
				let value_in_array = unsafe { self.values.get_unchecked_mut(index) };
				// SAFETY: this value comes from the valid subslice of the array and therefore is valid
				let old_value_maybeuninit = replace(value_in_array, MaybeUninit::new(value));
				let old_value = unsafe { old_value_maybeuninit.assume_init() };

				NodeInsertResult::Existed(old_value)
			}
			Err(index) => {
				if self.len() != B as usize - 1 {
					// SAFETY: binary search guarantees index <= self.len
					unsafe { self.insert_unchecked(index, (key, value)) };
					NodeInsertResult::Ok
				}
				else {
					let (bubble, new_node) = if index <= (B as usize - 1) / 2 {
						// SAFETY: node is full
						// SAFETY: index is on the left half of the node
						unsafe { self.split_left_unchecked((key, value), index) }
					}
					else {
						// SAFETY: node is full
						// SAFETY: index is on the right half of the node
						unsafe { self.split_right_unchecked((key, value), index) }
					};
					NodeInsertResult::SplitLeaf { bubble, new_node }
				}
			}
		}
	}

	pub fn remove(&mut self, key: &K) -> NodeRemoveResult<K, V>
	where
		K: Ord,
	{
		let index = search(key, self.valid_keys());

		match index {
			Ok(index) => {
				// SAFETY: index < self.len therefore this is sound
				let (key, value) = unsafe { self.remove_unchecked(index) };
				NodeRemoveResult::Removed(key, value)
			}
			Err(_) => NodeRemoveResult::NotThere,
		}
	}

	pub fn get(&self, key: &K) -> Option<&V>
	where
		K: Ord,
	{
		let index = search(key, self.valid_keys());

		match index {
			Ok(index) => {
				// SAFETY: index < self.len therefore this is sound
				let result = unsafe { self.values.get_unchecked(index).assume_init_ref() };
				Some(result)
			}
			Err(_) => None,
		}
	}

	pub fn get_mut(&mut self, key: &K) -> Option<&mut V>
	where
		K: Ord,
	{
		let index = search(key, self.valid_keys());

		match index {
			Ok(index) => {
				// SAFETY: index < self.len therefore this is sound
				let result = unsafe { self.values.get_unchecked_mut(index).assume_init_mut() };
				Some(result)
			}
			Err(_) => None,
		}
	}

	pub fn keys(&self) -> &[MaybeUninit<K>; (B - 1) as usize] { &self.keys }

	pub fn keys_mut(&mut self) -> &mut [MaybeUninit<K>; (B - 1) as usize] { &mut self.keys }

	pub fn values(&self) -> &[MaybeUninit<V>; (B - 1) as usize] { &self.values }

	pub fn values_mut(&mut self) -> &mut [MaybeUninit<V>; (B - 1) as usize] { &mut self.values }

	pub fn valid_keys(&self) -> &[K] {
		let len = self.len();
		// SAFETY: self.keys is always valid in range [0..self.len)
		unsafe { &*(self.keys.get_unchecked(0..len) as *const _ as *const _) }
	}

	pub fn valid_keys_mut(&mut self) -> &mut [K] {
		let len = self.len();
		// SAFETY: self.keys is always valid in range [0..self.len)
		unsafe { &mut *(self.keys.get_unchecked_mut(0..len) as *mut _ as *mut _) }
	}

	pub fn valid_values(&self) -> &[V] {
		let len = self.len();
		// SAFETY: self.values is always valid in range [0..self.len)
		unsafe { &*(self.values.get_unchecked(0..len) as *const _ as *const _) }
	}

	pub fn valid_values_mut(&mut self) -> &mut [V] {
		let len = self.len();
		// SAFETY: self.values is always valid in range [0..self.len)
		unsafe { &mut *(self.values.get_unchecked_mut(0..len) as *mut _ as *mut _) }
	}

	pub unsafe fn set_len(&mut self, new_len: usize) { self.len = new_len as _ }

	// SAFETY: node must be completely full
	// SAFETY: index must be <= (B - 1) / 2
	pub unsafe fn split_left_unchecked(
		&mut self,
		pair: (K, V),
		index: usize,
	) -> ((K, V), NodeRef<K, V, marker::Owned, marker::LeafNode>)
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
		let src = self.keys.as_ptr().add(pivot);
		let dest = right_node.keys.as_mut_ptr();
		copy_nonoverlapping(src, dest, right_len);

		// Copy half of values
		let src = self.values.as_ptr().add(pivot);
		let dest = right_node.values.as_mut_ptr();
		copy_nonoverlapping(src, dest, right_len);

		self.len = pivot as u8;

		self.insert_unchecked(index, pair);

		let (bubble_key, bubble_value) = self.remove_unchecked(pivot);

		right_node.len = right_len as u8;

		let right_node = NodeRef::from_boxed_leaf(Box::new(right_node));
		((bubble_key, bubble_value), right_node)
	}

	// SAFETY: node must be completely full
	// SAFETY: index must be < (B - 1)
	// SAFETY: index must be > (B - 1) / 2
	pub unsafe fn split_right_unchecked(
		&mut self,
		pair: (K, V),
		index: usize,
	) -> ((K, V), NodeRef<K, V, marker::Owned, marker::LeafNode>)
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
		let src = self.keys.as_ptr().add(pivot);
		let dest = right_node.keys.as_mut_ptr();
		copy_nonoverlapping(src, dest, right_len);

		// Copy half of values
		let src = self.values.as_ptr().add(pivot);
		let dest = right_node.values.as_mut_ptr();
		copy_nonoverlapping(src, dest, right_len);

		right_node.len = right_len as u8;

		right_node.insert_unchecked(index - pivot, pair);

		let bubble_key = self.keys.get_unchecked(pivot - 1).as_ptr().read();
		let bubble_value = self.values.get_unchecked(pivot - 1).as_ptr().read();

		self.len = pivot as u8 - 1;

		let right_node = NodeRef::from_boxed_leaf(Box::new(right_node));
		((bubble_key, bubble_value), right_node)
	}

	pub unsafe fn swap_with_left_leaf(&mut self, key_hole: *mut K, value_hole: *mut V) {
		let len = self.len();

		let (key, value) = self.remove_unchecked(len - 1);
		*key_hole = key;
		*value_hole = value;
	}

	// SAFETY: index must be <= self.len
	// SAFETY: self.len must be < B - 1
	pub unsafe fn insert_unchecked(&mut self, index: usize, (key, value): (K, V)) {
		debug_assert!(index <= self.len());
		debug_assert!(self.len() < B as usize - 1);

		let copy_len = self.len() - index;

		// copy keys forward
		let keys_ptr = self.keys.as_mut_ptr();
		let copy_src = keys_ptr.add(index);
		let copy_dst = keys_ptr.add(index + 1);
		copy(copy_src, copy_dst, copy_len);

		// copy values forward
		let values_ptr = self.values.as_mut_ptr();
		let copy_src = values_ptr.add(index);
		let copy_dst = values_ptr.add(index + 1);
		copy(copy_src, copy_dst, copy_len);

		// Insert new key / value
		*self.keys.get_unchecked_mut(index) = MaybeUninit::new(key);
		*self.values.get_unchecked_mut(index) = MaybeUninit::new(value);

		self.len += 1;
	}

	// SAFETY: index must be < self.len
	// SAFETY: self.len must be > 0
	pub unsafe fn remove_unchecked(&mut self, index: usize) -> (K, V) {
		debug_assert!(index < self.len());

		// copy key and value out of the array
		let output_key = self.keys.get_unchecked(index).as_ptr().read();
		let output_value = self.values.get_unchecked(index).as_ptr().read();

		let copy_len = self.len() - index - 1;

		// copy keys backwards from removal spot
		let keys_ptr = self.keys.as_mut_ptr();
		let copy_src = keys_ptr.add(index + 1);
		let copy_dst = keys_ptr.add(index);
		copy(copy_src, copy_dst, copy_len);

		// copy values backwards from removal spot
		let values_ptr = self.values.as_mut_ptr();
		let copy_src = values_ptr.add(index + 1);
		let copy_dst = values_ptr.add(index);
		copy(copy_src, copy_dst, copy_len);

		self.len -= 1;

		(output_key, output_value)
	}
}

impl<K, V> Debug for LeafNode<K, V>
where
	K: Debug,
	V: Debug,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		f.debug_struct("LeafNode")
			.field("len", &self.len())
			// Taking the valid array subslice
			.field("keys", &self.valid_keys())
			// Taking the valid array subslice
			.field("values", &self.valid_values())
			.finish()
	}
}

impl<K, V> Drop for LeafNode<K, V> {
	fn drop(&mut self) {
		// drop keys
		unsafe { drop_in_place(self.valid_keys_mut()) }
		// drop values
		unsafe { drop_in_place(self.valid_values_mut()) }
	}
}

impl<K, V> Clone for LeafNode<K, V>
where
	K: Clone,
	V: Clone,
{
	fn clone(&self) -> Self {
		let len = self.len;
		let is_internal = self.is_internal;
		let mut keys = uninit_array();
		// SAFETY: we know self.keys is valid in the range [0..len)
		// SAFETY: since we are cloning, the cloned array must also be valid in the same range
		unsafe {
			keys.get_unchecked_mut(0..len as usize)
				.iter_mut()
				.zip(self.keys.get_unchecked(0..len as usize).iter())
				.for_each(|(dest, src)| {
					dest.write(src.assume_init_ref().clone());
				})
		}
		let mut values = uninit_array();
		// SAFETY: we know self.values is valid in the range [0..len)
		// SAFETY: since we are cloning, the cloned array must also be valid in the same range
		unsafe {
			values
				.get_unchecked_mut(0..len as usize)
				.iter_mut()
				.zip(self.values.get_unchecked(0..len as usize).iter())
				.for_each(|(dest, src)| {
					dest.write(src.assume_init_ref().clone());
				})
		}
		Self {
			len,
			is_internal,
			keys,
			values,
		}
	}
}

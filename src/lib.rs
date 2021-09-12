mod node;
mod node_ref;

use crate::node::RootNode;

const B: u16 = 12;

#[derive(Debug)]
pub struct BTreeSet<K> {
	root: RootNode<K, ()>,
}

impl<K> BTreeSet<K>
where
	K: Ord,
{
	pub fn new() -> Self {
		Self {
			root: RootNode::new(),
		}
	}

	pub fn insert(&mut self, key: K) -> bool { self.root.insert(key, ()).is_some() }

	pub fn remove(&mut self, key: &K) -> bool { self.root.remove(key).is_some() }
}

impl<K> Default for BTreeSet<K>
where
	K: Ord,
{
	fn default() -> Self { Self::new() }
}

#[derive(Debug)]
pub struct BTreeMap<K, V> {
	root: RootNode<K, V>,
}

impl<K, V> BTreeMap<K, V>
where
	K: Ord,
{
	pub fn new() -> Self {
		Self {
			root: RootNode::new(),
		}
	}

	pub fn insert(&mut self, key: K, value: V) -> Option<V> { self.root.insert(key, value) }

	pub fn remove(&mut self, key: &K) -> Option<V> { self.root.remove(key) }
}

impl<K, V> Default for BTreeMap<K, V>
where
	K: Ord,
{
	fn default() -> Self { Self::new() }
}

mod node;
mod node_ref;

use crate::node::RootNode;

const B: u16 = 3;

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

	pub fn insert(&mut self, key: K) -> Option<()> { self.root.insert(key, ()) }

	pub fn remove(&mut self, key: K) -> Option<()> { self.root.remove(key) }
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

	pub fn remove(&mut self, key: K) -> Option<V> { self.root.remove(key) }
}

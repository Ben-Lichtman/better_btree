use std::marker::PhantomData;

pub trait BorrowType {}

pub enum Owned {}
pub struct Immut<'a>(PhantomData<&'a ()>);
pub struct Mut<'a>(PhantomData<&'a mut ()>);

impl BorrowType for Owned {}
impl BorrowType for Immut<'_> {}
impl BorrowType for Mut<'_> {}

pub enum LeafNode {}
pub enum InternalNode {}
pub enum LeafOrInternal {}

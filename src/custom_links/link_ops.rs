pub trait LinkOps {
    type LinkPtr: Copy;

    fn is_linked(&self, ptr: Self::LinkPtr) -> bool;

    unsafe fn mark_unlinked(&mut self, ptr: Self::LinkPtr);

    unsafe fn ptr_eq(&self, this: Self::LinkPtr, other: Self::LinkPtr) -> bool;
}

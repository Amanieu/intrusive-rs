pub trait LinkOps {
    type LinkPtr: Copy;

    fn is_linked(&self, ptr: Self::LinkPtr) -> bool;

    unsafe fn mark_unlinked(&mut self, ptr: Self::LinkPtr);
}

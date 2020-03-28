use super::adapter::Adapter;

pub trait KeyAdapter<'a>: Adapter {
    /// Type of the key returned by `get_key`.
    type Key;

    /// Gets the key for the given object.
    fn get_key(&self, value: &'a Self::Value) -> Self::Key;
}

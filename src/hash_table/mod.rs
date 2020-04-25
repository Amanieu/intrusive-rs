// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use core::borrow::Borrow;
use core::fmt;

use crate::adapter::Adapter;
use crate::key_adapter::KeyAdapter;
use crate::link_ops::{self, DefaultLinkOps};
use crate::linked_list;
use crate::pointer_ops::{DefaultPointerOps, PointerOps};
use crate::singly_linked_list;
use crate::unchecked_option::UncheckedOptionExt;
use crate::unsafe_ref::UnsafeRef;
use crate::xor_linked_list;

mod array;
mod bucket_ops;
mod hash_ops;
mod hash_table;
mod load_factor;

pub use self::array::Array;
pub use self::bucket_ops::{BucketOps, DefaultBucketOps};
pub use self::hash_ops::{DefaultHashOps, HashOps};
pub use self::hash_table::{
    BucketCursor, BucketCursorMut, Cursor, CursorMut, Drain, HashTable, HashTableAdapter,
    InsertCursor, IntoIter, Iter, KeyOps, RawEntryBuilder, RawEntryBuilderMut, RawEntryMut,
};
pub use self::load_factor::LoadFactor;

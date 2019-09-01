// Copyright 2019 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! Bits and bit arrays.

use core::fmt;
use core::mem::size_of;
use core::ops;

use crate::array::Array;

/// A binary representation.
pub trait Bits:
    Copy
    + Eq
    + Sized
    + Send
    + Sync
    + fmt::Binary
    + fmt::Debug
    + fmt::Display
    + fmt::LowerHex
    + fmt::UpperHex
    + ops::BitAnd<Self, Output = Self>
    + ops::BitAndAssign<Self>
    + ops::BitOr<Self, Output = Self>
    + ops::BitOrAssign<Self>
    + ops::BitXor<Self, Output = Self>
    + ops::BitXorAssign<Self>
    + ops::Not<Output = Self>
    + ops::Shl<usize, Output = Self>
    + ops::ShlAssign<usize>
    + ops::Shr<usize, Output = Self>
    + ops::ShrAssign<usize>
{
    /// The number of bits in the binary representation of `self`.
    const BITS: usize = size_of::<Self>() * 8;
    
    const MASK: usize = Self::BITS - 1;
    
    const INDX: usize = Self::BITS.trailing_zeros() as usize;

    /// The 'zero' value that can be represented by this integer type.
    const ZERO: Self;

    /// The 'one' value that can be represented by this integer type.
    const ONE: Self;

    /// The smallest value that can be represented by this integer type.
    const MIN: Self;

    /// The largest value that can be represented by this integer type.
    const MAX: Self;

    /// Returns the number of ones in the binary representation of `self`.
    fn count_ones(self) -> usize;

    /// Returns the number of zeros in the binary representation of `self`.
    fn count_zeros(self) -> usize;

    /// Returns the number of leading zeros in the binary representation of `self`.
    fn leading_zeros(self) -> usize;

    /// Returns the number of trailing zeros in the binary representation of `self`.
    fn trailing_zeros(self) -> usize;

    /// Shifts the bits to the left by a specified amount, `n`, wrapping the truncated bits to the end of the resulting integer.
    ///
    /// Please note this isn't the same operation as the `<<` shifting operator!
    fn rotate_left(self, n: usize) -> Self;

    /// Shifts the bits to the right by a specified amount, `n`, wrapping the truncated bits to the end of the resulting integer.
    ///
    /// Please note this isn't the same operation as the `>>` shifting operator!
    fn rotate_right(self, n: usize) -> Self;

    /// Panic-free bitwise shift-left; yields `self << mask(rhs)`,
    /// where `mask` removes any high-order bits of `rhs` that
    /// would cause the shift to exceed the bitwidth of the type.
    /// 
    /// Note that this is *not* the same as a rotate-left; the
    /// RHS of a wrapping shift-left is restricted to the range
    /// of the type, rather than the bits shifted out of the LHS
    /// being returned to the other end. The primitive integer
    /// types all implement a `rotate_left` function, which may
    /// be what you want instead.
    fn wrapping_shl(self, rhs: usize) -> Self;

    /// Panic-free bitwise shift-right; yields `self << mask(rhs)`,
    /// where `mask` removes any high-order bits of `rhs` that
    /// would cause the shift to exceed the bitwidth of the type.
    /// 
    /// Note that this is *not* the same as a rotate-right; the
    /// RHS of a wrapping shift-right is restricted to the range
    /// of the type, rather than the bits shifted out of the LHS
    /// being returned to the other end. The primitive integer
    /// types all implement a `rotate_right` function, which may
    /// be what you want instead.
    fn wrapping_shr(self, rhs: usize) -> Self;
}

macro_rules! impl_int_bits {
    ($($T:ty)+) => {
        $(
            impl Bits for $T {
                const ZERO: $T = 0;
                const ONE: $T = 1;
                const MIN: $T = <$T>::min_value();
                const MAX: $T = <$T>::max_value();

                #[inline(always)]
                fn count_ones(self) -> usize {
                    <$T>::count_ones(self) as usize
                }

                #[inline(always)]
                fn count_zeros(self) -> usize {
                    <$T>::count_zeros(self) as usize
                }

                #[inline(always)]
                fn leading_zeros(self) -> usize {
                    <$T>::leading_zeros(self) as usize
                }

                #[inline(always)]
                fn trailing_zeros(self) -> usize {
                    <$T>::trailing_zeros(self) as usize
                }

                #[inline(always)]
                fn rotate_left(self, n: usize) -> Self {
                    <$T>::rotate_left(self, n as u32)
                }

                #[inline(always)]
                fn rotate_right(self, n: usize) -> Self {
                    <$T>::rotate_right(self, n as u32)
                }

                #[inline(always)]
                fn wrapping_shl(self, rhs: usize) -> Self {
                    <$T>::wrapping_shl(self, rhs as u32)
                }

                #[inline(always)]
                fn wrapping_shr(self, rhs: usize) -> Self {
                    <$T>::wrapping_shr(self, rhs as u32)
                }
            }
        )+
    }
}

impl_int_bits! {
    i8 i16 i32 isize
    u8 u16 u32 usize
}

#[cfg(any(target_arch = "x86_64"))]
impl_int_bits! {
    i64 u64
}

impl_int_bits! {
    i128 u128
}

/// A binary representation of an array.
pub trait BitsArray<T: Bits>: Array<Item = T> {
    /// Returns the number of ones in the binary representation of `self`.
    #[inline]
    fn count_ones(&self) -> usize {
        self.as_slice()
            .iter()
            .fold(0, |acc, bits| acc + bits.count_ones())
    }

    /// Returns the number of zeros in the binary representation of `self`.
    #[inline]
    fn count_zeros(&self) -> usize {
        self.as_slice()
            .iter()
            .fold(0, |acc, bits| acc + bits.count_zeros())
    }

    /// Returns the number of leading zeros in the binary representation of `self`.
    #[inline]
    fn leading_zeros(&self) -> usize {
        let mut acc = 0;

        for bits in self.as_slice().iter() {
            if *bits == T::ZERO {
                acc += T::BITS;
            } else {
                acc += bits.leading_zeros();
                break;
            }
        }

        acc
    }

    /// Returns the number of trailing zeros in the binary representation of `self`.
    #[inline]
    fn trailing_zeros(&self) -> usize {
        let mut acc = 0;

        for bits in self.as_slice().iter().rev() {
            if *bits == T::ZERO {
                acc += T::BITS;
            } else {
                acc += bits.trailing_zeros();
                break;
            }
        }

        acc
    }

    /// Clears the bits.
    #[inline]
    fn clear(&mut self) {
        for i in self.as_mut_slice().iter_mut() {
            *i = T::ZERO;
        }
    }

    /// Returns the boolean representation of a bit.
    #[inline]
    fn get_bit(&self, index: usize) -> Option<bool> {
        if index >= self.len() * T::BITS {
            None
        } else {
            let word = index >> T::INDX;
            let bit = index & T::MASK;

            Some(self.as_slice()[word] >> bit & T::ONE == T::ONE)
        }
    }

    /// Sets the value of a bit.
    #[inline]
    fn set_bit(&mut self, index: usize, val: bool) {
        if index < self.len() * T::BITS {
            let word = index >> T::INDX;
            let bit = index & T::MASK;

            if val {
                self.as_mut_slice()[word] |= T::ONE << bit;
            } else {
                self.as_mut_slice()[word] &= !(T::ONE << bit);
            }
        }
    }

    /// Returns the offset of the next `1` bit that follows `after`.
    #[inline]
    fn find_next_one(&self, after: Option<usize>) -> Option<usize> {
        let start = match after {
            None => 0,
            Some(x) => x.saturating_add(1),
        };

        if start >= self.len() * T::BITS {
            return None;
        }

        let mut bit = start & T::MASK;
        let word_idx_base = start >> T::INDX;

        // word_idx starts at 0!
        for (word_idx, word) in (&self.as_slice()[(start >> T::INDX)..(self.len())])
            .iter()
            .enumerate()
        {
            let val = (*word >> bit) << bit;
            match val.trailing_zeros() {
                x if x >= T::BITS => {
                    bit = 0;
                    continue;
                }
                x => {
                    return Some(((word_idx + word_idx_base) << T::INDX) + x);
                }
            }
        }

        None
    }

    /// Returns the offset of the next `1` bit that preceeds `before`.
    #[inline]
    fn find_prev_one(&self, before: Option<usize>) -> Option<usize> {
        // inclusive end
        let (end_word, mut bit) = match before {
            None => (self.len().saturating_sub(1), T::BITS - 1),
            Some(0) => {
                return None;
            }
            Some(x) if x > T::BITS && x & T::MASK == 0 => ((x >> T::INDX).saturating_sub(1), 63),
            Some(x) => (x >> T::INDX, (x & T::INDX).saturating_sub(1)),
        };

        for word_idx in (0..=end_word).rev() {
            let word = self.as_slice()[word_idx];
            if word == T::ZERO {
                continue;
            }
            // clear the top bits
            let shift = T::BITS - bit;
            let val = word.wrapping_shl(shift).wrapping_shr(shift);

            match val.leading_zeros() {
                x if x >= T::BITS => {
                    bit = T::BITS;
                    continue;
                }
                x => {
                    return Some((word_idx << T::INDX) + T::BITS - x - 1);
                }
            }
        }

        None
    }

    /// Returns the offset of the next `0` bit that follows `after`.
    #[inline]
    fn find_next_zero(&self, after: Option<usize>) -> Option<usize> {
        let start = match after {
            None => 0,
            Some(x) => x.saturating_add(1),
        };

        if start >= self.len() * T::BITS {
            return None;
        }

        let mut bit = start & T::MASK;
        let word_idx_base = start >> T::INDX;

        // word_idx starts at 0!
        for (word_idx, word) in (&self.as_slice()[(start >> T::INDX)..(self.len())])
            .iter()
            .enumerate()
        {
            let val = ((!*word) >> bit) << bit;
            match val.trailing_zeros() {
                x if x >= T::BITS => {
                    bit = 0;
                    continue;
                }
                x => {
                    return Some(((word_idx + word_idx_base) << T::INDX) + x);
                }
            }
        }

        None
    }

    /// Returns the offset of the prev `0` bit that follows `after`.
    #[inline]
    fn find_prev_zero(&self, before: Option<usize>) -> Option<usize> {
        // inclusive end
        let (end_word, mut bit) = match before {
            None => (self.len().saturating_sub(1), T::BITS - 1),
            Some(0) => {
                return None;
            }
            Some(x) if x > T::BITS && x & T::MASK == 0 => ((x >> T::INDX).saturating_sub(1), 63),
            Some(x) => (x >> T::INDX, (x & T::INDX).saturating_sub(1)),
        };

        for word_idx in (0..=end_word).rev() {
            let word = self.as_slice()[word_idx];
            if word == T::ZERO {
                continue;
            }
            // clear the top bits
            let shift = T::BITS - bit;
            let val = !word.wrapping_shl(shift).wrapping_shr(shift);

            match val.leading_zeros() {
                x if x >= T::BITS => {
                    bit = T::BITS;
                    continue;
                }
                x => {
                    return Some((word_idx << T::INDX) + T::BITS - x - 1);
                }
            }
        }

        None
    }
}

impl<T: Bits, U: Array<Item = T>> BitsArray<T> for U {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_next_one() {
        assert_eq!(([1_u64 << 10]).find_next_one(None), Some(10));
        assert_eq!(([1_u64 << 10]).find_next_one(Some(10)), None);
        assert_eq!(([0_u64, 1 << 10]).find_next_one(None), Some(74));
        assert_eq!(([0_u64, 1 << 10]).find_next_one(Some(10)), Some(74));
        assert_eq!(([1_u64, 1 << 10]).find_next_one(Some(10)), Some(74));
        assert_eq!(([1_u64 << 63]).find_next_one(Some(63)), None);
        assert_eq!(([1_u64 << 63, 1 << 0]).find_next_one(Some(63)), Some(64));
    }

    #[test]
    fn test_find_prev_one() {
        assert_eq!(([1_u64 << 10]).find_prev_one(None), Some(10));
        assert_eq!(([1_u64 << 10]).find_prev_one(Some(10)), None);
        assert_eq!(([0_u64, 1 << 10]).find_prev_one(None), Some(74));
        assert_eq!(([0_u64, 1 << 10]).find_prev_one(Some(10)), None);
        assert_eq!(([1_u64, 1 << 10]).find_prev_one(Some(10)), Some(0));
    }
}

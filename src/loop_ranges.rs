// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//!
//! Loop ranges in regular expressions.
//!
//! SMT-LIB has a loop construct for regular expressions:
//! Given a language L, `(loop i j L)` means repetition of L for some number
//! between i and j. So we have:
//!
//!   `(loop i j L)` = union for k=i to j of L<sup>k</sup> (provided i<=j).
//!
//! We generalize this construct by allowing j to be +infinity. Then we
//! use loop to reduce the number of regular expression primitives that we need:
//! 1) L? is `(loop 0 1 L)`
//! 2) L<sup>+</sup> is `(loop 1 +infinity L)`
//! 3) L<sup>*</sup> is `(loop 0 +infinity L)`
//! 4) L<sup>k</sup> is `(loop k k L)`
//!
//! This module implements operations on loop ranges. Each range is
//! a pair (i, j) where 0 <= i <= j and j may be infinite.
//!
//! We limit i and j to u32. The code will panic in case of arithmetic overflow.
//!

use std::fmt::Display;

///
/// Loop range
///
/// A loop range is either a finite interval [i, j] or an infinite interval [i, ..]
/// - A finite interval is represented as `LoopRange(i, Some(j))` where 0 <= i <= j
/// - An infinite interval is represented as `LoopRange(i, None)`.
///
/// The integers i and j are stored as u32. Operations on loop ranges will panic if
/// results cannot be stored using 32bit unsigned integers.
///
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct LoopRange(u32, Option<u32>);

/// Wrapper for addition with overflow detection
///
/// Panics if there's an overflow.
/// Returns x + y otherwise.
fn add32(x: u32, y: u32) -> u32 {
    x.checked_add(y).expect("Arithmetic overflow (add u32)")
}

/// Wrapper for multiplication with overflow detection
///
/// Panics is there's an overflow.
/// Returns x * y otherwise.
fn mul32(x: u32, y: u32) -> u32 {
    x.checked_mul(y).expect("Arithmetic overflow (mul 32)")
}

impl Display for LoopRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoopRange(0, Some(1)) => write!(f, "?"),
            LoopRange(0, None) => write!(f, "*"),
            LoopRange(1, None) => write!(f, "+"),
            LoopRange(i, Some(j)) => {
                if i == j {
                    write!(f, "{}", i)
                } else {
                    write!(f, "[{}..{}]", i, j)
                }
            }
            LoopRange(i, None) => write!(f, "[{}..inf)", i),
        }
    }
}

impl LoopRange {
    /// Construct the finite range [i, j]
    pub fn finite(i: u32, j: u32) -> LoopRange {
        debug_assert!(i <= j);
        LoopRange(i, Some(j))
    }

    /// Construct the infinite range [i, +infinity]
    pub fn infinite(i: u32) -> LoopRange {
        LoopRange(i, None)
    }

    /// Construct the range [0, 1]
    pub fn opt() -> LoopRange {
        LoopRange::finite(0, 1)
    }

    /// Construct the range [0, +infinity]
    pub fn star() -> LoopRange {
        LoopRange::infinite(0)
    }

    /// Construct the range [1, +infinity]
    pub fn plus() -> LoopRange {
        LoopRange::infinite(1)
    }

    /// Construct the range [k, k]
    pub fn point(k: u32) -> LoopRange {
        LoopRange::finite(k, k)
    }

    /// Check whether this range is finite
    pub fn is_finite(&self) -> bool {
        matches!(self, LoopRange(_, Some(_)))
    }

    /// Check whether this range is infinite
    pub fn is_infinite(&self) -> bool {
        matches!(self, LoopRange(_, None))
    }

    /// Check whether this range is a singleton
    pub fn is_point(&self) -> bool {
        match self {
            LoopRange(i, Some(j)) => *i == *j,
            _ => false,
        }
    }

    /// Check whether this range is the singleton 0
    pub fn is_zero(&self) -> bool {
        matches!(self, LoopRange(0, Some(0)))
    }

    /// Check whether this range is the singleton 1
    pub fn is_one(&self) -> bool {
        matches!(self, LoopRange(1, Some(1)))
    }

    /// Check whether this range is [0, +infinity]
    pub fn is_all(&self) -> bool {
        matches!(self, LoopRange(0, None))
    }

    /// Start of the range
    pub fn start(&self) -> u32 {
        self.0
    }

    /// End of the range
    ///
    /// # Panics
    ///
    /// If the range is infinite, the end of the range is not an integer.
    /// This method will panic.
    fn end(&self) -> u32 {
        debug_assert!(self.is_finite());
        self.1.unwrap()
    }

    /// Size of the range.
    ///
    /// - For a finite range [i, j], the size is the number of of integers
    /// in the interval [i, j] (i.e., j - i + 1).
    /// - For an infinite range, the size is not defined,
    ///
    /// # Panics
    ///
    /// If the range is infinite.
    fn size(&self) -> u32 {
        debug_assert!(self.is_finite());
        self.1.unwrap() - self.0 + 1
    }

    ///
    /// Check whether an index is in a loop range
    ///
    pub fn contains(&self, i: u32) -> bool {
        match self {
            LoopRange(j, Some(k)) => *j <= i && i <= *k,
            LoopRange(j, None) => *j <= i,
        }
    }

    ///
    /// Check inclusion
    ///
    /// - return true if other is included in self.
    pub fn includes(&self, other: &LoopRange) -> bool {
        match (&self, other) {
            (LoopRange(i1, None), LoopRange(i2, _)) => i1 <= i2,
            (LoopRange(i1, Some(j1)), LoopRange(i2, Some(j2))) => i1 <= i2 && j2 <= j1,
            _ => false,
        }
    }

    ///
    /// Add two ranges
    ///
    /// The result is the union of both ranges.
    ///
    /// This is used to rewrite `(concat (loop L a b) (loop L c d))`
    /// to `(loop L (add [a, b], [c, d]))`.
    ///
    /// # Panics
    ///
    /// If an arithmetic overflow occurs, that is, the union of the two ranges
    /// cannot be represented using 32bit unsigned integers, this method will panic.
    ///
    pub fn add(&self, other: &LoopRange) -> LoopRange {
        let i = add32(self.start(), other.start());
        if self.is_infinite() || other.is_infinite() {
            LoopRange::infinite(i)
        } else {
            let j = add32(self.end(), other.end());
            LoopRange::finite(i, j)
        }
    }

    ///
    /// Add a point interval
    ///
    /// Add the point interval [x, x] to self.
    ///
    /// # Panics
    ///
    /// If there's an arithmetic overflow. See [add][Self::add].
    pub fn add_point(&self, x: u32) -> LoopRange {
        self.add(&Self::point(x))
    }

    ///
    /// Multiply by a constant k
    ///
    /// - If the current range is a finite interval [i, j], return [k * i, k * j]
    /// - If the current range is an infinite interval [i, +infinity] and
    ///   k is not zero, return [k * i, +infinity]
    /// - If k is zero, return [0, 0] even if the current range is infinite
    ///
    /// This can be used to rewrite
    ///
    ///   `(loop L i j)^k` = `(loop L k * i k * j)`
    ///
    /// # Panics
    ///
    /// If there's an arithmetic overflow in k * i or k * j.
    ///
    pub fn scale(&self, k: u32) -> LoopRange {
        if k == 0 {
            LoopRange::point(0)
        } else if self.is_infinite() {
            let i = mul32(self.start(), k);
            LoopRange::infinite(i)
        } else {
            let i = mul32(self.start(), k);
            let j = mul32(self.end(), k);
            LoopRange::finite(i, j)
        }
    }

    ///
    /// Multiply two ranges
    ///
    /// The product of the ranges [a, b] and [c, d] (where b or d may be +infinity)
    /// is the range [a * c, b * d]. The following rules handle multiplication with
    /// infinity:
    /// - 0 * infinity = infinity * 0 = 0
    /// - k * infinity = infinity * k = infinity if k is finite and non-zero
    /// - infinity * infinity = infinity
    ///
    /// **Note:**
    ///
    /// The actual product of [a, b] and [c, d] is the set of integers
    /// P = { x * y | a <= x <= b and c <= y <= d }.
    ///
    /// The interval [a * c, b * d] is an over approximation of P,
    /// since P may not be an interval.
    ///
    /// For example: if [a, b] = [0, 1] and [c, d] = [3, 4] then
    /// P is { 0, 3, 4 } but [0, 1] * [3, 4] is [0, 4].
    ///
    /// Method [right_mul_is_exact][Self::right_mul_is_exact] can be used to check
    /// whether the product is exact.
    ///
    /// # Panics
    ///
    /// If there's an arithmetic overflow in the product computation,
    /// that is, the result cannot be stored using u32 integers, this
    /// method will panic.
    ///
    pub fn mul(&self, other: &LoopRange) -> LoopRange {
        if self.is_zero() || other.is_zero() {
            LoopRange::point(0)
        } else if self.is_infinite() || other.is_infinite() {
            let i = mul32(self.start(), other.start());
            LoopRange::infinite(i)
        } else {
            let i = mul32(self.start(), other.start());
            let j = mul32(self.end(), other.end());
            LoopRange::finite(i, j)
        }
    }

    ///
    /// Check whether the product of two ranges is an interval.
    ///
    /// Given a range r = [a, b] and s = [c, d], then
    ///
    ///    `r.right_mul_is_exact(s)`
    ///
    /// returns true if the Union(k * [a, b]) for k in s is equal [a, b] * [c, d].
    ///
    /// If it is, we can rewrite `(loop (loop L a b) c d)` to `(loop L a * c b * d)`.
    ///
    /// **Note**: the product of two ranges is commutative but this method
    /// is not. For example:
    /// 1) Union(k * [0, +infinity], k in [2, 2]) = 2 * [0, +infinity] = [0, +infinity]
    ///    so
    ///
    ///      `(loop (loop L 0 +infinity) 2 2)` = (L*)^2 = L*
    ///
    /// 2) Union(k * [2, 2], k in [0, +infinity]) = { 2 * k | k in [0, +infinity] }
    ///    so
    ///
    ///      `(loop (loop L 2 2) 0 +infinity)` = (L^2)*  (not the same as L*)
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::loop_ranges::*;
    ///
    /// let r = LoopRange::point(2); // range [2, 2]
    /// let s = LoopRange::star();   // range [0, +infinity]
    ///
    /// assert!(s.right_mul_is_exact(&r));  // [0, +infinity] * [2, 2] is [0, +infinity] (exact)
    /// assert!(!r.right_mul_is_exact(&s)); // [2, 2] * [0, +infinity] is not an interval
    /// ```
    pub fn right_mul_is_exact(&self, other: &LoopRange) -> bool {
        //
        // Explanation:
        // let self = [a, b] and other = [c, d].
        // let K = { x * y | a <= x <= b and c <= y <= d}
        // then K = Union( [y * a, y * b] for y=c to d).
        //
        // IF c == d then K is an interval since then K=[c*a, c*b].
        //
        // If b == +infinity then there are two cases:
        // 1) c == 0, then K = is [0, 0] \union [a, +infinity]
        //    K is an interval if a <= 1
        // 2) c > 0 then K is the interval [c * a, +infinity]
        //
        // Otherwise, K is an interval if there's no gap between
        // subsequent intervals [y*a, y*b] and [(y+1)*a, (y+1)*b].
        // There's a gap iff (y+1)*a - y*b > 1, which is equivalent
        //   to y * (b - a) + 1 < a.
        // So no gap for y is y * (b - a) + 1 >= a.
        // This condition holds for all y in [c, d] iff it holds when y = c.
        //
        other.is_point()
            || if self.is_infinite() {
                other.start() > 0 || self.start() <= 1
            } else {
                mul32(other.start(), self.size()) + 1 >= self.start()
            }
    }

    ///
    /// Shift by one.
    ///
    /// If self = [a, b], return [dec(a), dec(b)] where dec(x) *decrements* x by 1:
    /// - dec(0) = 0
    /// - dec(+infinity) = +infinity
    /// - dec(x) = x-1 otherwise
    ///
    pub fn shift(&self) -> LoopRange {
        match self {
            LoopRange(0, None) => LoopRange::infinite(0),
            LoopRange(0, Some(0)) => LoopRange::point(0),
            LoopRange(0, Some(j)) => LoopRange::finite(0, *j - 1),
            LoopRange(i, None) => LoopRange::infinite(*i - 1),
            LoopRange(i, Some(j)) => LoopRange::finite(*i - 1, *j - 1),
        }
    }
}

#[cfg(test)]
mod test {
    use super::LoopRange;

    fn make_examples() -> Vec<LoopRange> {
        vec![
            LoopRange::finite(2, 3),
            LoopRange::finite(4, 9),
            LoopRange::finite(1, 3),
            LoopRange::infinite(3),
            LoopRange::infinite(20),
            LoopRange::point(0),
            LoopRange::point(2),
            LoopRange::point(5),
            LoopRange::opt(),
            LoopRange::star(),
            LoopRange::plus(),
        ]
    }

    #[test]
    fn basic() {
        println!("Test examples");
        for rng in make_examples() {
            println!(
                "range {}: finite: {}, infinite: {}, point: {}",
                rng,
                rng.is_finite(),
                rng.is_infinite(),
                rng.is_point()
            );
        }
        println!()
    }

    #[test]
    fn test_shift() {
        println!("Shift tests");
        for rng in make_examples() {
            println!("shift({}) = {}", rng, rng.shift());
        }
        println!()
    }

    #[test]
    fn test_add() {
        println!("Add tests");
        let v = make_examples();
        for r in &v {
            for s in &v {
                println!("add({}, {}) = {}", r, s, r.add(s))
            }
        }
        println!()
    }

    #[test]
    fn test_scale() {
        println!("Scaling tests");
        for r in make_examples() {
            for k in 0..5 {
                let s = r.scale(k);
                println!("scale({}, {}) = {}", r, k, &s);
                match k {
                    0 => assert!(s.is_zero()),
                    1 => assert_eq!(s, r),
                    _ => assert_eq!(s.is_finite(), r.is_finite()),
                }
            }
        }
        println!();
    }

    #[test]
    fn test_mul() {
        println!("Product tests");
        let v = make_examples();
        for r in &v {
            for s in &v {
                let product = r.mul(s);
                let exact = r.right_mul_is_exact(s);
                println!("mul({}, {}) = {} (exact: {})", r, s, product, exact);

                if r.is_zero() || s.is_zero() {
                    assert!(product.is_zero());
                }
                if product.is_point() {
                    assert!(exact);
                }
            }
        }
        println!()
    }
}

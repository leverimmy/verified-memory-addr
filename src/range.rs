use core::{fmt, ops::Range};

use crate::{MemoryAddr, PhysAddr, VirtAddr};

/// A range of a given memory address type `A`.
///
/// The range is inclusive on the start and exclusive on the end. A range is
/// considered **empty** iff `start == end`, and **invalid** iff `start > end`.
/// An invalid range should not be created and cannot be obtained without unsafe
/// operations, calling methods on an invalid range will cause unexpected
/// consequences.
///
/// # Example
///
/// ```
/// use memory_addr::AddrRange;
///
/// let range = AddrRange::<usize>::new(0x1000, 0x2000);
/// assert_eq!(range.start, 0x1000);
/// assert_eq!(range.end, 0x2000);
/// ```
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct AddrRange<A: MemoryAddr> {
    /// The lower bound of the range (inclusive).
    pub start: A,
    /// The upper bound of the range (exclusive).
    pub end: A,
}

/// Methods for [`AddrRange`].
impl<A> AddrRange<A>
where
    A: MemoryAddr,
{
    /// Creates a new address range from the start and end addresses.
    ///
    /// # Panics
    ///
    /// Panics if `start > end`.
    ///
    /// # Example
    ///
    /// ```
    /// use memory_addr::AddrRange;
    ///
    /// let range = AddrRange::new(0x1000usize, 0x2000);
    /// assert_eq!(range.start, 0x1000);
    /// assert_eq!(range.end, 0x2000);
    /// ```
    ///
    /// And this will panic:
    ///
    /// ```should_panic
    /// # use memory_addr::AddrRange;
    /// let _ = AddrRange::new(0x2000usize, 0x1000);
    /// ```
    #[inline]
    pub fn new(start: A, end: A) -> Self {
        assert!(
            start <= end,
            "invalid `AddrRange`: {}..{}",
            start.into(),
            end.into()
        );
        Self { start, end }
    }

    /// Creates a new address range from the given range.
    ///
    /// Returns `None` if `start > end`.
    ///
    /// # Example
    ///
    /// ```
    /// use memory_addr::AddrRange;
    ///
    /// let range = AddrRange::try_new(0x1000usize, 0x2000).unwrap();
    /// assert_eq!(range.start, 0x1000);
    /// assert_eq!(range.end, 0x2000);
    /// assert!(AddrRange::try_new(0x2000usize, 0x1000).is_none());
    /// ```
    #[inline]
    pub fn try_new(start: A, end: A) -> Option<Self> {
        if start <= end {
            Some(Self { start, end })
        } else {
            None
        }
    }

    /// Creates a new address range from the given range without checking the
    /// validity.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `start <= end`, otherwise the range will be
    /// invalid and unexpected consequences will occur.
    ///
    /// # Example
    ///
    /// ```
    /// use memory_addr::AddrRange;
    ///
    /// let range = unsafe { AddrRange::new_unchecked(0x1000usize, 0x2000) };
    /// assert_eq!(range.start, 0x1000);
    /// assert_eq!(range.end, 0x2000);
    /// ```
    #[inline]
    pub const unsafe fn new_unchecked(start: A, end: A) -> Self {
        Self { start, end }
    }

    /// Creates a new address range from the start address and the size.
    ///
    /// # Panics
    ///
    /// Panics if `size` is too large and causes overflow during evaluating the
    /// end address.
    ///
    /// # Example
    ///
    /// ```
    /// use memory_addr::AddrRange;
    ///
    /// let range = AddrRange::from_start_size(0x1000usize, 0x1000);
    /// assert_eq!(range.start, 0x1000);
    /// assert_eq!(range.end, 0x2000);
    /// ```
    ///
    /// And this will panic:
    ///
    /// ```should_panic
    /// # use memory_addr::AddrRange;
    /// let _ = AddrRange::from_start_size(0x1000usize, usize::MAX);
    /// ```
    #[inline]
    pub fn from_start_size(start: A, size: usize) -> Self {
        if let Some(end) = start.checked_add(size) {
            Self { start, end }
        } else {
            panic!(
                "size too large for `AddrRange`: {} + {}",
                start.into(),
                size
            );
        }
    }

    /// Creates a new address range from the start address and the size.
    ///
    /// Returns `None` if `size` is too large and causes overflow during
    /// evaluating the end address.
    ///
    /// # Example
    ///
    /// ```
    /// use memory_addr::AddrRange;
    ///
    /// let range = AddrRange::try_from_start_size(0x1000usize, 0x1000).unwrap();
    /// assert_eq!(range.start, 0x1000);
    /// assert_eq!(range.end, 0x2000);
    /// assert!(AddrRange::try_from_start_size(0x1000usize, usize::MAX).is_none());
    /// ```
    #[inline]
    pub fn try_from_start_size(start: A, size: usize) -> Option<Self> {
        start.checked_add(size).map(|end| Self { start, end })
    }

    /// Creates a new address range from the start address and the size without
    /// checking the validity.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `size` is not too large and won't cause
    /// overflow during evaluating the end address. Failing to do so will
    /// create an invalid range and cause unexpected consequences.
    ///
    /// # Example
    ///
    /// ```
    /// use memory_addr::AddrRange;
    ///
    /// let range = unsafe { AddrRange::from_start_size_unchecked(0x1000usize, 0x1000) };
    /// assert_eq!(range.start, 0x1000);
    /// assert_eq!(range.end, 0x2000);
    /// ```
    #[inline]
    pub unsafe fn from_start_size_unchecked(start: A, size: usize) -> Self {
        Self {
            start,
            end: start.wrapping_add(size),
        }
    }

    /// Returns `true` if the range is empty.
    ///
    /// It's also guaranteed that `false` will be returned if the range is
    /// invalid (i.e., `start > end`).
    ///
    /// # Example
    ///
    /// ```
    /// use memory_addr::AddrRange;
    ///
    /// assert!(AddrRange::new(0x1000usize, 0x1000).is_empty());
    /// assert!(!AddrRange::new(0x1000usize, 0x2000).is_empty());
    /// ```
    #[inline]
    pub fn is_empty(self) -> bool {
        self.start >= self.end
    }

    /// Returns the size of the range.
    ///
    /// # Example
    ///
    /// ```
    /// use memory_addr::AddrRange;
    ///
    /// assert_eq!(AddrRange::new(0x1000usize, 0x1000).size(), 0);
    /// assert_eq!(AddrRange::new(0x1000usize, 0x2000).size(), 0x1000);
    /// ```
    #[inline]
    pub fn size(self) -> usize {
        self.end.wrapping_sub_addr(self.start)
    }

    /// Checks if the range contains the given address.
    ///
    /// # Example
    ///
    /// ```
    /// use memory_addr::AddrRange;
    ///
    /// let range = AddrRange::new(0x1000usize, 0x2000);
    /// assert!(!range.contains(0x0fff));
    /// assert!(range.contains(0x1000));
    /// assert!(range.contains(0x1fff));
    /// assert!(!range.contains(0x2000));
    /// ```
    #[inline]
    pub fn contains(self, addr: A) -> bool {
        self.start <= addr && addr < self.end
    }

    /// Checks if the range contains the given address range.
    ///
    /// # Example
    ///
    /// ```
    /// use memory_addr::{addr_range, AddrRange};
    ///
    /// let range = AddrRange::new(0x1000usize, 0x2000);
    /// assert!(!range.contains_range(addr_range!(0x0usize..0xfff)));
    /// assert!(!range.contains_range(addr_range!(0x0fffusize..0x1fff)));
    /// assert!(range.contains_range(addr_range!(0x1001usize..0x1fff)));
    /// assert!(range.contains_range(addr_range!(0x1000usize..0x2000)));
    /// assert!(!range.contains_range(addr_range!(0x1001usize..0x2001)));
    /// assert!(!range.contains_range(addr_range!(0x2001usize..0x3001)));
    /// ```
    #[inline]
    pub fn contains_range(self, other: Self) -> bool {
        self.start <= other.start && other.end <= self.end
    }

    /// Checks if the range is contained in the given address range.
    ///
    /// # Example
    ///
    /// ```
    /// use memory_addr::{addr_range, AddrRange};
    ///
    /// let range = AddrRange::new(0x1000usize, 0x2000);
    /// assert!(!range.contained_in(addr_range!(0xfffusize..0x1fff)));
    /// assert!(!range.contained_in(addr_range!(0x1001usize..0x2001)));
    /// assert!(range.contained_in(addr_range!(0xfffusize..0x2001)));
    /// assert!(range.contained_in(addr_range!(0x1000usize..0x2000)));
    /// ```
    #[inline]
    pub fn contained_in(self, other: Self) -> bool {
        other.contains_range(self)
    }

    /// Checks if the range overlaps with the given address range.
    ///
    /// # Example
    ///
    /// ```
    /// use memory_addr::{addr_range, AddrRange};
    ///
    /// let range = AddrRange::new(0x1000usize, 0x2000usize);
    /// assert!(!range.overlaps(addr_range!(0xfffusize..0xfff)));
    /// assert!(!range.overlaps(addr_range!(0x2000usize..0x2000)));
    /// assert!(!range.overlaps(addr_range!(0xfffusize..0x1000)));
    /// assert!(range.overlaps(addr_range!(0xfffusize..0x1001)));
    /// assert!(range.overlaps(addr_range!(0x1fffusize..0x2001)));
    /// assert!(range.overlaps(addr_range!(0xfffusize..0x2001)));
    /// ```
    #[inline]
    pub fn overlaps(self, other: Self) -> bool {
        self.start < other.end && other.start < self.end
    }
}

/// Conversion from [`Range`] to [`AddrRange`], provided that the type of the
/// endpoints can be converted to the address type `A`.
impl<A, T> TryFrom<Range<T>> for AddrRange<A>
where
    A: MemoryAddr + From<T>,
{
    type Error = ();

    #[inline]
    fn try_from(range: Range<T>) -> Result<Self, Self::Error> {
        Self::try_new(range.start.into(), range.end.into()).ok_or(())
    }
}

/// Implementations of [`Default`] for [`AddrRange`].
///
/// The default value is an empty range `Range { start: 0, end: 0 }`.
impl<A> Default for AddrRange<A>
where
    A: MemoryAddr,
{
    #[inline]
    fn default() -> Self {
        Self {
            start: 0.into(),
            end: 0.into(),
        }
    }
}

/// Implementations of [`Debug`](fmt::Debug) for [`AddrRange`].
impl<A> fmt::Debug for AddrRange<A>
where
    A: MemoryAddr + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}..{:?}", self.start, self.end)
    }
}

/// Implementations of [`LowerHex`](fmt::LowerHex) for [`AddrRange`].
impl<A> fmt::LowerHex for AddrRange<A>
where
    A: MemoryAddr + fmt::LowerHex,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:x}..{:x}", self.start, self.end)
    }
}

/// Implementations of [`UpperHex`](fmt::UpperHex) for [`AddrRange`].
impl<A> fmt::UpperHex for AddrRange<A>
where
    A: MemoryAddr + fmt::UpperHex,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:X}..{:X}", self.start, self.end)
    }
}

/// A range of virtual addresses [`VirtAddr`].
pub type VirtAddrRange = AddrRange<VirtAddr>;
/// A range of physical addresses [`PhysAddr`].
pub type PhysAddrRange = AddrRange<PhysAddr>;

/// Converts the given range expression into [`AddrRange`]. Panics if the range
/// is invalid.
///
/// The concrete address type is inferred from the context.
///
/// # Example
///
/// ```
/// use memory_addr::{addr_range, AddrRange};
///
/// let range: AddrRange<usize> = addr_range!(0x1000usize..0x2000);
/// assert_eq!(range.start, 0x1000usize);
/// assert_eq!(range.end, 0x2000usize);
/// ```
///
/// And this will panic:
///
/// ```should_panic
/// # use memory_addr::{addr_range, AddrRange};
/// let _: AddrRange<usize> = addr_range!(0x2000usize..0x1000);
/// ```
#[macro_export]
macro_rules! addr_range {
    ($range:expr) => {
        $crate::AddrRange::try_from($range).expect("invalid address range in `addr_range!`")
    };
}

/// Converts the given range expression into [`VirtAddrRange`]. Panics if the
/// range is invalid.
///
/// # Example
///
/// ```
/// use memory_addr::va_range;
///
/// let range = va_range!(0x1000..0x2000);
/// assert_eq!(range.start, 0x1000.into());
/// assert_eq!(range.end, 0x2000.into());
/// ```
///
/// And this will panic:
///
/// ```should_panic
/// # use memory_addr::va_range;
/// let _ = va_range!(0x2000..0x1000);
/// ```
#[macro_export]
macro_rules! va_range {
    ($range:expr) => {
        $crate::VirtAddrRange::try_from($range).expect("invalid address range in `va_range!`")
    };
}

/// Converts the given range expression into [`PhysAddrRange`]. Panics if the
/// range is invalid.
///
/// # Example
///
/// ```
/// use memory_addr::pa_range;
///
/// let range = pa_range!(0x1000..0x2000);
/// assert_eq!(range.start, 0x1000.into());
/// assert_eq!(range.end, 0x2000.into());
/// ```
///
/// And this will panic:
///
/// ```should_panic
/// # use memory_addr::pa_range;
/// let _ = pa_range!(0x2000..0x1000);
/// ```
#[macro_export]
macro_rules! pa_range {
    ($range:expr) => {
        $crate::PhysAddrRange::try_from($range).expect("invalid address range in `pa_range!`")
    };
}

#[cfg(test)]
mod test {
    use crate::{va, va_range, VirtAddrRange};

    #[test]
    fn test_range_format() {
        let range = va_range!(0xfec000..0xfff000usize);

        assert_eq!(format!("{:?}", range), "VA:0xfec000..VA:0xfff000");
        assert_eq!(format!("{:x}", range), "VA:0xfec000..VA:0xfff000");
        assert_eq!(format!("{:X}", range), "VA:0xFEC000..VA:0xFFF000");
    }

    #[test]
    fn test_range() {
        let start = va!(0x1000);
        let end = va!(0x2000);
        let range = va_range!(start..end);

        println!("range: {:?}", range);

        assert!((0x1000..0x1000).is_empty());
        assert!((0x1000..0xfff).is_empty());
        assert!(!range.is_empty());

        assert_eq!(range.start, start);
        assert_eq!(range.end, end);
        assert_eq!(range.size(), 0x1000);

        assert!(range.contains(va!(0x1000)));
        assert!(range.contains(va!(0x1080)));
        assert!(!range.contains(va!(0x2000)));

        assert!(!range.contains_range(addr_range!(0xfff..0x1fff)));
        assert!(!range.contains_range(addr_range!(0xfff..0x2000)));
        assert!(!range.contains_range(va_range!(0xfff..0x2001))); // test both `va_range!` and `addr_range!`
        assert!(range.contains_range(va_range!(0x1000..0x1fff)));
        assert!(range.contains_range(addr_range!(0x1000..0x2000)));
        assert!(!range.contains_range(addr_range!(0x1000..0x2001)));
        assert!(range.contains_range(va_range!(0x1001..0x1fff)));
        assert!(range.contains_range(va_range!(0x1001..0x2000)));
        assert!(!range.contains_range(va_range!(0x1001..0x2001)));
        assert!(!range.contains_range(VirtAddrRange::from_start_size(0xfff.into(), 0x1)));
        assert!(!range.contains_range(VirtAddrRange::from_start_size(0x2000.into(), 0x1)));

        assert!(range.contained_in(addr_range!(0xfff..0x2000)));
        assert!(range.contained_in(addr_range!(0x1000..0x2000)));
        assert!(range.contained_in(va_range!(0x1000..0x2001)));

        assert!(!range.overlaps(addr_range!(0x800..0x1000)));
        assert!(range.overlaps(addr_range!(0x800..0x1001)));
        assert!(range.overlaps(addr_range!(0x1800..0x2000)));
        assert!(range.overlaps(va_range!(0x1800..0x2001)));
        assert!(!range.overlaps(va_range!(0x2000..0x2800)));
        assert!(range.overlaps(va_range!(0xfff..0x2001)));

        let default_range: VirtAddrRange = Default::default();
        assert!(default_range.is_empty());
        assert_eq!(default_range.size(), 0);
        assert_eq!(default_range.start, va!(0));
        assert_eq!(default_range.end, va!(0));
    }
}

#[cfg(kani)]
mod range_proofs {
    use crate::AddrRange;

    // For simplicity in these proofs, we'll use `usize` as the concrete type `A`
    // for `AddrRange<A>`. `usize` satisfies the `MemoryAddr` trait bounds
    // (Copy, From<usize>, Into<usize>, Ord) and has the necessary arithmetic methods.

    #[kani::proof]
    fn proof_new_valid_range() {
        let start: usize = kani::any();
        let end: usize = kani::any();
        kani::assume(start <= end); // Precondition for a valid range

        let range = AddrRange::new(start, end);
        assert_eq!(range.start, start, "Range start not initialized correctly.");
        assert_eq!(range.end, end, "Range end not initialized correctly.");
    }

    #[kani::proof]
    #[kani::should_panic]
    fn proof_new_panic_on_invalid_range() {
        let start: usize = kani::any();
        let end: usize = kani::any();
        kani::assume(start > end); // Condition to trigger panic

        let _ = AddrRange::new(start, end);
    }

    #[kani::proof]
    fn proof_try_new_behavior() {
        let start: usize = kani::any();
        let end: usize = kani::any();

        let opt_range = AddrRange::try_new(start, end);

        if start <= end {
            kani::assert(opt_range.is_some(), "`try_new` should return Some for valid start <= end.");
            let range = opt_range.unwrap();
            assert_eq!(range.start, start);
            assert_eq!(range.end, end);
        } else {
            kani::assert(opt_range.is_none(), "`try_new` should return None for invalid start > end.");
        }
    }

    #[kani::proof]
    fn proof_from_start_size_valid() {
        let start: usize = kani::any();
        let size: usize = kani::any();

        // Precondition: start + size does not overflow
        if let Some(expected_end) = start.checked_add(size) {
            let range = AddrRange::from_start_size(start, size);
            assert_eq!(range.start, start, "from_start_size: start incorrect.");
            assert_eq!(range.end, expected_end, "from_start_size: end incorrect.");
            // For A=usize and size: usize, if checked_add succeeds, end >= start.
            kani::assert(range.start <= range.end, "from_start_size: valid range invariant failed.");
        }
        // The else case (overflow) is covered by the panic test.
    }

    #[kani::proof]
    #[kani::should_panic]
    fn proof_from_start_size_panic_on_overflow() {
        let start: usize = kani::any();
        let size: usize = kani::any();

        // Condition: start + size overflows
        kani::assume(start.checked_add(size).is_none());

        let _ = AddrRange::from_start_size(start, size);
    }

    #[kani::proof]
    fn proof_try_from_start_size_behavior() {
        let start: usize = kani::any();
        let size: usize = kani::any();

        let opt_range = AddrRange::try_from_start_size(start, size);

        if let Some(expected_end) = start.checked_add(size) {
            kani::assert(opt_range.is_some(), "`try_from_start_size` should be Some when no overflow.");
            let range = opt_range.unwrap();
            assert_eq!(range.start, start);
            assert_eq!(range.end, expected_end);
        } else {
            kani::assert(opt_range.is_none(), "`try_from_start_size` should be None on overflow.");
        }
    }

    #[kani::proof]
    fn proof_is_empty_definition() {
        let start: usize = kani::any();
        let end: usize = kani::any();

        // `is_empty` can be called on any range, including those from `new_unchecked`.
        let range = unsafe { AddrRange::new_unchecked(start, end) };
        assert_eq!(range.is_empty(), start >= end, "is_empty behavior mismatch with definition.");
    }

    #[kani::proof]
    fn proof_size_method() {
        let start: usize = kani::any();
        let end: usize = kani::any();

        // Test with a valid range (start <= end)
        kani::assume(start <= end);
        let valid_range = AddrRange::new(start, end); // Constructor ensures start <= end
        assert_eq!(valid_range.size(), end.wrapping_sub(start), "size() for valid range.");
        // For usize and start <= end, wrapping_sub is equivalent to standard subtraction.
        assert_eq!(valid_range.size(), end - start, "size() for valid range (direct subtraction).");

        // Test with an invalid range (start > end) created via unsafe
        // Use different symbolic variables to ensure Kani explores this path independently.
        let inv_start: usize = kani::any();
        let inv_end: usize = kani::any();
        kani::assume(inv_start > inv_end);
        let invalid_range = unsafe { AddrRange::new_unchecked(inv_start, inv_end) };
        assert_eq!(invalid_range.size(), inv_end.wrapping_sub(inv_start), "size() for invalid range (start > end).");
    }

    #[kani::proof]
    fn proof_contains_method() {
        let r_start: usize = kani::any();
        let r_end: usize = kani::any();
        let addr_to_check: usize = kani::any();

        // Test with a valid range
        kani::assume(r_start <= r_end);
        let valid_range = AddrRange::new(r_start, r_end);
        let expected_for_valid = r_start <= addr_to_check && addr_to_check < r_end;
        assert_eq!(valid_range.contains(addr_to_check), expected_for_valid, "contains() for valid range.");

        // Test with an invalid range (start > end)
        let inv_start: usize = kani::any();
        let inv_end: usize = kani::any();
        kani::assume(inv_start > inv_end);
        let invalid_range = unsafe { AddrRange::new_unchecked(inv_start, inv_end) };
        // For an invalid range (e.g., 5..2), `inv_start <= addr && addr < inv_end` is always false.
        kani::assert(!invalid_range.contains(addr_to_check), "contains() for invalid range should always be false.");
    }

    #[kani::proof]
    fn proof_overlaps_method() {
        let s1: usize = kani::any();
        let e1: usize = kani::any();
        let s2: usize = kani::any();
        let e2: usize = kani::any();

        // `overlaps` can be called on any ranges, including those from `new_unchecked`.
        let r1 = unsafe { AddrRange::new_unchecked(s1, e1) };
        let r2 = unsafe { AddrRange::new_unchecked(s2, e2) };

        let expected_overlap_result = s1 < e2 && s2 < e1;
        assert_eq!(r1.overlaps(r2), expected_overlap_result, "overlaps() behavior mismatch with definition.");
        // Verify symmetry
        assert_eq!(r1.overlaps(r2), r2.overlaps(r1), "overlaps() should be symmetric.");

        // Example: Touching but not overlapping valid ranges (e.g., 0..10 and 10..20)
        let touch_s1: usize = 0; let touch_e1: usize = 10;
        let touch_s2: usize = 10; let touch_e2: usize = 20;
        let r_touch1 = AddrRange::new(touch_s1, touch_e1);
        let r_touch2 = AddrRange::new(touch_s2, touch_e2);
        kani::assert(!r_touch1.overlaps(r_touch2), "Touching ranges (0..10, 10..20) should not overlap by this definition.");
    }

    #[kani::proof]
    fn proof_contains_range_method() {
        let s1: usize = kani::any();
        let e1: usize = kani::any();
        let s2: usize = kani::any();
        let e2: usize = kani::any();

        let r1 = unsafe { AddrRange::new_unchecked(s1, e1) };
        let r2 = unsafe { AddrRange::new_unchecked(s2, e2) };

        let expected_contains_range_result = s1 <= s2 && e2 <= e1;
        assert_eq!(r1.contains_range(r2), expected_contains_range_result, "contains_range() behavior mismatch with definition.");

        // Test `contained_in` implicitly via its definition
        assert_eq!(r2.contained_in(r1), r1.contains_range(r2), "contained_in() should be equivalent to other.contains_range(self).");
    }
    
    #[kani::proof]
    fn proof_default_impl() {
        let default_range: AddrRange<usize> = Default::default();
        assert_eq!(default_range.start, 0, "Default start should be 0.");
        assert_eq!(default_range.end, 0, "Default end should be 0.");
        kani::assert(default_range.is_empty(), "Default range should be empty.");
    }

    // --- Unsafe constructor proofs ---
    #[kani::proof]
    fn proof_new_unchecked_when_contract_met() {
        let start: usize = kani::any();
        let end: usize = kani::any();
        kani::assume(start <= end); // Caller meets the safety contract

        let range = unsafe { AddrRange::new_unchecked(start, end) };
        assert_eq!(range.start, start);
        assert_eq!(range.end, end);
    }

    #[kani::proof]
    fn proof_new_unchecked_when_contract_violated() {
        let start: usize = kani::any();
        let end: usize = kani::any();
        kani::assume(start > end); // Caller violates safety contract (creates an "invalid" range)

        let range = unsafe { AddrRange::new_unchecked(start, end) };
        assert_eq!(range.start, start, "start field for unchecked invalid range.");
        assert_eq!(range.end, end, "end field for unchecked invalid range.");
        kani::assert(range.is_empty(), "Invalid range (start > end) should be considered 'empty' by is_empty().");
    }

    #[kani::proof]
    fn proof_from_start_size_unchecked_behavior() {
        let start: usize = kani::any();
        let size: usize = kani::any();
        // Assume that it won't overflow
        kani::assume(size <= usize::MAX - start);

        // Behavior is defined by `start.wrapping_add(size)` for `end`.
        let expected_end = start.wrapping_add(size);
        let range = unsafe { AddrRange::from_start_size_unchecked(start, size) };

        assert_eq!(range.start, start, "from_start_size_unchecked: start incorrect.");
        assert_eq!(range.end, expected_end, "from_start_size_unchecked: end incorrect (should match wrapping_add).");

        // Check properties if this created an "invalid" range (end wrapped below start)
        if expected_end < start {
            kani::assert(range.is_empty(), "Range from from_start_size_unchecked where end wrapped below start should be 'empty' by is_empty().");
            assert_ne!(range.size(), expected_end.wrapping_sub(start), "Size calculation for wrapped range might need care in assertion if expected_end is very small, but the direct equality should hold.");
            assert_eq!(range.size(), expected_end.wrapping_sub(start), "Size calculation for wrapped range.");
        }
    }

    // --- Macro proofs ---
    // Kani verifies the code *after* macro expansion.
    #[kani::proof]
    #[kani::should_panic]
    fn proof_addr_range_macro_panics_on_invalid() {
        let start: usize = kani::any();
        let end: usize = kani::any();
        kani::assume(start > end);

        // Ensure the macro is in scope. If `addr_range` is exported from crate root:
        let _range: AddrRange<usize> = crate::addr_range!(start..end);
    }

    #[kani::proof]
    fn proof_addr_range_macro_valid_input() {
        let start: usize = kani::any();
        let end: usize = kani::any();
        kani::assume(start <= end);

        let range: AddrRange<usize> = crate::addr_range!(start..end);
        assert_eq!(range.start, start);
        assert_eq!(range.end, end);
    }
}

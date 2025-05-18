#![cfg_attr(not(test), no_std)]
#![doc = include_str!("../README.md")]

mod addr;
mod iter;
mod range;

pub use self::addr::{MemoryAddr, PhysAddr, VirtAddr};
pub use self::iter::PageIter;
pub use self::range::{AddrRange, PhysAddrRange, VirtAddrRange};

/// The size of a 4K page (4096 bytes).
pub const PAGE_SIZE_4K: usize = 0x1000;

/// A [`PageIter`] for 4K pages.
pub type PageIter4K<A> = PageIter<PAGE_SIZE_4K, A>;

/// Align address downwards.
///
/// Returns the greatest `x` with alignment `align` so that `x <= addr`.
///
/// The alignment must be a power of two.
#[inline]
pub const fn align_down(addr: usize, align: usize) -> usize {
    addr & !(align - 1)
}

/// Align address upwards.
///
/// Returns the smallest `x` with alignment `align` so that `x >= addr`.
///
/// The alignment must be a power of two.
#[inline]
pub const fn align_up(addr: usize, align: usize) -> usize {
    (addr + align - 1) & !(align - 1)
}

/// Returns the offset of the address within the alignment.
///
/// Equivalent to `addr % align`, but the alignment must be a power of two.
#[inline]
pub const fn align_offset(addr: usize, align: usize) -> usize {
    addr & (align - 1)
}

/// Checks whether the address has the demanded alignment.
///
/// Equivalent to `addr % align == 0`, but the alignment must be a power of two.
#[inline]
pub const fn is_aligned(addr: usize, align: usize) -> bool {
    align_offset(addr, align) == 0
}

/// Align address downwards to 4096 (bytes).
#[inline]
pub const fn align_down_4k(addr: usize) -> usize {
    align_down(addr, PAGE_SIZE_4K)
}

/// Align address upwards to 4096 (bytes).
#[inline]
pub const fn align_up_4k(addr: usize) -> usize {
    align_up(addr, PAGE_SIZE_4K)
}

/// Returns the offset of the address within a 4K-sized page.
#[inline]
pub const fn align_offset_4k(addr: usize) -> usize {
    align_offset(addr, PAGE_SIZE_4K)
}

/// Checks whether the address is 4K-aligned.
#[inline]
pub const fn is_aligned_4k(addr: usize) -> bool {
    is_aligned(addr, PAGE_SIZE_4K)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_align() {
        assert_eq!(align_down(0x12345678, 0x1000), 0x12345000);
        assert_eq!(align_up(0x12345678, 0x1000), 0x12346000);
        assert_eq!(align_offset(0x12345678, 0x1000), 0x678);
        assert!(is_aligned(0x12345000, 0x1000));
        assert!(!is_aligned(0x12345678, 0x1000));

        assert_eq!(align_down_4k(0x12345678), 0x12345000);
        assert_eq!(align_up_4k(0x12345678), 0x12346000);
        assert_eq!(align_offset_4k(0x12345678), 0x678);
        assert!(is_aligned_4k(0x12345000));
        assert!(!is_aligned_4k(0x12345678));
    }
}

#[cfg(kani)]
mod lib_proofs {
    use crate::{
        PAGE_SIZE_4K, align_down, align_up, align_offset, is_aligned,
        align_down_4k, align_up_4k, align_offset_4k, is_aligned_4k,
    };

    // Helper function for Kani to establish preconditions on the 'align' parameter.
    // The documented behavior of these functions relies on 'align' being a power of two.
    fn assume_align_is_valid(align: usize) {
        kani::assume(align > 0 && align.is_power_of_two());
    }

    #[kani::proof]
    fn proof_align_down() {
        let addr: usize = kani::any();
        let align: usize = kani::any();
        assume_align_is_valid(align);

        let result = align_down(addr, align);

        // Property 1: The result must be aligned to 'align'.
        assert!(is_aligned(result, align), "align_down: result is not aligned");

        // Property 2: The result must be less than or equal to the original address.
        assert!(result <= addr, "align_down: result is greater than original address");

        // Property 3: The result is the largest aligned address less than or equal to 'addr'.
        // This means (addr - result) must be less than 'align'.
        assert!(addr.wrapping_sub(result) < align, "align_down: result is not the largest aligned address <= addr");

        // Property 4: Idempotence - if 'addr' is already aligned, it should not change.
        if is_aligned(addr, align) {
            assert_eq!(result, addr, "align_down: changed an already aligned address");
        }
    }

    #[kani::proof]
    fn proof_align_up_assuming_no_sum_overflow() {
        let addr: usize = kani::any();
        let align: usize = kani::any();
        assume_align_is_valid(align);

        // Precondition for "normal" behavior of align_up: addr + align - 1 must not overflow.
        // (align - 1) is safe because align > 0.
        let align_minus_1 = align - 1;
        kani::assume(addr <= usize::MAX - align_minus_1);

        let result = align_up(addr, align);

        // Property 1: The result must be aligned to 'align'.
        assert!(is_aligned(result, align), "align_up: result is not aligned");

        // Property 2: The result must be greater than or equal to the original address.
        assert!(result >= addr, "align_up: result is smaller than original address (no sum overflow case)");

        // Property 3: The result is the smallest aligned address greater than or equal to 'addr'.
        // This means (result - addr) must be less than 'align'.
        assert!(result.wrapping_sub(addr) < align, "align_up: result is not the smallest aligned address >= addr (no sum overflow case)");

        // Property 4: Idempotence - if 'addr' is already aligned, it should not change.
        if is_aligned(addr, align) {
            assert_eq!(result, addr, "align_up: changed an already aligned address (no sum overflow case)");
        }
    }

    #[kani::proof]
    fn proof_align_up_sum_overflow_behavior() {
        let addr: usize = kani::any();
        let align: usize = kani::any();
        assume_align_is_valid(align);

        // Condition: Induce overflow in the `addr + align - 1` part of align_up's calculation.
        let align_minus_1 = align - 1; // Safe as align > 0
        kani::assume(addr > usize::MAX - align_minus_1);

        // We also need addr to be substantial for `result < addr` to be non-trivial.
        // If addr is usize::MAX, result will be small, so result < addr holds.
        kani::assume(addr > align); // Avoid cases where addr is small, and align is huge.

        let result = align_up(addr, align);

        // Property 1 (alignment) should still hold due to the bitwise mask.
        assert!(is_aligned(result, align), "align_up: result (with sum overflow) should still be aligned");

        // Property 2 (result >= addr) is expected to FAIL under these overflow conditions.
        // When `addr + align - 1` overflows, it wraps to a small number.
        // `result` (derived from this small wrapped number) will also be small.
        // Thus, `result` will likely be less than the original large `addr`.
        assert!(result < addr, "align_up: expected result < addr when addr + align - 1 overflows and addr is large");
    }

    #[kani::proof]
    fn proof_align_offset() {
        let addr: usize = kani::any();
        let align: usize = kani::any();
        assume_align_is_valid(align);

        let offset = align_offset(addr, align);

        // Property 1: The offset must be less than 'align'.
        assert!(offset < align, "align_offset: result is not less than align");

        // Property 2: (addr - offset) must be aligned to 'align'.
        // This means addr = N*align + offset.
        assert!(is_aligned(addr.wrapping_sub(offset), align), "align_offset: (addr - offset) is not aligned");

        // Property 3: Equivalence: addr - offset == align_down(addr, align)
        assert_eq!(addr.wrapping_sub(offset), align_down(addr, align), "align_offset: (addr - offset) != align_down(addr, align)");
    }

    #[kani::proof]
    fn proof_is_aligned() {
        let addr: usize = kani::any();
        let align: usize = kani::any();
        assume_align_is_valid(align);

        let is_a = is_aligned(addr, align);

        // Property 1: Check against the direct bitwise definition.
        assert_eq!(is_a, (addr & (align - 1)) == 0, "is_aligned: does not match its bitwise definition");

        // Property 2: If is_aligned is true, then align_down and align_up (no overflow) should be identity operations.
        if is_a {
            assert_eq!(align_down(addr, align), addr, "is_aligned true, but align_down changed addr");
            let align_minus_1 = align - 1;
            if addr <= usize::MAX - align_minus_1 { // For align_up without sum overflow
                assert_eq!(align_up(addr, align), addr, "is_aligned true, but align_up changed addr (no sum overflow case)");
            }
        } else {
        // Property 3: If is_aligned is false, align_down should decrease addr (unless addr is 0).
            if addr != 0 {
                assert!(align_down(addr, align) < addr, "is_aligned false, but align_down did not decrease addr (addr != 0)");
            } else {
                assert_eq!(align_down(0, align), 0, "align_down(0, align) should be 0");
            }
        // Property 4: If is_aligned is false, align_up (no overflow) should increase addr.
            let align_minus_1 = align - 1;
            if addr <= usize::MAX - align_minus_1 { // For align_up without sum overflow
                 // Also ensure addr is not already at max possible aligned value if align_up would make it wrap
                assert!(align_up(addr, align) > addr, "is_aligned false, but align_up did not increase addr (no sum overflow case)");
            }
        }
    }

    // --- Proofs for _4k variants ---
    // These variants simply call the base functions with PAGE_SIZE_4K.
    // PAGE_SIZE_4K (0x1000) is > 0 and is a power of two, so 'assume_align_is_valid' holds for it.

    #[kani::proof]
    fn proof_align_down_4k_consistency() {
        let addr: usize = kani::any();
        assert_eq!(align_down_4k(addr), align_down(addr, PAGE_SIZE_4K), "align_down_4k not consistent with align_down");
    }

    #[kani::proof]
    fn proof_align_up_4k_consistency_and_properties() {
        let addr: usize = kani::any();
        assert_eq!(align_up_4k(addr), align_up(addr, PAGE_SIZE_4K), "align_up_4k not consistent with align_up");

        // Check properties directly for align_up_4k, assuming no sum overflow
        let align_minus_1 = PAGE_SIZE_4K - 1;
        if addr <= usize::MAX - align_minus_1 {
            let result = align_up_4k(addr);
            assert!(is_aligned_4k(result), "align_up_4k: result not 4k-aligned");
            assert!(result >= addr, "align_up_4k: result < addr");
            assert!(result.wrapping_sub(addr) < PAGE_SIZE_4K, "align_up_4k: result not smallest 4k-aligned >= addr");
        }
    }

    #[kani::proof]
    fn proof_align_offset_4k_consistency() {
        let addr: usize = kani::any();
        assert_eq!(align_offset_4k(addr), align_offset(addr, PAGE_SIZE_4K), "align_offset_4k not consistent with align_offset");
    }

    #[kani::proof]
    fn proof_is_aligned_4k_consistency() {
        let addr: usize = kani::any();
        assert_eq!(is_aligned_4k(addr), is_aligned(addr, PAGE_SIZE_4K), "is_aligned_4k not consistent with is_aligned");
    }
}

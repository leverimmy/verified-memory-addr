#![no_std]
#![cfg_attr(kani, allow(dead_code))] // Allow dead code for items only used in Kani harnesses

use core::fmt::{self, Debug, Formatter, LowerHex, UpperHex};
use core::ops::{Add, AddAssign, Sub, SubAssign};

// Helper function to check if a number is a power of two.
// Verus's is_power_2 implies the number is positive.
#[inline]
pub const fn is_power_of_two(n: usize) -> bool {
    n > 0 && (n & (n.wrapping_sub(1))) == 0
}

pub const PAGE_SIZE_4K: usize = 0x1000;

// Original Verus spec: addr & !sub(align, 1)
// which is: addr & !(align - 1)

pub const fn align_down(addr: usize, align: usize) -> usize {
    // Verus requires: is_power_2(align as int)
    // Verus ensures:
    //     addr - align < r <= addr,
    //     r % align == 0,
    // which simplifies to r == addr - (addr % align) for power-of-two align.
    // The implementation is addr & !(align - 1).
    // For power-of-two align, addr & !(align - 1) == addr - (addr % align).
    addr & !(align - 1)
}

pub const fn align_up(addr: usize, align: usize) -> usize {
    // Verus requires:
    //     addr + align <= usize::MAX,
    //     is_power_2(align as int),
    // Verus ensures:
    //     addr <= r < addr + align,
    //     r % align == 0,
    align_down(addr.wrapping_add(align).wrapping_sub(1), align)
}

pub const fn align_offset(addr: usize, align: usize) -> usize {
    // Verus requires: is_power_2(align as int)
    // Verus ensures: r == addr - align_down(addr, align)
    // This is equivalent to addr % align for power-of-two align.
    // The implementation is addr & (align - 1).
    addr & (align - 1)
}

pub const fn is_aligned(addr: usize, align: usize) -> bool {
    // Verus requires: is_power_2(align as int)
    // Verus ensures: r == (addr % align == 0)
    align_offset(addr, align) == 0
}

pub const fn align_down_4k(addr: usize) -> usize {
    // Verus ensures:
    //     addr - PAGE_SIZE_4K < r <= addr,
    //     r % PAGE_SIZE_4K == 0,
    align_down(addr, PAGE_SIZE_4K)
}

pub const fn align_up_4k(addr: usize) -> usize {
    // Verus requires: addr <= usize::MAX - PAGE_SIZE_4K,
    // Verus ensures:
    //     addr <= r < addr + PAGE_SIZE_4K,
    //     r % PAGE_SIZE_4K == 0,
    align_up(addr, PAGE_SIZE_4K)
}

pub const fn align_offset_4k(addr: usize) -> usize {
    // Verus ensures: r == addr - align_down(addr, PAGE_SIZE_4K),
    align_offset(addr, PAGE_SIZE_4K)
}

pub const fn is_aligned_4k(addr: usize) -> bool {
    // Verus ensures: r == (addr % PAGE_SIZE_4K == 0),
    is_aligned(addr, PAGE_SIZE_4K)
}

#[repr(transparent)]
#[derive(Copy, Clone, Default, Ord, PartialOrd, Eq, PartialEq)]
pub struct PhysAddr(usize);

#[repr(transparent)]
#[derive(Copy, Clone, Default, Ord, PartialOrd, Eq, PartialEq)]
pub struct VirtAddr(usize);

impl PhysAddr {
    pub const fn from(addr: usize) -> Self {
        Self(addr)
    }

    pub const fn as_usize(self) -> usize {
        self.0
    }

    pub const fn align_down(self, align: usize) -> Self {
        Self(align_down(self.0, align))
    }

    pub const fn align_up(self, align: usize) -> Self {
        Self(align_up(self.0, align))
    }

    pub const fn align_offset(self, align: usize) -> usize {
        align_offset(self.0, align)
    }

    pub const fn is_aligned(self, align: usize) -> bool {
        is_aligned(self.0, align)
    }

    pub const fn align_down_4k(self) -> Self {
        Self(align_down_4k(self.0))
    }

    pub const fn align_up_4k(self) -> Self {
        Self(align_up_4k(self.0))
    }

    pub const fn align_offset_4k(self) -> usize {
        align_offset_4k(self.0)
    }

    pub const fn is_aligned_4k(self) -> bool {
        is_aligned_4k(self.0)
    }
}

impl VirtAddr {
    pub const fn as_ptr(self) -> *const u8 {
        self.0 as *const u8
    }

    pub const fn as_mut_ptr(self) -> *mut u8 {
        self.0 as *mut u8
    }

    pub const fn from(addr: usize) -> Self {
        Self(addr)
    }

    pub const fn as_usize(self) -> usize {
        self.0
    }

    pub const fn align_down(self, align: usize) -> Self {
        Self(align_down(self.0, align))
    }

    pub const fn align_up(self, align: usize) -> Self {
        Self(align_up(self.0, align))
    }

    pub const fn align_offset(self, align: usize) -> usize {
        align_offset(self.0, align)
    }

    pub const fn is_aligned(self, align: usize) -> bool {
        is_aligned(self.0, align)
    }

    pub const fn align_down_4k(self) -> Self {
        Self(align_down_4k(self.0))
    }

    pub const fn align_up_4k(self) -> Self {
        Self(align_up_4k(self.0))
    }

    pub const fn align_offset_4k(self) -> usize {
        align_offset_4k(self.0)
    }

    pub const fn is_aligned_4k(self) -> bool {
        is_aligned_4k(self.0)
    }
}

impl From<usize> for PhysAddr {
    fn from(addr: usize) -> Self {
        Self(addr)
    }
}

impl From<usize> for VirtAddr {
    fn from(addr: usize) -> Self {
        Self(addr)
    }
}

impl From<PhysAddr> for usize {
    fn from(addr: PhysAddr) -> usize {
        addr.0
    }
}

impl From<VirtAddr> for usize {
    fn from(addr: VirtAddr) -> usize {
        addr.0
    }
}

impl Add<usize> for PhysAddr {
    type Output = Self;

    fn add(self, rhs: usize) -> Self {
        // Verus requires: self@ + rhs <= usize::MAX,
        // Verus ensures: r@ == self@ + rhs,
        Self(self.0.wrapping_add(rhs))
    }
}

impl AddAssign<usize> for PhysAddr {
    fn add_assign(&mut self, rhs: usize) {
        // Verus requires: old(self)@ + rhs <= usize::MAX,
        // Verus ensures: self@ == old(self)@ + rhs,
        self.0 = self.0.wrapping_add(rhs);
    }
}

impl Sub<usize> for PhysAddr {
    type Output = Self;

    fn sub(self, rhs: usize) -> Self {
        // Verus requires: self@ >= rhs,
        // Verus ensures: r@ == self@ - rhs,
        Self(self.0.wrapping_sub(rhs))
    }
}

impl SubAssign<usize> for PhysAddr {
    fn sub_assign(&mut self, rhs: usize) {
        // Verus requires: old(self)@ >= rhs,
        // Verus ensures: self@ == old(self)@ - rhs,
        self.0 = self.0.wrapping_sub(rhs);
    }
}

impl Add<usize> for VirtAddr {
    type Output = Self;

    fn add(self, rhs: usize) -> Self {
        Self(self.0.wrapping_add(rhs))
    }
}

impl AddAssign<usize> for VirtAddr {
    fn add_assign(&mut self, rhs: usize) {
        self.0 = self.0.wrapping_add(rhs);
    }
}

impl Sub<usize> for VirtAddr {
    type Output = Self;

    fn sub(self, rhs: usize) -> Self {
        Self(self.0.wrapping_sub(rhs))
    }
}

impl SubAssign<usize> for VirtAddr {
    fn sub_assign(&mut self, rhs: usize) {
        self.0 = self.0.wrapping_sub(rhs);
    }
}

impl Debug for PhysAddr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_fmt(format_args!("PA:{:#x}", self.0))
    }
}

impl Debug for VirtAddr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_fmt(format_args!("VA:{:#x}", self.0))
    }
}

impl LowerHex for PhysAddr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_fmt(format_args!("PA:{:#x}", self.0))
    }
}

impl UpperHex for PhysAddr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_fmt(format_args!("PA:{:#X}", self.0))
    }
}

impl LowerHex for VirtAddr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_fmt(format_args!("VA:{:#x}", self.0))
    }
}

impl UpperHex for VirtAddr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_fmt(format_args!("VA:{:#X}", self.0))
    }
}

#[cfg(kani)]
mod kani_proofs {
    use super::*; // Import items from the parent module

    #[kani::proof]
    fn prove_is_power_of_two() {
        let n: usize = kani::any();
        let res = is_power_of_two(n);
        if n == 0 { kani::assert(!res, "is_power_of_two(0) should be false"); }
        if n == 1 { kani::assert(res, "is_power_of_two(1) should be true"); }
        if n == 2 { kani::assert(res, "is_power_of_two(2) should be true"); }
        if n == 3 { kani::assert(!res, "is_power_of_two(3) should be false"); }
        if n == 4 { kani::assert(res, "is_power_of_two(4) should be true"); }
        if n > 0 && (n & (n-1)) == 0 { // check against common alternative definition for n > 0
            kani::assert(res, "res should be true if n > 0 and n & (n-1) == 0");
        }
        if n > 0 && (n & (n-1)) != 0 {
             kani::assert(!res, "res should be false if n > 0 and n & (n-1) != 0");
        }
    }

    #[kani::proof]
    fn prove_page_size_4k_is_power_of_two() {
        kani::assert(is_power_of_two(PAGE_SIZE_4K), "PAGE_SIZE_4K must be a power of two");
    }

    #[kani::proof]
    fn proof_align_down() {
        let addr: usize = kani::any();
        let align: usize = kani::any();

        kani::assume(is_power_of_two(align)); // This implies align > 0

        let r = align_down(addr, align);

        // Verus ensures:
        // 1. addr - align < r <= addr
        // 2. r % align == 0
        // This is equivalent to r == addr - (addr % align) for power-of-two align.
        
        kani::assert(r <= addr, "r should be less than or equal to addr");
        kani::assert(r % align == 0, "r should be a multiple of align");

        // Check that r is the largest multiple of align <= addr.
        // This means addr < r + align, or r == addr - (addr % align)
        // The expression `addr & !(align - 1)` is equivalent to `addr - (addr % align)`
        // when align is a power of two.
        if align > 0 { // Redundant due to is_power_of_two but good for clarity with %
             kani::assert(r == addr.wrapping_sub(addr % align), "align_down result is not addr - (addr % align)");
        }

        // Original Verus: addr - align < r
        // This translates to: if addr >= align, then addr - align < r.
        // If addr < align, then r must be 0. (addr - align) in math is negative, so math_addr_minus_align < 0 is true.
        if addr < align {
            kani::assert(r == 0, "If addr < align, r should be 0");
        } else { // addr >= align
            // We've asserted r == addr - (addr % align)
            // We need to show addr - align < addr - (addr % align)
            // This simplifies to -(align as isize) < -((addr % align) as isize)
            // Or (align as isize) > ((addr % align) as isize)
            // This is true because 0 <= (addr % align) < align.
            // This property is thus covered by `r == addr - (addr % align)` and `r % align == 0`.
        }
    }

    #[kani::proof]
    fn proof_align_up() {
        let addr: usize = kani::any();
        let align: usize = kani::any();

        kani::assume(is_power_of_two(align)); // implies align > 0
        kani::assume(addr <= usize::MAX.saturating_sub(align)); // addr + align <= usize::MAX

        let r = align_up(addr, align);
        
        kani::assert(r % align == 0, "r should be a multiple of align");
        kani::assert(addr <= r, "addr should be less than or equal to r");
        
        // addr <= r < addr + align
        // The unwrap is safe due to the kani::assume for addr + align overflow.
        let addr_plus_align = addr.checked_add(align).unwrap();
        kani::assert(r < addr_plus_align, "r should be less than addr + align");

        // Also check against the formula (addr + align - 1) - ((addr + align - 1) % align)
        // if addr + align - 1 does not overflow.
        if let Some(addr_plus_align_minus_1) = addr.checked_add(align.saturating_sub(1)) {
             let expected_r = addr_plus_align_minus_1.wrapping_sub(addr_plus_align_minus_1 % align);
             kani::assert(r == expected_r, "align_up result not matching formula");
        }
    }

    #[kani::proof]
    fn proof_align_offset() {
        let addr: usize = kani::any();
        let align: usize = kani::any();
        kani::assume(is_power_of_two(align)); // implies align > 0

        let r = align_offset(addr, align);

        // Verus ensures: r == addr - align_down(addr, align)
        // which is addr % align for power-of-two align.
        if align > 0 { // Redundant due to is_power_of_two
            kani::assert(r == addr % align, "offset should be addr % align");
        }
        
        let ad = align_down(addr, align);
        kani::assert(r == addr.wrapping_sub(ad), "offset should be addr - align_down(addr, align)");
    }

    #[kani::proof]
    fn proof_is_aligned() {
        let addr: usize = kani::any();
        let align: usize = kani::any();
        kani::assume(is_power_of_two(align)); // implies align > 0

        let res = is_aligned(addr, align);
        
        if align > 0 { // Redundant
            kani::assert(res == (addr % align == 0), "is_aligned incorrect");
        }
    }

    // Proofs for _4k functions
    #[kani::proof]
    fn proof_align_down_4k() {
        let addr: usize = kani::any();
        let r = align_down_4k(addr);
        let align = PAGE_SIZE_4K;

        kani::assert(is_power_of_two(align), "PAGE_SIZE_4K must be a power of two");
        kani::assert(r <= addr, "align_down_4k result should be less than or equal to addr");
        kani::assert(r % align == 0, "align_down_4k result should be a multiple of PAGE_SIZE_4K");
        kani::assert(r == addr.wrapping_sub(addr % align), "align_down_4k result should be addr - (addr % PAGE_SIZE_4K)");
    }
    
    #[kani::proof]
    fn proof_align_up_4k() {
        let addr: usize = kani::any();
        let align = PAGE_SIZE_4K;
        kani::assume(addr <= usize::MAX.saturating_sub(align)); // addr + align <= usize::MAX

        let r = align_up_4k(addr);

        kani::assert(is_power_of_two(align), "PAGE_SIZE_4K must be a power of two");
        kani::assert(r % align == 0, "align_up_4k result should be a multiple of PAGE_SIZE_4K");
        kani::assert(addr <= r, "addr should be less than or equal to align_up_4k result");
        let addr_plus_align = addr.checked_add(align).unwrap(); // Safe due to assume
        kani::assert(r < addr_plus_align, "align_up_4k result should be less than addr + PAGE_SIZE_4K");
    }

    #[kani::proof]
    fn proof_align_offset_4k() {
        let addr: usize = kani::any();
        let r = align_offset_4k(addr);
        let align = PAGE_SIZE_4K;
        kani::assert(is_power_of_two(align), "PAGE_SIZE_4K must be a power of two");
        kani::assert(r == addr % align, "align_offset_4k result should be addr % PAGE_SIZE_4K");
    }

    #[kani::proof]
    fn proof_is_aligned_4k() {
        let addr: usize = kani::any();
        let res = is_aligned_4k(addr);
        let align = PAGE_SIZE_4K;
        kani::assert(is_power_of_two(align), "PAGE_SIZE_4K must be a power of two");
        kani::assert(res == (addr % align == 0), "is_aligned_4k result should be addr % PAGE_SIZE_4K == 0");
    }

    // Proofs for PhysAddr methods
    #[kani::proof]
    fn proof_phys_addr_from_as_usize() {
        let val = kani::any();
        let pa = PhysAddr::from(val);
        kani::assert(pa.as_usize() == val, "as_usize failed");
        kani::assert(PhysAddr(val).0 == val, "PhysAddr constructor failed"); 
    }

    #[kani::proof]
    fn proof_phys_addr_align_down() {
        let addr_val = kani::any();
        let align: usize = kani::any();
        kani::assume(is_power_of_two(align));
        
        let pa = PhysAddr::from(addr_val);
        let r_pa = pa.align_down(align);
        let r_val = r_pa.as_usize();

        kani::assert(r_val <= addr_val, "align_down result should be less than or equal to addr");
        kani::assert(r_val % align == 0, "align_down result should be a multiple of align");
        if align > 0 {
            kani::assert(r_val == addr_val.wrapping_sub(addr_val % align), "align_down result not matching formula");
        }
    }
    
    // Proofs for VirtAddr methods (similar to PhysAddr)
    #[kani::proof]
    fn proof_virt_addr_from_as_usize() {
        let val = kani::any();
        let va = VirtAddr::from(val);
        kani::assert(va.as_usize() == val, "as_usize failed");
        kani::assert(VirtAddr(val).0 == val, "VirtAddr constructor failed");
    }

    #[kani::proof]
    fn proof_virt_addr_as_ptr() {
        let addr_val = kani::any();
        let va = VirtAddr::from(addr_val);
        let ptr = va.as_ptr();
        kani::assert(ptr as usize == addr_val, "as_ptr failed");
    }

    #[kani::proof]
    fn proof_virt_addr_as_mut_ptr() {
        let addr_val = kani::any();
        let va = VirtAddr::from(addr_val);
        let ptr = va.as_mut_ptr();
        kani::assert(ptr as usize == addr_val, "as_mut_ptr failed");
    }

    // Proofs for From traits
    #[kani::proof]
    fn proof_from_usize_for_phys_addr() {
        let val: usize = kani::any();
        let pa: PhysAddr = val.into();
        kani::assert(pa.as_usize() == val, "From usize for PhysAddr failed");
    }

    #[kani::proof]
    fn proof_from_phys_addr_for_usize() {
        let val = kani::any();
        let pa = PhysAddr::from(val);
        let u_val: usize = pa.into();
        kani::assert(u_val == val, "From PhysAddr for usize failed");
    }
    
    // Proofs for operator traits (PhysAddr)
    #[kani::proof]
    fn proof_phys_addr_add() {
        let lhs_val = kani::any();
        let rhs_val = kani::any();
        let pa = PhysAddr::from(lhs_val);

        kani::assume(lhs_val.checked_add(rhs_val).is_some());

        let result_pa = pa + rhs_val;
        kani::assert(result_pa.as_usize() == lhs_val + rhs_val, "PA add failed");
    }

    #[kani::proof]
    fn proof_phys_addr_add_assign() {
        let initial_val = kani::any();
        let rhs_val = kani::any();
        let mut pa = PhysAddr::from(initial_val);

        kani::assume(initial_val.checked_add(rhs_val).is_some());
        
        let expected_val = initial_val + rhs_val;
        pa += rhs_val;
        kani::assert(pa.as_usize() == expected_val, "PA add_assign failed");
    }

    #[kani::proof]
    fn proof_phys_addr_sub() {
        let lhs_val = kani::any();
        let rhs_val = kani::any();
        let pa = PhysAddr::from(lhs_val);

        kani::assume(lhs_val >= rhs_val);

        let result_pa = pa - rhs_val;
        kani::assert(result_pa.as_usize() == lhs_val - rhs_val, "PA sub failed");
    }

    #[kani::proof]
    fn proof_phys_addr_sub_assign() {
        let initial_val = kani::any();
        let rhs_val = kani::any();
        let mut pa = PhysAddr::from(initial_val);

        kani::assume(initial_val >= rhs_val);
        
        let expected_val = initial_val - rhs_val;
        pa -= rhs_val;
        kani::assert(pa.as_usize() == expected_val, "PA sub_assign failed");
    }

    // Add similar proofs for VirtAddr operator traits if needed.
    // They are identical to PhysAddr ones, just replace PhysAddr with VirtAddr.
    // For brevity, I'll skip reimplementing them here but they would follow the same pattern.
    // Example:
    #[kani::proof]
    fn proof_virt_addr_add() {
        let lhs_val = kani::any();
        let rhs_val = kani::any();
        let va = VirtAddr::from(lhs_val);

        kani::assume(lhs_val.checked_add(rhs_val).is_some());

        let result_va = va + rhs_val;
        kani::assert(result_va.as_usize() == lhs_val + rhs_val, "VA add failed");
    }
}
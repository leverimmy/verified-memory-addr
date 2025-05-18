use crate::MemoryAddr;

/// A page-by-page iterator.
///
/// The page size is specified by the generic parameter `PAGE_SIZE`, which must
/// be a power of 2.
///
/// The address type is specified by the type parameter `A`.
///
/// # Examples
///
/// ```
/// use memory_addr::PageIter;
///
/// let mut iter = PageIter::<0x1000, usize>::new(0x1000, 0x3000).unwrap();
/// assert_eq!(iter.next(), Some(0x1000));
/// assert_eq!(iter.next(), Some(0x2000));
/// assert_eq!(iter.next(), None);
///
/// assert!(PageIter::<0x1000, usize>::new(0x1000, 0x3001).is_none());
/// ```
pub struct PageIter<const PAGE_SIZE: usize, A>
where
    A: MemoryAddr,
{
    start: A,
    end: A,
}

impl<A, const PAGE_SIZE: usize> PageIter<PAGE_SIZE, A>
where
    A: MemoryAddr,
{
    /// Creates a new [`PageIter`].
    ///
    /// Returns `None` if `PAGE_SIZE` is not a power of 2, or `start` or `end`
    /// is not page-aligned.
    pub fn new(start: A, end: A) -> Option<Self> {
        if !PAGE_SIZE.is_power_of_two()
            || !start.is_aligned(PAGE_SIZE)
            || !end.is_aligned(PAGE_SIZE)
        {
            None
        } else {
            Some(Self { start, end })
        }
    }
}

impl<A, const PAGE_SIZE: usize> Iterator for PageIter<PAGE_SIZE, A>
where
    A: MemoryAddr,
{
    type Item = A;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let ret = self.start;
            self.start = self.start.add(PAGE_SIZE);
            Some(ret)
        } else {
            None
        }
    }
}

#[cfg(kani)]
mod iter_proofs {
    use crate::{MemoryAddr, PageIter};

    // Define a constant for loop unrolling bounds if not using Kani's default
    const MAX_ITER_CHECK: usize = 5; // Arbitrary small number for bounded checks

    // --- Harnesses for PageIter::new ---

    #[kani::proof]
    fn proof_new_valid_inputs() {
        const VALID_PAGE_SIZE: usize = 0x1000; // Concrete, valid power-of-two
        let start_val: usize = kani::any();
        let end_val: usize = kani::any();

        // Ensure inputs are aligned for the "valid" case
        let aligned_start = start_val.align_down(VALID_PAGE_SIZE);
        let aligned_end = end_val.align_down(VALID_PAGE_SIZE);

        // Ensure start <= end for a typical scenario (can be equal for empty iter)
        kani::assume(aligned_start <= aligned_end);

        let iter_opt = PageIter::<VALID_PAGE_SIZE, usize>::new(aligned_start, aligned_end);

        let iter = iter_opt.expect("PageIter::new should succeed for valid inputs");
        assert_eq!(iter.start, aligned_start, "Iterator start not initialized correctly");
        assert_eq!(iter.end, aligned_end, "Iterator end not initialized correctly");
    }

    #[kani::proof]
    fn proof_new_invalid_page_size_zero() {
        const INVALID_PAGE_SIZE: usize = 0;
        let start_addr: usize = kani::any();
        let end_addr: usize = kani::any();

        let iter_opt = PageIter::<INVALID_PAGE_SIZE, usize>::new(start_addr, end_addr);
        assert!(iter_opt.is_none(), "PAGE_SIZE 0 should result in None");
    }

    #[kani::proof]
    fn proof_new_invalid_page_size_not_power_of_two() {
        const INVALID_PAGE_SIZE: usize = 0x600; // e.g., 1536 (not a power of two)
        let start_addr: usize = kani::any();
        let end_addr: usize = kani::any();

        let iter_opt = PageIter::<INVALID_PAGE_SIZE, usize>::new(start_addr, end_addr);
        assert!(iter_opt.is_none(), "Non-power-of-two PAGE_SIZE should result in None");
    }

    #[kani::proof]
    fn proof_new_unaligned_start() {
        const TEST_PAGE_SIZE: usize = 0x1000;
        let unaligned_start_addr: usize = kani::any();
        let end_addr_val: usize = kani::any();

        // Ensure start_addr is indeed unaligned
        kani::assume(!unaligned_start_addr.is_aligned(TEST_PAGE_SIZE));

        // Ensure end_addr is aligned to isolate the failure cause
        let aligned_end_addr = end_addr_val.align_down(TEST_PAGE_SIZE);

        let iter_opt = PageIter::<TEST_PAGE_SIZE, usize>::new(unaligned_start_addr, aligned_end_addr);
        assert!(iter_opt.is_none(), "Unaligned start address should result in None");
    }

    #[kani::proof]
    fn proof_new_unaligned_end() {
        const TEST_PAGE_SIZE: usize = 0x1000;
        let start_addr_val: usize = kani::any();
        let unaligned_end_addr: usize = kani::any();

        // Ensure end_addr is indeed unaligned
        kani::assume(!unaligned_end_addr.is_aligned(TEST_PAGE_SIZE));

        // Ensure start_addr is aligned
        let aligned_start_addr = start_addr_val.align_down(TEST_PAGE_SIZE);

        let iter_opt = PageIter::<TEST_PAGE_SIZE, usize>::new(aligned_start_addr, unaligned_end_addr);
        assert!(iter_opt.is_none(), "Unaligned end address should result in None");
    }

    // --- Harnesses for Iterator::next ---

    #[kani::proof]
    fn proof_iteration_empty_range() {
        const TEST_PAGE_SIZE: usize = 0x1000;
        let addr_val: usize = kani::any();
        let aligned_addr = addr_val.align_down(TEST_PAGE_SIZE);

        if let Some(mut iter) = PageIter::<TEST_PAGE_SIZE, usize>::new(aligned_addr, aligned_addr) {
            assert!(iter.next().is_none(), "Iterator over an empty range (start == end) should yield None immediately");
        } else {
            kani::panic("PageIter::new should succeed for aligned_addr, aligned_addr");
        }
    }

    #[kani::proof]
    fn proof_iteration_start_greater_than_end() {
        const TEST_PAGE_SIZE: usize = 0x1000;
        let start_val: usize = kani::any();
        let end_val: usize = kani::any();

        let aligned_start = start_val.align_down(TEST_PAGE_SIZE);
        let aligned_end = end_val.align_down(TEST_PAGE_SIZE);

        kani::assume(aligned_start > aligned_end); // Key condition

        if let Some(mut iter) = PageIter::<TEST_PAGE_SIZE, usize>::new(aligned_start, aligned_end) {
            assert!(iter.next().is_none(), "Iterator with start > end should yield None immediately");
        } else {
            kani::panic("PageIter::new should succeed for aligned start > aligned end");
        }
    }

    #[kani::proof]
    fn proof_iteration_model_based() {
        const TEST_PAGE_SIZE: usize = 0x1000;
        let start_val: usize = kani::any();
        let end_val: usize = kani::any();

        let initial_start = start_val.align_down(TEST_PAGE_SIZE);
        let initial_end = end_val.align_down(TEST_PAGE_SIZE);

        kani::assume(initial_start <= initial_end);

        // Prevent the model's tracking arithmetic from overflowing if end is usize::MAX.
        // The iterator's internal `add` uses `checked_add.expect()`.
        // This assumption is for the model variables `model_current_addr` below.
        if TEST_PAGE_SIZE > 0 { // Avoid division by zero if TEST_PAGE_SIZE could be 0 (it's const 0x1000 here)
            let num_iterations_possible = if initial_start < initial_end {
                (initial_end - initial_start) / TEST_PAGE_SIZE
            } else {
                0
            };
            // Ensure the model's loop doesn't run too many times if range is huge.
            kani::assume(num_iterations_possible <= MAX_ITER_CHECK + 1);

            // Also, ensure that `initial_start + num_iterations_possible * TEST_PAGE_SIZE` (which is initial_end)
            // does not cause overflow issues for the model's calculation of `model_current_addr`.
            // This is generally fine because `initial_end` is assumed to be a valid address.
        }


        if let Some(mut iter) = PageIter::<TEST_PAGE_SIZE, usize>::new(initial_start, initial_end) {
            let mut model_current_addr = initial_start;

            for _ in 0..(MAX_ITER_CHECK + 2) { // Kani unrolls this loop. Iterate a bit beyond MAX_ITER_CHECK.
                let iter_item = iter.next();

                if model_current_addr < initial_end {
                    assert_eq!(iter_item, Some(model_current_addr), "Iterator item mismatch with model expectation");
                    // Check if the model's next address would overflow before advancing it.
                    // This is to ensure the model itself doesn't panic.
                    // The iterator's `add` might panic, which would be caught by Kani unless `should_panic` is used.
                    let (next_model_addr, overflow) = model_current_addr.overflowing_add(TEST_PAGE_SIZE);
                    kani::assume(!overflow || model_current_addr.checked_add(TEST_PAGE_SIZE).is_none()); // If model overflows, it should be where iter.add would panic
                    model_current_addr = next_model_addr;

                } else { // model_current_addr >= initial_end
                    assert!(iter_item.is_none(), "Iterator should be exhausted when model expects exhaustion");
                }
            }
        } else {
            kani::panic("PageIter::new should have succeeded for the given inputs");
        }
    }

    #[kani::proof]
    #[kani::should_panic]
    fn proof_iteration_add_overflow_panic() {
        const TEST_PAGE_SIZE: usize = 0x1000;
        // Kani requires const generics to be concrete, TEST_PAGE_SIZE is fine.

        let start_addr_sym: usize = kani::any();
        let start_addr = start_addr_sym.align_down(TEST_PAGE_SIZE);

        // Condition 1: The `add` operation in `next()` will cause an overflow.
        kani::assume(start_addr.checked_add(TEST_PAGE_SIZE).is_none());

        // Condition 2: `end_addr` must be > `start_addr` for `next()` to attempt the `add`.
        // `end_addr` must also be aligned.
        // If `start_addr` is already `usize::MAX.align_down(TEST_PAGE_SIZE)`,
        // then no aligned `end_addr > start_addr` exists.
        // This means the combination of assumptions might be unsatisfiable for some `usize` sizes / `PAGE_SIZE`.
        // Kani will report this if the proof becomes vacuous.
        let end_addr_sym: usize = kani::any();
        let end_addr = end_addr_sym.align_up(TEST_PAGE_SIZE); // Align up to get a potentially larger address
                                                              // Or use .align_down for consistency, depends on how end_addr_sym is chosen.
                                                              // Let's use align_down as in other places.
        let end_addr_final = end_addr_sym.align_down(TEST_PAGE_SIZE);


        kani::assume(end_addr_final > start_addr);

        if let Some(mut iter) = PageIter::<TEST_PAGE_SIZE, usize>::new(start_addr, end_addr_final) {
            // At this point, iter.start < iter.end is true from the assume.
            // The .add() method inside iter.next() should panic.
            let _ = iter.next();
            // If iter.next() returned without panicking, our assumption about the panic was wrong
            // or the conditions weren't sufficient.
            kani::panic("iter.next() should have panicked due to overflow in MemoryAddr::add");
        } else {
            // This means PageIter::new failed.
            // Given aligned start/end and valid PAGE_SIZE, it shouldn't, unless assumptions conflict.
            kani::panic("PageIter::new failed unexpectedly in panic test setup");
        }
    }
}

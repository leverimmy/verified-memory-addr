# verified-memory-addr

A verified crate ([memory_addr`](https://github.com/arceos-org/axmm_crates/tree/main/memory_addr)) using [Kani](https://github.com/model-checking/kani).

This repository mainly verifies:

- **MemoryAddr Trait and Implementations:** The core `MemoryAddr` trait, which abstracts over physical and virtual addresses, and its automatic implementation for types satisfying `Copy`, `From<usize>`, `Into<usize>`, and `Ord`. This includes utility methods for alignment (e.g., `align_down`, `align_up`, `is_aligned`) and arithmetic operations (e.g., `offset`, `add`, `sub`, `offset_from`), with both panicking and wrapping/checked variants.
- **`PageIter` for Page-by-Page Iteration:** This iterator allows traversing a memory range page by page, with compile-time checked page sizes. Verification ensures correct iteration, proper handling of invalid page sizes (not a power of two or zero), and unaligned start/end addresses.
- **`AddrRange` for Memory Address Ranges:** This structure defines a memory range with `start` (inclusive) and `end` (exclusive) addresses. It includes methods for construction (checked and unchecked), checking for emptiness, calculating size, and determining containment or overlap with addresses and other ranges. Proofs confirm the correctness of these methods, including panic conditions for invalid range creation or overflow during size calculation.
- **Core Alignment Functions:** Standalone functions like `align_down`, `align_up`, `align_offset`, and `is_aligned` that operate directly on `usize` values. These are verified to correctly implement bitwise alignment logic, with proofs covering their core properties and behavior under various conditions, including overflow for `align_up`.
- **Type Aliases and Macros:** `PhysAddr`, `VirtAddr`, `PhysAddrRange`, `VirtAddrRange`, and convenience macros like `pa!`, `va!`, `addr_range!`, `va_range!`, and `pa_range!` are also part of the verified API, ensuring type safety and correct instantiation.

## Run

```bash
cargo kani
```

## Result

The expected output should be:

```bash
Manual Harness Summary:
Complete - 55 successfully verified harnesses, 0 failures, 55 total.
```

However, even minor deviations from the expected behavior, such as a miswritten `align_up` function in [lib.rs](./src/lib.rs) like this:

```rust
#[inline]
pub const fn align_up(addr: usize, align: usize) -> usize {
    // should be
    // addr.wrapping_add(align - 1) & !(align - 1)
    addr.wrapping_add(align) & !(align - 1)
}
```

can lead to verification failures. In such a scenario, Kani's output would highlight the specific failing harnesses:

```bash
Manual Harness Summary:
Verification failed for - addr::addr_proofs::proof_align_up
Verification failed for - lib_proofs::proof_align_up_4k_consistency_and_properties
Verification failed for - lib_proofs::proof_is_aligned
Verification failed for - lib_proofs::proof_align_up_assuming_no_sum_overflow
Complete - 51 successfully verified harnesses, 4 failures, 55 total.
```

# verified-memory-addr

A verified [`crate::memory_addr`](https://github.com/rcore-os/arceos/tree/dev/crates/memory_addr) using [Kani](https://github.com/model-checking/kani).

This repository mainly verifies:

- Address Alignment Logic
- Address Type Safety and Conversions
- Pointer Conversions
- Arithmetic Operations

## Run

```bash
cargo kani
```

## Result

```bash
Manual Harness Summary:
Complete - 22 successfully verified harnesses, 0 failures, 22 total.
```

# Contract Reasoning: array_count_zero

## Source semantics

The raw program scans the integer array `a[0..n-1]`, increments `count` once for each element equal to `0`, and returns `count`. It does not write through `a` or modify any other caller-owned memory.

## Interface decision

The original interface

```c
int array_count_zero(int n, int *a)
```

is already verification-friendly:

- `n` is the logical array length.
- `a` is an input array of exactly `n` integers.
- The return value is a scalar count.
- No heap allocation, I/O, global state, or test scaffolding is involved.

No interface rewrite is needed.

## Boundary conditions

- Allow `n == 0`; the loop body is skipped and the result is `0`.
- Require `0 <= n`.
- Bind a logical list `l` with `Zlength(l) == n`.
- Require `IntArray::full(a, n, l)` for memory safety and value semantics.
- Preserve the same `IntArray::full(a, n, l)` in the postcondition because the function is read-only.

The returned count is always between `0` and `n`, so with C `int n` and `0 <= n`, `count++` cannot overflow beyond the range already implied by the representable function argument.

## Mathematical specification

The result is the number of entries in `l` equal to `0`. Existing inputs in this repository use small task-specific Coq functions for conditional list counts, such as `count_positive_spec` and `count_equal_to_k_spec`. This task follows that established pattern with:

```coq
Fixpoint array_count_zero_spec (l : list Z) : Z := ...
```

## Coq dependency judgment

An additional `input/array_count_zero.v` is justified because the repository does not expose a generic public zero-count function in the C annotation layer, and the contract needs a stable list-level count semantics. The `.v` file contains only the task-specific recursive definition and basic imports.

## Verify-stage exclusions

The C output contains only the function body plus its top-level contract. Proof guidance and loop reasoning are left to the Verify stage.

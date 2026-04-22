# Contract reasoning: array_remove_value_to_output

## Source semantics

The function scans the input array `a[0..n)` from left to right. For each element not equal to `k`, it copies that element to the next free position in `out` and increments `write`. Elements equal to `k` are skipped. The return value is the number of copied elements.

The input array is not modified. The output array keeps the filtered prefix in the same order as the input; positions after the returned count are unspecified but remain part of the caller-provided `out` buffer.

## Interface and bounds

The raw interface is already verification-friendly:

```c
int array_remove_value_to_output(int n, int *a, int k, int *out)
```

No allocation, I/O, global state, or test harness code is involved. The contract requires `0 <= n`, an input list `la` of length `n`, and an initial output list `lo` of length `n`. The separating conjunction between the two `IntArray::full` predicates requires disjoint ownership of `a` and `out`, matching the intended read-input/write-output behavior.

The local variables `i` and `write` both range from `0` to `n`; no arithmetic other than increments by one is used. Since `n` is an `int` parameter and no `n + 1` buffer is formed, no extra `n < INT_MAX` precondition is needed for the contract shape.

## Mathematical specification

The natural result is the list obtained by filtering `la`, keeping exactly the elements whose value is not equal to `k`. This is a task-specific list transform, so a small Coq definition is useful:

```coq
array_remove_value_to_output_spec : list Z -> Z -> list Z
```

The C postcondition states:

- `__return` is the `Zlength` of the filtered list.
- `a` still owns the original list `la`.
- `out` owns a length-`n` list whose prefix is the filtered list.
- The remaining suffix has length `n - Zlength(filtered)`, and its contents are intentionally unspecified.

## Coq dependency decision

This task needs a reusable filter function over `list Z` parameterized by `k`. There is no sufficiently direct built-in project function for this exact output-list semantics, so `input/array_remove_value_to_output.v` is created with only that task-specific definition.

No invariants, assertions, bridge assertions, or loop-exit annotations are included in the contract output; those belong to the Verify stage.

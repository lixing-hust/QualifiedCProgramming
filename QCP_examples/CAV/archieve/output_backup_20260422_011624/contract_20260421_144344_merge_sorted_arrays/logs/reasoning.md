# Contract reasoning: merge_sorted_arrays

## Source semantics

The raw task defines a void function:

```c
void merge_sorted_arrays(int n, int *a, int m, int *b, int *out)
```

Inputs `a` and `b` are nondecreasing integer arrays with exact lengths `n` and `m`.
The function writes the stable merge of the two arrays into `out`, whose exact
length is `n + m`. It does not modify `a` or `b`.

The implementation is already verification-friendly: it has no I/O, allocation,
global state, or test harness. The three-pointer implementation is preserved
unchanged.

## Contract shape

The contract binds three logical lists:

- `la` for the initial contents of `a`
- `lb` for the initial contents of `b`
- `lo` for the initial contents of `out`

The precondition requires:

- `0 <= n`, `0 <= m`
- `n + m <= INT_MAX`, so the output length and index variable `k` remain in
  signed-int range
- `Zlength(la) == n`, `Zlength(lb) == m`, and `Zlength(lo) == n + m`
- both input lists are nondecreasing
- disjoint owned array regions for `a`, `b`, and `out`

The postcondition preserves `a` and `b` with their original logical contents and
states that `out` contains exactly `merge_sorted_arrays_spec(la, lb)`.

The separating conjunction between the three `IntArray::full` predicates is used
to express that the output buffer is distinct from the input buffers. This is
stronger than the natural language "does not modify `a` and `b`" but matches the
implementation's in-place writes to `out` and keeps the memory contract direct.

## Coq dependency decision

An exact merge result is easier and clearer as a recursive list function than as
a large quantified C postcondition. Existing inputs include `sorted_z` for sort
results and several task-specific list functions, but no reusable merge function
for two sorted lists. Therefore this contract uses a small task-specific
`input/merge_sorted_arrays.v` defining:

```coq
merge_sorted_arrays_spec : list Z -> list Z -> list Z
```

No loop invariants, assertions, bridge assertions, or verify-stage comments are
included in `input/merge_sorted_arrays.c`.

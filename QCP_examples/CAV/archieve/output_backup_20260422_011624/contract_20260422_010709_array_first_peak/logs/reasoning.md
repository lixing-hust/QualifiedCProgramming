# Contract reasoning: array_first_peak

## Source semantics

The source function scans an integer array from index `1` through `n - 2`.
It returns the first index `i` such that:

- `0 < i < n - 1`
- `a[i] >= a[i - 1]`
- `a[i] >= a[i + 1]`

If no such interior peak exists, it returns `-1`.

The implementation initializes `i = 1`, checks `i + 1 < n`, returns
immediately on the first matching peak, and otherwise increments `i`.
For `n <= 2`, the loop body is never executed, so the result is `-1`.

## Boundary and memory conditions

The input length satisfies `0 <= n`. The pointer `a` is modeled with
`IntArray::full(a, n, l)` and `Zlength(l) == n`, which gives ownership of
exactly the `n` readable integer cells used by the scan.

All array reads happen only when `i + 1 < n` and `i` starts at `1`, so the
accesses `a[i - 1]`, `a[i]`, and `a[i + 1]` are within `[0, n)`.

The loop expression `i + 1 < n` uses signed integer arithmetic. To keep this
verification-friendly and avoid overflow obligations around `i + 1`, the
contract includes `n <= INT_MAX`. This matches the `int` parameter domain and
keeps all loop indices within `int` range.

## Postcondition design

The postcondition has two cases:

1. Return `-1` and every interior index fails the peak predicate.
2. Return an interior peak index, and every earlier interior index fails the
   peak predicate.

This expresses both correctness of the returned index and the "first" part of
the result. The array is read-only, so the postcondition restores
`IntArray::full(a, n, l)`.

## Coq dependency decision

No additional `input/array_first_peak.v` file is needed. The peak predicate
and first-result property are simple arithmetic/list-index formulas that can
be written directly in the C contract using existing list and integer-array
support.

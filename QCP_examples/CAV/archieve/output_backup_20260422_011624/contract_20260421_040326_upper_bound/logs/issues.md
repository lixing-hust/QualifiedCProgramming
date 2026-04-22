# Contract issues for `upper_bound`

## Resolved decisions

- The raw interface is already verification-friendly: a single target function with scalar parameters and one input array.
- The array is read-only, so the contract preserves `IntArray::full(a, n, l)` unchanged.
- The nondecreasing precondition is written directly as a two-index quantified property over `l`.
- The upper-bound result is specified by a prefix condition `l[i] <= target` before `__return` and a candidate condition `l[__return] > target` when `__return < n`.

## Open issues

None.

## Deferred to Verify

- Loop invariants for the half-open binary search.
- Any exit facts needed by symbolic execution.
- Manual Coq proof details for sorted-array boundary reasoning.

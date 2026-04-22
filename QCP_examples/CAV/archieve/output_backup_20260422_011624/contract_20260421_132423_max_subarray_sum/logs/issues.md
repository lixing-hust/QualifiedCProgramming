# Contract issues: max_subarray_sum

## Resolved

- Needed a task-specific Coq specification because no existing repository function directly expresses maximum non-empty contiguous subarray sum.
  - Fix: added `input/max_subarray_sum.v` with `max_subarray_sum_spec` and Kadane-style helper definitions.
- The implementation evaluates `cur + a[i]`, so a simple element-bound precondition would not be enough to rule out signed overflow.
  - Fix: required every non-empty contiguous subarray sum `sum(sublist(lo, hi, l))` to lie within `[INT_MIN, INT_MAX]`.
- Existing contracts use one quantified variable per binder.
  - Fix: encoded the overflow condition as nested `forall (lo: Z), (forall (hi: Z), ...)`.

## Open

- None for the Contract stage.


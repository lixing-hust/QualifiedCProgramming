# Issues for `binary_search_last`

## Resolved

- The raw implementation is already a single verification-friendly function. No interface rewrite was needed.
- The array is read-only, so the contract preserves `IntArray::full(a, n, l)` in the postcondition.
- Added `n <= INT_MAX` to support arithmetic safety for the half-open binary-search interval and midpoint computation.
- Used a direct first-order postcondition for the last occurrence: either no element equals `target`, or the returned index equals `target` and all later indices differ from `target`.

## Open issues

- None for the Contract stage.

## Deferred to Verify

- Loop invariant and bridge assertions for the upper-bound search are intentionally not included in `input/binary_search_last.c`.

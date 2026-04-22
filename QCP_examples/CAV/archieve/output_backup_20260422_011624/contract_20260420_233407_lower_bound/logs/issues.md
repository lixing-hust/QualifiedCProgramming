# Issues for `lower_bound`

## Resolved decisions

- The raw nondecreasing precondition was written as pairwise monotonicity instead of adjacent-only monotonicity. This keeps the contract close to the mathematical meaning of "nondecreasing" while making binary-search exclusion properties explicit for the Verify phase.
- Added `n <= INT_MAX` to the precondition. The implementation stores `n` in `right` and may return `n`; this bound also supports midpoint and `mid + 1` integer-safety obligations.
- Did not create `input/lower_bound.v` because the lower-bound property is expressible directly in the C contract.

## Open issues

None.

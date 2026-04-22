# Contract Issues: min_cost_two_steps

## Resolved

- A problem-specific Coq recurrence was required because no existing shared
  definition directly modeled the one-or-two-step minimum path cost.
- The implementation uses signed `int` arithmetic, so the contract adds a
  nonnegative-total-sum bound to prevent overflow.

## Open

- None.

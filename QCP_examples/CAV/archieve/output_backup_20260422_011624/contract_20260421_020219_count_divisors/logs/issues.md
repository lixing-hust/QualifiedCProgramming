# Issues: count_divisors contract

## Resolved

- Added the required overflow precondition `n < INT_MAX` because the `for` loop update computes `d + 1` after the final `d == n` iteration.
- Added a task-specific Coq definition for exact divisor counting, since no existing shared definition was found for this mathematical result.

## Open

- None.

## Notes for Verify

- The C file intentionally contains no loop invariants, assertions, bridge assertions, or loop-exit assertions.
- The postcondition is intentionally compact and delegates exact counting semantics to `count_divisors_spec`.

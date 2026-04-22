# Contract issues: count_multiples

## Resolved

- Added `n < INT_MAX` beyond the raw statement's `n >= 1` to rule out signed overflow in the final `for` loop increment.
- Used a task-specific Coq counting function instead of a bare closed form so the postcondition states the enumeration semantics directly.

## Open

- None.

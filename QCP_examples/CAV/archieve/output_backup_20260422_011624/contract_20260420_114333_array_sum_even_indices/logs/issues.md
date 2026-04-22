# Issues: array_sum_even_indices contract

## Resolved

- The plain list `sum(l)` helper is not sufficient because the function sums only positions with even zero-based indices. Added a task-specific Coq helper in `input/array_sum_even_indices.v`.
- A final-result overflow bound alone would not protect intermediate accumulator updates for mixed-sign arrays. The contract requires every even-index prefix sum to stay in signed-int range.

## Open

- None.

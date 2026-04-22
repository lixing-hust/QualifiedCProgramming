## Semantic summary

Target function: `array_adjacent_diff`

- Input array `a` has logical length `n`.
- Output array `out` has logical length `n - 1`.
- For each index `i` such that `0 <= i` and `i + 1 < n`, the function writes `out[i] = a[i + 1] - a[i]`.
- The function does not modify `a`.

## Boundary analysis

- The raw statement requires `n >= 1`, so the contract uses `1 <= n`.
- When `n == 1`, the loop body does not execute and `out` has length `0`.
- The loop guard `i + 1 < n` matches the intended output domain exactly, so the postcondition is expressed over the same index form.

## Memory shape

- `a` is modeled as `IntArray::full(a, n, la)`.
- `out` is modeled as `IntArray::full(out, n - 1, lo)` in the precondition and `IntArray::full(out, n - 1, lr)` in the postcondition.
- The postcondition restores the full ownership of `a` unchanged and gives the updated full ownership of `out`.

## Arithmetic safety

- C signed subtraction must stay within `int` range.
- The contract therefore requires:
  `forall i, 0 <= i && i + 1 < n -> INT_MIN <= la[i + 1] - la[i] <= INT_MAX`.
- No stronger arithmetic condition is needed.

## Coq dependency decision

- No custom `.v` file is needed.
- The result relation is a direct pointwise array specification and does not require a problem-specific logical wrapper or helper function.

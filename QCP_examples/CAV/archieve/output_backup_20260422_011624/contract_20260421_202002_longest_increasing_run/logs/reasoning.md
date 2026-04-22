# Contract reasoning: longest_increasing_run

## Source semantics

The raw task defines `longest_increasing_run(int n, int *a)` for an integer array of length `n`.

- `n >= 0`.
- The array length is exactly `n`.
- The result for an empty array is `0`.
- For a non-empty array, the result is the maximum length of a contiguous strictly increasing segment.
- The function reads but does not modify the array.

The supplied C implementation initializes `cur = 1` and `best = 1` for non-empty arrays, then scans from index `1` to `n - 1`. At each index it extends the current run when `a[i - 1] < a[i]`, otherwise resets it to `1`; `best` tracks the maximum seen current run.

## Contract shape

The function is a single read-only array scan. The original interface is already verification-friendly:

- `n` is retained as an integer length.
- `a` is represented by `IntArray::full(a, n, l)`.
- The postcondition restores the same `IntArray::full(a, n, l)` because the function does not mutate the array.

The precondition uses:

- `0 <= n`
- `n <= INT_MAX`
- `Zlength(l) == n`
- `IntArray::full(a, n, l)`

The `n <= INT_MAX` bound is included because the loop counter and return value are C `int`s, and the longest run length is bounded by `n`.

## Mathematical specification

The natural result is not a simple existing scalar function. A small problem-specific Coq definition is therefore appropriate in `input/longest_increasing_run.v`.

The Coq specification mirrors the implementation:

- `longest_increasing_run_spec nil = 0`
- for `x :: xs`, scan the tail with current run `1`, best run `1`, and previous value `x`
- for each next value, update `cur` by either `cur + 1` or `1`, then update `best` with `Z.max`

This keeps the C postcondition compact:

`__return == longest_increasing_run_spec(l)`

## Verify-stage boundaries

No loop invariants, assertions, bridge assertions, or loop-exit assertions are included in the contract input. Those belong to the Verify stage.

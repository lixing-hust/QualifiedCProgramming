## Task

- Target function: `array_count_increasing_steps`
- Raw source: `raw/array_count_increasing_steps.md`
- Formal outputs: `input/array_count_increasing_steps.c` and `input/array_count_increasing_steps.v`

## Semantic Summary

- The function scans an integer array `a` of logical length `n`.
- For each index `i` such that `0 <= i` and `i + 1 < n`, it checks whether `a[i] < a[i + 1]`.
- It returns the number of indices that satisfy that strict adjacent-increase predicate.
- The function does not modify the input array.

## Interface Judgment

- The original interface `int array_count_increasing_steps(int n, int *a)` is already verification-friendly.
- No interface rewrite is needed.
- This is a standard read-only array scan with one integer accumulator.

## Boundary Analysis

- The raw statement allows `n >= 0`, so the contract keeps `0 <= n`.
- When `n == 0` or `n == 1`, there are no valid indices with `i + 1 < n`, so the result should be `0`.
- The implementation loop guard `i + 1 < n` matches the intended counting domain directly.

## Memory Shape

- Bind the array contents as a logical list `l`.
- Require `Zlength(l) == n` and `IntArray::full(a, n, l)`.
- Preserve `IntArray::full(a, n, l)` in the postcondition because the code only reads from `a`.

## Result Semantics

- The return value is a count derived from the whole logical list, not a simple pointwise relation.
- A task-specific Coq function over `list Z` is the cleanest way to express this semantics.
- The intended recursive meaning is:
  - lists of length `0` or `1` map to `0`
  - for `x :: y :: xs`, contribute `1` iff `x < y`, then continue on `y :: xs`

## Coq Dependency Decision

- `input/array_count_increasing_steps.v` is needed.
- It will define `array_count_increasing_steps_spec : list Z -> Z`.
- `input/array_count_increasing_steps.c` should import that file and state the postcondition using this logical function.

## Contract Shape

- Use:
  - `With l`
  - `Require 0 <= n && Zlength(l) == n && IntArray::full(a, n, l)`
  - `Ensure __return == array_count_increasing_steps_spec(l) && IntArray::full(a, n, l)`

## Bounds / Safety Notes

- The loop only reads `a[i]` and `a[i + 1]` within the array bounds induced by `Zlength(l) == n`.
- No arithmetic side condition is needed for the comparison `a[i] < a[i + 1]` because it does not compute on the values.
- As with nearby counting examples, no explicit `INT_MAX` bound on the accumulator is added at contract time unless Verify later shows it is required.

## Verify-Stage Deferral

- Do not add loop invariants, assertions, bridge assertions, or loop-exit assertions here.
- Those belong to Verify, not Contract.

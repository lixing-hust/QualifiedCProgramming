## Task

- Target function: `count_positive`
- Raw source: `raw/count_positive.md`
- Formal outputs: `input/count_positive.c` and `input/count_positive.v`

## Semantic Summary

- The function scans an integer array `a` of logical length `n`.
- It returns the number of elements strictly greater than `0`.
- The input array is read-only from the function's semantic point of view and must be preserved in the postcondition.

## Interface Judgment

- The original interface `int count_positive(int n, int *a)` is already verification-friendly.
- No interface rewrite is needed.
- The function is a single-pass array scan with one accumulator, which matches the repository's standard array-contract pattern.

## Memory Shape

- Require `0 <= n`.
- Bind the array contents as a logical list `l`.
- Require `Zlength(l) == n` and `IntArray::full(a, n, l)`.
- Preserve `IntArray::full(a, n, l)` in the postcondition because the code does not write through `a`.

## Result Semantics

- The result should be expressed as a pure logical function over `list Z`.
- A repository-wide existing Coq function for this exact semantics was not found.
- Therefore a small task-specific `.v` bridge is justified.

## Coq Dependency Decision

- `input/count_positive.v` is needed.
- It will define `count_positive_spec : list Z -> Z`.
- The definition is a straightforward recursive count:
  - empty list maps to `0`
  - `x :: xs` contributes `1` iff `x > 0`, then recurses on `xs`

## Contract Shape

- `input/count_positive.c` should follow nearby patterns such as `count_equal_to_k.c`.
- Use:
  - `With l`
  - `Require 0 <= n && Zlength(l) == n && IntArray::full(a, n, l)`
  - `Ensure __return == count_positive_spec(l) && IntArray::full(a, n, l)`

## Bounds / Safety Notes

- The raw problem statement guarantees logical array length exactly `n`; this is captured via `Zlength(l) == n`.
- No additional arithmetic precondition is added here.
- The implementation increments an `int` accumulator at most `n` times. Repository neighbors for similar counting scans do not add an explicit `INT_MAX` bound in the contract, so this task keeps the same style unless Verify later proves it necessary.

## Verify-Stage Deferral

- Do not add loop invariants, assertions, bridge assertions, or loop-exit assertions in the contract file.
- Those belong to Verify, not Contract.

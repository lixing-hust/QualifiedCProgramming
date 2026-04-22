# Contract Reasoning: array_last_positive

## Source Semantics

The raw task defines `array_last_positive(int n, int *a)`.

The function scans array positions `0 .. n - 1` from left to right, keeps `ans` as the most recent index whose element is positive, and returns `ans` after the scan. If no positive element is found, `ans` remains `-1`.

The implementation does not modify the array.

## Boundary Conditions

- `n >= 0`.
- `a` has exactly `n` integer elements.
- For `n == 0`, the loop does not execute and the result is `-1`.
- Valid returned indices, when present, are in `[0, n)`.

## Memory Model

The function only reads from `a`.

Use `IntArray::full(a, n, l)` in both precondition and postcondition to express ownership of the whole array and preservation of its contents. Bind `l` with `With` because the postcondition refers to input values.

## Result Specification

The result has two cases:

1. `__return == -1` and every element in `l[0 .. n - 1]` is non-positive.
2. `0 <= __return < n`, `l[__return] > 0`, and every element after `__return` is non-positive.

This directly captures the last positive index without an auxiliary Coq definition.

## Coq Dependency Decision

No `input/array_last_positive.v` is needed. The specification is expressible directly with integer comparisons, list indexing, `Zlength`, and quantified conditions already used by existing array scan contracts.

## Target

- Function: `array_any_negative`
- Raw source: `raw/array_any_negative.md`
- Output C: `input/array_any_negative.c`

## Semantics

The function scans an integer array `a` of logical length `n` and returns whether any element is negative. It returns `1` as soon as it finds an index `i` such that `a[i] < 0`; otherwise, after scanning the whole array, it returns `0`.

The function is read-only with respect to the input array.

## Interface / memory decision

The original interface is already verification-friendly:

- `n` is the logical array length
- `a` is caller-owned array memory
- the function performs no allocation and has no hidden side effects

Use `IntArray::full(a, n, l)` to connect the C array with the logical list `l`. Since the implementation does not modify the array, preserve the same `IntArray::full(a, n, l)` predicate in the postcondition.

## Boundary conditions

- Require `0 <= n`.
- Require `Zlength(l) == n`.
- For `n == 0`, the existential negative branch is false and the universal nonnegative branch is vacuously true, so the result is `0`.

No array-content arithmetic overflow condition is needed because the implementation only compares existing `int` elements against `0`.

## Postcondition shape

The result can be expressed directly with first-order quantification over the logical list:

- return `1` iff there exists an index `i` with `0 <= i < n` and `l[i] < 0`
- return `0` iff every index `i` with `0 <= i < n` satisfies `l[i] >= 0`

This gives a precise boolean contract for the early-return scan and preserves the input array predicate.

## Coq dependency decision

Do not create `input/array_any_negative.v`.

Reason:

- the specification is a direct quantified property over `l`
- no reusable or problem-specific mathematical function is required
- existing list indexing and quantifier support are sufficient

## Verify-stage restraint

Per the contract workflow, do not add loop invariants, asserts, `which implies`, bridge assertions, or loop-exit assertions to the generated C file. Only emit the target function and its complete pre/postconditions.

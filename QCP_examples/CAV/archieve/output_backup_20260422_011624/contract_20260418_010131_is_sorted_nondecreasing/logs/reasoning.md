## Target

- Function: `is_sorted_nondecreasing`
- Raw source: `raw/is_sorted_nondecreasing.md`

## Semantics

The function checks whether the integer array `a` of logical length `n` is nondecreasing. It returns `1` exactly when every adjacent pair satisfies `a[i] <= a[i + 1]`, and returns `0` as soon as it finds a witness index with `a[i] > a[i + 1]`. The array is read-only from the function's point of view.

## Interface / memory decision

The original interface `int is_sorted_nondecreasing(int n, int *a)` is already verification-friendly:

- `n` provides the logical array length
- `a` is caller-owned readable memory
- there are no side effects and no allocation

Use `IntArray::full(a, n, l)` for the array shape and logical contents. Because the implementation does not modify `a`, the same predicate should be preserved in the postcondition.

## Boundary conditions

- `n >= 0`
- `Zlength(l) == n`
- if `n == 0` or `n == 1`, the quantified sortedness condition over adjacent pairs is vacuously true, so the function should return `1`

No arithmetic-overflow side condition is needed for array contents because the function only compares existing `int` values.

For the loop guard `i + 1 < n`, the natural precondition `n >= 0` is sufficient at the contract level for this repository style. No interface rewrite is required.

## Postcondition shape

The result can be expressed directly in the C contract without a dedicated Coq bridge file:

- success branch: `__return == 1` and all adjacent logical elements are ordered
- failure branch: `__return == 0` and there exists an adjacent inversion witness

This yields a precise boolean contract while keeping the array content unchanged in both branches.

## Coq dependency decision

Do not create `input/is_sorted_nondecreasing.v`.

Reason:

- the required property is a first-order quantified relation over the logical list `l`
- no problem-specific helper function is necessary
- existing list indexing and quantifiers are enough to describe the specification directly

## Verify-stage restraint

Per the contract workflow, do not add loop invariants, asserts, bridge asserts, `which implies`, or loop-exit assertions in the generated C file. Only emit the target function and its full pre/postconditions.

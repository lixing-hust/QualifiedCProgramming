# Reasoning

## Semantics

Target function `find_first_equal` scans an integer array `a` of length `n` from left to right and returns the first index `i` such that `a[i] == k`. If no such index exists, it returns `-1`.

The implementation is read-only with respect to `a`, so the contract should preserve the same `IntArray::full(a, n, l)` ownership/value relation after the call.

## Interface judgment

The original interface is already verification-friendly:

- `n` is an `int` length parameter
- `a` points to exactly `n` integers
- `k` is a plain scalar input
- the function returns an `int` result and does not allocate memory

No interface rewrite is needed.

## Preconditions

The problem statement gives `n >= 0` and says the array length is exactly `n`. In the contract this becomes:

- `0 <= n`
- `Zlength(l) == n`
- `IntArray::full(a, n, l)`

No extra element-wise range condition is needed because the function only reads array elements, compares them with `k`, and returns either `-1` or an in-bounds index.

## Postcondition

The postcondition needs to express both cases:

- if some element equals `k`, the return value is the least index where this happens
- otherwise the return value is `-1`

Writing this directly as a quantified C annotation is possible but unnecessarily heavy for a basic scan pattern. A dedicated recursive logical function keeps the C contract small and stable:

- `find_first_equal_spec : list Z -> Z -> Z`

Then specify:

- `__return == find_first_equal_spec(l, k)`
- `IntArray::full(a, n, l)`

Using `k` directly in the postcondition is sufficient because `k` is not modified.

## Coq dependency decision

A dedicated `input/find_first_equal.v` is needed.

Reason:

- no obvious existing repository-level logical function was identified for “first index of value in a list, else `-1`”
- the target semantics is naturally expressed by a short recursive definition
- this avoids pushing a long minimality/non-membership condition into the C annotation

The `.v` file should contain only the task-specific logical definition and no proof script.

## Verify-stage restraint

Do not pre-write loop invariants, assertions, bridge assertions, or loop-exit assertions here. This stage only prepares the contract input.

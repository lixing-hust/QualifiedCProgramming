# Reasoning

## Semantics

Target function `count_equal_to_k` scans an integer array `a` of length `n` and returns the number of indices `i` such that `a[i] == k`.

The implementation is read-only with respect to `a`, so the postcondition should preserve the same `IntArray::full(a, n, l)` ownership/value relation from the precondition.

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

No element-wise bound is needed because the function only performs equality comparison and increments `ret` by at most `n` times. Since `n` is an `int`, the returned count is within the `int` range whenever the function executes with a valid C `int` input.

## Postcondition

The result is not a stock arithmetic aggregate like `sum(l)` or `max_list_nonempty(l)`. It is the count of occurrences of value `k` in the logical list `l`.

To keep the C contract direct and stable, use a small task-specific Coq function:

- `count_equal_to_k_spec : list Z -> Z -> Z`

Then specify:

- `__return == count_equal_to_k_spec(l, k)`
- `IntArray::full(a, n, l)`

Using `k` directly in the postcondition is sufficient because `k` is not modified.

## Coq dependency decision

A dedicated `input/count_equal_to_k.v` is needed.

Reason:

- no clearly reusable repository-level list-count function was identified in the existing CAV input examples
- the target semantics is naturally expressed by a short recursive definition
- this keeps the C contract simple and avoids encoding counting logic directly in the C annotation

The `.v` file should contain only the task-specific logical definition and no proof script.

## Verify-stage restraint

Do not pre-write loop invariants, assertions, bridge assertions, or loop-exit assertions here. This stage only prepares the contract input.

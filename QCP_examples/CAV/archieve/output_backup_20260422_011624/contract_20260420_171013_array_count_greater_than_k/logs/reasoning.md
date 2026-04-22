# Contract reasoning: array_count_greater_than_k

## Raw semantics

The target function scans an integer array `a` of length `n` and returns the number of elements whose value is strictly greater than the threshold `k`.

The implementation is read-only over `a`:

- initialize `cnt` to `0`
- iterate `i` from `0` to `n - 1`
- increment `cnt` exactly when `a[i] > k`
- return `cnt`

## Input domain and memory

The raw problem states:

- `n >= 0`
- `a` has exactly length `n`
- the function does not modify the array

The contract therefore binds a logical list `l` for the contents of `a`, requires `Zlength(l) == n`, and owns `IntArray::full(a, n, l)`.

Since `cnt` is at most `n`, the C increment `cnt++` is safe when `n` is within signed `int` range. The project examples for array count functions use the C `int n` parameter plus `0 <= n` and the array shape; this contract follows that established pattern.

## Postcondition

The result is specified by a recursive Coq function:

`array_count_greater_than_k_spec : list Z -> Z -> Z`

It returns `0` for an empty list and otherwise adds `1` for a head `x` exactly when `x > k`, then recurses over the tail.

The postcondition states:

- `__return == array_count_greater_than_k_spec(l, k@pre)`
- `IntArray::full(a, n, l)` is preserved

`k@pre` is used because the result depends on the input threshold value.

## Coq dependency decision

No existing public Coq definition directly expresses "count elements greater than a threshold". This task needs a small problem-specific recursive specification, so `input/array_count_greater_than_k.v` is required.

The `.v` file contains only the task-specific logical definition and imports needed for `Z` and lists.

## Verify-stage boundary

The contract output contains only the function body, precondition, postcondition, and task-specific Coq definition. Verification annotations and proof guidance are left to the Verify stage.

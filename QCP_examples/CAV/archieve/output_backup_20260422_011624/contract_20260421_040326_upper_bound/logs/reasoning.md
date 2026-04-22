# Contract reasoning for `upper_bound`

## Source semantics

The raw task defines `upper_bound(n, a, target)` over a nondecreasing integer array segment `a[0..n)`. The function returns the first index `i` such that `a[i] > target`; if no such index exists, it returns `n`.

The implementation is a half-open binary search over `[left, right)`, initialized as `[0, n)`. At each step:

- `mid = left + (right - left) / 2`
- if `a[mid] <= target`, the answer cannot be at or before `mid`, so `left = mid + 1`
- otherwise `mid` remains a candidate, so `right = mid`

The function only reads `a` and does not mutate the array.

## Boundary conditions

- `n` may be `0`; then the loop is skipped and the result is `0`, which equals `n`.
- The result is always in the closed interval `[0, n]`.
- Every index before the result contains a value `<= target`.
- If the result is not `n`, then the value at the result is `> target`.
- If the result is `n`, all array elements are `<= target`, captured by the prefix condition with `__return == n`.

## Preconditions

The contract uses `With l` to bind the logical contents of the input array.

Required facts:

- `0 <= n`
- `n <= INT_MAX`, to keep binary-search index arithmetic inside signed `int` range
- `Zlength(l) == n`
- nondecreasing order: for all valid `i <= j`, `l[i] <= l[j]`
- full ownership/read permission for the input array: `IntArray::full(a, n, l)`

## Postconditions

The postcondition states the direct upper-bound semantics:

- `0 <= __return && __return <= n`
- every prior element satisfies `l[i] <= target`
- either `__return == n`, or `__return < n && l[__return] > target`
- the input array ownership is preserved unchanged

## Coq dependency judgment

No task-specific Coq file is needed. The specification can be expressed directly using integer comparisons, quantifiers, list indexing, `Zlength`, and `IntArray::full`, all already used by existing C contracts in this repository.

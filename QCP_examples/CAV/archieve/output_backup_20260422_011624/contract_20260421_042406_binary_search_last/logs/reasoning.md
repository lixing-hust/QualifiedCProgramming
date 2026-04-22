# Contract reasoning for `binary_search_last`

## Source semantics

The raw program implements an upper-bound binary search on a nondecreasing integer array. It searches the first index `left` such that `a[left] > target`; after the loop, `left - 1` is the last index whose value is at most `target`. The final guard checks whether that predecessor exists and equals `target`.

The intended result is:

- return the greatest index `r` in `[0, n)` such that `a[r] == target`;
- return `-1` if no index in `[0, n)` stores `target`;
- do not modify the input array.

## Boundary conditions

- `n` may be `0`. In that case `left == 0`, the final guard fails, and the function returns `-1`.
- The loop uses the half-open interval `[left, right)` with `right` initialized to `n`.
- The expression `mid = left + (right - left) / 2` is safe under `0 <= left <= right <= n` and `n <= INT_MAX`.
- The only array read in the loop is `a[mid]`, where `0 <= mid < n` whenever `left < right`.
- The final read `a[left - 1]` is guarded by `left > 0`; loop bounds imply `left <= n`, so `left - 1` is in `[0, n)`.

## Memory model

The input array is represented by `IntArray::full(a, n, l)`, with `Zlength(l) == n`. The function only reads from `a`, so the same predicate is restored unchanged in the postcondition.

## Mathematical contract

The precondition states that:

- `0 <= n`;
- `n <= INT_MAX`;
- `Zlength(l) == n`;
- `l` is nondecreasing, expressed with the pairwise fact `(forall i j, 0 <= i <= j < n -> l[i] <= l[j])`;
- the full input array is available.

The postcondition states that:

- if `__return == -1`, every in-range element differs from `target`;
- otherwise `__return` is in range, `l[__return] == target`, and every later index differs from `target`;
- the input array is unchanged.

This is a direct first-order specification and does not need any problem-specific Coq bridge file.

## Coq dependency decision

No `input/binary_search_last.v` is needed. The contract uses only existing list indexing, quantifiers, integer bounds, and `IntArray::full`.

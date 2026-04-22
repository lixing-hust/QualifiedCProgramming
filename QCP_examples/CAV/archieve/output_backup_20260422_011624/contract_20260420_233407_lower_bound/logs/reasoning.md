# Contract reasoning for `lower_bound`

## Source semantics

The raw task defines `lower_bound(int n, int *a, int target)` over an integer array `a` of length `n`.

The function performs a half-open binary search over `[left, right)`, initially `[0, n)`, and returns the first index `i` such that `a[i] >= target`. If every element is less than `target`, it returns `n`.

The implementation is read-only with respect to `a`.

## Preconditions

- `0 <= n`: the raw task allows empty arrays.
- `n <= INT_MAX`: loop variables and the returned index are C `int` values; the implementation may assign `n` to `right` and eventually to `left`.
- `Zlength(l) == n`: the logical list exactly represents the array length.
- `forall (i j), 0 <= i <= j < n -> l[i] <= l[j]`: this records the nondecreasing-array assumption in pairwise form. Pairwise monotonicity is verification-friendly for binary search because each branch excludes a whole prefix or suffix.
- `IntArray::full(a, n, l)`: the function needs read permission to the whole array and must preserve it.

No extra per-element arithmetic bound is required beyond the integer-array predicate and the fact that `target` is an `int` parameter. The midpoint calculation `left + (right - left) / 2` is protected by `0 <= left <= right <= n <= INT_MAX`.

## Postcondition

The result is specified relationally:

- `0 <= __return <= n`;
- every index before `__return` contains a value `< target`;
- either `__return == n`, or `__return < n` and `l[__return] >= target`;
- the input array ownership is restored unchanged as `IntArray::full(a, n, l)`.

This directly expresses the lower-bound contract without introducing a problem-specific Coq function.

## Coq dependency decision

No `input/lower_bound.v` is needed. The specification can be written with existing list indexing, integer comparisons, quantifiers, and `IntArray::full`.

## Interface decision

The raw interface is already verification-friendly:

- single target function;
- no I/O or global state;
- no allocation;
- no mutation of the input array;
- no need to change the signature.

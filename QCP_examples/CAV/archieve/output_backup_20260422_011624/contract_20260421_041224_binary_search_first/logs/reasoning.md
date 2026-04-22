# Contract Reasoning: binary_search_first

## Source Semantics

The raw task defines `binary_search_first(int n, int *a, int target)` over an integer array `a` of length `n`.

The input array is nondecreasing and is not modified. The function performs a lower-bound style binary search for the first index whose value is at least `target`, then returns that index only if the value is exactly `target`; otherwise it returns `-1`.

Mathematical result relation:

- If the function returns `-1`, then no index `i` with `0 <= i < n` satisfies `a[i] == target`.
- If the function returns `r`, then `0 <= r < n`, `a[r] == target`, and every earlier index `i` with `0 <= i < r` satisfies `a[i] != target`.

This directly captures "first equal index" without introducing a separate Coq helper predicate.

## Boundary Conditions

- `n` may be `0`; in that case the loop is skipped and the function returns `-1`.
- The binary-search interval is `[left, right)`, initialized as `[0, n)`.
- The implementation computes `mid = left + (right - left) / 2`, so the contract follows existing lower-bound examples and includes `n <= INT_MAX` along with `0 <= n`.
- `target` needs no domain restriction beyond the C `int` parameter type.

## Memory

The only memory argument is `a`, modeled as `IntArray::full(a, n, l)`.

The function reads from `a` but does not write to it, so the postcondition restores the same `IntArray::full(a, n, l)` predicate.

## Sortedness

The precondition uses the stronger pairwise nondecreasing form:

```c
(forall (i: Z) (j: Z),
  (0 <= i && i <= j && j < n) => l[i] <= l[j])
```

This matches the existing `lower_bound` and `upper_bound` contract style and is convenient for reasoning about all positions before or after the search boundary.

## Coq Dependency Decision

No `input/binary_search_first.v` is needed.

The full specification can be expressed directly with quantifiers over the logical list `l`, integer comparisons, and `IntArray::full`. There is no task-specific recursive function, relation, or abstraction layer that would justify a separate Coq file.

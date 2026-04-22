# Contract reasoning: max_subarray_sum

## Source semantics

The raw task asks for `max_subarray_sum(int n, int *a)`, where `a` is an integer array of length `n`, `n >= 1`, and the function returns the maximum sum of a non-empty contiguous subarray. The implementation is Kadane's algorithm:

- `cur` is initialized to `a[0]` and tracks the best non-empty suffix sum ending at the current index.
- `best` is initialized to `a[0]` and tracks the best non-empty subarray sum seen so far.
- For each later element `a[i]`, the next suffix best is `max(a[i], cur + a[i])`, and the global best is updated with that suffix best.

The function only reads from `a` and returns an `int`; it does not allocate memory and does not modify the array.

## Interface and memory

The original interface is already verification-friendly. The formal input should keep the same signature:

```c
int max_subarray_sum(int n, int *a)
```

The contract binds a logical list `l` for the array contents and requires:

- `1 <= n && n <= INT_MAX`
- `Zlength(l) == n`
- `IntArray::full(a, n, l)`

The postcondition preserves `IntArray::full(a, n, l)` because the implementation is read-only.

## Mathematical specification

The repository does not have an existing public Coq definition for maximum non-empty contiguous subarray sum. This task therefore needs `input/max_subarray_sum.v`.

The Coq spec is written as the same mathematical recurrence as Kadane's algorithm:

- `max_subarray_sum_step cur x = Z.max x (cur + x)`
- `max_subarray_sum_acc cur best rest` scans the remaining list with the same suffix/global-best recurrence.
- `max_subarray_sum_spec l` initializes the recurrence with the first element; for `nil` it returns `0`, but the C contract requires `n >= 1`, so the nil case is unreachable for the target function.

This keeps the C postcondition simple:

```c
__return == max_subarray_sum_spec(l)
```

## Overflow and bounds

The implementation evaluates `cur + a[i]`, so the contract must rule out signed-int overflow for every such update. Since `cur` is a non-empty contiguous subarray sum and `cur + a[i]` is another non-empty contiguous subarray sum, the precondition requires every non-empty contiguous subarray sum to be within the C `int` range:

```c
forall lo, forall hi,
  0 <= lo && lo < hi && hi <= n =>
  INT_MIN <= sum(sublist(lo, hi, l)) &&
  sum(sublist(lo, hi, l)) <= INT_MAX
```

This also bounds singleton elements and the final returned maximum. It is a semantic overflow condition rather than a loop invariant or proof hint.

## Verify-stage boundary

No loop invariant, assertion, bridge assertion, loop-exit assertion, or `which implies` block is included in the generated C file. Those belong to the Verify stage.

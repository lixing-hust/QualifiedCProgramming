# Contract reasoning: array_count_distinct_sorted

## Source semantics

The raw task defines `array_count_distinct_sorted(int n, int *a)` for an input array of length `n`.

- `n >= 0`.
- `a` points to at least `n` integers.
- The input array is sorted in nondecreasing order.
- If `n == 0`, the function returns `0`.
- Otherwise, the function starts with one distinct value and increments the count whenever `a[i] != a[i - 1]`.

Because equal values are contiguous in a nondecreasing array, counting the first element plus adjacent value changes is exactly the number of distinct values.

## Contract shape

The function is read-only with respect to the input array, so the postcondition restores the same `IntArray::full(a, n, l)` predicate.

The contract binds the logical input list `l` with `With l`, requiring:

- `0 <= n`
- `n <= INT_MAX`, to keep the returned count and loop counter within C `int` range
- `Zlength(l) == n`
- sortedness: for every valid adjacent pair, `l[i] <= l[i + 1]`
- `IntArray::full(a, n, l)`

The postcondition states:

- `__return == array_count_distinct_sorted_spec(l)`
- the input array remains unchanged as `IntArray::full(a, n, l)`

The spec function returns `0` on `nil`; otherwise it returns `1` plus the number of adjacent changes in the tail.

## Coq dependency decision

There is an existing `array_count_transitions_spec`, but the target task's natural result is `0` for an empty list and `1 + transitions` for a nonempty list. Writing that conditional directly in the C contract would be less stable than importing a task-specific Coq definition. Therefore this task uses `input/array_count_distinct_sorted.v` with only the mathematical spec needed by the contract.

## Boundary conditions

- `n == 0`: the list is empty by `Zlength(l) == n`, and the Coq spec returns `0`.
- `n > 0`: the first element contributes one distinct value.
- All later increments correspond exactly to adjacent changes.

No loop invariants, assertions, bridge assertions, or verify-stage comments are included in the contract output.

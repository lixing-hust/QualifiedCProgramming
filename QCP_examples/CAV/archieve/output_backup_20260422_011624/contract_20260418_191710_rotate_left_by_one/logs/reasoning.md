## Semantics

Target function: `rotate_left_by_one(int n, int *a)`.

Raw semantics are straightforward:

- `n >= 1`
- `a` owns exactly `n` writable integer cells
- the update is in place
- for every old index `i` with `0 <= i < n - 1`, the new value at `a[i]` is the old value at `a[i + 1]`
- the new value at `a[n - 1]` is the old value at `a[0]`

This is a pure permutation of the input array contents. No arithmetic on element values is performed, so there is no integer-overflow side condition on array contents.

## Boundary Conditions

- `n == 1`: the loop body does not execute and the final write restores `a[0]`, so the array is unchanged
- `n > 1`: the loop shifts every suffix element one slot left, then writes the saved first element into the final slot

The precondition must require `1 <= n` so that `a[0]` is a valid read before the loop and `a[n - 1]` is a valid write after the loop.

## Memory Shape

`IntArray::full(a, n, l)` is sufficient to describe the owned writable array. I also keep `Zlength(l) == n` explicitly, following the existing repository style for array contracts.

The function only mutates `a` and does not allocate memory or access external state.

## Contract Encoding Choice

I do not need a dedicated `.v` bridge file.

Reason:

- the post-state can be written directly as an existential list `l0`
- the rotated relation is expressible with one point equation for the last cell and one quantified equation for indices `0 .. n - 2`
- no reusable higher-level mathematical function is required to state the specification

Chosen postcondition shape:

- `exists l0`
- `Zlength(l0) == n`
- `l0[n - 1] == l[0]`
- `forall i, 0 <= i && i + 1 < n -> l0[i] == l[i + 1]`
- `IntArray::full(a, n, l0)`

This covers both `n == 1` and `n > 1` without a separate case split.

## Verification-Friendliness

The implementation from the raw statement is already verification-friendly:

- save `a[0]` into `first`
- shift with a simple forward loop over `i`
- write `first` back to `a[n - 1]`

No interface rewrite is needed.

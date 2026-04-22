## Semantic summary

Target function: `array_prefix_max(int n, int *a, int *out)`.

The function reads an input array `a[0..n-1]` and writes an output array `out[0..n-1]`.
For each valid index `i`, the final value `out[i]` is the maximum element of the input prefix `a[0..i]`.
The function does not modify `a`.

The implementation has one special case:

- if `n == 0`, it returns immediately and touches neither array cell

For `n > 0`, it initializes `cur = a[0]`, writes `out[0] = a[0]`, then scans from left to right.
At step `i`, `cur` is the maximum of `a[0..i]`, and `out[i]` is assigned that same value.

## Contract shape

Use the standard array contract style:

- `IntArray::full(a, n, la)` for the immutable input array
- `IntArray::full(out, n, lo)` for the writable output array
- an existential post-state list `lr` for the final output contents

The postcondition states:

- `a` is unchanged, so it still owns `la`
- `out` owns `lr`
- `Zlength(lr) == n`
- for every `i` with `0 <= i < n`,
  `lr[i] == max_list_nonempty(sublist(0, i + 1, la))`

This matches the intended prefix-maximum semantics exactly and stays at the contract layer, without introducing verify-stage assertions or loop facts.

## Memory and aliasing

The raw statement only says both arrays have length `n` and that `a` is not modified.
To preserve the program semantics under separation-logic memory ownership, require:

- `IntArray::full(a, n, la) * IntArray::full(out, n, lo)`

This makes `a` and `out` disjoint. That is slightly stronger than allowing aliasing, but it is verification-friendly and still matches the intended two-buffer interface from the problem statement.

## Coq dependency judgment

No new problem-specific `.v` bridge is necessary.

Reason:

- the needed mathematical notion is only the maximum of a nonempty integer list
- the repository already uses `max_list_nonempty : list Z -> Z` in `array_max`
- the prefix semantics can be expressed directly in the C postcondition via `sublist(0, i + 1, la)`

So `input/array_prefix_max.c` can import `array_max` and reuse `max_list_nonempty`, and `input/array_prefix_max.v` should not be created.

## Boundary conditions

- `n` may be `0`; then the quantified postcondition over output indices is vacuous
- when `n > 0`, every prefix `sublist(0, i + 1, la)` is nonempty because `i + 1 >= 1`
- no arithmetic over array values is performed except comparison, so there is no extra integer-overflow precondition

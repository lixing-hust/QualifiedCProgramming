# Contract reasoning: array_reverse_in_place

## Source semantics

The raw task defines `array_reverse_in_place(int n, int *a)` over an integer
array segment of length `n`. The function mutates the caller-provided array in
place and does not allocate auxiliary storage.

The implementation uses two indices:

- `left` starts at `0`
- `right` starts at `n - 1`
- while `left < right`, the two symmetric elements are swapped, then the
  indices move inward

The observable post-state is that every final element at index `i` equals the
initial element at index `n - 1 - i`. This is exactly the list reversal of the
initial contents.

The original interface is already verification-friendly: it is a single target
function, it has no I/O, no hidden global state, and the only memory effect is
the caller-owned array segment.

## Boundary and memory conditions

The natural domain is `0 <= n`. For `n = 0`, `right` becomes `-1`, the loop is
skipped, and the empty array remains the reverse of itself. For `n = 1`, the
loop is also skipped and the single-element array remains unchanged.

The contract binds the initial contents with:

```c
IntArray::full(a, n, l)
```

This gives the function ownership and write permission for exactly the segment
`a[0..n)`. The explicit condition `Zlength(l) == n` records the mathematical
length of the logical list used in the postcondition.

No data-value overflow precondition is needed because the program only reads,
writes, and swaps existing integers. It performs no arithmetic on array values.
Index arithmetic is limited to `n - 1`, `left + 1`, and `right - 1` under
`0 <= n`; these stay within ordinary `int` loop-counter behavior for valid C
`int` inputs.

## Postcondition choice

The postcondition is:

```c
IntArray::full(a, n, rev(l))
```

This states the full in-place reversal result directly, without exposing the
two-pointer algorithm or any intermediate processed-prefix/suffix facts.
Algorithm-specific facts belong to the Verify stage as invariants or
assertions, not to the Contract output.

## Coq dependency decision

The only logical operation needed beyond the array predicate is list reversal
`rev`. Existing CAV contracts, such as `string_reverse_copy`, use `rev(l)`
directly with `verification_list.h`, so no task-specific Coq bridge is needed.

Therefore this task should not create `input/array_reverse_in_place.v`.

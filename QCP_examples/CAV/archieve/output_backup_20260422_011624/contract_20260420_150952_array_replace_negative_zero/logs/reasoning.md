# Contract reasoning: array_replace_negative_zero

## Source semantics

The raw task defines:

```c
void array_replace_negative_zero(int n, int *a)
```

The function scans the first `n` elements of integer array `a` and updates the
array in place:

- if an original element is negative, the final element is `0`
- if an original element is nonnegative, the final element is unchanged

The function returns no value, allocates no memory, and has no I/O or global
state effects.

## Interface decision

The original interface is already verification-friendly:

- `n` explicitly gives the array length
- `a` is caller-owned writable memory
- the update is in place and does not require an output buffer

No interface rewrite is needed.

## Memory model

Use `IntArray::full(a, n, l)` in the precondition to bind the initial logical
array contents.

The precondition states:

- `0 <= n`
- `Zlength(l) == n`
- `IntArray::full(a, n, l)`

The postcondition uses an existential list `l0` for the final array contents.
It preserves the length and states the pointwise update rule for every index in
`[0, n)`.

## Boundary and safety conditions

For `n == 0`, the loop executes zero times. The existential post-state list can
be the original empty logical list, and the pointwise condition is vacuous.

No arithmetic overflow side condition is needed. The implementation only
compares an element with `0` and assigns the constant `0`; it does not perform
integer arithmetic on array elements.

## Coq dependency decision

No `input/array_replace_negative_zero.v` file is needed. The full semantic
property is expressible directly in the C contract with quantification over the
logical array list and the existing `IntArray::full` predicate.

## Verify-stage restraint

Per the contract workflow, the generated C file should contain only the target
function and complete pre/postconditions. It should not include loop invariants,
assertions, bridge assertions, or loop-exit assertions.

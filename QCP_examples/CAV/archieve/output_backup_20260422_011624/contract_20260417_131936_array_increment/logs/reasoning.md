## Target

- Function: `array_increment`
- Raw source: `raw/array_increment.md`

## Semantics

The function updates the input array `a` in place. For each index `i` with `0 <= i < n`, the final value is the original value plus one. The function does not allocate memory and does not return a value.

## Interface / memory decision

The original interface `void array_increment(int n, int *a)` is already verification-friendly:

- `n` gives the logical array length
- `a` is caller-owned writable memory
- the update is in place

So no interface rewrite is needed.

For memory shape, `IntArray::full(a, n, l)` is the right precondition and postcondition frame. It captures ownership of exactly `n` writable integer cells and their logical contents.

## Boundary conditions

- `n >= 0`
- if `n == 0`, the loop executes zero times and the array content is unchanged; the postcondition should still hold
- the problem statement says the array length is exactly `n`, so `Zlength(l) == n` should be stated explicitly

## Overflow condition

The loop performs `a[i] = a[i] + 1`. To keep C signed addition defined, the precondition must ensure every original element can be incremented safely.

The minimal useful condition is:

- for all `i` in `[0, n)`, `l[i] < 2147483647`

No lower-bound side condition is needed for `+ 1`.

## Postcondition shape

No extra Coq file is needed. Existing list notation and array predicates are enough to express the result directly in C contract form.

Use an existential post-state list `l0` with:

- `Zlength(l0) == n`
- for all `i` in `[0, n)`, `l0[i] == l[i] + 1`
- `IntArray::full(a, n, l0)`

This avoids introducing a task-specific logical function such as `inc_list`, so `input/array_increment.v` is unnecessary.

## Verify-stage restraint

Per skill rules, do not add loop invariants, asserts, bridge asserts, or loop-exit assertions in the contract file. Only emit the target function plus full pre/postconditions.

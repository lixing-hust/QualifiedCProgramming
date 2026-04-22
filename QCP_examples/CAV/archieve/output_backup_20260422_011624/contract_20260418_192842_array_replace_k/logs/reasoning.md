## Semantics

Target function: `array_replace_k(int n, int *a, int old_k, int new_k)`.

The function scans the first `n` cells of `a` and updates `a[i]` in place iff the original value equals `old_k`. The semantic result is a list `l0` of the same length as the input logical list `l` such that for every valid index:

- if `l[i] == old_k`, then `l0[i] == new_k`
- if `l[i] != old_k`, then `l0[i] == l[i]`

## Interface And Memory

The original interface is already verification-friendly:

- `n` is the array length
- `a` is the unique mutable array segment
- `old_k` and `new_k` are pure scalar inputs

No interface rewrite is needed. The memory contract is a single `IntArray::full(a, n, l)` footprint. Because the function mutates in place, the postcondition returns a new full ownership predicate over the same array pointer and length.

## Boundary Conditions

- `n >= 0`
- `Zlength(l) == n`
- no additional aliasing constraints are needed because there is only one owned memory block
- no extra arithmetic precondition is needed: the only written value is `new_k`, already of type `int`

When `n == 0`, the loop does not execute and the postcondition is satisfied by choosing `l0 = l`.

## Coq Dependency Decision

No `input/array_replace_k.v` is needed.

Reason:

- the required postcondition is expressible directly in the C contract with `exists l0`
- no reusable problem-specific mathematical function is necessary
- no extra bridge `pre/spec` layer improves clarity here

## Contract Shape

Use:

- `With l`
- `Require 0 <= n && Zlength(l) == n && IntArray::full(a, n, l)`
- `Ensure exists l0, Zlength(l0) == n && ... && IntArray::full(a, n, l0)`

The result relation is written pointwise with an implication pair, avoiding any Verify-stage annotations or auxiliary Coq definitions.

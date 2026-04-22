# Contract reasoning: array_pairwise_sum

## Source summary

Raw markdown specifies:

- Function: `void array_pairwise_sum(int n, int *a, int *b, int *out)`
- Precondition from problem statement: `n >= 0`
- `a`, `b`, and `out` are arrays of exactly length `n`
- For each index `i` with `0 <= i < n`, write `out[i] = a[i] + b[i]`
- The function must not modify `a` or `b`

## Semantic model

Use three logical lists:

- `la` for the initial and final contents of `a`
- `lb` for the initial and final contents of `b`
- `lo` for the initial contents of `out`

The result is represented by an existential list `lr` such that:

- `Zlength(lr) == n`
- for every valid index `i`, `lr[i] == la[i] + lb[i]`
- `a` and `b` are returned with their original list contents
- `out` is returned with `lr`

## Memory model

The contract uses `IntArray::full` for each array:

- `IntArray::full(a, n, la)`
- `IntArray::full(b, n, lb)`
- `IntArray::full(out, n, lo)`

These are separated by `*`, so the contract requires disjoint ownership of the three array regions. This is appropriate for the original function because it reads from `a` and `b` while writing to `out`; allowing aliasing would change observable behavior depending on write order.

For `n == 0`, all three arrays have zero length and the loop performs no writes. The contract remains valid with zero-length `IntArray::full` predicates.

## Integer safety

The C statement `out[i] = a[i] + b[i]` performs signed integer addition. To keep the contract verification-friendly and avoid undefined signed overflow, the precondition requires:

```c
forall i, 0 <= i < n => -2147483648 <= la[i] + lb[i] <= 2147483647
```

No additional restrictions are needed for loop indices beyond `0 <= n`; the implementation iterates while `i < n`.

## Coq dependency decision

No optional `input/array_pairwise_sum.v` is needed. The required postcondition is a direct pointwise relation over existing list and integer expressions and does not need a problem-specific Coq predicate or helper function.

## Verify-stage boundary

This contract intentionally stays at the precondition and postcondition level. Loop proof details and intermediate proof hints belong to the Verify phase.

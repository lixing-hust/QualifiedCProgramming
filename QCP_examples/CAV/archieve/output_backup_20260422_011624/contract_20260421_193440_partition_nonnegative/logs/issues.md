# Contract issues: partition_nonnegative

## Resolved

- The raw interface is already suitable for verification: one target function, caller-owned array
  memory, no I/O, no allocation, and no hidden global state.
- The function mutates the array by swaps, so the contract must preserve element multiset semantics.
  This is expressed with `Permutation(l, l0)` rather than any stable-order relation.
- The partition output does not need a task-specific Coq recursive function. The final shape is
  expressed directly with quantified index conditions over the final list `l0`.

## Open issues

None for the Contract stage.

## Deferred to Verify

- Loop invariants for the two-pointer shrinking interval.
- Any bridge assertions or loop-exit assertions needed to connect the loop state to the final
  partition postcondition.
- Manual Coq lemmas, if needed, for proving that swaps preserve `Permutation` and partition shape.

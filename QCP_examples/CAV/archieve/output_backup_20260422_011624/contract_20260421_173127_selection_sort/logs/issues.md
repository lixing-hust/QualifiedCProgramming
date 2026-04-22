# Contract issues: selection_sort

## Resolved

- The raw implementation was already a single target function with a verification-friendly in-place
  array interface, so no interface rewrite was needed.
- The sorting postcondition needs a nondecreasing-list predicate. A task-local `sorted_z` definition
  was added in `input/selection_sort.v` instead of depending on another problem module.

## Open

- None.

## Verification-stage notes

- Loop invariants will need to capture sorted prefix, suffix minimum selection, and permutation
  preservation through swaps. These are intentionally not included in the Contract output.

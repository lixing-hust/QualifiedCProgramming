# Issues

## Resolved

- Chose a direct quantified postcondition instead of introducing a task-specific Coq recursive spec.
- Preserved the original implementation and interface.
- Preserved read-only array ownership with `IntArray::full(a, n, l)` in both precondition and postcondition.

## Open

- None.

## Notes for Verify

- The postcondition has two cases: no match anywhere, or a returned matching index with no later match.
- No loop invariant, assertion, bridge assertion, or loop-exit assertion has been added in this Contract output.

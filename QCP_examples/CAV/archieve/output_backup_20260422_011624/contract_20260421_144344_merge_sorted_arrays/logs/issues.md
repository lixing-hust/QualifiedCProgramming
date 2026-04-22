# Contract issues: merge_sorted_arrays

## Resolved

- Added a task-specific Coq definition because no existing reusable merge
  function was present in the current input set.
- Used a nested structurally recursive Coq definition so `coqc` accepts the
  merge specification.
- Preserved the raw C implementation unchanged.

## Open

- None.

## Notes for Verify

- The C file intentionally contains no loop invariants or assertions.
- The postcondition includes the exact output list
  `merge_sorted_arrays_spec(la, lb)` and a length fact for that list.
- The precondition uses separating conjunction for `a`, `b`, and `out`, so the
  contract models them as distinct owned buffers.

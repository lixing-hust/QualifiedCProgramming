# Issues

## Summary

- Status: completed
- Blocking issues: none
- Annotation changes required: loop invariant added
- Manual proof required: yes

## Notes

- `symexec` succeeded after adding a loop invariant that tracks `ret` as the maximum of `sublist(0, i, l)`.
- `array_max_proof_manual.v` originally contained two `Admitted.` goals:
  - `proof_of_array_max_entail_wit_2_2`
  - `proof_of_array_max_return_wit_1`
- These were discharged with local list lemmas about:
  - `sublist 0 (Zlength l) l = l`
  - preserving `max_list_nonempty` when appending an element bounded by the current prefix maximum
- Coq compilation for generated files requires the workspace-local auxiliary file on the load path:
  - compile `original/array_max.v` with `-Q $WS/original ""`
  - then compile generated files with both `-Q $WS/original ""` and `-R $WS/coq/generated SimpleC.EE.CAV.verify_20260418_014342_array_max`
- Final result:
  - `goal.v` compiled
  - `proof_auto.v` compiled
  - `proof_manual.v` compiled
  - `goal_check.v` compiled
  - `proof_manual.v` contains no `Admitted.` or added `Axiom`

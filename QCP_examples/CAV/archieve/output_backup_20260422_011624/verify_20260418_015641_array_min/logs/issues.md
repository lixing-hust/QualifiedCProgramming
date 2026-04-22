# Issues

## Summary

- Status: completed
- Blocking issues: none
- Annotation changes required: loop invariant added
- Manual proof required: yes

## Notes

- `symexec` succeeded after adding a loop invariant that tracks `ret` as `min_list_nonempty(sublist(0, i, l))`.
- `array_min_proof_manual.v` originally contained two `Admitted.` goals:
  - `proof_of_array_min_entail_wit_2_2`
  - `proof_of_array_min_return_wit_1`
- The manual proof needed local list lemmas for:
  - `sublist 0 (Zlength l) l = l`
  - preserving `min_list_nonempty` when appending an element greater than or equal to the current prefix minimum
- Coq compilation for generated files required the workspace-local auxiliary file on the load path:
  - compile `original/array_min.v` with `-Q $WS/original ""`
  - then compile generated files with `-Q $WS/original ""` and `-R $WS/coq/generated SimpleC.EE.CAV.verify_20260418_015641_array_min`
- The proof development had three non-blocking compile iterations:
  - swapped `Z.min_glb_l` / `Z.min_glb_r` to `Z.le_min_l` / `Z.le_min_r`
  - rewrote `min_list_nonempty_extend_le` as an induction proof
  - fixed the boundedness branch and normalized a `>=` hypothesis with `lia`
- Final result:
  - `goal.v` compiled
  - `proof_auto.v` compiled
  - `proof_manual.v` compiled
  - `goal_check.v` compiled
  - `proof_manual.v` contains no `Admitted.` or added `Axiom`
  - `coq/` intermediate non-`.v` files were removed

## Symexec log

- Log file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_015641_array_min/logs/qcp_run.log`
- Result: `Successfully finished symbolic execution`

## Verification summary for `array_sum`

- `symexec` succeeded after adding the loop invariant and exit assertion to the annotated C file.
- `array_sum_proof_manual.v` initially contained four `Admitted.` obligations:
  - `proof_of_array_sum_safety_wit_3`
  - `proof_of_array_sum_entail_wit_1`
  - `proof_of_array_sum_entail_wit_2`
  - `proof_of_array_sum_entail_wit_3`
- The main proof issue was `proof_of_array_sum_safety_wit_3`.
  The positive-only `SeparationLogic/examples/sum` pattern was not enough because this contract allows negative array elements, so the proof needed a local signed-prefix bound lemma for `sum`.
- Proof iteration issues resolved during compile:
  - Older Coq syntax in this repo rejected the newer `induction ... as [...]` style and the compact `[lia |]` proof branch form.
  - The safety witness splits into two top-level goals after `entailer!`, so the prefix-bound setup had to be duplicated per branch instead of being introduced once.
  - The loop-exit witness needed rewriting through the retained equality `ret = sum (sublist 0 n_pre l)` before converting `sublist 0 (Zlength l) l` to `l`.
- Final status:
  - `goal.v` compiled
  - `proof_auto.v` compiled
  - `proof_manual.v` compiled
  - `goal_check.v` compiled
  - `proof_manual.v` contains no `Admitted.` or added `Axiom`
  - Non-`.v` files under `coq/` were removed
  - Log file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_020228_array_sum/logs/qcp_run.log`

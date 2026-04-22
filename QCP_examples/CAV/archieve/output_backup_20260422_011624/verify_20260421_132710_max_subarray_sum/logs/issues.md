## Workspace fingerprint placeholder

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the verify workflow requires filling these early and constraining `keywords` to `doc/retrieval/INDEX.md` vocabulary.
- Localization: `logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a non-empty Kadane/max-subarray semantic description and controlled keywords for `dynamic_programming`, `greedy`, `for_loop`, `if`, `array`, `return_max`, `preserve_input`, `loop_invariant`, `case_split`, `range_bound`, `overflow_guard`, `int_range`, and `empty_loop_possible`. After final verification, added `goal_check_passed` and `proof_check_passed` under `verification_status`.
- Result: the fingerprint no longer contains empty placeholder semantic fields and uses only controlled-vocabulary keys and values.

## Initial symexec invocation missing output files

- Phenomenon: the first manual `symexec` run exited with status 1 and `logs/qcp_run.log` only reported `goal file not specified`.
- Trigger: this `symexec` binary requires explicit generated output flags, not just `--input-file` and `--coq-logic-path`.
- Localization: `logs/qcp_run.log`, first run at `2026-04-21T13:29:29+08:00`.
- Fix action: reran with explicit `--goal-file`, `--proof-auto-file`, `--proof-manual-file`, and `--goal-check-file` under `coq/generated/`, plus the workspace logic path `SimpleC.EE.CAV.verify_20260421_132710_max_subarray_sum`.
- Result: the next properly flagged run reached the verifier and generated Coq artifacts.

## Invariant shape too proof-heavy

- Phenomenon: the first successful `symexec` used an invariant where `best == max_subarray_sum_spec(sublist(0, i, l))`; the generated branch witnesses then required proving a direct subarray-maximum characterization of `max_subarray_sum_spec` at every loop step.
- Trigger: the input Coq definition exposes the algorithm through `max_subarray_sum_acc`, not through an all-subarrays max predicate.
- Localization: active annotated file invariant before `for (i = 1; i < n; ++i)` and generated `coq/generated/max_subarray_sum_goal.v` branch entailments.
- Fix action: changed the loop invariant to preserve the future-oriented equality `max_subarray_sum_acc(cur, best, sublist(i, n, l)) == max_subarray_sum_spec(l)`, while keeping the suffix-sum and suffix-maximum facts needed for overflow and branch updates.
- Result: regenerated branch entailments matched one unfolding step of `max_subarray_sum_acc`, and the final proof only needed local `sublist`/sum helper lemmas.

## Missing Extern declaration for accumulator helper

- Phenomenon: after switching the invariant to `max_subarray_sum_acc`, `symexec` failed before VC generation with `Use of undeclared identifier max_subarray_sum_acc`.
- Trigger: `input/max_subarray_sum.v` defines and imports `max_subarray_sum_acc`, but the C annotation parser still requires an `Extern Coq` declaration for identifiers used in annotations.
- Localization: `logs/qcp_run.log`, failed run at `2026-04-21T13:32:10+08:00`; active annotated invariant line using `max_subarray_sum_acc`.
- Fix action: added `/*@ Extern Coq (max_subarray_sum_acc : Z -> Z -> list Z -> Z) */` next to the existing `max_subarray_sum_spec` declaration in the active annotated copy only.
- Result: the next clean `symexec` run succeeded and regenerated `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Stale generated Coq build artifacts

- Phenomenon: early proof inspection showed old processed-prefix goals even after regenerating `.v` files with the accumulator invariant.
- Trigger: stale `.vo` files under `coq/generated/` were still being imported by Coq.
- Localization: `coq/generated/max_subarray_sum_goal.vo` and related non-`.v` artifacts.
- Fix action: deleted all non-`.v` files under `coq/`, then recompiled `original/max_subarray_sum.v`, `goal.v`, and `proof_auto.v` before compiling the manual proof.
- Result: Coq imported the current regenerated `goal.v` shape, and manual proof iteration proceeded on the correct obligations.

## Manual proof obligations

- Phenomenon: fresh `coq/generated/max_subarray_sum_proof_manual.v` contained eight `Admitted.` placeholders: two overflow safety witnesses, four loop-step entailment witnesses, one initialization entailment, and one return witness.
- Trigger: the verifier generated pure list/arithmetic obligations around `sublist`, `sum`, and one-step unfolding of `max_subarray_sum_acc`.
- Localization: `coq/generated/max_subarray_sum_proof_manual.v`.
- Fix action: replaced all placeholders with concrete proofs and local helper lemmas for sublist head decomposition, suffix sum extension, accumulator one-step unfolding, and Kadane suffix-bound preservation.
- Result: `max_subarray_sum_proof_manual.v` compiles, contains no `Admitted.`, and has no new top-level `Axiom`; the full compile replay through `max_subarray_sum_goal_check.v` succeeds.

## Final compile and cleanup

- Phenomenon: verification required full replay, not just successful `symexec` and `proof_manual.v`.
- Trigger: the verify completion criteria require `original`, `goal`, `proof_auto`, `proof_manual`, and `goal_check` compilation with the workspace load path, followed by cleanup of Coq byproducts.
- Localization: compile logs under `logs/compile_*.log`; generated Coq files under `coq/generated/`.
- Fix action: compiled from `/home/yangfp/QualifiedCProgramming/SeparationLogic` using the documented `BASE` and `EXTRA` load paths, confirmed `goal_check` success, then deleted all non-`.v` files under `coq/`.
- Result: final replay succeeded and `coq/` contains only `.v` source files.


# Issues

## Summary

- Status: completed.
- Blocking issues: resolved.
- Annotation changes required: yes.
- Manual proof required: yes.
- Final verification result: `goal_check.v` compiled successfully.

## Fingerprint initialization

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: workspace was freshly initialized before verification.
- Localization: `logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, filled in a non-empty semantic description for first-occurrence binary search, and used only controlled vocabulary keys and values for `keywords`.
- Result: fingerprint records the program shape and final `verification_status` using controlled vocabulary.

## Missing loop invariant and branch bridges

- Phenomenon: the active annotated C initially had no invariant for `while (left < right)`.
- Trigger: the binary-search loop needs a loop-head summary for the half-open candidate interval `[left, right)`, the strict-less excluded prefix, the at-least-target excluded suffix, unchanged parameters, sortedness, and preserved array ownership.
- Localization: `annotated/verify_20260421_041506_binary_search_first.c`, immediately before the loop and around the `mid` branch.
- Fix: added a loop invariant carrying `0 <= left <= right <= n`, unchanged `a/n/target`, sortedness, `Zlength(l) == n`, prefix fact `j < left -> l[j] < target`, suffix fact `right <= j < n -> l[j] >= target`, the empty-interval point fact, and `IntArray::full(a, n, l)`. Added bridge assertions after computing `mid` and in the `else` branch before `right = mid`.
- Result: `symexec` completed successfully and generated fresh Coq files.

## Coq logical path alignment

- Phenomenon: the first successful local `symexec` run generated Coq files whose `Require Import` path included `SimpleC.EE.CAV.output...`, which did not match the compile template for this workspace.
- Trigger: the initial manual command used an overly literal `--coq-logic-path`.
- Localization: generated file headers in `coq/generated/*.v`.
- Fix: cleared the generated files and reran `symexec` with `--coq-logic-path=SimpleC.EE.CAV.verify_20260421_041506_binary_search_first`.
- Result: generated files now compile with the standard workspace load path.

## Manual proof obligations

- Phenomenon: `binary_search_first_proof_manual.v` contained seven `Admitted.` placeholders after successful `symexec`.
- Trigger: midpoint arithmetic, loop-preservation entailments, and the final missing-target return branch require reasoning beyond the generated auto proofs.
- Localization: `coq/generated/binary_search_first_proof_manual.v`.
- Fix: added local quotient-by-2 helper lemmas, proved midpoint bounds and branch invariant preservation using the same pattern as the lower-bound example, used `store_int_undef_store_int` for the local `mid` slot, and proved `return -1` by splitting every index relative to `left`.
- Result: `binary_search_first_proof_manual.v` compiles and contains no `Admitted.` or user-added top-level `Axiom`.

## Return disjunction proof shape

- Phenomenon: the first manual proof compile failed in `proof_of_binary_search_first_return_wit_2` with `Attempt to save an incomplete proof`.
- Trigger: the proof had constructed the universal no-target fact but had not explicitly selected the right disjunct of the postcondition for `__return == -1`.
- Localization: `coq/generated/binary_search_first_proof_manual.v`, final return witness.
- Fix: added `right.` before the final entailment step, then explicitly unfolded the residual pure assertions over the model with `hnf` and supplied the constructed `Hnone` plus the preserved `IntArray.full` fact.
- Result: the manual proof, `goal.v`, `proof_auto.v`, and `goal_check.v` all compile.

## Compile and cleanup

- Phenomenon: successful Coq compilation produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated`.
- Trigger: normal `coqc` output.
- Localization: `output/verify_20260421_041506_binary_search_first/coq/generated`.
- Fix: removed all non-`.v` files under `coq/` after the full compile replay passed.
- Result: only the four generated `.v` files remain under `coq/generated`.

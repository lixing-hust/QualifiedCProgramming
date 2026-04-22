# Verification Issues

## Summary

- Added verification annotations to the active annotated copy for the last-character string scan.
- Regenerated fresh Coq files with `symexec` after each annotation change.
- Completed all manual witnesses in `coq/generated/string_ends_with_char_proof_manual.v`.
- Full compile replay passed for `string_ends_with_char_goal.v`, `string_ends_with_char_proof_auto.v`, `string_ends_with_char_proof_manual.v`, and `string_ends_with_char_goal_check.v`.
- `proof_manual.v` contains no `Admitted.` and no user-added top-level `Axiom`.
- Non-`.v` Coq intermediate files under the current workspace were removed after successful compilation.

## Issue 1: workspace fingerprint was initialized with empty semantic fields

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and `{}` keywords.
- Trigger: the existing workspace had only the scaffolded fingerprint from task initialization.
- Localization: `logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, then filled a non-empty semantic description and controlled-vocabulary keywords for a read-only string search/scan with loop-invariant, case-split, range-bound, and heap-reasoning proof patterns.
- Result: the fingerprint now has non-empty semantic metadata and `verification_status: goal_check_passed`.

## Issue 2: first loop invariant attempt dropped the local `i` permission

- Phenomenon: first `symexec` failed with `Partial Solve Invariant Error` at the loop invariant in `annotated/verify_20260420_183816_string_ends_with_char.c`.
- Trigger: the pre-loop `Assert` recorded `0 < n`, preserved parameters, and array ownership, but did not mention `i == 0`.
- Diagnosis: the assertion transition discarded the stack permission for local variable `i`, while the loop invariant needed `store(i, ..., signed int)`.
- Fix: added `i == 0` to the fall-through assertion before the loop.
- Result: the next `symexec` run passed loop-invariant initialization and reached the post-loop read.

## Issue 3: loop-exit assertion lacked direct bounds for `s[i]`

- Phenomenon: the next `symexec` run failed with `Cannot derive the precondition of Memory Read` at the final `if (s[i] == c)`.
- Trigger: the loop-exit assertion recorded `i == n - 1`, but did not explicitly retain `0 < n` and `0 <= i && i < n`.
- Diagnosis: the memory-read checker did not reconstruct the needed in-bounds fact from `i == n - 1` alone.
- Fix: strengthened the loop-exit assertion with `0 < n` and `0 <= i && i < n`.
- Result: `symexec` succeeded and generated fresh goals.

## Issue 4: loop invariant omitted the original `n < INT_MAX` bound

- Phenomenon: after the first successful `symexec`, `coqc` failed in `proof_of_string_ends_with_char_safety_wit_6` with an incomplete proof; the remaining goal was `i + 1 <= 2147483647`.
- Trigger: the loop context preserved `0 <= i`, `i < n`, and `0 < n`, but not `n < INT_MAX`.
- Diagnosis: the upper bound came from the original precondition and should be preserved through the loop rather than reconstructed in manual proof.
- Fix: added `n < INT_MAX` to the pre-loop assertion, loop invariant, and loop-exit assertion; cleared generated files and reran `symexec`.
- Result: the increment/read safety witnesses moved out of the manual proof set, and the regenerated manual file contained only entailment and return witnesses.

## Issue 5: string terminator witnesses needed explicit length extraction

- Phenomenon: `pre_process; entailer!` left `entail_wit_1`, `entail_wit_3`, `entail_wit_4`, `return_wit_1`, and `return_wit_3` incomplete.
- Trigger: the proof needed to relate `n` to `Zlength l` in order to reason about `Znth` over `l ++ 0 :: nil`.
- Diagnosis: the length fact is available through `CharArray.full`, but must be exposed with `prop_apply CharArray.full_length; Intros`, then converted with `Zlength_correct` and `Zlength_app_cons`.
- Fix: added manual proof steps that derive `Zlength l = n`, use `app_Znth1` for prefix reads and `app_Znth2` for the terminator, and prove the sentinel is unique under the contract's nonzero-prefix property.
- Result: all sentinel and final-comparison witnesses reduced to direct arithmetic/list facts.

## Issue 6: postcondition disjunction uses separation-logic `orp`

- Phenomenon: using lowercase `right; right` in `return_wit_1` failed with `Not an inductive goal with 2 constructors`; using uppercase `Right; Right` then failed to find the expected subterm.
- Trigger: the generated postcondition cases are joined by the separation-logic `||`, not Coq's inductive `or`, and the three-way disjunction is parsed as `(case1 || case2) || case3`.
- Diagnosis: disjunction case selection must use `derivable1_orp_intros1` / `derivable1_orp_intros2` rewrites.
- Fix: used `rewrite <- derivable1_orp_intros2` to select the empty-string third case in `return_wit_1`, and two `rewrite <- derivable1_orp_intros1` steps to select the first case in `return_wit_3`.
- Result: `proof_manual.v` compiled, and the full replay reached `goal_check.v`.

## Trace Files

- Symexec log: `logs/qcp_run.log`
- Compile logs: `logs/compile_goal.log`, `logs/compile_proof_auto.log`, `logs/compile_proof_manual.log`, `logs/compile_goal_check.log`

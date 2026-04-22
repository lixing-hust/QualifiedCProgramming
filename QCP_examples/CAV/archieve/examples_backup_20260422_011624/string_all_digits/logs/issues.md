# Verify Issues

## Fingerprint Initialization

- Phenomenon: the workspace was initialized with an empty `semantic_description` and empty `keywords`.
- Trigger: the verify workflow requires the fingerprint to be filled early, and the user explicitly required reading `doc/retrieval/INDEX.md` before choosing keywords.
- Localization: `logs/workspace_fingerprint.json`.
- Fix: read `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/doc/retrieval/INDEX.md`, filled the semantic summary, and used only controlled vocabulary values: `search`, `while_loop`, `if`, `string`, `array`, `pointer`, `loop_invariant`, `case_split`, `heap_reasoning`, `int_range`, and `empty_loop_possible`.
- Result: the fingerprint now describes the read-only NUL-terminated string scan and, after successful verification, records `verification_status` values `goal_check_passed` and `proof_check_passed`.

## Annotation And Symexec

- Phenomenon: the active annotated C copy initially had no loop invariant before the `while (1)` string scan.
- Trigger: `string_all_digits` returns early on the first non-digit and otherwise exits on the terminator, so the verifier needs a loop-head summary connecting index `i`, the processed prefix, and `string_all_digits_spec`.
- Localization:
  - active annotated file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_035043_string_all_digits.c`
  - reasoning log: `logs/annotation_reasoning.md`
- Fix: added one invariant with a prefix/suffix split `l == app(l1, l2)`, `Zlength(l1) == i`, `string_all_digits_spec(l1) == 1`, preserved the original nonzero-prefix fact, preserved `s == s@pre`, and kept the full `CharArray::full` ownership.
- Result: after clearing stale generated files, `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` completed successfully and regenerated `string_all_digits_goal.v`, `string_all_digits_proof_auto.v`, `string_all_digits_proof_manual.v`, and `string_all_digits_goal_check.v`.

## Manual Proof

- Phenomenon: `coq/generated/string_all_digits_proof_manual.v` contained five generated `Admitted.` obligations after successful symbolic execution.
- Trigger: the loop invariant creates pure list witnesses for invariant initialization, invariant preservation, two bad-character early returns, and the terminator return.
- Localization:
  - `proof_of_string_all_digits_entail_wit_1`
  - `proof_of_string_all_digits_entail_wit_2`
  - `proof_of_string_all_digits_return_wit_1`
  - `proof_of_string_all_digits_return_wit_2`
  - `proof_of_string_all_digits_return_wit_3`
- Fix: adapted the existing verified `string_all_lowercase` proof pattern to the digit bounds `[48,57]`, adding local helper lemmas for appending a valid digit and for appending a character below `48` or above `57`.
- Result: `string_all_digits_proof_manual.v` compiled successfully, contains no remaining `Admitted.`, and contains no new `Axiom`.

## Compile And Cleanup

- Phenomenon: completion requires compiling the original task-specific Coq file plus all generated files with the workspace-qualified logic prefix.
- Trigger: `proof_manual.v` imports `string_all_digits`, and generated files import `SimpleC.EE.CAV.verify_20260420_035043_string_all_digits`.
- Localization: compile log `logs/compile_all.log`.
- Fix: compiled from `/home/yangfp/QualifiedCProgramming/SeparationLogic` using the documented base `-R` load paths, `-Q "$ORIG" ""`, and `-R "$GEN" SimpleC.EE.CAV.verify_20260420_035043_string_all_digits`.
- Result: `original/string_all_digits.v`, `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all compiled successfully. Non-`.v` files under `coq/` were deleted after the successful compile.

## Final Outcome

- `symexec` succeeded on the latest active annotated C file.
- `goal_check.v` compiled successfully.
- `proof_manual.v` contains no `Admitted.` and no new `Axiom`.
- The `coq/` tree contains only `.v` files after cleanup.

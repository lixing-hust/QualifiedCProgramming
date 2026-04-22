# Verify Issues

## Fingerprint Initialization

- Phenomenon: `logs/workspace_fingerprint.json` was initialized with an empty `semantic_description` and empty `keywords`.
- Trigger: the verify workflow requires this metadata to be filled early, and the user explicitly required reading `doc/retrieval/INDEX.md` first.
- Localization: `logs/workspace_fingerprint.json`.
- Fix: read `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/doc/retrieval/INDEX.md`, filled a non-empty semantic description for the read-only null-terminated lowercase-count string scan, and used only controlled vocabulary keys and values. After successful verification, added `verification_status` values `goal_check_passed` and `proof_check_passed`.
- Result: the fingerprint is no longer an empty placeholder and uses only the controlled vocabulary.

## Annotation And Symexec

- Phenomenon: the active annotated file initially had no loop invariant for the `while (1)` string scan.
- Trigger: the verifier needed a loop-head summary for `i`, `cnt`, the processed prefix, and the preserved `CharArray::full` ownership.
- Localization:
  - active annotated file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_154725_string_count_lowercase.c`
  - reasoning log: `logs/annotation_reasoning.md`
- First fix: added an invariant using `cnt == string_count_lowercase_spec(sublist(0, i, l))` plus a loop-exit assertion.
- First result: `symexec` failed before usable VC generation with `Use of undeclared identifier 'sublist'` at the invariant.
- Final fix: replaced the `sublist` invariant with the accepted prefix/suffix form `exists l1 l2`, preserving `l == app(l1, l2)`, `Zlength(l1) == i`, and `cnt == string_count_lowercase_spec(l1)`.
- Final result: after clearing stale generated files, `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` succeeded and regenerated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Manual Proof

- Phenomenon: `coq/generated/string_count_lowercase_proof_manual.v` contained six generated `Admitted.` obligations after successful symbolic execution.
- Trigger: the prefix/suffix invariant generated one integer-range safety witness, invariant initialization, three preservation branches for lowercase / below-97 / above-122 characters, and one terminator-exit witness.
- Localization:
  - `proof_of_string_count_lowercase_safety_wit_7`
  - `proof_of_string_count_lowercase_entail_wit_1`
  - `proof_of_string_count_lowercase_entail_wit_2_1`
  - `proof_of_string_count_lowercase_entail_wit_2_2`
  - `proof_of_string_count_lowercase_entail_wit_2_3`
  - `proof_of_string_count_lowercase_entail_wit_3`
- Fix: added local helper lemmas `string_count_lowercase_spec_range` and `string_count_lowercase_spec_app_single`, then adapted the proven `string_count_not_char` prefix/suffix proof pattern for the lowercase bounds `[97, 122]`.
- Iteration details:
  - fixed the helper lemma base case by destructing both `Z_le_dec` tests explicitly;
  - replaced a brittle generated-hypothesis-name rewrite in the safety witness with a shape match for `Zlength l1 = i`;
  - moved character-bound extraction before `entailer!` in preservation branches;
  - normalized `Znth 0 ((x :: xs) ++ 0 :: nil) 0` to `x` with `change`;
  - expanded compact `destruct ...; [| lia]` syntax into explicit branches.
- Result: `string_count_lowercase_proof_manual.v` compiles and contains no `Admitted.` or top-level `Axiom`.

## Compile And Cleanup

- Phenomenon: completion requires compiling the original task-specific Coq file plus all generated files with the workspace-qualified generated load path.
- Trigger: generated files import `SimpleC.EE.CAV.verify_20260420_154725_string_count_lowercase`, and `proof_manual.v` imports the task-specific `string_count_lowercase` spec from `original/`.
- Localization: compile log `logs/compile_all.log`.
- Fix: compiled from `/home/yangfp/QualifiedCProgramming/SeparationLogic` using the documented base `-R` load paths, `-Q "$ORIG" ""`, and `-R "$GEN" SimpleC.EE.CAV.verify_20260420_154725_string_count_lowercase`.
- Result: `original/string_count_lowercase.v`, `string_count_lowercase_goal.v`, `string_count_lowercase_proof_auto.v`, `string_count_lowercase_proof_manual.v`, and `string_count_lowercase_goal_check.v` all compiled successfully.
- Cleanup: deleted all non-`.v` files under `output/verify_20260420_154725_string_count_lowercase/coq/`.

## Final Outcome

- `symexec` succeeded on the latest active annotated C file.
- `goal_check.v` compiled successfully.
- `proof_manual.v` contains no `Admitted.` and no top-level `Axiom`.
- The `coq/` tree contains only `.v` files after cleanup.

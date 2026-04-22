# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: no
- Manual proof required: yes

## Fingerprint Initialization

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the workspace was freshly initialized with placeholder fingerprint fields.
- Localization: `logs/workspace_fingerprint.json`
- Fix: read `doc/retrieval/INDEX.md` early as requested, then filled in a concrete semantic description and controlled keywords for a first-character string selection function over a preserved `CharArray`.
- Result: the fingerprint has non-empty semantic content, uses only controlled keyword keys and values, and now records `verification_status: goal_check_passed`.

## Annotation Layer

- Phenomenon: the active annotated C file already matched the input C and contained no loop or intermediate control point requiring `Inv` or `Assert`.
- Trigger: `string_starts_with` is a straight single `if` over `s[0]`, so there is no loop summary or bridge assertion needed before symbolic execution.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_032003_string_starts_with.c`
- Fix: left the annotated C unchanged and skipped `logs/annotation_reasoning.md` under the verify skill rule for tasks that do not need annotation edits.
- Result: symbolic execution succeeded from the unchanged active annotated file.

## Symexec Invocation

- Phenomenon: the workspace initially had no generated Coq verification files.
- Trigger: this was a fresh verify workspace, so `symexec` had to be run against the active annotated C file.
- Localization: `logs/qcp_run.log`
- Fix: ran `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` with explicit output paths for `string_starts_with_goal.v`, `string_starts_with_proof_auto.v`, `string_starts_with_proof_manual.v`, and the generated goal-check file, using `--input-file=/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_032003_string_starts_with.c`, `--coq-logic-path=SimpleC.EE.CAV.verify_20260420_032003_string_starts_with`, `--no-exec-info`, and `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE`.
- Result: `logs/qcp_run.log` ends with `Successfully finished symbolic execution`, and the four expected generated `.v` files were produced under `coq/generated/`.

## Manual Proof Parser Issue

- Phenomenon: the first `coqc` replay failed in `string_starts_with_proof_manual.v` with `Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'`.
- Trigger: the proof script used `destruct l as [| x xs]`, which this Coq/parser setup rejected in the current generated proof context.
- Localization: `coq/generated/string_starts_with_proof_manual.v`, line 34 in the first edited version.
- Fix: changed both list splits to the older `destruct l.` style used by existing CAV proofs.
- Result: the parser error disappeared and compilation advanced to the disjunction-selection proof.

## Manual Proof Disjunction Shape

- Phenomenon: the next compile failed with `Error: Not an inductive goal with 2 constructors.`
- Trigger: the initial proof selected disjuncts as if the generated `||` postcondition was right-associated.
- Localization: `coq/generated/string_starts_with_proof_manual.v`, line 44 in the second edited version.
- Fix: adjusted selectors for the left-associated generated shape `(((case1 || case2) || case3) || case4)`: nonempty false uses `left; left; left`, nonempty true uses `left; left; right`, empty false uses `left; right`, and empty true uses `right`.
- Result: the disjunction-selection error disappeared.

## Manual Proof Pure Cleanup

- Phenomenon: after the selector fix, compilation failed with `Wrong bullet -: Current bullet - is not finished`.
- Trigger: `entailer!` reduced the selected branch to a model-level pure conjunction but did not close the remaining arithmetic/list simplification facts by itself.
- Localization: `coq/generated/string_starts_with_proof_manual.v`, first return witness empty-string branch.
- Fix: inspected the branch with `coqtop`, then added `unfold coq_prop, andp; simpl; repeat split; auto; lia` after each `entailer!` in the return witnesses.
- Result: `string_starts_with_proof_manual.v` compiled successfully.

## Compile Replay

- Phenomenon: final verification required compiling all generated Coq files including `goal_check.v`.
- Trigger: the verify workflow completion criteria require the current generated files to compile with the full load-path template.
- Localization: `logs/compile.log`
- Fix: compiled from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the documented base load paths plus `-Q "$ORIG" ""` and `-R "$GEN" SimpleC.EE.CAV.verify_20260420_032003_string_starts_with`.
- Result: `string_starts_with_goal.v`, `string_starts_with_proof_auto.v`, `string_starts_with_proof_manual.v`, and `string_starts_with_goal_check.v` all compiled successfully.

## Cleanup

- Phenomenon: Coq compilation produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Trigger: normal `coqc` compilation output.
- Localization: `coq/generated/`
- Fix: deleted all non-`.v` files under `coq/` after the successful replay.
- Result: only the four generated `.v` files remain under `coq/generated/`.

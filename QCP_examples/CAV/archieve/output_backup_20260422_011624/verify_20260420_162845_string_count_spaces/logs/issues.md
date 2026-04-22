## Verification issues and resolutions, 2026-04-20

### Issue 1: missing loop invariant in active annotated C

- Phenomenon: the active annotated file had a `while (1)` string scan with no `Inv`, so the verifier would not have a stable loop-head relation between `i`, `cnt`, the processed prefix of `l`, and the preserved `CharArray::full` ownership.
- Trigger condition: `string_count_spaces` scans until the terminator and returns a count over the whole logical list, but the postcondition mentions `string_count_spaces_spec(l)`.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_162845_string_count_spaces.c`, immediately before the loop and immediately after loop exit.
- Fix: added a prefix split invariant `exists l1 l2` with `l == app(l1, l2)`, `Zlength(l1) == i`, `cnt == string_count_spaces_spec(l1)`, the nonzero-prefix premise, `s == s@pre`, and preserved `CharArray::full`. Added a minimal loop-exit `Assert` exposing `i == n`, `cnt == string_count_spaces_spec(l)`, and preserved memory.
- Result: after clearing stale generated targets and rerunning `symexec`, `logs/qcp_run.log` ended with `Successfully finished symbolic execution` and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

### Issue 2: manual proof obligations after symexec

- Phenomenon: `coq/generated/string_count_spaces_proof_manual.v` contained five generated `Admitted.` placeholders: `safety_wit_6`, `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, and `entail_wit_3`.
- Trigger condition: the generated verification conditions require pure list/count facts for the accumulator range, appending the current character to the processed prefix, and deriving loop exit index `i == n` from the terminator read plus the nonzero-prefix precondition.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_162845_string_count_spaces/coq/generated/string_count_spaces_proof_manual.v`.
- Fix: added helper lemmas `string_count_spaces_spec_range` and `string_count_spaces_spec_app_single`, then proved the five manual witnesses by adapting the existing string-counting proof pattern to `Z.eq_dec x 32`.
- Result: `string_count_spaces_proof_manual.v` compiles and contains no `Admitted.` proof and no top-level `Axiom` declaration.

### Issue 3: full compile and cleanup required before success

- Phenomenon: verification is not complete until the generated goal, auto proof, manual proof, and goal check all compile under the workspace logical path, and Coq intermediates are removed afterward.
- Trigger condition: normal completion rule for the verify workflow.
- Localization: compile replay log `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_162845_string_count_spaces/logs/compile_full.log` and generated directory `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_162845_string_count_spaces/coq/generated/`.
- Fix: compiled `original/string_count_spaces.v`, `string_count_spaces_goal.v`, `string_count_spaces_proof_auto.v`, `string_count_spaces_proof_manual.v`, and `string_count_spaces_goal_check.v` from `/home/yangfp/QualifiedCProgramming/SeparationLogic` using the documented load-path template. Removed all non-`.v` files under the workspace `coq/` directory afterward.
- Result: the full compile chain exited with status 0, `goal_check.v` compiled, and `find coq -type f ! -name '*.v'` returned no files.

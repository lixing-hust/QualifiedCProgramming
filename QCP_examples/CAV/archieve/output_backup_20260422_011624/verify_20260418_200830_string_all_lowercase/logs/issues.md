# Verify Issues

## Summary

- Status: incomplete
- Blocking issues: unresolved in manual proof
- Annotation changes required: yes
- Manual proof required: yes

## Annotation Layer

- Phenomenon: the first loop invariant encoded the processed-prefix summary as `string_all_lowercase_spec(sublist(0, i, l)) == 1`.
- Trigger: this was the most direct semantic summary for the string scan.
- Localization:
  - active file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260418_200830_string_all_lowercase.c`
  - first failing log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_200830_string_all_lowercase/logs/qcp_run.log`
- Failure text:
  - `fatal error: Use of undeclared identifier 'sublist'`
- Diagnosis:
  - in this workspace, the frontend rejected the nested `string_all_lowercase_spec(sublist(...))` shape even though `sublist` is accepted in other verify examples.
- Fix:
  - replaced the invariant summary with the parser-stable pure fact
    - `forall k < i, 97 <= l[k] <= 122`
  - added a loop-exit assertion fixing `i == n`
- Result:
  - rerunning `symexec` succeeded and generated fresh `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`

## Symexec Invocation

- Phenomenon: the workspace initially had no useful generated Coq artifacts for the revised annotation.
- Trigger: the verify workflow requires a fresh symbolic run after every annotation edit.
- Localization:
  - log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_200830_string_all_lowercase/logs/qcp_run.log`
- Fix:
  - deleted stale generated targets under `coq/generated/`
  - ran `/home/yangfp/QualifiedCProgramming/linux-binary/symexec`
  - used:
    - `--input-file=/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260418_200830_string_all_lowercase.c`
    - `--goal-file=.../string_all_lowercase_goal.v`
    - `--proof-auto-file=.../string_all_lowercase_proof_auto.v`
    - `--proof-manual-file=.../string_all_lowercase_proof_manual.v`
    - `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE`
    - `--coq-logic-path=SimpleC.EE.CAV.verify_20260418_200830_string_all_lowercase`
    - `--no-exec-info`
- Result:
  - symbolic execution completed successfully on the current annotated file

## Manual Proof Iteration

- Phenomenon: the generated `string_all_lowercase_proof_manual.v` contained five unfinished witness theorems.
- Trigger: the boolean string-scan invariant generated pure list obligations that the auto proof did not discharge.
- Localization:
  - file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_200830_string_all_lowercase/coq/generated/string_all_lowercase_proof_manual.v`
- Proof work performed:
  - replaced the generated placeholders with explicit proofs
  - added helper lemmas:
    - `string_all_lowercase_spec_all`
    - `string_all_lowercase_spec_bad_at`
  - rewrote several proof fragments into an older-Coq-compatible style after parser failures
- Stable compile failures encountered:
  - `Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'`
  - `Syntax error: ']' expected after [for_each_goal]`
  - `Wrong bullet -: Current bullet - is not finished`
  - `No matching clauses for match`
- Diagnosis chain:
  - the early failures were pure script-shape incompatibilities and were partially repaired
  - the remaining blocker is `proof_of_string_all_lowercase_entail_wit_2`
  - the script still depends on proof-state-sensitive extraction of the current-character bounds after `entailer!`
  - the current `match goal with` pattern is too fragile for the actual proof state
- Current result:
  - `proof_manual.v` has been substantially filled in and no longer contains `Admitted.`
  - but `proof_manual.v` still does not compile, so verification is not complete

## Compile Status

- `original/string_all_lowercase.v`: pass
- `coq/generated/string_all_lowercase_goal.v`: pass
- `coq/generated/string_all_lowercase_proof_auto.v`: pass
- `coq/generated/string_all_lowercase_proof_manual.v`: fail
- `coq/generated/string_all_lowercase_goal_check.v`: not reached in the final compile chain because `proof_manual.v` failed first

## Cleanup

- Non-`.v` files under `coq/` were deleted after the compile attempts.
- Remaining files under `coq/generated/` are only:
  - `string_all_lowercase_goal.v`
  - `string_all_lowercase_proof_auto.v`
  - `string_all_lowercase_proof_manual.v`
  - `string_all_lowercase_goal_check.v`

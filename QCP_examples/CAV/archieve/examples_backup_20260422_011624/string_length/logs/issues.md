# Verify Issues

## Loop Invariant Placement

- Phenomenon: the first `symexec` rerun failed with:
  - `fatal error: Expected loop after loop invariant.`
- Trigger: I placed the invariant after the `while (1)` header instead of attaching it immediately before the loop statement.
- Localization:
  - active annotated file: `annotated/verify_20260418_151824_string_length.c`
  - failing line was the loop body opening brace after the misplaced invariant block
- Fix:
  - moved `/*@ Inv ... */` to the repository’s accepted placement, directly before `while (1)`
  - kept the invariant content unchanged for the next probe
- Result:
  - `symexec` reran successfully
  - `qcp_run.log` ended with `Successfully finished symbolic execution`

## Manual Proof Goal Overrun

- Phenomenon: the first `coqc` pass for `string_length_proof_manual.v` failed with:
  - `Error: No such goal.`
- Trigger: in `proof_of_string_length_entail_wit_2`, the script called `lia` after `entailer!`, but `entailer!` had already solved the remaining goal.
- Localization:
  - file: `output/verify_20260418_151824_string_length/coq/generated/string_length_proof_manual.v`
  - failing location: the trailing tactic after `entailer!` in `proof_of_string_length_entail_wit_2`
- Fix:
  - removed the redundant trailing `lia`
  - reran the full compile chain from `goal.v` through `goal_check.v`
- Result:
  - `string_length_proof_manual.v` compiled successfully
  - `string_length_goal_check.v` compiled successfully

## Final Outcome

- Added one loop invariant to the active annotated copy.
- Generated fresh Coq files from the current annotated program with `symexec`.
- Completed all manual obligations in `string_length_proof_manual.v`.
- Verified that `proof_manual.v` contains no `Admitted.` and no newly introduced `Axiom`.
- Compiled:
  - `string_length_goal.v`
  - `string_length_proof_auto.v`
  - `string_length_proof_manual.v`
  - `string_length_goal_check.v`
- Deleted all non-`.v` files under `coq/` after the successful compile pass.

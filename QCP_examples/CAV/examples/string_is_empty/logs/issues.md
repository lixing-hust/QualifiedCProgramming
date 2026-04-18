# Verify Issues

## Symexec Invocation Recovery

- Phenomenon: the first manual `symexec` attempts returned exit code `0` but generated an empty `VC_Correct` module, and `qcp_run.log` showed `Start to symbolic execution on program : (null)`.
- Trigger: I initially used `--program-path=...` and an incomplete strategy setup, which does not match the repository's stable `symexec` entrypoint for these C tasks.
- Localization: comparing against `/home/yangfp/QualifiedCProgramming/run-example-linux.sh` showed that the canonical invocation is:
  - `--input-file=<annotated.c>`
  - `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE`
  - `--no-exec-info`
- Fix: cleared the stale generated files and reran `symexec` with the canonical flag set.
- Result: `qcp_run.log` then showed real strategy parsing (`common`, `char_array`) and `Symbolic Execution into function string_is_empty`, and the generated Coq files contained the expected witnesses.

## Annotated Parser Compatibility

- Phenomenon: even after fixing the invocation, char-array verification was still at risk of frontend mismatch because the active annotated program used `'\0'`.
- Trigger: the repository's prior `string_copy` verify run records this frontend as fragile around concrete `'\0'` tokens in annotated char-array code.
- Localization: this function only branches on `s[0] == '\0'`, so the parser-sensitive token was isolated to that comparison.
- Fix: updated only the active annotated copy to use `s[0] == 0`, leaving the contract unchanged.
- Result: the rerun completed symbolic execution successfully and produced the expected char-array witnesses.

## Annotated Working Copy Restoration

- Phenomenon: during the manual rerun setup, the active annotated file was found empty.
- Trigger: the workspace copy had been clobbered during earlier failed iterations.
- Localization: `annotated/verify_20260418_145048_string_is_empty.c` printed as empty while `input/string_is_empty.c` and `original/string_is_empty.c` still contained the correct source.
- Fix: restored the annotated working copy from the task input and kept the parser-safe `0` literal in that restored file.
- Result: the workspace returned to a valid single-source state and could be fed back into `symexec`.

## Manual Proof Compatibility

- Phenomenon: the generated `string_is_empty_proof_manual.v` needed two manual return-witness proofs, and several initial proof scripts failed for Coq-version compatibility rather than logic.
- Trigger conditions:
  - `destruct ... as ...` forms were rejected at this proof location
  - more complex `match goal` patterns were also rejected by the older Ltac parser shape used here
  - `lia` needed explicit `Zlength_nil` / `Zlength_nonneg` bridges before it could solve the branch arithmetic
- Localization: all failures were confined to `output/verify_20260418_145048_string_is_empty/coq/generated/string_is_empty_proof_manual.v`.
- Fix actions:
  - switched to conservative `destruct l.` style
  - used direct branch hypotheses instead of fragile Ltac pattern matching
  - made list-length normalization explicit with `Zlength_nil`, `Zlength_cons`, and `Zlength_nonneg`
  - finished the successful branches after `entailer!` with explicit `simpl; repeat split; auto; lia`
- Result:
  - `proof_manual.v` compiled
  - `goal_check.v` compiled
  - `proof_manual.v` now contains no `Admitted.` and no newly introduced `Axiom`

## Final Outcome

- No additional `Inv`, `Assert`, `which implies`, bridge assertion, or loop-exit assertion was needed for this straight-line function.
- Final generated files:
  - `string_is_empty_goal.v`
  - `string_is_empty_proof_auto.v`
  - `string_is_empty_proof_manual.v`
  - `string_is_empty_goal_check.v`
- Non-`.v` files under `coq/` were deleted after the successful compile pass.

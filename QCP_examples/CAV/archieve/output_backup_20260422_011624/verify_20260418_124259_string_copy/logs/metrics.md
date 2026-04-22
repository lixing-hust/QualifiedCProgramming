# Metrics

- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/string_copy.c`
- Optional input V: not provided
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260418_124259_string_copy.c`
- Workspace: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_124259_string_copy`

## Verification status

- `symexec`: passed on the regenerated annotated file
- `coq/generated/string_copy_goal.v`: generated successfully and compiled successfully
- `coq/generated/string_copy_proof_auto.v`: generated successfully and compiled successfully
- `coq/generated/string_copy_proof_manual.v`:
  - `proof_of_string_copy_entail_wit_1`: complete
  - `proof_of_string_copy_entail_wit_2`: complete
  - `proof_of_string_copy_return_wit_1`: complete
- `goal_check.v`: compiled successfully

## Manual proof counts

- Manual obligations generated: 3
- Manual obligations completed: 3
- Manual obligations blocked: 0

## Compile status

- `goal.v`: success
- `proof_auto.v`: success
- `proof_manual.v`: success
- `goal_check.v`: success

## Outcome

- The workspace now verifies successfully under the strengthened string contract and regenerated VC.
- The earlier “contract gap” diagnosis is obsolete for the current workspace state.

## External Codex Run `20260418_124259`

- Start time: `2026-04-18 12:42:59 +0800`
- End time: `2026-04-18 13:20:50 +0800`
- Wall-clock time (seconds): `2270.73`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `29265032`
- Codex CLI cached input tokens: `28773632`
- Codex CLI output tokens: `85497`
- Codex CLI total tokens: `29350529`
- Approx workspace-authored text tokens: `5291`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_124259_string_copy/logs/codex_prompt_20260418_124259.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_124259_string_copy/logs/codex_stdout_20260418_124259.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_124259_string_copy/logs/codex_stderr_20260418_124259.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_124259_string_copy/logs/codex_last_message_20260418_124259.txt`

## Manual continuation `2026-04-18 14:27:25 +0800`

- Reused the existing workspace and regenerated VC
- Repaired and completed all three manual lemmas
- Recompiled the full chain:
  - `string_copy_goal.v`
  - `string_copy_proof_auto.v`
  - `string_copy_proof_manual.v`
  - `string_copy_goal_check.v`
- Pending cleanup of non-`.v` Coq artifacts was completed after successful compilation

Final Result: Success

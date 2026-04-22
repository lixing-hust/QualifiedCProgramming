# Verify Metrics

- Workspace: `verify_20260418_151824_string_length`
- Function: `string_length`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/string_length.c`
- Input V: `<not provided>`
- Annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260418_151824_string_length.c`

## Annotation

- Annotation iterations: `2`
- Verify annotations added:
  - one loop invariant
- Additional assertions added: `none`

## Symexec

- symexec_start: `2026-04-18 15:21:22 +0800`
- symexec_end: `2026-04-18 15:21:22 +0800`
- symexec_elapsed: `under 1 second`
- symexec_result: `success`
- symexec_log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_151824_string_length/logs/qcp_run.log`

## Proof

- Manual proof obligations: `2`
- Manual proof completed: `2`
- `proof_manual.v` contains `Admitted.`: `no`
- `proof_manual.v` contains newly added `Axiom`: `no`

## Compile

- Compile working directory: `/home/yangfp/QualifiedCProgramming/SeparationLogic`
- Compiled targets:
  - `string_length_goal.v`
  - `string_length_proof_auto.v`
  - `string_length_proof_manual.v`
  - `string_length_goal_check.v`
- Compile result: `success`

## Cleanup

- Non-`.v` files removed from `coq/`: `yes`

## Experience

- Experience updates: none

Final Result: Success

## External Codex Run `20260418_151824`

- Start time: `2026-04-18 15:18:24 +0800`
- End time: `2026-04-18 15:23:41 +0800`
- Wall-clock time (seconds): `316.95`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `1530335`
- Codex CLI cached input tokens: `1415808`
- Codex CLI output tokens: `13189`
- Codex CLI total tokens: `1543524`
- Approx workspace-authored text tokens: `2747`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_151824_string_length/logs/codex_prompt_20260418_151824.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_151824_string_length/logs/codex_stdout_20260418_151824.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_151824_string_length/logs/codex_stderr_20260418_151824.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_151824_string_length/logs/codex_last_message_20260418_151824.txt`

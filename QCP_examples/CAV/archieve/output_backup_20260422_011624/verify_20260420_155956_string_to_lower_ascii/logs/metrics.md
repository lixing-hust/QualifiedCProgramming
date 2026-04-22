# Verify Metrics

## Summary

- Workspace: `output/verify_20260420_155956_string_to_lower_ascii`
- Target function: `string_to_lower_ascii`
- Active annotated C: `annotated/verify_20260420_155956_string_to_lower_ascii.c`
- Input C: `input/string_to_lower_ascii.c`
- Input V: `input/string_to_lower_ascii.v`

## Annotation

- Added loop invariant: yes
- Added Assert / which implies: no
- Annotation reasoning log: `logs/annotation_reasoning.md`

## Symexec

- symexec_start: `2026-04-20T16:02:21+08:00`
- symexec_end: `2026-04-20T16:02:22+08:00`
- symexec_elapsed: `1s`
- symexec_status: `0`
- symexec log: `logs/qcp_run.log`

## Proof

- Manual proof obligations generated: `5`
- Manual proof obligations completed: `5`
- `proof_manual.v` contains `Admitted.`: no
- `proof_manual.v` contains added `Axiom`: no
- Proof reasoning log: `logs/proof_reasoning.md`

## Compile

- compile_start: `2026-04-20T16:10:54+08:00`
- compile_end: `2026-04-20T16:10:59+08:00`
- compile_elapsed: `5s`
- compiled `original/string_to_lower_ascii.v`: yes
- compiled `generated/string_to_lower_ascii_goal.v`: yes
- compiled `generated/string_to_lower_ascii_proof_auto.v`: yes
- compiled `generated/string_to_lower_ascii_proof_manual.v`: yes
- compiled `generated/string_to_lower_ascii_goal_check.v`: yes
- compile log: `logs/coq_compile.log`

## Cleanup

- Non-`.v` files under `coq/` cleaned: yes
- Experience updates: none

Final Result: Success

## External Codex Run `20260420_155956`

- Start time: `2026-04-20 15:59:56 +0800`
- End time: `2026-04-20 16:12:38 +0800`
- Wall-clock time (seconds): `762.23`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `8278800`
- Codex CLI cached input tokens: `7997568`
- Codex CLI output tokens: `26854`
- Codex CLI total tokens: `8305654`
- Approx workspace-authored text tokens: `8747`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_155956_string_to_lower_ascii/logs/codex_prompt_20260420_155956.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_155956_string_to_lower_ascii/logs/codex_stdout_20260420_155956.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_155956_string_to_lower_ascii/logs/codex_stderr_20260420_155956.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_155956_string_to_lower_ascii/logs/codex_last_message_20260420_155956.txt`

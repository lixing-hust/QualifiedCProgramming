# Verify Metrics

## Run

- task_start: `2026-04-18 14:50:49 +0800`
- annotation_edit_required: `yes`
- proof_manual_required: `yes`
- symexec_start: `2026-04-18 14:55:20 +0800`
- symexec_end: `2026-04-18 14:55:20 +0800`
- symexec_elapsed: `0s`
- compile_start: `2026-04-18 15:00:05 +0800`
- compile_end: `2026-04-18 15:01:58 +0800`
- compile_elapsed: `113s`
- task_end: `2026-04-18 15:01:58 +0800`
- total_elapsed: `669s`

## Checks

- `symexec`: success
- `goal.v`: compiled
- `proof_auto.v`: compiled
- `proof_manual.v`: compiled
- `goal_check.v`: compiled
- `proof_manual.v` contains `Admitted.`: `no`
- `proof_manual.v` introduces new `Axiom`: `no`
- `coq/` non-`.v` artifacts cleaned: `yes`

## Notes

- Experience updates: none
- Active annotated file differs from input only in the parser-safe replacement `s[0] == 0` for the verify-stage working copy.

Final Result: Success

## External Codex Run `20260418_145049`

- Start time: `2026-04-18 14:50:49 +0800`
- End time: `2026-04-18 15:03:07 +0800`
- Wall-clock time (seconds): `738.44`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `7213834`
- Codex CLI cached input tokens: `7113728`
- Codex CLI output tokens: `32602`
- Codex CLI total tokens: `7246436`
- Approx workspace-authored text tokens: `3134`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_145048_string_is_empty/logs/codex_prompt_20260418_145049.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_145048_string_is_empty/logs/codex_stdout_20260418_145049.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_145048_string_is_empty/logs/codex_stderr_20260418_145049.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_145048_string_is_empty/logs/codex_last_message_20260418_145049.txt`

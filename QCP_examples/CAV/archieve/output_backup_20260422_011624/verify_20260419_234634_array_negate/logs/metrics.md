# Verify Metrics

## Inputs

- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/array_negate.c`
- Optional input V: `<not provided>`
- Target function: `array_negate`
- Workspace: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_234634_array_negate`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260419_234634_array_negate.c`

## File Counts

- Annotated C lines: `43`
- Generated goal lines: `275`
- Generated proof_auto lines: `32`
- Generated proof_manual lines: `144`
- Generated goal_check lines: `11`
- Annotation reasoning lines: `7`
- Proof reasoning lines: `5`

## Symexec

- symexec_start: `2026-04-19 23:49:02 +0800`
- symexec_end: `2026-04-19 23:49:05 +0800`
- symexec_elapsed: `3` seconds
- symexec_status: `0`
- Generated files: `array_negate_goal.v`, `array_negate_proof_auto.v`, `array_negate_proof_manual.v`, `array_negate_goal_check.v`

## Proof And Compile

- Manual proof obligations completed: `4`
- `proof_manual.v` remaining `Admitted.`: `0`
- `proof_manual.v` newly defined `Axiom`: `0`
- `proof_auto.v` generated `Admitted.` placeholders: `4`
- `goal.v` compile: `passed`
- `proof_auto.v` compile: `passed`
- `proof_manual.v` compile: `passed`
- `goal_check.v` compile: `passed`
- Non-`.v` files under `coq/` after cleanup: `0`

## Experience Updates

- Experience updates: none

Final Result: Success

## External Codex Run `20260419_234634`

- Start time: `2026-04-19 23:46:34 +0800`
- End time: `2026-04-19 23:52:23 +0800`
- Wall-clock time (seconds): `348.89`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `1880343`
- Codex CLI cached input tokens: `1792640`
- Codex CLI output tokens: `14422`
- Codex CLI total tokens: `1894765`
- Approx workspace-authored text tokens: `4445`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_234634_array_negate/logs/codex_prompt_20260419_234634.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_234634_array_negate/logs/codex_stdout_20260419_234634.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_234634_array_negate/logs/codex_stderr_20260419_234634.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_234634_array_negate/logs/codex_last_message_20260419_234634.txt`

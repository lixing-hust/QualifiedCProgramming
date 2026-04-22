# Verify Metrics

## Workspace

- Workspace: `output/verify_20260420_115922_array_first_negative`
- Input C: `input/array_first_negative.c`
- Optional input V: `<not provided>`
- Target function: `array_first_negative`
- Active annotated C: `annotated/verify_20260420_115922_array_first_negative.c`

## Annotation

- Annotation reasoning log: `logs/annotation_reasoning.md`
- Added loop invariant: yes
- Added loop-exit assertion: yes
- Manual contract changes: none

## Symexec

- symexec_start: `2026-04-20 12:01:22 +0800`
- symexec_end: `2026-04-20 12:01:22 +0800`
- symexec_elapsed: `<1 second`
- symexec_exit: `0`
- Generated files:
  - `coq/generated/array_first_negative_goal.v`
  - `coq/generated/array_first_negative_proof_auto.v`
  - `coq/generated/array_first_negative_proof_manual.v`
  - `coq/generated/array_first_negative_goal_check.v`

## Proof

- Manual proof required: no
- `proof_manual.v` contains `Admitted.`: no
- `proof_manual.v` contains newly added `Axiom`: no

## Compile

- compile_start: `2026-04-20 12:01:53 +0800`
- compile_end: `2026-04-20 12:01:56 +0800`
- compile_elapsed: `3 seconds`
- `array_first_negative_goal.v`: passed
- `array_first_negative_proof_auto.v`: passed
- `array_first_negative_proof_manual.v`: passed
- `array_first_negative_goal_check.v`: passed

## Cleanup

- Removed non-`.v` files under `coq/`: yes
- Remaining non-`.v` files under `coq/`: none

## Experience

- Experience updates: none

Final Result: Success

## External Codex Run `20260420_115923`

- Start time: `2026-04-20 11:59:23 +0800`
- End time: `2026-04-20 12:03:16 +0800`
- Wall-clock time (seconds): `233.22`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `1220910`
- Codex CLI cached input tokens: `1135616`
- Codex CLI output tokens: `9092`
- Codex CLI total tokens: `1230002`
- Approx workspace-authored text tokens: `2766`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_115922_array_first_negative/logs/codex_prompt_20260420_115923.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_115922_array_first_negative/logs/codex_stdout_20260420_115923.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_115922_array_first_negative/logs/codex_stderr_20260420_115923.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_115922_array_first_negative/logs/codex_last_message_20260420_115923.txt`

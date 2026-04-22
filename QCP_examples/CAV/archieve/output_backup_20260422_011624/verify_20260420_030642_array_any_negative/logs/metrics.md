# Verify Metrics

## Workspace

- Workspace: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_030642_array_any_negative`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/array_any_negative.c`
- Optional input V: `<not provided>`
- Target function: `array_any_negative`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_030642_array_any_negative.c`
- Annotated C sha256 after edits: `598e37efe7729e8d8ed3e4a6e063be8e27bbc2232984adbc5784159be0dc2849`

## Annotation

- Annotation changes: added one loop invariant and one loop-exit assertion.
- Annotation reasoning log: `logs/annotation_reasoning.md`
- Proof reasoning log: not created because no manual proof theorem was generated.

## Symexec

- symexec_start: `2026-04-20T03:08:55+08:00`
- symexec_end: `2026-04-20T03:08:55+08:00`
- symexec_elapsed: `0s` wall-clock at one-second shell timestamp resolution
- Symexec log: `logs/qcp_run.log`
- Generated files:
  - `coq/generated/array_any_negative_goal.v`
  - `coq/generated/array_any_negative_proof_auto.v`
  - `coq/generated/array_any_negative_proof_manual.v`
  - `coq/generated/array_any_negative_goal_check.v`
- Goal sha256: `2cd85092b1a2a4f4a89fa6e3ec4e7d912b8f30dc799c3be33ee0971423175f5c`
- Goal-check sha256: `3a5f8708ebb1d0d9d488232a8a590c6b93d670dfbc1c187d43a3ca3532a51016`

## Proof And Compile

- Manual proof required: no
- `proof_manual.v` `Admitted.` check: no matches
- `proof_manual.v` top-level `Axiom` check: no matches
- Compile start: `2026-04-20T03:09:25+08:00`
- Compile end: `2026-04-20T03:09:28+08:00`
- Compile log: `logs/compile.log`
- Compiled successfully:
  - `array_any_negative_goal.v`
  - `array_any_negative_proof_auto.v`
  - `array_any_negative_proof_manual.v`
  - `array_any_negative_goal_check.v`

## Cleanup

- Non-`.v` files under `coq/`: cleaned after successful compile replay.
- Experience updates: none

Final Result: Success

## External Codex Run `20260420_030642`

- Start time: `2026-04-20 03:06:42 +0800`
- End time: `2026-04-20 03:11:22 +0800`
- Wall-clock time (seconds): `280.42`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `1128679`
- Codex CLI cached input tokens: `1007616`
- Codex CLI output tokens: `11194`
- Codex CLI total tokens: `1139873`
- Approx workspace-authored text tokens: `3036`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_030642_array_any_negative/logs/codex_prompt_20260420_030642.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_030642_array_any_negative/logs/codex_stdout_20260420_030642.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_030642_array_any_negative/logs/codex_stderr_20260420_030642.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_030642_array_any_negative/logs/codex_last_message_20260420_030642.txt`

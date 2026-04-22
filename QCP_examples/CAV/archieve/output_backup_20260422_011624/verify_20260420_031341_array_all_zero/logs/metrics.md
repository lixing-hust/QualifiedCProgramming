# Verify Metrics

## Workspace

- Workspace: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_031341_array_all_zero`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/array_all_zero.c`
- Optional input V: `<not provided>`
- Target function: `array_all_zero`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_031341_array_all_zero.c`
- Annotated C sha256 after edits: `4211f60e9c6194e0f1903b6ec6d2ad2054515b9e25b1ca4afe9dbb7d3135673f`

## Fingerprint

- Fingerprint updated early: yes
- Retrieval index read before keyword selection: yes
- `semantic_description`: non-empty
- `keywords`: controlled vocabulary only

## Annotation

- Annotation changes: added one loop invariant and one loop-exit assertion.
- Invariant location: `annotated/verify_20260420_031341_array_all_zero.c:21`
- Loop-exit assertion location: `annotated/verify_20260420_031341_array_all_zero.c:34`
- Annotation reasoning log: `logs/annotation_reasoning.md`

## Symexec

- symexec_start: `2026-04-20T03:15:48+08:00`
- symexec_end: `2026-04-20T03:15:48+08:00`
- symexec_elapsed: `0s` wall-clock at one-second shell timestamp resolution
- Symexec status: `0`
- Symexec log: `logs/qcp_run.log`
- Generated files:
  - `coq/generated/array_all_zero_goal.v`
  - `coq/generated/array_all_zero_proof_auto.v`
  - `coq/generated/array_all_zero_proof_manual.v`
  - `coq/generated/array_all_zero_goal_check.v`
- Goal sha256: `7ae83f95630a6a2462f00fbb8589c74d534bcdd1c13a036721ccdd1b51f14af4`
- Goal-check sha256: `2028c4611ba59c15f6ad2821bf2851c96f250cefc7bc09673976f7c9c0ad2448`

## Proof And Compile

- Manual proof required: no generated manual theorem bodies.
- Proof reasoning log: not created because no manual proof theorem was generated.
- `proof_manual.v` `Admitted.` check: no matches
- `proof_manual.v` top-level `Axiom` check: no matches
- Compile start: `2026-04-20T03:16:52+08:00`
- Compile end: `2026-04-20T03:16:55+08:00`
- Compile log: `logs/compile.log`
- Compiled successfully:
  - `array_all_zero_goal.v`
  - `array_all_zero_proof_auto.v`
  - `array_all_zero_proof_manual.v`
  - `array_all_zero_goal_check.v`

## Cleanup

- Non-`.v` files under `coq/`: cleaned after successful compile replay.
- Issues log: `logs/issues.md`
- Experience updates: none

Final Result: Success

## External Codex Run `20260420_031341`

- Start time: `2026-04-20 03:13:41 +0800`
- End time: `2026-04-20 03:18:18 +0800`
- Wall-clock time (seconds): `277.09`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `1405193`
- Codex CLI cached input tokens: `1341696`
- Codex CLI output tokens: `11348`
- Codex CLI total tokens: `1416541`
- Approx workspace-authored text tokens: `2845`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_031341_array_all_zero/logs/codex_prompt_20260420_031341.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_031341_array_all_zero/logs/codex_stdout_20260420_031341.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_031341_array_all_zero/logs/codex_stderr_20260420_031341.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_031341_array_all_zero/logs/codex_last_message_20260420_031341.txt`

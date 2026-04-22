# Verify Metrics

## Workspace

- Workspace: `verify_20260420_032003_string_starts_with`
- Target function: `string_starts_with`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/string_starts_with.c`
- Optional input V: none
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_032003_string_starts_with.c`

## Symexec

- symexec_start: `2026-04-20 03:21:28 +0800`
- symexec_end: `2026-04-20 03:21:28 +0800`
- symexec_elapsed: `0.02` seconds
- symexec_result: `Success`
- symexec_log: `logs/qcp_run.log`

## Annotation

- Annotation edits: none
- Reason: no loop, no intermediate assertion point, and `symexec` succeeded from the initial active annotated C.

## Manual Proof

- Manual proof required: yes
- Manual lemmas completed:
  - `proof_of_string_starts_with_return_wit_1`
  - `proof_of_string_starts_with_return_wit_2`
- `proof_manual.v` contains `Admitted.`: no
- `proof_manual.v` contains new top-level `Axiom`: no
- Proof reasoning log: `logs/proof_reasoning.md`

## Compile

- compile_start: `2026-04-20 03:25:16 +0800`
- goal_ok: `2026-04-20 03:25:17 +0800`
- proof_auto_ok: `2026-04-20 03:25:17 +0800`
- proof_manual_ok: `2026-04-20 03:25:18 +0800`
- goal_check_ok: `2026-04-20 03:25:19 +0800`
- Compile result: `Success`
- Compile log: `logs/compile.log`

## Cleanup

- Coq non-`.v` intermediate files cleaned: yes
- Remaining generated files:
  - `coq/generated/string_starts_with_goal.v`
  - `coq/generated/string_starts_with_proof_auto.v`
  - `coq/generated/string_starts_with_proof_manual.v`
  - `coq/generated/string_starts_with_goal_check.v`

## Experience Updates

- Experience updates: none

Final Result: Success

## External Codex Run `20260420_032003`

- Start time: `2026-04-20 03:20:03 +0800`
- End time: `2026-04-20 03:26:38 +0800`
- Wall-clock time (seconds): `395.51`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `3417178`
- Codex CLI cached input tokens: `3313792`
- Codex CLI output tokens: `16009`
- Codex CLI total tokens: `3433187`
- Approx workspace-authored text tokens: `2938`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_032003_string_starts_with/logs/codex_prompt_20260420_032003.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_032003_string_starts_with/logs/codex_stdout_20260420_032003.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_032003_string_starts_with/logs/codex_stderr_20260420_032003.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_032003_string_starts_with/logs/codex_last_message_20260420_032003.txt`

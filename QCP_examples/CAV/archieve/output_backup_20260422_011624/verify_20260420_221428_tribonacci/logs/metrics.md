# Verify Metrics

## Summary

- Workspace: `output/verify_20260420_221428_tribonacci`
- Target function: `tribonacci`
- Active annotated C: `annotated/verify_20260420_221428_tribonacci.c`
- Input C: `input/tribonacci.c`
- Input V: `input/tribonacci.v`

## Symexec

- symexec_start: `2026-04-20T22:16:45+08:00`
- symexec_end: `2026-04-20T22:16:45+08:00`
- symexec_elapsed: `<1s`
- symexec_exit: `0`
- qcp log: `logs/qcp_run.log`

## Compile Replay

- original: `compile_original_exit=0`
- goal: `compile_goal_exit=0`
- proof_auto: `compile_proof_auto_exit=0`
- proof_manual: `compile_proof_manual_exit=0`
- goal_check: `compile_goal_check_exit=0`

## Proof And Cleanup

- Manual proof required: `yes`
- Manual obligations completed: `6`
- proof_manual contains `Admitted.`: `no`
- proof_manual contains top-level `Axiom`: `no`
- Non-`.v` Coq intermediates cleaned: `yes`
- Experience updates: none

Final Result: Success

## External Codex Run `20260420_221428`

- Start time: `2026-04-20 22:14:28 +0800`
- End time: `2026-04-20 22:24:48 +0800`
- Wall-clock time (seconds): `620.22`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `5974664`
- Codex CLI cached input tokens: `5823232`
- Codex CLI output tokens: `23323`
- Codex CLI total tokens: `5997987`
- Approx workspace-authored text tokens: `4971`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_221428_tribonacci/logs/codex_prompt_20260420_221428.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_221428_tribonacci/logs/codex_stdout_20260420_221428.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_221428_tribonacci/logs/codex_stderr_20260420_221428.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_221428_tribonacci/logs/codex_last_message_20260420_221428.txt`

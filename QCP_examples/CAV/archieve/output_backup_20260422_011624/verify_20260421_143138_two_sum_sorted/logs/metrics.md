# Verify Metrics

## Workspace

- Workspace: `output/verify_20260421_143138_two_sum_sorted`
- Input C: `input/two_sum_sorted.c`
- Optional input V: `<not provided>`
- Target function: `two_sum_sorted`
- Active annotated C: `annotated/verify_20260421_143138_two_sum_sorted.c`

## Symexec

- symexec_start: `2026-04-21T14:36:00+08:00`
- symexec_end: `2026-04-21T14:36:02+08:00`
- symexec_elapsed: approximately `2s`
- symexec_result: `Success`
- qcp_run_log: `output/verify_20260421_143138_two_sum_sorted/logs/qcp_run.log`
- Generated files:
  - `coq/generated/two_sum_sorted_goal.v`
  - `coq/generated/two_sum_sorted_proof_auto.v`
  - `coq/generated/two_sum_sorted_proof_manual.v`
  - `coq/generated/two_sum_sorted_goal_check.v`

## Proof

- Manual proof obligations completed: `8`
- Manual proof file: `coq/generated/two_sum_sorted_proof_manual.v`
- Manual proof status: `coqc passed`
- Manual proof `Admitted.` check: `none`
- Manual proof added `Axiom` check: `none`

## Compile

- compile_start: `2026-04-21T14:42:13+08:00`
- compile_end: `2026-04-21T14:42:20+08:00`
- compile_elapsed: approximately `7s`
- `two_sum_sorted_goal.v`: `passed`
- `two_sum_sorted_proof_auto.v`: `passed`
- `two_sum_sorted_proof_manual.v`: `passed`
- `two_sum_sorted_goal_check.v`: `passed`
- compile_log: `output/verify_20260421_143138_two_sum_sorted/logs/coq_compile.log`

## Cleanup

- Coq non-`.v` artifact cleanup: `completed`
- Remaining files under `coq/generated/`: `two_sum_sorted_goal.v`, `two_sum_sorted_proof_auto.v`, `two_sum_sorted_proof_manual.v`, `two_sum_sorted_goal_check.v`

## Experience Updates

- Experience updates: none
- Reason: the user execution rule restricted writes to the existing workspace.

Final Result: Success

## External Codex Run `20260421_143138`

- Start time: `2026-04-21 14:31:38 +0800`
- End time: `2026-04-21 14:43:44 +0800`
- Wall-clock time (seconds): `725.62`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `7096226`
- Codex CLI cached input tokens: `6919296`
- Codex CLI output tokens: `28349`
- Codex CLI total tokens: `7124575`
- Approx workspace-authored text tokens: `11094`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_143138_two_sum_sorted/logs/codex_prompt_20260421_143138.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_143138_two_sum_sorted/logs/codex_stdout_20260421_143138.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_143138_two_sum_sorted/logs/codex_stderr_20260421_143138.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_143138_two_sum_sorted/logs/codex_last_message_20260421_143138.txt`

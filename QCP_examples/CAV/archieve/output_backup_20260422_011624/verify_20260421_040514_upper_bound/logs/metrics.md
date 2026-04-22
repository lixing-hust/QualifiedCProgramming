# Verify Metrics

## Workspace

- Workspace: `verify_20260421_040514_upper_bound`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/upper_bound.c`
- Optional input V: none
- Target function: `upper_bound`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_040514_upper_bound.c`

## Symexec

- Failed symexec attempts before final success: `2`
- Failure signature: `The array i_94 of Znth is not a list type. The type is Z`
- Final symexec_start: `2026-04-21T04:09:18+08:00`
- Final symexec_end: `2026-04-21T04:09:20+08:00`
- Final symexec_elapsed_seconds: `2`
- Final symexec_status: `0`
- Final symexec log: `logs/qcp_run.log`

## Proof And Compile

- Manual proof obligations completed: `6`
- Manual proof file: `coq/generated/upper_bound_proof_manual.v`
- Manual proof contains `Admitted.`: `no`
- Manual proof contains added top-level `Axiom`: `no`
- Compile_start: `2026-04-21T04:10:35+08:00`
- Compile_end: `2026-04-21T04:10:41+08:00`
- Compile_elapsed_seconds: `6`
- Compiled files: `upper_bound_goal.v`, `upper_bound_proof_auto.v`, `upper_bound_proof_manual.v`, `upper_bound_goal_check.v`
- Compile log: `logs/compile_full.log`
- Non-`.v` files remaining under `coq/`: `0`

## Notes

- Active annotated postcondition workaround: replaced the original disjunctive indexed upper_bound condition with the stronger sorted-suffix condition in the active annotated verification copy only. This avoids a frontend return-witness generation failure and implies the original disjunction.
- Experience updates: none

Final Result: Success

## External Codex Run `20260421_040515`

- Start time: `2026-04-21 04:05:15 +0800`
- End time: `2026-04-21 04:12:24 +0800`
- Wall-clock time (seconds): `429.38`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `2740710`
- Codex CLI cached input tokens: `2637312`
- Codex CLI output tokens: `16865`
- Codex CLI total tokens: `2757575`
- Approx workspace-authored text tokens: `7599`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_040514_upper_bound/logs/codex_prompt_20260421_040515.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_040514_upper_bound/logs/codex_stdout_20260421_040515.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_040514_upper_bound/logs/codex_stderr_20260421_040515.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_040514_upper_bound/logs/codex_last_message_20260421_040515.txt`

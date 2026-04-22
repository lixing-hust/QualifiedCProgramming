# Verify Metrics

## Workspace

- Workspace: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010149_array_longest_nonnegative_run`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/array_longest_nonnegative_run.c`
- Input V: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/array_longest_nonnegative_run.v`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260422_010149_array_longest_nonnegative_run.c`
- Target function: `array_longest_nonnegative_run`

## Symexec

- symexec_start: `2026-04-22 01:03:42 CST`
- symexec_end: `2026-04-22 01:03:43 CST`
- symexec_elapsed_seconds: `1`
- symexec_status: `0`
- qcp log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010149_array_longest_nonnegative_run/logs/qcp_run.log`
- Generated Coq:
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010149_array_longest_nonnegative_run/coq/generated/array_longest_nonnegative_run_goal.v`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010149_array_longest_nonnegative_run/coq/generated/array_longest_nonnegative_run_proof_auto.v`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010149_array_longest_nonnegative_run/coq/generated/array_longest_nonnegative_run_proof_manual.v`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010149_array_longest_nonnegative_run/coq/generated/array_longest_nonnegative_run_goal_check.v`

## Manual Proof

- Manual obligations generated: `5`
- Manual obligations completed: `5`
- `proof_manual.v` contains `Admitted.`: `no`
- `proof_manual.v` contains new `Axiom`: `no`
- Main local helper added: `sublist_head_cons_Z`

## Compile Replay

- compile_start: `2026-04-22 01:05:25 CST`
- compile_end: `2026-04-22 01:05:31 CST`
- compile_elapsed_seconds: `6`
- compile_status: `0`
- Compile logs:
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010149_array_longest_nonnegative_run/logs/compile_original.log`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010149_array_longest_nonnegative_run/logs/compile_goal.log`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010149_array_longest_nonnegative_run/logs/compile_proof_auto.log`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010149_array_longest_nonnegative_run/logs/compile_proof_manual.log`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010149_array_longest_nonnegative_run/logs/compile_goal_check.log`

## Cleanup And Experience

- Non-`.v` files under workspace `coq/` after cleanup: `0`
- Experience updates: none
Final Result: Success

## External Codex Run `20260422_010150`

- Start time: `2026-04-22 01:01:50 +0800`
- End time: `2026-04-22 01:07:09 +0800`
- Wall-clock time (seconds): `319.25`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `2627682`
- Codex CLI cached input tokens: `2511872`
- Codex CLI output tokens: `13521`
- Codex CLI total tokens: `2641203`
- Approx workspace-authored text tokens: `5173`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010149_array_longest_nonnegative_run/logs/codex_prompt_20260422_010150.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010149_array_longest_nonnegative_run/logs/codex_stdout_20260422_010150.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010149_array_longest_nonnegative_run/logs/codex_stderr_20260422_010150.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010149_array_longest_nonnegative_run/logs/codex_last_message_20260422_010150.txt`

# Verify Metrics

## Verification Run

- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/partition_nonnegative.c`
- Optional input V: `<not provided>`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_193642_partition_nonnegative.c`
- Workspace: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_193642_partition_nonnegative`
- Target function: `partition_nonnegative`
- symexec_start: `2026-04-21 19:38:50 +0800`
- symexec_end: `2026-04-21 19:38:52 +0800`
- symexec_elapsed: `about 2 seconds`
- symexec_result: `success`
- Generated Coq files:
  - `coq/generated/partition_nonnegative_goal.v`
  - `coq/generated/partition_nonnegative_proof_auto.v`
  - `coq/generated/partition_nonnegative_proof_manual.v`
  - `coq/generated/partition_nonnegative_goal_check.v`
- Manual obligations completed:
  - `proof_of_partition_nonnegative_entail_wit_1`
  - `proof_of_partition_nonnegative_entail_wit_2_1`
- Compile replay: `success`
- Compile end: `2026-04-21 19:52:31 +0800`
- Cleanup: `find coq -type f ! -name '*.v'` returned no files after deletion
- Manual proof grep: no `Admitted.` and no top-level `Axiom` in `partition_nonnegative_proof_manual.v`
- Experience updates: none

Final Result: Success

## External Codex Run `20260421_193642`

- Start time: `2026-04-21 19:36:42 +0800`
- End time: `2026-04-21 19:54:06 +0800`
- Wall-clock time (seconds): `1043.59`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `16598915`
- Codex CLI cached input tokens: `16371968`
- Codex CLI output tokens: `39615`
- Codex CLI total tokens: `16638530`
- Approx workspace-authored text tokens: `8161`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_193642_partition_nonnegative/logs/codex_prompt_20260421_193642.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_193642_partition_nonnegative/logs/codex_stdout_20260421_193642.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_193642_partition_nonnegative/logs/codex_stderr_20260421_193642.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_193642_partition_nonnegative/logs/codex_last_message_20260421_193642.txt`

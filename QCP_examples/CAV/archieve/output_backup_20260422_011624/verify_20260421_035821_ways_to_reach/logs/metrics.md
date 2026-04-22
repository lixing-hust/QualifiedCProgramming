# Verify Metrics

## Manual Verify Run

- Workspace: `verify_20260421_035821_ways_to_reach`
- Target function: `ways_to_reach`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/ways_to_reach.c`
- Input V: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/ways_to_reach.v`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_035821_ways_to_reach.c`
- Started: `2026-04-21 03:58:21 +0800`
- Completed: `2026-04-21 04:02:24 +0800`

## Symexec

- symexec_start: `2026-04-21 04:00:36 +0800`
- symexec_end: `2026-04-21 04:00:36 +0800`
- symexec_elapsed: `0` seconds
- symexec_status: `0`
- qcp log: `logs/qcp_run.log`

## Coq Compile

- compile_start: `2026-04-21 04:01:51 +0800`
- compile_end: `2026-04-21 04:01:54 +0800`
- compile_status: `0`
- compile log: `logs/compile_full.log`
- Compiled files:
  - `original/ways_to_reach.v`
  - `coq/generated/ways_to_reach_goal.v`
  - `coq/generated/ways_to_reach_proof_auto.v`
  - `coq/generated/ways_to_reach_proof_manual.v`
  - `coq/generated/ways_to_reach_goal_check.v`

## Artifact Checks

- `coq/generated/ways_to_reach_proof_manual.v` contains no `Admitted.`.
- `coq/generated/ways_to_reach_proof_manual.v` contains no top-level `Axiom`.
- `coq/` non-`.v` intermediate artifacts were removed after successful compile.
- Experience updates: none

Final Result: Success

## External Codex Run `20260421_035821`

- Start time: `2026-04-21 03:58:21 +0800`
- End time: `2026-04-21 04:03:25 +0800`
- Wall-clock time (seconds): `304.19`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `1823117`
- Codex CLI cached input tokens: `1741696`
- Codex CLI output tokens: `13609`
- Codex CLI total tokens: `1836726`
- Approx workspace-authored text tokens: `3604`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_035821_ways_to_reach/logs/codex_prompt_20260421_035821.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_035821_ways_to_reach/logs/codex_stdout_20260421_035821.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_035821_ways_to_reach/logs/codex_stderr_20260421_035821.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_035821_ways_to_reach/logs/codex_last_message_20260421_035821.txt`

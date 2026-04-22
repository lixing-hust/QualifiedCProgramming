# Verify Metrics

## Workspace

- Workspace: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_113742_array_count_even`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/array_count_even.c`
- Input V: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/array_count_even.v`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_113742_array_count_even.c`
- Target function: `array_count_even`

## Annotation

- Added loop invariant: yes
- Added loop-exit assertion: yes
- Annotation reasoning log: `logs/annotation_reasoning.md`

## Symexec

- symexec_start: `2026-04-20 11:39:28 +0800`
- symexec_end: `2026-04-20 11:39:28 +0800`
- symexec_elapsed: `0` seconds
- symexec_status: `0`
- symexec log: `logs/qcp_run.log`
- Generated files:
  - `coq/generated/array_count_even_goal.v`
  - `coq/generated/array_count_even_proof_auto.v`
  - `coq/generated/array_count_even_proof_manual.v`
  - `coq/generated/array_count_even_goal_check.v`

## Manual Proof

- Manual proof required: yes
- Manual obligations completed: `5`
- Helper lemmas added in `proof_manual.v`: `2`
- `Admitted.` in `proof_manual.v`: none
- New `Axiom` in `proof_manual.v`: none
- Proof reasoning log: `logs/proof_reasoning.md`

## Compile

- Compile start: `2026-04-20 11:42:08 +0800`
- Compile end: `2026-04-20 11:42:12 +0800`
- Compile elapsed: `4` seconds
- Compile log: `logs/compile.log`
- Compiled successfully:
  - `original/array_count_even.v`
  - `coq/generated/array_count_even_goal.v`
  - `coq/generated/array_count_even_proof_auto.v`
  - `coq/generated/array_count_even_proof_manual.v`
  - `coq/generated/array_count_even_goal_check.v`

## Cleanup

- Non-`.v` files under `coq/` after cleanup: none

## Experience

- Experience updates: none
- Reason: the user execution rule restricted writes to the existing workspace; no repository-level experience documents were modified.

Final Result: Success

## External Codex Run `20260420_113742`

- Start time: `2026-04-20 11:37:42 +0800`
- End time: `2026-04-20 11:43:33 +0800`
- Wall-clock time (seconds): `351.54`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `1903498`
- Codex CLI cached input tokens: `1753984`
- Codex CLI output tokens: `15081`
- Codex CLI total tokens: `1918579`
- Approx workspace-authored text tokens: `4072`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_113742_array_count_even/logs/codex_prompt_20260420_113742.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_113742_array_count_even/logs/codex_stdout_20260420_113742.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_113742_array_count_even/logs/codex_stderr_20260420_113742.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_113742_array_count_even/logs/codex_last_message_20260420_113742.txt`

# Verify Metrics

## Workspace

- Workspace: `output/verify_20260420_114610_array_sum_even_indices`
- Target function: `array_sum_even_indices`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/array_sum_even_indices.c`
- Input V: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/array_sum_even_indices.v`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_114610_array_sum_even_indices.c`

## Annotation

- Fingerprint updated: yes
- Loop invariant added: yes
- Loop-exit assertion added: yes
- Annotation reasoning log: `logs/annotation_reasoning.md`

## Symexec

- symexec_start: `2026-04-20 11:48:01 +0800`
- symexec_end: `2026-04-20 11:48:01 +0800`
- symexec_elapsed: `<1s`
- symexec_log: `logs/qcp_run.log`
- symexec_result: `Success`

## Proof And Compile

- Manual proof obligations generated: `5`
- Manual proof obligations completed: `5`
- `proof_manual.v` contains `Admitted.`: no
- `proof_manual.v` contains newly added `Axiom`: no
- Coq compile command directory: `/home/yangfp/QualifiedCProgramming/SeparationLogic`
- `original/array_sum_even_indices.v` compiled: yes
- `generated/array_sum_even_indices_goal.v` compiled: yes
- `generated/array_sum_even_indices_proof_auto.v` compiled: yes
- `generated/array_sum_even_indices_proof_manual.v` compiled: yes
- `generated/array_sum_even_indices_goal_check.v` compiled: yes
- Final compile completed: `2026-04-20 11:56:49 +0800`

## Cleanup

- Non-`.v` files under `coq/` cleaned: yes
- Experience updates: none

Final Result: Success

## External Codex Run `20260420_114610`

- Start time: `2026-04-20 11:46:10 +0800`
- End time: `2026-04-20 11:58:00 +0800`
- Wall-clock time (seconds): `710.16`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `7872129`
- Codex CLI cached input tokens: `7725952`
- Codex CLI output tokens: `27920`
- Codex CLI total tokens: `7900049`
- Approx workspace-authored text tokens: `6509`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_114610_array_sum_even_indices/logs/codex_prompt_20260420_114610.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_114610_array_sum_even_indices/logs/codex_stdout_20260420_114610.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_114610_array_sum_even_indices/logs/codex_stderr_20260420_114610.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_114610_array_sum_even_indices/logs/codex_last_message_20260420_114610.txt`

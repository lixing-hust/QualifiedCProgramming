# Verify Metrics

## Summary

- Workspace: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_024109_power_nonnegative`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/power_nonnegative.c`
- Input V: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/power_nonnegative.v`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_024109_power_nonnegative.c`
- Target function: `power_nonnegative`
- Annotation changes: added one loop invariant before `for (i = 0; i < exp; ++i)`.
- Manual proof changes: added helper lemma `power_nonnegative_z_succ` and completed three generated manual witness lemmas.
- Experience updates: none. The user explicitly constrained writes to the existing workspace for this run.

## Symexec

- symexec_start: `2026-04-21 02:43:13 +0800`
- symexec_end: `2026-04-21 02:43:13 +0800`
- symexec_elapsed: `0.05` seconds
- symexec_log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_024109_power_nonnegative/logs/qcp_run.log`
- symexec_result: success; generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Compile

- compile_start: `2026-04-21 02:45:31 +0800`
- compile_end: `2026-04-21 02:45:34 +0800`
- compile_log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_024109_power_nonnegative/logs/compile.log`
- compiled_spec: `original/power_nonnegative.v`
- compiled_generated_files: `power_nonnegative_goal.v`, `power_nonnegative_proof_auto.v`, `power_nonnegative_proof_manual.v`, `power_nonnegative_goal_check.v`
- compile_result: success

## Final Checks

- `power_nonnegative_proof_manual.v` contains no `Admitted.`
- `power_nonnegative_proof_manual.v` contains no newly introduced `Axiom`.
- `goal_check.v` compiled successfully.
- `coq/` cleanup: complete; only `.v` files remain under `coq/`.

Final Result: Success

## External Codex Run `20260421_024110`

- Start time: `2026-04-21 02:41:10 +0800`
- End time: `2026-04-21 02:47:27 +0800`
- Wall-clock time (seconds): `377.18`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `2723077`
- Codex CLI cached input tokens: `2639616`
- Codex CLI output tokens: `14553`
- Codex CLI total tokens: `2737630`
- Approx workspace-authored text tokens: `2839`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_024109_power_nonnegative/logs/codex_prompt_20260421_024110.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_024109_power_nonnegative/logs/codex_stdout_20260421_024110.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_024109_power_nonnegative/logs/codex_stderr_20260421_024110.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_024109_power_nonnegative/logs/codex_last_message_20260421_024110.txt`

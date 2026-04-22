# Verify Metrics

## Manual Verify Run

- Workspace: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_005007_array_intersection_count_sorted`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260422_005007_array_intersection_count_sorted.c`
- Target function: `array_intersection_count_sorted`
- Fingerprint update: completed early after reading `doc/retrieval/INDEX.md`
- Annotation iterations: `1`
- Symexec runs: `1`
- symexec_start: `2026-04-22T00:52:15+08:00`
- symexec_end: `2026-04-22T00:52:22+08:00`
- symexec_elapsed: `7s`
- symexec_status: `0`
- Symexec final result: success; generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check`
- Manual proof obligations completed: `6`
- Compile replay: success for `original/array_intersection_count_sorted.v`, generated `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`
- Manual proof grep: no `Admitted.` and no top-level `Axiom` in `array_intersection_count_sorted_proof_manual.v`
- Coq cleanup: removed all non-`.v` artifacts under workspace `coq/`
- Experience updates: none, because this run was constrained to work only inside the existing workspace

Final Result: Success

## External Codex Run `20260422_005007`

- Start time: `2026-04-22 00:50:07 +0800`
- End time: `2026-04-22 00:59:43 +0800`
- Wall-clock time (seconds): `575.67`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `5533608`
- Codex CLI cached input tokens: `5400064`
- Codex CLI output tokens: `21619`
- Codex CLI total tokens: `5555227`
- Approx workspace-authored text tokens: `12100`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_005007_array_intersection_count_sorted/logs/codex_prompt_20260422_005007.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_005007_array_intersection_count_sorted/logs/codex_stdout_20260422_005007.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_005007_array_intersection_count_sorted/logs/codex_stderr_20260422_005007.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_005007_array_intersection_count_sorted/logs/codex_last_message_20260422_005007.txt`

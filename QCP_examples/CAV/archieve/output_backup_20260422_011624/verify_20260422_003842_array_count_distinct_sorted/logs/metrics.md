# Verify Metrics

## Manual Verify Run

- Workspace: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_003842_array_count_distinct_sorted`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260422_003842_array_count_distinct_sorted.c`
- Target function: `array_count_distinct_sorted`
- Fingerprint update: completed early after reading `doc/retrieval/INDEX.md`
- Annotation iterations: `1`
- Symexec runs: `2`
- Symexec first run result: failed before parsing because long options were passed without `=`
- Symexec final result: success; generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check`
- Manual proof obligations completed: `5`
- Compile replay: success for `original/array_count_distinct_sorted.v`, generated `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`
- Manual proof grep: no `Admitted.` and no `Axiom`
- Coq cleanup: removed all non-`.v` artifacts under workspace `coq/`
- Experience updates: none

Final Result: Success

## External Codex Run `20260422_003842`

- Start time: `2026-04-22 00:38:42 +0800`
- End time: `2026-04-22 00:48:04 +0800`
- Wall-clock time (seconds): `561.59`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `3907930`
- Codex CLI cached input tokens: `3708032`
- Codex CLI output tokens: `22432`
- Codex CLI total tokens: `3930362`
- Approx workspace-authored text tokens: `6211`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_003842_array_count_distinct_sorted/logs/codex_prompt_20260422_003842.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_003842_array_count_distinct_sorted/logs/codex_stdout_20260422_003842.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_003842_array_count_distinct_sorted/logs/codex_stderr_20260422_003842.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_003842_array_count_distinct_sorted/logs/codex_last_message_20260422_003842.txt`

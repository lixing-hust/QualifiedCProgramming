# Verify Metrics

- Workspace: `output/verify_20260421_140942_remove_duplicates_sorted`
- Target function: `remove_duplicates_sorted`
- Input C: `input/remove_duplicates_sorted.c`
- Input V: `input/remove_duplicates_sorted.v`
- Active annotated C: `annotated/verify_20260421_140942_remove_duplicates_sorted.c`
- symexec_start: `2026-04-21 14:16:00 +0800`
- symexec_end: `2026-04-21 14:16:02 +0800`
- symexec_elapsed: `about 2 seconds`
- symexec result: success; generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.
- Manual proof obligations: `5`
- Manual proof result: success; `remove_duplicates_sorted_proof_manual.v` has no `Admitted.` and no local `Axiom`.
- Full compile result: success; `original/remove_duplicates_sorted.v`, `remove_duplicates_sorted_goal.v`, `remove_duplicates_sorted_proof_auto.v`, `remove_duplicates_sorted_proof_manual.v`, and `remove_duplicates_sorted_goal_check.v` compiled with the documented load-path template.
- Cleanup: removed all non-`.v` files under workspace `coq/`.
- Experience updates: none; the user required work only inside this existing workspace.

Final Result: Success

## External Codex Run `20260421_140942`

- Start time: `2026-04-21 14:09:42 +0800`
- End time: `2026-04-21 14:29:29 +0800`
- Wall-clock time (seconds): `1186.71`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `20630839`
- Codex CLI cached input tokens: `20229888`
- Codex CLI output tokens: `42703`
- Codex CLI total tokens: `20673542`
- Approx workspace-authored text tokens: `54604`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_140942_remove_duplicates_sorted/logs/codex_prompt_20260421_140942.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_140942_remove_duplicates_sorted/logs/codex_stdout_20260421_140942.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_140942_remove_duplicates_sorted/logs/codex_stderr_20260421_140942.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_140942_remove_duplicates_sorted/logs/codex_last_message_20260421_140942.txt`

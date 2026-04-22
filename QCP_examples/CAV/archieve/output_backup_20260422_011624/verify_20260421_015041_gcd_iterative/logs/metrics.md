# Metrics

## Verify Run 2026-04-21

- Workspace: `output/verify_20260421_015041_gcd_iterative`
- Input C: `input/gcd_iterative.c`
- Input V: `input/gcd_iterative.v`
- Active annotated C: `annotated/verify_20260421_015041_gcd_iterative.c`
- Target function: `gcd_iterative`
- Fingerprint initialized: yes
- Annotation edits: yes; added the Euclidean gcd loop invariant
- symexec_start: `2026-04-21T01:52:27+08:00`
- symexec_end: `2026-04-21T01:52:27+08:00`
- symexec_elapsed: less than 1 second
- Symexec result: success
- Generated Coq result: success; generated `goal`, `proof_auto`, `proof_manual`, and `goal_check`
- Manual proof required: yes; three manual witness lemmas
- Manual proof result: success
- Full compile replay: success
- `goal_check.v` compiled: yes
- `proof_manual.v` contains `Admitted.`: no
- `proof_manual.v` contains added top-level `Axiom`: no
- Coq non-`.v` cleanup: done
- Experience updates: none

Final Result: Success

## External Codex Run `20260421_015041`

- Start time: `2026-04-21 01:50:41 +0800`
- End time: `2026-04-21 02:00:13 +0800`
- Wall-clock time (seconds): `571.52`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `4995950`
- Codex CLI cached input tokens: `4869760`
- Codex CLI output tokens: `22198`
- Codex CLI total tokens: `5018148`
- Approx workspace-authored text tokens: `3079`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_015041_gcd_iterative/logs/codex_prompt_20260421_015041.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_015041_gcd_iterative/logs/codex_stdout_20260421_015041.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_015041_gcd_iterative/logs/codex_stderr_20260421_015041.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_015041_gcd_iterative/logs/codex_last_message_20260421_015041.txt`

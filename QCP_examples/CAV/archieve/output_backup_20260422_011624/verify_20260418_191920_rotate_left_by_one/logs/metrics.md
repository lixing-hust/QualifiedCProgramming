# Verify Metrics

- Workspace: `verify_20260418_191920_rotate_left_by_one`
- Function: `rotate_left_by_one`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/rotate_left_by_one.c`
- Input V: `<not provided>`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260418_191920_rotate_left_by_one.c`
- Annotation reasoning log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_191920_rotate_left_by_one/logs/annotation_reasoning.md`
- Proof reasoning log: not created
- symexec_start: `2026-04-18T19:19:40+08:00`
- symexec_end: `2026-04-18T19:31:00+08:00`
- symexec_elapsed: `multiple reruns over approximately 11m20s`
- symexec_status: `fail`
- symexec_reruns: `6`
- Generated files present: `goal.v`, `proof_auto.v`, `proof_manual.v`, `goal_check.v` were created during failed reruns, but `symexec` did not finish successfully on the current annotated file
- Manual proof status: not started because `symexec` never reached a clean successful generation point
- Compile status:
  - `goal.v`: not compiled
  - `proof_auto.v`: not compiled
  - `proof_manual.v`: not compiled
  - `goal_check.v`: not compiled
- `proof_manual.v` contains no verified completion claim because proof work did not start
- Coq non-`.v` cleanup status: no non-`.v` artifacts were produced under `coq/`
- Experience updates: none

Final Result: Fail

## External Codex Run `20260418_191921`

- Start time: `2026-04-18 19:19:21 +0800`
- End time: `2026-04-18 19:28:42 +0800`
- Wall-clock time (seconds): `561.45`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `3193557`
- Codex CLI cached input tokens: `3116800`
- Codex CLI output tokens: `25669`
- Codex CLI total tokens: `3219226`
- Approx workspace-authored text tokens: `2120`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_191920_rotate_left_by_one/logs/codex_prompt_20260418_191921.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_191920_rotate_left_by_one/logs/codex_stdout_20260418_191921.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_191920_rotate_left_by_one/logs/codex_stderr_20260418_191921.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_191920_rotate_left_by_one/logs/codex_last_message_20260418_191921.txt`

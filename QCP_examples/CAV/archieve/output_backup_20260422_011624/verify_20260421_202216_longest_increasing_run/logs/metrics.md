# Metrics

## Verify run

- Workspace: `output/verify_20260421_202216_longest_increasing_run`
- Input C: `input/longest_increasing_run.c`
- Input V: `input/longest_increasing_run.v`
- Active annotated C: `annotated/verify_20260421_202216_longest_increasing_run.c`
- Target function: `longest_increasing_run`

## Symexec

- symexec_start: `2026-04-21T20:26:06+08:00`
- symexec_end: `2026-04-21T20:26:06+08:00`
- symexec_elapsed: `<1s`
- symexec_status: `0`
- qcp log: `logs/qcp_run.log`

## Coq compile

- compile_original: `Success`
- compile_goal: `Success`
- compile_proof_auto: `Success`
- compile_proof_manual: `Success`
- compile_goal_check: `Success`
- compile completed: `2026-04-21T20:30:44+08:00`

## Proof status

- Manual proof obligations completed: `6`
- `proof_manual.v` contains `Admitted.`: `no`
- `proof_manual.v` adds `Axiom`: `no`
- `goal_check.v` compiled: `yes`
- Non-`.v` files under `coq/` cleaned: `yes`

## Experience updates

Experience updates: none. The reusable lessons were already covered by existing guidance (`PROOF.md` on `sac` scope and stable proof scripts), and the user's execution rule restricted work to the existing workspace.

Final Result: Success

## External Codex Run `20260421_202216`

- Start time: `2026-04-21 20:22:16 +0800`
- End time: `2026-04-21 20:31:57 +0800`
- Wall-clock time (seconds): `580.95`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `5210667`
- Codex CLI cached input tokens: `5062784`
- Codex CLI output tokens: `24984`
- Codex CLI total tokens: `5235651`
- Approx workspace-authored text tokens: `7507`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_202216_longest_increasing_run/logs/codex_prompt_20260421_202216.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_202216_longest_increasing_run/logs/codex_stdout_20260421_202216.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_202216_longest_increasing_run/logs/codex_stderr_20260421_202216.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_202216_longest_increasing_run/logs/codex_last_message_20260421_202216.txt`

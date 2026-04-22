# Verify Metrics

## Workspace

- Workspace: `output/verify_20260421_020437_count_divisors`
- Target function: `count_divisors`
- Input C: `input/count_divisors.c`
- Input V: `input/count_divisors.v`
- Active annotated C: `annotated/verify_20260421_020437_count_divisors.c`

## Symexec

- symexec_start: `2026-04-21 02:08:51 +0800`
- symexec_end: `2026-04-21 02:08:51 +0800`
- symexec_elapsed: `0s`
- Symexec log: `logs/qcp_run.log`
- Result: success; fresh generated Coq files were produced from the latest annotated C.

## Coq Compile

- compile_start: `2026-04-21 02:20:29 +0800`
- compile_end: `2026-04-21 02:20:33 +0800`
- compile_elapsed: `4s`
- Compile log: `logs/coq_compile.log`
- Compiled successfully:
  - `original/count_divisors.v`
  - `coq/deps/count_divisors_verify_aux.v`
  - `coq/generated/count_divisors_goal.v`
  - `coq/generated/count_divisors_proof_auto.v`
  - `coq/generated/count_divisors_proof_manual.v`
  - `coq/generated/count_divisors_goal_check.v`

## Artifacts

- `coq/generated/count_divisors_goal.v`: 227 lines
- `coq/generated/count_divisors_proof_auto.v`: 43 lines
- `coq/generated/count_divisors_proof_manual.v`: 192 lines
- `coq/generated/count_divisors_goal_check.v`: 7 lines
- `coq/deps/count_divisors_verify_aux.v`: 7 lines
- `proof_manual.v` contains no `Admitted.` and no locally added `Axiom`.
- Coq intermediate cleanup: completed; only `.v` files remain under `coq/`, and `original/` contains only `count_divisors.c` and `count_divisors.v`.

## Experience Updates

- Experience updates: none, because the user required work only inside the existing workspace.

Final Result: Success

## External Codex Run `20260421_020437`

- Start time: `2026-04-21 02:04:37 +0800`
- End time: `2026-04-21 02:23:11 +0800`
- Wall-clock time (seconds): `1114.57`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `12514626`
- Codex CLI cached input tokens: `12345088`
- Codex CLI output tokens: `39578`
- Codex CLI total tokens: `12554204`
- Approx workspace-authored text tokens: `4003`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_020437_count_divisors/logs/codex_prompt_20260421_020437.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_020437_count_divisors/logs/codex_stdout_20260421_020437.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_020437_count_divisors/logs/codex_stderr_20260421_020437.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_020437_count_divisors/logs/codex_last_message_20260421_020437.txt`

# Verify Metrics

## Run Summary

- Workspace: `verify_20260421_015753_is_prime_simple`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/is_prime_simple.c`
- Optional input V: none
- Target function: `is_prime_simple`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_015753_is_prime_simple.c`
- Annotation changes: added one loop invariant; removed a post-loop assertion after it caused local permission cleanup failure.
- Manual proof changes: none; generated `is_prime_simple_proof_manual.v` contains no manual theorem body.
- Experience updates: none

## Symexec

- symexec_start: `2026-04-21 02:00:29 +0800`
- symexec_end: `2026-04-21 02:00:30 +0800`
- symexec_elapsed: `0.04` seconds
- symexec_exit: `0`
- symexec_log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_015753_is_prime_simple/logs/qcp_run.log`
- Generated files:
  - `coq/generated/is_prime_simple_goal.v`
  - `coq/generated/is_prime_simple_proof_auto.v`
  - `coq/generated/is_prime_simple_proof_manual.v`
  - `coq/generated/is_prime_simple_goal_check.v`

## Compile Replay

- `is_prime_simple_goal.v`: compiled successfully, status `0`
- `is_prime_simple_proof_auto.v`: compiled successfully, status `0`
- `is_prime_simple_proof_manual.v`: compiled successfully, status `0`
- `is_prime_simple_goal_check.v`: compiled successfully, status `0`
- Full compile log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_015753_is_prime_simple/logs/compile_full.log`

## Final Checks

- `proof_manual.v` contains no `Admitted.`
- `proof_manual.v` contains no newly added `Axiom`
- `goal_check.v` compiled successfully
- Non-`.v` files under workspace `coq/` were removed

Final Result: Success

## External Codex Run `20260421_015753`

- Start time: `2026-04-21 01:57:53 +0800`
- End time: `2026-04-21 02:02:19 +0800`
- Wall-clock time (seconds): `265.36`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `1612321`
- Codex CLI cached input tokens: `1531008`
- Codex CLI output tokens: `11423`
- Codex CLI total tokens: `1623744`
- Approx workspace-authored text tokens: `3304`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_015753_is_prime_simple/logs/codex_prompt_20260421_015753.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_015753_is_prime_simple/logs/codex_stdout_20260421_015753.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_015753_is_prime_simple/logs/codex_stderr_20260421_015753.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_015753_is_prime_simple/logs/codex_last_message_20260421_015753.txt`

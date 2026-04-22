# Verify Metrics

## Run Summary

- Workspace: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_215456_fibonacci`
- Function: `fibonacci`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/fibonacci.c`
- Input V: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/fibonacci.v`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_215456_fibonacci.c`
- Completion time: `2026-04-20 22:10:50 +0800`

## Verification Steps

- Fingerprint initialized: yes
- Annotation updated: yes
- Symexec start: `2026-04-20 21:57:00 +0800` approximately
- Symexec end: `2026-04-20 21:57:00 +0800` approximately
- Symexec elapsed: `0` seconds as reported by the shell wrapper
- Symexec result: success
- Manual proof required: yes
- Manual proof result: success
- Full compile replay result: success
- `goal_check.v` result: success
- `proof_manual.v` contains `Admitted.`: no
- `proof_manual.v` contains user-added `Axiom`: no
- Coq non-`.v` cleanup: completed
- Experience updates: none, because the user required work only inside the existing workspace

## Compile Replay

The final successful compile replay was run from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the workspace `original/` directory on `-Q` and `coq/generated/` on `-R SimpleC.EE.CAV.verify_20260420_215456_fibonacci`.

Compiled successfully:

- `original/fibonacci.v`
- `coq/generated/fibonacci_goal.v`
- `coq/generated/fibonacci_proof_auto.v`
- `coq/generated/fibonacci_proof_manual.v`
- `coq/generated/fibonacci_goal_check.v`

Final Result: Success

## External Codex Run `20260420_215457`

- Start time: `2026-04-20 21:54:57 +0800`
- End time: `2026-04-20 22:11:53 +0800`
- Wall-clock time (seconds): `1016.62`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `7285088`
- Codex CLI cached input tokens: `7035776`
- Codex CLI output tokens: `33913`
- Codex CLI total tokens: `7319001`
- Approx workspace-authored text tokens: `4323`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_215456_fibonacci/logs/codex_prompt_20260420_215457.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_215456_fibonacci/logs/codex_stdout_20260420_215457.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_215456_fibonacci/logs/codex_stderr_20260420_215457.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_215456_fibonacci/logs/codex_last_message_20260420_215457.txt`

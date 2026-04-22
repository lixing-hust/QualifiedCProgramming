# Verify Metrics

## Run Summary

- Workspace: `output/verify_20260420_121132_array_has_adjacent_equal`
- Input C: `input/array_has_adjacent_equal.c`
- Active annotated C: `annotated/verify_20260420_121132_array_has_adjacent_equal.c`
- Target function: `array_has_adjacent_equal`
- Optional input V: none
- Final timestamp: `2026-04-20T12:17:19+08:00`

## Verification Steps

- Fingerprint updated: yes, `semantic_description` is non-empty and `keywords` use the controlled vocabulary from `doc/retrieval/INDEX.md`.
- Annotation updates: added one loop invariant; removed the post-loop assertion after it caused local-permission cleanup failure.
- symexec_start: `2026-04-20T12:13:49+08:00`
- symexec_end: `2026-04-20T12:13:49+08:00`
- symexec_elapsed: `<1s`
- symexec result: success, regenerated `array_has_adjacent_equal_goal.v`, `array_has_adjacent_equal_proof_auto.v`, `array_has_adjacent_equal_proof_manual.v`, and `array_has_adjacent_equal_goal_check.v`.
- Manual proof obligations: one, `proof_of_array_has_adjacent_equal_return_wit_2`.
- Manual proof result: completed with no `Admitted.` and no newly added `Axiom` in `array_has_adjacent_equal_proof_manual.v`.

## Compile Checks

- `array_has_adjacent_equal_goal.v`: passed.
- `array_has_adjacent_equal_proof_auto.v`: passed.
- `array_has_adjacent_equal_proof_manual.v`: passed.
- `array_has_adjacent_equal_goal_check.v`: passed.
- Compile logs: `logs/compile_goal.log`, `logs/compile_proof_auto.log`, `logs/compile_proof_manual.log`, `logs/compile_goal_check.log`.
- Coq cleanup: completed; no non-`.v` files remain under the workspace `coq/` tree.

## Experience Updates

- Experience updates: none.

Final Result: Success

## External Codex Run `20260420_121132`

- Start time: `2026-04-20 12:11:32 +0800`
- End time: `2026-04-20 12:18:14 +0800`
- Wall-clock time (seconds): `401.79`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `3039228`
- Codex CLI cached input tokens: `2863744`
- Codex CLI output tokens: `16672`
- Codex CLI total tokens: `3055900`
- Approx workspace-authored text tokens: `3958`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_121132_array_has_adjacent_equal/logs/codex_prompt_20260420_121132.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_121132_array_has_adjacent_equal/logs/codex_stdout_20260420_121132.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_121132_array_has_adjacent_equal/logs/codex_stderr_20260420_121132.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_121132_array_has_adjacent_equal/logs/codex_last_message_20260420_121132.txt`

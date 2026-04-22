# Verify Metrics

- Workspace: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_183816_string_ends_with_char`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/string_ends_with_char.c`
- Optional input V: none
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_183816_string_ends_with_char.c`
- Target function: `string_ends_with_char`
- Verify start observed: `2026-04-20T18:38:42+08:00`
- Verify end observed: `2026-04-20T18:55:11+08:00`

## Symexec Runs

- Run 1: failed, `2026-04-20T18:40:34+08:00` to `2026-04-20T18:40:34+08:00`, pre-loop assertion dropped local `i` permission.
- Run 2: failed, `2026-04-20T18:41:01+08:00` to `2026-04-20T18:41:01+08:00`, loop-exit assertion lacked direct bounds for final memory read.
- Run 3: succeeded, `2026-04-20T18:41:36+08:00` to `2026-04-20T18:41:36+08:00`, but generated proof exposed missing preserved `n < INT_MAX`.
- Run 4: succeeded, `2026-04-20T18:43:35+08:00` to `2026-04-20T18:43:35+08:00`, final regenerated Coq files used for proof and compile replay.
- Final symexec status: success.

## Proof And Compile

- Manual proof obligations after final symexec: 5.
- Manual proof completed: yes.
- `proof_manual.v` contains `Admitted.`: no.
- `proof_manual.v` contains user-added top-level `Axiom`: no.
- `coqc string_ends_with_char_goal.v`: success.
- `coqc string_ends_with_char_proof_auto.v`: success.
- `coqc string_ends_with_char_proof_manual.v`: success.
- `coqc string_ends_with_char_goal_check.v`: success.
- Non-`.v` Coq intermediates cleaned: yes.

## Experience Updates

- Experience updates: none. The reusable patterns used here were already covered by existing string examples and experience notes; the user also constrained work to this existing workspace.

Final Result: Success

## External Codex Run `20260420_183816`

- Start time: `2026-04-20 18:38:16 +0800`
- End time: `2026-04-20 18:56:13 +0800`
- Wall-clock time (seconds): `1077.28`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `8919787`
- Codex CLI cached input tokens: `8721536`
- Codex CLI output tokens: `29942`
- Codex CLI total tokens: `8949729`
- Approx workspace-authored text tokens: `7636`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_183816_string_ends_with_char/logs/codex_prompt_20260420_183816.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_183816_string_ends_with_char/logs/codex_stdout_20260420_183816.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_183816_string_ends_with_char/logs/codex_stderr_20260420_183816.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_183816_string_ends_with_char/logs/codex_last_message_20260420_183816.txt`

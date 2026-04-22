# Verify Metrics

## Manual Verify Run

- Workspace: `output/verify_20260422_010902_array_first_peak`
- Function: `array_first_peak`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/array_first_peak.c`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260422_010902_array_first_peak.c`
- Optional input V: none

## Symexec

- symexec_start: `2026-04-22T01:12:46+08:00`
- symexec_end: `2026-04-22T01:12:51+08:00`
- symexec_elapsed: `5 seconds`
- symexec_exit_code: `0`
- symexec result: success; regenerated `array_first_peak_goal.v`, `array_first_peak_proof_auto.v`, `array_first_peak_proof_manual.v`, and `array_first_peak_goal_check.v` from the latest annotated file.

## Proof

- Manual obligations after final symexec: `1`
- Completed manual theorem: `proof_of_array_first_peak_entail_wit_3`
- `proof_manual.v` forbidden-token check: no `Admitted.` and no new `Axiom`; the only `Axioms` occurrence is the imported library module name in `From AUXLib Require Import ... Axioms ...`.

## Compile

- `array_first_peak_goal.v`: passed
- `array_first_peak_proof_auto.v`: passed
- `array_first_peak_proof_manual.v`: passed
- `array_first_peak_goal_check.v`: passed
- Compile logs: `logs/compile_goal.log`, `logs/compile_proof_auto.log`, `logs/compile_proof_manual.log`, and `logs/compile_goal_check.log`; all are empty because `coqc` emitted no diagnostics.

## Cleanup

- Removed non-`.v` Coq compilation artifacts from `output/verify_20260422_010902_array_first_peak/coq/`.
- Post-cleanup check: `find .../coq -type f ! -name '*.v'` returned no files.

## Experience

- Experience updates: none. The run stayed within the user-specified workspace-only write rule; no shared experience document was modified.

Final Result: Success

## External Codex Run `20260422_010902`

- Start time: `2026-04-22 01:09:02 +0800`
- End time: `2026-04-22 01:15:12 +0800`
- Wall-clock time (seconds): `369.57`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `2719816`
- Codex CLI cached input tokens: `2617984`
- Codex CLI output tokens: `15168`
- Codex CLI total tokens: `2734984`
- Approx workspace-authored text tokens: `6863`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010902_array_first_peak/logs/codex_prompt_20260422_010902.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010902_array_first_peak/logs/codex_stdout_20260422_010902.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010902_array_first_peak/logs/codex_stderr_20260422_010902.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010902_array_first_peak/logs/codex_last_message_20260422_010902.txt`

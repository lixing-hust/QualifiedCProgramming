# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `grant-result`; attempt 1; earlier compact attempts 0
- Difficulty hint: 1/5
- Required suffix for every new or adapted helper: `__grant_result`


### `proof_of_ucos_Grant_Cap_return_wit_1_valid_target` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_ucos_Grant_Cap_return_wit_1_valid_target_split_goal_1`: Introduce the generated binders, discharge the pure entailment, unfold grant_cap_transition and grant_slot_result, introduce slot and ptr, and close the resulting record/pair equality by reflexivity after projection reduction.
  - `proof_of_ucos_Grant_Cap_return_wit_1_valid_target_split_goal_spatial`: Introduce binders and substitute destination, class, and right using PreH11, PreH12, and PreH13; cancel the four unchanged table/type/content/right resources after commutative separation reordering.

## Write boundary

- Editable top-level proof spans: `proof_of_ucos_Grant_Cap_return_wit_1_valid_target`.
- Editable aggressive split-goal proof spans: `proof_of_ucos_Grant_Cap_return_wit_1_valid_target_split_goal_1`, `proof_of_ucos_Grant_Cap_return_wit_1_valid_target_split_goal_spatial`.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- In `group_worker_lib`, append only proved suffixed helpers, token-identical sealed helper copies, and needed official imports.
- All declaration statements, other proof tokens, the manual prelude, and the seed library stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/home/lixing/projects/QualifiedCProgramming/verification_runs/ucos_Grant_Cap-20260916223647/ucos_Grant_Cap-vc-proving-r1/groups/group_00__grant-result/ucos_Grant_Cap_proof_manual.v`
- `group_worker_lib`: `/home/lixing/projects/QualifiedCProgramming/verification_runs/ucos_Grant_Cap-20260916223647/ucos_Grant_Cap-vc-proving-r1/groups/group_00__grant-result/ucos_Grant_Cap_lib.v`
- Read-only `formal_case_lib`: `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_lib.v`
- Frozen helper candidates: `/home/lixing/projects/QualifiedCProgramming/verification_runs/ucos_Grant_Cap-20260916223647/ucos_Grant_Cap-vc-proving-r1/public_helper_snapshot.txt` — inspect and copy useful declarations; never import this file
- Terminal report: `/home/lixing/projects/QualifiedCProgramming/reports/ucos_Grant_Cap-20260916223647/rounds/ucos_Grant_Cap-vc-proving-r1/groups/group_00__grant-result/group_worker_report.json`
- Notes: `/home/lixing/projects/QualifiedCProgramming/reports/ucos_Grant_Cap-20260916223647/rounds/ucos_Grant_Cap-vc-proving-r1/groups/group_00__grant-result/group_worker_output.md`. They are optional for ordinary outcomes, but an
  `annotation-gap` blocker requires a non-empty explanation here because the controller preserves this
  exact Markdown as part of the aggregated annotation feedback.
- Proof reuse hints: none (there was no immediately preceding sealed vc-proving source eligible for comparison)

The group directory must finish with the copied manual and `group_worker_lib`.

## Planned helpers

- none planned

`local` stays in this group. A proved `public` helper is promoted by the controller for later rounds. Historical token-identical copies may keep their sealed suffix; adaptations use this group's suffix.

## Commands

Run a needed command unchanged with its bound cwd. Prefer a direct system-terminal call. If terminal operations are available only through `functions.exec`, use a transparent cell that awaits exactly one `tools.exec_command` to launch, or one `tools.write_stdin` to continue the same live session (or the runtime-documented normalized equivalent), and only forwards the result. Pass command/argv, every argument, and cwd unchanged when launching; preserve the exact session handle when continuing. Use a normalized equivalent only if its input shape accepts those values unchanged; never serialize argv into shell text, reparse a rendered command, or add quoting. Do not call another tool in the cell, construct, alter, sequence, wrap, pipe, or background commands. Preserve every outer cell and inner process/session handle until terminal exit; if the bridge yields a running cell, resume only that cell with `functions.wait`.

```text
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming coq-debug --run ucos_Grant_Cap-20260916223647 --round ucos_Grant_Cap-vc-proving-r1 --group grant-result
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming coq-check --run ucos_Grant_Cap-20260916223647 --round ucos_Grant_Cap-vc-proving-r1 --target-kind group-development --group grant-result
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming coq-check --run ucos_Grant_Cap-20260916223647 --round ucos_Grant_Cap-vc-proving-r1 --target-kind group-check --group grant-result
```

Debug script: `/home/lixing/projects/QualifiedCProgramming/verification_runs/ucos_Grant_Cap-20260916223647/_coq_builds/ucos_Grant_Cap-vc-proving-r1/group_00/src/.coq_debug/group_00_grant_result.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the two formal files and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If the assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `location` must name every affected assigned witness. The controller will seal this group, continue dispatching independent groups, and aggregate all such gaps only after the accepted plan reaches terminal group states.

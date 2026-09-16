# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `delete-results`; attempt 1; earlier compact attempts 0
- Difficulty hint: 1/5
- Required suffix for every new or adapted helper: `__delete_results`


### `proof_of_ucos_CNode_Delete_return_wit_1_category_cap` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_ucos_CNode_Delete_return_wit_1_category_cap_split_goal_1`: Unfold the split definition, introduce binders, unfold delete_slot_transition and delete_slot_result, then cbn and reflexivity: category deletion clears both words and preserves the pointer.

### `proof_of_ucos_CNode_Delete_return_wit_2_object_cap` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_ucos_CNode_Delete_return_wit_2_object_cap_split_goal_1`: Unfold the split definition, introduce binders, unfold delete_slot_transition and delete_slot_result, then cbn and reflexivity: object deletion clears word0 and the pointer while preserving word1.

### `proof_of_ucos_CNode_Delete_return_wit_3_unsupported_cap` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_ucos_CNode_Delete_return_wit_3_unsupported_cap_split_goal_1`: Unfold the split definition, introduce binders, unfold delete_slot_transition and delete_slot_result and cbn. Destruct Z.eq_dec old_cap_unsupported_cap 1 and then Z.eq_dec old_cap_unsupported_cap 2; close equal branches by the existing disequalities and the remaining unchanged-state result by reflexivity.

## Write boundary

- Editable top-level proof spans: `proof_of_ucos_CNode_Delete_return_wit_1_category_cap`, `proof_of_ucos_CNode_Delete_return_wit_2_object_cap`, `proof_of_ucos_CNode_Delete_return_wit_3_unsupported_cap`.
- Editable aggressive split-goal proof spans: `proof_of_ucos_CNode_Delete_return_wit_1_category_cap_split_goal_1`, `proof_of_ucos_CNode_Delete_return_wit_2_object_cap_split_goal_1`, `proof_of_ucos_CNode_Delete_return_wit_3_unsupported_cap_split_goal_1`.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- In `group_worker_lib`, append only proved suffixed helpers, token-identical sealed helper copies, and needed official imports.
- All declaration statements, other proof tokens, the manual prelude, and the seed library stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/home/lixing/projects/QualifiedCProgramming/verification_runs/ucos_CNode_Delete-20260916225404/ucos_CNode_Delete-vc-proving-r1/groups/group_00__delete-results/ucos_CNode_Delete_proof_manual.v`
- `group_worker_lib`: `/home/lixing/projects/QualifiedCProgramming/verification_runs/ucos_CNode_Delete-20260916225404/ucos_CNode_Delete-vc-proving-r1/groups/group_00__delete-results/ucos_CNode_Delete_lib.v`
- Read-only `formal_case_lib`: `Rocq/examples/osverify_qcp/cases/ucos_CNode_Delete_lib.v`
- Frozen helper candidates: `/home/lixing/projects/QualifiedCProgramming/verification_runs/ucos_CNode_Delete-20260916225404/ucos_CNode_Delete-vc-proving-r1/public_helper_snapshot.txt` — inspect and copy useful declarations; never import this file
- Terminal report: `/home/lixing/projects/QualifiedCProgramming/reports/ucos_CNode_Delete-20260916225404/rounds/ucos_CNode_Delete-vc-proving-r1/groups/group_00__delete-results/group_worker_report.json`
- Notes: `/home/lixing/projects/QualifiedCProgramming/reports/ucos_CNode_Delete-20260916225404/rounds/ucos_CNode_Delete-vc-proving-r1/groups/group_00__delete-results/group_worker_output.md`. They are optional for ordinary outcomes, but an
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
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming coq-debug --run ucos_CNode_Delete-20260916225404 --round ucos_CNode_Delete-vc-proving-r1 --group delete-results
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming coq-check --run ucos_CNode_Delete-20260916225404 --round ucos_CNode_Delete-vc-proving-r1 --target-kind group-development --group delete-results
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming coq-check --run ucos_CNode_Delete-20260916225404 --round ucos_CNode_Delete-vc-proving-r1 --target-kind group-check --group delete-results
```

Debug script: `/home/lixing/projects/QualifiedCProgramming/verification_runs/ucos_CNode_Delete-20260916225404/_coq_builds/ucos_CNode_Delete-vc-proving-r1/group_00/src/.coq_debug/group_00_delete_results.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the two formal files and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If the assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `location` must name every affected assigned witness. The controller will seal this group, continue dispatching independent groups, and aggregate all such gaps only after the accepted plan reaches terminal group states.

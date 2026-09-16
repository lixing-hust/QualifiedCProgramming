# vc-checking handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `ucos_CNode_Delete-vc-checking-r1`
- Attempt: `ucos_CNode_Delete-vc-checking-r1-attempt-1` (index 1)
- Main root: `/home/lixing/projects/QualifiedCProgramming`
- Terminal report: `/home/lixing/projects/QualifiedCProgramming/reports/ucos_CNode_Delete-20260916213458/rounds/ucos_CNode_Delete-vc-checking-r1/agent_report.json`
- Optional human notes: `/home/lixing/projects/QualifiedCProgramming/reports/ucos_CNode_Delete-20260916213458/rounds/ucos_CNode_Delete-vc-checking-r1/agent_output.md`

## Target files

- C: `QCP_examples/osverify_qcp/cases/ucos_CNode_Delete.c`
- `formal_case_lib` candidate (present; read-only in this phase): `Rocq/examples/osverify_qcp/cases/ucos_CNode_Delete_lib.v`
- Manual (present; generated/proved artifact, never edit it as annotation source): `Rocq/examples/osverify_qcp/cases/ucos_CNode_Delete_proof_manual.v`
- Goal/auto/check: `Rocq/examples/osverify_qcp/cases/ucos_CNode_Delete_goal.v`, `Rocq/examples/osverify_qcp/cases/ucos_CNode_Delete_proof_auto.v`, `Rocq/examples/osverify_qcp/cases/ucos_CNode_Delete_goal_check.v`

## Rules to read

- `.agents/skills/verification-orchestrator/SKILL.md`
- `.agents/skills/verification-orchestrator/workflows/state-handoffs-and-reports.md`
- `.agents/skills/verification-orchestrator/workflows/paths-and-commands.md`
- `.agents/skills/vc-checking/SKILL.md`
- `.agents/skills/vc-checking/workflows/vc-analysis-and-grouping.md`

## Previous attempts

- none

Required lessons:

- none

## Controller command execution contract

Run every listed controller command unchanged with its bound cwd. Prefer a direct system-terminal call. If the runtime
exposes terminal tools only through `functions.exec`, use a transparent bridge. Each bridge cell may await exactly one
terminal operation: `tools.exec_command` to launch the command, or `tools.write_stdin` to continue the same live
session (or the runtime-documented normalized name for that same terminal operation), and may only forward its result.
Pass the rendered command/argv, every argument, and cwd unchanged when launching, and preserve the exact session
handle when continuing. A normalized equivalent is permitted only when its input shape accepts those values unchanged;
never serialize an argv array into shell text, reparse a rendered command, or add quoting.

Do not call a second tool in a bridge cell, add JavaScript/Python orchestration, construct, alter, sequence,
parallelize, or interpret commands, wrap them in a generated shell/PowerShell/Python script or another `uv run`, use
`sh -c`, command substitution, a pipeline or background execution, or invoke another wrapper. Never recreate
controller behavior with a custom command or script.

Preserve every outer cell and inner process/session handle until the actual command reaches a terminal exit. If a
transparent bridge yields a running `functions.exec` cell, resume only that cell with `functions.wait` until its one
nested terminal operation returns. Empty output, an initial-yield response, and outer-cell messages such as
`Script completed` do not prove that the controller command finished. Record a check as passed only after the terminal
process exits with code 0 and the controller JSON reports
`status: passed`.


## VC checking inputs

- Group plan output: `/home/lixing/projects/QualifiedCProgramming/reports/ucos_CNode_Delete-20260916213458/rounds/ucos_CNode_Delete-vc-checking-r1/group_plan.json`
- Maximum witnesses per group: 12

The fixed run topology contains `formal_case_lib`, so groups may plan owner-suffixed helpers when needed.

Target witnesses:

- `proof_of_ucos_CNode_Delete_return_wit_1_category_cap` -> debug target `SimpleC.EE.osverify_qcp.cases.ucos_CNode_Delete_goal.ucos_CNode_Delete_return_wit_1_category_cap`; generated split goals: `proof_of_ucos_CNode_Delete_return_wit_1_category_cap_split_goal_1` -> `SimpleC.EE.osverify_qcp.cases.ucos_CNode_Delete_goal.ucos_CNode_Delete_return_wit_1_category_cap_split_goal_1`
- `proof_of_ucos_CNode_Delete_return_wit_2_object_cap` -> debug target `SimpleC.EE.osverify_qcp.cases.ucos_CNode_Delete_goal.ucos_CNode_Delete_return_wit_2_object_cap`; generated split goals: `proof_of_ucos_CNode_Delete_return_wit_2_object_cap_split_goal_1` -> `SimpleC.EE.osverify_qcp.cases.ucos_CNode_Delete_goal.ucos_CNode_Delete_return_wit_2_object_cap_split_goal_1`
- `proof_of_ucos_CNode_Delete_return_wit_3_unsupported_cap` -> debug target `SimpleC.EE.osverify_qcp.cases.ucos_CNode_Delete_goal.ucos_CNode_Delete_return_wit_3_unsupported_cap`; generated split goals: `proof_of_ucos_CNode_Delete_return_wit_3_unsupported_cap_split_goal_1` -> `SimpleC.EE.osverify_qcp.cases.ucos_CNode_Delete_goal.ucos_CNode_Delete_return_wit_3_unsupported_cap_split_goal_1`

First judge every generated split goal across all target VCs, without analyzing any top-level VC. In this pass, record
only whether each split goal is provable; do not yet plan helpers, proof strategies, or reuse. For a top-level VC with
at least one generated split goal, select `aggressive_pre_process` exactly when all of its split goals are provable; do
not analyze that top-level VC's provability. If any split goal is not provable, or no split goal exists, then judge only
the whole top-level VC's provability and select `LLM_pre_process` when it is provable. If that whole VC is not provable,
report the annotation/specification boundary instead of creating a proving assignment.

After every `proof_mode` is fixed, write the natural-language proof strategy and perform the sealed-source reuse analysis
as one step. For `aggressive_pre_process`, analyze and compare only the split goals; do not write or compare a top-level
proof strategy. For `LLM_pre_process`, analyze and compare only the whole top-level VC. Only after these strategies are
complete, group the top-level VCs by their proof ideas. Never assign a split goal independently: every split goal follows
its parent top-level VC into the same group.

## Proof-state inspection

- Current debug script: `/home/lixing/projects/QualifiedCProgramming/verification_runs/ucos_CNode_Delete-20260916213458/_coq_builds/ucos_CNode_Delete-vc-checking-r1/vc-checking/src/.coq_debug/vc-checking.v`
- Current debug command: `/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming coq-debug --run ucos_CNode_Delete-20260916213458 --round ucos_CNode_Delete-vc-checking-r1`

The `.coq_debug` directory may contain only that declared script. Before a goal block, the script may contain only
imports, scope openings, and `Set Printing All.`. Inspect every listed target with this exact command shape:

```coq
Goal <fully-qualified-target>.
Show.
(* optional proof tactics and additional Show. commands *)
Abort.
```

The fully-qualified target must be copied from the current targets in `VC checking inputs` or, for the preserved
previous build, from the `Previous comparison target` list below. The first executable command after `Goal` must be
`Show.` so it binds the original generated goal. Definitions, declarations, `Load`, command wrappers, and attributes
are forbidden. Run the exact controller command after writing the final script. Current and preserved debug use the
same controller-owned load-path plan: only current-case closure files live in the sealed build, while fixed dependency
`.vo` files are read from the selected sealed base (Dune `_build/default` or Makefile main-root artifacts) and are not
copied into the local build tree. Their accepted snapshot digest is bound into the combined build seal; those files do
not increase the local build file count.


## Proof reuse

There is no immediately preceding sealed vc-proving source eligible for comparison. Skip proof-reuse comparison and do not create reuse-hint files.


All formal files are read-only. Form initial groups by invariant, proof pattern, array/frame transformation, refinement
transition, and helper family. Then perform a second load-and-coupling review using top-level witness count, aggressive
split-goal count, expected helper families, proof-mode differences, program phase, and persistent proof context. Prefer
coherent groups of roughly 2--6 witnesses; justify every group above 6 witnesses and every single-witness group in
`/home/lixing/projects/QualifiedCProgramming/reports/ucos_CNode_Delete-20260916213458/rounds/ucos_CNode_Delete-vc-checking-r1/agent_output.md`. Heavy aggressive/helper work should not be bundled with many lightweight projection/rewrite/lia
VCs. Explicitly review the expected critical path: for every likely tail group, record split/helper/library/context
load in `/home/lixing/projects/QualifiedCProgramming/reports/ucos_CNode_Delete-20260916213458/rounds/ucos_CNode_Delete-vc-checking-r1/agent_output.md`, split final-result work from independently provable transition/safety work when helper
ownership permits, and otherwise explain the indivisible helper/context coupling. Plan stable permutation, sum/length,
mask-clear, and similar cross-group facts as annotation-approved or public helpers rather than rediscovering them in a
tail group. Assign each group an integer `estimated_difficulty` from 1 (light) to 5 (heaviest). Groups remain independent and
cannot read sibling outputs. Put every helper expected to be newly proved or modified in this round in the owner group's
plan with an exact Rocq declaration `name`, a short `strategy`, and `visibility` set to `local` or `public`. Historical helpers
from the frozen snapshot or a sealed reuse hint are opportunistic token-identical copies, not new planned-helper declarations. An
owner's local helper still participates in helper-first reuse comparison when it is a current planned helper. Mark a
stable mathematical helper useful to other groups as public. The controller promotes only successfully proved
matching public declarations into the run-level append-only candidate pool; workers copy candidates into their own
group_worker_lib and still pass the ordinary controller group validation. This pool is not an imported or active fourth library.

    Keep `/home/lixing/projects/QualifiedCProgramming/reports/ucos_CNode_Delete-20260916213458/rounds/ucos_CNode_Delete-vc-checking-r1/agent_output.md` as a decision summary. Record proof-mode reasons, grouping and critical-path decisions,
    define each common proof pattern once, and give each VC only a pattern reference plus its actual delta. Do not copy
    this handoff, the JSON schema, controller commands, or identical proof steps into that Markdown. Write
    `group_plan.json`: each group has `id`, `estimated_difficulty`, witness objects with
`name` and `proof_mode`. An aggressive witness has `split_strategies`, mapping each generated split-goal name to its
short strategy in declaration order, and omits `strategy`. An `LLM_pre_process` witness has one whole-goal `strategy`
and omits `split_strategies`. Optional planned
helpers use `{name, strategy, visibility}`. Do not copy a version or controller acceptance marker into the plan.
Write the final report: success contains only `status: completed`; a
blocked result adds one `blocker` with `failure_class`, `kind`, `location`, `message`, and `repair_boundary`. Do not
copy the current version or controller checks into the report. Its `failure_class` must be exactly one of
`annotation-gap`, `specification-gap`, `dependency-gap`, `source-version`, `plan-defect`, `report-defect`, or
`infrastructure`. The controller routes the first four to annotation and the last three to a same-phase vc-checking
retry; it never infers the repair phase from `kind` or prose.

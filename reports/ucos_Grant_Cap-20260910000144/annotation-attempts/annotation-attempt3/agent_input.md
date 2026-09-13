# Annotation blocker summary and repair handoff

This is annotation iteration 3 in the run's single persistent annotation-agent session. The controller generated the factual sections and template; the main agent must read the original evidence and replace every `MAIN_AGENT` comment with a concrete summary before running `annotation-summary-ready`. Do not change controller-owned paths, evidence references, or commands.

## Assignment

- Session: `ucos_Grant_Cap-annotation-agent`
- Round: `ucos_Grant_Cap-annotation-r3`
- Attempt: `ucos_Grant_Cap-annotation-r3-attempt-1`
- Retry reason: `vc-checking-annotation-gap`
- Main root: `/home/lixing/projects/QualifiedCProgramming`
- Terminal report: `/home/lixing/projects/QualifiedCProgramming/reports/ucos_Grant_Cap-20260910000144/annotation-attempts/annotation-attempt3/agent_report.json`
- Human notes: `/home/lixing/projects/QualifiedCProgramming/reports/ucos_Grant_Cap-20260910000144/annotation-attempts/annotation-attempt3/agent_output.md`

## Target files

- C: `QCP_examples/osverify_qcp/cases/ucos_Grant_Cap.c`
- `formal_case_lib` candidate (missing in the run topology; there is no active/editable case lib, and this candidate path is read-only and must not be created): `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_lib.v`
- Manual (present; generated/proved artifact, never edit it as annotation source): `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_proof_manual.v`
- Goal/auto/check: `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_goal.v`, `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_proof_auto.v`, `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_goal_check.v`

## Original blocker evidence

- `vc-checking` / `ucos_Grant_Cap-vc-checking-r1-attempt-1`: `/home/lixing/projects/QualifiedCProgramming/reports/ucos_Grant_Cap-20260910000144/rounds/ucos_Grant_Cap-vc-checking-r1/agent_report.json`; `/home/lixing/projects/QualifiedCProgramming/reports/ucos_Grant_Cap-20260910000144/rounds/ucos_Grant_Cap-vc-checking-r1/agent_output.md`

Previous annotation attempt artifacts:

- `ucos_Grant_Cap-annotation-r2-attempt-1`: report `/home/lixing/projects/QualifiedCProgramming/reports/ucos_Grant_Cap-20260910000144/annotation-attempts/annotation-attempt2/agent_report.json`; notes `/home/lixing/projects/QualifiedCProgramming/reports/ucos_Grant_Cap-20260910000144/annotation-attempts/annotation-attempt2/agent_output.md`

Controller-recorded blocker details:

- {"failure_class": "annotation-gap", "kind": "missing-annotation-premise", "location": "proof_of_ucos_Grant_Cap_return_wit_1 and proof_of_ucos_Grant_Cap_return_wit_2", "message": "The return obligations universally quantify cap_Class_pre and destTask_Prio_pre independently of cap_Class and destTask_Prio. Without equality bridges, current bounds cannot establish the required pre-variable bounds and ownership at current table/slot addresses cannot entail ownership at the pre-variable addresses; all three split goals for return_wit_1 and both whole return VCs are therefore unprovable.", "repair_boundary": "Repair the ucos_Grant_Cap return annotation/contract so the relevant exits preserve cap_Class_pre = cap_Class and destTask_Prio_pre = destTask_Prio (or equivalent facts) in the generated obligations, then regenerate the formal files."}
- Controller main-check failure: {"clean_output_freshness": {"source_goal_version": {"fresh": "51b5934813470cdb1db977a8ee61ea7ab5adfe2fcb7afbe5f638f195220edadd", "reference": "51b5934813470cdb1db977a8ee61ea7ab5adfe2fcb7afbe5f638f195220edadd"}, "status": "passed"}, "formal_case_lib_contract": {"reason": "optional formal_case_lib candidate is absent", "skipped": true, "status": "passed"}, "formal_case_lib_coqc": {"reason": "optional formal_case_lib candidate is absent", "skipped": true, "status": "passed"}, "symexec": {"returncode": 0, "status": "passed"}}

## Main-agent blocker conclusion

VC-checking found a shared annotation premise gap in `proof_of_ucos_Grant_Cap_return_wit_1` and `proof_of_ucos_Grant_Cap_return_wit_2`. The generated return obligations quantify `cap_Class_pre` and `destTask_Prio_pre` independently from the current parameters, so neither the pure bounds nor the spatial addresses can be related. This is a contract/return-annotation defect and requires regeneration; it cannot be repaired by a proof tactic or helper lemma.

## Evidence and causal analysis

The vc-checking report states that all three split goals of `return_wit_1` fail: the priority split lacks `destTask_Prio_pre = destTask_Prio`, the class split lacks `cap_Class_pre = cap_Class`, and the spatial split owns table/slot addresses indexed by current variables while demanding addresses indexed by unrelated pre variables. `return_wit_2` has the same table-address mismatch on the null-target branch. The controller evidence separately confirms canonical symexec and clean-output freshness passed, so generation and tooling are sound. The root cause is that the function contract uses `@pre` observations in the postcondition without preserving equality between those observations and unchanged scalar parameters at the return boundary.

## Reflection on the previous annotation attempt

Attempt 2 correctly modeled the selected table cell, selected slot, exact four-field update, failure framing, and unsigned-char promotion, but assumed QCP would automatically retain unchanged scalar-parameter identities across return annotations. Generated goals show that assumption is false. Preserve the current footprint decomposition and exact functional behavior; do not weaken the postcondition, duplicate resources, or try to hide the mismatch behind existentially chosen indices.

## Required annotation repair

Revise the C function contract and/or return assertions so every relevant exit carries facts equivalent to `cap_Class_pre = cap_Class` and `destTask_Prio_pre = destTask_Prio`, with the orientation needed to rewrite pre-state bounds and addresses to current ones. Keep the exact invalid-class, invalid-priority, null-entry, and success disjuncts; keep success as `(old_right & 4095) | cap_Right`; and keep unrelated resources framed. The topology has no editable case lib, so do not create one. Success requires canonical symexec to pass and regenerated goals to contain sufficient equality bridges for both return witnesses and all three `return_wit_1` split goals, as confirmed by annotation-checking without forbidden proof placeholders.

## Controller scope requirement

Choose local repair or broader redesign from the evidence, and justify the boundary.

## Scope decision

Use a local contract repair after explicitly reassessing the whole design. The pure behavior, selected-cell/selected-slot footprint, branch partition, and update relation are mutually consistent; both witnesses fail at exactly one cross-cutting boundary: missing identities for unchanged scalar inputs. There is no evidence of a faulty mathematical state model or footprint decomposition, so rebuilding the specification would discard sound work without resolving a different root cause.

## Rules to reload

The annotation agent must completely reload both annotation skills on every appended iteration, then follow all linked rules and inspect the original blocker evidence above. The main-agent summary prioritizes the repair but does not replace the original evidence or current main-root files.

- `.agents/skills/verification-orchestrator/SKILL.md`
- `.agents/skills/verification-orchestrator/workflows/state-handoffs-and-reports.md`
- `.agents/skills/verification-orchestrator/workflows/paths-and-commands.md`
- `.agents/skills/annotation-filling/SKILL.md`
- `.agents/skills/annotation-filling/workflows/annotation-filling.md`
- `.agents/skills/annotation-checking/SKILL.md`
- `.agents/skills/annotation-checking/workflows/annotation-checking.md`

## Writable formal paths

- `QCP_examples/osverify_qcp/cases/ucos_Grant_Cap.c`
- `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_goal.v`
- `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_proof_auto.v`
- `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_proof_manual.v`
- `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

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

## Commands

```text
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming symexec --run ucos_Grant_Cap-20260910000144 --round ucos_Grant_Cap-annotation-r3
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming timing-stage --run ucos_Grant_Cap-20260910000144 --round ucos_Grant_Cap-annotation-r3 --stage annotation-checking --event start
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming timing-stage --run ucos_Grant_Cap-20260910000144 --round ucos_Grant_Cap-annotation-r3 --stage annotation-checking --event finish
```

No formal-case-lib Coq command is listed because the optional candidate lib is absent from this run's fixed topology. The controller does not create a placeholder, and the annotation owner must not create a new lib at the read-only candidate path.

The dependency graph comes only from the selected backend's exact target; the agent never observes, supplies, or
expands build targets. Do not copy selected-base output, dependency sources/artifacts, or another `_coq_builds` scope.

The timing-stage commands are optional telemetry. If used, bracket the real annotation-checking work honestly; they
never replace a check or affect acceptance.

## Completion

Revise the mathematical spec first, editing the case lib only when it is listed as present and writable, then revise C annotations. Never create a missing candidate lib. Use the listed commands when useful for feedback and complete
the semantic annotation review. At the end, success contains only `status: completed`; a blocked result adds one
`blocker` with `failure_class`, `kind`, `location`, `message`, and
`repair_boundary`. Do not copy diff, version, or check results into the report. Notes are optional.

# Annotation attempt 2

## Blocker repair and candidate semantics

The main-owned source repair supplied the missing sequential `grant_cspace_cap` body, so the attempt-1 `missing-target-function` blocker is fully covered. Canonical symbolic execution now generates actual `grant_cspace_cap_*` safety, return, and call-boundary witnesses in addition to the callee witnesses.

The wrapper contract distinguishes the original outcomes:

- destination priority at least `OS_LOWEST_PRIO`: return `OS_PRIO_INVALID` without touching kernel state;
- valid destination with a null current-task CSpace: update `OSPrioCur` from `OSTCBCur->OSTCBPrio`, preserve the table entry, and return `CNODE_GRANT_FAILURE`;
- non-null current CSpace without grant authorization: preserve the destination capability and return `USER_CAPABILITY_NONE`;
- authorized call with invalid class or null destination CSpace: preserve the destination state and return `CNODE_GRANT_FAILURE`;
- authorized valid call: preserve the caller's current-task and authorization footprint, update only the selected destination capability fields, set rights to exactly `(old_right & 4095) | right`, and return `CSPACE_NONE_FAULT`.

The local footprint owns `OSTCBCur`, its priority field, writable `OSPrioCur`, `OSRunning`, the selected current and destination `OSCSpacePrioTbl` cells, the current CSpace grant-right field, `CapParent[dest]`, and the destination slot fields required by the callee. Other global/table/CSpace memory remains in the caller frame. The valid shared-state branch records distinct current/destination priorities and CSpace pointers so the two selected-cell/slot footprints are disjoint; this is the local separation-logic form of the parent/child well-formedness expected by the original kernel state.

The optional `formal_case_lib` remains absent as required. There is no algorithm-mirror definition or higher-order existential witness. ENTER/EXIT critical boundaries remain executable no-op comments, and the contract makes no concurrency claim.

## Callee composition repair

The previous single branching contract of `ucos_Grant_Cap` was split into four logically corresponding named specs: `class_invalid`, `prio_invalid`, `null_target`, and `valid_target`. The executable callee body is unchanged. This exposes exactly one pre/post footprint per call case and avoids asking the call transformer to match every caller branch against a branching default precondition.

At the wrapper call, branch control names the three reachable cases `callee_invalid`, `callee_null`, and `callee_success`. Branch-scoped `where` clauses select the matching named callee spec and bind all logical input, target, and old-field values. The callee's old ordinary Assert was removed because after the named-spec split it redundantly restated only the valid/null footprints and caused variables from one spec to leak into another spec's return check.

## Symbolic-execution repair record

- First candidate failure: call precondition matching selected the invalid-class disjunct while processing a valid-class/null-target caller state. Classification: call instantiation over a branching callee contract. Repair: introduce named callee specs and branch-scoped call instantiations.
- First named-spec candidate failure: the old callee phase Assert mixed `valid_target` logical values into the `null_target` verification branch, producing a false return-value conflict. Classification: redundant cross-spec Assert. Repair: remove that Assert; each named Require already provides the exact phase state.
- Final canonical symexec: exit code 0 and controller `status: passed`; generated goals contain `grant_cspace_cap_*` witnesses.

## Ordinary Assert review

There is no ordinary `Assert` in the final candidate. The former callee Assert was removed because it became redundant with the named Require states and was actively harmful across specs. The wrapper uses `Branch name` rather than an ordinary Assert at the call boundary; no loop invariant or exit bridge is applicable.

## Branch-control review

- `callee_invalid`: `class > CAP_CHANNEL_CLASS`; selects `class_invalid` and requires no destination footprint.
- `callee_null`: valid class with `target == 0`; selects `null_target` and passes the selected destination table cell.
- `callee_success`: valid class with `target != 0`; selects `valid_target` and passes the table cell plus the three selected slot fields.
- Each `where ... $ branch` is deliberately scoped to one named branch. No `Destruct`, `Branch clear`, `Branch join`, or multi-invariant is used.
- The names affect witness suffixes and keep call cases separate, but do not change executable control flow.

## Annotation-checking conclusion

The candidate expresses execution bounds, exact owned memory, authorization semantics, callee return mapping, and the successful capability update. The callee specs expose the precise decision/update facts the wrapper needs; all call bindings are explicit. There are no loops, array/string abstraction duplicates, forbidden proof constructs in annotation-owned sources, manual proof edits, or generated-file hand edits. The attempt-1 blocker is covered and the candidate is ready for controller-owned acceptance.

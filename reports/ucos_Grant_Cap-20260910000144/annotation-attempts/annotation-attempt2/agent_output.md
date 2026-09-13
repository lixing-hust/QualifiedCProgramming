# Annotation attempt 2

## Candidate semantics

The contract uses a local separation-logic footprint. It owns exactly the selected `OSCSpacePrioTbl[destTask_Prio]` cell when the implementation can reach that access and, for a non-null target, the three destination-slot fields that the function reads or writes. All other table entries, CSpaces, slots, and fields remain in the caller's frame and are therefore preserved.

The postcondition distinguishes:

- class above 16 or promoted destination priority at least 64: return 11 with an empty local footprint;
- valid class/priority and a null table entry: return 11 and preserve that exact null entry;
- valid class/priority and a non-null table entry: return 0, preserve the table pointer, set `cap_type` to 1 and `category_content` to the class, and set `category_right` to exactly `(old_right & 4095) | right`.

The unsigned preconditions make the source's `CAP_NULL_CLASS > cap_Class` branch unreachable, so class 0 remains accepted. The requested rights are not masked. The explicit `unsigned_last_nbits(destTask_Prio, 32) == destTask_Prio` bridge records the value-preserving integer promotion used by the C comparison.

The optional `formal_case_lib` is fixed as missing, so no placeholder or alternative library was created. There is no higher-order existential witness.

## Symbolic-execution repair record

- Initial whole-array `PtrArray::full` candidate did not align with the global-array element address at the read. Classification: resource shape. Repair: use the exact selected-cell `store(pointer_offset(&(OSCSpacePrioTbl), ...))` footprint and frame all other entries.
- Direct annotation indexing of the global program variable was rejected, and a typedef alias in annotation types was not resolved. Classification: annotation syntax/type translation. Repair: use `pointer_offset` and `struct cspace *`.
- The guard and the specification initially used differently normalized forms of unsigned-char promotion, leaving an infeasible precondition branch alive at the phase Assert. Classification: pure fact. Repair: state the exact `unsigned_last_nbits(..., 32)` guard and its equality to the bounded source value.
- `cap_Right@pre` was not available at the full Assert because the original Require did not bind that input to a logical value. Classification: pre-state bridge. Repair: introduce the logical value `right`, bind `cap_Right == right`, and use it consistently in the exact rights formula.

The final canonical symbolic-execution command completed with `status: passed` after the last C annotation change.

## Ordinary Assert review

location: immediately after the class and destination-priority guards, before reading `OSCSpacePrioTbl`
purpose: semantic-phase-transition | path-join
named_semantic_state: none
upstream_paths: the entry contract contains invalid-input and valid-input footprint branches, and the two early-return guards eliminate invalid class and priority paths
downstream_work: one global-table read, a null branch, and four nested destination-slot accesses/updates
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: the Assert closes the guard phase, eliminates infeasible normalized-promotion paths, retains the live `cap_Right == right` bridge, and presents the exact table-cell/slot footprint required by the subsequent memory operations. There is no loop invariant that can serve this role.

## Retry coverage

The attempt-1 `unsupported-c-declaration-form` blocker is covered by the main-owned combined `typedef struct cspace { ... } CSPACE` declaration. The current frontend parses the declaration and reaches and completes symbolic execution. The constants, field order, nested struct/union layout, global 64-entry table, branch order, and executable rights update remain unchanged.

## Annotation-checking conclusion

The contract contains execution bounds, exact owned memory, and the functional return/update relation. It neither weakens the function to return codes nor mirrors a loop/state machine. There are no loops or helper-call instantiations in this function. Generated files were refreshed only by the controller command, and no case library was created. The candidate is ready for controller-owned acceptance; the remaining generated manual witnesses are proof obligations rather than annotation gaps.

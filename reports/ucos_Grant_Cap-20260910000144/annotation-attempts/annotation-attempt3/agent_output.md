# Annotation attempt 3

## Repair

The contract now introduces stable logical values `dest`, `class`, and `right` and binds the three unchanged C parameters to them in `Require`. Every precondition footprint, postcondition footprint, guard predicate, slot index, and update value is expressed using those logical values. The phase Assert preserves the three program-variable equalities while the implementation continues to use the C parameters.

This is a local contract repair after reassessing the complete specification. The branch partition, selected-table-cell footprint, selected-slot footprint, and exact update relation remain coherent and unchanged in meaning; only the missing cross-return identities were repaired.

## Blocker coverage

- `proof_of_ucos_Grant_Cap_return_wit_1`: regenerated antecedent and consequent both use `dest` for the table offset and `class` for all slot offsets. Its priority/class/spatial split mismatch no longer exists.
- `proof_of_ucos_Grant_Cap_return_wit_2`: regenerated antecedent and consequent both own the null table entry at the offset indexed by `dest`. The previous table-address mismatch no longer exists.

The regenerated raw manual contains no lemma declaration, so no manual VC remains after the repair. Canonical symbolic execution completed with `status: passed`.

## Semantic review

The contract still has exact outcome branches:

- class greater than 16 or promoted destination at least 64 returns 11;
- valid class/priority with a null destination entry returns 11 and preserves that entry;
- valid class/priority with a non-null entry returns 0, preserves the table pointer, and changes exactly the three modeled destination-slot fields;
- the new rights value remains exactly `(old_right & 4095) | right`, with no mask applied to `right`;
- class 0 remains accepted because the unsigned lower-bound branch is unreachable.

Every table entry, CSpace, slot, and field outside the selected footprint remains in the caller's separation-logic frame. The optional case lib remains absent. There is no loop, helper-call instantiation, algorithm-mirror declaration, or higher-order existential witness.

## Ordinary Assert review

location: immediately after the class and destination-priority guards, before reading `OSCSpacePrioTbl`
purpose: semantic-phase-transition | path-join
named_semantic_state: none
upstream_paths: invalid class and priority paths have returned; normalized integer-promotion branches must be collapsed to the valid footprint
downstream_work: the global table read, null test, and four nested destination-slot accesses
redundant_with_invariant_or_postcondition: no
decision: revise and keep
rationale: the Assert now explicitly preserves `destTask_Prio == dest`, `cap_Class == class`, and `cap_Right == right`, while retaining the exact table/slot resources needed downstream. This closes the return-state identity gap reported by VC-checking and performs a genuine phase transition that no loop invariant can express.

## Annotation-checking conclusion

The generated return goals now contain the needed stable identities structurally rather than leaving them to proof search. The functional specification was not weakened, generated artifacts were refreshed only by the controller, and no forbidden placeholder or proof construct was introduced. The candidate is ready for controller-owned acceptance.

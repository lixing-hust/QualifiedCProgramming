#include "osverify_qcp/include/ios_cap_types.h"
#include "QCP_demos_LLM/verification_stdlib.h"
#include "QCP_demos_LLM/verification_list.h"

/* Source: ios_cap_defs.v:94. The array type is the user-authorized
 * (Tarray Tint32 64) fragment, interpreted with generic unsigned-word
 * operations. It is type evidence held in a specification, not a recovered
 * standalone source-language global declaration. */
#define OBJ_POSITION 17U
extern unsigned int OSCSpaceObjectPointer[64];

/*@ Import Coq Require Import SimpleC.EE.osverify_qcp.cases.get_obj_slot_without_critical_inferred_20261013_lib */
/*@ Extern Coq (gos_heap :: *) */
/*@ Extern Coq
    (gos_read_uint : gos_heap -> Z -> Z -> Prop)
    (gos_read_ptr : gos_heap -> Z -> Z -> Prop)
    (gos_exact : gos_heap -> Assertion)
    (gos_preserved : gos_heap -> Assertion)
    (gos_restore_uint : gos_heap -> Z -> Z -> Assertion)
    (gos_restore_ptr : gos_heap -> Z -> Z -> Assertion)
    (gos_input : gos_heap -> Z -> Z -> Z -> Z -> Z -> Z -> list Z -> Prop)
    (gos_result : Z -> Z -> Z -> Z -> list Z -> Z -> Prop)
    (gos_safe_observation : list Z -> Z -> Z -> Prop)
    (gos_no_match : list Z -> Z -> Z -> Prop)
    (gos_limit : list Z -> Z)
    (gos_nth : list Z -> Z -> Z)
 */

unsigned int Get_Obj_Slot_without_critical(unsigned char prio, void *func_object)
/*@ With (h : gos_heap) (p : Z) (e : Z) (xs : list Z)
    Require
      gos_input(h, prio, &OSCSpaceObjectPointer, &OSCSpacePrioTbl,
                p, e, func_object, xs) && gos_exact(h)
    Ensure
      gos_result(prio, p, e, func_object, xs, __return) && gos_preserved(h)
 */
{
    unsigned int i;
    unsigned int endPtr;
    CSPACE *pCSpace;

    /*@ gos_exact(h) which implies gos_preserved(h) */

    if (prio >= OS_LOWEST_PRIO) {
        return (unsigned int)OS_PRIO_INVALID;
    }

    /*@ gos_read_uint(h, pointer_offset(&OSCSpaceObjectPointer, prio@pre, sizeof(unsigned int), unsigned int), e) && gos_preserved(h)
        which implies
        data_at(pointer_offset(&OSCSpaceObjectPointer, prio@pre, sizeof(unsigned int), unsigned int), unsigned int, e) *
        gos_restore_uint(h, pointer_offset(&OSCSpaceObjectPointer, prio@pre, sizeof(unsigned int), unsigned int), e) */
    endPtr = OSCSpaceObjectPointer[prio];
    /*@ data_at(pointer_offset(&OSCSpaceObjectPointer, prio@pre, sizeof(unsigned int), unsigned int), unsigned int, e) *
        gos_restore_uint(h, pointer_offset(&OSCSpaceObjectPointer, prio@pre, sizeof(unsigned int), unsigned int), e)
        which implies gos_preserved(h) */

    /*@ gos_read_ptr(h, pointer_offset(&OSCSpacePrioTbl, prio@pre, sizeof(struct cspace *), struct cspace *), p) && gos_preserved(h)
        which implies
        data_at(pointer_offset(&OSCSpacePrioTbl, prio@pre, sizeof(struct cspace *), struct cspace *), struct cspace *, p) *
        gos_restore_ptr(h, pointer_offset(&OSCSpacePrioTbl, prio@pre, sizeof(struct cspace *), struct cspace *), p) */
    pCSpace = OSCSpacePrioTbl[prio];
    /*@ data_at(pointer_offset(&OSCSpacePrioTbl, prio@pre, sizeof(struct cspace *), struct cspace *), struct cspace *, p) *
        gos_restore_ptr(h, pointer_offset(&OSCSpacePrioTbl, prio@pre, sizeof(struct cspace *), struct cspace *), p)
        which implies gos_preserved(h) */

    if (pCSpace == (CSPACE *)0) {
        return (unsigned int)SLOT_NULL_CAP;
    }

    i = OBJ_POSITION;
    /*@ Inv Assert
        prio == prio@pre && func_object == func_object@pre &&
        pCSpace == p && p != 0 && endPtr == e &&
        0 <= prio && prio < OS_LOWEST_PRIO &&
        0 <= e && e <= 4294967295 &&
        OBJ_POSITION <= i && i <= gos_limit(xs) && gos_limit(xs) <= SLOT_NUM &&
        gos_input(h, prio@pre, &OSCSpaceObjectPointer, &OSCSpacePrioTbl,
                  p, e, func_object@pre, xs) &&
        gos_safe_observation(xs, e, func_object@pre) &&
        gos_no_match(xs, func_object@pre, i) && gos_preserved(h)
     */
    while (i < endPtr) {
        /*@ exists (j : Z), i == j && gos_read_ptr(h,
              field_addr(field_addr(field_addr(field_addr(pointer_offset(field_addr(field_addr(p, struct cspace, cnode), struct cte, slots), j, sizeof(struct slot), struct slot), struct slot, capability), struct cap, cap_content), union content, object), struct cap_object, object_t),
              gos_nth(xs, j)) && gos_preserved(h)
            which implies exists (j : Z), i == j &&
            data_at(field_addr(field_addr(field_addr(field_addr(pointer_offset(field_addr(field_addr(p, struct cspace, cnode), struct cte, slots), j, sizeof(struct slot), struct slot), struct slot, capability), struct cap, cap_content), union content, object), struct cap_object, object_t),
                    void *, gos_nth(xs, j)) *
            gos_restore_ptr(h,
              field_addr(field_addr(field_addr(field_addr(pointer_offset(field_addr(field_addr(p, struct cspace, cnode), struct cte, slots), j, sizeof(struct slot), struct slot), struct slot, capability), struct cap, cap_content), union content, object), struct cap_object, object_t),
              gos_nth(xs, j)) */
        if (pCSpace->cnode.slots[i].capability.cap_content.object.object_t == func_object) {
            /*@ exists (j : Z), i == j && data_at(field_addr(field_addr(field_addr(field_addr(pointer_offset(field_addr(field_addr(p, struct cspace, cnode), struct cte, slots), j, sizeof(struct slot), struct slot), struct slot, capability), struct cap, cap_content), union content, object), struct cap_object, object_t),
                        void *, gos_nth(xs, j)) *
                gos_restore_ptr(h,
                  field_addr(field_addr(field_addr(field_addr(pointer_offset(field_addr(field_addr(p, struct cspace, cnode), struct cte, slots), j, sizeof(struct slot), struct slot), struct slot, capability), struct cap, cap_content), union content, object), struct cap_object, object_t),
                  gos_nth(xs, j))
                which implies exists (j : Z), i == j && gos_preserved(h) */
            return i;
        }
        /*@ exists (j : Z), i == j && data_at(field_addr(field_addr(field_addr(field_addr(pointer_offset(field_addr(field_addr(p, struct cspace, cnode), struct cte, slots), j, sizeof(struct slot), struct slot), struct slot, capability), struct cap, cap_content), union content, object), struct cap_object, object_t),
                    void *, gos_nth(xs, j)) *
            gos_restore_ptr(h,
              field_addr(field_addr(field_addr(field_addr(pointer_offset(field_addr(field_addr(p, struct cspace, cnode), struct cte, slots), j, sizeof(struct slot), struct slot), struct slot, capability), struct cap, cap_content), union content, object), struct cap_object, object_t),
              gos_nth(xs, j))
            which implies exists (j : Z), i == j && gos_preserved(h) */
        ++i;
    }
    return (unsigned int)SLOT_NULL_CAP;
}

#include "osverify_qcp/include/ios_cap_types.h"
#include "QCP_demos_LLM/verification_stdlib.h"
#include "QCP_demos_LLM/verification_list.h"

/* Authorized original declaration: OSCSpaceObjectPointer : Tarray Tint32 64.
 * Int32u notation is Tint32; use the shared sequential model's unsigned int. */
extern unsigned int OSCSpaceObjectPointer[64];
#define OBJ_POSITION 17U
/* Sequential projection: these named operations are retained, with no
 * interrupt/scheduler state in this model. No concurrency property is proved. */
#define ENTER_CRITICAL
#define EXIT_CRITICAL

/*@ Import Coq Require Import SimpleC.EE.osverify_qcp.cases.ucos_get_obj_slot_copy_independent_20261013_lib */
/*@ Extern Coq
    (copy_lookup_at : list Z -> Z -> Z)
    (copy_lookup_input_safe : Z -> Z -> Z -> Z -> list Z -> Prop)
    (copy_lookup_result : Z -> Z -> Z -> Z -> list Z -> Z -> Prop)
    (copy_lookup_read_safe : list Z -> Z -> Z -> Prop)
    (copy_lookup_scan_inv : list Z -> Z -> Z -> Z -> Prop)
    (copy_lookup_cells : Z -> Z -> Z -> list Z -> Assertion)
    (copy_lookup_cells_hole : Z -> Z -> Z -> list Z -> Z -> Assertion)
*/

unsigned int Get_Obj_Slot(unsigned char prio, void *func_object)
/*@ With (p : Z) (finish : Z) (xs : list Z) (prio0 : Z) (key0 : Z)
    Require
      0 <= prio && prio <= 255 && prio == prio0 && func_object == key0 &&
      copy_lookup_input_safe(prio, p, finish, func_object, xs) &&
      ((prio >= 63 && emp) ||
       (prio < 63 &&
        data_at(pointer_offset(&OSCSpaceObjectPointer, prio, sizeof(unsigned int), unsigned int), unsigned int, finish) *
        data_at(pointer_offset(&OSCSpacePrioTbl, prio, sizeof(struct cspace *), struct cspace *), struct cspace *, p) *
        ((p == 0 && emp) ||
         (p != 0 && copy_lookup_cells(p, sizeof(struct slot), 17, xs)))))
    Ensure
      copy_lookup_result(prio0, p, finish, key0, xs, __return) &&
      ((prio0 >= 63 && emp) ||
       (prio0 < 63 &&
        data_at(pointer_offset(&OSCSpaceObjectPointer, prio0, sizeof(unsigned int), unsigned int), unsigned int, finish) *
        data_at(pointer_offset(&OSCSpacePrioTbl, prio0, sizeof(struct cspace *), struct cspace *), struct cspace *, p) *
        ((p == 0 && emp) ||
         (p != 0 && copy_lookup_cells(p, sizeof(struct slot), 17, xs)))))
*/
{
    unsigned int i;
    unsigned int endPtr;
    CSPACE *pCSpace;
    if (prio >= OS_LOWEST_PRIO) {
        return (unsigned int)OS_PRIO_INVALID;
    }
    ENTER_CRITICAL;
    endPtr = OSCSpaceObjectPointer[prio];
    pCSpace = OSCSpacePrioTbl[prio];
    EXIT_CRITICAL;
    if (pCSpace == (CSPACE *)0) {
        return (unsigned int)SLOT_NULL_CAP;
    }
    i = OBJ_POSITION;
    /*@ Inv Assert
        prio == prio0 && func_object == key0 &&
        0 <= prio && prio < 63 && pCSpace == p && p != 0 &&
        endPtr == finish && copy_lookup_scan_inv(xs, func_object, finish, i) &&
        data_at(pointer_offset(&OSCSpaceObjectPointer, prio, sizeof(unsigned int), unsigned int), unsigned int, finish) *
        data_at(pointer_offset(&OSCSpacePrioTbl, prio, sizeof(struct cspace *), struct cspace *), struct cspace *, p) *
        copy_lookup_cells(p, sizeof(struct slot), 17, xs)
    */
    while (i < endPtr) {
        /*@ Assert
            exists v,
            prio == prio0 && func_object == key0 &&
            0 <= prio && prio < 63 && pCSpace == p && p != 0 &&
            endPtr == finish && copy_lookup_scan_inv(xs, func_object, finish, i) &&
            i < endPtr && i < 255 && v == copy_lookup_at(xs, i) &&
            data_at(pointer_offset(&OSCSpaceObjectPointer, prio, sizeof(unsigned int), unsigned int), unsigned int, finish) *
            data_at(pointer_offset(&OSCSpacePrioTbl, prio, sizeof(struct cspace *), struct cspace *), struct cspace *, p) *
            copy_lookup_cells_hole(p, sizeof(struct slot), 17, xs, i) *
            data_at(field_addr(field_addr(field_addr(field_addr(pointer_offset(field_addr(field_addr(pCSpace, struct cspace, cnode), struct cte, slots), i, sizeof(struct slot), struct slot), struct slot, capability), struct cap, cap_content), union content, object), struct cap_object, object_t),
                    void *, v)
        */
        if (pCSpace->cnode.slots[i].capability.cap_content.object.object_t == func_object) {
            return i;
        }
        ++i;
    }
    return (unsigned int)SLOT_NULL_CAP;
}

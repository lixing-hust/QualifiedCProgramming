/* First candidate, implementation-derived sequential model.
 * Counter source type: authorized Tarray Tint32 64, with Int32u := Tint32.
 * No proof/check has run; the lookup contract is this experiment dependency. */
#include "osverify_qcp/include/ios_cap_types.h"
#include "QCP_demos_LLM/verification_stdlib.h"
#include "QCP_demos_LLM/verification_list.h"
#define CNODE_COPY_FAILURE 6U
#define SLOT_RANGE_OVERFLOW 2U
/* Authorized original array type, 32-bit unsigned sequential C mapping. */
extern unsigned int OSCSpaceObjectPointer[64];
/*@ Import Coq Require Import SimpleC.EE.osverify_qcp.cases.ucos_get_obj_slot_copy_independent_20261013_lib */
/*@ Import Coq Require Import SimpleC.EE.osverify_qcp.cases.ucos_cnode_copy_independent_20261013_lib */
/*@ Extern Coq
    (copy_state :: *)
    (copy_cell :: *)
    (copy_cap :: *)
*/
/*@ Extern Coq
    (copy_table : copy_state -> Z -> Z)
    (copy_counter : copy_state -> Z -> Z)
    (copy_slots : copy_state -> Z -> Z -> copy_cap)
    (copy_tag : copy_cap -> Z)
    (copy_word0 : copy_cap -> Z)
    (copy_word1 : copy_cap -> Z)
    (copy_pointer : copy_cap -> Z)
    (copy_hole : list copy_cell -> Z -> Assertion)
    (copy_two_holes : list copy_cell -> Z -> Z -> Assertion)
    (copy_put : list copy_cell -> Z -> Z -> list copy_cell)
    (copy_lookup_resources : Z -> Z -> Z -> Z -> Z -> Z -> Z -> list Z -> Assertion)
    (copy_call_rest : list copy_cell -> Z -> Z -> Z -> Z -> Z -> Z -> list Z -> Assertion)
    (copy_lookup : copy_state -> Z -> Z -> Z -> Prop)
    (copy_call_records : list copy_cell -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> list Z -> Prop)
    (copy_lookup_agrees : copy_state -> Z -> list Z -> Prop)
    (copy_call_frame : list copy_cell -> Z -> Z -> Z -> Z -> Z -> Z -> list Z -> Assertion)
    (copy_allocation_state : list copy_cell -> list copy_cell -> copy_state -> Z -> Z -> Z -> Z -> Prop)
    (copy_heap : list copy_cell -> Assertion)
    (copy_pre : list copy_cell -> copy_state -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
    (copy_post : list copy_cell -> list copy_cell -> copy_state -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
    (copy_lookup_input_safe : Z -> Z -> Z -> Z -> list Z -> Prop)
    (copy_lookup_result : Z -> Z -> Z -> Z -> list Z -> Z -> Prop)
    (copy_lookup_cells : Z -> Z -> Z -> list Z -> Assertion)
*/

unsigned int Get_Obj_Slot(unsigned char prio, void *func_object)
/*@ With (p : Z) (finish : Z) (xs : list Z) (prio0 : Z) (key0 : Z)
    Require
      0 <= prio && prio <= 255 && prio == prio0 && func_object == key0 &&
      copy_lookup_input_safe(prio, p, finish, func_object, xs) &&
      copy_lookup_resources(&OSCSpacePrioTbl,&OSCSpaceObjectPointer,sizeof(struct cspace *),sizeof(struct slot),prio,p,finish,xs)
    Ensure
      copy_lookup_result(prio0, p, finish, key0, xs, __return) &&
      copy_lookup_resources(&OSCSpacePrioTbl,&OSCSpaceObjectPointer,sizeof(struct cspace *),sizeof(struct slot),prio0,p,finish,xs)
*/;

unsigned char ucos_CNode_Copy(unsigned char destTask_Prio,
                              unsigned char srcTask_Prio,
                              unsigned int func_capability)
/*@ With (a : copy_state) (h : list copy_cell) (d0 : Z) (s0 : Z) (f0 : Z)
    Require
      destTask_Prio == d0 && srcTask_Prio == s0 && func_capability == f0 &&
      copy_pre(h, a, &OSCSpacePrioTbl, &OSCSpaceObjectPointer,
               sizeof(struct cspace *), sizeof(struct slot),
               destTask_Prio, srcTask_Prio, func_capability) && copy_heap(h)
    Ensure
      exists hout,
      copy_post(h, hout, a, &OSCSpaceObjectPointer, sizeof(struct slot),
                d0, s0, f0,
                __return) && copy_heap(hout)
*/
{
    unsigned int idx;
    CSPACE *pCSpace1;
    CSPACE *pCSpace2;
    Cap *cap1;
    Cap *cap2;
    cap1 = (Cap *)0;
    cap2 = (Cap *)0;
    if (func_capability >= SLOT_NUM) {
        return CNODE_COPY_FAILURE;
    }
    if (destTask_Prio >= 64 || srcTask_Prio >= 64) {
        return CNODE_COPY_FAILURE;
    }
    /*@ Assert
      destTask_Prio == d0 && srcTask_Prio == s0 && func_capability == f0 &&
      f0 < 255 && d0 < 64 && s0 < 64 &&
      copy_pre(h, a, &OSCSpacePrioTbl, &OSCSpaceObjectPointer, sizeof(struct cspace *), sizeof(struct slot), d0, s0, f0) &&
      cap1 == 0 && cap2 == 0 &&
      copy_hole(h, pointer_offset(&OSCSpacePrioTbl, destTask_Prio, sizeof(struct cspace *), struct cspace *)) * data_at(pointer_offset(&OSCSpacePrioTbl, destTask_Prio, sizeof(struct cspace *), struct cspace *), struct cspace *, copy_table(a, d0)) *
      undef_data_at(&pCSpace1, struct cspace *) * undef_data_at(&pCSpace2, struct cspace *) * undef_data_at(&idx, unsigned int)
    */
    pCSpace1 = OSCSpacePrioTbl[destTask_Prio];
    /*@ Assert
      destTask_Prio == d0 && srcTask_Prio == s0 && func_capability == f0 &&
      f0 < 255 && d0 < 64 && s0 < 64 &&
      copy_pre(h, a, &OSCSpacePrioTbl, &OSCSpaceObjectPointer, sizeof(struct cspace *), sizeof(struct slot), d0, s0, f0) &&
      cap1 == 0 && cap2 == 0 && pCSpace1 == copy_table(a,d0) &&
      copy_hole(h, pointer_offset(&OSCSpacePrioTbl, srcTask_Prio, sizeof(struct cspace *), struct cspace *)) * data_at(pointer_offset(&OSCSpacePrioTbl, srcTask_Prio, sizeof(struct cspace *), struct cspace *), struct cspace *, copy_table(a, s0)) *
      undef_data_at(&pCSpace2, struct cspace *) * undef_data_at(&idx, unsigned int)
    */
    pCSpace2 = OSCSpacePrioTbl[srcTask_Prio];
    if (pCSpace1 == (CSPACE *)0 || pCSpace2 == (CSPACE *)0) {
        return CNODE_COPY_FAILURE;
    }
    cap1 = &(pCSpace1->cnode.slots[func_capability].capability);
    cap2 = &(pCSpace2->cnode.slots[func_capability].capability);
    /*@ Assert
      destTask_Prio == d0 && srcTask_Prio == s0 && func_capability == f0 &&
      f0 < 255 && d0 < 64 && s0 < 64 &&
      copy_pre(h, a, &OSCSpacePrioTbl, &OSCSpaceObjectPointer, sizeof(struct cspace *), sizeof(struct slot), d0, s0, f0) &&
      pCSpace1 == copy_table(a,d0) && pCSpace2 == copy_table(a,s0) && pCSpace1 != 0 && pCSpace2 != 0 &&
      cap1 == field_addr(pointer_offset(field_addr(field_addr(pCSpace1, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) && cap2 == field_addr(pointer_offset(field_addr(field_addr(pCSpace2, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) &&
      copy_hole(h, field_addr(cap2, struct cap, cap_type)) * data_at(field_addr(cap2, struct cap, cap_type), unsigned int, copy_tag(copy_slots(a,copy_table(a,s0),f0))) * undef_data_at(&idx, unsigned int)
    */
    if (cap2->cap_type == CAP_CATEGORY_TYPE) {
        /*@ Assert
      destTask_Prio == d0 && srcTask_Prio == s0 && func_capability == f0 &&
      f0 < 255 && d0 < 64 && s0 < 64 &&
      copy_pre(h, a, &OSCSpacePrioTbl, &OSCSpaceObjectPointer, sizeof(struct cspace *), sizeof(struct slot), d0, s0, f0) &&
      pCSpace1 == copy_table(a,d0) && pCSpace2 == copy_table(a,s0) && pCSpace1 != 0 && pCSpace2 != 0 &&
      cap1 == field_addr(pointer_offset(field_addr(field_addr(pCSpace1, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) && cap2 == field_addr(pointer_offset(field_addr(field_addr(pCSpace2, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) &&
      copy_tag(copy_slots(a,copy_table(a,s0),f0)) == 1 &&
      copy_hole(h,field_addr(cap1, struct cap, cap_type)) * undef_data_at(field_addr(cap1, struct cap, cap_type),unsigned int) * undef_data_at(&idx, unsigned int)
        */
        cap1->cap_type = CAP_CATEGORY_TYPE;
        /*@ Assert
      destTask_Prio == d0 && srcTask_Prio == s0 && func_capability == f0 &&
      f0 < 255 && d0 < 64 && s0 < 64 &&
      copy_pre(h, a, &OSCSpacePrioTbl, &OSCSpaceObjectPointer, sizeof(struct cspace *), sizeof(struct slot), d0, s0, f0) &&
      pCSpace1 == copy_table(a,d0) && pCSpace2 == copy_table(a,s0) && pCSpace1 != 0 && pCSpace2 != 0 &&
      cap1 == field_addr(pointer_offset(field_addr(field_addr(pCSpace1, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) && cap2 == field_addr(pointer_offset(field_addr(field_addr(pCSpace2, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) &&
      copy_tag(copy_slots(a,copy_table(a,s0),f0)) == 1 &&
      ((field_addr(field_addr(field_addr(cap1, struct cap, cap_content), union content, category), struct cap_category, category_content) == field_addr(field_addr(field_addr(cap2, struct cap, cap_content), union content, category), struct cap_category, category_content) && copy_hole(copy_put(h,field_addr(cap1, struct cap, cap_type),1),field_addr(field_addr(field_addr(cap2, struct cap, cap_content), union content, category), struct cap_category, category_content)) * data_at(field_addr(field_addr(field_addr(cap2, struct cap, cap_content), union content, category), struct cap_category, category_content),unsigned int,copy_word0(copy_slots(a,copy_table(a,s0),f0)))) ||
      (field_addr(field_addr(field_addr(cap1, struct cap, cap_content), union content, category), struct cap_category, category_content) != field_addr(field_addr(field_addr(cap2, struct cap, cap_content), union content, category), struct cap_category, category_content) && copy_two_holes(copy_put(h,field_addr(cap1, struct cap, cap_type),1),field_addr(field_addr(field_addr(cap1, struct cap, cap_content), union content, category), struct cap_category, category_content),field_addr(field_addr(field_addr(cap2, struct cap, cap_content), union content, category), struct cap_category, category_content)) * data_at(field_addr(field_addr(field_addr(cap2, struct cap, cap_content), union content, category), struct cap_category, category_content),unsigned int,copy_word0(copy_slots(a,copy_table(a,s0),f0))) * undef_data_at(field_addr(field_addr(field_addr(cap1, struct cap, cap_content), union content, category), struct cap_category, category_content),unsigned int))) * undef_data_at(&idx, unsigned int)
        */
        cap1->cap_content.category.category_content = cap2->cap_content.category.category_content;
        /*@ Assert
      destTask_Prio == d0 && srcTask_Prio == s0 && func_capability == f0 &&
      f0 < 255 && d0 < 64 && s0 < 64 &&
      copy_pre(h, a, &OSCSpacePrioTbl, &OSCSpaceObjectPointer, sizeof(struct cspace *), sizeof(struct slot), d0, s0, f0) &&
      pCSpace1 == copy_table(a,d0) && pCSpace2 == copy_table(a,s0) && pCSpace1 != 0 && pCSpace2 != 0 &&
      cap1 == field_addr(pointer_offset(field_addr(field_addr(pCSpace1, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) && cap2 == field_addr(pointer_offset(field_addr(field_addr(pCSpace2, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) &&
      copy_tag(copy_slots(a,copy_table(a,s0),f0)) == 1 &&
      ((field_addr(field_addr(field_addr(cap1, struct cap, cap_content), union content, category), struct cap_category, category_right) == field_addr(field_addr(field_addr(cap2, struct cap, cap_content), union content, category), struct cap_category, category_right) && copy_hole(copy_put(copy_put(h,field_addr(cap1, struct cap, cap_type),1),field_addr(field_addr(field_addr(cap1, struct cap, cap_content), union content, category), struct cap_category, category_content),copy_word0(copy_slots(a,copy_table(a,s0),f0))),field_addr(field_addr(field_addr(cap2, struct cap, cap_content), union content, category), struct cap_category, category_right)) * data_at(field_addr(field_addr(field_addr(cap2, struct cap, cap_content), union content, category), struct cap_category, category_right),unsigned int,copy_word1(copy_slots(a,copy_table(a,s0),f0)))) ||
      (field_addr(field_addr(field_addr(cap1, struct cap, cap_content), union content, category), struct cap_category, category_right) != field_addr(field_addr(field_addr(cap2, struct cap, cap_content), union content, category), struct cap_category, category_right) && copy_two_holes(copy_put(copy_put(h,field_addr(cap1, struct cap, cap_type),1),field_addr(field_addr(field_addr(cap1, struct cap, cap_content), union content, category), struct cap_category, category_content),copy_word0(copy_slots(a,copy_table(a,s0),f0))),field_addr(field_addr(field_addr(cap1, struct cap, cap_content), union content, category), struct cap_category, category_right),field_addr(field_addr(field_addr(cap2, struct cap, cap_content), union content, category), struct cap_category, category_right)) * data_at(field_addr(field_addr(field_addr(cap2, struct cap, cap_content), union content, category), struct cap_category, category_right),unsigned int,copy_word1(copy_slots(a,copy_table(a,s0),f0))) * undef_data_at(field_addr(field_addr(field_addr(cap1, struct cap, cap_content), union content, category), struct cap_category, category_right),unsigned int))) * undef_data_at(&idx, unsigned int)
        */
        cap1->cap_content.category.category_right = cap2->cap_content.category.category_right;
    } else {
        if (cap2->cap_type == CAP_OBJECT_TYPE) {
            void *lookup_object;
        /*@ Assert
      destTask_Prio == d0 && srcTask_Prio == s0 && func_capability == f0 &&
      f0 < 255 && d0 < 64 && s0 < 64 &&
      copy_pre(h, a, &OSCSpacePrioTbl, &OSCSpaceObjectPointer, sizeof(struct cspace *), sizeof(struct slot), d0, s0, f0) &&
      pCSpace1 == copy_table(a,d0) && pCSpace2 == copy_table(a,s0) && pCSpace1 != 0 && pCSpace2 != 0 &&
      cap1 == field_addr(pointer_offset(field_addr(field_addr(pCSpace1, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) && cap2 == field_addr(pointer_offset(field_addr(field_addr(pCSpace2, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) &&
      copy_tag(copy_slots(a,copy_table(a,s0),f0)) == 2 &&
      copy_hole(h,field_addr(field_addr(field_addr(cap2, struct cap, cap_content), union content, object), struct cap_object, object_t)) * data_at(field_addr(field_addr(field_addr(cap2, struct cap, cap_content), union content, object), struct cap_object, object_t),void *,copy_pointer(copy_slots(a,copy_table(a,s0),f0))) * undef_data_at(&idx, unsigned int) * undef_data_at(&lookup_object, void *)
        */
            lookup_object = cap2->cap_content.object.object_t;
        /*@ Assert
      exists xs,
      destTask_Prio == d0 && srcTask_Prio == s0 && func_capability == f0 &&
      f0 < 255 && d0 < 64 && s0 < 64 &&
      copy_pre(h, a, &OSCSpacePrioTbl, &OSCSpaceObjectPointer, sizeof(struct cspace *), sizeof(struct slot), d0, s0, f0) &&
      pCSpace1 == copy_table(a,d0) && pCSpace2 == copy_table(a,s0) && pCSpace1 != 0 && pCSpace2 != 0 &&
      cap1 == field_addr(pointer_offset(field_addr(field_addr(pCSpace1, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) && cap2 == field_addr(pointer_offset(field_addr(field_addr(pCSpace2, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) &&
      copy_tag(copy_slots(a,copy_table(a,s0),f0)) == 2 &&
      lookup_object == copy_pointer(copy_slots(a,copy_table(a,s0),f0)) && 0 <= d0 && d0 <= 255 &&
      copy_lookup_agrees(a,d0,xs) && copy_lookup_input_safe(d0,pCSpace1,copy_counter(a,d0),lookup_object,xs) &&
      copy_call_records(h,&OSCSpacePrioTbl,&OSCSpaceObjectPointer,sizeof(struct cspace *),sizeof(struct slot),d0,pCSpace1,copy_counter(a,d0),xs) &&
      copy_call_rest(h,&OSCSpacePrioTbl,&OSCSpaceObjectPointer,sizeof(struct cspace *),sizeof(struct slot),d0,pCSpace1,xs) *
      copy_lookup_resources(&OSCSpacePrioTbl,&OSCSpaceObjectPointer,sizeof(struct cspace *),sizeof(struct slot),d0,pCSpace1,copy_counter(a,d0),xs) * undef_data_at(&idx,unsigned int)
        */
            idx = Get_Obj_Slot(destTask_Prio, lookup_object) /*@ where p = pCSpace1, finish = copy_counter(a,d0), prio0 = destTask_Prio, key0 = lookup_object */;
        /*@ Assert
      destTask_Prio == d0 && srcTask_Prio == s0 && func_capability == f0 &&
      f0 < 255 && d0 < 64 && s0 < 64 &&
      copy_pre(h, a, &OSCSpacePrioTbl, &OSCSpaceObjectPointer, sizeof(struct cspace *), sizeof(struct slot), d0, s0, f0) &&
      pCSpace1 == copy_table(a,d0) && pCSpace2 == copy_table(a,s0) && pCSpace1 != 0 && pCSpace2 != 0 &&
      cap1 == field_addr(pointer_offset(field_addr(field_addr(pCSpace1, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) && cap2 == field_addr(pointer_offset(field_addr(field_addr(pCSpace2, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) &&
      copy_tag(copy_slots(a,copy_table(a,s0),f0)) == 2 &&
      lookup_object == copy_pointer(copy_slots(a,copy_table(a,s0),f0)) && copy_lookup(a,d0,lookup_object,idx) &&
      copy_heap(h)
        */

            if (idx == SLOT_NULL_CAP) {
        /*@ Assert
      destTask_Prio == d0 && srcTask_Prio == s0 && func_capability == f0 &&
      f0 < 255 && d0 < 64 && s0 < 64 &&
      copy_pre(h, a, &OSCSpacePrioTbl, &OSCSpaceObjectPointer, sizeof(struct cspace *), sizeof(struct slot), d0, s0, f0) &&
      pCSpace1 == copy_table(a,d0) && pCSpace2 == copy_table(a,s0) && pCSpace1 != 0 && pCSpace2 != 0 &&
      cap1 == field_addr(pointer_offset(field_addr(field_addr(pCSpace1, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) && cap2 == field_addr(pointer_offset(field_addr(field_addr(pCSpace2, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) &&
      copy_tag(copy_slots(a,copy_table(a,s0),f0)) == 2 &&
      lookup_object == copy_pointer(copy_slots(a,copy_table(a,s0),f0)) && idx == 0 && copy_lookup(a,d0,lookup_object,0) &&
      copy_hole(h,pointer_offset(&OSCSpaceObjectPointer, destTask_Prio, sizeof(unsigned int), unsigned int)) * data_at(pointer_offset(&OSCSpaceObjectPointer, destTask_Prio, sizeof(unsigned int), unsigned int),unsigned int,copy_counter(a,d0))
        */
                idx = OSCSpaceObjectPointer[destTask_Prio];
                if (idx >= SLOT_NUM) {
                    return SLOT_RANGE_OVERFLOW;
                }
                ++OSCSpaceObjectPointer[destTask_Prio];
            }
        /*@ Assert
      exists hc,
      destTask_Prio == d0 && srcTask_Prio == s0 && func_capability == f0 &&
      f0 < 255 && d0 < 64 && s0 < 64 &&
      copy_pre(h, a, &OSCSpacePrioTbl, &OSCSpaceObjectPointer, sizeof(struct cspace *), sizeof(struct slot), d0, s0, f0) &&
      pCSpace1 == copy_table(a,d0) && pCSpace2 == copy_table(a,s0) && pCSpace1 != 0 && pCSpace2 != 0 &&
      cap1 == field_addr(pointer_offset(field_addr(field_addr(pCSpace1, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) && cap2 == field_addr(pointer_offset(field_addr(field_addr(pCSpace2, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) &&
      copy_tag(copy_slots(a,copy_table(a,s0),f0)) == 2 &&
      lookup_object == copy_pointer(copy_slots(a,copy_table(a,s0),f0)) && copy_allocation_state(h,hc,a,&OSCSpaceObjectPointer,d0,lookup_object,idx) &&
      copy_heap(hc)
        */
            cap1 = &(pCSpace1->cnode.slots[idx].capability);
        /*@ Assert
      exists hc,
      destTask_Prio == d0 && srcTask_Prio == s0 && func_capability == f0 &&
      f0 < 255 && d0 < 64 && s0 < 64 &&
      copy_pre(h, a, &OSCSpacePrioTbl, &OSCSpaceObjectPointer, sizeof(struct cspace *), sizeof(struct slot), d0, s0, f0) &&
      pCSpace1 == copy_table(a,d0) && pCSpace2 == copy_table(a,s0) && pCSpace1 != 0 && pCSpace2 != 0 &&
      cap1 == field_addr(pointer_offset(field_addr(field_addr(pCSpace1, struct cspace, cnode), struct cte, slots), idx, sizeof(struct slot), struct slot), struct slot, capability) && cap2 == field_addr(pointer_offset(field_addr(field_addr(pCSpace2, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) &&
      copy_tag(copy_slots(a,copy_table(a,s0),f0)) == 2 &&
      lookup_object == copy_pointer(copy_slots(a,copy_table(a,s0),f0)) && copy_allocation_state(h,hc,a,&OSCSpaceObjectPointer,d0,lookup_object,idx) &&
      copy_hole(hc,field_addr(cap1, struct cap, cap_type)) * undef_data_at(field_addr(cap1, struct cap, cap_type),unsigned int)
        */
            cap1->cap_type = CAP_OBJECT_TYPE;
        /*@ Assert
      exists hc,
      destTask_Prio == d0 && srcTask_Prio == s0 && func_capability == f0 &&
      f0 < 255 && d0 < 64 && s0 < 64 &&
      copy_pre(h, a, &OSCSpacePrioTbl, &OSCSpaceObjectPointer, sizeof(struct cspace *), sizeof(struct slot), d0, s0, f0) &&
      pCSpace1 == copy_table(a,d0) && pCSpace2 == copy_table(a,s0) && pCSpace1 != 0 && pCSpace2 != 0 &&
      cap1 == field_addr(pointer_offset(field_addr(field_addr(pCSpace1, struct cspace, cnode), struct cte, slots), idx, sizeof(struct slot), struct slot), struct slot, capability) && cap2 == field_addr(pointer_offset(field_addr(field_addr(pCSpace2, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) &&
      copy_tag(copy_slots(a,copy_table(a,s0),f0)) == 2 &&
      lookup_object == copy_pointer(copy_slots(a,copy_table(a,s0),f0)) && copy_allocation_state(h,hc,a,&OSCSpaceObjectPointer,d0,lookup_object,idx) &&
      ((field_addr(field_addr(field_addr(cap1,struct cap,cap_content),union content,object),struct cap_object,object_right) == field_addr(field_addr(field_addr(cap2,struct cap,cap_content),union content,object),struct cap_object,object_right) && copy_hole(copy_put(hc,field_addr(cap1, struct cap, cap_type),2),field_addr(field_addr(field_addr(cap2,struct cap,cap_content),union content,object),struct cap_object,object_right)) * data_at(field_addr(field_addr(field_addr(cap2,struct cap,cap_content),union content,object),struct cap_object,object_right),unsigned int,copy_word0(copy_slots(a,copy_table(a,s0),f0)))) ||
      (field_addr(field_addr(field_addr(cap1,struct cap,cap_content),union content,object),struct cap_object,object_right) != field_addr(field_addr(field_addr(cap2,struct cap,cap_content),union content,object),struct cap_object,object_right) && copy_two_holes(copy_put(hc,field_addr(cap1, struct cap, cap_type),2),field_addr(field_addr(field_addr(cap1,struct cap,cap_content),union content,object),struct cap_object,object_right),field_addr(field_addr(field_addr(cap2,struct cap,cap_content),union content,object),struct cap_object,object_right)) * data_at(field_addr(field_addr(field_addr(cap2,struct cap,cap_content),union content,object),struct cap_object,object_right),unsigned int,copy_word0(copy_slots(a,copy_table(a,s0),f0))) * undef_data_at(field_addr(field_addr(field_addr(cap1,struct cap,cap_content),union content,object),struct cap_object,object_right),unsigned int)))
        */
            cap1->cap_content.object.object_right = cap2->cap_content.object.object_right;
        /*@ Assert
      exists hc,
      destTask_Prio == d0 && srcTask_Prio == s0 && func_capability == f0 &&
      f0 < 255 && d0 < 64 && s0 < 64 &&
      copy_pre(h, a, &OSCSpacePrioTbl, &OSCSpaceObjectPointer, sizeof(struct cspace *), sizeof(struct slot), d0, s0, f0) &&
      pCSpace1 == copy_table(a,d0) && pCSpace2 == copy_table(a,s0) && pCSpace1 != 0 && pCSpace2 != 0 &&
      cap1 == field_addr(pointer_offset(field_addr(field_addr(pCSpace1, struct cspace, cnode), struct cte, slots), idx, sizeof(struct slot), struct slot), struct slot, capability) && cap2 == field_addr(pointer_offset(field_addr(field_addr(pCSpace2, struct cspace, cnode), struct cte, slots), func_capability, sizeof(struct slot), struct slot), struct slot, capability) &&
      copy_tag(copy_slots(a,copy_table(a,s0),f0)) == 2 &&
      lookup_object == copy_pointer(copy_slots(a,copy_table(a,s0),f0)) && copy_allocation_state(h,hc,a,&OSCSpaceObjectPointer,d0,lookup_object,idx) &&
      ((field_addr(field_addr(field_addr(cap1,struct cap,cap_content),union content,object),struct cap_object,object_t) == field_addr(field_addr(field_addr(cap2,struct cap,cap_content),union content,object),struct cap_object,object_t) && copy_hole(copy_put(copy_put(hc,field_addr(cap1, struct cap, cap_type),2),field_addr(field_addr(field_addr(cap1,struct cap,cap_content),union content,object),struct cap_object,object_right),copy_word0(copy_slots(a,copy_table(a,s0),f0))),field_addr(field_addr(field_addr(cap2,struct cap,cap_content),union content,object),struct cap_object,object_t)) * data_at(field_addr(field_addr(field_addr(cap2,struct cap,cap_content),union content,object),struct cap_object,object_t),void *,copy_pointer(copy_slots(a,copy_table(a,s0),f0)))) ||
      (field_addr(field_addr(field_addr(cap1,struct cap,cap_content),union content,object),struct cap_object,object_t) != field_addr(field_addr(field_addr(cap2,struct cap,cap_content),union content,object),struct cap_object,object_t) && copy_two_holes(copy_put(copy_put(hc,field_addr(cap1, struct cap, cap_type),2),field_addr(field_addr(field_addr(cap1,struct cap,cap_content),union content,object),struct cap_object,object_right),copy_word0(copy_slots(a,copy_table(a,s0),f0))),field_addr(field_addr(field_addr(cap1,struct cap,cap_content),union content,object),struct cap_object,object_t),field_addr(field_addr(field_addr(cap2,struct cap,cap_content),union content,object),struct cap_object,object_t)) * data_at(field_addr(field_addr(field_addr(cap2,struct cap,cap_content),union content,object),struct cap_object,object_t),void *,copy_pointer(copy_slots(a,copy_table(a,s0),f0))) * undef_data_at(field_addr(field_addr(field_addr(cap1,struct cap,cap_content),union content,object),struct cap_object,object_t),void *)))
        */
            cap1->cap_content.object.object_t = cap2->cap_content.object.object_t;
            return (unsigned char)CNODE_NONE_FAULT;
        } else {
            return CNODE_COPY_FAILURE;
        }
    }
    return (unsigned char)CNODE_NONE_FAULT;
}

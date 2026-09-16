/* Sequential transcription of certiucos/code/ios_cap.v:
 * ucos_CNode_Delete_impl. Layout matches the existing ucos_Grant_Cap case.
 * Authoritative legacy contract: proofs/capability/lib/CapSpec.v,
 * ucos_CNode_DeletePre'/Post'. No executable critical-section primitive
 * occurs in this leaf function.
 */
#include "include/ios_cap_types.h"

/*@ Extern Coq (delete_slot_transition : Z -> Z -> Z -> Z -> Z -> Z ->
                                         Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.osverify_qcp.cases.ucos_CNode_Delete_lib */

/* These contracts expose a selected table entry and the complete slot storage.
 * All other table entries, slots, CSpace fields and OS resources are frames.
 * They instantiate the sequential storage update of the legacy global spec;
 * the legacy AOSCSpacePrioTbl abstraction and interrupt invariants are not
 * themselves encoded or proved by this local QCP contract.
 */
unsigned char ucos_CNode_Delete(unsigned char destTask_Prio,
                                unsigned int func_capability)
/*@ slot_invalid
    With (dest slot : Z)
    Require destTask_Prio == dest && func_capability == slot &&
      0 <= dest && dest <= 255 && unsigned_last_nbits(dest, 32) == dest &&
      SLOT_NUM <= slot && slot <= UINT_MAX && emp
    Ensure __return == CNODE_DELETE_FAILURE && emp
 */
/*@ prio_invalid
    With (dest slot : Z)
    Require destTask_Prio == dest && func_capability == slot &&
      64 <= dest && dest <= 255 && unsigned_last_nbits(dest, 32) == dest &&
      0 <= slot && slot < SLOT_NUM && emp
    Ensure __return == CNODE_DELETE_FAILURE && emp
 */
/*@ null_target
    With (dest slot : Z)
    Require destTask_Prio == dest && func_capability == slot &&
      0 <= dest && dest < 64 && unsigned_last_nbits(dest, 32) == dest &&
      0 <= slot && slot < SLOT_NUM &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, 0)
    Ensure __return == CNODE_DELETE_FAILURE &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, 0)
 */
/*@ unsupported_cap
    With (dest slot target old_slot old_cap word0 word1 ptr : Z)
    Require destTask_Prio == dest && func_capability == slot &&
      0 <= dest && dest < 64 && unsigned_last_nbits(dest, 32) == dest &&
      0 <= slot && slot < SLOT_NUM && target != 0 &&
      old_cap != CAP_CATEGORY_TYPE && old_cap != CAP_OBJECT_TYPE &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(&(target->cnode.slots[slot].slot_type), unsigned int, old_slot) *
      store(&(target->cnode.slots[slot].capability.cap_type), unsigned int, old_cap) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_content), unsigned int, word0) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_right), unsigned int, word1) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.Dummy_ptr), void *, ptr)
    Ensure __return == CNODE_DELETE_FAILURE &&
      delete_slot_transition(__return, old_slot, old_cap, word0, word1, ptr,
                             old_slot, old_cap, word0, word1, ptr) &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(&(target->cnode.slots[slot].slot_type), unsigned int, old_slot) *
      store(&(target->cnode.slots[slot].capability.cap_type), unsigned int, old_cap) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_content), unsigned int, word0) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_right), unsigned int, word1) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.Dummy_ptr), void *, ptr)
 */
/*@ category_cap
    With (dest slot target old_slot word0 word1 ptr : Z)
    Require destTask_Prio == dest && func_capability == slot &&
      0 <= dest && dest < 64 && unsigned_last_nbits(dest, 32) == dest &&
      0 <= slot && slot < SLOT_NUM && target != 0 &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(&(target->cnode.slots[slot].slot_type), unsigned int, old_slot) *
      store(&(target->cnode.slots[slot].capability.cap_type), unsigned int, CAP_CATEGORY_TYPE) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_content), unsigned int, word0) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_right), unsigned int, word1) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.Dummy_ptr), void *, ptr)
    Ensure __return == CNODE_NONE_FAULT &&
      delete_slot_transition(__return, old_slot, CAP_CATEGORY_TYPE, word0, word1, ptr,
                             0, 0, 0, 0, ptr) &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(&(target->cnode.slots[slot].slot_type), unsigned int, 0) *
      store(&(target->cnode.slots[slot].capability.cap_type), unsigned int, 0) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_content), unsigned int, 0) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_right), unsigned int, 0) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.Dummy_ptr), void *, ptr)
 */
/*@ object_cap
    With (dest slot target old_slot word0 word1 ptr : Z)
    Require destTask_Prio == dest && func_capability == slot &&
      0 <= dest && dest < 64 && unsigned_last_nbits(dest, 32) == dest &&
      0 <= slot && slot < SLOT_NUM && target != 0 &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(&(target->cnode.slots[slot].slot_type), unsigned int, old_slot) *
      store(&(target->cnode.slots[slot].capability.cap_type), unsigned int, CAP_OBJECT_TYPE) *
      store(&(target->cnode.slots[slot].capability.cap_content.object.object_right), unsigned int, word0) *
      store(&(target->cnode.slots[slot].capability.cap_content.object.Dummy_int), unsigned int, word1) *
      store(&(target->cnode.slots[slot].capability.cap_content.object.object_t), void *, ptr)
    Ensure __return == CNODE_NONE_FAULT &&
      delete_slot_transition(__return, old_slot, CAP_OBJECT_TYPE, word0, word1, ptr,
                             0, 0, 0, word1, 0) &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(&(target->cnode.slots[slot].slot_type), unsigned int, 0) *
      store(&(target->cnode.slots[slot].capability.cap_type), unsigned int, 0) *
      store(&(target->cnode.slots[slot].capability.cap_content.object.object_right), unsigned int, 0) *
      store(&(target->cnode.slots[slot].capability.cap_content.object.Dummy_int), unsigned int, word1) *
      store(&(target->cnode.slots[slot].capability.cap_content.object.object_t), void *, 0)
 */;

unsigned char ucos_CNode_Delete(unsigned char destTask_Prio,
                                unsigned int func_capability)
/*@ slot_invalid */
/*@ prio_invalid */
/*@ null_target */
/*@ unsupported_cap */
/*@ category_cap */
/*@ object_cap */
{
    CSPACE *pCSpace1;
    Cap *cap1;
    if (func_capability >= SLOT_NUM) {
        return CNODE_DELETE_FAILURE;
    }
    if (destTask_Prio >= 64U) {
        return CNODE_DELETE_FAILURE;
    }
    pCSpace1 = OSCSpacePrioTbl[destTask_Prio];
    if (pCSpace1 == (CSPACE *)0) {
        return CNODE_DELETE_FAILURE;
    }
    cap1 = &pCSpace1->cnode.slots[func_capability].capability;
    if (cap1->cap_type == CAP_CATEGORY_TYPE) {
        cap1->cap_type = 0U;
        cap1->cap_content.category.category_content = 0U;
        cap1->cap_content.category.category_right = 0U;
    } else {
        if (cap1->cap_type == CAP_OBJECT_TYPE) {
            cap1->cap_type = 0U;
            cap1->cap_content.object.object_right = 0U;
            cap1->cap_content.object.object_t = (void *)0;
        } else {
            return (unsigned char)CNODE_DELETE_FAILURE;
        }
    }
    pCSpace1->cnode.slots[func_capability].slot_type = SLOT_NULL_CAP;
    return (unsigned char)CNODE_NONE_FAULT;
}

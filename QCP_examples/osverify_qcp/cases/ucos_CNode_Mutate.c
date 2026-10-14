#include "include/ios_cap_types.h"

/* Sequential transcription of ios_cap.v: ucos_CNode_Mutate_impl.
 * Source update order is intentional, including when the two spaces alias. */
#define CNODE_MUTATE_FAILURE 8U

/*@ Extern Coq
      (mutate_alias_fields : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (mutate_distinct_fields : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z ->
                                Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.osverify_qcp.cases.ucos_CNode_Mutate_lib */

/* The seven footprints cover early failures and every priority/CSpace alias
 * layout. Untouched pointer fields, the destination tag, other slots and other
 * table entries are disjoint frames. Aliased slots are owned exactly once. */
unsigned char ucos_CNode_Mutate(unsigned char destTask_Prio,
                               unsigned char srcTask_Prio,
                               unsigned int func_capability,
                               unsigned int rights)
/*@ class_invalid
    With (dest src slot requested : Z)
    Require destTask_Prio == dest && srcTask_Prio == src &&
      func_capability == slot && rights == requested &&
      0 <= dest && dest <= 255 && 0 <= src && src <= 255 &&
      unsigned_last_nbits(dest, 32) == dest &&
      unsigned_last_nbits(src, 32) == src &&
      CAP_CHANNEL_CLASS < slot && slot <= UINT_MAX &&
      0 <= requested && requested <= UINT_MAX && emp
    Ensure __return == CNODE_MUTATE_FAILURE && emp
 */
/*@ prio_invalid
    With (dest src slot requested : Z)
    Require destTask_Prio == dest && srcTask_Prio == src &&
      func_capability == slot && rights == requested &&
      0 <= dest && dest <= 255 && 0 <= src && src <= 255 &&
      unsigned_last_nbits(dest, 32) == dest &&
      unsigned_last_nbits(src, 32) == src &&
      (64 <= dest || 64 <= src) &&
      0 <= slot && slot <= CAP_CHANNEL_CLASS &&
      0 <= requested && requested <= UINT_MAX && emp
    Ensure __return == CNODE_MUTATE_FAILURE && emp
 */
/*@ null_same_priority
    With (prio slot requested : Z)
    Require destTask_Prio == prio && srcTask_Prio == prio &&
      func_capability == slot && rights == requested &&
      0 <= prio && prio < 64 && unsigned_last_nbits(prio, 32) == prio &&
      0 <= slot && slot <= CAP_CHANNEL_CLASS &&
      0 <= requested && requested <= UINT_MAX &&
      store(pointer_offset(&(OSCSpacePrioTbl), prio,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, 0)
    Ensure __return == CNODE_MUTATE_FAILURE &&
      store(pointer_offset(&(OSCSpacePrioTbl), prio,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, 0)
 */
/*@ null_distinct_priorities
    With (dest src slot requested target source : Z)
    Require destTask_Prio == dest && srcTask_Prio == src &&
      func_capability == slot && rights == requested &&
      0 <= dest && dest < 64 && 0 <= src && src < 64 && dest != src &&
      unsigned_last_nbits(dest, 32) == dest &&
      unsigned_last_nbits(src, 32) == src &&
      0 <= slot && slot <= CAP_CHANNEL_CLASS &&
      0 <= requested && requested <= UINT_MAX &&
      (target == 0 || source == 0) &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(pointer_offset(&(OSCSpacePrioTbl), src,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, source)
    Ensure __return == CNODE_MUTATE_FAILURE &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(pointer_offset(&(OSCSpacePrioTbl), src,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, source)
 */
/*@ same_priority
    With (prio slot requested target old_tag old_kind word0 word1 : Z)
    Require destTask_Prio == prio && srcTask_Prio == prio &&
      func_capability == slot && rights == requested &&
      0 <= prio && prio < 64 && unsigned_last_nbits(prio, 32) == prio &&
      0 <= slot && slot <= CAP_CHANNEL_CLASS && target != 0 &&
      0 <= requested && requested <= UINT_MAX &&
      0 <= word1 && word1 <= UINT_MAX &&
      store(pointer_offset(&(OSCSpacePrioTbl), prio,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(&(target->cnode.slots[slot].slot_type), unsigned int, old_tag) *
      store(&(target->cnode.slots[slot].capability.cap_type), unsigned int, old_kind) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_content), unsigned int, word0) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_right), unsigned int, word1)
    Ensure exists new_tag new_kind new_word0 new_word1,
      mutate_alias_fields(__return, requested, old_tag, old_kind, word0, word1,
                          new_tag, new_kind, new_word0, new_word1) &&
      store(pointer_offset(&(OSCSpacePrioTbl), prio,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(&(target->cnode.slots[slot].slot_type), unsigned int, new_tag) *
      store(&(target->cnode.slots[slot].capability.cap_type), unsigned int, new_kind) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_content), unsigned int, new_word0) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_right), unsigned int, new_word1)
 */
/*@ shared_cspace
    With (dest src slot requested target old_tag old_kind word0 word1 : Z)
    Require destTask_Prio == dest && srcTask_Prio == src &&
      func_capability == slot && rights == requested &&
      0 <= dest && dest < 64 && 0 <= src && src < 64 && dest != src &&
      unsigned_last_nbits(dest, 32) == dest &&
      unsigned_last_nbits(src, 32) == src &&
      0 <= slot && slot <= CAP_CHANNEL_CLASS && target != 0 &&
      0 <= requested && requested <= UINT_MAX &&
      0 <= word1 && word1 <= UINT_MAX &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(pointer_offset(&(OSCSpacePrioTbl), src,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(&(target->cnode.slots[slot].slot_type), unsigned int, old_tag) *
      store(&(target->cnode.slots[slot].capability.cap_type), unsigned int, old_kind) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_content), unsigned int, word0) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_right), unsigned int, word1)
    Ensure exists new_tag new_kind new_word0 new_word1,
      mutate_alias_fields(__return, requested, old_tag, old_kind, word0, word1,
                          new_tag, new_kind, new_word0, new_word1) &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(pointer_offset(&(OSCSpacePrioTbl), src,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(&(target->cnode.slots[slot].slot_type), unsigned int, new_tag) *
      store(&(target->cnode.slots[slot].capability.cap_type), unsigned int, new_kind) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_content), unsigned int, new_word0) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_right), unsigned int, new_word1)
 */
/*@ distinct_cspaces
    With (dest src slot requested target source src_tag
          src_kind src_word0 src_word1 dst_kind dst_word0 dst_word1 : Z)
    Require destTask_Prio == dest && srcTask_Prio == src &&
      func_capability == slot && rights == requested &&
      0 <= dest && dest < 64 && 0 <= src && src < 64 && dest != src &&
      unsigned_last_nbits(dest, 32) == dest &&
      unsigned_last_nbits(src, 32) == src &&
      0 <= slot && slot <= CAP_CHANNEL_CLASS &&
      target != 0 && source != 0 && target != source &&
      0 <= requested && requested <= UINT_MAX &&
      0 <= src_word1 && src_word1 <= UINT_MAX &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(pointer_offset(&(OSCSpacePrioTbl), src,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, source) *
      store(&(source->cnode.slots[slot].slot_type), unsigned int, src_tag) *
      store(&(source->cnode.slots[slot].capability.cap_type), unsigned int, src_kind) *
      store(&(source->cnode.slots[slot].capability.cap_content.category.category_content), unsigned int, src_word0) *
      store(&(source->cnode.slots[slot].capability.cap_content.category.category_right), unsigned int, src_word1) *
      store(&(target->cnode.slots[slot].capability.cap_type), unsigned int, dst_kind) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_content), unsigned int, dst_word0) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_right), unsigned int, dst_word1)
    Ensure exists new_src_tag new_src_word1 new_dst_kind new_dst_word0 new_dst_word1,
      mutate_distinct_fields(__return, requested, src_tag, src_kind, src_word0, src_word1,
                             dst_kind, dst_word0, dst_word1, new_src_tag, new_src_word1,
                             new_dst_kind, new_dst_word0, new_dst_word1) &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(pointer_offset(&(OSCSpacePrioTbl), src,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, source) *
      store(&(source->cnode.slots[slot].slot_type), unsigned int, new_src_tag) *
      store(&(source->cnode.slots[slot].capability.cap_type), unsigned int, src_kind) *
      store(&(source->cnode.slots[slot].capability.cap_content.category.category_content), unsigned int, src_word0) *
      store(&(source->cnode.slots[slot].capability.cap_content.category.category_right), unsigned int, new_src_word1) *
      store(&(target->cnode.slots[slot].capability.cap_type), unsigned int, new_dst_kind) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_content), unsigned int, new_dst_word0) *
      store(&(target->cnode.slots[slot].capability.cap_content.category.category_right), unsigned int, new_dst_word1)
 */;

unsigned char ucos_CNode_Mutate(unsigned char destTask_Prio,
                               unsigned char srcTask_Prio,
                               unsigned int func_capability,
                               unsigned int rights)
/*@ class_invalid */
/*@ prio_invalid */
/*@ null_same_priority */
/*@ null_distinct_priorities */
/*@ same_priority */
/*@ shared_cspace */
/*@ distinct_cspaces */
{
    CSPACE *pCSpace1;
    CSPACE *pCSpace2;
    Cap *cap1;
    Cap *cap2;

    if (CAP_NULL_CLASS > func_capability || func_capability > CAP_CHANNEL_CLASS) {
        return CNODE_MUTATE_FAILURE;
    }
    if (destTask_Prio >= 64U || srcTask_Prio >= 64U) {
        return CNODE_MUTATE_FAILURE;
    }
    pCSpace1 = OSCSpacePrioTbl[destTask_Prio];
    pCSpace2 = OSCSpacePrioTbl[srcTask_Prio];
    if (pCSpace1 == (CSPACE *)0 || pCSpace2 == (CSPACE *)0) {
        return CNODE_MUTATE_FAILURE;
    }
    cap1 = &pCSpace1->cnode.slots[func_capability].capability;
    cap2 = &pCSpace2->cnode.slots[func_capability].capability;
    if (cap2->cap_type == CAP_CATEGORY_TYPE &&
        ((~cap2->cap_content.category.category_right) & rights) == 0U &&
        cap2->cap_content.category.category_right != rights) {
        cap1->cap_type = CAP_CATEGORY_TYPE;
        cap1->cap_content.category.category_content =
            cap2->cap_content.category.category_content;
        cap1->cap_content.category.category_right = rights;
        cap2->cap_content.category.category_right &= ~rights;
    } else {
        return (unsigned char)CNODE_MUTATE_FAILURE;
    }
    pCSpace2->cnode.slots[func_capability].slot_type = SLOT_NULL_CAP;
    return (unsigned char)CNODE_NONE_FAULT;
}

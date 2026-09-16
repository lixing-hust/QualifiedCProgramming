#ifndef OSVERIFY_QCP_UCOS_GRANT_CAP_SPEC_H
#define OSVERIFY_QCP_UCOS_GRANT_CAP_SPEC_H
#include "ios_cap_types.h"

/* Shared declaration: the implementation and all callers use this contract. */
/*@ Extern Coq (grant_cap_transition : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.osverify_qcp.cap_model */

unsigned char ucos_Grant_Cap(unsigned char destTask_Prio,
                             unsigned int cap_Class,
                             unsigned int cap_Right)
/*@ class_invalid
    With (dest class right : Z)
    Require
      destTask_Prio == dest && cap_Class == class && cap_Right == right &&
      0 <= dest && dest <= 255 &&
      unsigned_last_nbits(dest, 32) == dest &&
      0 <= class && class <= UINT_MAX &&
      0 <= right && right <= UINT_MAX &&
      class > CAP_CHANNEL_CLASS && emp
    Ensure
      __return == CNODE_GRANT_FAILURE && emp
 */
/*@ prio_invalid
    With (dest class right : Z)
    Require
      destTask_Prio == dest && cap_Class == class && cap_Right == right &&
      0 <= dest && dest <= 255 &&
      unsigned_last_nbits(dest, 32) == dest &&
      0 <= class && class <= CAP_CHANNEL_CLASS &&
      0 <= right && right <= UINT_MAX &&
      unsigned_last_nbits(dest, 32) >= 64 && emp
    Ensure
      __return == CNODE_GRANT_FAILURE && emp
 */
/*@ null_target
    With (target dest class right : Z)
    Require
      destTask_Prio == dest && cap_Class == class && cap_Right == right &&
      0 <= dest && dest <= 255 &&
      unsigned_last_nbits(dest, 32) == dest &&
      0 <= class && class <= CAP_CHANNEL_CLASS &&
      0 <= right && right <= UINT_MAX &&
      unsigned_last_nbits(dest, 32) < 64 && target == 0 &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target)
    Ensure
      __return == CNODE_GRANT_FAILURE &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, 0)
 */
/*@ valid_target
    With (target dest class right : Z)
         (old_type old_content old_right : Z)
    Require
      destTask_Prio == dest && cap_Class == class && cap_Right == right &&
      0 <= dest && dest <= 255 &&
      unsigned_last_nbits(dest, 32) == dest &&
      0 <= class && class <= CAP_CHANNEL_CLASS &&
      0 <= right && right <= UINT_MAX &&
      unsigned_last_nbits(dest, 32) < 64 && target != 0 &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(&(target->cnode.slots[class].capability.cap_type),
            unsigned int, old_type) *
      store(&(target->cnode.slots[class].capability.cap_content.category.category_content),
            unsigned int, old_content) *
      store(&(target->cnode.slots[class].capability.cap_content.category.category_right),
            unsigned int, old_right)
    Ensure
      __return == CNODE_NONE_FAULT &&
      grant_cap_transition(__return, class, right, old_type, old_content, old_right,
                           CAP_CATEGORY_TYPE, class, (old_right & 4095) | right) &&
      store(pointer_offset(&(OSCSpacePrioTbl), dest,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      store(&(target->cnode.slots[class].capability.cap_type),
            unsigned int, CAP_CATEGORY_TYPE) *
      store(&(target->cnode.slots[class].capability.cap_content.category.category_content),
            unsigned int, class) *
      store(&(target->cnode.slots[class].capability.cap_content.category.category_right),
            unsigned int, (old_right & 4095) | right)
 */;
#endif

#include "include/ucos_Grant_Cap_spec.h"

/*
 * Sequential transcription of grant_cspace_cap_impl.  The original
 * ENTER_CRITICAL/EXIT_CRITICAL operations are deliberately omitted here:
 * this case verifies only the single-threaded control flow and the call to
 * ucos_Grant_Cap.  Their concurrency semantics will be introduced in a
 * separate refinement.
 */
unsigned char grant_cspace_cap(unsigned char destTask_Prio,
                               unsigned int cap_Class,
                               unsigned int cap_Right)
/*@ With (dest class right current_tcb current_prio old_os_prio : Z)
          (running current_space parent grant_right target : Z)
          (old_type old_content old_right : Z)
    Require
      destTask_Prio == dest && cap_Class == class && cap_Right == right &&
      0 <= dest && dest <= 255 &&
      unsigned_last_nbits(dest, 32) == dest &&
      0 <= class && class <= UINT_MAX &&
      0 <= right && right <= UINT_MAX &&
      ((dest >= OS_LOWEST_PRIO && emp) ||
       (dest < OS_LOWEST_PRIO &&
        current_tcb != 0 &&
        0 <= current_prio && current_prio < 64 &&
        current_prio != dest && current_space != target &&
        store(&(OSTCBCur), struct os_tcb *, current_tcb) *
        store(&(current_tcb->OSTCBPrio), unsigned char, current_prio) *
        store(&(OSPrioCur), unsigned char, old_os_prio) *
        store(pointer_offset(&(OSCSpacePrioTbl), current_prio,
                             sizeof(struct cspace *), struct cspace *),
              struct cspace *, current_space) *
        ((current_space == 0 && emp) ||
         (current_space != 0 &&
          store(&(OSRunning), unsigned char, running) *
          store(&(current_space->cnode.slots[SLOT_CNODE_CAP]
                    .capability.cap_content.category.category_right),
                unsigned int, grant_right) *
          store(pointer_offset(&(CapParent), dest,
                               sizeof(unsigned char), unsigned char),
                unsigned char, parent) *
          (((class <= CAP_CHANNEL_CLASS) &&
            store(pointer_offset(&(OSCSpacePrioTbl), dest,
                                 sizeof(struct cspace *), struct cspace *),
                  struct cspace *, target) *
            ((target == 0 && emp) ||
             (target != 0 &&
              store(&(target->cnode.slots[class].capability.cap_type),
                    unsigned int, old_type) *
              store(&(target->cnode.slots[class].capability.cap_content.category.category_content),
                    unsigned int, old_content) *
              store(&(target->cnode.slots[class].capability.cap_content.category.category_right),
                    unsigned int, old_right)))) ||
           (class > CAP_CHANNEL_CLASS && emp))))))
    Ensure
      ((__return == OS_PRIO_INVALID && dest >= OS_LOWEST_PRIO && emp) ||
       (dest < OS_LOWEST_PRIO &&
        store(&(OSTCBCur), struct os_tcb *, current_tcb) *
        store(&(current_tcb->OSTCBPrio), unsigned char, current_prio) *
        store(&(OSPrioCur), unsigned char, current_prio) *
        store(pointer_offset(&(OSCSpacePrioTbl), current_prio,
                             sizeof(struct cspace *), struct cspace *),
              struct cspace *, current_space) *
        (((current_space == 0 && __return == CNODE_GRANT_FAILURE) && emp) ||
         (current_space != 0 &&
          store(&(OSRunning), unsigned char, running) *
          store(&(current_space->cnode.slots[SLOT_CNODE_CAP]
                    .capability.cap_content.category.category_right),
                unsigned int, grant_right) *
          store(pointer_offset(&(CapParent), dest,
                               sizeof(unsigned char), unsigned char),
                unsigned char, parent) *
          (((running == CFalse ||
             ((grant_right & CNODE_GRANT_CAP) != 0 &&
              parent == current_prio)) &&
            (((class <= CAP_CHANNEL_CLASS && target != 0 &&
               __return == CSPACE_NONE_FAULT) &&
              store(pointer_offset(&(OSCSpacePrioTbl), dest,
                                   sizeof(struct cspace *), struct cspace *),
                    struct cspace *, target) *
              store(&(target->cnode.slots[class].capability.cap_type),
                    unsigned int, CAP_CATEGORY_TYPE) *
              store(&(target->cnode.slots[class].capability.cap_content.category.category_content),
                    unsigned int, class) *
              store(&(target->cnode.slots[class].capability.cap_content.category.category_right),
                    unsigned int, (old_right & 4095) | right)) ||
             (((class > CAP_CHANNEL_CLASS || target == 0) &&
               __return == CNODE_GRANT_FAILURE) &&
              (((class <= CAP_CHANNEL_CLASS) &&
                store(pointer_offset(&(OSCSpacePrioTbl), dest,
                                     sizeof(struct cspace *), struct cspace *),
                      struct cspace *, target) *
                ((target == 0 && emp) ||
                 (target != 0 &&
                  store(&(target->cnode.slots[class].capability.cap_type),
                        unsigned int, old_type) *
                  store(&(target->cnode.slots[class].capability.cap_content.category.category_content),
                        unsigned int, old_content) *
                  store(&(target->cnode.slots[class].capability.cap_content.category.category_right),
                        unsigned int, old_right)))) ||
               (class > CAP_CHANNEL_CLASS && emp))))) ||
           ((running != CFalse &&
             ((grant_right & CNODE_GRANT_CAP) == 0 ||
              parent != current_prio) &&
             __return == USER_CAPABILITY_NONE) &&
            (((class <= CAP_CHANNEL_CLASS) &&
              store(pointer_offset(&(OSCSpacePrioTbl), dest,
                                   sizeof(struct cspace *), struct cspace *),
                    struct cspace *, target) *
              ((target == 0 && emp) ||
               (target != 0 &&
                store(&(target->cnode.slots[class].capability.cap_type),
                      unsigned int, old_type) *
                store(&(target->cnode.slots[class].capability.cap_content.category.category_content),
                      unsigned int, old_content) *
                store(&(target->cnode.slots[class].capability.cap_content.category.category_right),
                      unsigned int, old_right)))) ||
             (class > CAP_CHANNEL_CLASS && emp))))))))
 */
{
    unsigned char i;
    CSPACE *pCSpace;

    if (destTask_Prio >= OS_LOWEST_PRIO) {
        return (unsigned char)OS_PRIO_INVALID;
    }

    /* ENTER_CRITICAL -- sequential abstraction. */
    OSPrioCur = OSTCBCur->OSTCBPrio;
    pCSpace = OSCSpacePrioTbl[OSPrioCur];
    if (pCSpace == (CSPACE *)0) {
        /* EXIT_CRITICAL -- sequential abstraction. */
        return (unsigned char)CNODE_GRANT_FAILURE;
    }

    if (OSRunning == CFalse ||
        (((pCSpace->cnode.slots[SLOT_CNODE_CAP]
               .capability.cap_content.category.category_right &
           CNODE_GRANT_CAP) != 0U) &&
         CapParent[destTask_Prio] == OSPrioCur)) {
        /*@ Branch name
              callee_invalid: class > CAP_CHANNEL_CLASS;
              callee_null: class <= CAP_CHANNEL_CLASS && target == 0;
              callee_success: class <= CAP_CHANNEL_CLASS && target != 0
         */
        i = ucos_Grant_Cap(destTask_Prio, cap_Class, cap_Right)
            /*@ where (class_invalid)
                       dest = dest, class = class, right = right
                       $ callee_invalid
                 where (null_target)
                       target = target, dest = dest, class = class,
                       right = right
                       $ callee_null
                 where (valid_target)
                       target = target, dest = dest, class = class,
                       right = right, old_type = old_type,
                       old_content = old_content, old_right = old_right
                       $ callee_success */;
        if (i == CNODE_NONE_FAULT) {
            /* EXIT_CRITICAL -- sequential abstraction. */
            return (unsigned char)CSPACE_NONE_FAULT;
        } else {
            /* EXIT_CRITICAL -- sequential abstraction. */
            return (unsigned char)CNODE_GRANT_FAILURE;
        }
    } else {
        /* EXIT_CRITICAL -- sequential abstraction. */
        return (unsigned char)USER_CAPABILITY_NONE;
    }
}

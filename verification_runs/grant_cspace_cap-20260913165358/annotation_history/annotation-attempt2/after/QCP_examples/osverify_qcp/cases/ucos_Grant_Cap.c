/*
 * Faithful C transcription of:
 *   QCP_examples/osverify/certiucos/code/ios_cap.v
 *   Definition ucos_Grant_Cap_impl
 *
 * Keep the constants, checks, nested CSpace layout, and rights update in the
 * same form as the legacy CertiUCOS model.  The dummy union members mirror the
 * layout trick used by ios_cap_defs.v to keep differently typed union storage
 * explicit in the original proof.
 */

#define SLOT_NUM 255U
#define MAX_CHILD_NUM 64U

#define CAP_NULL_CLASS 0U
#define CAP_CHANNEL_CLASS 16U
#define CAP_CATEGORY_TYPE 1U

#define CNODE_NONE_FAULT 0U
#define CNODE_GRANT_FAILURE 11U
#define OS_LOWEST_PRIO 63U
#define OS_PRIO_INVALID 42U
#define CNODE_GRANT_CAP 64U
#define CSPACE_NONE_FAULT 0U
#define USER_CAPABILITY_NONE 252U
#define SLOT_CNODE_CAP 11U
#define CFalse 0U

typedef struct cap_category {
    unsigned int category_content;
    unsigned int category_right;
    void *Dummy_ptr;
} Cap_Category;

typedef struct cap_object {
    unsigned int object_right;
    unsigned int Dummy_int;
    void *object_t;
} Cap_Object;

typedef union content {
    Cap_Category category;
    Cap_Object object;
} Content;

typedef struct cap {
    unsigned int cap_type;
    Content cap_content;
} Cap;

typedef struct slot {
    unsigned int slot_type;
    Cap capability;
} Slot;

typedef struct cte {
    unsigned int guide_num;
    unsigned int slot_num;
    Slot slots[SLOT_NUM];
} Cte;

typedef struct cspace {
    Cte cnode;
    unsigned int child_num;
    struct cspace *cspace_children[MAX_CHILD_NUM];
    struct cspace *OSCSpaceNext;
    unsigned int taskPrio;
} CSPACE;

CSPACE *OSCSpacePrioTbl[64];

typedef struct os_tcb {
    unsigned char OSTCBPrio;
} OS_TCB;

unsigned char OSRunning;
unsigned char OSPrioCur;
unsigned char CapParent[64];
OS_TCB *OSTCBCur;

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

unsigned char ucos_Grant_Cap(unsigned char destTask_Prio,
                             unsigned int cap_Class,
                             unsigned int cap_Right)
/*@ class_invalid */
/*@ prio_invalid */
/*@ null_target */
/*@ valid_target */
{
    if (CAP_NULL_CLASS > cap_Class || cap_Class > CAP_CHANNEL_CLASS) {
        return (unsigned char)CNODE_GRANT_FAILURE;
    }
    if (destTask_Prio >= 64U) {
        return (unsigned char)CNODE_GRANT_FAILURE;
    }
    if (OSCSpacePrioTbl[destTask_Prio] == (CSPACE *)0) {
        return (unsigned char)CNODE_GRANT_FAILURE;
    }
    OSCSpacePrioTbl[destTask_Prio]
        ->cnode.slots[cap_Class].capability.cap_type = CAP_CATEGORY_TYPE;
    OSCSpacePrioTbl[destTask_Prio]
        ->cnode.slots[cap_Class].capability.cap_content.category.category_content =
        cap_Class;
    OSCSpacePrioTbl[destTask_Prio]
        ->cnode.slots[cap_Class].capability.cap_content.category.category_right &=
        4095U;
    OSCSpacePrioTbl[destTask_Prio]
        ->cnode.slots[cap_Class].capability.cap_content.category.category_right |=
        cap_Right;
    return (unsigned char)CNODE_NONE_FAULT;
}

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

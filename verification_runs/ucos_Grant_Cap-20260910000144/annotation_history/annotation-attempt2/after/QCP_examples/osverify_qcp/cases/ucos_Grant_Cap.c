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

unsigned char ucos_Grant_Cap(unsigned char destTask_Prio,
                             unsigned int cap_Class,
                             unsigned int cap_Right)
/*@ With (target right : Z) (old_type old_content old_right : Z)
    Require
      0 <= destTask_Prio && destTask_Prio <= 255 &&
      unsigned_last_nbits(destTask_Prio, 32) == destTask_Prio &&
      0 <= cap_Class && cap_Class <= UINT_MAX &&
      0 <= cap_Right && cap_Right <= UINT_MAX &&
      cap_Right == right &&
      (((cap_Class <= CAP_CHANNEL_CLASS &&
         unsigned_last_nbits(destTask_Prio, 32) < 64) &&
        store(pointer_offset(&(OSCSpacePrioTbl), destTask_Prio,
                             sizeof(struct cspace *), struct cspace *),
              struct cspace *, target) *
        ((target == 0 && emp) ||
         (target != 0 &&
          store(&(target->cnode.slots[cap_Class].capability.cap_type),
                unsigned int, old_type) *
          store(&(target->cnode.slots[cap_Class].capability.cap_content.category.category_content),
                unsigned int, old_content) *
          store(&(target->cnode.slots[cap_Class].capability.cap_content.category.category_right),
                unsigned int, old_right)))) ||
       ((cap_Class > CAP_CHANNEL_CLASS ||
         unsigned_last_nbits(destTask_Prio, 32) >= 64) && emp))
    Ensure
      (((__return == CNODE_NONE_FAULT &&
         cap_Class <= CAP_CHANNEL_CLASS &&
         unsigned_last_nbits(destTask_Prio, 32) < 64 && target != 0) &&
        store(pointer_offset(&(OSCSpacePrioTbl), destTask_Prio,
                             sizeof(struct cspace *), struct cspace *),
              struct cspace *, target) *
        store(&(target->cnode.slots[cap_Class].capability.cap_type),
              unsigned int, CAP_CATEGORY_TYPE) *
        store(&(target->cnode.slots[cap_Class].capability.cap_content.category.category_content),
              unsigned int, cap_Class) *
        store(&(target->cnode.slots[cap_Class].capability.cap_content.category.category_right),
              unsigned int, (old_right & 4095) | right)) ||
       ((__return == CNODE_GRANT_FAILURE &&
         cap_Class <= CAP_CHANNEL_CLASS &&
         unsigned_last_nbits(destTask_Prio, 32) < 64 && target == 0) &&
        store(pointer_offset(&(OSCSpacePrioTbl), destTask_Prio,
                             sizeof(struct cspace *), struct cspace *),
              struct cspace *, 0)) ||
       ((__return == CNODE_GRANT_FAILURE &&
         (cap_Class > CAP_CHANNEL_CLASS ||
          unsigned_last_nbits(destTask_Prio, 32) >= 64)) && emp))
 */
{
    if (CAP_NULL_CLASS > cap_Class || cap_Class > CAP_CHANNEL_CLASS) {
        return (unsigned char)CNODE_GRANT_FAILURE;
    }
    if (destTask_Prio >= 64U) {
        return (unsigned char)CNODE_GRANT_FAILURE;
    }
    /*@ Assert
      cap_Class <= CAP_CHANNEL_CLASS &&
      unsigned_last_nbits(destTask_Prio, 32) < 64 &&
      cap_Right == right &&
      store(pointer_offset(&(OSCSpacePrioTbl), destTask_Prio,
                           sizeof(struct cspace *), struct cspace *),
            struct cspace *, target) *
      ((target == 0 && emp) ||
       (target != 0 &&
        store(&(target->cnode.slots[cap_Class].capability.cap_type),
              unsigned int, old_type) *
        store(&(target->cnode.slots[cap_Class].capability.cap_content.category.category_content),
              unsigned int, old_content) *
        store(&(target->cnode.slots[cap_Class].capability.cap_content.category.category_right),
              unsigned int, old_right)))
     */
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

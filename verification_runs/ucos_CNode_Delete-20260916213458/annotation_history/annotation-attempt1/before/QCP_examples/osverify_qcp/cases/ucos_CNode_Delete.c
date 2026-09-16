/* Sequential transcription of certiucos/code/ios_cap.v:
 * ucos_CNode_Delete_impl. Layout matches the existing ucos_Grant_Cap case.
 * Authoritative legacy contract: proofs/capability/lib/CapSpec.v,
 * ucos_CNode_DeletePre'/Post'. No executable critical-section primitive
 * occurs in this leaf function.
 */
#define SLOT_NUM 255U
#define MAX_CHILD_NUM 64U
#define CAP_CATEGORY_TYPE 1U
#define CAP_OBJECT_TYPE 2U
#define SLOT_NULL_CAP 0U
#define CNODE_DELETE_FAILURE 9U
#define CNODE_NONE_FAULT 0U

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

unsigned char ucos_CNode_Delete(unsigned char destTask_Prio,
                                unsigned int func_capability)
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

#ifndef OSVERIFY_QCP_IOS_CAP_TYPES_H
#define OSVERIFY_QCP_IOS_CAP_TYPES_H

/* Shared sequential layout transcribed from certiucos/code/ios_cap_defs.v.
 * Do not own both views of the union at once in separation assertions. */
#define SLOT_NUM 255U
#define MAX_CHILD_NUM 64U
#define CAP_NULL_CLASS 0U
#define CAP_CHANNEL_CLASS 16U
#define CAP_CATEGORY_TYPE 1U
#define CAP_OBJECT_TYPE 2U
#define SLOT_NULL_CAP 0U
#define CNODE_NONE_FAULT 0U
#define CNODE_DELETE_FAILURE 9U
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
typedef struct os_tcb {
    unsigned char OSTCBPrio;
} OS_TCB;

/* One definition lives in ios_cap_globals.c; each case sees the same symbols. */
extern CSPACE *OSCSpacePrioTbl[64];
extern unsigned char OSRunning;
extern unsigned char OSPrioCur;
extern unsigned char CapParent[64];
extern OS_TCB *OSTCBCur;

#endif

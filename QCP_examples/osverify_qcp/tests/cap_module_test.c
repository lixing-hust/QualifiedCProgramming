#include <assert.h>
#include <string.h>
#include "include/ucos_Grant_Cap_spec.h"

/* Native smoke test only; controller/Coq evidence remains authoritative. */
unsigned char ucos_CNode_Delete(unsigned char dest, unsigned int slot);
unsigned char grant_cspace_cap(unsigned char dest, unsigned int cls,
                              unsigned int rights);

int main(void)
{
    static CSPACE target;
    static CSPACE current;
    static OS_TCB tcb;
    int sentinel;
    Slot *slot = &target.cnode.slots[3];
    OSCSpacePrioTbl[2] = &target;
    slot->slot_type = 7;
    slot->capability.cap_type = CAP_CATEGORY_TYPE;
    slot->capability.cap_content.category.category_content = 8;
    slot->capability.cap_content.category.category_right = 0x12345;
    slot->capability.cap_content.category.Dummy_ptr = &sentinel;
    assert(ucos_Grant_Cap(2, 3, 0x8000) == CNODE_NONE_FAULT);
    assert(slot->slot_type == 7);
    assert(slot->capability.cap_type == CAP_CATEGORY_TYPE);
    assert(slot->capability.cap_content.category.category_content == 3);
    assert(slot->capability.cap_content.category.category_right == 0x8345);
    assert(slot->capability.cap_content.category.Dummy_ptr == &sentinel);
    assert(ucos_CNode_Delete(2, 3) == CNODE_NONE_FAULT);
    assert(slot->slot_type == SLOT_NULL_CAP && slot->capability.cap_type == 0);
    assert(slot->capability.cap_content.category.category_content == 0);
    assert(slot->capability.cap_content.category.category_right == 0);
    assert(slot->capability.cap_content.category.Dummy_ptr == &sentinel);

    slot->slot_type = 7;
    slot->capability.cap_type = CAP_OBJECT_TYPE;
    slot->capability.cap_content.object.object_right = 99;
    slot->capability.cap_content.object.Dummy_int = 123;
    slot->capability.cap_content.object.object_t = &sentinel;
    assert(ucos_CNode_Delete(2, 3) == CNODE_NONE_FAULT);
    assert(slot->slot_type == 0 && slot->capability.cap_type == 0);
    assert(slot->capability.cap_content.object.object_right == 0);
    assert(slot->capability.cap_content.object.Dummy_int == 123);
    assert(slot->capability.cap_content.object.object_t == 0);

    Slot snapshot;
    memcpy(&snapshot, slot, sizeof snapshot);
    assert(ucos_CNode_Delete(2, 3) == CNODE_DELETE_FAILURE);
    assert(memcmp(&snapshot, slot, sizeof snapshot) == 0);
    assert(ucos_CNode_Delete(2, SLOT_NUM) == CNODE_DELETE_FAILURE);
    assert(ucos_CNode_Delete(64, 0) == CNODE_DELETE_FAILURE);
    assert(ucos_CNode_Delete(5, 0) == CNODE_DELETE_FAILURE);
    assert(ucos_Grant_Cap(2, 17, 0) == CNODE_GRANT_FAILURE);
    assert(ucos_Grant_Cap(64, 0, 0) == CNODE_GRANT_FAILURE);
    assert(ucos_Grant_Cap(5, 0, 0) == CNODE_GRANT_FAILURE);

    tcb.OSTCBPrio = 1;
    OSTCBCur = &tcb;
    OSCSpacePrioTbl[1] = &current;
    OSRunning = 1;
    CapParent[2] = 1;
    current.cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right = CNODE_GRANT_CAP;
    assert(grant_cspace_cap(2, 3, 16) == CSPACE_NONE_FAULT);
    assert(OSPrioCur == 1);
    assert(slot->capability.cap_type == CAP_CATEGORY_TYPE);
    current.cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right = 0;
    assert(grant_cspace_cap(2, 3, 16) == USER_CAPABILITY_NONE);
    assert(grant_cspace_cap(63, 3, 16) == OS_PRIO_INVALID);
    return 0;
}

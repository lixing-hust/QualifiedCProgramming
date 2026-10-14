#include <assert.h>
#include <stdint.h>
#include <string.h>
#include "include/ios_cap_types.h"

/* Supplementary native regression test, not a replacement for QCP proofs. */
unsigned char ucos_CNode_Mint(unsigned char dest, unsigned char src,
                             unsigned int cls, unsigned int rights);

static CSPACE source_space;
static CSPACE dest_space;
static int marker;

static void setup(unsigned int source_rights)
{
    memset(OSCSpacePrioTbl, 0, sizeof OSCSpacePrioTbl);
    memset(&source_space, 0, sizeof source_space);
    memset(&dest_space, 0, sizeof dest_space);
    OSCSpacePrioTbl[1] = &source_space;
    OSCSpacePrioTbl[2] = &dest_space;
    Slot *src = &source_space.cnode.slots[3];
    Slot *dst = &dest_space.cnode.slots[3];
    src->slot_type = 19;
    src->capability.cap_type = CAP_CATEGORY_TYPE;
    src->capability.cap_content.category.category_content = 77;
    src->capability.cap_content.category.category_right = source_rights;
    src->capability.cap_content.category.Dummy_ptr = &marker;
    dst->slot_type = 23;
    dst->capability.cap_type = 0;
    dst->capability.cap_content.category.category_content = 8;
    dst->capability.cap_content.category.category_right = 0x80000000U;
    dst->capability.cap_content.category.Dummy_ptr = &dest_space;
}

static void failure(unsigned char dest, unsigned char src,
                    unsigned int cls, unsigned int rights)
{
    CSPACE source_before, dest_before;
    CSPACE *table_before[64];
    memcpy(&source_before, &source_space, sizeof source_before);
    memcpy(&dest_before, &dest_space, sizeof dest_before);
    memcpy(table_before, OSCSpacePrioTbl, sizeof table_before);
    assert(ucos_CNode_Mint(dest, src, cls, rights) == 5U);
    assert(memcmp(&source_before, &source_space, sizeof source_before) == 0);
    assert(memcmp(&dest_before, &dest_space, sizeof dest_before) == 0);
    assert(memcmp(table_before, OSCSpacePrioTbl, sizeof table_before) == 0);
}

int main(void)
{
    CSPACE source_before;
    setup(15);
    memcpy(&source_before, &source_space, sizeof source_before);
    assert(ucos_CNode_Mint(2, 1, 3, 5) == CNODE_NONE_FAULT);
    Slot *dst = &dest_space.cnode.slots[3];
    assert(dst->slot_type == 23 && dst->capability.cap_type == CAP_CATEGORY_TYPE);
    assert(dst->capability.cap_content.category.category_content == 77);
    assert(dst->capability.cap_content.category.category_right == 5);
    assert(dst->capability.cap_content.category.Dummy_ptr == &dest_space);
    assert(memcmp(&source_before, &source_space, sizeof source_before) == 0);

    setup(15);
    failure(2, 1, 17, 5);
    failure(64, 1, 3, 5);
    failure(2, 255, 3, 5);
    failure(5, 1, 3, 5);
    failure(2, 5, 3, 5);
    failure(5, 5, 3, 5);
    failure(2, 1, 3, 16); /* requests a bit absent from the source */
    failure(2, 1, 3, 15); /* equality is rejected, even though it is a subset */
    source_space.cnode.slots[3].capability.cap_type = CAP_OBJECT_TYPE;
    failure(2, 1, 3, 5);

    setup(15);
    assert(ucos_CNode_Mint(1, 1, 3, 5) == CNODE_NONE_FAULT);
    Slot *src = &source_space.cnode.slots[3];
    assert(src->slot_type == 19 && src->capability.cap_type == CAP_CATEGORY_TYPE);
    assert(src->capability.cap_content.category.category_content == 77);
    assert(src->capability.cap_content.category.category_right == 5);
    assert(src->capability.cap_content.category.Dummy_ptr == &marker);
    failure(1, 1, 3, 5);

    setup(15);
    OSCSpacePrioTbl[2] = &source_space;
    assert(ucos_CNode_Mint(2, 1, 3, 5) == CNODE_NONE_FAULT);
    assert(source_space.cnode.slots[3].capability.cap_content.category.category_right == 5);
    assert(source_space.cnode.slots[3].slot_type == 19);
    failure(2, 1, 3, 5);

    setup(UINT32_MAX);
    assert(ucos_CNode_Mint(2, 1, 3, 0x80000000U) == CNODE_NONE_FAULT);
    assert(dest_space.cnode.slots[3].capability.cap_content.category.category_right == 0x80000000U);
    setup(1);
    assert(ucos_CNode_Mint(2, 1, 3, 0) == CNODE_NONE_FAULT);
    setup(0);
    failure(2, 1, 3, 0);
    return 0;
}

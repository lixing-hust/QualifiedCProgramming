#include <assert.h>
#include <limits.h>
#include <stdint.h>
#include <string.h>
#include "include/ios_cap_types.h"

/* Supplementary native tests; the QCP proof remains a separate deliverable. */
unsigned char ucos_CNode_Mutate(unsigned char dest, unsigned char src,
                               unsigned int cls, unsigned int rights);
_Static_assert(UINT_MAX == UINT32_MAX, "QCP example uses 32-bit unsigned int");

static CSPACE source_space;
static CSPACE dest_space;
static int marker;

static void setup(unsigned int old_rights, unsigned int cls, int layout)
{
    memset(OSCSpacePrioTbl, 0, sizeof OSCSpacePrioTbl);
    memset(&source_space, 0, sizeof source_space);
    memset(&dest_space, 0, sizeof dest_space);
    OSCSpacePrioTbl[1] = &source_space;
    OSCSpacePrioTbl[2] = layout == 2 ? &source_space : &dest_space;
    Slot *src = &source_space.cnode.slots[cls];
    Slot *dst = &dest_space.cnode.slots[cls];
    src->slot_type = 19;
    src->capability.cap_type = CAP_CATEGORY_TYPE;
    src->capability.cap_content.category.category_content = 77;
    src->capability.cap_content.category.category_right = old_rights;
    src->capability.cap_content.category.Dummy_ptr = &marker;
    dst->slot_type = 23;
    dst->capability.cap_type = CAP_OBJECT_TYPE;
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
    assert(ucos_CNode_Mutate(dest, src, cls, rights) == 8U);
    assert(memcmp(&source_before, &source_space, sizeof source_before) == 0);
    assert(memcmp(&dest_before, &dest_space, sizeof dest_before) == 0);
    assert(memcmp(table_before, OSCSpacePrioTbl, sizeof table_before) == 0);
}

static void check_rights(unsigned int old_rights, unsigned int rights,
                         unsigned int cls, int layout)
{
    setup(old_rights, cls, layout);
    unsigned char dest = layout == 1 ? 1 : 2;
    /* Equivalent subset oracle expressed differently from the implementation. */
    if ((rights & old_rights) != rights || rights == old_rights) {
        failure(dest, 1, cls, rights);
        return;
    }
    CSPACE source_expected, dest_expected;
    CSPACE *table_before[64];
    memcpy(&source_expected, &source_space, sizeof source_expected);
    memcpy(&dest_expected, &dest_space, sizeof dest_expected);
    memcpy(table_before, OSCSpacePrioTbl, sizeof table_before);
    Slot *src = &source_expected.cnode.slots[cls];
    src->slot_type = SLOT_NULL_CAP;
    src->capability.cap_content.category.category_right =
        layout == 0 ? old_rights & ~rights : 0;
    if (layout == 0) {
        Slot *dst = &dest_expected.cnode.slots[cls];
        dst->capability.cap_type = CAP_CATEGORY_TYPE;
        dst->capability.cap_content.category.category_content = 77;
        dst->capability.cap_content.category.category_right = rights;
    }
    assert(ucos_CNode_Mutate(dest, 1, cls, rights) == CNODE_NONE_FAULT);
    assert(memcmp(&source_expected, &source_space, sizeof source_expected) == 0);
    assert(memcmp(&dest_expected, &dest_space, sizeof dest_expected) == 0);
    assert(memcmp(table_before, OSCSpacePrioTbl, sizeof table_before) == 0);
}

int main(void)
{
    /* All 5-bit masks, for distinct spaces and both forms of aliasing. */
    for (int layout = 0; layout < 3; ++layout) {
        for (unsigned int old = 0; old < 32; ++old) {
            for (unsigned int rights = 0; rights < 32; ++rights) {
                check_rights(old, rights, 3, layout);
            }
        }
        check_rights(UINT32_MAX, 0x80000000U, 16, layout);
        check_rights(UINT32_MAX, 0x7fffffffU, 0, layout);
        check_rights(1, 0, 3, layout);
        check_rights(0x80000000U, 0, 3, layout);
        check_rights(0x80000000U, UINT32_MAX, 3, layout);
        check_rights(UINT32_MAX, UINT32_MAX, 3, layout);
    }

    setup(15, 3, 0);
    failure(2, 1, 17, 5);
    failure(2, 1, UINT32_MAX, 5);
    failure(64, 1, 3, 5);
    failure(2, 255, 3, 5);
    failure(5, 1, 3, 5);
    failure(2, 5, 3, 5);
    failure(5, 5, 3, 5);
    failure(5, 6, 3, 5);
    source_space.cnode.slots[3].capability.cap_type = CAP_OBJECT_TYPE;
    failure(2, 1, 3, 5);
    source_space.cnode.slots[3].capability.cap_type = 0;
    failure(2, 1, 3, 5);
    return 0;
}

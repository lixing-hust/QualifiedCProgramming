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

#include "../include/ucos_Grant_Cap_spec.h"

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

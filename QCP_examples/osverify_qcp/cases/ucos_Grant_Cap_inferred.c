/* Independent implementation-derived experiment.
 * Mandatory information boundary and provenance requirements for ALL agents:
 * experiments/ucos_Grant_Cap_inferred_20260918/task.md
 * Do not read pre-existing osverify specifications, models, proofs or runs.
 * Body transcribed only from Definition ucos_Grant_Cap_impl in ios_cap.v.
 */
#include "osverify_qcp/include/ios_cap_types.h"

/*@ Import Coq Require Import SimpleC.EE.osverify_qcp.cases.ucos_Grant_Cap_inferred_lib */
/*@ Extern Coq
      (grant_rights : Z -> Z -> Z)
      (grant_success_fields : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 */

unsigned char ucos_Grant_Cap(unsigned char destTask_Prio,
                             unsigned int cap_Class,
                             unsigned int cap_Right)
/*@ With (p : Z) (old_right : Z)
    Require
      0 <= destTask_Prio && destTask_Prio <= 255 &&
      0 <= cap_Class && cap_Class <= 4294967295 &&
      0 <= cap_Right && cap_Right <= 4294967295 &&
      (((cap_Class > 16 || destTask_Prio >= 64) && emp) ||
       (cap_Class <= 16 && destTask_Prio < 64 &&
        data_at(((struct cspace **)&OSCSpacePrioTbl + destTask_Prio), struct cspace *, p) *
        ((p == 0 && emp) ||
         (p != 0 && 0 <= old_right && old_right <= 4294967295 &&
          undef_data_at(&(((struct slot *)&(((struct cspace *)p)->cnode.slots) + cap_Class)->capability.cap_type), unsigned int) *
          undef_data_at(&(((struct slot *)&(((struct cspace *)p)->cnode.slots) + cap_Class)->capability.cap_content.category.category_content), unsigned int) *
          data_at(&(((struct slot *)&(((struct cspace *)p)->cnode.slots) + cap_Class)->capability.cap_content.category.category_right), unsigned int, old_right)))))
    Ensure
      (((cap_Class > 16 || destTask_Prio >= 64) && __return == 11 && emp) ||
       (cap_Class <= 16 && destTask_Prio < 64 &&
        data_at(((struct cspace **)&OSCSpacePrioTbl + destTask_Prio), struct cspace *, p) *
        ((p == 0 && __return == 11 && emp) ||
         (p != 0 && exists new_type new_content new_right,
          grant_success_fields(cap_Class, old_right, cap_Right, __return,
                               new_type, new_content, new_right) &&
          data_at(&(((struct slot *)&(((struct cspace *)p)->cnode.slots) + cap_Class)->capability.cap_type), unsigned int, new_type) *
          data_at(&(((struct slot *)&(((struct cspace *)p)->cnode.slots) + cap_Class)->capability.cap_content.category.category_content), unsigned int, new_content) *
          data_at(&(((struct slot *)&(((struct cspace *)p)->cnode.slots) + cap_Class)->capability.cap_content.category.category_right), unsigned int, new_right)))))
 */
{
    if (CAP_NULL_CLASS > cap_Class || cap_Class > CAP_CHANNEL_CLASS) {
        return CNODE_GRANT_FAILURE;
    }
    if (destTask_Prio >= 64) {
        return CNODE_GRANT_FAILURE;
    }
    if (OSCSpacePrioTbl[destTask_Prio] == (CSPACE *)0) {
        return CNODE_GRANT_FAILURE;
    }
    OSCSpacePrioTbl[destTask_Prio]->cnode.slots[cap_Class].capability.cap_type = CAP_CATEGORY_TYPE;
    OSCSpacePrioTbl[destTask_Prio]->cnode.slots[cap_Class].capability.cap_content.category.category_content = cap_Class;
    OSCSpacePrioTbl[destTask_Prio]->cnode.slots[cap_Class].capability.cap_content.category.category_right &= 4095;
    OSCSpacePrioTbl[destTask_Prio]->cnode.slots[cap_Class].capability.cap_content.category.category_right |= cap_Right;
    return (unsigned char)0;
}

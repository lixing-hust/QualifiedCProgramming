#include "osverify_qcp/include/ios_cap_types.h"

/* Core-only sequential ordinary-memory verification.
   Source: this experiment's exact ucos_CNode_Delete_impl extraction.
   The global table and CSPACE are valid separate declared objects;
   only accessed fields are owned. No configuration, helper call, or
   independent duplicate union view is introduced. */
/*@ Import Coq Require Import SimpleC.EE.osverify_qcp.cases.ucos_cnode_delete_inferred_20261011_lib */
/*@ Extern Coq
    (cd_input_domain : Z -> Z -> Prop)
    (cd_result : Z -> Z -> Z -> Z -> Z -> Prop)
    (cd_cap_type_after : Z -> Z)
*/

unsigned char ucos_CNode_Delete(unsigned char destTask_Prio, unsigned int func_capability)
/*@ With (space : Z) (old_type : Z)
    Require cd_input_domain(destTask_Prio, func_capability) &&
    0 <= destTask_Prio && destTask_Prio <= 255 &&
    (((func_capability >= 255 || destTask_Prio >= 64) && emp) ||
     (func_capability < 255 && destTask_Prio < 64 &&
      data_at(((struct cspace **)&(OSCSpacePrioTbl) + destTask_Prio), struct cspace *, space) *
      ((space == 0 && emp) ||
       (space != 0 &&
        data_at(&((((struct slot *)&(((struct cspace *)space)->cnode.slots)) + func_capability)->capability.cap_type), unsigned int, old_type) *
        ((old_type == 1 &&
          undef_data_at(&((((struct slot *)&(((struct cspace *)space)->cnode.slots)) + func_capability)->slot_type), unsigned int) *
          undef_data_at(&((((struct slot *)&(((struct cspace *)space)->cnode.slots)) + func_capability)->capability.cap_content.category.category_content), unsigned int) *
          undef_data_at(&((((struct slot *)&(((struct cspace *)space)->cnode.slots)) + func_capability)->capability.cap_content.category.category_right), unsigned int)) ||
         (old_type == 2 &&
          undef_data_at(&((((struct slot *)&(((struct cspace *)space)->cnode.slots)) + func_capability)->slot_type), unsigned int) *
          undef_data_at(&((((struct slot *)&(((struct cspace *)space)->cnode.slots)) + func_capability)->capability.cap_content.object.object_right), unsigned int) *
          undef_data_at(&((((struct slot *)&(((struct cspace *)space)->cnode.slots)) + func_capability)->capability.cap_content.object.object_t), void *)) ||
         (old_type != 1 && old_type != 2 && emp))))))
    Ensure cd_result(destTask_Prio, func_capability, space, old_type, __return) &&
    (((func_capability >= 255 || destTask_Prio >= 64) && emp) ||
     (func_capability < 255 && destTask_Prio < 64 &&
      data_at(((struct cspace **)&(OSCSpacePrioTbl) + destTask_Prio), struct cspace *, space) *
      ((space == 0 && emp) ||
       (space != 0 &&
        data_at(&((((struct slot *)&(((struct cspace *)space)->cnode.slots)) + func_capability)->capability.cap_type), unsigned int, cd_cap_type_after(old_type)) *
        ((old_type == 1 &&
          data_at(&((((struct slot *)&(((struct cspace *)space)->cnode.slots)) + func_capability)->slot_type), unsigned int, 0) *
          data_at(&((((struct slot *)&(((struct cspace *)space)->cnode.slots)) + func_capability)->capability.cap_content.category.category_content), unsigned int, 0) *
          data_at(&((((struct slot *)&(((struct cspace *)space)->cnode.slots)) + func_capability)->capability.cap_content.category.category_right), unsigned int, 0)) ||
         (old_type == 2 &&
          data_at(&((((struct slot *)&(((struct cspace *)space)->cnode.slots)) + func_capability)->slot_type), unsigned int, 0) *
          data_at(&((((struct slot *)&(((struct cspace *)space)->cnode.slots)) + func_capability)->capability.cap_content.object.object_right), unsigned int, 0) *
          data_at(&((((struct slot *)&(((struct cspace *)space)->cnode.slots)) + func_capability)->capability.cap_content.object.object_t), void *, 0)) ||
         (old_type != 1 && old_type != 2 && emp))))))
*/
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
  cap1 = &(pCSpace1->cnode.slots[func_capability].capability);
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

#include "osverify_qcp/include/ios_cap_types.h"
#include "QCP_demos_LLM/verification_stdlib.h"
#include "QCP_demos_LLM/verification_list.h"

#define NULL 0
#define CNODE_MINT_CAP 1U
#define CNODE_MINT_SUCCESS 0U
#define CNODE_MINT_FAILURE 5U
/* Explicit sequential ordinary-memory projection only. These preserve source
 * marker sites as empty statements; they say nothing about interrupt masking,
 * scheduling, atomicity or the correctness of the original marker primitives. */

/*@ Extern Coq (MintCell :: *) (MintLayout :: *) */
/*@ Extern Coq
  (mint_heap : list MintCell -> Assertion)
  (mint_eligible : list MintCell -> MintLayout -> Z -> Z -> Z -> Z -> Prop)
  (mint_core_pre : list MintCell -> MintLayout -> Z -> Z -> Z -> Z -> Prop)
  (mint_core_result : list MintCell -> MintLayout -> Z -> Z -> Z -> Z -> Z -> list MintCell -> Prop)
  (mint_user_pre : list MintCell -> MintLayout -> Z -> Z -> Z -> Z -> Prop)
  (mint_user_result : list MintCell -> MintLayout -> Z -> Z -> Z -> Z -> Z -> list MintCell -> Prop)
*/
/*@ Extern Coq
 (mint_core_layout : MintLayout -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (mint_user_layout : MintLayout -> Z -> Z -> Z -> Z -> Z -> Prop)
 (mint_dst : list MintCell -> MintLayout -> Z)
 (mint_src : list MintCell -> MintLayout -> Z)
 (mint_cur : list MintCell -> MintLayout -> Z)
 (mint_value : list MintCell -> Z -> Z)
 (mint_remove : list MintCell -> Z -> list MintCell)
 (mint_set : list MintCell -> Z -> Z -> list MintCell)
 (mint_dt : MintLayout -> Z)
 (mint_st : MintLayout -> Z)
 (mint_dty : MintLayout -> Z)
 (mint_dco : MintLayout -> Z)
 (mint_dri : MintLayout -> Z)
 (mint_sty : MintLayout -> Z)
 (mint_sco : MintLayout -> Z)
 (mint_sri : MintLayout -> Z)
 (mint_cp : MintLayout -> Z)
 (mint_pr : MintLayout -> Z)
 (mint_ct : MintLayout -> Z)
 (mint_ar : MintLayout -> Z)
 (mint_pa : MintLayout -> Z)
*/
/*@ Extern Coq
 (mint_wellformed : list MintCell -> Prop)
 (mint_readable : list MintCell -> Z -> Z -> Prop)
 (mint_writable : list MintCell -> Z -> Z -> Prop)
 (mint_source_reads : list MintCell -> Z -> Z -> Prop)
 (mint_auth_reads : list MintCell -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.osverify_qcp.cases.user_cnode_mint_inferred_20260923_lib */

unsigned char ucos_CNode_Mint(unsigned char destTask_Prio,
                            unsigned char srcTask_Prio,
                            unsigned int func_capability,
                            unsigned int rights)
/*@ With (h : list MintCell) (L : MintLayout)
    Require mint_core_layout(L, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio), ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio),
      &((((struct slot *)&(((struct cspace *)mint_dst(h, L))->cnode.slots)) + func_capability)->capability.cap_type),
      &((((struct slot *)&(((struct cspace *)mint_dst(h, L))->cnode.slots)) + func_capability)->capability.cap_content.category.category_content),
      &((((struct slot *)&(((struct cspace *)mint_dst(h, L))->cnode.slots)) + func_capability)->capability.cap_content.category.category_right),
      &((((struct slot *)&(((struct cspace *)mint_src(h, L))->cnode.slots)) + func_capability)->capability.cap_type),
      &((((struct slot *)&(((struct cspace *)mint_src(h, L))->cnode.slots)) + func_capability)->capability.cap_content.category.category_content),
      &((((struct slot *)&(((struct cspace *)mint_src(h, L))->cnode.slots)) + func_capability)->capability.cap_content.category.category_right)) &&
      mint_core_pre(h, L, destTask_Prio, srcTask_Prio, func_capability, rights) &&
            mint_heap(h)
    Ensure exists (h1 : list MintCell),
      mint_core_result(h, L, destTask_Prio@pre, srcTask_Prio@pre,
                       func_capability@pre, rights@pre, __return, h1) &&
      mint_heap(h1)
*/
{
    CSPACE *pCSpace1;
    CSPACE *pCSpace2;
    Cap *cap1;
    Cap *cap2;
    if (CAP_NULL_CLASS > func_capability || func_capability > CAP_CHANNEL_CLASS) {
        return CNODE_MINT_FAILURE;
    }
    if (destTask_Prio >= 64U || srcTask_Prio >= 64U) {
        return CNODE_MINT_FAILURE;
    }
    /*@ mint_wellformed(h) && mint_readable(h, 2, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)) && mint_heap(h)
          which implies data_at(((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre), struct cspace *, mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre))) * mint_heap(mint_remove(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre))) */
    pCSpace1 = OSCSpacePrioTbl[destTask_Prio];
    /*@ mint_wellformed(h) && mint_readable(h, 2, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)) && data_at(((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre), struct cspace *, mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre))) * mint_heap(mint_remove(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))
          which implies mint_heap(h) */
    
    /*@ mint_wellformed(h) && mint_readable(h, 2, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)) && mint_heap(h)
          which implies data_at(((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre), struct cspace *, mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre))) * mint_heap(mint_remove(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre))) */
    pCSpace2 = OSCSpacePrioTbl[srcTask_Prio];
    /*@ mint_wellformed(h) && mint_readable(h, 2, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)) && data_at(((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre), struct cspace *, mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre))) * mint_heap(mint_remove(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))
          which implies mint_heap(h) */
    if (pCSpace1 == NULL || pCSpace2 == NULL) {
        return CNODE_MINT_FAILURE;
    }
    cap1 = &(pCSpace1->cnode.slots[func_capability].capability);
    cap2 = &(pCSpace2->cnode.slots[func_capability].capability);
    /*@ mint_wellformed(h) && mint_source_reads(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_right)) && mint_heap(h)
          which implies (mint_value(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type)) != 1 && data_at(&((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), unsigned int, mint_value(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type))) * mint_heap(mint_remove(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type)))) ||
      (mint_value(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type)) == 1 && &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type) == &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_right) && data_at(&((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), unsigned int, mint_value(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type))) * mint_heap(mint_remove(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type)))) ||
      (mint_value(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type)) == 1 && &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type) != &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_right) && data_at(&((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), unsigned int, mint_value(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type))) * data_at(&((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_right), unsigned int, mint_value(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_right))) * mint_heap(mint_remove(mint_remove(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type)), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_right)))) */
    if (cap2->cap_type == CAP_CATEGORY_TYPE &&
        ((~cap2->cap_content.category.category_right) & rights) == 0U &&
        cap2->cap_content.category.category_right != rights) {
        
        /*@ Assert  mint_core_layout(L, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre), ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre),
      &((((struct slot *)&(((struct cspace *)mint_dst(h, L))->cnode.slots)) + func_capability@pre)->capability.cap_type),
      &((((struct slot *)&(((struct cspace *)mint_dst(h, L))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content),
      &((((struct slot *)&(((struct cspace *)mint_dst(h, L))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_right),
      &((((struct slot *)&(((struct cspace *)mint_src(h, L))->cnode.slots)) + func_capability@pre)->capability.cap_type),
      &((((struct slot *)&(((struct cspace *)mint_src(h, L))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content),
      &((((struct slot *)&(((struct cspace *)mint_src(h, L))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_right)) &&
      mint_core_pre(h, L, destTask_Prio@pre, srcTask_Prio@pre, func_capability@pre, rights@pre) &&
      mint_eligible(h, L, destTask_Prio@pre, srcTask_Prio@pre, func_capability@pre, rights@pre) &&
      mint_heap(h) * data_at(&destTask_Prio, unsigned char, destTask_Prio@pre) *
      data_at(&srcTask_Prio, unsigned char, srcTask_Prio@pre) *
      data_at(&func_capability, unsigned int, func_capability@pre) *
      data_at(&rights, unsigned int, rights@pre) *
      data_at(&pCSpace1, struct cspace *, mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre))) *
      data_at(&pCSpace2, struct cspace *, mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre))) *
      data_at(&cap1, struct cap *, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability)) *
      data_at(&cap2, struct cap *, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability)) */
        /*@ mint_wellformed(h) && mint_writable(h, 0, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type)) && mint_heap(h)
          which implies undef_data_at(&((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), unsigned int) * mint_heap(mint_remove(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type))) */
        cap1->cap_type = CAP_CATEGORY_TYPE;
        /*@ mint_wellformed(h) && mint_writable(h, 0, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type)) && data_at(&((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), unsigned int, 1) * mint_heap(mint_remove(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type)))
          which implies mint_heap(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1)) */
        
        /*@ mint_wellformed(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1)) && mint_readable(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), 0, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content)) && mint_writable(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), 0, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content)) && mint_heap(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1))
          which implies (&((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content) == &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content) && data_at(&((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content), unsigned int, mint_value(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content))) * mint_heap(mint_remove(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content)))) || (&((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content) != &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content) && data_at(&((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content), unsigned int, mint_value(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content))) * undef_data_at(&((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content), unsigned int) * mint_heap(mint_remove(mint_remove(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content)), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content)))) */
        cap1->cap_content.category.category_content =
            cap2->cap_content.category.category_content;
        
        /*@ Assert  mint_core_layout(L, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre), ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre),
      &((((struct slot *)&(((struct cspace *)mint_dst(h, L))->cnode.slots)) + func_capability@pre)->capability.cap_type),
      &((((struct slot *)&(((struct cspace *)mint_dst(h, L))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content),
      &((((struct slot *)&(((struct cspace *)mint_dst(h, L))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_right),
      &((((struct slot *)&(((struct cspace *)mint_src(h, L))->cnode.slots)) + func_capability@pre)->capability.cap_type),
      &((((struct slot *)&(((struct cspace *)mint_src(h, L))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content),
      &((((struct slot *)&(((struct cspace *)mint_src(h, L))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_right)) &&
      mint_core_pre(h, L, destTask_Prio@pre, srcTask_Prio@pre, func_capability@pre, rights@pre) &&
      mint_eligible(h, L, destTask_Prio@pre, srcTask_Prio@pre, func_capability@pre, rights@pre) &&
      mint_heap(mint_set(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content), mint_value(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content)))) * data_at(&destTask_Prio, unsigned char, destTask_Prio@pre) *
      data_at(&srcTask_Prio, unsigned char, srcTask_Prio@pre) *
      data_at(&func_capability, unsigned int, func_capability@pre) *
      data_at(&rights, unsigned int, rights@pre) *
      data_at(&pCSpace1, struct cspace *, mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre))) *
      data_at(&pCSpace2, struct cspace *, mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre))) *
      data_at(&cap1, struct cap *, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability)) *
      data_at(&cap2, struct cap *, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability)) */
        /*@ mint_wellformed(mint_set(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content), mint_value(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content)))) && mint_writable(mint_set(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content), mint_value(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content))), 0, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_right)) && mint_heap(mint_set(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content), mint_value(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content))))
          which implies undef_data_at(&((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_right), unsigned int) * mint_heap(mint_remove(mint_set(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content), mint_value(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content))), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_right))) */
        cap1->cap_content.category.category_right = rights;
        /*@ mint_wellformed(mint_set(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content), mint_value(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content)))) && mint_writable(mint_set(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content), mint_value(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content))), 0, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_right)) && data_at(&((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_right), unsigned int, rights@pre) * mint_heap(mint_remove(mint_set(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content), mint_value(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content))), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_right)))
          which implies mint_heap(mint_set(mint_set(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content), mint_value(mint_set(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_type), 1), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_content))), &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio@pre)))->cnode.slots)) + func_capability@pre)->capability.cap_content.category.category_right), rights@pre)) */
    } else {
        return (unsigned char)CNODE_MINT_FAILURE;
    }
    return (unsigned char)CNODE_NONE_FAULT;
}

unsigned char user_cnode_mint(unsigned char destTask_Prio,
                             unsigned char srcTask_Prio,
                             unsigned int func_capability,
                             unsigned int rights)
/*@ With (h : list MintCell) (L : MintLayout)
    Require mint_core_layout(L, ((struct cspace **)&OSCSpacePrioTbl + destTask_Prio), ((struct cspace **)&OSCSpacePrioTbl + srcTask_Prio),
      &((((struct slot *)&(((struct cspace *)mint_dst(h, L))->cnode.slots)) + func_capability)->capability.cap_type),
      &((((struct slot *)&(((struct cspace *)mint_dst(h, L))->cnode.slots)) + func_capability)->capability.cap_content.category.category_content),
      &((((struct slot *)&(((struct cspace *)mint_dst(h, L))->cnode.slots)) + func_capability)->capability.cap_content.category.category_right),
      &((((struct slot *)&(((struct cspace *)mint_src(h, L))->cnode.slots)) + func_capability)->capability.cap_type),
      &((((struct slot *)&(((struct cspace *)mint_src(h, L))->cnode.slots)) + func_capability)->capability.cap_content.category.category_content),
      &((((struct slot *)&(((struct cspace *)mint_src(h, L))->cnode.slots)) + func_capability)->capability.cap_content.category.category_right)) &&
      mint_user_layout(L, &OSTCBCur,
      &(((struct os_tcb *)mint_value(h, mint_cp(L)))->OSTCBPrio),
      ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, mint_pr(L))),
      &((((struct slot *)&(((struct cspace *)mint_cur(h, L))->cnode.slots)) + SLOT_CNODE_CAP)->capability.cap_content.category.category_right),
      ((unsigned char *)&CapParent + destTask_Prio)) &&
      mint_user_pre(h, L, destTask_Prio, srcTask_Prio, func_capability, rights) &&
            mint_heap(h)
    Ensure exists (h1 : list MintCell),
      mint_user_result(h, L, destTask_Prio@pre, srcTask_Prio@pre,
                       func_capability@pre, rights@pre, __return, h1) &&
      mint_heap(h1)
*/
{
    CSPACE *pCSpace;
    unsigned char i;
    unsigned char y;
    if (srcTask_Prio >= OS_LOWEST_PRIO || destTask_Prio >= OS_LOWEST_PRIO) {
        return (unsigned char)OS_PRIO_INVALID;
    }
    ; /* ENTER_CRITICAL: sequential ordinary-memory identity */
    /*@ mint_wellformed(h) && mint_readable(h, 2, &OSTCBCur) && mint_readable(h, 1, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)) && mint_heap(h)
          which implies data_at(&OSTCBCur, struct os_tcb *, mint_value(h, &OSTCBCur)) * data_at(&(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio), unsigned char, mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio))) * mint_heap(mint_remove(mint_remove(h, &OSTCBCur), &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio))) */
    y = OSTCBCur->OSTCBPrio;
    /*@ mint_wellformed(h) && mint_readable(h, 2, &OSTCBCur) && mint_readable(h, 1, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)) && data_at(&OSTCBCur, struct os_tcb *, mint_value(h, &OSTCBCur)) * data_at(&(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio), unsigned char, mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio))) * mint_heap(mint_remove(mint_remove(h, &OSTCBCur), &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)))
          which implies mint_heap(h) */
    
    /*@ mint_wellformed(h) && mint_readable(h, 2, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)))) && mint_heap(h)
          which implies data_at(((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio))), struct cspace *, mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio))))) * mint_heap(mint_remove(h, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio))))) */
    pCSpace = OSCSpacePrioTbl[y];
    /*@ mint_wellformed(h) && mint_readable(h, 2, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)))) && data_at(((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio))), struct cspace *, mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio))))) * mint_heap(mint_remove(h, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)))))
          which implies mint_heap(h) */
    if (pCSpace == NULL) {
        ; /* EXIT_CRITICAL: sequential ordinary-memory identity */
        return (unsigned char)CNODE_MINT_FAILURE;
    }
    /*@ mint_wellformed(h) && mint_auth_reads(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)))))->cnode.slots)) + SLOT_CNODE_CAP)->capability.cap_content.category.category_right), ((unsigned char *)&CapParent + destTask_Prio@pre)) && mint_heap(h)
          which implies ((mint_value(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)))))->cnode.slots)) + SLOT_CNODE_CAP)->capability.cap_content.category.category_right)) & 1) == 0 && data_at(&((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)))))->cnode.slots)) + SLOT_CNODE_CAP)->capability.cap_content.category.category_right), unsigned int, mint_value(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)))))->cnode.slots)) + SLOT_CNODE_CAP)->capability.cap_content.category.category_right))) * mint_heap(mint_remove(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)))))->cnode.slots)) + SLOT_CNODE_CAP)->capability.cap_content.category.category_right)))) ||
      ((mint_value(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)))))->cnode.slots)) + SLOT_CNODE_CAP)->capability.cap_content.category.category_right)) & 1) != 0 && data_at(&((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)))))->cnode.slots)) + SLOT_CNODE_CAP)->capability.cap_content.category.category_right), unsigned int, mint_value(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)))))->cnode.slots)) + SLOT_CNODE_CAP)->capability.cap_content.category.category_right))) * data_at(((unsigned char *)&CapParent + destTask_Prio@pre), unsigned char, mint_value(h, ((unsigned char *)&CapParent + destTask_Prio@pre))) * mint_heap(mint_remove(mint_remove(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)))))->cnode.slots)) + SLOT_CNODE_CAP)->capability.cap_content.category.category_right)), ((unsigned char *)&CapParent + destTask_Prio@pre)))) */
    if ((pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right &
         CNODE_MINT_CAP) == 0U || CapParent[destTask_Prio] != srcTask_Prio) {
        ; /* EXIT_CRITICAL: sequential ordinary-memory identity */
        return (unsigned char)USER_CAPABILITY_NONE;
    } else {
        /*@ mint_wellformed(h) && mint_readable(h, 0, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)))))->cnode.slots)) + SLOT_CNODE_CAP)->capability.cap_content.category.category_right)) && mint_readable(h, 1, ((unsigned char *)&CapParent + destTask_Prio@pre)) && data_at(&((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)))))->cnode.slots)) + SLOT_CNODE_CAP)->capability.cap_content.category.category_right), unsigned int, mint_value(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)))))->cnode.slots)) + SLOT_CNODE_CAP)->capability.cap_content.category.category_right))) * data_at(((unsigned char *)&CapParent + destTask_Prio@pre), unsigned char, mint_value(h, ((unsigned char *)&CapParent + destTask_Prio@pre))) * mint_heap(mint_remove(mint_remove(h, &((((struct slot *)&(((struct cspace *)mint_value(h, ((struct cspace **)&OSCSpacePrioTbl + mint_value(h, &(((struct os_tcb *)mint_value(h, &OSTCBCur))->OSTCBPrio)))))->cnode.slots)) + SLOT_CNODE_CAP)->capability.cap_content.category.category_right)), ((unsigned char *)&CapParent + destTask_Prio@pre)))
          which implies mint_heap(h) */
        i = ucos_CNode_Mint(destTask_Prio, srcTask_Prio, func_capability, rights) /*@ where L = L, h = h */;
        if (i == CNODE_NONE_FAULT) {
            ; /* EXIT_CRITICAL: sequential ordinary-memory identity */
            return (unsigned char)CNODE_MINT_SUCCESS;
        } else {
            ; /* EXIT_CRITICAL: sequential ordinary-memory identity */
            return (unsigned char)CNODE_MINT_FAILURE;
        }
    }
}

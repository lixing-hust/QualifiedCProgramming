/* User-selected sequential ordinary-memory projection (see experiment
 * sequential-scope.md): critical markers are identity steps in THIS model.
 * No claim about original encrit/excrit, interrupts or concurrency follows.
 * Marker sites, all data/control behavior, the real union and callee remain. */
#define ENTER_CRITICAL
#define EXIT_CRITICAL
#include "osverify_qcp/include/ios_cap_types.h"
#include "QCP_demos_LLM/verification_stdlib.h"
/*@ Import Coq Require Import SimpleC.EE.osverify_qcp.cases.grant_cspace_cap_inferred_lib */
/*@ Extern Coq
    (grant_call_pre : Z -> Z -> Z -> Z -> Assertion)
    (unsigned_last_nbits : Z -> Z -> Z)
    (grant_rights : Z -> Z -> Z)
    (grant_permit : Z -> Z -> Z -> Z -> Prop)
    (grant_call_success : Z -> Z -> Z -> Prop)
    (grant_success : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
    (grant_return : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z)
    (grant_call_return : Z -> Z -> Z -> Z)
*/

unsigned char ucos_Grant_Cap(unsigned char destTask_Prio,
                           unsigned int cap_Class, unsigned int cap_Right)
/*@ With dp oldright
    Require grant_call_pre(destTask_Prio, cap_Class, dp, oldright)
    Ensure (cap_Class > 16 && __return == 11 && emp)
      || (cap_Class <= 16 && destTask_Prio >= 64 && __return == 11 && emp)
      || (cap_Class <= 16 && destTask_Prio < 64 && dp == 0 && __return == 11 && data_at(((struct cspace **)&OSCSpacePrioTbl + destTask_Prio), struct cspace *, dp))
      || (cap_Class <= 16 && destTask_Prio < 64 && dp != 0 && __return == 0 && data_at(((struct cspace **)&OSCSpacePrioTbl + destTask_Prio), struct cspace *, dp) * data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + cap_Class))->capability.cap_type), unsigned int, 1) * data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + cap_Class))->capability.cap_content.category.category_content), unsigned int, cap_Class) * data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + cap_Class))->capability.cap_content.category.category_right), unsigned int, grant_rights(oldright, cap_Right)))
*/
{
    /*@ 0 <= cap_Class by local */
    /*@ Assert
        destTask_Prio == destTask_Prio@pre && cap_Class == cap_Class@pre && cap_Right == cap_Right@pre &&
        0 <= cap_Class &&
        ((cap_Class > 16 && emp)
      || (cap_Class <= 16 && destTask_Prio >= 64 && emp)
      || (cap_Class <= 16 && destTask_Prio < 64 && dp == 0 && data_at(((struct cspace **)&OSCSpacePrioTbl + destTask_Prio), struct cspace *, dp))
      || (cap_Class <= 16 && destTask_Prio < 64 && dp != 0 && data_at(((struct cspace **)&OSCSpacePrioTbl + destTask_Prio), struct cspace *, dp) * undef_data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + cap_Class))->capability.cap_type), unsigned int) * undef_data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + cap_Class))->capability.cap_content.category.category_content), unsigned int) * data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + cap_Class))->capability.cap_content.category.category_right), unsigned int, oldright)))
    */
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

unsigned char grant_cspace_cap(unsigned char destTask_Prio,
                              unsigned int cap_Class, unsigned int cap_Right)
/*@ With cp p dp q oldcur run auth parent oldright dest0 class0 right0
    Require
      destTask_Prio == dest0 && cap_Class == class0 && cap_Right == right0 && (
      (destTask_Prio >= 63 &&
        emp)
      ||
      (destTask_Prio < 63 && 0 <= q && q < 64 && cp != 0 && p == 0 &&
        data_at(&OSPrioCur, unsigned char, oldcur) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p))
      ||
      (destTask_Prio < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) == 0 &&
        data_at(&OSPrioCur, unsigned char, oldcur) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth))
      ||
      (destTask_Prio < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent != q &&
        data_at(&OSPrioCur, unsigned char, oldcur) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth) *
        data_at(((unsigned char *)&CapParent + destTask_Prio), unsigned char, parent))
      ||
      (destTask_Prio < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run == 0 && cap_Class > 16 &&
        data_at(&OSPrioCur, unsigned char, oldcur) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run))
      ||
      (destTask_Prio < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run == 0 && destTask_Prio == q && dp == p && cap_Class <= 16 && dp != 0 &&
        data_at(&OSPrioCur, unsigned char, oldcur) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        undef_data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_type), unsigned int) *
        undef_data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_content.category.category_content), unsigned int) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_content.category.category_right), unsigned int, oldright))
      ||
      (destTask_Prio < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run == 0 && destTask_Prio != q && cap_Class <= 16 && dp == 0 &&
        data_at(&OSPrioCur, unsigned char, oldcur) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + destTask_Prio), struct cspace *, dp))
      ||
      (destTask_Prio < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run == 0 && destTask_Prio != q && cap_Class <= 16 && dp != 0 &&
        data_at(&OSPrioCur, unsigned char, oldcur) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + destTask_Prio), struct cspace *, dp) *
        undef_data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_type), unsigned int) *
        undef_data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_content.category.category_content), unsigned int) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_content.category.category_right), unsigned int, oldright))
      ||
      (destTask_Prio < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && cap_Class > 16 &&
        data_at(&OSPrioCur, unsigned char, oldcur) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((unsigned char *)&CapParent + destTask_Prio), unsigned char, parent) *
        data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth))
      ||
      (destTask_Prio < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && destTask_Prio == q && dp == p && cap_Class <= 16 && dp != 0 && p == dp && cap_Class == SLOT_CNODE_CAP && oldright == auth &&
        data_at(&OSPrioCur, unsigned char, oldcur) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((unsigned char *)&CapParent + destTask_Prio), unsigned char, parent) *
        undef_data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_type), unsigned int) *
        undef_data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_content.category.category_content), unsigned int) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_content.category.category_right), unsigned int, oldright))
      ||
      (destTask_Prio < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && destTask_Prio == q && dp == p && cap_Class <= 16 && dp != 0 && p == dp && cap_Class != SLOT_CNODE_CAP &&
        data_at(&OSPrioCur, unsigned char, oldcur) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((unsigned char *)&CapParent + destTask_Prio), unsigned char, parent) *
        data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth) *
        undef_data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_type), unsigned int) *
        undef_data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_content.category.category_content), unsigned int) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_content.category.category_right), unsigned int, oldright))
      ||
      (destTask_Prio < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && destTask_Prio != q && cap_Class <= 16 && dp == 0 &&
        data_at(&OSPrioCur, unsigned char, oldcur) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((unsigned char *)&CapParent + destTask_Prio), unsigned char, parent) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + destTask_Prio), struct cspace *, dp) *
        data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth))
      ||
      (destTask_Prio < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && destTask_Prio != q && cap_Class <= 16 && dp != 0 && p == dp && cap_Class == SLOT_CNODE_CAP && oldright == auth &&
        data_at(&OSPrioCur, unsigned char, oldcur) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((unsigned char *)&CapParent + destTask_Prio), unsigned char, parent) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + destTask_Prio), struct cspace *, dp) *
        undef_data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_type), unsigned int) *
        undef_data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_content.category.category_content), unsigned int) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_content.category.category_right), unsigned int, oldright))
      ||
      (destTask_Prio < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && destTask_Prio != q && cap_Class <= 16 && dp != 0 && p == dp && cap_Class != SLOT_CNODE_CAP &&
        data_at(&OSPrioCur, unsigned char, oldcur) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((unsigned char *)&CapParent + destTask_Prio), unsigned char, parent) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + destTask_Prio), struct cspace *, dp) *
        data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth) *
        undef_data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_type), unsigned int) *
        undef_data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_content.category.category_content), unsigned int) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_content.category.category_right), unsigned int, oldright))
      ||
      (destTask_Prio < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && destTask_Prio != q && cap_Class <= 16 && dp != 0 && p != dp &&
        data_at(&OSPrioCur, unsigned char, oldcur) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((unsigned char *)&CapParent + destTask_Prio), unsigned char, parent) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + destTask_Prio), struct cspace *, dp) *
        data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth) *
        undef_data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_type), unsigned int) *
        undef_data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_content.category.category_content), unsigned int) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (cap_Class)))->capability.cap_content.category.category_right), unsigned int, oldright))
      )
    Ensure
      (dest0 >= 63 && __return == 42 &&
        emp)
      ||
      (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p == 0 && __return == 11 &&
        data_at(&OSPrioCur, unsigned char, q) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p))
      ||
      (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) == 0 && __return == 252 &&
        data_at(&OSPrioCur, unsigned char, q) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth))
      ||
      (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent != q && __return == 252 &&
        data_at(&OSPrioCur, unsigned char, q) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth) *
        data_at(((unsigned char *)&CapParent + dest0), unsigned char, parent))
      ||
      (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run == 0 && class0 > 16 && __return == 11 &&
        data_at(&OSPrioCur, unsigned char, q) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run))
      ||
      (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run == 0 && dest0 == q && dp == p && class0 <= 16 && dp != 0 && __return == 0 &&
        data_at(&OSPrioCur, unsigned char, q) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_type), unsigned int, 1) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_content.category.category_content), unsigned int, class0) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_content.category.category_right), unsigned int, grant_rights(oldright, right0)))
      ||
      (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run == 0 && dest0 != q && class0 <= 16 && dp == 0 && __return == 11 &&
        data_at(&OSPrioCur, unsigned char, q) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + dest0), struct cspace *, dp))
      ||
      (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run == 0 && dest0 != q && class0 <= 16 && dp != 0 && __return == 0 &&
        data_at(&OSPrioCur, unsigned char, q) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + dest0), struct cspace *, dp) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_type), unsigned int, 1) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_content.category.category_content), unsigned int, class0) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_content.category.category_right), unsigned int, grant_rights(oldright, right0)))
      ||
      (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && class0 > 16 && __return == 11 &&
        data_at(&OSPrioCur, unsigned char, q) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((unsigned char *)&CapParent + dest0), unsigned char, parent) *
        data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth))
      ||
      (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && dest0 == q && dp == p && class0 <= 16 && dp != 0 && p == dp && class0 == SLOT_CNODE_CAP && oldright == auth && __return == 0 &&
        data_at(&OSPrioCur, unsigned char, q) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((unsigned char *)&CapParent + dest0), unsigned char, parent) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_type), unsigned int, 1) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_content.category.category_content), unsigned int, class0) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_content.category.category_right), unsigned int, grant_rights(oldright, right0)))
      ||
      (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && dest0 == q && dp == p && class0 <= 16 && dp != 0 && p == dp && class0 != SLOT_CNODE_CAP && __return == 0 &&
        data_at(&OSPrioCur, unsigned char, q) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((unsigned char *)&CapParent + dest0), unsigned char, parent) *
        data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_type), unsigned int, 1) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_content.category.category_content), unsigned int, class0) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_content.category.category_right), unsigned int, grant_rights(oldright, right0)))
      ||
      (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && dest0 != q && class0 <= 16 && dp == 0 && __return == 11 &&
        data_at(&OSPrioCur, unsigned char, q) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((unsigned char *)&CapParent + dest0), unsigned char, parent) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + dest0), struct cspace *, dp) *
        data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth))
      ||
      (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && dest0 != q && class0 <= 16 && dp != 0 && p == dp && class0 == SLOT_CNODE_CAP && oldright == auth && __return == 0 &&
        data_at(&OSPrioCur, unsigned char, q) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((unsigned char *)&CapParent + dest0), unsigned char, parent) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + dest0), struct cspace *, dp) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_type), unsigned int, 1) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_content.category.category_content), unsigned int, class0) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_content.category.category_right), unsigned int, grant_rights(oldright, right0)))
      ||
      (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && dest0 != q && class0 <= 16 && dp != 0 && p == dp && class0 != SLOT_CNODE_CAP && __return == 0 &&
        data_at(&OSPrioCur, unsigned char, q) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((unsigned char *)&CapParent + dest0), unsigned char, parent) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + dest0), struct cspace *, dp) *
        data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_type), unsigned int, 1) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_content.category.category_content), unsigned int, class0) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_content.category.category_right), unsigned int, grant_rights(oldright, right0)))
      ||
      (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && dest0 != q && class0 <= 16 && dp != 0 && p != dp && __return == 0 &&
        data_at(&OSPrioCur, unsigned char, q) *
        data_at(&OSTCBCur, struct os_tcb *, cp) *
        data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
        data_at(&OSRunning, unsigned char, run) *
        data_at(((unsigned char *)&CapParent + dest0), unsigned char, parent) *
        data_at(((struct cspace **)&OSCSpacePrioTbl + dest0), struct cspace *, dp) *
        data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_type), unsigned int, 1) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_content.category.category_content), unsigned int, class0) *
        data_at(&(((((struct slot *)&(((struct cspace *)dp)->cnode.slots)) + (class0)))->capability.cap_content.category.category_right), unsigned int, grant_rights(oldright, right0)))
*/
{
    unsigned char i;
    CSPACE *pCSpace;
    /*@ 0 <= destTask_Prio && destTask_Prio <= 255 by local */
    /*@ (unsigned int)destTask_Prio == destTask_Prio by local */
    if (destTask_Prio >= OS_LOWEST_PRIO) {
        return (unsigned char)OS_PRIO_INVALID;
    }
    ENTER_CRITICAL;
    OSPrioCur = OSTCBCur->OSTCBPrio;
    pCSpace = OSCSpacePrioTbl[OSPrioCur];
    if (pCSpace == (CSPACE *)0) {
        EXIT_CRITICAL;
        return (unsigned char)CNODE_GRANT_FAILURE;
    }
    /*@ 0 <= run && run <= 255 by local */
    /*@ unsigned_last_nbits(run, 32) == run by local */
    if (OSRunning == CFalse ||
        (pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right & CNODE_GRANT_CAP) != 0 &&
        CapParent[destTask_Prio] == OSPrioCur) {
        /*@ Assert
          (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run == 0 && class0 > 16 && destTask_Prio == dest0 && cap_Class == class0 && cap_Right == right0 && pCSpace == p &&
            data_at(&OSPrioCur, unsigned char, q) *
            data_at(&OSTCBCur, struct os_tcb *, cp) *
            data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
            data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
            data_at(&OSRunning, unsigned char, run) *
            undef_data_at(&i, unsigned char) *
            grant_call_pre(dest0, class0, dp, oldright))
          ||
          (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run == 0 && dest0 == q && dp == p && class0 <= 16 && dp != 0 && destTask_Prio == dest0 && cap_Class == class0 && cap_Right == right0 && pCSpace == p &&
            data_at(&OSPrioCur, unsigned char, q) *
            data_at(&OSTCBCur, struct os_tcb *, cp) *
            data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
            data_at(&OSRunning, unsigned char, run) *
            undef_data_at(&i, unsigned char) *
            grant_call_pre(dest0, class0, dp, oldright))
          ||
          (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run == 0 && dest0 != q && class0 <= 16 && dp == 0 && destTask_Prio == dest0 && cap_Class == class0 && cap_Right == right0 && pCSpace == p &&
            data_at(&OSPrioCur, unsigned char, q) *
            data_at(&OSTCBCur, struct os_tcb *, cp) *
            data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
            data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
            data_at(&OSRunning, unsigned char, run) *
            undef_data_at(&i, unsigned char) *
            grant_call_pre(dest0, class0, dp, oldright))
          ||
          (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run == 0 && dest0 != q && class0 <= 16 && dp != 0 && destTask_Prio == dest0 && cap_Class == class0 && cap_Right == right0 && pCSpace == p &&
            data_at(&OSPrioCur, unsigned char, q) *
            data_at(&OSTCBCur, struct os_tcb *, cp) *
            data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
            data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
            data_at(&OSRunning, unsigned char, run) *
            undef_data_at(&i, unsigned char) *
            grant_call_pre(dest0, class0, dp, oldright))
          ||
          (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && class0 > 16 && destTask_Prio == dest0 && cap_Class == class0 && cap_Right == right0 && pCSpace == p &&
            data_at(&OSPrioCur, unsigned char, q) *
            data_at(&OSTCBCur, struct os_tcb *, cp) *
            data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
            data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
            data_at(&OSRunning, unsigned char, run) *
            data_at(((unsigned char *)&CapParent + dest0), unsigned char, parent) *
            data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth) *
            undef_data_at(&i, unsigned char) *
            grant_call_pre(dest0, class0, dp, oldright))
          ||
          (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && dest0 == q && dp == p && class0 <= 16 && dp != 0 && p == dp && class0 == SLOT_CNODE_CAP && oldright == auth && destTask_Prio == dest0 && cap_Class == class0 && cap_Right == right0 && pCSpace == p &&
            data_at(&OSPrioCur, unsigned char, q) *
            data_at(&OSTCBCur, struct os_tcb *, cp) *
            data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
            data_at(&OSRunning, unsigned char, run) *
            data_at(((unsigned char *)&CapParent + dest0), unsigned char, parent) *
            undef_data_at(&i, unsigned char) *
            grant_call_pre(dest0, class0, dp, oldright))
          ||
          (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && dest0 == q && dp == p && class0 <= 16 && dp != 0 && p == dp && class0 != SLOT_CNODE_CAP && destTask_Prio == dest0 && cap_Class == class0 && cap_Right == right0 && pCSpace == p &&
            data_at(&OSPrioCur, unsigned char, q) *
            data_at(&OSTCBCur, struct os_tcb *, cp) *
            data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
            data_at(&OSRunning, unsigned char, run) *
            data_at(((unsigned char *)&CapParent + dest0), unsigned char, parent) *
            data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth) *
            undef_data_at(&i, unsigned char) *
            grant_call_pre(dest0, class0, dp, oldright))
          ||
          (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && dest0 != q && class0 <= 16 && dp == 0 && destTask_Prio == dest0 && cap_Class == class0 && cap_Right == right0 && pCSpace == p &&
            data_at(&OSPrioCur, unsigned char, q) *
            data_at(&OSTCBCur, struct os_tcb *, cp) *
            data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
            data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
            data_at(&OSRunning, unsigned char, run) *
            data_at(((unsigned char *)&CapParent + dest0), unsigned char, parent) *
            data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth) *
            undef_data_at(&i, unsigned char) *
            grant_call_pre(dest0, class0, dp, oldright))
          ||
          (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && dest0 != q && class0 <= 16 && dp != 0 && p == dp && class0 == SLOT_CNODE_CAP && oldright == auth && destTask_Prio == dest0 && cap_Class == class0 && cap_Right == right0 && pCSpace == p &&
            data_at(&OSPrioCur, unsigned char, q) *
            data_at(&OSTCBCur, struct os_tcb *, cp) *
            data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
            data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
            data_at(&OSRunning, unsigned char, run) *
            data_at(((unsigned char *)&CapParent + dest0), unsigned char, parent) *
            undef_data_at(&i, unsigned char) *
            grant_call_pre(dest0, class0, dp, oldright))
          ||
          (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && dest0 != q && class0 <= 16 && dp != 0 && p == dp && class0 != SLOT_CNODE_CAP && destTask_Prio == dest0 && cap_Class == class0 && cap_Right == right0 && pCSpace == p &&
            data_at(&OSPrioCur, unsigned char, q) *
            data_at(&OSTCBCur, struct os_tcb *, cp) *
            data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
            data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
            data_at(&OSRunning, unsigned char, run) *
            data_at(((unsigned char *)&CapParent + dest0), unsigned char, parent) *
            data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth) *
            undef_data_at(&i, unsigned char) *
            grant_call_pre(dest0, class0, dp, oldright))
          ||
          (dest0 < 63 && 0 <= q && q < 64 && cp != 0 && p != 0 && run != 0 && (auth & 64) != 0 && parent == q && dest0 != q && class0 <= 16 && dp != 0 && p != dp && destTask_Prio == dest0 && cap_Class == class0 && cap_Right == right0 && pCSpace == p &&
            data_at(&OSPrioCur, unsigned char, q) *
            data_at(&OSTCBCur, struct os_tcb *, cp) *
            data_at(&(((struct os_tcb *)cp)->OSTCBPrio), unsigned char, q) *
            data_at(((struct cspace **)&OSCSpacePrioTbl + (q)), struct cspace *, p) *
            data_at(&OSRunning, unsigned char, run) *
            data_at(((unsigned char *)&CapParent + dest0), unsigned char, parent) *
            data_at(&(((((struct slot *)&(((struct cspace *)p)->cnode.slots)) + (SLOT_CNODE_CAP)))->capability.cap_content.category.category_right), unsigned int, auth) *
            undef_data_at(&i, unsigned char) *
            grant_call_pre(dest0, class0, dp, oldright))
        */
        i = ucos_Grant_Cap(destTask_Prio, cap_Class, cap_Right);
        /*@ (unsigned int)i == i by local */
        if (i == CNODE_NONE_FAULT) {
            EXIT_CRITICAL;
            return (unsigned char)CSPACE_NONE_FAULT;
        } else {
            EXIT_CRITICAL;
            return (unsigned char)CNODE_GRANT_FAILURE;
        }
    } else {
        EXIT_CRITICAL;
        return (unsigned char)USER_CAPABILITY_NONE;
    }
}

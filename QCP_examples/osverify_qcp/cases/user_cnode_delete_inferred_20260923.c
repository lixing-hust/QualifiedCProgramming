#include "QCP_examples/osverify_qcp/include/ios_cap_types.h"
#define CAP_FUNCTION_TYPE 1U
#define CAP_SEM_TYPE 2U
#define CAP_MUTEX_TYPE 3U
#define CAP_Q_TYPE 4U
#define CAP_TASK_TYPE 5U
#define OS_STAT_PRIO 62U
#define OBJ_POSITION 17U
#define EINVAL 30U
#define CNODE_DELETE_CAP 16U
#define CNODE_DELETE_SUCCESS 0U
#define NULL ((void *)0)
/* Identity markers only under the explicit sequential ordinary-memory projection. */
#define ENTER_CRITICAL ((void)0)
#define EXIT_CRITICAL ((void)0)

struct os_event;
/* Source Int32, pthread_t and long are all Tint32; int fixes the 32-bit layout. */
struct sem_info {
  int sem_type; char *sem_name;
  int sem_maxvalue; int sem_curvalue; int sem_opencnt; int sem_linked;
  int tasks_blocked; struct os_event *pevent; unsigned char sem_cap[28];
};
struct pthread_mutex_info {
  int mutex_type; int protocol; int prio_ceiling; int waitq_type;
  int cancel_safe; int mutex_owner; int recursive_cnt; int tasks_blocked;
  struct os_event *pevent; unsigned char mutex_cap[28];
};
struct mq_attr {
  int mq_waittype; int mq_flags; int mq_maxmsg; int mq_msgsize; int mq_curmsgs;
  struct os_event *pevent; unsigned char mq_cap[28];
};
/* Required compile-time binding of the source's symbolic OS_MAX_EVENTS.
   No default is chosen; no runtime configuration read is introduced. */
#ifndef QCP_DELETE_OS_MAX_EVENTS
#error "Bind QCP_DELETE_OS_MAX_EVENTS to the source configuration (19..255)"
#endif
#if QCP_DELETE_OS_MAX_EVENTS < 19 || QCP_DELETE_OS_MAX_EVENTS > 255
#error "QCP_DELETE_OS_MAX_EVENTS is outside the source parameter range"
#endif
enum { DELETE_CONFIG_MAX_EVENTS = QCP_DELETE_OS_MAX_EVENTS };
#define OS_USER_MAX_EVENTS (DELETE_CONFIG_MAX_EVENTS - 16U)
extern struct sem_info Sem_info[];
extern struct pthread_mutex_info Pthread_Mutex[];
extern struct mq_attr Mq_Attr[];
extern OS_TCB *OSTCBPrioTbl[64];
extern unsigned int OSCSpaceObjectPointer[];

/*@ Import Coq Require Import SimpleC.EE.osverify_qcp.cases.user_cnode_delete_inferred_20260923_lib */
/*@ Extern Coq
  (DMemory : Type)
  (DHeap : DMemory -> Assertion)
  (DHeapRest : DMemory -> Z -> Assertion)
  (DHeapRest2 : DMemory -> Z -> Z -> Assertion)
  (DHeapRest3 : DMemory -> Z -> Z -> Z -> Assertion)
  (DHeapRest4 : DMemory -> Z -> Z -> Z -> Z -> Assertion)
  (DWrite : DMemory -> Z -> Z -> DMemory)
  (DPayloadDeleted : DMemory -> Z -> Z -> DMemory)
  (DDeleted : DMemory -> Z -> Z -> DMemory)
  (DCurrent : DMemory -> Z)
  (DPrioAddress : DMemory -> Z)
  (DPrio : DMemory -> Z)
  (DRightAddress : DMemory -> Z)
  (DRightBits : DMemory -> Z)
  (DTyped : DMemory -> Prop)
  (DUnionLayout : Prop)
  (DGetSafe : DMemory -> Z -> Z -> Prop)
  (DGetResult : DMemory -> Z -> Z -> Z -> Prop)
  (DCheckSafe : DMemory -> Z -> Z -> Z -> Z -> Prop)
  (DCheckResult : DMemory -> Z -> Z -> Z -> Z -> Z -> Prop)
  (DCoreSafe : DMemory -> Z -> Z -> Prop)
  (DCoreResult : DMemory -> Z -> Z -> Z -> DMemory -> Prop)
  (DUserSafe : DMemory -> Z -> Z -> Z -> Z -> Prop)
  (DUserResult : DMemory -> Z -> Z -> Z -> Z -> Z -> DMemory -> Prop)
  (DSpace : DMemory -> Z -> Z)
  (DEnd : DMemory -> Z -> Z)
  (DAbsent : DMemory -> Z -> Z -> Z -> Z -> Prop)
  (DVal : DMemory -> Z -> Z)
  (DReadUInt : DMemory -> Z -> Prop)
  (DReadPtr : DMemory -> Z -> Prop)
  (DReadByte : DMemory -> Z -> Prop)
  (DWriteUInt : DMemory -> Z -> Prop)
  (DWritePtr : DMemory -> Z -> Prop)
  (DAuthFootprint : DMemory -> Z -> Prop)
  (DAuthorized : DMemory -> Z -> Prop)
*/

unsigned int Get_Obj_Slot(unsigned char prio, void *func_object)
/*@ With (m : DMemory)
    Require DTyped(m) && DUnionLayout && DGetSafe(m, prio, func_object) && DHeap(m)
    Ensure DGetResult(m, prio, func_object, __return) && DTyped(m) && DUnionLayout && DHeap(m)
*/
{
  unsigned int i;
  unsigned int endPtr;
  CSPACE *pCSpace;
  if (prio >= OS_LOWEST_PRIO) { return (unsigned int)OS_PRIO_INVALID; }
  ENTER_CRITICAL;
  /*@ DTyped(m) && DReadUInt(m, &(OSCSpaceObjectPointer[prio])) && (DHeap(m))
      which implies DTyped(m) && DReadUInt(m, &(OSCSpaceObjectPointer[prio])) && (data_at(&(OSCSpaceObjectPointer[prio]), unsigned int, DEnd(m, prio)) *
      DHeapRest(m, &(OSCSpaceObjectPointer[prio]))) */
  endPtr = OSCSpaceObjectPointer[prio];
  /*@ DTyped(m) && DReadUInt(m, &(OSCSpaceObjectPointer[prio])) && (data_at(&(OSCSpaceObjectPointer[prio]), unsigned int, DEnd(m, prio)) *
      DHeapRest(m, &(OSCSpaceObjectPointer[prio])))
      which implies DTyped(m) && DReadUInt(m, &(OSCSpaceObjectPointer[prio])) && (DHeap(m)) */
  /*@ DTyped(m) && DReadPtr(m, &(OSCSpacePrioTbl[prio])) && (DHeap(m))
      which implies DTyped(m) && DReadPtr(m, &(OSCSpacePrioTbl[prio])) && (data_at(&(OSCSpacePrioTbl[prio]), struct cspace *, DSpace(m, prio)) *
      DHeapRest(m, &(OSCSpacePrioTbl[prio]))) */
  pCSpace = OSCSpacePrioTbl[prio];
  /*@ DTyped(m) && DReadPtr(m, &(OSCSpacePrioTbl[prio])) && (data_at(&(OSCSpacePrioTbl[prio]), struct cspace *, DSpace(m, prio)) *
      DHeapRest(m, &(OSCSpacePrioTbl[prio])))
      which implies DTyped(m) && DReadPtr(m, &(OSCSpacePrioTbl[prio])) && (DHeap(m)) */
  EXIT_CRITICAL;
  if (pCSpace == (CSPACE *)NULL) { return (unsigned int)SLOT_NULL_CAP; }
  i = OBJ_POSITION;
  /*@ Inv Assert
      prio == prio@pre && prio < 63 && func_object == func_object@pre &&
      pCSpace == DSpace(m, prio) && pCSpace != 0 && endPtr == DEnd(m, prio) &&
      0 <= endPtr && endPtr <= 4294967295 &&
      17 <= i && i <= 255 && DAbsent(m, pCSpace, func_object, 17, i) &&
      DTyped(m) && DUnionLayout && DGetSafe(m, prio, func_object) && DHeap(m)
  */
  while (i < endPtr) {
    /*@ DTyped(m) && DReadPtr(m, &(pCSpace->cnode.slots[i].capability.cap_content.object.object_t)) && (DHeap(m))
      which implies DTyped(m) && DReadPtr(m, &(pCSpace->cnode.slots[i].capability.cap_content.object.object_t)) && (data_at(&(pCSpace->cnode.slots[i].capability.cap_content.object.object_t), void *,
                DVal(m, &(pCSpace->cnode.slots[i].capability.cap_content.object.object_t))) *
        DHeapRest(m, &(pCSpace->cnode.slots[i].capability.cap_content.object.object_t))) */
    if (pCSpace->cnode.slots[i].capability.cap_content.object.object_t == func_object) {
      /*@ DTyped(m) && DReadPtr(m, &(pCSpace->cnode.slots[i].capability.cap_content.object.object_t)) && (data_at(&(pCSpace->cnode.slots[i].capability.cap_content.object.object_t), void *,
                  DVal(m, &(pCSpace->cnode.slots[i].capability.cap_content.object.object_t))) *
          DHeapRest(m, &(pCSpace->cnode.slots[i].capability.cap_content.object.object_t)))
      which implies DTyped(m) && DReadPtr(m, &(pCSpace->cnode.slots[i].capability.cap_content.object.object_t)) && (DHeap(m)) */
      return i;
    }
    /*@ DTyped(m) && DReadPtr(m, &(pCSpace->cnode.slots[i].capability.cap_content.object.object_t)) && (data_at(&(pCSpace->cnode.slots[i].capability.cap_content.object.object_t), void *,
                DVal(m, &(pCSpace->cnode.slots[i].capability.cap_content.object.object_t))) *
        DHeapRest(m, &(pCSpace->cnode.slots[i].capability.cap_content.object.object_t)))
      which implies DTyped(m) && DReadPtr(m, &(pCSpace->cnode.slots[i].capability.cap_content.object.object_t)) && (DHeap(m)) */
    ++i;
  }
  return (unsigned int)SLOT_NULL_CAP;
}

int Check_Cap_Type(unsigned int func_capability, unsigned char func_capType, unsigned char prio)
/*@ With (m : DMemory) (max_events : Z)
    Require max_events == DELETE_CONFIG_MAX_EVENTS && DTyped(m) && DUnionLayout && DCheckSafe(m, max_events, func_capability, func_capType, prio) && DHeap(m)
    Ensure DCheckResult(m, max_events, func_capability, func_capType, prio, __return) &&
           0 <= __return && __return <= 255 && DTyped(m) && DUnionLayout && DHeap(m)
*/
{
  int ret;
  if (func_capType == CAP_FUNCTION_TYPE) {
    if (func_capability <= CAP_CHANNEL_CLASS) { return func_capability; }
    else { return (int)SLOT_NUM; }
  }
  if ((func_capType == CAP_SEM_TYPE || func_capType == CAP_MUTEX_TYPE || func_capType == CAP_Q_TYPE)
      && func_capability < OS_USER_MAX_EVENTS / 3U) {
    if (func_capType == CAP_SEM_TYPE) {
      /*@ DTyped(m) && DReadPtr(m, &(Sem_info[func_capability].pevent)) && (DHeap(m))
      which implies DTyped(m) && DReadPtr(m, &(Sem_info[func_capability].pevent)) && (data_at(&(Sem_info[func_capability].pevent), struct os_event *, DVal(m, &(Sem_info[func_capability].pevent))) * DHeapRest(m, &(Sem_info[func_capability].pevent))) */
      if (Sem_info[func_capability].pevent == NULL) {
        /*@ DTyped(m) && DReadPtr(m, &(Sem_info[func_capability].pevent)) && (data_at(&(Sem_info[func_capability].pevent), struct os_event *, DVal(m, &(Sem_info[func_capability].pevent))) * DHeapRest(m, &(Sem_info[func_capability].pevent)))
      which implies DTyped(m) && DReadPtr(m, &(Sem_info[func_capability].pevent)) && (DHeap(m)) */
        return (int)SLOT_NUM;
      }
      /* The argument cell must remain exposed for its read. The required call
         entailment data_at * DHeapRest -> DHeap(m) is not yet tool-validated. */
      ret = Get_Obj_Slot(prio, (void *)Sem_info[func_capability].pevent) /*@ where m = m */;
      if (ret == SLOT_NULL_CAP) { return (int)SLOT_NUM; }
      else { return (int)ret; }
    }
    if (func_capType == CAP_MUTEX_TYPE) {
      /*@ DTyped(m) && DReadPtr(m, &(Pthread_Mutex[func_capability].pevent)) && (DHeap(m))
      which implies DTyped(m) && DReadPtr(m, &(Pthread_Mutex[func_capability].pevent)) && (data_at(&(Pthread_Mutex[func_capability].pevent), struct os_event *, DVal(m, &(Pthread_Mutex[func_capability].pevent))) * DHeapRest(m, &(Pthread_Mutex[func_capability].pevent))) */
      if (Pthread_Mutex[func_capability].pevent == NULL) {
        /*@ DTyped(m) && DReadPtr(m, &(Pthread_Mutex[func_capability].pevent)) && (data_at(&(Pthread_Mutex[func_capability].pevent), struct os_event *, DVal(m, &(Pthread_Mutex[func_capability].pevent))) * DHeapRest(m, &(Pthread_Mutex[func_capability].pevent)))
      which implies DTyped(m) && DReadPtr(m, &(Pthread_Mutex[func_capability].pevent)) && (DHeap(m)) */
        return (unsigned int)SLOT_NUM;
      }
      /* The argument cell must remain exposed for its read. The required call
         entailment data_at * DHeapRest -> DHeap(m) is not yet tool-validated. */
      ret = Get_Obj_Slot(prio, (void *)Pthread_Mutex[func_capability].pevent) /*@ where m = m */;
      if (ret == SLOT_NULL_CAP) { return (int)SLOT_NUM; }
      else { return (int)ret; }
    }
    if (func_capType == CAP_Q_TYPE) {
      /*@ DTyped(m) && DReadPtr(m, &(Mq_Attr[func_capability].pevent)) && (DHeap(m))
      which implies DTyped(m) && DReadPtr(m, &(Mq_Attr[func_capability].pevent)) && (data_at(&(Mq_Attr[func_capability].pevent), struct os_event *, DVal(m, &(Mq_Attr[func_capability].pevent))) * DHeapRest(m, &(Mq_Attr[func_capability].pevent))) */
      if (Mq_Attr[func_capability].pevent == NULL) {
        /*@ DTyped(m) && DReadPtr(m, &(Mq_Attr[func_capability].pevent)) && (data_at(&(Mq_Attr[func_capability].pevent), struct os_event *, DVal(m, &(Mq_Attr[func_capability].pevent))) * DHeapRest(m, &(Mq_Attr[func_capability].pevent)))
      which implies DTyped(m) && DReadPtr(m, &(Mq_Attr[func_capability].pevent)) && (DHeap(m)) */
        return (unsigned int)SLOT_NUM;
      }
      /* The argument cell must remain exposed for its read. The required call
         entailment data_at * DHeapRest -> DHeap(m) is not yet tool-validated. */
      ret = Get_Obj_Slot(prio, (void *)Mq_Attr[func_capability].pevent) /*@ where m = m */;
      if (ret == SLOT_NULL_CAP) { return (int)SLOT_NUM; }
      else { return (int)ret; }
    }
    return (int)EINVAL;
  }
  if (func_capType == CAP_TASK_TYPE && func_capability < OS_STAT_PRIO && func_capability > 0U) {
    /*@ DTyped(m) && DReadPtr(m, &(OSTCBPrioTbl[func_capability])) && (DHeap(m))
      which implies DTyped(m) && DReadPtr(m, &(OSTCBPrioTbl[func_capability])) && (data_at(&(OSTCBPrioTbl[func_capability]), struct os_tcb *, DVal(m, &(OSTCBPrioTbl[func_capability]))) * DHeapRest(m, &(OSTCBPrioTbl[func_capability]))) */
    if (OSTCBPrioTbl[func_capability] == (OS_TCB *)NULL) {
      /*@ DTyped(m) && DReadPtr(m, &(OSTCBPrioTbl[func_capability])) && (data_at(&(OSTCBPrioTbl[func_capability]), struct os_tcb *, DVal(m, &(OSTCBPrioTbl[func_capability]))) * DHeapRest(m, &(OSTCBPrioTbl[func_capability])))
      which implies DTyped(m) && DReadPtr(m, &(OSTCBPrioTbl[func_capability])) && (DHeap(m)) */
      return (int)SLOT_NUM;
    }
    /* The argument cell must remain exposed for its read. The required call
       entailment data_at * DHeapRest -> DHeap(m) is not yet tool-validated. */
    ret = Get_Obj_Slot(prio, (void *)OSTCBPrioTbl[func_capability]) /*@ where m = m */;
    if (ret == SLOT_NULL_CAP) { return (int)SLOT_NUM; }
    else { return (int)ret; }
  }
  return (int)SLOT_NUM;
}

unsigned char ucos_CNode_Delete(unsigned char destTask_Prio, unsigned int func_capability)
/*@ With (m : DMemory)
    Require DTyped(m) && DUnionLayout && DCoreSafe(m, destTask_Prio, func_capability) && DHeap(m)
    Ensure exists m1,
      DCoreResult(m, destTask_Prio, func_capability, __return, m1) && DHeap(m1)
*/
{
  CSPACE *pCSpace1;
  Cap *cap1;
  if (func_capability >= SLOT_NUM) { return CNODE_DELETE_FAILURE; }
  if (destTask_Prio >= 64U) { return CNODE_DELETE_FAILURE; }
  /*@ DTyped(m) && DReadPtr(m, &(OSCSpacePrioTbl[destTask_Prio])) && (DHeap(m))
      which implies DTyped(m) && DReadPtr(m, &(OSCSpacePrioTbl[destTask_Prio])) && (data_at(&(OSCSpacePrioTbl[destTask_Prio]), struct cspace *, DSpace(m, destTask_Prio)) * DHeapRest(m, &(OSCSpacePrioTbl[destTask_Prio]))) */
  pCSpace1 = OSCSpacePrioTbl[destTask_Prio];
  /*@ DTyped(m) && DReadPtr(m, &(OSCSpacePrioTbl[destTask_Prio])) && (data_at(&(OSCSpacePrioTbl[destTask_Prio]), struct cspace *, DSpace(m, destTask_Prio)) * DHeapRest(m, &(OSCSpacePrioTbl[destTask_Prio])))
      which implies DTyped(m) && DReadPtr(m, &(OSCSpacePrioTbl[destTask_Prio])) && (DHeap(m)) */
  if (pCSpace1 == (CSPACE *)NULL) { return CNODE_DELETE_FAILURE; }
  cap1 = &(pCSpace1->cnode.slots[func_capability].capability);
  /*@ DTyped(m) && DReadUInt(m, &(cap1->cap_type)) && (DHeap(m))
      which implies DTyped(m) && DReadUInt(m, &(cap1->cap_type)) && (data_at(&(cap1->cap_type), unsigned int, DVal(m, &(cap1->cap_type))) * DHeapRest(m, &(cap1->cap_type))) */
  if (cap1->cap_type == CAP_CATEGORY_TYPE) {
    cap1->cap_type = 0U;
    /*@ DTyped(m) && DWriteUInt(m, &(cap1->cap_type)) && (data_at(&(cap1->cap_type), unsigned int, 0) * DHeapRest(m, &(cap1->cap_type)))
      which implies DTyped(m) && DWriteUInt(m, &(cap1->cap_type)) && (DHeap(DWrite(m, &(cap1->cap_type), 0))) */
    /*@ DTyped(DWrite(m, &(cap1->cap_type), 0)) && DWriteUInt(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content)) && (DHeap(DWrite(m, &(cap1->cap_type), 0)))
      which implies DTyped(DWrite(m, &(cap1->cap_type), 0)) && DWriteUInt(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content)) && (undef_data_at(&(cap1->cap_content.category.category_content), unsigned int) *
        DHeapRest(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content))) */
    cap1->cap_content.category.category_content = 0U;
    /*@ DTyped(DWrite(m, &(cap1->cap_type), 0)) && DWriteUInt(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content)) && (data_at(&(cap1->cap_content.category.category_content), unsigned int, 0) * DHeapRest(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content)))
      which implies DTyped(DWrite(m, &(cap1->cap_type), 0)) && DWriteUInt(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content)) && (DHeap(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content), 0))) */
    /*@ DTyped(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content), 0)) && DWriteUInt(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content), 0), &(cap1->cap_content.category.category_right)) && (DHeap(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content), 0)))
      which implies DTyped(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content), 0)) && DWriteUInt(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content), 0), &(cap1->cap_content.category.category_right)) && (undef_data_at(&(cap1->cap_content.category.category_right), unsigned int) *
        DHeapRest(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content), 0), &(cap1->cap_content.category.category_right))) */
    cap1->cap_content.category.category_right = 0U;
    /*@ DTyped(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content), 0)) && DWriteUInt(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content), 0), &(cap1->cap_content.category.category_right)) && (data_at(&(cap1->cap_content.category.category_right), unsigned int, 0) * DHeapRest(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content), 0), &(cap1->cap_content.category.category_right)))
      which implies DTyped(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content), 0)) && DWriteUInt(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content), 0), &(cap1->cap_content.category.category_right)) && (DHeap(DWrite(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content), 0), &(cap1->cap_content.category.category_right), 0))) */
    /*@ (DWrite(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content), 0), &(cap1->cap_content.category.category_right), 0) == DPayloadDeleted(m, destTask_Prio, func_capability)) && (DHeap(DWrite(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content), 0), &(cap1->cap_content.category.category_right), 0)))
      which implies (DWrite(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.category.category_content), 0), &(cap1->cap_content.category.category_right), 0) == DPayloadDeleted(m, destTask_Prio, func_capability)) && (DHeap(DPayloadDeleted(m, destTask_Prio, func_capability))) */
  } else {
    if (cap1->cap_type == CAP_OBJECT_TYPE) {
      cap1->cap_type = 0U;
      /*@ DTyped(m) && DWriteUInt(m, &(cap1->cap_type)) && (data_at(&(cap1->cap_type), unsigned int, 0) * DHeapRest(m, &(cap1->cap_type)))
      which implies DTyped(m) && DWriteUInt(m, &(cap1->cap_type)) && (DHeap(DWrite(m, &(cap1->cap_type), 0))) */
      /*@ DTyped(DWrite(m, &(cap1->cap_type), 0)) && DWriteUInt(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right)) && (DHeap(DWrite(m, &(cap1->cap_type), 0)))
      which implies DTyped(DWrite(m, &(cap1->cap_type), 0)) && DWriteUInt(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right)) && (undef_data_at(&(cap1->cap_content.object.object_right), unsigned int) *
          DHeapRest(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right))) */
      cap1->cap_content.object.object_right = 0U;
      /*@ DTyped(DWrite(m, &(cap1->cap_type), 0)) && DWriteUInt(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right)) && (data_at(&(cap1->cap_content.object.object_right), unsigned int, 0) * DHeapRest(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right)))
      which implies DTyped(DWrite(m, &(cap1->cap_type), 0)) && DWriteUInt(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right)) && (DHeap(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right), 0))) */
      /*@ DTyped(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right), 0)) && DWritePtr(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right), 0), &(cap1->cap_content.object.object_t)) && (DHeap(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right), 0)))
      which implies DTyped(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right), 0)) && DWritePtr(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right), 0), &(cap1->cap_content.object.object_t)) && (undef_data_at(&(cap1->cap_content.object.object_t), void *) *
          DHeapRest(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right), 0), &(cap1->cap_content.object.object_t))) */
      cap1->cap_content.object.object_t = (void *)NULL;
      /*@ DTyped(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right), 0)) && DWritePtr(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right), 0), &(cap1->cap_content.object.object_t)) && (data_at(&(cap1->cap_content.object.object_t), void *, 0) * DHeapRest(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right), 0), &(cap1->cap_content.object.object_t)))
      which implies DTyped(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right), 0)) && DWritePtr(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right), 0), &(cap1->cap_content.object.object_t)) && (DHeap(DWrite(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right), 0), &(cap1->cap_content.object.object_t), 0))) */
      /*@ (DWrite(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right), 0), &(cap1->cap_content.object.object_t), 0) == DPayloadDeleted(m, destTask_Prio, func_capability)) && (DHeap(DWrite(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right), 0), &(cap1->cap_content.object.object_t), 0)))
      which implies (DWrite(DWrite(DWrite(m, &(cap1->cap_type), 0), &(cap1->cap_content.object.object_right), 0), &(cap1->cap_content.object.object_t), 0) == DPayloadDeleted(m, destTask_Prio, func_capability)) && (DHeap(DPayloadDeleted(m, destTask_Prio, func_capability))) */
    } else {
      /*@ DTyped(m) && DReadUInt(m, &(cap1->cap_type)) && (data_at(&(cap1->cap_type), unsigned int, DVal(m, &(cap1->cap_type))) * DHeapRest(m, &(cap1->cap_type)))
      which implies DTyped(m) && DReadUInt(m, &(cap1->cap_type)) && (DHeap(m)) */
      return (unsigned char)CNODE_DELETE_FAILURE;
    }
  }
  /*@ DTyped(DPayloadDeleted(m, destTask_Prio, func_capability)) && DWriteUInt(DPayloadDeleted(m, destTask_Prio, func_capability), &(pCSpace1->cnode.slots[func_capability].slot_type)) && (DHeap(DPayloadDeleted(m, destTask_Prio, func_capability)))
      which implies DTyped(DPayloadDeleted(m, destTask_Prio, func_capability)) && DWriteUInt(DPayloadDeleted(m, destTask_Prio, func_capability), &(pCSpace1->cnode.slots[func_capability].slot_type)) && (undef_data_at(&(pCSpace1->cnode.slots[func_capability].slot_type), unsigned int) *
      DHeapRest(DPayloadDeleted(m, destTask_Prio, func_capability), &(pCSpace1->cnode.slots[func_capability].slot_type))) */
  pCSpace1->cnode.slots[func_capability].slot_type = SLOT_NULL_CAP;
  /*@ DTyped(DPayloadDeleted(m, destTask_Prio, func_capability)) && DWriteUInt(DPayloadDeleted(m, destTask_Prio, func_capability), &(pCSpace1->cnode.slots[func_capability].slot_type)) && (data_at(&(pCSpace1->cnode.slots[func_capability].slot_type), unsigned int, 0) * DHeapRest(DPayloadDeleted(m, destTask_Prio, func_capability), &(pCSpace1->cnode.slots[func_capability].slot_type)))
      which implies DTyped(DPayloadDeleted(m, destTask_Prio, func_capability)) && DWriteUInt(DPayloadDeleted(m, destTask_Prio, func_capability), &(pCSpace1->cnode.slots[func_capability].slot_type)) && (DHeap(DWrite(DPayloadDeleted(m, destTask_Prio, func_capability), &(pCSpace1->cnode.slots[func_capability].slot_type), 0))) */
  /*@ (DWrite(DPayloadDeleted(m, destTask_Prio, func_capability), &(pCSpace1->cnode.slots[func_capability].slot_type), 0) == DDeleted(m, destTask_Prio, func_capability)) && (DHeap(DWrite(DPayloadDeleted(m, destTask_Prio, func_capability), &(pCSpace1->cnode.slots[func_capability].slot_type), 0)))
      which implies (DWrite(DPayloadDeleted(m, destTask_Prio, func_capability), &(pCSpace1->cnode.slots[func_capability].slot_type), 0) == DDeleted(m, destTask_Prio, func_capability)) && (DHeap(DDeleted(m, destTask_Prio, func_capability))) */
  return (unsigned char)CNODE_NONE_FAULT;
}

unsigned char user_cnode_delete(unsigned char destTask_Prio, unsigned char func_capType, unsigned int func_capability)
/*@ With (m : DMemory) (max_events : Z)
    Require max_events == DELETE_CONFIG_MAX_EVENTS && DTyped(m) && DUnionLayout && DUserSafe(m, max_events, destTask_Prio, func_capType, func_capability) && DHeap(m)
    Ensure exists m1,
      DUserResult(m, max_events, destTask_Prio, func_capType, func_capability, __return, m1) && DHeap(m1)
*/
{
  CSPACE *pCSpace;
  unsigned char i;
  unsigned char y;
  if (destTask_Prio >= OS_LOWEST_PRIO) { return (unsigned char)OS_PRIO_INVALID; }
  ENTER_CRITICAL;
  if (func_capType > CAP_TASK_TYPE) {
    EXIT_CRITICAL;
    return (unsigned char)EINVAL;
  }
  /*@ DUserSafe(m, max_events, destTask_Prio, func_capType, func_capability) &&
      destTask_Prio < 63 && func_capType <= 5 && DHeap(m) which implies
      DUserSafe(m, max_events, destTask_Prio, func_capType, func_capability) &&
      DCheckSafe(m, max_events, func_capability, func_capType, destTask_Prio) && DHeap(m) */
  func_capability = Check_Cap_Type(func_capability, func_capType, destTask_Prio) /*@ where m = m, max_events = max_events */;
  if (func_capability == SLOT_NUM) {
    EXIT_CRITICAL;
    return (unsigned char)EINVAL;
  }
  /*@ DTyped(m) && DReadPtr(m, &(OSTCBCur)) && DReadByte(m, DPrioAddress(m)) && (DHeap(m))
      which implies DTyped(m) && DReadPtr(m, &(OSTCBCur)) && DReadByte(m, DPrioAddress(m)) && (data_at(&(OSTCBCur), struct os_tcb *, DCurrent(m)) *
      data_at(DPrioAddress(m), unsigned char, DPrio(m)) * DHeapRest2(m, &(OSTCBCur), DPrioAddress(m))) */
  y = OSTCBCur->OSTCBPrio;
  /*@ DTyped(m) && DReadPtr(m, &(OSTCBCur)) && DReadByte(m, DPrioAddress(m)) && (data_at(&(OSTCBCur), struct os_tcb *, DCurrent(m)) *
      data_at(DPrioAddress(m), unsigned char, DPrio(m)) * DHeapRest2(m, &(OSTCBCur), DPrioAddress(m)))
      which implies DTyped(m) && DReadPtr(m, &(OSTCBCur)) && DReadByte(m, DPrioAddress(m)) && (DHeap(m)) */
  /*@ DTyped(m) && DReadPtr(m, &(OSCSpacePrioTbl[y])) && (DHeap(m))
      which implies DTyped(m) && DReadPtr(m, &(OSCSpacePrioTbl[y])) && (data_at(&(OSCSpacePrioTbl[y]), struct cspace *, DSpace(m, y)) * DHeapRest(m, &(OSCSpacePrioTbl[y]))) */
  pCSpace = OSCSpacePrioTbl[y];
  /*@ DTyped(m) && DReadPtr(m, &(OSCSpacePrioTbl[y])) && (data_at(&(OSCSpacePrioTbl[y]), struct cspace *, DSpace(m, y)) * DHeapRest(m, &(OSCSpacePrioTbl[y])))
      which implies DTyped(m) && DReadPtr(m, &(OSCSpacePrioTbl[y])) && (DHeap(m)) */

  if (pCSpace == (CSPACE *)NULL) {
    EXIT_CRITICAL;
    return (unsigned char)CNODE_DELETE_FAILURE;
  }
  /*@ DTyped(m) && DAuthFootprint(m, destTask_Prio) && &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right) == DRightAddress(m) && (DHeap(m))
      which implies DTyped(m) && DAuthFootprint(m, destTask_Prio) && &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right) == DRightAddress(m) && ((DRightBits(m) == 0 && data_at(&(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right), unsigned int, DVal(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right))) * DHeapRest(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right))) ||
      (DRightBits(m) != 0 && &(CapParent[destTask_Prio]) == DPrioAddress(m) &&
      data_at(&(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right), unsigned int, DVal(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right))) * data_at(&(OSTCBCur), struct os_tcb *, DCurrent(m)) * data_at(DPrioAddress(m), unsigned char, DPrio(m)) *
      DHeapRest3(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right), &(OSTCBCur), DPrioAddress(m))) ||
      (DRightBits(m) != 0 && &(CapParent[destTask_Prio]) != DPrioAddress(m) &&
      data_at(&(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right), unsigned int, DVal(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right))) * data_at(&(OSTCBCur), struct os_tcb *, DCurrent(m)) * data_at(DPrioAddress(m), unsigned char, DPrio(m)) * data_at(&(CapParent[destTask_Prio]), unsigned char, DVal(m, &(CapParent[destTask_Prio]))) *
      DHeapRest4(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right), &(OSTCBCur), DPrioAddress(m), &(CapParent[destTask_Prio])))) */
  if ((pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right & CNODE_DELETE_CAP) == 0U
      || (CapParent[destTask_Prio] != OSTCBCur->OSTCBPrio && destTask_Prio != OSTCBCur->OSTCBPrio)) {
    /*@ DTyped(m) && DAuthFootprint(m, destTask_Prio) && &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right) == DRightAddress(m) && (((DRightBits(m) == 0 && data_at(&(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right), unsigned int, DVal(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right))) * DHeapRest(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right))) ||
      (DRightBits(m) != 0 && &(CapParent[destTask_Prio]) == DPrioAddress(m) &&
      data_at(&(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right), unsigned int, DVal(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right))) * data_at(&(OSTCBCur), struct os_tcb *, DCurrent(m)) * data_at(DPrioAddress(m), unsigned char, DPrio(m)) *
      DHeapRest3(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right), &(OSTCBCur), DPrioAddress(m))) ||
      (DRightBits(m) != 0 && &(CapParent[destTask_Prio]) != DPrioAddress(m) &&
      data_at(&(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right), unsigned int, DVal(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right))) * data_at(&(OSTCBCur), struct os_tcb *, DCurrent(m)) * data_at(DPrioAddress(m), unsigned char, DPrio(m)) * data_at(&(CapParent[destTask_Prio]), unsigned char, DVal(m, &(CapParent[destTask_Prio]))) *
      DHeapRest4(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right), &(OSTCBCur), DPrioAddress(m), &(CapParent[destTask_Prio])))))
      which implies DTyped(m) && DAuthFootprint(m, destTask_Prio) && &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right) == DRightAddress(m) && (DHeap(m)) */
    EXIT_CRITICAL;
    return (unsigned char)USER_CAPABILITY_NONE;
  } else {
    /*@ DTyped(m) && DAuthFootprint(m, destTask_Prio) && &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right) == DRightAddress(m) && (((DRightBits(m) == 0 && data_at(&(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right), unsigned int, DVal(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right))) * DHeapRest(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right))) ||
      (DRightBits(m) != 0 && &(CapParent[destTask_Prio]) == DPrioAddress(m) &&
      data_at(&(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right), unsigned int, DVal(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right))) * data_at(&(OSTCBCur), struct os_tcb *, DCurrent(m)) * data_at(DPrioAddress(m), unsigned char, DPrio(m)) *
      DHeapRest3(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right), &(OSTCBCur), DPrioAddress(m))) ||
      (DRightBits(m) != 0 && &(CapParent[destTask_Prio]) != DPrioAddress(m) &&
      data_at(&(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right), unsigned int, DVal(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right))) * data_at(&(OSTCBCur), struct os_tcb *, DCurrent(m)) * data_at(DPrioAddress(m), unsigned char, DPrio(m)) * data_at(&(CapParent[destTask_Prio]), unsigned char, DVal(m, &(CapParent[destTask_Prio]))) *
      DHeapRest4(m, &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right), &(OSTCBCur), DPrioAddress(m), &(CapParent[destTask_Prio])))))
      which implies DTyped(m) && DAuthFootprint(m, destTask_Prio) && &(pCSpace->cnode.slots[SLOT_CNODE_CAP].capability.cap_content.category.category_right) == DRightAddress(m) && (DHeap(m)) */
    /*@ DUserSafe(m, max_events, destTask_Prio, func_capType, func_capability@pre) &&
        DCheckResult(m, max_events, func_capability@pre, func_capType, destTask_Prio, func_capability) &&
        destTask_Prio < 63 && func_capType <= 5 && func_capability != 255 &&
        DSpace(m, DPrio(m)) != 0 && DAuthorized(m, destTask_Prio) && DHeap(m) which implies
        DUserSafe(m, max_events, destTask_Prio, func_capType, func_capability@pre) &&
        DCheckResult(m, max_events, func_capability@pre, func_capType, destTask_Prio, func_capability) &&
        DAuthorized(m, destTask_Prio) && DCoreSafe(m, destTask_Prio, func_capability) && DHeap(m) */
    i = ucos_CNode_Delete(destTask_Prio, func_capability) /*@ where m = m */;
    if (i == CNODE_NONE_FAULT) {
      EXIT_CRITICAL;
      return (unsigned char)CNODE_DELETE_SUCCESS;
    } else {
      EXIT_CRITICAL;
      return (unsigned char)CNODE_DELETE_FAILURE;
    }
  }
}

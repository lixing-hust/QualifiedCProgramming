Require Import PIF_os_code_defs.
Require Import PIF_code_notations.
Require Import PIF_ev_aux_code.

Open Scope code_scope.

Definition OS_EVENT : type := 
  STRUCT os_event ­{ 
                    ⌞OSEventType @ Int8u;
                    OSEventGrp @ Int8u; 
                    OSEventCnt @ Int16u; 
                    OSEventPtr @ (Void ∗);
                    OSEventTbl @ (Tarray Int8u ∘OS_EVENT_TBL_SIZE);
                    OSEventListPtr @ STRUCT os_event ⋆;
                    OSPostEventGrp @ Int8u;
                    OSPostEventTbl @ (Tarray Int8u ∘OS_EVENT_TBL_SIZE)⌟
                   }­.

Definition OS_Q_FREEBLK : type :=
  STRUCT os_q_freeblk ­{
                        ⌞nextblk @ STRUCT os_q_freeblk ⋆ ; 
                        msgqueuetbl @ (Tarray (Void ∗) ∘OS_MAX_Q_SIZE)⌟
                       }­.


Definition OS_Q : type := 
    STRUCT os_q ­{
                  ⌞OSQPtr @ Void ∗;
                  OSQStart @ Void ∗ ∗;
                  OSQEnd @ Void ∗ ∗;
                  OSQIn @ Void ∗ ∗;
                  OSQOut @ Void ∗ ∗;
                  OSQSize @ Int16u ;
                  OSQEntries @ Int16u ;
                  qfreeblk @ OS_Q_FREEBLK ∗⌟
                 }­.

Definition OS_TCB : type := 
  STRUCT os_tcb ­{
                  ⌞OSTCBNext @ STRUCT os_tcb ⋆;
                  OSTCBPrev @ STRUCT os_tcb ⋆ ;
                  OSTCBEventPtr @ OS_EVENT ∗ ; 
                  OSTCBMsg @ Void ∗ ;
                  OSTCBDly @ Int16u ;
                  OSTCBStat @ Int16u ;
                  OSTCBPrio @ Int8u ;
                  OSTCBX @ Int8u ;
                  OSTCBY @ Int8u ; 
                  OSTCBBitX @ Int8u ;
                  OSTCBBitY @ Int8u ;
                  OSTCBflag @ Int8u ;
                  __OSTskEvLoc @ Int8u ;
                  __OSTskMuxPtr @ Tptr OS_EVENT; 
                  __OSTskSemPtr @ Tptr OS_EVENT;
                  __OSTskQPtr @ Tptr OS_EVENT⌟ 
                 }­.



Definition OS_STK : type := Int32.

Definition OS_STK_BLK : type := 
  STRUCT os_stk_blk ­{
                      ⌞nextblk @ Void ∗;
                      taskstk @ (Tarray OS_STK ∘TASK_STK_SIZE)⌟
                     }­.


Definition PlaceHolder:= &ₐ OSPlaceHolder′.


Definition gvarlist1 : decllist := 
             ⌞ 
              OSCtxSwCtr @ Int32u ;
              OSEventList @ OS_EVENT ∗ ;
              OSEventFreeList @ OS_EVENT ∗ ;
              OSEventTbl @ (Tarray OS_EVENT ∘OS_MAX_EVENTS);
              OSIntNesting @ Int8u;                                       
              OSIntExitY @ Int8u;
              OSPrioCur @ Int8u;
              OSPrioHighRdy @ Int8u;
              OSRdyGrp @ Int8u;
              OSRdyTbl @ (Tarray Int8u ∘OS_RDY_TBL_SIZE);
              OSRunning @ Int8u                                       
             ⌟.

Definition gvarlist2 :decllist := 
             ⌞ 
              OSTaskCtr @ Int8u;
              OSIdleCtr @ Int32u;
              OSTCBCur @ OS_TCB ∗;
              OSTCBFreeList @ OS_TCB ∗;
              OSTCBHighRdy @ OS_TCB ∗; 
              OSTCBList @ OS_TCB;                                       
              OSTCBPrioTbl @ (Tarray (OS_TCB ∗ ) ∘(OS_LOWEST_PRIO + 1)%Z );
              OSTCBTbl @ (Tarray OS_TCB ∘(OS_LOWEST_PRIO + 1));
              OSQFreeBlk @ OS_Q_FREEBLK ∗;
              OSQFreeBlkTbl @ (Tarray OS_Q_FREEBLK ∘OS_MAX_QS)
            ⌟.

Definition gvarlist3 :decllist := 
             ⌞
              OSQFreeList @ OS_Q ∗;
              OSQTbl @ (Tarray OS_Q ∘OS_MAX_QS);
              OSTime @ Int32u;
              OSMapTbl @ (Tarray Int8u 8);                                                   OSUnMapTbl @ (Tarray Int8u 256)
             ⌟.


Fixpoint plus_decl  (d1 d2 : decllist) {struct d1} :=
    match d1 with
     | dnil => d2
     | dcons x t d1' => dcons x t (plus_decl d1' d2)
    end.


Definition GlobalVariables := 
  plus_decl (plus_decl gvarlist1 gvarlist2) gvarlist3.

(************** new struct definition ***************************)

Definition sem_info_t : type := 
  STRUCT sem_info ­{ 
                        ⌞sem_type @ Int32;
                        sem_name @ (char_t ∗) ; 
                        sem_maxvalue @ Int32; 
                        sem_curvalue @ Int32;
                        sem_opencnt @ Int32;
                        sem_linked @ Int32;
                        tasks_blocked @ Int32;
                        pevent @ OS_EVENT ∗(* ; *)
                        (* del_flag @ Int32 *)
(*                         sem_cap @  (Tarray Int8u ∘(OS_MAX_TASKS - OS_N_SYS_TASKS)) *)
                      ⌟
                        }­.


Definition timespec_t : type := 
  STRUCT timespec ­{ 
                    ⌞
                    timeout @ Int16u
                  ⌟
                   }­.


Definition pthread_mutexattr_t : type := 
  STRUCT pthread_mutexattr ­{ 
                    ⌞is_initialized @ Int32;
                    process_shared @ Int32; 
                    prio_ceiling@ Int32; 
                    protocol @ Int32; 
                    recursive @ Int32; 
                    waitq_type @ Int32; 
                    cancel_safe @ Int32⌟
                   }­.



Definition pthread_mutex_info_t : type := 
  STRUCT pthread_mutex_info ­{ 
                        ⌞mutex_type @ Int32;
                        protocol @ Int32; 
                        prio_ceiling @ Int32; 
                        waitq_type @ Int32;
                        cancel_safe @ Int32;
                        mutex_owner @ pthread_t;
                        recursive_cnt @ Int32;
                        tasks_blocked @ Int32;
                        pevent @ OS_EVENT ∗(* ; *)
(*                         mutex_cap @  (Tarray Int8u ∘(OS_MAX_TASKS - OS_N_SYS_TASKS)) *)
                      ⌟
                        }­.

(* Definition Mq_Attr := Tarray mq_attr' ∘(OS_USER_MAX_EVENTS ÷ 3 ). *)

Definition mq_attr_t : type := 
  STRUCT mq_attr ­{ 
                        ⌞mq_waittype @ Int32;
                        mq_flags @ long; 
                        mq_maxmsg @ long;
                        mq_msgsize @ long;
                        mq_curmsgs @ long;
                        pevent @ OS_EVENT ∗
(*                         mq_cap @  (Tarray Int8u ∘(OS_MAX_TASKS - OS_N_SYS_TASKS)) *) (*cap*)
                      ⌟
                        }­.

Definition mq_info_t : type := 
    STRUCT mq_info ­{
                  ⌞
                  mq_waittype @ Int32; 
                  mq_flags @ Long; 
                  mq_maxmsg @ Long;
                  mq_msgsize @ Long;
                  mq_curmsgs @ Long;
                  task_blocked @ Int8u;
                  OSEventTbl @ (Tarray Int8u ∘OS_EVENT_TBL_SIZE) 
                  ⌟
                 }­.

Definition OS_Q_DATA : type := 
    STRUCT os_q_data ­{
                  ⌞
                  OSMsg @ Void ∗; 
                  OSNMsgs @ Int16u; 
                  OSQSize @ Int16u;
                  OSEventTbl @ (Tarray Int8u ∘OS_EVENT_TBL_SIZE) ;
                  OSEventGrp @ Int8u
                  ⌟
                 }­.

Definition gvarlist4 :decllist := 
             ⌞
              Sem_info @ (Tarray sem_info_t ∘(OS_USER_MAX_EVENTS/3)); 
              Pthread_Mutex @ (Tarray pthread_mutex_info_t ∘(OS_USER_MAX_EVENTS/3));
              Mq_Attr @ (Tarray mq_attr_t ∘(OS_USER_MAX_EVENTS/3));
              Domain2Index  @ (Tarray Int8s ∘DOMAIN_SIZE);
              ksCurDomain @ dom_t
             ⌟.

Definition gvarlist5 : decllist :=
  ⌞
    GJB_pos_list @ dom_t 
    ⌟.  

Close Scope code_scope.

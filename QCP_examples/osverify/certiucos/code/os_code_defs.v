Require Export include_frm.

(* identifiers *)
Definition OSRunning : ident := 0%Z.
Definition OSRdyGrp : ident := 1%Z.
Definition OSUnMapTbl: ident := 2%Z.
Definition OSRdyTbl: ident := 3%Z.
Definition OSPrioHighRdy: ident := 4%Z.
Definition OSPrioCur: ident := 5%Z.
Definition OSStartHighRdy: ident := 6%Z.
Definition OSIntNesting: ident := 7%Z.
Definition OSIntExitY: ident := 8%Z.
Definition OSCtxSwCtr: ident := 9%Z.
Definition OSInitHookBegin: ident := 10%Z.
Definition OSInitHookEnd: ident := 11%Z.
Definition OS_InitMisc := 12%Z.
Definition OS_InitRdyList := 13%Z.
Definition OS_InitSTKList := 14%Z.
Definition OS_InitTCBList := 15%Z.
Definition OS_InitEventList := 16%Z.
Definition OS_QInit := 17%Z.
Definition OS_SemInit := 18%Z.
Definition OS_InitTaskIdle := 19%Z.
Definition OS_TCBInit := 20%Z.
Definition OSStatRdy: ident := 21%Z.
Definition OSMapTbl: ident := 22%Z.
Definition OSEventGrp: ident := 23%Z.
Definition OSEventCnt: ident := 24%Z.
Definition OSEventTbl: ident := 25%Z.

Definition OSPostEventGrp :ident := 781%Z.
Definition OSPostEventTbl :ident := 782%Z.

Definition OSEventListPtr: ident := 36%Z.
Definition OSTCBEventPtr: ident := 26%Z.
Definition OSEventType: ident := 27%Z.
Definition OSEventPtr: ident := 28%Z.
Definition OSEventFreeList: ident := 29%Z.
Definition OS_EventWaitListInit := 30%Z.
Definition OS_EventTO := 31%Z.
Definition OS_EventTaskRdy := 32%Z.
Definition OS_EventTaskWait := 33%Z.
Definition OSQPtr: ident := 34%Z.
Definition OSEventList: ident := 35%Z.
Definition OSIntToyCount: ident := 500%Z.
Definition OSQStart: ident := 37%Z.
Definition OSQEnd: ident := 38%Z.
Definition OSQIn: ident := 39%Z.
Definition OSQOut: ident := 40%Z.
Definition OSQSize: ident := 41%Z.
Definition OSQEntries: ident := 42%Z.
Definition OSQFreeBlk: ident := 43%Z.
Definition OSQFreeBlkTbl: ident := 44%Z.
Definition OSQFreeList: ident := 45%Z.
Definition OSQTbl: ident := 46%Z.
Definition qfreeblk: ident := 47%Z.
Definition nextblk: ident := 48%Z.
Definition OSTCBDly: ident := 51%Z.
Definition OSTCBMsg: ident := 52%Z.
Definition OSTCBStat: ident := 53%Z.
Definition OSTCBTbl: ident := 54%Z.
Definition OSTCBNext: ident := 55%Z.
Definition OSTCBPrev: ident := 56%Z.
Definition OSTCBFreeList: ident := 57%Z.
Definition OSTCBPrioTbl: ident := 58%Z.
(*
Definition OSTCBHighRdy: ident := 59%Z.
*)
Definition OSTCBList: ident := 61%Z.
Definition OSTCBPrio: ident := 62%Z.
Definition OSTCBBitY: ident := 63%Z.
Definition OSTCBY: ident := 64%Z.
Definition OSTCBX: ident := 65%Z.
Definition OSTCBBitX: ident := 66%Z.
Definition OSTCBflag :ident :=300%Z.
 Definition OS_Sched := 67%Z.
Definition OSLockNesting: ident := 68%Z.
Definition OSTaskCtr: ident := 69%Z.
Definition OSTaskCreate := 70%Z.
Definition OS_TaskIdle := 71%Z.
Definition OSSTKTbl: ident := 72%Z.
Definition OSSTKFreeList: ident := 73%Z.
Definition OSTimeTick := 74%Z.
Definition OSTime: ident := 75%Z.
Definition OSIntExit := 76%Z.
Definition OSIdleCtr: ident := 77%Z.
Definition OSIdleCtrRun: ident := 78%Z.
Definition OSIdleCtrMax: ident := 79%Z.
Definition OSPlaceHolder: ident := 80%Z.
(*Definition OS_SemPtrAdd := 80%Z.
Definition OS_SemPtrRemove := 81%Z.
Definition OS_SemPtrSearch := 82%Z.*)
(*Definition OS_EventPtrAdd := 83%Z.*)
Definition OS_EventRemove := 84%Z.
Definition OS_EventRemoveDel := 85%Z. 
(* Definition OS_EventSearch := 85%Z. *)
Definition os_event: ident := 86%Z.
Definition os_q: ident := 87%Z.
Definition os_q_freeblk: ident := 88%Z.
Definition msgqueuetbl: ident := 89%Z.
Definition os_tcb: ident := 90%Z.
Definition OS_IsSomeMutexOwner := 933%Z.
Definition os_tcb_flag: ident := 190%Z.

Definition os_stk_blk: ident := 91%Z.
Definition taskstk: ident := 92%Z.
Definition os_q_ptr: ident := 93%Z.
Definition os_sem_ptr: ident := 94%Z.
Definition qeventptr: ident := 95%Z.
Definition next: ident := 96%Z.
Definition x : ident := 97%Z.
Definition y : ident := 98%Z.
Definition ptcb : ident := 99%Z.
Definition pevent : ident := 100%Z.
(*Definition msg : ident := 101%Z.*)
Definition message : ident := 101%Z.
Definition msk : ident := 102%Z.
Definition bitx : ident := 103%Z.
Definition bity : ident := 104%Z.
Definition prio : ident := 105%Z.
Definition ptbl : ident := 106%Z.
Definition i : ident := 107%Z.
Definition pevent1 : ident := 108%Z.
Definition pevent2 : ident := 109%Z.
Definition prdytbl : ident := 110%Z.
Definition pstk1 : ident := 111%Z.
Definition pstk2 : ident := 112%Z.
Definition ptcb1 : ident := 113%Z.
Definition ptcb2 : ident := 114%Z.
Definition task : ident := 115%Z.
Definition pdata : ident := 116%Z.
Definition p : ident := 117%Z.
Definition p1 : ident := 118%Z.
Definition p2 : ident := 119%Z.
Definition pq : ident := 120%Z.
Definition pqblk : ident := 121%Z.
Definition start : ident := 122%Z.
Definition err : ident := 123%Z.
Definition tasks_waiting : ident := 124%Z.
Definition tasks_post_waiting : ident := 135%Z. 
Definition timeout : ident := 125%Z.
Definition size : ident := 126%Z.
Definition cnt : ident := 127%Z.
Definition self : ident := 128%Z.
Definition ticks : ident := 129%Z.
Definition legal : ident := 130%Z.
Definition pqptr : ident := 131%Z.
Definition p3 : ident := 132%Z.
Definition pip : ident := 133%Z.
Definition mprio : ident := 134%Z.
Definition isrdy : ident := 140%Z.
Definition tcb_flag: ident := 500%Z.
(* constants *)
  (* in file 'os_cfg.h' *)
(* Definition OS_MAX_EVENTS := 10%Z. *)
Definition OS_MAX_QS := 10%Z.
Definition OS_MAX_SEM := 10%Z.
Definition OS_MAX_Q_SIZE := 20%Z.
Definition OS_MAX_TASKS := 30%Z.
Definition OS_LOWEST_PRIO := 63%Z.
Definition TASK_STK_SIZE := 1024%Z.

  (* in file 'ucos_ii.h' *)
Definition OS_PRIO_SELF := 255%Z.
Definition OS_N_SYS_TASKS := 2%Z.
Definition OS_IDLE_PRIO := OS_LOWEST_PRIO.
Definition OS_EVENT_TBL_SIZE := 8%Z. (* OS_LOWEST_PRIO / 8 + 1*)
Definition OS_RDY_TBL_SIZE := 8%Z. (* OS_LOWEST_PRIO / 8 + 1 *)

Definition OS_STAT_RDY := 0%Z.
Definition OS_STAT_SEM := 1%Z.
Definition OS_STAT_MBOX := 2%Z.
Definition OS_STAT_Q := 4%Z.
Definition OS_STAT_SUSPEND := 8%Z.
Definition OS_STAT_MUTEX := 16%Z.
Definition OS_STAT_PORT := 256%Z.
Definition OS_STAT_FLAG := 32%Z.
Definition OS_STAT_POSTQ := 512%Z.
Definition OS_STAT_ILLEGAL := 64%Z.

Definition OS_EVENT_TYPE_UNUSED := 0%Z.
Definition OS_EVENT_TYPE_MBOX := 1%Z.
Definition OS_EVENT_TYPE_Q := 2%Z.
Definition OS_EVENT_TYPE_SEM := 3%Z.
Definition OS_EVENT_TYPE_MUTEX := 4%Z.

Definition OS_NO_ERR := 0%Z.
Definition OS_ERR_EVENT_TYPE := 1%Z.
Definition OS_ERR_PEND_ISR := 2%Z.
Definition OS_ERR_POST_NULL_PTR :=3%Z.
Definition OS_ERR_PEVENT_NULL := 4%Z.
Definition OS_ERR_TASK_WAITING := 8%Z.
Definition OS_TIMEOUT := 10%Z.
Definition OS_Q_FULL := 30%Z.
Definition OS_STAT_ERR := 31%Z.
Definition OS_ERR_NOT_MUTEX_OWNER := 120%Z.
Definition OS_ERR_MUTEX_PRIO := 121%Z.
Definition OS_ERR_PEVENT_NO_EX := 122%Z.
Definition OS_ERR_IDLE := 123%Z.
Definition OS_ERR_STAT := 124%Z.
Definition OS_ERR_OWN := 125%Z.
Definition OS_ERR_MUTEXPR_NOT_HOLDER := 126%Z.
Definition OS_ERR_ORIGINAL_NOT_HOLDER := 127%Z.
Definition OS_ERR_MUTEX_WL_HIGHEST_PRIO := 128%Z.
Definition OS_PRIO_EXIST := 40%Z.
Definition OS_PRIO_ERR := 41%Z.
Definition OS_PRIO_INVALID := 42%Z.
Definition OS_ERR_NEST:= 1000%Z.
Definition OS_ERR_MUTEX_DEADLOCK := 1001%Z.
Definition OS_ERR_MUTEX_IDLE := 1002%Z.

(* add by CNU for mutexes *)
Definition OS_ERR_CREATE_ISR := 141%Z.
Definition OS_ERR_POST_ISR: ident := 5%Z.
(* end add by CNU for mutexes *) 

Definition OS_SEM_OVF := 50%Z.

Definition OS_TASK_DEL_ERR := 60%Z.
Definition OS_TASK_DEL_IDLE := 61%Z.
Definition OS_TASK_DEL_SOME_MUTEX_OWNER := 62%Z.
Definition OS_TASK_DEL_HAS_NO_NEXT := 64%Z. 
Definition OS_TASK_DEL_ISR := 63%Z.

(* 2022/04/29 *)
Definition OS_TASK_SUSPEND_IDLE := 91%Z.
(* 2022/04/30 *)
Definition OS_TASK_SUSPEND_ERR := 92%Z.
(* 2022/05/01 *)
Definition OS_TASK_SUSPEND_SOME_MUTEX_OWNER := 93%Z.
(* 2022/05/06 *)
Definition OS_TASK_SUSPEND_PRIO := 94%Z.
Definition OS_TASK_RESUME_PRIO := 100%Z.
Definition OS_TASK_NOT_SUSPENDED := 101%Z.
Definition OS_TASK_DELAY_ZERO := 102%Z.

Definition OS_NO_MORE_TCB := 70%Z.
Definition OS_ERR_DEL_ISR := 140%Z.

Definition OS_VERSION := 252%Z.

Definition OS_MUTEX_KEEP_LOWER_8 := 255%Z.
Definition OS_MUTEX_KEEP_UPPER_8 := 65280%Z.
Definition OS_MUTEX_AVAILABLE := 255%Z.


Definition OS_PrioChange := 400%Z.
Definition OSInit := 253%Z.
Definition OSStart := 254%Z.
(*Definition OSIntEnter := 255%Z.*)
Definition OSVersion := 256%Z.
Definition OSQAccept := 257%Z.
Definition OSQCreate := 258%Z.
Definition OSQDel := 259%Z.
Definition OSQPend := 260%Z.
Definition OSQGetMsg := 261%Z.
Definition OSQPost := 262%Z.
Definition OSSemAccept := 263%Z.
Definition OSSemCreate := 264%Z.
Definition OSSemDel := 265%Z.
Definition OSSemPend := 266%Z.
Definition OSTaskDel := 267%Z.
Definition OSTimeDly := 268%Z.
Definition OSTimeGet := 269%Z.
Definition OSSemPost := 270%Z.
Definition OSSemPostBin := 285%Z.
Definition OSMboxCreate := 271%Z.
Definition OSMboxDel := 272%Z.
Definition OSMboxPend := 273%Z.
Definition OSMboxPost := 274%Z.
Definition OSMboxAccept := 275%Z.
Definition OSMutexCreate := 276%Z.
Definition OSMutexDel := 277%Z.
Definition OSMutexPend := 278%Z.
Definition OSMutexPost := 279%Z.
Definition OSMutexAccept := 280%Z.
Definition OSTickISR := 4.
(*Definition OSToyISR := 1.*)
Definition OSTaskSuspend := 281%Z.
Definition OSTaskResume := 282%Z.
(* mailbox definitions *)

Definition SOME_P_NOT_LEGAL_ERR     := 1312%Z.

Definition MBOX_DEL_NULL_ERR        := OS_ERR_PEVENT_NULL.
Definition MBOX_DEL_P_NOT_LEGAL_ERR := SOME_P_NOT_LEGAL_ERR.
Definition MBOX_DEL_WRONG_TYPE_ERR  := OS_ERR_EVENT_TYPE.
Definition MBOX_DEL_TASK_WAITING_ERR := OS_ERR_TASK_WAITING.
Definition MBOX_DEL_SUCC       := OS_NO_ERR.

Definition MBOX_POST_NULL_ERR := OS_ERR_PEVENT_NULL.
Definition MBOX_POST_MSG_NULL_ERR := OS_ERR_POST_NULL_PTR.
Definition MBOX_POST_P_NOT_LEGAL_ERR := SOME_P_NOT_LEGAL_ERR.
Definition MBOX_POST_WRONG_TYPE_ERR := OS_ERR_EVENT_TYPE.
Definition MBOX_POST_TASK_WT_ERR := OS_ERR_TASK_WAITING.
Definition MBOX_POST_FULL_ERR := OS_Q_FULL.
Definition MBOX_POST_SUCC := OS_NO_ERR.

Definition MBOX_PEND_NULL_ERR := OS_ERR_PEVENT_NULL.
Definition MBOX_PEND_P_NOT_LEGAL_ERR := SOME_P_NOT_LEGAL_ERR.
Definition MBOX_PEND_WRONG_TYPE_ERR := OS_ERR_EVENT_TYPE.
Definition MBOX_PEND_FROM_IDLE_ERR := 1313%Z.
Definition MBOX_PEND_NOT_READY_ERR := 1314%Z.
Definition MBOX_PEND_TIMEOUT_ERR := OS_TIMEOUT.
Definition MBOX_PEND_SUCC := OS_NO_ERR.



(* add by CNU *)

(******************errno******************)

Definition errno : ident := 286%Z. (*这是一个全局变量*)

Definition EMFILE := 24%Z. 
Definition EINVAL := 22%Z.
Definition EAGAIN  := 11%Z.
Definition ENOSPC  := 28%Z.
Definition EINTR := 4%Z.
Definition ETIMEDOUT:= 116%Z.
Definition EBUSY := 16%Z.
Definition EDEADLK:= 45%Z.
Definition EPERM:= 1%Z.
(* Definition EINVAL := 30%Z. *)
(** 源代码中EINVAL有22和30两种宏定义 ，在cfg/ucos_ii.h中为30，在errno.h中为22**)
Definition EBADF := 10%Z.
Definition ENOENT := 47%Z.
Definition ECALLEDINISR := 101%Z.
(* Definition EAGAIN := 6%Z. *) (** 源代码中有两种宏定义 *)
(* Definition EINTR := 29%Z. *) (** 源代码中有两种宏定义 *)
Definition ETIMEOUT := 78%Z.
Definition EMSGSIZE := 37%Z.

(******************end errno******************)

(*** for UserAddrCheck ***) 
Section UserSpace. 
  Parameter userAddrStart : addrval. 
  Parameter userAddrEnd : addrval.  
End UserSpace. 

Parameter vhold_addr : addrval.

(**************************** GJB events ***************************) 

(*********************macros********************)
Definition CORENUM := 8%Z.

(* Definition OS_MAX_EVENTS := 36%Z.  *)
Parameter OS_MAX_EVENTS : Z.
Parameter OS_MAX_EVENTS_range : Z.le (Z.add (Z.mul CORENUM 2%Z) 3%Z) OS_MAX_EVENTS /\ Z.le OS_MAX_EVENTS 255%Z.

Definition OS_USER_MAX_EVENTS :=(OS_MAX_EVENTS-CORENUM*2)%Z.
(* Definition OS_USER_MAX_EVENTS := 20%Z. *)
Definition SEM_VALUE_MAX := 65535%Z.
Definition SEM_BINARY := 1%Z. 
Definition SEM_COUNTING := 2%Z.
Definition OS_DEL_NO_PEND := 0%Z.
Definition OS_DEL_ALWAYS := 1%Z.

Definition PTHREAD_PRIO_INHERIT := 1%Z.
(* Definition OS_MAX_TASKS:= 63%Z. *)  (* Definition OS_MAX_TASKS := 30%Z. *) 
(* Definition OS_N_SYS_TASKS := 2%Z.  *)

Definition PTHREAD_MUTEX_ERRORCHECK := 1%Z.
Definition PTHREAD_CANCEL_UNSAFE : ident := 1%Z.
Definition PTHREAD_CANCEL_SAFE := 2%Z.
Definition PTHREAD_MUTEX_DEFAULT := 3%Z.
Definition PTHREAD_MUTEX_RECURSIVE := 2%Z.
Definition PTHREAD_MUTEX_RECURSIVE_MAX := 64%Z.
Definition PTHREAD_MUTEX_NORMAL := 0%Z.

Definition PTHREAD_WAITQ_PRIO := 1%Z. 

Definition O_NONBLOCK := 1%Z.

(******************** structures for events ***********************)

Definition sem_info : ident := 700%Z. 
Definition sem_type : ident := 701%Z. 
Definition sem_name : ident := 702%Z. 
Definition sem_maxvalue : ident := 703%Z. 
Definition sem_curvalue : ident := 704%Z. 
Definition sem_opencnt : ident := 705%Z. 
Definition sem_linked : ident := 706%Z. 
Definition tasks_blocked : ident := 707%Z. 
Definition sem_cap : ident := 708%Z.
Definition Sem_info : ident := 709%Z.

Definition timespec: ident := 308%Z.

Definition pthread_mutex_info : ident := 710%Z.
Definition mutex_type : ident := 711%Z. (*由type改成mutex_type*)
Definition protocol : ident := 712%Z.
Definition prio_ceiling : ident := 713%Z.
Definition waitq_type : ident := 714%Z.
Definition cancel_safe : ident := 715%Z.
Definition mutex_owner : ident := 716%Z. (*由onwer改成mutex_owner*)
Definition recursive_cnt : ident := 717%Z.
Definition mutex_cap : ident := 718%Z.
Definition Pthread_Mutex : ident := 719%Z.

Definition is_initialized: ident := 621%Z.
Definition process_shared: ident := 622%Z.
Definition recursive: ident := 625%Z.

Definition pthread_mutexattr : ident := 620%Z.

Definition mq_attr : ident := 720%Z.
Definition mq_waittype : ident := 721%Z.
Definition mq_flags : ident := 722%Z.
Definition mq_maxmsg : ident := 723%Z.
Definition mq_msgsize : ident := 724%Z.
Definition mq_curmsgs : ident := 727%Z.
Definition mq_cap : ident := 725%Z.
Definition Mq_Attr : ident := 726%Z.


(************ IDs for interface functions (events) *************)

Definition sem_trywait := 282%Z.
Definition sem_init := 288%Z.
Definition sem_init_bin := 295%Z.
Definition sem_destroy := 296%Z.
Definition sem_wait := 297%Z.
Definition sem_timedwait := 298%Z.
Definition sem_signal := 299%Z. 
Definition sem_flush := 300%Z.
Definition sem_getvalue := 301%Z.

Definition pthread_mutexattr_init := 602%Z.
Definition pthread_mutexattr_destroy:= 603%Z.
Definition pthread_mutexattr_settype:= 604%Z.
Definition pthread_mutexattr_gettype:= 605%Z.
Definition pthread_mutexattr_setprioceiling:= 606%Z.
Definition pthread_mutexattr_getprioceiling:= 607%Z.
Definition pthread_mutex_trylock:= 608%Z.
Definition pthread_mutex_init:= 609%Z.
Definition pthread_mutex_destroy:= 610%Z.
Definition pthread_mutex_lock:= 611%Z.
Definition pthread_mutex_timedlock:= 612%Z.
Definition pthread_mutex_unlock:= 613%Z.

Definition mq_delete := 675%Z.
Definition mq_receive := 676%Z.
Definition mq_timedreceive := 682%Z.
Definition mq_create := 771%Z.
Definition mq_send := 775%Z.
Definition mq_getinfo := 776%Z.

Definition OSQTimedPost := 818%Z.
(* Definition OSQPost := 819%Z.  *)
Definition OSQQuery := 824%Z.

Definition OS_EventTaskPostRdy := 784%Z.
Definition OS_EventTaskPostWait := 785%Z.
Definition OS_EventPostTO := 786%Z.
Definition UserAddrCheck := 287%Z.
Definition UserAddrCheckCrit := 291%Z. 
Definition OS_EventTaskPostRdyDel := 788%Z. 

Definition getFreePos := 290%Z.
Definition memcpy := 681%Z.

(* vars (sem) *)
Definition sem : ident := 283%Z. 
Definition pos : ident := 284%Z. 

Definition value : ident := 289%Z. 

Definition abs_timeout : ident := 293%Z. (*sem_timedwait中使用，参数*)
(*abs_timeout结构体中的timeout不知道需不需要重新定义*)
Definition sval : ident := 294%Z. (*sem_getvalue的参数*) 

(* vars (mutex) *)
Definition addre: ident := 628%Z.
Definition attr: ident := 629%Z.
Definition prioceiling: ident := 631%Z.
Definition mutex: ident := 632%Z.
Definition z: ident := 639%Z.
Definition ret: ident := 642%Z.
Definition attrEntity: ident := 643%Z.

(* vars (queue) *)
Definition mqdes : ident := 674%Z.

Definition msg_ptr : ident := 677%Z.
Definition msg_len : ident := 678%Z.
Definition pmsgprio : ident := 679%Z.
Definition msg_l : ident := 680%Z.

Definition mq_blockflag: ident  := 777%Z.
Definition max_msgs: ident  := 778%Z.
Definition msg_size: ident  := 779%Z.
Definition Val_uacheck: ident  := 786%Z.  (* UserAddrCheck函数 返回值*)
Definition Val_sizeof: ident  := 787%Z.    (* sizeof(Int8u)函数 返回值*)

Definition mq_info: ident  := 808%Z.
Definition task_blocked: ident  := 809%Z.

Definition msgprio: ident  := 813%Z.
Definition O_NONBLOCKL: ident  := 817%Z. 

Definition os_q_data: ident := 820%Z.
Definition OSMsg: ident := 821%Z.
Definition OSNMsgs: ident := 822%Z.
Definition pdest: ident := 823%Z.
Definition sizeof: ident  := 826%Z.
Definition Val_osqquery: ident  :=827%Z.

(** internal funcs **)
Definition tp : ident := 672%Z. (*函数参数由type改成tp*)
Definition addr : ident := 670%Z.

(** ghost locs **)
Definition __EvLoc_normal : Z := 1. 
Definition __EvLoc_ecbcre1 : Z := 2.
Definition __EvLoc_ecbcre2 : Z := 3.
Definition __EvLoc_ecbdel : Z := 4. 

(** ghost vars (fields) **) 
Definition __OSTskEvLoc : ident := 788%Z.
Definition __OSTskMuxPtr : ident := 796%Z. 
Definition __OSTskSemPtr : ident := 797%Z.
Definition __OSTskQPtr : ident := 798%Z. 
Definition tcb_cap : ident := 799%Z.

(**************************** MPAX ***************************) 
(* vars *)

Definition MPAXSHIPARTIONSTKCUR := 7%Z.
Definition MPAXSHIPARTIONCUR := 6%Z.
Definition MPAXSHIPARTIONALL := 5%Z.
Definition MPAXSHAREDAREA := 4%Z.
Definition MPAXALLAREA := 3%Z.

(************ IDs for interface functions (MPAX) *************)

(* vars (mpax)*)
Definition index : ident := 3039%Z.
Definition mpaxl : ident := 3040%Z.
Definition mpaxh : ident := 3041%Z.
Definition ses_mpaxl : ident := 3042%Z.
Definition ses_mpaxh : ident := 3043%Z.
Definition sms_mpaxl : ident := 3044%Z.
Definition sms_mpaxh : ident := 3045%Z.
Definition paddress : ident := 3046%Z.
Definition vaddress : ident := 3047%Z.
Definition segSize : ident := 3048%Z.

Definition initDefaultMPAX : ident := 14000%Z.
Definition initMPAX : ident := 14001%Z.
Definition switchDomain : ident := 14002%Z.
Definition switchDomain' : ident := 14003%Z.

(****************** definitions about partitions *****************************)
Definition PTHREAD_STACK_MIN := 4096%Z.
Definition PARTITION_ENABLE := 0%Z.
Definition MEM_VIOLATION := 254%Z.
Definition PARTITION_NUM := 8%Z.
Definition DOMAIN_SIZE := PARTITION_NUM.

Definition Core_partition_num : ident := 2000%Z.
Definition Domain2Index : ident := 752%Z.

Definition DeviceIO_CONF : ident := 2001%Z. 
Definition deviceId : ident := 2002%Z. 
Definition DOMAIN_CONF : ident := 2003%Z.

Definition dschedule_conf : ident := 2004%Z. 
Definition CPU_CONF : ident := 2005%Z.
Definition AREA_CONF : ident := 2006%Z.
Definition CHANNEL_CONF : ident := 2007%Z. 
Definition PORT_CONF : ident := 2008%Z. 
Definition UCOS_CONF : ident := 2009%Z.
Definition startAddr : ident := 2010%Z. 
Definition TaskEn : ident := 2011%Z.
Definition Cap_CONF : ident := 2012%Z.
Definition PartitionEn : ident := 2013%Z.
Definition InterCommEn : ident := 2014%Z.
Definition IntraCommSemEn : ident := 2015%Z.
Definition IntraCommMutexEn : ident := 2016%Z.
Definition IntraCommQueueEn : ident := 2017%Z.

(* Definition domain : ident := 2018%Z. *)
Definition coreId : ident := 2019%Z.
Definition ID : ident := 2020%Z.
Definition binAddress : ident := 2021%Z.
Definition RootTaskPrio : ident := 2022%Z.
(* Definition OSPartitionPeriod : ident := 2023%Z. *)
(* Definition pAddress : ident := 2024%Z.  *)
(* Definition vAddress : ident := 2025%Z. *)
(* Definition len : ident := 2026%Z. *)
Definition domaincf_size : ident := 2027%Z.
(* Definition status : ident := 2028%Z. *)
Definition portRdyGrp : ident := 2029%Z.
Definition DeviceNum : ident := 2030%Z. 
Definition portRdyTbl : ident := 2031%Z. 
Definition CapEnTbl : ident := 2032%Z.
Definition DeviceioTbl : ident := 2033%Z.

Definition areat_pAddress : ident := 2034%Z.
Definition areat_vAddress : ident := 2035%Z.
Definition areat_size : ident := 2036%Z.
Definition AREA : ident := 2037%Z.

Definition coreType : ident := 2038%Z.
Definition channelType : ident := 2039%Z.
Definition srcportID : ident := 2040%Z.
Definition dstGrp : ident := 2041%Z.
Definition dstTbl : ident := 2042%Z.
Definition CHANNEL_NUMS := 32%Z.

(* new add channel_conf_t struct*)
(* Definition direction : ident := 2043%Z. *)
(* Definition partitionID : ident := 2044%Z. *)
(* Definition channelID : ident := 2045%Z. *)
Definition channeltype : ident := 2046%Z.
Definition PORT_NUMS := 64%Z.

Definition dslength : ident := 2047%Z.

Definition core : ident := 2048%Z.
Definition domainRdy : ident := 2049%Z.
Definition cpu_ksDomScheduleLength : ident := 2050%Z.
Definition ksDomainLength : ident := 2051%Z.
Definition cpu_ksDomSchedule : ident := 2052%Z.
Definition cpu_ksDomains : ident := 2053%Z.

Definition magicf : ident := 2054%Z. 
Definition fileVersion : ident := 2055%Z.
Definition coreNums : ident := 2056%Z.
Definition noPartitions : ident := 2057%Z.
Definition noCommChannels : ident := 2058%Z.
Definition noPorts : ident := 2059%Z.
Definition IntrDomainMux : ident := 2060%Z.
Definition allArea : ident := 2061%Z. 
Definition cpus : ident := 2062%Z.
Definition channelTbl : ident := 2063%Z.
(* Definition  ucosportRdyGrp : ident := 2095%Z. *)
(* Definition  ucosportRdyTbl : ident := 2096%Z. *)
Definition portTbl : ident := 2064%Z.
Definition magicl : ident := 2065%Z.

Definition dvsize : ident := 2066%Z.
Definition dom_ID : ident := 2067%Z.
Definition dom_len : ident := 2068%Z.
Definition ch_ID : ident := 2069%Z.
Definition port_ID : ident := 2070%Z.
Definition ds_domain : ident := 2071%Z.

Definition IntPartitionMuxInit : ident := 2201%Z.
Definition ucoscfg : ident := 2202%Z.
Definition IntPartitionMux : ident := 2203%Z.
Definition USER_INT_MAX_N := 11%Z.
Definition BOOT_DATA_ADDRESS := (0x80000000%positive, Int.zero).

Definition ksDomSchedule : ident := 3201%Z.
(* Definition ksDomains : ident := 3202%Z. *)
Definition ksDomScheduleLength :ident := 3203%Z.
(* Definition ksCurDomain : ident := 3204%Z. *)
Definition ksLastDomain : ident := 3205%Z.
Definition ksDomainTime : ident := 3206%Z.
Definition ksDomScheduleIdx : ident := 3207%Z.
Definition isChangePartion : ident := 3208%Z.
Definition nextDomain : ident := 3209%Z.
Definition dschedule : ident := 3210%Z.
Definition dscd_domain : ident := 3211%Z.
Definition dscd_length : ident := 3212%Z.
Definition DSCHEDULE_SIZE := 10%Z.

(* Definition coreNum : ident := 3212%Z. *)
Definition isSame : ident := 3213%Z.
Definition Port_num_cur : ident := 3214%Z.
Definition OSAll_Partition_Area : ident := 3215%Z.
Definition partitionID2Domain : ident := 3216%Z.
Definition sysEndian : ident := 3217%Z.
Definition confEndian : ident := 3218%Z.
Definition base : ident := 3219%Z.
Definition littl_endian : ident := 3220%Z.

Definition is_bigEndian : ident := 3221%Z.
Definition InitDNUM: ident := 3222%Z.
Definition initConf: ident := 3223%Z.

Definition DTdomain : ident := 3224%Z.
Definition dom_t_ID : ident := 3225%Z.
Definition dom_t_OSPartitionPeriod : ident := 3226%Z.
Definition dom_t_pAddress : ident := 3227%Z.
Definition dom_t_vAddress : ident := 3228%Z.
Definition dom_t_len : ident := 3229%Z.
Definition dom_t_size : ident := 3230%Z.
Definition dom_t_status : ident := 3231%Z.
(* Definition domainIntStatusTbl : ident := 3232%Z. *)
Definition DOMAIN  : ident := 3233%Z.

Definition isCoreBoot : ident := 3234%Z.
Definition systemStck : ident := 3235%Z.
Definition OSSystemSP : ident := 3236%Z.
Definition SYS_STK_SIZE := 512%Z.

Definition partitionSysInit : ident :=3237%Z.
Definition getPartitionID : ident :=3238%Z.
Definition ksdid : ident :=3239%Z.
Definition ksdid1 : ident :=3240%Z.

Definition a:ident :=3241%Z.
Definition b:ident :=3242%Z.
Definition j : ident := 3243%Z.
Definition uconf : ident := 3244%Z.

Definition RootTaskStk : ident:= 3248%Z.

Definition temp_dom:ident := 4001%Z.
Definition temp_num:ident := 4002%Z.

(* Auxiliary variables *)
Definition to1 : ident :=  4003%Z.
Definition to2 : ident :=  4004%Z.
Definition to3 : ident :=  4005%Z.
Definition to4: ident :=   4006%Z.
Definition to5 : ident :=  4007%Z.
Definition to6 : ident :=  4008%Z.
Definition to7 : ident :=  4009%Z.
Definition to8 : ident :=  4010%Z.
Definition tox1 : ident := 4011%Z.
Definition tox2 : ident := 4012%Z.
Definition tox3 : ident := 4013%Z.
Definition tox4 : ident := 4014%Z.

(* port_attr_t *)
Definition portat_enable         : ident := 4015%Z.
Definition portat_partitionID    : ident := 4016%Z.
Definition portat_domain         : ident := 4017%Z.
Definition portat_direction      : ident := 4018%Z.
Definition portat_mode           : ident := 4019%Z.
Definition portat_channnelID     : ident := 4020%Z.
Definition port_attr             : ident := 4021%Z.
(* Definition OSPortAttrTbl         : ident := 4022%Z. *)

Definition InitCorePartition: ident := 4023%Z.
Definition pt : ident := 4024%Z.
Definition entry : ident := 4025%Z.
Definition is_ELFProgramValid := 4026%Z.
Definition pthread_attr_init := 4027%Z.
Definition LoadElf2Mem'' := 4028%Z.

(* Definition CAP_TASK_CLASS := 2%Z.
Definition CAP_PARTITION_CLASS := 1%Z.
Definition CAP_CHANNEL_CLASS := 16%Z.
Definition CAP_PORT_CLASS := 10%Z.
Definition CAP_SEM_CLASS := 9%Z.
Definition CAP_QUEUE_CLASS := 5%Z.
Definition CAP_MUTEX_CLASS := 8%Z. *)

(* end add by CNU *) 

(* add by SJTU *)
(*timer and time definitions*)
(* vars *)
Definition OS_TICKS_PER_SEC_SYS : ident := 10001%Z.
Definition OSIntHandler: ident := 10002%Z. (*array*)
Definition OSIntHandlerParam: ident := 10003%Z. (*array*)
Definition TIMER_BASE : ident := 10004%Z.
Definition TGCR_REG : ident := 10005%Z.
Definition TCR_REG : ident := 10006%Z.
(* Definition TIMER_BASE := 35651584%Z. (* 0x02200000 *)
Definition TGCR_REG := 35651620%Z. (* 0x02200024 *)
Definition TCR_REG := 35651616%Z. (* 0x02200020 *)  *)
(* timer ptr: Vptr Tint32 ,
+1 : EMUMGT_CLKSPD
+2 : RSVD1
+4 : cntlo
+5 : cnthi
+6 : prdlo
+7 : prdhi
+8 : tcr
+9 : tgcr
+10 : wdtcr *)
Definition __timerregs : ident := 10007%Z. 
Definition OS_timerid_used : ident  := 10008%Z.
(* regs addr *)
Definition CSL_TIMER_0_REGS := 35651584%Z. (* 0x02200000 *)
Definition timerRegs0_RSVD0 := 35651584%Z. (* 0x02200000 *)
Definition timerRegs0_EMUMGT_CLKSPD := 35651588%Z. (* 0x02200004*)
Definition timerRegs0_RSVD1 := 35651592%Z. (*0x02200008*)
Definition timerRegs0_CNTLO := 35651600%Z. (*0x02200010*)
Definition timerRegs0_CNTHI := 35651604%Z. (*0x02200014*)
Definition timerRegs0_PRDLO := 35651608%Z. (*0x02200018*)
Definition timerRegs0_PRDHI := 35651612%Z. (*0x0220001C*)
Definition timerRegs0_TCR := 35651616%Z. (*0x02200020*)
Definition timerRegs0_TGCR := 35651620%Z. (*0x02200024*)
Definition timerRegs0_WDTCR := 35651624%Z. (*0x02200028*)
(*tmr struct*)
Definition OS_Timer_Regs : ident := 10009%Z.
Definition OSRSVD0 : ident := 10010%Z.
Definition OSEMUMGT : ident := 10011%Z.
Definition OSRSVD1 : ident := 10012%Z.
Definition OSCNTLO : ident := 10013%Z.
Definition OSCNTHI : ident := 10014%Z.
Definition OSPRDLO : ident := 10015%Z.
Definition OSPRDHI : ident := 10016%Z.
Definition OSTCRreg : ident := 10017%Z.
Definition OSTGCR : ident := 10018%Z.
(*vars *)
Definition tickspersecond : ident := 10019%Z.
Definition period : ident := 10020%Z.
Definition timerid : ident := 10021%Z. 
Definition mode : ident := 10022%Z.
Definition intfunc: ident := 10023%Z.
Definition intarg : ident := 10024%Z.
Definition Timer_TGCR : ident := 10025%Z.
Definition TimerRegs_CNTLO : ident := 10026%Z.
Definition TimerRegs_CNTHI : ident := 10027%Z.
Definition cntlow : ident := 10028%Z.
Definition cnthigh : ident := 10029%Z.
Definition TimerRegs_PRDLO : ident := 10030%Z.
Definition TimerRegs_PRDHI : ident := 10031%Z.
Definition TimerRegs_EMUMGT_CLKSPD : ident := 10032%Z.
Definition TimerRegs_TGCR : ident := 10033%Z.
Definition TimerRegs_TCR : ident := 10034%Z.
Definition timerx : ident := 10035%Z.
Definition prdlo : ident := 10036%Z.
Definition prdhi : ident := 10037%Z.
Definition enable64bit : ident := 10038%Z.
Definition outputmode : ident := 10039%Z.
Definition tmp_timeridused : ident := 10040%Z.

(* constants*)
Definition CPU_CLK_KHZ := 1000000%Z.
Definition INT_NUM_MIN := 5%Z.
Definition INT_NUM_MAX := 15%Z.
Definition INTHANDLER_LENGTH := 11%nat.


(* CSL constants*)
Definition CSL_TMR_TIMMODE_GPT:= 0%Z.
Definition CSL_TMR_TGCR_TIMMODE_SHIFT := 2%Z.
Definition CSL_TMR_TGCR_TIMLORS_RESET_OFF :=1%Z.
Definition CSL_TMR_TGCR_TIMLORS_SHIFT := 0%Z.
Definition CSL_TMR_TGCR_TIMHIRS_SHIFT := 1%Z.
Definition CSL_TMR_TGCR_TIMHIRS_RESET_OFF := 1%Z.
Definition CSL_TMR_EMUMGT_CLKSPD_FREE_MASK := 1%Z.
Definition CSL_TMR_EMUMGT_CLKSPD_SOFT_MASK := 2%Z.
Definition CSL_TMR_EMUMGT_CLKSPD_MASK :=4294967292%Z. (* ~ (′CSL_TMR_EMUMGT_CLKSPD_FREE_MASK |ₑ ′CSL_TMR_EMUMGT_CLKSPD_SOFT_MASK)*)
Definition CSL_TMR_CLOCK_INP_NOGATE := 0%Z.
Definition CSL_TMR_TCR_TIEN_LO_SHIFT := 9%Z.
Definition CSL_TMR_CLKSRC_INTERNAL := 0%Z.
Definition CSL_TMR_TCR_CLKSRC_LO_SHIFT := 8%Z.
Definition CSL_TMR_ENAMODE_CONT := 2%Z.
Definition CSL_TMR_TCR_ENAMODE_LO_SHIFT := 6%Z.
Definition CSL_TMR_TCR_PWID_LO_SHIFT := 4%Z.
Definition CSL_TMR_CP_CLOCK := 1%Z.
Definition CSL_TMR_TCR_CP_LO_SHIFT := 3%Z.
Definition CSL_TMR_INVINP_UNINVERTED := 0%Z.
Definition CSL_TMR_TCR_INVINP_LO_SHIFT := 2%Z.
Definition CSL_TMR_INVOUTP_UNINVERTED := 0%Z.
Definition CSL_TMR_TCR_INVOUTP_LO_SHIFT := 1%Z.
Definition CSL_TMR_TCR_TSTAT_LO_SHIFT := 0%Z.
Definition CSL_GEM_TINT8L := 66%Z.

(*funcs *)
Definition sys_clk_rate_get := 10401%Z.
Definition sys_clk_rate_set := 10402%Z.
Definition OStimer_create := 10403%Z.
Definition OStimer_start := 10404%Z.
Definition OStimer_stop := 10405%Z.
Definition OStimer_resume := 10406%Z.
Definition OStimer_delete := 10407%Z.
Definition OStimer_gettime := 10408%Z.
Definition OStimer_Init := 10409%Z.
Definition OStimer_Config := 10410%Z.
Definition OStimer_outConfig := 10411%Z. 
Definition OSreset_timer := 10412%Z.
Definition OSint_install_handler_timer := 10413%Z.
Definition compute_period := 10414%Z.


(*core communication*)
(*current core id 未知，但是不能修改*)
Parameter DNUM : Z.
Parameter dnum_range :  Z.le 0 DNUM /\  Z.le DNUM 7.
(*constants*)
Definition CORE0_IPC := 2048%Z.
Definition CORE1_IPC := 4096%Z.
Definition CORE2_IPC := 8192%Z.
Definition CORE3_IPC := 16384%Z.
Definition CORE4_IPC := 32768%Z.
Definition CORE5_IPC := 65536%Z.
Definition CORE6_IPC := 131072%Z.
Definition CORE7_IPC := 262144%Z.
Definition IPC_MESSAGE_BROAD := 16%Z.
Definition IPC_MESSAGE_RDY := 256%Z.
Definition IPC_MESSAGE_ACK := 512%Z.
Definition IPC_STEP := 10240%Z.
Definition IPC_BROAD := 2%Z.
Definition IPC_BLOCK := 1%Z.
Definition IPC_NONACK := 0%Z.
(*vars*)
Definition IPCMem : ident := 10600%Z.
Definition IPCSem : ident := 10601%Z.
Definition IPCSemShared : ident := 10602%Z.
Definition IPCSendSem : ident := 10603%Z.
Definition srcCore : ident := 10604%Z.
Definition dstAddr : ident := 10605%Z.
Definition flag : ident := 10606%Z.
Definition IPCBroad_cur : ident := 10607%Z.
Definition step : ident := 10608%Z.
Definition ipcinfo : ident := 10609%Z.
Definition tmpsem : ident := 10610%Z.
Definition read_ipcgr : ident := 10611%Z.
Definition iIPCGRInfo : ident := 10612%Z.
Definition corenum : ident := 10613%Z.
Definition IPCBroad_Core_Current : ident := 10614%Z.
Definition IPCBroad_pointer : ident := 10615%Z.
Definition dstCore : ident := 10616%Z.
Definition srcAddr : ident := 10617%Z.
(*funcs*)
Definition corecomm_memcpy := 10701%Z.
Definition IPCrecv :=10702%Z.
Definition OSIPCSemPend := 10703%Z.
Definition OSIpc := 10704%Z.
Definition OS_getCoreIPC := 10706%Z.
Definition OSIPCSemPost := 10707%Z.
Definition IPCsend := 10708%Z.
Definition OS_IPCSched := 10709%Z.
Definition OSIPCQPost := 10710%Z.

(* add by wxy *)
Definition Refactsend :=10800%Z.
Definition doRefactorISR := 10801%Z.
Definition dynamic_refactor_pend := 10802%Z.
Definition RefacMsgQueue:=10803%Z.
Definition elf:ident:=10804%Z.
Definition dstcoreid:ident:= 10805%Z.
Definition refac_cfg:ident:= 10806%Z.
Definition dynrefaccfgFreeList:ident:=10807%Z.
Definition Next:ident:= 10808%Z.
Definition dynrefaccfg:ident:=10809%Z.
Definition dynrefcmsgQ:ident:= 10810%Z.
Definition size_of_dyn_refac_cfg:=160%Z.
Definition REFACTOR_RDY := 1024%Z.
Definition REFAC_MSG_QUEE_MAX_LEN := 10%Z.
Definition dynrefaccfgTbl: ident:= 10811 %Z.
Definition prefcfg1:=10812%Z.
Definition prefcfg2:=10813%Z.
Definition memcpy1:= 10814 %Z.
Definition memcpy2:= 10815 %Z.
Definition memcpy3:= 10816 %Z.
Definition memcpy4:= 10817 %Z.
Definition memcpy5:= 10818 %Z.
Definition LoadElf2Mem:= 10819%Z.
Definition Pro_header:ident:=10820 % Z.
Definition Elf_header:ident:=10821 %Z.
Definition Pro_header_ptr: ident:= 10822 % Z.
Definition addrPoint:ident:= 10823%Z.
Definition file: ident:= 10824% Z.
Definition PT_LOAD:= 1% Z.
Definition TaskEntry: ident:= 10825%Z.
Definition stkaddr: ident:= 10826%Z.
Definition elf32ehdr: ident:= 10827 %Z.
Definition elf32phdr: ident:= 10828%Z.
Definition e_type: ident:= 10829%Z.
Definition e_machine: ident:= 10830%Z.
Definition e_version: ident:= 10831%Z.
Definition e_entry: ident:= 10832%Z.
Definition e_phoff: ident:= 10833%Z.
Definition e_shoff: ident:= 10834%Z.
Definition e_flags: ident:= 10835%Z.
Definition e_ehsize: ident:= 10836%Z.
Definition e_phentsize: ident:= 10837%Z.
Definition e_phnum: ident:= 10838%Z.
Definition e_shentsize: ident:= 10839%Z.
Definition e_shnum: ident:= 10840%Z.
Definition e_shstrndx: ident:= 10841%Z.
Definition p_type: ident:= 10842%Z.
Definition p_offset:ident:= 10843%Z.
Definition p_vaddr:ident:= 10844%Z.
Definition p_paddr: ident:= 10845%Z.
Definition p_filesz: ident:= 10846%Z.
Definition p_memsz: ident:= 10847%Z.
Definition p_flags: ident:= 10848%Z.
Definition p_align: ident:= 10849%Z.
Definition memset:= 10850%Z.
Definition size_of_Elf32_Phdr:= 256%Z.
Definition refactaskStk := 10851%Z.
Parameter dynrefcmsgQ_addr: addrval.
Definition malloc_Elf32_Phdr:= 10852 %Z.
Definition free_Elf32_Phdr:= 10853%Z.
Definition malloc_Elf32_Ehdr:= 10854 %Z.
Definition free_Elf32_Ehdr:= 10855%Z.
Definition LoadElf2Mem':= 10856%Z.
Definition dyn_refac_init:=10857%Z.
Parameter refactstk_addr: addrval.


(***** definitions about partitions *****) 
(* Definition PARTITION_ENABLE := 0%Z. *)
(* Definition MEM_VIOLATION := 254%Z. *)
(* Definition PARTITION_NUM := 8%Z. *)
(* Definition DOMAIN_SIZE := PARTITION_NUM. *)

(* Definition Core_partition_num : ident := 751%Z. *)
(* Definition Domain2Index : ident := 752%Z. *)
(* Definition ksCurDomain : ident := 753%Z. *)

(* funcs *)
Definition receivePortMsg := 10900%Z.
Definition OS_PortTaskRdy := 10901%Z.
Definition OSQSendToDomain := 10902%Z.
Definition OSSampleSendToDomain := 10903%Z.
Definition OSPortAcceptWithoutCheck := 10904%Z.
Definition QPortPost := 10905%Z.
Definition PortAccept := 10906%Z.
Definition PortFlush := 10907%Z.
Definition QPortPend := 10908%Z.
Definition SamplePortPost := 10909%Z.
Definition CSL_semAcquireDirect := 11001%Z.
Definition CSL_semReleaseSemaphore := 11002%Z.
Definition OSPortAcceptWithoutCheck2 := 11003%Z.
Definition OSPortAddToChannel := 11004%Z.
Definition portBindCheck := 11005%Z.
Definition OSKernelPortCreate := 11006%Z.
Definition OSChannelCreate := 11007%Z.
Definition channleCreateCheck := 11008%Z.
Definition portCreateCheck := 11009%Z.
Definition SamplePortCreate := 11010%Z.
Definition QPortCreate := 11011%Z.

(* vars *)
Definition maxMsgSize : ident := 10910%Z.
Definition coreNum : ident := 10911%Z.
Definition domain : ident := 10912%Z.
Definition portID : ident := 10913%Z.
Definition direction : ident := 10914%Z.
Definition refreshRate : ident := 10915%Z.
Definition status : ident := 10916%Z.
Definition msgInTick : ident := 10917%Z.
Definition msgOutTick : ident := 10918%Z.
Definition nextPort : ident := 10919%Z.
Definition len : ident := 10920%Z.
Definition data : ident := 10921%Z.
Definition channelID : ident := 10922%Z.
Definition dmport : ident := 10923%Z.
Definition channel : ident := 10924%Z.
Definition srcPortsNum : ident := 10925%Z.
Definition dstPortsNum : ident := 10926%Z.
Definition semaphore : ident := 10927%Z.
Definition dstPortsHead : ident := 10928%Z.
Definition dstPortsTail : ident := 10929%Z.
Definition srcPort : ident := 10930%Z.
Definition enable : ident := 10931%Z.
Definition partitionID : ident := 10932%Z.
Definition port_ptr : ident := 10933%Z.
Definition os_domain_port : ident := 10935%Z.
Definition os_k_port : ident := 10936%Z.
Definition os_channel : ident := 10937%Z.
Definition os_message : ident := 10938%Z.
Definition inTime : ident := 10939%Z.
Definition kport : ident := 10940%Z.
Definition resource_get_res : ident := 10941%Z.
Definition dstKPort :ident := 10942%Z.
Definition error : ident := 10943%Z.
Definition os_domain_port_seg : ident := 10945%Z.
Definition OSEventPtrPort : ident := 10956%Z.
Definition re : ident := 10957%Z. 
Definition dmPort : ident := 10958%Z.
Definition portId : ident := 10959%Z.
Definition port : ident := 10960%Z.
Definition corPort_ptr : ident := 10961%Z.
(* init struct vars *)
Definition osport_attr_t : ident := 10962 %Z.
Definition osdomain_t : ident := 10963%Z.
Definition OSPartitionPeriod : ident :=  10964%Z.
Definition pAddress : ident := 10965%Z.
Definition vAddress: ident := 10966%Z.
Definition domainIntStatusTbl : ident := 10967%Z.
Definition domainID : ident := 10968%Z.
Definition OSPortAttrTbl : ident := 10969%Z.
Definition ksDomains: ident := 10970%Z.
Definition ksCurDomain: ident:= 10971%Z.
Definition channel_semaphore: ident := 10972%Z.
Definition sys_channel_info := 10973%Z.
Definition count : ident := 10974%Z.
Definition freeTbl : ident := 10975%Z.
Definition ch_type : ident := 10976%Z.
Definition buff : ident := 10977%Z.

(* global vars *)
Definition OSKernelPortIDTbl : ident := 11101%Z.
Definition OSKernelPortFreeList : ident := 11102%Z.
Definition OSKernelPortTbl : ident := 11103%Z.
Definition OSDomainPortPtrList : ident := 11104%Z.
Definition OSCorePortPtrList : ident := 11105%Z.
Definition OSChannelFreeList : ident := 11106%Z.
Definition OSChannelIDTbl : ident := 11107%Z.

(* constants *)
Definition CHANNEL_CACHE_SZIE := 32%Z.
Definition OS_PARTITION_MESSAGE_COME := 1%Z.
Parameter OS_PARTITION_MESSAGE_COME_ptr: addrval.
Definition SAMPLE := 0%Z.
Definition QUEUE := 1%Z.
Definition SOURCE := 0%Z.
Definition DESTINATION := 1%Z.
Definition OUTCORE := 0%Z.
Definition INCORE := 1%Z.
Definition GET_PORT_MESSAGE := 256%Z.
Definition OS_PORT_ERR_DIRECTION_TYPE := 184%Z.
Definition OS_PORT_MSG_ARG_NULL := 183%Z.
Definition OS_ERR_PORT_UNBIND := 168%Z.
Definition DEFAULT_CHANNLE_SEMAPHROE := 255%Z.
Definition OS_RESOURCE_SEMAPHORE_PORT := 9%Z.
Definition OS_CHANNEL_ERR_BEING_USED := 178%Z.
Definition OS_PORT_ERR_TYPE := 165%Z.
Definition OS_PORT_ERR_NULL := 164%Z.
Definition OS_ERR_PARTITION_UNMAPPED := 190%Z.
(* Definition PORT_NUMS := 64%Z. *)
(* Definition CHANNEL_NUMS := 32%Z. *)
Definition OS_ERR_PORT_NO_CHANNEL := 169%Z.
Definition OS_ERR_DSTPORT_FULL := 167%Z.
Definition OS_EVENT_TYPE_PORT := 6%Z.
Definition OS_PORT_ID_INVALID := 162%Z.
Definition OS_PORT_FAIL_TO_GET := 166%Z.
Definition OS_PORT_ID_EXIST := 163%Z.
Definition OS_PORT_DEPLETED := 161%Z.
Definition DEFAULT_PORTID := 255%Z.
Definition DEFAULT_CORENUM := 255%Z.
Definition DEFAULT_CHANELID := 255%Z.
Definition DEFAULT_PARTITIONID := 255%Z.
Definition DEFAULT_PORTSTATE := 255%Z.
Definition CHECK_ERROR := 185%Z.
Definition OS_CHANNEL_ERR_NULL := 175%Z.
Definition OS_ERR_PORT_HAVE_BEEN_BINDED := 182%Z.
Definition OS_PORT_ERR_MULTICORE := 179%Z.
(* Definition USER_INT_MAX_N := 11%Z. *)
Definition OS_CHANNEL_ID_INVALID := 171%Z.
Definition OS_CHANNEL_ERR_SEMAPHORE_NULL := 177%Z.
Definition OS_CHANNEL_DEPLETED := 170%Z.
Definition OS_RESOURCE_SEMAPHORE_CHANNEL := 10%Z.
Definition OS_CHANNEL_ID_EXIST := 172%Z.
Definition OS_CHANNEL_FAIL_TO_GET := 173%Z.
Definition OS_INTER_CORE_CHANNEL_NUMS := 8%Z.

(* end add by SJTU *)

Definition pthread_attr : ident := 1700%Z. 
Definition stackaddr : ident := 1701%Z. 
Definition stacksize : ident := 1702%Z. 
Definition sched_priority : ident := 1703%Z. 

Definition pthread_create : ident := 1704%Z. 
Definition thread: ident := 1705%Z. 
(* Definition attr: ident := 1706%Z.  *)
Definition start_routine : ident := 1706%Z. 
Definition arg: ident := 1708%Z. 



Definition PrioTbl: ident := 1709%Z. 
Definition pthread_cancel : ident := 1710%Z. 


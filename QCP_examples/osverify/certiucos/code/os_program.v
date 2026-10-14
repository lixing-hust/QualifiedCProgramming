Require Import include_frm.
Require Import os_core.
Require Import os_time.
Require Import os_mutex.
Require Import os_sem.
Require Import os_q.
Require Import os_mutex_cap.
Require Import os_sem_cap. 
Require Import os_q_cap. 
Require Import os_cpu_a.
Require Import os_code_defs.
Require Import code_notations.

Require Import os_task.

Require Import ios_int_ipc.
Require Import ios_int_nmi.
Require Import ios_int_tick.
Require Import ios_int.

Require Import useraddrcheck. 

Require Import os_timer.
Require Import os_inter_communication.
Require Import ios_cap.
Require Import inter_partition_communication.

Require Import partition.
Require Import partition_CPU.
Require Import partition_xml_init.
(* eta i, all the functions defined in 'os_core.v' are os internal functions. *)

Definition internal_fun_list := 
  ( OSTimeTick_impl :: 
    OS_EventTaskRdy_impl ::
    OS_EventTaskPostRdy_impl :: 
    OS_EventTaskPostRdyDel_impl :: 
    OS_EventTaskWait_impl ::
    OS_EventTaskPostWait_impl :: 
    OS_EventTO_impl ::
    OS_EventPostTO_impl :: 
    OS_Sched_impl ::
    OS_IPCSched_impl ::
    OS_EventWaitListInit_impl :: 
    OS_EventRemove_impl ::
    OS_EventRemoveDel_impl ::
    UserAddrCheck_impl :: 
    UserAddrCheckCrit_impl :: 
    (* OS_EventSearch_impl :: *)
    OS_TCBInit_impl ::
    OS_IsSomeMutexOwner_impl :: 
    Interrupt_Init_impl ::
    UserAddrCheck_6678_impl :: UserAddrCheck_6713_impl ::
    OSIntEnter_impl :: OSIntExit_impl ::
    EXC_HANDLER_impl :: fnull_impl ::
    OSTaskSuspend_impl :: OSTaskResume_impl :: OSIpc_impl :: OSTimeTick_impl :: 
    getFreePos_impl :: 
    pthread_mutexattr_init_impl ::
    OSSemAccept_impl ::
    OSSemCreate_impl ::
    OSSemDel_impl ::
    OSSemPend_impl ::
    OSSemPost_impl ::
    OSSemPostBin_impl ::
    OSIPCSemPost_impl ::
    OSMutexAccept_impl ::
    OSMutexCreate_impl ::
    OSMutexDel_impl :: 
    OSMutexPend_impl :: 
    OSMutexPost_impl :: 
    OSQAccept_impl ::
    OSQCreate_impl ::
    OSQDel_impl ::
    OSQPend_impl ::
    OSQPost_impl ::
    OSQTimedPost_impl ::
    OSIPCQPost_impl ::
    OSQQuery_impl ::
    partitionSysInit_impl ::
    nextDomain_impl ::
    switchDomain_impl ::
    switchDomain_impl' ::
    initDefaultMPAX_impl ::
    initMPAX_impl ::
    is_bigEndian_impl ::
    InitDNUM_impl ::
    initConf_impl ::
    IntPartitionMuxInit_impl ::
    InitCorePartition_impl ::
    OSreset_timer_impl::
    OStimer_Config_impl ::
    OStimer_outConfig_impl ::
    OStimer_Init_impl ::
    doRefactorISR_impl::
    LoadElf2Mem_impl ::
    OSIpc_impl:: 
    ucos_Grant_Cap_impl::
    ucos_CNode_Mint_impl ::
    ucos_CNode_Copy_impl ::
    ucos_CNode_Move_impl ::
    ucos_CNode_Mutate_impl ::
    ucos_CNode_Delete_impl::
    Get_Obj_Slot_impl ::
    Get_Obj_Slot_without_critical_impl ::
    CNode_delete_recursive_impl ::
    Check_Cap_Type_impl ::
    ucos_CNode_Revoke_impl ::
    OSSampleSendToDomain_impl ::
    OS_PortTaskRdy_impl ::
    OSQSendToDomain_impl::
    OSPortAcceptWithoutCheck_impl ::
    OSPortAcceptWithoutCheck2_impl ::
    OSKernelPortCreate_impl ::
    SamplePortCreate_impl ::
    QPortCreate_impl ::
    OSPortAddToChannel_impl :: 
    OSChannelCreate_impl ::
    receivePortMsg_impl ::
    nil )%list.

Definition os_internal := convert_cfuns internal_fun_list.

Definition api_fun_list := 
  ( mq_create_impl ::  mq_delete_impl ::
    mq_receive_impl :: mq_timedreceive_impl :: mq_send_impl :: mq_getinfo_impl :: 
    sem_trywait_impl :: sem_init_impl :: sem_init_bin_impl :: sem_destroy_impl :: 
    sem_wait_impl :: sem_timedwait_impl :: sem_signal_impl :: sem_flush_impl :: sem_getvalue_impl :: 
    pthread_mutexattr_init_impl :: pthread_mutexattr_destroy_impl ::
    pthread_mutexattr_settype_impl :: pthread_mutexattr_gettype_impl ::
    pthread_mutexattr_setprioceiling_impl :: pthread_mutexattr_getprioceiling_impl ::
    pthread_mutex_init_impl :: pthread_mutex_destroy_impl ::
    pthread_mutex_trylock_impl :: pthread_mutex_lock_impl :: pthread_mutex_timedlock_impl :: 
    pthread_mutex_unlock_impl :: getPartitionID_impl ::
    OSTimeDly_impl :: OSTimeGet_impl ::  
    OSTaskCreate_impl :: OSTaskDel_impl ::
    int_lock_impl :: int_unlock_impl :: int_enable_pic_impl :: int_disable_pic_impl ::
    int_unstall_handler_6678_impl :: int_unstall_handler_6713_impl ::
    int_install_handler_6678_impl :: int_install_handler_6713_impl ::
    exception_handler_set_impl ::
    IPCrecv_impl :: IPCsend_impl ::
    Refactsend_impl:: dynamic_refactor_pend_impl::
    sys_clk_rate_get_impl :: sys_clk_rate_set_impl ::
    OStimer_create_impl :: OStimer_start_impl :: OStimer_stop_impl :: OStimer_resume_impl :: 
    OStimer_delete_impl :: OStimer_gettime_impl :: 
    grant_cspace_cap_impl :: user_cnode_mint_impl :: 
    user_cnode_copy_impl :: user_cnode_move_impl ::
    user_cnode_mutate_impl :: user_cnode_delete_impl ::
    user_cnode_revoke_impl ::
    SamplePortPost_impl :: PortAccept_impl :: PortFlush_impl :: QPortPend_impl :: QPortPost_impl:: nil )%list.
    
Definition os_api :=   convert_cfuns api_fun_list.                             

(* theta*)

Definition interrupt_list := 
  ( user_nmi_ISR_impl ::  
    OSTickISR_impl ::
    OSUserISR_impl ::
    OSIpcISR_impl ::
    OSDispatchISR_impl :: nil )%list.
    
Definition os_interrupt := convert_ifuns interrupt_list.

Definition low_level_os_code := (os_api, os_internal, os_interrupt).

(*Definition getFunType fid : type :=
    match os_api fid with
    | Some (t, _ , _ , _) => t
    | None => Tnull
    end.

Definition getFunArgs fid : decllist :=
    match os_api fid with
    | Some (_, args , _ , _) => args
    | None => dnil
    end.

Definition getFunDecls fid : decllist :=
    match os_api fid with
    | Some (_ , _ , decls , _) => decls
    | None => dnil
    end.

Definition getFunBody fid : stmts :=
    match os_api fid with
    | Some (_ , _ , _ , body) => body
    | None => sskip None
    end. *)

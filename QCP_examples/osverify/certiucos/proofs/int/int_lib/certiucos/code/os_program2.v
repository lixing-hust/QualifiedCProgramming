Require Import include_frm2.
Require Import os_core2.
Require Import os_q2.
Require Import os_mbox2.
Require Import os_time2.
Require Import os_mutex2.
Require Import os_sem2.
Require Import os_cpu_a2.
Require Import os_code_defs2.
Require Import code_notations2.

Require Import os_task2.

Require Import ios_int_ipc2.
Require Import ios_int_nmi2.
Require Import ios_int_tick2.
Require Import ios_int2.

(* eta i, all the functions defined in 'os_core.v' are os internal functions. *)

Definition internal_fun_list := 
  ( OSTimeTick_impl :: OS_EventTaskRdy_impl ::
    OS_EventTaskWait_impl :: OS_Sched_impl::
    OS_EventWaitListInit_impl :: 
    OS_EventRemove_impl ::
    OS_EventSearch_impl :: OS_TCBInit_impl :: OS_IsSomeMutexOwner_impl :: 
    Interrupt_Init_impl ::
    UserAddrCheck_6678_impl :: UserAddrCheck_6713_impl ::
    OSIntEnter_impl :: OSIntExit_impl ::
    EXC_HANDLER_impl :: fnull_impl ::
    OSTaskSuspend_impl :: OSIpc_impl :: OSTimeTick_impl :: nil )%list.

Definition os_internal := convert_cfuns internal_fun_list.

Definition api_fun_list := 
  ( OSQAccept_impl ::  OSQCreate_impl ::
    OSQDel_impl  :: OSQPend_impl :: 
    OSQGetMsg_impl ::  OSQPost_impl ::  OSSemAccept_impl ::
    OSSemCreate_impl :: OSSemDel_impl ::  OSSemPend_impl ::  
    OSSemPost_impl :: OSTimeDly_impl :: OSTimeGet_impl ::  OSMboxCreate_impl:: OSMboxDel_impl :: OSMboxAccept_impl::OSMboxPost_impl ::OSMboxPend_impl:: OSMutexAccept_impl :: OSMutexCreate_impl :: OSMutexDel_impl :: OSMutexPend_impl :: OSMutexPost_impl :: OSTaskCreate_impl :: OSTaskDel_impl ::
    int_lock_impl :: int_unlock_impl :: int_enable_pic_impl :: int_disable_pic_impl ::
    int_unstall_handler_6678_impl :: int_unstall_handler_6713_impl ::
    int_install_handler_6678_impl :: int_install_handler_6713_impl ::
    exception_handler_set_impl :: nil )%list.
    
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

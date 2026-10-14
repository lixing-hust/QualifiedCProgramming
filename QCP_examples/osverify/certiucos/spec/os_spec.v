Require Import os_program.
Require Import abs_op.
Require Import abs_op_capability. 
Require Import abs_op_partition_ext.
Require Import include_frm.
Require Import os_code_defs.
Require Import ios_int.
Require Import ios_cap_defs.
Require Import ios_cap.

Local Open Scope list_scope.

Definition api_spec_list := 
  (sem_trywait, semtrywaitapi) :: 
  (sem_init, seminitapi) :: 
  (sem_init_bin, seminitbinapi) :: 
  (sem_destroy, semdestroyapi) ::
  (sem_wait, semwaitapi) :: 
  (sem_timedwait, semtimedwaitapi) :: 
  (sem_signal, semsignalapi) :: 
  (sem_flush, semflushapi) :: 
  (sem_getvalue, semgetvalueapi) :: 
  (pthread_mutexattr_init, mutexattrinitapi) :: 
  (pthread_mutexattr_destroy, mutexattrdestroyapi) :: 
  (pthread_mutexattr_settype, mutexattrsettypeapi) :: 
  (pthread_mutexattr_gettype, mutexattrgettypeapi) :: 
  (pthread_mutexattr_setprioceiling, mutexattrsetprioceilingapi) :: 
  (pthread_mutexattr_getprioceiling, mutexattrgetprioceilingapi) :: 
  (pthread_mutex_init, mutexinitapi) :: 
  (pthread_mutex_destroy, pthread_mutex_destroy_api) ::
  (pthread_mutex_trylock, mutextrylockapi) :: 
  (pthread_mutex_lock, mutexlockapi) ::
  (pthread_mutex_timedlock, mutextimedlockapi) ::
  (pthread_mutex_unlock, mutexunlockapi) :: 
  (mq_create, mqcreateapi) ::
  (mq_delete, mqdeleteapi) ::
  (mq_receive, mqreceiveapi) ::
  (mq_timedreceive, mqtimedreceiveapi) ::
  (mq_send, mqsendapi) ::
  (mq_getinfo, mqgetinfoapi) :: 
  (getPartitionID, getPartitionIDapi) ::
  (OSTimeDly, dlyapi) ::
  (OSTimeGet, tmgetapi) :: 
  (OSTaskCreate, taskcreapi) :: 
  (OSTaskDel, taskdelapi) ::
  (int_lock, lockapi) :: 
  (int_unlock, unlockapi) :: 
  (int_enable_pic, enablepicapi) :: 
  (int_disable_pic, disablepicapi) ::
  (int_unstall_handler_6678, unstall_handler_6678api) ::
  (int_unstall_handler_6713, unstall_handler_6713api) ::
  (int_install_handler_6678, install_handler_6678api) ::
  (int_install_handler_6713, install_handler_6713api) ::
  (exception_handler_set, exchandler_setapi) ::
  (grant_cspace_cap, grant_cspace_cap_api) ::
  (user_cnode_mint, user_cnode_mint_api) ::
  (user_cnode_move, user_cnode_move_api) :: 
  (user_cnode_copy, user_cnode_copy_api) ::
  (user_cnode_mutate, user_cnode_mutate_api) ::
  (user_cnode_delete, user_cnode_delete_api) ::
  nil.

Fixpoint convert_api_spec (ls : list (fid * osapi)) : fid -> option osapi :=
  match ls with
    | nil => fun _ : fid => None
    | (id, imp) :: ls' =>
      fun id' : fid =>
        if Zbool.Zeq_bool id id' then Some imp 
        else convert_api_spec ls' id'
  end.

Definition api_spec := convert_api_spec api_spec_list.

Definition int_spec_list := 
  (user_nmi_ISR, usernmi_isr) :: 
  (OSTickISR, tickisr) :: (5%nat, userisr) :: (OSIpcISR, ipcisr)
  ::(7%nat, userisr)::(8%nat, userisr)::(9%nat, userisr)
  ::(10%nat, userisr)::(11%nat, userisr)::(12%nat, userisr)
  ::(13%nat, userisr)::(14%nat, userisr)::(15%nat, userisr) :: nil.

Fixpoint convert_int_spec (ls : list (hid * int_code)) : hid -> option int_code :=
  match ls with
    | nil => fun _ : hid => None
    | (id, imp) :: ls' =>
      fun id' : hid =>
        if EqNat.beq_nat id id' then Some imp 
        else convert_int_spec ls' id'
  end.

Definition int_spec  := convert_int_spec int_spec_list.

Definition os_spec :osspec:=(api_spec,int_spec,GetHPrio).



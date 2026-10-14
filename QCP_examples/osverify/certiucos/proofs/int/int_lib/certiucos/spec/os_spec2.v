Require Import os_program2.
Require Import abs_op2.
Require Import include_frm2.
Require Import os_code_defs2.
Require Import ios_int2.

Local Open Scope list_scope.

Definition api_spec_list := 
  (OSQAccept,qaccapi) ::
  (OSQCreate,qcreapi) ::
  (OSQDel, qdelapi) ::
  (OSQPend,qpendapi) ::
  (OSQGetMsg, getmsgapi) ::
  (OSQPost,qpostapi) ::
  (OSSemAccept, semaccapi) ::
  (OSSemCreate, semcreapi) ::
  (OSSemDel, semdelapi) ::
  (OSSemPend, sem_pendapi) ::
  (OSSemPost, sem_postapi) :: 
  (OSTimeDly, dlyapi) ::
  (OSTimeGet, tmgetapi) ::
  (OSMboxCreate, mbox_createapi) ::
  (OSMboxDel, mbox_delapi) ::
  (OSMboxAccept, mbox_accapi) ::
  (OSMboxPend, mbox_pendapi) ::
  (OSMboxPost, mbox_postapi) ::
  (OSMutexCreate, mutexcreapi) ::
  (OSMutexDel, mutexdelapi) ::
  (OSMutexAccept, mutexaccapi) ::
  (OSMutexPend, mutexpendapi) ::
  (OSMutexPost, mutexpostapi) ::
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



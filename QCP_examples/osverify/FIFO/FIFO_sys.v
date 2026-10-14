Require Import log_code_defs.
Require Import FIFO_spec. 
(* Require Import FIFO_succ.  *)

Fixpoint convert_api_spec (ls : list (fid * osapi)) : fid -> option osapi :=
  match ls with
    | nil => fun _ : fid => None
    | (id, imp) :: ls' =>
      fun id' : fid =>
        if Zbool.Zeq_bool id id' then Some imp 
        else convert_api_spec ls' id'
  end.

Definition int_spec_list : list (hid * int_code) := nil .

Fixpoint convert_int_spec (ls : list (hid * int_code)) : hid -> option int_code :=
  match ls with
    | nil => fun _ : hid => None
    | (id, imp) :: ls' =>
      fun id' : hid =>
        if EqNat.beq_nat id id' then Some imp 
        else convert_int_spec ls' id'
  end.

Definition int_spec  := convert_int_spec int_spec_list.

Definition api_spec_list' := 
  (mq_create, mqcreateapi)
  :: (mq_delete, mqdeleteapi)
  :: (mq_send, mqsendapi)
  :: (mq_receive, mqreceiveapi)
  :: (mq_timedreceive, mqtimedreceiveapi)
  :: (mq_getinfo, mqgetinfoapi)
    :: nil
.

Definition api_spec':= convert_api_spec api_spec_list'.

Definition os_spec' := (api_spec', int_spec, GetHPrio).

Require Import memory.
Require Import if_language.
Require Import if_opsem.
Require Import spec_aux_defs. 
Require Import mq_apispecs.
Require Import buffer_apispecs. 
Require Import prt_apispecs.
Require Import intspecs.

(* api spec list *)

Definition mq_send := 1%Z. 
Definition mq_recv := 2%Z.
Definition mq_timedrecv := 3%Z. 

Definition q_port_pend := 11%Z.
Definition q_port_post := 12%Z.
Definition sample_port_post := 13%Z.
Definition port_accept := 14%Z. 

Definition buffer_post := 15%Z.
Definition buffer_accept := 16%Z.
Definition buffer_pend := 17%Z. 

Notation "'size_t'" := (Tint32) (at level 5).
Notation "'ssize_t'" := (Tint32) (at level 5).
Notation "'mqd_t'" := (Tint32) (at level 5). 

Notation "'Int8u'" := (Tint8) (at level 5).
Notation "'char'" := (Tint8) (at level 5).
Notation "'Int16u'" := (Tint16) (at level 5). 
Notation "'unsigned'" := (Tint32) (at level 5).

(* Require Import code_notations. *)
(* Open Scope code_scope. *)

Parameter OS_Port: type. 

Definition mqsendapi := (mqsend, (Tint32, Tint32 :: Tptr Tint8 :: Tint32 :: Tint32 :: nil)). 
Definition mqrecvapi := (mqreceive, (ssize_t, mqd_t :: Tptr char :: size_t :: Tptr Int8u :: nil)).
Definition mqtimedrecvapi := (mqtimedreceive, (ssize_t, mqd_t :: Tptr char :: size_t :: Tptr Int8u :: Int16u :: nil)). 

Definition qportpostapi := (qportpost, (Tint8, Tptr OS_Port :: nil)).
Definition qportpendapi := (qportpend, (Tint8, Tptr OS_Port :: Tint32 :: nil)).
Definition sampleportpostapi := (sampleportpost, (Tint8, Tptr OS_Port :: nil)). 
Definition portacceptapi := (portaccept, (Tint8, Tptr OS_Port :: nil)).  

Definition bufferpostapi := (bufferpost, (Tint8, Tptr OS_EVENT :: Tptr Tint8 :: nil)). 
Definition bufferacceptapi := (bufferaccept, (Tptr OS_EVENT, Tptr OS_EVENT :: nil)). 
Definition bufferpendapi := (bufferpend, (Tptr OS_EVENT, Tptr OS_EVENT :: Int16u :: nil)). 

Definition api_spec_list :=
  
  (* message queues *)
  (mq_send, mqsendapi) ::
  (mq_recv, mqrecvapi) :: 
  (mq_timedrecv, mqtimedrecvapi) :: 

  (* ports *) 
  (q_port_post, qportpostapi) ::
  (q_port_pend, qportpendapi) ::
  (sample_port_post, sampleportpostapi) :: 
  (port_accept, portacceptapi) :: 

  (* buffers *) 
  (buffer_post, bufferpostapi) ::
  (buffer_accept, bufferacceptapi) ::
  (buffer_pend, bufferpendapi) :: 

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

(* interrupt spec list *)

Definition OSTickISR := 5%nat.

Definition int_spec_list := (OSTickISR, tickisr) :: nil.

Fixpoint convert_int_spec (ls : list (hid * int_code)) : hid -> option int_code :=
  match ls with
    | nil => fun _ : hid => None
    | (id, imp) :: ls' =>
      fun id' : hid =>
        if EqNat.beq_nat id id' then Some imp 
        else convert_int_spec ls' id'
  end.

Definition int_spec  := convert_int_spec int_spec_list.

(* sched management*)

Definition in_rtbl (st:taskstatus):=
  match st with
    | rdy => True
    | wait x t_opt => match t_opt with
                                     | Some time => if Int.eq time Int.zero then True else False
                                     | None => False
                                  end
  end.

Definition get_hprio_d (O:osabst) (t:tid) : Prop :=  
  exists tls prio st msg pr d,
    get O abstcblsid = Some (abstcblist tls) /\
      get tls t = Some (prio, st, msg, false, pr) /\ 
      in_rtbl st /\ 
      get O kscurdomid = Some (kscurdom d) /\ 
      dom_for_prio pr = d /\ 
      forall i prio' st' msg' pr',
        i <> t ->
        get tls i = Some (prio', st', msg', false, pr') -> 
        in_rtbl st' ->
        dom_for_prio pr' = d -> 
        Int.ltu pr pr' = true. 
(* in the system model the current priority
    is the same as the original priority *)


Definition os_spec := (api_spec, int_spec, get_hprio_d).


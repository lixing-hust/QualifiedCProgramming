Require Import memory.
Require Export Integers.

Set Implicit Arguments.
Unset Strict Implicit.

(**The High-level Specification Language **)
Definition priority := int32.
Definition ecbid := addrval.
Definition msg := val.
Definition maxlen := int32.
Definition ostime := int32.
Definition waitset := list tid.
Definition ier := nat -> bool.
Definition Hier := ier.
Definition Hinthandler := int32->int32(*nat->int32*).
Definition HinthandlerParam := int32->addrval.
Definition Hexchandler := int32.
Definition susstatus := bool.


(* types for events *)
Definition rec_cnt := int32.
Definition wq := int32.
Definition cnsa:= int32.
Definition prot := int32.
Definition prioc := int32.
Definition eid := addrval.
Definition q_waittype := int32.
Definition q_flags := int32.
Definition q_maxmsg := int32.
Definition q_msgsize:= int32.
Definition q_curmsgs := int32.
Definition pos := int32.
(* end of types for events *)

(* types for tmr and corecom *)
Definition osclkrate := int32.
Definition coreid := nat.
(* end of types for tmr and corecom *)

Inductive tcbstats:=
| os_stat_sem: ecbid -> tcbstats
| os_stat_q: ecbid -> tcbstats
| os_stat_postq: ecbid -> tcbstats
| os_stat_time:  tcbstats
| os_stat_mbox: ecbid -> tcbstats
| os_stat_mutexsem: ecbid -> tcbstats
| os_stat_port: ecbid -> tcbstats.

Inductive taskstatus :=
 | rdy: taskstatus
 | wait : tcbstats -> option int32 -> taskstatus.
(* "wait (os_stat_x eid) (Some t)" or "wait (os_stat_x eid) None" *) 

Module abstcb.
  Definition B : Set := (priority * taskstatus * msg * susstatus)%type.
  Definition holder : B:= (Int.zero, rdy, Vnull, false).
End abstcb.

Module TcbMod := MapLib.MapFun tidspec abstcb.

(* Definition tcbdel := fun (M:TcbMod.map) a => TcbMod.minus M (TcbMod.sig a (Int.zero,rdy,Vnull)). *)

Program Instance TcbMap: PermMap tid ( priority * taskstatus * msg * susstatus) TcbMod.map :=
  {
    usePerm := TcbMod.usePerm;
    isRw := TcbMod.isRw;
    flip := TcbMod.flip;
    sameV := TcbMod.sameV;
    same := TcbMod.same;
    emp := TcbMod.emp;
    join := TcbMod.join;
    del := TcbMod.del;
    get := TcbMod.get;
    set := TcbMod.set;
    sig := TcbMod.sig;
    merge := TcbMod.merge;
    minus := TcbMod.minus;
    map_dec_a := TcbMod.map_dec_a
}.
Next Obligation.
  apply TcbMod.map_join_emp.
Qed.
Next Obligation.
  apply TcbMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply TcbMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply TcbMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply TcbMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply TcbMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_eql; auto.
Qed.
Next Obligation.
  apply TcbMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply TcbMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_get_sig.
Qed.
Next Obligation.
  apply TcbMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply TcbMod.map_get_set.
Qed.
Next Obligation.
  apply TcbMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply TcbMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply TcbMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_set_emp.
Qed.
Next Obligation.
  apply TcbMod.map_set_sig.
Qed.
Next Obligation.
  apply TcbMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply TcbMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply TcbMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply TcbMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply TcbMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_del_sem.
Qed.

Definition owner:= option (tid * int32).

Inductive edata:=
| abssem: int32 -> edata
| absmsgq : list msg -> maxlen -> list tid -> edata
| absmbox: msg -> edata
| absmutexsem: int32 -> owner -> edata
| absport : edata.

Module absecb.
  Definition B : Set := prod edata waitset.
  Definition holder : B := (absmbox Vnull, nil).
End absecb.

Module EcbMod := MapLib.MapFun tidspec absecb.

Program Instance EcbMap: PermMap tid (prod edata waitset) EcbMod.map :=
  {
    usePerm := EcbMod.usePerm;
    isRw := EcbMod.isRw;
    flip := EcbMod.flip;
    sameV := EcbMod.sameV;
    same := EcbMod.same;
    emp := EcbMod.emp;
    join := EcbMod.join;
    del := EcbMod.del;
    get := EcbMod.get;
    set := EcbMod.set;
    sig := EcbMod.sig;
    merge := EcbMod.merge;
    minus := EcbMod.minus;
    map_dec_a := EcbMod.map_dec_a
  }.
Next Obligation.
  apply EcbMod.map_join_emp.
Qed.
Next Obligation.
  apply EcbMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply EcbMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply EcbMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply EcbMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply EcbMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply EcbMod.map_eql; auto.
Qed.
Next Obligation.
  apply EcbMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply EcbMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply EcbMod.map_get_sig.
Qed.
Next Obligation.
  apply EcbMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply EcbMod.map_get_set.
Qed.
Next Obligation.
  apply EcbMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply EcbMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply EcbMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply EcbMod.map_set_emp.
Qed.
Next Obligation.
  apply EcbMod.map_set_sig.
Qed.
Next Obligation.
  apply EcbMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply EcbMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply EcbMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply EcbMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply EcbMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply EcbMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply EcbMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply EcbMod.map_del_sem.
Qed.


(************************ add by CNU ************************)

(* Module about absseminfo *)

Inductive infoeid :=
| infotid: addrval -> infoeid
| infonull
| infohold.

(* 1 -- binary, 2 -- counting *) 
Definition sem_tp := int32. 

(* Mapping from priority of task owning capability to the semaphore
   to slot index. Length is OS_MAX_TASKS - OS_N_SYS_TASKS = 61. *)
Definition sem_cap_ty := list int32.

Module absemb.
  Definition B : Set := (infoeid * sem_tp * sem_cap_ty)%type. 
  Definition holder : B := (infonull, (Int.repr 2), repeat Int.zero 61).
End absemb.

Module EmbMod := MapLib.MapFun idxspec absemb. 

Definition Pos := int32 .

Program Instance EmbMap: PermMap Pos (infoeid * sem_tp * sem_cap_ty) EmbMod.map := 
 {
    usePerm := EmbMod.usePerm;
    isRw := EmbMod.isRw;
    flip := EmbMod.flip;
    sameV := EmbMod.sameV;
    same := EmbMod.same;
    emp := EmbMod.emp;
    join := EmbMod.join;
    del := EmbMod.del;
    get := EmbMod.get;
    set := EmbMod.set;
    sig := EmbMod.sig;
    merge := EmbMod.merge;
    minus := EmbMod.minus;
    map_dec_a := EmbMod.map_dec_a
}.

Next Obligation.
  apply EmbMod.map_join_emp.
Qed.
Next Obligation.
  apply EmbMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply EmbMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply EmbMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply EmbMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply EmbMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply EmbMod.map_eql; auto.
Qed.
Next Obligation.
  apply EmbMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply EmbMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply EmbMod.map_get_sig.
Qed.
Next Obligation.
  apply EmbMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply EmbMod.map_get_set.
Qed.
Next Obligation.
  apply EmbMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply EmbMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply EmbMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply EmbMod.map_set_emp.
Qed.
Next Obligation.
  apply EmbMod.map_set_sig.
Qed.
Next Obligation.
  apply EmbMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply EmbMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply EmbMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply EmbMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply EmbMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply EmbMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply EmbMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply EmbMod.map_del_sem.
Qed.

(* Module about absmuxinfo *)

Definition muxtype := int32.

Inductive eid_type : Type :=
  Null | Holder | Valid_Addr: tid -> eid_type.

(* Mapping from priority of tasks owning capability to the mutex
   to slot index. Length is OS_MAX_TASKS - OS_N_SYS_TASK = 61. *)
Definition mux_cap_ty := list int32.

Module absmuxinfob.
  Definition B := ( eid_type * owner * muxtype * rec_cnt * prot * prioc * wq * cnsa * mux_cap_ty)%type.
  Definition holder : B := ( Null, None,  Int.zero, Int.zero, Int.zero, Int.zero, Int.zero, Int.zero, repeat Int.zero 61).
End absmuxinfob.


Module MibMod := MapLib.MapFun idxspec absmuxinfob.

Program Instance MibMap: PermMap Pos (eid_type * owner * muxtype * rec_cnt  * prot * prioc * wq * cnsa * mux_cap_ty) MibMod.map :=
  {
    usePerm := MibMod.usePerm;
    isRw := MibMod.isRw;
    flip :=MibMod.flip;
    sameV := MibMod.sameV;
    same := MibMod.same;
    emp := MibMod.emp;
    join := MibMod.join;
    del := MibMod.del;
    get := MibMod.get;
    set := MibMod.set;
    sig := MibMod.sig;
    merge := MibMod.merge;
    minus := MibMod.minus;
    map_dec_a := MibMod.map_dec_a
  }.
Next Obligation.
  apply MibMod.map_join_emp.
Qed.
Next Obligation.
  apply MibMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply MibMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply MibMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply MibMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply MibMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply MibMod.map_eql; auto.
Qed.
Next Obligation.
  apply MibMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply MibMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply MibMod.map_get_sig. 
Qed.
Next Obligation.
  apply MibMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply MibMod.map_get_set.
Qed.
Next Obligation.
  apply MibMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply MibMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply MibMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply MibMod.map_set_emp.
Qed.
Next Obligation.
  apply MibMod.map_set_sig.
Qed.
Next Obligation.
  apply MibMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply MibMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply MibMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply MibMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply MibMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply MibMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply MibMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply MibMod.map_del_sem.
Qed.

(* Module about absmqattr *)

(* Mapping from priority of task owning capability to the queue
   to slot index. Length is OS_MAX_TASKS - OS_N_SYS_TASKS = 61. *)
Definition mq_cap_ty := list int32.

Module absqattrb.
  Definition B: Set :=  (eid_type * q_waittype * q_flags * q_maxmsg * q_msgsize * q_curmsgs * mq_cap_ty)%type. 
  Definition holder : B := (Null, Int.zero, Int.zero, Int.zero, Int.zero, Int.zero, repeat Int.zero 61). 
End absqattrb.

Module MqattrMod := MapLib.MapFun idxspec absqattrb.

Program Instance MqattrMap:
  PermMap pos (eid_type * q_waittype * q_flags * q_maxmsg * q_msgsize * q_curmsgs * mq_cap_ty) MqattrMod.map :=
  {
    usePerm := MqattrMod.usePerm;
    isRw := MqattrMod.isRw;
    flip :=MqattrMod.flip;
    sameV := MqattrMod.sameV;
    same := MqattrMod.same;
    emp := MqattrMod.emp;
    join := MqattrMod.join;
    del := MqattrMod.del;
    get := MqattrMod.get;
    set := MqattrMod.set;
    sig := MqattrMod.sig;
    merge := MqattrMod.merge;
    minus := MqattrMod.minus;
    map_dec_a := MqattrMod.map_dec_a
  }.
Next Obligation.
  apply MqattrMod.map_join_emp.
Qed.
Next Obligation.
  apply MqattrMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply MqattrMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply MqattrMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply MqattrMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply MqattrMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply MqattrMod.map_eql; auto.
Qed.
Next Obligation.
  apply MqattrMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply MqattrMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply MqattrMod.map_get_sig.
Qed.
Next Obligation.
  apply MqattrMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply MqattrMod.map_get_set.
Qed.
Next Obligation.
  apply MqattrMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply MqattrMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply MqattrMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply MqattrMod.map_set_emp.
Qed.
Next Obligation.
  apply MqattrMod.map_set_sig.
Qed.
Next Obligation.
  apply MqattrMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply MqattrMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply MqattrMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply MqattrMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply MqattrMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply MqattrMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply MqattrMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply MqattrMod.map_del_sem.
Qed.

(* Module about absposblk *)

Module abspb.
  Definition B : Set := Pos%type. 
  Definition holder : B := Int.zero.  
End abspb. 

Module PbMod := MapLib.MapFun tidspec abspb. 

Program Instance PbMap: PermMap tid Pos PbMod.map := 
 {
    usePerm := EmbMod.usePerm;
    isRw := PbMod.isRw;
    flip := PbMod.flip;
    sameV := PbMod.sameV;
    same := PbMod.same;
    emp := PbMod.emp;
    join := PbMod.join;
    del := PbMod.del;
    get := PbMod.get;
    set := PbMod.set;
    sig := PbMod.sig;
    merge := PbMod.merge;
    minus := PbMod.minus;
    map_dec_a := PbMod.map_dec_a 
}.

Next Obligation.
  apply PbMod.map_join_emp.
Qed.
Next Obligation.
  apply PbMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply PbMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply PbMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply PbMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply PbMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply PbMod.map_eql; auto.
Qed.
Next Obligation.
  apply PbMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply PbMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply PbMod.map_get_sig.
Qed.
Next Obligation.
  apply PbMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply PbMod.map_get_set.
Qed.
Next Obligation.
  apply PbMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply PbMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply PbMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply PbMod.map_set_emp.
Qed.
Next Obligation.
  apply PbMod.map_set_sig.
Qed.
Next Obligation.
  apply PbMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply PbMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply PbMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply PbMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply PbMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply PbMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply PbMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply PbMod.map_del_sem.
Qed.

(* Module about abserrblk *)

Definition Err := int32 .

Module abserrb.
  Definition B : Set := Pos%type. 
  Definition holder : B := Int.zero.  
End abserrb. 

Module EbMod := MapLib.MapFun tidspec abserrb. 

Program Instance EbMap: PermMap tid Err EbMod.map := 
 {
    usePerm := EbMod.usePerm;
    isRw := EbMod.isRw;
    flip := EbMod.flip;
    sameV := EbMod.sameV;
    same := EbMod.same;
    emp := EbMod.emp;
    join := EbMod.join;
    del := EbMod.del;
    get := EbMod.get;
    set := EbMod.set;
    sig := EbMod.sig;
    merge := EbMod.merge;
    minus := EbMod.minus;
    map_dec_a := EbMod.map_dec_a 
}.

Next Obligation.
  apply EbMod.map_join_emp.
Qed.
Next Obligation.
  apply EbMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply EbMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply EbMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply EbMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply EbMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply EbMod.map_eql; auto.
Qed.
Next Obligation.
  apply EbMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply EbMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply EbMod.map_get_sig.
Qed.
Next Obligation.
  apply EbMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply EbMod.map_get_set.
Qed.
Next Obligation.
  apply EbMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply EbMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply EbMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply EbMod.map_set_emp.
Qed.
Next Obligation.
  apply EbMod.map_set_sig.
Qed.
Next Obligation.
  apply EbMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply EbMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply EbMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply EbMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply EbMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply EbMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply EbMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply EbMod.map_del_sem.
Qed.

(* Module about abstract OSTCBPrioTbl block *)

Module absptb.
  Definition B := ( eid_type )%type.
  Definition holder : B := ( Null ).
End absptb.

Module PtbMod := MapLib.MapFun idxspec absptb. 

Program Instance PtbMap: PermMap Pos ( eid_type ) PtbMod.map := 
 {
    usePerm := PtbMod.usePerm;
    isRw := PtbMod.isRw;
    flip := PtbMod.flip;
    sameV := PtbMod.sameV;
    same := PtbMod.same;
    emp := PtbMod.emp;
    join := PtbMod.join;
    del := PtbMod.del;
    get := PtbMod.get;
    set := PtbMod.set;
    sig := PtbMod.sig;
    merge := PtbMod.merge;
    minus := PtbMod.minus;
    map_dec_a := PtbMod.map_dec_a 
}.

Next Obligation.
  apply PtbMod.map_join_emp.
Qed.
Next Obligation.
  apply PtbMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply PtbMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply PtbMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply PtbMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply PtbMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply PtbMod.map_eql; auto.
Qed.
Next Obligation.
  apply PtbMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply PtbMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply PtbMod.map_get_sig.
Qed.
Next Obligation.
  apply PtbMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply PtbMod.map_get_set.
Qed.
Next Obligation.
  apply PtbMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply PtbMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply PtbMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply PtbMod.map_set_emp.
Qed.
Next Obligation.
  apply PtbMod.map_set_sig.
Qed.
Next Obligation.
  apply PtbMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply PtbMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply PtbMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply PtbMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply PtbMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply PtbMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply PtbMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply PtbMod.map_del_sem.
Qed.

(* Module about abstract auxiliary variable about event location *)

Module absevauxloc.
  Definition B : Set := val. 
  Definition holder : B := Vundef.  
End absevauxloc. 

Module EvAuxLocMod := MapLib.MapFun tidspec absevauxloc. 

Program Instance EvAuxLocMap: PermMap tid val EvAuxLocMod.map := 
 {
    usePerm := EvAuxLocMod.usePerm;
    isRw := EvAuxLocMod.isRw;
    flip := EvAuxLocMod.flip;
    sameV := EvAuxLocMod.sameV;
    same := EvAuxLocMod.same;
    emp := EvAuxLocMod.emp;
    join := EvAuxLocMod.join;
    del := EvAuxLocMod.del;
    get := EvAuxLocMod.get;
    set := EvAuxLocMod.set;
    sig := EvAuxLocMod.sig;
    merge := EvAuxLocMod.merge;
    minus := EvAuxLocMod.minus;
    map_dec_a := EvAuxLocMod.map_dec_a
}.

Next Obligation.
  apply EvAuxLocMod.map_join_emp.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply EvAuxLocMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply EvAuxLocMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply EvAuxLocMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_eql; auto.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply EvAuxLocMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_get_sig.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_get_set.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply EvAuxLocMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply EvAuxLocMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_set_emp.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_set_sig.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply EvAuxLocMod.map_del_sem.
Qed.

(* Module about abstract auxiliary variable about event  pointer *)

Module absevauxptr.
  Definition B : Set := val * val * val. 
  Definition holder : B := (Vundef, Vundef, Vundef).  
End absevauxptr. 

Module EvAuxPtrMod := MapLib.MapFun tidspec absevauxptr. 

Program Instance EvAuxPtrMap: PermMap tid (val * val * val) EvAuxPtrMod.map := 
 {
    usePerm := EvAuxPtrMod.usePerm;
    isRw := EvAuxPtrMod.isRw;
    flip := EvAuxPtrMod.flip;
    sameV := EvAuxPtrMod.sameV;
    same := EvAuxPtrMod.same;
    emp := EvAuxPtrMod.emp;
    join := EvAuxPtrMod.join;
    del := EvAuxPtrMod.del;
    get := EvAuxPtrMod.get;
    set := EvAuxPtrMod.set;
    sig := EvAuxPtrMod.sig;
    merge := EvAuxPtrMod.merge;
    minus := EvAuxPtrMod.minus;
    map_dec_a := EvAuxPtrMod.map_dec_a
}.

Next Obligation.
  apply EvAuxPtrMod.map_join_emp.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply EvAuxPtrMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply EvAuxPtrMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply EvAuxPtrMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_eql; auto.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply EvAuxPtrMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_get_sig.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_get_set.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply EvAuxPtrMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply EvAuxPtrMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_set_emp.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_set_sig.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply EvAuxPtrMod.map_del_sem.
Qed. 
(********************* end add by CNU *********************) 

(* ---------------------------------- content about partition ----------------------------------------- *)
(* ---------------------------------- add by CNU ------------------------------------------------------- *)

Definition absarea_t := ( int32 * int32 * int32 )%type.
Definition index := int32.

(* Module about absxmapx*)
Definition xmpaxl := int32.
Definition xmpaxh := int32.

Module absxmcb.
  Definition B : Set := (xmpaxl * xmpaxh)%type.
  Definition holder : B := (Int.zero, Int.zero).
End absxmcb.

Module XmcMod := MapLib.MapFun idxspec absxmcb.

Program Instance XmcMap : PermMap index (xmpaxl * xmpaxh) XmcMod.map :=
  {
    usePerm := XmcMod.usePerm;
    isRw := XmcMod.isRw;
    flip := XmcMod.flip;
    sameV := XmcMod.sameV;
    same := XmcMod.same;
    emp := XmcMod.emp;
    join := XmcMod.join;
    del := XmcMod.del;
    get := XmcMod.get;
    set := XmcMod.set;
    sig := XmcMod.sig;
    merge := XmcMod.merge;
    minus := XmcMod.minus;
    map_dec_a := XmcMod.map_dec_a
}.

Next Obligation.
  apply XmcMod.map_join_emp.
Qed.
Next Obligation.
  apply XmcMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply XmcMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply XmcMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply XmcMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply XmcMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply XmcMod.map_eql; auto.
Qed.
Next Obligation.
  apply XmcMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply XmcMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply XmcMod.map_get_sig.
Qed.
Next Obligation.
  apply XmcMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply XmcMod.map_get_set.
Qed.
Next Obligation.
  apply XmcMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply XmcMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply XmcMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply XmcMod.map_set_emp.
Qed.
Next Obligation.
  apply XmcMod.map_set_sig.
Qed.
Next Obligation.
  apply XmcMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply XmcMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply XmcMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply XmcMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply XmcMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply XmcMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply XmcMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply XmcMod.map_del_sem.
Qed.

(* Module about abssms_mapx*)

Definition smsmpaxl := int32.
Definition smsmpaxh := int32.

Module abssmsb.
  Definition B : Set := (smsmpaxl * smsmpaxh)%type.
  Definition holder : B := (Int.zero, Int.zero).
End abssmsb.

Module SmsMod := MapLib.MapFun idxspec abssmsb.

Program Instance SmsMap : PermMap index (smsmpaxl * smsmpaxh) SmsMod.map :=
  {
    usePerm := SmsMod.usePerm;
    isRw := SmsMod.isRw;
    flip := SmsMod.flip;
    sameV := SmsMod.sameV;
    same := SmsMod.same;
    emp := SmsMod.emp;
    join := SmsMod.join;
    del := SmsMod.del;
    get := SmsMod.get;
    set := SmsMod.set;
    sig := SmsMod.sig;
    merge := SmsMod.merge;
    minus := SmsMod.minus;
    map_dec_a := SmsMod.map_dec_a
}.

Next Obligation.
  apply SmsMod.map_join_emp.
Qed.
Next Obligation.
  apply SmsMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply SmsMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply SmsMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply SmsMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply SmsMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply SmsMod.map_eql; auto.
Qed.
Next Obligation.
  apply SmsMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply SmsMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply SmsMod.map_get_sig.
Qed.
Next Obligation.
  apply SmsMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply SmsMod.map_get_set.
Qed.
Next Obligation.
  apply SmsMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply SmsMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply SmsMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply SmsMod.map_set_emp.
Qed.
Next Obligation.
  apply SmsMod.map_set_sig.
Qed.
Next Obligation.
  apply SmsMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply SmsMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply SmsMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply SmsMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply SmsMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply SmsMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply SmsMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply SmsMod.map_del_sem.
Qed.

(* Module about absses_mapx*)

Definition sesmpaxl := int32.
Definition sesmpaxh := int32.

Module abssesb.
  Definition B : Set := (sesmpaxl * sesmpaxh)%type.
  Definition holder : B := (Int.zero, Int.zero).
End abssesb.

Module SesMod := MapLib.MapFun idxspec abssesb.

Program Instance SesMap : PermMap index (sesmpaxl * sesmpaxh) SesMod.map :=
  {
    usePerm := SesMod.usePerm;
    isRw := SesMod.isRw;
    flip := SesMod.flip;
    sameV := SesMod.sameV;
    same := SesMod.same;
    emp := SesMod.emp;
    join := SesMod.join;
    del := SesMod.del;
    get := SesMod.get;
    set := SesMod.set;
    sig := SesMod.sig;
    merge := SesMod.merge;
    minus := SesMod.minus;
    map_dec_a := SesMod.map_dec_a
}.

Next Obligation.
  apply SesMod.map_join_emp.
Qed.
Next Obligation.
  apply SesMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply SesMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply SesMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply SesMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply SesMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply SesMod.map_eql; auto.
Qed.
Next Obligation.
  apply SesMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply SesMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply SesMod.map_get_sig.
Qed.
Next Obligation.
  apply SesMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply SesMod.map_get_set.
Qed.
Next Obligation.
  apply SesMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply SesMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply SesMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply SesMod.map_set_emp.
Qed.
Next Obligation.
  apply SesMod.map_set_sig.
Qed.
Next Obligation.
  apply SesMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply SesMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply SesMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply SesMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply SesMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply SesMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply SesMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply SesMod.map_del_sem.
Qed.

(* variables about Domain *)

Definition  ksdscdidx := int32.
Definition  ksdscdlen := int32.
Definition  kscur := int32.
Definition  kslast := int32.
Definition  ksdtime := int32.

(* Module about abstract KsDomSchedule block *)

Module absdomscd.
  Definition B : Set := int32 * int32.
  Definition holder : B := (Int.zero, Int.zero).
End absdomscd.

Module KsDScdMod := MapLib.MapFun idxspec absdomscd.

Program Instance KsDScdMap: PermMap Pos ( int32 * int32 ) KsDScdMod.map := 
 {
    usePerm := KsDScdMod.usePerm;
    isRw := KsDScdMod.isRw;
    flip := KsDScdMod.flip;
    sameV := KsDScdMod.sameV;
    same := KsDScdMod.same;
    emp := KsDScdMod.emp;
    join := KsDScdMod.join;
    del := KsDScdMod.del;
    get := KsDScdMod.get;
    set := KsDScdMod.set;
    sig := KsDScdMod.sig;
    merge := KsDScdMod.merge;
    minus := KsDScdMod.minus;
    map_dec_a := KsDScdMod.map_dec_a 
}.

Next Obligation.
  apply KsDScdMod.map_join_emp.
Qed.
Next Obligation.
  apply KsDScdMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply KsDScdMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply KsDScdMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply KsDScdMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply KsDScdMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply KsDScdMod.map_eql; auto.
Qed.
Next Obligation.
  apply KsDScdMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply KsDScdMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply KsDScdMod.map_get_sig.
Qed.
Next Obligation.
  apply KsDScdMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply KsDScdMod.map_get_set.
Qed.
Next Obligation.
  apply KsDScdMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply KsDScdMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply KsDScdMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply KsDScdMod.map_set_emp.
Qed.
Next Obligation.
  apply KsDScdMod.map_set_sig.
Qed.
Next Obligation.
  apply KsDScdMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply KsDScdMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply KsDScdMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply KsDScdMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply KsDScdMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply KsDScdMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply KsDScdMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply KsDScdMod.map_del_sem.
Qed.

(*------------------------------------- content about ucos_conf_t -----------------------*)

(* Module about deviceId *)
Definition devid :=int32.

Module absdevID.
  Definition B : Set := int. 
  Definition holder : B := Int.zero.  
End absdevID.

Module DevIDMod := MapLib.MapFun idxspec absdevID. 

Program Instance DevIDMap: PermMap devid int DevIDMod.map := 
 {
    usePerm := DevIDMod.usePerm;
    isRw := DevIDMod.isRw;
    flip := DevIDMod.flip;
    sameV := DevIDMod.sameV;
    same := DevIDMod.same;
    emp := DevIDMod.emp;
    join := DevIDMod.join;
    del := DevIDMod.del;
    get := DevIDMod.get;
    set := DevIDMod.set;
    sig := DevIDMod.sig;
    merge := DevIDMod.merge;
    minus := DevIDMod.minus;
    map_dec_a := DevIDMod.map_dec_a 
}.

Next Obligation.
  apply DevIDMod.map_join_emp.
Qed.
Next Obligation.
  apply DevIDMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply DevIDMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply DevIDMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply DevIDMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply DevIDMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply DevIDMod.map_eql; auto.
Qed.
Next Obligation.
  apply DevIDMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply DevIDMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply DevIDMod.map_get_sig.
Qed.
Next Obligation.
  apply DevIDMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply DevIDMod.map_get_set.
Qed.
Next Obligation.
  apply DevIDMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply DevIDMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply DevIDMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply DevIDMod.map_set_emp.
Qed.
Next Obligation.
  apply DevIDMod.map_set_sig.
Qed.
Next Obligation.
  apply DevIDMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply DevIDMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply DevIDMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply DevIDMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply DevIDMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply DevIDMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply DevIDMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply DevIDMod.map_del_sem.
Qed.

(* Module about deviceioconf *)
Definition conf := int32.
Definition DcfstartAddr :=int32.
Definition Dcfdeviceio_size :=int32.

Module deviceioconf.
  Definition B := (DcfstartAddr * Dcfdeviceio_size * DevIDMod.map)%type.
  Definition holder : B := (Int.zero, Int.zero, DevIDMod.emp).
End deviceioconf.

Module DevMod := MapLib.MapFun idxspec deviceioconf.

Program Instance DevMap: PermMap conf (DcfstartAddr * Dcfdeviceio_size * DevIDMod.map) DevMod.map :=
  {
    usePerm := DevMod.usePerm;
    isRw := DevMod.isRw;
    flip :=DevMod.flip;
    sameV := DevMod.sameV;
    same := DevMod.same;
    emp := DevMod.emp;
    join := DevMod.join;
    del := DevMod.del;
    get := DevMod.get;
    set := DevMod.set;
    sig := DevMod.sig;
    merge := DevMod.merge;
    minus := DevMod.minus;
    map_dec_a := DevMod.map_dec_a
  }.
Next Obligation.
  apply DevMod.map_join_emp.
Qed.
Next Obligation.
  apply DevMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply DevMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply DevMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply DevMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply DevMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply DevMod.map_eql; auto.
Qed.
Next Obligation.
  apply DevMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply DevMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply DevMod.map_get_sig. 
Qed.
Next Obligation.
  apply DevMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply DevMod.map_get_set.
Qed.
Next Obligation.
  apply DevMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply DevMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply DevMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply DevMod.map_set_emp.
Qed.
Next Obligation.
  apply DevMod.map_set_sig.
Qed.
Next Obligation.
  apply DevMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply DevMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply DevMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply DevMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply DevMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply DevMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply DevMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply DevMod.map_del_sem.
Qed.

(* Module about portrdytbl *)
Module portrdytbl.
  Definition B : Set := int. 
  Definition holder : B := Int.zero.  
End portrdytbl.

Module PortRdyTblMod := MapLib.MapFun idxspec portrdytbl. 

Program Instance PortRdyTblMap: PermMap conf int PortRdyTblMod.map := 
 {
    usePerm := PortRdyTblMod.usePerm;
    isRw := PortRdyTblMod.isRw;
    flip := PortRdyTblMod.flip;
    sameV := PortRdyTblMod.sameV;
    same := PortRdyTblMod.same;
    emp := PortRdyTblMod.emp;
    join := PortRdyTblMod.join;
    del := PortRdyTblMod.del;
    get := PortRdyTblMod.get;
    set := PortRdyTblMod.set;
    sig := PortRdyTblMod.sig;
    merge := PortRdyTblMod.merge;
    minus := PortRdyTblMod.minus;
    map_dec_a := PortRdyTblMod.map_dec_a 
}.

Next Obligation.
  apply PortRdyTblMod.map_join_emp.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply PortRdyTblMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply PortRdyTblMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply PortRdyTblMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_eql; auto.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply PortRdyTblMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_get_sig.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_get_set.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply PortRdyTblMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply PortRdyTblMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_set_emp.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_set_sig.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply PortRdyTblMod.map_del_sem.
Qed.

(* Module about Capconft *)

Definition   ccfTaskEn := int32. 
Definition   ccfPartitionEn := int32.
Definition   ccfInterCommEn := int32.
Definition   ccfIntraCommSemEn := int32.
Definition   ccfIntraCommMutexEn := int32.
Definition   ccfIntraCommQueueEn := int32.

Module capconft.
  Definition B : Set:= (ccfTaskEn * ccfPartitionEn * ccfInterCommEn * ccfIntraCommSemEn *
                        ccfIntraCommMutexEn * ccfIntraCommQueueEn)%type.
  Definition holder : B := (Int.zero, Int.zero, Int.zero, Int.zero, Int.zero, Int.zero).
End capconft.

Module CapTblMod := MapLib.MapFun idxspec capconft.

Program Instance CapTblMap: PermMap conf (ccfTaskEn * ccfPartitionEn * ccfInterCommEn *
 ccfIntraCommSemEn * ccfIntraCommMutexEn * ccfIntraCommQueueEn) CapTblMod.map :=
  {
    usePerm := CapTblMod.usePerm;
    isRw := CapTblMod.isRw;
    flip := CapTblMod.flip;
    sameV := CapTblMod.sameV;
    same := CapTblMod.same;
    emp := CapTblMod.emp;
    join := CapTblMod.join;
    del := CapTblMod.del;
    get := CapTblMod.get;
    set := CapTblMod.set;
    sig := CapTblMod.sig;
    merge := CapTblMod.merge;
    minus := CapTblMod.minus;
    map_dec_a := CapTblMod.map_dec_a
  }.
Next Obligation.
  apply CapTblMod.map_join_emp.
Qed.
Next Obligation.
  apply CapTblMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply CapTblMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply CapTblMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply CapTblMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply CapTblMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply CapTblMod.map_eql; auto.
Qed.
Next Obligation.
  apply CapTblMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply CapTblMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply CapTblMod.map_get_sig. 
Qed.
Next Obligation.
  apply CapTblMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply CapTblMod.map_get_set.
Qed.
Next Obligation.
  apply CapTblMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply CapTblMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply CapTblMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply CapTblMod.map_set_emp.
Qed.
Next Obligation.
  apply CapTblMod.map_set_sig.
Qed.
Next Obligation.
  apply CapTblMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply CapTblMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply CapTblMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply CapTblMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply CapTblMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply CapTblMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply CapTblMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply CapTblMod.map_del_sem.
Qed.

(* Module about domainconft*)

Definition   Dcfdomain := int32.
Definition   DcfcoreId := int32.
Definition   DcfID := int32.
Definition   DcfbinAddress := int32.
Definition   DcfRootTaskPrio := int32.
Definition   DcfOSPartitionPeriod := int32.
Definition   DcfpAddress := int32.
Definition   DcfvAddress := int32.
Definition   Dcflen := int32.
Definition   Dcfdomain_size := int32. 
Definition   Dcfstatus := int32.
Definition   DcfportRdyGrp := int32.
Definition   DcfDeviceNum := int32.

Module domainconft.
  Definition B := (Dcfdomain * DcfcoreId * DcfID * DcfbinAddress * DcfRootTaskPrio *
                   DcfOSPartitionPeriod * DcfpAddress * DcfvAddress * Dcflen *
                   Dcfdomain_size * Dcfstatus * DcfportRdyGrp * DcfDeviceNum *
                   PortRdyTblMod.map * DevMod.map * CapTblMod.map)%type.
  Definition holder : B := (Int.zero, Int.zero, Int.zero, Int.zero, Int.zero, Int.zero,
                            Int.zero, Int.zero, Int.zero, Int.zero, Int.zero, Int.zero,
                            Int.zero, PortRdyTblMod.emp, DevMod.emp, CapTblMod.emp).
End domainconft.

Module DomCTMod := MapLib.MapFun idxspec domainconft.

Program Instance DomCTMap: PermMap conf (Dcfdomain * DcfcoreId * DcfID * DcfbinAddress * 
                                         DcfRootTaskPrio * DcfOSPartitionPeriod *
                                         DcfpAddress * DcfvAddress * Dcflen *
                                         Dcfdomain_size * Dcfstatus * DcfportRdyGrp *
                                         DcfDeviceNum * PortRdyTblMod.map * DevMod.map *
                                         CapTblMod.map) DomCTMod.map :=
  {
    usePerm := DomCTMod.usePerm;
    isRw := DomCTMod.isRw;
    flip := DomCTMod.flip;
    sameV := DomCTMod.sameV;
    same := DomCTMod.same;
    emp := DomCTMod.emp;
    join := DomCTMod.join;
    del := DomCTMod.del;
    get := DomCTMod.get;
    set := DomCTMod.set;
    sig := DomCTMod.sig;
    merge := DomCTMod.merge;
    minus := DomCTMod.minus;
    map_dec_a := DomCTMod.map_dec_a
  }.
Next Obligation.
  apply DomCTMod.map_join_emp.
Qed.
Next Obligation.
  apply DomCTMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply DomCTMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply DomCTMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply DomCTMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply DomCTMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply DomCTMod.map_eql; auto.
Qed.
Next Obligation.
  apply DomCTMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply DomCTMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply DomCTMod.map_get_sig. 
Qed.
Next Obligation.
  apply DomCTMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply DomCTMod.map_get_set.
Qed.
Next Obligation.
  apply DomCTMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply DomCTMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply DomCTMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply DomCTMod.map_set_emp.
Qed.
Next Obligation.
  apply DomCTMod.map_set_sig.
Qed.
Next Obligation.
  apply DomCTMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply DomCTMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply DomCTMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply DomCTMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply DomCTMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply DomCTMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply DomCTMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply DomCTMod.map_del_sem.
Qed.

(* Module about dschedule_conf_t*)
Definition DSlength := int32.
Definition DSdomain := int32.

Module dscheduleconft.
  Definition B : Set:= (DSdomain * DSlength)%type.
  Definition holder : B := (Int.zero, Int.zero).
End dscheduleconft.

Module DSchMod := MapLib.MapFun idxspec dscheduleconft.

Program Instance DSchMap: PermMap conf (DSdomain * DSlength) DSchMod.map :=
  {
    usePerm := DSchMod.usePerm;
    isRw := DSchMod.isRw;
    flip := DSchMod.flip;
    sameV := DSchMod.sameV;
    same := DSchMod.same;
    emp := DSchMod.emp;
    join := DSchMod.join;
    del := DSchMod.del;
    get := DSchMod.get;
    set := DSchMod.set;
    sig := DSchMod.sig;
    merge := DSchMod.merge;
    minus := DSchMod.minus;
    map_dec_a := DSchMod.map_dec_a
  }.
Next Obligation.
  apply DSchMod.map_join_emp.
Qed.
Next Obligation.
  apply DSchMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply DSchMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply DSchMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply DSchMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply DSchMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply DSchMod.map_eql; auto.
Qed.
Next Obligation.
  apply DSchMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply DSchMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply DSchMod.map_get_sig. 
Qed.
Next Obligation.
  apply DSchMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply DSchMod.map_get_set.
Qed.
Next Obligation.
  apply DSchMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply DSchMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply DSchMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply DSchMod.map_set_emp.
Qed.
Next Obligation.
  apply DSchMod.map_set_sig.
Qed.
Next Obligation.
  apply DSchMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply DSchMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply DSchMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply DSchMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply DSchMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply DSchMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply DSchMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply DSchMod.map_del_sem.
Qed.

(* Module about domianRdy*)
Definition domRdy := int32.

Module absdomRdy.
  Definition B := int.
  Definition holder : B := Int.zero.
End absdomRdy.

Module DomRdyMod := MapLib.MapFun idxspec absdomRdy.

Program Instance DomRdyMap: PermMap domRdy int DomRdyMod.map :=
  {
    usePerm := DomRdyMod.usePerm;
    isRw := DomRdyMod.isRw;
    flip := DomRdyMod.flip;
    sameV := DomRdyMod.sameV;
    same := DomRdyMod.same;
    emp := DomRdyMod.emp;
    join := DomRdyMod.join;
    del := DomRdyMod.del;
    get := DomRdyMod.get;
    set := DomRdyMod.set;
    sig := DomRdyMod.sig;
    merge := DomRdyMod.merge;
    minus := DomRdyMod.minus;
    map_dec_a := DomRdyMod.map_dec_a
  }.
Next Obligation.
  apply DomRdyMod.map_join_emp.
Qed.
Next Obligation.
  apply DomRdyMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply DomRdyMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply DomRdyMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply DomRdyMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply DomRdyMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply DomRdyMod.map_eql; auto.
Qed.
Next Obligation.
  apply DomRdyMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply DomRdyMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply DomRdyMod.map_get_sig. 
Qed.
Next Obligation.
  apply DomRdyMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply DomRdyMod.map_get_set.
Qed.
Next Obligation.
  apply DomRdyMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply DomRdyMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply DomRdyMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply DomRdyMod.map_set_emp.
Qed.
Next Obligation.
  apply DomRdyMod.map_set_sig.
Qed.
Next Obligation.
  apply DomRdyMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply DomRdyMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply DomRdyMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply DomRdyMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply DomRdyMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply DomRdyMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply DomRdyMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply DomRdyMod.map_del_sem.
Qed.

(* Module about cpuconft*)
Definition CPUcore := int32.
Definition CPUksDomScheduleLength := int32.
Definition CPUksDomainLength :=int32.

Module cpuconft.
  Definition B := (CPUcore * CPUksDomScheduleLength * CPUksDomainLength * 
                                    DomRdyMod.map * DSchMod.map * DomCTMod.map)%type.
  Definition holder : B := (Int.zero, Int.zero, Int.zero, DomRdyMod.emp, DSchMod.emp,
                                                    DomCTMod.emp ).
End cpuconft.

Module CPUsMod := MapLib.MapFun idxspec cpuconft.

Program Instance CPUsMap: PermMap conf (CPUcore * CPUksDomScheduleLength *
                                         CPUksDomainLength * DomRdyMod.map * 
                                         DSchMod.map * DomCTMod.map) CPUsMod.map :=
  {
    usePerm := CPUsMod.usePerm;
    isRw := CPUsMod.isRw;
    flip := CPUsMod.flip;
    sameV := CPUsMod.sameV;
    same := CPUsMod.same;
    emp := CPUsMod.emp;
    join := CPUsMod.join;
    del := CPUsMod.del;
    get := CPUsMod.get;
    set := CPUsMod.set;
    sig := CPUsMod.sig;
    merge := CPUsMod.merge;
    minus := CPUsMod.minus;
    map_dec_a := CPUsMod.map_dec_a
  }.
Next Obligation.
  apply CPUsMod.map_join_emp.
Qed.
Next Obligation.
  apply CPUsMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply CPUsMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply CPUsMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply CPUsMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply CPUsMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply CPUsMod.map_eql; auto.
Qed.
Next Obligation.
  apply CPUsMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply CPUsMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply CPUsMod.map_get_sig. 
Qed.
Next Obligation.
  apply CPUsMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply CPUsMod.map_get_set.
Qed.
Next Obligation.
  apply CPUsMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply CPUsMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply CPUsMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply CPUsMod.map_set_emp.
Qed.
Next Obligation.
  apply CPUsMod.map_set_sig.
Qed.
Next Obligation.
  apply CPUsMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply CPUsMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply CPUsMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply CPUsMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply CPUsMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply CPUsMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply CPUsMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply CPUsMod.map_del_sem.
Qed.

(* Module about dstTbl *)
Module absdstTbl.
  Definition B : Set := int. 
  Definition holder : B := Int.zero.
End absdstTbl.

Module DstTblMod := MapLib.MapFun idxspec absdstTbl. 

Program Instance DstTblMap: PermMap conf int DstTblMod.map := 
 {
    usePerm := DstTblMod.usePerm;
    isRw := DstTblMod.isRw;
    flip := DstTblMod.flip;
    sameV := DstTblMod.sameV;
    same := DstTblMod.same;
    emp := DstTblMod.emp;
    join := DstTblMod.join;
    del := DstTblMod.del;
    get := DstTblMod.get;
    set := DstTblMod.set;
    sig := DstTblMod.sig;
    merge := DstTblMod.merge;
    minus := DstTblMod.minus;
    map_dec_a := DstTblMod.map_dec_a 
}.

Next Obligation.
  apply DstTblMod.map_join_emp.
Qed.
Next Obligation.
  apply DstTblMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply DstTblMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply DstTblMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply DstTblMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply DstTblMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply DstTblMod.map_eql; auto.
Qed.
Next Obligation.
  apply DstTblMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply DstTblMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply DstTblMod.map_get_sig.
Qed.
Next Obligation.
  apply DstTblMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply DstTblMod.map_get_set.
Qed.
Next Obligation.
  apply DstTblMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply DstTblMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply DstTblMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply DstTblMod.map_set_emp.
Qed.
Next Obligation.
  apply DstTblMod.map_set_sig.
Qed.
Next Obligation.
  apply DstTblMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply DstTblMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply DstTblMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply DstTblMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply DstTblMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply DstTblMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply DstTblMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply DstTblMod.map_del_sem.
Qed.

(* Module about channelconft*)
Definition ChfcoreType := int32. 
Definition ChfID := int32. 
Definition ChfchannelType :=int32.
Definition ChfsrcportID :=int32.
Definition ChfdstGrp :=int32.

Module channelconft.
  Definition B := (ChfcoreType * ChfID * ChfchannelType * ChfsrcportID * 
                   ChfdstGrp * DstTblMod.map)%type.
  Definition holder : B := (Int.zero, Int.zero, Int.zero, Int.zero, 
                            Int.zero, DstTblMod.emp).
End channelconft.

Module ChanCFMod := MapLib.MapFun idxspec channelconft.

Program Instance ChanCFMap: PermMap conf (ChfcoreType * ChfID * ChfchannelType *
                                          ChfsrcportID * ChfdstGrp * DstTblMod.map)
                                         ChanCFMod.map :=
  {
    usePerm := ChanCFMod.usePerm;
    isRw := ChanCFMod.isRw;
    flip := ChanCFMod.flip;
    sameV := ChanCFMod.sameV;
    same := ChanCFMod.same;
    emp := ChanCFMod.emp;
    join := ChanCFMod.join;
    del := ChanCFMod.del;
    get := ChanCFMod.get;
    set := ChanCFMod.set;
    sig := ChanCFMod.sig;
    merge := ChanCFMod.merge;
    minus := ChanCFMod.minus;
    map_dec_a := ChanCFMod.map_dec_a
  }.
Next Obligation.
  apply ChanCFMod.map_join_emp.
Qed.
Next Obligation.
  apply ChanCFMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply ChanCFMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply ChanCFMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply ChanCFMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply ChanCFMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply ChanCFMod.map_eql; auto.
Qed.
Next Obligation.
  apply ChanCFMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply ChanCFMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply ChanCFMod.map_get_sig. 
Qed.
Next Obligation.
  apply ChanCFMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply ChanCFMod.map_get_set.
Qed.
Next Obligation.
  apply ChanCFMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply ChanCFMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply ChanCFMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply ChanCFMod.map_set_emp.
Qed.
Next Obligation.
  apply ChanCFMod.map_set_sig.
Qed.
Next Obligation.
  apply ChanCFMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply ChanCFMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply ChanCFMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply ChanCFMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply ChanCFMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply ChanCFMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply ChanCFMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply ChanCFMod.map_del_sem.
Qed.

(* Module about portconft*)
Definition PcfID := int32.
Definition Pcfdirection := int32.
Definition Pcfport_type :=int32.
Definition PcfpartitionID :=int32.
Definition PcfchannelID :=int32.

Module portconft.
  Definition B: Set := (PcfID * Pcfdirection * Pcfport_type * 
                        PcfpartitionID * PcfchannelID)%type.
  Definition holder : B := (Int.zero, Int.zero, Int.zero, Int.zero, Int.zero).
End portconft.

Module PortCFMod := MapLib.MapFun idxspec portconft.

Program Instance PortCFMap: PermMap conf (PcfID * Pcfdirection * Pcfport_type * 
                                          PcfpartitionID * PcfchannelID) PortCFMod.map :=
  {
    usePerm := PortCFMod.usePerm;
    isRw := PortCFMod.isRw;
    flip := PortCFMod.flip;
    sameV := PortCFMod.sameV;
    same := PortCFMod.same;
    emp := PortCFMod.emp;
    join := PortCFMod.join;
    del := PortCFMod.del;
    get := PortCFMod.get;
    set := PortCFMod.set;
    sig := PortCFMod.sig;
    merge := PortCFMod.merge;
    minus := PortCFMod.minus;
    map_dec_a := PortCFMod.map_dec_a
  }.
Next Obligation.
  apply PortCFMod.map_join_emp.
Qed.
Next Obligation.
  apply PortCFMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply PortCFMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply PortCFMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply PortCFMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply PortCFMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply PortCFMod.map_eql; auto.
Qed.
Next Obligation.
  apply PortCFMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply PortCFMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply PortCFMod.map_get_sig. 
Qed.
Next Obligation.
  apply PortCFMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply PortCFMod.map_get_set.
Qed.
Next Obligation.
  apply PortCFMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply PortCFMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply PortCFMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply PortCFMod.map_set_emp.
Qed.
Next Obligation.
  apply PortCFMod.map_set_sig.
Qed.
Next Obligation.
  apply PortCFMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply PortCFMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply PortCFMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply PortCFMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply PortCFMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply PortCFMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply PortCFMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply PortCFMod.map_del_sem.
Qed.

(* Module about IntrDomModindex *)
Definition domid := int32.

Module absintrdom.
  Definition B : Set := int. 
  Definition holder : B := Int.zero.  
End absintrdom.

Module IntrDomMod := MapLib.MapFun idxspec absintrdom. 

Program Instance IntrDomMap: PermMap domid int IntrDomMod.map := 
 {
    usePerm := IntrDomMod.usePerm;
    isRw := IntrDomMod.isRw;
    flip := IntrDomMod.flip;
    sameV := IntrDomMod.sameV;
    same := IntrDomMod.same;
    emp := IntrDomMod.emp;
    join := IntrDomMod.join;
    del := IntrDomMod.del;
    get := IntrDomMod.get;
    set := IntrDomMod.set;
    sig := IntrDomMod.sig;
    merge := IntrDomMod.merge;
    minus := IntrDomMod.minus;
    map_dec_a := IntrDomMod.map_dec_a 
}.

Next Obligation.
  apply IntrDomMod.map_join_emp.
Qed.
Next Obligation.
  apply IntrDomMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply IntrDomMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply IntrDomMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply IntrDomMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply IntrDomMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply IntrDomMod.map_eql; auto.
Qed.
Next Obligation.
  apply IntrDomMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply IntrDomMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply IntrDomMod.map_get_sig.
Qed.
Next Obligation.
  apply IntrDomMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply IntrDomMod.map_get_set.
Qed.
Next Obligation.
  apply IntrDomMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply IntrDomMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply IntrDomMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply IntrDomMod.map_set_emp.
Qed.
Next Obligation.
  apply IntrDomMod.map_set_sig.
Qed.
Next Obligation.
  apply IntrDomMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply IntrDomMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply IntrDomMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply IntrDomMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply IntrDomMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply IntrDomMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply IntrDomMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply IntrDomMod.map_del_sem.
Qed.

(* Module about ucosconft *)
Definition Ucfmagicf := int32.
Definition UcffileVersion := int32.
Definition UcfcoreNums := int32.
Definition UcfnoPartitions := int32.
Definition UcfnoPorts := int32.
Definition UcfnoCommChannels := int32.
Definition UcfportRdyGrp := int32.
Definition Ucfmagicl := int32.

Definition AcfpAddress := int32.
Definition AcfvAddress := int32.
Definition area_size :=int32.
Definition Acflen :=int32.  

Definition area := (AcfpAddress * AcfvAddress * area_size * Acflen)%type.
Definition areaholder := (Int.zero, Int.zero, Int.zero, Int.zero ).

Definition absucosconf := 
     (Ucfmagicf * UcffileVersion * UcfcoreNums * UcfnoPartitions *
      UcfnoCommChannels * UcfnoPorts * IntrDomMod.map * area *
      CPUsMod.map * ChanCFMod.map * UcfportRdyGrp * PortRdyTblMod.map *
      PortCFMod.map * Ucfmagicl)%type.

(* Module about dom2index *)

Module absdom2.
  Definition B : Set := int. 
  Definition holder : B := Int.zero.  
End absdom2.

Module Dom2IdxMod := MapLib.MapFun idxspec absdom2. 

Program Instance Dom2IdxMap: PermMap domid int Dom2IdxMod.map := 
 {
    usePerm := Dom2IdxMod.usePerm;
    isRw := Dom2IdxMod.isRw;
    flip := Dom2IdxMod.flip;
    sameV := Dom2IdxMod.sameV;
    same := Dom2IdxMod.same;
    emp := Dom2IdxMod.emp;
    join := Dom2IdxMod.join;
    del := Dom2IdxMod.del;
    get := Dom2IdxMod.get;
    set := Dom2IdxMod.set;
    sig := Dom2IdxMod.sig;
    merge := Dom2IdxMod.merge;
    minus := Dom2IdxMod.minus;
    map_dec_a := Dom2IdxMod.map_dec_a 
}.

Next Obligation.
  apply Dom2IdxMod.map_join_emp.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply Dom2IdxMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply Dom2IdxMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply Dom2IdxMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_eql; auto.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply Dom2IdxMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_get_sig.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_get_set.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply Dom2IdxMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply Dom2IdxMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_set_emp.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_set_sig.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply Dom2IdxMod.map_del_sem.
Qed.

(* Module about domainIntStatusTbl *)

Definition  domst := int32.

Module absDomIntSta.
  Definition B : Set := int. 
  Definition holder : B := Int.zero.  
End absDomIntSta.

Module DomIntStaMod := MapLib.MapFun idxspec absDomIntSta. 

Program Instance DomIntStaMap: PermMap domid int DomIntStaMod.map := 
 {
    usePerm := DomIntStaMod.usePerm;
    isRw := DomIntStaMod.isRw;
    flip := DomIntStaMod.flip;
    sameV := DomIntStaMod.sameV;
    same := DomIntStaMod.same;
    emp := DomIntStaMod.emp;
    join := DomIntStaMod.join;
    del := DomIntStaMod.del;
    get := DomIntStaMod.get;
    set := DomIntStaMod.set;
    sig := DomIntStaMod.sig;
    merge := DomIntStaMod.merge;
    minus := DomIntStaMod.minus;
    map_dec_a := DomIntStaMod.map_dec_a 
}.

Next Obligation.
  apply DomIntStaMod.map_join_emp.
Qed.
Next Obligation.
  apply DomIntStaMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply DomIntStaMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply DomIntStaMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply DomIntStaMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply DomIntStaMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply DomIntStaMod.map_eql; auto.
Qed.
Next Obligation.
  apply DomIntStaMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply DomIntStaMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply DomIntStaMod.map_get_sig.
Qed.
Next Obligation.
  apply DomIntStaMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply DomIntStaMod.map_get_set.
Qed.
Next Obligation.
  apply DomIntStaMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply DomIntStaMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply DomIntStaMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply DomIntStaMod.map_set_emp.
Qed.
Next Obligation.
  apply DomIntStaMod.map_set_sig.
Qed.
Next Obligation.
  apply DomIntStaMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply DomIntStaMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply DomIntStaMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply DomIntStaMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply DomIntStaMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply DomIntStaMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply DomIntStaMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply DomIntStaMod.map_del_sem.
Qed.

(* Module about ksDomains *)

Definition DDTdomain := int32.
Definition Ddom_t_ID := int32.
Definition DOSPartitionPeriod :=int32.
Definition Ddom_t_pAddress := int32.
Definition Ddom_t_vAddress := int32.
Definition Ddom_t_len := int32.
Definition Ddom_t_status := int32.
Definition Ddom_t_size := int32.

Module absdomain_t.
    Definition B:= ( DDTdomain * Ddom_t_ID * DOSPartitionPeriod * 
                                         Ddom_t_pAddress * Ddom_t_vAddress * Ddom_t_len * 
                                         Ddom_t_size * Ddom_t_status *DomIntStaMod.map  )%type.
  Definition holder : B := (Int.zero, Int.zero, Int.zero, Int.zero, Int.zero, Int.zero, Int.zero, Int.zero, 
                                                  DomIntStaMod.emp ).
End absdomain_t.

Module KsDomsMod := MapLib.MapFun idxspec absdomain_t. 

Program Instance KsDomsMap: PermMap domid (DDTdomain * Ddom_t_ID * DOSPartitionPeriod * 
                                         Ddom_t_pAddress * Ddom_t_vAddress * Ddom_t_len * 
                                         Ddom_t_size * Ddom_t_status *DomIntStaMod.map) KsDomsMod.map := 
 {
    usePerm := KsDomsMod.usePerm;
    isRw := KsDomsMod.isRw;
    flip := KsDomsMod.flip;
    sameV := KsDomsMod.sameV;
    same := KsDomsMod.same;
    emp := KsDomsMod.emp;
    join := KsDomsMod.join;
    del := KsDomsMod.del;
    get := KsDomsMod.get;
    set := KsDomsMod.set;
    sig := KsDomsMod.sig;
    merge := KsDomsMod.merge;
    minus := KsDomsMod.minus;
    map_dec_a := KsDomsMod.map_dec_a 
}.

Next Obligation.
  apply KsDomsMod.map_join_emp.
Qed.
Next Obligation.
  apply KsDomsMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply KsDomsMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply KsDomsMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply KsDomsMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply KsDomsMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply KsDomsMod.map_eql; auto.
Qed.
Next Obligation.
  apply KsDomsMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply KsDomsMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply KsDomsMod.map_get_sig.
Qed.
Next Obligation.
  apply KsDomsMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply KsDomsMod.map_get_set.
Qed.
Next Obligation.
  apply KsDomsMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply KsDomsMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply KsDomsMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply KsDomsMod.map_set_emp.
Qed.
Next Obligation.
  apply KsDomsMod.map_set_sig.
Qed.
Next Obligation.
  apply KsDomsMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply KsDomsMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply KsDomsMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply KsDomsMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply KsDomsMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply KsDomsMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply KsDomsMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply KsDomsMod.map_del_sem.
Qed.

(* Module about IntPartitionMux*)

Module absintpmux.
  Definition B : Set := int. 
  Definition holder : B := Int.zero.  
End absintpmux.

Module IntPMuxMod := MapLib.MapFun idxspec absintpmux. 

Program Instance IntPMuxMap: PermMap int int IntPMuxMod.map := 
 {
    usePerm := IntPMuxMod.usePerm;
    isRw := IntPMuxMod.isRw;
    flip := IntPMuxMod.flip;
    sameV := IntPMuxMod.sameV;
    same := IntPMuxMod.same;
    emp := IntPMuxMod.emp;
    join := IntPMuxMod.join;
    del := IntPMuxMod.del;
    get := IntPMuxMod.get;
    set := IntPMuxMod.set;
    sig := IntPMuxMod.sig;
    merge := IntPMuxMod.merge;
    minus := IntPMuxMod.minus;
    map_dec_a := IntPMuxMod.map_dec_a 
}.

Next Obligation.
  apply IntPMuxMod.map_join_emp.
Qed.
Next Obligation.
  apply IntPMuxMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply IntPMuxMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply IntPMuxMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply IntPMuxMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply IntPMuxMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply IntPMuxMod.map_eql; auto.
Qed.
Next Obligation.
  apply IntPMuxMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply IntPMuxMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply IntPMuxMod.map_get_sig.
Qed.
Next Obligation.
  apply IntPMuxMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply IntPMuxMod.map_get_set.
Qed.
Next Obligation.
  apply IntPMuxMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply IntPMuxMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply IntPMuxMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply IntPMuxMod.map_set_emp.
Qed.
Next Obligation.
  apply IntPMuxMod.map_set_sig.
Qed.
Next Obligation.
  apply IntPMuxMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply IntPMuxMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply IntPMuxMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply IntPMuxMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply IntPMuxMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply IntPMuxMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply IntPMuxMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply IntPMuxMod.map_del_sem.
Qed.

(* ---------------------------------------end add by CNU -----------------------------------------*)



(*-------------------------------------------------- add by sjtu ------------------------------------*)
(* timer and core *)

Definition timerid := Z.

Inductive timerstatus :=
| tm_idle : timerstatus
| tm_start : timerstatus.

Definition timertick := Z.
Definition timerperiod := Z.

Inductive enable_mode :=
| onetime | continuously .

Inductive timer := 
| gp_t :  timerperiod -> enable_mode -> timer
| wd_t :  timerperiod -> timer.

Inductive outMode :=
 | om_pulse  | om_clock.

Module abstmr.
  Definition B : Set := ( timer * timerstatus *  timertick * outMode )%type.
  Definition holder : B := (gp_t 0 onetime, tm_idle, 0, om_pulse).
End abstmr.

Module TmrMod := MapLib.MapFun identspec abstmr.

Program Instance TmrMap: PermMap timerid  (timer * timerstatus *  timertick * outMode ) TmrMod.map :=
  {
    usePerm := TmrMod.usePerm;
    isRw := TmrMod.isRw;
    flip := TmrMod.flip;
    sameV := TmrMod.sameV;
    same := TmrMod.same;
    emp := TmrMod.emp;
    join := TmrMod.join;
    del := TmrMod.del;
    get := TmrMod.get;
    set := TmrMod.set;
    sig := TmrMod.sig;
    merge := TmrMod.merge;
    minus := TmrMod.minus;
    map_dec_a := TmrMod.map_dec_a
}.
Next Obligation.
  apply TmrMod.map_join_emp.
Qed.
Next Obligation.
  apply TmrMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply TmrMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply TmrMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply TmrMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply TmrMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply TmrMod.map_eql; auto.
Qed.
Next Obligation.
  apply TmrMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply TmrMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply TmrMod.map_get_sig.
Qed.
Next Obligation.
  apply TmrMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply TmrMod.map_get_set.
Qed.
Next Obligation.
  apply TmrMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply TmrMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply TmrMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply TmrMod.map_set_emp.
Qed.
Next Obligation.
  apply TmrMod.map_set_sig.
Qed.
Next Obligation.
  apply TmrMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply TmrMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply TmrMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply TmrMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply TmrMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply TmrMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply TmrMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply TmrMod.map_del_sem.
Qed.

Module semBool.
  Definition B := bool.
  Definition holder : B := false.
End semBool.  

Module coreidspec.

  Definition A := coreid.

  Definition B := coreid.
  
  Definition beq : A -> A -> bool := Nat.eqb.
  
  Definition blt : A -> A -> bool := Nat.ltb.
  
  Require Import Lia.
  Lemma beq_true_eq : forall a a' : A,
    beq a a' = true -> a = a'.
  Proof.
    unfold beq;intros. apply beq_nat_true;auto.
  Qed.

  Lemma beq_false_neq : forall a a' : A,
    beq a a' = false -> a <> a'.
  Proof.
   unfold beq;intros. apply beq_nat_false;auto.
  Qed.


  Lemma eq_beq_true : forall a a' : A,
    a = a' -> beq a a' = true.
  Proof.
    unfold beq;intros. apply Nat.eqb_eq;auto.
  Qed.

  Lemma neq_beq_false : forall a a' : A,
    a <> a' -> beq a a' = false.
  Proof.
    unfold beq;intros. apply Nat.eqb_neq;auto. 
  Qed.


  Lemma blt_trans : forall a a' a'' : A,
                      blt a a' = true -> blt a' a'' = true -> blt a a'' = true.
  Proof.
    unfold blt;intros. rewrite Nat.ltb_lt in *. lia.
  Qed.

  Lemma blt_irrefl : forall a : A,
                       blt a a = false.
  Proof.
    intros; unfolds. rewrite Nat.ltb_nlt in *. lia.
  Qed.

  Lemma blt_asym :  forall a b : A, 
    blt a b = true -> blt b a = false.
   Proof.
    intros; unfolds. rewrite  Nat.ltb_lt,Nat.ltb_nlt in *. lia.
  Qed.

   Lemma blt_beq_dec : forall a b : A,
                         {blt a b = true} + {beq a b = true} + {blt b a = true}.
   Proof.
     intros.
     unfold blt, beq. 
     remember ((a <? b)%nat) as bool1 eqn: H;
     remember ((a =? b)%nat) as bool2 eqn: H0;
     remember ((b <? a)%nat) as bool3 eqn: H1.
     symmetry in H,H0,H1.
     destruct bool1, bool2, bool3;auto.
      rewrite Nat.eqb_neq , Nat.ltb_nlt in *. lia.
   Qed.  
End coreidspec.

Module SoftSem.
  Definition B := ecbid.
  Definition holder : B := ( Z.to_pos 1, Int.repr 0).
End SoftSem.

Module SoftSemMod := MapLib.MapFun coreidspec SoftSem.

(* Corresponds to either cap_category_t or cap_object_t *)
Definition cap_content_type := (int32 * int32 * val)%type.

(* Corresponds to struct slot_t. The fields are type in slot_t, type in cap_t,
   and content in cap_t respectively.
*)
Definition slot_val_type := (int32 * (int32* cap_content_type))%type.

(* Corresponds to struct cte_t. The fields are guide_num, slot_num and slot,
   respectively.
*)
Definition cnode_val_type := (int32 * int32 * list slot_val_type)%type.
Definition cnode_val_type_Null :cnode_val_type := (Int.zero, Int.zero, nil).

(* Corresponds to struct OS_CSpace. The fields are cnode, child_num,
   cspace (child cnodes), and OSCSpaceNext taskPrio.
*)
Definition cspace_val_type := (cnode_val_type * int32 * (list val) * val * int32) %type.

Module CapCSpace.
  Definition B := ((list slot_val_type) * (list priority) * priority)%type.
  Definition holder : B := (nil, nil, (Int.repr (-1))).
End CapCSpace.

Module CSpaceMod := MapLib.MapFun idxspec CapCSpace.

Program Instance CSpaceModMap: PermMap priority ((list slot_val_type) * (list priority) * priority) CSpaceMod.map :=
  {
    usePerm := CSpaceMod.usePerm;
    isRw := CSpaceMod.isRw;
    flip := CSpaceMod.flip;
    sameV := CSpaceMod.sameV;
    same := CSpaceMod.same;
    emp := CSpaceMod.emp;
    join := CSpaceMod.join;
    del := CSpaceMod.del;
    get := CSpaceMod.get;
    set := CSpaceMod.set;
    sig := CSpaceMod.sig;
    merge := CSpaceMod.merge;
    minus := CSpaceMod.minus;
    map_dec_a := CSpaceMod.map_dec_a
}.
Next Obligation.
  apply CSpaceMod.map_join_emp.
Qed.
Next Obligation.
  apply CSpaceMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply CSpaceMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply CSpaceMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply CSpaceMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply CSpaceMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply CSpaceMod.map_eql; auto.
Qed.
Next Obligation.
  apply CSpaceMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply CSpaceMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply CSpaceMod.map_get_sig.
Qed.
Next Obligation.
  apply CSpaceMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply CSpaceMod.map_get_set.
Qed.
Next Obligation.
  apply CSpaceMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply CSpaceMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply CSpaceMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply CSpaceMod.map_set_emp.
Qed.
Next Obligation.
  apply CSpaceMod.map_set_sig.
Qed.
Next Obligation.
  apply CSpaceMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply CSpaceMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply CSpaceMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply CSpaceMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply CSpaceMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply CSpaceMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply CSpaceMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply CSpaceMod.map_del_sem.
Qed.

Module abscspace.
 Definition B: Set := int32.
 Definition holder: B:= Int.zero.
End abscspace.

(*定义这个ptr -> int32的映射*)
Module CSpaceptr2prioMod := MapLib.MapFun tidspec abscspace.

Program Instance CSpaceptr2prioModMap: PermMap tid int32 CSpaceptr2prioMod.map :=
 {
   usePerm := CSpaceptr2prioMod.usePerm;
   isRw := CSpaceptr2prioMod.isRw;
   flip := CSpaceptr2prioMod.flip;
   sameV := CSpaceptr2prioMod.sameV;
   same := CSpaceptr2prioMod.same;
   emp := CSpaceptr2prioMod.emp;
   join := CSpaceptr2prioMod.join;
   del := CSpaceptr2prioMod.del;
   get := CSpaceptr2prioMod.get;
   set := CSpaceptr2prioMod.set;
   sig := CSpaceptr2prioMod.sig;
   merge := CSpaceptr2prioMod.merge;
   minus := CSpaceptr2prioMod.minus;
   map_dec_a := CSpaceptr2prioMod.map_dec_a
}.
Next Obligation.
 apply CSpaceptr2prioMod.map_join_emp.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_join_pos; auto.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_join_comm; auto.
Qed.
Next Obligation.
 eapply CSpaceptr2prioMod.map_join_assoc; eauto.
Qed.
Next Obligation.
 eapply CSpaceptr2prioMod.map_join_cancel; eauto.
Qed.
Next Obligation.
 eapply CSpaceptr2prioMod.map_join_deter; eauto.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_eql; auto.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_disjoint; auto.
Qed.
Next Obligation.
 eapply CSpaceptr2prioMod.map_get_unique; eauto.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_get_sig.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_get_sig'; auto.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_get_set.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_get_set'; auto.
Qed.
Next Obligation.
 eapply CSpaceptr2prioMod.map_join_get_none; eauto.
Qed.
Next Obligation.
 eapply CSpaceptr2prioMod.map_join_get_some; eauto.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_set_emp.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_set_sig.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_join_set_none; auto.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_join_get_sig; auto.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_merge_sem; auto.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_join_merge; eauto.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_merge_comm; eauto.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_minus_sem; auto.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_join_minus; eauto.
Qed.
Next Obligation.
 apply CSpaceptr2prioMod.map_del_sem.
Qed.
(*-------------------------------------------------- add end sjtu ------------------------------------*)

Definition stacksize := int32.
(* Module about abspthattr *)

Module abspthattrb.
  Definition B: Set :=  (addrval * stacksize * priority )%type. 
  Definition holder : B := (( Z.to_pos 1, Int.repr 0), Int.zero, Int.zero). 
End abspthattrb.

Module PthattrMod := MapLib.MapFun idxspec abspthattrb.

Program Instance PthattrMod:
  PermMap pos (addrval * stacksize * priority) PthattrMod.map :=
  {
    usePerm := PthattrMod.usePerm;
    isRw := PthattrMod.isRw;
    flip := PthattrMod.flip;
    sameV := PthattrMod.sameV;
    same := PthattrMod.same;
    emp := PthattrMod.emp;
    join := PthattrMod.join;
    del := PthattrMod.del;
    get := PthattrMod.get;
    set := PthattrMod.set;
    sig := PthattrMod.sig;
    merge := PthattrMod.merge;
    minus := PthattrMod.minus;
    map_dec_a := PthattrMod.map_dec_a
  }.
Next Obligation.
  apply PthattrMod.map_join_emp.
Qed.
Next Obligation.
  apply PthattrMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply PthattrMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply PthattrMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply PthattrMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply PthattrMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply PthattrMod.map_eql; auto.
Qed.
Next Obligation.
  apply PthattrMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply PthattrMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply PthattrMod.map_get_sig.
Qed.
Next Obligation.
  apply PthattrMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply PthattrMod.map_get_set.
Qed.
Next Obligation.
  apply PthattrMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply PthattrMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply PthattrMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply PthattrMod.map_set_emp.
Qed.
Next Obligation.
  apply PthattrMod.map_set_sig.
Qed.
Next Obligation.
  apply PthattrMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply PthattrMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply PthattrMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply PthattrMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply PthattrMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply PthattrMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply PthattrMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply PthattrMod.map_del_sem.
Qed.

Inductive absdataid:=
| abstcblsid : absdataid
| absecblsid: absdataid
| ostmid : absdataid
| curtid:absdataid
| ierid : absdataid
| inthandlerid : absdataid
| inthandlerParamid : absdataid
| exchandlerid: absdataid
(* add by CNU *)                  
| absptlsid: absdataid (* ostcbpriotbl *)
| seminfoid: absdataid (* gjb seminfo *)
| absmutinfoid: absdataid (* gjb mutexinfo*)
| absmqattrid: absdataid (* gjb mqattr *)
| pblsid: absdataid (* pos blocks *)
| eblsid: absdataid (* err blocks *) 
| evatomheapid:absdataid (* atom heaps *)
| evstructheapid:absdataid (* struct heaps *)
| evarrayheapid:absdataid (* array heaps *)
| evlocid: absdataid (* auxliary event location *)
| evptrid: absdataid (* auxliary event pointer *)
| rootskid : absdataid (* RootTaskStk *)
| allpartareaid: absdataid (* area_t  *)
| sms_mpaxid : absdataid (* SMS_MPAX *)
| ses_mpaxid : absdataid (* SES_MPAX *)
| xmpaxid : absdataid (* XMC_XMPAX *)
| xmpfarid : absdataid (* XMPFAR *)
| xmpfsrid : absdataid (* XMPFSR *)
| mdmaerrid : absdataid (* MDMAERR *)
| ksdschedidxid: absdataid (* KsDomScheduleIdx *)
| ksdschedlenid: absdataid (* KsDomScheduleLength *)
| kscurdomid: absdataid (* KsCurDomain *)
| kslastdomid: absdataid (* KsLastDomain *)
| ksdomtimeid: absdataid (* KsDomainTime *)
| ksdschedid: absdataid (* KsDomSchedule[idx] *)
| dom2indexid: absdataid (* Domain2Index *)
| uconfid: absdataid (* ucos_conf_t *)
| intpmuxid: absdataid (* IntPartitionMux *)
| ksdomsid: absdataid (* ksDomains[curd] *)
| cpartnumid: absdataid (* Core_partition_num *)
(* end add by CNU *) 
(* add by SJTU *)
| ostmrid : absdataid 
| osclkrateid : absdataid 
| curcoreid: absdataid
| oscoreheapid: absdataid
| ipcsendid: absdataid
| ipcrecvid: absdataid
| ipcsemid : absdataid
| ipcsendsemid : absdataid
| ipcsemshareid : absdataid
| ipcbroadid : absdataid
| ipcgrid : absdataid 
| freedynid : absdataid
| dynheapid : absdataid
(* end add by SJTU *) 
(* add by ISCAS*)
| cspaceid : absdataid
| abspthattrid: absdataid 
(* Eend add by ISCAS*)
(* add for Partition *)
| oskportid : absdataid   (* OSKernelPortIDTbl *)
| oschannelid : absdataid  (* OSChannelIDTbl *)
| osdomainportid : absdataid (* partition sem *)
| oscoreportplid : absdataid (* addr of destination ports *)
(* end add for Partition *).

Definition absdataid_eq (id1 id2:absdataid):=
  match id1, id2 with
    | abstcblsid, abstcblsid => true
    | absecblsid,absecblsid => true
    | ostmid, ostmid => true
    | curtid,curtid => true
    | ierid, ierid => true
    | inthandlerid, inthandlerid => true
    | inthandlerParamid, inthandlerParamid => true
    | exchandlerid, exchandlerid => true
    (* add by CNU *)
    | absptlsid, absptlsid => true 
    | seminfoid, seminfoid => true
    | absmutinfoid, absmutinfoid => true
    | absmqattrid, absmqattrid => true
    | pblsid, pblsid => true 
    | eblsid, eblsid => true
    | evatomheapid, evatomheapid => true 
    | evstructheapid, evstructheapid => true 
    | evarrayheapid, evarrayheapid => true 
    | evlocid, evlocid => true 
    | evptrid, evptrid => true
    | rootskid, rootskid => true 
    | allpartareaid, allpartareaid => true
    | sms_mpaxid, sms_mpaxid => true
    | ses_mpaxid, ses_mpaxid => true
    | xmpaxid, xmpaxid => true
    | xmpfarid, xmpfarid => true
    | xmpfsrid, xmpfsrid => true
    | mdmaerrid, mdmaerrid => true
    | ksdschedidxid, ksdschedidxid => true
    | ksdschedlenid, ksdschedlenid => true
    | kscurdomid, kscurdomid => true
    | kslastdomid, kslastdomid => true
    | ksdomtimeid, ksdomtimeid => true
    | ksdschedid, ksdschedid => true
    | dom2indexid, dom2indexid => true
    | uconfid, uconfid => true
    | intpmuxid, intpmuxid => true
    | ksdomsid, ksdomsid => true
    | cpartnumid, cpartnumid => true
    (* add by CNU *)
    (* add by SJTU *)
    | ostmrid, ostmrid => true
    | osclkrateid, osclkrateid => true 
    | curcoreid, curcoreid => true  
    | oscoreheapid, oscoreheapid => true
    | ipcsendid, ipcsendid => true 
    | ipcrecvid, ipcrecvid => true 
    | ipcsemid, ipcsemid => true
    | ipcsendsemid, ipcsendsemid => true
    | ipcsemshareid, ipcsemshareid => true
    | ipcbroadid, ipcbroadid => true
    | ipcgrid, ipcgrid => true 
    | freedynid, freedynid => true
    | dynheapid, dynheapid => true
    (* end add by SJTU *) 
    | cspaceid, cspaceid => true 
    | abspthattrid, abspthattrid => true  
    (* add for Partition *)
    | oskportid, oskportid => true 
    | oschannelid, oschannelid => true 
    | osdomainportid, osdomainportid => true
    | oscoreportplid, oscoreportplid => true
    (* end add for Partition *)
    | _,_ => false
  end.

Definition absdataid_lt (id1 id2:absdataid):=
  match id1, id2 with
    | abstcblsid, abstcblsid => false
    | abstcblsid, _ => true
    | absecblsid, abstcblsid => false
    | absecblsid, absecblsid => false
    | absecblsid, _ =>true
    | ostmid, abstcblsid =>false
    | ostmid, absecblsid => false
    | ostmid, ostmid => false
    | ostmid, _ => true
    | curtid, abstcblsid => false
    | curtid, absecblsid => false
    | curtid, ostmid => false
    | curtid, curtid => false
    | curtid, _ => true
    | ierid, abstcblsid => false
    | ierid, absecblsid => false
    | ierid, ostmid => false
    | ierid, curtid => false
    | ierid, ierid => false
    | ierid, _ => true
    | inthandlerid, abstcblsid => false
    | inthandlerid, absecblsid => false
    | inthandlerid, ostmid => false
    | inthandlerid, curtid => false
    | inthandlerid, ierid => false
    | inthandlerid, inthandlerid => false
    | inthandlerid, _ => true
    | inthandlerParamid, abstcblsid => false
    | inthandlerParamid, absecblsid => false
    | inthandlerParamid, ostmid => false
    | inthandlerParamid, curtid => false
    | inthandlerParamid, ierid => false
    | inthandlerParamid, inthandlerid => false
    | inthandlerParamid, inthandlerParamid => false
    | inthandlerParamid, _ => true
    | exchandlerid, abstcblsid => false
    | exchandlerid, absecblsid => false 
    | exchandlerid, ostmid => false
    | exchandlerid, curtid => false 
    | exchandlerid, ierid => false
    | exchandlerid, inthandlerid => false 
    | exchandlerid, inthandlerParamid => false
    | exchandlerid, exchandlerid => false 
    | exchandlerid, _ => true 
    (* add by CNU *)
    | absptlsid, abstcblsid => false 
    | absptlsid, absecblsid => false
    | absptlsid, ostmid => false
    | absptlsid, curtid => false
    | absptlsid, ierid => false
    | absptlsid, inthandlerid => false 
    | absptlsid, inthandlerParamid => false
    | absptlsid, exchandlerid => false
    | absptlsid, absptlsid => false
    | absptlsid, _ => true
    | seminfoid, abstcblsid => false 
    | seminfoid, absecblsid => false
    | seminfoid, ostmid => false 
    | seminfoid, curtid => false
    | seminfoid, ierid => false 
    | seminfoid, inthandlerid => false
    | seminfoid, inthandlerParamid => false 
    | seminfoid, exchandlerid => false
    | seminfoid, absptlsid => false 
    | seminfoid, seminfoid => false
    | seminfoid, _ => true
    | absmutinfoid, abstcblsid => false
    | absmutinfoid, absecblsid => false
    | absmutinfoid, ostmid => false 
    | absmutinfoid, curtid => false 
    | absmutinfoid, ierid => false
    | absmutinfoid, inthandlerid => false 
    | absmutinfoid, inthandlerParamid => false 
    | absmutinfoid, exchandlerid => false
    | absmutinfoid, absptlsid => false
    | absmutinfoid, seminfoid => false 
    | absmutinfoid, absmutinfoid => false 
    | absmutinfoid, _ => true
    | absmqattrid, abstcblsid => false 
    | absmqattrid, absecblsid => false
    | absmqattrid, ostmid => false 
    | absmqattrid, curtid => false
    | absmqattrid, ierid => false
    | absmqattrid, inthandlerid => false 
    | absmqattrid, inthandlerParamid => false 
    | absmqattrid, exchandlerid => false 
    | absmqattrid, absptlsid => false
    | absmqattrid, seminfoid => false 
    | absmqattrid, absmutinfoid => false
    | absmqattrid, absmqattrid => false 
    | absmqattrid, _ => true    
    | pblsid, abstcblsid => false
    | pblsid, absecblsid => false
    | pblsid, ostmid => false 
    | pblsid, curtid => false
    | pblsid, ierid => false 
    | pblsid, inthandlerid => false
    | pblsid, inthandlerParamid => false 
    | pblsid, exchandlerid => false
    | pblsid, absptlsid => false 
    | pblsid, seminfoid => false
    | pblsid, absmutinfoid => false
    | pblsid, absmqattrid => false     
    | pblsid, pblsid => false
    | pblsid, _ => true
    | eblsid, abstcblsid => false
    | eblsid, absecblsid => false
    | eblsid, ostmid => false 
    | eblsid, curtid => false
    | eblsid, ierid => false 
    | eblsid, inthandlerid => false
    | eblsid, inthandlerParamid => false
    | eblsid, exchandlerid => false
    | eblsid, absptlsid => false 
    | eblsid, seminfoid => false
    | eblsid, absmutinfoid => false 
    | eblsid, absmqattrid => false
    | eblsid, pblsid => false 
    | eblsid, eblsid => false
    | eblsid, _ => true
    | evatomheapid, abstcblsid => false 
    | evatomheapid, absecblsid => false 
    | evatomheapid, ostmid => false 
    | evatomheapid, curtid => false 
    | evatomheapid, ierid => false
    | evatomheapid, inthandlerid => false 
    | evatomheapid, inthandlerParamid => false
    | evatomheapid, exchandlerid => false 
    | evatomheapid, absptlsid => false
    | evatomheapid, seminfoid => false 
    | evatomheapid, absmutinfoid => false
    | evatomheapid, absmqattrid => false 
    | evatomheapid, pblsid => false
    | evatomheapid, eblsid => false 
    | evatomheapid, evatomheapid => false
    | evatomheapid, _ => true
    | evstructheapid, abstcblsid => false 
    | evstructheapid, absecblsid => false 
    | evstructheapid, ostmid => false 
    | evstructheapid, curtid => false 
    | evstructheapid, ierid => false
    | evstructheapid, inthandlerid => false 
    | evstructheapid, inthandlerParamid => false
    | evstructheapid, exchandlerid => false 
    | evstructheapid, absptlsid => false
    | evstructheapid, seminfoid => false 
    | evstructheapid, absmutinfoid => false
    | evstructheapid, absmqattrid => false 
    | evstructheapid, pblsid => false
    | evstructheapid, eblsid => false 
    | evstructheapid, evatomheapid => false
    | evstructheapid, evstructheapid => false     
    | evstructheapid, _ => true    
    | evarrayheapid, abstcblsid => false 
    | evarrayheapid, absecblsid => false 
    | evarrayheapid, ostmid => false 
    | evarrayheapid, curtid => false 
    | evarrayheapid, ierid => false
    | evarrayheapid, inthandlerid => false 
    | evarrayheapid, inthandlerParamid => false
    | evarrayheapid, exchandlerid => false 
    | evarrayheapid, absptlsid => false
    | evarrayheapid, seminfoid => false 
    | evarrayheapid, absmutinfoid => false
    | evarrayheapid, absmqattrid => false 
    | evarrayheapid, pblsid => false
    | evarrayheapid, eblsid => false 
    | evarrayheapid, evatomheapid => false
    | evarrayheapid, evstructheapid => false
    | evarrayheapid, evarrayheapid => false     
    | evarrayheapid, _ => true
    | evlocid, abstcblsid => false 
    | evlocid, absecblsid => false 
    | evlocid, ostmid => false 
    | evlocid, curtid => false 
    | evlocid, ierid => false
    | evlocid, inthandlerid => false 
    | evlocid, inthandlerParamid => false
    | evlocid, exchandlerid => false 
    | evlocid, absptlsid => false
    | evlocid, seminfoid => false 
    | evlocid, absmutinfoid => false
    | evlocid, absmqattrid => false 
    | evlocid, pblsid => false
    | evlocid, eblsid => false 
    | evlocid, evatomheapid => false
    | evlocid, evstructheapid => false
    | evlocid, evarrayheapid => false
    | evlocid, evlocid => false  
    | evlocid, _ => true 
    | evptrid, abstcblsid => false 
    | evptrid, absecblsid => false 
    | evptrid, ostmid => false 
    | evptrid, curtid => false 
    | evptrid, ierid => false
    | evptrid, inthandlerid => false 
    | evptrid, inthandlerParamid => false
    | evptrid, exchandlerid => false 
    | evptrid, absptlsid => false
    | evptrid, seminfoid => false 
    | evptrid, absmutinfoid => false
    | evptrid, absmqattrid => false 
    | evptrid, pblsid => false
    | evptrid, eblsid => false 
    | evptrid, evatomheapid => false
    | evptrid, evstructheapid => false
    | evptrid, evarrayheapid => false
    | evptrid, evlocid => false  
    | evptrid, evptrid => false 
    | evptrid, _ => true
    | rootskid, abstcblsid => false 
    | rootskid, absecblsid => false 
    | rootskid, ostmid => false 
    | rootskid, curtid => false 
    | rootskid, ierid => false
    | rootskid, inthandlerid => false 
    | rootskid, inthandlerParamid => false
    | rootskid, exchandlerid => false 
    | rootskid, absptlsid => false
    | rootskid, seminfoid => false 
    | rootskid, absmutinfoid => false
    | rootskid, absmqattrid => false 
    | rootskid, pblsid => false
    | rootskid, eblsid => false 
    | rootskid, evatomheapid => false
    | rootskid, evstructheapid => false
    | rootskid, evarrayheapid => false
    | rootskid, evlocid => false  
    | rootskid, evptrid => false 
    | rootskid, rootskid => false 
    | rootskid, _ => true
    | allpartareaid, abstcblsid => false 
    | allpartareaid, absecblsid => false 
    | allpartareaid, ostmid => false 
    | allpartareaid, curtid => false 
    | allpartareaid, ierid => false
    | allpartareaid, inthandlerid => false 
    | allpartareaid, inthandlerParamid => false
    | allpartareaid, exchandlerid => false 
    | allpartareaid, absptlsid => false
    | allpartareaid, seminfoid => false 
    | allpartareaid, absmutinfoid => false
    | allpartareaid, absmqattrid => false 
    | allpartareaid, pblsid => false
    | allpartareaid, eblsid => false 
    | allpartareaid, evatomheapid => false
    | allpartareaid, evstructheapid => false
    | allpartareaid, evarrayheapid => false
    | allpartareaid, evlocid => false  
    | allpartareaid, evptrid => false 
    | allpartareaid, rootskid => false 
    | allpartareaid, allpartareaid => false
    | allpartareaid, _ => true
    | sms_mpaxid, abstcblsid => false
    | sms_mpaxid, absecblsid => false
    | sms_mpaxid, ostmid => false
    | sms_mpaxid, curtid => false
    | sms_mpaxid, ierid => false
    | sms_mpaxid, inthandlerid => false
    | sms_mpaxid, inthandlerParamid => false
    | sms_mpaxid, exchandlerid => false
    | sms_mpaxid, absptlsid => false
    | sms_mpaxid, seminfoid => false
    | sms_mpaxid, absmutinfoid => false
    | sms_mpaxid, absmqattrid => false
    | sms_mpaxid, pblsid => false
    | sms_mpaxid, eblsid => false
    | sms_mpaxid, evatomheapid => false
    | sms_mpaxid, evstructheapid => false
    | sms_mpaxid, evarrayheapid => false
    | sms_mpaxid, evlocid => false
    | sms_mpaxid, evptrid => false
    | sms_mpaxid, rootskid => false 
    | sms_mpaxid, allpartareaid => false
    | sms_mpaxid, sms_mpaxid => false
    | sms_mpaxid, _ => true
    | ses_mpaxid, abstcblsid => false
    | ses_mpaxid, absecblsid => false
    | ses_mpaxid, ostmid => false
    | ses_mpaxid, curtid => false
    | ses_mpaxid, ierid => false
    | ses_mpaxid, inthandlerid => false
    | ses_mpaxid, inthandlerParamid => false
    | ses_mpaxid, exchandlerid => false
    | ses_mpaxid, absptlsid => false
    | ses_mpaxid, seminfoid => false
    | ses_mpaxid, absmutinfoid => false
    | ses_mpaxid, absmqattrid => false
    | ses_mpaxid, pblsid => false
    | ses_mpaxid, eblsid => false
    | ses_mpaxid, evatomheapid => false
    | ses_mpaxid, evstructheapid => false
    | ses_mpaxid, evarrayheapid => false
    | ses_mpaxid, evlocid => false
    | ses_mpaxid, evptrid => false
    | ses_mpaxid, rootskid => false 
    | ses_mpaxid, allpartareaid => false
    | ses_mpaxid, sms_mpaxid => false
    | ses_mpaxid, ses_mpaxid => false
    | ses_mpaxid, _ => true
    | xmpaxid, abstcblsid => false
    | xmpaxid, absecblsid => false
    | xmpaxid, ostmid => false
    | xmpaxid, curtid => false
    | xmpaxid, ierid => false
    | xmpaxid, inthandlerid => false
    | xmpaxid, inthandlerParamid => false
    | xmpaxid, exchandlerid => false
    | xmpaxid, absptlsid => false
    | xmpaxid, seminfoid => false
    | xmpaxid, absmutinfoid => false
    | xmpaxid, absmqattrid => false
    | xmpaxid, pblsid => false
    | xmpaxid, eblsid => false
    | xmpaxid, evatomheapid => false
    | xmpaxid, evstructheapid => false
    | xmpaxid, evarrayheapid => false
    | xmpaxid, evlocid => false
    | xmpaxid, evptrid => false
    | xmpaxid, rootskid => false 
    | xmpaxid, allpartareaid => false
    | xmpaxid, sms_mpaxid => false
    | xmpaxid, ses_mpaxid => false
    | xmpaxid, xmpaxid => false
    | xmpaxid, _ => true
    | xmpfarid, abstcblsid => false
    | xmpfarid, absecblsid => false
    | xmpfarid, ostmid => false
    | xmpfarid, curtid => false
    | xmpfarid, ierid => false
    | xmpfarid, inthandlerid => false
    | xmpfarid, inthandlerParamid => false
    | xmpfarid, exchandlerid => false
    | xmpfarid, absptlsid => false
    | xmpfarid, seminfoid => false
    | xmpfarid, absmutinfoid => false
    | xmpfarid, absmqattrid => false
    | xmpfarid, pblsid => false
    | xmpfarid, eblsid => false
    | xmpfarid, evatomheapid => false
    | xmpfarid, evstructheapid => false
    | xmpfarid, evarrayheapid => false
    | xmpfarid, evlocid => false
    | xmpfarid, evptrid => false
    | xmpfarid, rootskid => false 
    | xmpfarid, allpartareaid => false
    | xmpfarid, sms_mpaxid => false
    | xmpfarid, ses_mpaxid => false
    | xmpfarid, xmpaxid => false
    | xmpfarid, xmpfarid => false
    | xmpfarid, _ => true
    | xmpfsrid, abstcblsid => false
    | xmpfsrid, absecblsid => false
    | xmpfsrid, ostmid => false
    | xmpfsrid, curtid => false
    | xmpfsrid, ierid => false
    | xmpfsrid, inthandlerid => false
    | xmpfsrid, inthandlerParamid => false
    | xmpfsrid, exchandlerid => false
    | xmpfsrid, absptlsid => false
    | xmpfsrid, seminfoid => false
    | xmpfsrid, absmutinfoid => false
    | xmpfsrid, absmqattrid => false
    | xmpfsrid, pblsid => false
    | xmpfsrid, eblsid => false
    | xmpfsrid, evatomheapid => false
    | xmpfsrid, evstructheapid => false
    | xmpfsrid, evarrayheapid => false
    | xmpfsrid, evlocid => false
    | xmpfsrid, evptrid => false
    | xmpfsrid, rootskid => false 
    | xmpfsrid, allpartareaid => false
    | xmpfsrid, sms_mpaxid => false
    | xmpfsrid, ses_mpaxid => false
    | xmpfsrid, xmpaxid => false
    | xmpfsrid, xmpfarid => false
    | xmpfsrid, xmpfsrid => false
    | xmpfsrid, _ => true
    | mdmaerrid, abstcblsid => false
    | mdmaerrid, absecblsid => false
    | mdmaerrid, ostmid => false
    | mdmaerrid, curtid => false
    | mdmaerrid, ierid => false
    | mdmaerrid, inthandlerid => false
    | mdmaerrid, inthandlerParamid => false
    | mdmaerrid, exchandlerid => false
    | mdmaerrid, absptlsid => false
    | mdmaerrid, seminfoid => false
    | mdmaerrid, absmutinfoid => false
    | mdmaerrid, absmqattrid => false
    | mdmaerrid, pblsid => false
    | mdmaerrid, eblsid => false
    | mdmaerrid, evatomheapid => false
    | mdmaerrid, evstructheapid => false
    | mdmaerrid, evarrayheapid => false
    | mdmaerrid, evlocid => false
    | mdmaerrid, evptrid => false
    | mdmaerrid, rootskid => false 
    | mdmaerrid, allpartareaid => false
    | mdmaerrid, sms_mpaxid => false
    | mdmaerrid, ses_mpaxid => false
    | mdmaerrid, xmpaxid => false
    | mdmaerrid, xmpfarid => false
    | mdmaerrid, xmpfsrid => false
    | mdmaerrid, mdmaerrid => false
    | mdmaerrid, _ => true
    | ksdschedidxid, abstcblsid => false 
    | ksdschedidxid, absecblsid => false 
    | ksdschedidxid, ostmid => false 
    | ksdschedidxid, curtid => false 
    | ksdschedidxid, ierid => false
    | ksdschedidxid, inthandlerid => false 
    | ksdschedidxid, inthandlerParamid => false
    | ksdschedidxid, exchandlerid => false 
    | ksdschedidxid, absptlsid => false
    | ksdschedidxid, seminfoid => false 
    | ksdschedidxid, absmutinfoid => false
    | ksdschedidxid, absmqattrid => false
    | ksdschedidxid, pblsid => false
    | ksdschedidxid, eblsid => false 
    | ksdschedidxid, evatomheapid => false
    | ksdschedidxid, evstructheapid => false
    | ksdschedidxid, evarrayheapid => false
    | ksdschedidxid, evlocid => false
    | ksdschedidxid, evptrid => false
    | ksdschedidxid, rootskid => false 
    | ksdschedidxid, allpartareaid => false
    | ksdschedidxid, sms_mpaxid => false
    | ksdschedidxid, ses_mpaxid => false
    | ksdschedidxid, xmpaxid => false
    | ksdschedidxid, xmpfarid => false
    | ksdschedidxid, xmpfsrid => false
    | ksdschedidxid, mdmaerrid => false
    | ksdschedidxid, ksdschedidxid => false
    | ksdschedidxid, _ => true
    | ksdschedlenid, abstcblsid => false 
    | ksdschedlenid, absecblsid => false 
    | ksdschedlenid, ostmid => false 
    | ksdschedlenid, curtid => false 
    | ksdschedlenid, ierid => false
    | ksdschedlenid, inthandlerid => false 
    | ksdschedlenid, inthandlerParamid => false
    | ksdschedlenid, exchandlerid => false 
    | ksdschedlenid, absptlsid => false
    | ksdschedlenid, seminfoid => false 
    | ksdschedlenid, absmutinfoid => false
    | ksdschedlenid, absmqattrid => false
    | ksdschedlenid, pblsid => false
    | ksdschedlenid, eblsid => false 
    | ksdschedlenid, evatomheapid => false
    | ksdschedlenid, evstructheapid => false
    | ksdschedlenid, evarrayheapid => false
    | ksdschedlenid, evlocid => false
    | ksdschedlenid, evptrid => false
    | ksdschedlenid, rootskid => false 
    | ksdschedlenid, allpartareaid => false
    | ksdschedlenid, sms_mpaxid => false
    | ksdschedlenid, ses_mpaxid => false
    | ksdschedlenid, xmpaxid => false
    | ksdschedlenid, xmpfarid => false
    | ksdschedlenid, xmpfsrid => false
    | ksdschedlenid, mdmaerrid => false
    | ksdschedlenid, ksdschedidxid => false
    | ksdschedlenid, ksdschedlenid => false
    | ksdschedlenid, _ => true
    | kscurdomid, abstcblsid => false 
    | kscurdomid, absecblsid => false 
    | kscurdomid, ostmid => false 
    | kscurdomid, curtid => false 
    | kscurdomid, ierid => false
    | kscurdomid, inthandlerid => false 
    | kscurdomid, inthandlerParamid => false
    | kscurdomid, exchandlerid => false 
    | kscurdomid, absptlsid => false
    | kscurdomid, seminfoid => false 
    | kscurdomid, absmutinfoid => false
    | kscurdomid, absmqattrid => false
    | kscurdomid, pblsid => false
    | kscurdomid, eblsid => false 
    | kscurdomid, evatomheapid => false
    | kscurdomid, evstructheapid => false
    | kscurdomid, evarrayheapid => false
    | kscurdomid, evlocid => false
    | kscurdomid, evptrid => false
    | kscurdomid, rootskid => false 
    | kscurdomid, allpartareaid => false
    | kscurdomid, sms_mpaxid => false
    | kscurdomid, ses_mpaxid => false
    | kscurdomid, xmpaxid => false
    | kscurdomid, xmpfarid => false
    | kscurdomid, xmpfsrid => false
    | kscurdomid, mdmaerrid => false
    | kscurdomid, ksdschedidxid => false
    | kscurdomid, ksdschedlenid => false
    | kscurdomid, kscurdomid => false
    | kscurdomid, _ => true
    | kslastdomid, abstcblsid => false 
    | kslastdomid, absecblsid => false 
    | kslastdomid, ostmid => false 
    | kslastdomid, curtid => false 
    | kslastdomid, ierid => false
    | kslastdomid, inthandlerid => false 
    | kslastdomid, inthandlerParamid => false
    | kslastdomid, exchandlerid => false 
    | kslastdomid, absptlsid => false
    | kslastdomid, seminfoid => false 
    | kslastdomid, absmutinfoid => false
    | kslastdomid, absmqattrid => false
    | kslastdomid, pblsid => false
    | kslastdomid, eblsid => false 
    | kslastdomid, evatomheapid => false
    | kslastdomid, evstructheapid => false
    | kslastdomid, evarrayheapid => false
    | kslastdomid, evlocid => false
    | kslastdomid, evptrid => false
    | kslastdomid, rootskid => false 
    | kslastdomid, allpartareaid => false
    | kslastdomid, sms_mpaxid => false
    | kslastdomid, ses_mpaxid => false
    | kslastdomid, xmpaxid => false
    | kslastdomid, xmpfarid => false
    | kslastdomid, xmpfsrid => false
    | kslastdomid, mdmaerrid => false
    | kslastdomid, ksdschedidxid => false
    | kslastdomid, ksdschedlenid => false
    | kslastdomid, kscurdomid => false
    | kslastdomid, kslastdomid => false
    | kslastdomid, _ => true
    | ksdomtimeid, abstcblsid => false 
    | ksdomtimeid, absecblsid => false 
    | ksdomtimeid, ostmid => false 
    | ksdomtimeid, curtid => false 
    | ksdomtimeid, ierid => false
    | ksdomtimeid, inthandlerid => false 
    | ksdomtimeid, inthandlerParamid => false
    | ksdomtimeid, exchandlerid => false 
    | ksdomtimeid, absptlsid => false
    | ksdomtimeid, seminfoid => false 
    | ksdomtimeid, absmutinfoid => false
    | ksdomtimeid, absmqattrid => false
    | ksdomtimeid, pblsid => false
    | ksdomtimeid, eblsid => false 
    | ksdomtimeid, evatomheapid => false
    | ksdomtimeid, evstructheapid => false
    | ksdomtimeid, evarrayheapid => false
    | ksdomtimeid, evlocid => false
    | ksdomtimeid, evptrid => false
    | ksdomtimeid, rootskid => false 
    | ksdomtimeid, allpartareaid => false
    | ksdomtimeid, sms_mpaxid => false
    | ksdomtimeid, ses_mpaxid => false
    | ksdomtimeid, xmpaxid => false
    | ksdomtimeid, xmpfarid => false
    | ksdomtimeid, xmpfsrid => false
    | ksdomtimeid, mdmaerrid => false
    | ksdomtimeid, ksdschedidxid => false
    | ksdomtimeid, ksdschedlenid => false
    | ksdomtimeid, kscurdomid => false
    | ksdomtimeid, kslastdomid => false
    | ksdomtimeid, ksdomtimeid => false
    | ksdomtimeid, _ => true
    | ksdschedid, abstcblsid => false 
    | ksdschedid, absecblsid => false 
    | ksdschedid, ostmid => false 
    | ksdschedid, curtid => false 
    | ksdschedid, ierid => false
    | ksdschedid, inthandlerid => false 
    | ksdschedid, inthandlerParamid => false
    | ksdschedid, exchandlerid => false 
    | ksdschedid, absptlsid => false
    | ksdschedid, seminfoid => false 
    | ksdschedid, absmutinfoid => false
    | ksdschedid, absmqattrid => false
    | ksdschedid, pblsid => false
    | ksdschedid, eblsid => false 
    | ksdschedid, evatomheapid => false
    | ksdschedid, evstructheapid => false
    | ksdschedid, evarrayheapid => false
    | ksdschedid, evlocid => false
    | ksdschedid, evptrid => false
    | ksdschedid, rootskid => false 
    | ksdschedid, allpartareaid => false
    | ksdschedid, sms_mpaxid => false
    | ksdschedid, ses_mpaxid => false
    | ksdschedid, xmpaxid => false
    | ksdschedid, xmpfarid => false
    | ksdschedid, xmpfsrid => false
    | ksdschedid, mdmaerrid => false
    | ksdschedid, ksdschedidxid => false
    | ksdschedid, ksdschedlenid => false
    | ksdschedid, kscurdomid => false
    | ksdschedid, kslastdomid => false
    | ksdschedid, ksdomtimeid => false
    | ksdschedid, ksdschedid => false
    | ksdschedid, _ => true
    | dom2indexid, abstcblsid => false 
    | dom2indexid, absecblsid => false 
    | dom2indexid, ostmid => false 
    | dom2indexid, curtid => false 
    | dom2indexid, ierid => false
    | dom2indexid, inthandlerid => false 
    | dom2indexid, inthandlerParamid => false
    | dom2indexid, exchandlerid => false 
    | dom2indexid, absptlsid => false
    | dom2indexid, seminfoid => false 
    | dom2indexid, absmutinfoid => false
    | dom2indexid, absmqattrid => false
    | dom2indexid, pblsid => false
    | dom2indexid, eblsid => false 
    | dom2indexid, evatomheapid => false
    | dom2indexid, evstructheapid => false
    | dom2indexid, evarrayheapid => false
    | dom2indexid, evlocid => false
    | dom2indexid, evptrid => false
    | dom2indexid, rootskid => false 
    | dom2indexid, allpartareaid => false
    | dom2indexid, sms_mpaxid => false
    | dom2indexid, ses_mpaxid => false
    | dom2indexid, xmpaxid => false
    | dom2indexid, xmpfarid => false
    | dom2indexid, xmpfsrid => false
    | dom2indexid, mdmaerrid => false
    | dom2indexid, ksdschedidxid => false
    | dom2indexid, ksdschedlenid => false
    | dom2indexid, kscurdomid => false
    | dom2indexid, kslastdomid => false
    | dom2indexid, ksdomtimeid => false
    | dom2indexid, ksdschedid => false
    | dom2indexid, dom2indexid => false
    | dom2indexid, _ => true
    | uconfid, abstcblsid => false 
    | uconfid, absecblsid => false 
    | uconfid, ostmid => false 
    | uconfid, curtid => false 
    | uconfid, ierid => false
    | uconfid, inthandlerid => false 
    | uconfid, inthandlerParamid => false
    | uconfid, exchandlerid => false 
    | uconfid, absptlsid => false
    | uconfid, seminfoid => false 
    | uconfid, absmutinfoid => false
    | uconfid, absmqattrid => false
    | uconfid, pblsid => false
    | uconfid, eblsid => false 
    | uconfid, evatomheapid => false
    | uconfid, evstructheapid => false
    | uconfid, evarrayheapid => false
    | uconfid, evlocid => false
    | uconfid, evptrid => false
    | uconfid, rootskid => false 
    | uconfid, allpartareaid => false
    | uconfid, sms_mpaxid => false
    | uconfid, ses_mpaxid => false
    | uconfid, xmpaxid => false
    | uconfid, xmpfarid => false
    | uconfid, xmpfsrid => false
    | uconfid, mdmaerrid => false
    | uconfid, ksdschedidxid => false
    | uconfid, ksdschedlenid => false
    | uconfid, kscurdomid => false
    | uconfid, kslastdomid => false
    | uconfid, ksdomtimeid => false
    | uconfid, ksdschedid => false
    | uconfid, dom2indexid => false
    | uconfid, uconfid => false
    | uconfid, _ => true
    | intpmuxid, abstcblsid => false 
    | intpmuxid, absecblsid => false 
    | intpmuxid, ostmid => false 
    | intpmuxid, curtid => false 
    | intpmuxid, ierid => false
    | intpmuxid, inthandlerid => false 
    | intpmuxid, inthandlerParamid => false
    | intpmuxid, exchandlerid => false 
    | intpmuxid, absptlsid => false
    | intpmuxid, seminfoid => false 
    | intpmuxid, absmutinfoid => false
    | intpmuxid, absmqattrid => false
    | intpmuxid, pblsid => false
    | intpmuxid, eblsid => false 
    | intpmuxid, evatomheapid => false
    | intpmuxid, evstructheapid => false
    | intpmuxid, evarrayheapid => false
    | intpmuxid, evlocid => false
    | intpmuxid, evptrid => false
    | intpmuxid, rootskid => false 
    | intpmuxid, allpartareaid => false
    | intpmuxid, sms_mpaxid => false
    | intpmuxid, ses_mpaxid => false
    | intpmuxid, xmpaxid => false
    | intpmuxid, xmpfarid => false
    | intpmuxid, xmpfsrid => false
    | intpmuxid, mdmaerrid => false
    | intpmuxid, ksdschedidxid => false
    | intpmuxid, ksdschedlenid => false
    | intpmuxid, kscurdomid => false
    | intpmuxid, kslastdomid => false
    | intpmuxid, ksdomtimeid => false
    | intpmuxid, ksdschedid => false
    | intpmuxid, dom2indexid => false
    | intpmuxid, uconfid => false
    | intpmuxid, intpmuxid => false
    | intpmuxid, _ => true
    | ksdomsid, abstcblsid => false 
    | ksdomsid, absecblsid => false 
    | ksdomsid, ostmid => false 
    | ksdomsid, curtid => false 
    | ksdomsid, ierid => false
    | ksdomsid, inthandlerid => false 
    | ksdomsid, inthandlerParamid => false
    | ksdomsid, exchandlerid => false 
    | ksdomsid, absptlsid => false
    | ksdomsid, seminfoid => false 
    | ksdomsid, absmutinfoid => false
    | ksdomsid, absmqattrid => false
    | ksdomsid, pblsid => false
    | ksdomsid, eblsid => false 
    | ksdomsid, evatomheapid => false
    | ksdomsid, evstructheapid => false
    | ksdomsid, evarrayheapid => false
    | ksdomsid, evlocid => false
    | ksdomsid, evptrid => false
    | ksdomsid, rootskid => false 
    | ksdomsid, allpartareaid => false
    | ksdomsid, sms_mpaxid => false
    | ksdomsid, ses_mpaxid => false
    | ksdomsid, xmpaxid => false
    | ksdomsid, xmpfarid => false
    | ksdomsid, xmpfsrid => false
    | ksdomsid, mdmaerrid => false
    | ksdomsid, ksdschedidxid => false
    | ksdomsid, ksdschedlenid => false
    | ksdomsid, kscurdomid => false
    | ksdomsid, kslastdomid => false
    | ksdomsid, ksdomtimeid => false
    | ksdomsid, ksdschedid => false
    | ksdomsid, dom2indexid => false
    | ksdomsid, uconfid => false
    | ksdomsid, intpmuxid => false
    | ksdomsid, ksdomsid => false
    | ksdomsid, _ => true
    | cpartnumid, abstcblsid => false 
    | cpartnumid, absecblsid => false 
    | cpartnumid, ostmid => false 
    | cpartnumid, curtid => false 
    | cpartnumid, ierid => false
    | cpartnumid, inthandlerid => false 
    | cpartnumid, inthandlerParamid => false
    | cpartnumid, exchandlerid => false 
    | cpartnumid, absptlsid => false
    | cpartnumid, seminfoid => false 
    | cpartnumid, absmutinfoid => false
    | cpartnumid, absmqattrid => false
    | cpartnumid, pblsid => false
    | cpartnumid, eblsid => false 
    | cpartnumid, evatomheapid => false
    | cpartnumid, evstructheapid => false
    | cpartnumid, evarrayheapid => false
    | cpartnumid, evlocid => false
    | cpartnumid, evptrid => false
    | cpartnumid, rootskid => false 
    | cpartnumid, allpartareaid => false
    | cpartnumid, sms_mpaxid => false
    | cpartnumid, ses_mpaxid => false
    | cpartnumid, xmpaxid => false
    | cpartnumid, xmpfarid => false
    | cpartnumid, xmpfsrid => false
    | cpartnumid, mdmaerrid => false
    | cpartnumid, ksdschedidxid => false
    | cpartnumid, ksdschedlenid => false
    | cpartnumid, kscurdomid => false
    | cpartnumid, kslastdomid => false
    | cpartnumid, ksdomtimeid => false
    | cpartnumid, ksdschedid => false
    | cpartnumid, dom2indexid => false
    | cpartnumid, uconfid => false
    | cpartnumid, intpmuxid => false
    | cpartnumid, ksdomsid => false
    | cpartnumid, cpartnumid => false
    | cpartnumid, _ => true
    (* end add by CNU *)
    (* add by SJTU *)
    | ostmrid, abstcblsid => false
    | ostmrid, absecblsid => false
    | ostmrid, ostmid => false
    | ostmrid, curtid => false
    | ostmrid, ierid => false
    | ostmrid, inthandlerid => false
    | ostmrid, inthandlerParamid => false
    | ostmrid, exchandlerid => false
    | ostmrid, absptlsid => false
    | ostmrid, seminfoid => false
    | ostmrid, absmutinfoid => false
    | ostmrid, absmqattrid => false
    | ostmrid, pblsid => false
    | ostmrid, eblsid => false
    | ostmrid, evatomheapid => false
    | ostmrid, evstructheapid => false
    | ostmrid, evarrayheapid => false
    | ostmrid, evlocid => false
    | ostmrid, evptrid => false
    | ostmrid, rootskid => false 
    | ostmrid, allpartareaid => false
    | ostmrid, sms_mpaxid => false
    | ostmrid, ses_mpaxid => false
    | ostmrid, xmpaxid => false
    | ostmrid, xmpfarid => false
    | ostmrid, xmpfsrid => false
    | ostmrid, mdmaerrid => false
    | ostmrid, ksdschedidxid => false
    | ostmrid, ksdschedlenid => false
    | ostmrid, kscurdomid => false
    | ostmrid, kslastdomid => false
    | ostmrid, ksdomtimeid => false
    | ostmrid, ksdschedid => false
    | ostmrid, dom2indexid => false
    | ostmrid, uconfid => false
    | ostmrid, intpmuxid => false
    | ostmrid, ksdomsid => false
    | ostmrid, cpartnumid => false
    | ostmrid, ostmrid => false
    | ostmrid, _ => true
    | osclkrateid, abstcblsid => false
    | osclkrateid, absecblsid => false
    | osclkrateid, ostmid => false
    | osclkrateid, curtid => false
    | osclkrateid, ierid => false
    | osclkrateid, inthandlerid => false
    | osclkrateid, inthandlerParamid => false
    | osclkrateid, exchandlerid => false
    | osclkrateid, absptlsid => false
    | osclkrateid, seminfoid => false
    | osclkrateid, absmutinfoid => false
    | osclkrateid, absmqattrid => false
    | osclkrateid, pblsid => false
    | osclkrateid, eblsid => false
    | osclkrateid, evatomheapid => false
    | osclkrateid, evstructheapid => false
    | osclkrateid, evarrayheapid => false
    | osclkrateid, evlocid => false
    | osclkrateid, evptrid => false
    | osclkrateid, rootskid => false 
    | osclkrateid, allpartareaid => false
    | osclkrateid, sms_mpaxid => false
    | osclkrateid, ses_mpaxid => false
    | osclkrateid, xmpaxid => false
    | osclkrateid, xmpfarid => false
    | osclkrateid, xmpfsrid => false
    | osclkrateid, mdmaerrid => false
    | osclkrateid, ksdschedidxid => false
    | osclkrateid, ksdschedlenid => false
    | osclkrateid, kscurdomid => false
    | osclkrateid, kslastdomid => false
    | osclkrateid, ksdomtimeid => false
    | osclkrateid, ksdschedid => false
    | osclkrateid, dom2indexid => false
    | osclkrateid, uconfid => false
    | osclkrateid, intpmuxid => false
    | osclkrateid, ksdomsid => false
    | osclkrateid, cpartnumid => false
    | osclkrateid, ostmrid => false
    | osclkrateid, osclkrateid => false
    | osclkrateid, _ => true
    | curcoreid, abstcblsid => false
    | curcoreid, absecblsid => false
    | curcoreid, ostmid => false
    | curcoreid, curtid => false
    | curcoreid, ierid => false
    | curcoreid, inthandlerid => false
    | curcoreid, inthandlerParamid => false
    | curcoreid, exchandlerid => false
    | curcoreid, absptlsid => false
    | curcoreid, seminfoid => false
    | curcoreid, absmutinfoid => false
    | curcoreid, absmqattrid => false
    | curcoreid, pblsid => false
    | curcoreid, eblsid => false
    | curcoreid, evatomheapid => false
    | curcoreid, evstructheapid => false
    | curcoreid, evarrayheapid => false
    | curcoreid, evlocid => false
    | curcoreid, evptrid => false
    | curcoreid, rootskid => false 
    | curcoreid, allpartareaid => false
    | curcoreid, sms_mpaxid => false
    | curcoreid, ses_mpaxid => false
    | curcoreid, xmpaxid => false
    | curcoreid, xmpfarid => false
    | curcoreid, xmpfsrid => false
    | curcoreid, mdmaerrid => false
    | curcoreid, ksdschedidxid => false
    | curcoreid, ksdschedlenid => false
    | curcoreid, kscurdomid => false
    | curcoreid, kslastdomid => false
    | curcoreid, ksdomtimeid => false
    | curcoreid, ksdschedid => false
    | curcoreid, dom2indexid => false
    | curcoreid, uconfid => false
    | curcoreid, intpmuxid => false
    | curcoreid, ksdomsid => false
    | curcoreid, cpartnumid => false
    | curcoreid, ostmrid => false
    | curcoreid, osclkrateid => false
    | curcoreid, curcoreid => false
    | curcoreid, _ => true
    | oscoreheapid, abstcblsid => false
    | oscoreheapid, absecblsid => false
    | oscoreheapid, ostmid => false
    | oscoreheapid, curtid => false
    | oscoreheapid, ierid => false
    | oscoreheapid, inthandlerid => false
    | oscoreheapid, inthandlerParamid => false
    | oscoreheapid, exchandlerid => false
    | oscoreheapid, absptlsid => false
    | oscoreheapid, seminfoid => false
    | oscoreheapid, absmutinfoid => false
    | oscoreheapid, absmqattrid => false
    | oscoreheapid, pblsid => false
    | oscoreheapid, eblsid => false
    | oscoreheapid, evatomheapid => false
    | oscoreheapid, evstructheapid => false
    | oscoreheapid, evarrayheapid => false
    | oscoreheapid, evlocid => false
    | oscoreheapid, evptrid => false
    | oscoreheapid, rootskid => false 
    | oscoreheapid, allpartareaid => false
    | oscoreheapid, sms_mpaxid => false
    | oscoreheapid, ses_mpaxid => false
    | oscoreheapid, xmpaxid => false
    | oscoreheapid, xmpfarid => false
    | oscoreheapid, xmpfsrid => false
    | oscoreheapid, mdmaerrid => false
    | oscoreheapid, ksdschedidxid => false
    | oscoreheapid, ksdschedlenid => false
    | oscoreheapid, kscurdomid => false
    | oscoreheapid, kslastdomid => false
    | oscoreheapid, ksdomtimeid => false
    | oscoreheapid, ksdschedid => false
    | oscoreheapid, dom2indexid => false
    | oscoreheapid, uconfid => false
    | oscoreheapid, intpmuxid => false
    | oscoreheapid, ksdomsid => false
    | oscoreheapid, cpartnumid => false
    | oscoreheapid, ostmrid => false
    | oscoreheapid, osclkrateid => false
    | oscoreheapid, curcoreid => false
    | oscoreheapid, oscoreheapid => false
    | oscoreheapid, _ => true
    | ipcsendid, abstcblsid => false
    | ipcsendid, absecblsid => false
    | ipcsendid, ostmid => false
    | ipcsendid, curtid => false
    | ipcsendid, ierid => false
    | ipcsendid, inthandlerid => false
    | ipcsendid, inthandlerParamid => false
    | ipcsendid, exchandlerid => false
    | ipcsendid, absptlsid => false
    | ipcsendid, seminfoid => false
    | ipcsendid, absmutinfoid => false
    | ipcsendid, absmqattrid => false
    | ipcsendid, pblsid => false
    | ipcsendid, eblsid => false
    | ipcsendid, evatomheapid => false
    | ipcsendid, evstructheapid => false
    | ipcsendid, evarrayheapid => false
    | ipcsendid, evlocid => false
    | ipcsendid, evptrid => false
    | ipcsendid, rootskid => false 
    | ipcsendid, allpartareaid => false
    | ipcsendid, sms_mpaxid => false
    | ipcsendid, ses_mpaxid => false
    | ipcsendid, xmpaxid => false
    | ipcsendid, xmpfarid => false
    | ipcsendid, xmpfsrid => false
    | ipcsendid, mdmaerrid => false
    | ipcsendid, ksdschedidxid => false
    | ipcsendid, ksdschedlenid => false
    | ipcsendid, kscurdomid => false
    | ipcsendid, kslastdomid => false
    | ipcsendid, ksdomtimeid => false
    | ipcsendid, ksdschedid => false
    | ipcsendid, dom2indexid => false
    | ipcsendid, uconfid => false
    | ipcsendid, intpmuxid => false
    | ipcsendid, ksdomsid => false
    | ipcsendid, cpartnumid => false
    | ipcsendid, ostmrid => false
    | ipcsendid, osclkrateid => false
    | ipcsendid, curcoreid => false
    | ipcsendid, oscoreheapid => false
    | ipcsendid, ipcsendid => false
    | ipcsendid, _ => true
    | ipcrecvid, abstcblsid => false
    | ipcrecvid, absecblsid => false
    | ipcrecvid, ostmid => false
    | ipcrecvid, curtid => false
    | ipcrecvid, ierid => false
    | ipcrecvid, inthandlerid => false
    | ipcrecvid, inthandlerParamid => false
    | ipcrecvid, exchandlerid => false
    | ipcrecvid, absptlsid => false
    | ipcrecvid, seminfoid => false
    | ipcrecvid, absmutinfoid => false
    | ipcrecvid, absmqattrid => false
    | ipcrecvid, pblsid => false
    | ipcrecvid, eblsid => false
    | ipcrecvid, evatomheapid => false
    | ipcrecvid, evstructheapid => false
    | ipcrecvid, evarrayheapid => false
    | ipcrecvid, evlocid => false
    | ipcrecvid, evptrid => false
    | ipcrecvid, rootskid => false 
    | ipcrecvid, allpartareaid => false
    | ipcrecvid, sms_mpaxid => false
    | ipcrecvid, ses_mpaxid => false
    | ipcrecvid, xmpaxid => false
    | ipcrecvid, xmpfarid => false
    | ipcrecvid, xmpfsrid => false
    | ipcrecvid, mdmaerrid => false
    | ipcrecvid, ksdschedidxid => false
    | ipcrecvid, ksdschedlenid => false
    | ipcrecvid, kscurdomid => false
    | ipcrecvid, kslastdomid => false
    | ipcrecvid, ksdomtimeid => false
    | ipcrecvid, ksdschedid => false
    | ipcrecvid, dom2indexid => false
    | ipcrecvid, uconfid => false
    | ipcrecvid, intpmuxid => false
    | ipcrecvid, ksdomsid => false
    | ipcrecvid, cpartnumid => false
    | ipcrecvid, ostmrid => false
    | ipcrecvid, osclkrateid => false
    | ipcrecvid, curcoreid => false
    | ipcrecvid, oscoreheapid => false
    | ipcrecvid, ipcsendid => false
    | ipcrecvid, ipcrecvid => false
    | ipcrecvid, _ => true
    | ipcsemid, abstcblsid => false
    | ipcsemid, absecblsid => false
    | ipcsemid, ostmid => false
    | ipcsemid, curtid => false
    | ipcsemid, ierid => false
    | ipcsemid, inthandlerid => false
    | ipcsemid, inthandlerParamid => false
    | ipcsemid, exchandlerid => false
    | ipcsemid, absptlsid => false
    | ipcsemid, seminfoid => false
    | ipcsemid, absmutinfoid => false
    | ipcsemid, absmqattrid => false
    | ipcsemid, pblsid => false
    | ipcsemid, eblsid => false
    | ipcsemid, evatomheapid => false
    | ipcsemid, evstructheapid => false
    | ipcsemid, evarrayheapid => false
    | ipcsemid, evlocid => false
    | ipcsemid, evptrid => false
    | ipcsemid, rootskid => false 
    | ipcsemid, allpartareaid => false
    | ipcsemid, sms_mpaxid => false
    | ipcsemid, ses_mpaxid => false
    | ipcsemid, xmpaxid => false
    | ipcsemid, xmpfarid => false
    | ipcsemid, xmpfsrid => false
    | ipcsemid, mdmaerrid => false
    | ipcsemid, ksdschedidxid => false
    | ipcsemid, ksdschedlenid => false
    | ipcsemid, kscurdomid => false
    | ipcsemid, kslastdomid => false
    | ipcsemid, ksdomtimeid => false
    | ipcsemid, ksdschedid => false
    | ipcsemid, dom2indexid => false
    | ipcsemid, uconfid => false
    | ipcsemid, intpmuxid => false
    | ipcsemid, ksdomsid => false
    | ipcsemid, cpartnumid => false
    | ipcsemid, ostmrid => false
    | ipcsemid, osclkrateid => false
    | ipcsemid, curcoreid => false
    | ipcsemid, oscoreheapid => false
    | ipcsemid, ipcsendid => false
    | ipcsemid, ipcrecvid => false
    | ipcsemid, ipcsemid => false
    | ipcsemid, _ => true
    | ipcsendsemid, abstcblsid => false
    | ipcsendsemid, absecblsid => false
    | ipcsendsemid, ostmid => false
    | ipcsendsemid, curtid => false
    | ipcsendsemid, ierid => false
    | ipcsendsemid, inthandlerid => false
    | ipcsendsemid, inthandlerParamid => false
    | ipcsendsemid, exchandlerid => false
    | ipcsendsemid, absptlsid => false
    | ipcsendsemid, seminfoid => false
    | ipcsendsemid, absmutinfoid => false
    | ipcsendsemid, absmqattrid => false
    | ipcsendsemid, pblsid => false
    | ipcsendsemid, eblsid => false
    | ipcsendsemid, evatomheapid => false
    | ipcsendsemid, evstructheapid => false
    | ipcsendsemid, evarrayheapid => false
    | ipcsendsemid, evlocid => false
    | ipcsendsemid, evptrid => false
    | ipcsendsemid, rootskid => false 
    | ipcsendsemid, allpartareaid => false
    | ipcsendsemid, sms_mpaxid => false
    | ipcsendsemid, ses_mpaxid => false
    | ipcsendsemid, xmpaxid => false
    | ipcsendsemid, xmpfarid => false
    | ipcsendsemid, xmpfsrid => false
    | ipcsendsemid, mdmaerrid => false
    | ipcsendsemid, ksdschedidxid => false
    | ipcsendsemid, ksdschedlenid => false
    | ipcsendsemid, kscurdomid => false
    | ipcsendsemid, kslastdomid => false
    | ipcsendsemid, ksdomtimeid => false
    | ipcsendsemid, ksdschedid => false
    | ipcsendsemid, dom2indexid => false
    | ipcsendsemid, uconfid => false
    | ipcsendsemid, intpmuxid => false
    | ipcsendsemid, ksdomsid => false
    | ipcsendsemid, cpartnumid => false
    | ipcsendsemid, ostmrid => false
    | ipcsendsemid, osclkrateid => false
    | ipcsendsemid, curcoreid => false
    | ipcsendsemid, oscoreheapid => false
    | ipcsendsemid, ipcsendid => false
    | ipcsendsemid, ipcrecvid => false
    | ipcsendsemid, ipcsemid => false
    | ipcsendsemid, ipcsendsemid => false
    | ipcsendsemid, _ => true
    | ipcsemshareid, abstcblsid => false
    | ipcsemshareid, absecblsid => false
    | ipcsemshareid, ostmid => false
    | ipcsemshareid, curtid => false
    | ipcsemshareid, ierid => false
    | ipcsemshareid, inthandlerid => false
    | ipcsemshareid, inthandlerParamid => false
    | ipcsemshareid, exchandlerid => false
    | ipcsemshareid, absptlsid => false
    | ipcsemshareid, seminfoid => false
    | ipcsemshareid, absmutinfoid => false
    | ipcsemshareid, absmqattrid => false
    | ipcsemshareid, pblsid => false
    | ipcsemshareid, eblsid => false
    | ipcsemshareid, evatomheapid => false
    | ipcsemshareid, evstructheapid => false
    | ipcsemshareid, evarrayheapid => false
    | ipcsemshareid, evlocid => false
    | ipcsemshareid, evptrid => false
    | ipcsemshareid, rootskid => false 
    | ipcsemshareid, allpartareaid => false
    | ipcsemshareid, sms_mpaxid => false
    | ipcsemshareid, ses_mpaxid => false
    | ipcsemshareid, xmpaxid => false
    | ipcsemshareid, xmpfarid => false
    | ipcsemshareid, xmpfsrid => false
    | ipcsemshareid, mdmaerrid => false
    | ipcsemshareid, ksdschedidxid => false
    | ipcsemshareid, ksdschedlenid => false
    | ipcsemshareid, kscurdomid => false
    | ipcsemshareid, kslastdomid => false
    | ipcsemshareid, ksdomtimeid => false
    | ipcsemshareid, ksdschedid => false
    | ipcsemshareid, dom2indexid => false
    | ipcsemshareid, uconfid => false
    | ipcsemshareid, intpmuxid => false
    | ipcsemshareid, ksdomsid => false
    | ipcsemshareid, cpartnumid => false
    | ipcsemshareid, ostmrid => false
    | ipcsemshareid, osclkrateid => false
    | ipcsemshareid, curcoreid => false
    | ipcsemshareid, oscoreheapid => false
    | ipcsemshareid, ipcsendid => false
    | ipcsemshareid, ipcrecvid => false
    | ipcsemshareid, ipcsemid => false
    | ipcsemshareid, ipcsendsemid => false
    | ipcsemshareid, ipcsemshareid => false
    | ipcsemshareid, _ => true
    | ipcbroadid, abstcblsid => false
    | ipcbroadid, absecblsid => false
    | ipcbroadid, ostmid => false
    | ipcbroadid, curtid => false
    | ipcbroadid, ierid => false
    | ipcbroadid, inthandlerid => false
    | ipcbroadid, inthandlerParamid => false
    | ipcbroadid, exchandlerid => false
    | ipcbroadid, absptlsid => false
    | ipcbroadid, seminfoid => false
    | ipcbroadid, absmutinfoid => false
    | ipcbroadid, absmqattrid => false
    | ipcbroadid, pblsid => false
    | ipcbroadid, eblsid => false
    | ipcbroadid, evatomheapid => false
    | ipcbroadid, evstructheapid => false
    | ipcbroadid, evarrayheapid => false
    | ipcbroadid, evlocid => false
    | ipcbroadid, evptrid => false
    | ipcbroadid, rootskid => false 
    | ipcbroadid, allpartareaid => false
    | ipcbroadid, sms_mpaxid => false
    | ipcbroadid, ses_mpaxid => false
    | ipcbroadid, xmpaxid => false
    | ipcbroadid, xmpfarid => false
    | ipcbroadid, xmpfsrid => false
    | ipcbroadid, mdmaerrid => false
    | ipcbroadid, ksdschedidxid => false
    | ipcbroadid, ksdschedlenid => false
    | ipcbroadid, kscurdomid => false
    | ipcbroadid, kslastdomid => false
    | ipcbroadid, ksdomtimeid => false
    | ipcbroadid, ksdschedid => false
    | ipcbroadid, dom2indexid => false
    | ipcbroadid, uconfid => false
    | ipcbroadid, intpmuxid => false
    | ipcbroadid, ksdomsid => false
    | ipcbroadid, cpartnumid => false
    | ipcbroadid, ostmrid => false
    | ipcbroadid, osclkrateid => false
    | ipcbroadid, curcoreid => false
    | ipcbroadid, oscoreheapid => false
    | ipcbroadid, ipcsendid => false
    | ipcbroadid, ipcrecvid => false
    | ipcbroadid, ipcsemid => false
    | ipcbroadid, ipcsendsemid => false
    | ipcbroadid, ipcsemshareid => false
    | ipcbroadid, ipcbroadid => false
    | ipcbroadid, _ => true
    | ipcgrid, abstcblsid => false
    | ipcgrid, absecblsid => false
    | ipcgrid, ostmid => false
    | ipcgrid, curtid => false
    | ipcgrid, ierid => false
    | ipcgrid, inthandlerid => false
    | ipcgrid, inthandlerParamid => false
    | ipcgrid, exchandlerid => false
    | ipcgrid, absptlsid => false
    | ipcgrid, seminfoid => false
    | ipcgrid, absmutinfoid => false
    | ipcgrid, absmqattrid => false
    | ipcgrid, pblsid => false
    | ipcgrid, eblsid => false
    | ipcgrid, evatomheapid => false
    | ipcgrid, evstructheapid => false
    | ipcgrid, evarrayheapid => false
    | ipcgrid, evlocid => false
    | ipcgrid, evptrid => false
    | ipcgrid, rootskid => false 
    | ipcgrid, allpartareaid => false
    | ipcgrid, sms_mpaxid => false
    | ipcgrid, ses_mpaxid => false
    | ipcgrid, xmpaxid => false
    | ipcgrid, xmpfarid => false
    | ipcgrid, xmpfsrid => false
    | ipcgrid, mdmaerrid => false
    | ipcgrid, ksdschedidxid => false
    | ipcgrid, ksdschedlenid => false
    | ipcgrid, kscurdomid => false
    | ipcgrid, kslastdomid => false
    | ipcgrid, ksdomtimeid => false
    | ipcgrid, ksdschedid => false
    | ipcgrid, dom2indexid => false
    | ipcgrid, uconfid => false
    | ipcgrid, intpmuxid => false
    | ipcgrid, ksdomsid => false
    | ipcgrid, cpartnumid => false
    | ipcgrid, ostmrid => false
    | ipcgrid, osclkrateid => false
    | ipcgrid, curcoreid => false
    | ipcgrid, oscoreheapid => false
    | ipcgrid, ipcsendid => false
    | ipcgrid, ipcrecvid => false
    | ipcgrid, ipcsemid => false
    | ipcgrid, ipcsendsemid => false
    | ipcgrid, ipcsemshareid => false
    | ipcgrid, ipcbroadid => false
    | ipcgrid, ipcgrid => false
    | ipcgrid, _ => true
    | freedynid, abstcblsid => false
    | freedynid, absecblsid => false
    | freedynid, ostmid => false
    | freedynid, curtid => false
    | freedynid, ierid => false
    | freedynid, inthandlerid => false
    | freedynid, inthandlerParamid => false
    | freedynid, exchandlerid => false
    | freedynid, absptlsid => false
    | freedynid, seminfoid => false
    | freedynid, absmutinfoid => false
    | freedynid, absmqattrid => false
    | freedynid, pblsid => false
    | freedynid, eblsid => false
    | freedynid, evatomheapid => false
    | freedynid, evstructheapid => false
    | freedynid, evarrayheapid => false
    | freedynid, evlocid => false
    | freedynid, evptrid => false
    | freedynid, rootskid => false 
    | freedynid, allpartareaid => false
    | freedynid, sms_mpaxid => false
    | freedynid, ses_mpaxid => false
    | freedynid, xmpaxid => false
    | freedynid, xmpfarid => false
    | freedynid, xmpfsrid => false
    | freedynid, mdmaerrid => false
    | freedynid, ksdschedidxid => false
    | freedynid, ksdschedlenid => false
    | freedynid, kscurdomid => false
    | freedynid, kslastdomid => false
    | freedynid, ksdomtimeid => false
    | freedynid, ksdschedid => false
    | freedynid, dom2indexid => false
    | freedynid, uconfid => false
    | freedynid, intpmuxid => false
    | freedynid, ksdomsid => false
    | freedynid, cpartnumid => false
    | freedynid, ostmrid => false
    | freedynid, osclkrateid => false
    | freedynid, curcoreid => false
    | freedynid, oscoreheapid => false
    | freedynid, ipcsendid => false
    | freedynid, ipcrecvid => false
    | freedynid, ipcsemid => false
    | freedynid, ipcsendsemid => false
    | freedynid, ipcsemshareid => false
    | freedynid, ipcbroadid => false
    | freedynid, ipcgrid => false
    | freedynid, freedynid => false
    | freedynid, _ => true

  (* end add by SJTU *)
    | dynheapid, abstcblsid => false
    | dynheapid, absecblsid => false
    | dynheapid, ostmid => false
    | dynheapid, curtid => false
    | dynheapid, ierid => false
    | dynheapid, inthandlerid => false
    | dynheapid, inthandlerParamid => false
    | dynheapid, exchandlerid => false
    | dynheapid, absptlsid => false
    | dynheapid, seminfoid => false
    | dynheapid, absmutinfoid => false
    | dynheapid, absmqattrid => false
    | dynheapid, pblsid => false
    | dynheapid, eblsid => false
    | dynheapid, evatomheapid => false
    | dynheapid, evstructheapid => false
    | dynheapid, evarrayheapid => false
    | dynheapid, evlocid => false
    | dynheapid, evptrid => false
    | dynheapid, rootskid => false 
    | dynheapid, allpartareaid => false
    | dynheapid, sms_mpaxid => false
    | dynheapid, ses_mpaxid => false
    | dynheapid, xmpaxid => false
    | dynheapid, xmpfarid => false
    | dynheapid, xmpfsrid => false
    | dynheapid, mdmaerrid => false
    | dynheapid, ksdschedidxid => false
    | dynheapid, ksdschedlenid => false
    | dynheapid, kscurdomid => false
    | dynheapid, kslastdomid => false
    | dynheapid, ksdomtimeid => false
    | dynheapid, ksdschedid => false
    | dynheapid, dom2indexid => false
    | dynheapid, uconfid => false
    | dynheapid, intpmuxid => false
    | dynheapid, ksdomsid => false
    | dynheapid, cpartnumid => false
    | dynheapid, ostmrid => false
    | dynheapid, osclkrateid => false
    | dynheapid, curcoreid => false
    | dynheapid, oscoreheapid => false
    | dynheapid, ipcsendid => false
    | dynheapid, ipcrecvid => false
    | dynheapid, ipcsemid => false
    | dynheapid, ipcsendsemid => false
    | dynheapid, ipcsemshareid => false
    | dynheapid, ipcbroadid => false
    | dynheapid, ipcgrid => false
    | dynheapid, freedynid => false
    | dynheapid, dynheapid => false
    | dynheapid, _ => true

    | cspaceid, abstcblsid => false
    | cspaceid, absecblsid => false
    | cspaceid, ostmid => false
    | cspaceid, curtid => false
    | cspaceid, ierid => false
    | cspaceid, inthandlerid => false
    | cspaceid, inthandlerParamid => false
    | cspaceid, exchandlerid => false
    | cspaceid, absptlsid => false
    | cspaceid, seminfoid => false
    | cspaceid, absmutinfoid => false
    | cspaceid, absmqattrid => false
    | cspaceid, pblsid => false
    | cspaceid, eblsid => false
    | cspaceid, evatomheapid => false
    | cspaceid, evstructheapid => false
    | cspaceid, evarrayheapid => false
    | cspaceid, evlocid => false
    | cspaceid, evptrid => false
    | cspaceid, rootskid => false 
    | cspaceid, allpartareaid => false
    | cspaceid, sms_mpaxid => false
    | cspaceid, ses_mpaxid => false
    | cspaceid, xmpaxid => false
    | cspaceid, xmpfarid => false
    | cspaceid, xmpfsrid => false
    | cspaceid, mdmaerrid => false
    | cspaceid, ksdschedidxid => false
    | cspaceid, ksdschedlenid => false
    | cspaceid, kscurdomid => false
    | cspaceid, kslastdomid => false
    | cspaceid, ksdomtimeid => false
    | cspaceid, ksdschedid => false
    | cspaceid, dom2indexid => false
    | cspaceid, uconfid => false
    | cspaceid, intpmuxid => false
    | cspaceid, ksdomsid => false
    | cspaceid, cpartnumid => false
    | cspaceid, ostmrid => false
    | cspaceid, osclkrateid => false
    | cspaceid, curcoreid => false
    | cspaceid, oscoreheapid => false
    | cspaceid, ipcsendid => false
    | cspaceid, ipcrecvid => false
    | cspaceid, ipcsemid => false
    | cspaceid, ipcsendsemid => false
    | cspaceid, ipcsemshareid => false
    | cspaceid, ipcbroadid => false
    | cspaceid, ipcgrid => false
    | cspaceid, freedynid => false
    | cspaceid, dynheapid => false
    | cspaceid, cspaceid => false
    | cspaceid, _ => true
    | abspthattrid, abstcblsid => false
    | abspthattrid, absecblsid => false
    | abspthattrid, ostmid => false
    | abspthattrid, curtid => false
    | abspthattrid, ierid => false
    | abspthattrid, inthandlerid => false
    | abspthattrid, inthandlerParamid => false
    | abspthattrid, exchandlerid => false
    | abspthattrid, absptlsid => false
    | abspthattrid, seminfoid => false
    | abspthattrid, absmutinfoid => false
    | abspthattrid, absmqattrid => false
    | abspthattrid, pblsid => false
    | abspthattrid, eblsid => false
    | abspthattrid, evatomheapid => false
    | abspthattrid, evstructheapid => false
    | abspthattrid, evarrayheapid => false
    | abspthattrid, evlocid => false
    | abspthattrid, evptrid => false
    | abspthattrid, rootskid => false 
    | abspthattrid, allpartareaid => false
    | abspthattrid, sms_mpaxid => false
    | abspthattrid, ses_mpaxid => false
    | abspthattrid, xmpaxid => false
    | abspthattrid, xmpfarid => false
    | abspthattrid, xmpfsrid => false
    | abspthattrid, mdmaerrid => false
    | abspthattrid, ksdschedidxid => false
    | abspthattrid, ksdschedlenid => false
    | abspthattrid, kscurdomid => false
    | abspthattrid, kslastdomid => false
    | abspthattrid, ksdomtimeid => false
    | abspthattrid, ksdschedid => false
    | abspthattrid, dom2indexid => false
    | abspthattrid, uconfid => false
    | abspthattrid, intpmuxid => false
    | abspthattrid, ksdomsid => false
    | abspthattrid, cpartnumid => false
    | abspthattrid, ostmrid => false
    | abspthattrid, osclkrateid => false
    | abspthattrid, curcoreid => false
    | abspthattrid, oscoreheapid => false
    | abspthattrid, ipcsendid => false
    | abspthattrid, ipcrecvid => false
    | abspthattrid, ipcsemid => false
    | abspthattrid, ipcsendsemid => false
    | abspthattrid, ipcsemshareid => false
    | abspthattrid, ipcbroadid => false
    | abspthattrid, ipcgrid => false
    | abspthattrid, freedynid => false
    | abspthattrid, dynheapid => false
    | abspthattrid, cspaceid => false
    | abspthattrid, abspthattrid => false
    | abspthattrid, _ => true
    | oskportid, abstcblsid => false
    | oskportid, absecblsid => false
    | oskportid, ostmid => false
    | oskportid, curtid => false
    | oskportid, ierid => false
    | oskportid, inthandlerid => false
    | oskportid, inthandlerParamid => false
    | oskportid, exchandlerid => false
    | oskportid, absptlsid => false
    | oskportid, seminfoid => false
    | oskportid, absmutinfoid => false
    | oskportid, absmqattrid => false
    | oskportid, pblsid => false
    | oskportid, eblsid => false
    | oskportid, evatomheapid => false
    | oskportid, evstructheapid => false
    | oskportid, evarrayheapid => false
    | oskportid, evlocid => false
    | oskportid, evptrid => false
    | oskportid, rootskid => false 
    | oskportid, allpartareaid => false
    | oskportid, sms_mpaxid => false
    | oskportid, ses_mpaxid => false
    | oskportid, xmpaxid => false
    | oskportid, xmpfarid => false
    | oskportid, xmpfsrid => false
    | oskportid, mdmaerrid => false
    | oskportid, ksdschedidxid => false
    | oskportid, ksdschedlenid => false
    | oskportid, kscurdomid => false
    | oskportid, kslastdomid => false
    | oskportid, ksdomtimeid => false
    | oskportid, ksdschedid => false
    | oskportid, dom2indexid => false
    | oskportid, uconfid => false
    | oskportid, intpmuxid => false
    | oskportid, ksdomsid => false
    | oskportid, cpartnumid => false
    | oskportid, ostmrid => false
    | oskportid, osclkrateid => false
    | oskportid, curcoreid => false
    | oskportid, oscoreheapid => false
    | oskportid, ipcsendid => false
    | oskportid, ipcrecvid => false
    | oskportid, ipcsemid => false
    | oskportid, ipcsendsemid => false
    | oskportid, ipcsemshareid => false
    | oskportid, ipcbroadid => false
    | oskportid, ipcgrid => false
    | oskportid, freedynid => false
    | oskportid, dynheapid => false
    | oskportid, cspaceid => false
    | oskportid, abspthattrid => false
    | oskportid, oskportid => false
    | oskportid, _ => true
    | oschannelid, abstcblsid => false
    | oschannelid, absecblsid => false
    | oschannelid, ostmid => false
    | oschannelid, curtid => false
    | oschannelid, ierid => false
    | oschannelid, inthandlerid => false
    | oschannelid, inthandlerParamid => false
    | oschannelid, exchandlerid => false
    | oschannelid, absptlsid => false
    | oschannelid, seminfoid => false
    | oschannelid, absmutinfoid => false
    | oschannelid, absmqattrid => false
    | oschannelid, pblsid => false
    | oschannelid, eblsid => false
    | oschannelid, evatomheapid => false
    | oschannelid, evstructheapid => false
    | oschannelid, evarrayheapid => false
    | oschannelid, evlocid => false
    | oschannelid, evptrid => false
    | oschannelid, rootskid => false 
    | oschannelid, allpartareaid => false
    | oschannelid, sms_mpaxid => false
    | oschannelid, ses_mpaxid => false
    | oschannelid, xmpaxid => false
    | oschannelid, xmpfarid => false
    | oschannelid, xmpfsrid => false
    | oschannelid, mdmaerrid => false
    | oschannelid, ksdschedidxid => false
    | oschannelid, ksdschedlenid => false
    | oschannelid, kscurdomid => false
    | oschannelid, kslastdomid => false
    | oschannelid, ksdomtimeid => false
    | oschannelid, ksdschedid => false
    | oschannelid, dom2indexid => false
    | oschannelid, uconfid => false
    | oschannelid, intpmuxid => false
    | oschannelid, ksdomsid => false
    | oschannelid, cpartnumid => false
    | oschannelid, ostmrid => false
    | oschannelid, osclkrateid => false
    | oschannelid, curcoreid => false
    | oschannelid, oscoreheapid => false
    | oschannelid, ipcsendid => false
    | oschannelid, ipcrecvid => false
    | oschannelid, ipcsemid => false
    | oschannelid, ipcsendsemid => false
    | oschannelid, ipcsemshareid => false
    | oschannelid, ipcbroadid => false
    | oschannelid, ipcgrid => false
    | oschannelid, freedynid => false
    | oschannelid, dynheapid => false
    | oschannelid, cspaceid => false
    | oschannelid, abspthattrid => false
    | oschannelid, oskportid => false
    | oschannelid, oschannelid => false
    | oschannelid, _ => true
    | osdomainportid, abstcblsid => false
    | osdomainportid, absecblsid => false
    | osdomainportid, ostmid => false
    | osdomainportid, curtid => false
    | osdomainportid, ierid => false
    | osdomainportid, inthandlerid => false
    | osdomainportid, inthandlerParamid => false
    | osdomainportid, exchandlerid => false
    | osdomainportid, absptlsid => false
    | osdomainportid, seminfoid => false
    | osdomainportid, absmutinfoid => false
    | osdomainportid, absmqattrid => false
    | osdomainportid, pblsid => false
    | osdomainportid, eblsid => false
    | osdomainportid, evatomheapid => false
    | osdomainportid, evstructheapid => false
    | osdomainportid, evarrayheapid => false
    | osdomainportid, evlocid => false
    | osdomainportid, evptrid => false
    | osdomainportid, rootskid => false 
    | osdomainportid, allpartareaid => false
    | osdomainportid, sms_mpaxid => false
    | osdomainportid, ses_mpaxid => false
    | osdomainportid, xmpaxid => false
    | osdomainportid, xmpfarid => false
    | osdomainportid, xmpfsrid => false
    | osdomainportid, mdmaerrid => false
    | osdomainportid, ksdschedidxid => false
    | osdomainportid, ksdschedlenid => false
    | osdomainportid, kscurdomid => false
    | osdomainportid, kslastdomid => false
    | osdomainportid, ksdomtimeid => false
    | osdomainportid, ksdschedid => false
    | osdomainportid, dom2indexid => false
    | osdomainportid, uconfid => false
    | osdomainportid, intpmuxid => false
    | osdomainportid, ksdomsid => false
    | osdomainportid, cpartnumid => false
    | osdomainportid, ostmrid => false
    | osdomainportid, osclkrateid => false
    | osdomainportid, curcoreid => false
    | osdomainportid, oscoreheapid => false
    | osdomainportid, ipcsendid => false
    | osdomainportid, ipcrecvid => false
    | osdomainportid, ipcsemid => false
    | osdomainportid, ipcsendsemid => false
    | osdomainportid, ipcsemshareid => false
    | osdomainportid, ipcbroadid => false
    | osdomainportid, ipcgrid => false
    | osdomainportid, freedynid => false
    | osdomainportid, dynheapid => false
    | osdomainportid, cspaceid => false
    | osdomainportid, abspthattrid => false
    | osdomainportid, oskportid => false
    | osdomainportid, oschannelid => false
    | osdomainportid, osdomainportid => false
    | osdomainportid, _ => true
    | oscoreportplid, _ => false
  end.

Module absdataidspec.
  Definition A := absdataid.
  Definition beq := absdataid_eq.
  Definition blt := absdataid_lt.
 
Lemma beq_true_eq : forall a a' : A,
    beq a a' = true -> a = a'.
Proof.
  intros.
  destruct a,a';simpl in H;auto;tryfalse.
Qed.    


Lemma beq_false_neq : forall a a' : A,
    beq a a' = false -> a <> a'.
Proof. 
  intros.
  destruct a,a';simpl in H; introv Hf; auto;tryfalse.
Qed.  

Lemma eq_beq_true : forall a a' : A,
    a = a' -> beq a a' = true.
Proof.
  intros.
  destruct a,a';simpl in H;auto;tryfalse.
Qed.

Lemma neq_beq_false : forall a a' : A,
    a <> a' -> beq a a' = false.
Proof.
intros.
destruct a ,a';simpl in H;auto;tryfalse.
Qed.

Lemma blt_trans : 
  forall a a' a'' : A,
    blt a a' = true -> blt a' a'' = true -> blt a a'' = true.
Proof.
  unfold blt; intros.
  destruct a'; simpl in H,H0; destruct a''; auto; tryfalse;
  try solve[ destruct a; simpl in H; auto; tryfalse].
(*   destruct a,a',a'';simpl in H, H0;auto;tryfalse. *)
Qed.

Lemma blt_irrefl :
  forall a : A,
    blt a a = false.
Proof.  
  unfold blt; intros.
  destruct a;simpl;auto.
Qed.

Lemma blt_asym : 
  forall a b : A, 
    blt a b = true -> blt b a = false.
Proof.  
  unfold blt; intros.
  destruct a,b;simpl in *;auto;tryfalse.
Qed.

Lemma blt_beq_dec :
  forall a b : A,
    {blt a b = true} + {beq a b = true} + {blt b a = true}.
Proof.
  unfold blt; unfold beq; intros.
  remember (absdataid_lt a b) as bool1; destruct bool1.
  left; left; auto.
  remember (absdataid_eq a b) as bool2; destruct bool2.
  left; right; auto.
  destruct a,b;simpl in *;auto;tryfalse.
Qed.  


End absdataidspec.


(******************************************************* ADD FOR PARTITION **********************************************************)
(******************************************************* ADD FOR PARTITION **********************************************************)
Inductive direction : Type :=
| SourceP | DestinationP (next: option addrval).

Definition port_coreNum := nat.
Definition port_domain := nat.
Definition port_id:= nat.
Definition port_status:= nat.
Definition port_intick := nat.
Definition port_outick := nat.
Definition port_queue := list (list msg ).
Inductive Portt : Type := 
| SamplePort : option (list msg) -> Portt
| QueuePort  : nat(*port_size*) -> port_queue -> Portt.
Definition Port : Type := (port_coreNum * port_domain * port_id * direction * port_status * port_intick * port_outick * Portt)%type.
(* Module about abstract OSDomainPortPtrList *)
Module absdomainport.
  Definition B := Port.
  Definition holder : B := (0%nat ,0%nat ,0%nat, SourceP, 0%nat , 0%nat, 0%nat, SamplePort None).
End absdomainport. 

Module DomainPortMod := MapLib.MapFun tidspec absdomainport.

Program Instance DomainPortMap: PermMap tid absdomainport.B DomainPortMod.map := 
 {
    usePerm := DomainPortMod.usePerm;
    isRw := DomainPortMod.isRw;
    flip := DomainPortMod.flip;
    sameV := DomainPortMod.sameV;
    same := DomainPortMod.same;
    emp := DomainPortMod.emp;
    join := DomainPortMod.join;
    del := DomainPortMod.del;
    get := DomainPortMod.get;
    set := DomainPortMod.set;
    sig := DomainPortMod.sig;
    merge := DomainPortMod.merge;
    minus := DomainPortMod.minus;
    map_dec_a := DomainPortMod.map_dec_a
}.

Next Obligation.
  apply DomainPortMod.map_join_emp.
Qed.
Next Obligation.
  apply DomainPortMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply DomainPortMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply DomainPortMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply DomainPortMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply DomainPortMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply DomainPortMod.map_eql; auto.
Qed.
Next Obligation.
  apply DomainPortMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply DomainPortMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply DomainPortMod.map_get_sig.
Qed.
Next Obligation.
  apply DomainPortMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply DomainPortMod.map_get_set.
Qed.
Next Obligation.
  apply DomainPortMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply DomainPortMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply DomainPortMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply DomainPortMod.map_set_emp.
Qed.
Next Obligation.
  apply DomainPortMod.map_set_sig.
Qed.
Next Obligation.
  apply DomainPortMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply DomainPortMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply DomainPortMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply DomainPortMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply DomainPortMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply DomainPortMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply DomainPortMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply DomainPortMod.map_del_sem.
Qed.


Definition KPort: Type := 
  (port_id * option addrval (* dmport*) * 
  option addrval (* channel *) * port_coreNum * port_status )%type.

(* Module about abstract kernelporttbl *)
Module abskernelport.
  Definition B := KPort.
  Definition holder : B := (0%nat, None, None, 0%nat,  0%nat).  
End abskernelport. 

Module KernelPMod := MapLib.MapFun tidspec abskernelport. 

Program Instance KernelPortMap: PermMap tid abskernelport.B KernelPMod.map := 
 {
    usePerm := KernelPMod.usePerm;
    isRw := KernelPMod.isRw;
    flip := KernelPMod.flip;
    sameV := KernelPMod.sameV;
    same := KernelPMod.same;
    emp := KernelPMod.emp;
    join := KernelPMod.join;
    del := KernelPMod.del;
    get := KernelPMod.get;
    set := KernelPMod.set;
    sig := KernelPMod.sig;
    merge := KernelPMod.merge;
    minus := KernelPMod.minus;
    map_dec_a := KernelPMod.map_dec_a
}.

Next Obligation.
  apply KernelPMod.map_join_emp.
Qed.
Next Obligation.
  apply KernelPMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply KernelPMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply KernelPMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply KernelPMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply KernelPMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply KernelPMod.map_eql; auto.
Qed.
Next Obligation.
  apply KernelPMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply KernelPMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply KernelPMod.map_get_sig.
Qed.
Next Obligation.
  apply KernelPMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply KernelPMod.map_get_set.
Qed.
Next Obligation.
  apply KernelPMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply KernelPMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply KernelPMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply KernelPMod.map_set_emp.
Qed.
Next Obligation.
  apply KernelPMod.map_set_sig.
Qed.
Next Obligation.
  apply KernelPMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply KernelPMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply KernelPMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply KernelPMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply KernelPMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply KernelPMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply KernelPMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply KernelPMod.map_del_sem.
Qed.

(* 分区通信使用的信号量 
   可用于核间通信的通道所需的核间信号量有0-7 
   以及固定信号量
#define OS_RESOURCE_SEMAPHORE_PORT  		    9	
#define OS_RESOURCE_SEMAPHORE_CHANNEL 		    10	
#define OS_RESOURCE_SEMAPHORE_SYSTEM 		    11	
*)
Definition channel_id := nat.
Definition channel_dstnum :=nat. 
Definition channel_semaphore := nat.
Definition channel_dstport := list addrval.
Inductive Channelt : Type :=
| IncoreC  :  Channelt
| OutcoreC : channel_semaphore -> Channelt.
Definition Channel : Type := (channel_id * channel_dstnum * channel_dstport * Channelt)%type.

(* Module about abstract kernelporttbl *)

Module abschannel.
  Definition B := Channel.
  Definition holder : B := (0%nat, 0%nat, (@nil addrval), IncoreC).  
End abschannel. 

Module ChannelMod := MapLib.MapFun tidspec abschannel. 

Program Instance ChannelMap: PermMap tid abschannel.B ChannelMod.map := 
 {
    usePerm := ChannelMod.usePerm;
    isRw := ChannelMod.isRw;
    flip := ChannelMod.flip;
    sameV := ChannelMod.sameV;
    same := ChannelMod.same;
    emp := ChannelMod.emp;
    join := ChannelMod.join;
    del := ChannelMod.del;
    get := ChannelMod.get;
    set := ChannelMod.set;
    sig := ChannelMod.sig;
    merge := ChannelMod.merge;
    minus := ChannelMod.minus;
    map_dec_a := ChannelMod.map_dec_a
}.

Next Obligation.
  apply ChannelMod.map_join_emp.
Qed.
Next Obligation.
  apply ChannelMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply ChannelMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply ChannelMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply ChannelMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply ChannelMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply ChannelMod.map_eql; auto.
Qed.
Next Obligation.
  apply ChannelMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply ChannelMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply ChannelMod.map_get_sig.
Qed.
Next Obligation.
  apply ChannelMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply ChannelMod.map_get_set.
Qed.
Next Obligation.
  apply ChannelMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply ChannelMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply ChannelMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply ChannelMod.map_set_emp.
Qed.
Next Obligation.
  apply ChannelMod.map_set_sig.
Qed.
Next Obligation.
  apply ChannelMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply ChannelMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply ChannelMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply ChannelMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply ChannelMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply ChannelMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply ChannelMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply ChannelMod.map_del_sem.
Qed.

(******************************************************* END ADD FOR PARTITION **********************************************************)
Inductive absdata:= 
| abstcblist: TcbMod.map -> absdata
| absecblist : EcbMod.map -> absdata
| ostm: ostime -> absdata
| oscurt: addrval -> absdata
| hier: Hier -> absdata
| hinthandler: Hinthandler -> absdata
| hinthandlerParam: HinthandlerParam -> absdata
| hexchandler: Hexchandler -> absdata
(* add by CNU *)
| absptls: PtbMod.map -> absdata (* ostcbpriotbl *)
| seminfo: EmbMod.map -> absdata (* gjb seminfo *)
| absmutinfo: MibMod.map -> absdata (* gjb mutexinfo*)
| absmqattr: MqattrMod.map -> absdata (* gjb mqattr *)
| pblist: PbMod.map -> absdata (* pos list *)
| eblist: EbMod.map -> absdata (* err list *) 
| evatomheap: ( list (addrval * type * val) )  -> absdata (* atom heaps *)
| evstructheap: ( list (addrval * type * (list val)) )  -> absdata (* struct heaps *)
| evarrayheap: ( list (addrval * nat * (list val)) )  -> absdata (* array heaps *)
| evloc: EvAuxLocMod.map -> absdata (* auxliary event location *)
| evptr: EvAuxPtrMod.map -> absdata (* auxliary event pointer *)
| rootsk: list (list int32) -> absdata (* RootTaskStk *)
| allpartarea:  absarea_t -> absdata (* area_t *)
| ossms_mpax: SmsMod.map -> absdata (* SMS_MPAX *)
| osses_mpax: SesMod.map -> absdata (* SES_MPAX *)
| osxmpax: XmcMod.map -> absdata (* XMC_XMPAX *)
| xmpfar : int32 -> absdata (* XMPFAR *)
| xmpfsr : int32 -> absdata (* XMPFSR *)
| mdmaerr : int32 -> absdata (* MDMAERR *)
| ksdschedidx:  ksdscdidx  -> absdata (* KsDomScheduleIdx *)
| ksdschedlen:  ksdscdlen  -> absdata (* KsDomScheduleLength *)
| kscurdom: kscur  -> absdata (* KsCurDomain *)
| kslastdom: kslast  -> absdata (* KsLastDomain *)
| ksdomtime: ksdtime  -> absdata (* KsDomainTime *)
| ksdsched: KsDScdMod.map  -> absdata (* KsDomSchedule[idx] *)
| domindexlist: Dom2IdxMod.map -> absdata (* Domain2Index *)
| absuconf: absucosconf -> absdata (* ucos_conf_t *)
| intparmux: IntPMuxMod.map -> absdata (* IntPartitionMux *)
| ksdoms:  KsDomsMod.map -> absdata (* ksDomains[curd] *)
| cpartnum:  int32 -> absdata (* Core_partition_num *)
(* end add by CNU *) 
(* add by SJTU *) 
| ostmr : option TmrMod.map -> absdata
| osrate : osclkrate -> absdata
| oscurtcore : coreid -> absdata
| oscoreheap : ( list (addrval * nat * (list val)) * list (addrval * type * val) * list (addrval * type * (list val)) )  -> absdata
| ossend :  list (list val) -> absdata
| osrecv :  list (list val) -> absdata
| osipcsem : list ecbid  -> absdata
| osipcsendsem : list ecbid -> absdata
| osipcsemshared : ecbid -> absdata 
| osipcbroad : list coreid -> absdata
| osipcgr: val -> absdata
| osfreedyn:  val -> nat -> absdata
| osdynheap: list (addrval * list val) -> absdata
(* end add by SJTU *) 
(* add by ISCAS*)
| capcspace : CSpaceMod.map -> absdata
| abspthattr: PthattrMod.map  -> absdata 
(* end add by ISCAS*)
(* add for Partition *)
| oskport : KernelPMod.map -> absdata  (*0-PORTNUM*)
| oschannel : ChannelMod.map -> absdata
| osdomainport : DomainPortMod.map -> absdata (* 本核 *)
| oscoreportpl: list addrval -> absdata
.

Module absdatastru.
 
 Definition B := absdata. 
 Definition holder : B := (abstcblist emp).
 
End absdatastru.

Module OSAbstMod := MapLib.MapFun absdataidspec absdatastru.

Definition osabst:= OSAbstMod.map. 

(* Definition abstdel := fun (M:OSAbstMod.map) a => OSAbstMod.minus M (OSAbstMod.sig a (abstcblist emp)). *)

Program Instance AMap: PermMap absdataid absdata osabst :=
  {
    usePerm := OSAbstMod.usePerm;
    isRw := OSAbstMod.isRw;
    flip := OSAbstMod.flip;
    sameV := OSAbstMod.sameV;
    same := OSAbstMod.same;
    emp := OSAbstMod.emp;
    join := OSAbstMod.join;
    del := OSAbstMod.del;
    get := OSAbstMod.get;
    set := OSAbstMod.set;
    sig := OSAbstMod.sig;
    merge := OSAbstMod.merge;
    minus := OSAbstMod.minus;
    map_dec_a := OSAbstMod.map_dec_a
  }.
Next Obligation.
  apply OSAbstMod.map_join_emp.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_eql; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_get_sig.
Qed.
Next Obligation.
  apply OSAbstMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_get_set.
Qed.
Next Obligation.
  apply OSAbstMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_set_emp.
Qed.
Next Obligation.
  apply OSAbstMod.map_set_sig.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_del_sem.
Qed.

Definition osabstep := vallist -> osabst -> (option val * option osabst) -> Prop. 

Definition absexpr := osabst -> Prop.

Inductive spec_code:=
| spec_prim :  vallist-> osabstep -> spec_code
| sched : spec_code
| spec_crt : val -> val -> val -> spec_code
| spec_del : val -> spec_code
| spec_done : option val -> spec_code
| spec_seq : spec_code -> spec_code -> spec_code
| spec_choice : spec_code -> spec_code -> spec_code
| spec_assume : absexpr -> spec_code
(* add by CNU *)
| spec_assert : absexpr -> spec_code
| spec_abort : spec_code
(* end add by CNU *) 
(* add by SJTU *)
| getsem : coreid -> spec_code
| postsem : coreid -> spec_code
| coreint : coreid -> val -> spec_code
| clearipc : coreid -> val -> spec_code
| cslsemacc : nat -> val -> spec_code
| cslsemrel : nat -> spec_code
(* end add by SJTU *)
(* add by CNU *)
| csl_msmc_getSMSMPAXL : coreid -> val -> addrval -> spec_code
| csl_msmc_setSMSMPAXL : coreid -> val -> addrval -> spec_code
| csl_msmc_setSMSMPAXH : coreid -> val -> addrval -> spec_code
| csl_msmc_getSESMPAXL : coreid -> val -> addrval -> spec_code
| csl_msmc_setSESMPAXL : coreid -> val -> addrval -> spec_code
| csl_msmc_setSESMPAXH : coreid -> val -> addrval -> spec_code
| csl_xmc_getXMPAXL : val -> addrval -> spec_code
| csl_xmc_setXMPAXL : val -> addrval -> spec_code
| csl_xmc_setXMPAXH : val -> addrval -> spec_code
| csl_xmc_clearFault : spec_code
| csl_cgem_clearMDMAError : spec_code
(* end add by CNU *) 
. 


Notation " x '(|' vl '|)' " := (spec_prim vl x) (at level 40).
Notation  " 'END' v " := (spec_done v)(at level 40).
Notation  " x ';;' y " := (spec_seq x y) (right associativity, at level 44). 
Notation  " x '??' y " := (spec_choice x y) (right associativity, at level 45).
Notation  " 'ASSUME' b " := (spec_assume b) (at level 40).
(* add by CNU *)
Notation " 'ASSERT' b " := (spec_assert b) (at level 40).
Notation " 'ABORT' " := (spec_abort) (at level 40).  
(* end add by CNU *) 

(**The Low-level Language ***)

(**The expressions and statements for the Low-level Language**)
Definition fid :=  ident.

(**The max number of interrupt handlers**)
Definition INUM := 16%nat.

Definition  hid := nat.

Inductive expr:=
 | enull : expr
 | evar : var -> expr
 | econst32 : int32 -> expr
 | eptrconst: addrval -> expr 
 | eunop : uop -> expr -> expr
 | ebinop : bop -> expr -> expr -> expr
 | ederef : expr -> expr
 | eaddrof : expr -> expr 
 | efield : expr -> ident -> expr
 | ecast : expr -> type -> expr
 | earrayelem : expr -> expr -> expr.  (* expr1 [ expr2 ] *)

Definition exprlist : Set := list expr.

Inductive prim :=
 | exint : prim
 | switch : var -> prim
 | eoi : int32 -> prim
 | eoint : var -> prim
 | excrit : prim
 | encrit : prim
 | cli : prim
 | sti : prim
 | checkis : var -> prim 
 | stkinit : expr -> expr -> expr -> prim
 | stkfree : expr -> prim
 | dint : var -> prim
 | rint : var -> prim
 | dintp : var -> prim
 | rintp : var -> prim
 (* add by SJTU *)
 (* sgetsem acquires the core hardware semaphore *)
 (* spostsem releases the core hardware semaphore *)
 | sgetsem : expr -> prim
 | spostsem : expr -> prim
 | sgenerateipc : expr -> expr -> prim
 | sclearipc : expr -> expr -> prim
 (* scsl_semaccdir acquires the hardware semaphore of number expr,
    succ return 1, fail return 0 *)
 (* scsl_semrel releases the hardware semaphore of number expr *)
 | scsl_semaccdir : expr -> expr -> prim
 | scsl_semrel : expr -> prim
 (* end add by SJTU *)
(* (add by CNU) *)
 | scsl_msmc_getSMSMPAXL : expr -> expr -> expr ->prim
 | scsl_msmc_setSMSMPAXL : expr -> expr -> expr ->prim
 | scsl_msmc_setSMSMPAXH : expr -> expr -> expr ->prim
 | scsl_msmc_getSESMPAXL : expr -> expr -> expr ->prim
 | scsl_msmc_setSESMPAXL : expr -> expr -> expr ->prim
 | scsl_msmc_setSESMPAXH : expr -> expr -> expr ->prim
 | scsl_xmc_getXMPAXL : expr -> expr ->prim
 | scsl_xmc_setXMPAXL : expr -> expr ->prim
 | scsl_xmc_setXMPAXH : expr -> expr ->prim
 | scsl_xmc_clearFault : prim
 | scsl_cgem_clearMDMAError : prim
 (* (end add by CNU) *)
.

Inductive stmts :=
 | sskip : option val -> stmts
 | sassign : expr -> expr -> stmts (* expr1 = expr2 *)
 | sif : expr -> stmts -> stmts -> stmts (* if ( expr ) stmts1 else stmts2 *)
 | sifthen:expr->stmts->stmts
 | swhile : expr -> stmts -> stmts
 | sret : stmts
 | srete : expr -> stmts
 | scall : fid -> exprlist -> stmts
 | scalle : expr -> fid -> exprlist -> stmts
 | sseq : stmts -> stmts -> stmts (* right associative *)
 | sprint : expr -> stmts
 | sfexec : fid -> vallist -> typelist -> stmts
 | sfree : freelist -> option val ->  stmts
(*
 | sfreev : freelist -> val -> stmts
*)
 | salloc : vallist -> decllist -> stmts
 | sprim : prim -> stmts
 | hapi_code:spec_code -> stmts .

Open Scope type_scope.

Definition function  :=  (type  *  decllist * decllist *  stmts).

Definition progunit  := fid -> option function.

Definition intunit  := hid -> option stmts.

Definition oscode := (progunit * progunit * intunit).

Definition lprog  := (progunit * oscode).


Inductive cureval:=
|cure : expr -> cureval
(*
|curv : val-> cureval
*)
|curs : stmts -> cureval.
Notation "'SKIP'  " := (curs (sskip None))  (at level 0).

Notation "'[' v ']'" := (curs (sskip (Some v))) (at level 0).

(*Definition of continuation, which is a pair of expression continuation and statement continuation*)
Inductive exprcont:=
| kenil : exprcont
| keop1 : uop -> type -> exprcont -> exprcont
| keop2r : bop -> expr -> type -> type -> exprcont -> exprcont
| keop2l: bop -> val -> type -> type ->exprcont -> exprcont
| kederef : type -> exprcont -> exprcont 
| keoffset: int32 -> exprcont -> exprcont
| kearrbase: expr -> type -> exprcont -> exprcont
| kearrindex: val -> type -> exprcont -> exprcont
| kecast: type -> type -> exprcont -> exprcont.

Inductive stmtcont:=
| kstop : stmtcont
| kseq : stmts -> stmtcont -> stmtcont
| kcall : fid  -> stmts -> env -> stmtcont -> stmtcont
| kint : cureval -> exprcont -> env -> stmtcont -> stmtcont
| kassignr: expr -> type -> stmtcont -> stmtcont
| kassignl : val -> type -> stmtcont -> stmtcont
(*
| kcalle : fid -> exprlist -> type -> stmtcont -> stmtcont
*)
| kfuneval : fid -> vallist -> typelist -> exprlist -> stmtcont -> stmtcont
| kif : stmts -> stmts -> stmtcont -> stmtcont
| kwhile : expr -> stmts -> stmtcont -> stmtcont
| kret :   stmtcont -> stmtcont

| kevent : cureval -> exprcont -> stmtcont -> stmtcont
.

Definition  cont := (exprcont * stmtcont).

Definition code  := (cureval * cont).

Module CodeSpec.
  Definition B:= code.
  Definition holder : B := (curs (sskip None), (kenil, kstop)).
End CodeSpec.

Module TasksMod := MapLib.MapFun tidspec CodeSpec.

Definition tasks :=TasksMod.map.

(* Definition tasksdel := fun (M:tasks) a => TasksMod.minus M (TasksMod.sig a (curs (sskip None),(kenil,kstop))). *)

Program Instance TasksMap: PermMap tid code tasks :=
  {
    usePerm := TasksMod.usePerm;
    isRw := TasksMod.isRw;
    flip := TasksMod.flip;
    sameV := TasksMod.sameV;
    same := TasksMod.same;
    emp := TasksMod.emp;
    join := TasksMod.join;
    del := TasksMod.del;
    get := TasksMod.get;
    set := TasksMod.set;
    sig := TasksMod.sig;
    merge := TasksMod.merge;
    minus := TasksMod.minus;
    map_dec_a := TasksMod.map_dec_a
  }.
Next Obligation.
  apply TasksMod.map_join_emp.
Qed.
Next Obligation.
  apply TasksMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply TasksMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply TasksMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply TasksMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply TasksMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply TasksMod.map_eql; auto.
Qed.
Next Obligation.
  apply TasksMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply TasksMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply TasksMod.map_get_sig.
Qed.
Next Obligation.
  apply TasksMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply TasksMod.map_get_set.
Qed.
Next Obligation.
  apply TasksMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply TasksMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply TasksMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply TasksMod.map_set_emp.
Qed.
Next Obligation.
  apply TasksMod.map_set_sig.
Qed.
Next Obligation.
  apply TasksMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply TasksMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply TasksMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply TasksMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply TasksMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply TasksMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply TasksMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply TasksMod.map_del_sem.
Qed.

Module EnvSpec.
  Definition B:= env.
  Definition holder : B := emp.
End EnvSpec.

Module CltEnvMod:= MapFun tidspec EnvSpec.

Definition cltenvs := CltEnvMod.map.
(* Definition cltenvdel := fun (M:CltEnvMod.map) a => CltEnvMod.minus M (CltEnvMod.sig a emp). *)

Program Instance CMap: PermMap tid env cltenvs :=
  {
    usePerm := CltEnvMod.usePerm;
    isRw := CltEnvMod.isRw;
    flip := CltEnvMod.flip;
    sameV := CltEnvMod.sameV;
    same := CltEnvMod.same;
    emp := CltEnvMod.emp;
    join := CltEnvMod.join;
    del := CltEnvMod.del;
    get := CltEnvMod.get;
    set := CltEnvMod.set;
    sig := CltEnvMod.sig;
    merge := CltEnvMod.merge;
    minus := CltEnvMod.minus;
    map_dec_a := CltEnvMod.map_dec_a
  }.
Next Obligation.
  apply CltEnvMod.map_join_emp.
Qed.
Next Obligation.
  apply CltEnvMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply CltEnvMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply CltEnvMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply CltEnvMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply CltEnvMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply CltEnvMod.map_eql; auto.
Qed.
Next Obligation.
  apply CltEnvMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply CltEnvMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply CltEnvMod.map_get_sig.
Qed.
Next Obligation.
  apply CltEnvMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply CltEnvMod.map_get_set.
Qed.
Next Obligation.
  apply CltEnvMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply CltEnvMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply CltEnvMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply CltEnvMod.map_set_emp.
Qed.
Next Obligation.
  apply CltEnvMod.map_set_sig.
Qed.
Next Obligation.
  apply CltEnvMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply CltEnvMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply CltEnvMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply CltEnvMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply CltEnvMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply CltEnvMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply CltEnvMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply CltEnvMod.map_del_sem.
Qed.

(**The Low-level World**)
Definition  clientst :=  (env * cltenvs * mem)%type.
(*Interrupt Enable*)
Definition ie := bool.
(**Interrupt Stack**)
Definition is := list hid.
(**Historical values of ie**)
Definition cs := list ie.

Definition localst := (ie * is * cs)%type.

Module LocalStSpec.
  Definition B:= localst.
  Definition holder : B := (true, nil, nil).
End LocalStSpec.

Module TaskLStMod:= MapFun tidspec LocalStSpec.

Definition ltaskstset:= TaskLStMod.map.

(* Definition tasklstdel := fun (M:ltaskstset) a => TaskLStMod.minus M (TaskLStMod.sig a (true,nil,nil)). *)

Program Instance TaskLStMap: PermMap tid localst ltaskstset :=
  {
    usePerm := TaskLStMod.usePerm;
    isRw := TaskLStMod.isRw;
    flip := TaskLStMod.flip;
    sameV := TaskLStMod.sameV;
    same := TaskLStMod.same;
    emp := TaskLStMod.emp;
    join := TaskLStMod.join;
    del := TaskLStMod.del;
    get := TaskLStMod.get;
    set := TaskLStMod.set;
    sig := TaskLStMod.sig;
    merge := TaskLStMod.merge;
    minus := TaskLStMod.minus;
    map_dec_a := TaskLStMod.map_dec_a
  }.
Next Obligation.
  apply TaskLStMod.map_join_emp.
Qed.
Next Obligation.
  apply TaskLStMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply TaskLStMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply TaskLStMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply TaskLStMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply TaskLStMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply TaskLStMod.map_eql; auto.
Qed.
Next Obligation.
  apply TaskLStMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply TaskLStMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply TaskLStMod.map_get_sig.
Qed.
Next Obligation.
  apply TaskLStMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply TaskLStMod.map_get_set.
Qed.
Next Obligation.
  apply TaskLStMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply TaskLStMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply TaskLStMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply TaskLStMod.map_set_emp.
Qed.
Next Obligation.
  apply TaskLStMod.map_set_sig.
Qed.
Next Obligation.
  apply TaskLStMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply TaskLStMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply TaskLStMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply TaskLStMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply TaskLStMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply TaskLStMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply TaskLStMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply TaskLStMod.map_del_sem.
Qed.

(*Definition isr register*)
Definition isr :=  hid -> bool.

Definition isrupd (r : isr) (x : hid) (b : bool):= 
      fun (y : hid) => if beq_nat x y then b else r y.

Definition ierupd(r : ier) (x : hid) (b : bool):=
      fun (y : hid) => if beq_nat x y then b else r y. 

Definition base1 : int := Int.repr 1.

Fixpoint inLevel(level : int) (y : hid) : bool :=
  match y with
  | S y' => inLevel (Int.shru level base1) y'
  | O => Int.eq (Int.and level base1) base1
  end.

Definition ierupds(r : ier) (level : var) := 
      fun (y : hid) => if inLevel (Int.repr level) y then true else r y.

Definition ierupds_int(r : ier) (level : int) := 
      fun (y : hid) => if inLevel level y then true else r y.

Definition empier := fun (x : hid) => match x with
                                      | S (S (S (S _))) => false
                                      | _ => true
                                      end.

Definition empupd(r : ier) := fun (x : hid) => match x with
                                                | S (S (S (S _))) => false
                                                | _ => r x
                                                end.

Fixpoint leb_nat (m : nat) : nat -> bool :=
  match m with
  | O => fun _ : nat => true
  | S m' => fun n : nat => match n with
                           | O  => false
                           | S n' =>  leb_nat  m' n'
                           end
  end.

Fixpoint highpri' (r : isr) (n : nat) : hid :=
  match n with
   | O => INUM
   | S n' => let y := highpri' r n' in 
                 if r n' then
                    if (leb_nat  n' y) then n' else y 
                 else y
 end.

Definition highpri (r:isr) := highpri' r INUM.

Definition higherint (r:isr) (i:hid) :=  forall i', Nat.le i' i -> r i' = false. 

Definition empisr := fun (x : hid) => false. 

Definition  osstate  := (clientst * isr * ier * ltaskstset).

Definition  smem  :=  (env * env * mem).

Definition  taskst := (smem *  isr * ier * localst).

Definition get_smem (ts : taskst) :=
      match ts with
      (m, _, _, _) => m
     end.

Definition  lworld :=  (lprog * tasks * clientst * osstate * tid).

Parameter ipcgr_block : block.

Definition ipcgr_addr: addrval:= (ipcgr_block, Int.zero).

Parameter sms_mpax_block : block.

Definition sms_mpax_addr: addrval:= (sms_mpax_block, Int.zero).

Parameter ses_mpax_block : block.

Definition ses_mpax_addr: addrval:= (ses_mpax_block, Int.zero).

Parameter xmpax_block : block.

Definition xmpax_addr: addrval:= (xmpax_block, Int.zero).

Parameter xmpfar_block : block.

Definition xmpfar_addr: addrval:= (xmpfar_block, Int.zero).

Parameter xmpfsr_block : block.

Definition xmpfsr_addr: addrval:= (xmpfsr_block, Int.zero).

Parameter mdmaerr_block : block.

Definition mdmaerr_addr: addrval:= (mdmaerr_block, Int.zero).

(**The High-level World**)

Definition funtype : Set := prod type typelist.

Definition api_code := vallist -> spec_code.

Definition osapi := prod api_code  funtype.
  
Definition osapispec :=  fid -> option osapi.

Definition int_code := spec_code.

Definition osintspec := hid -> option int_code.

Definition ossched := osabst -> tid -> Prop.

Definition osspec := (osapispec * osintspec * ossched).

Definition hprog := (progunit * osspec). 

Definition hworld := (hprog * tasks * clientst * osabst ). 

Definition isrdy (st:taskstatus):=
  match st with
    | rdy => True
    | _ => False
  end.

Definition eqenv (o o': taskst) : Prop :=
     match o, o' with
          | (G,E,M,isr,ier,aux),(G',E',M',isr',ier',aux') => G =G' /\ E = E' 
      end.


(**The c6713 max number of level**)
Definition MLEVEL := 65520%Z. (*0xffff = 65535*) (*0xFFF0 = 65520*)

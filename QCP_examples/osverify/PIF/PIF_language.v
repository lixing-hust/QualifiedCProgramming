Require Import PIF_memory.
Set Implicit Arguments.
Unset Strict Implicit.

(**The High-level Specification Language **)
Definition priority := int32.
Definition ecbid := addrval.
Definition msg := val.
Definition maxlen := int32.
Definition  ostime := int32.
Definition waitset := list tid.

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
(* Definition eid := addrval. *)
Definition pos := int32.
Definition ier := nat -> bool.
Definition Hier := ier.
Definition Hinthandler := int32->int32(*nat->int32*).
Definition HinthandlerParam := int32->addrval.
Definition Hexchandler := int32.
Definition susstatus := bool.

Inductive tcbstats:=
| os_stat_sem: ecbid -> tcbstats
| os_stat_q: ecbid -> tcbstats
| os_stat_postq: ecbid -> tcbstats
| os_stat_time:  tcbstats
| os_stat_mbox: ecbid -> tcbstats
| os_stat_mutexsem: ecbid -> tcbstats.

Inductive taskstatus :=
 | rdy: taskstatus
 | wait : tcbstats -> option int32 -> taskstatus.
(* "wait (os_stat_x eid) (Some t)" or "wait (os_stat_x eid) None" *) 

Module abstcb.
  Definition B : Set := ( priority * taskstatus * msg  * susstatus)%type.
  Definition holder : B:= (Int.zero, rdy, Vnull ,false).
End abstcb.

Module TcbMod := PIF_MapLib.MapFun tidspec abstcb.

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
| absmutexsem: int32 -> owner -> edata.

Module absecb.
  Definition B : Set := prod edata waitset.
  Definition holder : B := (absmbox Vnull, nil).
End absecb.

Module EcbMod := PIF_MapLib.MapFun tidspec absecb.

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

(* Module about absseminfo *)

Inductive infoeid :=
| infotid: addrval -> infoeid
| infonull
| infohold.

(* 1 -- binary, 2 -- counting *) 
Definition sem_tp := int32. 

Module absemb.
  Definition B : Set := (infoeid * sem_tp)%type. 
  Definition holder : B := (infonull, (Int.repr 2)). 
End absemb.

Module EmbMod := PIF_MapLib.MapFun idxspec absemb. 

Definition Pos := int32 .

Program Instance EmbMap: PermMap Pos (infoeid * sem_tp) EmbMod.map := 
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

Module absmuxinfob.
  Definition B := ( eid_type * owner * muxtype * rec_cnt * prot * prioc * wq * cnsa )%type.
  Definition holder : B := ( Null, None,  Int.zero, Int.zero, Int.zero, Int.zero, Int.zero, Int.zero).
End absmuxinfob.


Module MibMod := PIF_MapLib.MapFun idxspec absmuxinfob.

Program Instance MibMap: PermMap Pos (eid_type * owner * muxtype * rec_cnt  * prot * prioc * wq * cnsa) MibMod.map :=
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

Module absqattrb.
  Definition B: Set :=  (eid_type * q_waittype * q_flags * q_maxmsg * q_msgsize *q_curmsgs )%type. 
  Definition holder : B := (Null, Int.zero,Int.zero,Int.zero,Int.zero,Int.zero). 
End absqattrb.

Module MqattrMod := PIF_MapLib.MapFun idxspec absqattrb.

Program Instance MqattrMap:
  PermMap pos (eid_type * q_waittype * q_flags * q_maxmsg * q_msgsize *q_curmsgs) MqattrMod.map :=
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

Module PbMod := PIF_MapLib.MapFun tidspec abspb. 

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

Module EbMod := PIF_MapLib.MapFun tidspec abserrb. 

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

Module PtbMod := PIF_MapLib.MapFun idxspec absptb. 

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

Module EvAuxLocMod := PIF_MapLib.MapFun tidspec absevauxloc. 

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

Module EvAuxPtrMod := PIF_MapLib.MapFun tidspec absevauxptr. 

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
.

Definition absdataid_eq (id1 id2:absdataid):=
  match id1, id2 with
  | abstcblsid, abstcblsid => true
  | absecblsid, absecblsid => true
  | ostmid, ostmid => true
  | curtid, curtid => true
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
  | evatomheapid,evatomheapid => true
  | evstructheapid,evstructheapid => true
  | evarrayheapid,evarrayheapid => true
  | evlocid, evlocid => true 
  | evptrid, evptrid => true 
  | _, _ => false
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
  | evptrid, _ => false (* auxliary event pointer *)
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
  destruct a,a',a'';simpl in H, H0;auto;tryfalse.
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

Inductive absdata:= 
| abstcblist: TcbMod.map -> absdata
| absecblist: EcbMod.map -> absdata
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
.

Module absdatastru.
 
 Definition B := absdata. 
 Definition holder : B := (abstcblist emp).
 
End absdatastru.

Module OSAbstMod := PIF_MapLib.MapFun absdataidspec absdatastru.

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

Definition loop_init := osabst -> vallist -> Prop. 
Definition loop_cond := vallist -> osabst -> Prop.

Inductive spec_code :=
| spec_prim :  vallist-> osabstep -> spec_code
| sched : spec_code
(* | spec_crt : val -> val -> val -> spec_code *)
(* | spec_del : val -> spec_code *)
| spec_done : option val -> spec_code
| spec_seq : spec_code -> spec_code -> spec_code
| spec_choice : spec_code -> spec_code -> spec_code
| spec_loop : loop_init -> loop_cond -> (vallist -> vallist -> spec_code) -> spec_code
| spec_lp : vallist -> loop_cond -> (vallist -> vallist -> spec_code) -> spec_code 
| spec_assume : absexpr -> spec_code
| spec_assert : absexpr -> spec_code
| spec_abort : spec_code 
.

Definition loop_body := vallist -> vallist -> spec_code. 

Notation " x '(|' vl '|)' " := (spec_prim vl x) (at level 40).
Notation  " 'END' v " := (spec_done v)(at level 40).
Notation  " x ';;' y " := (spec_seq x y) (right associativity, at level 44). 
Notation  " x '??' y " := (spec_choice x y) (right associativity, at level 45).
Notation  " 'ASSUME' b " := (spec_assume b) (at level 40).
Notation " 'ASSERT' b " := (spec_assert b) (at level 40).
Notation " 'ABORT' " := (spec_abort) (at level 40).  

(**The Low-level Language ***)

(**The expressions and statements for the Low-level Language**)
Definition fid :=  ident.

(**The max number of interrupt handlers**)
Definition INUM := 2%nat.

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
 | excrit : prim
 | encrit : prim
 | cli : prim
 | sti : prim
 | checkis : var -> prim 
 | stkinit : expr -> expr -> expr -> prim
 | stkfree : expr -> prim.

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

Module TasksMod := PIF_MapLib.MapFun tidspec CodeSpec.

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

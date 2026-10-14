Require Import memory1.

Set Implicit Arguments.
Unset Strict Implicit.

(**The High-level Specification Language **)
Definition priority := int32.
Definition ecbid := addrval.
Definition msg := val.
Definition maxlen := int32.
Definition  ostime := int32.
Definition waitset := list tid.

Inductive tcbstats:=
| os_stat_sem: ecbid -> tcbstats
| os_stat_q: ecbid -> tcbstats
| os_stat_time:  tcbstats
| os_stat_mbox: ecbid -> tcbstats
| os_stat_mutexsem: ecbid -> tcbstats.

Inductive taskstatus :=
 | rdy: taskstatus
 | wait : tcbstats -> int32 -> taskstatus.

Module abstcb.
  Definition B : Set := ( priority * taskstatus * msg)%type.
  Definition holder : B:= (Int.zero, rdy, Vnull).
End abstcb.

Module TcbMod := MapLib1.MapFun tidspec abstcb.

(* Definition tcbdel := fun (M:TcbMod.map) a => TcbMod.minus M (TcbMod.sig a (Int.zero,rdy,Vnull)). *)

Program Instance TcbMap: PermMap tid ( priority * taskstatus * msg) TcbMod.map :=
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
| absmsgq : list msg -> maxlen -> edata
| absmbox: msg -> edata
| absmutexsem: int32 -> owner -> edata.

Module absecb.
  Definition B : Set := prod edata waitset.
  Definition holder : B := (absmbox Vnull, nil).
End absecb.

Module EcbMod := MapLib1.MapFun tidspec absecb.

(* Definition ecbdel := fun (M:EcbMod.map) a => EcbMod.minus M (EcbMod.sig a (absmbox Vnull,nil)). *)

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
(*
Inductive eid_type : Type :=
Null | Holder | Valid_Addr: tid -> eid_type.
*)



Inductive infoeid :=
| infotid: addrval -> infoeid
| infonull
| infohold.

(* Inductive sem_tp : Type := *)
(*   | SEM_COUNTING *)
(*   | SEM_BINARY. *)

(* 1 -- binary, 2 -- counting *) 
Definition sem_tp := int32. 

(* Inductive amuinbl:= *)
(* | absseminfo: tid -> sem_tp -> int32 -> int32 -> amuinbl. *)

Module absemb.
  Definition B : Set := (infoeid * sem_tp * int32 * int32)%type. 
  Definition holder : B := (infonull, (Int.repr 2), Int.zero, Int.zero). 
End absemb.

Module EmbMod := MapLib1.MapFun posspec absemb. 

Definition Pos := int32 .

Program Instance EmbMap: PermMap Pos (infoeid * sem_tp * int32 * int32) EmbMod.map := 
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




Module abspb.
  Definition B : Set := Pos%type. 
  Definition holder : B := Int.zero.  
End abspb. 

Module PbMod := MapLib1.MapFun tidspec abspb. 

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

(************type**************)
Definition typebl := int32.
Module abstype.
  Definition B : Set := typebl.
  Definition holder : B:= (Int.zero).
End abstype.

Module TypMod := MapLib1.MapFun typspec abstype.

Program Instance TypMap: PermMap typ typebl TypMod.map :=
  {
    usePerm := TypMod.usePerm;
    isRw := TypMod.isRw;
    flip := TypMod.flip;
    sameV := TypMod.sameV;
    same := TypMod.same;
    emp := TypMod.emp;
    join := TypMod.join;
    del := TypMod.del;
    get := TypMod.get;
    set := TypMod.set;
    sig := TypMod.sig;
    merge := TypMod.merge;
    minus := TypMod.minus;
    map_dec_a := TypMod.map_dec_a
}.
Next Obligation.
  apply TypMod.map_join_emp.
Qed.
Next Obligation.
  apply TypMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply TypMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply TypMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply TypMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply TypMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply TypMod.map_eql; auto.
Qed.
Next Obligation.
  apply TypMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply TypMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply TypMod.map_get_sig.
Qed.
Next Obligation.
  apply TypMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply TypMod.map_get_set.
Qed.
Next Obligation.
  apply TypMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply TypMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply TypMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply TypMod.map_set_emp.
Qed.
Next Obligation.
  apply TypMod.map_set_sig.
Qed.
Next Obligation.
  apply TypMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply TypMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply TypMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply TypMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply TypMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply TypMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply TypMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply TypMod.map_del_sem.
Qed.
(************proceil**************)
Definition procelbl := int32.
Module absprocel.
  Definition B : Set := procelbl.
  Definition holder : B:= (Int.zero).
End absprocel.

Module  ProcMod := MapLib1.MapFun procspec absprocel.
Definition proc:= addrval.
Program Instance ProcMap: PermMap proc procelbl ProcMod.map :=
  {
    usePerm := ProcMod.usePerm;
    isRw := ProcMod.isRw;
    flip := ProcMod.flip;
    sameV := ProcMod.sameV;
    same := ProcMod.same;
    emp := ProcMod.emp;
    join := ProcMod.join;
    del := ProcMod.del;
    get := ProcMod.get;
    set := ProcMod.set;
    sig := ProcMod.sig;
    merge := ProcMod.merge;
    minus := ProcMod.minus;
    map_dec_a := ProcMod.map_dec_a
}.
Next Obligation.
  apply ProcMod.map_join_emp.
Qed.
Next Obligation.
  apply ProcMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply ProcMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply ProcMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply ProcMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply ProcMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply ProcMod.map_eql; auto.
Qed.
Next Obligation.
  apply ProcMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply ProcMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply ProcMod.map_get_sig.
Qed.
Next Obligation.
  apply ProcMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply ProcMod.map_get_set.
Qed.
Next Obligation.
  apply ProcMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply ProcMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply ProcMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply ProcMod.map_set_emp.
Qed.
Next Obligation.
  apply ProcMod.map_set_sig.
Qed.
Next Obligation.
  apply ProcMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply ProcMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply ProcMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply ProcMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply ProcMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply ProcMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply ProcMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply ProcMod.map_del_sem.
Qed.

(*
Module absptb.
  Definition B := ( eid_type )%type.
  Definition holder : B := ( Null ).
End absptb.

Module PtbMod := MapLib1.MapFun posspec absptb. 

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
*)


Inductive absdataid:=
| abstcblsid : absdataid
| absecblsid: absdataid
| ostmid : absdataid
| curtid:absdataid
| abspthattrid: absdataid (* add ptbl by llm *)
| abspthattrtypeid:absdataid (*add*)
| abspthattrprocelid:absdataid(*add*)
(*| absptlsid: absdataid (* add ptbl by csy *)*).



Definition absdataid_eq (id1 id2:absdataid):=
  match id1, id2 with
  | abstcblsid, abstcblsid => true
  | absecblsid, absecblsid => true
  | ostmid, ostmid => true
  | curtid, curtid => true
  | abspthattrid, abspthattrid => true (* add ptbl by llm *)
  | abspthattrtypeid,abspthattrtypeid => true (*add*)
  | abspthattrprocelid,abspthattrprocelid => true (*add*)
 (* | absptlsid, absptlsid => true (* add ptbl by csy *)*)
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
(* | pblsid,abstcblsid => false (*add*)
  | pblsid, absecblsid => false (*add*)
  | pblsid,ostmid => false (*add*)
  | pblsid,curtid => false (*add*)
  | pblsid,pblsid => false (*add*)*) 
  (*| pblsid,_ => true (*add*)*)
  | abspthattrid,abstcblsid => false (*add*)
  | abspthattrid, absecblsid => false (*add*)
  | abspthattrid,ostmid => false (*add*)
  | abspthattrid,curtid => false (*add*)
  | abspthattrid,abspthattrid => false (*add*)
  | abspthattrid,_ => true (*add*)
  | abspthattrtypeid,abstcblsid => false (*add*)
  | abspthattrtypeid, absecblsid => false (*add*)
  | abspthattrtypeid,ostmid => false (*add*)
  | abspthattrtypeid,curtid => false (*add*)
  | abspthattrtypeid,abspthattrid  => false (*add*)
  | abspthattrtypeid,abspthattrtypeid => false (*add*)
  | abspthattrtypeid,_ => true (*add*)
  | abspthattrprocelid,abstcblsid => false (*add*)
  | abspthattrprocelid, absecblsid => false (*add*)
  | abspthattrprocelid,ostmid => false (*add*)
  | abspthattrprocelid,curtid => false (*add*)
  | abspthattrprocelid,abspthattrid  => false (*add*)
  | abspthattrprocelid,abspthattrtypeid => false (*add*)
  | abspthattrprocelid,abspthattrprocelid => false (*add*)
  (*| abspthattrprocelid,_ => true (*add*)*)
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
  unfold blt. intros. 
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
| abspthattr: ( list (addrval * type * (list val)) )  -> absdata (*add*)
| abspthattrtyp: TypMod.map-> absdata (*add*)
| abspthattrproceil: ProcMod.map-> absdata (*add*).

Module absdatastru.
 
 Definition B := absdata. 
 Definition holder : B := (abstcblist emp).
 
End absdatastru.

Module OSAbstMod := MapLib1.MapFun absdataidspec absdatastru.

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
| spec_assert : absexpr -> spec_code
| spec_abort : spec_code. 

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

Module TasksMod := MapLib1.MapFun tidspec CodeSpec.

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

Definition  osstate  := (clientst * isr * ltaskstset).

Definition  smem  :=  (env * env * mem).

Definition  taskst := (smem *  isr * localst).

Definition get_smem (ts : taskst) :=
      match ts with
      (m, _, _) => m
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
          | (G,E,M,isr,aux),(G',E',M',isr',aux') => G =G' /\ E = E' 
      end.


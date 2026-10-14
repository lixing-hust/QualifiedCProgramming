Require Import include_frm.
Require Import Lists.ListSet.
Require Import os_code_defs.
Require Import os_ucos_h.
Require Export os_inv.
Require Import abs_op.
Require Import abs_op_corecommu.
Require Import abs_op_partition.
Require Import int_lock.
Require Import os_core.
Require Import ios_cap_defs.
Require Import code_notations.
(* Require Import inv_prop. *)
Require Import ios_int.
Require Import partinv_lemmas.
Require Import abs_op_partition_ext.
Require Import evt_spec_defs.
Require Import ucos_frmaop.

(*----------------------------------------------------------------*)
(* internal function spec                                         *)
(*----------------------------------------------------------------*)
Open Scope Z_scope.
Open Scope int_scope.
Require Import List.

Lemma GoodFunAsrt_Astruct' :
  forall vl v d, GoodFunAsrt(Astruct' v d vl).
Proof.
  inductions vl; intros.
  destruct d; simpl; auto.
  destruct d; simpl; auto.
  destruct t; destruct v;
  try solve [simpl; split; auto];
  try eapply IHvl.
Qed.

Lemma GoodFunAsrt_Astruct :
  forall v t vl, GoodFunAsrt(Astruct v t vl).
Proof.
  intros; unfold Astruct; destruct t; simpl; auto.
  apply GoodFunAsrt_Astruct'.
  apply GoodFunAsrt_Astruct'.
Qed.

(* Lemma GoodFunAsrt_Aarray' :
  forall vl n t l, GoodFunAsrt (Aarray' l n t vl).
Proof.
  inductions vl; intros.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct l.
  unfold GoodFunAsrt; fold GoodFunAsrt.
  split; simpl; auto.
Qed.

Lemma GoodFunAsrt_Aarray :
  forall l t vl, GoodFunAsrt(Aarray l t vl).
Proof.
  destruct t; simpl; auto.
  intros.
  apply GoodFunAsrt_Aarray'.
Qed. *)

Lemma GoodFunAsrt_AOSEvent :
  forall v osevent etbl petbl,
    GoodFunAsrt (AOSEvent v osevent etbl petbl).
Proof.
  intros.
  unfold AOSEvent; unfold GoodFunAsrt; fold GoodFunAsrt; intros.
  repeat (split; auto).
  apply GoodFunAsrt_Astruct.
  
  apply GoodFunAsrt_Aarray.
  apply GoodFunAsrt_Aarray.
Qed.

Lemma GoodFunAsrt_AEventData :
  forall osevent d,
    GoodFunAsrt (AEventData osevent d).
Proof.
  intros.
  destruct d;
    try solve [
          unfold AEventData;
          unfold GoodFunAsrt; fold GoodFunAsrt;
          repeat (split; try (apply GoodFunAsrt_Astruct); try (apply GoodFunAsrt_Aarray);auto)].
Qed.

Lemma GoodFunAstr_AEventNode :
  forall v osevent etbl petbl d,
    GoodFunAsrt (AEventNode v osevent etbl petbl d).
Proof.
  intros.
  unfold AEventNode; unfold GoodFunAsrt; fold GoodFunAsrt.    
  split.
  apply GoodFunAsrt_AOSEvent.
  apply GoodFunAsrt_AEventData.
Qed.

Lemma GoodFunAsrt_evsllseg :
  forall vl head tailnext ecbls,
    GoodFunAsrt (evsllseg head tailnext vl ecbls).
Proof.
  inductions vl; intros.
  simpl; auto.
  simpl; destruct ecbls; simpl; auto.
  destruct a. destruct p. 
  unfold GoodFunAsrt; fold GoodFunAsrt.
  intros; split; auto.
  split.
  apply GoodFunAstr_AEventNode.
  apply IHvl.
Qed.

Lemma GoodFunAsrt_dllseg :
  forall l head headprev tail tailnext t pre next,
    GoodFunAsrt(dllseg head headprev tail tailnext l t pre next).
Proof.
  inductions l; intros.
  simpl; auto.
  simpl.
  repeat (split; auto).
  apply GoodFunAsrt_Astruct.
Qed.

Lemma GoodFunAsrt_tcbdllseg :
  forall head headprev tail tailnext l,
    GoodFunAsrt (tcbdllseg head headprev tail tailnext l).
Proof.
  intros; unfold tcbdllseg.
  apply GoodFunAsrt_dllseg.
Qed.

Lemma GoodFunAsrt_qblkf_sllseg :
  forall l head tailnext t next,
    GoodFunAsrt (qblkf_sllseg head tailnext l t next).
Proof.
  inductions l; intros.
  simpl; auto.
  repeat (split;
          try (apply GoodFunAsrt_Aarray);
          try (apply GoodFunAsrt_Astruct);
          try (apply GoodFunAsrt_AEventData);
          try (apply GoodFunAsrt_evsllseg);
          try (apply GoodFunAsrt_tcbdllseg);
          try (apply GoodFunAsrt_dllseg);
          auto).
Qed.

Lemma GoodFunAsrt_qblkf_sll :
  forall head l t next,
    GoodFunAsrt (qblkf_sll head l t next).
Proof.
  unfold qblkf_sll.
  intros; apply GoodFunAsrt_qblkf_sllseg.
Qed.

Lemma GoodFunAsrt_ecbf_sllseg :
  forall l head tailnext t next,
    GoodFunAsrt (ecbf_sllseg head tailnext l t next).
Proof.
  inductions l; intros.
  simpl; auto.
  repeat (split;
          try (apply GoodFunAsrt_Aarray);
          try (apply GoodFunAsrt_Astruct);
          try (apply GoodFunAsrt_AEventData);
          try (apply GoodFunAsrt_evsllseg);
          try (apply GoodFunAsrt_tcbdllseg);
          try (apply GoodFunAsrt_dllseg);
          auto).
Qed.

Lemma GoodFunAsrt_ecbf_sll :
  forall head l t next,
    GoodFunAsrt (ecbf_sllseg head Vnull l t next).
Proof.
  intros.
  apply GoodFunAsrt_ecbf_sllseg.
Qed.

Lemma GoodFunAsrt_sllseg :
  forall l head tailnext t next,
    GoodFunAsrt (sllseg head tailnext l t next).
Proof.
  inductions l; intros.
  simpl; auto.
  repeat (split;
          try (apply GoodFunAsrt_Aarray);
          try (apply GoodFunAsrt_Astruct);
          try (apply GoodFunAsrt_AEventData);
          try (apply GoodFunAsrt_evsllseg);
          try (apply GoodFunAsrt_tcbdllseg);
          try (apply GoodFunAsrt_dllseg);
          auto).
Qed.

Lemma GoodFunAsrt_sll :
  forall head l t next,
      GoodFunAsrt(sll head l t next).
Proof.
  intros.
  unfold sll.
  apply GoodFunAsrt_sllseg.
Qed.

Definition invlth_isr' (I:Inv) l h:=
  match leb l h with
    | true => atoy_inv'
    | false => Aemp
  end.

Lemma GoodFunAsrt_invlth_isr' :
  forall x l h,
    GoodFunAsrt (invlth_isr' x l h).
Proof.
  intros; unfold invlth_isr'.
  destruct (leb l h); simpl; auto.
Qed.


(* add by CNU *)

Lemma GoodFunAsrt_Aarray_new' :
  forall vl n t l, GoodFunAsrt (Aarray_new' l n t vl).
Proof.
  inductions vl; intros.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct l.
  destruct t; 
  inductions a; intros;
  unfold GoodFunAsrt; fold GoodFunAsrt;
  try (inductions a0);
  unfold Aptrmapsto;
  split;
  try(apply GoodFunAsrt_Aarray' );
  try(apply GoodFunAsrt_Astruct' );
  simpl ; eauto.
Qed.

Lemma GoodFunAsrt_Aarray_new :
  forall l t vl, GoodFunAsrt(Aarray_new l t vl).
Proof.
  destruct t; simpl; auto.
  intros.
  apply GoodFunAsrt_Aarray_new'.
Qed.

Lemma GoodFunAsrt_ASeminfo :
  forall l vll,
    GoodFunAsrt (ASeminfo l vll).
Proof.
  intros.
  unfold ASeminfo; unfold GoodFunAsrt; fold GoodFunAsrt; intros.
  repeat (split; auto).
  apply GoodFunAsrt_Aarray_new.
Qed.

Lemma GoodFunAsrt_star: forall p q, GoodFunAsrt p -> GoodFunAsrt q ->
GoodFunAsrt (p ** q). 
Proof. cbn. tauto. Qed.

Lemma GoodFunAsrt_ex: forall {A: Type} (p: A -> asrt), 
(forall a,  GoodFunAsrt (p a)) -> 
GoodFunAsrt (EX a, p a). 
Proof. cbn. tauto. Qed.

(* Lemma GoodFunAsrt_AOSPortAttrTbl':forall x t vl,
GoodFunAsrt (EX l,  GV x @ (Tptr t)|-> Vptr l 
** Aarray_new l (Tarray t (Z.to_nat PORT_NUMS)) vl).
Proof.
intros.
apply GoodFunAsrt_ex.
intros.
apply GoodFunAsrt_star.
cbn. tauto.
apply GoodFunAsrt_Aarray_new.
Qed. *)

Lemma GoodFunAsrt_AOSPortAttrTbl':
  forall x,
    GoodFunAsrt (AOSPortAttrTbl' x ).  
  Proof.
intros. apply GoodFunAsrt_ex.
intros. apply GoodFunAsrt_star.
cbn. tauto.
apply GoodFunAsrt_star.
cbn. tauto.
apply GoodFunAsrt_Aarray_new.
Qed.

Lemma GoodFunAsrt_AEvtCap:
  forall scapl l fieldname eibtype,
    GoodFunAsrt (AEvtCap l scapl fieldname eibtype).
Proof.
  inductions scapl; intros.
  destruct l; simpl; auto.
  destruct l.
  unfold AEvtCap.
  fold AEvtCap.
  unfold GoodFunAsrt; fold GoodFunAsrt; intros.
  repeat (split; auto).
  apply GoodFunAsrt_Aarray.
Qed.

Lemma GoodFunAsrt_ASemCap:
  forall l scapl,
    GoodFunAsrt (ASemCap l scapl).
Proof.
  intros.
  unfold ASemCap.
  apply GoodFunAsrt_AEvtCap.
Qed. 

Lemma GoodFunAsrt_APthreadMutex :
  forall l vll,
    GoodFunAsrt (APthreadMutex l vll).
Proof.
  intros.
  unfold APthreadMutex; unfold GoodFunAsrt; fold GoodFunAsrt; intros.
  repeat (split; auto).
  apply GoodFunAsrt_Aarray_new.
Qed.

Lemma GoodFunAsrt_AMuxCap:
  forall l mcapl,
    GoodFunAsrt (AMuxCap l mcapl).
Proof.
  intros.
  unfold AMuxCap; unfold GoodFunAsrt; fold GoodFunAsrt; intros. 
  eapply GoodFunAsrt_AEvtCap.
Qed.

Lemma GoodFunAsrt_AMqAttr :
  forall l vll,
    GoodFunAsrt (AMqAttr l vll).
Proof.
  intros.
  unfold AMqAttr; unfold GoodFunAsrt; fold GoodFunAsrt; intros.
  repeat (split; auto).
  apply GoodFunAsrt_Aarray_new.
Qed.

Lemma GoodFunAsrt_AMqCap:
  forall l qcapl,
    GoodFunAsrt (AMqCap l qcapl).
Proof.
  intros.
  unfold AMqCap; unfold GoodFunAsrt; fold GoodFunAsrt; intros.
  eapply GoodFunAsrt_AEvtCap.
Qed. 

Lemma GoodFunAsrt_AEvAtomHeap :
forall evHeap,
 GoodFunAsrt (AEvAtomHeap evHeap).
Proof.
  induction evHeap.
  simpl; auto.
  simpl AEvAtomHeap.
  destruct a.
  destruct p.
  destruct t; try simpl GoodFunAsrt; auto.
Qed.

Lemma GoodFunAsrt_AEvStructHeap :
forall evHeap,
 GoodFunAsrt (AEvStructHeap evHeap).
Proof.
  induction evHeap.
  simpl; auto.
  simpl AEvStructHeap.
  destruct a.
  destruct p.
  destruct t; try simpl GoodFunAsrt; auto.
  splits; auto.
  apply GoodFunAsrt_Astruct'.
Qed.

Lemma GoodFunAsrt_AEvArrayHeap :
forall evHeap,
 GoodFunAsrt (AEvArrayHeap evHeap).
Proof.
  induction evHeap.
  simpl; auto.
  simpl AEvArrayHeap.
  destruct a.
  destruct p.
  try simpl GoodFunAsrt; auto.
  splits; auto.
  apply GoodFunAsrt_Aarray'.
Qed.

Lemma GoodFunAsrt_pos_sllseg:
  forall vll hd tn pbls,
    GoodFunAsrt (pos_sllseg hd tn vll pbls). 
Proof.
  inductions vll; intros.
  unfold pos_sllseg. simpl; auto.
  unfold pos_sllseg.
  simpl. splits; auto.
  intros.
  split; auto.
  destruct a.
  simpl; auto.
  simpl. 
  destruct a; splits; auto.
  simpl; auto.
  destruct a; simpl; auto.
Qed. 

Lemma GoodFunAsrt_err_sllseg :
forall vll p t ebls,
 GoodFunAsrt (err_sllseg p t vll ebls).
Proof.
  induction vll.
  simpl; auto.
  simpl err_sllseg.
  unfold GoodFunAsrt; fold GoodFunAsrt.
  intros; splits; auto.
  unfold node.
  unfold GoodFunAsrt; fold GoodFunAsrt.
  intros; splits; auto.
  apply GoodFunAsrt_Astruct.
Qed.

Lemma GoodFunAsrt_AErrblkList :
forall ebls,
 GoodFunAsrt (AErrblkList ebls).
Proof.
  induction ebls.
  simpl; auto.
  intros; splits; auto.
  intros.
  eapply GoodFunAsrt_err_sllseg.
Qed.

Lemma GoodFunAsrt_AOSPostEventTbl :
  forall l petbl,
    GoodFunAsrt (AOSPostEventTbl l petbl).
Proof.
  intros.
  unfold AOSPostEventTbl; unfold GoodFunAsrt; fold GoodFunAsrt; intros.
  repeat (split; auto).
  apply GoodFunAsrt_Aarray.
Qed.

Lemma GoodFunAsrt_llsegevaux:
  forall l hd tn locmp ptrmp nextf, 
    GoodFunAsrt (llsegevaux hd tn l locmp ptrmp nextf).  
Proof.
  induction l.
  intros. simpl. splits; auto.
  intros. simpl. intros. splits; auto. splits; auto. 
Qed.

Lemma GoodFunAsrt_AchannelTbl':
  forall x0 x,
    GoodFunAsrt (AchannelTbl' x x0).  
Proof.
  induction x0; intros;
  unfold AchannelTbl'; fold AchannelTbl';
  try destruct a;
  unfold GoodFunAsrt; fold GoodFunAsrt.
  auto. auto. auto.
  repeat (split; auto).
  apply GoodFunAsrt_Astruct.
  apply GoodFunAsrt_Aarray.
Qed.

Lemma GoodFunAsrt_AportTbl':
  forall x0 x,
    GoodFunAsrt (AportTbl' x x0).  
Proof.
  induction x0; intros;
  unfold AportTbl'; fold AportTbl';
  unfold GoodFunAsrt; fold GoodFunAsrt.
  auto.
  repeat (split; auto).
  apply GoodFunAsrt_Astruct.
Qed.

Lemma GoodFunAsrt_AksDomSchedule':
  forall x0 x,
    GoodFunAsrt (AksDomSchedule' x x0).  
Proof.
  induction x0; intros;
  unfold AksDomSchedule'; fold AksDomSchedule';
  unfold GoodFunAsrt; fold GoodFunAsrt.
  auto.
  repeat (split; auto).
  apply GoodFunAsrt_Astruct.
Qed.

Lemma GoodFunAsrt_ADeviceioTbl':
  forall x0 x,
    GoodFunAsrt (ADeviceioTbl' x x0).  
Proof.
  induction x0; intros;
  unfold ADeviceioTbl'; fold ADeviceioTbl';
  try destruct a;
  unfold GoodFunAsrt; fold GoodFunAsrt.
  auto. auto. auto.
  repeat (split; auto).
  apply GoodFunAsrt_Aarray.
  apply GoodFunAsrt_Astruct.
Qed.

Lemma GoodFunAsrt_AksDomains':
  forall x0 x,
    GoodFunAsrt (AksDomains' x x0).  
Proof.
  induction x0; intros;
  unfold AksDomains'; fold AksDomains';
  try destruct a as [[[]]];
  unfold GoodFunAsrt; fold GoodFunAsrt.
  auto.
  repeat (split; auto).
  apply GoodFunAsrt_Astruct.
  apply GoodFunAsrt_Aarray.
  apply GoodFunAsrt_ADeviceioTbl'.
  apply GoodFunAsrt_Astruct.
Qed.

Lemma GoodFunAsrt_Acpus':
  forall x0 x,
    GoodFunAsrt (Acpus' x x0).  
Proof.
  induction x0; intros;
  unfold Acpus'; fold Acpus';
  try destruct a as [[[]]];
  unfold GoodFunAsrt; fold GoodFunAsrt.
  auto.
  repeat (split; auto).
  apply GoodFunAsrt_Astruct.
  apply GoodFunAsrt_Aarray.
  apply GoodFunAsrt_AksDomSchedule'.
  apply GoodFunAsrt_AksDomains'.
Qed.

Lemma GoodFunAsrt_AucosConf:
  forall x x0, 
    GoodFunAsrt (AucosConf x x0).  
Proof.
  intros.
  unfold AucosConf.
  destruct x as [[[[[[]]]]]].
  destruct x0 as [[[[[[[[[[[[[]]]]]]]]]]]]].
  unfold GoodFunAsrt; fold GoodFunAsrt.
  repeat (split; auto).
  apply GoodFunAsrt_Astruct.
  apply GoodFunAsrt_Aarray.
  apply GoodFunAsrt_Astruct.
  apply GoodFunAsrt_Acpus'.
  apply GoodFunAsrt_AchannelTbl'.
  apply GoodFunAsrt_AportTbl'.
Qed.

Lemma GoodFunAsrt_AKsDomains':
  forall x0 x,
    GoodFunAsrt (AKsDomains' x x0).  
Proof.
  induction x0.
  simpl; auto.
  destruct a.
  unfold AKsDomains'; fold AKsDomains'.
  intros.
  unfold GoodFunAsrt; fold GoodFunAsrt.
  repeat (split; try intros; auto).
  apply GoodFunAsrt_Astruct.
  apply GoodFunAsrt_Aarray.
Qed.

(* add by CNU end *) 

Lemma GoodFunAsrt_AOScoreheapl : 
  forall x, GoodFunAsrt (AOScoreheapl x).
Proof.
  induction x;intros.
  simpl;auto.
  unfold AOScoreheapl;fold AOScoreheapl.
  destruct a as [ [? ?] ?].
  splits;auto.
  apply GoodFunAsrt_Aarray.
Qed.

Lemma GoodFunAsrt_AOScoreheape : 
  forall x, GoodFunAsrt (AOScoreheape x).
Proof.
  induction x;intros.
  simpl;auto.
  unfold AOScoreheape;fold AOScoreheape.
  destruct a as [ [? ?] ?].
  simpl;split;auto.
Qed.


Lemma GoodFunAsrt_AOScoreheapt : 
  forall x, GoodFunAsrt (AOScoreheapt x).
Proof.
  induction x;intros.
  simpl;auto.
  unfold AOScoreheapt;fold AOScoreheapt.
  destruct a as [ [? ?] ?].
  simpl. split;auto.
  apply GoodFunAsrt_Astruct.
Qed. 

Lemma GoodFunAsrt_Memory_sigcore_aux :
forall l n a, GoodFunAsrt (Memory_sigcore_aux n a l).
Proof. 
  induction l;intros.
  - unfold Memory_sigcore_aux;simpl;auto.
  - cbn [Memory_sigcore_aux].
    split;auto.
    unfold Memory_Node.
    split;[ |simpl; auto].
    apply GoodFunAsrt_Aarray.
Qed.

Lemma GoodFunAsrt_AOSIPCMem_aux : 
  forall x x0, GoodFunAsrt (AOSIPCMem_aux x x0).
Proof.
  induction x;intros.
  - destruct x0; simpl;auto.
  - 
  destruct x0;[ 
  destruct a;simpl;auto | ].
  destruct a; simpl;auto.
  split;auto.
  split;auto.
  apply GoodFunAsrt_Memory_sigcore_aux.
Qed.

Lemma GoodFunAsrt_Adynheap: forall h,
  GoodFunAsrt (Adynheap h).
Proof.
  induction h. now simpl. 
  destruct a. cbn [Adynheap]. repeat constructor; auto.
  apply GoodFunAsrt_Astruct.
Qed.

(*********************************)

Fixpoint nth_ectr (n : nat) (ll : list EventCtr) {struct ll} := 
  match ll with
  | nil => None
  | l :: ll' =>
      match n with
      | 0%nat => Some l
      | S n' => nth_ectr n' ll'
      end
  end.


(*add by xjl, some lemmas about capability*)
(* Lemma  GoodFunAsrt_ACap: 
    forall l vl, GoodFunAsrt(ACap l vl).
Proof.
    intros.
    unfold ACap.
    destruct vl.
    destruct c.
    destruct l.
    destruct p.
    unfold GoodFunAsrt; fold GoodFunAsrt.
    splits; simpl; auto.
Qed.

Lemma GoodFrm_ACap: 
    forall l vl, GoodFrm(ACap l vl).
Proof.
    intros.
    unfold ACap.
    destruct vl. destruct c. destruct l. destruct p.
    unfold GoodFrm; fold GoodFrm; simpl; auto.
Qed.
 
Lemma GoodFunAsrt_ASlots: 
    forall vl n l, GoodFunAsrt(ASlots l n vl).
Proof.
    inductions vl; intros.
    destruct n; simpl; auto.
    destruct n; simpl; auto.
    destruct a. simpl. auto.
    destruct a. destruct l. 
    unfold GoodFunAsrt; fold GoodFunAsrt.
    splits; simpl; auto.
    apply  GoodFunAsrt_ACap.
Qed.

Lemma GoodFrm_ASlots: 
    forall vl n l, GoodFrm(ASlots l n vl).
Proof.
    inductions vl; intros.
    destruct n; simpl; auto.
    destruct n; simpl; auto.
    destruct a. simpl. auto.
    destruct a. destruct l. 
    unfold GoodFrm; fold GoodFrm.
    splits; simpl; auto.
    apply GoodFrm_ACap.
Qed.

Lemma GoodFunAsrt_Acnode: 
    forall vl l, GoodFunAsrt(Acnode l vl).
Proof.
  unfold Acnode. intros.
  destruct vl. destruct p. destruct l. 
  unfold GoodFunAsrt; fold GoodFunAsrt.
  splits. simpl. auto.
  simpl. auto.
  apply GoodFunAsrt_ASlots.
  auto.
Qed.

Lemma GoodFrm_Acnode: 
    forall vl l, GoodFrm(Acnode l vl).
Proof.
  unfold Acnode. intros.
  destruct vl. destruct p. destruct l. 
  unfold GoodFrm; fold GoodFrm.
  splits. simpl. auto.
  simpl. auto.
  apply GoodFrm_ASlots.
  auto.
Qed.

Lemma GoodFunAsrt_ACSpaceAarrayTptr :
    forall vl pvl n cspacels, GoodFunAsrt(ACSpaceAarrayTptr n pvl vl cspacels).
Proof.
    inductions vl; intros.
    destruct n; destruct pvl. simpl. auto.
    simpl. destruct v; simpl; auto.
    simpl. auto.
    simpl. destruct v; simpl; auto.
    destruct n; destruct pvl; simpl; auto.
    destruct v; simpl; auto.
    destruct v; simpl; auto.
    splits; simpl; auto.
    unfold ACSpace.
    destruct a. destruct p.  destruct p. destruct a0. destruct p.
    unfold GoodFunAsrt; fold GoodFunAsrt.
    splits.
    apply GoodFunAsrt_Acnode.
    simpl. auto. auto.
    eapply GoodFunAsrt_Aarray.
    auto. simpl. auto.
    simpl. auto.
    simpl. auto.
Qed.

Require Import go.

Lemma GoodFrm_ACSpaceAarrayTptr :
    forall vl pvl n cspacels, GoodFrm(ACSpaceAarrayTptr  n pvl vl cspacels).
Proof.
    inductions vl; intros.
    destruct n; destruct pvl. simpl. auto.
    simpl. destruct v; simpl; auto.
    simpl. auto.
    simpl. destruct v; simpl; auto.
    destruct n; destruct pvl; simpl; auto.
    destruct v; simpl; auto.
    destruct v; simpl; auto.
    splits; simpl; auto.
    unfold ACSpace.
    destruct a. destruct p. destruct p. destruct a0. destruct p.
    unfold GoodFrm; fold GoodFrm.
    splits.
    apply GoodFrm_Acnode.
    simpl. auto. auto.
    unfold Aarray.
    go. auto. go.
    simpl. auto.
    simpl. auto.
Qed.
Lemma GoodFunAsrt_comm: 
  forall p q,
  GoodFunAsrt p ->
  GoodFunAsrt q ->
  GoodFunAsrt (p ** q).
Proof.
  intros.
  unfold GoodFunAsrt.
  fold GoodFunAsrt.
  splits; eauto.
Qed.



Lemma GoodFunAsrt_AOSCSpacePrioTbl: 
    forall l ptrvl vl cspacels, GoodFunAsrt (AOSCSpacePrioTbl l ptrvl vl cspacels).
Proof.
intros.
    unfold AOSCSpacePrioTbl.
    eapply GoodFunAsrt_comm.
    simpl. auto. 
    eapply GoodFunAsrt_comm.
    eapply GoodFunAsrt_Aarray.
    eapply GoodFunAsrt_comm.
    eapply GoodFunAsrt_ACSpaceAarrayTptr.
    simpl. auto. 
Qed.

Lemma GoodFrm_comm: 
  forall p q,
  GoodFrm p ->
  GoodFrm q ->
  GoodFrm (p ** q).
Proof.
  intros.
  unfold GoodFrm.
  fold GoodFrm.
  splits; eauto.
Qed.


Lemma GoodFrm_AOSCSpacePrioTbl: 
    forall l ptrvl vl cspacels, GoodFrm(AOSCSpacePrioTbl l ptrvl vl cspacels).
Proof.
intros.
  unfold AOSCSpacePrioTbl.
  eapply GoodFrm_comm.
  simpl. auto.
  eapply GoodFrm_comm.
  go.
  eapply GoodFrm_comm.
  eapply GoodFrm_ACSpaceAarrayTptr.
  simpl. 
  auto.
Qed. *)

Ltac GoodFunAsrt_solver :=
  repeat (split;
          try (apply GoodFunAsrt_Aarray);
          try (apply GoodFunAsrt_Astruct);
          try (apply GoodFunAsrt_AEventData);
          try (apply GoodFunAsrt_evsllseg);
          try (apply GoodFunAsrt_tcbdllseg);
          try (apply GoodFunAsrt_dllseg);
          try (apply GoodFunAsrt_ecbf_sll);
          try (apply GoodFunAsrt_sll);
          try (apply GoodFunAsrt_qblkf_sll);
          try (apply GoodFunAsrt_invlth_isr');
          try (apply GoodFunAsrt_Aarray_new);
          try simple apply GoodFunAsrt_AOSPortAttrTbl';
                    auto).

Require Import seplog_tactics.
Require Import seplog_lemmas.
Lemma sub_eq_succ:
forall m n l,  (S m <= l -> S n = l - m -> n = l - (S m))%nat. 
intros. auto with zarith. Qed.

Lemma ACSpaceAarrayTptr_succ_alt :
  forall s a vll n P p ptrvl2 cspacels, 
    s |= ACSpaceAarrayTptr  1 (p::nil) (a::nil) cspacels** ACSpaceAarrayTptr  n ptrvl2 vll cspacels ** P -> 
    s |= ACSpaceAarrayTptr  (S n) (p :: ptrvl2) (a :: vll) cspacels ** P.
Proof.
    intros.
    sep pauto.
    simpl ACSpaceAarrayTptr in *.
    destruct p. simpl.
    eapply astar_l_afalse_elim in H.
    simpl in H. tryfalse.
sep auto. 
    eapply astar_l_afalse_elim in H.
    simpl in H. tryfalse.
    sep auto.
Qed.




Lemma ACSpaceAarrayTptr_succ_imp :
  forall s a vll n  p ptrvl2 cspacels, 
  s |= ACSpaceAarrayTptr  (S n) (p :: ptrvl2) (a :: vll) cspacels->
    s |= ACSpaceAarrayTptr  1 (p::nil) (a::nil) cspacels ** ACSpaceAarrayTptr  n ptrvl2 vll cspacels.
    
Proof.
    intros.
    sep pauto.
    simpl ACSpaceAarrayTptr in *.
    destruct p. simpl in H. tryfalse.
sep auto.
    simpl in H. tryfalse.
        sep auto.
Qed.

Lemma ACSpaceAarrayTptr_succ_imp_frm :
  forall s a vll n  p ptrvl2 cspacels P, 
  s |= ACSpaceAarrayTptr  (S n) (p :: ptrvl2) (a :: vll) cspacels ** P->
    s |= ACSpaceAarrayTptr  1 (p::nil) (a::nil) cspacels ** ACSpaceAarrayTptr  n ptrvl2 vll cspacels ** P.
    
Proof.
  intros.
  sep cancel P.
  eapply ACSpaceAarrayTptr_succ_imp; eauto.
Qed.
Open Scope Z_scope.
Open Scope int_scope.
Lemma ACSpaceAarrayTptr_split_strong :
  forall ptrvl1 n ptrvl2 m  s vll1 vll2 cspacels, 
    s |= ACSpaceAarrayTptr (n + m) (ptrvl1 ++ ptrvl2) (vll1 ++ vll2) cspacels->
    Z.of_nat (S n * typelen (Tptr CSPACE)) <= Int.max_unsigned -> 
    (* 0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned -> *)
    length ptrvl1 = n /\ length ptrvl2 = m ->
    length vll1 = n /\ length vll2 = m ->
    s |= ACSpaceAarrayTptr n ptrvl1 vll1 cspacels** ACSpaceAarrayTptr  m ptrvl2 vll2 cspacels.
Proof.
  induction ptrvl1;induction n; intros.
  simpl ACSpaceAarrayTptr in *.
  simpl in H.
  destruct vll1.
  eapply astar_l_aemp_intro.
  auto.
  destruct H2.
  tryfalse.
  destruct H1. tryfalse.
  destruct H2; tryfalse.
  destruct H1. tryfalse.
  destruct vll1.
  destruct H2; tryfalse.
  eapply ACSpaceAarrayTptr_succ_alt.
  change ((a :: ptrvl1) ++ ptrvl2) with (a :: (ptrvl1 ++ ptrvl2)) in H.
  change ((c :: vll1) ++ vll2) with (c :: (vll1 ++ vll2)) in H.
  rewrite Nat.add_succ_l in H.
  eapply ACSpaceAarrayTptr_succ_imp in H.
  sep pauto.
  eapply IHptrvl1.

  sep pauto.
  auto with zarith.
  inverts H1. auto.
  inverts H2. splits; auto.
Qed.




(* OS_EventWaitListInit *)
(* pre *)

Open Scope code_scope.

Definition OS_EventWaitListInitPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX b  i1 i0 i2 x2 x3 v'22 v'24 s lg' pegrp petbl_addr petbl er,
    Aisr empisr ** Aie true ** Ais nil ** Acs nil ** Aier er **
         Astruct (b,  Int.zero) OS_EVENT
         (Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'22 :: Vint32 pegrp :: petbl_addr :: nil) **
         Aarray (b,  Int.zero+ᵢ($ 4+ᵢ($ 2+ᵢ($ 1+ᵢ($ 1+ᵢInt.zero)))))
         (Tarray Int8u ∘OS_EVENT_TBL_SIZE) v'24 **
          Aarray (b,  Int.zero+ᵢ ($ 1 +ᵢ  ($ 4 +ᵢ ($ 8 +ᵢ ($ 4+ᵢ($ 2+ᵢ($ 1+ᵢ($ 1+ᵢInt.zero))))))))
         (Tarray Int8u ∘OS_EVENT_TBL_SIZE) petbl **
          (* A_isr_is_prop ** *) <||s||> **
         [| nth_val 0 vl = Some (Vptr (b, Int.zero)) /\ Int.unsigned i1 <= 255/\Int.unsigned i0 <= 255/\Int.unsigned i2 <= 65535 /\
            isptr x2 /\ isptr v'22 /\ 
            logicl = logic_val (Vint32 i1) :: logic_val (Vint32 i2) :: logic_val x2 :: logic_val x3 :: logic_val v'22 :: logic_val petbl_addr :: logic_code s :: lg' |] ** 
         p_local OSLInv ct (logic_val (V$ 1) :: lg').

(* Definition OS_EventWaitListInitPre' (vl:vallist) (logicl:list logicvar) ct:= *)
(*   EX b  i1 i0 i2 x2 x3 v'22 v'24 s, *)
(*     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** *)
(*          Astruct (b,  Int.zero) OS_EVENT *)
(*          (Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'22 :: nil) ** *)
(*          Aarray (b,  Int.zero+ᵢ($ 4+ᵢ($ 2+ᵢ($ 1+ᵢ($ 1+ᵢInt.zero))))) *)
(*          (Tarray Int8u ∘OS_EVENT_TBL_SIZE) v'24 ** A_isr_is_prop ** <||s||> ** *)
(*          [| nth_val 0 vl = Some (Vptr (b, Int.zero)) /\ Int.unsigned i1 <= 255/\Int.unsigned i0 <= 255/\Int.unsigned i2 <= 65535 /\ *)
(*             isptr x2 /\ isptr v'22 /\ logicl = logic_code s :: nil|] ** p_local OSLInv ct init_lg. *)

Theorem OS_EventWaitListInitPreGood (vl:vallist)  (logicl:list logicvar) ct:
  GoodFunAsrt (OS_EventWaitListInitPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventWaitListInitPre : fpre :=
  fun vl ll ct=> mkfunasrt (OS_EventWaitListInitPreGood vl ll ct).

Notation INIT_EVENT_TBL :=
  (Vint32 Int.zero::
          Vint32 Int.zero::
          Vint32 Int.zero::
          Vint32 Int.zero::
          Vint32 Int.zero::
          Vint32 Int.zero::
          Vint32 Int.zero::
          Vint32 Int.zero::nil).

Definition OS_EventWaitListInitPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX b i1 i2 x2 x3 v'22 s lg' petbl_addr er,
    Aisr empisr ** Aie true ** Ais nil ** Acs nil ** Aier er **
         Astruct (b, Int.zero) OS_EVENT
         (Vint32 i1 :: Vint32 Int.zero :: 
                 Vint32 i2 :: x2 :: x3 :: v'22 :: Vint32 Int.zero :: petbl_addr :: nil) **
         Aarray (b,  Int.zero+ᵢ($ 4+ᵢ($ 2+ᵢ($ 1+ᵢ($ 1+ᵢInt.zero)))))
         (Tarray Int8u ∘OS_EVENT_TBL_SIZE) INIT_EVENT_TBL **
         Aarray (b,  Int.zero+ᵢ($ 1 +ᵢ  ($ 4 +ᵢ ($ 8 +ᵢ ($ 4+ᵢ($ 2+ᵢ($ 1+ᵢ($ 1+ᵢInt.zero))))))))
         (Tarray Int8u ∘OS_EVENT_TBL_SIZE) INIT_EVENT_TBL **
           (* A_isr_is_prop ** *) <||s||> **
         [| nth_val 0 vl = Some (Vptr (b, Int.zero)) /\ Int.unsigned i1 <= 255/\
            Int.unsigned i2 <= 65535 /\
            isptr x2 /\ isptr v'22 /\ v = None/\
            logicl =  logic_val (Vint32 i1) :: logic_val (Vint32 i2) :: logic_val x2 :: logic_val x3 :: logic_val v'22 :: logic_val petbl_addr :: logic_code s :: lg' |]
         ** p_local OSLInv ct (logic_val (V$ 1) :: lg').

(* Definition OS_EventWaitListInitPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:= *)
(*   EX b i1 i2 x2 x3 v'22 s, *)
(*     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** *)
(*          Astruct (b, Int.zero) OS_EVENT *)
(*          (Vint32 i1 :: Vint32 Int.zero ::  *)
(*                  Vint32 i2 :: x2 :: x3 :: v'22 :: nil) ** *)
(*          Aarray (b,  Int.zero+ᵢ($ 4+ᵢ($ 2+ᵢ($ 1+ᵢ($ 1+ᵢInt.zero))))) *)
(*          (Tarray Int8u ∘OS_EVENT_TBL_SIZE) INIT_EVENT_TBL ** A_isr_is_prop ** <||s||> ** *)
(*          [| nth_val 0 vl = Some (Vptr (b, Int.zero)) /\ Int.unsigned i1 <= 255/\ *)
(*             Int.unsigned i2 <= 65535 /\ *)
(*             isptr x2 /\ isptr v'22 /\ v = None/\ logicl = logic_code s :: nil|] ** p_local OSLInv  ct init_lg. *)

Theorem OS_EventWaitListInitPostGood (vl:vallist) (v:option val) (logicl:list logicvar) ct:
  GoodFunAsrt (OS_EventWaitListInitPost' vl v logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventWaitListInitPost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_EventWaitListInitPostGood vl v ll ct).

Close Scope code_scope.

(* OS_QPtrSearch *)
(* pre *)

(* Definition OS_EventSearchPre' (vl:vallist) (logicl:list logicvar) ct:= *)
(*   EX msgql ectrl ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp mqls tcbls qid vhold s, *)
(*     Aie false  ** Ais nil ** Acs (true::nil) ** Aisr empisr ** *)
(*     AECBList ectrl msgql mqls tcbls ** (* msgqlist *) *)
(*     AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls ** (* tcblist *) *)
(*     tcbdllflag p1 (tcbl1 ++ tcbcur :: tcbl2) ** *)
(*     AOSRdyTblGrp rtbl rgrp ** AOSTCBPrioTbl ptbl rtbl tcbls  vhold** (* rdy table & prio table *) *)
(*     HECBList mqls ** HTCBList tcbls ** HCurTCB ct  (* high level *) ** *)
(*      A_isr_is_prop ** <||s||> ** *)
(*     [| RH_TCBList_ECBList_P mqls tcbls ct|] ** *)
(*     [| nth_val 0 vl = Some (Vptr qid)|] ** *)
(*     [| RH_CurTCB ct tcbls |] ** [|logicl = logic_code s::nil|] ** p_local OSLInv  ct init_lg. *)

Lemma GoodFunAsrt_tcbdllflag:
  forall  ls p,
    GoodFunAsrt (tcbdllflag p ls).
Proof.
  inductions ls.
  simpl.
  auto.
  intros.
  simpl.
  intros.
  unfold tcbdllflag in IHls.
  splits; auto.
Qed.

(* Theorem OS_EventSearchPreGood (vl:vallist) logicl ct: *)
(*   GoodFunAsrt (OS_EventSearchPre' vl logicl ct). *)
(* Proof. *)
(*   GoodFunAsrt_solver. *)
(*   apply GoodFunAsrt_tcbdllflag; auto. *)
(* Qed. *)

(* Definition OS_EventSearchPre : fpre := *)
(*   fun vl ll ct=> mkfunasrt (OS_EventSearchPreGood vl ll ct). *)

(* post *)

(* Definition OS_EventSearchPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:= *)
(*   (EX msgqls ectrl1 ectrl2 msgqls1 msgqls2 ectrl ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp mqls tcbls qid p a b msgq vn mqls1 mqls2 mqls' mq vhold s, *)

(*   Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** *)
(*       GV OSEventList @ (Tptr OS_EVENT)  |-> p **  *)
(*       AEventNode (Vptr qid) a b msgq ** *)
(*       evsllseg p (Vptr qid) ectrl1 msgqls1 ** *)
(*       evsllseg vn Vnull ectrl2 msgqls2 ** *)
(*        A_isr_is_prop ** *)
(*       [|ECBList_P p Vnull ectrl msgqls mqls tcbls|] ** *)
(*       [|ECBList_P p (Vptr qid) ectrl1 msgqls1 mqls1 tcbls|] ** *)
(*       [|ECBList_P vn Vnull ectrl2 msgqls2 mqls2 tcbls|] ** *)
(*       [| RLH_ECBData_P msgq mq |] **  *)
(*       [| R_ECB_ETbl_P qid (a,b) tcbls |] ** *)
(*       [| EcbMod.joinsig qid mq mqls2 mqls'/\ EcbMod.join mqls1 mqls' mqls |] ** *)
(*       AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls ** (* tcblist *) *)
(*       tcbdllflag p1 (tcbl1 ++ tcbcur :: tcbl2) ** *)
(*       AOSRdyTblGrp rtbl rgrp ** AOSTCBPrioTbl ptbl rtbl tcbls vhold**(* rdy table & prio table *) *)
(*       HECBList mqls ** HTCBList tcbls ** HCurTCB ct  ** <||s ||> **  (* high level *)  *)
(*       [| RH_TCBList_ECBList_P mqls tcbls ct|] ** *)
(*       [| RH_CurTCB ct tcbls |] ** *)
(*       [| nth_val 0 vl = Some (Vptr qid)|] ** *)
(*       [| ectrl = ectrl1 ++ ((a,b)::nil) ++ ectrl2 |] ** *)
(*       [| msgqls = msgqls1 ++ (msgq::nil) ++msgqls2|] ** *)
(*       [|length ectrl1 = length msgqls1 |] ** *)
(*       [|V_OSEventListPtr a = Some vn|] ** *)
(*       [| v = Some (V$1) |] ** [|logicl = logic_code s :: nil|] ** p_local OSLInv  ct init_lg) \\//  *)
(*    (EX  msgql ectrl ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp mqls tcbls  qid  vhold s, *)
(*     Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** *)
(*         AECBList ectrl msgql mqls tcbls ** (* msgqlist *) *)
(*         AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls ** (* tcblist *) *)
(*         tcbdllflag p1 (tcbl1 ++ tcbcur :: tcbl2) ** *)
(*         AOSRdyTblGrp rtbl rgrp ** AOSTCBPrioTbl ptbl rtbl tcbls vhold** (* rdy table & prio table *) *)
(*         HECBList mqls ** HTCBList tcbls ** HCurTCB ct  ** <||s ||> **  (* high level *) *)
(*          A_isr_is_prop ** *)
(*         [| RH_TCBList_ECBList_P mqls tcbls ct|] ** *)
(*         [| RH_CurTCB ct tcbls |] ** *)
(*         [| nth_val 0 vl = Some (Vptr qid)|] ** *)
(*         [| (v = Some (V$0) /\  EcbMod.get mqls qid = None) |] *)
(*         ** [|logicl = logic_code s :: nil|]  ** p_local OSLInv  ct init_lg). *)

(* Theorem OS_EventSearchPostGood (vl:vallist) (v:option val) ll ct: *)
(*   GoodFunAsrt (OS_EventSearchPost' vl v ll ct). *)
(* Proof. *)
(*   GoodFunAsrt_solver. *)
(*  apply GoodFunAsrt_tcbdllflag; auto. *)
(*  apply GoodFunAsrt_tcbdllflag; auto. *)
(* Qed. *)

(* Definition OS_EventSearchPost : fpost := *)
(*  fun vl v ll ct=> mkfunasrt (OS_EventSearchPostGood vl v ll ct). *)

Fixpoint get_eid_ecbls (ecbls:list EventCtr):=
  match ecbls with
    | nil => nil 
    | (a,b,c)::ecbls' => (nth_val' 5 a) :: (get_eid_ecbls ecbls')
  end.

Definition get_eidls eid ecbls := eid::(List.removelast (get_eid_ecbls ecbls)).

Definition get_last_ptr (els : list EventCtr) :=
  match(last els (nil,nil,nil)) with
    | (a,b,c) => V_OSEventListPtr a
  end.

Definition OS_EventRemovePre' (vl:vallist) (logicl:list logicvar) ct:= 
  EX (msgql1 msgql2 : list EventData)
     (ectrl1 ectrl2 : list EventCtr)  
     p qid s ier,
  Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** Aier ier ** 
      GV OSEventList @ Tptr OS_EVENT |-> p **
      evsllseg p Vnull (ectrl1 ++ ectrl2) (msgql1 ++ msgql2) **
      A_isr_is_prop ** <||s||> **
      [|nth_val 0 vl = Some (Vptr qid) |] **
      [| length ectrl1 = length msgql1 |] **
      [| (ectrl1 = nil -> Vptr qid = p)
         /\ (ectrl1 <> nil -> Some (Vptr qid) = get_last_ptr ectrl1)|] ** 
      [| logicl = logic_val p ::  logic_leventc ectrl1 ::
                            logic_leventc ectrl2 :: logic_leventd msgql1 ::
                            logic_leventd msgql2 :: logic_code s ::
                            nil|]  ** p_local OSLInv  ct init_lg.

Theorem OS_EventRemovePreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_EventRemovePre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventRemovePre : fpre :=
  fun vl ll ct => mkfunasrt (OS_EventRemovePreGood vl ll ct).

(* post *)

Fixpoint update_nth  (t :  Type ) (n : nat) (vl : list t) (v : t) {struct vl} : list t :=
  match vl with
    | nil => nil
    | v' :: vl' =>
      match n with
      | 0%nat => v :: vl'
      | S n' => v' :: update_nth t n' vl' v
      end
  end.

Definition update_ectr (x : EventCtr)  (v : val) :=
  match x with
   | (a , b, c) => (update_nth _ 5%nat a v, b, c)
  end.

Fixpoint update_nth_ectrls (els : list EventCtr) (n: nat) (v:val) :=
  match els with
    | nil => nil
    | v' :: vl' =>
      match n with
        | 0%nat => (update_ectr v' v) :: vl'
        | S n' => v' :: update_nth_ectrls vl' n' v
      end
  end.

Definition upd_last_ectrls (els : list EventCtr) (v:val) :=
  update_nth_ectrls els (length els - 1)%nat v.
(*here can compile*)
 Definition OS_EventRemovePost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
 (EX (msgql1 msgql2 : list EventData)
     (ectrl1 ectrl2 ectrl1': list EventCtr) 
     p p' next  ectr msgq osevent etbl petbl qid s ier,
  Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** Aier ier ** 
      GV OSEventList @ Tptr OS_EVENT |-> p' **
      evsllseg p' Vnull (ectrl1'++ectrl2) (msgql1++msgql2) **
      AEventNode (Vptr qid) osevent etbl petbl msgq **
       A_isr_is_prop ** <||s||> **
      [| logicl = logic_val p ::  logic_leventc ectrl1 ::
           logic_leventc  (ectr::ectrl2) :: logic_leventd msgql1 ::
                                logic_leventd (msgq::msgql2) ::logic_code s ::
                                 nil|]**
      [| nth_val 0 vl = Some (Vptr qid) |] **
      [| ectr = (osevent,etbl,petbl) |] **
      [| length ectrl1 = length msgql1 |] **
      [| Some next = V_OSEventListPtr osevent |] **
      [| (ectrl1 = nil -> (Vptr qid = p /\ p' = next /\ ectrl1' = nil))
       /\ (ectrl1 <> nil -> (p' = p /\ Some (Vptr qid) = get_last_ptr ectrl1 /\
       ectrl1' = upd_last_ectrls ectrl1 next))|]  ** p_local OSLInv  ct init_lg 
 ).

Theorem OS_EventRemovePostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_EventRemovePost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventRemovePost : fpost :=
  fun vl v ll ct=> mkfunasrt (OS_EventRemovePostGood vl v ll ct).

(* OS_EventRemoveDel *)

Definition OS_EventRemoveDelPre' (vl:vallist) (logicl:list logicvar) ct:= 
  EX (msgql1 : list EventData) (ectrl1 : list EventCtr)  
     p qid osevent etbl petbl s lg' ier, 
      Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** Aier ier **
      GV OSEventList @ Tptr OS_EVENT |-> p **
      evsllseg p (Vptr qid) ectrl1 msgql1 **
      AOSEvent (Vptr qid) osevent etbl petbl **
      A_isr_is_prop **
      <||s||> ** 
      [| nth_val 0 vl = Some (Vptr qid) |] **
      [| logicl = logic_val p :: logic_leventc ectrl1 :: logic_leventd msgql1 ::
                            logic_code s ::
                            logic_lv osevent :: logic_lv etbl :: logic_lv petbl :: lg' |]  **
      p_local OSLInv ct (logic_val (V$1) :: lg'). 

Theorem OS_EventRemoveDelPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_EventRemoveDelPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventRemoveDelPre : fpre := 
  fun vl ll ct => mkfunasrt (OS_EventRemoveDelPreGood vl ll ct).

Definition OS_EventRemoveDelPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  (EX (msgql1 : list EventData) (ectrl1 ectrl1': list EventCtr)  
      p p' next osevent etbl petbl qid s lg' ier,
     Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** Aier ier **
       GV OSEventList @ Tptr OS_EVENT |-> p' **
       evsllseg p' next ectrl1' msgql1 **
       AOSEvent (Vptr qid) osevent etbl petbl **
       A_isr_is_prop **
       <||s||> **
       [| logicl = logic_val p :: logic_leventc ectrl1 :: logic_leventd msgql1 :: 
                             logic_code s ::
                             logic_lv osevent :: logic_lv etbl :: logic_lv petbl :: lg' |] ** 
       [| nth_val 0 vl = Some (Vptr qid) |] **
       [| Some next = V_OSEventListPtr osevent |] **
       [| (ectrl1 = nil -> (Vptr qid = p /\ p' = next /\ ectrl1' = nil)) /\ 
          (ectrl1 <> nil ->
           (p' = p /\ Some (Vptr qid) = get_last_ptr ectrl1 /\
            ectrl1' = upd_last_ectrls ectrl1 next)) |]  ** 
       p_local OSLInv ct (logic_val (V$1) :: lg')
  ).

Theorem OS_EventRemoveDelPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_EventRemoveDelPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventRemoveDelPost : fpost :=
  fun vl v ll ct=> mkfunasrt (OS_EventRemoveDelPostGood vl v ll ct).

(* OS_EventTO *)
Definition OS_EventTOPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX tcbcur qid osevent etbl (d:EventData) s lg' petbl er,
    Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** A_isr_is_prop ** Aier er **
     <||s||> **
      GV OSTCBCur @ Tptr OS_TCB |-r-> (Vptr ct) **
      node (Vptr ct) tcbcur OS_TCB_flag ** (* OSTCBCur node *)
      AEventNode (Vptr qid) osevent etbl petbl d **
    [| RL_TCBblk_P tcbcur |] **
    [| nth_val 0 vl = Some (Vptr qid)|] ** 
    [| logicl = logic_lv tcbcur :: logic_lv osevent ::
                logic_lv etbl ::  logic_lv petbl :: logic_leventd (d::nil) :: logic_code s :: lg' |] **
     p_local OSLInv ct (logic_val (V$ 1) :: lg').


Theorem OS_EventTOPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_EventTOPre' vl ll ct).
Proof.
GoodFunAsrt_solver.
Qed.

Definition OS_EventTOPre : fpre :=
  fun vl ll ct => mkfunasrt (OS_EventTOPreGood vl ll ct).

Definition OS_EventTOPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
   EX tcbcur qid osevent etbl d s y bitx bity ey tcbcur' osevent' etbl' egrp' lg' petbl er, 
    Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** A_isr_is_prop ** Aier er **
     <||s||> **
      GV OSTCBCur @ Tptr OS_TCB |-r-> (Vptr ct) **
      node (Vptr ct) tcbcur' OS_TCB_flag ** (* OSTCBCur node *)
      AEventNode (Vptr qid) osevent' etbl' petbl d **
    [| logicl = logic_lv tcbcur :: logic_lv osevent ::
                logic_lv etbl ::  logic_lv petbl :: logic_leventd (d::nil) :: logic_code s :: lg' |] **
    [| nth_val 0 vl = Some (Vptr qid)|] **
    [| V_OSTCBY tcbcur = Some (Vint32 y) /\
        V_OSTCBBitX tcbcur = Some (Vint32 bitx) /\
        V_OSTCBBitY tcbcur = Some (Vint32 bity) /\
        nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 ey /\
        etbl' = update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (ey&ᵢInt.not bitx)) /\
        osevent' = update_nth_val 1 osevent (Vint32 egrp') /\
        tcbcur' = update_nth_val 5 (update_nth_val 2 tcbcur (Vnull)) (Vint32 (Int.repr OS_STAT_RDY)) |] **
     p_local OSLInv ct (logic_val (V$ 1) :: lg'). 

Theorem OS_EventTOPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_EventTOPost' vl v ll ct).
Proof.
GoodFunAsrt_solver.
Qed.

Definition OS_EventTOPost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_EventTOPostGood vl v ll ct).


(* OS_EventPostTO *)
(* pre *)
Definition OS_EventPostTOPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX tcbcur qid osevent etbl petbl (d:EventData) s ptrv er,
    Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** A_isr_is_prop ** Aier er **
     <||s||> **
      GV OSTCBCur @ Tptr OS_TCB |-r-> (Vptr ct) **
      node (Vptr ct) tcbcur OS_TCB_flag ** (* OSTCBCur node *)
      AEventNode (Vptr qid) osevent etbl petbl d **
    [| RL_TCBblk_P tcbcur |] **
    [| nth_val 0 vl = Some (Vptr qid)|] ** 
    [| logicl = logic_lv tcbcur :: logic_lv osevent ::
                logic_lv etbl :: logic_lv petbl :: logic_leventd (d::nil) :: logic_code s :: logic_val ptrv :: nil |] **
     p_local OSLInv  ct (  logic_val (V$ 1)
                     :: logic_val (V$ __EvLoc_normal)
                     :: logic_val Vnull :: logic_val Vnull :: logic_val ptrv :: nil).


Theorem OS_EventPostTOPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_EventPostTOPre' vl ll ct).
Proof.
GoodFunAsrt_solver.
Qed.

Definition OS_EventPostTOPre : fpre :=
  fun vl ll ct => mkfunasrt (OS_EventPostTOPreGood vl ll ct).

Open Scope int_scope.

Definition OS_EventPostTOPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
   EX tcbcur qid osevent etbl petbl d s y bitx bity ey tcbcur' osevent' petbl' pegrp' ptrv er,
    Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** A_isr_is_prop ** Aier er **
     <||s||> **
      GV OSTCBCur @ Tptr OS_TCB |-r-> (Vptr ct) **
      node (Vptr ct) tcbcur' OS_TCB_flag ** (* OSTCBCur node *)
      AEventNode (Vptr qid) osevent' etbl petbl' d **
    [| logicl = logic_lv tcbcur :: logic_lv osevent ::
                logic_lv etbl :: logic_lv petbl :: logic_leventd (d::nil) :: logic_code s :: logic_val ptrv :: nil |] **
    [| nth_val 0 vl = Some (Vptr qid)|] **
    [| V_OSTCBY tcbcur = Some (Vint32 y) /\
        V_OSTCBBitX tcbcur = Some (Vint32 bitx) /\
        V_OSTCBBitY tcbcur = Some (Vint32 bity) /\
        nth_val' (Z.to_nat (Int.unsigned y)) petbl = Vint32 ey /\
        petbl' = update_nth_val (Z.to_nat (Int.unsigned y)) petbl (Vint32 (ey&ᵢInt.not bitx)) /\
        osevent' = update_nth_val 6 osevent (Vint32 pegrp') /\
        tcbcur' = update_nth_val 5 (update_nth_val 3 (update_nth_val 2 tcbcur (Vnull)) (Vnull) ) (Vint32 (Int.repr OS_STAT_RDY)) |] **
     p_local OSLInv  ct (  logic_val (V$ 1)
                     :: logic_val (V$ __EvLoc_normal)
                     :: logic_val Vnull :: logic_val Vnull :: logic_val ptrv :: nil).

Theorem OS_EventPostTOPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_EventPostTOPost' vl v ll ct).
Proof.
GoodFunAsrt_solver.
Qed.

Definition OS_EventPostTOPost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_EventPostTOPostGood vl v ll ct).



(* OS_EventTaskRdy *)
(* pre *)
(* OS_EventTaskRdy *)
(* pre *)
(*参考对象*)
Definition OS_EventTaskRdyPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX message msk vhold tcbls ptbl rtbl rgrp vltcb egrp qid osevent etbl petbl d s head headprev tail tailnext lg' er cs is isr,
  Aie false ** Ais is ** Acs cs ** Aisr isr **  A_isr_is_prop ** Aier er **
  AEventNode (Vptr qid) osevent etbl petbl d ** (*has pure properties*)
  <||s||> **
  AOSUnMapTbl **
  AOSMapTbl **
  AOSRdyTblGrp rtbl rgrp ** (*has pure properties*)
  GAarray OSTCBPrioTbl (Tarray (Tptr OS_TCB) 64) ptbl **
  tcbdllseg head headprev tail tailnext vltcb **

  [| ptr_in_tcblist (Vptr ct) head vltcb |] **
  [| array_type_vallist_match (Tptr OS_TCB) ptbl /\ length ptbl = 64%nat |] **
  [| RL_RTbl_PrioTbl_P rtbl ptbl vhold |] **
  [| R_PrioTbl_P ptbl tcbls vhold |] **
  [| R_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls |] **
  [| TCBList_P head vltcb rtbl tcbls |] **

  [| nth_val 0 vl = Some (Vptr qid) |] **
  [| nth_val 1 vl = Some message |] **
  [| nth_val 2 vl = Some (Vint32 msk) |] **
  
  [| V_OSEventGrp osevent = Some (Vint32 egrp) /\ egrp <> Int.zero |] **
  [| logicl = logic_val (Vptr vhold) :: logic_val head ::
              logic_val headprev :: logic_val tail :: logic_val tailnext ::
              logic_lv ptbl :: logic_lv rtbl :: logic_val rgrp ::
              logic_lv osevent :: logic_lv etbl :: logic_lv petbl :: logic_leventd (d::nil) ::
              logic_code s :: logic_abstcb tcbls :: logic_llv vltcb ::
              logic_val (Vint32 egrp) :: logic_cs cs :: 
              logic_is is :: logic_isr isr :: logic_ier er :: lg' |] **
  p_local OSLInv ct (logic_val (V$ 1) :: lg').
  
Theorem OS_EventTaskRdyPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_EventTaskRdyPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventTaskRdyPre : fpre :=
  fun vl ll ct => mkfunasrt (OS_EventTaskRdyPreGood vl ll ct).

Fixpoint tcblist_get p head tcbl :=
  match tcbl with
    | nil => None
    | h::tcbl' =>
      if beq_val p head
      then
        Some h
      else
        match (V_OSTCBNext h) with
          | Some head' => tcblist_get p head' tcbl'
          | None => None
        end
  end.

Fixpoint set_node (p:val) (vl':vallist) (head:val) (l:list vallist) :=
  match l with
    | nil => nil
    | vl::l' =>
      if beq_val p head
      then vl'::l'
      else vl::set_node p vl' (nth_val' 0 vl) l'
  end.

Definition rel_edata_tcbstat edata tcbstat :=
  match edata with
    | DMsgQ _ _ _ _ =>
      tcbstat = Int.repr OS_STAT_Q \/ tcbstat = Int.or (Int.repr OS_STAT_Q) (Int.repr OS_STAT_SUSPEND)
    | DSem _ =>
      tcbstat = Int.repr OS_STAT_SEM \/ tcbstat = Int.or (Int.repr OS_STAT_SEM) (Int.repr OS_STAT_SUSPEND)
    | DMbox _ =>
      tcbstat = Int.repr OS_STAT_MBOX \/ tcbstat = Int.or (Int.repr OS_STAT_MBOX) (Int.repr OS_STAT_SUSPEND)
    | DMutex _ _ =>
      tcbstat = Int.repr OS_STAT_MUTEX \/ tcbstat = Int.or (Int.repr OS_STAT_MUTEX) (Int.repr OS_STAT_SUSPEND)
    | DPort =>
    tcbstat = Int.repr OS_STAT_PORT \/ tcbstat = Int.or (Int.repr OS_STAT_PORT) (Int.repr OS_STAT_SUSPEND)
  end.

Open Scope int_scope.
Definition OS_EventTaskRdyPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX vhold tcbls vltcb vltcb' ptbl rtbl rtbl' rgrp rgrp' egrp egrp' etbl etbl' petbl qid osevent osevent' d s head headprev tail tailnext message msk lg'
         er cs is isr,
    Aie false ** Ais is ** Acs cs ** Aisr isr ** A_isr_is_prop ** Aier er **
    AEventNode (Vptr qid) osevent' etbl' petbl d ** <||s||> **
    AOSUnMapTbl **
    AOSMapTbl **
    AOSRdyTblGrp rtbl' rgrp' **

    GAarray OSTCBPrioTbl (Tarray (Tptr OS_TCB) 64) ptbl **    
    tcbdllseg head headprev tail tailnext vltcb' **

    [| nth_val 0 vl = Some (Vptr qid) |] **
    [| nth_val 1 vl = Some message |] **
    [| nth_val 2 vl = Some (Vint32 msk) |] **
    
    [| ptr_in_tcblist (Vptr ct) head vltcb'|] **
    [| array_type_vallist_match (Tptr OS_TCB) ptbl /\ length ptbl = 64%nat |] ** (*same as in pre*)
    [| RL_RTbl_PrioTbl_P rtbl' ptbl vhold |] **
    [| R_PrioTbl_P ptbl tcbls vhold |] ** (*same as in pre*)
    [| R_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls |] ** (*same as in pre*)
    [| TCBList_P head vltcb rtbl tcbls |] ** (*same as in pre*)
    (*pevent′→OSEventTbl[y′] =ₑ pevent′→OSEventTbl[y′] &ₑ (∼bitx′);ₛ*)
    [| logicl = logic_val (Vptr vhold) :: logic_val head ::
                logic_val headprev :: logic_val tail :: logic_val tailnext ::
                logic_lv ptbl :: logic_lv rtbl :: logic_val rgrp ::
                logic_lv osevent :: logic_lv etbl :: logic_lv petbl :: logic_leventd (d::nil) ::
                logic_code s :: logic_abstcb tcbls :: logic_llv vltcb ::
                logic_val (Vint32 egrp) :: logic_cs cs ::
                logic_is is :: logic_isr isr :: logic_ier er :: lg' |] **

    EX x y i1 bitx bity,
    [| nth_val' (Z.to_nat (Int.unsigned egrp)) OSUnMapVallist = Vint32 y |] **
    [| nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 i1 |] **
    [| nth_val' (Z.to_nat (Int.unsigned i1)) OSUnMapVallist = Vint32 x |] **
    [| nth_val' (Z.to_nat (Int.unsigned y)) OSMapVallist = Vint32 bity |] **
    [| nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 bitx |] **
    
    [| osevent' = update_nth_val 1 osevent (Vint32 egrp') |] **
    [| etbl' = update_nth_val
                 (Z.to_nat (Int.unsigned y)) etbl (Vint32 (i1&ᵢInt.not bitx)) |] **
      (*etbl = pevent′→OSEventTbl*)     
    (*ret value prio = get highest wait task in etbl*)
    [| v = Some (Vint32 ((y<<ᵢ$ 3)+ᵢx)) |] **

    (*relation between old vltcb and new vltcb*)
    (EX vl vl' next prev eptr msg dly stat prio tcbx tcby tcbbitx tcbbity t,
     [| nth_val' (Z.to_nat (Int.unsigned ((y<<ᵢ$ 3)+ᵢx))) ptbl  = (Vptr (t, Int.zero))
        /\ (t, Int.zero) <> vhold|] **
    [| tcblist_get (Vptr (t, Int.zero)) head vltcb = Some vl /\ struct_type_vallist_match OS_TCB_flag vl|] **
    [| vltcb' = set_node (Vptr (t, Int.zero)) vl' head vltcb |] **
    [| vl = next::prev::eptr::msg::dly::(Vint32 stat)::prio::tcbx::tcby::tcbbitx::tcbbity::nil|] **
    [| vl' = next::prev::Vnull::message::(Vint32 Int.zero)::(Vint32 (Int.and stat (Int.not msk)))::prio::tcbx::tcby::tcbbitx::tcbbity::nil|] **

    (*relation between data and tcbstat, for proving tcb rdy*)
    [| rel_edata_tcbstat d stat |]
    (* ) *) **
    
    (* ( *)EX i1', [| nth_val' (Z.to_nat (Int.unsigned y)) rtbl = Vint32 i1' |] **    
      [| rtbl' = ( if Int.eq (Int.and stat (Int.not msk)) (Int.repr OS_STAT_RDY)
                           then update_nth_val (Z.to_nat (Int.unsigned y)) rtbl (Vint32 (Int.or i1' bitx))
                           else rtbl)|]) **
    
 (*pure properties on old values in AOSRdyTblGrp, keep them in the post condition *)
    [|RL_Tbl_Grp_P rtbl rgrp /\ prio_in_tbl ($ OS_IDLE_PRIO) rtbl|] **
    [|array_type_vallist_match Tint8 rtbl /\ length rtbl = nat_of_Z OS_RDY_TBL_SIZE|] **
    [|rule_type_val_match Tint8 rgrp = true|] **
    [|RL_Tbl_Grp_P etbl (Vint32 egrp)|] **
    [|array_type_vallist_match Tint8 etbl|]
    ** p_local OSLInv ct (logic_val (V$ 1) :: lg').

Theorem OS_EventTaskRdyPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_EventTaskRdyPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventTaskRdyPost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_EventTaskRdyPostGood vl v ll ct).

(* OS_EventTaskWait *)
(* pre *)
Definition OS_EventTaskWaitPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX tcbcur rtbl rgrp qid osevent etbl petbl d s lg' er,
   <||s||> ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** Aier er **
    GV OSTCBCur @ Tptr OS_TCB |-r-> (Vptr ct) **
    node (Vptr ct) tcbcur OS_TCB_flag ** (*modified by zhanghui*)  (* OSTCBCur node *)
    [| RL_TCBblk_P tcbcur |] **
      AOSRdyTblGrp rtbl rgrp ** AEventNode (Vptr qid) osevent etbl petbl d **
    [| logicl =logic_lv rtbl :: logic_val rgrp :: logic_lv tcbcur :: logic_lv osevent ::
                logic_lv etbl :: logic_lv petbl :: logic_leventd (d::nil) :: logic_code s :: lg' |] **
    [| nth_val 0 vl = Some (Vptr qid) /\ (exists p,V_OSTCBPrio tcbcur = Some (Vint32 p) /\ Int.eq p ($ OS_IDLE_PRIO) = false) |] ** p_local OSLInv ct (logic_val (V$ 1) :: lg').

Theorem OS_EventTaskWaitPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_EventTaskWaitPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventTaskWaitPre : fpre :=
  fun vl ll ct => mkfunasrt (OS_EventTaskWaitPreGood vl ll ct).

(* post *)
Definition OS_EventTaskWaitPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:= 
  (EX tcbcur rtbl rgrp qid osevent etbl petbl d
     tcbcur' rtbl' rgrp' osevent' etbl'
     y bitx bity ry ey egrp s lg' er,
  Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** Aier er **
    GV OSTCBCur @ Tptr OS_TCB |-r-> (Vptr ct) **
    node (Vptr ct) tcbcur' OS_TCB_flag (*modified by zhanghui*) ** (* OSTCBCur node *) 
    AOSRdyTblGrp rtbl' (Vint32 rgrp') ** AEventNode (Vptr qid) osevent' etbl' petbl d **
    <||s||> **
    [| logicl = logic_lv rtbl :: logic_val (Vint32 rgrp) :: logic_lv tcbcur :: logic_lv osevent ::
                logic_lv etbl :: logic_lv petbl :: logic_leventd (d::nil) :: logic_code s :: lg' |] **
    [| nth_val 0 vl = Some (Vptr qid) |] ** 
    [| tcbcur' = update_nth_val 2 tcbcur (Vptr qid) /\ 
       V_OSTCBY tcbcur = Some (Vint32 y) /\
       V_OSTCBBitX tcbcur = Some (Vint32 bitx) /\
       V_OSTCBBitY tcbcur = Some (Vint32 bity) /\
       nth_val (nat_of_Z (Int.unsigned y)) rtbl = Some (Vint32 ry) /\
       rtbl' = update_nth_val (nat_of_Z (Int.unsigned y)) rtbl (Vint32 (Int.and ry (Int.not bitx))) /\
       nth_val (nat_of_Z (Int.unsigned y)) etbl = Some (Vint32 ey) /\ 
       etbl' = update_nth_val (nat_of_Z (Int.unsigned y)) etbl (Vint32 (Int.or ey bitx)) /\
       V_OSEventGrp osevent = Some (Vint32 egrp) /\
       osevent' = update_nth_val 1 osevent (Vint32 (Int.or egrp bity)) |] ** 
       p_local OSLInv ct (logic_val (V$ 1) :: lg')).


Theorem OS_EventTaskWaitPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_EventTaskWaitPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventTaskWaitPost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_EventTaskWaitPostGood vl v ll ct).


Definition OS_SchedPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX s v logicl' er,
  Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
      <||isched;;s||> ** [|logicl = logic_code s :: logicl'|]  ** p_local OSLInv ct (logic_val v :: logicl') ** [| isflag v |].

Definition OS_SchedPost' (vl:vallist) (v:option val)  (logicl:list logicvar) ct:=
  EX s logicl' er,
  Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
      <||s||> ** [|logicl = logic_code s :: logicl'|]  ** p_local OSLInv ct (logic_val (V$ 1) :: logicl').


Theorem OS_SchedPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_SchedPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Theorem OS_SchedPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_SchedPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_SchedPre : fpre :=
  fun vl ll ct => mkfunasrt (OS_SchedPreGood vl ll ct).

Definition OS_SchedPost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_SchedPostGood vl v ll ct).

(* IPC Sched *)

(*
Definition OS_IPCSchedPre' (vl:vallist) (logicl:list logicvar) ct:=
  (EX s v logicl' er is cs isr vnest vlock,
  Aie false ** Ais is ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
     [|logicl = logic_ier er :: logic_is is :: logic_isr isr :: logic_cs cs ::
                        logic_val (Vint32 vnest):: logic_val (Vint32 vlock) ::
                        logic_code s :: logic_val v :: logicl'|]  **
     GV OSIntNesting @ Tint32 |-> Vint32 vnest **
     GV OSLockNesting @ Tint32 |-> Vint32 vlock **
     [| Int.eq vnest Int.zero = false \/ Int.eq vlock Int.zero = false |]  **
     p_local OSLInv ct (logic_val v :: logicl') ** [| isflag v |]).

Definition OS_IPCSchedPost' (vl:vallist) (v:option val)  (logicl:list logicvar) ct:=
  (EX s v logicl' er is cs isr vnest vlock,
    Aie false ** Ais is ** Acs cs ** Aisr isr ** Aier er **
    <||s||> **
   [|logicl = logic_ier er :: logic_is is :: logic_isr isr :: logic_cs cs ::
                      logic_val (Vint32 vnest):: logic_val (Vint32 vlock) ::
                      logic_code s :: logic_val v :: logicl'|]  **
   GV OSIntNesting @ Tint32 |-> Vint32 vnest **
   GV OSLockNesting @ Tint32 |-> Vint32 vlock **
   [| Int.eq vnest Int.zero = false \/ Int.eq vlock Int.zero = false |]  **
    p_local OSLInv ct (logic_val v :: logicl') ** [| isflag v |]).
*)


Definition OS_IPCSchedPre' (vl:vallist) (logicl:list logicvar) ct:=
  (EX s v logicl' er ie is cs isr vnest vlock,
  Aie ie ** Ais is ** Acs cs ** Aisr isr ** Aier er **
     [|logicl = logic_ier er :: logic_ie ie :: logic_is is :: logic_isr isr :: logic_cs cs ::
                        logic_val (Vint32 vnest):: logic_val (Vint32 vlock) ::
                        logic_code s :: logic_val v :: logicl'|]  **   
     GV OSIntNesting @ Tint32 |-> Vint32 vnest **
     GV OSLockNesting @ Tint32 |-> Vint32 vlock **     
     (<|| s ||> **  [| Int.eq vnest Int.zero = false \/ Int.eq vlock Int.zero = false |]  ** [|ie = false|] \\//
     <||isched;;s||> ** [| Int.eq vnest Int.zero = true /\ Int.eq vlock Int.zero = true |]  ** [|ie = true /\ is = nil /\ cs = nil /\ isr = empisr |]) **
     p_local OSLInv ct (logic_val v :: logicl') ** [| isflag v |]).

Definition OS_IPCSchedPost' (vl:vallist) (v:option val)  (logicl:list logicvar) ct:=
  (EX s v logicl' er ie is cs isr vnest vlock,
    Aie ie ** Ais is ** Acs cs ** Aisr isr ** Aier er **
    <|| s ||> ** 
    [|logicl = logic_ier er :: logic_ie ie :: logic_is is :: logic_isr isr :: logic_cs cs ::
                      logic_val (Vint32 vnest):: logic_val (Vint32 vlock) ::
                      logic_code s :: logic_val v :: logicl'|]  **  
    GV OSIntNesting @ Tint32 |-> Vint32 vnest **
    GV OSLockNesting @ Tint32 |-> Vint32 vlock **   
    ([| Int.eq vnest Int.zero = false \/ Int.eq vlock Int.zero = false |]  ** [|ie = false|] \\// [| Int.eq vnest Int.zero = true /\ Int.eq vlock Int.zero = true |] **
    [|ie = true /\ is = nil /\ cs = nil /\ isr = empisr|] ** [| v = (V$ 1) |]
    ) ** p_local OSLInv ct (logic_val v :: logicl') ** [| isflag v |]).



Theorem OS_IPCSchedPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_IPCSchedPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Theorem OS_IPCSchedPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_IPCSchedPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_IPCSchedPre : fpre :=
  fun vl ll ct => mkfunasrt (OS_IPCSchedPreGood vl ll ct).

Definition OS_IPCSchedPost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_IPCSchedPostGood vl v ll ct).

Definition OS_IPCSched_spec : fspec:= (OS_IPCSchedPre,OS_IPCSchedPost,(Tvoid,nil)).

(* OSIntExit *)

(*
Definition fx is (O : osabst)  := is_nest is = false.
Definition nfx is  (O : osabst)  := is_nest is = true.
*)
(*
Definition OSIntExitPre' (vl:vallist) (logicl:list logicvar) ct :=
  EX ir ie si i v, [|logicl=  (logic_isr ir) :: (logic_ie ie) ::
                                           (logic_is si) :: (logic_hid i) :: (logic_val v) :: nil |] ** Aisr (isrupd ir i%nat false) **
       Aie ie **
       Ais (i%nat :: si) **
       Acs nil ** <|| (isched;; END None ?? END None)||> **
       [| isr_is_prop (isrupd ir i%nat false) (i%nat :: si) |] **
       [| (i <= INUM)%nat /\ (forall j : nat, (0 <= j < i)%nat ->  (isrupd ir i%nat false) j = false) |] **
       ((
       (EX (eventl osql qblkl : list vallist) (msgql : list EventData)
           (ectrl : list EventCtr) (ptbl : vallist) (p1 p2 : val) 
           (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
           (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map) 
           (tcbls : TcbMod.map) (t : int32) pf lf vhold,
        AOSEventFreeList eventl **
                         AOSQFreeList osql **
                         AOSQFreeBlk qblkl **
                         AECBList ectrl msgql ecbls tcbls **
                         AOSMapTbl **
                         AOSUnMapTbl **
                         AOSTCBPrioTbl ptbl rtbl tcbls vhold**
                         AOSIntNesting **
                         AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf**
                         AOSTCBFreeList' pf lf ct tcbls **
                         AOSRdyTblGrp rtbl rgrp **
                         AOSTime (Vint32 t) **
                         HECBList ecbls **
                         HTCBList tcbls **
                         HTime t **
                         HCurTCB ct **
                         AGVars **
                         [|RH_TCBList_ECBList_P ecbls tcbls ct|] ) ** invlth_isr' I 1%nat i%nat ** [| ie = false |] )\\//[|ie=true|])  ** p_local OSLInv ct (logic_val v :: nil) ** [| isflag v |].

Definition OSIntExitPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX ir ie si i lv, [|logicl=  (logic_isr ir) :: (logic_ie ie)
                                           :: (logic_is si) :: (logic_hid i) :: (logic_val lv) :: nil |]  ** ((Aisr (isrupd ir i%nat false)**
       Aie ie **
       Ais (i%nat :: si) **
       Acs nil ** <||END None||> **
       [| isr_is_prop (isrupd ir i%nat false) (i%nat :: si) |] **
       [| (i<=INUM)%nat |] **
       ((
       (EX (eventl osql qblkl : list vallist) (msgql : list EventData)
           (ectrl : list EventCtr) (ptbl : vallist) (p1 p2 : val) 
           (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
           (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map) 
           (tcbls : TcbMod.map) (t : int32) pf lf vhold,
        AOSEventFreeList eventl **
                         AOSQFreeList osql **
                         AOSQFreeBlk qblkl **
                         AECBList ectrl msgql ecbls tcbls **
                         AOSMapTbl **
                         AOSUnMapTbl **
                         AOSTCBPrioTbl ptbl rtbl tcbls vhold**
                         AOSIntNesting **
                         AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf **
                         AOSTCBFreeList' pf lf ct tcbls**
                         AOSRdyTblGrp rtbl rgrp **
                         AOSTime (Vint32 t) **
                         HECBList ecbls **
                         HTCBList tcbls **
                         HTime t **
                         HCurTCB ct **
                         AGVars **
                         [|RH_TCBList_ECBList_P ecbls tcbls ct|] ) ** invlth_isr' I 1%nat i%nat ** [| ie = false |]) \\// [|ie = true |])  **  p_local OSLInv ct ((logic_val lv)::nil) ** [|lv = Vint32 ($ 1) \/ si <> nil |]) \\// ( [|lv = Vint32 ($ 0) /\ si = nil |] ** Afalse)).
*)
(* ** ac: Check tcbdllflag. *)
(* ** ac: Check GoodFunAsrt_tcbdllflag. *)
Lemma GoodFunAsrt_sllfreeflag :
  forall l x,
    GoodFunAsrt (sllfreeflag x l).
  unfold sllfreeflag.
  induction l.

  intros.
  unfold sllsegfreeflag.
  simpl.
  auto.

  intros.
  simpl.
  intros.
  splits; auto.
Qed.
  
(* ** ac: Print Ltac GoodFunAsrt_solver. *)
Lemma GoodFunAsrt_IntInv: 
  GoodFunAsrt IntInv.
Proof.
  GoodFunAsrt_solver.
Qed.

Lemma GoodFunAsrt_TmrInv: 
  GoodFunAsrt TmrInv.
Proof.
  GoodFunAsrt_solver.
  eapply GoodFunAsrt_AOScoreheapl.
  eapply GoodFunAsrt_AOScoreheape.
  eapply GoodFunAsrt_AOScoreheapt.
Qed.

Lemma GoodFunAsrt_CoreCommuInv:
  forall v,
  GoodFunAsrt (CoreCommuInv v).
Proof.
  GoodFunAsrt_solver.
  eapply GoodFunAsrt_AOSIPCMem_aux.
  eapply GoodFunAsrt_Adynheap.
Qed.

Lemma GoodFunAsrt_APortStruct: forall x y,
  GoodFunAsrt (APortStruct x y).
Proof.
  unfold APortStruct. intros.
  apply GoodFunAsrt_Astruct'. 
Qed.

Lemma GoodFunAsrt_dmportp_sllseg_qport_msg: forall c x y z a b ,
  GoodFunAsrt (dmportp_sllseg_qport_msg x y z a b c).
Proof.
  induction c; destruct b;intros; GoodFunAsrt_solver.
Qed.

Lemma GoodFunAsrt_OtherPortPtrList: forall x y z,
  GoodFunAsrt (OtherPortPtrList x y z).
Proof.
  induction x; intros; destruct y; destruct z; intros; GoodFunAsrt_solver.
  apply GoodFunAsrt_APortStruct.
  apply GoodFunAsrt_dmportp_sllseg_qport_msg.
  apply GoodFunAsrt_dmportp_sllseg_qport_msg.
Qed.

Lemma GoodFunAsrt_dmportp_sllseg: forall z a x y  b,
  GoodFunAsrt (dmportp_sllseg x y z a b).
Proof. 
  induction z; intros; destruct a; try now simpl; GoodFunAsrt_solver. 
  cbn [dmportp_sllseg].
  destruct a0; GoodFunAsrt_solver.
  apply GoodFunAsrt_dmportp_sllseg_qport_msg.
  apply GoodFunAsrt_dmportp_sllseg_qport_msg.
  cbn [dmportp_sllseg]. 
  destruct a0; GoodFunAsrt_solver. 
  apply GoodFunAsrt_Astruct'.
  apply GoodFunAsrt_dmportp_sllseg_qport_msg.
  apply GoodFunAsrt_dmportp_sllseg_qport_msg.
Qed.

Lemma GoodFunAsrt_dmportp_sll: forall x y z w,
  GoodFunAsrt (dmportp_sll x y z w).
Proof.
  intros. unfold dmportp_sll. apply GoodFunAsrt_dmportp_sllseg.
Qed.

Lemma GoodFunAsrt_kportNode_P: forall x y,
  GoodFunAsrt (kportNode_P x y).
Proof.
  induction x; intros; destruct y; intros; GoodFunAsrt_solver.
  apply GoodFunAsrt_Astruct'.
Qed.

Lemma GoodFunAsrt_Channel_dstkport_get: forall  w x y z,
  GoodFunAsrt (Channel_dstkport_get x y z w).
Proof.
  induction w;  intros; destruct z; GoodFunAsrt_solver.
Qed.

Lemma GoodFunAsrt_ChannelNode: forall a b c,
  GoodFunAsrt (ChannelNode a b c).
Proof.
  induction a; intros; destruct b; destruct c; intros; GoodFunAsrt_solver.
  apply GoodFunAsrt_Channel_dstkport_get.
Qed.

Lemma GoodFunAsrt_kportf_sllseg: forall z x y  w a,
  GoodFunAsrt (kportf_sllseg x y z w a).
Proof.
  induction z; intros; GoodFunAsrt_solver.
Qed.

Lemma GoodFunAsrt_kportf_sll: forall x y z w,
  GoodFunAsrt (kportf_sll x y z w).
Proof.
  intros. unfold kportf_sll. apply GoodFunAsrt_kportf_sllseg.
Qed.

Lemma GoodFunAsrt_channelf_sllseg: forall z x y  w a,
  GoodFunAsrt (channelf_sllseg x y z w a).
Proof.
  induction z; intros; GoodFunAsrt_solver.
Qed.

Lemma GoodFunAsrt_channelf_sll: forall x y z w,
  GoodFunAsrt (channelf_sll x y z w).
Proof.
  intros. unfold channelf_sll. apply GoodFunAsrt_channelf_sllseg.
Qed.

Lemma  GoodFunAsrt_Partition1 :forall ecbls,
  GoodFunAsrt (PartitionInv_part1 ecbls).
Proof.
  unfold PartitionInv_part1.
  GoodFunAsrt_solver.
  apply GoodFunAsrt_dmportp_sll.
  apply GoodFunAsrt_kportNode_P.
  apply GoodFunAsrt_ChannelNode.
  apply GoodFunAsrt_kportf_sll.
  apply GoodFunAsrt_channelf_sll.
  apply GoodFunAsrt_OtherPortPtrList.
Qed.

Lemma  GoodFunAsrt_Partition2 :
  GoodFunAsrt (PartitionInv_part2).
Proof.
  unfold PartitionInv_part2.
  GoodFunAsrt_solver.
  eapply GoodFunAsrt_AucosConf.
  eapply GoodFunAsrt_AKsDomains'.
Qed.

Lemma GoodFunAsrt_PartionInv:
  forall ecbls, GoodFunAsrt (PartitionInv ecbls).
Proof.
  GoodFunAsrt_solver.
  apply GoodFunAsrt_dmportp_sll.
  apply GoodFunAsrt_kportNode_P.
  apply GoodFunAsrt_ChannelNode.
  apply GoodFunAsrt_kportf_sll.
  apply GoodFunAsrt_channelf_sll.
  apply GoodFunAsrt_OtherPortPtrList.
  eapply GoodFunAsrt_AucosConf.
  eapply GoodFunAsrt_AKsDomains'.
Qed.

Lemma GoodFunAsrt_CapabilityInv:
  forall acspace, 
  GoodFunAsrt (CapabilityInv acspace).
Proof.
  split. 
  eapply GoodFunAsrt_AOSCSpacePrioTbl.
  unfold AOSCSpaceCapParent, CSpaceGVars.
  GoodFunAsrt_solver.
  (* eapply GoodFunAsrt_ACSpaceAarrayTptr. *)
Qed.

Local Ltac GoodFunAsrt_solver ::=
  repeat
   (split; try apply GoodFunAsrt_Aarray;
     try apply GoodFunAsrt_Astruct;
     try apply GoodFunAsrt_AEventData;
     try apply GoodFunAsrt_evsllseg;
     try apply GoodFunAsrt_tcbdllseg; try apply GoodFunAsrt_dllseg;
     try apply GoodFunAsrt_ecbf_sll; try apply GoodFunAsrt_sll;
     try apply GoodFunAsrt_qblkf_sll;
     try apply GoodFunAsrt_invlth_isr';
     try apply GoodFunAsrt_tcbdllflag;
     try apply GoodFunAsrt_sllfreeflag;
     try apply GoodFunAsrt_Aarray_new; 
     try apply GoodFunAsrt_pos_sllseg; 
     try apply GoodFunAsrt_err_sllseg; 
     try apply GoodFunAsrt_AEvAtomHeap; 
     try apply GoodFunAsrt_AEvStructHeap; 
     try apply GoodFunAsrt_AEvArrayHeap; 
     try apply GoodFunAsrt_llsegevaux;
     try simple apply GoodFunAsrt_AOSPortAttrTbl';
     try apply GoodFunAsrt_AucosConf;
     try apply GoodFunAsrt_AKsDomains';
     try apply GoodFunAsrt_AOScoreheape;
     try apply GoodFunAsrt_AOScoreheapl;
     try apply GoodFunAsrt_AOScoreheapt;
     try apply GoodFunAsrt_AOSIPCMem_aux;
     try apply GoodFunAsrt_Adynheap;
     try (simple apply GoodFunAsrt_PartionInv);
     try (simple apply GoodFunAsrt_CapabilityInv);
     auto).

(*
Theorem OSIntExitPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSIntExitPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Theorem OSIntExitPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSIntExitPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OSIntExitPre : fpre :=
  fun vl ll ct => mkfunasrt (OSIntExitPreGood vl ll ct).

Definition OSIntExitPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSIntExitPostGood vl v ll ct).
*)

(* OS_PrioChange *)
Definition OS_PrioChangePre' (vl:vallist) (logicl:list logicvar) (ct:tid):=
  EX ptcb prio pip next pre eptr msg dly stat p x y bitx bity rtbl rgrp ptbl vhold s,
  <||s||> ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr **
     [| vl = (Vptr ptcb)::(Vint32 prio)::(Vint32 pip)::nil|] **
     [|logicl = (logic_val next)::(logic_val pre)::(logic_val eptr) :: (logic_val msg) :: (logic_val dly) :: (logic_val stat) :: (logic_val p) :: (logic_val x) :: (logic_val y) :: (logic_val bitx) :: (logic_val bity) :: (logic_lv rtbl) :: (logic_val rgrp) :: (logic_lv ptbl) :: (logic_val (Vptr vhold)) :: (logic_code s) :: nil|] **
     [| struct_type_vallist_match OS_TCB (next::pre::eptr::msg::dly::stat::p::x::y::bitx::bity::nil) |] **
     [| 0 <= Int.unsigned prio < 64 |] **
     [| 0 <= Int.unsigned pip < 64 |] **
     [| RL_TCBblk_P (next::pre::eptr::msg::dly::stat::p::x::y::bitx::bity::nil) |] **
     Astruct ptcb OS_TCB
     (next::pre::eptr::msg::dly::stat::p::x::y::bitx::bity::nil) **
     AOSRdyTblGrp rtbl rgrp **
     GAarray OSTCBPrioTbl (Tarray (Tptr OS_TCB) 64) ptbl  **
     G&OSPlaceHolder @ (Tint8) == vhold **
     AOSMapTbl.

Definition OS_PrioChangePost' (vl:vallist) (v:option val) (logicl:list logicvar) (ct:tid):=Aemp.
   (*
  EX ptcb prio pip next pre eptr msg dly stat p x y bitx bity rtbl rgrp ptbl vhold s x' y' bitx' bity' rtbl' rgrp' ptbl' x12 x11 x8,
  <||s||> ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr **
     [| vl = (Vptr ptcb)::(Vint32 prio)::(Vint32 pip)::nil|] **
     [|logicl = (logic_val next)::(logic_val pre)::(logic_val eptr) :: (logic_val msg) :: (logic_val dly) :: (logic_val stat) :: (logic_val p) :: (logic_val x) :: (logic_val y) :: (logic_val bitx) :: (logic_val bity) :: (logic_lv rtbl) :: (logic_val rgrp) :: (logic_lv ptbl) :: (logic_val (Vptr vhold)) :: (logic_code s) :: nil|] **
     [| struct_type_vallist_match OS_TCB (next::pre::eptr::msg::dly::stat::p::x::y::bitx::bity::nil) |] **
     [| 0 <= Int.unsigned prio < 64 |] **
     [| 0 <= Int.unsigned pip < 64 |] **
     [| x' = (Int.and prio ($7)) |] **
     [| y' = (Int.shru prio ($3)) |] **
     [| bity' = nth_val' (Z.to_nat (Int.unsigned y')) OSMapVallist |] **
     [| bitx' = nth_val' (Z.to_nat (Int.unsigned x')) OSMapVallist |] **
     [| nth_val' (Z.to_nat (Int.unsigned (pip>>ᵢ$ 3))) rtbl = Vint32 x12 |] **
     [| nth_val' (Z.to_nat (Int.unsigned (prio>>ᵢ$ 3))) rtbl = Vint32 x8 |] **
     [| nth_val' (Z.to_nat (Int.unsigned (prio&$ 7))) rtbl = Vint32 x11 |] **
     [| rtbl' =  (update_nth_val
          (Z.to_nat (Int.unsigned (prio >>ᵢ $ 3)))
          (update_nth_val (Z.to_nat (Int.unsigned pip)) rtbl
             (val_inj (and (Vint32 x12) (Vint32 (Int.not ($ 1<<(pip&$ 7)))))))
          (val_inj
             (or
                (nth_val'
                   (Z.to_nat
                      (Int.unsigned ((prio)>>ᵢ$ 3)))
                   (update_nth_val (Z.to_nat (Int.unsigned (pip>>ᵢ$ 3))) rtbl
                      (val_inj
                         (and (Vint32 x12) (Vint32 (Int.not ($ 1<<(pip&$ 7))))))))
                (Vint32 x11)))) |] **
(*     [| rgrp' = rgrp |] ** *)
     [| ptbl' = (update_nth_val (Z.to_nat (Int.unsigned pip))
          (update_nth_val
             (Z.to_nat (Int.unsigned prio)) ptbl
             (Vptr ptcb)) (Vptr vhold)) |] **
     [| RL_TCBblk_P (next::pre::eptr::msg::dly::stat::(Vint32 prio)::(Vint32 x')::(Vint32 y')::bitx'::bity'::nil) |] **
     Astruct ptcb OS_TCB
     (next::pre::eptr::msg::dly::stat::(Vint32 prio)::(Vint32 x')::(Vint32 y')::bitx'::bity'::nil) **
     AOSRdyTblGrp rtbl' rgrp' **
     GAarray OSTCBPrioTbl (Tarray (Tptr OS_TCB) 64) ptbl'  **
     G&OSPlaceHolder @ (Tint8) == vhold **
     AOSMapTbl.
*)

Theorem OS_PrioChangePreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_PrioChangePre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Theorem OS_PrioChangePostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_PrioChangePost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_PrioChangePre : fpre :=
  fun vl ll ct => mkfunasrt (OS_PrioChangePreGood vl ll ct).

Definition OS_PrioChangePost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_PrioChangePostGood vl v ll ct).

(* Time Tick *)

Open Scope code_scope.

(* Time Tick *)
Definition OSTimeTickPre' (vl:vallist) (logicl:list logicvar) ct:=
   EX isrr si er v'5 v'7, EX v'8 v'9 v'10 v'11 v'14 v'17 v'18 tcbls tcbls1 tcbls2 v'3 v'2 v'12 v'15 s ctx v,  
   [|logicl = (logic_isr isrr) :: (logic_is si) :: (logic_ier er) :: 
     logic_val (Vint32 v'14) :: (logic_val (Vptr v'5))  ::  (logic_val (Vptr v'5)) :: (logic_llv v'7) ::
     (logic_lv v'8) :: (logic_llv v'9) :: (logic_lv v'10) :: (logic_val v'11) ::
     (logic_val v'17) :: (logic_val v'18) :: (logic_abstcb tcbls) ::
     (logic_abstcb tcbls1) :: (logic_abstcb tcbls2) :: (logic_leventc v'3) :: (logic_leventd v'2) ::
     (logic_absecb v'12):: logic_code s ::logic_val (Vptr ctx):: logic_val v:: nil|] **
     Aisr (isrupd isrr 4%nat false) **
     Aier (ierupd er 4%nat true) **
     Aie false **
     Ais (4%nat :: si) **
     Acs nil **
     <||s||> **
     GV OSTCBList @ OS_TCB ∗ |-> (Vptr v'5) **
     tcbdllseg (Vptr v'5) Vnull v'17 (Vptr ctx) v'7 **
     GV OSTCBCur @ OS_TCB ∗ |-r-> (Vptr ct) **
     tcbdllseg (Vptr ctx) v'17 v'18 Vnull (v'8 :: v'9) **
     [|TcbMod.join tcbls1 tcbls2 tcbls|] **
     [|TCBList_P (Vptr v'5) v'7 v'10 tcbls1|] ** [|TCBList_P (Vptr ctx) (v'8::v'9) v'10 tcbls2|] ** 
     AOSRdyTblGrp v'10 v'11 **
     GV OSTime @ Int32u |-> (Vint32 v'14)**
     AECBList v'3 v'2 v'12 tcbls **
     [| RH_TCBList_ECBList_P v'12 tcbls v'15 |]   ** p_local OSLInv ct (logic_val v :: nil) ** [| isflag v |].

Definition tmdly_sub_1 (vl:vallist):=
  match nth_val 4%nat vl with
    | Some (Vint32 v) => Some (update_nth_val 5%nat vl (Vint32 (Int.sub v Int.one)))
    | _ => None
  end.

Definition set_rdy_grp tcbbity rgrp := bop_eval rgrp tcbbity Tint8 Tint8 obitor.

Definition nth_val_vallist tcby rtbl:=
  match tcby with
    | Vint32 v => nth_val (Z.to_nat (Int.unsigned v)) rtbl
    | _ => None
  end.

Definition set_rdy_tbl tcbbitx tcby rtbl:=
  match tcby with
    | Vint32 vi => 
      match nth_val (Z.to_nat (Int.unsigned vi)) rtbl with
        | Some v => match bop_eval v tcbbitx Tint8 Tint8 obitor with
                      | Some v' => Some (update_nth_val (Z.to_nat (Int.unsigned vi)) rtbl v')
                      | None => None
                    end
        | None => None
      end
    | _ => None
  end. 
    
Definition add_option_first (vl:vallist) (tri: option ((list vallist)*vallist*val*(list EventCtr))):=
  match tri with
    | Some (a,b,c,d) => Some (vl::a,b,c,d)
    | _ => None
  end.
  
Definition set_rdy (vl:vallist):=
  update_nth_val 3%nat (update_nth_val 6%nat vl (Vint32 (Int.repr OS_STAT_RDY))) Vnull.

Definition beq_addrval := 
fun n m : addrval =>
  let (b, i) := n in let (b', i') := m in beq_pos b b' && Int.eq i i'.

Definition rdy_ectr (vl:vallist) (ectr:EventCtr) :option EventCtr:=
  match ectr with
    | (v1::Vint32 v2::v3::v4::v5::v6::v7:: v8 :: nil,etbl,petbl) =>
      match V_OSTCBY vl, (V_OSTCBBitX vl), (V_OSTCBBitY vl) with
        | Some (Vint32 y),Some (Vint32 bitx),Some (Vint32 bity) =>
          match nth_val' (Z.to_nat (Int.unsigned y)) etbl with
            | Vint32 xx =>
              match Int.eq (xx&ᵢInt.not bitx) ($ 0) with
                | true => Some (v1::Vint32 (v2&ᵢInt.not bity)::v3::v4::v5::v6:: v7 :: v8 :: nil,
                                update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (xx&ᵢInt.not bitx)),petbl)
                | false => Some (v1::Vint32 v2::v3::v4::v5::v6::v7 :: v8 :: nil,
                                update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (xx&ᵢInt.not bitx)),petbl)
              end
            | _ => None
          end
        | _,_,_ => None
      end
    | _ => None
  end.

Fixpoint tick_rdy_ectr' (e:addrval) (vl:vallist) (head:val) (ectrl:list EventCtr) :=
  match head with
    | (Vptr e') =>
      match ectrl with
        |(osevent, etbl, petbl)::vll =>
         match beq_addrval e e' with
           | true => match (rdy_ectr vl (osevent, etbl, petbl)) with
                       | Some x => Some (x :: vll)
                       | None => None
                     end
           | false => match V_OSEventListPtr osevent with
                        | Some vn => match (tick_rdy_ectr' e vl vn vll) with
                                       | Some x => Some ((osevent, etbl, petbl)::x)
                                       | None => None
                                     end
                        | _ => None
                      end
         end
        | _ => Some ectrl
      end
    | Vnull => Some ectrl
    | _=> None
  end.

Definition tick_rdy_ectr (vl:vallist) (head:val) (ectrl:list EventCtr) :=
  match nth_val 2%nat vl with
    | Some (Vptr eid) => tick_rdy_ectr' eid vl head ectrl
    | Some (Vnull) => Some ectrl
    | _ => None
  end.

Definition os_stat_not_suspend (stat : int32) : bool :=
  if Int.eq (Int.and stat (Int.repr OS_STAT_ILLEGAL)) (Int.repr OS_STAT_RDY) then 
     (Int.eq (Int.and stat (Int.repr OS_STAT_SUSPEND)) (Int.repr OS_STAT_RDY)) else false.

Fixpoint tcbls_rtbl_timetci_update (vll:list vallist) (rtbl:vallist) (rgrp:val) (head:val) (ectrl:list EventCtr) :=
  match vll with
    | nil => Some ((nil:list vallist),rtbl,rgrp,ectrl)
    | vl::vll' =>
      match vl with
        | (vnext :: vprev ::
           eid :: msg :: Vint32 vdly ::
           (Vint32 stat) :: (Vint32 prio) ::
           (Vint32 vx) :: (Vint32 vy) ::
           (Vint32 vbitx) :: (Vint32 vbity) :: nil) =>
          match Int.eq vdly Int.zero with
            | true => add_option_first vl (tcbls_rtbl_timetci_update vll' rtbl rgrp head ectrl)
            | false =>
              match Int.eq (Int.sub vdly Int.one) Int.zero with
                | true =>
                  match os_stat_not_suspend stat with 
                  | true =>
                      match set_rdy_grp (Vint32 vbity) rgrp with
                        | Some (Vint32 rgrp') =>
                          match set_rdy_tbl (Vint32 vbitx) (Vint32 vy) rtbl with
                            | Some rtbl' => add_option_first
                                  (vnext :: vprev ::
                                  eid :: msg :: Vint32 (Int.sub vdly Int.one) ::
                                  (Vint32 stat) :: (Vint32 prio) ::
                                  (Vint32 vx) :: (Vint32 vy) ::
                                  (Vint32 vbitx) :: (Vint32 vbity) :: nil)
                                  (tcbls_rtbl_timetci_update vll' rtbl' (Vint32 rgrp') head ectrl)
                            | _ => None
                          end
                        | _ => None
                      end
                  | false => add_option_first
                             (vnext :: vprev ::
                                    eid :: msg :: Vint32 (Int.one) ::
                                    (Vint32 stat) :: (Vint32 prio) ::
                                    (Vint32 vx) :: (Vint32 vy) ::
                                    (Vint32 vbitx) :: (Vint32 vbity) :: nil)
                             (tcbls_rtbl_timetci_update vll' rtbl rgrp head ectrl)
                  end 
                | false => add_option_first
                             (vnext :: vprev ::
                                    eid :: msg :: Vint32 (Int.sub vdly Int.one) ::
                                    (Vint32 stat) :: (Vint32 prio) ::
                                    (Vint32 vx) :: (Vint32 vy) ::
                                    (Vint32 vbitx) :: (Vint32 vbity) :: nil)
                             (tcbls_rtbl_timetci_update vll' rtbl rgrp head ectrl)
              end
          end
        | _ => None
      end
  end.

Inductive  tickchange_l: vallist -> vallist -> val -> val -> list EventCtr -> vallist -> vallist -> val  -> list EventCtr -> Prop:=
| rdy_change_l: forall vnext vprev eid msg vdly stat prio vx vy vbitx vbity l rtbl rgrp head ectr,
                  l = (vnext :: vprev ::
                             eid :: msg :: Vint32 vdly ::
                             (Vint32 stat) :: (Vint32 prio) ::
                             (Vint32 vx) :: (Vint32 vy) ::
                             (Vint32 vbitx) :: (Vint32 vbity) :: nil) ->
                  Int.eq vdly Int.zero = true ->
                  tickchange_l l rtbl rgrp head ectr l rtbl rgrp ectr
(* 'wait_change' and 'waite_change' *)
| wait_change_l: forall vnext vprev eid msg vdly stat prio vx vy vbitx vbity l l' rtbl rgrp head ectr,
                  l = (vnext :: vprev ::
                             eid :: msg :: Vint32 vdly ::
                             (Vint32 stat) :: (Vint32 prio) ::
                             (Vint32 vx) :: (Vint32 vy) ::
                             (Vint32 vbitx) :: (Vint32 vbity) :: nil) ->
                  Int.eq vdly Int.zero = false ->
                  Int.eq (Int.sub vdly Int.one) Int.zero = false ->
                  l' =  (vnext :: vprev ::
                               eid:: msg :: Vint32 (Int.sub vdly Int.one) ::
                               (Vint32 stat) :: (Vint32 prio) ::
                               (Vint32 vx) :: (Vint32 vy) ::
                               (Vint32 vbitx) :: (Vint32 vbity) :: nil)->
                  tickchange_l l rtbl rgrp head ectr l' rtbl rgrp ectr
| wait_rdy_change_l: forall vnext vprev eid msg vdly stat prio vx vy vbitx vbity
                            l l' rtbl rgrp head ectr rgrp' rtbl',
                       l = (vnext :: vprev ::
                                  eid :: msg :: Vint32 vdly ::
                                  (Vint32 stat) :: (Vint32 prio) ::
                                  (Vint32 vx) :: (Vint32 vy) ::
                                  (Vint32 vbitx) :: (Vint32 vbity) :: nil) ->
                  Int.eq vdly Int.zero = false ->
                  Int.eq (Int.sub vdly Int.one) Int.zero = true ->
                  os_stat_not_suspend stat = true ->
                  l' =  (vnext :: vprev ::
                               eid:: msg :: Vint32 (Int.sub vdly Int.one) ::
                               (Vint32 stat) :: (Vint32 prio) ::
                               (Vint32 vx) :: (Vint32 vy) ::
                               (Vint32 vbitx) :: (Vint32 vbity) :: nil) ->
                  set_rdy_grp (Vint32 vbity) rgrp = Some rgrp' ->
                  set_rdy_tbl (Vint32 vbitx) (Vint32 vy) rtbl = Some rtbl' ->
                  tickchange_l l rtbl rgrp head ectr l' rtbl' rgrp' ectr
| suspend_chang_l : forall vnext vprev eid msg vdly stat prio vx vy vbitx vbity l l' rtbl rgrp head ectr,
                  l = (vnext :: vprev ::
                             eid :: msg :: Vint32 vdly ::
                             (Vint32 stat) :: (Vint32 prio) ::
                             (Vint32 vx) :: (Vint32 vy) ::
                             (Vint32 vbitx) :: (Vint32 vbity) :: nil) ->
                  Int.eq vdly Int.zero = false ->
                  Int.eq (Int.sub vdly Int.one) Int.zero = true ->
                  os_stat_not_suspend stat = false ->
                  l' =  (vnext :: vprev ::
                               eid:: msg :: Vint32 (Int.one) ::
                               (Vint32 stat) :: (Vint32 prio) ::
                               (Vint32 vx) :: (Vint32 vy) ::
                               (Vint32 vbitx) :: (Vint32 vbity) :: nil) ->
                  tickchange_l l rtbl rgrp head ectr l' rtbl rgrp ectr. (* remain ectr *)

Inductive tickstep_l: list vallist -> vallist -> val -> val -> list EventCtr -> list vallist -> vallist -> val  -> list EventCtr -> Prop :=
| emp_update: forall rtbl rgrp head ectr,
                tickstep_l nil rtbl rgrp head ectr nil rtbl rgrp ectr
| tl_update: forall l ll rtbl rgrp head ectr l' ll' rtbl' rgrp' ectr' rtbl'' rgrp'' ectr'',
               tickchange_l l rtbl rgrp head ectr l' rtbl' rgrp' ectr' ->
               tickstep_l ll rtbl' rgrp' head ectr' ll' rtbl'' rgrp'' ectr'' ->
               tickstep_l (l::ll) rtbl rgrp head ectr (l'::ll') rtbl'' rgrp'' ectr''.
             
Definition OSTimeTickPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:= 
EX isrr si er v'5  v'7, EX v'8 v'9 v'10 v'11 v'14 v'17 v'18  rtbl' rgrp' v'15 tcbls tcbls1 tcbls2 i v'20 v'3 v'2 ectrl' v'12 s ctx v,  
[|logicl = (logic_isr isrr) :: (logic_is si) :: (logic_ier er) :: (logic_val (Vint32 v'14)) ::
            (logic_val (Vptr v'5)) ::   (logic_val (Vptr v'5)) ::
            (logic_llv v'7) :: (logic_lv v'8) :: (logic_llv v'9) :: (logic_lv v'10) ::
            (logic_val v'11) :: (logic_val v'17) :: (logic_val v'18) :: (logic_abstcb tcbls) ::
            (logic_abstcb tcbls1) :: (logic_abstcb tcbls2) ::  (logic_leventc v'3) :: (logic_leventd v'2) ::
            (logic_absecb v'12)::logic_code s ::logic_val (Vptr ctx)::logic_val v:: nil|] **
  [| array_type_vallist_match Int8u v'10|] **
  [| length v'10 = ∘OS_RDY_TBL_SIZE |] **
  [| v'11 = Vint32 i|] ** [| Int.unsigned i <= 255 |] **
  [| RL_Tbl_Grp_P v'10 v'11 |] **
  [| v'7 = nil /\ (Vptr ctx) = Vptr v'5 \/
                  (exists vl, v'7 <> nil /\ last v'7 nil = vl /\ nth_val 0 vl = Some (Vptr ctx)) |] **
  Aisr (isrupd isrr 4%nat false) **
  Aier (ierupd er 4%nat true) **
  Aie false **
  Ais (4%nat :: si) **
  Acs nil **
  <||s||> **
  GV OSTCBList @ OS_TCB ∗ |-> (Vptr v'5) **
  GV OSEventList @ OS_EVENT ∗ |-> v'20 **
  evsllseg v'20 Vnull ectrl' v'2 **
  tcbdllseg (Vptr v'5) Vnull v'18 Vnull v'15 **
  [|TcbMod.join tcbls1 tcbls2 tcbls|] **
  [|TCBList_P (Vptr v'5) v'7 v'10 tcbls1|] ** [|TCBList_P (Vptr ctx) (v'8::v'9) v'10 tcbls2|] **
  [|ECBList_P v'20 Vnull v'3 v'2 v'12 tcbls|] **
  GV OSTCBCur @ OS_TCB ∗ |-r-> (Vptr ct) **
  GAarray OSRdyTbl (Tarray Int8u ∘OS_RDY_TBL_SIZE) rtbl' **
  GV OSRdyGrp @ Int8u |-> rgrp' **
  GV OSTime @ Int32u |-> Vint32 (Int.add v'14 Int.one) **
  [| tcbls_rtbl_timetci_update (v'7++(v'8::v'9)) v'10 v'11 v'20 v'3= Some (v'15,rtbl',rgrp',ectrl')|] **
  [| prio_in_tbl ($ OS_IDLE_PRIO) rtbl'|]  ** p_local OSLInv ct (logic_val v :: nil) ** [| isflag v |].

Theorem OSTimeTickPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSTimeTickPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Theorem OSTimeTickPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSTimeTickPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

(*here can compile*)

Definition OSTimeTickPre : fpre :=
  fun vl ll ct => mkfunasrt (OSTimeTickPreGood vl ll ct).

Definition OSTimeTickPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSTimeTickPostGood vl v ll ct).

(*OS_TCBInit*)

Definition OS_TCBInitPre' (vl:vallist) (logicl:list logicvar) (ct:tid):=
  EX (ptfree:val) (lfree:list vallist) (rtbl:vallist) (ptbl:vallist) (rgrp:val) (p1 tail1 tail2:val) (l1 l2:list vallist) (prio: priority) (vhold: addrval) s vholdx,
      Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** (EX (er:ier), Aier er) ** A_isr_is_prop **
      AOSTCBFreeList ptfree lfree **
      AOSMapTbl **
      <||s||> **
      [|nth_val 0 vl = Some (Vint32 prio) /\ Int.ltu ($ OS_LOWEST_PRIO) prio = false |] **
      (*prio table*)
      GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) ptbl **
      G& OSPlaceHolder @ Int8u == vhold **
      PV vhold @ Int8u |-> vholdx **
      (* GV OSPlaceHolder @ Tint8 |-> vholdx ** *)
      [|array_type_vallist_match OS_TCB ∗ ptbl /\ length ptbl = 64%nat|] **
      [|RL_RTbl_PrioTbl_P rtbl ptbl vhold|] **
      (*tcb list*)
      GV OSTCBList @ OS_TCB ∗ |-> p1 **
      tcbdllseg p1 Vnull tail1 (Vptr ct) l1 **
      GV OSTCBCur @ OS_TCB ∗ |-r-> (Vptr ct) **
      tcbdllseg (Vptr ct) tail1 tail2 Vnull l2 **
      [|p1 <> Vnull|] **
      AOSRdyTblGrp rtbl rgrp **
      (*logic vars*)
      [|logicl = logic_val (Vptr vhold)::logic_val p1 ::
                 logic_val tail1 :: logic_val tail2 :: logic_llv l1 :: logic_llv l2 ::
                 logic_lv ptbl :: logic_lv rtbl :: logic_val rgrp :: logic_code s :: nil|] ** p_local OSLInv ct init_lg.

Definition new_tcb_node_p (prio:priority) (prev:val) (next:val) (l:vallist) : Prop :=
    struct_type_vallist_match OS_TCB_flag l /\
    V_OSTCBPrio l = Some (Vint32 prio) /\
    V_OSTCBStat l = Some (Vint32 ($ OS_STAT_RDY)) /\
    V_OSTCBDly l = Some (Vint32 ($ 0)) /\
    V_OSTCBY l = Some (Vint32 (Int.shru prio ($ 3))) /\
    V_OSTCBBitY l = Some (nth_val' (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) OSMapVallist) /\
    V_OSTCBX l = Some (Vint32 (Int.and prio ($ 7))) /\
    V_OSTCBBitX l = Some (nth_val' (Z.to_nat (Int.unsigned (Int.and prio ($ 7)))) OSMapVallist) /\
    V_OSTCBEventPtr l = Some Vnull /\
    V_OSTCBMsg l = Some Vnull /\
    V_OSTCBPrev l = Some prev /\
    V_OSTCBNext l = Some next.

Fixpoint set_nth {A:Type} (vl: list A) (n:nat) (v:A) : option (list A) :=
  match vl with
    | nil => None
    | h::t => match n with
                | O => Some (v::t)
                | S x => match set_nth t x v with
                           | Some r => Some (h::r)
                           | None => None
                         end
              end
  end.

Definition tcbls_change_prev_ptr (vl : list vallist) (ptr: val) : option (list vallist) :=
  match vl with
    | nil => None
    | h :: t => Some (update_nth_val 1%nat h ptr :: t)
  end.

Definition OS_TCBInitPost' (vl:vallist) (r:option val) (logicl:list logicvar) ct:=  
  EX (er:ier),
  Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** (EX (er:ier), Aier er) ** A_isr_is_prop **
  (( [| r = Some (Vint32 ($ OS_NO_MORE_TCB)) |] **
      EX (ptfree:val) (lfree:list vallist) (rtbl:vallist) (ptbl:vallist) (rgrp:val) (p1 tail1 tail2:val) (l1 l2:list vallist) (prio:priority) (vhold:addrval) s vholdx,
      AOSTCBFreeList ptfree lfree ** AOSMapTbl **
      (*prio table*)
      GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) ptbl **
      G& OSPlaceHolder @ Int8u == vhold **
      PV vhold @ Int8u |-> vholdx **
(*      GV OSPlaceHolder @ Tint8 |-> vholdx ** *)
      <||s||> **
      [|array_type_vallist_match OS_TCB ∗ ptbl /\ length ptbl = 64%nat|] **
      [|RL_RTbl_PrioTbl_P rtbl ptbl vhold|] **
      (*tcb list*)
      GV OSTCBList @ OS_TCB ∗ |-> p1 **
      tcbdllseg p1 Vnull tail1 (Vptr ct) l1 **
      GV OSTCBCur @ OS_TCB ∗ |-r-> (Vptr ct) **
      tcbdllseg (Vptr ct) tail1 tail2 Vnull l2 **
      [|p1 <> Vnull|] **
      AOSRdyTblGrp rtbl rgrp **
      (*logic vars*)
      [|logicl = logic_val (Vptr vhold) :: logic_val p1 ::
                 logic_val tail1 :: logic_val tail2 :: logic_llv l1 :: logic_llv l2 ::
                 logic_lv ptbl :: logic_lv rtbl :: logic_val rgrp :: logic_code s::nil|] **
      [| ptfree = Vnull |] ** p_local OSLInv ct init_lg
    ) 
    \\//
    ( [|r = Some (Vint32 ($ OS_NO_ERR))|] **
      EX (ptfree:val) (lfree:list vallist) (rtbl rtbl':vallist) (ptbl ptbl':vallist) (p1 tail1 tail1' tail2:val) anew (l1 l1' l2 l2':list vallist) (lnew:vallist) (rgrp rgrp':val) (prio:priority) (vhold:addrval) s vholdx,
      AOSTCBFreeList ptfree lfree ** AOSMapTbl **
      (*prio table*)
      GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) ptbl' **
      G& OSPlaceHolder @ Int8u == vhold **
      PV vhold @ Int8u |-> vholdx **
(*      GV OSPlaceHolder @ Tint8 |-> vholdx ** *)
      <||s||> **
      [|array_type_vallist_match OS_TCB ∗ ptbl' /\ length ptbl' = 64%nat|] **
      [|RL_RTbl_PrioTbl_P rtbl' ptbl' vhold|] **
      (*new tcb head*)
      [|nth_val 0 vl = Some (Vint32 prio)|] **
      GV OSTCBList @ OS_TCB ∗ |-> (Vptr anew) **
      node (Vptr anew) lnew OS_TCB_flag ** PV get_off_addr anew flag_off @ Int8u |-> (V$ 1) **
      PV get_off_addr anew evloc_off @ Int8u |-> (V$ 1) **
      PV get_off_addr anew muxptr_off @ (Tptr OS_EVENT) |-> Vnull **
      PV get_off_addr anew semptr_off @ (Tptr OS_EVENT) |-> Vnull **
      PV get_off_addr anew qptr_off @ (Tptr OS_EVENT) |-> Vnull **[| new_tcb_node_p prio Vnull p1 lnew|] **
      (*old tcbdllseg*)
      tcbdllseg p1 (Vptr anew) tail1' (Vptr ct) l1' **
      GV OSTCBCur @ OS_TCB ∗ |-r-> (Vptr ct) **
      tcbdllseg (Vptr ct) tail1' tail2 Vnull l2' **
      AOSRdyTblGrp rtbl' rgrp' **
      (*logic vars*)
      [| logicl = logic_val (Vptr vhold) :: logic_val p1 ::
                  logic_val tail1 :: logic_val tail2 :: logic_llv l1 :: logic_llv l2 ::
                  logic_lv ptbl :: logic_lv rtbl :: logic_val rgrp ::logic_code s :: nil |] **
      [| ptbl' = update_nth_val (Z.to_nat (Int.unsigned prio)) ptbl (Vptr anew) |] **
      [| rtbl' = update_nth_val
           (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
           (val_inj (or (nth_val' (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl) (nth_val' (Z.to_nat (Int.unsigned (Int.and prio ($ 7)))) OSMapVallist))) |] **
      [| or rgrp (nth_val' (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) OSMapVallist) = Some rgrp' |] **
      [| (l1 = nil /\ l1' = l1 /\ tcbls_change_prev_ptr l2 (Vptr anew) = Some l2') \/
         (l1 <> nil /\ tcbls_change_prev_ptr l1 (Vptr anew) = Some l1' /\ l2 = l2' /\ tail1 = tail1') |] ** p_local OSLInv ct init_lg
    )).

Theorem OS_TCBInitPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_TCBInitPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Theorem OS_TCBInitPostGood (vl:vallist) (v:option val) ll ct :
  GoodFunAsrt (OS_TCBInitPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_TCBInitPre : fpre :=
  fun vl ll ct=> mkfunasrt (OS_TCBInitPreGood vl ll ct).

Definition OS_TCBInitPost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_TCBInitPostGood vl v ll ct).

(* OS_isSomeMutexOwner *)
Definition OS_IsSomeMutexOwnerPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX msgql ectrl ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp mqls tcbls tcbptr vhold s ptls er,
    Aie false  ** Ais nil ** Acs (true::nil) ** Aisr empisr ** Aier er **
    AECBList ectrl msgql mqls tcbls ** (* msgqlist *)
    AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls ** (* tcblist *)
    tcbdllflag p1 (tcbl1 ++ tcbcur :: tcbl2) **
    AOSRdyTblGrp rtbl rgrp ** AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold** (* rdy table & prio table *)
    HECBList mqls ** HTCBList tcbls ** HCurTCB ct  (* high level *) **
     A_isr_is_prop ** <||s||> **
    [| RH_TCBList_ECBList_P mqls tcbls ct|] **
    [| nth_val 0 vl = Some (Vptr tcbptr)|] **
    [| RH_CurTCB ct tcbls |] **
    [| logicl = logic_leventd msgql :: logic_leventc ectrl :: logic_lv ptbl :: logic_val p1 :: logic_val p2 :: logic_llv tcbl1 :: logic_lv tcbcur :: logic_llv tcbl2 :: logic_lv rtbl :: logic_val rgrp :: logic_absecb mqls :: logic_abstcb tcbls :: logic_val (Vptr tcbptr) :: logic_val (Vptr vhold) :: logic_code s :: nil |] ** 
    p_local OSLInv  ct init_lg.

Theorem OS_IsSomeMutexOwnerPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OS_IsSomeMutexOwnerPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_IsSomeMutexOwnerPre: fpre :=
  fun vl ll ct=> mkfunasrt (OS_IsSomeMutexOwnerPreGood vl ll ct).

(* post *)
Definition is_some_mutex_owner ptr ecbmap :=
  exists eid pr opr wls, (EcbMod.get ecbmap eid = Some (absmutexsem pr (Some (ptr, opr)), wls)).
(* Definition at_most_once_in_ecbmap ptr ecbmap :=
 *         forall x y wl x' y' wl',
 *           EcbMod.get ecbmap x' = Some (y', wl') ->
 *           EcbMod.get ecbmap x = Some (y, wl) ->
 *           In ptr wl ->
 *           In ptr wl' ->
 *           x' = x . *)

(* Definition task_delete_pure_hyp ptr ecbmap :=
 *   ~ is_some_mutex_owner ptr ecbmap (* /\ at_most_once_in_ecbmap ptr ecbmap *). *)

Definition OS_IsSomeMutexOwnerPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
EX msgql ectrl ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp mqls tcbls tcbptr vhold s ptls er,
    Aie false  ** Ais nil ** Acs (true::nil) ** Aisr empisr ** Aier er **
    AECBList ectrl msgql mqls tcbls ** (* msgqlist *)
    AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls ** (* tcblist *)
    tcbdllflag p1 (tcbl1 ++ tcbcur :: tcbl2) **
    AOSRdyTblGrp rtbl rgrp ** AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold** (* rdy table & prio table *)
    HECBList mqls ** HTCBList tcbls ** HCurTCB ct  (* high level *) **
     A_isr_is_prop ** <||s||> **
    [| RH_TCBList_ECBList_P mqls tcbls ct|] **
    [| nth_val 0 vl = Some (Vptr tcbptr)|] **
    [| RH_CurTCB ct tcbls |] **
    [| logicl = logic_leventd msgql :: logic_leventc ectrl :: logic_lv ptbl :: logic_val p1 :: logic_val p2 :: logic_llv tcbl1 :: logic_lv tcbcur :: logic_llv tcbl2 :: logic_lv rtbl :: logic_val rgrp :: logic_absecb mqls :: logic_abstcb tcbls :: logic_val (Vptr tcbptr) :: logic_val (Vptr vhold) :: logic_code s :: nil |] ** 
    p_local OSLInv  ct init_lg **
    [| (v = Some (V$0) /\ ~ is_some_mutex_owner tcbptr mqls) \/
       (v = Some (V$1) /\ is_some_mutex_owner tcbptr mqls) |]
.

Theorem OS_IsSomeMutexOwnerPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_IsSomeMutexOwnerPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_IsSomeMutexOwnerPost : fpost :=
 fun vl v ll ct=> mkfunasrt (OS_IsSomeMutexOwnerPostGood vl v ll ct).

Open Scope list_scope.

Definition OS_Sched_spec : fspec:= (OS_SchedPre,OS_SchedPost,(Tvoid,nil)).
(*
Definition OSIntExit_spec : fspec:= (OSIntExitPre,OSIntExitPost,(Tvoid,nil)). 
*)
Definition OSTimeTick_spec : fspec:= (OSTimeTickPre,OSTimeTickPost,(Tvoid,nil)).

(* Definition OS_EventSearch_spec : fspec :=(OS_EventSearchPre, OS_EventSearchPost, (Tint8, (Tptr OS_EVENT) :: nil)). *)

Definition OS_EventRemove_spec : fspec :=(OS_EventRemovePre, OS_EventRemovePost, (Tvoid, (Tptr OS_EVENT) :: nil)).

Definition OS_EventRemoveDel_spec : fspec := (OS_EventRemoveDelPre, OS_EventRemoveDelPost, (Void, Tptr OS_EVENT :: nil)). 

Definition OS_EventTaskRdy_spec  : fspec :=(OS_EventTaskRdyPre, OS_EventTaskRdyPost, (Tint8, (Tptr OS_EVENT) :: (Tptr Tvoid) :: Tint16 :: nil)).

Definition OS_EventTaskWait_spec : fspec :=(OS_EventTaskWaitPre, OS_EventTaskWaitPost, (Tvoid, (Tptr OS_EVENT) :: nil)).

Definition OS_EventWaitListInit_spec : fspec := 
  (OS_EventWaitListInitPre, OS_EventWaitListInitPost, (Tvoid, (Tptr OS_EVENT)::nil)).

Definition OS_PrioChange_spec : fspec :=(OS_PrioChangePre, OS_PrioChangePost, (Tvoid, (Tptr OS_TCB) :: Tint8 :: Tint8 :: nil)).
 
Definition OS_TCBInit_spec : fspec :=
  (OS_TCBInitPre, OS_TCBInitPost, (Int8u, (Int8u (*:: Int32 :: Void∗ *) :: nil))).

Definition OS_IsSomeMutexOwner_spec : fspec :=(OS_IsSomeMutexOwnerPre, OS_IsSomeMutexOwnerPost, (Tint8, (Tptr OS_TCB) :: nil)).

Definition OS_EventTO_spec : fspec:= (OS_EventTOPre,OS_EventTOPost,(Tvoid, (Tptr OS_EVENT)::nil)). 

Definition OS_EventPostTO_spec : fspec :=(OS_EventPostTOPre, OS_EventPostTOPost, (Tvoid, (Tptr OS_EVENT) :: nil)).

(*here can compile*)
(***************)
(* UserAddrCheck *)
(* pre *)
Definition UserAddrCheckPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX a s,
    Aisr empisr ** Aie true ** Ais nil ** Acs nil **
     <||s||> **
    [| nth_val 0 vl = Some (Vint32 a)|] ** [|logicl = logic_code s::nil|] ** p_local OSLInv  ct init_lg.

Theorem UserAddrCheckPreGood (vl:vallist) ll ct:
  GoodFunAsrt (UserAddrCheckPre' vl ll ct).
Proof.
unfold GoodFunAsrt.
unfold UserAddrCheckPre'.
intros.
simpl.
repeat split; try auto.
Qed.

Definition UserAddrCheckPre : fpre :=
  fun vl ll ct => mkfunasrt (UserAddrCheckPreGood vl ll ct).

Open Scope code_scope.
Local Open Scope int_scope.

(*Definition UserAddrStart := UserAddrStart_6713.*)
(*Definition UserAddrCheck := UserAddrCheck_6713.*)

Definition UserAddrCheckPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct UserAddrStart :=
   (EX a s,
     Aisr empisr ** Aie true ** Ais nil ** Acs nil **
     <||s||> **
    [| nth_val 0 vl = Some (Vint32 a) /\ (Z.le (Int.unsigned a) (UserAddrStart) \/ Z.lt (UserAddrEnd) (Int.unsigned a)) |] **
    [| v = Some (V$ 0)|] **
    [|logicl = logic_code s::nil|] ** p_local OSLInv  ct init_lg) \\//
  (EX a s,
      Aisr empisr ** Aie true ** Ais nil ** Acs nil **
     <||s||> **
    [| nth_val 0 vl = Some (Vint32 a) /\ Z.lt (UserAddrStart) (Int.unsigned a) /\  Z.le (Int.unsigned a) (UserAddrEnd) |] **
    [| v = Some (V$ 1)|] **
    [|logicl = logic_code s::nil|] ** p_local OSLInv  ct init_lg).

Theorem UserAddrCheckPostGood (vl:vallist) (v:option val) ll ct UserAddrStart:
  GoodFunAsrt (UserAddrCheckPost' vl v ll ct UserAddrStart).
Proof.
 unfold GoodFunAsrt.
 unfold UserAddrCheckPost'.
 intros.
 simpl.
 repeat split; try auto.
Qed.
(*here can compile*)
Definition UserAddrCheckPost_6678 : fpost :=
  fun vl v ll ct => mkfunasrt (UserAddrCheckPostGood vl v ll ct UserAddrStart_6678).
Definition UserAddrCheckPost_6713 : fpost :=
  fun vl v ll ct => mkfunasrt (UserAddrCheckPostGood vl v ll ct UserAddrStart_6713).
  
Definition UserAddrCheck6678_spec : fspec := (UserAddrCheckPre, UserAddrCheckPost_6678, (Int8u, Int32u::nil)).
Definition UserAddrCheck6713_spec : fspec := (UserAddrCheckPre, UserAddrCheckPost_6713, (Int8u, Int32u::nil)).

(*OSIntEnter*)
Definition OSIntEnterPre_int (vl:vallist) (logicl:list logicvar) ct :=
  EX ir er si i v s evloc muxptr semptr qptr, [|logicl = (logic_isr ir) :: (logic_ier er) :: (logic_ie false) ::
        (logic_is si) :: (logic_hid i) :: (logic_val v) ::
        (logic_val evloc) :: (logic_val muxptr) :: (logic_val semptr) :: (logic_val qptr) :: logic_code s :: nil|] **
    Aisr (isrupd ir i%nat true) **
    ([|i%nat = 1%nat|] ** Aier (ierupd er i%nat false) \\//
    [|i%nat <> 1%nat|] ** Aier (ierupd er i%nat true)) **
    Aie false ** 
    Ais (i%nat :: si) **
    Acs nil ** <||s||> **
    [| isr_is_prop (isrupd ir i%nat true) (i%nat :: si) |] **
    (
    (EX (ptbl : vallist) (p1 p2 : val) 
        (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
        (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map) 
        (tcbls : TcbMod.map) (t : int32) pf lf vhold scapl mcapl qcapl ptls (pattr : PthattrMod.map) acspace,
          AOSMapTbl **
          AOSUnMapTbl **
          AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold**
          AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf**
          AOSTCBFreeList' pf lf ct tcbls **
          AOSRdyTblGrp rtbl rgrp **
          AOSTime (Vint32 t) **
          HTCBList tcbls **
          HTime t **
          HCurTCB ct **
          AGVars **
          APthreadAttr pattr **
          IntInv ** TmrInv ** CoreCommuInv ecbls ** PartitionInv ecbls** (CapabilityInv acspace) **
          EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
          [|RH_TCBList_ECBList_P ecbls tcbls ct|] ))  ** p_local OSLInv ct (logic_val v :: logic_val evloc :: logic_val muxptr :: logic_val semptr :: logic_val qptr :: nil)  ** [| isflag v |].
  
Definition OSIntEnterPost_int (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
EX ir er si i v s evloc muxptr semptr qptr, [|logicl = (logic_isr ir) :: (logic_ier er) :: (logic_ie false) ::
      (logic_is si) :: (logic_hid i) :: (logic_val v) ::
      (logic_val evloc) :: (logic_val muxptr) :: (logic_val semptr) :: (logic_val qptr) :: logic_code s::nil |] **
  Aisr (isrupd ir i%nat true) **
  ([|i%nat = 1%nat|] ** Aier (ierupd er i%nat false) \\//
  [|i%nat <> 1%nat|] ** Aier (ierupd er i%nat true)) ** 
  Aie false **
  Ais (i%nat :: si) **
  Acs nil ** <||s||> **
  [| isr_is_prop (isrupd ir i%nat true) (i%nat :: si) |] **
  (
  (EX (ptbl : vallist) (p1 p2 : val) 
      (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
      (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map) 
      (tcbls : TcbMod.map) (t : int32) pf lf vhold scapl mcapl qcapl ptls (pattr : PthattrMod.map) acspace,
        AOSMapTbl **
        AOSUnMapTbl **
        AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold**
        AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf**
        AOSTCBFreeList' pf lf ct tcbls **
        AOSRdyTblGrp rtbl rgrp **
        AOSTime (Vint32 t) **
        HTCBList tcbls **
        HTime t **
        HCurTCB ct **
        AGVars **
        APthreadAttr pattr **
        IntInv ** TmrInv ** CoreCommuInv ecbls ** PartitionInv ecbls** (CapabilityInv acspace) **
        EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl ** 
        [|RH_TCBList_ECBList_P ecbls tcbls ct|] ))  ** p_local OSLInv ct (logic_val v :: logic_val evloc :: logic_val muxptr :: logic_val semptr :: logic_val qptr :: nil)  ** [| isflag v |].

Theorem OSIntEnterPreIntGood (vl:vallist) ll ct:
  GoodFunAsrt (OSIntEnterPre_int vl ll ct).
Proof.
  GoodFunAsrt_solver.
  intro; apply GoodFunAsrt_err_sllseg.
  intro; apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.
  
Theorem OSIntEnterPostIntGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSIntEnterPost_int vl v ll ct).
Proof.
  GoodFunAsrt_solver.
  intro; apply GoodFunAsrt_err_sllseg.
  intro; apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.  


Definition OSIntEnterIntPre : fpre :=
  fun vl ll ct => mkfunasrt (OSIntEnterPreIntGood vl ll ct).
  
Definition OSIntEnterIntPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSIntEnterPostIntGood vl v ll ct).

Definition OSIntEnter_spec : fspec := (OSIntEnterIntPre,OSIntEnterIntPost,(Tvoid,nil)). 



(*OSIntExit*)
Definition OSIntExitPre_int (vl:vallist) (logicl:list logicvar) ct :=
    EX ir er ie si i v s evloc muxptr semptr qptr, [|logicl=  (logic_isr ir) :: (logic_ier er) :: (logic_ie false) ::
    (logic_is si) :: (logic_hid i) :: (logic_val v) ::
    (logic_val evloc) :: (logic_val muxptr) :: (logic_val semptr) :: (logic_val qptr) :: logic_code s::nil  |] **  
      Aisr (isrupd ir i%nat false) **
      ([|i%nat = 1%nat|] ** Aier (ierupd er i%nat false) \\//
      [|i%nat <> 1%nat|] ** Aier (ierupd er i%nat true)) **
      Aie ie ** 
      Ais (i%nat :: si) ** 
      Acs nil ** <|| (isched;; END None ?? END None)||> **
      [| isr_is_prop (isrupd ir i%nat false) (i%nat :: si) |] **
      ((
      (EX (ptbl : vallist) (p1 p2 : val) 
          (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
          (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map) 
          (tcbls : TcbMod.map) (t : int32) pf lf vhold
          scapl mcapl qcapl ptls (pattr : PthattrMod.map) acspace,
            AOSMapTbl **
            AOSUnMapTbl **
            AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold **
            AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf**
            AOSTCBFreeList' pf lf ct tcbls **
            AOSRdyTblGrp rtbl rgrp **
            AOSTime (Vint32 t) **
            HTCBList tcbls **
            HTime t **
            HCurTCB ct **
            AGVars **
            APthreadAttr pattr **
            IntInv ** TmrInv ** CoreCommuInv ecbls ** PartitionInv ecbls** (CapabilityInv acspace) **
            EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
            [|RH_TCBList_ECBList_P ecbls tcbls ct|] ) ** [| ie = false |] ) \\//([|ie=true|] ** Afalse))  ** p_local OSLInv ct (logic_val v :: logic_val evloc :: logic_val muxptr :: logic_val semptr :: logic_val qptr :: nil) ** [| isflag v |].
            (*delete ie = true*)
(*加上[]*)

Definition OSIntExitPost_int (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
    EX ir er ie si i lv s evloc muxptr semptr qptr, [|logicl=  (logic_isr ir) :: (logic_ier er) :: (logic_ie false) ::
    (logic_is si) :: (logic_hid i) :: (logic_val lv) :: (logic_val evloc) :: (logic_val muxptr) :: (logic_val semptr) :: (logic_val qptr) :: logic_code s::nil  |]   ** 
      Aisr (isrupd ir i%nat false)**
      ([|i%nat = 1%nat|] ** Aier (ierupd er i%nat false) \\//
      [|i%nat <> 1%nat|] ** Aier (ierupd er i%nat true)) **
        Aie ie **
        Ais (i%nat :: si) **
        Acs nil ** <||END None||> **
        [| isr_is_prop (isrupd ir i%nat false) (i%nat :: si) |] **
        ((
        (EX (ptbl : vallist) (p1 p2 : val) 
            (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
            (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map) 
            (tcbls : TcbMod.map) (t : int32) pf lf vhold
            scapl mcapl qcapl ptls (pattr : PthattrMod.map) acspace,
              AOSMapTbl **
              AOSUnMapTbl **
              AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold **
              AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf **
              AOSTCBFreeList' pf lf ct tcbls**
              AOSRdyTblGrp rtbl rgrp **
              AOSTime (Vint32 t) **
              HTCBList tcbls **
              HTime t **
              HCurTCB ct **
              AGVars **
              APthreadAttr pattr **
              IntInv ** TmrInv ** CoreCommuInv ecbls ** PartitionInv ecbls** (CapabilityInv acspace) **
              EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
              [|RH_TCBList_ECBList_P ecbls tcbls ct|] )**[| ie = false |]) \\//([|ie=true|] ** Afalse))  **  p_local OSLInv ct (logic_val lv :: logic_val evloc :: logic_val muxptr :: logic_val semptr :: logic_val qptr :: nil) ** [|isflag lv|].

Theorem OSIntExitPreIntGood (vl:vallist) ll ct:
  GoodFunAsrt (OSIntExitPre_int vl ll ct).
Proof.
  GoodFunAsrt_solver.
  intro; apply GoodFunAsrt_err_sllseg.
  intro; apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.
  
Theorem OSIntExitPostIntGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSIntExitPost_int vl v ll ct).
Proof.
  GoodFunAsrt_solver.
  intro; apply GoodFunAsrt_err_sllseg.
  intro; apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition OSIntExitIntPre : fpre :=
  fun vl ll ct => mkfunasrt (OSIntExitPreIntGood vl ll ct).

Definition OSIntExitIntPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSIntExitPostIntGood vl v ll ct).

Definition OSIntExit_spec : fspec:= (OSIntExitIntPre,OSIntExitIntPost,(Tvoid,nil)).

(*EXC_HANDLER(­)*)

Definition EXC_HANDLERPre' (vl:vallist) (logicl:list logicvar) ct :=
  EX ir er si i v s evloc muxptr semptr qptr, [|logicl = (logic_isr ir) :: (logic_ier er) :: (logic_ie false) ::
      (logic_is si) :: (logic_hid i) :: (logic_val v) ::
      (logic_val evloc) :: (logic_val muxptr) :: (logic_val semptr) :: (logic_val qptr) :: logic_code s :: nil|] **
    Aisr (isrupd ir i%nat true) **
    ([|i%nat = 1%nat|] ** Aier (ierupd er i%nat false) \\//
      [|i%nat <> 1%nat|] ** Aier (ierupd er i%nat true)) **
    Aie false **
    Ais (i%nat :: si) **
    Acs nil ** <||s||> **
    [| isr_is_prop (isrupd ir i%nat true) (i%nat :: si) |] **
    ((EX (ptbl : vallist) (p1 p2 : val)
      (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
      (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map)
      (tcbls : TcbMod.map) (t : int32) pf lf vhold
      scapl mcapl qcapl ptls (pattr : PthattrMod.map) acspace,
        AOSMapTbl **
        AOSUnMapTbl **
        AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold **
        AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf **
        AOSTCBFreeList' pf lf ct tcbls **
        AOSRdyTblGrp rtbl rgrp **
        AOSTime (Vint32 t) **
        HTCBList tcbls **
        HTime t **
        HCurTCB ct **
        AGVars **
        APthreadAttr pattr **
        IntInv ** TmrInv ** CoreCommuInv ecbls ** PartitionInv ecbls** (CapabilityInv acspace)**
        EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
        [|RH_TCBList_ECBList_P ecbls tcbls ct|] )) **
    p_local OSLInv ct (logic_val v :: logic_val evloc :: logic_val muxptr :: logic_val semptr :: logic_val qptr :: nil) **
    [| isflag v |].

Definition EXC_HANDLERPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX ir er si i v s evloc muxptr semptr qptr, [|logicl = (logic_isr ir) :: (logic_ier er) :: (logic_ie false) ::
        (logic_is si) :: (logic_hid i) :: (logic_val v) ::
        (logic_val evloc) :: (logic_val muxptr) :: (logic_val semptr) :: (logic_val qptr) :: logic_code s ::nil |] **
    Aisr (isrupd ir i%nat true) **
    ([|i%nat = 1%nat|] ** Aier (ierupd er i%nat false) \\//
      [|i%nat <> 1%nat|] ** Aier (ierupd er i%nat true)) **
    Aie false **
    Ais (i%nat :: si) **
    Acs nil ** <||s||> **
    [| isr_is_prop (isrupd ir i%nat true) (i%nat :: si) |] **
    ((EX (ptbl : vallist) (p1 p2 : val)
        (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
        (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map)
        (tcbls : TcbMod.map) (t : int32) pf lf vhold
        scapl mcapl qcapl ptls (pattr : PthattrMod.map) acspace,
          AOSMapTbl **
          AOSUnMapTbl **
          AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold **
          AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf **
          AOSTCBFreeList' pf lf ct tcbls **
          AOSRdyTblGrp rtbl rgrp **
          AOSTime (Vint32 t) **
          HTCBList tcbls **
          HTime t **
          HCurTCB ct **
          AGVars **
          APthreadAttr pattr **
          IntInv ** TmrInv ** CoreCommuInv ecbls ** PartitionInv ecbls** (CapabilityInv acspace) **
          EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
          [|RH_TCBList_ECBList_P ecbls tcbls ct|] )) **
    p_local OSLInv ct (logic_val v :: logic_val evloc :: logic_val muxptr :: logic_val semptr :: logic_val qptr :: nil) **
    [| isflag v |].

Theorem EXC_HANDLERPre'_Good (vl:vallist) ll ct:
  GoodFunAsrt (EXC_HANDLERPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
  intro; apply GoodFunAsrt_err_sllseg.
  intro; apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Theorem EXC_HANDLERPost'_Good (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (EXC_HANDLERPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
  intro; apply GoodFunAsrt_err_sllseg.
  intro; apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition EXC_HANDLERPre : fpre :=
fun vl ll ct => mkfunasrt (EXC_HANDLERPre'_Good vl ll ct).

Definition EXC_HANDLERPost : fpost :=
fun vl v ll ct => mkfunasrt (EXC_HANDLERPost'_Good vl v ll ct).

Definition EXC_HANDLER_spec : fspec:= (EXC_HANDLERPre, EXC_HANDLERPost, (Tvoid,nil)).

(*OSTaskSuspend(­)*)

Definition OSTaskSuspendPre' (vl:vallist) (logicl:list logicvar) ct :=
  EX ir er si i v s evloc muxptr semptr qptr, [|logicl = (logic_isr ir) :: (logic_ier er) :: (logic_ie false) ::
        (logic_is si) :: (logic_hid i) :: (logic_val v) ::
        (logic_val evloc) :: (logic_val muxptr) :: (logic_val semptr) :: (logic_val qptr) :: logic_code s :: nil|] **
    Aisr (isrupd ir i%nat true) **
    ([|i%nat = 1%nat|] ** Aier (ierupd er i%nat false) \\//
      [|i%nat <> 1%nat|] ** Aier (ierupd er i%nat true)) **
    Aie false **
    Ais (i%nat :: si) **
    Acs nil ** <||s||> **
    [| isr_is_prop (isrupd ir i%nat true) (i%nat :: si) |] **
    ((EX (ptbl : vallist) (p1 p2 : val)
        (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
        (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map)
        (tcbls : TcbMod.map) (t : int32) pf lf vhold
        scapl mcapl qcapl ptls (pattr : PthattrMod.map) acspace,
          AOSMapTbl **
          AOSUnMapTbl **
          AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold **
          AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf **
          AOSTCBFreeList' pf lf ct tcbls **
          AOSRdyTblGrp rtbl rgrp **
          AOSTime (Vint32 t) **
          HTCBList tcbls **
          HTime t **
          HCurTCB ct **
          AGVars **
          APthreadAttr pattr **
          IntInv ** TmrInv ** CoreCommuInv ecbls ** PartitionInv ecbls** (CapabilityInv acspace) **
          EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
          [|RH_TCBList_ECBList_P ecbls tcbls ct|] )) **
      p_local OSLInv ct (logic_val v :: logic_val evloc :: logic_val muxptr :: logic_val semptr :: logic_val qptr :: nil) **
      [| isflag v |].

Definition OSTaskSuspendPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX ir er si i v s evloc muxptr semptr qptr, [|logicl = (logic_isr ir) :: (logic_ier er) :: (logic_ie false) ::
        (logic_is si) :: (logic_hid i) :: (logic_val v) ::
        (logic_val evloc) :: (logic_val muxptr) :: (logic_val semptr) :: (logic_val qptr) :: logic_code s ::nil |] **
    Aisr (isrupd ir i%nat true) **
    ([|i%nat = 1%nat|] ** Aier (ierupd er i%nat false) \\//
      [|i%nat <> 1%nat|] ** Aier (ierupd er i%nat true)) **
    Aie false **
    Ais (i%nat :: si) **
    Acs nil ** <||s||> **
    [| isr_is_prop (isrupd ir i%nat true) (i%nat :: si) |] **
    ((EX (ptbl : vallist) (p1 p2 : val)
        (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
        (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map)
        (tcbls : TcbMod.map) (t : int32) pf lf vhold
        scapl mcapl qcapl ptls (pattr : PthattrMod.map) acspace,
          AOSMapTbl **
          AOSUnMapTbl **
          AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold **
          AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf **
          AOSTCBFreeList' pf lf ct tcbls **
          AOSRdyTblGrp rtbl rgrp **
          AOSTime (Vint32 t) **
          HTCBList tcbls **
          HTime t **
          HCurTCB ct **
          AGVars **
          APthreadAttr pattr **
          IntInv ** TmrInv ** CoreCommuInv ecbls ** PartitionInv ecbls** (CapabilityInv acspace) **
          EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
          [|RH_TCBList_ECBList_P ecbls tcbls ct|] )) **
      p_local OSLInv ct (logic_val v :: logic_val evloc :: logic_val muxptr :: logic_val semptr :: logic_val qptr :: nil) **
      [| isflag v |].

Theorem OSTaskSuspendPre'_Good (vl:vallist) ll ct:
  GoodFunAsrt (OSTaskSuspendPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
  intro; apply GoodFunAsrt_err_sllseg.
  intro; apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Theorem OSTaskSuspendPost'_Good (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSTaskSuspendPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
  intro; apply GoodFunAsrt_err_sllseg.
  intro; apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition OSTaskSuspendPre : fpre :=
  fun vl ll ct => mkfunasrt (OSTaskSuspendPre'_Good vl ll ct).

Definition OSTaskSuspendPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSTaskSuspendPost'_Good vl v ll ct).

Definition OSTaskSuspend_spec : fspec:= (OSTaskSuspendPre, OSTaskSuspendPost, (Tint8,Tint8::nil)).

Definition fnullPre' (vl:vallist) (logicl:list logicvar) ct :=
  EX ir er si i v s evloc muxptr semptr qptr, [|logicl = (logic_isr ir) :: (logic_ier er) :: (logic_ie false) ::
  (logic_is si) :: (logic_hid i) :: (logic_val v) ::
  (logic_val evloc) :: (logic_val muxptr) :: (logic_val semptr) :: (logic_val qptr) :: logic_code s :: nil|] **
Aisr (isrupd ir i%nat true) **
([|i%nat = 1%nat|] ** Aier (ierupd er i%nat false) \\//
[|i%nat <> 1%nat|] ** Aier (ierupd er i%nat true)) **
Aie false ** 
Ais (i%nat :: si) **
Acs nil ** <||s||> **
[| isr_is_prop (isrupd ir i%nat true) (i%nat :: si) |] **
(
(EX (ptbl : vallist) (p1 p2 : val) 
  (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
  (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map) 
  (tcbls : TcbMod.map) (t : int32) pf lf vhold
  scapl mcapl qcapl ptls (pattr : PthattrMod.map) acspace,
    AOSMapTbl **
    AOSUnMapTbl **
    AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold**
    AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf**
    AOSTCBFreeList' pf lf ct tcbls **
    AOSRdyTblGrp rtbl rgrp **
    AOSTime (Vint32 t) **
    HTCBList tcbls **
    HTime t **
    HCurTCB ct **
    AGVars **
    APthreadAttr pattr **
    IntInv ** TmrInv ** CoreCommuInv ecbls ** PartitionInv ecbls** (CapabilityInv acspace) **
    EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
    [|RH_TCBList_ECBList_P ecbls tcbls ct|] ))  ** p_local OSLInv ct (logic_val v :: logic_val evloc :: logic_val muxptr :: logic_val semptr :: logic_val qptr :: nil)  ** [| isflag v |].

Definition fnullPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX ir er si i v s evloc muxptr semptr qptr, [|logicl = (logic_isr ir) :: (logic_ier er) :: (logic_ie false) ::
  (logic_is si) :: (logic_hid i) :: (logic_val v) ::
  (logic_val evloc) :: (logic_val muxptr) :: (logic_val semptr) :: (logic_val qptr) :: logic_code s::nil |] **
Aisr (isrupd ir i%nat true) **
([|i%nat = 1%nat|] ** Aier (ierupd er i%nat false) \\//
[|i%nat <> 1%nat|] ** Aier (ierupd er i%nat true)) ** 
Aie false **
Ais (i%nat :: si) **
Acs nil ** <||s||> **
[| isr_is_prop (isrupd ir i%nat true) (i%nat :: si) |] **
(
(EX (ptbl : vallist) (p1 p2 : val) 
  (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
  (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map) 
  (tcbls : TcbMod.map) (t : int32) pf lf vhold
  scapl mcapl qcapl ptls (pattr : PthattrMod.map) acspace,
      AOSMapTbl **
      AOSUnMapTbl **
      AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold**
      AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf**
      AOSTCBFreeList' pf lf ct tcbls **
      AOSRdyTblGrp rtbl rgrp **
      AOSTime (Vint32 t) **
      HTCBList tcbls **
      HTime t **
      HCurTCB ct **
      AGVars **
      APthreadAttr pattr **
      IntInv ** TmrInv ** CoreCommuInv ecbls ** PartitionInv ecbls** (CapabilityInv acspace)**
      EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl ** 
      [|RH_TCBList_ECBList_P ecbls tcbls ct|] ))  ** p_local OSLInv ct (logic_val v :: logic_val evloc :: logic_val muxptr :: logic_val semptr :: logic_val qptr :: nil)  ** [| isflag v |].

Theorem fnullPre'_Good (vl:vallist) ll ct:
  GoodFunAsrt (fnullPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
  intro; apply GoodFunAsrt_err_sllseg.
  intro; apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Theorem fnullPost'_Good (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (fnullPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
  intro; apply GoodFunAsrt_err_sllseg.
  intro; apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition fnullPre : fpre :=
  fun vl ll ct => mkfunasrt (fnullPre'_Good vl ll ct).

Definition fnullPost : fpost :=
  fun vl v ll ct => mkfunasrt (fnullPost'_Good vl v ll ct).

Definition fnull_spec : fspec:= (fnullPre, fnullPost, (Tvoid,nil)).

Definition OSIpc1Pre' (vl:vallist) (logicl:list logicvar) ct :=
  EX ir er si i v s evloc muxptr semptr qptr, [|logicl = (logic_isr ir) :: (logic_ier er) :: (logic_ie false) ::
  (logic_is si) :: (logic_hid i) :: (logic_val v) ::
  (logic_val evloc) :: (logic_val muxptr) :: (logic_val semptr) :: (logic_val qptr) :: logic_code s :: nil|] **
Aisr (isrupd ir i%nat true) **
([|i%nat = 1%nat|] ** Aier (ierupd er i%nat false) \\//
[|i%nat <> 1%nat|] ** Aier (ierupd er i%nat true)) **
Aie false ** 
Ais (i%nat :: si) **
Acs nil ** <||s||> **
[| isr_is_prop (isrupd ir i%nat true) (i%nat :: si) |] **
(
(EX (ptbl : vallist) (p1 p2 : val) 
  (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
  (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map) 
  (tcbls : TcbMod.map) (t : int32) pf lf vhold
  scapl mcapl qcapl ptls (pattr : PthattrMod.map) acspace, 
      AOSMapTbl **
      AOSUnMapTbl **
      AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold**
      AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf**
      AOSTCBFreeList' pf lf ct tcbls **
      AOSRdyTblGrp rtbl rgrp **
      AOSTime (Vint32 t) **
      HTCBList tcbls **
      HTime t **
      HCurTCB ct **
      AGVars **
      APthreadAttr pattr **
      IntInv ** TmrInv ** CoreCommuInv ecbls ** PartitionInv ecbls** (CapabilityInv acspace) **
      EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
      [|RH_TCBList_ECBList_P ecbls tcbls ct|] ))  ** p_local OSLInv ct (logic_val v :: logic_val evloc :: logic_val muxptr :: logic_val semptr :: logic_val qptr :: nil)  ** [| isflag v |].

Definition OSIpc1Post' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX ir er si i v s evloc muxptr semptr qptr, [|logicl = (logic_isr ir) :: (logic_ier er) :: (logic_ie false) ::
        (logic_is si) :: (logic_hid i) :: (logic_val v) ::
        (logic_val evloc) :: (logic_val muxptr) :: (logic_val semptr) :: (logic_val qptr) :: logic_code s::nil |] **
    Aisr (isrupd ir i%nat true) **
    ([|i%nat = 1%nat|] ** Aier (ierupd er i%nat false) \\//
    [|i%nat <> 1%nat|] ** Aier (ierupd er i%nat true)) ** 
    Aie false **
    Ais (i%nat :: si) **
    Acs nil ** <||s||> **
    [| isr_is_prop (isrupd ir i%nat true) (i%nat :: si) |] **
    (
    (EX (ptbl : vallist) (p1 p2 : val) 
        (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
        (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map) 
        (tcbls : TcbMod.map) (t : int32) pf lf vhold
        scapl mcapl qcapl ptls (pattr : PthattrMod.map) acspace,
            AOSMapTbl **
            AOSUnMapTbl **
            AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold**
            AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf**
            AOSTCBFreeList' pf lf ct tcbls **
            AOSRdyTblGrp rtbl rgrp **
            AOSTime (Vint32 t) **
            HTCBList tcbls **
            HTime t **
            HCurTCB ct **
            AGVars **
            APthreadAttr pattr **
            IntInv ** TmrInv ** CoreCommuInv ecbls ** PartitionInv ecbls** (CapabilityInv acspace) **
            EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl ** 
            [|RH_TCBList_ECBList_P ecbls tcbls ct|] ))  ** p_local OSLInv ct (logic_val v :: logic_val evloc :: logic_val muxptr :: logic_val semptr :: logic_val qptr :: nil)  ** [| isflag v |].
  
Theorem OSIpc1Pre'_Good (vl:vallist) ll ct:
  GoodFunAsrt (OSIpc1Pre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
  intro; apply GoodFunAsrt_err_sllseg.
  intro; apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Theorem OSIpc1Post'_Good (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSIpc1Post' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
  intro; apply GoodFunAsrt_err_sllseg.
  intro; apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition OSIpc1Pre : fpre :=
  fun vl ll ct => mkfunasrt (OSIpc1Pre'_Good vl ll ct).

Definition OSIpc1Post : fpost :=
  fun vl v ll ct => mkfunasrt (OSIpc1Post'_Good vl v ll ct).

Definition OSIpc1_spec : fspec:= (OSIpc1Pre, OSIpc1Post, (Tvoid,nil)).

Definition Interrupt_InitPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX a s isr ier is cs Hier,
    [|logicl = logic_val (Vint32 a) ::logic_code s:: (logic_isr isr) :: (logic_ier ier) :: (logic_is is) :: (logic_cs cs) :: (logic_ier Hier) ::nil|] **
    Aisr isr ** Aier ier ** Aie false ** Ais is ** Acs cs ** Aabsdata ierid (hier Hier) ** AGVars **
    [| nth_val 1 vl = Some (Vint32 a) /\ (Int.ltu a (Int.repr INT_NUM_MIN) = false) /\ (Int.ltu (Int.repr INT_NUM_MAX) a = false)|] **
    <|| int_enable_pic_aop(|nil|);; s||> ** p_local OSLInv ct init_lg.

Definition Interrupt_InitPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
   (EX a s isr ier is cs Hier,
     [|logicl = logic_val (Vint32 a) ::logic_code s:: (logic_isr isr) :: (logic_ier ier) :: (logic_is is) :: (logic_cs cs) :: (logic_ier Hier) ::nil|] **
     [| nth_val 1 vl = Some (Vint32 a)|] **
     Aisr isr ** Aier (ierupd ier (Z.to_nat (Int.unsigned a)) true) ** Aie false ** Ais is ** Acs cs ** 
      Aabsdata ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned a)) true)) ** AGVars **
     <||s||> ** p_local OSLInv ct init_lg) \\//
    (EX a s isr ier is cs Hier,
    [|logicl = logic_val (Vint32 a) ::logic_code s:: (logic_isr isr) :: (logic_ier ier) :: (logic_is is) :: (logic_cs cs) :: (logic_ier Hier) ::nil|] **
    Aisr isr ** Aier ier ** Aie false ** Ais is ** Acs cs ** Aabsdata ierid (hier Hier) ** AGVars **
    [| nth_val 1 vl = Some (Vint32 a) /\ (Int.ltu a (Int.repr INT_NUM_MIN) = false) /\ (Int.ltu (Int.repr INT_NUM_MAX) a = false)|] **
    <|| int_enable_pic_aop(|nil|);; s||> ** p_local OSLInv ct init_lg).

Theorem Interrupt_InitPreGood (vl:vallist) ll ct:
  GoodFunAsrt (Interrupt_InitPre' vl ll ct).
Proof.
  unfold GoodFunAsrt.
  unfold Interrupt_InitPre'.
  intros.
  simpl.
  repeat split; try auto.
Qed.

Definition Interrupt_InitPre : fpre :=
  fun vl ll ct => mkfunasrt (Interrupt_InitPreGood vl ll ct).

Theorem Interrupt_InitPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (Interrupt_InitPost' vl v ll ct).
Proof.
 unfold GoodFunAsrt.
 unfold Interrupt_InitPost'.
 intros.
 simpl.
 repeat split; try auto.
Qed.

Definition Interrupt_InitPost : fpost :=
  fun vl v ll ct => mkfunasrt (Interrupt_InitPostGood vl v ll ct).

Definition Interrupt_Init_spec : fspec := (Interrupt_InitPre,Interrupt_InitPost,(Tvoid, Tint32 :: Tint32 :: nil)).


(***************** spec for functions for events *******************)

Open Scope int_scope.

(* UserAddrCheck *)
(* this spec is to be used for UserAddrCheck that is invoked from GJB functions, outside of critical sections *)

Definition UserAddrCheckEvtPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX s er,
    Aisr empisr ** Aie true ** Ais nil ** Acs nil ** Aier er **
     <||s||> **
     [| nth_val 0 vl = Some Vnull \/ exists a, nth_val 0 vl = Some (Vptr a) |] **
     [|logicl = (* (logic_ier er) :: *) logic_code s::nil|] **
     p_local OSLInv ct init_lg.   

Theorem UserAddrCheckEvtPreGood (vl:vallist) ll ct:
  GoodFunAsrt (UserAddrCheckEvtPre' vl ll ct).
Proof.
  unfold GoodFunAsrt.
  unfold UserAddrCheckEvtPre'.
  intros.
  simpl.
  repeat split; try auto.
Qed.

Definition UserAddrCheckEvtPre : fpre :=
  fun vl ll ct => mkfunasrt (UserAddrCheckEvtPreGood vl ll ct).

Definition UserAddrCheckEvtPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
   (EX s er,
     Aisr empisr ** Aie true ** Ais nil ** Acs nil ** Aier er **
     <||s||> **
     [| nth_val 0 vl = Some Vnull \/ 
          exists a, nth_val 0 vl = Some (Vptr a) /\
                      (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true) |] ** 
    [| v = Some (V$ 0)|] ** 
    [| logicl =(*  (logic_ier er) ::  *)logic_code s::nil |] ** p_local OSLInv  ct init_lg) 
     \\// 
  (EX s er,
      Aisr empisr ** Aie true ** Ais nil ** Acs nil ** Aier er **
     <||s||> **
     [| exists a, nth_val 0 vl = Some (Vptr a) /\
                    cmpaddr Clt userAddrStart a = true /\
                    cmpaddr Cle a userAddrEnd = true |] **  
     [| v = Some (V$ 1)|] **
     [| logicl = (* (logic_ier er) :: *) logic_code s::nil |] ** p_local OSLInv  ct init_lg). 


Theorem UserAddrCheckEvtPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (UserAddrCheckEvtPost' vl v ll ct).
Proof.
  unfold GoodFunAsrt.
  unfold UserAddrCheckEvtPost'.
  intros.
  simpl.
  repeat split; try auto.
Qed.

Definition UserAddrCheckEvtPost : fpost :=
  fun vl v ll ct => mkfunasrt (UserAddrCheckEvtPostGood vl v ll ct).

Definition UserAddrCheckEvt_spec : fspec :=
  (UserAddrCheckEvtPre, UserAddrCheckEvtPost, (Int8s, (Tptr Tint32)::nil)).

(* UserAddrCheck *)
(* this spec is to be used for UserAddrCheck that is invoked from GJB functions, inside critical sections *) 

Definition UserAddrCheckCritPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX s er,
    Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** A_isr_is_prop ** Aier er **
     <||s||> **
     [| nth_val 0 vl = Some Vnull \/ exists a, nth_val 0 vl = Some (Vptr a) |] **
     [|logicl = logic_code s::nil|] **
     p_local OSLInv  ct init_lg.  

Theorem UserAddrCheckCritPreGood (vl:vallist) ll ct:
  GoodFunAsrt (UserAddrCheckCritPre' vl ll ct).
Proof.
  unfold GoodFunAsrt.
  unfold UserAddrCheckCritPre'.
  intros.
  simpl.
  repeat split; try auto.
Qed.

Definition UserAddrCheckCritPre : fpre :=
  fun vl ll ct => mkfunasrt (UserAddrCheckCritPreGood vl ll ct).

Definition UserAddrCheckCritPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
   (EX s er,
     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** A_isr_is_prop ** Aier er **
     <||s||> **
     [| nth_val 0 vl = Some Vnull \/ 
          exists a, nth_val 0 vl = Some (Vptr a) /\
                      (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true) |] ** 
    [| v = Some (V$ 0)|] ** 
    [| logicl = logic_code s::nil |] ** p_local OSLInv  ct init_lg) 
     \\// 
  (EX s er,
      Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** A_isr_is_prop ** Aier er **
     <||s||> **
     [| exists a, nth_val 0 vl = Some (Vptr a) /\
                    cmpaddr Clt userAddrStart a = true /\
                    cmpaddr Cle a userAddrEnd = true |] **  
     [| v = Some (V$ 1)|] **
     [| logicl = logic_code s::nil |] ** p_local OSLInv  ct init_lg). 


Theorem UserAddrCheckCritPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (UserAddrCheckCritPost' vl v ll ct).
Proof.
  unfold GoodFunAsrt.
  unfold UserAddrCheckCritPost'.
  intros.
  simpl.
  repeat split; try auto.
Qed.



Definition UserAddrCheckCritPost : fpost :=
  fun vl v ll ct => mkfunasrt (UserAddrCheckCritPostGood vl v ll ct).

Definition UserAddrCheckCrit_spec : fspec :=
  (UserAddrCheckCritPre, UserAddrCheckCritPost, (Int8s, (Tptr sem_t)::nil)).  


(* getFreePos *)
(* pre *)

Definition getFreePosPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX tp s semvl muxvl qattrl lg' er dom2index domls kscurd cpn lsem lmux lmq,
    Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** Aier er **
    ASeminfo lsem semvl ** APthreadMutex lmux muxvl ** AMqAttr lmq qattrl **
    A_isr_is_prop ** <||s||> **
    Adomain2index dom2index domls ** AKsCurDomain kscurd **
    [|(0 <= Int.unsigned kscurd < DOMAIN_SIZE)%Z |] **
    ACorepartnum cpn ** [| R_Cpartnum_Dom2idx_P cpn dom2index |] **
    [| nth_val 0 vl = Some (Vint32 tp)|] ** 
    [|logicl = logic_val (Vptr lsem) :: logic_val (Vptr lmux) :: logic_val (Vptr lmq) :: 
                      logic_val (Vint32 kscurd) :: logic_val (Vint32 cpn) :: logic_lv dom2index :: 
                      logic_llv semvl :: logic_llv muxvl :: logic_llv qattrl :: logic_code s :: lg'|] ** 
    p_local OSLInv ct (logic_val (V$ 1) :: lg').

Theorem getFreePosPreGood (vl:vallist) ll ct:
  GoodFunAsrt (getFreePosPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition getFreePosPre : fpre :=
  fun vl ll ct => mkfunasrt (getFreePosPreGood vl ll ct).

Definition Seminfo_full_P' semvl idx cpn :=
forall i vl1,
    ((OS_USER_MAX_EVENTS / 3)/ (Int.unsigned cpn) *(Int.unsigned idx) <= i /\ 
      i < Z.of_nat (length semvl)) ->
      nth_vallist (nat_of_Z i) semvl = Some vl1 ->
      ~(V_OSSINFOPevent vl1 = Some Vnull).

Definition nth_Seminfo_free_P' i semvl idx cpn :=
exists vl1, ((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)*(Int.unsigned idx) <= i /\
                     i < (OS_USER_MAX_EVENTS / 3) / (Int.unsigned cpn) * ( (Int.unsigned idx) + 1 )) /\ 
                      nth_vallist (nat_of_Z i) semvl = Some vl1 /\
                      V_OSSINFOPevent vl1 = Some Vnull.

Definition PthreadMutex_full_P' muxvl idx cpn :=
forall i vl1, ( (OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)*(Int.unsigned idx) <= i
                         /\   i < Z.of_nat (length muxvl)) ->
                        nth_vallist (nat_of_Z i) muxvl = Some vl1 ->
                        ~(V_OSMUXINFOPevent vl1 = Some Vnull).

Definition nth_PthreadMutex_free_P' i muxvl idx cpn :=
exists vl1, ( (OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)*(Int.unsigned idx) <= i /\
                       i < (OS_USER_MAX_EVENTS / 3) / (Int.unsigned cpn) * ( (Int.unsigned idx) + 1 )) /\ 
                      nth_vallist (nat_of_Z i) muxvl = Some vl1 /\
                      V_OSMUXINFOPevent vl1 = Some Vnull.

Definition Qattr_full_P' mqvl idx cpn:=
forall i vl1, ( (OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)*(Int.unsigned idx) <= i /\
                          i < Z.of_nat (length mqvl)) ->
                        nth_vallist (nat_of_Z i) mqvl = Some vl1 ->
                        ~(V_QATTRpevent vl1 = Some Vnull).

Definition nth_Qattr_free_P' i mqvl idx cpn :=
exists vl1, ( (OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn) *(Int.unsigned idx) <= i /\
                       i < (OS_USER_MAX_EVENTS / 3) / (Int.unsigned cpn) * ( (Int.unsigned idx) + 1 )) /\ 
                      nth_vallist (nat_of_Z i) mqvl = Some vl1 /\
                      V_QATTRpevent vl1 = Some Vnull.

Definition getFreePosPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
   (EX s semvl muxvl qattrl i lg' er dom2index domls kscurd cpn idx lsem lmux lmq,
     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** Aier er **
     ASeminfo lsem semvl ** APthreadMutex lmux muxvl ** AMqAttr lmq qattrl **
     A_isr_is_prop ** <||s||> **
     Adomain2index dom2index domls ** AKsCurDomain kscurd **
    [|(0 <= Int.unsigned kscurd < DOMAIN_SIZE)%Z |] **
    ACorepartnum cpn ** [| R_Cpartnum_Dom2idx_P cpn dom2index |] **
    [| nth_val 0 vl = Some (Vint32 ($ 0)) |] **
    [| nth_val' (Z.to_nat (Int.unsigned kscurd)) dom2index = Vint32 idx |] **
    [| nth_Seminfo_free_P' i semvl idx cpn |] **
    [| v = Some (V$ i)|] **
    [|logicl = logic_val (Vptr lsem) :: logic_val (Vptr lmux) :: logic_val (Vptr lmq) :: 
               logic_val (Vint32 kscurd) :: logic_val (Vint32 cpn) :: logic_lv dom2index :: 
               logic_llv semvl :: logic_llv muxvl :: logic_llv qattrl :: logic_code s :: lg' |] ** p_local OSLInv ct (logic_val (V$1) :: lg')) \\// (*type == 0, i.e. sem return i*)
  (EX s semvl muxvl qattrl lg' er dom2index domls kscurd cpn idx vll1 vll2 lsem lmux lmq,
     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** Aier er **
     ASeminfo lsem semvl ** APthreadMutex lmux muxvl ** AMqAttr lmq qattrl **
     A_isr_is_prop ** <||s||> **
     Adomain2index dom2index domls ** AKsCurDomain kscurd **
    [|(0 <= Int.unsigned kscurd < DOMAIN_SIZE)%Z |] **
    ACorepartnum cpn ** [| R_Cpartnum_Dom2idx_P cpn dom2index |] **
    [| nth_val 0 vl = Some (Vint32 ($ 0)) |] **
    [| nth_val' (Z.to_nat (Int.unsigned kscurd)) dom2index = Vint32 idx |] **
    [|vll1 ++ vll2 = semvl|] **
    [|length vll1 = ∘ (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) * (Int.unsigned idx + 1))|] **
    [| Seminfo_full_P' vll1 idx cpn |] **
    [| v = Some (V$ 255)|] **
    [|logicl =  logic_val (Vptr lsem) :: logic_val (Vptr lmux) :: logic_val (Vptr lmq) :: 
                logic_val (Vint32 kscurd) :: logic_val (Vint32 cpn) :: logic_lv dom2index :: 
                logic_llv semvl :: logic_llv muxvl :: logic_llv qattrl :: logic_code s :: lg'|] ** p_local OSLInv ct (logic_val (V$1) :: lg')) \\// (*type == 0, i.e. sem, return -1*)
  (EX s semvl muxvl qattrl i lg' er dom2index domls kscurd cpn idx lsem lmux lmq,
     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** Aier er **
     ASeminfo lsem semvl ** APthreadMutex lmux muxvl ** AMqAttr lmq qattrl **
     A_isr_is_prop ** <||s||> **
     Adomain2index dom2index domls ** AKsCurDomain kscurd **
    [|(0 <= Int.unsigned kscurd < DOMAIN_SIZE)%Z |] **
    ACorepartnum cpn ** [| R_Cpartnum_Dom2idx_P cpn dom2index |] **
    [| nth_val 0 vl = Some (Vint32 ($ 1)) |] **
    [| nth_val' (Z.to_nat (Int.unsigned kscurd)) dom2index = Vint32 idx |] **
    [| nth_PthreadMutex_free_P' i muxvl idx cpn |] **
    [| v = Some (V$ i)|] **
    [|logicl = logic_val (Vptr lsem) :: logic_val (Vptr lmux) :: logic_val (Vptr lmq) :: 
               logic_val (Vint32 kscurd) :: logic_val (Vint32 cpn) :: logic_lv dom2index :: 
               logic_llv semvl :: logic_llv muxvl :: logic_llv qattrl :: logic_code s:: lg'|] ** p_local OSLInv  ct (logic_val (V$1) :: lg')) \\// (*type == 1, i.e. mux return i*)
  (EX s semvl muxvl qattrl lg' er dom2index domls kscurd cpn idx vll1 vll2 lsem lmux lmq,
     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** Aier er **
     ASeminfo lsem semvl ** APthreadMutex lmux muxvl ** AMqAttr lmq qattrl **
     A_isr_is_prop ** <||s||> **
     Adomain2index dom2index domls ** AKsCurDomain kscurd **
    [|(0 <= Int.unsigned kscurd < DOMAIN_SIZE)%Z |] **
    ACorepartnum cpn ** [| R_Cpartnum_Dom2idx_P cpn dom2index |] **
    [| nth_val 0 vl = Some (Vint32 ($ 1)) |] **
    [| nth_val' (Z.to_nat (Int.unsigned kscurd)) dom2index = Vint32 idx |] **
    [|vll1 ++ vll2 = muxvl|] **
    [|length vll1 = ∘ (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) * (Int.unsigned idx + 1))|] **
    [| PthreadMutex_full_P' vll1 idx cpn |] **
    [| v = Some (V$ 255 (* -1 *))|] **
    [|logicl = logic_val (Vptr lsem) :: logic_val (Vptr lmux) :: logic_val (Vptr lmq) :: 
               logic_val (Vint32 kscurd) :: logic_val (Vint32 cpn) :: logic_lv dom2index ::  
               logic_llv semvl :: logic_llv muxvl :: logic_llv qattrl :: logic_code s:: lg'|] ** p_local OSLInv  ct (logic_val (V$1) :: lg')) \\// (*type == 1, i.e. mux return -1*)
  (EX s semvl muxvl qattrl i lg' er dom2index domls kscurd cpn idx lsem lmux lmq,
     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** Aier er **
     ASeminfo lsem semvl ** APthreadMutex lmux muxvl ** AMqAttr lmq qattrl **
     A_isr_is_prop ** <||s||> **
     Adomain2index dom2index domls ** AKsCurDomain kscurd **
    [|(0 <= Int.unsigned kscurd < DOMAIN_SIZE)%Z |] **
    ACorepartnum cpn ** [| R_Cpartnum_Dom2idx_P cpn dom2index |] **
    [| nth_val 0 vl = Some (Vint32 ($ 2)) |] **
    [| nth_val' (Z.to_nat (Int.unsigned kscurd)) dom2index = Vint32 idx |] **
    [| nth_Qattr_free_P' i qattrl idx cpn |] ** 
    [| v = Some (V$ i)|] **
    [|logicl = logic_val (Vptr lsem) :: logic_val (Vptr lmux) :: logic_val (Vptr lmq) :: 
               logic_val (Vint32 kscurd) :: logic_val (Vint32 cpn) :: logic_lv dom2index ::  
               logic_llv semvl :: logic_llv muxvl :: logic_llv qattrl :: logic_code s :: lg' |] ** p_local OSLInv ct (logic_val (V$1) :: lg')) \\// (*type == 2, queue return i*)
  (EX s semvl muxvl qattrl lg' er dom2index domls kscurd cpn idx vll1 vll2 lsem lmux lmq,
     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** Aier er **
     ASeminfo lsem semvl ** APthreadMutex lmux muxvl ** AMqAttr lmq qattrl **
     A_isr_is_prop ** <||s||> **
     Adomain2index dom2index domls ** AKsCurDomain kscurd **
    [|(0 <= Int.unsigned kscurd < DOMAIN_SIZE)%Z |] **
    ACorepartnum cpn ** [| R_Cpartnum_Dom2idx_P cpn dom2index |] **
    [| nth_val 0 vl = Some (Vint32 ($ 2)) |] **
    [| nth_val' (Z.to_nat (Int.unsigned kscurd)) dom2index = Vint32 idx |] **
    [|vll1 ++ vll2 = qattrl|] **
    [|length vll1 = ∘ (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) * (Int.unsigned idx + 1))|] **
    [| Qattr_full_P' vll1 idx cpn |] **
    [| v = Some (V$ 255)|] **
    [|logicl = logic_val (Vptr lsem) :: logic_val (Vptr lmux) :: logic_val (Vptr lmq) :: 
               logic_val (Vint32 kscurd) :: logic_val (Vint32 cpn) :: logic_lv dom2index ::  
               logic_llv semvl :: logic_llv muxvl :: logic_llv qattrl :: logic_code s :: lg'|] ** p_local OSLInv ct (logic_val (V$1) :: lg')) \\// (*type == 2, queue return -1*)
  (EX s tp semvl muxvl qattrl lg' er dom2index domls kscurd cpn lsem lmux lmq,
     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** Aier er **
     ASeminfo lsem semvl ** APthreadMutex lmux muxvl ** AMqAttr lmq qattrl **
     A_isr_is_prop ** <||s||> **
     Adomain2index dom2index domls ** AKsCurDomain kscurd **
    [|(0 <= Int.unsigned kscurd < DOMAIN_SIZE)%Z |] **
    ACorepartnum cpn ** [| R_Cpartnum_Dom2idx_P cpn dom2index |] **
    [| nth_val 0 vl = Some (Vint32 tp) /\ tp <> Int.zero /\ tp <> Int.one /\ tp <> ($ 2) |] **
    [| v = Some (V$ 255)|] **
    [|logicl = logic_val (Vptr lsem) :: logic_val (Vptr lmux) :: logic_val (Vptr lmq) :: 
               logic_val (Vint32 kscurd) :: logic_val (Vint32 cpn) :: logic_lv dom2index ::  
               logic_llv semvl :: logic_llv muxvl :: logic_llv qattrl :: logic_code s :: lg'|] ** p_local OSLInv ct (logic_val (V$1) :: lg')). (*3 <= type , i.e.  return -1*)

Theorem getFreePosPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (getFreePosPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition getFreePosPost : fpost :=
  fun vl v ll ct => mkfunasrt (getFreePosPostGood vl v ll ct).

Definition getFreePos_spec : fspec := (getFreePosPre,getFreePosPost,(Int8s, Int32u::nil)).

(*  internal function version of pthread_mutexattr_init *)

Definition MutexAttrInitPre' (vl:vallist) (logicl:list logicvar) ct :=
  EX s v' er,
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
      [| logicl = logic_val v' :: logic_code s :: nil |] **
      <|| (mutexattrinit (vl++(v' ::nil)));; s ||> **
      p_local OSLInv ct init_lg). 

Theorem MutexAttrInitPreGood (vl:vallist) ll ct:
  GoodFunAsrt (MutexAttrInitPre' vl ll ct).
Proof.
simpl.
tauto.
Qed.

Definition MutexAttrInitPre : fpre :=
  fun vl ll ct => mkfunasrt (MutexAttrInitPreGood vl ll ct).

Definition MutexAttrInitPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v' k er,
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
      [| logicl = logic_val v' :: logic_code s :: nil |] **
      [| v = Some v' /\ v' = Vint32 k  /\ 
          Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k) (Int.max_unsigned) |] **
      [| nth_val' 0 vl = Vnull -> k = (Int.repr EINVAL) |] **
      <|| s ||> ** 
      p_local OSLInv ct init_lg).


Theorem MutexAttrInitPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (MutexAttrInitPost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition MutexAttrInitPost : fpost :=
  fun vl v ll ct => mkfunasrt (MutexAttrInitPostGood vl v ll ct).

Definition MutexAttrInit_spec : fspec :=
    (MutexAttrInitPre,MutexAttrInitPost,(Tint32,Tptr pthread_mutexattr_t::nil)).

(* memcpy used for events *)

Definition MemcpyPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX s v1 v2 v3  er,
    ( Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
      [| logicl =  logic_code s :: nil |] **
      [| vl = v1 :: v2 :: v3 :: nil |] ** (* [| pdata = Vptr x|] ** *)
      <|| spec_code_cons (memcpy_spec (vl))  s ||>**  
       p_local OSLInv ct init_lg  ).


Theorem MemcpyPreGood (vl:vallist) ll ct:
  GoodFunAsrt (MemcpyPre' vl ll ct).
Proof.
simpl.
tauto.
Qed.

Definition MemcpyPre : fpre :=
  fun vl ll ct => mkfunasrt (MemcpyPreGood vl ll ct).

Definition MemcpyPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s k er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl =  logic_code s :: nil |] **
       [| v = Some (Vint32 k)  /\
          Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k) (Byte.max_unsigned) |] ** 
     <|| s ||> ** p_local OSLInv ct init_lg).
     
Theorem MemcpyPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (MemcpyPost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition MemcpyPost : fpost :=
  fun vl v ll ct => mkfunasrt (MemcpyPostGood vl v ll ct).

Definition Memcpy_spec : fspec:= (MemcpyPre,MemcpyPost,(Tptr Void, Tptr Void:: Tptr Void :: size_t ::nil)).

(* OS_EventTaskPostRdy *)

Definition rel_edata_tcbstat_postrdy edata tcbstat :=
  match edata with
    | DMsgQ _ _ _ _ =>
      tcbstat = Int.repr OS_STAT_POSTQ \/ tcbstat = Int.or (Int.repr OS_STAT_POSTQ) (Int.repr OS_STAT_SUSPEND)
    | DSem _ =>
      tcbstat = Int.repr OS_STAT_SEM \/ tcbstat = Int.or (Int.repr OS_STAT_SEM) (Int.repr OS_STAT_SUSPEND)
    | DMbox _ =>
      tcbstat = Int.repr OS_STAT_MBOX \/ tcbstat = Int.or (Int.repr OS_STAT_MBOX) (Int.repr OS_STAT_SUSPEND)
    | DMutex _ _ =>
      tcbstat = Int.repr OS_STAT_MUTEX \/ tcbstat = Int.or (Int.repr OS_STAT_MUTEX) (Int.repr OS_STAT_SUSPEND)
    | DPort =>
      tcbstat = Int.repr OS_STAT_PORT \/ tcbstat = Int.or (Int.repr OS_STAT_PORT) (Int.repr OS_STAT_SUSPEND)
  end.

Definition OS_EventTaskPostRdyPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX msk vhold tcbls ptbl rtbl rgrp vltcb (*egrp*) pegrp qid osevent etbl petbl dd1 
  dd3 dd4 s head headprev tail tailnext absmq dd2' d2 d3 d4 d5 d6 d7 d8 d9 lg' er,
  Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr **  A_isr_is_prop ** Aier er **
  AEventNode (Vptr qid) osevent etbl petbl (DMsgQ dd1 (d2 :: d3 :: Vptr d4 :: d5 :: d6 :: Vint32 d7 :: Vint32 (d8 -ᵢ $ 1) :: Vptr (d9, Int.zero) :: nil) dd3 dd4) ** (*has pure properties*)
  <||s||> **
  AOSUnMapTbl **
  AOSMapTbl **
  AOSRdyTblGrp rtbl rgrp ** (*has pure properties*)
  GAarray OSTCBPrioTbl (Tarray (Tptr OS_TCB) 64) ptbl **
  tcbdllseg head headprev tail tailnext vltcb **

  [| ptr_in_tcblist (Vptr ct) head vltcb |] **
  [| array_type_vallist_match (Tptr OS_TCB) ptbl /\ length ptbl = 64%nat |] **
  [| RL_RTbl_PrioTbl_P rtbl ptbl vhold |] **
  [| R_PrioTbl_P ptbl tcbls vhold |] **
  [| R_ECB_ETbl_P qid ((osevent,etbl),petbl) tcbls |] **
  [| TCBList_P head vltcb rtbl tcbls |] **

  [| nth_val 0 vl = Some (Vptr qid) |] **
  [| nth_val 1 vl = Some (Vint32 msk) |] **
  
  [| V_OSPostEventGrp osevent = Some (Vint32 pegrp) /\ pegrp <> Int.zero |] **
  [| V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_Q))|] ** (*add*)
  [| R_ECB_PETbl_P qid ((osevent,etbl),petbl) tcbls |] ** (*add*)
  [| RLH_ECBData_P (DMsgQ dd1 dd2' dd3 dd4) absmq |] ** (*add*)
  [|Int.unsigned ((d8 -ᵢ $ 1) +ᵢ$ 1) <= Int16.max_unsigned |] **
  [| Int.unsigned ((d8 -ᵢ $ 1) +ᵢ$ 1) <= Int.unsigned d7 |] ** (* new add *)
  (* [| RLH_ECBData_P
         (DMsgQ (Vptr (z1, Int.zero))
            (z2z
             :: Vptr (z3, $ 4)
                :: Vptr (z3, Int.mul z4 ($ 4) +ᵢ  $ 4)
                   :: z5 :: Vptr (z3, z6) :: Vint32 z4 :: Vint32 z7 :: Vptr (z3, Int.zero) :: nil)
            (z8 :: z9 :: nil) z10) (z11, z12) |] ** *)
  [| logicl = logic_val (Vptr vhold) :: logic_val head ::
              logic_val headprev :: logic_val tail :: logic_val tailnext ::
              logic_lv ptbl :: logic_lv rtbl :: logic_val rgrp ::
              logic_lv osevent :: logic_lv etbl :: logic_lv petbl :: logic_leventd ((DMsgQ dd1 (d2 :: d3 :: Vptr d4 :: d5 :: d6 :: Vint32 d7 :: Vint32 (d8 -ᵢ $ 1) :: Vptr (d9, Int.zero) :: nil) dd3 dd4)::nil) ::
              logic_code s :: logic_abstcb tcbls :: logic_llv vltcb :: (*add petbl*)
              logic_val (Vint32 pegrp) :: logic_leventd ((DMsgQ dd1 dd2' dd3 dd4)::nil)  :: lg' |] **
    p_local OSLInv ct (logic_val (V$ 1) :: lg').
  
Theorem OS_EventTaskPostRdyPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_EventTaskPostRdyPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventTaskPostRdyPre : fpre :=
  fun vl ll ct => mkfunasrt (OS_EventTaskPostRdyPreGood vl ll ct).


Definition OS_EventTaskPostRdyPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX vhold tcbls vltcb vltcb' ptbl rtbl rtbl' rgrp rgrp' pegrp pegrp' etbl (* etbl' *) petbl petbl' qid osevent osevent' d d' s head headprev msg tail tailnext  msk
  (* d1 *) d2 d3 d4 d5 d5' d6 d7 d8 d9 (d10:val) d11 (* d12 *) d14 dd2' dd1 dd3 dd4
   lg' er,
    Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop ** Aier er **
    AEventNode (Vptr qid) osevent' etbl petbl' d' ** <||s||> **
    AOSUnMapTbl **
    AOSMapTbl **
    AOSRdyTblGrp rtbl' rgrp' **

    GAarray OSTCBPrioTbl (Tarray (Tptr OS_TCB) 64) ptbl **    
    tcbdllseg head headprev tail tailnext vltcb' **

    [| nth_val 0 vl = Some (Vptr qid) |] **
    [| nth_val 1 vl = Some (Vint32 msk) |] **
    
    [| ptr_in_tcblist (Vptr ct) head vltcb'|] **
    [| array_type_vallist_match (Tptr OS_TCB) ptbl /\ length ptbl = 64%nat |] ** (*same as in pre*)
    [| RL_RTbl_PrioTbl_P rtbl' ptbl vhold |] **
    [| R_PrioTbl_P ptbl tcbls vhold |] ** (*same as in pre*)
    [| R_ECB_ETbl_P qid ((osevent,etbl),petbl) tcbls |] ** (*same as in pre*)
    [| TCBList_P head vltcb rtbl tcbls |] ** (*same as in pre*)
    (* [| RLH_ECBData_P d'' absmq |] ** (*add*) *)
    [| V_OSPostEventGrp osevent = Some (Vint32 pegrp) /\ pegrp <> Int.zero |] **
    [| logicl = logic_val (Vptr vhold) :: logic_val head ::
                logic_val headprev :: logic_val tail :: logic_val tailnext ::
                logic_lv ptbl :: logic_lv rtbl :: logic_val rgrp ::
                logic_lv osevent :: logic_lv etbl :: logic_lv petbl:: logic_leventd (d::nil) ::
                logic_code s :: logic_abstcb tcbls :: logic_llv vltcb ::
                logic_val (Vint32 pegrp) ::logic_leventd ((DMsgQ dd1 dd2' dd3 dd4)::nil) :: lg' |] **
     (*add logic_lv petbl*)

    EX x y i1 bitx bity,
    [| nth_val' (Z.to_nat (Int.unsigned pegrp)) OSUnMapVallist = Vint32 y |] **
    [| nth_val' (Z.to_nat (Int.unsigned y)) petbl = Vint32 i1 |] **
    [| nth_val' (Z.to_nat (Int.unsigned i1)) OSUnMapVallist = Vint32 x |] **
    [| nth_val' (Z.to_nat (Int.unsigned y)) OSMapVallist = Vint32 bity |] **
    [| nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 bitx |] **
    
    (* osevent' etbl' egrp' *)
    (* osevent' = osevent set egrp to egrp'
       etbl' = etbl clear highest bit
       RL_Tbl_Grp_P etbl' egrp' (in AOSEvent)
     *)
    [| osevent' = update_nth_val 6 osevent (Vint32 pegrp') |] **
    [| petbl' = update_nth_val
                 (Z.to_nat (Int.unsigned y)) petbl (Vint32 (i1&ᵢInt.not bitx)) |] **
              
    (*ret value prio = get highest wait task in etbl*)
    [| v = Some (Vint32 ((y<<ᵢ$ 3)+ᵢx)) |] **

    (*relation between old vltcb and new vltcb*)
    (EX vl vl' next prev eptr dly stat prio tcbx tcby tcbbitx tcbbity t,
     [| nth_val' (Z.to_nat (Int.unsigned ((y<<ᵢ$ 3)+ᵢx))) ptbl  = (Vptr (t, Int.zero))
        /\ (t, Int.zero) <> vhold|] **
    [| tcblist_get (Vptr (t, Int.zero)) head vltcb = Some vl /\ struct_type_vallist_match OS_TCB_flag vl|] **
    [| vltcb' = set_node (Vptr (t, Int.zero)) vl' head vltcb |] **
    [| vl = next::prev::eptr::msg::dly::(Vint32 stat)::prio::tcbx::tcby::tcbbitx::tcbbity::nil|] **
    [| vl' = next::prev::Vnull::msg::(Vint32 Int.zero)::(Vint32 (Int.and stat (Int.not msk)))::prio::tcbx::tcby::tcbbitx::tcbbity::nil|] **
    [| d5 = Vptr (d9 , d14) |] **
(*     [| ( d5' = Vptr (d9 , d14 +ᵢ  Int.mul ($ 1) ($ 4)))  \/ ( d5' = d3 )|] ** *)
    [| (d9, d14 +ᵢ  Int.mul ($ 1) ($ 4)) = d4 /\ d5' = d3 \/
      (d9, d14 +ᵢ  Int.mul ($ 1) ($ 4)) <> d4 /\ d5' = Vptr (d9, d14 +ᵢ  Int.mul ($ 1) ($ 4)) |] **
    
    [| d = (DMsgQ dd1 (d2 :: d3 :: Vptr d4 :: d5 :: d6 :: Vint32 d7 :: Vint32 d8 :: Vptr (d9, Int.zero) :: nil) dd3 dd4)|]**
    [| d =  DMsgQ (dd1) (d2 :: d3 :: Vptr d4 :: d5 :: d6 :: Vint32 d7 :: Vint32 d8 :: Vptr (d9, Int.zero) :: nil)  (d10 :: d11 :: nil)  dd4|] **
    [| d' = DMsgQ (dd1) (d2 :: d3 ::Vptr d4 :: d5' :: d6 :: Vint32 d7 :: Vint32 (d8 +ᵢ  $ 1) :: Vptr (d9, Int.zero) :: nil)
 (d10 :: d11 :: nil) (update_nth_val (Z.to_nat ((Int.unsigned d14 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4)) dd4 msg) |] **

    (*relation between data and tcbstat, for proving tcb rdy*)
    [| rel_edata_tcbstat_postrdy d stat |]
    (* ) *) **
    
    (*rtbl' rgrp'*)
    (*rtbl' = rtbl set bit prio
      RL_Tbl_Grp_P rtbl' rgrp' *)
    (* ( *)EX i1', [| nth_val' (Z.to_nat (Int.unsigned y)) rtbl = Vint32 i1' |] **    
      [| rtbl' = (if Int.eq (Int.and stat (Int.not msk)) (Int.repr OS_STAT_RDY)
                         then update_nth_val (Z.to_nat (Int.unsigned y)) rtbl (Vint32 (Int.or i1' bitx))
                         else rtbl )|]) **
    
 (*pure properties on old values in AOSRdyTblGrp, keep them in the post condition *)
    [|RL_Tbl_Grp_P rtbl rgrp /\ prio_in_tbl ($ OS_IDLE_PRIO) rtbl|] **
    [|array_type_vallist_match Tint8 rtbl /\ length rtbl = nat_of_Z OS_RDY_TBL_SIZE|] **
    [|rule_type_val_match Tint8 rgrp = true|] **
    [|RL_Tbl_Grp_P petbl (Vint32 pegrp)|] **
    [|array_type_vallist_match Tint8 etbl|] **
    [|array_type_vallist_match Tint8 petbl|] **  (*add*)
    [|length petbl = ∘ OS_EVENT_TBL_SIZE|] (*add*)
    ** p_local OSLInv  ct (logic_val (V$ 1) :: lg').

Theorem OS_EventTaskPostRdyPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_EventTaskPostRdyPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventTaskPostRdyPost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_EventTaskPostRdyPostGood vl v ll ct).

Definition OS_EventTaskPostRdy_spec : fspec :=
  (OS_EventTaskPostRdyPre, OS_EventTaskPostRdyPost, (Tint8, (Tptr OS_EVENT) :: Tint16 :: nil)).



Definition WellformedOSQ0 (osq:vallist):=
  exists qstart qend qin qout qsize qtbl qblk, 
    V_OSQStart osq = Some (Vptr qstart) /\ 
    V_OSQEnd osq = Some (Vptr qend) /\ 
    V_OSQIn osq = Some (Vptr qin) /\
    V_OSQOut osq = Some (Vptr qout) /\
    V_OSQSize osq = Some (Vint32 qsize) /\
    V_qfreeblk osq = Some (Vptr qblk) /\
    id_addrval qblk msgqueuetbl OS_Q_FREEBLK = Some qtbl /\
    0 < Int.unsigned qsize <= OS_MAX_Q_SIZE /\ qstart = qtbl /\ 
    qend_right qend qtbl qsize /\
    arrayelem_addr_right qin qtbl qsize /\ 
    arrayelem_addr_right qout qtbl qsize. 



(* OS_EventTaskPostRdy *)
(* this spec is used for OS_EventTaskPostRdy when it is called from within OSQDel *) 
  
Definition OS_EventTaskPostRdyDelPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX msk vhold tcbls ptbl rtbl rgrp vltcb (*egrp*) pegrp qid osevent etbl petbl dd1 
     dd3 dd4 s head headprev tail tailnext (* absmq *) dd2 (* d2 d3 d4 d5 d6 d7 d8 d9 *) osq qblk lg' er,
    Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop ** Aier er **
    AOSEvent (Vptr qid) osevent etbl petbl **
    [| V_OSEventPtr osevent = Some dd1 |] ** 
    node dd1 osq OS_Q ** [|WellformedOSQ0 osq|] ** 
    [| V_qfreeblk osq = Some (Vptr qblk) |] ** 
    (* [| V_OSQIn osq = Some (Vptr qin) /\ V_qfreeblk osq = Some (Vptr qblk) /\ fst qin = fst qblk |] ** *)
    AOSQBlk (Vptr qblk) dd3 dd4 ** 
    <||s||> **
    AOSUnMapTbl **
    AOSMapTbl **
    AOSRdyTblGrp rtbl rgrp ** (*has pure properties*)
    GAarray OSTCBPrioTbl (Tarray (Tptr OS_TCB) 64) ptbl **
    tcbdllseg head headprev tail tailnext vltcb **

    [| ptr_in_tcblist (Vptr ct) head vltcb |] **
    [| array_type_vallist_match (Tptr OS_TCB) ptbl /\ length ptbl = 64%nat |] **
    [| RL_RTbl_PrioTbl_P rtbl ptbl vhold |] **
    [| R_PrioTbl_P ptbl tcbls vhold |] **
    [| R_ECB_ETbl_P qid ((osevent,etbl), petbl) tcbls |] **
    [| TCBList_P head vltcb rtbl tcbls |] **

    [| nth_val 0 vl = Some (Vptr qid) |] **
    [| nth_val 1 vl = Some (Vint32 msk) |] **
  
    [| V_OSPostEventGrp osevent = Some (Vint32 pegrp) /\ pegrp <> Int.zero |] **
    [| V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_Q))|] ** (*add*)
    [| R_ECB_PETbl_P qid ((osevent,etbl),petbl) tcbls |] ** (*add*)
    (* [| RLH_ECBData_P (DMsgQ dd1 dd2 dd3 dd4) absmq |] ** (*add*) *)
    (* [|Int.unsigned ((d8 -ᵢ $ 1) +ᵢ$ 1) <= Int16.max_unsigned |] ** *) 
    [| logicl = logic_val (Vptr vhold) :: logic_val head ::
                     logic_val headprev :: logic_val tail :: logic_val tailnext ::
                     logic_lv ptbl :: logic_lv rtbl :: logic_val rgrp ::
                     logic_lv osevent :: logic_lv etbl :: logic_lv petbl :: 
                     logic_code s :: logic_abstcb tcbls :: logic_llv vltcb :: (*add petbl*)
                     logic_val (Vint32 pegrp) :: logic_leventd ((DMsgQ dd1 dd2 dd3 dd4)::nil) :: lg' |] ** 
    p_local OSLInv ct (logic_val (V$ 1) :: lg').  
                     
  
Theorem OS_EventTaskPostRdyDelPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_EventTaskPostRdyDelPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventTaskPostRdyDelPre : fpre :=
  fun vl ll ct => mkfunasrt (OS_EventTaskPostRdyDelPreGood vl ll ct).


Definition OS_EventTaskPostRdyDelPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX vhold tcbls vltcb vltcb' ptbl rtbl rtbl' rgrp rgrp' pegrp pegrp' etbl (* etbl' *) petbl petbl' qid osevent osevent'
    s head headprev msg tail tailnext msk dd2 dd2' dd4' dd1 dd3 dd4 qblk lg' er,   
     
    Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop ** Aier er **
    (* AEventNode (Vptr qid) osevent' etbl petbl' d' **  *)
    AOSEvent (Vptr qid) osevent' etbl petbl' **
    [| V_OSEventPtr osevent' = Some dd1 |] ** 
    [| V_OSEventType osevent' = Some (V$ OS_EVENT_TYPE_Q) |] ** 
    node dd1 dd2' OS_Q ** [|WellformedOSQ0 dd2'|] **
    [| V_qfreeblk dd2' = Some (Vptr qblk) |] **
    AOSQBlk (Vptr qblk) dd3 dd4' **  
    <||s||> **
    AOSUnMapTbl **
    AOSMapTbl **
    AOSRdyTblGrp rtbl' rgrp' **

    GAarray OSTCBPrioTbl (Tarray (Tptr OS_TCB) 64) ptbl **    
    tcbdllseg head headprev tail tailnext vltcb' **

    [| nth_val 0 vl = Some (Vptr qid) |] **
    [| nth_val 1 vl = Some (Vint32 msk) |] **
    
    [| ptr_in_tcblist (Vptr ct) head vltcb'|] **
    [| array_type_vallist_match (Tptr OS_TCB) ptbl /\ length ptbl = 64%nat |] ** (*same as in pre*)
    [| RL_RTbl_PrioTbl_P rtbl' ptbl vhold |] **
    [| R_PrioTbl_P ptbl tcbls vhold |] ** (*same as in pre*)
    [| R_ECB_ETbl_P qid ((osevent, etbl), petbl) tcbls |] ** (*same as in pre*)
    [| TCBList_P head vltcb rtbl tcbls |] ** (*same as in pre*)
    (* [| RLH_ECBData_P d'' absmq |] ** (*add*) *)
    [| V_OSPostEventGrp osevent = Some (Vint32 pegrp) /\ pegrp <> Int.zero |] **
    [| logicl = logic_val (Vptr vhold) :: logic_val head ::
                logic_val headprev :: logic_val tail :: logic_val tailnext ::
                logic_lv ptbl :: logic_lv rtbl :: logic_val rgrp ::
                logic_lv osevent :: logic_lv etbl :: logic_lv petbl:: (* logic_leventd (d::nil) :: *)
                logic_code s :: logic_abstcb tcbls :: logic_llv vltcb ::
                logic_val (Vint32 pegrp) :: logic_leventd ((DMsgQ dd1 dd2 dd3 dd4)::nil) :: lg' |] ** (*add logic_lv petbl*)

    EX x y i1 bitx bity,
    [| nth_val' (Z.to_nat (Int.unsigned pegrp)) OSUnMapVallist = Vint32 y |] **
    [| nth_val' (Z.to_nat (Int.unsigned y)) petbl = Vint32 i1 |] **
    [| nth_val' (Z.to_nat (Int.unsigned i1)) OSUnMapVallist = Vint32 x |] **
    [| nth_val' (Z.to_nat (Int.unsigned y)) OSMapVallist = Vint32 bity |] **
    [| nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 bitx |] **
    
    (* osevent' etbl' egrp' *)
    (* osevent' = osevent set egrp to egrp'
       etbl' = etbl clear highest bit
       RL_Tbl_Grp_P etbl' egrp' (in AOSEvent)
     *)
    [| osevent' = update_nth_val 6 osevent (Vint32 pegrp') |] **
    [| petbl' = update_nth_val
                 (Z.to_nat (Int.unsigned y)) petbl (Vint32 (i1&ᵢInt.not bitx)) |] **
              
    (*ret value prio = get highest wait task in etbl*)
    [| v = Some (Vint32 ((y<<ᵢ$ 3)+ᵢx)) |] **

    (*relation between old vltcb and new vltcb*)
    (EX vl vl' next prev eptr dly stat prio tcbx tcby tcbbitx tcbbity t,
      [| nth_val' (Z.to_nat (Int.unsigned ((y<<ᵢ$ 3)+ᵢx))) ptbl  = (Vptr (t, Int.zero))
          /\ (t, Int.zero) <> vhold |] **
      [| tcblist_get (Vptr (t, Int.zero)) head vltcb = Some vl /\ struct_type_vallist_match OS_TCB_flag vl|] **
      [| vltcb' = set_node (Vptr (t, Int.zero)) vl' head vltcb |] **
      [| vl = next::prev::eptr::msg::dly::(Vint32 stat)::prio::tcbx::tcby::tcbbitx::tcbbity::nil|] **
      [| vl' = next::prev::Vnull::msg::(Vint32 Int.zero)::(Vint32 (Int.and stat (Int.not msk)))::prio::tcbx::tcby::tcbbitx::tcbbity::nil|] **

      (*relation between data and tcbstat, for proving tcb rdy*)
      (* [| rel_edata_tcbstat_postrdy d stat |] *)
      [| stat = $OS_STAT_POSTQ \/ stat = ( Int.or ($ OS_STAT_POSTQ) ($ OS_STAT_SUSPEND)) |] 
    (* )  *) **
    
    (*rtbl' rgrp'*)
    (*rtbl' = rtbl set bit prio
      RL_Tbl_Gr    p_P rtbl' rgrp' *)
    (* ( *)EX i1', [| nth_val' (Z.to_nat (Int.unsigned y)) rtbl = Vint32 i1' |] **    
                 [| rtbl' = (if Int.eq (Int.and stat (Int.not msk)) (Int.repr OS_STAT_RDY)
                                     then update_nth_val (Z.to_nat (Int.unsigned y)) rtbl (Vint32 (Int.or i1' bitx))
                                      else rtbl )|]) ** 
    
    (*pure properties on old values in AOSRdyTblGrp, keep them in the post condition *)
    [|RL_Tbl_Grp_P rtbl rgrp /\ prio_in_tbl ($ OS_IDLE_PRIO) rtbl|] **
    [|array_type_vallist_match Tint8 rtbl /\ length rtbl = nat_of_Z OS_RDY_TBL_SIZE|] **
    [|rule_type_val_match Tint8 rgrp = true|] **
    [|RL_Tbl_Grp_P petbl (Vint32 pegrp)|] **
    [|array_type_vallist_match Tint8 etbl|] **
    [|array_type_vallist_match Tint8 petbl|] **  (*add*)
    [|length petbl = ∘ OS_EVENT_TBL_SIZE|] ** (*add*)
    p_local OSLInv ct (logic_val (V$ 1) :: lg').  


Theorem OS_EventTaskPostRdyDelPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_EventTaskPostRdyDelPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventTaskPostRdyDelPost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_EventTaskPostRdyDelPostGood vl v ll ct).

Definition OS_EventTaskPostRdy_qdel_spec : fspec :=
  (OS_EventTaskPostRdyDelPre,
   OS_EventTaskPostRdyDelPost, (Tint8, (Tptr OS_EVENT) :: Tint16 :: nil)).  


(* OS_EventTaskPostWait *)
(* pre *)
Definition OS_EventTaskPostWaitPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX tcbcur rtbl rgrp qid msg osevent etbl petbl d s ptrv er,
   <||s||> ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** Aier er **
    GV OSTCBCur @ Tptr OS_TCB |-r-> (Vptr ct) **
    node (Vptr ct) tcbcur OS_TCB_flag ** (*modified by zhanghui*)  (* OSTCBCur node *)
    [| RL_TCBblk_P tcbcur |] **
      AOSRdyTblGrp rtbl rgrp ** AEventNode (Vptr qid) osevent etbl petbl d **
    [| logicl =logic_lv rtbl :: logic_val rgrp :: logic_lv tcbcur :: logic_lv osevent ::
                logic_lv etbl :: logic_lv petbl ::logic_leventd (d::nil) :: logic_code s :: logic_val ptrv :: nil |] **(*change*)
    [| nth_val 0 vl = Some (Vptr qid) /\ (exists p,V_OSTCBPrio tcbcur = Some (Vint32 p) /\ Int.eq p ($ OS_IDLE_PRIO) = false) |] **
    [| nth_val 1 vl = Some  msg |] ** (*add*)
     p_local OSLInv ct (  logic_val (V$ 1)
                     :: logic_val (V$ __EvLoc_normal)
                     :: logic_val Vnull :: logic_val Vnull :: logic_val ptrv :: nil).


Theorem OS_EventTaskPostWaitPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_EventTaskPostWaitPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventTaskPostWaitPre : fpre :=
  fun vl ll ct => mkfunasrt (OS_EventTaskPostWaitPreGood vl ll ct).

(* post *)
Definition OS_EventTaskPostWaitPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:= 
  (EX tcbcur rtbl rgrp qid msg osevent etbl petbl d
     tcbcur' rtbl' rgrp' osevent' petbl'
     y bitx bity ry ey pegrp s ptrv er,
  Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** Aier er **
    GV OSTCBCur @ Tptr OS_TCB |-r-> (Vptr ct) **
    node (Vptr ct) tcbcur' OS_TCB_flag (*modified by zhanghui*) ** (* OSTCBCur node *) 
    AOSRdyTblGrp rtbl' (Vint32 rgrp') ** AEventNode (Vptr qid) osevent' etbl petbl' d **
    <||s||> **
    [| logicl = logic_lv rtbl :: logic_val (Vint32 rgrp) :: logic_lv tcbcur :: logic_lv osevent ::
                logic_lv etbl ::logic_lv petbl :: logic_leventd (d::nil) :: logic_code s :: logic_val ptrv :: nil |] **
    [| nth_val 0 vl = Some (Vptr qid) |] **
    [| nth_val 1 vl = Some  msg |] **
    [| tcbcur' = update_nth_val 3 (update_nth_val 2 tcbcur (Vptr qid) ) ( msg) /\ (*change*)
       V_OSTCBY tcbcur = Some (Vint32 y) /\
       V_OSTCBBitX tcbcur = Some (Vint32 bitx) /\
       V_OSTCBBitY tcbcur = Some (Vint32 bity) /\
       nth_val (nat_of_Z (Int.unsigned y)) rtbl = Some (Vint32 ry) /\
       rtbl' = update_nth_val (nat_of_Z (Int.unsigned y)) rtbl (Vint32 (Int.and ry (Int.not bitx))) /\
       nth_val (nat_of_Z (Int.unsigned y)) petbl = Some (Vint32 ey) /\ 
       petbl' = update_nth_val (nat_of_Z (Int.unsigned y)) petbl (Vint32 (Int.or ey bitx)) /\
       V_OSPostEventGrp osevent = Some (Vint32 pegrp) /\
       osevent' = update_nth_val 6 osevent (Vint32 (Int.or pegrp bity)) |] **
        p_local OSLInv  ct (  logic_val (V$ 1)
                     :: logic_val (V$ __EvLoc_normal)
                     :: logic_val Vnull :: logic_val Vnull :: logic_val ptrv :: nil) ).

Theorem OS_EventTaskPostWaitPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_EventTaskPostWaitPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventTaskPostWaitPost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_EventTaskPostWaitPostGood vl v ll ct).
 

Definition OS_EventTaskPostWait_spec : fspec :=
  (OS_EventTaskPostWaitPre, OS_EventTaskPostWaitPost, (Tvoid, (Tptr OS_EVENT) :: (Tptr Void) :: nil)).


(* OSSemAccept *) 

Definition OSSemAcceptPre' (vl:vallist) (logicl:list logicvar) ct :=
  EX s ptrv v' er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v' :: logic_code s :: logic_val ptrv :: nil |] **
       <|| (semacc (vl++(v' ::nil)));; s ||> **  
       [| nth_val 0 vl = Some ptrv |] **
       p_local OSLInv ct 
          (logic_val (V$ 1)
                     :: logic_val (V$ __EvLoc_normal)
                     :: logic_val Vnull :: logic_val ptrv :: logic_val Vnull :: nil)). 

Theorem OSSemAcceptPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSSemAcceptPre' vl ll ct).
Proof.
  simpl.
  tauto.
Qed.

Definition OSSemAcceptPre : fpre :=
  fun vl ll ct => mkfunasrt (OSSemAcceptPreGood vl ll ct).

Definition OSSemAcceptPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v' k ptrv er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v' :: logic_code s :: logic_val ptrv :: nil |] **
       [| v = Some v' /\ v' = Vint32 k  /\ 
          Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k) (Int16.max_unsigned) |] ** 
       <|| s ||> **
       [| nth_val' 0 vl = Vnull -> k = Int.zero |] ** 
       p_local OSLInv ct
       (logic_val (V$ 1)
                  :: logic_val (V$ __EvLoc_normal)
                  :: logic_val Vnull :: logic_val ptrv :: logic_val Vnull :: nil)).

Theorem OSSemAcceptPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSSemAcceptPost' vl v ll ct).
Proof.
  simpl.
  tauto.
Qed.

Definition OSSemAcceptPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSSemAcceptPostGood vl v ll ct).

Definition OSSemAccept_spec : fspec:= (OSSemAcceptPre,OSSemAcceptPost,(Tint16, Tptr OS_EVENT::nil)).


(* OSSemCreate *)

Definition OSSemCreatePre' (vl:vallist) (logicl:list logicvar) ct :=
  EX s v' er,
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
      [| logicl = logic_val v' :: logic_code s :: nil |] **
      <|| (semcre (vl++(v' ::nil)));; s ||> **
      p_local OSLInv ct init_lg).

Theorem OSSemCreatePreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSSemCreatePre' vl ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSSemCreatePre : fpre :=
  fun vl ll ct => mkfunasrt (OSSemCreatePreGood vl ll ct).

Definition OSSemCreatePost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v' ptrv vloc er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
      [| logicl = logic_val v' :: logic_code s :: nil |] **
      [| v = Some v' /\ isptr v' /\ v' = ptrv |] ** 
      [| v' = Vnull /\ (vloc = Vint32 ($__EvLoc_normal) \/ vloc = Vint32 ($__EvLoc_ecbcre1)) \/
          v' <> Vnull /\ vloc = Vint32 ($__EvLoc_ecbcre2) /\ (exists eid, v'= Vptr eid /\ notIncoreSemQ eid) |] **
      <|| s ||> ** 
      p_local OSLInv ct (logic_val (V$ 1)
                                   :: logic_val vloc 
                                   :: logic_val Vnull :: logic_val ptrv :: logic_val Vnull :: nil)).


Theorem OSSemCreatePostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSSemCreatePost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSSemCreatePost : fpost :=
  fun vl v ll ct => mkfunasrt (OSSemCreatePostGood vl v ll ct).

Definition OSSemCreate_spec : fspec:= (OSSemCreatePre,OSSemCreatePost,(Tptr OS_EVENT, Int16u::nil)).

(* OSSemDel *)

Definition OSSemDelPre' (vl: vallist) (logicl: list logicvar) ct :=  
  EX s (* els *) tcbls pevent_blk elptr etbl letbl i1 x10 x11 
     v'22 v'23 v'43 v'44 v'45 v'46 v' tid v'3 pegrp petbl_addr lpetbl petbl er,
  (Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop ** Aier er **
       [| logicl = logic_code s :: logic_val (Vptr (pevent_blk, Int.zero)) ::
                              logic_val (Vint32 i1) :: logic_val x10 :: logic_val x11 :: logic_val elptr ::
                              logic_val (Vint32 pegrp) :: logic_val petbl_addr :: (* new add *)
                              logic_val (Vptr letbl) :: logic_lv etbl ::
                              logic_val (Vptr lpetbl) :: logic_lv petbl :: (* new add *)
                              logic_val v'23 :: 
                              logic_leventc v'43 :: logic_leventc v'44 :: logic_leventd v'45 :: logic_leventd v'46 ::
                              logic_val (Vptr tid) ::
                              logic_val v'22 :: logic_llv v' :: nil |] ** 
       [| vl = (Vptr (pevent_blk, Int.zero)) :: nil |] **
       <|| s ||> **   
       Astruct (pevent_blk,Int.zero) OS_EVENT (V$ OS_EVENT_TYPE_SEM :: V$ 0 :: Vint32 i1 :: x10 :: x11 :: elptr :: Vint32 pegrp :: petbl_addr :: nil) ** 
       Aarray letbl (Tarray char_t ∘ OS_EVENT_TBL_SIZE) etbl **
       Aarray lpetbl (Tarray char_t ∘ OS_EVENT_TBL_SIZE) petbl **
       evsllseg v'23 (Vptr (pevent_blk, Int.zero)) v'43 v'45 **
       evsllseg elptr Vnull v'44 v'46 **
       GV OSEventList @ OS_EVENT ∗ |-> v'23 **
       AOSEventFreeList v'22 v' **
       (* HECBList els ** *)
       HCurTCB tid **
       (* AGVars ** *)
       p_local OSLInv ct init_lg **
       GV OSIntNesting @ long |-> Vint32 v'3 **
       [|Int.ltu ($ 0) v'3 = false |] **
       (* [| RH_TCBList_ECBList_P els tcbls tid |] **  *)
       [| RH_CurTCB tid tcbls |] ** 
       [| id_addrval' (Vptr (pevent_blk, Int.zero)) OSEventTbl OS_EVENT = Some letbl |] ** 
       [| length etbl = ∘ OS_EVENT_TBL_SIZE |] ** 
       [| array_type_vallist_match char_t etbl |] ** 
       [| RL_Tbl_Grp_P etbl (V$ 0) |] ** 
       [| Int.unsigned i1 <= 65535 |] ** 
       [| isptr v'23 |] **
       [| isptr x10 |] **
       [| Int.unsigned pegrp <= Byte.max_unsigned |] ** 
       [| id_addrval' (Vptr (pevent_blk, Int.zero)) OSPostEventTbl OS_EVENT = Some lpetbl |] ** 
       [| RL_Tbl_Grp_P petbl (Vint32 pegrp) |] **
       [| array_type_vallist_match Int8u petbl |] ** 
       [| length petbl = ∘ OS_EVENT_TBL_SIZE |] ). 

Theorem OSSemDelPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSSemDelPre' vl ll ct).
Proof.
try GoodFunAsrt_solver.
Qed.

Definition OSSemDelPre : fpre :=
  fun vl ll ct => mkfunasrt (OSSemDelPreGood vl ll ct). 

Definition OSSemDelPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s (* els *) pevent_blk letbl etbl elptr x10 x11
     v'22 v'23 v'24 v'43 v'' v'44 v'45 v'46 i1 v'16 tid pegrp petbl_addr lpetbl petbl er, 
    (Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop ** Aier er **
         [| logicl = logic_code s :: logic_val (Vptr (pevent_blk, Int.zero)) :: 
                                logic_val (Vint32 i1) :: logic_val x10 :: logic_val x11 :: logic_val elptr :: 
                                logic_val (Vint32 pegrp) :: logic_val petbl_addr :: (* new add *)
                                logic_val (Vptr letbl) :: logic_lv etbl ::
                                logic_val (Vptr lpetbl) :: logic_lv petbl :: (* new add *)
                                logic_val v'23 :: 
                                logic_leventc v'43 :: logic_leventc v'44 :: logic_leventd v'45 :: logic_leventd v'46 ::
                                logic_val (Vptr tid) :: 
                                logic_val v'22 :: logic_llv v'16 :: nil |] **  
         [|  v = Some Vnull |] **  
         <|| s ||> **
         GV OSEventFreeList @ OS_EVENT ∗ |-> Vptr (pevent_blk, Int.zero) **
         Astruct (pevent_blk, Int.zero) OS_EVENT
         (V$ OS_EVENT_TYPE_UNUSED :: V$ 0 :: Vint32 i1 :: x10 :: x11 :: v'22 ::  Vint32 pegrp :: petbl_addr :: nil) **
         Aarray letbl (Tarray char_t ∘ OS_EVENT_TBL_SIZE) etbl **
         Aarray lpetbl (Tarray char_t ∘ OS_EVENT_TBL_SIZE) petbl **
         GV OSEventList @ OS_EVENT ∗ |-> v'24 **
         evsllseg v'24 Vnull (v'' ++ v'44) (v'45 ++ v'46) **
         ecbf_sllseg v'22 Vnull v'16 OS_EVENT (fun vl : vallist => nth_val 5 vl) **
         (* HECBList els ** *) HCurTCB tid ** (* AGVars **  *)
         p_local OSLInv ct init_lg ** 
         AOSIntNesting **
         [| v'43 <> nil ->
            v'24 = v'23 /\
            Some (Vptr (pevent_blk, Int.zero)) = get_last_ptr v'43 /\ v'' = upd_last_ectrls v'43 elptr |] **
         [| v'43 = nil -> Vptr (pevent_blk, Int.zero) = v'23 /\ v'24 = elptr /\ v'' = nil |] **
         [| isptr x10 |] **
         [| isptr elptr |] **
         [| isptr v'22 |] ** 
         [| isptr v'24 |]).  

Theorem OSSemDelPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt ( OSSemDelPost' vl v ll ct).
Proof.
try GoodFunAsrt_solver.
Qed.

Definition OSSemDelPost : fpost :=
  fun vl v ll ct => mkfunasrt ( OSSemDelPostGood vl v ll ct).

Definition OSSemDel_spec : fspec:= (OSSemDelPre,OSSemDelPost,(Tptr OS_EVENT, Tptr OS_EVENT:: (* Int8u :: *)nil)).

(* OSSemPend *)

Definition OSSemPendPre' (vl:vallist) (logicl:list logicvar) ct :=
  EX s ptrv v' er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v' :: logic_code s :: logic_val ptrv :: nil |] ** 
       <|| spec_code_cons (sem_pend (vl ++ (v' :: nil))) s ||> **
       [| nth_val 0 vl = Some ptrv |] ** 
       p_local OSLInv ct
           (logic_val (V$ 1)
                      :: logic_val (V$ __EvLoc_normal)
                      :: logic_val Vnull :: logic_val ptrv :: logic_val Vnull :: nil)). 

Theorem OSSemPendPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSSemPendPre' vl ll ct). 
Proof.
  simpl.
  tauto.
Qed.

Definition OSSemPendPre : fpre :=
  fun vl ll ct => mkfunasrt (OSSemPendPreGood vl ll ct).

Definition OSSemPendPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v' k ptrv er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v' :: logic_code s :: logic_val ptrv :: nil |] ** 
       [| v = Some v' /\ v' = Vint32 k  /\ 
          Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k) (Byte.max_unsigned) |] ** 
       <|| s ||> **
       [| nth_val' 0 vl = Vnull -> Int.ltu Int.zero k = true |] ** 
       p_local OSLInv ct
           (logic_val (V$ 1) 
                      :: logic_val (V$ __EvLoc_normal)
                      :: logic_val Vnull :: logic_val ptrv :: logic_val Vnull :: nil)). 

Theorem OSSemPendPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSSemPendPost' vl v ll ct).
Proof.
  simpl.
  tauto.
Qed.

Definition OSSemPendPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSSemPendPostGood vl v ll ct).

Definition OSSemPend_spec : fspec:= (OSSemPendPre,OSSemPendPost,(Tint8, Tptr OS_EVENT::Tint16::nil)).


(* OSSemPost *)

Definition OSSemPostPre' (vl: vallist) (logicl: list logicvar) ct :=  
  EX s ptrv v' er,  
  (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v' :: logic_code s :: logic_val ptrv :: nil |] ** 
       <|| spec_code_cons (sem_post (vl ++ (v' :: nil))) s ||> **   
       [| nth_val 0 vl = Some ptrv |] ** 
       p_local OSLInv ct
           (logic_val (V$ 1)
                      :: logic_val (V$ __EvLoc_normal)
                      :: logic_val Vnull :: logic_val ptrv :: logic_val Vnull :: nil)). 

Theorem OSSemPostPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSSemPostPre' vl ll ct).
Proof.
  try GoodFunAsrt_solver.
Qed.

Definition OSSemPostPre : fpre :=
  fun vl ll ct => mkfunasrt ( OSSemPostPreGood vl ll ct).

Definition OSSemPostPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v' ptrv k er,  
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
         [| logicl = logic_val v' :: logic_code s :: logic_val ptrv :: nil |] **  
         [| v = Some v' /\ v' = Vint32 k /\
            Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k) (Byte.max_unsigned) |] **  
         <|| s ||> **
         [| nth_val' 0 vl = Vnull -> Int.ltu Int.zero k = true |] **
         p_local OSLInv ct
             (logic_val (V$ 1) 
                    :: logic_val (V$ __EvLoc_normal)
                    :: logic_val Vnull :: logic_val ptrv :: logic_val Vnull :: nil)). 

Theorem OSSemPostPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt ( OSSemPostPost' vl v ll ct).
Proof.
  try GoodFunAsrt_solver.
Qed.

Definition OSSemPostPost : fpost :=
  fun vl v ll ct => mkfunasrt ( OSSemPostPostGood vl v ll ct).

Definition OSSemPost_spec : fspec:= (OSSemPostPre,OSSemPostPost,(Int8u, Tptr OS_EVENT::nil)). 

(* OSSemPostBin *)

Definition OSSemPostBinPre' (vl: vallist) (logicl: list logicvar) ct :=  
  EX s ptrv v' er, 
  (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v' :: logic_code s :: logic_val ptrv :: nil |] ** 
       <|| spec_code_cons (sem_post_bin (vl ++ (v' :: nil))) s ||> **   
       [| nth_val 0 vl = Some ptrv |] ** 
       p_local OSLInv ct 
           (logic_val (V$ 1)
                      :: logic_val (V$ __EvLoc_normal)
                      :: logic_val Vnull :: logic_val ptrv :: logic_val Vnull :: nil)). 

Theorem OSSemPostBinPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSSemPostBinPre' vl ll ct).
Proof.
  try GoodFunAsrt_solver.
Qed.

Definition OSSemPostBinPre : fpre :=
  fun vl ll ct => mkfunasrt (OSSemPostBinPreGood vl ll ct).

Definition OSSemPostBinPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v' ptrv k er,  
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
         [| logicl = logic_val v' :: logic_code s :: logic_val ptrv :: nil |] **  
         [| v = Some v' /\ v' = Vint32 k /\
              Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k) (Byte.max_unsigned) |] **  
         <|| s ||> **
         [| nth_val' 0 vl = Vnull -> Int.ltu Int.zero k = true |] ** 
         p_local OSLInv ct
             (logic_val (V$ 1) 
                      :: logic_val (V$ __EvLoc_normal)
                      :: logic_val Vnull :: logic_val ptrv :: logic_val Vnull :: nil)). 

Theorem OSSemPostBinPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSSemPostBinPost' vl v ll ct).
Proof.
try GoodFunAsrt_solver.
Qed.

Definition OSSemPostBinPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSSemPostBinPostGood vl v ll ct).

Definition OSSemPostBin_spec : fspec:= (OSSemPostBinPre,OSSemPostBinPost,(Int8u, Tptr OS_EVENT::nil)). 

(* OSIPCSemPost *)

Definition OSIPCSemPostPre' (vl: vallist) (logicl: list logicvar) ct :=  
  EX s ptrv v' is isr er vnest vlock,
  (Aie false ** Ais is ** Acs nil ** Aisr isr ** A_isr_is_prop ** Aier er **
       <|| spec_code_cons (sem_post_ipc (vl ++ (v' :: nil))) s ||> **
       [| nth_val 0 vl = Some ptrv |] **
       p_local OSLInv ct init_lg **
       (* used for OS_Sched *)
       GV OSIntNesting @ Tint32 |-> Vint32 vnest **
       GV OSLockNesting @ Tint32 |-> Vint32 vlock **
       [| Int.eq vnest Int.zero = false |] **
      (* precondition used for OSSemPost *)
       (([| ptrv = Vnull |] **
          [| logicl = logic_val v' :: logic_code s :: logic_val ptrv ::
                         (logic_isr isr) :: (logic_ier er) :: (logic_is is) :: nil |]) \\//
         (EX eid ecbls p1 p2 tcbl1 tcbcur tcbl2 tcbls vhold scapl mcapl qcapl rtbl rgrp ptbl ptls t ct,
          [| ptrv =  Vptr eid |] **
          [| exists d, EcbMod.get ecbls eid = Some d |] **
            EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
           AOSUnMapTbl **
           AOSMapTbl **
           AOSRdyTblGrp rtbl rgrp **
           AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold **
           AOSTCBList p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
           HTCBList tcbls ** HTime t ** HCurTCB ct **
           [| RH_TCBList_ECBList_P ecbls tcbls ct|] **
           [| RH_CurTCB ct tcbls|] **
           [| logicl = logic_val v' :: logic_code s :: logic_val ptrv ::
                         (logic_isr isr) :: (logic_ier er) :: (logic_is is) :: 
                         (logic_abstcb tcbls) :: (logic_absecb ecbls) :: (logic_val (Vptr ct)) ::
                         (logic_val p1) :: (logic_val p2) ::  (logic_lv rtbl) :: (logic_val rgrp) ::
                         (logic_llv tcbl1) :: (logic_lv tcbcur) :: (logic_llv tcbl2) :: nil |]))).

Theorem OSIPCSemPostPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSIPCSemPostPre' vl ll ct).
Proof.
  try GoodFunAsrt_solver.
  unfold GoodFunAsrt.
  fold GoodFunAsrt.
  intros. apply GoodFunAsrt_err_sllseg.
  unfold GoodFunAsrt.
  fold GoodFunAsrt.
  intros. apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition OSIPCSemPostPre : fpre :=
  fun vl ll ct => mkfunasrt ( OSIPCSemPostPreGood vl ll ct).

Definition OSIPCSemPostPost' (vl: vallist) (v:option val) (logicl: list logicvar) ct :=  
  EX s ptrv v' is isr er vnest vlock tp,
  (Aie false ** Ais is ** Acs nil ** Aisr isr ** A_isr_is_prop ** Aier er **
       <|| s ||> **
       [| nth_val 0 vl = Some ptrv |] **
       [| v = Some v'  /\ v' = Vint32 tp  /\ Int.unsigned tp <= Byte.max_unsigned |] **
       p_local OSLInv ct init_lg **
       (* used for OS_Sched *)
       GV OSIntNesting @ long |-> Vint32 vnest **
       GV OSLockNesting @ long |-> Vint32 vlock **
       [| Int.eq vnest Int.zero = false |] **
      (* postcondition used for OSSemPost *)
       (([| ptrv = Vnull |] **
          [| logicl = logic_val v' :: logic_code s :: logic_val ptrv ::
                         (logic_isr isr) :: (logic_ier er) :: (logic_is is) :: nil |] **
          [| v' = (V$ OS_ERR_PEVENT_NULL) |]) \\// (* case: empty pevent *)
         (EX eid ecbls p1 p2 tcbl1 tcbcur tcbl2 tcbls vhold scapl mcapl qcapl rtbl rgrp ptbl ptls t ct
                 ecbls' tcbls' tcbvl tcbl1' tcbcur' tcbl2' rtbl' rgrp',
          [| ptrv =  Vptr eid |] **
          [| exists d, EcbMod.get ecbls eid = Some d |] **
           EvtInv ecbls' p1 tcbvl tcbls' vhold scapl mcapl qcapl **
           AOSUnMapTbl **
           AOSMapTbl **
           AOSRdyTblGrp rtbl' rgrp' **
           AOSTCBPrioTbl ptbl rtbl' tcbls' ptls vhold **
           AOSTCBList p1 p2 tcbl1' (tcbcur'::tcbl2') rtbl' ct tcbls' **
           HTCBList tcbls' ** HTime t ** HCurTCB ct **
           [| RH_TCBList_ECBList_P ecbls' tcbls' ct|] **
           [| RH_CurTCB ct tcbls' |] **
           [| logicl = logic_val v' :: logic_code s :: logic_val ptrv ::
                         (logic_isr isr) :: (logic_ier er) :: (logic_is is) :: 
                         (logic_abstcb tcbls) :: (logic_absecb ecbls) :: (logic_val (Vptr ct)) ::
                         (logic_val p1) :: (logic_val p2) ::  (logic_lv rtbl) :: (logic_val rgrp) ::
                         (logic_llv tcbl1) :: (logic_lv tcbcur) :: (logic_llv tcbl2) :: nil |] **
           [| tcbvl = (tcbl1' ++ (tcbcur'::tcbl2')) |] **
           [| (
                 ( ~(exists n wls, EcbMod.get ecbls eid = Some (abssem n, wls)) /\
                   ecbls' = ecbls /\  tcbls' = tcbls /\
                   tcbl1' = tcbl1 /\ tcbcur' = tcbcur /\ tcbl2' = tcbl2 /\
                   rtbl' = rtbl /\ rgrp' = rgrp /\ 
                   v' = (V$ OS_ERR_EVENT_TYPE)) (* case: wrong type *)
                 \/ ( exists n, EcbMod.get ecbls eid = Some (abssem n, nil) /\
                                        Int.ltu n ($ 65535) = false /\
                         ecbls' = ecbls /\  tcbls' = tcbls /\
                         tcbl1' = tcbl1 /\ tcbcur' = tcbcur /\ tcbl2' = tcbl2 /\
                         rtbl' = rtbl /\ rgrp' = rgrp /\ 
                         v' = (V$ OS_SEM_OVF)  ) (* case:  sem overflow *)
                 \/ (exists n, EcbMod.get ecbls eid = Some (abssem n, nil) /\
                                       Int.ltu n ($ 65535) = true /\
                         ecbls' = EcbMod.set ecbls eid (abssem (Int.add n Int.one), nil) /\
                         tcbls' = tcbls /\
                         tcbl1' = tcbl1 /\ tcbcur' = tcbcur /\ tcbl2' = tcbl2 /\
                         rtbl' = rtbl /\ rgrp' = rgrp /\ 
                         v' = (V$ OS_NO_ERR)) (* case: post sem success *)
                 \/ (exists n wls tid p t_opt m sus,
                         EcbMod.get ecbls eid = Some (abssem n, wls) /\ wls <> nil /\
                         GetHWait tcbls wls tid /\
                         TcbMod.get tcbls tid = Some (p, wait (os_stat_sem eid) t_opt, m, sus) /\
                         ecbls' = EcbMod.set ecbls eid (abssem n, remove_tid tid wls) /\
                         tcbls' = TcbMod.set tcbls tid (p, rdy,Vnull, sus) /\
                         (* changed value because of OS_EventTaskRdy *)
                         exists next prev wt tcbx tcby tcbbitx tcbbity,
                         exists bitx bity vl vl' i1 stat,
                         p = ((tcby<<ᵢ$ 3)+ᵢtcbx) /\
                         nth_val' (Z.to_nat (Int.unsigned tcby)) OSMapVallist = Vint32 bity /\
                         nth_val' (Z.to_nat (Int.unsigned tcbx)) OSMapVallist = Vint32 bitx /\
                         (* new OSTCBList  *)
                         nth_val' (Z.to_nat (Int.unsigned p)) ptbl  = (Vptr tid) /\ tid <> vhold /\
                         tcblist_get (Vptr tid) p1 (tcbl1 ++ (tcbcur::tcbl2)) = Some vl /\
                         tcbvl = set_node (Vptr tid) vl' p1 (tcbl1 ++ (tcbcur::tcbl2)) /\
                         vl = (next::prev::(Vptr eid)::m::(Vint32 wt)::(Vint32 stat)::(Vint32 p)::(Vint32 tcbx)::(Vint32 tcby)::tcbbitx::tcbbity::nil)%list /\
                         vl' = (next::prev::Vnull::Vnull::(Vint32 Int.zero)::(Vint32 (Int.and stat (Int.not ($ OS_STAT_SEM))))::(Vint32 p)::(Vint32 tcbx)::(Vint32 tcby)::tcbbitx::tcbbity::nil)%list /\
                        (* new OSRdyTbl *)
                         nth_val' (Z.to_nat (Int.unsigned tcby)) rtbl = Vint32 i1 /\
                         rtbl' = (if sus then rtbl else update_nth_val (Z.to_nat (Int.unsigned tcby)) rtbl (Vint32 (Int.or i1 bitx))) /\
                        (* value of return *)
                         v' = (V$ OS_NO_ERR)
                          ) (* case: exist tasks waiting for semaphore *)
              ) |]
                   ))).

Theorem OSIPCSemPostPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt ( OSIPCSemPostPost' vl v ll ct).
Proof.
  try GoodFunAsrt_solver.
  unfold GoodFunAsrt.
  fold GoodFunAsrt.
  intros. apply GoodFunAsrt_err_sllseg.
  unfold GoodFunAsrt.
  fold GoodFunAsrt.
  intros. apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition OSIPCSemPostPost : fpost :=
  fun vl v ll ct => mkfunasrt ( OSIPCSemPostPostGood vl v ll ct).

Definition OSIPCSemPost_spec : fspec:= (OSIPCSemPostPre,OSIPCSemPostPost,(Int8u, Tptr OS_EVENT::nil)). 

(* OSMutexAccept *)

Definition OSMutexAcceptPre' (vl:vallist) (logicl:list logicvar) ct :=
  EX s ptrv v' er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v' :: logic_code s :: logic_val ptrv :: nil |] **
       <|| (mutexacc (vl++(v' ::nil)));; s ||> **
      [| nth_val 0 vl = Some ptrv |] **
       p_local OSLInv ct (logic_val (V$ 1)
                     :: logic_val (V$ __EvLoc_normal)
                     :: logic_val ptrv :: logic_val Vnull :: logic_val Vnull :: nil)). 

Theorem OSMutexAcceptPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSMutexAcceptPre' vl ll ct).
Proof.
  simpl.
  tauto.
Qed.

Definition OSMutexAcceptPre : fpre :=
  fun vl ll ct => mkfunasrt (OSMutexAcceptPreGood vl ll ct).

Definition OSMutexAcceptPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s ptrv v' k er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v' :: logic_code s :: logic_val ptrv :: nil |] **
       [| v = Some v' /\ v' = Vint32 k  /\ (k = Int.zero \/ k = Int.one) |] ** 
       [| nth_val' 0 vl = Vnull -> k = Int.zero |] ** 
     <|| s ||> ** p_local OSLInv ct (logic_val (V$ 1)
                     :: logic_val (V$ __EvLoc_normal)
                     :: logic_val ptrv :: logic_val Vnull :: logic_val Vnull :: nil)). 

Theorem OSMutexAcceptPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSMutexAcceptPost' vl v ll ct).
Proof.
  simpl.
  tauto.
Qed.

Definition OSMutexAcceptPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSMutexAcceptPostGood vl v ll ct).

Definition OSMutexAccept_spec : fspec:= 
    (OSMutexAcceptPre,OSMutexAcceptPost,(Int8u, Tptr OS_EVENT::nil)).


(* OSMutexCreate *)

Definition OSMutexCreatePre' (vl:vallist) (logicl:list logicvar) ct :=
  EX s v' er,
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
      [| logicl = logic_val v' :: logic_code s :: nil |] **
      <|| (mutexcre (vl++(v' ::nil)));; s ||> **
      p_local OSLInv ct init_lg).  (*  ** *)

Theorem OSMutexCreatePreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSMutexCreatePre' vl ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSMutexCreatePre : fpre :=
  fun vl ll ct => mkfunasrt (OSMutexCreatePreGood vl ll ct).

Definition OSMutexCreatePost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v' ptrv vloc er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
      [| logicl = logic_val v' :: logic_code s :: nil |] **
      [| v = Some v' /\ isptr v' /\ v' = ptrv |] ** 
      [| v' = Vnull /\ vloc = Vint32 ($__EvLoc_normal) \/
          v' <> Vnull /\ vloc = Vint32 ($__EvLoc_ecbcre2) |] **
      <|| s ||> ** 
      p_local OSLInv ct (logic_val (V$ 1)
                                   :: logic_val vloc 
                                   :: logic_val ptrv :: logic_val Vnull :: logic_val Vnull :: nil)). (* **  *) 

Theorem OSMutexCreatePostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSMutexCreatePost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSMutexCreatePost : fpost :=
  fun vl v ll ct => mkfunasrt (OSMutexCreatePostGood vl v ll ct).

Definition OSMutexCreate_spec : fspec:= (OSMutexCreatePre,OSMutexCreatePost,(Tptr OS_EVENT, Int8u:: Tptr Int8u :: nil)).


(* OSMutexDel *)

Definition OSMutexDelPre' (vl: vallist) (logicl: list logicvar) ct :=  
  EX s (* els *) tcbls pevent_blk elptr etbl letbl i1 x10 x11 
     v'22 v'23 v'43 v'44 v'45 v'46 v' tid (* err_blk *)hecb ptbl rtbl (* ptls *) vhold v'3 pegrp petbl_addr lpetbl petbl er, 
  (Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop ** Aier er **
       [| logicl = logic_code s :: logic_val (Vptr (pevent_blk, Int.zero)) ::
                              logic_val (Vint32 i1) :: logic_val x10 :: logic_val x11 :: logic_val elptr ::
                              logic_val (Vint32 pegrp) :: logic_val petbl_addr :: (* new add *)
                              logic_val (Vptr letbl) :: logic_lv etbl ::
                              logic_val (Vptr lpetbl) :: logic_lv petbl ::
                              logic_val v'23 :: 
                              logic_leventc v'43 :: logic_leventc v'44 :: logic_leventd v'45 :: logic_leventd v'46 ::
                              logic_val (Vptr tid) ::
                              logic_val v'22 :: logic_llv v' :: 
                              (* logic_val (Vptr vhold) :: *) logic_lv ptbl :: (* logic_lv rtbl :: logic_abstcb tcbls :: *) (* new add *)
                              nil |] ** 
       [| vl = (Vptr (pevent_blk, Int.zero)) (* :: Vptr (err_blk, Int.zero) *):: nil |] **
       <|| s ||> **   
       Astruct (pevent_blk,Int.zero) OS_EVENT 
                        (V$ OS_EVENT_TYPE_MUTEX :: V$ 0 :: Vint32 i1 :: x10 :: x11 :: elptr :: Vint32 pegrp :: petbl_addr :: nil) ** 
       Aarray letbl (Tarray char_t ∘ OS_EVENT_TBL_SIZE) etbl **
       Aarray lpetbl (Tarray char_t ∘ OS_EVENT_TBL_SIZE) petbl **
       evsllseg v'23 (Vptr (pevent_blk, Int.zero)) v'43 v'45 **
       evsllseg elptr Vnull v'44 v'46 **
       GV OSEventList @ OS_EVENT ∗ |-> v'23 **
       AOSEventFreeList v'22 v' **
       (* HECBList els ** *)
       HCurTCB tid **
       (* AGVars ** *)
       GAarray OSTCBPrioTbl (Tarray (Tptr OS_TCB) 64) ptbl **
       p_local OSLInv ct init_lg **
       GV OSIntNesting @ long |-> Vint32 v'3 **
       [|Int.ltu ($ 0) v'3 = false |] **
       (* [| RH_TCBList_ECBList_P els tcbls tid |] **  *)
(*        HPriotls ptls ** *)
       [|RLH_ECBData_P (DMutex (Vint32 i1) x10) hecb|]**
       [| array_type_vallist_match (Tptr OS_TCB) ptbl /\ length ptbl = 64%nat |] **
       [| RL_RTbl_PrioTbl_P rtbl ptbl vhold |] **
       [| R_PrioTbl_P ptbl tcbls vhold |] **
(*        [| RH_PrioTbl_P ptbl ptls vhold |] ** *)
       [| RH_CurTCB tid tcbls |] ** 
       [| id_addrval' (Vptr (pevent_blk, Int.zero)) OSEventTbl OS_EVENT = Some letbl |] ** 
       [| length etbl = ∘ OS_EVENT_TBL_SIZE |] ** 
       [| array_type_vallist_match char_t etbl |] ** 
       [| RL_Tbl_Grp_P etbl (V$ 0) |] ** 
       [| Int.unsigned i1 <= 65535 |] ** 
       [| isptr v'23 |] **
       [| isptr x10 |] **
       [| Int.unsigned pegrp <= Byte.max_unsigned |] ** 
       [| id_addrval' (Vptr (pevent_blk, Int.zero)) OSPostEventTbl OS_EVENT = Some lpetbl |] ** 
       [| RL_Tbl_Grp_P petbl (Vint32 pegrp) |] **
       [| array_type_vallist_match Int8u petbl |] ** 
       [| length petbl = ∘ OS_EVENT_TBL_SIZE |] ). 

Theorem OSMutexDelPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSMutexDelPre' vl ll ct).
Proof.
try GoodFunAsrt_solver.
Qed.

Definition OSMutexDelPre : fpre :=
  fun vl ll ct => mkfunasrt (OSMutexDelPreGood vl ll ct). 
Definition OSMutexDelPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s (* els *) pevent_blk letbl etbl elptr x10 x11
     v'22 v'23 v'24 v'43 v'' v'44 v'45 v'46 i1 v'16 tid (* tcbls *) ptbl ptbl' (* rtbl ptls' vhold *) pegrp petbl_addr lpetbl petbl er, 
    (Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop ** Aier er **
         [| logicl = logic_code s :: logic_val (Vptr (pevent_blk, Int.zero)) :: 
                                logic_val (Vint32 i1) :: logic_val x10 :: logic_val x11  :: logic_val elptr :: 
                                 logic_val (Vint32 pegrp) :: logic_val petbl_addr :: (* new add *)
                                logic_val (Vptr letbl) :: logic_lv etbl ::
                                logic_val (Vptr lpetbl) :: logic_lv petbl ::
                                logic_val v'23 :: 
                                logic_leventc v'43 :: logic_leventc v'44 :: logic_leventd v'45 :: logic_leventd v'46 ::
                                logic_val (Vptr tid) :: 
                                logic_val v'22 :: logic_llv v'16 :: logic_lv ptbl :: nil |] **  
         [|  v = Some Vnull |] **  
         <|| s ||> **
         GV OSEventFreeList @ OS_EVENT ∗ |-> Vptr (pevent_blk, Int.zero) **
         Astruct (pevent_blk, Int.zero) OS_EVENT
         (V$ OS_EVENT_TYPE_UNUSED :: V$ 0 :: Vint32 i1 :: x10 :: x11 :: v'22 :: Vint32 pegrp :: petbl_addr ::  nil) **
         Aarray letbl (Tarray char_t ∘ OS_EVENT_TBL_SIZE) etbl **
         Aarray lpetbl (Tarray char_t ∘ OS_EVENT_TBL_SIZE) petbl **
         GV OSEventList @ OS_EVENT ∗ |-> v'24 **
         evsllseg v'24 Vnull (v'' ++ v'44) (v'45 ++ v'46) **
         ecbf_sllseg v'22 Vnull v'16 OS_EVENT (fun vl : vallist => nth_val 5 vl) **
         (* HECBList els ** *) HCurTCB tid ** (* AGVars **  *)
         p_local OSLInv ct init_lg ** 
        AOSIntNesting **
        GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
           (update_nth_val (Z.to_nat(Int.unsigned (i1 >>ᵢ $ 8)))
              ptbl Vnull) **
         [| ptbl' =  (update_nth_val(Z.to_nat(Int.unsigned (i1 >>ᵢ $ 8) )) ptbl Vnull) |] **
         [| array_type_vallist_match (Tptr OS_TCB) ptbl' /\ length ptbl' = 64%nat |] **
         [| v'43 <> nil ->
            v'24 = v'23 /\
            Some (Vptr (pevent_blk, Int.zero)) = get_last_ptr v'43 /\ v'' = upd_last_ectrls v'43 elptr |] **
         [| v'43 = nil -> Vptr (pevent_blk, Int.zero) = v'23 /\ v'24 = elptr /\ v'' = nil |] **
         [| isptr x10 |] **
         [| isptr elptr |] **
         [| isptr v'22 |] ** 
         [| isptr v'24 |]). 

Theorem OSMutexDelPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt ( OSMutexDelPost' vl v ll ct).
Proof.
try GoodFunAsrt_solver.
Qed.

Definition OSMutexDelPost : fpost :=
  fun vl v ll ct => mkfunasrt ( OSMutexDelPostGood vl v ll ct).

Definition OSMutexDel_spec : fspec:= (OSMutexDelPre,OSMutexDelPost,(Tptr OS_EVENT, Tptr OS_EVENT:: (* Int8u :: *)nil)).


(* OSMutexPend *) 
Definition OSMutexPendPre' (vl:vallist) (logicl:list logicvar) ct :=
  EX s v' ptrv er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v' :: logic_code s ::  logic_val ptrv ::  nil |] **
        <|| spec_code_cons (mutexpend (vl++(v' ::nil))) s ||> **  
       [| nth_val 0 vl = Some ptrv |] ** 
       p_local OSLInv ct
           (logic_val (V$ 1)
                      :: logic_val (V$ __EvLoc_normal)
                      :: logic_val ptrv ::  logic_val Vnull :: logic_val Vnull :: nil)).
                      

Theorem OSMutexPendPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSMutexPendPre' vl ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSMutexPendPre : fpre :=
  fun vl ll ct => mkfunasrt (OSMutexPendPreGood vl ll ct).

Definition OSMutexPendPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v' k ptrv er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v' :: logic_code s ::  logic_val ptrv :: nil |] **
       [| v = Some v' /\ v' = Vint32 k  /\
          Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k) (Byte.max_unsigned) |] ** 
     <|| s ||> ** 
      [| nth_val' 0 vl = Vnull -> Int.ltu Int.zero k = true |] **
      p_local OSLInv ct
           (logic_val (V$ 1) 
                      :: logic_val (V$ __EvLoc_normal)
                      :: logic_val ptrv :: logic_val Vnull :: logic_val Vnull :: nil)).

Theorem OSMutexPendPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSMutexPendPost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSMutexPendPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSMutexPendPostGood vl v ll ct).

Definition OSMutexPend_spec : fspec:= 
    (OSMutexPendPre,OSMutexPendPost,(Int8u, Tptr OS_EVENT:: Int16u :: nil)).


(* OSMutexPost *)
Definition OSMutexPostPre' (vl:vallist) (logicl:list logicvar) ct :=
  EX s v' ptrv er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v' :: logic_code s :: logic_val ptrv :: nil |] **
        <|| spec_code_cons (mutexpost (vl++(v' ::nil))) s ||> **  
       [| nth_val 0 vl = Some ptrv |] ** 
       p_local OSLInv ct
           (logic_val (V$ 1)
                      :: logic_val (V$ __EvLoc_normal)
                      :: logic_val ptrv :: logic_val Vnull :: logic_val Vnull :: nil)). 



Theorem OSMutexPostPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSMutexPostPre' vl ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSMutexPostPre : fpre :=
  fun vl ll ct => mkfunasrt (OSMutexPostPreGood vl ll ct).

Definition OSMutexPostPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v' k ptrv er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v' :: logic_code s :: logic_val ptrv :: nil |] **
       [| v = Some v' /\ v' = Vint32 k  /\
          Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k) (Byte.max_unsigned) |] ** 
     <|| s ||> **
     [| nth_val' 0 vl = Vnull -> Int.ltu Int.zero k = true |] **
     p_local OSLInv ct
           (logic_val (V$ 1) :: logic_val (V$ __EvLoc_normal)
             :: logic_val ptrv :: logic_val Vnull :: logic_val Vnull :: nil)). 

Theorem OSMutexPostPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSMutexPostPost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSMutexPostPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSMutexPostPostGood vl v ll ct).

Definition OSMutexPost_spec : fspec:= 
    (OSMutexPostPre,OSMutexPostPost,(Int8u, Tptr OS_EVENT::nil)).


(* OSQAccept *)

Definition OSQAcceptPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX s v_ret V_ptr er,
    ( Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
      [| logicl = logic_val v_ret :: logic_code s :: logic_val V_ptr :: nil |] **
      <|| spec_code_cons (qacceptnew (vl++(v_ret ::nil)))  s ||>**  
      [|nth_val 0 vl =Some V_ptr|] **
       p_local OSLInv ct (logic_val (V$ 1)
            :: logic_val (V$ __EvLoc_normal)
               :: logic_val Vnull
                  :: logic_val Vnull :: logic_val V_ptr :: nil)  ).

Theorem OSQAcceptPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSQAcceptPre' vl ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSQAcceptPre : fpre :=
  fun vl ll ct => mkfunasrt (OSQAcceptPreGood vl ll ct).

Definition OSQAcceptPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v_ret k V_ptr er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v_ret :: logic_code s ::logic_val V_ptr ::  nil |] **
       [| v = Some v_ret /\ (v_ret = Vptr k \/ v_ret = Vnull)|] ** 
     <|| s ||> ** p_local OSLInv ct (logic_val (V$ 1)
            :: logic_val (V$ __EvLoc_normal)
               :: logic_val Vnull
                  :: logic_val Vnull :: logic_val V_ptr :: nil) ).

Theorem OSQAcceptPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSQAcceptPost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSQAcceptPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSQAcceptPostGood vl v ll ct).

Definition OSQAccept_spec : fspec:= (OSQAcceptPre,OSQAcceptPost,(Tptr Tvoid, Tptr OS_EVENT::nil)).


(* OSQCreate *)

Definition OSQCreatePre' (vl:vallist) (logicl:list logicvar) ct:=
  EX s v' er,
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
      [| logicl = logic_val v' :: logic_code s :: nil |] **
      <|| (qcre (vl++(v' ::nil)));; s ||> **
(*       [| isptr v' |] ** *)
(*       [| exists i, vl = Vint32 i :: nil /\ Int.ltu ($ OS_MAX_Q_SIZE) i = false /\ Int.eq i ($ 0) = false |] **  *)
      p_local OSLInv ct init_lg). 

Theorem OSQCreatePreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSQCreatePre' vl ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSQCreatePre : fpre :=
  fun vl ll ct => mkfunasrt (OSQCreatePreGood vl ll ct).

Definition OSQCreatePost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v' ptrv vloc er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
      [| logicl = logic_val v' :: logic_code s :: nil |] **
      [| v = Some v' /\ isptr v' /\ v' = ptrv |] ** 
      [| v' = Vnull /\ ( vloc = Vint32 ($__EvLoc_normal)  ) \/
          v' <> Vnull /\ vloc = Vint32 ($__EvLoc_ecbcre2) /\ (exists eid, v'= Vptr eid /\ notIncoreSemQ eid) |] **
      <|| s ||> ** 
      p_local OSLInv ct (logic_val (V$ 1)
                                   :: logic_val vloc 
                                   :: logic_val Vnull :: logic_val Vnull :: logic_val ptrv :: nil)). 

Theorem OSQCreatePostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSQCreatePost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSQCreatePost : fpost :=
  fun vl v ll ct => mkfunasrt (OSQCreatePostGood vl v ll ct).

Definition OSQCreate_spec : fspec:= (OSQCreatePre,OSQCreatePost, (Tptr OS_EVENT, Int16u::nil) ).


(* OSQDel *)
(* add by SJTU *)
(* Definition  notIncoreSemQ (x: ecbid) := 
  ~ In x OSIPCSem_val /\ ~ In x OSSendSem_val /\ x <> OSSemShared_val /\ x <> dynrefcmsgQ_addr.
Definition Qdel_notcoresem (x: val) (O : osabst) : Prop :=
  match x with 
  | Vptr eid => notIncoreSemQ eid 
  | _ => True 
end. *)
(* end add by SJTU *)
Definition OSQDelPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX s ptrv er, 
  (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
        [| logicl = logic_code s :: nil |] **
        <|| spec_code_cons (qdel vl)  s ||>**  
        [| nth_val 0 vl = Some ptrv |] **
        [| (forall eid, ptrv = Vptr eid -> notIncoreSemQ eid) |] **
        p_local OSLInv ct
            (logic_val (V$ 1)
                   :: logic_val (V$ __EvLoc_ecbdel)
                   :: logic_val Vnull :: logic_val Vnull :: logic_val ptrv :: nil)). 

Theorem OSQDelPreGood (vl:vallist) ll ct: 
  GoodFunAsrt (OSQDelPre' vl ll ct).
Proof.
  simpl.
  tauto.
Qed. 

Definition OSQDelPre : fpre :=
  fun vl ll ct => mkfunasrt (OSQDelPreGood vl ll ct).

Definition OSQDelPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_code s :: nil |] **
       [| v = Some Vnull |] ** 
       <|| s ||> **
       p_local OSLInv ct
                (logic_val (V$ 1)
                   :: logic_val (V$ __EvLoc_ecbdel)
                   :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil)).

Theorem OSQDelPostGood (vl:vallist) (v:option val) ll ct: 
  GoodFunAsrt (OSQDelPost' vl v ll ct). 
Proof.
  simpl.
  tauto.
Qed.

Definition OSQDelPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSQDelPostGood vl v ll ct).

Definition OSQDel_spec : fspec :=
  (OSQDelPre, OSQDelPost, (Tptr OS_EVENT, (Tptr OS_EVENT)::nil)).   


(* OSQPend *)
Definition OSQPendPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX s v1 v2 v3 v4 x V_pevt er,
    ( Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
      [| logicl = logic_val v4 :: logic_code s :: logic_val V_pevt :: nil |] **
      [| vl = v1 :: v2 :: v3  :: nil |] ** [| v3 = Vptr x|] **
      [|nth_val 0 vl = Some V_pevt|] **
      <|| spec_code_cons (qpendnew (vl++(v4 ::nil)))  s ||>**  
      p_local OSLInv ct (logic_val (V$ 1)
           :: logic_val (V$ __EvLoc_normal)
              :: logic_val Vnull :: logic_val Vnull :: logic_val V_pevt :: nil)  ).

Theorem OSQPendPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSQPendPre' vl ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSQPendPre : fpre :=
  fun vl ll ct => mkfunasrt (OSQPendPreGood vl ll ct).

Definition OSQPendPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v4 k V_pevt er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v4 :: logic_code s :: logic_val V_pevt :: nil |] **
       [| v = Some v4 /\ (v4 = Vptr k \/ v4 = Vnull)|] ** 
     <|| s ||> ** p_local OSLInv ct (logic_val (V$ 1)
           :: logic_val (V$ __EvLoc_normal)
              :: logic_val Vnull :: logic_val Vnull :: logic_val V_pevt :: nil)).

Theorem OSQPendPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSQPendPost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSQPendPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSQPendPostGood vl v ll ct).

Definition OSQPend_spec : fspec:= (OSQPendPre,OSQPendPost,(Tptr Tvoid, Tptr OS_EVENT :: Int16u ::Tptr Int8u ::nil)).


(* OSQPost *)
Definition OSQPostPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX s ptrv v_ret er,
    ( Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
      [| logicl = logic_val v_ret :: logic_code s :: logic_val ptrv :: nil |] **
      <|| spec_code_cons (qpost (vl++(v_ret ::nil)))  s ||>**  
       [| nth_val 0 vl = Some ptrv |] **
       p_local OSLInv ct  
                (  logic_val (V$ 1)
                     :: logic_val (V$ __EvLoc_normal)
                     :: logic_val Vnull :: logic_val Vnull :: logic_val ptrv :: nil)  ).

Theorem OSQPostPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSQPostPre' vl ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSQPostPre : fpre :=
  fun vl ll ct => mkfunasrt (OSQPostPreGood vl ll ct).

Definition OSQPostPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v_ret k ptrv er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v_ret :: logic_code s :: logic_val ptrv :: nil |] **
       [| v = Some v_ret /\ v_ret = Vint32 k  /\   
          Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k)  ( Byte.max_unsigned )|] ** 
     <|| s ||> ** 
     [| nth_val' 0 vl = Vnull -> Int.ltu Int.zero k = true |] **
     p_local OSLInv ct 
              (  logic_val (V$ 1)
                     :: logic_val (V$ __EvLoc_normal)
                     :: logic_val Vnull :: logic_val Vnull :: logic_val ptrv :: nil) ).

Theorem OSQPostPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSQPostPost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSQPostPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSQPostPostGood vl v ll ct).

Definition OSQPost_spec : fspec:= (OSQPostPre,OSQPostPost,(Int8u, Tptr OS_EVENT::Tptr Tvoid::nil)).

(* OSIPCQPost *)

Definition OSIPCQPostPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX s ptrv v_ret is isr er vnest vlock msg,
    ( Aie false ** Ais is ** Acs nil ** Aisr isr ** A_isr_is_prop ** Aier er **
      <|| spec_code_cons (ipcqpost (vl++(v_ret ::nil)))  s ||>**  
       [| nth_val 0 vl = Some ptrv |] **
       [| nth_val 1 vl = Some msg |] **
       p_local OSLInv ct init_lg**
       (* used for OS_Sched *)
       GV OSIntNesting @ long |-> Vint32 vnest **
       GV OSLockNesting @ long |-> Vint32 vlock **
       [| Int.eq vnest Int.zero = false |] **
       ( ( [| ptrv = Vnull |] **
           [| logicl = logic_val v_ret :: logic_code s :: logic_val ptrv :: logic_val msg :: 
                      (logic_isr isr) :: (logic_ier er) :: (logic_is is) ::nil |] ) \\//
         (EX eid ecbls p1 p2 tcbl1 tcbcur tcbl2 tcbls vhold scapl mcapl qcapl rtbl rgrp ptbl ptls t ct,
          [| ptrv =  Vptr eid |] **
          [| exists d, EcbMod.get ecbls eid = Some d |] **
           EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
           AOSUnMapTbl **
           AOSMapTbl **
           AOSRdyTblGrp rtbl rgrp **
           AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold **
           AOSTCBList p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
           HTCBList tcbls ** HTime t ** HCurTCB ct **
           [| RH_TCBList_ECBList_P ecbls tcbls ct|] **
           [| RH_CurTCB ct tcbls|] **
           [| logicl = logic_val v_ret :: logic_code s :: logic_val ptrv :: logic_val msg :: 
                         (logic_isr isr) :: (logic_ier er) :: (logic_is is) :: 
                         (logic_abstcb tcbls) :: (logic_absecb ecbls) :: (logic_val (Vptr ct)) ::
                         (logic_val p1) :: (logic_val p2) ::  (logic_lv rtbl) :: (logic_val rgrp) ::
                         (logic_llv tcbl1) :: (logic_lv tcbcur) :: (logic_llv tcbl2) :: nil |] ) ) ).

Theorem OSIPCQPostPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSIPCQPostPre' vl ll ct).
Proof.
  try GoodFunAsrt_solver.
  unfold GoodFunAsrt.
  fold GoodFunAsrt.
  intros. apply GoodFunAsrt_err_sllseg.
  unfold GoodFunAsrt.
  fold GoodFunAsrt.
  intros. apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition OSIPCQPostPre : fpre :=
  fun vl ll ct => mkfunasrt (OSIPCQPostPreGood vl ll ct).

Definition OSIPCQPostPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v_ret tp ptrv is isr er vnest vlock msg, 
  (Aie false ** Ais is ** Acs nil ** Aisr isr ** A_isr_is_prop ** Aier er **
       <|| s ||> ** 
       [| nth_val 0 vl = Some ptrv |] **
       [| nth_val 1 vl = Some msg |] **
       [| v = Some v_ret /\ v_ret = Vint32 tp /\ Int.unsigned tp <= Byte.max_unsigned |] ** 
       p_local OSLInv ct init_lg **
       (* used for OS_Sched *)
       GV OSIntNesting @ long |-> Vint32 vnest **
       GV OSLockNesting @ long |-> Vint32 vlock **
       [| Int.eq vnest Int.zero = false |] **
(* postcondition used for OSQPost *)
       (([| ptrv = Vnull |] **
          [| logicl = logic_val v_ret :: logic_code s :: logic_val ptrv :: logic_val msg ::
                         (logic_isr isr) :: (logic_ier er) :: (logic_is is) :: nil |] **
          [| v_ret = (V$ OS_ERR_PEVENT_NULL) |]) \\// (* case: empty pevent *)
         (EX eid ecbls p1 p2 tcbl1 tcbcur tcbl2 tcbls vhold scapl mcapl qcapl rtbl rgrp ptbl ptls t ct
                 ecbls' tcbls' tcbvl tcbl1' tcbcur' tcbl2' rtbl' rgrp',
          [| ptrv =  Vptr eid |] **
          [| exists d, EcbMod.get ecbls eid = Some d |] **
           EvtInv ecbls' p1 tcbvl tcbls' vhold scapl mcapl qcapl **
           AOSUnMapTbl **
           AOSMapTbl **
           AOSRdyTblGrp rtbl' rgrp' **
           AOSTCBPrioTbl ptbl rtbl' tcbls' ptls vhold **
           AOSTCBList p1 p2 tcbl1' (tcbcur'::tcbl2') rtbl' ct tcbls' **
           HTCBList tcbls' ** HTime t ** HCurTCB ct **
           [| RH_TCBList_ECBList_P ecbls' tcbls' ct|] **
           [| RH_CurTCB ct tcbls' |] **
           [| logicl = logic_val v_ret :: logic_code s :: logic_val ptrv :: logic_val msg :: 
                         (logic_isr isr) :: (logic_ier er) :: (logic_is is) :: 
                         (logic_abstcb tcbls) :: (logic_absecb ecbls) :: (logic_val (Vptr ct)) ::
                         (logic_val p1) :: (logic_val p2) ::  (logic_lv rtbl) :: (logic_val rgrp) ::
                         (logic_llv tcbl1) :: (logic_lv tcbcur) :: (logic_llv tcbl2) :: nil |] **
           [| tcbvl = (tcbl1' ++ (tcbcur'::tcbl2')) |] **
           [| (
                 ( msg = Vnull /\
                   ecbls' = ecbls /\  tcbls' = tcbls /\
                   tcbl1' = tcbl1 /\ tcbcur' = tcbcur /\ tcbl2' = tcbl2 /\
                   rtbl' = rtbl /\ rgrp' = rgrp /\ 
                   v_ret = (V$ OS_ERR_POST_NULL_PTR)) (* case: msg null *)
                 \/ ( ~(exists x y pwl wls, EcbMod.get ecbls eid = Some (absmsgq x y pwl, wls)) /\
                   ecbls' = ecbls /\  tcbls' = tcbls /\
                   tcbl1' = tcbl1 /\ tcbcur' = tcbcur /\ tcbl2' = tcbl2 /\
                   rtbl' = rtbl /\ rgrp' = rgrp /\ 
                   v_ret = (V$ OS_ERR_EVENT_TYPE)) (* case: wrong type *)
                 \/ ( exists  x y pwl, EcbMod.get ecbls eid = Some (absmsgq x y pwl, nil) /\
                                        Z.ge (Z_of_nat (length x)) (Int.unsigned y)/\ 
                         ecbls' = ecbls /\  tcbls' = tcbls /\
                         tcbl1' = tcbl1 /\ tcbcur' = tcbcur /\ tcbl2' = tcbl2 /\
                         rtbl' = rtbl /\ rgrp' = rgrp /\ 
                         v_ret = (V$ MSGQ_OVF_ERR)  ) (* case:  q overflow *)
                 \/ (exists x y pwl, EcbMod.get ecbls eid = Some (absmsgq x y pwl, nil) /\
                                       Z.lt (Z_of_nat (length x)) (Int.unsigned y)/\ 
                         ecbls' = EcbMod.set ecbls eid (absmsgq (x++(msg::nil)) y pwl , nil) /\
                         tcbls' = tcbls /\
                         tcbl1' = tcbl1 /\ tcbcur' = tcbcur /\ tcbl2' = tcbl2 /\
                         rtbl' = rtbl /\ rgrp' = rgrp /\ 
                         v_ret = (V$ OS_NO_ERR)) (* case: post q success *)
                 \/ (exists x y pwl wls tid p t_opt m msg sus,
                         EcbMod.get ecbls eid = Some (absmsgq x y pwl, wls) /\ wls <> nil /\
                         GetHWait tcbls wls tid /\
                         TcbMod.get tcbls tid = Some (p, wait (os_stat_q eid) t_opt, m, sus) /\
                         ecbls' = EcbMod.set ecbls eid (absmsgq nil y pwl, remove_tid tid wls) /\
                         tcbls' = TcbMod.set tcbls tid (p, rdy,msg, sus) /\
                         (* changed value because of OS_EventTaskRdy *)
                         exists next prev wt tcbx tcby tcbbitx tcbbity,
                         exists bitx bity vl vl' i1 stat,
                         p = ((tcby<<ᵢ$ 3)+ᵢtcbx) /\
                         nth_val' (Z.to_nat (Int.unsigned tcby)) OSMapVallist = Vint32 bity /\
                         nth_val' (Z.to_nat (Int.unsigned tcbx)) OSMapVallist = Vint32 bitx /\
                         (* new OSTCBList  *)
                         nth_val' (Z.to_nat (Int.unsigned p)) ptbl  = (Vptr tid) /\ tid <> vhold /\
                         tcblist_get (Vptr tid) p1 (tcbl1 ++ (tcbcur::tcbl2)) = Some vl /\
                         tcbvl = set_node (Vptr tid) vl' p1 (tcbl1 ++ (tcbcur::tcbl2)) /\
                         vl = (next::prev::(Vptr eid)::m::(Vint32 wt)::(Vint32 stat)::(Vint32 p)::(Vint32 tcbx)::(Vint32 tcby)::tcbbitx::tcbbity::nil)%list /\
                         vl' = (next::prev::Vnull::msg::(Vint32 Int.zero)::(Vint32 (Int.and stat (Int.not ($ OS_STAT_Q))))::(Vint32 p)::(Vint32 tcbx)::(Vint32 tcby)::tcbbitx::tcbbity::nil)%list /\
                        (* new OSRdyTbl  *)
                         nth_val' (Z.to_nat (Int.unsigned tcby)) rtbl = Vint32 i1 /\
                        rtbl' = (if sus then rtbl else update_nth_val (Z.to_nat (Int.unsigned tcby)) rtbl (Vint32 (Int.or i1 bitx))) /\
                        (* value of return *)
                         v_ret = (V$ OS_NO_ERR)
                          ) (* case: exist tasks waiting for queue *)
              ) |]
                   ))).

Theorem OSIPCQPostPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSIPCQPostPost' vl v ll ct).
Proof.
  try GoodFunAsrt_solver.
  unfold GoodFunAsrt.
  fold GoodFunAsrt.
  intros. apply GoodFunAsrt_err_sllseg.
  unfold GoodFunAsrt.
  fold GoodFunAsrt.
  intros. apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition OSIPCQPostPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSIPCQPostPostGood vl v ll ct).

Definition OSIPCQPost_spec : fspec:= (OSIPCQPostPre,OSIPCQPostPost,(Int8u, Tptr OS_EVENT::Tptr Tvoid::nil)).


(* OSQTimedPost *)
Definition OSQTimedPostPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX s ptrv v_ret er,
    ( Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
      [| logicl = logic_val v_ret :: logic_code s :: logic_val ptrv :: nil |] **
      <|| spec_code_cons (qtimedpost (vl++(v_ret ::nil)))  s ||>**
      [| nth_val 0 vl = Some ptrv |] ** [| nth_val 1 vl = Some (Vint32 Int.zero) |] **
      p_local OSLInv ct  
                (  logic_val (V$ 1)
                     :: logic_val (V$ __EvLoc_normal)
                     :: logic_val Vnull :: logic_val Vnull :: logic_val ptrv :: nil)  ).

Theorem OSQTimedPostPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSQTimedPostPre' vl ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSQTimedPostPre : fpre :=
  fun vl ll ct => mkfunasrt (OSQTimedPostPreGood vl ll ct).


Definition OSQTimedPostPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v_ret k ptrv er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
     [| logicl = logic_val v_ret :: logic_code s :: logic_val ptrv :: nil |] **
     [| v = Some v_ret /\ v_ret = Vint32 k   /\   
          Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k) ( Byte.max_unsigned )  |] ** 
     <|| s ||> **
     [| nth_val' 0 vl = Vnull -> Int.ltu Int.zero k = true |] **
     p_local OSLInv ct 
              (  logic_val (V$ 1)
                     :: logic_val (V$ __EvLoc_normal)
                     :: logic_val Vnull :: logic_val Vnull :: logic_val ptrv :: nil) ).

Theorem OSQTimedPostPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSQTimedPostPost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSQTimedPostPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSQTimedPostPostGood vl v ll ct).

Definition OSQTimedPost_spec : fspec:= (OSQTimedPostPre,OSQTimedPostPost,(Int8u, Tptr OS_EVENT::Int16u::Tptr Tvoid::nil)).


(* OSQQuery *)

Definition OSQQueryPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX s pevent pdata v_ret x er,
    ( Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
      [| logicl = logic_val v_ret :: logic_code s :: nil |] **
      [| vl = pevent :: pdata :: nil |] ** [| pdata = Vptr x|] **
      <|| spec_code_cons (qquerynew (vl++( v_ret ::nil)))  s ||>**  
       p_local OSLInv ct init_lg  ).


Theorem OSQQueryPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSQQueryPre' vl ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSQQueryPre : fpre :=
  fun vl ll ct => mkfunasrt (OSQQueryPreGood vl ll ct).

Definition OSQQueryPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v_ret k er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v_ret :: logic_code s :: nil |] **
       [| v = Some v_ret /\ v_ret = Vint32 k  /\   (* 杩斿洖鍊间负鏁村瀷锛屼緥濡侽S_NO_ERR = 0%Z  : Z *)
          Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k) (Byte.max_unsigned) |] ** 
     <|| s ||> ** p_local OSLInv ct init_lg).
     
Theorem OSQQueryPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSQQueryPost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSQQueryPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSQQueryPostGood vl v ll ct).

Definition OSQQuery_spec : fspec:= (OSQQueryPre,OSQQueryPost,(Int8u, Tptr OS_EVENT:: Tptr OS_Q_DATA ::nil)).


(*capability部分的spec*)



(***************** end spec for functions for events *******************)

(* ------------------------- add sepc by SJTU  -----------------------*)
(* reset timer *) 
Definition OS_resettimerPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX tmrid tmri s er,
    <|| s ||> **
     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** Aier er **
     A_isr_is_prop **
     AOSTMRNode tmrid tmri **
     GV __timerregs @ (Tptr Tint32) |-> Vptr tmrRegsAddr **
    [| nth_val 0 vl = Some (Vint32 tmrid)|] **
    [| Int.ltu tmrid ($ 16) = true |] **
    [| logicl = logic_lv tmri :: (logic_ier er) :: logic_code s :: nil |] ** 
    p_local OSLInv ct init_lg.

Theorem OS_resettimerPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OS_resettimerPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_resettimerPre: fpre :=
  fun vl ll ct=> mkfunasrt (OS_resettimerPreGood vl ll ct).

Definition OS_resettimerPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX tmrid tmri s er,
    <|| s ||> **
     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** Aier er **
     A_isr_is_prop **
     (([| V_OSTGCR tmri <> Some (V$ 0) |] ** AOSTMRNode tmrid (update_nth_val 7%nat (update_nth_val 8%nat tmri (V$ 0)) (V$ 0))) \\//
      [| V_OSTGCR tmri = Some (V$ 0) |] ** AOSTMRNode tmrid tmri
     ) **
    GV __timerregs @ (Tptr Tint32) |-> Vptr tmrRegsAddr **
    [| nth_val 0 vl = Some (Vint32 tmrid)|] **
    [| logicl = logic_lv tmri :: (logic_ier er) :: logic_code s :: nil |] ** 
    [| v = None|] **
    p_local OSLInv ct init_lg.

Theorem OS_resettimerPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_resettimerPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_resettimerPost : fpost :=
 fun vl v ll ct=> mkfunasrt (OS_resettimerPostGood vl v ll ct).

Definition OS_resettimer_spec : fspec:= (OS_resettimerPre,OS_resettimerPost,(Tvoid,Tint32 :: nil)).

(* tmr config *)
Definition OS_timerConfigPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX tmrid prdlo prdhi tmrmode bitflag tmri s er,
    <|| s ||> **
     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** Aier er **
     A_isr_is_prop **
     AOSTMRNode tmrid tmri **
     GV __timerregs @ (Tptr Tint32) |-> Vptr tmrRegsAddr **
    [| nth_val 0 vl = Some (Vint32 tmrid)|] **
    [| nth_val 1 vl = Some (Vint32 prdlo)|] **
    [| nth_val 2 vl = Some (Vint32 prdhi)|] **
    [| nth_val 3 vl = Some (Vint32 tmrmode)|] **
    [| nth_val 4 vl = Some (Vint32 bitflag)|] **
    [| Int.ltu ($ 0) tmrid = true /\ Int.ltu tmrid ($ 16) = true |] **
    [| logicl = logic_lv tmri :: (logic_ier er) :: logic_code s :: nil |] ** 
    p_local OSLInv ct init_lg.

Theorem OS_timerConfigPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OS_timerConfigPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_timerConfigPre: fpre :=
  fun vl ll ct=> mkfunasrt (OS_timerConfigPreGood vl ll ct).

Definition tmrmode_config  i : Z :=
  if Int.eq Int.zero i then 64 else 128.

Definition enable64bit_config  i : Z :=
  if Int.eq Int.zero i then 4 else 0.

Definition OS_timerConfigPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX tmrid prdlo prdhi tmrmode bitflag tmri s er,
    <|| s ||> **
     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** Aier er **
     A_isr_is_prop **
     AOSTMRNode tmrid (update_nth_val 8%nat 
     (update_nth_val 7%nat 
     (update_nth_val 4%nat 
      ( update_nth_val 3%nat
        (update_nth_val 6%nat (update_nth_val 5%nat tmri (Vint32 prdlo)) (Vint32 prdhi))
        (Vint32 (Int.repr 0))) (Vint32 (Int.repr 0)))
      (Vint32 ($ (tmrmode_config tmrmode))))  (Vint32 ($ (enable64bit_config bitflag))))**
    GV __timerregs @ (Tptr Tint32) |-> Vptr tmrRegsAddr **
    [| nth_val 0 vl = Some (Vint32 tmrid)|] **
    [| nth_val 1 vl = Some (Vint32 prdlo)|] **
    [| nth_val 2 vl = Some (Vint32 prdhi)|] **
    [| nth_val 3 vl = Some (Vint32 tmrmode)|] **
    [| nth_val 4 vl = Some (Vint32 bitflag)|] **
    [| logicl = logic_lv tmri :: (logic_ier er) :: logic_code s :: nil |] ** 
    [| v = None|] **
    p_local OSLInv ct init_lg.

Theorem OS_timerConfigPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_timerConfigPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_timerConfigPost : fpost :=
 fun vl v ll ct=> mkfunasrt (OS_timerConfigPostGood vl v ll ct).

Definition OS_timerConfig_spec : fspec:= (OS_timerConfigPre,OS_timerConfigPost,(Tvoid,Tint32 :: Tint32 ::Tint32 ::Tint32 ::Tint32 ::nil)).

(* tmr outconfig *)
Definition OS_timerOutConfigPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX tmrid tmroutmode tmri tcg s er,
    <|| s ||> **
     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** Aier er **
     A_isr_is_prop **
     AOSTMRNode tmrid tmri **
     GV __timerregs @ (Tptr Tint32) |-> Vptr tmrRegsAddr **
    [| nth_val 0 vl = Some (Vint32 tmrid)|] **
    [| nth_val 1 vl = Some (Vint32 tmroutmode)|] **
    [| Int.ltu ($ 0) tmrid = true /\ Int.ltu tmrid ($ 16) = true |] **
    [| V_OSTCRreg tmri = Some (Vint32 tcg) |] **
    [| logicl = logic_val (Vint32 tcg) :: logic_lv tmri :: (logic_ier er) :: logic_code s :: nil |] ** 
    p_local OSLInv ct init_lg.

Theorem OS_timerOutConfigPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OS_timerOutConfigPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_timerOutConfigPre: fpre :=
  fun vl ll ct=> mkfunasrt (OS_timerOutConfigPreGood vl ll ct).

Definition tmroutmode_config  tcg i : int :=
  if Int.eq Int.zero i then  Int.and tcg ($ 4294967287) else Int.or tcg ($ 8).

Definition OS_timerOutConfigPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
   EX tmrid tmroutmode tmri tcg s er,
    <|| s ||> **
     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** Aier er **
     A_isr_is_prop **
     AOSTMRNode tmrid (update_nth_val 7%nat tmri (Vint32 (tmroutmode_config tcg tmroutmode))) **
     GV __timerregs @ (Tptr Tint32) |-> Vptr tmrRegsAddr **
    [| nth_val 0 vl = Some (Vint32 tmrid)|] **
    [| nth_val 1 vl = Some (Vint32 tmroutmode)|] **
    [| V_OSTCRreg tmri = Some (Vint32 tcg) |] **
    [| logicl = logic_val (Vint32 tcg) :: logic_lv tmri :: (logic_ier er) :: logic_code s :: nil |] ** 
    [| v = None|] **
    p_local OSLInv ct init_lg.

Theorem OS_timerOutConfigPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_timerOutConfigPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_timerOutConfigPost : fpost :=
 fun vl v ll ct=> mkfunasrt (OS_timerOutConfigPostGood vl v ll ct).

Definition OS_timerOutConfig_spec : fspec:= (OS_timerOutConfigPre,OS_timerOutConfigPost,(Tvoid,Tint32 :: Tint32  ::nil)).

(* tmr init : OStimer_Init *)
Definition OS_timerInitPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX tmrid prdlo prdhi clkpsd tmri s er,
    <|| s ||> **
     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** Aier er **
     A_isr_is_prop **
     AOSTMRNode tmrid tmri **
     GV __timerregs @ (Tptr Tint32) |-> Vptr tmrRegsAddr **
    [| nth_val 0 vl = Some (Vint32 tmrid)|] **
    [| nth_val 1 vl = Some (Vint32 prdlo)|] **
    [| nth_val 2 vl = Some (Vint32 prdhi)|] **
    [| V_OSEMUMGT tmri = Some (Vint32 clkpsd) |] **
    [| Int.ltu tmrid ($ 16) = true |] **
    [| logicl =  logic_val (Vint32 clkpsd) :: logic_lv tmri :: (logic_ier er) :: logic_code s :: nil |] ** 
    p_local OSLInv ct init_lg.

Theorem OS_timerInitPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OS_timerInitPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_timerInitPre: fpre :=
  fun vl ll ct=> mkfunasrt (OS_timerInitPreGood vl ll ct).
Definition tmrinit_emumgt_clkpsd (clkpsd : int32) := Int.and clkpsd (Int.repr CSL_TMR_EMUMGT_CLKSPD_MASK).


Definition OS_timerInitPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
   EX tmrid prdlo prdhi clkpsd tmri s er,
    <|| s ||> **
     Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) ** Aier er **
     A_isr_is_prop **
     AOSTMRNode tmrid (update_nth_val 7%nat
                        (update_nth_val 1%nat 
                          (update_nth_val 8%nat 
                            (update_nth_val 6%nat 
                              (update_nth_val 5%nat
                                (update_nth_val 4%nat 
                                  (update_nth_val 3%nat tmri (Vint32 Int.zero)) 
                                (Vint32 Int.zero))
                              (Vint32 prdlo))
                            (Vint32 prdhi))
                          (Vint32 (Int.repr 3)))
                        (Vint32 (tmrinit_emumgt_clkpsd clkpsd)))
                      (Vint32 (Int.repr 136)))  **
     GV __timerregs @ (Tptr Tint32) |-> Vptr tmrRegsAddr **
    [| nth_val 0 vl = Some (Vint32 tmrid)|] **
    [| nth_val 1 vl = Some (Vint32 prdlo)|] **
    [| nth_val 2 vl = Some (Vint32 prdhi)|] **
    [| V_OSEMUMGT tmri = Some (Vint32 clkpsd) |] **
    [| logicl =  logic_val (Vint32 clkpsd) ::logic_lv tmri :: (logic_ier er) :: logic_code s :: nil |] ** 
    [| v = None|] **
    p_local OSLInv ct init_lg.

Theorem OS_timerInitPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_timerInitPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_timerInitPost : fpost :=
 fun vl v ll ct=> mkfunasrt (OS_timerInitPostGood vl v ll ct).

Definition OS_timerInit_spec : fspec:= (OS_timerInitPre,OS_timerInitPost,(Tvoid,Tint32 :: Tint32 :: Tint32 ::nil)).

(* compute_period *)
Definition OS_compute_periodPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX tkps hz s er,
  <|| s||> ** Aisr empisr ** Ais nil ** 
     Aie false ** Acs (true :: nil) ** A_isr_is_prop ** Aier er **
    [|vl = (Vint32 tkps) :: (Vint32 hz) :: nil|] **
    [| logicl = (logic_ier er) :: logic_code s :: nil |] ** 
    p_local OSLInv ct init_lg.


Theorem OS_compute_periodPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OS_compute_periodPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_compute_periodPre: fpre :=
  fun vl ll ct=> mkfunasrt (OS_compute_periodPreGood vl ll ct).

Definition OS_compute_periodPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
   EX tkps hz prdlo s er,
  <|| s||> ** Aisr empisr ** Ais nil ** 
     Aie false ** Acs (true :: nil) ** A_isr_is_prop ** Aier er **
    [| prdlo = (1000 * (Int.unsigned hz)) / ((Int.unsigned tkps) * 6)|] **
    [|vl = (Vint32 tkps) :: (Vint32 hz) :: nil|] **
    [| logicl = (logic_ier er) :: logic_code s :: nil |] ** 
    [| v = Some (Vint32 ($ prdlo)) |] **
    p_local OSLInv ct init_lg.

Theorem OS_compute_periodPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_compute_periodPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_compute_periodPost : fpost :=
 fun vl v ll ct=> mkfunasrt (OS_compute_periodPostGood vl v ll ct).

Definition OS_compute_period_spec : fspec:= (OS_compute_periodPre,OS_compute_periodPost,(Tint32, Tint32:: Tint32 :: nil)).

(* int_install_handler_tmr *)
(* Definition Inthandler_valid_range (funcl : vallist) (hiz: Z) := 
   (forall x,  INT_NUM_MIN <= x <= hiz ->
    exists funcaddr, nth_val (Z.to_nat (Int.unsigned ($ x -ᵢ $ INT_NUM_MIN))) funcl = Some (Vptr funcaddr)). *)

Definition OSint_install_handler_timerPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX i prio handler param eventID s er funcl paral iz',
  <|| install_handler_6678code vl ;; s||> ** Aisr empisr ** Ais nil ** 
    Aie false ** Acs (true :: nil) ** A_isr_is_prop ** Aier er **
    (* [|flag_z = 1 /\ iz = iz' + 1 /\ (iz' < INT_NUM_MIN \/ Inthandler_valid_range funcl iz')|] ** *)
    GAarray OSIntHandler (Tarray (Tptr Tint32) INTHANDLER_LENGTH) funcl ** 
    GAarray OSIntHandlerParam (Tarray (Void) ∗ INTHANDLER_LENGTH) paral **
    [| vl = (Vint32 i)::(Vint32 prio)::(Vint32 handler)::(param)::(Vint32 eventID) :: nil|] **
    [| logicl = (logic_val (Vint32 iz')) :: (logic_lv funcl) :: (logic_lv paral) :: (logic_ier er) :: logic_code s :: nil |] ** 
    p_local OSLInv ct init_lg.

Theorem OSint_install_handler_timerPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OSint_install_handler_timerPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OSint_install_handler_timerPre: fpre :=
  fun vl ll ct=> mkfunasrt (OSint_install_handler_timerPreGood vl ll ct).

Definition OSint_install_handler_timerPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX i prio handler param eventID s er funcl paral iz',
  <|| s||> ** Aisr empisr ** Ais nil ** 
    Aie false ** Acs (true :: nil) ** A_isr_is_prop ** Aier er **
    (* [|flag_z = 0 /\ iz = iz' + 1 /\ INT_NUM_MIN <= iz' /\ nth_val (Z.to_nat (Int.unsigned ($ iz' -ᵢ $ INT_NUM_MIN))) funcl = Some Vnull /\ Inthandler_valid_range funcl (iz' - 1)|]  ** *)
    GAarray OSIntHandler (Tarray (Tptr Tint32) INTHANDLER_LENGTH) (update_nth_val (Z.to_nat (Int.unsigned (iz' -ᵢ $ INT_NUM_MIN))) funcl (Vint32 handler)) **
    GAarray OSIntHandlerParam (Tarray (Void) ∗ INTHANDLER_LENGTH) (update_nth_val (Z.to_nat (Int.unsigned (iz' -ᵢ $ INT_NUM_MIN))) paral param) **
    [| vl = (Vint32 i)::(Vint32 prio)::(Vint32 handler)::(param)::(Vint32 eventID) :: nil|] **
    [| logicl = (logic_val (Vint32 iz')) :: (logic_lv funcl) :: (logic_lv paral) :: (logic_ier er) :: logic_code s :: nil |] ** 
    [| v = Some (Vint32 (Int.repr OS_NO_ERR)) |] **
    p_local OSLInv ct init_lg.

Theorem OSint_install_handler_timerPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSint_install_handler_timerPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OSint_install_handler_timerPost : fpost :=
  fun vl v ll ct=> mkfunasrt (OSint_install_handler_timerPostGood vl v ll ct).

Definition OSint_install_handler_timer_spec : fspec:= (OSint_install_handler_timerPre,OSint_install_handler_timerPost,(Tint32, Tint32:: Tint32 :: Tint32 :: Tptr Void :: Tint32 :: nil)).

(* ------------------------- inter core communication -----------------------*)
(* MemCopy *)
Definition OS_memcopyPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX dstAddr srcAddr size dstvl srcvl s er,
  <|| s||> ** Aisr empisr ** Ais nil ** 
   (* (( *)
     Aie false ** Acs (true :: nil) ** A_isr_is_prop ** Aier er 
     (* ) \\// (Aie true ** Acs nil) )  *)
     **
    Aarray dstAddr (Tarray Tint8 (Z.to_nat (Int.unsigned size))) dstvl **
    Aarray srcAddr (Tarray Tint8 (Z.to_nat (Int.unsigned size))) srcvl **
    [|vl = (Vptr dstAddr) :: (Vptr srcAddr) :: (Vint32 size) :: nil|] **
    [| logicl = logic_lv dstvl :: logic_lv srcvl:: (logic_ier er) :: logic_code s :: nil |] ** 
    p_local OSLInv ct init_lg.


Theorem OS_memcopyPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OS_memcopyPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_memcopyPre: fpre :=
  fun vl ll ct=> mkfunasrt (OS_memcopyPreGood vl ll ct).

Definition OS_memcopyPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX dstAddr srcAddr size dstvl srcvl s er ,
  <|| s ||> ** Aisr empisr ** Ais nil ** 
   (* ((  *)
    Aie false ** Acs (true :: nil) ** A_isr_is_prop ** Aier er 
    (* ) \\// (Aie true ** Acs nil))  *)
    **
  Aarray dstAddr (Tarray Tint8 (Z.to_nat (Int.unsigned size))) srcvl **
  Aarray srcAddr (Tarray Tint8 (Z.to_nat (Int.unsigned size))) srcvl **
  [|vl = (Vptr dstAddr) :: (Vptr srcAddr) :: (Vint32 size) :: nil|] **
  [| logicl = logic_lv dstvl :: logic_lv srcvl:: (logic_ier er) :: logic_code s ::  nil |] ** 
  p_local OSLInv ct init_lg.

Theorem OS_memcopyPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_memcopyPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_memcopyPost : fpost :=
 fun vl v ll ct=> mkfunasrt (OS_memcopyPostGood vl v ll ct).

Definition OS_memcpy_spec : fspec:= (OS_memcopyPre,OS_memcopyPost,(Tvoid,Tptr Int8u :: Tptr Int8u :: Tint32 :: nil)).



Definition OS_memcpy1Pre' (vl:vallist) (logicl:list logicvar) ct:=
  EX dstAddr srcAddr dstvl srcvl s,
  <|| s||> ** Aisr empisr ** Ais nil ** 
   (* (( *)
     Aie false ** Acs (true :: nil) ** A_isr_is_prop
     (* ) \\// (Aie true ** Acs nil) )  *)
     **
    Astruct dstAddr  dyn_refac_cfg dstvl **
    Astruct srcAddr  dyn_refac_cfg srcvl **
    [|vl = (Vptr dstAddr) :: (Vptr srcAddr) :: nil|] **
    [| logicl = logic_lv dstvl :: logic_lv srcvl:: logic_code s :: nil |] ** 
    p_local OSLInv ct init_lg.


Theorem OS_memcpy1PreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OS_memcpy1Pre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_memcpy1Pre: fpre :=
  fun vl ll ct=> mkfunasrt (OS_memcpy1PreGood vl ll ct).

Definition OS_memcpy1Post' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX dstAddr srcAddr dstvl srcvl s,
  <|| s ||> ** Aisr empisr ** Ais nil ** 
   (* ((  *)
    Aie false ** Acs (true :: nil) ** A_isr_is_prop
    (* ) \\// (Aie true ** Acs nil))  *)
    **
   Astruct dstAddr  dyn_refac_cfg srcvl **
    Astruct srcAddr  dyn_refac_cfg srcvl **
  [|vl = (Vptr dstAddr) :: (Vptr srcAddr):: nil|] **
  [| logicl = logic_lv dstvl :: logic_lv srcvl:: logic_code s ::  nil |] ** 
  [| v = None|] **
  p_local OSLInv ct init_lg.

Theorem OS_memcpy1PostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_memcpy1Post' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_memcpy1Post : fpost :=
 fun vl v ll ct=> mkfunasrt (OS_memcpy1PostGood vl v ll ct).

 Definition OS_memcpy1_spec : fspec:= (OS_memcpy1Pre,OS_memcpy1Post, (Tvoid, Tptr Tvoid::Tptr Tvoid :: nil)).

Definition OS_memcpy2Pre' (vl:vallist) (logicl:list logicvar) ct:=
  EX dstAddr srcAddr dstvl srcvl s,
  <|| s||> ** Aisr empisr ** Ais nil ** 
   (* (( *)
     Aie false ** Acs (true :: nil) ** A_isr_is_prop
     (* ) \\// (Aie true ** Acs nil) )  *)
     **
    Astruct dstAddr  Elf32_Ehdr dstvl **
    Astruct srcAddr  Elf32_Ehdr srcvl **
    [|vl = (Vptr dstAddr) :: (Vptr srcAddr) :: nil|] **
    [| logicl = logic_lv dstvl :: logic_lv srcvl:: logic_code s :: nil |] ** 
    p_local OSLInv ct init_lg.


Theorem OS_memcpy2PreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OS_memcpy2Pre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_memcpy2Pre: fpre :=
  fun vl ll ct=> mkfunasrt (OS_memcpy2PreGood vl ll ct).

Definition OS_memcpy2Post' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX dstAddr srcAddr dstvl srcvl s,
  <|| s ||> ** Aisr empisr ** Ais nil ** 
   (* ((  *)
    Aie false ** Acs (true :: nil) ** A_isr_is_prop
    (* ) \\// (Aie true ** Acs nil))  *)
    **
   Astruct dstAddr  Elf32_Ehdr srcvl **
    Astruct srcAddr  Elf32_Ehdr srcvl **
  [|vl = (Vptr dstAddr) :: (Vptr srcAddr):: nil|] **
  [| logicl = logic_lv dstvl :: logic_lv srcvl:: logic_code s ::  nil |] ** 
  [| v = None|] **
  p_local OSLInv ct init_lg.

Theorem OS_memcpy2PostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_memcpy2Post' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_memcpy2Post : fpost :=
 fun vl v ll ct=> mkfunasrt (OS_memcpy2PostGood vl v ll ct).

 Definition OS_memcpy2_spec : fspec:= (OS_memcpy2Pre,OS_memcpy2Post,(Tvoid, Tptr Tvoid::Tptr Tvoid :: nil)).
 
 Definition OS_memcpy3Pre' (vl:vallist) (logicl:list logicvar) ct:=
  EX dstAddr srcAddr dstvl srcvl s,
  <|| s||> ** Aisr empisr ** Ais nil ** 
   (* (( *)
     Aie false ** Acs (true :: nil) ** A_isr_is_prop
     (* ) \\// (Aie true ** Acs nil) )  *)
     **
    Astruct dstAddr  Elf32_Phdr dstvl **
    Astruct srcAddr  Elf32_Phdr srcvl **
    [|vl = (Vptr dstAddr) :: (Vptr srcAddr) :: nil|] **
    [| logicl = logic_lv dstvl :: logic_lv srcvl:: logic_code s :: nil |] ** 
    p_local OSLInv ct init_lg.

Theorem OS_memcpy3PreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OS_memcpy3Pre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_memcpy3Pre: fpre :=
  fun vl ll ct=> mkfunasrt (OS_memcpy3PreGood vl ll ct).

Definition OS_memcpy3Post' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX dstAddr srcAddr dstvl srcvl s,
  <|| s ||> ** Aisr empisr ** Ais nil ** 
   (* ((  *)
    Aie false ** Acs (true :: nil) ** A_isr_is_prop
    (* ) \\// (Aie true ** Acs nil))  *)
    **
   Astruct dstAddr  Elf32_Phdr srcvl **
    Astruct srcAddr  Elf32_Phdr srcvl **
  [|vl = (Vptr dstAddr) :: (Vptr srcAddr):: nil|] **
  [| logicl = logic_lv dstvl :: logic_lv srcvl:: logic_code s ::  nil |] ** 
  [| v = None|] **
  p_local OSLInv ct init_lg.

Theorem OS_memcpy3PostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_memcpy3Post' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_memcpy3Post : fpost :=
 fun vl v ll ct=> mkfunasrt (OS_memcpy3PostGood vl v ll ct).

Definition OS_memcpy3_spec : fspec:= (OS_memcpy3Pre,OS_memcpy3Post,(Tvoid, Tptr Tvoid::Tptr Tvoid :: nil)).

Definition OS_memcpy5Pre' (vl:vallist) (logicl:list logicvar) ct:=
  EX is isr er dstAddr srcAddr size dstvl srcvl s,
    <|| s||> ** Aisr isr ** Ais is ** 
     Aie false ** Acs nil ** Aier er ** A_isr_is_prop **
    Astruct dstAddr dyn_refac_cfg dstvl **
    Aarray srcAddr (Tarray Tint8 (Z.to_nat (Int.unsigned size))) srcvl  **
    [| size = $ size_of_dyn_refac_cfg |] **
    [|vl = (Vptr dstAddr) :: (Vptr srcAddr) :: (Vint32 size)::nil|] **
    [| logicl = logic_lv dstvl :: logic_lv srcvl:: logic_code s :: logic_is is :: logic_isr isr:: logic_ier er:: nil |] ** 
    p_local OSLInv ct init_lg.

Theorem OS_memcpy5PreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OS_memcpy5Pre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_memcpy5Pre: fpre :=
  fun vl ll ct=> mkfunasrt (OS_memcpy5PreGood vl ll ct).


Definition OS_memcpy5Post' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX is isr er dstAddr srcAddr size dstvl srcvl s,
    <|| s||> ** Aisr isr ** Ais is ** 
    Aie false ** Acs nil ** Aier er ** A_isr_is_prop **
    Astruct dstAddr dyn_refac_cfg srcvl **
    Aarray srcAddr (Tarray Tint8 (Z.to_nat (Int.unsigned size))) srcvl  **
    [| struct_type_vallist_match dyn_refac_cfg srcvl|] **
    [| size = $ size_of_dyn_refac_cfg |] **
    [| vl = (Vptr dstAddr) :: (Vptr srcAddr) :: (Vint32 size)::nil|] **
    [| logicl = logic_lv dstvl :: logic_lv srcvl:: logic_code s :: logic_is is :: logic_isr isr:: logic_ier er:: nil |] ** 
    [| v = None|] **
  p_local OSLInv ct init_lg.

Theorem OS_memcpy5PostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_memcpy5Post' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_memcpy5Post : fpost :=
 fun vl v ll ct=> mkfunasrt (OS_memcpy5PostGood vl v ll ct).

Definition OS_memcpy5_spec : fspec:= (OS_memcpy5Pre,OS_memcpy5Post,(Tvoid,Tptr Tvoid :: Tptr Tvoid :: Tint32 :: nil)).

(* Malloc *)
Definition malloc_Elf32_PhdrPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX  s,
  <|| s||> ** Aisr empisr ** Ais nil ** 
     Aie true ** Acs nil **
    [|vl =  nil|] **
    [| logicl =  logic_code s :: nil |] ** 
    p_local OSLInv ct init_lg.

Theorem malloc_Elf32_PhdrPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (malloc_Elf32_PhdrPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition malloc_Elf32_PhdrPre: fpre :=
  fun vl ll ct=> mkfunasrt (malloc_Elf32_PhdrPreGood vl ll ct).

Definition malloc_Elf32_PhdrPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX p vl s,
   <|| s||> ** Aisr empisr ** Ais nil ** 
     Aie true ** Acs nil **
    [|vl =  nil|] **
    [| logicl =  logic_code s :: nil |] ** 
   [| v = Some (Vptr p)|] **
   Astruct p Elf32_Phdr vl **
  p_local OSLInv ct init_lg.

Theorem malloc_Elf32_PhdrPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (malloc_Elf32_PhdrPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition malloc_Elf32_PhdrPost : fpost :=
 fun vl v ll ct=> mkfunasrt (malloc_Elf32_PhdrPostGood vl v ll ct).

Definition malloc_Elf32_Phdr_spec : fspec:= (malloc_Elf32_PhdrPre,malloc_Elf32_PhdrPost, (Tptr os_ucos_h.Elf32_Phdr, nil)).

Definition malloc_Elf32_EhdrPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX  s,
  <|| s||> ** Aisr empisr ** Ais nil ** 
     Aie true ** Acs nil **
    [|vl =  nil|] **
    [| logicl =  logic_code s :: nil |] ** 
    p_local OSLInv ct init_lg.


Theorem malloc_Elf32_EhdrPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (malloc_Elf32_EhdrPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition malloc_Elf32_EhdrPre: fpre :=
  fun vl ll ct=> mkfunasrt (malloc_Elf32_EhdrPreGood vl ll ct).


Definition malloc_Elf32_EhdrPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX p vl s,
   <|| s||> ** Aisr empisr ** Ais nil ** 
     Aie true ** Acs nil **
    [|vl =  nil|] **
    [| logicl =  logic_code s :: nil |] ** 
   [| v = Some (Vptr p)|] **
   Astruct p Elf32_Ehdr vl **
  p_local OSLInv ct init_lg.

Theorem malloc_Elf32_EhdrPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (malloc_Elf32_EhdrPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition malloc_Elf32_EhdrPost : fpost :=
 fun vl v ll ct=> mkfunasrt (malloc_Elf32_EhdrPostGood vl v ll ct).

Definition malloc_Elf32_Ehdr_spec : fspec:= (malloc_Elf32_EhdrPre,malloc_Elf32_EhdrPost, (Tptr os_ucos_h.Elf32_Ehdr, nil)).

(* free *)
Definition free_Elf32_EhdrPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX p vl s,
   <|| s||> ** Aisr empisr ** Ais nil ** 
     Aie true ** Acs nil **
    [|vl =  Vptr p:: nil|] **
    [| logicl =  logic_code s :: nil |] ** 
    Astruct p Elf32_Ehdr vl **
  p_local OSLInv ct init_lg.


Theorem free_Elf32_EhdrPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (free_Elf32_EhdrPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition free_Elf32_EhdrPre: fpre :=
  fun vl ll ct=> mkfunasrt (free_Elf32_EhdrPreGood vl ll ct).


 Definition free_Elf32_EhdrPost' (vl:vallist) (v: option val)(logicl:list logicvar) ct:=
  EX  s ,
  <|| s||> ** Aisr empisr ** Ais nil ** 
     Aie true ** Acs nil **
     [| v = None|] **
    [| logicl =  logic_code s :: nil |] ** 
    p_local OSLInv ct init_lg.


Theorem free_Elf32_EhdrPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (free_Elf32_EhdrPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition free_Elf32_EhdrPost : fpost :=
 fun vl v ll ct=> mkfunasrt (free_Elf32_EhdrPostGood vl v ll ct).

Definition free_Elf32_Ehdr_spec : fspec:= (free_Elf32_EhdrPre, free_Elf32_EhdrPost, ( Tvoid , Tptr os_ucos_h.Elf32_Ehdr::nil)).
 
Definition free_Elf32_PhdrPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX p vl s,
   <|| s||> ** Aisr empisr ** Ais nil ** 
     Aie true ** Acs nil **
    [|vl =  Vptr p:: nil|] **
    [| logicl =  logic_code s :: nil |] ** 
    Astruct p Elf32_Phdr vl **
  p_local OSLInv ct init_lg.


Theorem free_Elf32_PhdrPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (free_Elf32_PhdrPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition free_Elf32_PhdrPre: fpre :=
  fun vl ll ct=> mkfunasrt (free_Elf32_PhdrPreGood vl ll ct).

 Definition free_Elf32_PhdrPost' (vl:vallist) (v: option val)(logicl:list logicvar) ct:=
  EX  s ,
  <|| s||> ** Aisr empisr ** Ais nil ** 
     Aie true ** Acs nil **
     [| v = None|] **
    [| logicl =  logic_code s :: nil |] ** 
    p_local OSLInv ct init_lg.

Theorem free_Elf32_PhdrPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (free_Elf32_EhdrPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition free_Elf32_PhdrPost : fpost :=
 fun vl v ll ct=> mkfunasrt (free_Elf32_EhdrPostGood vl v ll ct).

Definition free_Elf32_Phdr_spec : fspec:= (free_Elf32_PhdrPre, free_Elf32_PhdrPost, ( Tvoid , Tptr os_ucos_h.Elf32_Phdr::nil)). 
 
Definition zero_vallist(vl:vallist):= forall v, In v vl -> v = Vint32 (Int.zero).

Definition zero_list_vallist(vl: list vallist):= forall v, In v vl -> zero_vallist v. 
 
Definition OS_memsetPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX  srcAddr size srcvl s,
  <|| s||> ** Aisr empisr ** Ais nil ** 
   (* (( *)
     Aie false ** Acs (true :: nil) ** A_isr_is_prop
     (* ) \\// (Aie true ** Acs nil) )  *)
     **
    Aarray srcAddr (Tarray Tint8 (Z.to_nat (Int.unsigned size))) srcvl **
    [|vl = (Vptr srcAddr) :: (Vint32 size) :: nil|] **
    [| logicl =  logic_lv srcvl:: logic_code s :: nil |] ** 
    p_local OSLInv ct init_lg.


Theorem OS_memsetPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OS_memsetPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_memsetPre: fpre :=
  fun vl ll ct=> mkfunasrt (OS_memsetPreGood vl ll ct).

Definition OS_memsetPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX  srcAddr size srcvl s dstvl,
  <|| s||> ** Aisr empisr ** Ais nil ** 
   (* (( *)
     Aie false ** Acs (true :: nil) ** A_isr_is_prop
     (* ) \\// (Aie true ** Acs nil) )  *)
     **
    Aarray srcAddr (Tarray Tint8 (Z.to_nat (Int.unsigned size))) dstvl **
    [| zero_vallist dstvl |]**
    [|vl = (Vptr srcAddr) :: (Vint32 size) :: nil|] **
    [| logicl =  logic_lv srcvl:: logic_code s :: nil |] ** 
   [| v = None|] **
    p_local OSLInv ct init_lg.

Theorem OS_memsetPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_memsetPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_memsetPost : fpost :=
 fun vl v ll ct=> mkfunasrt (OS_memsetPostGood vl v ll ct).

Definition OS_memset_spec : fspec:= (OS_memsetPre,OS_memsetPost,(Tvoid,Tptr Int8u :: Tptr Int8u :: Tint32 :: nil)).
 
(* OS_getCoreIPC *)
Definition OS_getCoreIPCPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX ir er si i s ipcgr,
    <|| s ||> ** 
    Aisr (isrupd ir i%nat true) **
    ([|i%nat = 1%nat|] ** Aier (ierupd er i%nat false) \\//
    [|i%nat <> 1%nat|] ** Aier (ierupd er i%nat true)) ** 
    Aie false **
    Ais (i%nat :: si) **
    Acs nil ** 
    [| isr_is_prop (isrupd ir i%nat true) (i%nat :: si) |] **
    [|vl = (Vint32 ipcgr) :: nil|] **
    [| logicl =  (logic_isr ir) :: (logic_ier er) :: (logic_ie false) ::
    (logic_is si) :: (logic_hid i) :: logic_code s :: nil |] **
    p_local OSLInv ct init_lg.

Theorem OS_getCoreIPCPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OS_getCoreIPCPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_getCoreIPCPre: fpre :=
  fun vl ll ct=> mkfunasrt (OS_getCoreIPCPreGood vl ll ct).

Definition OS_getCoreIPCPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX ir er si i s ipcgr,
    <|| s ||> ** 
    Aisr (isrupd ir i%nat true) **
    ([|i%nat = 1%nat|] ** Aier (ierupd er i%nat false) \\//
    [|i%nat <> 1%nat|] ** Aier (ierupd er i%nat true)) ** 
    Aie false **
    Ais (i%nat :: si) **
    Acs nil ** 
    [| isr_is_prop (isrupd ir i%nat true) (i%nat :: si) |] **
    [|vl = (Vint32 ipcgr) :: nil|] **
    [| logicl =  (logic_isr ir) :: (logic_ier er) :: (logic_ie false) ::
    (logic_is si) :: (logic_hid i) :: logic_code s :: nil |] **
    [|(Int.and ipcgr ($ CORE0_IPC) = ($ CORE0_IPC) /\ DNUM <> 0 /\ v = Some (V$ 0)) \/
        Int.and ipcgr ($ CORE0_IPC) <> ($ CORE0_IPC) /\ (
      (Int.and ipcgr ($ CORE1_IPC) = ($ CORE1_IPC) /\ DNUM <> 1 /\ v = Some (V$ 1)) \/ 
        Int.and ipcgr ($ CORE1_IPC) <> ($ CORE1_IPC) /\ (
      (Int.and ipcgr ($ CORE2_IPC) = ($ CORE2_IPC) /\ DNUM <> 2 /\ v = Some (V$ 2)) \/
        Int.and ipcgr ($ CORE2_IPC) <> ($ CORE2_IPC) /\ (
      (Int.and ipcgr ($ CORE3_IPC) = ($ CORE3_IPC) /\ DNUM <> 3 /\ v = Some (V$ 3)) \/ 
        Int.and ipcgr ($ CORE3_IPC) <> ($ CORE3_IPC) /\ (
      (Int.and ipcgr ($ CORE4_IPC) = ($ CORE4_IPC) /\ DNUM <> 4 /\ v = Some (V$ 4)) \/
        Int.and ipcgr ($ CORE4_IPC) <> ($ CORE4_IPC) /\ (
      (Int.and ipcgr ($ CORE5_IPC) = ($ CORE5_IPC) /\ DNUM <> 5 /\ v = Some (V$ 5)) \/
        Int.and ipcgr ($ CORE5_IPC) <> ($ CORE5_IPC) /\ (
      (Int.and ipcgr ($ CORE6_IPC) = ($ CORE6_IPC) /\ DNUM <> 6 /\ v = Some (V$ 6)) \/
        Int.and ipcgr ($ CORE6_IPC) <> ($ CORE6_IPC) /\ (
      (Int.and ipcgr ($ CORE7_IPC) = ($ CORE7_IPC) /\ DNUM <> 7 /\ v = Some (V$ 7)) \/
        Int.and ipcgr ($ CORE7_IPC) <> ($ CORE7_IPC) /\ 
      v = Some (V$ (Zneg xH))))))))) |] **
    p_local OSLInv ct init_lg.

Theorem OS_getCoreIPCPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_getCoreIPCPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_getCoreIPCPost : fpost :=
 fun vl v ll ct=> mkfunasrt (OS_getCoreIPCPostGood vl v ll ct).

Definition OS_getCoreIPC_spec : fspec:= (OS_getCoreIPCPre,OS_getCoreIPCPost,(Tint32, Tint32:: nil)).

(* -------------------------dynamic refactor -----------------------*)
Definition LoadElf2MemPre' (vl:vallist) (logicl:list logicvar) (ct:tid):=
  EX file  (ehdrvl:vallist)   ephnum ephoff hdr eentry phdrvll filevll memvll dstvll s,
   <||s||> ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop **
   [| vl = (Vptr file)::nil|] **
    [| V_e_phnum ehdrvl = Some (Vint32 ephnum)|] **
    [| V_e_entry ehdrvl = Some (Vptr eentry)|] **
    [| V_e_phoff ehdrvl = Some (Vint32 ephoff) |] **
    [| hdr = get_off_addr file ephoff |] **
    [| PhdrArray_Pure phdrvll filevll memvll dstvll |] **
    [| length phdrvll = S (Z.to_nat (Int.unsigned ephnum)) |] **
     [| 0<= Int.unsigned ephnum|] **
     [| struct_type_vallist_match Elf32_Ehdr ehdrvl |] **
    PhdrArray file hdr phdrvll filevll memvll dstvll **
    [| logicl = logic_lv ehdrvl :: logic_llv phdrvll :: logic_ollv filevll:: logic_ollv memvll:: logic_ollv dstvll ::   logic_code s :: nil |] **
    Astruct file Elf32_Ehdr ehdrvl ** 
    p_local OSLInv ct init_lg.

Lemma GoodFunAsrt_PhdrArray: forall p1 p2 v1 v2 v3 v4,
  GoodFunAsrt (PhdrArray p1 p2 v1 v2 v3 v4).
Proof.
  intros. revert p1 p2 v2 v3 v4. induction v1; intros.
  + simpl.  destruct v2; GoodFunAsrt_solver.  destruct v3; GoodFunAsrt_solver. destruct v4; GoodFunAsrt_solver.
  + simpl. destruct v2; GoodFunAsrt_solver. destruct v3; GoodFunAsrt_solver.  destruct v4; GoodFunAsrt_solver.
      destruct a; GoodFunAsrt_solver.
     - destruct p2; GoodFunAsrt_solver.  destruct a; GoodFunAsrt_solver. destruct a; GoodFunAsrt_solver.
        destruct a; GoodFunAsrt_solver. destruct a; GoodFunAsrt_solver. destruct a; GoodFunAsrt_solver.
        destruct a; GoodFunAsrt_solver. destruct a; GoodFunAsrt_solver. destruct a; GoodFunAsrt_solver.
     - destruct o; GoodFunAsrt_solver. destruct o1; GoodFunAsrt_solver. destruct o1; GoodFunAsrt_solver.
     - destruct o0; GoodFunAsrt_solver. apply GoodFunAsrt_Aarray. 
Qed.

Theorem LoadElf2MemPreGood (vl:vallist) ll ct:
  GoodFunAsrt (LoadElf2MemPre' vl ll ct).
Proof.
  GoodFunAsrt_solver. apply GoodFunAsrt_PhdrArray.
Qed.

Definition LoadElf2MemPre : fpre :=
  fun vl ll ct => mkfunasrt (LoadElf2MemPreGood vl ll ct).

Definition zero_option_list_vallist(vll: list (option vallist)):=
  forall vl, In (Some vl) vll -> zero_vallist vl.

(* post *)
Definition LoadElf2MemPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:= 
   EX file (ehdrvl:vallist)   ephnum ephoff hdr eentry phdrvll filevll memvll dstvll s zerovll,
   <||s||> ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop **
   [| vl = (Vptr file)::nil|] **
    [| V_e_phnum ehdrvl = Some (Vint32 ephnum)|] **
    [| V_e_entry ehdrvl = Some (Vptr eentry)|] **
    [| V_e_phoff ehdrvl = Some (Vint32 ephoff)|] **
    [| hdr = get_off_addr file ephoff |] **
    [| PhdrArray_Pure phdrvll filevll (zerovll++(skipn (Z.to_nat (Int.unsigned ephnum)) memvll )) (firstn (Z.to_nat (Int.unsigned ephnum)) filevll ++  skipn (Z.to_nat (Int.unsigned ephnum)) dstvll)|] **
     [| length phdrvll = S (Z.to_nat (Int.unsigned ephnum)) |] **
     [| 0<= Int.unsigned ephnum|] **
     [| zero_option_list_vallist zerovll |] **
     [| length zerovll = Z.to_nat (Int.unsigned ephnum)  |] **
      [| struct_type_vallist_match Elf32_Ehdr ehdrvl |] **
    PhdrArray file hdr phdrvll filevll (zerovll++(skipn (Z.to_nat (Int.unsigned ephnum)) memvll )) (firstn (Z.to_nat (Int.unsigned ephnum)) filevll ++  skipn (Z.to_nat (Int.unsigned ephnum)) dstvll) **
    [| logicl = logic_lv ehdrvl :: logic_llv phdrvll :: logic_ollv filevll:: logic_ollv memvll:: logic_ollv dstvll ::   logic_code s :: nil |] **
    Astruct file Elf32_Ehdr ehdrvl ** 
    [| v=Some (Vptr eentry) |] **
     p_local OSLInv ct init_lg.
  
Theorem LoadElf2MemPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (LoadElf2MemPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver. apply GoodFunAsrt_PhdrArray.
Qed.

Definition LoadElf2MemPost : fpost :=
  fun vl v ll ct => mkfunasrt (LoadElf2MemPostGood vl v ll ct).
  
Definition LoadElf2Mem_spec: fspec:= (LoadElf2MemPre, LoadElf2MemPost, (Tptr Tvoid, (Tptr Tvoid)::nil)).

Definition LoadElf2Mem'Pre' (vl:vallist) (logicl:list logicvar) (ct:tid):=
  EX file  (ehdrvl:vallist)  eentry  s,
   <||s||> ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop **
   [| vl = (Vptr file)::nil|] **
    [| V_e_entry ehdrvl = Some (Vptr eentry)|] **
     [| struct_type_vallist_match Elf32_Ehdr ehdrvl |] **
    [| logicl = logic_lv ehdrvl ::  logic_code s :: nil |] **
    Astruct file Elf32_Ehdr ehdrvl ** 
      p_local OSLInv ct init_lg.

Theorem LoadElf2Mem'PreGood (vl:vallist) ll ct:
  GoodFunAsrt (LoadElf2Mem'Pre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition LoadElf2Mem'Pre : fpre :=
  fun vl ll ct => mkfunasrt (LoadElf2Mem'PreGood vl ll ct).

(* post *)
Definition LoadElf2Mem'Post' (vl:vallist) (v:option val) (logicl:list logicvar) ct:= 
   EX file (ehdrvl:vallist)   eentry s ,
   <||s||> ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop **
   [| vl = (Vptr file)::nil|] **
    [| V_e_entry ehdrvl = Some (Vptr eentry)|] **
     [| struct_type_vallist_match Elf32_Ehdr ehdrvl |] **
   
    [| logicl = logic_lv ehdrvl :: logic_code s :: nil |] **
    Astruct file Elf32_Ehdr ehdrvl ** 
    [| v=Some (Vptr eentry) |] **
     p_local OSLInv ct init_lg.
  
Theorem LoadElf2Mem'PostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (LoadElf2Mem'Post' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition LoadElf2Mem'Post : fpost :=
  fun vl v ll ct => mkfunasrt (LoadElf2Mem'PostGood vl v ll ct).
  
Definition LoadElf2Mem'_spec: fspec:= (LoadElf2Mem'Pre, LoadElf2Mem'Post, (Tptr Tvoid, (Tptr Tvoid)::nil)).

(* Spec code for doRefactorISR *)
Definition doRefactorISR_aspec_memcpy (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
  | (opv, O2) =>
     opv = None /\
     exists srcCore dnum recvheap dynheap cfglp cfglpv freedynn,
      vl = ((Vint32 srcCore) :: nil) /\
      get O1 curcoreid = Some (oscurtcore dnum) /\ 
      get O1 ipcrecvid = Some (osrecv recvheap) /\
      get O1 dynheapid = Some (osdynheap dynheap) /\
      get O1 freedynid = Some (osfreedyn cfglp freedynn) /\
      freedynn <> 0%nat /\ cfglp = Vptr cfglpv /\
    (
      exists cfglp' step cfgvl dynheap', step = compute_step (Z.to_nat (Int.unsigned srcCore)) dnum /\
      nth_error recvheap step = Some cfgvl /\
      dynheap' = dynheap_add dynheap cfglpv (firstn (Z.to_nat size_of_dyn_refac_cfg) cfgvl) /\
      O2 = Some (set (set O1 dynheapid (osdynheap dynheap')) freedynid (osfreedyn cfglp' (pred freedynn)))
    ) 
  end.


Definition doRefactorISR_aspec (vl:vallist): spec_code :=
  match vl with
  | Vint32 srccore :: vl' =>
   match vl' with
    | dynptr :: vl'' =>
    match vl'' with
    | v_ret::nil =>
      (ASSUME (fun O : osabst => get O freedynid = Some (osfreedyn Vnull 0%nat))) ?? 
      (  
        ASSERT (fun O : osabst => srccore <> Int.repr DNUM /\ exists i, get O freedynid = Some (osfreedyn dynptr i)) ;;
        ASSUME(fun O: osabst => exists i, get O freedynid = Some (osfreedyn dynptr i) /\ i<>0%nat );;
        doRefactorISR_aspec_memcpy (|(Vint32 srccore::nil)|);; 
        spec_code_cons (ipcqpost ((Vptr dynrefcmsgQ_addr:: dynptr::nil)++ (v_ret::nil)))
        (ASSUME (fun O: osabst => v_ret = (V$ MSGQ_OVF_ERR) \/ v_ret = (V$ OS_NO_ERR)))
      )
    | _ => spec_abort
    end 
  | _ => spec_abort
  end 
  | _ => spec_abort
  end.

Definition doRefactorISRPre' (vl:vallist) (logicl:list logicvar) (ct:tid):=
  EX s srcCore  is isr er pl memlls cfglp v_ret ecbls vnest vlock
     recvh ,
      (* Parameters *)
      [| vl = (Vint32 srcCore):: nil |] **
      [| srcCore = ($ 0) \/ srcCore = ($ 1) \/ srcCore = ($ 2) \/ srcCore = ($ 3)
         \/ srcCore = ($ 4) \/ srcCore = ($ 5) \/ srcCore = ($ 6) \/ srcCore = ($ 7) |] ** 
      (* [| Int.unsigned  srcCore > DNUM /\ step = Z.to_nat (Int.unsigned (Int.sub srcCore ($ 1))) \/ 
         Int.unsigned srcCore <= DNUM /\ step= Z.to_nat (Int.unsigned srcCore)|] ** *)

      (* Interrupt state *)
      Aie false ** Ais is ** Acs nil ** Aisr isr ** A_isr_is_prop ** Aier er **  p_local OSLInv ct init_lg **
      (* Abs spec *) 
      <|| spec_code_cons (doRefactorISR_aspec (vl++(cfglp::v_ret ::nil))) s||> **
      (* DynamicRefactorInv *)
      DynamicRefactorINV ecbls **
      (* CoreCommuInv *)
      AOSIPCMem pl memlls **
      HipcrecvHeap recvh **
      [| RLH_IpcRecvHeap_P memlls recvh |] **
      HcurCore curcore **
      (* Osipcqpost precondition *)
      (EX p1 p2 tcbl1 tcbcur tcbl2 tcbls vhold scapl mcapl qcapl rtbl rgrp  ptbl ptls t ct,
      GV OSIntNesting @ long |-> Vint32 vnest **
      GV OSLockNesting @ long |-> Vint32 vlock  **
      [| Int.eq vnest Int.zero = false |] **
      EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
      AOSUnMapTbl **
      AOSMapTbl **
      AOSRdyTblGrp rtbl rgrp **
      AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold **
      AOSTCBList p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
      HTCBList tcbls ** HTime t ** HCurTCB ct **
      [| RH_TCBList_ECBList_P ecbls tcbls ct|] **
      [| RH_CurTCB ct tcbls|] ** 
      (*logic vars*)
      [| logicl = logic_lv pl::  logic_val cfglp::  logic_code s ::
      logic_val v_ret :: (logic_isr isr) ::  (logic_ier er) :: (logic_is is) :: (logic_abstcb tcbls) :: (logic_absecb ecbls) :: (logic_val (Vptr ct)) ::
      (logic_val p1) :: (logic_val p2) ::  (logic_lv rtbl) :: (logic_val rgrp) ::
      (logic_llv tcbl1) :: (logic_lv tcbcur) :: (logic_llv tcbl2) :: 
      nil |] ).


Theorem doRefactorISRPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (doRefactorISRPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
  hnf. intros. apply GoodFunAsrt_err_sllseg.
  hnf. intros. apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition doRefactorISRPre: fpre :=
  fun vl ll ct=> mkfunasrt (doRefactorISRPreGood vl ll ct).

Definition doRefactorISRPost' (vl:vallist) (v: option val)(logicl:list logicvar) ct:=
  EX s srcCore  is isr er pl memlls cfglp  v_ret ecbls vnest vlock
   recvh ,
      (* Parameters *)
      [| vl = (Vint32 srcCore):: nil |] **
      [| srcCore = ($ 0) \/ srcCore = ($ 1) \/ srcCore = ($ 2) \/ srcCore = ($ 3)
         \/ srcCore = ($ 4) \/ srcCore = ($ 5) \/ srcCore = ($ 6) \/ srcCore = ($ 7) |] ** 
      [| v = None|] **
      (* Interrupt state *)
      Aie false ** Ais is ** Acs nil ** Aisr isr ** A_isr_is_prop ** Aier er ** p_local OSLInv ct init_lg ** 
       (* Abs spec *) 
       <||s||> **
      (* CoreCommuInv *)
      AOSIPCMem pl memlls **
      HipcrecvHeap recvh **
      [| RLH_IpcRecvHeap_P memlls recvh |] **
      HcurCore curcore **
      (* Osipcqpost postcondition *)
      GV OSIntNesting @ long |-> Vint32 vnest **
      GV OSLockNesting @ long |-> Vint32 vlock **
      [| Int.eq vnest Int.zero = false |] **
      (EX p1 p2 tcbl1 tcbcur tcbl2 tcbls vhold scapl mcapl qcapl rtbl rgrp  ptbl ptls  ecbls' tcbls' tcbvl tcbl1' tcbcur' tcbl2' rtbl' rgrp' t ct ,
      EvtInv ecbls' p1 tcbvl tcbls' vhold scapl mcapl qcapl **
      AOSUnMapTbl **
      AOSMapTbl **
      AOSRdyTblGrp rtbl' rgrp' **
      AOSTCBPrioTbl ptbl rtbl' tcbls' ptls vhold **
      AOSTCBList p1 p2 tcbl1' (tcbcur'::tcbl2') rtbl' ct tcbls' **
      HTCBList tcbls' ** HTime t ** HCurTCB ct **
      [| RH_TCBList_ECBList_P ecbls' tcbls' ct|] **
      [| RH_CurTCB ct tcbls' |] **
      [| tcbvl = (tcbl1' ++ (tcbcur'::tcbl2')) |] **
           [| ( ( exists  x y pwl, EcbMod.get ecbls dynrefcmsgQ_addr = Some (absmsgq x y pwl, nil) /\
                                        Z.ge (Z_of_nat (length x)) (Int.unsigned y)/\ 
                         ecbls' = ecbls /\  tcbls' = tcbls /\
                         tcbl1' = tcbl1 /\ tcbcur' = tcbcur /\ tcbl2' = tcbl2 /\
                         rtbl' = rtbl /\ rgrp' = rgrp /\ 
                         v_ret = (V$ MSGQ_OVF_ERR)  ) (* case:  q overflow *)
                 \/ (exists x y pwl, EcbMod.get ecbls dynrefcmsgQ_addr = Some (absmsgq x y pwl, nil) /\
                                       Z.lt (Z_of_nat (length x)) (Int.unsigned y)/\ 
                         ecbls' = EcbMod.set ecbls dynrefcmsgQ_addr (absmsgq (x++(cfglp::nil)) y pwl , nil) /\
                         tcbls' = tcbls /\
                         tcbl1' = tcbl1 /\ tcbcur' = tcbcur /\ tcbl2' = tcbl2 /\
                         rtbl' = rtbl /\ rgrp' = rgrp /\ 
                         v_ret = (V$ OS_NO_ERR)) (* case: post q success *)
                 \/ (exists x y pwl wls tid p t_opt m msg sus,
                         EcbMod.get ecbls dynrefcmsgQ_addr = Some (absmsgq x y pwl, wls) /\ wls <> nil /\
                         GetHWait tcbls wls tid /\
                         TcbMod.get tcbls tid = Some (p, wait (os_stat_q dynrefcmsgQ_addr) t_opt, m, sus) /\
                         ecbls' = EcbMod.set ecbls dynrefcmsgQ_addr (absmsgq nil y pwl, remove_tid tid wls) /\
                         tcbls' = TcbMod.set tcbls tid (p, rdy,msg, sus) /\
                         (* changed value because of OS_EventTaskRdy *)
                         exists next prev wt tcbx tcby tcbbitx tcbbity,
                         exists bitx bity vl vl' i1 stat,
                         p = ((tcby<<ᵢ$ 3)+ᵢtcbx) /\
                         nth_val' (Z.to_nat (Int.unsigned tcby)) OSMapVallist = Vint32 bity /\
                         nth_val' (Z.to_nat (Int.unsigned tcbx)) OSMapVallist = Vint32 bitx /\
                         (* new OSTCBList  *)
                         nth_val' (Z.to_nat (Int.unsigned p)) ptbl  = (Vptr tid) /\ tid <> vhold /\
                         tcblist_get (Vptr tid) p1 (tcbl1 ++ (tcbcur::tcbl2)) = Some vl /\
                         tcbvl = set_node (Vptr tid) vl' p1 (tcbl1 ++ (tcbcur::tcbl2)) /\
                         vl = (next::prev::(Vptr dynrefcmsgQ_addr)::m::(Vint32 wt)::(Vint32 stat)::(Vint32 p)::(Vint32 tcbx)::(Vint32 tcby)::tcbbitx::tcbbity::nil)%list /\
                         vl' = (next::prev::Vnull::msg::(Vint32 Int.zero)::(Vint32 (Int.and stat (Int.not ($ OS_STAT_Q))))::(Vint32 p)::(Vint32 tcbx)::(Vint32 tcby)::tcbbitx::tcbbity::nil)%list /\
                        (* new OSRdyTbl  *)
                         nth_val' (Z.to_nat (Int.unsigned tcby)) rtbl = Vint32 i1 /\
                         rtbl' = update_nth_val (Z.to_nat (Int.unsigned tcby)) rtbl (Vint32 (Int.or i1 bitx)) /\
                        (* value of return *)
                         v_ret = (V$ OS_NO_ERR)
                          ) (* case: exist tasks waiting for queue *)
              ) |] **
      (* DynamicRefactorInv *)
      DynamicRefactorINV ecbls' **
      (* logic vars *)
      [| logicl = logic_lv pl::  logic_val cfglp::  logic_code s ::
      logic_val v_ret :: (logic_isr isr) :: (logic_ier er) :: (logic_is is) :: (logic_abstcb tcbls) :: (logic_absecb ecbls) :: (logic_val (Vptr ct)) ::
      (logic_val p1) :: (logic_val p2) ::  (logic_lv rtbl) :: (logic_val rgrp) ::
      (logic_llv tcbl1) :: (logic_lv tcbcur) :: (logic_llv tcbl2) :: 
      nil |]).

Theorem doRefactorISRPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (doRefactorISRPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
  hnf. intros. apply GoodFunAsrt_err_sllseg.
  hnf. intros. apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition doRefactorISRPost : fpost :=
 fun vl v ll ct=> mkfunasrt (doRefactorISRPostGood vl v ll ct).

Definition doRefactorISR_spec: fspec:= (doRefactorISRPre, doRefactorISRPost, (Tptr Tvoid, (Tint32::nil))).
(******************************************************* OSIpc ********************************************************)
Definition OSIPC_broad_nodup (O : osabst) : Prop :=
  exists broadstack,  
  get O ipcbroadid = Some (osipcbroad broadstack) /\ (NoDup broadstack).

Definition OSIPC_broad (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
  | (opv, O2) =>
     opv = None /\ 
     exists ipcgr corenum, vl = Vint32 ipcgr :: Vint32 corenum :: nil /\
     Int.and ipcgr ($ IPC_MESSAGE_RDY) <> ($ IPC_MESSAGE_RDY) /\
     Int.and ipcgr ($ IPC_MESSAGE_ACK) <> ($ IPC_MESSAGE_ACK) /\ 
     Int.and ipcgr ($ IPC_MESSAGE_BROAD) = ($ IPC_MESSAGE_BROAD) /\ 
     Int.lt ($ -1) corenum = true /\ 
     Int.ltu corenum ($ 8) = true /\
     exists broadstack,  
        get O1 ipcbroadid = Some (osipcbroad broadstack) /\
     O2 = Some (set O1 ipcbroadid (osipcbroad ((Z.to_nat (Int.unsigned corenum))::broadstack)))
  end.

Definition OSIPC_computeinfos (ipcgr: int32) (corenum : int32) eid :Prop :=
    ((Int.and ipcgr ($ CORE0_IPC) = ($ CORE0_IPC) /\ DNUM <> 0 /\ corenum = ($ 0)) \/
    Int.and ipcgr ($ CORE0_IPC) <> ($ CORE0_IPC) /\ (
    (Int.and ipcgr ($ CORE1_IPC) = ($ CORE1_IPC) /\ DNUM <> 1 /\ corenum = ($ 1)) \/ 
      Int.and ipcgr ($ CORE1_IPC) <> ($ CORE1_IPC) /\ (
    (Int.and ipcgr ($ CORE2_IPC) = ($ CORE2_IPC) /\ DNUM <> 2 /\ corenum = ($ 2)) \/
      Int.and ipcgr ($ CORE2_IPC) <> ($ CORE2_IPC) /\ (
    (Int.and ipcgr ($ CORE3_IPC) = ($ CORE3_IPC) /\ DNUM <> 3 /\ corenum = ($ 3)) \/ 
      Int.and ipcgr ($ CORE3_IPC) <> ($ CORE3_IPC) /\ (
    (Int.and ipcgr ($ CORE4_IPC) = ($ CORE4_IPC) /\ DNUM <> 4 /\ corenum = ($ 4)) \/
      Int.and ipcgr ($ CORE4_IPC) <> ($ CORE4_IPC) /\ (
    (Int.and ipcgr ($ CORE5_IPC) = ($ CORE5_IPC) /\ DNUM <> 5 /\ corenum = ($ 5)) \/
      Int.and ipcgr ($ CORE5_IPC) <> ($ CORE5_IPC) /\ (
    (Int.and ipcgr ($ CORE6_IPC) = ($ CORE6_IPC) /\ DNUM <> 6 /\ corenum = ($ 6)) \/
      Int.and ipcgr ($ CORE6_IPC) <> ($ CORE6_IPC) /\ (
    (Int.and ipcgr ($ CORE7_IPC) = ($ CORE7_IPC) /\ DNUM <> 7 /\ corenum = ($ 7)) \/
      Int.and ipcgr ($ CORE7_IPC) <> ($ CORE7_IPC) /\ 
    corenum = ($ (Zneg xH)))))))))) /\ 
    ( Int.and ipcgr ($ IPC_MESSAGE_RDY) = ($ IPC_MESSAGE_RDY) /\ 
    nth_error OSIPCSem_val (Z.to_nat (Int.unsigned corenum)) = Some eid  \/ 
    Int.and ipcgr ($ IPC_MESSAGE_RDY) <> ($ IPC_MESSAGE_RDY) /\
    (Int.and ipcgr ($ REFACTOR_RDY) = ($ REFACTOR_RDY) /\
      eid = dynrefcmsgQ_addr \/ 
      Int.and ipcgr ($ REFACTOR_RDY) <> ($ REFACTOR_RDY) /\
    (Int.and ipcgr ($ IPC_MESSAGE_ACK) = ($ IPC_MESSAGE_ACK) /\ 
    nth_error OSSendSem_val (Z.to_nat (Int.unsigned corenum)) = Some eid \/ 
    Int.and ipcgr ($ IPC_MESSAGE_ACK) <> ($ IPC_MESSAGE_ACK) /\ (
    Int.and ipcgr ($ IPC_MESSAGE_BROAD) = ($ IPC_MESSAGE_BROAD) /\
    eid = OSSemShared_val \/
    Int.and ipcgr ($ IPC_MESSAGE_BROAD) <> ($ IPC_MESSAGE_BROAD))))
    ).

Definition OSIPC_aspec (dnum: nat) (ipcgr: int32) (corenum : int32) eid v' cfglp: spec_code := 
  clearipc dnum (Vint32 ipcgr) ;; 
  ( ASSUME (fun O : osabst => Int.eq corenum ($ (Zneg xH)) = true) ?? 
  (* rdy and ack cases : *)
  ( ASSUME (fun O : osabst => Int.and ipcgr ($ IPC_MESSAGE_RDY) = ($ IPC_MESSAGE_RDY) \/ 
    Int.and ipcgr ($ IPC_MESSAGE_ACK) = ($ IPC_MESSAGE_ACK)) ;; sem_post_ipc (Vptr eid :: v' :: nil)) ?? 
  (* dyn case : *)
  doRefactorISR_aspec ((Vint32 corenum::nil)++(cfglp::v' ::nil)) ??
  (* broad case : *)
  ( ASSERT OSIPC_broad_nodup ;; OSIPC_broad (|Vint32 ipcgr :: Vint32 corenum :: nil|) ;; sem_post_ipc (Vptr eid :: v' :: nil)) ?? 
  (* otherwise *)
    ASSUME (fun O : osabst => Int.and ipcgr ($ IPC_MESSAGE_RDY) <> ($ IPC_MESSAGE_RDY) /\
    Int.and ipcgr ($ REFACTOR_RDY) <> ($ REFACTOR_RDY) /\
    Int.and ipcgr ($ IPC_MESSAGE_ACK) <> ($ IPC_MESSAGE_ACK) /\ 
    Int.and ipcgr ($ IPC_MESSAGE_BROAD) <> ($ IPC_MESSAGE_BROAD))).


Definition OS_IpcPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX ir er si i s vnest vlock corenum eid v',
  (* corecommuinv ex variables *)
  EX recvh ipcbroadl broadvl cptrl memlls ipcgrm ,
  EX cfglp, 
  (* IPS SEM POST precondition's ex variables *)
  EX ecbls p1 p2 tcbl1 tcbcur tcbl2 tcbls vhold scapl mcapl qcapl rtbl rgrp ptbl ptls t,
  <|| (spec_code_cons (OSIPC_aspec (Z.to_nat DNUM) ipcgrm corenum eid v' cfglp) s) ||> ** 
    Aisr (isrupd ir i%nat true) **
    ([|i%nat = 1%nat|] ** Aier (ierupd er i%nat false) \\//
    [|i%nat <> 1%nat|] ** Aier (ierupd er i%nat true)) **
    Aie false ** 
    Ais (i%nat :: si) **
    Acs nil ** 
    [| isr_is_prop (isrupd ir i%nat true) (i%nat :: si) |] **
    GV OSIntNesting @ long |-> Vint32 vnest **
    GV OSLockNesting @ long |-> Vint32 vlock **
    [| Int.eq vnest Int.zero = false |] **
    HcurCore curcore **
    HipcrecvHeap recvh **
    Hipcsem OSIPCSem_val **
    Hipcsendsem OSSendSem_val **
    [| length OSIPCSem_val  = 8%nat |] **
    [| length OSSendSem_val  = 8%nat |] **
    [| CORESEM_INECB_P ecbls |] **
    Hipcsemshared OSSemShared_val **
    Hipcbroad ipcbroadl **
    Hipcgr ipcgrm **
    AOSIPCMem cptrl memlls**
    [| RLH_IpcRecvHeap_P memlls recvh |] **
    AOSIPCSem IPCSem_ptrl **
    AOSIPCSendSem IPCSendSem_ptrl **
    AOSIPCSemShared OSSemShared_val **
    AOSIPCBroadList broadvl ipcbroadl **
    AOSIPCGRinfo ipcgrm ** 
    [| OSIPC_computeinfos ipcgrm corenum eid |] **
    DynamicRefactorINV ecbls **
    (* IPS SEM POST precondition *)
    (     [| exists d, EcbMod.get ecbls eid = Some d |] **
           EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
           AOSUnMapTbl **
           AOSMapTbl **
           AOSRdyTblGrp rtbl rgrp **
           AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold **
           AOSTCBList p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
           HTCBList tcbls ** HTime t ** HCurTCB ct **
           [| RH_TCBList_ECBList_P ecbls tcbls ct|] **
           [| RH_CurTCB ct tcbls|] **
           [| logicl = (logic_isr ir) :: (logic_ier er) :: (logic_ie false) ::
                        (logic_is si) :: (logic_hid i) ::  
                        (logic_val (Vptr eid)) :: logic_code s ::
                         (logic_abstcb tcbls) :: (logic_absecb ecbls) :: (logic_val (Vptr ct)) ::
                         (logic_val p1) :: (logic_val p2) ::  (logic_lv rtbl) :: (logic_val rgrp) ::
                         (logic_llv tcbl1) :: (logic_lv tcbcur) :: (logic_llv tcbl2) :: nil |]) **
    [|vl =  nil|] ** 
    p_local OSLInv ct init_lg.

Theorem OS_IpcPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OS_IpcPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.  
  cbn;intros. apply GoodFunAsrt_err_sllseg.
  cbn;intros. apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition OS_IpcPre: fpre :=
  fun vl ll ct=> mkfunasrt (OS_IpcPreGood vl ll ct).

Definition OS_IpcPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX ir er si i s vnest vlock eid,
  (* corecommuinv ex variables *)
  EX recvh ipcbroadl broadvl cptrl memlls ipcgrm ,
   (* IPS SEM POST postcondition's ex variables *)
  EX ecbls p1 p2 tcbl1 tcbcur tcbl2 tcbls vhold scapl mcapl qcapl rtbl rgrp ptbl ptls t
                 ecbls' tcbls' tcbvl tcbl1' tcbcur' tcbl2' rtbl' rgrp',
    <|| s ||> ** 
    Aisr (isrupd ir i%nat true) **
    ([|i%nat = 1%nat|] ** Aier (ierupd er i%nat false) \\//
    [|i%nat <> 1%nat|] ** Aier (ierupd er i%nat true)) ** 
    Aie false **
    Ais (i%nat :: si) **
    Acs nil ** 
    [| isr_is_prop (isrupd ir i%nat true) (i%nat :: si) |] **
    GV OSIntNesting @ long |-> Vint32 vnest **
    GV OSLockNesting @ long |-> Vint32 vlock **
    [| Int.eq vnest Int.zero = false |] **
    HcurCore curcore **
    HipcrecvHeap recvh **
    Hipcsem OSIPCSem_val **
    Hipcsendsem OSSendSem_val **
    [| length OSIPCSem_val  = 8%nat |] **
    [| length OSSendSem_val  = 8%nat |] **
    [| CORESEM_INECB_P ecbls' |] **
    Hipcsemshared OSSemShared_val **
    Hipcbroad ipcbroadl **
    Hipcgr ipcgrm **
    AOSIPCMem cptrl memlls**
    [| RLH_IpcRecvHeap_P memlls recvh |] **
    AOSIPCSem IPCSem_ptrl **
    AOSIPCSendSem IPCSendSem_ptrl **
    AOSIPCSemShared OSSemShared_val **
    AOSIPCBroadList broadvl ipcbroadl **
    AOSIPCGRinfo ipcgrm ** 
    DynamicRefactorINV ecbls' **
    (* IPS SEM POST postcondition*)
    (
          [| exists d, EcbMod.get ecbls eid = Some d |] **
           EvtInv ecbls' p1 tcbvl tcbls' vhold scapl mcapl qcapl **
           AOSUnMapTbl **
           AOSMapTbl **
           AOSRdyTblGrp rtbl' rgrp' **
           AOSTCBPrioTbl ptbl rtbl' tcbls' ptls vhold **
           AOSTCBList p1 p2 tcbl1' (tcbcur'::tcbl2') rtbl' ct tcbls' **
           HTCBList tcbls' ** HTime t ** HCurTCB ct **
           [| RH_TCBList_ECBList_P ecbls' tcbls' ct|] **
           [| RH_CurTCB ct tcbls' |] **
           [| logicl = (logic_isr ir) :: (logic_ier er) :: (logic_ie false) ::
                        (logic_is si) :: (logic_hid i) :: 
                        (logic_val (Vptr eid)) :: logic_code s :: 
                         (logic_abstcb tcbls) :: (logic_absecb ecbls) :: (logic_val (Vptr ct)) ::
                         (logic_val p1) :: (logic_val p2) ::  (logic_lv rtbl) :: (logic_val rgrp) ::
                         (logic_llv tcbl1) :: (logic_lv tcbcur) :: (logic_llv tcbl2) :: nil |] **
           [| tcbvl = (tcbl1' ++ (tcbcur'::tcbl2')) |] )**
    [|vl =  nil /\ v = None|] **
    p_local OSLInv ct init_lg.

Theorem OS_IpcPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_IpcPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
  cbn;intros. apply GoodFunAsrt_err_sllseg.
  cbn;intros. apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition OS_IpcPost : fpost :=
 fun vl v ll ct=> mkfunasrt (OS_IpcPostGood vl v ll ct).

Definition OS_Ipc_spec : fspec:= (OS_IpcPre,OS_IpcPost,(Tvoid, nil)). 

Require Import os_program.

(* BuildRetA' os_api OSTaskDel taskdelapi vl  OSLInv tid init_lg *)
Definition OSTaskDelPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX s i er,
    ( Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
      [| logicl =  logic_code s :: nil |] **
      [| vl = Vint32 i :: nil |] ** 
      <|| spec_code_cons (taskdelcode (Vint32 i::nil))  s ||> **  
      p_local OSLInv ct init_lg).

Theorem OSTaskDelPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSTaskDelPre' vl ll ct).
Proof.
 simpl.
 tauto.
Qed.

Definition OSTaskDelPre : fpre :=
  fun vl ll ct => mkfunasrt (OSTaskDelPreGood vl ll ct).

Definition OSTaskDelPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s i er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_code s  :: nil |] **
       [| vl = Vint32 i :: nil |] ** 
       (* [| v = Some (Vint32 (Int.repr OS_TASK_DEL_IDLE)) \/
         v = Some (Vint32 (Int.repr OS_PRIO_INVALID)) \/
         v = Some (Vint32 (Int.repr OS_TASK_DEL_ERR))  \/ 
         v = Some (Vint32 (Int.repr OS_TASK_DEL_SOME_MUTEX_OWNER)) \/
         v = Some (Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT)) \/
         v = Some (Vint32 (Int.repr OS_NO_ERR)) 
       |] ** *)
     <|| s ||> ** p_local OSLInv ct init_lg).

Theorem OSTaskDelPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSTaskDelPost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSTaskDelPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSTaskDelPostGood vl v ll ct).

Definition OSTaskDel_spec : fspec:= (OSTaskDelPre,OSTaskDelPost,(Tint8, Tint8 ::nil)).

Definition OSSampleSendToDomainPre' (vl: vallist) (logicl: list logicvar) ct:=
  EX  s er pptr msgptr tm ori_msg_vl mlen pin cHeapl
      dstkportpl dstkportpl1 dstkportp dstkportpl2
      headptr dportl dportmsgll dpptrl dportls dstportp
      ndstpptrn ndstportupd dportl' dportmsgll' otherpl' othermsgll'
      otherppl otherpl othermsgll dportls1 dportls2 dportls1' dportls2'
      dportls' ndstportupdh ndstport kportls chanls vsem vsdstcl cHeape cHeapt
      pcn pd pid pst dstpin dstpout pm ppcn ppd ppid ppst pout srcmsg
      chanpl chanl chandstkportll kportpl kportl 
      kpaddr chanptr kpst cid cdn dstkpst nextdst corehd corepl,
  ( (
      EX csemid,
      <|| spec_code_cons (samplepost_sendmemcpy_aux_Outcore (S (length dstkportpl2))
          (Vptr pptr :: Vptr msgptr ::
          Vint32 (Int.repr (Z.of_nat (length dstkportpl))) :: vsem :: vsdstcl)) s ||> **
      [| vsem = Vint32 (Int.repr (Z.of_nat csemid)) |] **
      [| Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstcl |] **
      [| get chanls chanptr = Some (cid, cdn, dstkportpl, OutcoreC csemid) |] **
      [| pcn <> Z.to_nat DNUM |] **
      [| dportl' = dportl |] **
      [| dportmsgll' = dportmsgll |] **
      [| otherpl' = update_nth (vallist) ndstpptrn otherpl ndstportupd |] **
      [| othermsgll' = update_nth (list vallist) ndstpptrn othermsgll (ori_msg_vl::nil) |] **
      [| dportls2' = (set dportls2 dstportp ndstportupdh) |] **
      [| dportls1' = dportls1 |] **
      [| get dportls2 dstportp = Some (pcn, pd, pid,
          DestinationP nextdst, pst, dstpin, dstpout, SamplePort pm) |] **
      [| nth_error otherppl ndstpptrn = Some dstportp |] **
      [| nth_error otherpl ndstpptrn = Some ndstport |] **
      [| RLH_OtherPortPtrList otherppl otherpl othermsgll dportls2 |] **
      [| Channel_dstkport_Sample_OutcoreC otherppl chanptr dstkportpl kportls dportls2 |]
    ) \\// 
    (
      <|| spec_code_cons (samplepost_sendmemcpy_aux_Incore (S (length dstkportpl2))
        (Vptr pptr :: Vptr msgptr ::
        Vint32 (Int.repr (Z.of_nat (length dstkportpl))) :: vsem :: vsdstcl)) s ||> **
      [| vsem = Vnull |] **
      [| Forall (fun (v:val) => v = Vnull) vsdstcl |] **
      [| get chanls chanptr = Some (cid, cdn, dstkportpl, IncoreC) |] **
      [| pcn = Z.to_nat DNUM |] **
      [| dportl' = update_nth (vallist) ndstpptrn dportl ndstportupd |] **
      [| dportmsgll' = update_nth (list vallist) ndstpptrn dportmsgll (ori_msg_vl::nil) |] **
      [| otherpl' = otherpl |] **
      [| othermsgll' = othermsgll |] **
      [| dportls1' = (set dportls1 dstportp ndstportupdh) |] **
      [| dportls2' = dportls2 |] **
      [| get dportls1 dstportp = Some (pcn, pd, pid,
          DestinationP nextdst, pst, dstpin, dstpout, SamplePort pm) |] **
      [| nth_error dpptrl ndstpptrn = Some dstportp |] **
      [| nth_error dportl ndstpptrn = Some ndstport |] **
      [| RL_PortPtrList headptr dportl dpptrl |] **
      [| RL_PortAttr dpptrl dportl |] **
      [| RLH_Domainportl headptr dportl dportmsgll dportls1 |] **
      [| R_Kernelport_DomainPort kportpl kportl dportl dpptrl |] **
      [| Channel_dstkport_Sample_IncoreC otherppl chanptr dstkportpl kportls dportls1 |]
    )
  ) **
  [| dstkportpl = (dstkportpl1 ++ dstkportp :: dstkportpl2) |] **
  [| (length dstkportpl = length vsdstcl)%nat |] **
  Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
  dmportp_sllseg headptr Vnull dportl dportmsgll OS_Port_V_nextPort **
  OtherPortPtrList otherppl otherpl othermsgll **
  AOSCorePortPtrList corehd corepl dportls1 **
  HTime tm **
  AOSTime (Vint32 tm) **
  Hdomainportl dportls **
  Hkernelport kportls **
  Hchannell chanls **
  HCoreHeap cHeapl cHeape cHeapt **
  Aarray msgptr (Tarray char_t (S (length ori_msg_vl))) ((Vint32 mlen) :: ori_msg_vl) **
  
  [| vl = (Vptr dstportp) :: (Vptr msgptr) :: (Vint32 pin) :: nil |] **
  
  [| Get_heapl_addrval cHeapl msgptr (S (length ori_msg_vl)) (Vint32 mlen :: ori_msg_vl) |] **
  [| Int.unsigned mlen <= CHANNEL_CACHE_SZIE |] **
  [| S (length ori_msg_vl) = Z.to_nat (Int.unsigned mlen + 1) |] **

  [| struct_type_vallist_match' OS_Port_Seg_dls ndstportupd |] **
  [| OS_Port_V_msgInTick ndstportupd = Some (Vint32 pin) |] **
  [| OS_Port_V_msgOutTick ndstportupd = Some (Vint32 tm) |] **
  [| forall (m:nat), (m < 18)%nat -> (m <> 8)%nat -> (m <> 9)%nat -> 
      nth_val m ndstportupd = nth_val m ndstport |] **
  [| dportls' = (set dportls dstportp ndstportupdh) |] **
  
  [| get kportls dstkportp =
      Some (pid, Some dstportp, Some chanptr, pcn, dstkpst)  |] **
  [| ndstportupdh = (pcn, pd, pid,
      DestinationP nextdst, pst, Z.to_nat (Int.unsigned pin),
        Z.to_nat (Int.unsigned tm), SamplePort (Some ori_msg_vl)) |] **

  [| join dportls1 dportls2 dportls |] **
  [| RLH_Channel otherppl chanpl chanl chandstkportll chanls kportls dportls1 dportls2 |] **
  [| R_KernelPortIDTbl_ChannelIDTbl kportpl kportl chanpl chanl chandstkportll kportls dportls1 dportls2 |] **

  [| array_type_vallist_match char_t ((Vint32 mlen) :: ori_msg_vl) |] **

  [| get dportls1 pptr = Some (ppcn, ppd, ppid, SourceP, ppst,
        Z.to_nat (Int.unsigned pin), pout, SamplePort (Some srcmsg)) |] **
  [| get kportls kpaddr = Some (ppid, Some pptr, Some chanptr, ppcn, kpst) |] **
  
  [| (Z.of_nat pcn <> DNUM ->
        nth_error vsdstcl (length dstkportpl1) =
            Some (Vint32 (Int.repr (Z.of_nat pcn)))) |] **
  
  [| nodup_dport kportls |] **
  [| logicl = (logic_code s) :: (logic_ier er) :: (logic_lv ori_msg_vl) :: 
              (logic_val (Vint32 mlen)) :: (logic_lanlv cHeapl) :: (logic_val (Vptr dstkportp)) ::
              (logic_la dstkportpl1) :: (logic_la dstkportpl2) :: (logic_val headptr) ::
              (logic_llv dportl) :: (logic_lllv dportmsgll) :: (logic_la dpptrl) :: 
              (logic_absdmport dportls) :: (logic_absdmport dportls1) :: (logic_absdmport dportls2) :: 
              (logic_hid ndstpptrn) :: (logic_val (Vint32 tm)) :: (logic_val (Vptr pptr)) ::
              (logic_la otherppl) :: (logic_llv otherpl) :: (logic_lllv othermsgll) ::
              (logic_abskport kportls) :: (logic_abschan chanls) :: (logic_val vsem) ::
              (logic_lv chanpl) :: (logic_llv chanl) :: (logic_lla chandstkportll) ::
              (logic_lv kportpl) :: (logic_llv kportl) :: (logic_val (Vptr chanptr)) :: 
              (logic_lv vsdstcl) :: (logic_latv cHeape) :: (logic_latlv cHeapt) :: 
              (logic_val corehd) :: (logic_la corepl) ::  nil |] **
  p_local OSLInv ct init_lg.

Theorem OSSampleSendToDomainPreGood (vl: vallist) ll ct:
  GoodFunAsrt(OSSampleSendToDomainPre' vl ll ct).
Proof.
  GoodFunAsrt_solver. 
  apply GoodFunAsrt_dmportp_sllseg.
  apply GoodFunAsrt_OtherPortPtrList.
Qed.

Definition OSSampleSendToDomainPre: fpre:=
	fun vl ll ct => mkfunasrt(OSSampleSendToDomainPreGood vl ll ct).

Definition OSSampleSendToDomainPost' (vl: vallist) (v: option val) (logicl: list logicvar) ct:=
  EX  s er pptr msgptr tm ori_msg_vl mlen pin cHeapl
      dstkportpl dstkportpl1 dstkportp dstkportpl2
      headptr dportl dportmsgll dpptrl dportls dstportp
      ndstpptrn ndstportupd dportl' dportmsgll' otherpl' othermsgll'
      otherppl otherpl othermsgll dportls1 dportls2 dportls1' dportls2'
      dportls' ndstportupdh kportls chanls vsem vsdstcl cHeape cHeapt
      chanpl chanl chandstkportll kportpl kportl chanptr ndstport
      pcn pd pid pst dstpin dstpout pm nextdst corehd corepl,
  ( (
      EX csemid,
      <|| spec_code_cons (samplepost_sendmemcpy_aux_Outcore (length dstkportpl2)
          (Vptr pptr :: Vptr msgptr ::
          Vint32 (Int.repr (Z.of_nat (length dstkportpl))) :: vsem :: vsdstcl)) s ||> **
      [| vsem = Vint32 (Int.repr (Z.of_nat csemid)) |] **
      [| dportl' = dportl |] **
      [| dportmsgll' = dportmsgll |] **
      [| otherpl' = update_nth (vallist) ndstpptrn otherpl ndstportupd |] **
      [| othermsgll' = update_nth (list vallist) ndstpptrn othermsgll (ori_msg_vl::nil) |] **
      [| get dportls2 dstportp = Some (pcn, pd, pid,
          DestinationP nextdst, pst, dstpin, dstpout, SamplePort pm) |] **
      [| dportls2' = (set dportls2 dstportp ndstportupdh) |] **
      [| dportls1' = dportls1 |] **
      [| nth_error otherpl ndstpptrn = Some ndstport |] **
      [| RLH_OtherPortPtrList otherppl otherpl' othermsgll' dportls2' |] **
      [| Channel_dstkport_Sample_OutcoreC otherppl chanptr dstkportpl kportls dportls2' |]
    ) \\// 
    (
      <|| spec_code_cons (samplepost_sendmemcpy_aux_Incore (length dstkportpl2)
        (Vptr pptr :: Vptr msgptr ::
        Vint32 (Int.repr (Z.of_nat (length dstkportpl))) :: vsem :: vsdstcl)) s ||> **
      [| vsem = Vnull |] **
      [| dportl' = update_nth (vallist) ndstpptrn dportl ndstportupd |] **
      [| dportmsgll' = update_nth (list vallist) ndstpptrn dportmsgll (ori_msg_vl::nil) |] **
      [| otherpl' = otherpl |] **
      [| othermsgll' = othermsgll |] **
      [| get dportls1 dstportp = Some (pcn, pd, pid,
          DestinationP nextdst, pst, dstpin, dstpout, SamplePort pm) |] **
      [| dportls1' = (set dportls1 dstportp ndstportupdh) |] **
      [| dportls2' = dportls2 |] **
      [| nth_error dportl ndstpptrn = Some ndstport |] **
      [| RL_PortPtrList headptr dportl' dpptrl |] **
      [| RL_PortAttr dpptrl dportl' |] **
      [| RLH_Domainportl headptr dportl' dportmsgll' dportls1' |] **
      [| R_Kernelport_DomainPort kportpl kportl dportl' dpptrl |] **
      [| Channel_dstkport_Sample_IncoreC otherppl chanptr dstkportpl kportls dportls1' |]
    )
  ) **
  [| dstkportpl = (dstkportpl1 ++ dstkportp :: dstkportpl2) |] **
  Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
  dmportp_sllseg headptr Vnull dportl' dportmsgll' OS_Port_V_nextPort **
  OtherPortPtrList otherppl otherpl' othermsgll' **
  AOSCorePortPtrList corehd corepl dportls1' **
  HTime tm **
  AOSTime (Vint32 tm) **
  Hdomainportl dportls' **
  Hkernelport kportls **
  Hchannell chanls **
  HCoreHeap cHeapl cHeape cHeapt **
  Aarray msgptr (Tarray char_t (S (length ori_msg_vl))) ((Vint32 mlen) :: ori_msg_vl) **
  
  [| vl = (Vptr dstportp) :: (Vptr msgptr) :: (Vint32 pin) :: nil |] **
  
  [| struct_type_vallist_match' OS_Port_Seg_dls ndstportupd |] **
  [| OS_Port_V_msgInTick ndstportupd = Some (Vint32 pin) |] **
  [| OS_Port_V_msgOutTick ndstportupd = Some (Vint32 tm) |] **
  [| forall (m:nat), (m < 18)%nat -> (m <> 8)%nat -> (m <> 9)%nat -> 
      nth_val m ndstportupd = nth_val m ndstport |] **

  [| dportls' = (set dportls dstportp ndstportupdh) |] **
  [| ndstportupdh = (pcn, pd, pid,
      DestinationP nextdst, pst, Z.to_nat (Int.unsigned pin),
        Z.to_nat (Int.unsigned tm), SamplePort (Some ori_msg_vl)) |] **
  
  [| join dportls1' dportls2' dportls' |] **
  [| RLH_Channel otherppl chanpl chanl chandstkportll chanls kportls dportls1' dportls2' |] **
  [| R_KernelPortIDTbl_ChannelIDTbl kportpl kportl chanpl chanl chandstkportll kportls dportls1' dportls2' |] **

  [| logicl = (logic_code s) :: (logic_ier er) :: (logic_lv ori_msg_vl) :: 
              (logic_val (Vint32 mlen)) :: (logic_lanlv cHeapl) :: (logic_val (Vptr dstkportp)) ::
              (logic_la dstkportpl1) :: (logic_la dstkportpl2) :: (logic_val headptr) ::
              (logic_llv dportl) :: (logic_lllv dportmsgll) :: (logic_la dpptrl) :: 
              (logic_absdmport dportls) :: (logic_absdmport dportls1) :: (logic_absdmport dportls2) :: 
              (logic_hid ndstpptrn) :: (logic_val (Vint32 tm)) :: (logic_val (Vptr pptr)) ::
              (logic_la otherppl) :: (logic_llv otherpl) :: (logic_lllv othermsgll) ::
              (logic_abskport kportls) :: (logic_abschan chanls) :: (logic_val vsem) ::
              (logic_lv chanpl) :: (logic_llv chanl) :: (logic_lla chandstkportll) ::
              (logic_lv kportpl) :: (logic_llv kportl) :: (logic_val (Vptr chanptr)) :: 
              (logic_lv vsdstcl) :: (logic_latv cHeape) :: (logic_latlv cHeapt) ::
              (logic_val corehd) :: (logic_la corepl) :: nil |] **
  [| v = Some (Vint32 (Int.repr OS_NO_ERR)) |] ** 
  p_local OSLInv ct init_lg.

Theorem OSSampleSendToDomainPostGood (vl: vallist) (v: option val) ll ct:
	GoodFunAsrt(OSSampleSendToDomainPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
  apply GoodFunAsrt_dmportp_sllseg.
  apply GoodFunAsrt_OtherPortPtrList.
Qed.

Definition OSSampleSendToDomainPost: fpost:=
	fun vl v ll ct => mkfunasrt(OSSampleSendToDomainPostGood vl v ll ct).

Definition OSSampleSendToDomain_spec: fspec:=
  (OSSampleSendToDomainPre, OSSampleSendToDomainPost, (Tint8, (Tptr OS_Port) :: (Tptr OSMsg_t) :: Tint32 :: nil)).

(* OS_PortTaskRdy *)
(* pre *)
Definition OS_PortTaskRdyPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX msgptr msk vhold tcbls ptbl rtbl rgrp vltcb egrp qid osevent etbl petbl s head headprev tail tailnext  er  mlen ori_msg_vl
  dport qin qout qstart qend qentries qsize portmsgl irportmsgl,
  Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
  AEventNode (Vptr qid) osevent etbl petbl DPort ** (*has pure properties*)
  <||s||> **
  AOSUnMapTbl **
  AOSMapTbl **
  AOSRdyTblGrp rtbl rgrp ** (*has pure properties*)
  GAarray OSTCBPrioTbl (Tarray (Tptr OS_TCB) 64) ptbl **
  tcbdllseg head headprev tail tailnext vltcb **
  [| ptr_in_tcblist (Vptr ct) head vltcb |] **
  [| array_type_vallist_match (Tptr OS_TCB) ptbl /\ length ptbl = 64%nat |] **
  [| RL_RTbl_PrioTbl_P rtbl ptbl vhold |] **
  [| R_PrioTbl_P ptbl tcbls vhold |] **
  [| R_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls |] **
  [| TCBList_P head vltcb rtbl tcbls |] **

  [| vl = Vptr qid:: Vptr msgptr:: Vint32 msk::nil |] **
  
  [| V_OSEventGrp osevent = Some (Vint32 egrp) /\ egrp <> Int.zero |] **
  [| logicl = logic_val (Vptr vhold) :: logic_val head ::
              logic_val headprev :: logic_val tail :: logic_val tailnext ::
              logic_lv ptbl :: logic_lv rtbl :: logic_val rgrp ::
              logic_lv osevent :: logic_lv etbl :: logic_lv petbl ::
              logic_code s :: logic_abstcb tcbls :: logic_llv vltcb ::
              logic_val (Vint32 egrp) ::  logic_ier er :: 
              logic_val (Vint32 mlen) :: logic_lv ori_msg_vl ::
              logic_lv dport :: logic_val (Vptr qin) :: logic_val (Vptr qout) ::
              logic_val (Vptr qstart) :: logic_val (Vptr qend) ::
              logic_val (Vint32 qentries) :: logic_val (Vint32 qsize) ::
              logic_llv portmsgl :: nil |] **       
  Aarray msgptr (Tarray char_t (S (length ori_msg_vl))) ((Vint32 mlen) :: ori_msg_vl) **
  [| S (length ori_msg_vl) = Z.to_nat (Int.unsigned mlen + 1) |] **       
  APortStruct qid dport **
  dmportp_sllseg_qport_msg qout qin qstart qend ∘ (Int.unsigned qentries) portmsgl **
  dmportp_sllseg_qport_msg qin qout qstart qend ∘ (Int.unsigned qsize - Int.unsigned qentries) irportmsgl **
  [| OS_Port_V_OSQEnd dport = Some (Vptr qend) |] **
  [| OS_Port_V_OSQStart dport = Some (Vptr qstart) |] **
  [| OS_Port_V_OSQIn dport = Some (Vptr qin) |] **
  [| OS_Port_V_OSQOut dport = Some (Vptr qout) |] **
  [| OS_Port_V_OSQEntries dport = Some (Vint32 qentries) |] **
  [| OS_Port_V_OSQSize dport = Some (Vint32 qsize) |] **
  [| OS_Port_V_mode dport = Some (V$ QUEUE) |] **
  [| struct_type_vallist_match' OS_Port_Seg_dls dport |] **
  [| Int.unsigned qentries <= Int.unsigned qsize |] **
  [| Int.unsigned mlen <= CHANNEL_CACHE_SZIE |] **
  [| array_type_vallist_match char_t (Vint32 mlen :: ori_msg_vl) |] **
  [| Int.unsigned qsize <= 65535 |] **
  [| Qport_msg_ptrs_P qstart qend qout qin (Int.unsigned qsize) |] **
  p_local OSLInv ct init_lg.
  
Theorem OS_PortTaskRdyPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_PortTaskRdyPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
  apply GoodFunAsrt_APortStruct.
  apply GoodFunAsrt_dmportp_sllseg_qport_msg.
  apply GoodFunAsrt_dmportp_sllseg_qport_msg.
Qed.

Definition OS_PortTaskRdyPre : fpre :=
  fun vl ll ct => mkfunasrt (OS_PortTaskRdyPreGood vl ll ct).

Definition OS_PortTaskRdyPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX vhold tcbls vltcb vltcb' ptbl rtbl rtbl' rgrp rgrp' egrp egrp' etbl etbl' petbl qid osevent osevent' s head headprev tail tailnext msgptr msk
          er mlen ori_msg_vl dport qin qout qstart qend qentries qsize portmsgl,
    Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
    AEventNode (Vptr qid) osevent' etbl' petbl DPort ** <||s||> **
    AOSUnMapTbl **
    AOSMapTbl **
    AOSRdyTblGrp rtbl' rgrp' **

    GAarray OSTCBPrioTbl (Tarray (Tptr OS_TCB) 64) ptbl **    
    tcbdllseg head headprev tail tailnext vltcb' **
    [| vl = Vptr qid:: Vptr msgptr:: Vint32 msk::nil |] **
    
    [| ptr_in_tcblist (Vptr ct) head vltcb'|] **
    [| array_type_vallist_match (Tptr OS_TCB) ptbl /\ length ptbl = 64%nat |] ** (*same as in pre*)
    [| RL_RTbl_PrioTbl_P rtbl' ptbl vhold |] **
    [| R_PrioTbl_P ptbl tcbls vhold |] ** (*same as in pre*)
    [| R_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls |] ** (*same as in pre*)
    [| TCBList_P head vltcb rtbl tcbls |] ** (*same as in pre*)
    
    [| logicl = logic_val (Vptr vhold) :: logic_val head ::
    logic_val headprev :: logic_val tail :: logic_val tailnext ::
    logic_lv ptbl :: logic_lv rtbl :: logic_val rgrp ::
    logic_lv osevent :: logic_lv etbl :: logic_lv petbl ::
    logic_code s :: logic_abstcb tcbls :: logic_llv vltcb ::
    logic_val (Vint32 egrp) :: logic_ier er :: 
    logic_val (Vint32 mlen) :: logic_lv ori_msg_vl ::
    logic_lv dport :: logic_val (Vptr qin) :: logic_val (Vptr qout) ::
    logic_val (Vptr qstart) :: logic_val (Vptr qend) ::
    logic_val (Vint32 qentries) :: logic_val (Vint32 qsize) ::
    logic_llv portmsgl :: nil |] **   
    Aarray msgptr (Tarray char_t (S (length ori_msg_vl))) ((Vint32 mlen) :: ori_msg_vl) **
    [| S (length ori_msg_vl) = Z.to_nat (Int.unsigned mlen + 1) |] **       
    (EX irportmsgl, APortStruct qid dport **
    dmportp_sllseg_qport_msg qout qin qstart qend ∘ (Int.unsigned qentries) portmsgl **
    dmportp_sllseg_qport_msg qin qout qstart qend ∘ (Int.unsigned qsize - Int.unsigned qentries) irportmsgl 
    \\//
    EX irportmsgl', APortStruct qid
    (update_nth_val 17 (update_nth_val 14 dport (Vptr (dmportp_sllseg_qport_msg_next qin qstart qend)))
       (Vint32 (qentries +ᵢ  $ 1))) **
    dmportp_sllseg_qport_msg (dmportp_sllseg_qport_msg_next qin qstart qend) qout qstart qend
    (Init.Nat.pred ∘ (Int.unsigned qsize - Int.unsigned qentries)) irportmsgl' **
    dmportp_sllseg_qport_msg qout
    (dmportp_sllseg_qport_msg_next qin qstart qend) qstart qend
    (Z.to_nat (Int.unsigned (qentries +ᵢ  $ 1))) (portmsgl ++ ori_msg_vl :: nil) **
    [| Int.unsigned (qentries +ᵢ  $ 1) <= Int.unsigned qsize |]
    ) **

    EX x y i1 bitx bity,
    [| nth_val' (Z.to_nat (Int.unsigned egrp)) OSUnMapVallist = Vint32 y |] **
    [| nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 i1 |] **
    [| nth_val' (Z.to_nat (Int.unsigned i1)) OSUnMapVallist = Vint32 x |] **
    [| nth_val' (Z.to_nat (Int.unsigned y)) OSMapVallist = Vint32 bity |] **
    [| nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 bitx |] **
    
    [| osevent' = update_nth_val 1 osevent (Vint32 egrp') |] **
    [| etbl' = update_nth_val
                  (Z.to_nat (Int.unsigned y)) etbl (Vint32 (i1&ᵢInt.not bitx)) |] **
              
    (*ret value prio = get highest wait task in etbl*)
    [| v = Some (Vint32 ((y<<ᵢ$ 3)+ᵢx)) |] **

    (*relation between old vltcb and new vltcb*)
    (EX vl vl' next prev eptr msg dly stat prio tcbx tcby tcbbitx tcbbity t,
      [| nth_val' (Z.to_nat (Int.unsigned ((y<<ᵢ$ 3)+ᵢx))) ptbl  = (Vptr (t, Int.zero))
        /\ (t, Int.zero) <> vhold|] **
    [| tcblist_get (Vptr (t, Int.zero)) head vltcb = Some vl /\ struct_type_vallist_match OS_TCB_flag vl|] **
    [| vltcb' = set_node (Vptr (t, Int.zero)) vl' head vltcb |] **
    [| vl = next::prev::eptr::msg::dly::(Vint32 stat)::prio::tcbx::tcby::tcbbitx::tcbbity::nil|] **
    [| vl' = next::prev::Vnull::Vptr OS_PARTITION_MESSAGE_COME_ptr::(Vint32 Int.zero)::(Vint32 (Int.and stat (Int.not msk)))::prio::tcbx::tcby::tcbbitx::tcbbity::nil|] **

    (*relation between data and tcbstat, for proving tcb rdy*)
    [| rel_edata_tcbstat DPort stat |]
    (* ) *) **
    
    (* ( *)EX i1', [| nth_val' (Z.to_nat (Int.unsigned y)) rtbl = Vint32 i1' |] **    
      [| rtbl' = ( if Int.eq (Int.and stat (Int.not msk)) (Int.repr OS_STAT_RDY)
                            then update_nth_val (Z.to_nat (Int.unsigned y)) rtbl (Vint32 (Int.or i1' bitx))
                            else rtbl)|]) **
    
  (*pure properties on old values in AOSRdyTblGrp, keep them in the post condition *)
    [|RL_Tbl_Grp_P rtbl rgrp /\ prio_in_tbl ($ OS_IDLE_PRIO) rtbl|] **
    [|array_type_vallist_match Tint8 rtbl /\ length rtbl = nat_of_Z OS_RDY_TBL_SIZE|] **
    [|rule_type_val_match Tint8 rgrp = true|] **
    [|RL_Tbl_Grp_P etbl (Vint32 egrp)|] **
    [|array_type_vallist_match Tint8 etbl|]
    ** p_local OSLInv ct init_lg.

Theorem OS_PortTaskRdyPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_PortTaskRdyPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
  apply GoodFunAsrt_APortStruct.
  apply GoodFunAsrt_dmportp_sllseg_qport_msg.
  apply GoodFunAsrt_dmportp_sllseg_qport_msg.
  apply GoodFunAsrt_APortStruct.
  apply GoodFunAsrt_dmportp_sllseg_qport_msg.
  apply GoodFunAsrt_dmportp_sllseg_qport_msg.
Qed.

Definition OS_PortTaskRdyPost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_PortTaskRdyPostGood vl v ll ct).


Definition OS_PortTaskRdy_spec: fspec:=
  (OS_PortTaskRdyPre, OS_PortTaskRdyPost, (Tint8, (Tptr OS_Port) :: (Tptr OSMsg_t) :: Tint16 :: nil)).

Definition OSQSendToDomainPre' (vl: vallist) (logicl: list logicvar) ct:=
  (
    EX s er pptr msgptr ori_msg_vl mlen cHeapl
    dstkportpl dstkportpl1 dstkportp dstkportpl2
    dportls dstportp ndstpptrn  
    otherppl otherpl othermsgll dportls1 dportls2 
    kportls chanls vsdstcl cHeape cHeapt
    pcn pd pid pst dstpin dstpout dstsz dstpm ppcn ppid 
    chanpl chanl chandstkportll kportpl kportl 
    kpaddr chanptr kpst cid cdn dstkpst csemid nextdst,
      <|| spec_code_cons (qportpost_send_Outcore (S (length dstkportpl2))
          (Vptr pptr :: Vptr msgptr ::
          Vint32 (Int.repr (Z.of_nat (length dstkportpl))) :: Vint32 (Int.repr (Z.of_nat csemid)) :: vsdstcl)) s ||> **
      [| Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstcl |] **
      [| get chanls chanptr = Some (cid, cdn, dstkportpl, OutcoreC csemid) |] **
      [| Z.of_nat pcn <> DNUM |] **
      [| get dportls2 dstportp = Some (pcn, pd, pid,
          DestinationP nextdst, pst, dstpin, dstpout, QueuePort dstsz dstpm) |] **
      [| nth_error otherppl ndstpptrn = Some dstportp |] **
      [| RLH_OtherPortPtrList otherppl otherpl othermsgll dportls2 |] **
      [| Channel_dstkport_Queue_OutcoreC otherppl chanptr dstkportpl kportls dportls2 |] **
      [| dstkportpl = (dstkportpl1 ++ dstkportp :: dstkportpl2) |] **
      [| (length dstkportpl = length vsdstcl)%nat |] **
      Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
      OtherPortPtrList otherppl otherpl othermsgll **
      Hdomainportl dportls **
      Hkernelport kportls **
      Hchannell chanls **
      HCoreHeap cHeapl cHeape cHeapt **
      Aarray msgptr (Tarray char_t (S (length ori_msg_vl))) ((Vint32 mlen) :: ori_msg_vl) **
      
      [| vl = (Vptr dstportp) :: (Vptr msgptr)  :: nil |] **
      
      [| Get_heapl_addrval cHeapl msgptr (S (length ori_msg_vl)) (Vint32 mlen :: ori_msg_vl) |] **
      [| Int.unsigned mlen <= CHANNEL_CACHE_SZIE |] **
      [| S (length ori_msg_vl) = Z.to_nat (Int.unsigned mlen + 1) |] **

      [| get kportls dstkportp =
          Some (pid, Some dstportp, Some chanptr, pcn, dstkpst)  |] **

      [| join dportls1 dportls2 dportls |] **
      [| RLH_Channel otherppl chanpl chanl chandstkportll chanls kportls dportls1 dportls2 |] **
      [| R_KernelPortIDTbl_ChannelIDTbl kportpl kportl chanpl chanl chandstkportll kportls dportls1 dportls2 |] **

      [| array_type_vallist_match char_t ((Vint32 mlen) :: ori_msg_vl) |] **

      [| get kportls kpaddr = Some (ppid, Some pptr, Some chanptr, ppcn, kpst) |] **
      
      [| (Z.of_nat pcn <> DNUM ->
            nth_error vsdstcl (length dstkportpl1) =
                Some (Vint32 (Int.repr (Z.of_nat pcn)))) |] **
      
      [| nodup_dport kportls |] **
      [| logicl = (logic_code s) :: (logic_ier er) :: (logic_lv ori_msg_vl) :: 
                  (logic_val (Vint32 mlen)) :: (logic_lanlv cHeapl) :: (logic_val (Vptr dstkportp)) ::
                  (logic_la dstkportpl1) :: (logic_la dstkportpl2) :: 
                  (logic_absdmport dportls) :: (logic_absdmport dportls1) :: (logic_absdmport dportls2) :: 
                  (logic_hid ndstpptrn)  :: (logic_val (Vptr pptr)) :: logic_hid csemid::
                  (logic_la otherppl) :: (logic_llv otherpl) :: (logic_lllv othermsgll) ::
                  (logic_abskport kportls) :: (logic_abschan chanls) :: 
                  (logic_lv chanpl) :: (logic_llv chanl) :: (logic_lla chandstkportll) ::
                  (logic_lv kportpl) :: (logic_llv kportl) :: (logic_val (Vptr chanptr)) :: 
                  (logic_lv vsdstcl) :: (logic_latv cHeape) :: (logic_latlv cHeapt) ::
                  nil |] **
      p_local OSLInv ct init_lg
    ) \\// 
    (EX  s er pptr msgptr ori_msg_vl mlen cHeapl
    dstkportpl dstkportpl1 dstkportp dstkportpl2
    headptr dportl dportmsgll dpptrl dportls dstportp
    ndstpptrn  
    otherppl dportls1 dportls2 
    kportls chanls vsdstcl cHeape cHeapt
    pcn pd pid pst dstpin dstpout dstsz dstpm ppcn ppid 
    chanpl chanl chandstkportll kportpl kportl 
    kpaddr chanptr kpst cid cdn dstkpst
    rtbl rgrp ecbls p1 p2 tcbl1 tcbcur tcbl2 tcbls vhold scapl mcapl qcapl ptls ptbl nextdst cportlptr cportpl,
      <|| spec_code_cons (qportpost_send_Incore (S (length dstkportpl2))
        (Vptr pptr :: Vptr msgptr ::
        Vint32 (Int.repr (Z.of_nat (length dstkportpl))) :: Vnull :: vsdstcl)) s ||> **
      [| get chanls chanptr = Some (cid, cdn, dstkportpl, IncoreC) |] **
      [| pcn = Z.to_nat DNUM |] **
      [| get dportls1 dstportp = Some (pcn, pd, pid,
          DestinationP nextdst, pst, dstpin, dstpout, QueuePort dstsz dstpm) |] **
      [| nth_error dpptrl ndstpptrn = Some dstportp |] **
      [| RL_PortAttr dpptrl dportl |] **
      [| RLH_Domainportl headptr dportl dportmsgll dportls1 |] **
      [| R_Kernelport_DomainPort kportpl kportl dportl dpptrl |] **
      [| Channel_dstkport_Queue_IncoreC otherppl chanptr dstkportpl kportls dportls1 |] **
      [| dstkportpl = (dstkportpl1 ++ dstkportp :: dstkportpl2) |] **
      [| RLH_PortPtrINecb headptr dportl dpptrl ecbls |] **
      Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
      dmportp_sllseg headptr Vnull dportl dportmsgll OS_Port_V_nextPort **
      Hdomainportl dportls **
      Hkernelport kportls **
      Hchannell chanls **
      HCoreHeap cHeapl cHeape cHeapt **
      Aarray msgptr (Tarray char_t (S (length ori_msg_vl))) ((Vint32 mlen) :: ori_msg_vl) **
      AOSCorePortPtrList cportlptr cportpl dportls1 **

  [| vl = (Vptr dstportp) :: (Vptr msgptr)  :: nil |] **
  
  [| Get_heapl_addrval cHeapl msgptr (S (length ori_msg_vl)) (Vint32 mlen :: ori_msg_vl) |] **
  [| Int.unsigned mlen <= CHANNEL_CACHE_SZIE |] **
  [| S (length ori_msg_vl) = Z.to_nat (Int.unsigned mlen + 1) |] **

  [| get kportls dstkportp =
      Some (pid, Some dstportp, Some chanptr, pcn, dstkpst)  |] **

  [| join dportls1 dportls2 dportls |] **
  [| RLH_Channel otherppl chanpl chanl chandstkportll chanls kportls dportls1 dportls2 |] **
  [| R_KernelPortIDTbl_ChannelIDTbl kportpl kportl chanpl chanl chandstkportll kportls dportls1 dportls2 |] **

  [| array_type_vallist_match char_t ((Vint32 mlen) :: ori_msg_vl) |] **

  [| get kportls kpaddr = Some (ppid, Some pptr, Some chanptr, ppcn, kpst) |] **
  
  [| nodup_dport kportls |] **
  [| logicl = (logic_code s) :: (logic_ier er) :: (logic_lv ori_msg_vl) :: 
              (logic_val (Vint32 mlen)) :: (logic_lanlv cHeapl) :: (logic_val (Vptr dstkportp)) ::
              (logic_la dstkportpl1) :: (logic_la dstkportpl2) :: (logic_val headptr) ::
              (logic_llv dportl) :: (logic_lllv dportmsgll) :: (logic_la dpptrl) :: 
              (logic_absdmport dportls) :: (logic_absdmport dportls1) :: (logic_absdmport dportls2) :: 
              (logic_hid ndstpptrn)  :: (logic_val (Vptr pptr)) ::
              (logic_la otherppl) :: 
              (logic_abskport kportls) :: (logic_abschan chanls) :: 
              (logic_lv chanpl) :: (logic_llv chanl) :: (logic_lla chandstkportll) ::
              (logic_lv kportpl) :: (logic_llv kportl) :: (logic_val (Vptr chanptr)) :: 
              (logic_lv vsdstcl) :: (logic_latv cHeape) :: (logic_latlv cHeapt) ::
              logic_lv ptbl :: logic_lv rtbl:: logic_abstcb tcbls::
              logic_val (Vptr vhold) :: (logic_llv scapl) :: (logic_llv mcapl) :: (logic_llv qcapl) :: 
              logic_val p1:: logic_val p2::
              logic_llv tcbl1:: logic_lv tcbcur:: logic_llv tcbl2:: logic_val (Vptr ct)::
              logic_val rgrp:: logic_absecb ecbls:: logic_val cportlptr:: logic_la cportpl ::
              nil |] **
  p_local OSLInv ct init_lg **
  AOSMapTbl ** AOSUnMapTbl ** AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold ** 
  AOSTCBList p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
  AOSRdyTblGrp rtbl rgrp **(* tcblist & rdy table *)
  HTCBList tcbls **  HCurTCB ct ** 
  EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl**
  [| RH_TCBList_ECBList_P ecbls tcbls ct|] **
  [| RH_CurTCB ct tcbls|] ** 
  CoreCommuInv ecbls **
  tcbdllflag p1 (tcbl1 ++ (tcbcur::tcbl2))
  ).

Theorem OSQSendToDomainPreGood (vl: vallist) ll ct:
  GoodFunAsrt(OSQSendToDomainPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
  apply GoodFunAsrt_OtherPortPtrList.
  apply GoodFunAsrt_dmportp_sllseg.
  simpl. intros. apply GoodFunAsrt_err_sllseg.
  simpl. intros. apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition OSQSendToDomainPre: fpre:=
  fun vl ll ct => mkfunasrt(OSQSendToDomainPreGood vl ll ct).


Definition OSQSendToDomainPost' (vl: vallist) (v: option val) (logicl: list logicvar) ct:=
  (EX  s er pptr msgptr ori_msg_vl mlen cHeapl
      dstkportpl dstkportpl1 dstkportp dstkportpl2 dportls dstportp
      ndstpptrn  otherpl' othermsgll'
      otherppl otherpl othermsgll dportls1 dportls2 dportls2'
      dportls' kportls chanls vsdstcl cHeape cHeapt
      chanpl chanl chandstkportll kportpl kportl chanptr csemid,
      <|| spec_code_cons (qportpost_send_Outcore (length dstkportpl2)
          (Vptr pptr :: Vptr msgptr ::
          Vint32 (Int.repr (Z.of_nat (length dstkportpl))) :: Vint32 (Int.repr (Z.of_nat csemid)):: vsdstcl)) s||> **
      [| dportls2' = dportls2 /\ v = Some (Vint32 (Int.repr OS_Q_FULL)) \/
         exists ndstport, dportls2' = set dportls2 dstportp ndstport /\ v = Some (Vint32 (Int.repr OS_NO_ERR)) |] **
      [| RLH_OtherPortPtrList otherppl otherpl' othermsgll' dportls2' |] **
      [| Channel_dstkport_Queue_OutcoreC otherppl chanptr dstkportpl kportls dportls2' |] **
      [| dstkportpl = (dstkportpl1 ++ dstkportp :: dstkportpl2) |] **
      Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
      OtherPortPtrList otherppl otherpl' othermsgll' **
      Hdomainportl dportls' **
      Hkernelport kportls **
      Hchannell chanls **
      HCoreHeap cHeapl cHeape cHeapt **
      Aarray msgptr (Tarray char_t (S (length ori_msg_vl))) ((Vint32 mlen) :: ori_msg_vl) **
    [| vl = (Vptr dstportp) :: (Vptr msgptr)  :: nil |] **
    [| join dportls1 dportls2' dportls' |] **
    [| RLH_Channel otherppl chanpl chanl chandstkportll chanls kportls dportls1 dportls2' |] **
    [| R_KernelPortIDTbl_ChannelIDTbl kportpl kportl chanpl chanl chandstkportll kportls dportls1 dportls2' |] **
    [| logicl = (logic_code s) :: (logic_ier er) :: (logic_lv ori_msg_vl) :: 
                  (logic_val (Vint32 mlen)) :: (logic_lanlv cHeapl) :: (logic_val (Vptr dstkportp)) ::
                  (logic_la dstkportpl1) :: (logic_la dstkportpl2) :: 
                  (logic_absdmport dportls) :: (logic_absdmport dportls1) :: (logic_absdmport dportls2) :: 
                  (logic_hid ndstpptrn)  :: (logic_val (Vptr pptr)) :: logic_hid csemid::
                  (logic_la otherppl) :: (logic_llv otherpl) :: (logic_lllv othermsgll) ::
                  (logic_abskport kportls) :: (logic_abschan chanls) :: 
                  (logic_lv chanpl) :: (logic_llv chanl) :: (logic_lla chandstkportll) ::
                  (logic_lv kportpl) :: (logic_llv kportl) :: (logic_val (Vptr chanptr)) :: 
                  (logic_lv vsdstcl) :: (logic_latv cHeape) :: (logic_latlv cHeapt) ::
                   nil |] **
  p_local OSLInv ct init_lg
    ) \\// 
    (  EX  s er pptr msgptr ori_msg_vl mlen cHeapl
      dstkportpl dstkportpl1 dstkportp dstkportpl2
      headptr dportl dportmsgll dpptrl dportls dstportp
      ndstpptrn  dportl' dportmsgll'
      otherppl dportls1 dportls2 dportls1' 
      dportls' kportls chanls vsdstcl cHeape cHeapt
      chanpl chanl chandstkportll kportpl kportl chanptr
      rtbl rgrp ecbls p1 p2 tcbl1 tcbcur tcbl2 tcbls vhold scapl mcapl qcapl ptls ptbl
      rtbl' rgrp' ecbls' tcbl1' tcbcur' tcbl2' tcbls' cportlptr cportpl,
      <|| spec_code_cons (qportpost_send_Incore (length dstkportpl2)
        (Vptr pptr :: Vptr msgptr ::
        Vint32 (Int.repr (Z.of_nat (length dstkportpl))) :: Vnull :: vsdstcl)) s ||> **
      [| dportls1' = dportls1 /\ v = Some (Vint32 (Int.repr OS_Q_FULL)) \/
        ((dportls1' = dportls1 \/exists ndstport, dportls1' = set dportls1 dstportp ndstport) /\ v = Some (Vint32 (Int.repr OS_NO_ERR))) |] **
      [| RL_PortAttr dpptrl dportl' |] **
      [| RLH_Domainportl headptr dportl' dportmsgll' dportls1' |] **
      [| R_Kernelport_DomainPort kportpl kportl dportl' dpptrl |] **
      [| Channel_dstkport_Queue_IncoreC otherppl chanptr dstkportpl kportls dportls1' |]**
      [| dstkportpl = (dstkportpl1 ++ dstkportp :: dstkportpl2) |] **
      [| RLH_PortPtrINecb headptr dportl' dpptrl ecbls' |] **
      Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
      dmportp_sllseg headptr Vnull dportl' dportmsgll' OS_Port_V_nextPort **
      Hdomainportl dportls' **
      Hkernelport kportls **
      Hchannell chanls **
      HCoreHeap cHeapl cHeape cHeapt **
      Aarray msgptr (Tarray char_t (S (length ori_msg_vl))) ((Vint32 mlen) :: ori_msg_vl) **
      AOSCorePortPtrList cportlptr cportpl dportls1' **
      
      [| vl = (Vptr dstportp) :: (Vptr msgptr)  :: nil |] **
      
      [| join dportls1' dportls2 dportls' |] **
      [| RLH_Channel otherppl chanpl chanl chandstkportll chanls kportls dportls1' dportls2 |] **
      [| R_KernelPortIDTbl_ChannelIDTbl kportpl kportl chanpl chanl chandstkportll kportls dportls1' dportls2 |] **
      [| logicl = (logic_code s) :: (logic_ier er) :: (logic_lv ori_msg_vl) :: 
              (logic_val (Vint32 mlen)) :: (logic_lanlv cHeapl) :: (logic_val (Vptr dstkportp)) ::
              (logic_la dstkportpl1) :: (logic_la dstkportpl2) :: (logic_val headptr) ::
              (logic_llv dportl) :: (logic_lllv dportmsgll) :: (logic_la dpptrl) :: 
              (logic_absdmport dportls) :: (logic_absdmport dportls1) :: (logic_absdmport dportls2) :: 
              (logic_hid ndstpptrn)  :: (logic_val (Vptr pptr)) ::
              (logic_la otherppl) :: 
              (logic_abskport kportls) :: (logic_abschan chanls) :: 
              (logic_lv chanpl) :: (logic_llv chanl) :: (logic_lla chandstkportll) ::
              (logic_lv kportpl) :: (logic_llv kportl) :: (logic_val (Vptr chanptr)) :: 
              (logic_lv vsdstcl) :: (logic_latv cHeape) :: (logic_latlv cHeapt) ::
              logic_lv ptbl :: logic_lv rtbl:: logic_abstcb tcbls::
              logic_val (Vptr vhold) :: (logic_llv scapl) :: (logic_llv mcapl) :: (logic_llv qcapl) ::  
              logic_val p1:: logic_val p2::
              logic_llv tcbl1:: logic_lv tcbcur:: logic_llv tcbl2:: logic_val (Vptr ct)::
              logic_val rgrp:: logic_absecb ecbls:: logic_val cportlptr:: logic_la cportpl ::
              nil |] **
      p_local OSLInv ct init_lg **
      AOSMapTbl ** AOSUnMapTbl ** AOSTCBPrioTbl ptbl rtbl' tcbls' ptls vhold ** 
      AOSTCBList p1 p2 tcbl1' (tcbcur'::tcbl2') rtbl' ct tcbls' **
      AOSRdyTblGrp rtbl' rgrp' **(* tcblist & rdy table *)
      HTCBList tcbls' **  HCurTCB ct ** 
      EvtInv ecbls' p1 (tcbl1'++(tcbcur'::tcbl2')) tcbls' vhold scapl mcapl qcapl**
      [| RH_TCBList_ECBList_P ecbls' tcbls' ct|] **
      [| RH_CurTCB ct tcbls'|] **
      CoreCommuInv ecbls' **
      tcbdllflag p1 (tcbl1' ++ (tcbcur'::tcbl2'))
      ).

Theorem OSQSendToDomainPostGood (vl: vallist) (v: option val) ll ct:
  GoodFunAsrt(OSQSendToDomainPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
  apply GoodFunAsrt_OtherPortPtrList.
  apply GoodFunAsrt_dmportp_sllseg.
  simpl. intros. apply GoodFunAsrt_err_sllseg.
  simpl. intros. apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition OSQSendToDomainPost: fpost:=
  fun vl v ll ct => mkfunasrt(OSQSendToDomainPostGood vl v ll ct).

Definition OSQSendToDomain_spec: fspec:=
  (OSQSendToDomainPre, OSQSendToDomainPost, (Tint8, (Tptr OS_Port) :: (Tptr OSMsg_t) :: nil)).

Definition OSPortAcceptWithoutCheckPre' (vl: vallist) (logicl: list logicvar) ct:=
  EX s er msgptr pptr vsem,
  <|| spec_code_cons
      (port_acc_without_chk ((Vptr pptr) :: msgptr :: vsem :: nil)) s ||> **
  Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er ** 
  [| vl = (Vptr pptr) :: msgptr :: nil |] **
  [| logicl = (logic_code s) :: (logic_ier er) :: (logic_val vsem) :: nil |] **
  p_local OSLInv ct init_lg.

Theorem OSPortAcceptWithoutCheckPreGood (vl: vallist) ll ct:
  GoodFunAsrt(OSPortAcceptWithoutCheckPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OSPortAcceptWithoutCheckPre: fpre:=
  fun vl ll ct => mkfunasrt(OSPortAcceptWithoutCheckPreGood vl ll ct).

Definition OSPortAcceptWithoutCheckPost' (vl: vallist) (v: option val) (logicl: list logicvar) ct:=
  EX s er msgptr pptr vsem,
  <|| s ||> **
  Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er ** 
  [| vl = (Vptr pptr) :: msgptr :: nil |] **
  [| logicl = (logic_code s) :: (logic_ier er) :: (logic_val vsem) :: nil |] **
  [| v = Some (Vint32 (Int.repr OS_PORT_ERR_DIRECTION_TYPE)) \/
     v = Some (Vint32 (Int.repr OS_PORT_MSG_ARG_NULL)) \/
     (* v = Some (Vint32 (Int.repr OS_ERR_PORT_UNBIND)) \/ *)
     v = Some (Vint32 (Int.repr OS_ERR_PORT_NO_CHANNEL)) \/
     v = Some (Vint32 (Int.repr OS_CHANNEL_ERR_BEING_USED)) \/
     v = Some (Vint32 (Int.repr OS_NO_ERR)) |] ** 
  p_local OSLInv ct init_lg.

Theorem OSPortAcceptWithoutCheckPostGood (vl: vallist) (v: option val) ll ct:
  GoodFunAsrt(OSPortAcceptWithoutCheckPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OSPortAcceptWithoutCheckPost: fpost:=
  fun vl v ll ct => mkfunasrt(OSPortAcceptWithoutCheckPostGood vl v ll ct).

Definition OSPortAcceptWithoutCheck_spec: fspec:=
  (OSPortAcceptWithoutCheckPre, OSPortAcceptWithoutCheckPost, (Tint8, (Tptr OS_Port) :: (Tptr OSMsg_t) :: nil)).

Definition OSPortAcceptWithoutCheck2Pre' (vl: vallist) (logicl: list logicvar) ct:=
  EX s er p_v msg_p vsem errv,
  EX dportlptr dportl1 dport dportl2 dportmsgll1 msgl dportmsgll2 dpptrl otherppl,
  EX kportvl kportl chanvl chanl chandstportll,
  EX dportls1 dportls2 dportls kportls chanls cportlptr cportpl,
  EX pd pid pst pintick poutick sz pq nextdst,
  <|| spec_code_cons
      (portpend_accwithoutcheck (Vptr p_v :: Vptr msg_p :: vsem :: errv :: nil)) s ||> **
  Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
  (* partition inv *)
  AOSDomainPortPtrList dportlptr (dportl1 ++ dport :: dportl2) (dportmsgll1 ++ msgl :: dportmsgll2) **
  AOSKernelPortIDTbl kportvl kportl **
  AOSChannelIDTbl chanvl chanl chandstportll **
  AOSCorePortPtrList cportlptr cportpl dportls1 **
  Hdomainportl dportls **
  Hkernelport kportls **
  Hchannell chanls **
  HeapInv' ** 
  [| RL_PortPtrList dportlptr (dportl1 ++ dport :: dportl2) dpptrl |] **
  [| RL_PortAttr dpptrl (dportl1 ++ dport :: dportl2) |] **
  [| RLH_Domainportl dportlptr (dportl1 ++ dport :: dportl2) (dportmsgll1 ++ msgl :: dportmsgll2) dportls1 |] **
  [| RLH_Kernelport kportvl kportl kportls |] **
  [| RLH_Channel otherppl chanvl chanl chandstportll chanls kportls dportls1 dportls2 |] **
  [| R_Kernelport_DomainPort kportvl kportl (dportl1 ++ dport :: dportl2) dpptrl |] **
  [| R_KernelPortIDTbl_ChannelIDTbl kportvl kportl chanvl chanl chandstportll kportls dportls1 dportls2 |] **
  [| nth_error dpptrl (length dportl1) = Some p_v |] **
  [| length dportmsgll1 = length dportl1 |] **
  [| DomainportNode_P dport
  (Z.to_nat DNUM, pd, pid, DestinationP nextdst, pst, pintick, poutick, QueuePort sz pq) msgl|] **
  [| get dportls1 p_v =
  Some (Z.to_nat DNUM, pd, pid, DestinationP nextdst, pst, pintick, poutick, QueuePort sz pq) |] **
  [| join dportls1 dportls2 dportls |] **
  [| nodup_dport kportls |] **
  [| get dportls p_v =
      Some (Z.to_nat DNUM, pd, pid, DestinationP nextdst, pst, pintick, poutick, QueuePort sz pq) |] **
  [| vl = Vptr p_v :: Vptr msg_p :: nil |] **
  [| logicl = (logic_code s) :: (logic_ier er) :: (logic_val  vsem) :: (logic_val errv) :: 
              (logic_val dportlptr) :: (logic_llv dportl1) :: (logic_llv dportl2) ::  (logic_la dpptrl) ::  (logic_lllv dportmsgll1) :: (logic_lllv dportmsgll2) :: (logic_la otherppl) :: 
              (logic_lv kportvl)::(logic_llv kportl) ::(logic_lv chanvl) :: (logic_llv chanl) :: (logic_lla chandstportll) :: 
              (logic_absdmport dportls2) ::(logic_abskport kportls) :: (logic_abschan chanls) ::
              (logic_val cportlptr) :: (logic_la cportpl) :: nil |] **
  p_local OSLInv ct init_lg.

Theorem OSPortAcceptWithoutCheck2PreGood (vl: vallist) ll ct:
  GoodFunAsrt(OSPortAcceptWithoutCheck2Pre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
  apply GoodFunAsrt_dmportp_sll.
  apply GoodFunAsrt_kportNode_P.
  apply GoodFunAsrt_ChannelNode.
Qed.

Definition OSPortAcceptWithoutCheck2Pre: fpre:=
  fun vl ll ct => mkfunasrt(OSPortAcceptWithoutCheck2PreGood vl ll ct).

Definition OSPortAcceptWithoutCheck2Post' (vl: vallist) (v: option val) (logicl: list logicvar) ct:=
  EX s er p_v msg_p vsem errv,
  EX dportlptr dportl1 dport dportl2 dportmsgll1 msgl dportmsgll2 dpptrl otherppl,
  EX kportvl kportl chanvl chanl chandstportll,
  EX dportls1 dportls2 dportls kportls chanls cportlptr cportpl,
  EX pd pid pst pintick poutick sz pq nextdst,
  <|| s ||> **
  Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
  (* partition inv *)
  AOSDomainPortPtrList dportlptr (dportl1 ++ dport :: dportl2) (dportmsgll1 ++ msgl :: dportmsgll2) **
  AOSKernelPortIDTbl kportvl kportl **
  AOSChannelIDTbl chanvl chanl chandstportll **
  AOSCorePortPtrList cportlptr cportpl dportls1 **
  Hdomainportl dportls **
  Hkernelport kportls **
  Hchannell chanls **
  HeapInv' ** 
  [| RL_PortPtrList dportlptr (dportl1 ++ dport :: dportl2) dpptrl |] **
  [| RL_PortAttr dpptrl (dportl1 ++ dport :: dportl2) |] **
  [| RLH_Domainportl dportlptr (dportl1 ++ dport :: dportl2) (dportmsgll1 ++ msgl :: dportmsgll2) dportls1 |] **
  [| RLH_Channel otherppl chanvl chanl chandstportll chanls kportls dportls1 dportls2 |] **
  [| R_Kernelport_DomainPort kportvl kportl (dportl1 ++ dport :: dportl2) dpptrl |] **
  [| R_KernelPortIDTbl_ChannelIDTbl kportvl kportl chanvl chanl chandstportll kportls dportls1 dportls2 |] **
  [| DomainportNode_P dport
  (Z.to_nat DNUM, pd, pid, DestinationP nextdst, pst, pintick, poutick, QueuePort sz pq) msgl|] **
  [| get dportls1 p_v =
     Some (Z.to_nat DNUM, pd, pid, DestinationP nextdst, pst, pintick, poutick, QueuePort sz pq) |] **
  [| join dportls1 dportls2 dportls |] **
  [| get dportls p_v =
      Some (Z.to_nat DNUM, pd, pid, DestinationP nextdst, pst, pintick, poutick, QueuePort sz pq) |] **
  [| vl = Vptr p_v :: Vptr msg_p :: nil |] **
  [| logicl = (logic_code s) :: (logic_ier er) :: (logic_val vsem) :: (logic_val errv) :: 
              (logic_val dportlptr) :: (logic_llv dportl1) :: (logic_llv dportl2) ::  (logic_la dpptrl) ::  (logic_lllv dportmsgll1) :: (logic_lllv dportmsgll2) :: (logic_la otherppl) :: 
              (logic_lv kportvl)::(logic_llv kportl) ::(logic_lv chanvl) :: (logic_llv chanl) :: (logic_lla chandstportll) :: 
              (logic_absdmport dportls2) ::  (logic_abskport kportls) :: (logic_abschan chanls) :: 
              (logic_val cportlptr) :: (logic_la cportpl) :: nil |] **
  [| errv = (Vint32 (Int.repr OS_ERR_PORT_NO_CHANNEL)) \/ errv = (Vint32 (Int.repr OS_NO_ERR)) \/ 
     errv = (Vint32 (Int.repr OS_CHANNEL_ERR_BEING_USED)) /\ exists isem, vsem = Vint32 isem /\ Int.eq isem ($ DEFAULT_CHANNLE_SEMAPHROE) = false |] **
  [| v = Some errv |] ** 
  p_local OSLInv ct init_lg.

Theorem OSPortAcceptWithoutCheck2PostGood (vl: vallist) (v: option val) ll ct:
  GoodFunAsrt(OSPortAcceptWithoutCheck2Post' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
  apply GoodFunAsrt_dmportp_sll.
  apply GoodFunAsrt_kportNode_P.
  apply GoodFunAsrt_ChannelNode.
Qed.

Definition OSPortAcceptWithoutCheck2Post: fpost:=
  fun vl v ll ct => mkfunasrt(OSPortAcceptWithoutCheck2PostGood vl v ll ct).

Definition OSPortAcceptWithoutCheck2_spec: fspec:=
  (OSPortAcceptWithoutCheck2Pre, OSPortAcceptWithoutCheck2Post, (Tint8, (Tptr OS_Port) :: (Tptr OSMsg_t) :: nil)).


(* Spec code for receivePortMsg *)

Inductive receivePortMsg_tcbls_ecbls : list addrval -> EcbMod.map -> TcbMod.map -> TcbMod.map -> bool -> Prop:=
| receivePortmsg_tcbls_ecbls_nil : 
    forall tcbls ecbls, receivePortMsg_tcbls_ecbls nil ecbls tcbls tcbls true
| receivePortMsg_tcbls_ecbls_nochange : 
    forall portp pl tcbls ecbls tcbls' wt b,
      get ecbls portp = Some (absport, wt) ->
      receivePortMsg_tcbls_ecbls pl ecbls tcbls tcbls' b ->
      receivePortMsg_tcbls_ecbls (portp::pl) ecbls tcbls tcbls' b
| receivePortMsg_tcbls_ecbls_change :
    forall portp pl tcbls ecbls tcbls' wt t' p st tskm tcbls'' b,
      get ecbls portp = Some (absport, wt) ->
      wt <> nil ->
      GetHWait tcbls wt t' ->
      get tcbls t' = Some (p, st, tskm, false) ->
      tcbls' = set tcbls t' (p, st, Vptr OS_PARTITION_MESSAGE_COME_ptr, false) ->
      receivePortMsg_tcbls_ecbls pl ecbls tcbls' tcbls'' b ->
      receivePortMsg_tcbls_ecbls (portp::pl) ecbls tcbls tcbls'' b
| receivePortMsg_tcbls_ecbls_abort:
    forall portp pl tcbls ecbls tcbls' wt t' p st tskm b sus,
      get ecbls portp = Some (absport, wt) ->
      wt <> nil ->
      GetHWait tcbls wt t' ->
      get tcbls t' = Some (p, st, tskm, sus)  ->
      st <> rdy \/ sus = true ->
      receivePortMsg_tcbls_ecbls pl ecbls tcbls tcbls' b ->
      receivePortMsg_tcbls_ecbls (portp::pl) ecbls tcbls tcbls' false
.


Definition receivePortMsg_aspec (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
    exists cportpl tls ecbls tls',
      get O1 oscoreportplid = Some (oscoreportpl cportpl) /\
      get O1 absecblsid = Some (absecblist ecbls) /\
      get O1 abtcblsid = Some (abstcblist tls) /\
      ( receivePortMsg_tcbls_ecbls cportpl ecbls tls tls' true /\
        opo = Some (set O1 abtcblsid (abstcblist tls')) 
                     \/
        exists n, receivePortMsg_tcbls_ecbls (firstn n cportpl) ecbls tls tls' false /\
        opo = None )
  end.

Definition receivePortMsgPre' (vl:vallist) (logicl:list logicvar) (ct:tid):=
  EX s is isr er tcbls ecbls ptbl rtbl rgrp ptls vhold p1 p2 tcbl1 tcbcur tcbl2 scapl mcapl qcapl,
      (* Parameters *)
      [| vl = nil |] **
      (* Interrupt state *)
      Aie false ** Ais is ** Acs nil ** Aisr isr ** A_isr_is_prop ** Aier er **  p_local OSLInv ct init_lg **
      (* Abs spec *) 
      <|| (receivePortMsg_aspec (|vl|));; s||> **
      (* Conditions in OS_IpcPre *)
      DynamicRefactorINV ecbls **
      [| CORESEM_INECB_P ecbls |] **
      (* PartitionInv *)
      PartitionInv ecbls **
      (* Conditions for task rdy *)
      AOSMapTbl **
      AOSUnMapTbl **
      AOSRdyTblGrp rtbl rgrp **
      AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold **
      AOSTCBList p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
      EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
      HTCBList tcbls **  HCurTCB ct **
      [| RH_TCBList_ECBList_P ecbls tcbls ct|] **
      [| RH_CurTCB ct tcbls|] **
      (*logic vars*)
      [| logicl =  logic_code s ::(logic_isr isr) ::  (logic_ier er) :: (logic_is is) :: (logic_abstcb tcbls) :: (logic_absecb ecbls) :: (logic_val (Vptr ct)) ::
      (logic_val p1) :: (logic_val p2) ::  (logic_lv rtbl) :: (logic_val rgrp) ::
      (logic_llv tcbl1) :: (logic_lv tcbcur) :: (logic_llv tcbl2) :: 
      logic_lv ptbl :: logic_lv rtbl:: logic_val rgrp:: logic_val (Vptr vhold) ::
      nil |].

Theorem receivePortMsgPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (receivePortMsgPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
  hnf. intros. apply GoodFunAsrt_err_sllseg.
  hnf. intros. apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition receivePortMsgPre: fpre :=
  fun vl ll ct=> mkfunasrt (receivePortMsgPreGood vl ll ct).

Definition receivePortMsgPost' (vl:vallist) (v: option val)(logicl:list logicvar) ct:=
  EX s is isr er tcbls tcbls' ecbls ecbls' ptbl rtbl rtbl' rgrp rgrp' ptls vhold p1 p2 tcbl1 tcbl1' tcbcur tcbcur' tcbl2 tcbl2' scapl mcapl qcapl,
      (* Parameters *)
      [| vl = nil /\ v = Some (V$ OS_NO_ERR)|] **
      (* Interrupt state *)
      Aie false ** Ais is ** Acs nil ** Aisr isr ** A_isr_is_prop ** Aier er **  p_local OSLInv ct init_lg **
      (* Abs spec *) 
      <||s||> **
      (* Conditions in OS_IpcPre *)
      DynamicRefactorINV ecbls' **
      [| CORESEM_INECB_P ecbls' |] **
      (* PartitionInv *)
      PartitionInv ecbls' **
      (* Conditions for task rdy *)
      AOSMapTbl **
      AOSUnMapTbl **
      AOSRdyTblGrp rtbl' rgrp' **
      AOSTCBPrioTbl ptbl rtbl' tcbls' ptls vhold **
      AOSTCBList p1 p2 tcbl1' (tcbcur'::tcbl2') rtbl' ct tcbls' **
      EvtInv ecbls' p1 (tcbl1'++(tcbcur'::tcbl2')) tcbls' vhold scapl mcapl qcapl **
      HTCBList tcbls' **  HCurTCB ct **
      [| RH_TCBList_ECBList_P ecbls' tcbls' ct|] **
      [| RH_CurTCB ct tcbls'|] **
      (*logic vars*)
      [| logicl =  logic_code s ::(logic_isr isr) ::  (logic_ier er) :: (logic_is is) :: (logic_abstcb tcbls) :: (logic_absecb ecbls) :: (logic_val (Vptr ct)) ::
      (logic_val p1) :: (logic_val p2) ::  (logic_lv rtbl) :: (logic_val rgrp) ::
      (logic_llv tcbl1) :: (logic_lv tcbcur) :: (logic_llv tcbl2) :: 
      logic_lv ptbl :: logic_lv rtbl:: logic_val rgrp:: logic_val (Vptr vhold) ::
      nil |].

Theorem receivePortMsgPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (receivePortMsgPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
  hnf. intros. apply GoodFunAsrt_err_sllseg.
  hnf. intros. apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition receivePortMsgPost : fpost :=
  fun vl v ll ct=> mkfunasrt (receivePortMsgPostGood vl v ll ct).

Definition receivePortMsg_spec: fspec:= (receivePortMsgPre, receivePortMsgPost, (Tvoid, nil)).

Fixpoint update_nth_vallist (n : nat) (vl :list vallist) (v : vallist){struct vl} :=
  match vl with
    | nil => nil
    | v'::vl' => match n with
                  | O => v::vl'
                  | S n' => v'::(update_nth_vallist n' vl' v)
                end
  end.

(* partition initial predicates *)

Fixpoint R_Kernelport_DomainPort_init (kportvl: vallist) (kportl: list vallist) (dportl: list vallist) (dpptrl: list addrval): Prop :=
  match dportl, dpptrl with
  | nil, nil => True
  | dport :: dportl', dpptr :: ddptrl' => 
      ((exists id kportptr kport,
        OS_Port_V_portID dport = Some (Vint32 id) /\
        nth_error kportvl (nat_of_Z (Int.unsigned id)) = Some (Vptr kportptr) /\ 
        nth_error kportl (nat_of_Z (Int.unsigned id)) = Some kport /\
        struct_type_vallist_match OS_K_Port kport /\
        OS_K_Port_V_portID kport = Some (Vint32 id) /\
        OS_K_Port_V_dmport kport = Some (Vptr dpptr) /\
        OS_K_Port_V_coreNum kport = OS_Port_V_coreNum dport) \/ 
        (exists id,
        OS_Port_V_portID dport = Some (Vint32 id) /\
        nth_error kportvl (nat_of_Z (Int.unsigned id)) = Some (Vnull) /\ 
        nth_error kportl (nat_of_Z (Int.unsigned id)) = Some nil)) /\
        R_Kernelport_DomainPort_init kportvl kportl dportl' ddptrl'
  | _, _ => False
  end.


Fixpoint kport_V_OSEventPtr kportvl kportl (dportl: list vallist) dpptrl :=
  match kportvl, kportl with 
  | nil ,nil => Aemp 
  | Vptr kportptr:: kportvl', kport :: kportl' => 
        (( [| exists chanptr, OS_K_Port_V_channel kport = Some (Vptr chanptr)|]  ** 
             EX n dmptr dmport, [|OS_K_Port_V_dmport kport = Some (Vptr dmptr) /\ 
                          nth_error dpptrl n = Some dmptr /\ nth_error dportl n = Some dmport |] **
            ( [| OS_Port_V_direction dmport = Some (Vint32 (Int.repr SOURCE)) |] ** 
              PV (get_off_addr kportptr (Int.repr 12)) @ (Tptr Tvoid) |-> Vnull  \\//
            [| OS_Port_V_direction dmport = Some (Vint32 (Int.repr DESTINATION)) |] ** Aemp)
            )
             \\// 
        ([| OS_K_Port_V_channel kport = Some Vnull |] ** 
        PV (get_off_addr kportptr (Int.repr 12)) @ (Tptr Tvoid) |-> Vnull )) ** 
        kport_V_OSEventPtr kportvl' kportl' dportl dpptrl
  | _, _ => Afalse
  end.

Definition kport_V_OSEventPtr_sig kportv kport_ dpptrl dportl :=
  match kportv with
    | Vptr kportptr =>
      ( [|exists chanptr, OS_K_Port_V_channel kport_ = Some (Vptr chanptr)|] **
        ( EX (n : nat) (dmptr : addrval) (dmport : vallist),
          [|OS_K_Port_V_dmport kport_ = Some (Vptr dmptr) /\
            nth_error dpptrl n = Some dmptr /\
            nth_error dportl n = Some dmport|] **
          ( [|OS_Port_V_direction dmport = Some (V$ SOURCE)|] **
            PV get_off_addr kportptr ($ 12) @ (Void) ∗ |-> Vnull \\//
            [|OS_Port_V_direction dmport = Some (V$ DESTINATION)|] ** Aemp ) ) \\//
        [|OS_K_Port_V_channel kport_ = Some Vnull|] **
        PV get_off_addr kportptr ($ 12) @ (Void) ∗ |-> Vnull)
    | _ => Afalse
    end.

Fixpoint channel_V_dstPortsTail (channell: list vallist) (dstkportll: list (list addrval)) : Prop :=
  match channell, dstkportll with 
  | nil, nil => True
  | chann::channell', dstkportl :: dstkportll' => ( OS_Channel_V_dstPortsTail chann = Some Vnull /\ dstkportl = nil \/ 
                                                   exists kptail dstkportl', OS_Channel_V_dstPortsTail chann = Some (Vptr kptail) /\ 
                                                   dstkportl = dstkportl' ++ kptail :: nil) /\ 
                                                   channel_V_dstPortsTail channell' dstkportll'
  | _, _ => False
  end.

Definition channel_V_src_P ptr  (chann: vallist) (dstkportl:  (list addrval)) kportvl kportl (dportl: list vallist) dpptrl :=
  (forall srckp, OS_Channel_V_srcPort chann = Some (Vptr srckp) -> 
  (exists n kport, nth_error kportvl n = Some (Vptr srckp)  /\  nth_error kportl n = Some kport  /\ OS_K_Port_V_channel kport = Some (Vptr ptr) /\
   exists pid dmptr dmport, OS_K_Port_V_dmport kport = Some (Vptr dmptr) /\ 
                            nth_error dpptrl pid = Some dmptr /\ nth_error dportl pid = Some dmport /\ 
                            OS_Port_V_direction dmport = Some (Vint32 (Int.repr SOURCE))
                            )).
              
Fixpoint channel_V_dst_P ptr (dstkportl:  (list addrval))  kportvl kportl (dportl: list vallist) dpptrl  :=
  match dstkportl with 
  | dstkp :: dstkportl' => (exists n kport, nth_error kportvl n = Some (Vptr dstkp)  /\  nth_error kportl n = Some kport  /\ 
                            OS_K_Port_V_channel kport = Some (Vptr ptr) /\
                            exists pid dmptr dmport, OS_K_Port_V_dmport kport = Some (Vptr dmptr) /\ 
                            nth_error dpptrl pid = Some dmptr /\ nth_error dportl pid = Some dmport /\ 
                            OS_Port_V_direction dmport = Some (Vint32 (Int.repr DESTINATION))) /\ 
                            channel_V_dst_P ptr dstkportl' kportvl kportl dportl dpptrl 
  | nil => True
  end.

Definition channel_V_src_P' (chann: vallist) (dstkportl:  (list addrval)) kportvl kportl (dportl: list vallist) dpptrl (mode: Z) :=
(forall srckp, OS_Channel_V_srcPort chann = Some (Vptr srckp) -> 
(forall n kport, nth_error kportvl n = Some (Vptr srckp)  ->  nth_error kportl n = Some kport  -> 
  forall pid dmptr dmport, OS_K_Port_V_dmport kport = Some (Vptr dmptr) -> 
                          nth_error dpptrl pid = Some dmptr -> nth_error dportl pid = Some dmport -> 
                          OS_Port_V_mode dmport = Some (Vint32 (Int.repr mode)))).

Definition channel_V_srcdstkport_P (chaptr: val) (chann: vallist) (dstkportl:  (list addrval)) kportvl kportl (dportl: list vallist) dpptrl :=
  chaptr = Vnull /\ chann = nil /\ dstkportl = nil \/ 
  exists ptr, chaptr = Vptr ptr /\ 
  channel_V_src_P ptr chann dstkportl kportvl kportl dportl dpptrl /\ 
  channel_V_dst_P ptr dstkportl kportvl kportl dportl dpptrl.

Fixpoint channel_V_srcdstkport (chanvl: vallist ) (channell: list vallist) (dstkportll: list (list addrval)) kportvl kportl (dportl: list vallist) dpptrl :=
  match chanvl, channell, dstkportll with 
  | nil, nil, nil => True 
  | chaptr::chanvl', chann::channell', dstkportl :: dstkportll' => 
                                        (channel_V_srcdstkport_P chaptr chann dstkportl kportvl kportl dportl dpptrl) /\ 
                                        channel_V_srcdstkport chanvl' channell'  dstkportll'  kportvl kportl dportl dpptrl
  | _, _, _ => False
  end.

Definition  channel_V_srcdstkport_aux chanvl chanl chandstkportll kportvl kportl dportl  dpptrl :=
  channel_V_srcdstkport  chanvl chanl chandstkportll kportvl kportl dportl dpptrl /\ 
  NoDup (filter (fun a => (match a with 
  | Vptr x => true | _ => false end) )  kportvl).

(* channleCreateCheck *)
Definition channleCreateCheckPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX channid chtype s er,
  <||s||> ** Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
    [|vl = Vint32 channid:: Vint32 chtype:: nil|] **
    [| logicl =  logic_code s :: logic_ier er:: nil |] ** 
    p_local OSLInv ct init_lg.

Theorem channleCreateCheckPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (channleCreateCheckPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition channleCreateCheckPre: fpre :=
  fun vl ll ct=> mkfunasrt (channleCreateCheckPreGood vl ll ct).

Definition channleCreateCheckPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX channid chtype s er,
  <||s||> ** Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
    [| vl = Vint32 channid:: Vint32 chtype:: nil|] **
    [| v = Some (Vint32 Int.one) \/ v = Some (Vint32 Int.zero) |] **
    [| logicl =  logic_code s :: logic_ier er:: nil |] ** 
    p_local OSLInv ct init_lg.

Theorem channleCreateCheckPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (channleCreateCheckPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition channleCreateCheckPost : fpost :=
 fun vl v ll ct=> mkfunasrt (channleCreateCheckPostGood vl v ll ct).

Definition channleCreateCheck_spec : fspec:= (channleCreateCheckPre,channleCreateCheckPost,(Tint32, Tint8:: channnel_type_t ::  nil)).  

(* OSChannelCreate *)
Definition OSChannelCreate_aspec (vl:vallist): spec_code :=
  END None 
  ??
  Semacc_err (V$ OS_RESOURCE_SEMAPHORE_CHANNEL );; END None
  ?? 
  Semacc_succ (V$ OS_RESOURCE_SEMAPHORE_CHANNEL );;
  Semrelease (V$ OS_RESOURCE_SEMAPHORE_CHANNEL) ;; END None.

Definition OSChannelCreatePre' (vl:vallist) (logicl:list logicvar) ct:=
  EX channid chtype errptr errv s chanfptr chanfl syschinfoptr syschinfovl er chanvl chanl chandstkportll nest chncount,
  <|| spec_code_cons (OSChannelCreate_aspec vl) s||> ** Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
  [| vl = (Vint32 channid) :: (Vint32 chtype) :: (Vptr errptr):: nil|] **  
  PV errptr @ Int8u |-> errv **
  GV sys_channel_info @ Tptr channel_semaphore_t |-> Vptr syschinfoptr **
  node (Vptr syschinfoptr) syschinfovl channel_semaphore_t **
  [| nth_val 0 syschinfovl = Some (Vint32 chncount) |] **
  [| Int.unsigned chncount <=  OS_INTER_CORE_CHANNEL_NUMS |] **
  AOSChannelFreeList chanfptr chanfl **
  AOSUnMapTbl **
  AOSMapTbl **
  GAarray OSChannelIDTbl (Tarray (Tptr OS_Channel) (nat_of_Z CHANNEL_NUMS)) chanvl **
  ChannelNode chanvl chanl chandstkportll **
  [| array_type_vallist_match (Tptr OS_Channel) chanvl /\ length chanvl = (nat_of_Z CHANNEL_NUMS)|] **
  GV OSIntNesting @ Tint32 |-> (Vint32 nest) ** 
  [| logicl = logic_val chanfptr :: logic_llv chanfl :: logic_val (Vptr syschinfoptr) :: logic_lv syschinfovl :: 
    (logic_ier er) :: logic_lv chanvl :: logic_llv chanl :: 
    logic_lla chandstkportll :: 
    logic_val (Vint32 nest) ::
    logic_val (Vint32 chncount) ::
    logic_code s :: nil |] **
    p_local OSLInv ct init_lg.


Theorem OSChannelCreatePreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OSChannelCreatePre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
  apply GoodFunAsrt_channelf_sll.
  apply GoodFunAsrt_ChannelNode.
Qed.

Definition OSChannelCreatePre: fpre :=
  fun vl ll ct=> mkfunasrt (OSChannelCreatePreGood vl ll ct).

Definition OSChannelCreatePost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX channid chtype errptr errv s chanfptr chanfl syschinfoptr syschinfovl er chanvl chanl chandstkportll nest chncount,
  <|| s||> ** Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
  [| vl = (Vint32 channid) :: (Vint32 chtype) :: (Vptr errptr):: nil|] **  
  PV errptr @ Int8u |-> errv **
  AOSUnMapTbl **
  AOSMapTbl **
  GV OSIntNesting @ Tint32 |-> (Vint32 nest) ** 
  GV sys_channel_info @ Tptr channel_semaphore_t |-> Vptr syschinfoptr **
  [| logicl = logic_val chanfptr :: logic_llv chanfl :: logic_val (Vptr syschinfoptr) :: logic_lv syschinfovl :: 
    (logic_ier er) :: logic_lv chanvl :: logic_llv chanl :: 
    logic_lla chandstkportll :: 
    logic_val (Vint32 nest) ::
    logic_val (Vint32 chncount) ::
    logic_code s :: nil |] **
    p_local OSLInv ct init_lg **
  (
  node (Vptr syschinfoptr) syschinfovl channel_semaphore_t**
  AOSChannelFreeList chanfptr chanfl **
  GAarray OSChannelIDTbl (Tarray (Tptr OS_Channel) (nat_of_Z CHANNEL_NUMS)) chanvl **
  ChannelNode chanvl chanl chandstkportll **
  [| array_type_vallist_match (Tptr OS_Channel) chanvl /\ length chanvl = (nat_of_Z CHANNEL_NUMS)|] **
  [| errv = V$ OS_CHANNEL_ID_INVALID \/
     errv = V$ OS_ERR_CREATE_ISR  \/
     errv = V$ OS_CHANNEL_FAIL_TO_GET \/
     errv = V$ OS_CHANNEL_ERR_SEMAPHORE_NULL \/
     errv = V$ OS_CHANNEL_ID_EXIST \/
     errv = V$ CHECK_ERROR \/
     errv = V$ OS_CHANNEL_DEPLETED
  |] **
  [| v = Some Vnull|]
  \\// 
  EX chanfptr' chanfl' syschinfovl' newchanvl' chncount',
  node (Vptr syschinfoptr) syschinfovl' channel_semaphore_t**
  AOSChannelFreeList chanfptr' chanfl' **
  GAarray OSChannelIDTbl (Tarray (Tptr OS_Channel) (nat_of_Z CHANNEL_NUMS)) (update_nth_val  (Z.to_nat(Int.unsigned channid)) chanvl chanfptr ) **
  ChannelNode (update_nth_val  (Z.to_nat(Int.unsigned channid)) chanvl chanfptr ) (update_nth_vallist (Z.to_nat(Int.unsigned channid)) chanl newchanvl'  ) (update_nth (list addrval) (Z.to_nat(Int.unsigned channid)) chandstkportll nil  ) **
  [| array_type_vallist_match (Tptr OS_Channel) chanvl /\ length chanvl = (nat_of_Z CHANNEL_NUMS)|] **
  [| nth_val 0 syschinfovl' = Some (Vint32 chncount') |] **
  [| Int.unsigned chncount' <=  OS_INTER_CORE_CHANNEL_NUMS |] **
  [| OS_Channel_V_channelID newchanvl' = Some (Vint32 channid) |] **
  [| OS_Channel_V_srcPortsNum newchanvl' = Some (V$ 0) |] **
  [| OS_Channel_V_dstPortsNum newchanvl' = Some (V$ 0) |] **
  [| OS_Channel_V_dstPortsHead newchanvl' = Some Vnull |] **
  [| OS_Channel_V_dstPortsTail newchanvl' = Some Vnull |] **
  [| errv = V$ OS_NO_ERR |] **
  [| v = Some chanfptr|]
  ).

Theorem OSChannelCreatePostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSChannelCreatePost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
  apply GoodFunAsrt_channelf_sll.
  apply GoodFunAsrt_ChannelNode.
  apply GoodFunAsrt_channelf_sll.
  apply GoodFunAsrt_ChannelNode.
Qed.

Definition OSChannelCreatePost : fpost :=
 fun vl v ll ct=> mkfunasrt (OSChannelCreatePostGood vl v ll ct).

Definition OSChannelCreate_spec : fspec:= (OSChannelCreatePre,OSChannelCreatePost,(Tptr OS_Channel, Tint8:: channnel_type_t :: Tptr Tint8 :: nil)).

(* PortAddToChannel *)
Definition OSPortAddToChannel_aspec v: spec_code :=
  END None  ??
  Semacc_err v;; END None ??  Semacc_succ v ;;
  Semrelease v ;; END None.


Definition OSPortAddToChannelPre' (vl: vallist) (logicl: list logicvar) ct:=
  EX s er chan_v p_v err_l err_v curdomain domainv domainvl  vsem,
  <|| spec_code_cons (OSPortAddToChannel_aspec vsem) s ||> **
  Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
  (GV OSRunning @ (Tint8) |-> Vint32 Int.zero) **
  PV err_l @ Tint8 |-> Vint32 (err_v)  **
  (* initial data predicate *)
  (GV ksCurDomain @ (Tint32) |-> Vint32 curdomain) **
  [| Int.eq Int.zero curdomain  = true \/ Int.lt Int.zero curdomain = true /\ Int.lt curdomain (Int.repr 8) = true |] **
  GV ksDomains @ (Tptr OSdomain_t) |-> (Vptr domainv) ** 
  Astruct (get_off_addr domainv (Int.mul ($ 34) curdomain)) OSdomain_t domainvl **
  [| struct_type_vallist_match OSdomain_t domainvl |] **
  ( (* parameter port is null *)
    ([| p_v = Vnull |]  **
    [| logicl = (logic_val (Vint32 curdomain)) ::  (logic_val  (Vptr domainv)) :: (logic_lv domainvl) ::
                (logic_code s) :: (logic_ier er) :: nil |])  \\//
    (* parameter port is not null *)
    ( EX p_l, [| p_v = Vptr p_l |] **
      EX p1 p2 tcbl1 tcbcur tcbl2 rtbl tcbls,
      AOSTCBList  p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
      [| RH_CurTCB ct tcbls |] **
      (*  EvtInv *)
      EX ecbls vhold scapl mcapl qcapl,
      EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl**
      (* partition inv *)
      EX dportlptr dportl1 dport dportl2 dportmsgll1 msgl dportmsgll2 (* dportls1 *) dpptrl
      otherppl otherpl othermsgll (* dportls2 dportls *)
      kportvl kportl (* kportls *) kportfptr kportfl
      chanvl chanl chandstkportll (* chanls *) chanfptr chanfl dportls1 absport,
      EX portid portattrv portattrvl, 
      (* initial predicate *)
      [|OS_Port_V_portID dport = Some (Vint32 portid)|] **
      GV OSPortAttrTbl @ (Tptr OSport_attr_t) |-> (Vptr portattrv) ** 
      Astruct (get_off_addr portattrv (Int.mul ($ 12) portid)) OSport_attr_t portattrvl **
      [| struct_type_vallist_match OSport_attr_t portattrvl |] **
      (* 已经创建完成的 domain port 链表 *)
      AOSDomainPortPtrList dportlptr (dportl1 ++ dport :: dportl2) (dportmsgll1 ++ msgl :: dportmsgll2) **
      (* Hdomainportl dportls **  *)
      (* [| join dportls1 dportls2 dportls |] ** *)
      (* [| RL_PortAttr dpptrl dportl |] ** *)
      [| RLH_PortPtrINecb dportlptr (dportl1 ++ dport :: dportl2) dpptrl ecbls|] **
      (* [| RLH_Domainportl dportlptr (dportl1 ++ dport :: dportl2) (dportmsgll1 ++ msgl :: dportmsgll2) dportls1|] ** *)
      AOSKernelPortIDTbl kportvl kportl **
      (* Hkernelport kportls ** *)
      (* [| RLH_Kernelport kportvl kportl kportls|] **  *)
      AOSChannelIDTbl chanvl chanl chandstkportll**  
      (* Hchannell chanls ** *)
      (* [| RLH_Channel otherppl chanvl chanl chandstkportll chanls kportls dportls1 dportls2 |] ** *)
      AOSKernelPortFreeList kportfptr kportfl **
      AOSChannelFreeList chanfptr chanfl **
      [| R_Kernelport_DomainPort_init kportvl kportl (dportl1 ++ dport :: dportl2) dpptrl |] **
      (* [| R_KernelPortIDTbl_ChannelIDTbl kportvl kportl chanvl chanl chandstkportll kportls dportls1 dportls2 |] ** *)
      OtherPortPtrList otherppl otherpl othermsgll **
      (* [| RLH_OtherPortPtrList otherppl otherpl othermsgll dportls2 |] ** *)
      (* [| nodup_dport kportls |] ** *)
      [| nth_error dpptrl (length dportl1) = Some p_l |] **
      [| length dportmsgll1 = length dportl1 |] **
      [| DomainportNode_P dport absport msgl|] **
      [| get dportls1 p_l = Some absport |] **
      (* if kport has no channptr binded, there remains part of memory *)
      kport_V_OSEventPtr kportvl kportl (dportl1 ++ dport :: dportl2) dpptrl **
      (* if channelid valid, chanptr exists, vsem *)
      [| forall chanp chann sem, nth_error chanvl (Z.to_nat (Int.unsigned chan_v)) = Some (Vptr chanp) ->
         nth_error chanl (Z.to_nat (Int.unsigned chan_v)) = Some chann -> 
         OS_Channel_V_semaphore chann = Some (Vint32 sem) -> vsem = (Vint32 sem) |] **
      (* channel tail *)
      [| channel_V_dstPortsTail chanl chandstkportll |] **
      (* channel src dst port  *)
      [| channel_V_srcdstkport_aux chanvl chanl chandstkportll kportvl kportl (dportl1 ++ dport :: dportl2) dpptrl  |] **
      (* if channelid valid, chanptr exists, channel mode match dport *)
      [| forall chanp chann dstkportl, nth_error chanvl (Z.to_nat (Int.unsigned chan_v)) = Some (Vptr chanp) ->
           nth_error chanl (Z.to_nat (Int.unsigned chan_v)) = Some chann -> 
           nth_error chandstkportll (Z.to_nat (Int.unsigned chan_v)) =  Some dstkportl -> 
           OS_Port_V_direction dport = Some (Vint32 (Int.repr DESTINATION)) ->
           (forall dstnum, OS_Channel_V_dstPortsNum chann = Some (Vint32 dstnum) -> Int.unsigned dstnum <= 254) /\ 
           (OS_Port_V_mode dport = Some (Vint32 (Int.repr QUEUE)) ->
            OS_Port_V_OSQEntries dport = Some (Vint32 (Int.repr 0)) /\
            channel_V_src_P' chann dstkportl kportvl kportl (dportl1 ++ dport :: dportl2) dpptrl QUEUE) |] **
      [| logicl = (logic_val (Vint32 curdomain)) :: (logic_val (Vptr domainv)) :: (logic_lv domainvl) ::
              (logic_code s) :: (logic_ier er) ::
              (logic_val (Vint32 portid)) :: (logic_val (Vptr portattrv)) :: (logic_lv portattrvl) ::
              (logic_val p1) :: (logic_val p2) :: (logic_llv tcbl1) :: (logic_lv tcbcur) ::  (logic_llv tcbl2) ::  (logic_lv rtbl) :: (logic_abstcb tcbls) ::
              (logic_absecb ecbls) ::  (logic_val (Vptr vhold)) :: (logic_llv scapl) :: (logic_llv mcapl) :: (logic_llv qcapl) ::  
              (logic_val dportlptr) :: (logic_llv dportl1) :: (logic_lv dport) :: (logic_llv dportl2) ::  (logic_la dpptrl) ::  (logic_lllv dportmsgll1) :: (logic_llv msgl) :: (logic_lllv dportmsgll2) :: (logic_la otherppl) :: 
              (logic_lv kportvl)::(logic_llv kportl) ::(logic_lv chanvl) :: (logic_llv chanl) :: (logic_lla chandstkportll) :: nil |]
              (* (logic_absdmport dportls1) :: (logic_absdmport dportls2) :: (logic_absdmport dportls) ::  (logic_abskport kportls) :: (logic_abschan chanls) ::nil |]  *)
    )
    )  **
  [| vl = Vint32 chan_v :: p_v :: Vptr err_l :: nil |] **
  p_local OSLInv ct init_lg.


Lemma GoodFunAsrt_kport_V_OSEventPtr : 
  forall kportvl kportl (dportl: list vallist) dpptrl, GoodFunAsrt (kport_V_OSEventPtr kportvl kportl dportl dpptrl).
Proof.
  induction kportvl;intros.
  - destruct kportl.
    cbn. auto.
    cbn. auto.
  - destruct kportl.
    cbn. auto. destruct a;cbn;auto.
    cbn [kport_V_OSEventPtr].
    destruct a;cbn;auto.
    GoodFunAsrt_solver.
Qed.

Theorem OSPortAddToChannelPreGood (vl: vallist) ll ct:
  GoodFunAsrt(OSPortAddToChannelPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
  intro; apply GoodFunAsrt_err_sllseg.
  intro; apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
  apply GoodFunAsrt_dmportp_sll.
  apply GoodFunAsrt_kportNode_P.
  apply GoodFunAsrt_ChannelNode.
  apply GoodFunAsrt_kportf_sll.
  apply GoodFunAsrt_channelf_sll.
  apply GoodFunAsrt_OtherPortPtrList.
  apply GoodFunAsrt_kport_V_OSEventPtr.
Qed.

Definition OSPortAddToChannelPre: fpre:=
  fun vl ll ct => mkfunasrt(OSPortAddToChannelPreGood vl ll ct).

Definition OSPortAddToChannel_retvalue_case1 chan_v dport kportvl kportl chanvl (chanl : list vallist) (chandstkportll : list (list addrval)) err_v v  : Prop :=
  ((Int.ltu ($ CHANNEL_NUMS) chan_v = true \/  Int.eq chan_v ($ CHANNEL_NUMS) = true) /\ 
            err_v = Int.repr  OS_PORT_ID_INVALID /\ v = Some Vnull  \/ 
        nth_error chanvl (Z.to_nat (Int.unsigned chan_v)) = Some Vnull /\ err_v = Int.repr OS_CHANNEL_ERR_NULL /\ v = Some Vnull \/
        (exists pid, OS_Port_V_portID dport = Some (Vint32 pid) /\ nth_error kportvl (Z.to_nat(Int.unsigned pid)) = Some (Vnull) /\ 
                    err_v = Int.repr OS_PORT_ID_INVALID /\ v = Some Vnull) \/
        (exists chanp chann sem, nth_error chanvl (Z.to_nat (Int.unsigned chan_v)) = Some (Vptr chanp) /\ 
              nth_error chanl (Z.to_nat (Int.unsigned chan_v)) = Some chann /\ 
              OS_Channel_V_semaphore chann = Some (Vint32 sem) /\ Int.eq sem (Int.repr DEFAULT_CHANNLE_SEMAPHROE) = false /\ 
              err_v = Int.repr OS_CHANNEL_ERR_BEING_USED /\ v = Some Vnull) \/
        (exists pid kportptr kport chanptr,
              OS_Port_V_portID dport = Some (Vint32 pid) /\
              nth_error kportvl (nat_of_Z (Int.unsigned pid)) = Some (Vptr kportptr) /\ 
              nth_error kportl (nat_of_Z (Int.unsigned pid)) = Some kport /\ 
              OS_K_Port_V_channel kport = Some (Vptr chanptr) /\
              err_v = Int.repr OS_ERR_PORT_HAVE_BEEN_BINDED /\ v = Some Vnull) \/ 
        err_v = Int.repr CHECK_ERROR /\ v = Some Vnull
        ).

Definition OSPortAddToChannel_portchanninfo dport kportvl kportl chanvl (chanl : list vallist) (chandstkportll : list (list addrval))
                                            pid kportptr kport chanid chanptr chan dstkportl: Prop :=
    OS_Port_V_portID dport = Some (Vint32 pid) /\
    nth_error kportvl (nat_of_Z (Int.unsigned pid)) = Some (Vptr kportptr) /\ 
    nth_error kportl (nat_of_Z (Int.unsigned pid)) = Some kport /\ 
    OS_K_Port_V_channel kport = Some (Vnull) /\ 
    nth_error chanvl (nat_of_Z (Int.unsigned chanid)) = Some (Vptr chanptr) /\
    nth_error chanl (nat_of_Z (Int.unsigned chanid))  = Some chan /\
    nth_error chandstkportll (nat_of_Z (Int.unsigned chanid)) = Some dstkportl. 

Definition OSPortAddToChannel_retvalue_case2_1 kportvl kportl kport chan err_v v : Prop :=
    exists sem kphead,
      OS_Channel_V_semaphore chan = Some (Vint32 sem) /\ Int.eq sem (Int.repr DEFAULT_CHANNLE_SEMAPHROE) = true /\ 
      OS_Channel_V_dstPortsHead chan = Some (Vptr kphead) /\
      exists kpheadid khport, nth_error kportvl kpheadid = Some (Vptr kphead) /\ 
                              nth_error kportl kpheadid = Some khport /\ 
          OS_K_Port_V_coreNum khport <> OS_K_Port_V_coreNum kport /\
      err_v = Int.repr OS_PORT_ERR_MULTICORE /\ v = Some Vnull.

Definition OSPortAddToChannel_retvalue_case2_2 kportl  (chanl : list vallist)
                                          (pid : int32)  (kportptr : addrval) (kport : vallist) (chanid : int32)  (chanptr : addrval) (chan : vallist) 
                                          kportl' chanl'  
                                          err_v v: Prop := 
    exists chan', chan' = update_nth_val 1 (update_nth_val 6 chan (Vptr kportptr)) (Vint32 (Int.repr 1)) /\ 
    exists kport', kport' = update_nth_val 3 (update_nth_val 1 kport (Vint32 chanid)) (Vptr chanptr)  /\ 
    kportl' = update_nth_vallist (nat_of_Z (Int.unsigned pid)) kportl kport' /\ 
    chanl' = update_nth_vallist (nat_of_Z (Int.unsigned chanid)) chanl chan' /\ 
    err_v = Int.repr OS_NO_ERR /\ v = Some Vnull.

Definition OSPortAddToChannel_retvalue_case3_1 kportvl kportl kport chan err_v v : Prop :=
    exists sem srckp,
      OS_Channel_V_semaphore chan = Some (Vint32 sem) /\ Int.eq sem (Int.repr DEFAULT_CHANNLE_SEMAPHROE) = true /\ 
      OS_Channel_V_srcPort chan = Some (Vptr srckp) /\
      exists srckpid khport, nth_error kportvl srckpid = Some (Vptr srckp) /\ 
                              nth_error kportl srckpid = Some khport /\ 
          OS_K_Port_V_coreNum khport <> OS_K_Port_V_coreNum kport /\
      err_v = Int.repr OS_PORT_ERR_MULTICORE /\ v = Some Vnull.
      
Definition OSPortAddToChannelPost' (vl: vallist) (v: option val) (logicl: list logicvar) ct:=
  EX s er chan_v p_v err_l err_v curdomain domainv domainvl,
  <|| s ||> **
  Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
  (GV OSRunning @ (Tint8) |-> Vint32 Int.zero) **
  PV err_l @ Tint8 |-> Vint32 (err_v)  **
  (* initial data predicate *)
  (GV ksCurDomain @ (Tint32) |-> Vint32 curdomain) **
  GV ksDomains @ (Tptr OSdomain_t) |-> (Vptr domainv) ** 
  Astruct (get_off_addr domainv (Int.mul ($ 34) curdomain)) OSdomain_t domainvl **
  ( (* parameter port is null *)
    ([| p_v = Vnull |]  **
    [| logicl = (logic_val (Vint32 curdomain)) ::  (logic_val  (Vptr domainv)) :: (logic_lv domainvl) ::
                (logic_code s) :: (logic_ier er) :: nil |] **
    [| (Int.ltu ($ CHANNEL_NUMS) chan_v = true \/  Int.eq chan_v ($ CHANNEL_NUMS) = true)  /\  err_v = Int.repr  OS_PORT_ID_INVALID /\ v = Some Vnull  \/
        err_v = Int.repr OS_PORT_ERR_NULL  /\ v = Some Vnull |])   \\//
    (* parameter port is not null *)
    ( EX p_l, [| p_v = Vptr p_l |] **
      EX p1 p2 tcbl1 tcbcur tcbl2 rtbl tcbls,
      AOSTCBList  p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
      (*  EvtInv *)
      EX ecbls vhold scapl mcapl qcapl,
      EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
      (* partition inv *)
      EX dportlptr dportl1 dport dportl2 dportmsgll1 msgl dportmsgll2 (* dportls1 *) dpptrl
        otherppl otherpl othermsgll (* dportls2 dportls *)
        kportvl kportl (* kportls *) kportfptr kportfl
        chanvl chanl chandstkportll (* chanls *) chanfptr chanfl (* absport *),
      EX portid portattrv portattrvl, 
      (* initial predicate *)
      GV OSPortAttrTbl @ (Tptr OSport_attr_t) |-> (Vptr portattrv) ** 
      Astruct (get_off_addr portattrv (Int.mul ($ 12) portid)) OSport_attr_t portattrvl **
      EX dportl dportmsgll  kportl' chanl' chandstkportll'  (* dportls1' dportls' kportls' chanls' *),
      (* 已经创建完成的 domain port 链表 *)
      AOSDomainPortPtrList dportlptr dportl dportmsgll **
      (* Hdomainportl dportls' **  *)
      (* [| join dportls1' dportls2 dportls' |] ** *)
      (* [| RL_PortAttr dpptrl dportl |] ** *)
      [| RLH_PortPtrINecb dportlptr dportl dpptrl ecbls|] **
      (* [| RLH_Domainportl dportlptr dportl dportmsgll dportls1' |] ** *)
      AOSKernelPortIDTbl kportvl kportl' **
      (* Hkernelport kportls' ** *)
      (* [| RLH_Kernelport kportvl kportl' kportls'|] **  *)
      AOSChannelIDTbl chanvl chanl' chandstkportll'**  
      (* Hchannell chanls' ** *)
      (* [| RLH_Channel otherppl chanvl chanl' chandstkportll' chanls' kportls' dportls1' dportls2 |] ** *)
      AOSKernelPortFreeList kportfptr kportfl **
      AOSChannelFreeList chanfptr chanfl **
      [| R_Kernelport_DomainPort_init kportvl kportl' dportl dpptrl |] **
      (* [| R_KernelPortIDTbl_ChannelIDTbl kportvl kportl' chanvl chanl' chandstkportll' kportls' dportls1' dportls2 |] ** *)
      OtherPortPtrList otherppl otherpl othermsgll **
      (* [| RLH_OtherPortPtrList otherppl otherpl othermsgll dportls2 |] ** *)
      (* [| nodup_dport kportls' |] ** *)
      (* if kport has no channptr binded, there remains part of memory *)
      kport_V_OSEventPtr kportvl kportl' dportl  dpptrl **
      (* channel tail *)
      [| channel_V_dstPortsTail chanl' chandstkportll' |] **
      (* channel src dst port  *)
      [| channel_V_srcdstkport_aux chanvl chanl' chandstkportll' kportvl kportl' dportl dpptrl |] **
      [| logicl = (logic_val (Vint32 curdomain)) :: (logic_val (Vptr domainv)) :: (logic_lv domainvl) ::
              (logic_code s) :: (logic_ier er) ::
              (logic_val (Vint32 portid)) :: (logic_val (Vptr portattrv)) :: (logic_lv portattrvl) ::
              (logic_val p1) :: (logic_val p2) :: (logic_llv tcbl1) :: (logic_lv tcbcur) ::  (logic_llv tcbl2) ::  (logic_lv rtbl) :: (logic_abstcb tcbls) ::
              (logic_absecb ecbls) ::  (logic_val (Vptr vhold)) :: (logic_llv scapl) :: (logic_llv mcapl) :: (logic_llv qcapl) ::  
              (logic_val dportlptr) :: (logic_llv dportl1) :: (logic_lv dport) :: (logic_llv dportl2) ::  (logic_la dpptrl) ::  (logic_lllv dportmsgll1) :: (logic_llv msgl) :: (logic_lllv dportmsgll2) :: (logic_la otherppl) :: 
              (logic_lv kportvl)::(logic_llv kportl) ::(logic_lv chanvl) :: (logic_llv chanl) :: (logic_lla chandstkportll) :: nil |] **
      (* err msg  and rt value *)
      [| ((* case 1: update nothing, arguments check wrong *)
        (dportl = dportl1 ++ dport :: dportl2 /\ dportmsgll = (dportmsgll1 ++ msgl :: dportmsgll2) /\ kportl' = kportl /\ chanl' = chanl /\ chandstkportll' = chandstkportll ) /\ 
        OSPortAddToChannel_retvalue_case1 chan_v dport kportvl kportl chanvl chanl chandstkportll err_v v) \/
        exists pid kportptr kport chanid chanptr chan dstkportl,
          OSPortAddToChannel_portchanninfo dport kportvl kportl chanvl chanl chandstkportll
                                            pid kportptr kport chanid chanptr chan dstkportl /\ 
        ( (* case 2: direction SOURCE *)
          OS_Port_V_direction dport = Some (Vint32 (Int.repr SOURCE)) /\
          (* case 2.1: update nothing, arguments check wrong*)
          ((dportl = dportl1 ++ dport :: dportl2 /\ dportmsgll = (dportmsgll1 ++ msgl :: dportmsgll2) /\ kportl' = kportl /\ chanl' = chanl /\ chandstkportll' = chandstkportll ) /\
          OSPortAddToChannel_retvalue_case2_1 kportvl kportl kport chan err_v v \/
          (* case 2.1: update channel src port *)
          (dportl = dportl1 ++ dport :: dportl2 /\ dportmsgll = (dportmsgll1 ++ msgl :: dportmsgll2) /\ chandstkportll' = chandstkportll ) /\
          OSPortAddToChannel_retvalue_case2_2 kportl chanl pid kportptr kport chanid chanptr chan 
                                          kportl' chanl'  err_v v)  \/ 
          (* case 3: direction DESTINATION *)
          OS_Port_V_direction dport = Some (Vint32 (Int.repr DESTINATION)) /\
          ((* case 2.1: update nothing, arguments check wrong*)
          (dportl = dportl1 ++ dport :: dportl2 /\ dportmsgll = (dportmsgll1 ++ msgl :: dportmsgll2) /\ kportl' = kportl /\ chanl' = chanl /\ chandstkportll' = chandstkportll ) /\
          (OSPortAddToChannel_retvalue_case3_1 kportvl kportl kport chan err_v v 
            \/ OSPortAddToChannel_retvalue_case2_1 kportvl kportl kport chan err_v v)  \/
          (* case 2.1: update port kport channel *)
          err_v = Int.repr OS_NO_ERR /\ v = Some Vnull))
         |] 
    )
    )  ** 
  [| vl = Vint32 chan_v :: p_v :: Vptr err_l :: nil |] **
  p_local OSLInv ct init_lg.

Theorem OSPortAddToChannelPostGood (vl: vallist) (v: option val) ll ct:
  GoodFunAsrt(OSPortAddToChannelPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
  intro; apply GoodFunAsrt_err_sllseg.
  intro; apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
  apply GoodFunAsrt_dmportp_sll.
  apply GoodFunAsrt_kportNode_P.
  apply GoodFunAsrt_ChannelNode.
  apply GoodFunAsrt_kportf_sll.
  apply GoodFunAsrt_channelf_sll.
  apply GoodFunAsrt_OtherPortPtrList.
  apply GoodFunAsrt_kport_V_OSEventPtr.
Qed.

Definition OSPortAddToChannelPost: fpost:=
  fun vl v ll ct => mkfunasrt(OSPortAddToChannelPostGood vl v ll ct).

Definition OSPortAddToChannel_spec: fspec:=
  (OSPortAddToChannelPre, OSPortAddToChannelPost, ((Tptr OS_Port), Tint32 :: (Tptr OS_Port) :: (Tptr Tint8) :: nil)).


(* portBindCheck *)
Definition portBindCheckPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX portid channid s er curdomain portattrv portattrvl domainv domainvl,
  <|| s||> ** Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
    (GV ksCurDomain @ (Tint32) |-> Vint32 curdomain) **
    [| Int.eq Int.zero curdomain  = true \/ Int.lt Int.zero curdomain = true /\ Int.lt curdomain (Int.repr 8) = true |] **
    GV ksDomains @ (Tptr OSdomain_t) |-> (Vptr domainv) ** 
    Astruct (get_off_addr domainv (Int.mul ($ 34) curdomain)) OSdomain_t domainvl **
    [| struct_type_vallist_match OSdomain_t domainvl |] **
    GV OSPortAttrTbl @ (Tptr OSport_attr_t) |-> (Vptr portattrv) ** 
    Astruct (get_off_addr portattrv (Int.mul ($ 12) portid)) OSport_attr_t portattrvl **
    [| struct_type_vallist_match OSport_attr_t portattrvl |] **
    [|vl = (Vint32 portid) :: (Vint32 channid) :: nil|] **
    [| Int.eq Int.zero portid  = true \/ Int.ltu Int.zero portid = true /\ Int.ltu portid (Int.repr PORT_NUMS) = true |] **
    [| logicl = (logic_val (Vint32 curdomain)) ::
      (logic_val (Vptr portattrv)) :: (logic_lv portattrvl) :: (logic_val (Vptr domainv)) :: (logic_lv domainvl) ::
      (logic_ier er) :: logic_code s :: nil |] ** 
    p_local OSLInv ct init_lg.


Theorem portBindCheckPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (portBindCheckPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition portBindCheckPre: fpre :=
  fun vl ll ct=> mkfunasrt (portBindCheckPreGood vl ll ct).

Definition portBindCheckPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX portid channid s er curdomain portattrv portattrvl domainv domainvl,
  <|| s||> ** Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
    (GV ksCurDomain @ (Tint32) |-> Vint32 curdomain) **
    GV ksDomains @ (Tptr OSdomain_t) |-> (Vptr domainv) ** 
    Astruct (get_off_addr domainv (Int.mul ($ 34) curdomain)) OSdomain_t domainvl **
    GV OSPortAttrTbl @ (Tptr OSport_attr_t) |-> (Vptr portattrv) ** 
    Astruct (get_off_addr portattrv (Int.mul ($ 12) portid)) OSport_attr_t portattrvl **
    [|vl = (Vint32 portid) :: (Vint32 channid) :: nil|] **
    [| logicl = (logic_val (Vint32 curdomain)) ::
      (logic_val (Vptr portattrv)) :: (logic_lv portattrvl) :: (logic_val (Vptr domainv)) :: (logic_lv domainvl) ::
      (logic_ier er) :: logic_code s :: nil |]  ** 
    [| exists  en, nth_val 0%nat portattrvl = Some (Vint32 en) /\ 
       (v = Some (Vint32 ($ 0)) /\  Int.eq Int.zero en = true  \/ 
        Int.eq Int.zero en = false /\ 
        ( exists parid parid',  nth_val 1%nat portattrvl = Some (Vint32 parid) /\ 
            nth_val 1%nat domainvl = Some (Vint32 parid') /\ 
            (Int.eq parid parid' = false /\ v = Some (Vint32 ($ 0)) \/ 
            Int.eq parid parid' = true /\ 
            exists porchanid,  nth_val 5%nat portattrvl = Some (Vint32 porchanid) /\ 
              (Int.eq porchanid channid = false /\ v = Some (Vint32 ($ 0)) \/ 
              Int.eq porchanid channid = true /\ v = Some (Vint32 ($ 1)))   ) 
        ))   |] **
    p_local OSLInv ct init_lg.

Theorem portBindCheckPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (portBindCheckPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition portBindCheckPost : fpost :=
 fun vl v ll ct=> mkfunasrt (portBindCheckPostGood vl v ll ct).

Definition portBindCheck_spec : fspec:= (portBindCheckPre,portBindCheckPost,(Tint32, Tint32:: Tint32 :: nil)).

(* kernelPortCreate *)
Definition OSKernelPortCreate_aspec: spec_code :=
  END None ??
  Semacc_err (V$ OS_RESOURCE_SEMAPHORE_PORT );; END None ?? 
  Semacc_succ (V$ OS_RESOURCE_SEMAPHORE_PORT );;
  Semrelease (V$ OS_RESOURCE_SEMAPHORE_PORT) ;; END None.

Definition OSKernelPortCreatePre' (vl: vallist) (logicl: list logicvar) ct:=
  EX dmportp portid errptr errv s er nest kportp kportfl dportp dportl dportmsgll dpptrl cportp kportpl kportl dmport dmevetype,
  <|| spec_code_cons OSKernelPortCreate_aspec s||> **
    Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
  [| vl = (Vptr dmportp) :: (Vint32 portid) :: (Vptr errptr):: nil|] **  
  PV errptr @ Int8u |-> errv **
  GV OSIntNesting @ Tint32 |-> (Vint32 nest) ** 
  AOSKernelPortFreeList kportp kportfl **
  GV OSDomainPortPtrList @ (Tptr OS_Port) |-> dportp **
  dmportp_sll dportp dportl dportmsgll OS_Port_V_nextPort **
  GV OSCorePortPtrList @ (Tptr OS_Port) |-> cportp **
  [| RL_PortPtrList dportp dportl dpptrl |] **
  [| isptr cportp /\ isptr dportp |] **
  GAarray OSKernelPortIDTbl (Tarray (Tptr OS_K_Port) (nat_of_Z PORT_NUMS)) kportpl ** 
  kportNode_P kportpl kportl **
  [| array_type_vallist_match (Tptr OS_K_Port) kportpl /\ length kportpl = (nat_of_Z PORT_NUMS)|] **
  APortStruct dmportp dmport **
  [| struct_type_vallist_match' OS_Port_Seg_dls dmport |] **
  PV (get_off_addr dmportp ($0)) @ (char_t) |-> dmevetype **
  [| logicl = (logic_ier er) :: logic_val (Vint32 nest) :: logic_code s ::
              (logic_val kportp) :: (logic_llv kportfl) :: (logic_val dportp) ::
              (logic_llv dportl) :: (logic_la dpptrl) :: (logic_val cportp) ::
              (logic_lllv dportmsgll) :: (logic_lv kportpl) :: (logic_llv kportl) ::
              (logic_lv dmport) :: (logic_val dmevetype) :: nil |] **
    p_local OSLInv ct init_lg.

Theorem OSKernelPortCreatePreGood (vl: vallist) ll ct:
  GoodFunAsrt(OSKernelPortCreatePre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
  apply GoodFunAsrt_kportf_sll.
  apply GoodFunAsrt_dmportp_sll.
  apply GoodFunAsrt_kportNode_P.
  apply GoodFunAsrt_APortStruct.
Qed.

Definition OSKernelPortCreatePre: fpre:=
  fun vl ll ct => mkfunasrt(OSKernelPortCreatePreGood vl ll ct).

Definition OSKernelPortCreatePost' (vl: vallist) (v: option val) (logicl: list logicvar) ct:=
  EX dmportp portid errptr errv s er nest kportp kportfl dportp dportl dportmsgll dpptrl cportp kportpl kportl dmport dmevetype,
  <|| s||> ** Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
  [| vl = (Vptr dmportp) :: (Vint32 portid) :: (Vptr errptr):: nil|] **  
  PV errptr @ Int8u |-> errv **
  GV OSIntNesting @ Tint32 |-> (Vint32 nest) **
  dmportp_sll dportp dportl dportmsgll OS_Port_V_nextPort **
  [| logicl = (logic_ier er) :: logic_val (Vint32 nest) :: logic_code s ::
              (logic_val kportp) :: (logic_llv kportfl) :: (logic_val dportp) ::
              (logic_llv dportl) :: (logic_la dpptrl) :: (logic_val cportp) ::
              (logic_lllv dportmsgll) :: (logic_lv kportpl) :: (logic_llv kportl) ::
              (logic_lv dmport) :: (logic_val dmevetype) :: nil |] **
  p_local OSLInv ct init_lg ** 
  ( GV OSDomainPortPtrList @ (Tptr OS_Port) |-> dportp **
    GV OSCorePortPtrList @ (Tptr OS_Port) |-> cportp **
    AOSKernelPortFreeList kportp kportfl **
    APortStruct dmportp dmport **
    GAarray OSKernelPortIDTbl (Tarray (Tptr OS_K_Port) (nat_of_Z PORT_NUMS)) kportpl ** 
    kportNode_P kportpl kportl **
    PV (get_off_addr dmportp ($0)) @ (char_t) |-> dmevetype **
    [| errv = Vint32 (Int.repr OS_PORT_ID_INVALID) \/ 
       errv = Vint32 (Int.repr OS_ERR_CREATE_ISR) \/ 
       errv = Vint32 (Int.repr OS_PORT_FAIL_TO_GET) \/ 
       ( errv = Vint32 (Int.repr OS_PORT_ID_EXIST) /\
         exists p, nth_error kportpl (Z.to_nat (Int.unsigned portid)) = Some (Vptr p) ) |] **
    [| v = Some Vnull|]
    \\//
    GV OSDomainPortPtrList @ (Tptr OS_Port) |-> (Vptr dmportp) **
    [| nth_error kportpl (Z.to_nat (Int.unsigned portid)) = Some Vnull |] **
    ( GV OSCorePortPtrList @ (Tptr OS_Port) |-> cportp **
      APortStruct dmportp (update_nth_val 11 dmport dportp) **
      [| OS_Port_V_direction dmport <> Some (Vint32 (Int.repr DESTINATION)) |]
      \\//
      GV OSCorePortPtrList @ (Tptr OS_Port) |-> (Vptr dmportp) **
      APortStruct dmportp (update_nth_val 11 (update_nth_val 10 dmport cportp) dportp) **
      [| OS_Port_V_direction dmport = Some (Vint32 (Int.repr DESTINATION)) |] ) **
    ( AOSKernelPortFreeList kportp kportfl **
      GAarray OSKernelPortIDTbl (Tarray (Tptr OS_K_Port) (nat_of_Z PORT_NUMS)) kportpl ** 
      kportNode_P kportpl kportl **
      PV (get_off_addr dmportp ($0)) @ (char_t) |-> dmevetype **
      [| kportp = Vnull |] **
      [| errv = Vint32 (Int.repr OS_PORT_DEPLETED) |] **
      [| v = Some Vnull|] 
      \\//
      EX kportp' kportfl' kport kporta,
      AOSKernelPortFreeList kportp' kportfl' **
      [| kportfl' = skipn (S O) kportfl |] **
      GAarray OSKernelPortIDTbl (Tarray (Tptr OS_K_Port) (nat_of_Z PORT_NUMS))
              (update_nth_val (Z.to_nat (Int.unsigned portid)) kportpl kportp) ** 
      kportNode_P (update_nth_val (Z.to_nat (Int.unsigned portid)) kportpl kportp)
                  (update_nth_vallist (Z.to_nat (Int.unsigned portid)) kportl kport) **
      PV (get_off_addr kporta ($12)) @ (Void) ∗ |-> Vnull **
      PV (get_off_addr dmportp ($0)) @ (char_t) |-> (V$ OS_EVENT_TYPE_PORT) **
      [| OS_K_Port_V_portID     kport = Some (Vint32 portid) |] **
      [| OS_K_Port_V_dmport     kport = Some (Vptr dmportp) |] **
      [| OS_K_Port_V_channelID  kport = Some (V$ DEFAULT_CHANELID) |] **
      [| OS_K_Port_V_OSEventPtr kport = Some Vnull |] **
      [| OS_K_Port_V_coreNum    kport = OS_Port_V_coreNum dmport |] **
      [| OS_K_Port_V_channel    kport = Some Vnull |] **
      [| kportp = Vptr kporta |] **
      [| v = Some kportp |] **
      [| errv = Vint32 (Int.repr OS_NO_ERR) |] ) ).

Theorem OSKernelPortCreatePostGood (vl: vallist) (v: option val) ll ct:
  GoodFunAsrt(OSKernelPortCreatePost' vl v ll ct).
Proof. 
  GoodFunAsrt_solver.
  apply GoodFunAsrt_dmportp_sll.
  apply GoodFunAsrt_kportf_sll.
  apply GoodFunAsrt_APortStruct.
  apply GoodFunAsrt_kportNode_P.
  apply GoodFunAsrt_APortStruct.
  apply GoodFunAsrt_APortStruct.
  apply GoodFunAsrt_kportf_sll.
  apply GoodFunAsrt_kportNode_P.
  apply GoodFunAsrt_kportf_sll.
  apply GoodFunAsrt_kportNode_P.
Qed.

Definition OSKernelPortCreatePost: fpost:=
  fun vl v ll ct => mkfunasrt(OSKernelPortCreatePostGood vl v ll ct).

Definition OSKernelPortCreate_spec: fspec:=
  (OSKernelPortCreatePre, OSKernelPortCreatePost, ((Tptr OS_K_Port), (Tptr OS_Port) :: (Tint32) :: (Tptr Tint8) :: nil)).  

(* portCreateCheck *)
Definition portCreateCheckPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX portid s er,
  <||s||> ** Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
    [|vl = Vint32 portid:: nil|] **
    [| logicl =  logic_code s :: logic_ier er:: nil |] ** 
    p_local OSLInv ct init_lg.

Theorem portCreateCheckPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (portCreateCheckPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition portCreateCheckPre: fpre :=
  fun vl ll ct=> mkfunasrt (portCreateCheckPreGood vl ll ct).

Definition portCreateCheckPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX portid s er,
  <||s||> ** Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
    [| vl = Vint32 portid:: nil|] **
    [| v = Some (Vint32 Int.one) \/ v = Some (Vint32 Int.zero) |] **
    [| logicl =  logic_code s :: logic_ier er:: nil |] ** 
    p_local OSLInv ct init_lg.

Theorem portCreateCheckPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (portCreateCheckPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition portCreateCheckPost : fpost :=
 fun vl v ll ct=> mkfunasrt (portCreateCheckPostGood vl v ll ct).

Definition portCreateCheck_spec : fspec:= (portCreateCheckPre,portCreateCheckPost,(Tint32, Tint8 ::  nil)).

Fixpoint R_Kernelport_DomainPort_init_nonull (kportvl: vallist) (kportl: list vallist) (dportl: list vallist) (dpptrl: list addrval): Prop :=
  match dportl, dpptrl with
  | nil, nil => True
  | dport :: dportl', dpptr :: ddptrl' => 
      ( exists id kportptr kport,
        OS_Port_V_portID dport = Some (Vint32 id) /\
        nth_error kportvl (nat_of_Z (Int.unsigned id)) = Some (Vptr kportptr) /\ 
        nth_error kportl (nat_of_Z (Int.unsigned id)) = Some kport /\
        struct_type_vallist_match OS_K_Port kport /\
        OS_K_Port_V_portID kport = Some (Vint32 id) /\
        OS_K_Port_V_dmport kport = Some (Vptr dpptr) /\
        OS_K_Port_V_coreNum kport = OS_Port_V_coreNum dport) /\
        R_Kernelport_DomainPort_init_nonull kportvl kportl dportl' ddptrl'
  | _, _ => False
  end.
  
Fixpoint NoDup_kportf_kportvl kportfptr kportfl kportvl : Prop :=
  match kportfl with
  | nil => kportfptr = Vnull 
  | l :: kportfl' =>
      ( ~ In kportfptr kportvl ) /\
      ( exists vn,
        OS_K_Port_V_OSEventPtr l = Some vn /\
        NoDup_kportf_kportvl vn kportfl' kportvl )
  end.

(* samplePortCreate *)
Definition SamplePortCreatePre' (vl: vallist) (logicl: list logicvar) ct:=
  EX s vsem er dmportp portid msgp errptr errv nest cportp dportp portattrv portattrvl
     chan_v dmport dmevetype curdomain domainv domainvl
     p1 p2 tcbl1 tcbcur tcbl2 rtbl tcbls ecbls vhold scapl mcapl qcapl
     dportl dpptrl dportmsgll 
     kportvl kportl chanvl chanl chandstkportll kportfptr kportfl chanfptr chanfl
     otherppl otherpl othermsgll (abs_port: Port) (dportls1: DomainPortMod.map)
     dm dir absdir status intick outick buff,
  <|| spec_code_cons OSKernelPortCreate_aspec
                     (spec_code_cons (OSPortAddToChannel_aspec vsem) s)||> **
    Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
  [| vl = (Vptr dmportp) :: (Vint32 portid) :: (Vptr msgp) :: (Vptr errptr):: nil|] **  
  [| Int.ltu portid ($ PORT_NUMS) =true |] **
  GV OSRunning @ (Tint8) |-> Vint32 Int.zero **
  PV errptr @ Int8u |-> (Vint32 errv) **
  GV OSIntNesting @ Tint32 |-> (Vint32 nest) ** 
  GV OSCorePortPtrList @ (Tptr OS_Port) |-> cportp **
  [| isptr cportp /\ isptr dportp |] **
  GV OSPortAttrTbl @ (Tptr OSport_attr_t) |-> (Vptr portattrv) ** 
  Astruct (get_off_addr portattrv (Int.mul ($ 12) portid)) OSport_attr_t portattrvl **
  [| struct_type_vallist_match OSport_attr_t portattrvl |] **
  [| nth_error portattrvl 3%nat = Some (Vint32 (Int.repr dir)) |] **
  [| nth_error portattrvl 4%nat = Some (Vint32 (Int.repr SAMPLE)) |] **
  [| nth_error portattrvl 5%nat = Some (Vint32 chan_v) |] **
  APortStruct dmportp dmport **
  [| struct_type_vallist_match' OS_Port_Seg_dls dmport |] **
  PV (get_off_addr dmportp ($0)) @ (char_t) |-> dmevetype **
  dmportp_sllseg_sampleport_msg msgp (buff :: nil) **
  
  (* from portaddtochannel *)
  (* initial data predicate *)
  (GV ksCurDomain @ (Tint32) |-> Vint32 curdomain) **
  [| Int.eq Int.zero curdomain  = true \/ Int.lt Int.zero curdomain = true /\ Int.lt curdomain (Int.repr 8) = true |] **
  GV ksDomains @ (Tptr OSdomain_t) |-> (Vptr domainv) ** 
  Astruct (get_off_addr domainv (Int.mul ($ 34) curdomain)) OSdomain_t domainvl **
  [| struct_type_vallist_match OSdomain_t domainvl |] **
  AOSTCBList p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
  [| RH_CurTCB ct tcbls |] **
  (*  EvtInv *)
  EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
  (* partition inv *)
  AOSDomainPortPtrList dportp dportl dportmsgll **
  [| RLH_PortPtrINecb dportp dportl dpptrl ecbls|] **
  AOSKernelPortIDTbl kportvl kportl **
  AOSChannelIDTbl chanvl chanl chandstkportll **  
  AOSKernelPortFreeList kportfptr kportfl **
  AOSChannelFreeList chanfptr chanfl **
  [| R_Kernelport_DomainPort_init_nonull kportvl kportl dportl dpptrl |] **
  OtherPortPtrList otherppl otherpl othermsgll **
  (* if kport has no channptr binded, there remains part of memory *)
  kport_V_OSEventPtr kportvl kportl dportl dpptrl **
  (* if channelid valid, chanptr exists, vsem *)
  [| forall chanp chann sem, nth_error chanvl (Z.to_nat (Int.unsigned chan_v)) = Some (Vptr chanp) ->
      nth_error chanl (Z.to_nat (Int.unsigned chan_v)) = Some chann -> 
      OS_Channel_V_semaphore chann = Some (Vint32 sem) -> vsem = (Vint32 sem) |] **
  (* channel tail *)
  [| channel_V_dstPortsTail chanl chandstkportll |] **
  (* channel src dst port  *)
  [| channel_V_srcdstkport_aux chanvl chanl chandstkportll kportvl kportl dportl dpptrl |] **
  (* if channelid valid, chanptr exists, channel mode match dport *)
  [| forall chanp chann dstkportl, nth_error chanvl (Z.to_nat (Int.unsigned chan_v)) = Some (Vptr chanp) ->
           nth_error chanl (Z.to_nat (Int.unsigned chan_v)) = Some chann -> 
           nth_error chandstkportll (Z.to_nat (Int.unsigned chan_v)) =  Some dstkportl -> 
           (* OS_Port_V_direction dport = Some (Vint32 (Int.repr DESTINATION)) -> *)
           (forall dstnum, OS_Channel_V_dstPortsNum chann = Some (Vint32 dstnum) -> Int.unsigned dstnum <= 254) /\ 
           ( (* OS_Port_V_mode dport = Some (Vint32 (Int.repr QUEUE)) ->
            OS_Port_V_OSQEntries dport = Some (Vint32 (Int.repr 0)) /\ *)
            channel_V_src_P' chann dstkportl kportvl kportl dportl dpptrl QUEUE) |] **

  [| get dportls1 dmportp = Some abs_port |] **
  [| NoDup_kportf_kportvl kportfptr kportfl kportvl |] **
  [| nth_error portattrvl 2%nat = Some (Vint32 dm) |] **
  [| OS_Port_V_status dmport = Some (Vint32 status) |] **
  [| OS_Port_V_msgInTick dmport = Some (Vint32 intick) |] **
  [| OS_Port_V_msgOutTick dmport = Some (Vint32 outick) |] **
  [| abs_port = (Z.to_nat DNUM, Z.to_nat (Int.unsigned dm), 
                Z.to_nat (Int.unsigned portid), absdir,
                Z.to_nat (Int.unsigned status), Z.to_nat (Int.unsigned intick),
                Z.to_nat (Int.unsigned outick), SamplePort (Some buff)) |] **
  [| ( dir = SOURCE /\ absdir = SourceP ) \/
     ( dir = DESTINATION /\
       ( ( absdir = DestinationP None /\ cportp = Vnull ) \/
         ( exists p, absdir = DestinationP (Some p) /\ cportp = Vptr p ) ) ) |] **
  [| exists wt, get ecbls dmportp = Some (absport, wt) |] **
  [| ~ In dmportp dpptrl |] ** 

  [| logicl = (logic_code s) :: (logic_val vsem) :: (logic_ier er) :: 
              (logic_val (Vint32 nest)) :: (logic_val cportp) :: (logic_val dportp) ::
              (logic_val (Vptr portattrv)) :: (logic_lv portattrvl) :: (logic_val (Vint32 chan_v)) ::
              (logic_lv dmport) :: (logic_val (Vint32 curdomain)) ::
              (logic_val (Vptr domainv)) :: (logic_lv domainvl) :: (logic_val p1) :: 
              (logic_val p2) :: (logic_llv tcbl1) :: (logic_lv tcbcur) :: 
              (logic_llv tcbl2) ::  (logic_lv rtbl) :: (logic_abstcb tcbls) ::
              (logic_absecb ecbls) ::  (logic_val (Vptr vhold)) :: (logic_llv scapl) :: (logic_llv mcapl) :: (logic_llv qcapl) ::  
              (logic_llv dportl) :: 
              (logic_lllv dportmsgll) :: 
              (logic_la otherppl) :: nil |] **
    p_local OSLInv ct init_lg.

Theorem SamplePortCreatePreGood (vl: vallist) ll ct:
  GoodFunAsrt(SamplePortCreatePre' vl ll ct).
Proof. 
  GoodFunAsrt_solver.
  apply GoodFunAsrt_APortStruct.
  cbn. intros. apply GoodFunAsrt_err_sllseg.
  cbn. intros. apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
  apply GoodFunAsrt_dmportp_sll.
  apply GoodFunAsrt_kportNode_P.
  apply GoodFunAsrt_ChannelNode.
  apply GoodFunAsrt_kportf_sll.
  apply GoodFunAsrt_channelf_sll.
  apply GoodFunAsrt_OtherPortPtrList.
  apply GoodFunAsrt_kport_V_OSEventPtr.
Qed.

Definition SamplePortCreatePre: fpre:=
  fun vl ll ct => mkfunasrt(SamplePortCreatePreGood vl ll ct).


Definition SamplePortCreatePost' (vl: vallist) (v: option val) (logicl: list logicvar) ct:=
  EX s vsem er dmportp portid msgp errptr err_v nest cportp dportp portattrv portattrvl
  chan_v dmport dmevetype curdomain domainv domainvl
  p1 p2 tcbl1 tcbcur tcbl2 rtbl tcbls ecbls vhold scapl mcapl qcapl
  dpptrl dpptrl' kportvl kportl chanvl chanl chandstkportll kportfptr kportfl chanfptr chanfl
  otherppl otherpl othermsgll
  dportl dportl' dportmsgll dportmsgll' kportl' chanl' chandstkportll' dport dm dir mode kportv kport_ vret buff,
  <|| s ||> **
  Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
  [| vl = (Vptr dmportp) :: (Vint32 portid) :: (Vptr msgp) :: (Vptr errptr):: nil|] **  
  GV OSRunning @ (Tint8) |-> Vint32 Int.zero **
  PV errptr @ Int8u |-> (Vint32 err_v) **
  GV OSIntNesting @ Tint32 |-> (Vint32 nest) ** 
  GV OSPortAttrTbl @ (Tptr OSport_attr_t) |-> (Vptr portattrv) ** 
  Astruct (get_off_addr portattrv (Int.mul ($ 12) portid)) OSport_attr_t portattrvl **
  PV (get_off_addr dmportp ($0)) @ (char_t) |-> dmevetype **
  
  (* from portaddtochannel *)
  (* initial data predicate *)
  (GV ksCurDomain @ (Tint32) |-> Vint32 curdomain) **
  GV ksDomains @ (Tptr OSdomain_t) |-> (Vptr domainv) ** 
  Astruct (get_off_addr domainv (Int.mul ($ 34) curdomain)) OSdomain_t domainvl **
  AOSTCBList p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
  (*  EvtInv *)
  EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
  (
    (* partition inv *)
    APortStruct dmportp dport **
    [| dport = (update_nth_val 2 (update_nth_val 12
              (update_nth_val 0 (update_nth_val 4 (update_nth_val 5
              (update_nth_val 3 dmport (Vint32 portid)) (Vint32 mode)) (Vint32 dir)) 
              (Vint32 dm)) (Vptr msgp)) (V$ DNUM)) |] **
    GV OSCorePortPtrList @ OS_Port ∗ |-> cportp **
    dmportp_sllseg_sampleport_msg msgp (buff :: nil) **
    AOSDomainPortPtrList dportp dportl dportmsgll **
    AOSKernelPortIDTbl kportvl kportl **
    AOSChannelIDTbl chanvl chanl chandstkportll **
    AOSKernelPortFreeList kportfptr kportfl **
    AOSChannelFreeList chanfptr chanfl **
    OtherPortPtrList otherppl otherpl othermsgll **
    kport_V_OSEventPtr kportvl kportl dportl dpptrl
    \\//
    ( GV OSCorePortPtrList @ (Tptr OS_Port) |-> cportp **
      [| dport = (update_nth_val 11 (update_nth_val 2 (update_nth_val 12
                  (update_nth_val 0 (update_nth_val 4 (update_nth_val 5
                  (update_nth_val 3 dmport (Vint32 portid)) (Vint32 mode)) (Vint32 dir)) 
                  (Vint32 dm)) (Vptr msgp)) (V$ DNUM)) dportp) |] \\//
      GV OSCorePortPtrList @ (Tptr OS_Port) |-> (Vptr dmportp) **
      [| dport = (update_nth_val 11 (update_nth_val 10
                  (update_nth_val 2 (update_nth_val 12 (update_nth_val 0
                  (update_nth_val 4 (update_nth_val 5 (update_nth_val 3
                  dmport (Vint32 portid)) (Vint32 mode)) (Vint32 dir)) 
                  (Vint32 dm)) (Vptr msgp)) (V$ DNUM)) cportp) dportp) |] ) ** 
    AOSDomainPortPtrList (Vptr dmportp) dportl' dportmsgll' **
    [| RLH_PortPtrINecb (Vptr dmportp) dportl' dpptrl' ecbls |] **
    [| dpptrl' = dmportp :: dpptrl |] **
    [| dportl' = dport :: dportl /\ dportmsgll' = (buff :: nil) :: dportmsgll |] **
    AOSKernelPortIDTbl kportvl kportl **
    AOSChannelIDTbl chanvl chanl chandstkportll **
    AOSKernelPortFreeList kportfptr kportfl **
    AOSChannelFreeList chanfptr chanfl **
    OtherPortPtrList otherppl otherpl othermsgll **
    kport_V_OSEventPtr kportvl kportl dportl dpptrl
    \\//
    ( GV OSCorePortPtrList @ (Tptr OS_Port) |-> cportp **
      [| dport = (update_nth_val 11 (update_nth_val 2 (update_nth_val 12
                  (update_nth_val 0 (update_nth_val 4 (update_nth_val 5
                  (update_nth_val 3 dmport (Vint32 portid)) (Vint32 mode)) (Vint32 dir)) 
                  (Vint32 dm)) (Vptr msgp)) (V$ DNUM)) dportp) |] \\//
      GV OSCorePortPtrList @ (Tptr OS_Port) |-> (Vptr dmportp) **
      [| dport = (update_nth_val 11 (update_nth_val 10
                  (update_nth_val 2 (update_nth_val 12 (update_nth_val 0
                  (update_nth_val 4 (update_nth_val 5 (update_nth_val 3
                  dmport (Vint32 portid)) (Vint32 mode)) (Vint32 dir)) 
                  (Vint32 dm)) (Vptr msgp)) (V$ DNUM)) cportp) dportp) |] ) ** 
    AOSDomainPortPtrList (Vptr dmportp) dportl' dportmsgll' **
    [| RLH_PortPtrINecb (Vptr dmportp) dportl' dpptrl' ecbls |] **
    AOSKernelPortIDTbl kportvl kportl' **
    AOSChannelIDTbl chanvl chanl' chandstkportll' **   
    AOSKernelPortFreeList kportfptr kportfl **
    AOSChannelFreeList chanfptr chanfl **
    [| R_Kernelport_DomainPort_init kportvl kportl' dportl' dpptrl' |] **
    [| dpptrl' = dmportp :: dpptrl |] **
    OtherPortPtrList otherppl otherpl othermsgll **
    (* if kport has no channptr binded, there remains part of memory *)
    kport_V_OSEventPtr kportvl kportl' dportl'  dpptrl' **
    kport_V_OSEventPtr_sig kportv kport_ dpptrl dportl **
    (* channel tail *)
    [| channel_V_dstPortsTail chanl' chandstkportll' |] **
    (* channel src dst port  *)
    [| channel_V_srcdstkport_aux chanvl chanl' chandstkportll' kportvl kportl' dportl' dpptrl' |] **
    (* err msg  and rt value *)
    [| ((* case 1: update nothing, arguments check wrong *)
      (dportl' = dport :: dportl /\ dportmsgll' = (buff :: nil) :: dportmsgll /\ kportl' = kportl /\ chanl' = chanl /\ chandstkportll' = chandstkportll ) /\ 
      OSPortAddToChannel_retvalue_case1 chan_v dport kportvl kportl chanvl chanl chandstkportll err_v vret) \/
      exists pid kportptr kport chanid chanptr chan dstkportl,
        OSPortAddToChannel_portchanninfo dport kportvl kportl chanvl chanl chandstkportll
                                          pid kportptr kport chanid chanptr chan dstkportl /\ 
      ( (* case 2: direction SOURCE *)
        OS_Port_V_direction dport = Some (Vint32 (Int.repr SOURCE)) /\
        (* case 2.1: update nothing, arguments check wrong*)
        ((dportl' = dport :: dportl /\ dportmsgll' = (buff :: nil) :: dportmsgll /\ kportl' = kportl /\ chanl' = chanl /\ chandstkportll' = chandstkportll ) /\
        OSPortAddToChannel_retvalue_case2_1 kportvl kportl kport chan err_v vret \/
        (* case 2.1: update channel src port *)
        (dportl' = dport :: dportl /\ dportmsgll' = (buff :: nil) :: dportmsgll /\ chandstkportll' = chandstkportll ) /\
        OSPortAddToChannel_retvalue_case2_2 kportl chanl pid kportptr kport chanid chanptr chan 
                                        kportl' chanl'  err_v vret)  \/ 
        (* case 3: direction DESTINATION *)
        OS_Port_V_direction dport = Some (Vint32 (Int.repr DESTINATION)) /\
        ((* case 2.1: update nothing, arguments check wrong*)
        (dportl' = dport :: dportl /\ dportmsgll' = (buff :: nil) :: dportmsgll /\ kportl' = kportl /\ chanl' = chanl /\ chandstkportll' = chandstkportll ) /\
        (OSPortAddToChannel_retvalue_case3_1 kportvl kportl kport chan err_v vret 
          \/ OSPortAddToChannel_retvalue_case2_1 kportvl kportl kport chan err_v vret)  \/
        (* case 2.1: update port kport channel *)
        err_v = Int.repr OS_NO_ERR /\ vret = Some Vnull))
    |] 
  ) **

  [| logicl = (logic_code s) :: (logic_val vsem) :: (logic_ier er) :: 
              (logic_val (Vint32 nest)) :: (logic_val cportp) :: (logic_val dportp) ::
              (logic_val (Vptr portattrv)) :: (logic_lv portattrvl) :: (logic_val (Vint32 chan_v)) ::
              (logic_lv dmport) :: (logic_val (Vint32 curdomain)) ::
              (logic_val (Vptr domainv)) :: (logic_lv domainvl) :: (logic_val p1) :: 
              (logic_val p2) :: (logic_llv tcbl1) :: (logic_lv tcbcur) :: 
              (logic_llv tcbl2) ::  (logic_lv rtbl) :: (logic_abstcb tcbls) ::
              (logic_absecb ecbls) ::  (logic_val (Vptr vhold)) :: (logic_llv scapl) :: (logic_llv mcapl) :: (logic_llv qcapl) ::  
              (logic_llv dportl) :: 
              (logic_lllv dportmsgll) :: (logic_la otherppl) :: nil |] **
  [| v = None |] **
  p_local OSLInv ct init_lg.

Lemma GoodFunAsrt_kport_V_OSEventPtr_sig : 
  forall kportvl kportl dportl dpptrl, GoodFunAsrt (kport_V_OSEventPtr_sig kportvl kportl dportl dpptrl).
Proof. intros. destruct kportvl; cbn; tauto. Qed.

Theorem SamplePortCreatePostGood (vl: vallist) (v: option val) ll ct:
  GoodFunAsrt(SamplePortCreatePost' vl v ll ct).
Proof. 
  GoodFunAsrt_solver.
  cbn. intros. apply GoodFunAsrt_err_sllseg.
  cbn. intros. apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
  apply GoodFunAsrt_APortStruct.
  all: try apply GoodFunAsrt_dmportp_sll.
  all: try apply GoodFunAsrt_kportNode_P.
  all: try apply GoodFunAsrt_ChannelNode.
  all: try apply GoodFunAsrt_kportf_sll.
  all: try apply GoodFunAsrt_channelf_sll.
  all: try apply GoodFunAsrt_OtherPortPtrList.
  all: try apply GoodFunAsrt_kport_V_OSEventPtr.
  apply GoodFunAsrt_kport_V_OSEventPtr_sig.
Qed.

Definition SamplePortCreatePost: fpost:=
  fun vl v ll ct => mkfunasrt(SamplePortCreatePostGood vl v ll ct).

Definition SamplePortCreate_spec: fspec:=
  (SamplePortCreatePre, SamplePortCreatePost, ((Void), (Tptr OS_Port) :: (Tint32) :: (Tptr OSMsg_t) :: (Tptr Tint8) :: nil)).  

(* qPortCreate *)
Definition QPortCreatePre' (vl: vallist) (logicl: list logicvar) ct:=
  EX s vsem er dmportp portid msgp errptr errv nest cportp dportp portattrv portattrvl
     chan_v dmport dmevetype curdomain domainv domainvl
     p1 p2 tcbl1 tcbcur tcbl2 rtbl tcbls (ecbls: EcbMod.map) vhold scapl mcapl qcapl
     dportl dpptrl dportmsgll 
     kportvl kportl chanvl chanl chandstkportll kportfptr kportfl chanfptr chanfl
     otherppl otherpl othermsgll 
     buff size (abs_port: Port) (dportls1: DomainPortMod.map)
     dm dir absdir status intick outick,
  <|| spec_code_cons OSKernelPortCreate_aspec
                     (spec_code_cons (OSPortAddToChannel_aspec vsem) s)||> **
    Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
  [| vl = (Vptr dmportp) :: (Vint32 portid) :: (Vptr msgp) :: (Vint32 size) :: (Vptr errptr) :: nil|] **  
  [| Int.ltu portid ($ PORT_NUMS) =true |] **
  GV OSRunning @ (Tint8) |-> Vint32 Int.zero **
  PV errptr @ Int8u |-> (Vint32 errv) **
  GV OSIntNesting @ Tint32 |-> (Vint32 nest) ** 
  GV OSCorePortPtrList @ (Tptr OS_Port) |-> cportp **
  [| isptr cportp /\ isptr dportp |] **
  GV OSPortAttrTbl @ (Tptr OSport_attr_t) |-> (Vptr portattrv) ** 
  Astruct (get_off_addr portattrv (Int.mul ($ 12) portid)) OSport_attr_t portattrvl **
  [| struct_type_vallist_match OSport_attr_t portattrvl |] **
  [| nth_error portattrvl 3%nat = Some (Vint32 (Int.repr dir)) |] **
  [| nth_error portattrvl 4%nat = Some (Vint32 (Int.repr QUEUE)) |] **
  [| nth_error portattrvl 5%nat = Some (Vint32 chan_v) |] **
  APortStruct dmportp dmport **
  [| struct_type_vallist_match' OS_Port_Seg_dls dmport |] **
  PV (get_off_addr dmportp ($0)) @ (char_t) |-> dmevetype **
  dmportp_sllseg_qport_msg msgp msgp msgp (get_off_addr msgp (Int.mul ($ 33) size)) (Z.to_nat (Int.unsigned size)) buff **
  
  (* from portaddtochannel *)
  (* initial data predicate *)
  (GV ksCurDomain @ (Tint32) |-> Vint32 curdomain) **
  [| Int.eq Int.zero curdomain  = true \/ Int.lt Int.zero curdomain = true /\ Int.lt curdomain (Int.repr 8) = true |] **
  GV ksDomains @ (Tptr OSdomain_t) |-> (Vptr domainv) ** 
  Astruct (get_off_addr domainv (Int.mul ($ 34) curdomain)) OSdomain_t domainvl **
  [| struct_type_vallist_match OSdomain_t domainvl |] **
  AOSTCBList p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
  [| RH_CurTCB ct tcbls |] **
  (*  EvtInv *)
  EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
  (* partition inv *)
  AOSDomainPortPtrList dportp dportl dportmsgll **
  [| RLH_PortPtrINecb dportp dportl dpptrl ecbls|] **
  AOSKernelPortIDTbl kportvl kportl **
  AOSChannelIDTbl chanvl chanl chandstkportll **  
  AOSKernelPortFreeList kportfptr kportfl **
  AOSChannelFreeList chanfptr chanfl **
  [| R_Kernelport_DomainPort_init_nonull kportvl kportl dportl dpptrl |] **
  OtherPortPtrList otherppl otherpl othermsgll **
  (* if kport has no channptr binded, there remains part of memory *)
  kport_V_OSEventPtr kportvl kportl dportl dpptrl **
  (* if channelid valid, chanptr exists, vsem *)
  [| forall chanp chann sem, nth_error chanvl (Z.to_nat (Int.unsigned chan_v)) = Some (Vptr chanp) ->
      nth_error chanl (Z.to_nat (Int.unsigned chan_v)) = Some chann -> 
      OS_Channel_V_semaphore chann = Some (Vint32 sem) -> vsem = (Vint32 sem) |] **
  (* channel tail *)
  [| channel_V_dstPortsTail chanl chandstkportll |] **
  (* channel src dst port  *)
  [| channel_V_srcdstkport_aux chanvl chanl chandstkportll kportvl kportl dportl dpptrl |] **
  (* if channelid valid, chanptr exists, channel mode match dport *)
  [| forall chanp chann dstkportl, nth_error chanvl (Z.to_nat (Int.unsigned chan_v)) = Some (Vptr chanp) ->
           nth_error chanl (Z.to_nat (Int.unsigned chan_v)) = Some chann -> 
           nth_error chandstkportll (Z.to_nat (Int.unsigned chan_v)) =  Some dstkportl -> 
           (* OS_Port_V_direction dport = Some (Vint32 (Int.repr DESTINATION)) -> *)
           (forall dstnum, OS_Channel_V_dstPortsNum chann = Some (Vint32 dstnum) -> Int.unsigned dstnum <= 254) /\ 
           ( (* OS_Port_V_mode dport = Some (Vint32 (Int.repr QUEUE)) ->
            OS_Port_V_OSQEntries dport = Some (Vint32 (Int.repr 0)) /\ *)
            channel_V_src_P' chann dstkportl kportvl kportl dportl dpptrl QUEUE) |] **

  [| get dportls1 dmportp = Some abs_port |] **
  [| snd msgp = Int.zero |] **
  [| 0 < Int.unsigned size |] **
  [| NoDup_kportf_kportvl kportfptr kportfl kportvl |] **
  [| nth_error portattrvl 2%nat = Some (Vint32 dm) |] **
  [| OS_Port_V_status dmport = Some (Vint32 status) |] **
  [| OS_Port_V_msgInTick dmport = Some (Vint32 intick) |] **
  [| OS_Port_V_msgOutTick dmport = Some (Vint32 outick) |] **
  [| abs_port = (Z.to_nat DNUM, Z.to_nat (Int.unsigned dm), 
                Z.to_nat (Int.unsigned portid), absdir,
                Z.to_nat (Int.unsigned status), Z.to_nat (Int.unsigned intick),
                Z.to_nat (Int.unsigned outick), QueuePort (Z.to_nat (Int.unsigned size)) nil) |] **
  [| ( dir = SOURCE /\ absdir = SourceP ) \/
     ( dir = DESTINATION /\
       ( ( absdir = DestinationP None /\ cportp = Vnull ) \/
         ( exists p, absdir = DestinationP (Some p) /\ cportp = Vptr p ) ) ) |] **
  [| exists wt, get ecbls dmportp = Some (absport, wt) |] **
  [| ~ In dmportp dpptrl |] ** 

  [| logicl = (logic_code s) :: (logic_val vsem) :: (logic_ier er) :: 
              (logic_val (Vint32 nest)) :: (logic_val cportp) :: (logic_val dportp) ::
              (logic_val (Vptr portattrv)) :: (logic_lv portattrvl) :: (logic_val (Vint32 chan_v)) ::
              (logic_lv dmport) :: (logic_val (Vint32 curdomain)) ::
              (logic_val (Vptr domainv)) :: (logic_lv domainvl) :: (logic_val p1) :: 
              (logic_val p2) :: (logic_llv tcbl1) :: (logic_lv tcbcur) :: 
              (logic_llv tcbl2) ::  (logic_lv rtbl) :: (logic_abstcb tcbls) ::
              (logic_absecb ecbls) ::  (logic_val (Vptr vhold)) :: (logic_llv scapl) :: (logic_llv mcapl) :: (logic_llv qcapl) ::  (logic_llv dportl) :: 
              (logic_lllv dportmsgll) :: 
              (logic_la otherppl) :: (logic_llv buff) :: nil |] **
    p_local OSLInv ct init_lg.

Theorem QPortCreatePreGood (vl: vallist) ll ct:
  GoodFunAsrt(QPortCreatePre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
  apply GoodFunAsrt_APortStruct.
  apply GoodFunAsrt_dmportp_sllseg_qport_msg.
  cbn. intros. apply GoodFunAsrt_err_sllseg.
  cbn. intros. apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
  apply GoodFunAsrt_dmportp_sll.
  apply GoodFunAsrt_kportNode_P.
  apply GoodFunAsrt_ChannelNode.
  apply GoodFunAsrt_kportf_sll.
  apply GoodFunAsrt_channelf_sll.
  apply GoodFunAsrt_OtherPortPtrList.
  apply GoodFunAsrt_kport_V_OSEventPtr.
Qed.

Definition QPortCreatePre: fpre:=
  fun vl ll ct => mkfunasrt(QPortCreatePreGood vl ll ct).

Definition QPortCreatePost' (vl: vallist) (v: option val) (logicl: list logicvar) ct:=
  EX s vsem er dmportp portid msgp errptr err_v nest cportp dportp portattrv portattrvl
  chan_v dmport dmevetype curdomain domainv domainvl
  p1 p2 tcbl1 tcbcur tcbl2 rtbl tcbls ecbls vhold scapl mcapl qcapl
  dpptrl dpptrl' kportvl kportl chanvl chanl chandstkportll kportfptr kportfl chanfptr chanfl
  otherppl otherpl othermsgll buff size
  dportl dportl' dportmsgll dportmsgll' kportl' chanl' chandstkportll' dport dm dir mode kportv kport_ vret,
  <|| s ||> **
  Aie false ** Ais nil ** Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier er ** 
  [| vl = (Vptr dmportp) :: (Vint32 portid) :: (Vptr msgp) :: (Vint32 size) :: (Vptr errptr):: nil|] **  
  GV OSRunning @ (Tint8) |-> Vint32 Int.zero **
  PV errptr @ Int8u |-> (Vint32 err_v) **
  GV OSIntNesting @ Tint32 |-> (Vint32 nest) ** 
  GV OSPortAttrTbl @ (Tptr OSport_attr_t) |-> (Vptr portattrv) ** 
  Astruct (get_off_addr portattrv (Int.mul ($ 12) portid)) OSport_attr_t portattrvl **
  PV (get_off_addr dmportp ($0)) @ (char_t) |-> dmevetype **
  
  (* from portaddtochannel *)
  (* initial data predicate *)
  (GV ksCurDomain @ (Tint32) |-> Vint32 curdomain) **
  GV ksDomains @ (Tptr OSdomain_t) |-> (Vptr domainv) ** 
  Astruct (get_off_addr domainv (Int.mul ($ 34) curdomain)) OSdomain_t domainvl **
  AOSTCBList p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
  (*  EvtInv *)
  EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
  (
    (* partition inv *)
    APortStruct dmportp dport **
    [| dport = (update_nth_val 2 (update_nth_val 17
              (update_nth_val 16 (update_nth_val 15 (update_nth_val 14
              (update_nth_val 13 (update_nth_val 12 (update_nth_val 0
              (update_nth_val 4 (update_nth_val 5 (update_nth_val 3 dmport
              (Vint32 portid)) (Vint32 mode)) (Vint32 dir)) (Vint32 dm)) 
              (Vptr msgp)) (Vptr (get_off_addr msgp (Int.mul ($ 33) size))))
              (Vptr msgp)) (Vptr msgp)) (Vint32 size)) (V$ 0)) (V$ DNUM)) |] **
    GV OSCorePortPtrList @ OS_Port ∗ |-> cportp **
    dmportp_sllseg_qport_msg msgp msgp msgp
            (get_off_addr msgp (Int.mul ($ 33) size))
            (Z.to_nat (Int.unsigned size)) buff **
    AOSDomainPortPtrList dportp dportl dportmsgll **
    AOSKernelPortIDTbl kportvl kportl **
    AOSChannelIDTbl chanvl chanl chandstkportll **
    AOSKernelPortFreeList kportfptr kportfl **
    AOSChannelFreeList chanfptr chanfl **
    OtherPortPtrList otherppl otherpl othermsgll **
    kport_V_OSEventPtr kportvl kportl dportl dpptrl
    \\//
    ( GV OSCorePortPtrList @ (Tptr OS_Port) |-> cportp **
      [| dport = (update_nth_val 11 (update_nth_val 2 (update_nth_val 17
                  (update_nth_val 16 (update_nth_val 15 (update_nth_val 14
                  (update_nth_val 13 (update_nth_val 12 (update_nth_val 0
                  (update_nth_val 4 (update_nth_val 5 (update_nth_val 3 dmport
                  (Vint32 portid)) (Vint32 mode)) (Vint32 dir)) (Vint32 dm)) 
                  (Vptr msgp)) (Vptr (get_off_addr msgp (Int.mul ($ 33) size))))
                  (Vptr msgp)) (Vptr msgp)) (Vint32 size)) (V$ 0)) (V$ DNUM)) dportp) |] \\//
      GV OSCorePortPtrList @ (Tptr OS_Port) |-> (Vptr dmportp) **
      [| dport = (update_nth_val 11 (update_nth_val 10 (update_nth_val 2
                  (update_nth_val 17 (update_nth_val 16 (update_nth_val 15
                  (update_nth_val 14 (update_nth_val 13 (update_nth_val 12
                  (update_nth_val 0 (update_nth_val 4 (update_nth_val 5
                  (update_nth_val 3 dmport (Vint32 portid)) (Vint32 mode))
                  (Vint32 dir)) (Vint32 dm)) (Vptr msgp))
                  (Vptr (get_off_addr msgp (Int.mul ($ 33) size))))
                  (Vptr msgp)) (Vptr msgp))  (Vint32 size)) (V$ 0)) 
                  (V$ DNUM)) cportp) dportp) |] ) ** 
    AOSDomainPortPtrList (Vptr dmportp) dportl' dportmsgll' **
    [| RLH_PortPtrINecb (Vptr dmportp) dportl' dpptrl' ecbls |] **
    [| dpptrl' = dmportp :: dpptrl |] **
    [| dportl' = dport :: dportl /\ dportmsgll' = nil :: dportmsgll |] **
    AOSKernelPortIDTbl kportvl kportl **
    AOSChannelIDTbl chanvl chanl chandstkportll **
    AOSKernelPortFreeList kportfptr kportfl **
    AOSChannelFreeList chanfptr chanfl **
    OtherPortPtrList otherppl otherpl othermsgll **
    kport_V_OSEventPtr kportvl kportl dportl dpptrl
    \\//
    ( GV OSCorePortPtrList @ (Tptr OS_Port) |-> cportp **
      [| dport = (update_nth_val 11 (update_nth_val 2 (update_nth_val 17
                  (update_nth_val 16 (update_nth_val 15 (update_nth_val 14
                  (update_nth_val 13 (update_nth_val 12 (update_nth_val 0
                  (update_nth_val 4 (update_nth_val 5 (update_nth_val 3 dmport
                  (Vint32 portid)) (Vint32 mode)) (Vint32 dir)) (Vint32 dm)) 
                  (Vptr msgp)) (Vptr (get_off_addr msgp (Int.mul ($ 33) size))))
                  (Vptr msgp)) (Vptr msgp)) (Vint32 size)) (V$ 0)) (V$ DNUM)) dportp) |] \\//
      GV OSCorePortPtrList @ (Tptr OS_Port) |-> (Vptr dmportp) **
      [| dport = (update_nth_val 11 (update_nth_val 10 (update_nth_val 2
                  (update_nth_val 17 (update_nth_val 16 (update_nth_val 15
                  (update_nth_val 14 (update_nth_val 13 (update_nth_val 12
                  (update_nth_val 0 (update_nth_val 4 (update_nth_val 5
                  (update_nth_val 3 dmport (Vint32 portid)) (Vint32 mode))
                  (Vint32 dir)) (Vint32 dm)) (Vptr msgp))
                  (Vptr (get_off_addr msgp (Int.mul ($ 33) size))))
                  (Vptr msgp)) (Vptr msgp))  (Vint32 size)) (V$ 0)) 
                  (V$ DNUM)) cportp) dportp) |] ) ** 
    AOSDomainPortPtrList (Vptr dmportp) dportl' dportmsgll' **
    [| RLH_PortPtrINecb (Vptr dmportp) dportl' dpptrl' ecbls |] **
    AOSKernelPortIDTbl kportvl kportl' **
    AOSChannelIDTbl chanvl chanl' chandstkportll' **   
    AOSKernelPortFreeList kportfptr kportfl **
    AOSChannelFreeList chanfptr chanfl **
    [| R_Kernelport_DomainPort_init kportvl kportl' dportl' dpptrl' |] **
    [| dpptrl' = dmportp :: dpptrl |] **
    OtherPortPtrList otherppl otherpl othermsgll **
    (* if kport has no channptr binded, there remains part of memory *)
    kport_V_OSEventPtr kportvl kportl' dportl'  dpptrl' **
    kport_V_OSEventPtr_sig kportv kport_ dpptrl dportl **
    (* channel tail *)
    [| channel_V_dstPortsTail chanl' chandstkportll' |] **
    (* channel src dst port  *)
    [| channel_V_srcdstkport_aux chanvl chanl' chandstkportll' kportvl kportl' dportl' dpptrl' |] **
    (* err msg  and rt value *)
    [| ((* case 1: update nothing, arguments check wrong *)
      (dportl' = dport :: dportl /\ dportmsgll' = nil :: dportmsgll /\ kportl' = kportl /\ chanl' = chanl /\ chandstkportll' = chandstkportll ) /\ 
      OSPortAddToChannel_retvalue_case1 chan_v dport kportvl kportl chanvl chanl chandstkportll err_v vret) \/
      exists pid kportptr kport chanid chanptr chan dstkportl,
        OSPortAddToChannel_portchanninfo dport kportvl kportl chanvl chanl chandstkportll
                                          pid kportptr kport chanid chanptr chan dstkportl /\ 
      ( (* case 2: direction SOURCE *)
        OS_Port_V_direction dport = Some (Vint32 (Int.repr SOURCE)) /\
        (* case 2.1: update nothing, arguments check wrong*)
        ((dportl' = dport :: dportl /\ dportmsgll' = nil :: dportmsgll /\ kportl' = kportl /\ chanl' = chanl /\ chandstkportll' = chandstkportll ) /\
        OSPortAddToChannel_retvalue_case2_1 kportvl kportl kport chan err_v vret \/
        (* case 2.1: update channel src port *)
        (dportl' = dport :: dportl /\ dportmsgll' = nil :: dportmsgll /\ chandstkportll' = chandstkportll ) /\
        OSPortAddToChannel_retvalue_case2_2 kportl chanl pid kportptr kport chanid chanptr chan 
                                        kportl' chanl'  err_v vret)  \/ 
        (* case 3: direction DESTINATION *)
        OS_Port_V_direction dport = Some (Vint32 (Int.repr DESTINATION)) /\
        ((* case 2.1: update nothing, arguments check wrong*)
        (dportl' = dport :: dportl /\ dportmsgll' = nil :: dportmsgll /\ kportl' = kportl /\ chanl' = chanl /\ chandstkportll' = chandstkportll ) /\
        (OSPortAddToChannel_retvalue_case3_1 kportvl kportl kport chan err_v vret 
          \/ OSPortAddToChannel_retvalue_case2_1 kportvl kportl kport chan err_v vret)  \/
        (* case 2.1: update port kport channel *)
        err_v = Int.repr OS_NO_ERR /\ vret = Some Vnull))
    |] 
  ) **

  [| logicl = (logic_code s) :: (logic_val vsem) :: (logic_ier er) :: 
              (logic_val (Vint32 nest)) :: (logic_val cportp) :: (logic_val dportp) ::
              (logic_val (Vptr portattrv)) :: (logic_lv portattrvl) :: (logic_val (Vint32 chan_v)) ::
              (logic_lv dmport) :: (logic_val (Vint32 curdomain)) ::
              (logic_val (Vptr domainv)) :: (logic_lv domainvl) :: (logic_val p1) :: 
              (logic_val p2) :: (logic_llv tcbl1) :: (logic_lv tcbcur) :: 
              (logic_llv tcbl2) ::  (logic_lv rtbl) :: (logic_abstcb tcbls) ::
              (logic_absecb ecbls) ::  (logic_val (Vptr vhold)) :: (logic_llv scapl) :: (logic_llv mcapl) :: (logic_llv qcapl) ::  
              (logic_llv dportl) :: 
              (logic_lllv dportmsgll) :: 
              (logic_la otherppl) :: (logic_llv buff) :: nil |] **
  [| v = None |] **
  p_local OSLInv ct init_lg.

Theorem QPortCreatePostGood (vl: vallist) (v: option val) ll ct:
  GoodFunAsrt(QPortCreatePost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
  cbn. intros. apply GoodFunAsrt_err_sllseg.
  cbn. intros. apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
  apply GoodFunAsrt_APortStruct.
  apply GoodFunAsrt_dmportp_sllseg_qport_msg.
  all: try apply GoodFunAsrt_dmportp_sll.
  all: try apply GoodFunAsrt_kportNode_P.
  all: try apply GoodFunAsrt_ChannelNode.
  all: try apply GoodFunAsrt_kportf_sll.
  all: try apply GoodFunAsrt_channelf_sll.
  all: try apply GoodFunAsrt_OtherPortPtrList.
  all: try apply GoodFunAsrt_kport_V_OSEventPtr.
  apply GoodFunAsrt_kport_V_OSEventPtr_sig.
Qed.

Definition QPortCreatePost: fpost:=
  fun vl v ll ct => mkfunasrt(QPortCreatePostGood vl v ll ct).

Definition QPortCreate_spec: fspec:=
  (QPortCreatePre, QPortCreatePost, ((Void), (Tptr OS_Port) :: (Tint32) :: (Tptr OSMsg_t) :: (Tint16) :: (Tptr Tint8) :: nil)).  
(* ------------------------- add sepc by SJTU  -----------------------*)

(* ------------------------- add spec by CNU ------------------------ *)
(* partitionSysInit  *)

Definition partitionSysInitPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX s lg' isr is cs er ksdomscdidx  kscurd kslastd ksdomt
           ksdschedule ksdscd iscp iscor systm  ossy,
    Aisr isr ** Aie false ** Ais is ** Acs cs ** Aier er **
    AKsDSchdidx ksdomscdidx ** HKsDSchdidx ksdomscdidx **
    AKsCurDomain kscurd ** HKsCurDomain kscurd **
    AKsLastDomain kslastd ** HKsLastDomain kslastd **
    AKsDomainTime ksdomt ** HKsDomainTime ksdomt **
    AKsDomSchedule ksdschedule ksdscd **
    AisCoreBoot iscor**
    AsystemStck' systm   **
    AOSSystemSP ossy ** 
    AisChangePartion iscp **
     [| (Int.unsigned ksdomscdidx <= DSCHEDULE_SIZE)%Z |] **
     <|| partitionSys vl ;; s ||> **
    [|logicl = logic_val (Vint32 kscurd) :: 
                     logic_val (Vint32 ksdomt):: 
                     logic_llv ksdschedule ::  
                     logic_isr isr :: logic_ier er :: logic_is is :: logic_cs cs ::
                     logic_code s :: lg'|] **
    p_local OSLInv ct (logic_val (V$ 1) :: lg').

Theorem partitionSysInitPreGood (vl:vallist) ll ct:
  GoodFunAsrt (partitionSysInitPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition partitionSysInitPre : fpre :=
  fun vl ll ct => mkfunasrt (partitionSysInitPreGood vl ll ct).

Definition partitionSysInitPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct := 
  EX s lg' isr is cs er   kscurd  ksdomt ksdschedule ksdscd
         kscurd' ksdomt'  systm  ossy ,
    Aisr isr ** Aie false ** Ais is ** Acs cs ** Aier er **
    AKsDSchdidx Int.zero ** HKsDSchdidx Int.zero **
    AKsCurDomain kscurd' ** HKsCurDomain kscurd' **
    AKsLastDomain Int.mone ** HKsLastDomain Int.mone **
    AKsDomainTime ksdomt' ** HKsDomainTime ksdomt' **
    AKsDomSchedule ksdschedule ksdscd **
    AisCoreBoot Int.zero**
    AsystemStck' systm  ** 
    AOSSystemSP ossy ** 
    AisChangePartion Int.zero **
    [| nth_vallist (Z.to_nat(Int.unsigned Int.zero)) ksdschedule = Some (Vint32 kscurd'  :: Vint32 ksdomt' :: nil) |] **
     <|| s ||> **
    [|logicl = logic_val (Vint32 kscurd) :: 
                      logic_val (Vint32 ksdomt)::
                     logic_llv ksdschedule ::
                     logic_isr isr :: logic_ier er :: logic_is is :: logic_cs cs ::
                     logic_code s :: lg'|] **
    p_local OSLInv ct (logic_val (V$ 1) :: lg').

Theorem partitionSysInitPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (partitionSysInitPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition partitionSysInitPost : fpost :=
  fun vl v ll ct => mkfunasrt (partitionSysInitPostGood vl v ll ct).

Definition partitionSysInit_spec : fspec := (partitionSysInitPre,partitionSysInitPost,(Tvoid, nil)).

(* nextDomain *)

Definition nextDomainPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX s lg' isr is cs er ksdomscdidx ksdomscdlen kscurd kslastd ksdomt ksdschedule ksdscd iscp,
    Aisr isr ** Aie false ** Ais is ** Acs cs ** Aier er **
    AKsDSchdidx ksdomscdidx ** HKsDSchdidx ksdomscdidx **
    AKsDSchdlen ksdomscdlen ** HKsDSchdlen ksdomscdlen **
    AKsCurDomain kscurd ** HKsCurDomain kscurd **
    AKsLastDomain kslastd ** HKsLastDomain kslastd **
    AKsDomainTime ksdomt ** HKsDomainTime ksdomt **
    AKsDomSchedule ksdschedule ksdscd **
    AisChangePartion iscp **
    [| (Int.unsigned ksdomscdlen <= DSCHEDULE_SIZE)%Z |] **
     <|| nextdom vl ;; s ||> **
    [|logicl = logic_val (Vint32 ksdomscdidx) :: logic_val (Vint32 ksdomscdlen) :: logic_val (Vint32 kscurd) :: 
                     logic_val (Vint32 kslastd) :: logic_val (Vint32 ksdomt) :: logic_llv ksdschedule ::
                     logic_isr isr :: logic_ier er :: logic_is is :: logic_cs cs ::
                     logic_code s :: lg'|] **
    p_local OSLInv ct (logic_val (V$ 1) :: lg').

Theorem nextDomainPreGood (vl:vallist) ll ct:
  GoodFunAsrt (nextDomainPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition nextDomainPre : fpre :=
  fun vl ll ct => mkfunasrt (nextDomainPreGood vl ll ct).

Definition nextDomainPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct := 
  EX s lg' isr is cs er ksdomscdidx ksdomscdlen kscurd kslastd ksdomt ksdschedule ksdscd
        ksdomscdidx' kscurd' ksdomt',
    Aisr isr ** Aie false ** Ais is ** Acs cs ** Aier er **
    AKsDSchdidx ksdomscdidx' ** HKsDSchdidx ksdomscdidx' **
    AKsDSchdlen ksdomscdlen ** HKsDSchdlen ksdomscdlen **
    AKsCurDomain kscurd' ** HKsCurDomain kscurd' **
    AKsLastDomain kscurd ** HKsLastDomain kscurd **
    AKsDomainTime ksdomt' ** HKsDomainTime ksdomt' **
    AKsDomSchedule ksdschedule ksdscd **
    AisChangePartion Int.one **
    [| ksdomscdidx' = (if (Int.ltu (Int.add ksdomscdidx Int.one) ksdomscdlen) then (Int.add ksdomscdidx Int.one) else Int.zero) |] **
    [| nth_vallist (Z.to_nat(Int.unsigned ksdomscdidx')) ksdschedule = Some (Vint32 kscurd'  :: Vint32 ksdomt' :: nil) |] **
     <|| s ||> **
    [|logicl = logic_val (Vint32 ksdomscdidx) :: logic_val (Vint32 ksdomscdlen) :: logic_val (Vint32 kscurd) :: 
                     logic_val (Vint32 kslastd) :: logic_val (Vint32 ksdomt) :: logic_llv ksdschedule ::
                     logic_isr isr :: logic_ier er :: logic_is is :: logic_cs cs ::
                     logic_code s :: lg'|] **
    p_local OSLInv ct (logic_val (V$ 1) :: lg').

Theorem nextDomainPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (nextDomainPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition nextDomainPost : fpost :=
  fun vl v ll ct => mkfunasrt (nextDomainPostGood vl v ll ct).

Definition nextDomain_spec : fspec := (nextDomainPre,nextDomainPost,(Tvoid, nil)).

(* switchDomain *)

Definition ptr_no_dup (vl: vallist):=
forall i j x y,
  i <> j ->
  nth_val i vl = Some (Vptr x) ->
  nth_val j vl = Some (Vptr y) ->
  x <> y.

(* SUPERVISOR_MODE_EN > 0 *)
Definition switchDomainPre' (vl:vallist) (logicl:list logicvar) ct :=
  EX isr ie is ier cs kscurd kslastd ksdom absks rtsk_vll absrtsk
         xmpaxvl xmpax sms_mpaxvl sms_mpax ses_mpaxvl ses_mpax
         evstructs vl0 vl1 vl2 vl3 vl4 vl5
         lmpaxh lmpaxl lsms_mpaxh lsms_mpaxl lses_mpaxh lses_mpaxl
         vl' rv_baddr rv_raddr rv_size rv_vaddr rv_paddr s,
      Aisr isr ** Aie ie **  Ais is ** Acs cs ** Aier ier ** A_isr_is_prop ** 
      AKsCurDomain kscurd  ** HKsCurDomain kscurd **
      AKsLastDomain kslastd  ** HKsLastDomain kslastd **
      AKsDomains ksdom absks ** HKsDomains absks **
      ARootTaskStk rtsk_vll absrtsk **
      AXMpax xmpaxvl xmpax **
      ASMSMpax sms_mpaxvl sms_mpax ** 
      ASESMpax ses_mpaxvl ses_mpax **
      HEvStructHeap evstructs ** AEvStructHeap evstructs **
      [| Get_struct evstructs lmpaxh = Some (lmpaxh, XMC_XMPAXH, vl0) /\
          struct_type_vallist_match XMC_XMPAXH vl0 |] **
      [| Get_struct evstructs lsms_mpaxh = Some (lsms_mpaxh, MSMC_SMSMPAXH, vl1) /\
          struct_type_vallist_match MSMC_SMSMPAXH vl1 |] **
      [| Get_struct evstructs lses_mpaxh = Some (lses_mpaxh, MSMC_SESMPAXH, vl2) /\
          struct_type_vallist_match MSMC_SESMPAXH vl2 |] **
      [| Get_struct evstructs lmpaxl = Some (lmpaxl, XMC_XMPAXL, vl3) /\
          struct_type_vallist_match XMC_XMPAXL vl3 |] **
      [| Get_struct evstructs lsms_mpaxl = Some (lsms_mpaxl, MSMC_SMSMPAXL, vl4) /\
          struct_type_vallist_match MSMC_SMSMPAXL vl4 |] **
      [| Get_struct evstructs lses_mpaxl = Some (lses_mpaxl, MSMC_SESMPAXL, vl5) /\
          struct_type_vallist_match MSMC_SESMPAXL vl5 |] **
      [| ptr_no_dup vl |] **
      <|| spec_code_cons (switchDom (vl ++ vl')) s ||> **
      [| vl = (Vptr lmpaxh) :: (Vptr lmpaxl) :: (Vptr lses_mpaxh) ::
                   (Vptr lses_mpaxl) :: (Vptr lsms_mpaxh) :: (Vptr lsms_mpaxl) :: nil |] **
      [| vl' = rv_baddr :: rv_raddr :: rv_size :: rv_vaddr :: rv_paddr :: nil |] **
      [| logicl = (logic_isr isr) :: (logic_ie ie) :: (logic_is is) :: (logic_cs cs) :: (logic_ier ier) ::
                         (logic_lv xmpaxvl) :: (logic_lv sms_mpaxvl) :: (logic_lv ses_mpaxvl) ::
                          logic_latlv evstructs :: logic_code s :: nil |] **
      p_local OSLInv ct init_lg.

Theorem switchDomainPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (switchDomainPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition switchDomainPre: fpre :=
  fun vl ll ct=> mkfunasrt (switchDomainPreGood vl ll ct).

(* SUPERVISOR_MODE_EN = 0 *)
Definition switchDomainPre'_no_sup (vl:vallist) (logicl:list logicvar) ct :=
  EX isr ie is ier cs kscurd kslastd ksdom absks rtsk_vll absrtsk
         xmpaxvl xmpax sms_mpaxvl sms_mpax ses_mpaxvl ses_mpax
         evstructs vl0 vl1 vl2 vl3 vl4 vl5
         lmpaxh lmpaxl lsms_mpaxh lsms_mpaxl lses_mpaxh lses_mpaxl
         vl' rv_baddr rv_raddr rv_size rv_vaddr rv_paddr s,
      Aisr isr ** Aie ie **  Ais is ** Acs cs ** Aier ier ** A_isr_is_prop ** 
      AKsCurDomain kscurd  ** HKsCurDomain kscurd **
      AKsLastDomain kslastd  ** HKsLastDomain kslastd **
      AKsDomains ksdom absks ** HKsDomains absks **
      ARootTaskStk rtsk_vll absrtsk **
      AXMpax xmpaxvl xmpax **
      ASMSMpax sms_mpaxvl sms_mpax ** 
      ASESMpax ses_mpaxvl ses_mpax **
      HEvStructHeap evstructs ** AEvStructHeap evstructs **
      [| Get_struct evstructs lmpaxh = Some (lmpaxh, XMC_XMPAXH, vl0) /\
          struct_type_vallist_match XMC_XMPAXH vl0 |] **
      [| Get_struct evstructs lsms_mpaxh = Some (lsms_mpaxh, MSMC_SMSMPAXH, vl1) /\
          struct_type_vallist_match MSMC_SMSMPAXH vl1 |] **
      [| Get_struct evstructs lses_mpaxh = Some (lses_mpaxh, MSMC_SESMPAXH, vl2) /\
          struct_type_vallist_match MSMC_SESMPAXH vl2 |] **
      [| Get_struct evstructs lmpaxl = Some (lmpaxl, XMC_XMPAXL, vl3) /\
          struct_type_vallist_match XMC_XMPAXL vl3 |] **
      [| Get_struct evstructs lsms_mpaxl = Some (lsms_mpaxl, MSMC_SMSMPAXL, vl4) /\
          struct_type_vallist_match MSMC_SMSMPAXL vl4 |] **
      [| Get_struct evstructs lses_mpaxl = Some (lses_mpaxl, MSMC_SESMPAXL, vl5) /\
          struct_type_vallist_match MSMC_SESMPAXL vl5 |] **
      [| ptr_no_dup vl |] **
      <|| spec_code_cons (switchDom' (vl ++ vl')) s ||> **
      [| vl = (Vptr lmpaxh) :: (Vptr lmpaxl) :: (Vptr lses_mpaxh) ::
                   (Vptr lses_mpaxl) :: (Vptr lsms_mpaxh) :: (Vptr lsms_mpaxl) :: nil |] **
      [| vl' = rv_baddr :: rv_raddr :: rv_size :: rv_vaddr :: rv_paddr :: nil |] **
      [| logicl = (logic_isr isr) :: (logic_ie ie) :: (logic_is is) :: (logic_cs cs) :: (logic_ier ier) ::
                         (logic_lv xmpaxvl) :: (logic_lv sms_mpaxvl) :: (logic_lv ses_mpaxvl) ::
                          logic_latlv evstructs :: logic_code s :: nil |] **
      p_local OSLInv ct init_lg.

Theorem switchDomainPreGood_no_sup (vl:vallist) logicl ct:
  GoodFunAsrt (switchDomainPre'_no_sup vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition switchDomainPre_no_sup: fpre :=
  fun vl ll ct=> mkfunasrt (switchDomainPreGood_no_sup vl ll ct).

Definition switchDomainPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX isr ie is ier cs kscurd kslastd ksdom absks rtsk_vll absrtsk
         xmpaxvl sms_mpaxvl ses_mpaxvl evstructs
         xmpaxvl' xmpax' sms_mpaxvl' sms_mpax' ses_mpaxvl' ses_mpax'
         xmpaxl' xmpaxh' smsmpaxl' smsmpaxh' sesmpaxl' sesmpaxh'
         evstructs0 evstructs1 evstructs2 evstructs3 evstructs4 evstructs5
         evstructs' vl0' vl1' vl2' vl3' vl4' vl5'
         lmpaxh lmpaxl lsms_mpaxh lsms_mpaxl lses_mpaxh lses_mpaxl s,
     Aisr isr ** Aie ie **  Ais is ** Acs cs ** Aier ier ** A_isr_is_prop ** 
     AKsCurDomain kscurd  ** HKsCurDomain kscurd **
     AKsLastDomain kslastd  ** HKsLastDomain kslastd **
     AKsDomains ksdom absks ** HKsDomains absks **
     ARootTaskStk rtsk_vll absrtsk **
     AXMpax xmpaxvl' xmpax' **
     ASMSMpax sms_mpaxvl' sms_mpax' ** 
     ASESMpax ses_mpaxvl' ses_mpax' **
     HEvStructHeap evstructs' **
     AEvStructHeap evstructs' **
     [| kscurd = kslastd -> xmpaxvl' =  xmpaxvl /\  sms_mpaxvl' = sms_mpaxvl /\
                                                ses_mpaxvl' = ses_mpaxvl /\ evstructs' = evstructs |] **
     [| kscurd <> kslastd ->
         nth_val (Z.to_nat ( 2 * MPAXSHIPARTIONCUR)) xmpaxvl' = Some (Vint32 xmpaxl') /\
         nth_val (Z.to_nat ( 2 * MPAXSHIPARTIONCUR + 1)) xmpaxvl' = Some (Vint32 xmpaxh') /\
         nth_val (Z.to_nat ( 2 * MPAXSHIPARTIONCUR)) sms_mpaxvl' = Some (Vint32 smsmpaxl') /\
         nth_val (Z.to_nat ( 2 * MPAXSHIPARTIONCUR + 1)) sms_mpaxvl' = Some (Vint32 smsmpaxh') /\
         nth_val (Z.to_nat ( 2 * MPAXSHIPARTIONCUR)) ses_mpaxvl' = Some (Vint32 sesmpaxl') /\
         nth_val (Z.to_nat ( 2 * MPAXSHIPARTIONCUR + 1)) ses_mpaxvl' = Some (Vint32 sesmpaxh') /\
         evstructs5 = evstructs' /\
         vl5' = get_mpax_struct sesmpaxl' (sesl_raddr :: sesl_sr :: sesl_sw ::
                                                                              sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil) /\
         vl4' = get_mpax_struct smsmpaxl' (smsl_raddr :: smsl_sr :: smsl_sw ::
                                                                                smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil) /\
         vl3' = get_mpax_struct xmpaxl' (xmc_raddr :: xmc_sr :: xmc_sw ::
                                                                          xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil) /\
         vl2' = get_mpax_struct sesmpaxh' (sesh_baddr :: sesh_segsize :: nil) /\
         vl1' = get_mpax_struct smsmpaxh' (smsh_baddr :: smsh_segsize :: nil) /\
         vl0' = get_mpax_struct xmpaxh' (xmc_baddr :: xmc_segsize :: nil) /\
         (*   sesmpaxl *)
         struct_type_vallist_match MSMC_SESMPAXL vl5' /\
         Set_struct evstructs4 lses_mpaxl MSMC_SESMPAXL vl5' = evstructs5 /\
         (*   smsmpaxl *)
         struct_type_vallist_match MSMC_SMSMPAXL vl4' /\
         Set_struct evstructs3 lsms_mpaxl MSMC_SMSMPAXL vl4' = evstructs4 /\
         (*   xmpaxl *)
         struct_type_vallist_match XMC_XMPAXL vl3' /\
         Set_struct evstructs2 lmpaxl XMC_XMPAXL vl3' = evstructs3 /\
        (*   sesmpaxh *)
         struct_type_vallist_match MSMC_SESMPAXH vl2' /\
         Set_struct evstructs1 lses_mpaxh MSMC_SESMPAXH vl2' = evstructs2 /\
        (*   smsmpaxh *)
         struct_type_vallist_match MSMC_SMSMPAXH vl1' /\
         Set_struct evstructs0 lsms_mpaxh MSMC_SMSMPAXH vl1' = evstructs1 /\
         (*   xmpaxh *)
         struct_type_vallist_match XMC_XMPAXH vl0' /\
         Set_struct evstructs lmpaxh XMC_XMPAXH vl0' = evstructs0
          |] **
      <|| s ||> ** 
      [| vl = (Vptr lmpaxh) :: (Vptr lmpaxl) :: (Vptr lses_mpaxh) ::
                   (Vptr lses_mpaxl) :: (Vptr lsms_mpaxh) :: (Vptr lsms_mpaxl) :: nil |] **
      [| logicl = (logic_isr isr) :: (logic_ie ie) :: (logic_is is) :: (logic_cs cs) :: (logic_ier ier) ::
                         (logic_lv xmpaxvl) :: (logic_lv sms_mpaxvl) :: (logic_lv ses_mpaxvl) ::
                          logic_latlv evstructs :: logic_code s :: nil |] **
      p_local OSLInv ct init_lg.

Theorem switchDomainPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (switchDomainPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition switchDomainPost : fpost :=
 fun vl v ll ct=> mkfunasrt (switchDomainPostGood vl v ll ct).

Definition switchDomain_spec : fspec:=
     (switchDomainPre,switchDomainPost,
                     (Tvoid, Tptr XMC_XMPAXH :: Tptr XMC_XMPAXL ::
                                    Tptr MSMC_SESMPAXH :: Tptr MSMC_SESMPAXL ::
                                    Tptr MSMC_SMSMPAXH :: Tptr MSMC_SMSMPAXL :: nil)).

Definition switchDomain_no_sup_spec : fspec:=
     (switchDomainPre_no_sup,switchDomainPost,
                     (Tvoid, Tptr XMC_XMPAXH :: Tptr XMC_XMPAXL ::
                                    Tptr MSMC_SESMPAXH :: Tptr MSMC_SESMPAXL ::
                                    Tptr MSMC_SMSMPAXH :: Tptr MSMC_SMSMPAXL :: nil)).

(* initDefaultMPAX *)

Definition initDefaultMPAXPre' (vl:vallist) (logicl:list logicvar) ct :=
  EX isr ie is ier cs xmpax sms_mpax ses_mpax xmpaxvl sms_mpaxvl ses_mpaxvl 
      evstructs q0 q1 q2 vl0 vl1 vl2 s,
      Aisr isr ** Aie ie **  Ais is ** Acs cs ** Aier ier ** A_isr_is_prop ** 
      AXMpax xmpaxvl xmpax **
      ASMSMpax sms_mpaxvl sms_mpax ** 
      ASESMpax ses_mpaxvl ses_mpax **
      HEvStructHeap evstructs ** AEvStructHeap evstructs **
      [| Get_struct evstructs q0 = Some (q0, XMC_XMPAXL, vl0) /\ struct_type_vallist_match XMC_XMPAXL vl0 |] **
      [| Get_struct evstructs q1 = Some (q1, MSMC_SMSMPAXL, vl1) /\ struct_type_vallist_match MSMC_SMSMPAXL vl1 |] **
      [| Get_struct evstructs q2 = Some (q2, MSMC_SESMPAXL, vl2) /\ struct_type_vallist_match MSMC_SESMPAXL vl2 |] **
      [|q0 <> q1 /\ q0 <> q2 /\  q1 <> q2|] **
      <||  spec_code_cons (initDefaultMPAX' vl) s ||> **
      [| vl = (Vptr q0) :: (Vptr q1) :: (Vptr q2) :: nil |] **
      [| logicl = (logic_isr isr) :: (logic_ie ie) :: (logic_is is) :: (logic_cs cs) :: (logic_ier ier) :: logic_latlv evstructs :: logic_code s :: nil |] **
      p_local OSLInv ct init_lg.

Theorem initDefaultMPAXPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (initDefaultMPAXPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition initDefaultMPAXPre: fpre :=
  fun vl ll ct=> mkfunasrt (initDefaultMPAXPreGood vl ll ct).

Definition initDefaultMPAXPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX isr ie is ier cs xmpax' sms_mpax' ses_mpax' xmpaxvl' sms_mpaxvl' ses_mpaxvl'
     evstructs evstructs' evstructs'' evstructs''' q0 q1 q2 vl0' vl1' vl2'
     xmpaxl' smsmpaxl' sesmpaxl' s,
     Aisr isr ** Aie ie **  Ais is ** Acs cs ** Aier ier ** A_isr_is_prop ** 
     AXMpax xmpaxvl' xmpax' **
     ASMSMpax sms_mpaxvl' sms_mpax' ** 
     ASESMpax ses_mpaxvl' ses_mpax' **
     HEvStructHeap evstructs''' ** 
     AEvStructHeap evstructs''' **
  (*     xmpaxl *)
      [| Set_struct evstructs q0 XMC_XMPAXL vl0' = evstructs' /\   
         struct_type_vallist_match XMC_XMPAXL vl0' |] **
      [| vl0' = get_mpax_struct xmpaxl' (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx ::
                                          xmc_ur :: xmc_uw :: xmc_ux :: nil) |] **
      [| nth_val 2 xmpaxvl' = Some (Vint32 xmpaxl') |] **
  (*     sms_mpaxl *)
      [| Set_struct evstructs' q1 MSMC_SMSMPAXL vl1' = evstructs'' /\   
         struct_type_vallist_match MSMC_SMSMPAXL vl1' |] **
      [| vl1' = get_mpax_struct smsmpaxl' (smsl_raddr :: smsl_sr :: smsl_sw ::
                                smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil) |] **
      [| nth_val 0 sms_mpaxvl' = Some (Vint32 smsmpaxl') |] **
  (*     ses_mpaxl *)
      [| Set_struct evstructs'' q2 MSMC_SESMPAXL vl2' = evstructs''' /\   
         struct_type_vallist_match MSMC_SESMPAXL vl2' |] **
      [| vl2' = get_mpax_struct sesmpaxl' (sesl_raddr :: sesl_sr :: sesl_sw ::
                                sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil) |] **
      [| nth_val 0 ses_mpaxvl' = Some (Vint32 sesmpaxl') |] **
      <|| s ||> ** 
      [|vl = (Vptr q0) :: (Vptr q1) :: (Vptr q2) :: nil /\ v = None|] **
      [| logicl = (logic_isr isr) :: (logic_ie ie) :: (logic_is is) :: (logic_cs cs) :: (logic_ier ier) :: logic_latlv evstructs :: logic_code s :: nil |] **
      p_local OSLInv ct init_lg.

Theorem initDefaultMPAXPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (initDefaultMPAXPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition initDefaultMPAXPost : fpost :=
 fun vl v ll ct=> mkfunasrt (initDefaultMPAXPostGood vl v ll ct).

Definition initDefaultMPAX_spec : fspec:= 
            (initDefaultMPAXPre,initDefaultMPAXPost,
             (Tvoid, Tptr XMC_XMPAXL :: Tptr MSMC_SMSMPAXL :: Tptr MSMC_SESMPAXL :: nil)).

(* initMPAX *)

Definition initMPAXPre' (vl:vallist) (logicl:list logicvar) ct :=
  EX isr ie is ier cs xmpax sms_mpax ses_mpax
     xmpaxvl sms_mpaxvl ses_mpaxvl 
     evstructs vl0 vl1 vl2 vl3 vl4 vl5 
     lmpaxh lmpaxl lsms_mpaxh lsms_mpaxl lses_mpaxh lses_mpaxl
     vl' rv_baddr rv_raddr rv_size rv_vaddr rv_paddr
     kscurd ksdom absks rtsk_vll absrtsk s,
      Aisr isr ** Aie ie **  Ais is ** Acs cs ** Aier ier ** A_isr_is_prop ** 
      AKsCurDomain kscurd  ** HKsCurDomain kscurd **
      AKsDomains ksdom absks ** HKsDomains absks **
      ARootTaskStk rtsk_vll absrtsk **
      AXMpax xmpaxvl xmpax **
      ASMSMpax sms_mpaxvl sms_mpax ** 
      ASESMpax ses_mpaxvl ses_mpax **
      AXMPFR ** AMDMAER **
      HEvStructHeap evstructs ** AEvStructHeap evstructs **
      [| Get_struct evstructs lmpaxh = Some (lmpaxh, XMC_XMPAXH, vl0) /\ struct_type_vallist_match XMC_XMPAXH vl0 |] **
      [| Get_struct evstructs lmpaxl = Some (lmpaxl, XMC_XMPAXL, vl1) /\ struct_type_vallist_match XMC_XMPAXL vl1 |] **
      [| Get_struct evstructs lsms_mpaxh = Some (lsms_mpaxh, MSMC_SMSMPAXH, vl2) /\ struct_type_vallist_match MSMC_SMSMPAXH vl2 |] **
      [| Get_struct evstructs lsms_mpaxl = Some (lsms_mpaxl, MSMC_SMSMPAXL, vl3) /\ struct_type_vallist_match MSMC_SMSMPAXL vl3 |] **
      [| Get_struct evstructs lses_mpaxh = Some (lses_mpaxh, MSMC_SESMPAXH, vl4) /\ struct_type_vallist_match MSMC_SESMPAXH vl4 |] **
      [| Get_struct evstructs lses_mpaxl = Some (lses_mpaxl, MSMC_SESMPAXL, vl5) /\ struct_type_vallist_match MSMC_SESMPAXL vl5 |] **
      [| ptr_no_dup vl|] **
      <|| spec_code_cons' (initMPAX' (vl ++ vl')) s ||> **
      [| vl = (Vptr lmpaxh) :: (Vptr lmpaxl) :: (Vptr lses_mpaxh) ::
              (Vptr lses_mpaxl) :: (Vptr lsms_mpaxh) :: (Vptr lsms_mpaxl) ::
              nil |] **
      [| vl' = rv_baddr :: rv_raddr :: rv_size :: rv_vaddr :: rv_paddr :: nil |] **
      [| logicl = (logic_isr isr) :: (logic_ie ie) :: (logic_is is) :: (logic_cs cs) :: (logic_ier ier) :: logic_latlv evstructs :: logic_code s :: nil |] **
      p_local OSLInv ct init_lg.

Theorem initMPAXPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (initMPAXPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition initMPAXPre: fpre :=
  fun vl ll ct=> mkfunasrt (initMPAXPreGood vl ll ct).

Definition initMPAXPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX isr ie is ier cs xmpax' sms_mpax' ses_mpax' 
     xmpaxvl' sms_mpaxvl' ses_mpaxvl' 
     evstructs evstructs' evstructs0 evstructs1 evstructs2 evstructs3 evstructs4 evstructs5
     lmpaxh lmpaxl lsms_mpaxh lsms_mpaxl lses_mpaxh lses_mpaxl vl0' vl1' vl2' vl3' vl4' vl5'
     xmpaxl'  smsmpaxl' sesmpaxl' xmpaxh' smsmpaxh' sesmpaxh' 
     kscurd ksdom absks rtsk_vll absrtsk s,
     Aisr isr ** Aie ie **  Ais is ** Acs cs ** Aier ier ** A_isr_is_prop ** 
     AKsCurDomain kscurd  ** HKsCurDomain kscurd **
     AKsDomains ksdom absks ** HKsDomains absks **
     ARootTaskStk rtsk_vll absrtsk **
     AXMpax xmpaxvl' xmpax' **
     ASMSMpax sms_mpaxvl' sms_mpax' ** 
     ASESMpax ses_mpaxvl' ses_mpax' **
     AXMPFR ** AMDMAER **
     HEvStructHeap evstructs5 **
     AEvStructHeap evstructs5 **
(*   xmpaxh *)
      [| Set_struct evstructs' lmpaxh XMC_XMPAXH vl0' = evstructs0 /\   
         struct_type_vallist_match XMC_XMPAXH vl0' |] **
      [| vl0' = get_mpax_struct xmpaxh' (xmc_baddr :: xmc_segsize :: nil) |] **
      [| nth_val 7 xmpaxvl' = Some (Vint32 xmpaxh') |] **
(*   sms_mpaxh *)
      [| Set_struct evstructs0 lsms_mpaxh MSMC_SMSMPAXH vl1' = evstructs1 /\
         struct_type_vallist_match MSMC_SMSMPAXH vl1' |] **
      [| vl1' = get_mpax_struct smsmpaxh' (smsh_baddr :: smsh_segsize :: nil) |] **
      [| nth_val 7 sms_mpaxvl' = Some (Vint32 smsmpaxh') |] **
(*   ses_mpaxh *)
      [| Set_struct evstructs1 lses_mpaxh MSMC_SESMPAXH vl2' = evstructs2 /\
         struct_type_vallist_match MSMC_SESMPAXH vl2' |] **
      [| vl2' = get_mpax_struct sesmpaxh' (sesh_baddr :: sesh_segsize :: nil) |] **
      [| nth_val 7 ses_mpaxvl' = Some (Vint32 sesmpaxh') |] **
(*   xmpaxl *)
      [| Set_struct evstructs2 lmpaxl XMC_XMPAXL vl3' = evstructs3 /\
         struct_type_vallist_match XMC_XMPAXL vl3' |] **
      [| vl3' = get_mpax_struct xmpaxl' (xmc_raddr :: xmc_sr :: xmc_sw ::
                                    xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil) |] **
      [| nth_val 6 xmpaxvl' = Some (Vint32 xmpaxl') |] **
(*   sms_mpaxl *)
      [| Set_struct evstructs3 lsms_mpaxl MSMC_SMSMPAXL vl4' = evstructs4 /\
         struct_type_vallist_match MSMC_SMSMPAXL vl4' |] **
      [| vl4' = get_mpax_struct smsmpaxl' (smsl_raddr :: smsl_sr :: smsl_sw ::
                               smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil) |] **
      [| nth_val 6 sms_mpaxvl' = Some (Vint32 smsmpaxl') |] **
(*   ses_mpaxl *)
      [| Set_struct evstructs4 lses_mpaxl MSMC_SESMPAXL vl5' = evstructs5 /\
         struct_type_vallist_match MSMC_SESMPAXL vl5' |] **
      [| vl5' = get_mpax_struct sesmpaxl' (sesl_raddr :: sesl_sr :: sesl_sw ::
                               sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil) |] **
      [| nth_val 6 ses_mpaxvl' = Some (Vint32 sesmpaxl') |] **
      <|| s ||> ** 
      [| vl = (Vptr lmpaxh) :: (Vptr lmpaxl) :: (Vptr lses_mpaxh) ::
              (Vptr lses_mpaxl) :: (Vptr lsms_mpaxh) :: (Vptr lsms_mpaxl) :: nil /\ v = None|] **
      [| logicl = (logic_isr isr) :: (logic_ie ie) :: (logic_is is) :: (logic_cs cs) :: (logic_ier ier) :: logic_latlv evstructs :: logic_code s :: nil |] **
      p_local OSLInv ct init_lg.

Theorem initMPAXPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (initMPAXPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition initMPAXPost : fpost :=
 fun vl v ll ct=> mkfunasrt (initMPAXPostGood vl v ll ct).

Definition initMPAX_spec : fspec:= 
      (initMPAXPre,initMPAXPost,
               (Tvoid, Tptr XMC_XMPAXH :: Tptr XMC_XMPAXL :: 
                        Tptr MSMC_SESMPAXH :: Tptr MSMC_SESMPAXL :: 
                        Tptr MSMC_SMSMPAXH :: Tptr MSMC_SMSMPAXL :: nil)).

(* is_bigEndian *)

Definition is_bigEndianPre' (vl:vallist) (logicl:list logicvar) (ct :tid) :=
EX isr ie is cs er s  logicl' ,  
     Aisr isr ** Aie ie ** Ais is ** Acs cs** Aier er **
    <||s||> ** 
     [|logicl = logic_isr isr :: logic_is is :: logic_cs cs :: logic_ier er :: logic_code s :: logicl'|] ** 
     p_local OSLInv ct (logic_val (V$ 1) :: logicl') .

Definition is_bigEndianPost' (vl:vallist) (v:option val) (logicl:list logicvar) (ct :tid):=
    (EX isr ie is cs er s  logicl' b ,  
     Aisr isr ** Aie ie ** Ais is ** Acs cs** Aier er **
    [|Int.eq b ($ 52) = true|]**
    [| v = Some (V$ 0)|] **
    <||s||>**
    [|logicl = logic_isr isr :: logic_is is :: logic_cs cs :: logic_ier er :: logic_code s :: logicl'|] ** 
     p_local OSLInv ct (logic_val (V$ 1) :: logicl')) \\// 
    (EX isr ie is cs er s  logicl' b ,  
     Aisr isr ** Aie ie ** Ais is ** Acs cs** Aier er **
    [|Int.eq b ($ 52) = false|]**
    [| v = Some (V$ 1)|] **
    <||s||>**
    [|logicl = logic_isr isr :: logic_is is :: logic_cs cs :: logic_ier er :: logic_code s :: logicl'|] ** 
     p_local OSLInv ct (logic_val (V$ 1) :: logicl')).

Theorem is_bigEndianPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (is_bigEndianPost'  vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Theorem is_bigEndianPreGood (vl:vallist) ll ct:
  GoodFunAsrt (is_bigEndianPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition is_bigEndianPre : fpre :=
  fun vl ll ct => mkfunasrt (is_bigEndianPreGood vl ll ct).

Definition is_bigEndianPost : fpost :=
  fun vl v ll ct => mkfunasrt (is_bigEndianPostGood vl v ll ct).

Definition is_bigEndian_spec : fspec := (is_bigEndianPre,is_bigEndianPost,(Tint8, nil)).

(* InitDNUM *)

Fixpoint take  { A : Type} (n : nat) (l: list A)  : list A :=
  match n with
  | O => nil
  | S m => match (nth_error l m) with
                 | None => take m l
                 | Some v => v :: take m l
                 end
  end.

Fixpoint num_binaddr_e (l : list domainConfVal ) : nat :=
  match l with
  | nil => 0%nat
  | (v0,v1,v2,v3) :: l' => 
        match (nth_val 3 v0) with
          | (Some (Vint32 x) )=> 
              if(Int.eq x ($0)) 
                then (num_binaddr_e l') 
              else S (num_binaddr_e l')
          | _ => (num_binaddr_e l')
          end
end.

Definition ksDomain_P (cos : ucosConfVal) i corenum dom2inde j0 dom2inde0:=
  (forall k,0 <= k < (Int.unsigned i)  -> (
  exists vl0 intrdom areac cpuc channelc portc svl ,
    exists node1 ldomrtbl lksdstbl lksdomtbl curdom, 
      exists  v0 v1 v2 v3 cpucur ,  
        exists x3  x j',
        (cos = (vl0 , intrdom, areac, cpuc, channelc, portc, svl)  /\
        nth_error cpuc corenum  = Some cpucur  /\   
        cpucur = (node1,ldomrtbl, lksdstbl,lksdomtbl  )  /\
        nth_error lksdomtbl (nat_of_Z k)   =  Some curdom  /\
        curdom = (v0,v1,v2,v3) /\
        nth_val 3 v0 = Some (Vint32 x3) /\
        nth_val 0 v0 = Some (Vint32 x) /\
        num_binaddr_e (take (nat_of_Z (k + 1)) lksdomtbl) = (Z.to_nat (Int.unsigned j')) /\
        (k = (Int.unsigned i) - 1 -> j' = j0 ) /\
        (exists m1 ,  
            Int.eq x3 ($ 0) = false ->
                (m1 =  (j' -ᵢ  $ 1) /\
                 nth_val (Z.to_nat (Int.unsigned x)) dom2inde = Some (Vint32 m1)))))
   )  /\
  (forall k', 0 <= k' < 8 ->
  (
    exists vl0 intrdom areac cpuc channelc portc svl ,
     exists node1 ldomrtbl lksdstbl lksdomtbl curdom, 
      exists  v0 v1 v2 v3 cpucur m' m2 x x3,  
        (
        cos = (vl0 , intrdom, areac, cpuc, channelc, portc, svl)  /\
        nth_error cpuc corenum  = Some cpucur  /\   
        cpucur = (node1,ldomrtbl, lksdstbl,lksdomtbl  )  /\
        nth_error lksdomtbl (nat_of_Z k')   =  Some curdom  /\
        curdom = (v0,v1,v2,v3) /\
        nth_val 3 v0 = Some (Vint32 x3) /\
        nth_val 0 v0 = Some (Vint32 x) /\
        Int.eq x3 ($ 0) = true /\
        nth_val (Z.to_nat (Int.unsigned x)) dom2inde = Some (Vint32 m2) /\
        nth_val (Z.to_nat (Int.unsigned x)) dom2inde0  = Some (Vint32 m')
        ) ->
        m' = m2 
        )
   ).

Definition Domainslen_P n (cfDomvl : list domainConfVal)  (Domvl' : list Doamin_t_val) (ksDomsc : list dscheduleConfVal) pIDDomvl:=
  forall i , 0 <= i /\ i < n ->
  (
    forall j curksDomsc curDom curcfDom vl1 vl2 vl3 vl4,
    forall v0 v1 v2 v3 v4 v5 v6 v0' v1' v2',
    forall  v3' v4' v5' v6' pID vldomat,
      nth_error ksDomsc (nat_of_Z i) = Some curksDomsc ->
      nth_val 0 curksDomsc = Some (Vint32 j) ->
      nth_error Domvl' (nat_of_Z (Int.unsigned j))  = Some (curDom,vldomat) ->
      nth_error cfDomvl (nat_of_Z (Int.unsigned j))  = Some curcfDom ->
      curcfDom = (vl1,vl2,vl3,vl4) ->
      nth_val 0 curDom = Some v0 ->
      nth_val 1 curDom = Some v1 ->
      nth_val 2 curDom = Some v2 ->
      nth_val 3 curDom = Some v3 ->
      nth_val 4 curDom = Some v4 ->
      nth_val 5 curDom = Some v5 ->
      nth_val 6 curDom = Some v6 ->

      nth_val 0 vl1 = Some v0' ->
      nth_val 2 vl1 = Some (Vint32 v1') ->
      nth_val 5 vl1 = Some v2' ->
      nth_val 6 vl1 = Some v3' ->
      nth_val 7 vl1 = Some v4' ->
      nth_val 8 vl1 = Some v5' ->
      nth_val 9 vl1 = Some v6' ->
      nth_val (nat_of_Z (Int.unsigned v1')) pIDDomvl = Some pID 
      ->
      Some v0 = Some v0' /\
      Some v1 = Some (Vint32 v1') /\
      Some v2 = Some v2' /\
      Some v3 = Some v3' /\
      Some v4 = Some v4' /\
      Some v5 = Some v5' /\
      Some v6 = Some v6' /\
      Some pID = Some v0 
      ).

Definition ksDomSchedule_P n DomSchvl cfDomSchvl:=
  forall i domain length curcfDomsc cfdomain cflength curksDomsc, 
  0 <= i /\ i < n ->
  (
      nth_error cfDomSchvl (nat_of_Z i)  = Some curcfDomsc ->
      nth_val 0 curcfDomsc = Some (Vint32 cfdomain) ->
      nth_val 1 curcfDomsc = Some (Vint32 cflength) ->
      nth_vallist (nat_of_Z i) DomSchvl = Some curksDomsc ->
      nth_val 0 curksDomsc = Some (Vint32 domain) ->
      nth_val 1 curksDomsc = Some (Vint32 length) ->
      cfdomain = domain /\
      cflength = length
      ).

Definition Cfnoport_P n len cfportvll (domvll : list Doamin_t_val) domschvll portattrvll (partID2domvl : vallist):= 
  forall i j, 0 <= i < n ->
  (
    exists curcfport partID curdomsch dscd_domain curdom_t vl1 dom_ID ,
    0 <= (Z.of_nat j) < len /\
  nth_vallist (Z.to_nat i) cfportvll = Some curcfport /\
  nth_val 3 curcfport =Some (Vint32 partID) /\
  nth_vallist j domschvll = Some curdomsch /\
  nth_val 0 curdomsch =Some (Vint32 dscd_domain) /\
  nth_error domvll (Z.to_nat (Int.unsigned dscd_domain))  = Some (curdom_t,vl1) /\
  nth_val 1 curdom_t = Some dom_ID /\
  Vint32 partID = dom_ID ->
  (exists cfptblID curportvl ,
    nth_val 0 curcfport = Some (Vint32 cfptblID) /\
    nth_vallist (Z.to_nat (Int.unsigned cfptblID)) portattrvll = Some curportvl /\
    nth_val 1 curportvl = Some (Vint32 partID) /\
    nth_val 2 curportvl = nth_val (Z.to_nat (Int.unsigned partID)) partID2domvl /\
    nth_val 3 curportvl = nth_val 1 curcfport /\
    nth_val 4 curportvl = nth_val 2 curcfport /\
    nth_val 5 curportvl = nth_val 4 curcfport /\
    nth_val 0 curportvl = Some (V$ 1)
  )).

Definition PortAttr_P i j len flag cfportvll portattrvll (partID2domvl : vallist):= 
(exists curcfport partID ,
    exists cfptblID curportvl ,
    flag =( V$ 0) /\ 0 <= (Z.of_nat j )< len ->
    (
      nth_vallist i cfportvll = Some curcfport /\
      nth_val 3 curcfport =Some (Vint32 partID) /\

      nth_val 0 curcfport =Some (Vint32 cfptblID) /\
      nth_vallist (Z.to_nat (Int.unsigned cfptblID)) portattrvll = Some curportvl /\
      nth_val 1 curportvl = Some (Vint32 partID) /\
      nth_val 2 curportvl = nth_val (Z.to_nat (Int.unsigned partID)) partID2domvl /\
      nth_val 3 curportvl = nth_val 1 curcfport /\
      nth_val 4 curportvl = nth_val 2 curcfport /\
      nth_val 5 curportvl = nth_val 4 curcfport /\
      nth_val 0 curportvl = Some (V$ 1) 
    )).

Definition PortAttr_P1 i j flag cfportvll (domvll : list Doamin_t_val) domschvll := 
  forall k, flag =(V$ 1) /\ 0 <= (Z.of_nat k )< j->
  (exists curcfport partID curdomsch dscd_domain curdom_t vl1 dom_ID ,
    nth_vallist (Z.to_nat i) cfportvll = Some curcfport /\
    nth_val 3 curcfport =Some (Vint32 partID) /\
    nth_vallist k domschvll = Some curdomsch /\
    nth_val 0 curdomsch =Some (Vint32 dscd_domain) /\
    nth_error domvll (Z.to_nat (Int.unsigned dscd_domain))  = Some (curdom_t,vl1) /\
    nth_val 1 curdom_t = Some dom_ID /\
    Vint32 partID <> dom_ID).

(* a subset of AKsDomains vl ksdomls, without absdata *)
Definition AKsDomain vl := 
    (EX lksdomains b i,
         GV ksDomains @ Tptr domain_t |-> Vptr lksdomains **
         AKsDomains' (Vptr lksdomains) vl **
         [| length vl = (nat_of_Z DOMAIN_SIZE) |]**
         [| lksdomains = (b, i) |]).

Definition initDnumPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX  isr is cs ie s lg'  crecos absucos vl1  corenum
  ksdomain partID2dom allparta ksdschdlen ksdschedule portattrt er num,
     Aisr isr ** Aie ie ** Ais is ** Acs cs ** Aier er ** A_isr_is_prop **
     [|logicl = logic_lv vl1 :: logic_isr isr :: logic_is is :: logic_cs cs :: logic_ier er :: logic_code s :: lg'|] ** 
     p_local OSLInv ct (logic_val (V$ 1) :: lg') **
     [| nth_val 0 vl = Some (Vptr BOOT_DATA_ADDRESS) |] **
     [| nth_val 1 vl =Some  (Vint32 corenum)|] **
     [|  0 <= Int.unsigned corenum < 8  |] **
     <||s||> **  AucosConf crecos absucos ** Adomain2index' vl1 **
     AKsDomain ksdomain ** APartID2Dom partID2dom ** APortnumcur  ** APartArea' allparta **
     AKsDSchdlen ksdschdlen ** AKsDomSchedule' ksdschedule **
     AOSPortAttrTbl' portattrt ** ACorepartnum' num.

Theorem initDnumPreGood (vl:vallist) ll ct:
GoodFunAsrt (initDnumPre' vl ll ct).
Proof.
GoodFunAsrt_solver.
Qed.

Definition initDnumPre : fpre :=
  fun vl ll ct => mkfunasrt (initDnumPreGood vl ll ct).

Definition initDnumPost' (vl:vallist) (v:option val) (logicl:list logicvar) (ct : tid) := 
EX  isr is cs ie s lg'  crecos absucos vl1 vl1' corenum j domvl0 ksdomain' partID2dom' allparta'
        ksdschdlen' ksdschedule' portattrt' a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 n len er num',
    Aisr isr ** Aie ie ** Ais is ** Acs cs ** Aier er ** A_isr_is_prop  ** 
    [|logicl =logic_lv vl1 :: logic_isr isr :: logic_is is :: logic_cs cs  :: logic_ier er :: logic_code s :: lg'|] ** 
    p_local OSLInv ct (logic_val (V$ 1) :: lg') ** 
    <||s||> **
   [| ksDomain_P crecos ($ 8) corenum vl1' j domvl0|] **
   [| crecos = (a1,b1,c1,d1,e1,f1,g1) /\ nth_error d1 corenum  = Some (h1,i1,j1,k1)
         /\ nth_val 2 h1= Some (Vint32 len) |] **
   [| nth_val 3 h1= Some (Vint32 num') |] **
   [|  allparta' = ((nth_val' 0  c1):: (nth_val' 1 c1) :: (nth_val' 2 c1 ):: nil ) |] **
   [| Domainslen_P  (Int.unsigned len) k1 ksdomain' j1 partID2dom' |]  **
   [| ksdschdlen' = len |] **
   [| ksDomSchedule_P (Int.unsigned len) ksdschedule' j1 |] **
   [|  nth_val 5 a1 = Some (Vint32 n)|] **
   [| Cfnoport_P (Int.unsigned n) (Int.unsigned len) g1 ksdomain' ksdschedule' portattrt' partID2dom'|] **
   AucosConf crecos absucos ** Adomain2index' vl1' **
   AKsDomain ksdomain' ** APartID2Dom partID2dom' **  APortnumcur  ** APartArea' allparta' **
   AKsDSchdlen ksdschdlen' ** AKsDomSchedule' ksdschedule' ** AOSPortAttrTbl' portattrt' **
   ACorepartnum' num'.

Theorem initDnumPostGood (vl:vallist) (v:option val) ll ct:
GoodFunAsrt (initDnumPost' vl v ll ct).
Proof.
 GoodFunAsrt_solver.
Qed.

Definition initDnumPost : fpost :=
  fun vl v ll ct => mkfunasrt (initDnumPostGood vl v ll ct).

Definition initDnum_spec : fspec:= (initDnumPre,initDnumPost,(Void, Tptr ucos_conf_t::Tint32::Tint32::nil)).

(* initConf *)

Definition initConfPre' (vl:vallist)(logicl:list logicvar) (ct :tid) :=
EX isr ie is cs er ucosf ucosconf s logicl' vl1 ksdomain partID2dom allparta ksdschdlen ksdschedule portattrt num,
  Aisr isr ** Aie ie ** Ais is ** Acs cs ** Aier er ** A_isr_is_prop ** 
  AucosConf ucosconf ucosf **Adomain2index' vl1 **
  AKsDomain ksdomain ** APartID2Dom partID2dom ** APortnumcur  ** APartArea' allparta **
  AKsDSchdlen ksdschdlen ** AKsDomSchedule' ksdschedule **
  AOSPortAttrTbl' portattrt ** ACorepartnum' num **
  <||s||> **
  [|  0 <=  DNUM < 8  |] ** 
  [|logicl = logic_isr isr :: logic_is is :: logic_cs cs :: logic_ier er :: logic_code s :: logicl'|] **
  p_local OSLInv ct (logic_val (V$ 1) :: logicl').

Theorem initConfPreGood (vl:vallist) ll ct:
  GoodFunAsrt (initConfPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition initConfPre : fpre :=
  fun vl ll ct => mkfunasrt (initConfPreGood vl ll ct).

Definition initConfPost' (vl:vallist) (v:option val) (logicl:list logicvar) (ct :tid):=
EX isr ie is cs er ucosconf ucosf s logicl' vl1' ksdomain' partID2dom' allparta' ksdschdlen' ksdschedule' portattrt' num',
    Aisr isr ** Aie ie ** Ais is ** Acs cs ** Aier er ** A_isr_is_prop  ** 
    AucosConf ucosconf ucosf **Adomain2index' vl1' **
    AKsDomain ksdomain' ** APartID2Dom partID2dom' **  APortnumcur  ** APartArea' allparta' **
    AKsDSchdlen ksdschdlen' ** AKsDomSchedule' ksdschedule' **
    AOSPortAttrTbl' portattrt' ** ACorepartnum' num' **
    <||s||>**
    p_local OSLInv ct (logic_val (V$ 1) :: logicl') .

Theorem initConfPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (initConfPost'  vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition initConfPost : fpost :=
  fun vl v ll ct => mkfunasrt (initConfPostGood vl v ll ct).

Definition initConf_spec : fspec := (initConfPre,initConfPost,(Tvoid , nil)).

(* IntPartitionMuxInit *)

Definition IntPartitionMuxInitPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX isr is cs er intrvl intrabs ucosf intpvl intp
     mgf fv fn fps fccs fnps a cpus ccf ptrg ptrt pt mgl s lg',
    Aisr isr ** Aie false ** Ais is ** Acs cs ** Aier er **
    AIntrDomainMux BOOT_DATA_ADDRESS intrvl intrabs ** Hucosconf ucosf ** 
    Astruct BOOT_DATA_ADDRESS ucos_conf_t intrvl **
    AIntPartMux intpvl intp **
    <||intpartmux vl ;; s||> **
    [| ucosf = (mgf, fv, fn, fps, fccs, fnps, intrabs, a,
                cpus, ccf, ptrg, ptrt, pt, mgl) |] **
    [|struct_type_vallist_match ucos_conf_t intrvl|] **
    [|length intrvl = ∘ 11|] **
    [|logicl = logic_isr isr :: logic_is is :: logic_cs cs :: logic_ier er :: logic_lv intrvl :: logic_code s :: lg'|] ** 
    p_local OSLInv ct (logic_val (V$ 1) :: lg').

Theorem IntPartitionMuxInitPreGood (vl:vallist) ll ct:
  GoodFunAsrt (IntPartitionMuxInitPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition IntPartitionMuxInitPre : fpre :=
  fun vl ll ct => mkfunasrt (IntPartitionMuxInitPreGood vl ll ct).

Definition IntPartMux_P n intrvl intpvl' :=
forall i v1 v2, 0 <= i /\ i < n ->
                        nth_val (nat_of_Z i) intrvl = Some v1 ->
                        nth_val (nat_of_Z i) intpvl' = Some v2 ->
                        Some v1 = Some v2.

Definition IntPartitionMuxInitPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct := 
  EX isr is cs er intrvl intrabs ucosf intpvl' intp' s lg',
    Aisr isr ** Aie false ** Ais is ** Acs cs ** Aier er **
    AIntrDomainMux BOOT_DATA_ADDRESS intrvl intrabs ** Hucosconf ucosf **
    Astruct BOOT_DATA_ADDRESS ucos_conf_t intrvl **
    AIntPartMux intpvl' intp' **
    <||s||> **
    [| IntPartMux_P USER_INT_MAX_N intrvl intpvl'|] **
    [|logicl = logic_isr isr :: logic_is is :: logic_cs cs :: logic_ier er :: logic_lv intrvl :: logic_code s :: lg'|] ** 
    p_local OSLInv ct (logic_val (V$ 1) :: lg').

Theorem IntPartitionMuxInitPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (IntPartitionMuxInitPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition IntPartitionMuxInitPost : fpost :=
  fun vl v ll ct => mkfunasrt (IntPartitionMuxInitPostGood vl v ll ct).

Definition IntPartitionMuxInit_spec : fspec := (IntPartitionMuxInitPre, IntPartitionMuxInitPost, (Tvoid, nil)).

(* InitCorePartition *)

(* some internal function called in the InitCorePartition, can be changed *)
(* is_ELFProgramValid *)

Definition is_ELFProgramValidPre' (vl:vallist) (logicl:list logicvar) (ct:tid):=
  EX file  saddr eaddr (ehdrvl:vallist)  eentry  s er,
   <||s||> ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop ** Aier er **
   [| vl = (Vptr file):: (Vint32 saddr) :: (Vint32 eaddr) :: nil|] **
   [| V_e_entry ehdrvl = Some (Vptr eentry)|] **
   [| struct_type_vallist_match Elf32_Ehdr ehdrvl |] **
   [| logicl = logic_lv ehdrvl ::  logic_code s :: nil |] **
   Astruct file Elf32_Ehdr ehdrvl ** 
   p_local OSLInv ct init_lg.

Theorem is_ELFProgramValidPreGood (vl:vallist) ll ct:
  GoodFunAsrt (is_ELFProgramValidPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition is_ELFProgramValidPre : fpre :=
  fun vl ll ct => mkfunasrt (is_ELFProgramValidPreGood vl ll ct).

(* post *)
Definition is_ELFProgramValidPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:= 
  EX file  saddr eaddr (ehdrvl:vallist)  eentry  s er opv,
   <||s||> ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop ** Aier er **
    [| vl = (Vptr file):: (Vint32 saddr) :: (Vint32 eaddr) :: nil|] **
    [| V_e_entry ehdrvl = Some (Vptr eentry)|] **
    [| struct_type_vallist_match Elf32_Ehdr ehdrvl |] **
    [| logicl = logic_lv ehdrvl :: logic_code s :: nil |] **
    Astruct file Elf32_Ehdr ehdrvl ** 
    [| v = Some (Vint32 opv) |] **
    [| isflag (Vint32 opv) |] **
     p_local OSLInv ct init_lg.

Theorem is_ELFProgramValidPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (is_ELFProgramValidPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition is_ELFProgramValidPost : fpost :=
  fun vl v ll ct => mkfunasrt (is_ELFProgramValidPostGood vl v ll ct).

Definition is_ELFProgramValid_spec: fspec:=
          (is_ELFProgramValidPre, is_ELFProgramValidPost, (Tint32, (Tptr Tvoid):: Tint32 :: Tint32 :: nil)).

Definition LoadElf2Mem''Pre' (vl:vallist) (logicl:list logicvar) (ct:tid):=
  EX file  (ehdrvl:vallist)  eentry  s er,
   <||s||> ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop ** Aier er **
   [| vl = (Vptr file)::nil|] **
    [| V_e_entry ehdrvl = Some (Vptr eentry)|] **
     [| struct_type_vallist_match Elf32_Ehdr ehdrvl |] **
    [| logicl = logic_lv ehdrvl ::  logic_code s :: nil |] **
    Astruct file Elf32_Ehdr ehdrvl ** 
      p_local OSLInv ct init_lg.

Theorem LoadElf2Mem''PreGood (vl:vallist) ll ct:
  GoodFunAsrt (LoadElf2Mem''Pre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition LoadElf2Mem''Pre : fpre :=
  fun vl ll ct => mkfunasrt (LoadElf2Mem''PreGood vl ll ct).

(* post *)
Definition LoadElf2Mem''Post' (vl:vallist) (v:option val) (logicl:list logicvar) ct:= 
   EX file (ehdrvl:vallist)   eentry s er,
   <||s||> ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop ** Aier er **
   [| vl = (Vptr file)::nil|] **
    [| V_e_entry ehdrvl = Some (Vptr eentry)|] **
     [| struct_type_vallist_match Elf32_Ehdr ehdrvl |] **
    [| logicl = logic_lv ehdrvl :: logic_code s :: nil |] **
    Astruct file Elf32_Ehdr ehdrvl ** 
    [| v=Some (Vptr eentry) |] **
     p_local OSLInv ct init_lg.
  
Theorem LoadElf2Mem''PostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (LoadElf2Mem''Post' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition LoadElf2Mem''Post : fpost :=
  fun vl v ll ct => mkfunasrt (LoadElf2Mem''PostGood vl v ll ct).
  
Definition LoadElf2Mem''_spec: fspec:= (LoadElf2Mem''Pre, LoadElf2Mem''Post, (Tptr Tvoid, (Tptr Tvoid)::nil)).

(* pthread_attr_init  *)
(* lack of PrioTbl and Username *)
Definition PthreadInitPre' (vl:vallist) (logicl:list logicvar) ct :=
  EX s er attr pattr_vl ,
    Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop ** Aier er **
      [| logicl = logic_code s :: nil |] **
      <|| s ||> **
     Astruct attr pthread_attr_t pattr_vl **
    [| struct_type_vallist_match pthread_attr_t pattr_vl |] **
    [| nth_val 0 vl = Some (Vptr attr) |] **
      p_local OSLInv ct init_lg.

Theorem PthreadInitPreGood (vl:vallist) ll ct:
  GoodFunAsrt (PthreadInitPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition PthreadInitPre : fpre :=
  fun vl ll ct => mkfunasrt (PthreadInitPreGood vl ll ct).

Definition PthreadInitPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s er attr pattr_vl' opv prio,
    Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop ** Aier er **
      [| logicl = logic_code s :: nil |] **
      <|| s ||> **
     Astruct attr pthread_attr_t pattr_vl' **
    [| struct_type_vallist_match pthread_attr_t pattr_vl' |] **
    [| nth_val 0 vl = Some (Vptr attr) |] **
    [| v = Some (Vint32 opv) /\ (opv = Int.repr EINVAL \/ opv = Int.zero)|] **
    [| nth_val 2 pattr_vl' = Some (Vint32 prio) |] **
    [| (prio = Int.repr OS_MAX_TASKS /\ opv = Int.repr EINVAL) \/
        (prio <> Int.repr OS_MAX_TASKS /\ opv = Int.zero) |] **
      p_local OSLInv ct init_lg.

Theorem PthreadInitPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (PthreadInitPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition PthreadInitPost : fpost :=
  fun vl v ll ct => mkfunasrt (PthreadInitPostGood vl v ll ct).

Definition PthreadInit_spec : fspec :=
    (PthreadInitPre,PthreadInitPost,(Tint32, Tptr pthread_attr_t :: nil)).

(*  internal function version of pthread_create *)

Definition PthreadCreatePre' (vl:vallist) (logicl:list logicvar) ct :=
  EX s er,
    (Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop ** Aier er **
      [| logicl = logic_code s :: nil |] **
      <|| s ||> **
      (EX ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp ecbls tcbls vhold ptfree lfree ptls pattrb scapl mcapl qcapl,
                   AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold ** 
                   AOSTCBList' p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls ptfree **
                   AOSTCBFreeList' ptfree lfree ct tcbls**
                   AOSRdyTblGrp rtbl rgrp **
                   HTCBList tcbls ** HCurTCB ct **
                   APthreadAttr pattrb **
                   EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
                   [| RH_TCBList_ECBList_P ecbls tcbls ct|]) **
      p_local OSLInv ct init_lg).

Theorem PthreadCreatePreGood (vl:vallist) ll ct:
  GoodFunAsrt (PthreadCreatePre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
  simpl; intros.  apply GoodFunAsrt_err_sllseg.
  simpl; intros.  apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition PthreadCreatePre : fpre :=
  fun vl ll ct => mkfunasrt (PthreadCreatePreGood vl ll ct).

Definition PthreadCreatePost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s rv er k,
    (Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop ** Aier er **
      [| logicl = logic_code s :: nil |] **
      [| v = Some rv /\ rv = Vint32 k  /\ 
          Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k) (Int.max_unsigned) |] **
      [| nth_val' 0 vl = Vnull -> k = (Int.repr EINVAL) |] **
      <|| s ||> **
      (EX ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp ecbls tcbls vhold ptfree lfree ptls pattrb scapl mcapl qcapl,
                   AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold ** 
                   AOSTCBList' p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls ptfree **
                   AOSTCBFreeList' ptfree lfree ct tcbls**
                   AOSRdyTblGrp rtbl rgrp **
                   HTCBList tcbls ** HCurTCB ct **
                   APthreadAttr pattrb **
                   EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
                   [| RH_TCBList_ECBList_P ecbls tcbls ct|]) **
      p_local OSLInv ct init_lg).

Theorem PthreadCreatePostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (PthreadCreatePost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
  simpl; intros.  apply GoodFunAsrt_err_sllseg.
  simpl; intros.  apply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition PthreadCreatePost : fpost :=
  fun vl v ll ct => mkfunasrt (PthreadCreatePostGood vl v ll ct).

Definition PthreadCreate_spec : fspec :=
    (PthreadCreatePre,PthreadCreatePost,(Tint32, Tptr Tint32 :: Tptr pthread_attr_t :: Tptr Void :: Tptr Void :: nil)).

Definition get_cpu_ksdom_binaddr ksdomscdlen (dscd_vll :list dscheduleConfVal)
                                                                        (dom_vll :list domainConfVal) baddr_vl :=
(forall j, 0 <= j < (Int.unsigned ksdomscdlen) ->
               exists dscd_vl kscd_dom dom_vl prdytbl deviotbl capentbl v,
               nth_vallist (Z.to_nat j) dscd_vll = Some dscd_vl /\
               V_DSdomain dscd_vl = Some (Vint32 kscd_dom) /\
               nth_error dom_vll (Z.to_nat (Int.unsigned kscd_dom)) = Some (dom_vl, prdytbl, deviotbl, capentbl) /\
               V_binAddress dom_vl = Some (Vint32 v) /\
               nth_val (Z.to_nat j) baddr_vl = Some (Vint32 v)) /\
(length baddr_vl = Z.to_nat (Int.unsigned ksdomscdlen))%nat.

Definition cast_int_vl_to_ptr baddr_vl addr_vl :=
(forall i v,
   nth_val i baddr_vl = Some (Vint32 v) ->
   nth_val i addr_vl = Some (Vptr (int32_to_ptr v))) /\
length baddr_vl = length addr_vl.

Fixpoint Avalid addr_vl ehdrvll :=
match (addr_vl, ehdrvll) with
| (nil, nil) => Aemp
| ((Vptr adr) :: addr_vl', ehdrvl :: ehdrvll') =>
        Astruct adr Elf32_Ehdr ehdrvl ** [| struct_type_vallist_match Elf32_Ehdr ehdrvl |] **
       Avalid addr_vl' ehdrvll'
| _ => Afalse
end.

Lemma GoodFunAsrt_Avalid:
  forall addr_vl ehdrvll, GoodFunAsrt (Avalid addr_vl ehdrvll).
Proof.
  induction addr_vl; induction ehdrvll; try GoodFunAsrt_solver.
  destruct a; simpl;  GoodFunAsrt_solver.
  destruct a; unfold Avalid in *; fold Avalid in *; GoodFunAsrt_solver.
Qed.

Definition InitCorePartitionPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX s er ucosf absucos rtsk_vll absrtsk attr pattr_vl cnum ucos_vl intrdom areac cpuc channelc portc svl
        cpu_vl drtbl_vl dscd_vll dom_vll ksdomscdlen baddr_vl addr_vl ehdrvll
        b i ptrvl priotbl cspacels,
    Aisr empisr ** Aie false ** Ais nil ** Acs (true::nil) ** Aier er ** A_isr_is_prop **
    <|| s ||> **
    AucosConf ucosf absucos **
    ARootTaskStk rtsk_vll absrtsk **
    Astruct attr pthread_attr_t pattr_vl **
   [|struct_type_vallist_match pthread_attr_t pattr_vl|] **
   [| vl = (Vint32 cnum :: Vptr attr :: nil) |] **
   [| Int.unsigned cnum < CORENUM |] **
   [| ucosf = (ucos_vl, intrdom, areac, cpuc, channelc, portc, svl) |] **
   (* condition about is_ELFProgramValidPre' and LoadElf2Mem''Pre' *)
   (* get `conf->cpus[coreNum]` *)
   [| nth_error cpuc (Z.to_nat (Int.unsigned cnum)) = Some (cpu_vl, drtbl_vl, dscd_vll, dom_vll) |] **
   (* get `conf->cpus[coreNum].ksDomScheduleLength` *)
   [| V_CPUksDomScheduleLength cpu_vl = Some (Vint32 ksdomscdlen) |] **
   (* get all `conf->cpus[coreNum].ksDomains[i].binAddress` in the loop,
                    where i = conf->cpus[coreNum].ksDomSchedule[id].domain *)
   [| get_cpu_ksdom_binaddr ksdomscdlen dscd_vll dom_vll baddr_vl |] **
   (* convert the type of  `conf->cpus[coreNum].ksDomains[i].binAddress` form Tint32 to Tvoid * *)
   [| cast_int_vl_to_ptr baddr_vl addr_vl |] **
   Avalid addr_vl ehdrvll **
   [| forall i ehdrvl, nth_vallist i ehdrvll = Some ehdrvl ->
                                    exists eentry, V_e_entry ehdrvl = Some (Vptr eentry) |] **
    (* condition about PthreadCreatePre' *)
    (EX ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp ecbls tcbls vhold ptfree lfree ptls pattrb scapl mcapl qcapl,
                   AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold ** 
                   AOSTCBList' p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls ptfree **
                   AOSTCBFreeList' ptfree lfree ct tcbls**
                   AOSRdyTblGrp rtbl rgrp **
                   HTCBList tcbls ** HCurTCB ct **
                   APthreadAttr pattrb **
                   EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
                   [| RH_TCBList_ECBList_P ecbls tcbls ct|]) **
   (* condition about ucos_CNode_DeletePre' *)
    AOSCSpacePrioTbl (b, i) ptrvl priotbl cspacels** 
    [|CSPACEList_P ptrvl 0 cspacels|] **
    [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] **
    [| logicl = (* logic_code s :: *) nil |] **
    p_local OSLInv ct init_lg.

Local Ltac GoodFunAsrt_solver' :=
  repeat
   (split; try apply GoodFunAsrt_Aarray;
     try apply GoodFunAsrt_Astruct;
     try apply GoodFunAsrt_AEventData;
     try apply GoodFunAsrt_evsllseg;
     try apply GoodFunAsrt_tcbdllseg; try apply GoodFunAsrt_dllseg;
     try apply GoodFunAsrt_ecbf_sll; try apply GoodFunAsrt_sll;
     try apply GoodFunAsrt_qblkf_sll;
     try apply GoodFunAsrt_invlth_isr';
     try apply GoodFunAsrt_tcbdllflag;
     try apply GoodFunAsrt_sllfreeflag;
     try apply GoodFunAsrt_Aarray_new; 
     try apply GoodFunAsrt_pos_sllseg; 
     try apply GoodFunAsrt_err_sllseg; 
     try apply GoodFunAsrt_AEvAtomHeap; 
     try apply GoodFunAsrt_AEvStructHeap; 
     try apply GoodFunAsrt_AEvArrayHeap; 
     try apply GoodFunAsrt_llsegevaux;
     try apply GoodFunAsrt_AucosConf;
     try apply GoodFunAsrt_AKsDomains';
     try apply GoodFunAsrt_AOScoreheape;
     try apply GoodFunAsrt_AOScoreheapl;
     try apply GoodFunAsrt_AOScoreheapt;
     try apply GoodFunAsrt_AOSIPCMem_aux;
     try apply GoodFunAsrt_Adynheap;
     try simple apply GoodFunAsrt_AOSPortAttrTbl';
     try (simple apply GoodFunAsrt_AOSCSpacePrioTbl);
     auto).

Theorem InitCorePartitionPreGood (vl:vallist) ll ct:
  GoodFunAsrt (InitCorePartitionPre' vl ll ct).
Proof.
  GoodFunAsrt_solver'.
  eapply GoodFunAsrt_Avalid.
  simpl; intros.  eapply GoodFunAsrt_err_sllseg.
  simpl; intros.  eapply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition InitCorePartitionPre : fpre :=
  fun vl ll ct => mkfunasrt (InitCorePartitionPreGood vl ll ct).

Definition InitCorePartitionPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct := 
  EX s er ucosf absucos rtsk_vll absrtsk attr pattr_vl cnum ucos_vl intrdom areac cpuc channelc portc svl
        cpu_vl drtbl_vl dscd_vll dom_vll ksdomscdlen baddr_vl addr_vl ehdrvll 
        b i ptrvl priotbl'' cspacels,
    Aisr empisr ** Aie false ** Ais nil ** Acs (true::nil) ** Aier er ** A_isr_is_prop **
    <|| s ||> **
    AucosConf ucosf absucos **
    ARootTaskStk rtsk_vll absrtsk **
    Astruct attr pthread_attr_t pattr_vl **
   [|struct_type_vallist_match pthread_attr_t pattr_vl|] **
   [| vl = (Vint32 cnum :: Vptr attr :: nil) |] **
   [| Int.unsigned cnum < CORENUM |] **
   [| ucosf = (ucos_vl, intrdom, areac, cpuc, channelc, portc, svl) |] **
   (* condition about is_ELFProgramValidPre' and LoadElf2Mem''Pre' *)
   (* get `conf->cpus[coreNum]` *)
   [| nth_error cpuc (Z.to_nat (Int.unsigned cnum)) = Some (cpu_vl, drtbl_vl, dscd_vll, dom_vll) |] **
   (* get `conf->cpus[coreNum].ksDomScheduleLength` *)
   [| V_CPUksDomScheduleLength cpu_vl = Some (Vint32 ksdomscdlen) |] **
   (* get all `conf->cpus[coreNum].ksDomains[i].binAddress` in the loop,
                    where i = conf->cpus[coreNum].ksDomSchedule[id].domain *)
   [| get_cpu_ksdom_binaddr ksdomscdlen dscd_vll dom_vll baddr_vl |] **
   (* convert the type of  `conf->cpus[coreNum].ksDomains[i].binAddress` form Tint32 to Tvoid * *)
   [| cast_int_vl_to_ptr baddr_vl addr_vl |] **
   Avalid addr_vl ehdrvll **
   [| forall i ehdrvl, nth_vallist i ehdrvll = Some ehdrvl ->
                                    exists eentry, V_e_entry ehdrvl = Some (Vptr eentry) |] **
    (* condition about PthreadCreatePre' *)
    (EX ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp ecbls tcbls vhold ptfree lfree ptls pattrb scapl mcapl qcapl,
                   AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold ** 
                   AOSTCBList' p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls ptfree **
                   AOSTCBFreeList' ptfree lfree ct tcbls**
                   AOSRdyTblGrp rtbl rgrp **
                   HTCBList tcbls ** HCurTCB ct **
                   APthreadAttr pattrb **
                   EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
                   [| RH_TCBList_ECBList_P ecbls tcbls ct|]) **
   (* condition about ucos_CNode_DeletePre' *)
    AOSCSpacePrioTbl (b, i) ptrvl priotbl'' cspacels** 
    [|CSPACEList_P ptrvl 0 cspacels|] **
    [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] **
    [| logicl = (* logic_code s :: *) nil |] **
    p_local OSLInv ct init_lg.

Theorem InitCorePartitionPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (InitCorePartitionPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver'.
  eapply GoodFunAsrt_Avalid.
  simpl; intros.  eapply GoodFunAsrt_err_sllseg.
  simpl; intros.  eapply GoodFunAsrt_pos_sllseg.
  apply GoodFunAsrt_ASemCap.
  apply GoodFunAsrt_AMuxCap.
  apply GoodFunAsrt_AMqCap.
Qed.

Definition InitCorePartitionPost : fpost :=
  fun vl v ll ct => mkfunasrt (InitCorePartitionPostGood vl v ll ct).

Definition InitCorePartition_spec : fspec := (InitCorePartitionPre, InitCorePartitionPost, (Tvoid, Tint32 :: Tptr pthread_attr_t :: nil)).

(* ------------------------- end add spec by CNU ------------------ *)

Definition osq_spec_list := 
  (* (OS_EventSearch, OS_EventSearch_spec) :: *)
  (OS_EventRemove, OS_EventRemove_spec) ::
  (OS_EventRemoveDel, OS_EventRemoveDel_spec) ::
  (OS_EventTO, OS_EventTO_spec) :: 
  (OS_EventPostTO, OS_EventPostTO_spec) ::
  (OS_EventTaskRdy,  OS_EventTaskRdy_spec) ::
  (OS_EventTaskPostRdy, OS_EventTaskPostRdy_spec) :: 
  (OS_EventTaskPostRdyDel, OS_EventTaskPostRdy_qdel_spec) :: 
  (OS_EventTaskWait, OS_EventTaskWait_spec) ::
  (OS_EventTaskPostWait, OS_EventTaskPostWait_spec) :: 
  (getFreePos, getFreePos_spec) ::
  (pthread_mutexattr_init, MutexAttrInit_spec) ::
  (memcpy4, Memcpy_spec) ::
  (OS_Sched,  OS_Sched_spec) ::
  (OS_IPCSched,  OS_IPCSched_spec) ::
  (OSIntExit, OSIntExit_spec) ::
  (OSTimeTick, OSTimeTick_spec)::
  (OS_EventWaitListInit,OS_EventWaitListInit_spec) ::
  (OS_TCBInit, OS_TCBInit_spec) ::
  (OS_IsSomeMutexOwner, OS_IsSomeMutexOwner_spec) ::
  (Interrupt_Init, Interrupt_Init_spec) ::
  (UserAddrCheck_6678, UserAddrCheck6678_spec) ::
  (UserAddrCheck_6713, UserAddrCheck6713_spec) ::
  (OSIntEnter, OSIntEnter_spec) :: 
  (OSIntExit, OSIntExit_spec) :: 
  (EXC_HANDLER, EXC_HANDLER_spec) :: 
  (OSTaskSuspend, OSTaskSuspend_spec) ::
  (fnull, fnull_spec) :: 
  (* (OSIpc, OSIpc_spec) :: *)
  (OSTimeTick, OSTimeTick_spec) ::
  (UserAddrCheck, UserAddrCheckEvt_spec) :: 
  (UserAddrCheckCrit, UserAddrCheckCrit_spec) :: 
  (OSSemAccept, OSSemAccept_spec) ::
  (OSSemCreate, OSSemCreate_spec) :: 
  (OSSemDel, OSSemDel_spec) :: 
  (OSSemPend, OSSemPend_spec) :: 
  (OSSemPost, OSSemPost_spec) :: 
  (OSSemPostBin, OSSemPostBin_spec) ::
  (OSIPCSemPost, OSIPCSemPost_spec) :: 
  (OSMutexAccept, OSMutexAccept_spec) :: 
  (OSMutexCreate, OSMutexCreate_spec) :: 
  (OSMutexDel, OSMutexDel_spec) :: 
  (OSMutexPend, OSMutexPend_spec) :: 
  (OSMutexPost, OSMutexPost_spec) ::
  (OSQAccept, OSQAccept_spec) :: 
  (OSQCreate, OSQCreate_spec) ::
  (OSQDel, OSQDel_spec) ::
  (OSQPend, OSQPend_spec) ::
  (OSQPost, OSQPost_spec) ::
  (OSIPCQPost, OSIPCQPost_spec) ::
  (OSQTimedPost, OSQTimedPost_spec) :: 
  (OSQQuery, OSQQuery_spec) :: 
  (compute_period,OS_compute_period_spec)::
  (OStimer_Init,OS_timerInit_spec)::
  (OSreset_timer,OS_resettimer_spec)::
  (OStimer_Config,OS_timerConfig_spec) ::
  (OStimer_outConfig,OS_timerOutConfig_spec) ::
  (OSint_install_handler_timer, OSint_install_handler_timer_spec) ::
  (memcpy, OS_memcpy_spec) ::
  (OS_getCoreIPC, OS_getCoreIPC_spec) ::
  (OSIpc, OS_Ipc_spec) :: 
  (OSIpc1, OSIpc1_spec) :: 
  (memcpy1, OS_memcpy1_spec) ::
  (memcpy2, OS_memcpy2_spec) ::
  (memcpy3, OS_memcpy3_spec) ::
  (memcpy5, OS_memcpy5_spec) ::
  (memset, OS_memset_spec) ::
  (malloc_Elf32_Ehdr, malloc_Elf32_Ehdr_spec)::
  (malloc_Elf32_Phdr, malloc_Elf32_Phdr_spec)::
  (free_Elf32_Ehdr, free_Elf32_Ehdr_spec)::
  (free_Elf32_Ehdr, free_Elf32_Ehdr_spec)::
  (LoadElf2Mem, LoadElf2Mem_spec)::
  (LoadElf2Mem', LoadElf2Mem'_spec)::
  (OSTaskDel, OSTaskDel_spec)::
  (doRefactorISR, doRefactorISR_spec)::
  (OSSampleSendToDomain, OSSampleSendToDomain_spec) ::
  (OS_PortTaskRdy, OS_PortTaskRdy_spec) ::
  (OSQSendToDomain, OSQSendToDomain_spec) ::
  (OSPortAcceptWithoutCheck, OSPortAcceptWithoutCheck_spec) ::
  (OSPortAcceptWithoutCheck2, OSPortAcceptWithoutCheck2_spec) ::
  (OSChannelCreate, OSChannelCreate_spec) ::
  (channleCreateCheck, channleCreateCheck_spec) ::
  (OSPortAddToChannel, OSPortAddToChannel_spec) ::
  (portBindCheck, portBindCheck_spec) ::
  (OSKernelPortCreate, OSKernelPortCreate_spec) ::
  (SamplePortCreate, SamplePortCreate_spec) ::
  (portCreateCheck, portCreateCheck_spec) ::
  (QPortCreate, QPortCreate_spec) ::
  (partitionSysInit, partitionSysInit_spec) ::
  (nextDomain, nextDomain_spec) ::
  (switchDomain, switchDomain_spec) ::
  (switchDomain', switchDomain_no_sup_spec) ::
  (initDefaultMPAX, initDefaultMPAX_spec) :: 
  (initMPAX, initMPAX_spec) ::
  (is_bigEndian, is_bigEndian_spec) ::
  (InitDNUM, initDnum_spec) ::
  (initConf, initConf_spec) ::
  (IntPartitionMuxInit, IntPartitionMuxInit_spec) ::
  (InitCorePartition, InitCorePartition_spec) ::
  (is_ELFProgramValid, is_ELFProgramValid_spec) ::
  (LoadElf2Mem'', LoadElf2Mem''_spec) :: 
  (pthread_attr_init, PthreadInit_spec) :: 
  (pthread_create, PthreadCreate_spec) :: 
  nil.

Fixpoint convert_spec  (ls : list (fid * fspec)) : fid -> option fspec :=
   match ls with
   | nil => fun _ => None
   | (id,spec) :: ls' => 
     fun (id' : fid) =>  
       if Zeq_bool id id' then 
         Some spec else convert_spec ls' id'
   end.

Definition OS_spec :=  convert_spec osq_spec_list.

Close Scope list_scope.

Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import ios_cap_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import abs_op.
Require Import thread_resume.

Definition threadresume_curnull
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists thread v',
      vl = thread :: v' /\
      opv = (Some (Vint32 (Int.repr ESRCH))) /\
      O_opt = Some O1 
  end.

Definition threadresume_prio_invalid
(vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
| (opv, O_opt) =>
    exists thread v',
    vl = thread :: v' /\
    opv = (Some (Vint32 (Int.repr ESRCH))) /\
    O_opt = Some O1 
end.

Definition threadresume_tcbnullorplaceholder
(vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
| (opv, O_opt) =>
    exists thread v',
    vl = thread :: v' /\
    opv = (Some (Vint32 (Int.repr ESRCH))) /\
    O_opt = Some O1 
end.

Definition threadresume_sta_rdy
(vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
| (opv, O_opt) =>
    exists thread v',
    vl = thread ::v' /\
    opv = (Some (Vint32 (Int.repr EINVAL))) /\
    O_opt = Some O1 
end.

Definition threadresume_curpspace_null (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      (O2 = Some O1 /\ opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE))) 
        
end. 

Definition threadresume_nocapability (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      (O2 = Some O1 /\ opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE))) 
        
end. 

Definition threadresume_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
  exists rv,
     vl = (rv :: nil) /\
      (O2 = Some O1 /\ opv = Some (Vint32 (Int.repr 0))) 
        
end. 

Require Import ifun_taskres_spec.
Definition Int32toInt8 v:=
  match v with
  |Vint32 i => Vint32
  (Int.modu i (Int.repr Byte.modulus))
  | _ => Vint32 (Int.repr 0)
  end.
Definition threadresume (vl: vallist) :=
  match vl with
  (thread :: vl') => 
  threadresume_curnull  (|thread :: nil|) ??
  threadresume_prio_invalid (|thread :: nil|) ??
  threadresume_tcbnullorplaceholder(|thread :: nil|) ??
  threadresume_sta_rdy (|thread :: nil|) ??
  threadresume_curpspace_null (|thread :: nil|) ??
  threadresume_nocapability (|thread :: nil|) ??
  spec_code_cons (taskresumecode (Int32toInt8(thread)::Vint32 (Int.repr 0)::nil))
    (threadresume_succ (|Vint32(Int.repr 0) :: nil|))
  | _ => spec_abort
  end.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope int_scope.
Open Scope code_scope.
Set Nested Proofs Allowed.
Set Keyed Unification.
Require Import ucos_frmaop.
Require Import abs_step.
Lemma threadresume_absimp_curnull:
forall sch thread P,
  can_change_aop P ->
  absinfer sch 
            (<|| threadresume (thread ::nil) ||>  ** P)
            (<|| END (Some (Vint32 (Int.repr ESRCH))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma threadresume_absimp_prio_invalid:
  forall sch thread  P,
    can_change_aop P ->
    absinfer sch 
             (<|| threadresume (thread ::nil) ||>  ** P)
             (<|| END (Some (Vint32 (Int.repr ESRCH))) ||> ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma threadresume_absimp_tcbnullorplaceholder:
  forall sch thread vl' P,
    can_change_aop P ->
    absinfer sch 
             (<|| threadresume (thread ::vl') ||>  ** P)
             (<|| END (Some (Vint32 (Int.repr ESRCH))) ||> ** P).
Proof.
  infer_solver 2%nat.
Qed.

Lemma threadresume_absimp_sta_rdy:
  forall sch thread vl' P,
    can_change_aop P ->
    absinfer sch 
             (<|| threadresume (thread ::vl') ||>  ** P)
             (<|| END (Some (Vint32 (Int.repr EINVAL)) )||> ** P).
Proof.
  infer_solver 3%nat.
Qed.

Lemma threadresume_absimp_curpspace_null:
  forall sch thread vl' P,
    can_change_aop P ->
    absinfer sch 
             (<|| threadresume (thread ::vl') ||>  ** P)
             (<|| END (Some (Vint32 (Int.repr USER_CAPABILITY_NONE))) ||> ** P).
Proof.
  infer_solver 4%nat.
Qed.

Lemma threadresume_absimp_nocapability:
  forall sch thread P vl',
    can_change_aop P ->
    absinfer sch 
             (<|| threadresume (thread ::vl') ||>  ** P)
             (<|| END (Some (Vint32 (Int.repr USER_CAPABILITY_NONE))) ||> ** P).
Proof.
  infer_solver 5%nat.
Qed.

Lemma threadresume_absimp_succ:
  forall sch v'  P,
    can_change_aop P ->
    absinfer sch 
            (<|| threadresume_succ (|v' ::nil|) ||>  ** P)
            (<|| END (Some (Vint32 (Int.repr 0))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.
Definition pthreadresumeapi :=
  (threadresume, (Tint8, Tint32 :: nil)).
Require Import os_spec.
Definition new_api_spec_list :=
  ((pthread_resume, pthreadresumeapi) :: nil) ++ api_spec_list.

Definition new_api_spec :=
  convert_api_spec new_api_spec_list.

Definition new_os_spec := (new_api_spec, GetHPrio).

Require Import ifun_spec.
Local Open Scope list_scope.

Definition os_spec_list_ext :=
  (((OSTaskResume, OSTaskResume_spec) ::nil) ++ new_osq_spec_list).

Require Import abs_infer_step.
Require Import ucos_frmaop.
  
Definition api_fun_list_new := (pthread_resume_impl :: nil)%list.
Definition os_api_new := convert_cfuns api_fun_list_new.


Require Import hoare_tactics.
Require Import pure_auto.
Require Import ucos_pauto.
Require Import sep_auto.
Require Import seplog_tactics.
Require Import seplog_lemmas.
Require Import sep_cancel_ext.
Require Import derived_rules.
Require Import hoare_conseq.
Require Import ucos_forward.
Require Import math_auto.

Require Import sem_lab.
Require Import symbolic_lemmas.
Require Import sem_common.
Require Import Lia.
Require Import CapPure.
Require Import seplog_trm_tacs.
Lemma PthreadresumeProof:
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api_new pthread_resume pthreadresumeapi vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api_new pthread_resume pthreadresumeapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api_new pthread_resume = Some (t, d1, d2, s) /\
      {|new_OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}. 
Proof.
  init spec. 
  hoare_lifts_trms_pre(Aop).
  hoare forward prim;pure_auto.
  hoare_split_pure_all.

  try unfold OSInv; try unfold AOSTCBList;unfold_dll.
  pure intro.

  hoare forward.
  go.

  unfold AOSTCBPrioTbl.
  unfold AGVars.
  hoare_split_pure_all.

  assert(Hi4range: Int.unsigned i4 < 64).
  unfold TCBList_P in H8.
  simpljoin.
  unfold TCBNode_P in H27.
  destruct x2, p, p. simpljoin.
  simpl in H29. inverts H29.
  unfolds in H30.
  simpljoin.
  simpl in H29. inverts H29.
  auto.
  assert(Hi4true: Int.unsigned i4 <=? Byte.max_unsigned= true).
  
  change Byte.max_unsigned with 255.
  int auto.
  assert(Hv'4len: length v'4 = 64%nat).
  simpljoin. auto.
  assert(Hv'4match: array_type_vallist_match OS_TCB ∗ v'4).
  simpljoin. auto.
  assert(Hi4match:rule_type_val_match OS_TCB ∗
  (nth_val' (Z.to_nat (Int.unsigned i4)) v'4) =
true).
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hv'4len. lia.
  hoare forward; auto.
  rewrite Hi4true. auto.
  unfold val_inj, val_eq.
  clear -Hi4match.
  unfolds in Hi4match.
  destruct (nth_val'
  (Z.to_nat (Int.unsigned i4))
  v'4); tryfalse; auto.
  destruct a. auto.

  clear -Hi4match.
  unfolds in Hi4match.
  destruct (nth_val'
  (Z.to_nat (Int.unsigned i4))
  v'4); tryfalse; auto.
  destruct a. auto.
  clear -Hi4match.
  unfolds in Hi4match.
  destruct (nth_val'
  (Z.to_nat (Int.unsigned i4))
  v'4); tryfalse; auto.
  destruct a. auto.

  hoare_split_pure_all.
  eapply seq_rule.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros.
  unfold OldOSInvWL.
  sep cancel Aier.
  sep cancel Aisr. sep cancel Aie. sep cancel Ais.
  sep cancel Acs.
  instantiate(1:=
  LV pCSpace @ CSPACE ∗ |-> v'2 **
  LV ptcb @ OS_TCB ∗ |-> v'1 **
  LV thread @ long |-> Vint32 i **
  LV y @ char_t |-> Vint32 i4 ** 
  A_dom_lenv
  ((thread, long) :: (y, char_t) :: (ptcb, OS_TCB ∗):: (pCSpace, CSPACE ∗) :: nil)).
  sep auto; eauto.
  splits; go.
  go. 
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  go.
  eapply threadresume_absimp_curnull; eauto.
  go.
  hoare forward.

  eapply disj_rule.
  hoare_split_pure_all. eapply pfalse_rule.
  hoare_split_pure_all.
  clear H24.
  hoare forward.
  destruct (Int.eq i ($ OS_IDLE_PRIO)); auto.
  destruct (Int.ltu ($ ios_cap_defs.OS_LOWEST_PRIO)
  i); auto.
  destruct (Int.eq i ($ ios_cap_defs.OS_LOWEST_PRIO)); auto.
  destruct (Int.ltu
  ($ ios_cap_defs.OS_LOWEST_PRIO)
  i);
  destruct (Int.eq i
  ($ ios_cap_defs.OS_LOWEST_PRIO)); auto.
  destruct (Int.eq i ($ OS_IDLE_PRIO));
  destruct (Int.ltu($ ios_cap_defs.OS_LOWEST_PRIO) i);
  destruct (Int.eq i($ ios_cap_defs.OS_LOWEST_PRIO));
  auto.
  hoare_split_pure_all.

  hoare_split_pure_all.
  eapply seq_rule.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros.
  unfold OldOSInvWL.
  sep cancel Aier.
  sep cancel Aisr. sep cancel Aie. sep cancel Ais.
  sep cancel Acs.
  instantiate(1:=
  LV pCSpace @ CSPACE ∗ |-> v'2 **
  LV ptcb @ OS_TCB ∗ |-> v'1 **
  LV thread @ long |-> Vint32 i **
  LV y @ char_t |-> Vint32 i4 ** 
  A_dom_lenv
  ((thread, long) :: (y, char_t) :: (ptcb, OS_TCB ∗):: (pCSpace, CSPACE ∗) :: nil)).
  sep auto; eauto.
  splits; go.
  go. 
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  go.
  eapply threadresume_absimp_prio_invalid; eauto.
  go.
  hoare forward.
  eapply disj_rule; hoare_split_pure_all.
  eapply pfalse_rule.
  assert(Hirange: Int.unsigned i < 63).
  destruct (Int.eq i ($ OS_IDLE_PRIO)) eqn:Hieq;
  destruct (Int.ltu($ ios_cap_defs.OS_LOWEST_PRIO)
  i) eqn: Hiltu;
  destruct (Int.eq i ($ ios_cap_defs.OS_LOWEST_PRIO)) eqn: Heq2;
  val_help_H H24; simpl in H24;destruct H24; tryfalse.
  unfold ios_cap_defs.OS_LOWEST_PRIO in *.
  rewrite Intlt_false_is_Zge in Hiltu.
  rewrite Inteq_false_is_Zneq in Heq2.
  clear -Hiltu Heq2.
  int auto.
  assert(Himatch: rule_type_val_match OS_TCB ∗
  (nth_val' (Z.to_nat (Int.unsigned i)) v'4) =
true).
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hv'4len. lia.
  hoare forward; auto.
  
  hoare forward.
  unfold val_inj, val_eq.
  clear -Himatch.
  simpl in Himatch.
  destruct (nth_val' (Z.to_nat (Int.unsigned i)) v'4); tryfalse; auto.
  destruct a. auto.
  hoare_split_pure_all.
  eapply seq_rule.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros.
  unfold OldOSInvWL.
  sep cancel Aier.
  sep cancel Aisr. sep cancel Aie. sep cancel Ais.
  sep cancel Acs.
  instantiate(1:=
  LV pCSpace @ CSPACE ∗ |-> v'2 **
  LV ptcb @ OS_TCB ∗ |->  nth_val'
  (Z.to_nat (Int.unsigned i))
  v'4 **
  LV thread @ long |-> Vint32 i **
  LV y @ char_t |-> Vint32 i4 ** 
  A_dom_lenv
  ((thread, long) :: (y, char_t) :: (ptcb, OS_TCB ∗):: (pCSpace, CSPACE ∗) :: nil)).
  sep auto; eauto.
  splits; go.
  go. 
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  go.
  eapply threadresume_absimp_tcbnullorplaceholder; eauto.
  go.
  hoare forward.
  eapply disj_rule; hoare_split_pure_all.
  eapply pfalse_rule.

  eapply seq_rule.
  eapply ift_rule''.
  intros.
  eapply bop_rv.
  sep_get_rv.
  eapply addrof_gvar_rv.
  Require Import inline_tactics.
  gen_notin_lenv H26 OSPlaceHolder.
  eapply dom_lenv_imp_notin_lenv.
  eauto.
  sep cancel A_dom_lenv.
  sep cancel Agvarenv'.
  eauto.
  eauto.
  simpl.
  destruct x. destruct vhold_addr.
  unfold val_inj, val_eq.
  clear -Himatch.
  simpl in Himatch.
  destruct (nth_val' (Z.to_nat (Int.unsigned i)) v'4); tryfalse; auto.
  destruct v'15. auto.
  destruct a. destruct v'15.
  destruct (peq b b0); destruct (Int.eq i0 i1); auto.
  unfold val_inj, val_eq.
  clear -Himatch.
  simpl in Himatch.
  destruct (nth_val' (Z.to_nat (Int.unsigned i)) v'4); tryfalse; auto.
  destruct v'15. auto.
  destruct a. destruct v'15.
  destruct (peq b b0); destruct (Int.eq i0 i1); auto.
  clear -Himatch.
  simpl in Himatch.
  unfold val_inj, val_eq.
  destruct (nth_val' (Z.to_nat (Int.unsigned i)) v'4); tryfalse; auto.
  destruct v'15. auto.
  destruct a. destruct v'15.
  destruct (peq b b0); destruct (Int.eq i0 i1); auto.
  simpl. eauto.

  hoare_split_pure_all.
  eapply seq_rule.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros.
  unfold OldOSInvWL.
  sep cancel Aier.
  sep cancel Aisr. sep cancel Aie. sep cancel Ais.
  sep cancel Acs.
  instantiate(1:=
  LV pCSpace @ CSPACE ∗ |-> v'2 **
  LV ptcb @ OS_TCB ∗ |->  nth_val'
  (Z.to_nat (Int.unsigned i))
  v'4 **
  LV thread @ long |-> Vint32 i **
  LV y @ char_t |-> Vint32 i4 ** 
  A_dom_lenv
  ((thread, long) :: (y, char_t) :: (ptcb, OS_TCB ∗):: (pCSpace, CSPACE ∗) :: nil)).
  sep auto; eauto.
  splits; go.
  go. 
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  go.
  eapply threadresume_absimp_tcbnullorplaceholder; eauto.
  go.
  hoare forward.
  eapply disj_rule; hoare_split_pure_all.
  eapply pfalse_rule.


  assert(Hinotnull: nth_val'(Z.to_nat (Int.unsigned i))
  v'4 <> Vnull).
  clear -Himatch H25.
  simpl in Himatch.
  destruct (nth_val'
  (Z.to_nat (Int.unsigned i))
  v'4); tryfalse. auto.
  unfold val_inj, val_eq in H25.
  destruct H25; tryfalse.
  auto.
  assert(Hiexists: exists p,  nth_val'(Z.to_nat (Int.unsigned i))
  v'4 = Vptr p).
  simpl in Himatch.
  destruct (nth_val'(Z.to_nat (Int.unsigned i))
  v'4); tryfalse; auto. eauto.
  rename H26 into Hif.
  destruct Hiexists.
  rewrite H26 in Hif.
  assert(Hxneqv'15 : x <> v'15).
  clear -Hif.
  unfold val_inj, bop_eval, val_eq in Hif.
  destruct x; destruct v'15; auto.
  intro.
  inverts H.
  rewrite peq_true in Hif.
  rewrite Int.eq_true in Hif.
  destruct Hif; tryfalse.
  clear Hif.
  rewrite H26. rename H26 into Hi2x.
  rename v'7 into l1.
  rename v'9 into l2.
  rename v'13 into tcbls.
  assert (exists st0 m sus0, TcbMod.get tcbls x = Some (i, st0, m, sus0)). 
  {
    unfolds in H22.
    simpljoin.
    apply H22.
    splits.
    clear; int auto.
    lia.
    unfold nat_of_Z.
    rewrite nth_val_imp_nth_val'_2.
    rewrite Hi2x. eauto.
    rewrite Hv'4len. lia.
    auto.
  }
  destruct H26.  destruct H26. destruct H26. 
  rename H26 into Hgetx.
  Require Import new_inv.
  hoare remember (17::18::20::nil)%nat pre.
  remember (v'28
  :: v'24
     :: x7
        :: x6
           :: Vint32 i6
              :: Vint32 i5
                 :: Vint32 i4
                    :: Vint32 i3
                       :: Vint32 i2
                          :: Vint32 i1 :: Vint32 i0 :: nil) as tcbcur.
  eapply backward_rule1.
  intros.
  instantiate (1 := (
  [|ptr_in_tcbdllseg (Vptr (v'29, Int.zero)) v'5 (l1++tcbcur::l2)|] **
  tcbdllseg v'5 Vnull v'25 Vnull (l1++tcbcur::l2) **
  [|TCBList_P v'5 (l1++tcbcur::l2) v'10 tcbls|] ** H26)).
  eapply tcbdllseg_combine.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep cancel H26.
  sep pauto.
  go. go. go.
  go.
  hoare_split_pure_all.
  assert (ptr_in_tcbdllseg (Vptr x) v'5 (l1++tcbcur ::l2)).
  Lemma tcbget_ptr_in_tcblist:
  forall tcblst head rtbl tcbmap x xx,
   TCBList_P head tcblst rtbl tcbmap ->
   get tcbmap x = Some xx ->
   ptr_in_tcbdllseg (Vptr x) head tcblst.
  Proof.
    induction tcblst.
    intros.
    simpl in H.
    subst tcbmap.
    rewrite map_emp_get in H0.
    inverts H0.
    intros.
    unfold1 ptr_in_tcbdllseg.
    remember (beq_val (Vptr x) head).
    destruct b.
    auto.
    unfold1 TCBList_P in H.
    simpljoin.
    rewrite H1.
    eapply IHtcblst.
    exact H4.
    assert ( x <> x0).
    intro.
    subst x0.
    rewrite beq_val_true in Heqb.
    tryfalse.
    unfold join,get,sig in *; simpl in *.
    eapply TcbMod.join_get_or in H2.
    destruct H2; eauto.
    rewrite TcbMod.get_a_sig_a' in H2.
    inverts H2.
    go.
    eauto.
  Qed.

  eapply tcbget_ptr_in_tcblist; eauto.
  eapply backward_rule1.
  intros.
  eapply tcbdllseg_split' in H30; eauto.
  hoare unfold.
  destruct v'9.
  {
    unfold tcbdllseg.
    simpl.
    hoare unfold.
    tryfalse.
  }
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  hoare_split_pure_all.
  destruct H26. 
  inverts H26.

  hoare unfold.
  hoare forward.
  go.
  destruct (Int.eq (i12&ᵢ$ OS_STAT_SUSPEND)
  ($ OS_STAT_RDY)); auto.
  hoare_split_pure_all.
  instantiate(1:=Afalse).
  hoare remember (1::2::3::nil)%nat pre.
  remember (v'43
  :: v'13
     :: x12
        :: x11
           :: Vint32 i13
              :: 
              Vint32 i12
              :: 
              Vint32 i11
              :: 
              Vint32 i10
              :: 
              Vint32 i9
              :: 
              Vint32 i8
              :: 
              Vint32 i7
              :: nil) as needtcb.
  eapply backward_rule1.
  intros.
  instantiate (1 := (
  [|ptr_in_tcbdllseg (Vptr (v'44, Int.zero)) v'5 (v'7 ++ needtcb :: v'9)|] **
  tcbdllseg v'5 Vnull v'25 Vnull (v'7 ++ needtcb :: v'9) **
  [|TCBList_P v'5 (v'7 ++ needtcb :: v'9) v'10 tcbls|] ** H36)).

  eapply tcbdllseg_combine.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep cancel H36.
  sep pauto.
  go. go. go.
  go. eauto.
  hoare_split_pure_all.
  assert (ptr_in_tcbdllseg (Vptr (v'29, Int.zero)) v'5 (v'7 ++ needtcb :: v'9)).
  rewrite <- H30.
  auto.
  eapply backward_rule1.
  intros.
  eapply tcbdllseg_split' in H52; eauto.
  hoare_split_pure_all.
  destruct v'46.
  {
    unfold tcbdllseg.
    simpl.
    hoare unfold.
    inverts H56.
  }
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  hoare unfold.
  rewrite H30.
  rewrite H52.
  
  eapply seq_rule.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros.
  unfold OldOSInvWL.
  sep normal. sep eexists.
  sep cancel AOSTime.
  sep cancel APthreadAttr. 
  sep cancel IntInv. sep cancel TmrInv.
  sep cancel CoreCommuInv. sep cancel PartitionInv.
  sep cancel Acs. sep cancel Aier. sep cancel Ais.
  sep cancel Aisr. sep cancel Aie. sep cancel p_local.
  sep cancel aemp_isr_is. sep cancel AOSMapTbl.
  sep cancel AOSUnMapTbl. 
  sep cancel AOSTCBFreeList.
  sep cancel AOSRdyTblGrp. 
  sep cancel EvtInv. 
  instantiate(1:=
  LV pCSpace @ CSPACE ∗ |-> v'2 **
  LV ptcb @ OS_TCB ∗ |->  Vptr (v'44, Int.zero) **
  LV thread @ long |-> Vint32 i **
  LV y @ char_t |-> Vint32 i4 ** 
  A_dom_lenv
  ((thread, long) :: (y, char_t) :: (ptcb, OS_TCB ∗):: (pCSpace, CSPACE ∗) :: nil)).
  sep auto. go.
  go. go.
  splits; go.
  go. 
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  go.
  eapply threadresume_absimp_sta_rdy; eauto.
  go.
  hoare forward.

  eapply disj_rule; hoare_split_pure_all.
  eapply pfalse_rule.
  hoare remember (1::2::3::nil)%nat pre.
  remember (v'43
  :: v'13
     :: x12
        :: x11
           :: Vint32 i13
              :: 
              Vint32 i12
              :: 
              Vint32 i11
              :: 
              Vint32 i10
              :: 
              Vint32 i9
              :: 
              Vint32 i8
              :: 
              Vint32 i7
              :: nil) as needtcb.
  eapply backward_rule1.
  intros.
  instantiate (1 := (
  [|ptr_in_tcbdllseg (Vptr (v'44, Int.zero)) v'5 (v'7 ++ needtcb :: v'9)|] **
  tcbdllseg v'5 Vnull v'25 Vnull (v'7 ++ needtcb :: v'9) **
  [|TCBList_P v'5 (v'7 ++ needtcb :: v'9) v'10 tcbls|] ** H36)).

  eapply tcbdllseg_combine.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep cancel H36.
  sep pauto.
  go. go. go.
  go. eauto.
  hoare_split_pure_all.
  assert (ptr_in_tcbdllseg (Vptr (v'29, Int.zero)) v'5 (v'7 ++ needtcb :: v'9)).
  rewrite <- H30.
  auto.
  eapply backward_rule1.
  intros.
  eapply tcbdllseg_split' in H52; eauto.
  hoare_split_pure_all.
  destruct v'46.
  {
    unfold tcbdllseg.
    simpl.
    hoare unfold.
    inverts H56.
  }
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  hoare unfold.
  rewrite H30.
  rewrite H52.

  unfold CapabilityInv.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (AOSCSpacePrioTbl).
  hoare remember (1::nil)%nat pre.
  unfold AOSCSpacePrioTbl.
  hoare_split_pure_all.
  assert(Hv'52len: length v'52 = 64%nat).
  simpljoin. auto.
  assert(Hv'53len: length v'53 = 64%nat).
  simpljoin. auto.
  assert(Hv'52match: array_type_vallist_match 
  CSPACE ∗ v'52).
  simpljoin. auto.
  eapply backward_rule1 with (p:=AOSCSpacePrioTbl v'29 v'52 v'53 v'54 ** H75).
  intros. sep cancel H75.
  unfold AOSCSpacePrioTbl. sep auto.
  clear H76.
  subst H75.
  eapply seq_rule.
  hoare_lifts_trms_pre (Aop).
  eapply assign_rule_lvar.
  intros. splits; intros.
  sep cancel pCSpace. eauto.
  sep auto.
  intros.
  unfold AOSCSpacePrioTbl in H75.
  eapply array_member_rv_g.
  unfold GAarray.
  sep normal. sep eexists.
  sep cancel OSCSpacePrioTbl.
  sep cancel Aarray. sep cancel A_dom_lenv.
  eauto.
  simpl. auto.
  eauto. sep get rv. rewrite Hi4true. auto.
  eauto. auto. auto. lia.
  auto. rewrite Hv'52len. auto.
  2: eauto.
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hv'52len. 
  clear -Hi4range. lia.
  eapply eq_vptr. eauto.
  intros. eexists. sep cancel p_local.
  simpl. auto.
  assert(Hi4matchptr:
  rule_type_val_match CSPACE ∗
  (nth_val' (Z.to_nat (Int.unsigned i4)) v'52) = true).
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hv'52len. 
  clear -Hi4range. lia.
  
  eapply seq_rule.
  eapply ift_rule'.
  intros.
  eapply bop_rv.
  sep get rv.
  sep get rv.
  eauto. 
  unfold val_inj, bop_eval, val_eq.
  clear -Hi4matchptr.
  simpl in Hi4matchptr.
  destruct (nth_val' (Z.to_nat (Int.unsigned i4)) v'52); tryfalse; auto.
  destruct a. auto.
  simpl. eauto.
  hoare_split_pure_all.
  eapply seq_rule.
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros.
  unfold OldOSInvWL.
  sep normal. sep eexists.
  sep cancel AOSTime.
  sep cancel APthreadAttr. 
  sep cancel IntInv. sep cancel TmrInv.
  sep cancel CoreCommuInv. sep cancel PartitionInv.
  sep cancel Acs. sep cancel Aier. sep cancel Ais.
  sep cancel Aisr. sep cancel Aie. sep cancel p_local.
  sep cancel aemp_isr_is. sep cancel AOSMapTbl.
  sep cancel AOSUnMapTbl. 
  sep cancel AOSTCBFreeList.
  sep cancel AOSRdyTblGrp. 
  sep cancel EvtInv. 
  unfold CapabilityInv.
  instantiate(1:=
  LV pCSpace @ CSPACE ∗ |-> nth_val' (Z.to_nat (Int.unsigned i4))
  v'52 **
  LV ptcb @ OS_TCB ∗ |->Vptr (v'44, Int.zero) **
  LV thread @ long |-> Vint32 i **
  LV y @ char_t |-> Vint32 i4 ** 
  A_dom_lenv
  ((thread, long) :: (y, char_t) :: (ptcb, OS_TCB ∗):: (pCSpace, CSPACE ∗) :: nil)).
  sep auto. go. go. go.
  splits; go.
  go. 
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  go.
  eapply threadresume_absimp_curpspace_null; eauto.
  go.
  hoare forward.
  eapply disj_rule; hoare_split_pure_all.
  eapply pfalse_rule.
  assert(Hi4notnull: (nth_val' (Z.to_nat (Int.unsigned i4)) v'52) <> Vnull).
  unfold val_inj, bop_eval, val_eq in H75.
  simpl in Hi4matchptr.
  destruct (nth_val' (Z.to_nat (Int.unsigned i4)) v'52 ); tryfalse.
  destruct H75; tryfalse. auto.
  destruct v'29.
  eapply backward_rule1. intros.
  sep_lift_context_in H76 (AOSCSpacePrioTbl).
  Require Import ACSpace_defs.
  eapply AOSCSpacePrioTbl_unfold_any_idx_frm with(idx:= (Z.to_nat (Int.unsigned i4))) in H76; eauto.
  rewrite Hv'53len. 
  clear -Hi4range. lia.
  hoare_split_pure_all. unfold ACSpace.
  destruct v'57, p, p, p, v'61.
  unfold Acnode. 
  destruct c, p.
  hoare_split_pure_all.
  eapply backward_rule1. intros.
  sep_lift_context_in H85 (ASlots).
  eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat(CAP_TASK_CLASS)) in H85; eauto.
  unfold CAP_TASK_CLASS, SLOT_NUM. lia.
  hoare_split_pure_all.
  unfold ACap. destruct v'63, c, p.
  hoare_split_pure_all.
  rewrite H76.
  rewrite nth_val'_length_imp; eauto.
  2: destruct H78; auto.
  eapply seq_rule.
  hoare_lifts_trms_pre (Aop).
  eapply ift_rule'.
  intros.
  eapply bop_rv.
  eapply bop_rv.
  Require Import CapRelLemmas.
  eapply lv_mapsto_to_rv.
  2:{
    eapply field_asrt_impl_struct_aop.
    3:{
      eapply field_asrt_impl_union_aop'.
      2:{
        eapply field_asrt_impl_struct_aop'.
        3:{
          eapply field_asrt_impl_struct_aop'.
          3:{
          eapply expr_field_array_asrt_impl_frm_val.
            4:{
            eapply local_val_struct_member_addr_frm.
              4:{
                sep cancel pCSpace. 
                eauto.
                } 
                unfold CSPACE. eauto.
                unfold field_offset. simpl. eauto.
                simpl. unfold Cte. simpl. eauto. 
              }
              unfold field_offset. simpl.
              rewrite Int.add_zero.
              change ($ 4 +ᵢ  $ 4) with ($8). eauto.
              instantiate(1:=2%nat). simpl. auto.
              simpl. unfold Slot. eauto.
              }
              simpl. unfold Cap. eauto.
              unfold field_offset. simpl. rewrite Int.add_zero.
              eauto.
            }
            simpl.
            unfold Content. eauto.
            unfold field_offset. simpl.
            rewrite Int.add_zero. eauto.
          }
          simpl. unfold Cap_Category. eauto.
        }
        simpl. eauto.
        unfold field_offset. simpl.
        rewrite Int.add_zero. eauto.
      }
    2:{
    rewrite Int.add_zero.
    rewrite Int.add_zero.
    simpl typelen in *.
    rewrite <- addition_trans.
    rewrite Int.unsigned_repr.
    rewrite Int.add_assoc.
    change ($ 4 +ᵢ  $ 4) with ($8).

    sep normal in H89.
    sep lift 6%nat in H89.
    unfold Aptrmapsto in H89 at 1.
    exact H89.
    unfold CAP_TASK_CLASS. rewrite max_unsigned_val.
    lia. lia. 
    }
    simpl. auto.
    sep get rv.
    eauto.
    unfold val_inj, bop_eval, and. auto.
    simpl. eauto.
    sep get rv.
    eauto.
    unfold val_inj, bop_eval, and, val_eq.
    destruct (Int.eq (i29&ᵢ$ TASK_RESUME_CAP) ($ 0)); auto.
    simpl. eauto.
    hoare_split_pure_all.

    eapply backward_rule1.
    intros.
    sep lifts (4::5::6::7::nil)%nat in H90. 
    eapply fold_Cap in H90.
    sep lifts (3::4::1::5::nil)%nat in H90.
    eapply ASlots_fold_any_idx_frm in H90; [idtac | eauto..]. 
    sep lifts (7::8::1::nil)%nat in H90.
    eapply fold_Acnode in H90.
    sep lifts (1::7::8::9::10::nil)%nat in H90.
    eapply fold_ACSpace  in H90; [idtac | eauto..]. 
    sep lifts (6::1::7::nil)%nat in H90. 
    eapply ACSpaceAarray_fold_any_idx_frm in H90; [idtac | eauto; try lia..]. 
    sep lifts (4::5::nil)%nat in H90.
    rewrite addition_trans in H90.
    assert(i4 = $(Z.of_nat (Z.to_nat (Int.unsigned i4)))).
    rewrite of_to_nat_unsignedv'.
    rewrite Int.repr_unsigned. auto.
    rewrite H91 in H90 at 1.
    clear H91.
    eapply array_asrt_eq_frm in H90.
    sep lifts (4::2::1::nil)%nat in H90.
    eauto.
    clear -Hi4range. lia.
    rewrite nth_val_length_imp; eauto.
    destruct H78. auto.
    simpl. lia. auto.
    unfold CAP_TASK_CLASS, SLOT_NUM. lia.
    destruct H86. auto.
    destruct H86. auto.
    auto.
    eapply seq_rule.
    hoare_lifts_trms_pre (Aop).
    eapply excrit1_rule'_ISnil_ISRemp'''_lg.
    intros.
    unfold OldOSInvWL.
    sep normal. sep eexists.
    sep cancel AOSTime.
    sep cancel APthreadAttr. 
    sep cancel IntInv. sep cancel TmrInv.
    sep cancel CoreCommuInv. sep cancel PartitionInv.
    sep cancel Acs. sep cancel Aier. sep cancel Ais.
    sep cancel Aisr. sep cancel Aie. sep cancel p_local.
    sep cancel aemp_isr_is. sep cancel AOSMapTbl.
    sep cancel AOSUnMapTbl. 
    sep cancel AOSTCBFreeList.
    sep cancel AOSRdyTblGrp. 
    sep cancel EvtInv. 
    unfold CapabilityInv.
    unfold AOSCSpacePrioTbl.
    instantiate(1:=
    LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i24) **
    LV ptcb @ OS_TCB ∗ |->Vptr (v'44, Int.zero) **
    LV thread @ long |-> Vint32 i **
    LV y @ char_t |-> Vint32 i4 ** 
    A_dom_lenv
    ((thread, long) :: (y, char_t) :: (ptcb, OS_TCB ∗):: (pCSpace, CSPACE ∗) :: nil)).
    sep auto. go. go. go.
    splits; go. go.
    hoare abscsq.
  Hint Resolve noabs_oslinv.
  go.
  eapply threadresume_absimp_nocapability; eauto.
  go.
  hoare forward.
  eapply disj_rule; hoare_split_pure_all.
  eapply pfalse_rule.

  eapply backward_rule1.
    intros.
    sep lifts (4::5::6::7::nil)%nat in H90. 
    eapply fold_Cap in H90.
    sep lifts (3::4::1::5::nil)%nat in H90.
    eapply ASlots_fold_any_idx_frm in H90; [idtac | eauto..]. 
    sep lifts (7::8::1::nil)%nat in H90.
    eapply fold_Acnode in H90.
    sep lifts (1::7::8::9::10::nil)%nat in H90.
    eapply fold_ACSpace  in H90; [idtac | eauto..]. 
    sep lifts (6::1::7::nil)%nat in H90. 
    eapply ACSpaceAarray_fold_any_idx_frm in H90; [idtac | eauto; try lia..]. 
    sep lifts (4::5::nil)%nat in H90.
    rewrite addition_trans in H90.
    assert(i4 = $(Z.of_nat (Z.to_nat (Int.unsigned i4)))).
    rewrite of_to_nat_unsignedv'.
    rewrite Int.repr_unsigned. auto.
    rewrite H91 in H90 at 1.
    clear H91.
    eapply array_asrt_eq_frm in H90.
    sep lifts (4::2::1::nil)%nat in H90.
    eauto.
    clear -Hi4range. lia.
    rewrite nth_val_length_imp; eauto.
    destruct H78. auto.
    simpl. lia. auto.
    unfold CAP_TASK_CLASS, SLOT_NUM. lia.
    destruct H86. auto.
    destruct H86. auto.
    auto.
    eapply seq_rule.
    hoare_lifts_trms_pre (Aop).
    eapply excrit1_rule'_ISnil_ISRemp'''_lg.
    intros.
    unfold OldOSInvWL.
    sep normal. sep eexists.
    sep cancel AOSTime.
    sep cancel APthreadAttr. 
    sep cancel IntInv. sep cancel TmrInv.
    sep cancel CoreCommuInv. sep cancel PartitionInv.
    sep cancel Acs. sep cancel Aier. sep cancel Ais.
    sep cancel Aisr. sep cancel Aie. sep cancel p_local.
    sep cancel aemp_isr_is. sep cancel AOSMapTbl.
    sep cancel AOSUnMapTbl. 
    sep cancel AOSTCBFreeList.
    sep cancel AOSRdyTblGrp. 
    sep cancel EvtInv. 
    unfold CapabilityInv.
    unfold AOSCSpacePrioTbl.
    instantiate(1:=
    LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i24) **
    LV ptcb @ OS_TCB ∗ |->Vptr (v'44, Int.zero) **
    LV thread @ long |-> Vint32 i **
    LV y @ char_t |-> Vint32 i4 ** 
    A_dom_lenv
    ((thread, long) :: (y, char_t) :: (ptcb, OS_TCB ∗):: (pCSpace, CSPACE ∗) :: nil)).
    sep auto. go.
    go. go. splits; go.
    go.
    hoare abscsq.
    go.
    eapply absinfer_choice2; eauto; go.
    hoare abscsq.
    go.
    eapply absinfer_choice2; eauto; go.
    hoare abscsq.
    go.
    eapply absinfer_choice2; eauto; go.
    hoare abscsq.
    go.
    eapply absinfer_choice2; eauto; go.
    hoare abscsq.
    go.
    eapply absinfer_choice2; eauto; go.
    hoare abscsq.
    go.
    eapply absinfer_choice2; eauto; go.
    
    hoare abscsq.
    go.
    eapply absinfer_eq.
    eapply seq_rule.
    eapply call_rule'.
    unfold new_OS_spec. simpl.
    unfold OSTaskResume_spec. eauto. 
    intros.
    do 5 try (apply rvl_elim;[ symbolic_execution | ]);
    first [apply rvl_nil].
    intros. unfold_spec. sep normal. sep eexists.
    sep cancel Aie. sep cancel Ais.
    sep cancel Acs. sep cancel Aier.
    sep cancel Aisr. sep cancel p_local.
    unfold Int32toInt8 in H90.
    sep pauto. go.
    unfold getasrt. unfold OSTaskResumePost.
    unfold OSTaskResumePost'. intros.
    sep normal in H90. sep destruct H90.
    eexists. sep cancel p_local. simpl. auto.
    unfold getasrt. unfold OSTaskResumePre.
    unfold OSTaskResumePre'. intros.
    sep normal in H90. sep destruct H90.
    eexists. sep cancel p_local. simpl. auto.
    simpl. 
    clear -Hirange.
    rewrite inline_bittblfunctions.mutexpost_intlemma1; auto.
    assert(Int.unsigned i <=? Byte.max_unsigned = true).
    change Byte.max_unsigned with 255. int auto.
    rewrite H. auto. lia.
    unfold getasrt. unfold OSTaskResumePost.
    unfold OSTaskResumePost'.
    hoare_split_pure_all.
    inverts H90.
    hoare abscsq. go.
    eapply threadresume_absimp_succ; eauto.
    go. hoare forward.
    Unshelve. all: auto.
Qed.
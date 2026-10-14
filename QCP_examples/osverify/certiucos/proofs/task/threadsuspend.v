Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import ios_cap_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import abs_op.
Set Nested Proofs Allowed.
Set Keyed Unification.
Require Import thread_suspend.

Definition threadsuspend_curnull
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists thread v',
      vl = thread :: v' /\
      opv = (Some (Vint32 (Int.repr ESRCH))) /\
      O_opt = Some O1 
  end.

Definition threadsuspend_prio_inval
(vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
| (opv, O_opt) =>
    exists thread v',
    vl = thread :: v' /\
    opv = (Some (Vint32 (Int.repr ESRCH))) /\
    O_opt = Some O1 
end.

Definition threadsuspend_prio_placeholder
(vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
| (opv, O_opt) =>
    exists thread v',
    vl = thread :: v' /\
    opv = (Some (Vint32 (Int.repr ESRCH))) /\
    O_opt = Some O1 
end.

Definition threadsuspend_sta_notrdy
(vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
| (opv, O_opt) =>
    exists thread v',
    vl = thread ::v' /\
    opv = (Some (Vint32 (Int.repr EINVAL))) /\
    O_opt = Some O1 
end.

Definition threadsuspend_curpspace_null (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      (O2 = Some O1 /\ opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE))) 
        
end. 

Definition threadsuspend_nocapability (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      (O2 = Some O1 /\ opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE))) 
        
end. 

Definition threadsuspend_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
  exists rv,
     vl = (rv :: nil) /\
      (O2 = Some O1 /\ opv = Some (Vint32 (Int.repr 0))) 
        
end. 

Require Import ifun_tasksus_spec.

Definition Int32toInt8 v:=
  match v with
  |Vint32 i => Vint32
  (Int.modu i (Int.repr Byte.modulus))
  | _ => Vint32 (Int.repr 0)
  end.

Definition threadsuspend (vl: vallist) :=
  match vl with
  (thread :: vl') => 
  threadsuspend_curnull  (|thread :: nil|) ??
  threadsuspend_prio_inval (|thread :: nil|) ??
    threadsuspend_prio_placeholder (|thread :: nil|) ??
  threadsuspend_sta_notrdy (|thread :: nil|) ??
  threadsuspend_curpspace_null (|thread :: nil|) ??
  threadsuspend_nocapability (|thread :: nil|) ??
  spec_code_cons (ifun_tasksus_spec.tasksuspendcode (Int32toInt8(thread)::Vint32 (Int.repr 0)::nil))
    (threadsuspend_succ (|Vint32(Int.repr 0) :: nil|))
  | _ => spec_abort
  end.

Local Open Scope code_scope.

Require Import abs_op.
Require Import init_spec.
Require Import inv_prop.
Require Import hoare_tactics.
Require Import pure_auto.
Require Import ucos_pauto.
Require Import seplog_tactics.
Require Import seplog_lemmas.
Require Import sep_cancel_ext.
Require Import derived_rules.
Require Import hoare_conseq.
Require Import ucos_forward.
Require Import sem_common.

Local Open Scope code_scope.

(* From: abs_infer_abt *)
Ltac absimp_abt_solver := 
  unfolds; intros;
  eexists; exgamma;
  (first [ splits ; 
            [ try simpl_subst_gamma;
              try hmstep_call_consturctor; try eapply spec_prim_step_abt; 
              [ unfolds; repeat eexists; subst;
                try (eapply absdata_elim; eauto with abst_solver_base); try eauto 
              | try apply map_join_emp 
              |  repeat hmstep_call_consturctor
              | .. ]
            | sep remember (1 :: nil)%nat; simpl in *; simpljoin ;
            do 6 eexists ; splits ; try eauto ; eapply change_aop_rule; eauto]
          | idtac] ).

Lemma absinfer_seq1:
  forall (p : asrt) (s1 : absop)  (s2 : spec_code) (s1' : absop) (sc : ossched),
    can_change_aop p ->
    sc ⊢  <|| s1 ||>  ** p ⇒  <|| s1' ||>  ** p ->
    sc ⊢  <|| s1;; s2 ||>  ** p ⇒  <|| s1';; s2 ||>  ** p.
Proof.
  intros.
  eapply absinfer_seq; try eauto.
Qed.

Lemma threadsuspend_absimp_curnull:
  forall sch thread P,
    can_change_aop P ->
    absinfer sch 
             (<|| threadsuspend (thread ::nil) ||>  ** P)
             (<|| END (Some (Vint32 (Int.repr ESRCH))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma threadsuspend_absimp_prio_inval:
  forall sch thread  P,
    can_change_aop P ->
    absinfer sch 
             (<|| threadsuspend (thread ::nil) ||>  ** P)
             (<|| END (Some (Vint32 (Int.repr ESRCH))) ||> ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma threadsuspend_absimp_prio_placeholder:
  forall sch thread vl' P,
    can_change_aop P ->
    absinfer sch 
             (<|| threadsuspend (thread ::vl') ||>  ** P)
             (<|| END (Some (Vint32 (Int.repr ESRCH))) ||> ** P).
Proof.
  infer_solver 2%nat.
Qed.

Lemma threadsuspend_absimp_sta_notrdy:
  forall sch thread vl' P,
    can_change_aop P ->
    absinfer sch 
             (<|| threadsuspend (thread ::vl') ||>  ** P)
             (<|| END (Some (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 3%nat.
Qed.

Lemma threadsuspend_absimp_curpspace_null:
  forall sch thread vl' P,
    can_change_aop P ->
    absinfer sch 
             (<|| threadsuspend (thread ::vl') ||>  ** P)
             (<|| END (Some (Vint32 (Int.repr USER_CAPABILITY_NONE))) ||> ** P).
Proof.
  infer_solver 4%nat.
Qed.

Lemma threadsuspend_absimp_nocapability:
  forall sch thread P vl',
    can_change_aop P ->
    absinfer sch 
             (<|| threadsuspend (thread ::vl') ||>  ** P)
             (<|| END (Some (Vint32 (Int.repr USER_CAPABILITY_NONE))) ||> ** P).
Proof.
  infer_solver 5%nat.
Qed.

Lemma threadsuspend_absimp_succ:
  forall sch v'  P,
    can_change_aop P ->
    absinfer sch 
            (<|| threadsuspend_succ (|v' ::nil|) ||>  ** P)
            (<|| END (Some (Vint32 (Int.repr 0))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Definition pthreadsuspendapi :=
  (threadsuspend, (Tint8, Tint32 :: nil)).

Definition new_api_spec_list :=
  ((pthread_suspend, pthreadsuspendapi) :: nil) ++ api_spec_list.

Definition new_api_spec :=
  convert_api_spec new_api_spec_list.

Definition new_os_spec :=
  (new_api_spec, GetHPrio).

Require Import ifun_spec.
Local Open Scope list_scope.

Definition os_spec_list_ext :=
  (((OSTaskSuspend, OSTaskSuspend_spec) ::nil)
   ++ new_osq_spec_list).

Definition os_spec_ext :=
  convert_spec os_spec_list_ext.

Require Import abs_infer_step.
Require Import ucos_frmaop.
  
Definition api_fun_list_new := (pthread_suspend_impl :: nil)%list.
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
Require Import ucos_forward. (*change*)
Require Import math_auto.

Require Import sem_lab.
Require Import symbolic_lemmas.
Require Import sem_common.
Require Import Lia.
Require Import CapPure.

Ltac sep_lift_context_in H trm :=
  match type of H with
    | _ |= ?P =>
      match find_match_context P trm with
         | none _ => idtac 1 "no such term in the Hsat"; fail 1
         | some ?a => sep lifts (a::nil)%nat in H
      end
  end.

Ltac hoare_lift_pre trm :=
  match goal with
    | |-  {| _, _, _, _, _, _ |} |- _ {{ _ //\\ _ }} _ {{ _ //\\ _ }} =>
      let s := fresh in
      let H := fresh in
      eapply backward_rule3;
       [ intros s H; sep_lift_context_in H trm; exact H | idtac ]
    | |-  {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
      let s := fresh in
      let H := fresh in
      eapply backward_rule1;
       [ intros s H; sep_lift_context_in H trm; exact H | idtac ]
  end.

(* copy from CheckCapTypePure. *)
Lemma array_type_vallist_match_nth_val': 
  forall l n t,
    array_type_vallist_match t l ->
    (n < length l)%nat ->
    rule_type_val_match t (nth_val' n l) = true.
  Proof.
    induction l; destruct n; intros.
    simpl in H0. lia. 
    simpl in H0. lia. 
    simpl in H. simpljoin. simpl. auto.
    simpl in H0.  
    assert(n < length l)%nat by lia. 
    simpl in H. simpljoin. 
    lets Hx: IHl H2 H1. 
    simpl. auto.
  Qed.


Lemma PthreadsuspendProof:
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api_new pthread_suspend
              (threadsuspend, (Tint32,  Tint32 ::Tint32 :: nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api_new pthread_suspend
              (threadsuspend, (Tint32, Tint32 ::Tint32 :: nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api_new pthread_suspend = Some (t, d1, d2, s) /\
      {|new_OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  hoare_lift_pre Aop.
  hoare forward prim;pure_auto.
  hoare_split_pure_all.

  try unfold OSInv; try unfold AOSTCBList.
  unfold_dll.
  pure intro.
  hoare forward.
  go.

  unfold AOSTCBPrioTbl.
  unfold AGVars.
  hoare_split_pure_all.

  assert(Hpriolt64:Int.unsigned i4 < 64).
  unfold TCBList_P in H8.
  simpljoin.
  unfold TCBNode_P in H27.
  destruct x2, p, p.
  simpljoin. 
  unfold RL_TCBblk_P in H30.
  simpljoin.
  unfold V_OSTCBPrio in H30. simpl in H30. inverts H30. lia.
  assert(Htrue: Int.unsigned i4 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -Hpriolt64. int auto.
  assert(Hisptr: rule_type_val_match OS_TCB ∗ (nth_val' (Z.to_nat (Int.unsigned i4))
  v'4) = true).
  destruct H10.
  eapply array_type_vallist_match_nth_val'; eauto.
  rewrite H24.
  clear -Hpriolt64.
  int auto.

  hoare forward.
  Require Import seplog_trm_tacs.
  rewrite Htrue.
  eauto.
  eauto. 
  unfold val_inj, val_eq. 
  destruct (nth_val'
  (Z.to_nat (Int.unsigned i4))v'4); tryfalse.
  eauto.
  destruct a. auto.
  unfold val_inj, bop_eval, val_eq, and.
  destruct(Int.eq ($ 1) Int.one); auto.

  destruct (nth_val'
  (Z.to_nat (Int.unsigned i4))v'4); tryfalse.
  eauto.

  destruct a. auto.

  destruct (nth_val'
  (Z.to_nat (Int.unsigned i4))v'4); tryfalse.
  eauto.

  destruct a. auto.

  unfold val_inj, bop_eval, val_eq, and, bool_or.
  destruct(Int.eq ($ 1) Int.zero); auto.
  destruct(Int.eq ($ 1) Int.one); auto.
  destruct (nth_val'
  (Z.to_nat (Int.unsigned i4))v'4); tryfalse.
  try change (Int.ltu Int.zero Int.one) with (true).
  simpl. eauto.
  destruct a. auto.
  destruct (nth_val'
  (Z.to_nat (Int.unsigned i4))v'4); tryfalse.
  eauto.
  destruct a. auto.
  destruct(Int.eq ($ 1) Int.one); auto.
  destruct (nth_val'
  (Z.to_nat (Int.unsigned i4))v'4); tryfalse.
  eauto.
  destruct a. auto.

  destruct (nth_val'
  (Z.to_nat (Int.unsigned i4))v'4); tryfalse.
  eauto.
  destruct a. auto.

  hoare_split_pure_all.
  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros.

  unfold OldOSInvWL.

  sep normal. sep eexists.
  try unfold AOSTCBList;unfold_dll;unfold AGVars.
  unfold AOSTCBPrioTbl.
  sep normal. sep eexists.

  sep cancel AOSUnMapTbl. sep cancel OSTCBPrioTbl.
  sep cancel AOSRdyTblGrp. sep cancel AOSTime.
  sep cancel APthreadAttr. sep cancel EvtInv.
  sep cancel IntInv. sep cancel TmrInv.
  sep cancel CoreCommuInv. sep cancel PartitionInv.
  sep cancel Acs. sep cancel Aier. sep cancel Ais.
  sep cancel Aisr. sep cancel Aie. sep cancel p_local.  
  sep cancel Astruct. sep cancel dllseg.
  sep cancel dllseg. sep cancel AOSTCBFreeList.
  sep cancel CapabilityInv.

  instantiate(1:=
  LV pCSpace @ CSPACE ∗ |-> v'2 **
  LV ptcb @ OS_TCB ∗ |-> v'1 **
  LV thread @ long |-> Vint32 i **
  LV y @ char_t |-> Vint32 i4 ** 
  A_dom_lenv
  ((thread, long) :: (y, char_t) :: (ptcb, OS_TCB ∗):: (pCSpace, CSPACE ∗) :: nil)).
  sep auto; eauto.
  split. eauto.
  go.
  go.
  go.
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  go.
  eapply threadsuspend_absimp_curnull; eauto.
  can_change_aop_solver.
  hoare forward.
  eapply disj_rule.
  hoare_split_pure_all. eapply pfalse_rule.
  hoare_split_pure_all.

  hoare forward.

  destruct(Int.eq i ($ OS_IDLE_PRIO)); auto.
  unfold val_inj, bop_eval, val_eq.
  destruct(Int.ltu ($ ios_cap_defs.OS_LOWEST_PRIO) i); auto.
  unfold val_inj, bop_eval, val_eq.
  destruct(Int.eq i ($ ios_cap_defs.OS_LOWEST_PRIO)); auto.
  unfold val_inj, bop_eval, val_eq, bool_or.
  destruct(Int.ltu ($ ios_cap_defs.OS_LOWEST_PRIO) i); auto.
  destruct(Int.eq i ($ ios_cap_defs.OS_LOWEST_PRIO)); auto.
  destruct(Int.eq i ($ ios_cap_defs.OS_LOWEST_PRIO)); auto.
  unfold val_inj, bop_eval, val_eq, bool_or.
  destruct(Int.eq i ($ OS_IDLE_PRIO)); auto.
  destruct(Int.ltu ($ ios_cap_defs.OS_LOWEST_PRIO) i); auto.
  destruct(Int.eq i ($ ios_cap_defs.OS_LOWEST_PRIO)); auto.
  destruct(Int.eq i ($ ios_cap_defs.OS_LOWEST_PRIO)); auto.
  destruct(Int.ltu ($ ios_cap_defs.OS_LOWEST_PRIO) i); auto.
  destruct(Int.eq i ($ ios_cap_defs.OS_LOWEST_PRIO)); auto.
  destruct(Int.eq i ($ ios_cap_defs.OS_LOWEST_PRIO)); auto.

  hoare_split_pure_all.
  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros.

  unfold OldOSInvWL.
  sep normal. sep eexists.
  try unfold AOSTCBList;unfold_dll;unfold AGVars.
  unfold AOSTCBPrioTbl.
  sep normal. sep eexists.

  sep cancel AOSUnMapTbl. sep cancel OSTCBPrioTbl.
  sep cancel AOSRdyTblGrp. sep cancel AOSTime.
  sep cancel APthreadAttr. sep cancel EvtInv.
  sep cancel IntInv. sep cancel TmrInv.
  sep cancel CoreCommuInv. sep cancel PartitionInv.
  sep cancel Acs. sep cancel Aier. sep cancel Ais.
  sep cancel Aisr. sep cancel Aie. sep cancel p_local.
  
  sep cancel Astruct. sep cancel dllseg.
  sep cancel dllseg. sep cancel AOSTCBFreeList.
  sep cancel CapabilityInv.

  instantiate(1:=
  LV pCSpace @ CSPACE ∗ |-> v'2 **
  LV ptcb @ OS_TCB ∗ |-> v'1 **
  LV thread @ long |-> Vint32 i **
  LV y @ char_t |-> Vint32 i4 ** 
  A_dom_lenv
  ((thread, long) :: (y, char_t) :: (ptcb, OS_TCB ∗):: (pCSpace, CSPACE ∗) :: nil)).
  sep auto; eauto.
  split. eauto.
  go.  go.  go.
  hoare abscsq.
  go.
  eapply threadsuspend_absimp_prio_inval; eauto.
  can_change_aop_solver.
  hoare forward.
  eapply disj_rule.
  hoare_split_pure_all. eapply pfalse_rule.
  hoare_split_pure_all.

  assert(Hilt63: Int.unsigned i < 63).
  clear -H25.

  unfold val_inj, bop_eval, val_eq, bool_or in H25.
  destruct(Int.eq i ($ OS_IDLE_PRIO));
  destruct(Int.ltu ($ ios_cap_defs.OS_LOWEST_PRIO) i) eqn: Ha;
  destruct(Int.eq i ($ ios_cap_defs.OS_LOWEST_PRIO)) eqn: Hb; 
  try change (Int.ltu Int.zero Int.one) with (true) in H25;
  simpl in H25; destruct H25; tryfalse.
  
  unfold ios_cap_defs.OS_LOWEST_PRIO in Ha, Hb.
  clear -Ha Hb.
  int auto.
  assert(Hilt64: Int.unsigned i < 64).
  lia.

  assert(Hiisptr: rule_type_val_match OS_TCB ∗ (nth_val' (Z.to_nat (Int.unsigned i))
  v'4) = true).
  destruct H10.
  eapply array_type_vallist_match_nth_val'; eauto.
  rewrite H26.
  clear -Hilt64.
  int auto.

  hoare forward.
  eauto.

  hoare forward.
  unfold rule_type_val_match in Hiisptr.
  unfold val_inj, val_eq. 
  destruct (nth_val'
  (Z.to_nat (Int.unsigned i))v'4); tryfalse.
  eauto.
  destruct a. auto.
  hoare_split_pure_all.

  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros.

  unfold OldOSInvWL.

  sep normal. sep eexists.
  try unfold AOSTCBList;unfold_dll;unfold AGVars.
  unfold AOSTCBPrioTbl.
  sep normal. sep eexists.

  sep cancel AOSUnMapTbl. sep cancel OSTCBPrioTbl.
  sep cancel AOSRdyTblGrp. sep cancel AOSTime.
  sep cancel APthreadAttr. sep cancel EvtInv.
  sep cancel IntInv. sep cancel TmrInv.
  sep cancel CoreCommuInv. sep cancel PartitionInv.
  sep cancel Acs. sep cancel Aier. sep cancel Ais.
  sep cancel Aisr. sep cancel Aie. sep cancel p_local.
  
  sep cancel Astruct. sep cancel dllseg.
  sep cancel dllseg. sep cancel AOSTCBFreeList.
  sep cancel CapabilityInv.

  instantiate(1:=
  LV pCSpace @ CSPACE ∗ |-> v'2 **
  LV ptcb @ OS_TCB ∗ |-> nth_val' (Z.to_nat (Int.unsigned i)) v'4 **
  LV thread @ long |-> Vint32 i **
  LV y @ char_t |-> Vint32 i4 ** 
  A_dom_lenv
  ((thread, long) :: (y, char_t):: (ptcb, OS_TCB ∗) :: (pCSpace, CSPACE ∗) :: nil)).
  sep auto; eauto.
  split. eauto.
  go.  go.  go.
  hoare abscsq.
  go.
  eapply threadsuspend_absimp_prio_inval; eauto.
  can_change_aop_solver.
  hoare forward.
  eapply disj_rule.
  hoare_split_pure_all. eapply pfalse_rule.
  hoare_split_pure_all.

  rename v'4 into ptbl.
  assert (exists p, nth_val' (Z.to_nat (Int.unsigned i)) ptbl = Vptr p). {
    destruct (nth_val' (Z.to_nat (Int.unsigned i)) ptbl); eauto.
    destruct H26. discriminate.
    destruct H26. discriminate.
    destruct H26. discriminate.
    simpl in Hiisptr. destruct Hiisptr.
    discriminate. discriminate.
  } 
  simpljoin.
  rewrite H27.
  eapply seq_rule.
  {
    eapply ift_rule''.
    intros.
    eapply bop_rv.
    sep_get_rv.
    eapply addrof_gvar_rv.
    Require Import inline_tactics.
    gen_notin_lenv H29 OSPlaceHolder.
    eapply dom_lenv_imp_notin_lenv.
    eauto.
    sep cancel A_dom_lenv.
    sep cancel Agvarenv'.
    eauto.
    eauto.
    simpl.
    destruct x. destruct v'15.
    destruct ( Int.eq i7 i8 ); destruct (peq b b0); simpl; intro; tryfalse.
    simpl.
    eauto.
    hoare_split_pure_all.

    eapply seq_rule.
    eapply forward_rule2.
    hoare_lifts_trms_pre (Aop).
    eapply excrit1_rule'_ISnil_ISRemp'''_lg.
    intros.

    unfold OldOSInvWL.

    sep cancel Acs. sep cancel Aier. sep cancel Ais.
    sep cancel Aisr. sep cancel Aie. 
    instantiate(1:=
    LV pCSpace @ CSPACE ∗ |-> v'2 **
    LV ptcb @ OS_TCB ∗ |-> Vptr x **
    LV thread @ long |-> Vint32 i **
    LV y @ char_t |-> Vint32 i4 ** 
    A_dom_lenv
    ((thread, long) :: (y, char_t):: (ptcb, OS_TCB ∗) :: (pCSpace, CSPACE ∗) :: nil)).
    sep auto; eauto.
    split. eauto.
    go.    go.    go.
    hoare abscsq.
    go.
    eapply threadsuspend_absimp_prio_placeholder; eauto.
    can_change_aop_solver.
    hoare forward.
  }
  eapply disj_rule.
  hoare_split_pure_all. eapply pfalse_rule.
  hoare_split_pure_all.

(* In taskdelete.v *)
Lemma valinjbopevallemma:
forall x v'19, val_inj (bop_eval (Vptr x) (Vptr v'19) OS_TCB ∗ (Int8u) ∗ oeq) =
    Vint32 Int.zero \/
    val_inj (bop_eval (Vptr x) (Vptr v'19) OS_TCB ∗ (Int8u) ∗ oeq) =
    Vnull -> x <> v'19.
Proof.
  intros.
  destruct H.
  simpl in H.
  destruct x; destruct v'19.
  intro.
  inverts H0.
  rewrite peq_true in H.
  rewrite Int.eq_true in H.
  inverts H.
  simpl in H.
  destruct x; destruct v'19.
  destruct (peq b b0); destruct (Int.eq i i0); tryfalse.
Qed.

  apply valinjbopevallemma in H29.
  assert(Hinotnull: nth_val'(Z.to_nat (Int.unsigned i))
  ptbl <> Vnull).
  clear -Hiisptr H26.
  simpl in Hiisptr.
  destruct (nth_val'
  (Z.to_nat (Int.unsigned i))
  ptbl); tryfalse. 
  unfold val_inj, val_eq in H26.
  destruct H26; tryfalse.
  auto.
  clear H26.
  rename H29 into Hxneqv'15.
  rename H27 into Hi2x.
  rename v'29 into cur_tcb_blk.
  rename x into tosusptr.
  rename v'13 into tcbls.

  assert (
    exists st0 m sus0, TcbMod.get tcbls tosusptr = Some (i, st0, m, sus0)). {
      unfolds in H22.
      simpljoin.
      apply H22.
      splits.
      clear; int auto.
      lia.
      unfold nat_of_Z.
      rewrite nth_val_imp_nth_val'_2.
      rewrite Hi2x. eauto.
      rewrite H28. lia.
      assumption.
    }
  simpljoin.
  rename x into st0.
  rename x0 into m0.
  rename x1 into sus0.
  rename v'7 into l1.
  rename v'9 into l2.
  rename H26 into Hgetx.

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
  hoare remember (17::18::20::nil)%nat pre.
  eapply backward_rule1.
  intros.
  instantiate (1 := (
    [|ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'5 (l1++tcbcur::l2)|] **
    tcbdllseg v'5 Vnull v'25 Vnull (l1++tcbcur::l2) **
    [|TCBList_P v'5 (l1++tcbcur::l2) v'10 tcbls|] ** H26)).
  Require Import new_inv.
  eapply tcbdllseg_combine.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep cancel H26.
  sep pauto.
  go.    go.    go.     go.
  hoare_split_pure_all.
  assert (ptr_in_tcbdllseg (Vptr tosusptr) v'5 (l1++tcbcur ::l2)).

(* In taskdelete.v *)
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

  eapply tcbget_ptr_in_tcblist.
  eauto.
  eauto.

  eapply backward_rule1.
  intros.
  eapply tcbdllseg_split' in H31; eauto.
  hoare unfold.
  destruct v'7.
  {
    unfold tcbdllseg.
    simpl.
    hoare unfold.
    inverts H26.
  }
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  hoare_split_pure_all.
  destruct H26.
  inverts H26.
  rename v'42 into tosusblock.

  hoare unfold.
  hoare forward.
  go.
 
  destruct (Int.eq (i12&ᵢ$ OS_STAT_SUSPEND)
  ($ OS_STAT_RDY)); auto.
  destruct (Int.eq (i12&ᵢ$ OS_STAT_SUSPEND)
  ($ OS_STAT_RDY)); auto.
  hoare_split_pure_all.

  instantiate(1:=Afalse).
  hoare remember (1::2::3::nil)%nat pre.
  remember (v'41
  :: v'9
      :: x9
        :: x8
            :: Vint32 i13
              :: Vint32 i12
                  :: Vint32 i11 :: Vint32 i10 :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: nil) as needtcb.
  eapply backward_rule1.
  intros.
  instantiate (1 := (
    [|ptr_in_tcbdllseg (Vptr (tosusblock, Int.zero)) v'5 (v'4 ++ needtcb :: v'7)|] **
    tcbdllseg v'5 Vnull v'25 Vnull (v'4 ++ needtcb :: v'7) **
    [|TCBList_P v'5 (v'4 ++ needtcb :: v'7) v'10 tcbls|] ** H36)).
  eapply tcbdllseg_combine.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep cancel H36.
  sep pauto.
  go. go. go.
  go. eauto.
  hoare_split_pure_all.
  assert (ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'5 (v'4 ++ needtcb :: v'7)).
  rewrite H31 in H27.
  eauto.
  eapply backward_rule1.
  intros.
  eapply tcbdllseg_split' in H52; eauto.
  hoare_split_pure_all.
  destruct v'43.
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
  rewrite H31.
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
  LV ptcb @ OS_TCB ∗ |->  Vptr (tosusblock, Int.zero) **
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
  eapply threadsuspend_absimp_sta_notrdy; eauto.
  go.
  hoare forward.

  eapply disj_rule; hoare_split_pure_all.
  eapply pfalse_rule.
  hoare remember (1::2::3::nil)%nat pre.
  remember (v'41
  :: v'9
      :: x9
        :: x8
            :: Vint32 i13
              :: Vint32 i12
                  :: Vint32 i11
                    :: Vint32 i10
                        :: Vint32 i9
                          :: Vint32 i8 :: Vint32 i7 :: nil) as needtcb.

  eapply backward_rule1.
  intros.
  instantiate (1 := (
  [|ptr_in_tcbdllseg (Vptr (tosusblock, Int.zero)) v'5 (v'4 ++ needtcb :: v'7)|] **
  tcbdllseg v'5 Vnull v'25 Vnull (v'4 ++ needtcb :: v'7) **
  [|TCBList_P v'5 (v'4 ++ needtcb :: v'7) v'10 tcbls|] ** H36)).

  eapply tcbdllseg_combine.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep cancel H36.
  sep pauto.
  go. go. go.
  go. 
  hoare_split_pure_all.
  assert (ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'5 (v'4 ++ needtcb :: v'7)).
  rewrite <- H31.
  auto.
  eapply backward_rule1.
  intros.
  eapply tcbdllseg_split' in H52; eauto.
  hoare_split_pure_all.
  destruct v'43.
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
  rewrite H31.
  rewrite H52.

  unfold CapabilityInv.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (AOSCSpacePrioTbl).
  hoare remember (1::nil)%nat pre.
  unfold AOSCSpacePrioTbl.
  hoare_split_pure_all.
  assert(Hv'50len: length v'50 = 64%nat).
  simpljoin. auto.
  assert(Hv'51len: length v'51 = 64%nat).
  simpljoin. auto.
  assert(Hv'50match: array_type_vallist_match 
  CSPACE ∗ v'50).
  simpljoin. auto.
  eapply backward_rule1 with (p:=AOSCSpacePrioTbl v'49 v'50 v'51 v'52 ** H75).
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
  eauto. sep get rv. rewrite Htrue. auto.
  eauto. auto. auto. lia.
  auto. rewrite Hv'50len. auto.
  2: eauto.
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hv'50len. 
  clear -Hpriolt64. lia.
  eapply eq_vptr. eauto.
  intros. eexists. sep cancel p_local.
  simpl. auto.
  assert(Hi4matchptr:
  rule_type_val_match CSPACE ∗
  (nth_val' (Z.to_nat (Int.unsigned i4)) v'50) = true).
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hv'50len. 
  clear -Hpriolt64. lia.
  
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
  destruct (nth_val' (Z.to_nat (Int.unsigned i4)) v'50); tryfalse; auto.
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
  v'50 **
  LV ptcb @ OS_TCB ∗ |->Vptr (tosusblock, Int.zero) **
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
  eapply threadsuspend_absimp_curpspace_null; eauto.
  go.
  hoare forward.
  eapply disj_rule; hoare_split_pure_all.
  eapply pfalse_rule.
  assert(Hi4notnull: (nth_val' (Z.to_nat (Int.unsigned i4)) v'50) <> Vnull).
  unfold val_inj, bop_eval, val_eq in H75.
  simpl in Hi4matchptr.
  destruct (nth_val' (Z.to_nat (Int.unsigned i4)) v'50 ); tryfalse.
  destruct H75; tryfalse. auto.
  destruct v'49.
  eapply backward_rule1. intros.
  sep_lift_context_in H76 (AOSCSpacePrioTbl).
  Require Import ACSpace_defs.
  eapply AOSCSpacePrioTbl_unfold_any_idx_frm with(idx:= (Z.to_nat (Int.unsigned i4))) in H76; eauto.
  rewrite Hv'51len. 
  clear -Hpriolt64. lia.
  hoare_split_pure_all. unfold ACSpace.
  destruct v'55, p, p, p, v'59.
  unfold Acnode. 
  destruct c, p.
  hoare_split_pure_all.
  eapply backward_rule1. intros.
  sep_lift_context_in H85 (ASlots).
  eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat(CAP_TASK_CLASS)) in H85; eauto.
  unfold CAP_TASK_CLASS, SLOT_NUM. lia.
  hoare_split_pure_all.
  unfold ACap. destruct v'61, c, p.
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
  destruct (Int.eq (i29&ᵢ$ TASK_SUSPEND_CAP) ($ 0)); auto.
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
  clear -Hpriolt64. lia.
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
    LV ptcb @ OS_TCB ∗ |->Vptr (tosusblock, Int.zero) **
    LV thread @ long |-> Vint32 i **
    LV y @ char_t |-> Vint32 i4 ** 
    A_dom_lenv
    ((thread, long) :: (y, char_t) :: (ptcb, OS_TCB ∗):: (pCSpace, CSPACE ∗) :: nil)).
  sep auto. go. go. go.
  splits; go. go.
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  go.
  eapply threadsuspend_absimp_nocapability; eauto.
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
  clear -Hpriolt64. lia.
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
  LV ptcb @ OS_TCB ∗ |->Vptr (tosusblock, Int.zero) **
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
  unfold ifun_tasksus_spec.OSTaskSuspend_spec. eauto. 
  intros.
  do 5 try (apply rvl_elim;[ symbolic_execution | ]);
  first [apply rvl_nil].
  intros. unfold_spec. sep normal. sep eexists.
  sep cancel Aie. sep cancel Ais.
  sep cancel Acs. sep cancel Aier.
  sep cancel Aisr. sep cancel p_local.

  unfold Int32toInt8 in H90.
  sep pauto. go.
  unfold getasrt. unfold ifun_tasksus_spec.OSTaskSuspendPost.
  unfold ifun_tasksus_spec.OSTaskSuspendPost'. intros.
  sep normal in H90. sep destruct H90.
  eexists. sep cancel p_local. simpl. auto.
  unfold getasrt. unfold ifun_tasksus_spec.OSTaskSuspendPre.
  unfold ifun_tasksus_spec.OSTaskSuspendPre'. intros.
  sep normal in H90. sep destruct H90.
  eexists. sep cancel p_local. simpl. auto.
  simpl. 
  clear -Hilt64.
  rewrite inline_bittblfunctions.mutexpost_intlemma1; auto.
  assert(Int.unsigned i <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255. int auto.
  rewrite H. auto.
  unfold getasrt. unfold ifun_tasksus_spec.OSTaskSuspendPost.
  unfold ifun_tasksus_spec.OSTaskSuspendPost'.
  hoare_split_pure_all.
  inverts H90.
  hoare abscsq. go.
  eapply threadsuspend_absimp_succ; eauto.
  go. hoare forward.
  Unshelve. all: auto.
Qed.

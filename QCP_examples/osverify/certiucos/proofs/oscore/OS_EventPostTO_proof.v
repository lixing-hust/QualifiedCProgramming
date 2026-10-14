Require Import ifun_spec.
Require Import ucos_include.
Require Import OSETWaitPure. 
Require Import Lia.
Require Import seplog_trm_tacs.

Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Lemma OS_EventPostTO_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OS_EventPostTO
                  vl logicl OS_EventPostTOPre ct ->
      Some r =
      BuildRetI os_internal OS_EventPostTO vl logicl OS_EventPostTOPost ct ->
      exists t d1 d2 s,
        os_internal OS_EventPostTO = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init spec.
  rename v'6 into vptr.
  rename v'7 into ier.
  (*L1 : pevent′→OSEventTbl[OSTCBCur′→OSTCBY] &=ₑ  (∼OSTCBCur′→OSTCBBitX);*)
  simpl in H0.
  invert H0.
  subst.
  unfold AEventNode.
  unfold AOSEvent.
  (* unfold AEventData. *)
  unfold AOSPostEventTbl.
  pure_auto.

  hoare unfold.
  
    assert (v'9 = Vint32 i4).
  {
  clear -H7 H8.
  unfold V_OSPostEventGrp in H7. simpl in H7.
  apply TcbMod.option2val. auto.
  }
  subst v'9.
  
  rename v'10 into pid.
  rename v'11 into cur_b.

  lets Hi1: range_ostcby H.
  destruct Hi1 as [Hi1 Hi0].
  assert (Z.to_nat (Int.unsigned i1) < length v'3)%nat.
  {
    rewrite H13.
    unfold OS_EVENT_TBL_SIZE.
    apply z_le_7_imp_n;auto.
    lia.
  }

  lets Hx: array_int8u_nth_lt_len H5 H2.
  Import DeprecatedTactic.
  mytac.
  rename H9 into Hi1_eq.
  hoare_lifts_trms_pre Aop.
  hoare forward.

  go.
  rewrite Hi1_eq.
  simpl.
  rtmatch_solve.
  go.
  rewrite Hi1_eq.
  simpl.
  auto.
  go.
  eapply eq_int;auto.

  (*L2 : If (pevent′→OSPostEventTbl[OSTCBCur′→OSTCBY] ==ₑ ′0) *)
  rewrite Hi1_eq.
  unfold and. unfold val_inj.

  hoare forward.
  go.
  (*   rewrite Hi1_eq. *)
  rewrite <- update_nth_val_length_eq.
  rewrite H13.
  unfold OS_EVENT_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  rewrite len_lt_update_get_eq.
  (*   rewrite Hi1_eq. *)
  simpl.
  rtmatch_solve.
  apply int_lemma1;auto.
  rewrite H13.
  unfold OS_EVENT_TBL_SIZE.
  simpl Z.of_nat.
  auto.

  rewrite len_lt_update_get_eq.
  simpl.

  destruct (Int.eq (x&ᵢInt.not i0) ($ 0));auto.
  rewrite H13.
  unfold OS_EVENT_TBL_SIZE.
  simpl Z.of_nat.
  auto.

  (*L3 : pevent′→OSPostEventGrp &=  ∼OSTCBCur′→OSTCBBitY *)
  (*   rewrite Hi1_eq. *)
  (*   change ( (Int.and Int.zero (Int.not i0))) with Int.zero. *)
  hoare unfold.
  (*   eapply forward_rule2. *)
  hoare forward.
  go.
  go.

  lets Hi1_eq': nth_val'_imply_nth_val H2 Hi1_eq.
  assert (Hi1_upeq: (nth_val (Z.to_nat (Int.unsigned i1))
                             (update_nth_val (Z.to_nat (Int.unsigned i1)) v'3
                                             (Vint32 (Int.and x (Int.not i0))))) = Some (Vint32 (Int.and x (Int.not i0)))).
  {
    eapply update_nth. eauto.
  }
  eapply nth_val_nth_val'_some_eq in Hi1_upeq.
  rewrite Hi1_upeq.

  remember (val_inj (val_eq (Vint32 (Int.and x (Int.not i0))) (Vint32 (Int.repr 0)))) as v1.
  unfold val_eq in Heqv1.
  destruct (Int.eq (Int.and x (Int.not i0)) (Int.repr 0)) eqn : eq1;
    simpl in Heqv1;
    subst;
    hoare forward;
    hoare unfold.
  Focus 2. destruct H9; tryfalse.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  
  sep cancel 2%nat 1%nat.
  sep cancel Astruct.
  sep cancel 2%nat 1%nat.
  sep cancel Aarray.
  sep cancel AEventData.
  sep cancel p_local.
  splits; simpl; eauto.
  splits; try go; eauto.

  instantiate (1 := Vint32 (i4&ᵢInt.not i)).
  eapply event_wait_rl_tbl_grp'; try eauto.
  simpl; eauto.
  eauto.
  apply array_type_vallist_match_hold;auto.
  rtmatch_solve.
  apply int_lemma1; eauto.
  pure_auto. pure_auto. pure_auto.
  split; auto.
  go.

  destruct H9; auto.
  
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.

  sep cancel 3%nat 1%nat.
  sep cancel Astruct.
  sep cancel 2%nat 1%nat.
  sep cancel Aarray.
  sep cancel AEventData.
  sep cancel p_local.
  splits; simpl; eauto.
  splits; try go; eauto.

  instantiate (1 := Vint32 i4).
  eapply event_wait_rl_tbl_grp''; try eauto.
  simpl; eauto.
  eauto.
  apply array_type_vallist_match_hold;auto.
  rtmatch_solve.
  apply int_lemma1; eauto.
  pure_auto. pure_auto. pure_auto.
  split; auto.
  go.

Qed.

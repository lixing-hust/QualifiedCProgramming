(* Definition OS_EventTO_impl :=
Void ·OS_EventTO·(⌞pevent @ OS_EVENT∗⌟)··{
       ⌞ ⌟;

       pevent′→OSEventTbl[OSTCBCur′→OSTCBY] =ₑ 
          pevent′→OSEventTbl[OSTCBCur′→OSTCBY] &ₑ (∼OSTCBCur′→OSTCBBitX);ₛ
       If (pevent′→OSEventTbl[OSTCBCur′→OSTCBY] ==ₑ ′0) {
          pevent′→OSEventGrp &=  ∼OSTCBCur′→OSTCBBitY
       };ₛ
       OSTCBCur′→OSTCBStat =ₑ ′OS_STAT_RDY;ₛ
       OSTCBCur′→OSTCBEventPtr =ₑ NULL;ₛ
       RETURN
}·.   *)

Require Import ifun_spec.
Require Import ucos_include.
Require Import OSETWaitPure. 
Require Import Lia.
Require Import seplog_trm_tacs.

Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Lemma OS_EventTO_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OS_EventTO
                  vl logicl OS_EventTOPre ct ->
      Some r =
      BuildRetI os_internal OS_EventTO vl logicl OS_EventTOPost ct ->
      exists t d1 d2 s,
        os_internal OS_EventTO = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init spec.

  (*L1 : pevent′→OSEventTbl[OSTCBCur′→OSTCBY] &=ₑ  (∼OSTCBCur′→OSTCBBitX);*)
  simpl in H0.
  invert H0.
  subst.
  unfold AEventNode.
  unfold AOSEvent.
  (* unfold AEventData. *)
  rename v'7 into ier.
  pure_auto.
  hoare unfold.
  rename v'11 into pid.  (* v'8 -> v'11 *)
  rename v'12 into cur_b. (* v'9 -> v'12 *)
  (* new add *)
  rename v'9 into lpetbl.
  inverts H6.
  rename i4 into pegrp. (* i5 -> i4 *)
  rename v'6 into petbl.
  rename x4 into petbl_addr.
  (* end of new add *)

  lets Hi1: range_ostcby H.
  destruct Hi1 as [Hi1 Hi0].
  assert (Z.to_nat (Int.unsigned i1) < length v'2)%nat.
  {
    rewrite H11. (* H8 -> H11 *)
    unfold OS_EVENT_TBL_SIZE.
    
    apply z_le_7_imp_n;auto.
    lia.
  }

  lets Hx: array_int8u_nth_lt_len H10 H2. (* H7 -> H10 *)
  Import DeprecatedTactic.
  mytac.
  rename H6 into Hi1_eq. (* H5 -> H6 *)
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

  (*L2 : If (pevent′→OSEventTbl[OSTCBCur′→OSTCBY] ==ₑ ′0) *)
  rewrite Hi1_eq.
  unfold and. unfold val_inj.
  (* assert (Hifx: x = Int.zero \/ x <> Int.zero) by tauto.
  destruct Hifx.
  subst x. *)
  hoare forward.
  go.
  (*   rewrite Hi1_eq. *)
  rewrite <- update_nth_val_length_eq.
  rewrite H11. (* H8 -> H11 *)
  unfold OS_EVENT_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  rewrite len_lt_update_get_eq.
  (*   rewrite Hi1_eq. *)
  simpl.
  rtmatch_solve.
  apply int_lemma1;auto.
  rewrite H11. (* H8 -> H11 *)
  unfold OS_EVENT_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  (*   rewrite Hi1_eq. *)
  rewrite len_lt_update_get_eq.
  simpl.
  (*   destruct (Int.eq (Int.and Int.zero (Int.not i0)) (Int.repr 0));auto. *)
  destruct (Int.eq (x&ᵢInt.not i0) ($ 0));auto.
  rewrite H11. (* H8 -> H11 *)
  unfold OS_EVENT_TBL_SIZE.
  simpl Z.of_nat.
  auto.

  (*L3 : pevent′→OSEventGrp &=  ∼OSTCBCur′→OSTCBBitY *)
  (*   rewrite Hi1_eq. *)
  (*   change ( (Int.and Int.zero (Int.not i0))) with Int.zero. *)
  hoare unfold.
  (*   eapply forward_rule2. *)
  hoare forward.
  go.
  go.

  lets Hi1_eq': nth_val'_imply_nth_val H2 Hi1_eq.
  assert (Hi1_upeq: (nth_val (Z.to_nat (Int.unsigned i1))
                             (update_nth_val (Z.to_nat (Int.unsigned i1)) v'2
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
  Focus 2. destruct H6; tryfalse. (* H5 -> H6 *)
  hoare forward.
  hoare forward.
  hoare forward.

  sep cancel 2%nat 1%nat.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel AEventData.
  sep cancel AOSPostEventTbl. (* new add *)
  sep cancel p_local. 
  splits; simpl; eauto.
  splits; try go; eauto.
  eauto. (* new add *)
  unfolds; simpl; eauto. (* new add *)
  auto. (* new add *)

  instantiate (1 := Vint32 (i5&ᵢInt.not i)). (* i5 -> i6 *)
  eapply event_wait_rl_tbl_grp'; try eauto.
  simpl; eauto.
  eauto.
  apply array_type_vallist_match_hold;auto.
  rtmatch_solve.
  apply int_lemma1; eauto.
  split; auto.
  go.

  tryfalse. (* new add *)
(*   destruct H5; auto. *)
  
  hoare forward.
  hoare forward.
  hoare forward.

  sep cancel 3%nat 1%nat. 
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel AEventData.
  sep cancel AOSPostEventTbl. (* new add *)
  sep cancel p_local. 
  splits; simpl; eauto.
  splits; try go; eauto.
  eauto. (* new add *)
  unfolds; simpl; eauto. (* new add *)
  auto. (* new add *)

  instantiate (1 := Vint32 i5). (* i5 -> i6 *)
  eapply event_wait_rl_tbl_grp''; try eauto.
  simpl; eauto.
  eauto.
  apply array_type_vallist_match_hold;auto.
  rtmatch_solve.
  apply int_lemma1; eauto.
  split; auto.
  go.

Qed.

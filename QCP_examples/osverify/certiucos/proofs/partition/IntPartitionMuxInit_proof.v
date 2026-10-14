
Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import ifun_spec.
Require Import abs_op.

Require Import abs_infer_step.
Require Import abs_infer_abt. 
Require Import ucos_frmaop.

(* absimp lemmas *)
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
Require Import abs_op_partition_ext.

Require Import symbolic_lemmas.
Require Import Aarray_new_common.

Require Import ev_aux_code.
Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Require Import ucos_include.
Require Import IntPartitionMuxInit_pure.
Require Import tv_match.
Require Import inline_tactics.
Require Import Lia.
Require Import gjb_common.

Local Open Scope code_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Lemma intpartmux_absimp_succ:
   forall sch P uconf mgf fv fn fps fccs fnps idm a cpus ccf ptrg ptrt pt mgl ipm ipm' s, 
    can_change_aop P ->
    uconf = (mgf, fv, fn, fps, fccs, fnps, idm, a, cpus, ccf, ptrg, ptrt, pt, mgl) ->
    ipm' = set_idm_to_ipm (Z.to_nat (USER_INT_MAX_N - 1)%Z) idm ipm ->
    absinfer sch
      (<|| intpartmux nil ;; s||> ** HIntPartMux ipm ** Hucosconf uconf ** P)
      (<|| s ||> **  HIntPartMux ipm' ** Hucosconf uconf ** P).
Proof.
infer_solver 0%nat.
Qed.

Lemma ptrconst_rv: 
  forall (s : RstateOP) a, s |= Rv eptrconst a @ (Tptr Tint32) == Vptr a.
Proof.
  intros.
  simpl.
  destruct s as [[[[[[[]]]]]]].
  simpl.
  splits; auto.
Qed.

Lemma IntPartitionMuxInit_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal IntPartitionMuxInit vl logicl IntPartitionMuxInitPre ct->
      Some r =
      BuildRetI os_internal IntPartitionMuxInit vl logicl IntPartitionMuxInitPost ct->
      exists t d1 d2 s,
        os_internal IntPartitionMuxInit = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init spec.
  subst logicl.
  rename v'5 into intrvl.
  inverts H. inverts H1.

  (* ucoscfg ′ =ₑ 〈 ucos_conf_t ∗ 〉 eptrconst BOOT_DATA_ADDRESS;ₛ *)
  hoare forward.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_lvar. eauto.
  split; sep pauto.
  intros.
  eapply cast_rv_tptr.
  3:{ apply assign_type_match_true; simpl; auto. }
  3:{ pure_auto. sep auto. }
  eapply ptrconst_rv.
  split; intros.

  (* i ′ =ₑ ′ 0;ₛ *)
  hoare forward.

  (* WHILE (′ USER_INT_MAX_N >ₑ i ′) *)
  (*1: remember irrelevant sep-conjunctions*)
  unfold AIntPartMux.
  hoare_lifts_trms_pre (AIntPartMux', AIntrDomainMux, Alvarmapsto ios_cap_defs.i, Alvarmapsto ucoscfg).
  hoare remember (1 :: 2 :: 3 :: 4 :: nil)%nat pre.

  (*2: get the loop inv into the pre-condition,
    so the pre-condition after the while statement
    can be correctly instantiated *)
  eapply backward_rule1 with (p := (*below is the loop inv*)
     (EX vi intpvl,
      LV ios_cap_defs.i @ Int32u |-> (V$ (Z.of_nat vi)) **
      [| 0 <= (Z.of_nat vi) < USER_INT_MAX_N |] **
      AIntPartMux' intpvl**
      AIntrDomainMux BOOT_DATA_ADDRESS intrvl v'6 **
      LV ucoscfg @ ucos_conf_t ∗ |-> Vptr BOOT_DATA_ADDRESS **
      [| IntPartMux_P (Z.of_nat vi) intrvl intpvl |] ** H) \\//
     (EX intpvl,
      LV ios_cap_defs.i @ Int32u |-> (V$ (USER_INT_MAX_N)) **
      AIntPartMux' intpvl **
      AIntrDomainMux BOOT_DATA_ADDRESS intrvl v'6 **
      LV ucoscfg @ ucos_conf_t ∗ |-> Vptr BOOT_DATA_ADDRESS **
      [| IntPartMux_P USER_INT_MAX_N intrvl intpvl |] ** H)).
  intros.
  left.
  exists 0%nat. exists v'8.
  rewrite Nat2Z.inj_0.
  sep cancel AIntrDomainMux.
  sep cancel AIntPartMux'.
  sep cancel (Alvarmapsto ucoscfg).
  sep cancel (Alvarmapsto ios_cap_defs.i).
  sep split; eauto.
  unfold IntPartMux_P.
  intros. false.
  auto with zarith.
  unfold USER_INT_MAX_N.
  auto with zarith.
  unfold USER_INT_MAX_N.
  auto with zarith.

  (*3: apply the 'seq_rule' to get the while statement
    off the remaining statements, then apply the 'while_rule' *) 
  eapply seq_rule.
  (*4: prove the condition expression of while is legal *)
  eapply while_rule.
  intros.
  destruct H1.
  symbolic_execution.
  pure_auto.
  symbolic_execution.

  (*Aistrue (′ USER_INT_MAX_N >ₑ i ′)*)
  (*5: the cond-expr of while hold implies the left disjunct
    of the loop-inv*)
  eapply backward_rule1 with (p :=
     (EX (vi : nat) (intpvl : vallist),
     LV ios_cap_defs.i @ long |-> (V$ Z.of_nat vi) **
     [|0 <= Z.of_nat vi < USER_INT_MAX_N|] **
     AIntPartMux' intpvl**
     AIntrDomainMux BOOT_DATA_ADDRESS intrvl v'6 **
     LV ucoscfg @ ucos_conf_t ∗ |-> Vptr BOOT_DATA_ADDRESS **
     [|IntPartMux_P (Z.of_nat vi) intrvl intpvl|] ** H)).
  intros.
  destruct H1.
  destruct H1.
  sep destruct H1.
  exists x. exists x0.
  eauto.
  destruct H1.
  unfold USER_INT_MAX_N in *.
  exists 11%nat. exists x.
  change (Z.of_nat 11) with 11.
  sep remember (1::nil)%nat in H1.
  false.
  destruct_s s.
  simpl in H1; simpljoin1.
  simpl in H4.
  rewrite H14 in H4.
  unfold cmp_int_type in H4.
  unfold cmp_val in H4.
  unfold cmpu in H4.
  apply mapstoval_load in H15; auto.
  destruct (load Int32u m (x13, 0)) eqn : eq1.
  pose proof (load_mono Int32u (x13, Int.unsigned Int.zero) H6 H15).
  rewrite H15 in H.
  change (Int.unsigned Int.zero) with 0 in H.
  rewrite H in eq1.
  inverts eq1.
  change (if Int.ltu ($ 11) ($ 11) then Some (Vint32 Int.one) 
          else Some (Vint32 Int.zero)) with (Some (Vint32 Int.zero)) in H4.
  destruct H4.
  destruct H1. inverts H1.
  simpl in H.
  tryfalse.
  destruct H4.
  destruct H.
  inverts H.

  (* IntPartitionMux ′ [i ′] =ₑ (ucoscfg ′ .. IntrDomainMux) [i ′];ₛ *)
  subst.
  unfold AIntPartMux'.
  unfold AIntrDomainMux.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  destruct v'26.
  lets Hid: H.
  inverts H.

  destruct H6.
  assert (Int.unsigned ($ Z.of_nat v'5) = Z.of_nat v'5).
  { eapply int_usign_eq.
    rewrite H. auto with zarith.
    unfold Int.max_unsigned, Int.modulus; simpl.
    unfold USER_INT_MAX_N in *.
    auto with zarith.
  }

  hoare forward.
  hoare_lifts_trms_pre (Aop, Alvarmapsto ucoscfg).
  eapply assign_rule_ptr_array_aop.

  intros.
  sep_get_rv.
  intro. split.
  intros. sep pauto.
  sep pauto.
  introv Hsat.
  sep_lifts_trms_in Hsat (Aarray).
  eapply expr_array_member_rv.
  unfold BOOT_DATA_ADDRESS in Hsat.
  eapply struct_member_array_rv.
  sep pauto.
  unfold ucos_conf_t. eauto. 
  eauto.
  instantiate (1:=∘ 11). instantiate (1:=char_t). eauto.
  eauto.
  eauto.
  sep get rv.
  eauto.
  eauto.
  assert (Z.of_nat ∘ 11 = 11).
  { eapply Coqlib.nat_of_Z_eq. auto with zarith. }
  unfold USER_INT_MAX_N.
  auto with zarith.
  simpl.
  rewrite H10.
  unfold USER_INT_MAX_N in *.
  auto with zarith.
  rewrite H10.
  rewrite H3.
  simpl.
  auto with zarith.
  eapply array_type_vallist_match_imp_rule_type_val_match.
  instantiate (2:=(Z.to_nat (Int.unsigned ($ Z.of_nat v'5)))).
  instantiate (1:=intrvl).
  eapply ge0_z_nat_le.
  rewrite H10.
  rewrite H. auto with zarith.
  rewrite H10.
  rewrite H3.
  simpl.
  unfold USER_INT_MAX_N in *.
  auto with zarith.
  eauto.
  eauto.
  
  intros.
  sep get rv.
  eauto.
  eauto.
  rewrite H10.
  unfold USER_INT_MAX_N in *.
  assert (Z.of_nat (Z.to_nat 11) = 11).
  { eapply Z2Nat.id. auto with zarith. }
  rewrite H11. eauto.
  eauto.
  eapply eq_int. pure_auto.
  destruct H5.
  rewrite H10. rewrite H11.
  unfold USER_INT_MAX_N in *.
  simpl. eauto.
  intros.
  exists (logic_val (V$ 1) :: v'24).
  eauto.
  sep pauto.

  assert (Z.of_nat(S v'5) <= USER_INT_MAX_N).
  { unfold USER_INT_MAX_N in *.
    auto with zarith.
  }
  assert (Hsuc: ($ Z.of_nat v'5 +ᵢ  $ 1) = ($ (Z.of_nat (S v'5)))).
  {
   clear -H11.
   change USER_INT_MAX_N with 11 in H11.
   int auto.
  }

  lets Hex: H1.
  eapply array_type_vallist_match_imp_rule_type_val_match in Hex.
  2: { instantiate (1:=v'5).
       rewrite H3.
       unfold USER_INT_MAX_N in *.
       auto with zarith.
  }
  simpl in Hex.
  destruct (nth_val' v'5 intrvl) eqn :eq1; tryfalse.
  eapply int_true_le255 in Hex.

  assert (Hcond: Z.of_nat (S v'5) = USER_INT_MAX_N \/ Z.of_nat (S v'5) < USER_INT_MAX_N).
  clear -H11.
  int auto.
  destruct Hcond as [Hc1 | Hc2].
  (* case 1*)
  hoare forward.
  rewrite Hsuc in H12.
  rewrite Hc1 in H12.
  eapply adisj_intro.
  right.
  sep auto.
  change 11 with USER_INT_MAX_N.
  rewrite <- Hc1.
  eapply IntPartMux_P_succ_split; eauto.

  split.
  eapply array_type_vallist_match_hold.
  eauto.
  rewrite H10.
  rewrite H13.
  unfold nat_of_Z.
  eapply Z2Nat.inj_lt.
  eauto.
  auto with zarith.
  eauto.
  eapply array_type_vallist_match_imp_rule_type_val_match.
  eapply ge0_z_nat_le.
  rewrite H10. eauto.
  rewrite H10.
  rewrite H3.
  simpl.
  unfold USER_INT_MAX_N in *. eauto.
  eauto.
  rewrite <- H13.
  eapply update_nth_val_len_eq.
  (* case 2*)
  hoare forward.
  rewrite Hsuc in H12.
  eapply adisj_intro.
  left.
  sep auto.
  change 11 with USER_INT_MAX_N.
  eapply IntPartMux_P_succ_split; eauto.
  auto with zarith.
  
  split.
  eapply array_type_vallist_match_hold.
  eauto.
  rewrite H10.
  rewrite H13.
  unfold nat_of_Z.
  eapply Z2Nat.inj_lt.
  eauto.
  auto with zarith.
  eauto.
  eapply array_type_vallist_match_imp_rule_type_val_match.
  eapply ge0_z_nat_le.
  rewrite H10. eauto.
  rewrite H10.
  rewrite H3.
  simpl.
  unfold USER_INT_MAX_N in *. eauto.
  eauto.
  rewrite <- H13.
  eapply update_nth_val_len_eq.
  (* end of while Aistrue*)

  (* start of while Aisfalse *)
  eapply backward_rule1 with (p :=
    (EX intpvl : vallist,
     LV ios_cap_defs.i @ long |-> (V$ 11) **
     AIntPartMux' intpvl **
     AIntrDomainMux BOOT_DATA_ADDRESS intrvl v'6 **
     LV ucoscfg @ ucos_conf_t ∗ |-> Vptr BOOT_DATA_ADDRESS **
     [|IntPartMux_P 11 intrvl intpvl|] ** H) **
     [| Vint32 Int.zero = Vint32 Int.zero \/ Vint32 Int.zero = Vnull |]).
  intros.
  destruct H1.
  destruct H1.
  lets Hnew: aconj_intro H1 H4.
  clear H1 H4.
  eapply sep_aconj_r_aisfalse_to_astar in Hnew.
  2: {
      intros.
      do 2 destruct H1.
      sep get rv.
      sep split in H1.
      assert (Hif: Int.ltu ($ Z.of_nat x) ($ 11) = true).
      clear -H4.
      int auto.
      rewrite Hif.
      simpl. eauto. pure_auto.
  }
  sep normal in Hnew.
  destruct Hnew. 
  destruct H1.
  sep split in H1.
  destruct H6; tryfalse.

  lets Hnew: aconj_intro H1 H4.
  clear H1 H4.
  eapply sep_aconj_r_aisfalse_to_astar in Hnew.
  2: { intros. destruct H1. sep get rv. }
  change (Int.ltu ($ 11) ($ 11)) with false in Hnew.
  sep split in Hnew.
  simpl in H1.
  destruct Hnew.
  sep normal.
  exists x.
  sep auto.
  sep split in H4.
  auto.
  
  subst.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aop, intparmux, absuconf).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply intpartmux_absimp_succ; eauto.
  pure_auto.
  eapply absinfer_eq.

  unfold AIntPartMux'.
  unfold AIntrDomainMux.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  
  lets Hid: H6.
  inverts H6.

  (* RETURN *)
  hoare forward.
  eapply RHL_IntPartMux_P_succ_split.
  instantiate (1:=v'8). eauto.
  instantiate (1:=intrvl). eauto.
  eauto. eauto. eauto. eauto.
  eapply RLH_IntPartMux_P_succ_split.
  instantiate (1:=v'8). eauto.
  instantiate (1:=intrvl). eauto.
  eauto. eauto. eauto.
Qed.



Require Import include_frm1.
Require Import base_tac1.
Require Import sep_auto1.

Require Import symbolic_lemmas1.
Require Import lmachLib1. 

Require Import int_auto1. 
Require Import math_auto1.

Open Scope int_scope. 
Open Scope code_scope.

Require Import Lia.

Ltac change_smo hyp :=
  repeat (
      match type of hyp with
      | context [substmo (?e, ?e0, ?m, ?i0, ?l, ?o, ?a) ?m' ?o'] =>
          change (substmo (e, e0, m, i0, l, o, a) m' o') with (e, e0, m', i0, l, o', a) in hyp
      end).

Ltac change_smo_hyps :=
  repeat (
      match goal with
      | H: context [substmo (?e, ?e0, ?m, ?i0, ?l, ?o, ?a) ?m' ?o'] |- _ => 
          change (substmo (e, e0, m, i0, l, o, a) m' o') with (e, e0, m', i0, l, o', a) in H
      end).

Ltac simp_mem_abst :=
  repeat (
      match goal with
      | H: context [getmem (?t1, ?t2, ?t3, ?t4, ?t5, ?t6, ?t7)] |- _ =>
          change (getmem (t1, t2, t3, t4, t5, t6, t7)) with t3 in H
      | H: context [getabst (?t1, ?t2, ?t3, ?t4, ?t5, ?t6, ?t7)] |- _ =>
          change (getabst (?t1, ?t2, ?t3, ?t4, ?t5, ?t6, ?t7)) with t6 in H
      | H: Maps1.join ?t1 empenv ?t2 |- _ => (apply map_join_emp' in H; subst t1)
      | H: Maps1.join empenv ?t1 ?t2 |- _ => (apply map_join_emp'' in H; subst t1)
      | H: context [?t = empenv] |- _ => subst t
      end).

(* ltac def originally from inv_prop.v *) 
Ltac simpl_sat_goal := unfold sat; fold sat; unfold substmo; unfold substaskst; unfold getmem; unfold getabst; unfold get_smem; unfold get_mem.

Ltac join_to_sub := 
  match goal with
    H: Maps1.join ?t1 ?t2 ?t3 |- sub ?t1 ?t => apply join_sub_l in H; auto
  | H: Maps1.join ?t1 ?t2 ?t3 |- sub ?t2 ?t => apply join_sub_r in H; auto
  end; 
  repeat ( 
      match goal with
        H1: sub ?t1 ?t2 |- _ => 
          match goal with 
            H2: Maps1.join t2 ?t3 ?t |- _ => apply join_sub_l in H2
          | H2: Maps1.join ?t3 t2 ?t |- _ => apply join_sub_r in H2
          end
      end).

Fixpoint len_decllist dls : nat :=
  match dls with
    dnil => 0
  | dcons _ _ dls => S (len_decllist dls)
  end. 
    
Lemma id_nth'_lt_len:
  forall decls id n k,
    id_nth' id decls n = Some k -> (k - n < len_decllist decls)%nat.
Proof.
  inductions decls.
  intros.
  simpl in H. inverts H.
  intros.
  assert (id=i \/ id<>i) by tauto.
  destruct H0.
  subst id.
  simpl in H. 
  destruct (Zeq_bool i i) eqn: E.
  inverts H. simpl. auto with zarith.
  apply Zeq_bool_neq in E.
  tryfalse.
  simpl in H.
  destruct (Zeq_bool id i) eqn: E.
  assert (id = i). { rewrite Zeq_is_eq_bool; auto. }
  tryfalse.
  apply IHdecls in H. 
  simpl.
  auto with zarith.
Qed.   
  
Lemma id_nth_lt_len: 
  forall decls id k, 
    id_nth id decls = Some k -> (k < len_decllist decls)%nat.
Proof.
  intros.
  unfold id_nth in H.
  apply id_nth'_lt_len in H.
  auto with zarith.
Qed.

Lemma astruct_dls_vl_len: 
  forall decls l vl s, 
    s |= Astruct' l decls vl -> (len_decllist decls = length vl)%nat. 
Proof.
  inductions decls.
  intros.
  simpl. auto with zarith.
  intros.
  simpl in H.
  destruct vl. simpl. auto. tryfalse.
  destruct l.
  intros.
  destruct vl. simpl in H. tryfalse.
  assert (exists s, s |= Astruct' (b, i0 +ᵢ  $ Z.of_nat (typelen t)) decls vl).
  {
    destruct t; try (destruct H; simpljoin; eexists; eauto).
    eexists. eauto. eexists. eauto.
  }
  destruct H0.
  apply IHdecls in H0.
  simpl.
  auto with zarith.
Qed.

Lemma struct_rule_type_vll_mt: 
  forall vl decls id k t v, 
    good_decllist decls = true -> 
    struct_type_vallist_match' decls vl ->
    id_nth id decls = Some k ->
    ftype id decls = Some t -> 
    (~(exists t' n, t = Tarray t' n) /\ ~(exists sid dls, t = Tstruct sid dls)) -> 
    nth_val' k vl = v ->
    rule_type_val_match t v = true.  
Proof. 
  inductions vl.
  - 
    introv Hgd Hmt Hoff Htp Htpn Hv.
    unfold struct_type_vallist_match' in Hmt. 
    destruct decls. 
    unfold id_nth in Hoff. simpl in Hoff. inv Hoff.
    inv Hmt.
  -
    intros.
    destruct k.
    + 
      simpl in H4. subst a.
      unfold struct_type_vallist_match' in H.
      destruct decls.
      unfold ftype in H2. inv H2.
      unfold id_nth in H1.
      simpl in H1.
      destruct (Zeq_bool id i) eqn: E.
      unfold ftype in H2. rewrite E in H2. inverts H2.
      destruct t;
        try (destruct H0; auto).
      destruct H3. false.  apply H2. do 2 eexists. eauto.
      destruct H3. false.  apply H3. do 2 eexists. eauto.
      apply id_nth_ge in H1.
      auto with zarith.
    +
      simpl in H4.
      destruct decls.
      unfold id_nth in H1. simpl in H1. inv H1.
      assert (good_decllist (decls) = true).
      {
        unfold good_decllist in H. fold good_decllist in H.
        rewrite andb_true_iff in H. (heat; jeauto2).
      } 
      assert (struct_type_vallist_match'  decls vl).
      { simpl in H0. destruct t0; (heat; jeauto2); auto. }
      assert (Hneq: Zeq_bool id i = false).
      {
        unfold id_nth in H1. simpl in H1.
        destruct (Zeq_bool id i) eqn: E. 
        inv H1.
        auto.
      }
      assert (Hidnth: id_nth id decls = Some k).
      {
        unfold id_nth in H1. 
        simpl in H1. 
        rewrite Hneq in H1.
        apply id_nth'_suc in H1.
        auto.
      }
      eapply IHvl; eauto.
      eapply gooddecl_gettype in H2; auto.
      instantiate (1:=k).
      apply id_nth_eq; auto.
Qed.

Lemma  mul_sz_decls: 
  forall m decls, 
    Int.ltu m Int.zero = false -> 
    Int.unsigned m <= Int.max_signed ->
    Int.min_signed <= Z.of_nat (szstruct decls) -> 
    Z.of_nat (szstruct decls) <= Int.max_signed -> 
    $ Z.of_nat (Z.to_nat (Int.unsigned m) * szstruct decls) = 
      Int.mul ($ Z.of_nat (szstruct decls)) m. 
Proof.
  intros.
  rewrite Nat2Z.inj_mul.
  rewrite Int.mul_commut.
  rewrite Z2Nat.id.
  rewrite Int.mul_signed.
  rewrite Int.signed_repr; eauto.
  rewrite Int.signed_eq_unsigned; eauto.
  rewrite Intlt_false_is_Zge in H. 
  rewrite Int.unsigned_zero in H.
  auto with zarith.
Qed.

Lemma struct_array_member_rv:
  forall decls s e1 te1 e2 te2 b o t n m vl v k t' id sid P, 
    s |= Rv e1 @ te1 == Vptr (b, o) ->
    s |= Rv e2 @ te2 == Vint32 m -> 
    s |= Astruct (b, o +ᵢ  $ Z.of_nat (Z.to_nat (Int.unsigned m) * typelen t)) t vl ** P -> 
    t = Tstruct sid decls -> 
    good_decllist decls = true -> 
    (te1 = Tarray t n \/ te1 = t ∗) -> 
    (te2 = Int8u \/ te2 = Int16u \/ te2 = Int32u) ->
    Int.ltu m Int.zero = false -> 
    Int.unsigned m <= Int.max_signed -> 
    Int.min_signed <= Z.of_nat (szstruct decls) <= Int.max_signed -> 
    struct_type_vallist_match t vl -> 
    ftype id decls = Some t' ->
    (~(exists t'' n, t' = Tarray t'' n) /\ ~(exists sid' ds', t' = Tstruct sid' ds')) ->  
    (id_nth id decls) = Some k ->
    nth_val' k vl = v -> 
    s |= Rv efield (e1[e2]) id @ t' == v. 
Proof. 
  introv He1 He2 Hastruct Ht Hgdecls Hte1 Hte2 Hmgez. 
  introv Hmle Hszrgn.
  introv Hmt Hidtp Ht' Hoff Hv. 
  subst t.
  unfold Astruct in Hastruct.
  assert (Hnth: nth_id k decls = Some id).
  { apply id_nth_eq; auto. }
  pose proof (nth_id_exists_off _ _ Hnth).
  destruct H as (off & Hfdoff).
  gen Hv.
  destruct Hastruct. simpljoin.
  introv Hv.
  rename H7 into Hastruct.
  erewrite struct_asrt_eq with (id:=id) (dls:=decls) (v:=v) (t:=t') (n:=k) in Hastruct;
    eauto.
  2: {
    subst v. apply nth_val_imp_nth_val'_2.
    assert (k < len_decllist decls)%nat.
    { eapply id_nth_lt_len; eauto. }
    erewrite <- astruct_dls_vl_len; eauto.
  }

  destruct s as [[[[[[]]]]]].
  destruct Hastruct. 
  gen Hv.
  simpljoin. change_smo_hyps.
  destruct H10.
  simp_mem_abst.
  simpl in H.

  destruct He1. destruct He2. (heat; jeauto2). intro Hv.
  simpl in H10. simpl in H12. simpl in H13. simpl in H14.

  assert (Hrtpvmt: rule_type_val_match t' v = true).
  { eapply struct_rule_type_vll_mt; eauto. }

  simpl_sat_goal.
  change (getsmem (e, e0, m0, i, l, o0, a)) with (e, e0, m0).
  simpl.
  rewrite H12. 
  destruct Hte1 as [Hte1' | Hte1']; subst te1;
  rewrite H14;
  destruct Hte2 as [Hte2' | [Hte2' | Hte2']]; subst te2; 
    try (
        rewrite Hidtp; 
        rewrite H10; 
        rewrite H13; 
        unfold getoff;  
        simpl; rewrite H12; rewrite H14;
        rewrite Hfdoff; 
        splits; auto;
        [
          eapply mapstoval_load in H; auto;
          simpl; rewrite Int.repr_unsigned;
          rewrite <- mul_sz_decls; auto;
          assert (Hsub: sub x1 m0) by (join_to_sub; eapply sub_trans; eauto);
          eapply lmachLib1.load_mem_mono; eauto
        |
        eapply rule_type_val_match_nvundef; eauto]).
Qed.

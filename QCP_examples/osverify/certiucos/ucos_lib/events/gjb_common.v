Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import os_program.
Require Import abs_op.
Require Import os_inv.
Require Import ucos_frmaop.
Require Import abs_step.
Require Import inv_prop. 
Require Import init_spec.
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
Require Import evt_spec_defs.
Require Import sem_lab.
Require Import symbolic_lemmas.
Require Import seplog_trm_tacs.
Require Import Aarray_new_common.
Require Import Lia.
Require Import Maps.
Require Import join_lib.
Require Import OSTimeTickPure.
(* Require Import OSMutex_common. *)
Require Import ucos_include.
Require Import ev_aux_code.


Open Scope code_scope.
Open Scope int_scope.
Open Scope Z_scope.

(* Ltac change_smo hyp :=
  repeat (
      match type of hyp with
      | context [substmo (?e, ?e0, ?m, ?i0, ?l, ?o, ?a) ?m' ?o'] =>
          change (substmo (e, e0, m, i0, l, o, a) m' o') with (e, e0, m', i0, l, o', a) in hyp
      end).

(* add ier *)
Ltac change_smo_hyps :=
  repeat (
      match goal with
      | H: context [substmo (?e, ?e0, ?m, ?i, ?i0, ?l, ?o, ?a) ?m' ?o'] |- _ => 
          change (substmo (e, e0, m, i, i0, l, o, a) m' o') with (e, e0, m', i, i0, l, o', a) in H
      end).

(* add ier *)
Ltac simp_mem_abst :=
  repeat (
      match goal with
      | H: context [getmem (?t1, ?t2, ?t3, ?t4, ?t5, ?t6, ?t7,?t8)] |- _ =>
          change (getmem (t1, t2, t3, t4, t5, t6, t7, t8)) with t3 in H
      | H: context [getabst (?t1, ?t2, ?t3, ?t4, ?t5, ?t6, ?t7, ?t8)] |- _ =>
          change (getabst (?t1, ?t2, ?t3, ?t4, ?t5, ?t6, ?t7, ?t8)) with t7 in H
      | H: Maps.join ?t1 empenv ?t2 |- _ => (apply map_join_emp' in H; subst t1)
      | H: Maps.join empenv ?t1 ?t2 |- _ => (apply map_join_emp'' in H; subst t1)
      | H: context [?t = empenv] |- _ => subst t
      end).

Ltac simp_get_smem :=
  repeat (
      match goal with
      | H: context [getsmem (?t1, ?t2, ?t3, ?t4, ?t5, ?t6, ?t7)] |- _ =>
          change (getsmem (t1, t2, t3, t4, t5, t6, t7)) with (?t1, ?t2, ?t3) in H
      end).

Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by tauto;
  destruct h as [Ht | Hf]. *)

Ltac pure_auto_try_false1 := 
  match goal with
    [H: val_inj ?t = ?v |- _] =>
      assert (val_inj t <> v); pure_auto; tryfalse
  | [H: val_inj ?t <> ?v |- _] =>
      assert (val_inj t = v); pure_auto; tryfalse
  end.

(* Lemma i_ge_z: 
  forall i, 
    Int.ltu i Int.zero = false /\ Int.ltu ($ 6) i = false /\ i <> $ 6 ->
    i = Int.zero \/ Int.ltu Int.zero i = true. 
Proof.
  intros.
  mytac.
  apply Intlt_false_is_Zge in H.
  rewrite Intlt_true_is_Zlt.
  int auto. mauto.
Qed. *)

Lemma i_ge_z: 
  forall i, 
    Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\
    i <> Int.repr (OS_USER_MAX_EVENTS / 3) ->
    i = Int.zero \/ Int.ltu Int.zero i = true. 
Proof.
  intros.
  mytac.
  apply Intlt_false_is_Zge in H.
  rewrite Intlt_true_is_Zlt.
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  int auto.
  assert (Hi0:Int.unsigned Int.zero = 0) by int auto.
  assert (Heq: i = Int.zero <-> Int.unsigned i = 0).
  {
    split; intros.
    rewrite <- Hi0.
    rewrite ZInteq_imp_Zeq; eauto.
    eapply Int.unsigned_eq_zero; eauto.
  }
  rewrite Heq.
  mauto.
Qed.

Lemma i_lt_6:
  forall i, 
    Int.ltu i Int.zero = false /\ Int.ltu ($ 6) i = false /\ i <> $ 6 -> 
    Int.ltu i ($ 6) = true.
Proof.
  intros. mytac.
  apply Intlt_false_is_Zge in H0. 
  rewrite Intlt_true_is_Zlt. 
  assert (Int.unsigned i <> Int.unsigned ($ 6)).
  { intro Hf. apply H1. mauto. }
  mauto.
Qed.

Lemma i_lt_user_max_event:
  forall i, 
    Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ 
    i <> Int.repr (OS_USER_MAX_EVENTS / 3) -> 
    Int.ltu i (Int.repr (OS_USER_MAX_EVENTS / 3)) = true.
Proof.
  intros. mytac.
  apply Intlt_false_is_Zge in H0. 
  rewrite Intlt_true_is_Zlt. 
  assert (Int.unsigned i <> Int.unsigned (Int.repr (OS_USER_MAX_EVENTS / 3))).
  { intro Hf. apply H1. eapply ZInteq_imp_Zeq in Hf; eauto. }
  mauto.
Qed.


Lemma int_min_neq_20: 
  Int.eq ($ 20) ($ Int.min_signed) = false.
Proof.
  unfold Int.eq. unfold zeq.
  destruct (Z.eq_dec (Int.unsigned ($ 20)) (Int.unsigned ($ Int.min_signed))).
  inverts e.
  auto.
Qed.

Lemma int_min_neq_maxevents:
  Int.eq ($ OS_USER_MAX_EVENTS) ($ Int.min_signed) = false.
Proof.
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  unfold nat_of_Z in *.
  unfold Int.eq.
  rewrite Int.unsigned_repr.
  2:{ split; solve_usr_max_evts_rgn. }
  destruct (zeq OS_USER_MAX_EVENTS (Int.unsigned ($ Int.min_signed))).
  change (Int.unsigned ($ Int.min_signed)) with 2147483648  in *.
  rewrite e in Hrgn4.
  false. auto with zarith.
  auto.
Qed.

Lemma unsigned_repr_0: Int.unsigned ($0) = 0.
  mauto. Qed.   
  
(* Lemma int_lt_gt_false: 
  forall i, 
    Int.ltu i ($ 0) = true -> 
    Int.ltu (Int.divs ($ 20) ($ 3)) i = true -> 
    False. 
Proof.
  introv Hlt Hlt'.
  assert (Int.ltu ($0) (Int.divs ($ 20) ($ 3)) = true).
  { unfolds. unfold zlt.  auto with zarith. }
  rewrite Intlt_true_is_Zlt in *.
  auto with zarith.
Qed.  *)

Lemma int_lt_gt_false: 
  forall i, 
    Int.ltu i ($ 0) = true -> 
    Int.ltu (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) i = true -> 
    False. 
Proof.
  introv Hlt Hlt'.
  rewrite Intlt_true_is_Zlt in *.
  change (Int.unsigned ($ 0)) with 0 in Hlt.
  pose proof Int.unsigned_range i.
  auto with zarith.
Qed.

Lemma int_lt_gt_false': 
  forall i, 
    Int.ltu i ($ 0) = true -> 
    Int.ltu ($ OS_USER_MAX_EVENTS / 3) i = true -> 
    False. 
Proof.
  introv Hlt Hlt'.
  rewrite Intlt_true_is_Zlt in *.
  change (Int.unsigned ($ 0)) with 0 in Hlt.
  pose proof Int.unsigned_range i.
  auto with zarith.
Qed.

Lemma int_lt_eq_false:
  forall i, 
    Int.ltu i ($ 0) = true -> 
    Int.eq i (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) = true -> 
    False. 
Proof.
  introv Hlt Heq.
  rewrite Intlt_true_is_Zlt in Hlt.
  change (Int.unsigned ($ 0)) with 0 in Hlt.
  pose proof Int.unsigned_range i.
  auto with zarith.
Qed.

Lemma int_lt_eq_false':
  forall i, 
    Int.ltu i ($ 0) = true -> 
    Int.eq i ($ OS_USER_MAX_EVENTS / 3) = true -> 
    False. 
Proof.
  introv Hlt Heq.
  rewrite Intlt_true_is_Zlt in Hlt.
  change (Int.unsigned ($ 0)) with 0 in Hlt.
  pose proof Int.unsigned_range i.
  auto with zarith.
Qed.

Lemma sub_eq_succ:
  forall m n l,  (S m <= l -> S n = l - m -> n = l - (S m))%nat. 
intros. auto with zarith. Qed.

Ltac unfold_usr_max_evts := 
  unfold OS_USER_MAX_EVENTS; unfold OS_MAX_EVENTS; unfold CORENUM.

Ltac unfold_usr_max_evts_in h :=
  unfold OS_USER_MAX_EVENTS in h; unfold OS_MAX_EVENTS in h; unfold CORENUM in h.

Lemma div_20_3_res: Int.divs ($ 20) ($ 3) = ($6).
  mauto. Qed. 

Ltac pure_auto_try_false := 
  match goal with
    [H: val_inj ?t = ?v |- _] =>
      assert (val_inj t <> v); pure_auto; tryfalse
  | [H: val_inj ?t <> ?v |- _] =>
      assert (val_inj t = v); pure_auto; tryfalse
  end.

Lemma pos_to_nat_6: Pos.to_nat 6 = 6%nat. 
auto with arith. Qed. 

Lemma mul_arith:
  forall idx, (idx < 6)%nat -> Z.of_nat (idx * 32) < 192.
intros. auto with zarith. Qed.

Lemma sub_Z_nat:
  forall (a:nat) b, (a <= ∘ b)%nat -> (∘ (b - Z.of_nat a) = (∘ b) - a)%nat. 
  unfold nat_of_Z in *. intros. auto with zarith. Qed.

Lemma mul_typelen_transform: 
  forall i, 
    Int.ltu i ($ 0) = false -> 
    Z.of_nat (S (Z.to_nat (Int.unsigned i))) <= OS_USER_MAX_EVENTS / 3 ->
    Int.mul ($ Z.of_nat (typelen sem_info_t)) i =
      $ Z.of_nat (Z.to_nat (Int.unsigned i) * typelen sem_info_t).
Proof.
  introv Hrgn1 Hrgn2. 
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  simpl in Hrgn2.
  simpl.
  assert (Hle: 0 <= Int.unsigned i) by int auto.
  destruct (Int.unsigned i) eqn: E.
  mauto.
  2: {
    lets H0: Pos2Z.neg_is_nonpos p.
    assert (Z.neg p = 0) by auto with zarith.
    rewrite H. mauto.
  }
  rewrite <- E. 
  unfold Int.mul. 
  rewrite Nat2Z.inj_mul.
  rewrite Z.mul_comm.
  asserts_rewrite (Int.unsigned ($ 60) = Z.of_nat 60). { mauto. }
  rewrite Z2Nat.id; auto. 
  mauto.
Qed.

Lemma ge_ne_lt_6:
  forall i, 
    Int.unsigned (Int.divs ($ 20) ($ 3)) >= Int.unsigned i ->
    i <> Int.divs ($ 20) ($ 3) ->
    (Z.to_nat (Int.unsigned i) < 6)%nat. 
Proof.
  intros.
  rewrite div_20_3_res in H0. rewrite div_20_3_res in H.
  assert (Int.unsigned i <> 6).
  { intro Hf. apply H0. destruct Hf. int auto. }
  asserts_rewrite (Int.unsigned ($6) = 6) in H. { int auto. } 
  auto with zarith.
Qed.

Lemma ge_ne_lt_rgn:
  forall i, 
    Int.unsigned (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) >= Int.unsigned i ->
    i <> Int.divs ($ OS_USER_MAX_EVENTS) ($ 3) ->
    (Z.to_nat (Int.unsigned i) < Z.to_nat (OS_USER_MAX_EVENTS / 3))%nat. 
Proof.
  intros.
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  lets Hrgn': usr_max_evts_rgn'.
  destruct Hrgn' as (Hrgn5 & Hrgn6).
  assert (Hsieq : (Int.signed ($ OS_USER_MAX_EVENTS) / Int.signed ($ 3)) = (OS_USER_MAX_EVENTS / 3)).
  clear -Hrgn5 Hrgn6.
  int auto.
  assert (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3) = $ (OS_USER_MAX_EVENTS / 3)).
  { unfold Int.divs in *.
     rewrite zdiv_equiv in *.
     rewrite Hsieq in *.
     auto.
     clear -Hrgn5 Hrgn6. int auto.
     clear. int auto.
     clear -Hrgn5 Hrgn6. int auto.
     clear. int auto.
     clear -Hrgn5 Hrgn6. int auto.
     clear. int auto.
  }
  rewrite H1 in H0.
  rewrite H1 in H.
  assert (Int.unsigned i <> OS_USER_MAX_EVENTS / 3).
  { intro Hf. apply H0. destruct Hf. clear - H0. int auto. }
  asserts_rewrite (Int.unsigned ($OS_USER_MAX_EVENTS / 3) = OS_USER_MAX_EVENTS / 3) in H.
  { clear -Hrgn3 Hrgn4. int auto. } 
  auto with zarith.
Qed.

Lemma user_max_events_le:
forall idx, 
Z.of_nat (S (Z.to_nat idx)) <= OS_USER_MAX_EVENTS / 3 ->
idx <= Int.max_signed.
Proof.
intros.
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
(* change (OS_USER_MAX_EVENTS / 3) with 6%Z in *. *)
int auto.
Qed.

Lemma user_max_events_le':
forall idx, 
Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 ->
Z.of_nat idx <= Int.max_signed.
Proof.
intros.
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
(* change (OS_USER_MAX_EVENTS / 3) with 6%Z in *. *)
int auto.
Qed.

Lemma user_max_events_eq:
forall idx, 
Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 ->
Int.unsigned (Int.repr (Z.of_nat idx)) = Z.of_nat idx.
Proof.
intros.
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
(* change (OS_USER_MAX_EVENTS / 3) with 6%Z in *. *)
int auto.
Qed.

(* Ltac join_to_sub := 
  match goal with
    H: Maps.join ?t1 ?t2 ?t3 |- sub ?t1 ?t => apply join_sub_l in H; auto
  | H: Maps.join ?t1 ?t2 ?t3 |- sub ?t2 ?t => apply join_sub_r in H; auto
  end; 
  repeat ( 
      match goal with
        H1: sub ?t1 ?t2 |- _ => 
          match goal with 
            H2: Maps.join t2 ?t3 ?t |- _ => apply join_sub_l in H2
          | H2: Maps.join ?t3 t2 ?t |- _ => apply join_sub_r in H2
          end
      end). *)

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
  assert ({id=i} + {id<>i}) by decide equality.
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
    destruct t; try (destruct H; simpljoin1; eexists; eauto).
    eexists. eauto. eexists. eauto. eauto.
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
    (~(exists t' n, t = Tarray t' n) /\ ~(exists sid dls, t = Tstruct sid dls)
       /\ ~(exists sid dls, t = Tunion sid dls)) -> 
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
      destruct H3. destruct H3. false.  apply H3. do 2 eexists. eauto.
      destruct H3. destruct H3. false.  apply H4. do 2 eexists. eauto.
      apply id_nth_ge in H1.
      auto with zarith.
    +
      simpl in H4.
      destruct decls.
      unfold id_nth in H1. simpl in H1. inv H1.
      assert (good_decllist (decls) = true).
      {
        unfold good_decllist in H. fold good_decllist in H.
        rewrite andb_true_iff in H. mytac. 
      } 
      assert (struct_type_vallist_match'  decls vl).
      { simpl in H0. destruct t0; mytac; auto. }
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

(* the key lemma used in the proof is struct_asrt_eq *)
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
    (~(exists t'' n, t' = Tarray t'' n) /\ ~(exists sid' ds', t' = Tstruct sid' ds')
    /\ ~(exists sid' ds', t' = Tunion sid' ds')) ->  
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
  destruct Hastruct. simpljoin1.
  introv Hv.
  rename H8 into Hastruct.
  erewrite struct_asrt_eq with (id:=id) (dls:=decls) (v:=v) (t:=t') (n:=k) in Hastruct;
    eauto.
  2: {
    subst v. apply nth_val_imp_nth_val'_2.
    assert (k < len_decllist decls)%nat.
    { eapply id_nth_lt_len; eauto. }
    erewrite <- astruct_dls_vl_len; eauto.
  }

  destruct s as [[[[[[[]]]]]]].
  destruct Hastruct. 
  gen Hv.
  simpljoin1. change_smo_hyps.
  destruct H11.
  simp_mem_abst.
  simpl in H.

  destruct He1.  destruct He2. mytac. intro Hv.
  simpl in H11. simpl in H13. simpl in H14. simpl in H15.

  assert (Hrtpvmt: rule_type_val_match t' v = true).
  { eapply struct_rule_type_vll_mt; eauto. }

  simpl_sat_goal.
  change (getsmem (e, e0, m0, i, i0, l, o0, a)) with (e, e0, m0).
  simpl.
  rewrite H13.

  (* destruct Hte1 as [Hte1' | Hte1']. subst te1.
  rewrite H15.
  destruct Hte2 as [Hte2' | [Hte2' | Hte2']]. subst te2.
  rewrite Hidtp. rewrite H11.
  rewrite H14. unfold getoff.
  simpl. rewrite H13. rewrite H15.
  rewrite Hfdoff. 
  splits. auto.
  eapply mapstoval_load in H. auto.
  simpl. rewrite Int.repr_unsigned.
          rewrite <- mul_sz_decls. auto.
          assert (Hsub: sub x1 m0) by (join_to_sub; eapply sub_trans; eauto).
          eapply lmachLib.load_mem_mono. eauto. eauto. eauto. eauto. eauto.
          eauto. eauto. eauto.
          eapply rule_type_val_match_nvundef; eauto.

          subst te2. rewrite Hidtp. rewrite H11.
          rewrite H14. unfold getoff.
          simpl. rewrite H13. rewrite H15.
          rewrite Hfdoff. 
          splits. auto.
          eapply mapstoval_load in H. auto.
          simpl. rewrite Int.repr_unsigned.
                  rewrite <- mul_sz_decls. auto.
                  assert (Hsub: sub x1 m0) by (join_to_sub; eapply sub_trans; eauto).
                  eapply lmachLib.load_mem_mono. eauto. eauto. eauto. eauto. eauto.
                  eauto. eauto. eauto.
                  eapply rule_type_val_match_nvundef; eauto.

                  subst te2. rewrite Hidtp. rewrite H11.
                  rewrite H14. unfold getoff.
                  simpl. rewrite H13. rewrite H15.
                  rewrite Hfdoff. 
                  splits. auto.
                  eapply mapstoval_load in H. auto.
                  simpl. rewrite Int.repr_unsigned.
                          rewrite <- mul_sz_decls. auto.
                          assert (Hsub: sub x1 m0) by (join_to_sub; eapply sub_trans; eauto).
                          eapply lmachLib.load_mem_mono. eauto. eauto. eauto. eauto. eauto.
                          eauto. eauto. eauto.
                          eapply rule_type_val_match_nvundef; eauto.

                          subst te1.        rewrite H15.
  destruct Hte2 as [Hte2' | [Hte2' | Hte2']]. subst te2.
  rewrite Hidtp. rewrite H11.
  rewrite H14. unfold getoff.
  simpl. rewrite H13. rewrite H15.

  splits. auto.
  eapply mapstoval_load in H. auto.
  simpl. rewrite Int.repr_unsigned.
          rewrite <- mul_sz_decls. auto.
          assert (Hsub: sub x1 m0) by (join_to_sub; eapply sub_trans; eauto).
          eapply lmachLib.load_mem_mono. eauto. eauto. eauto. eauto. eauto.
          eauto. eauto. eauto.
          eapply rule_type_val_match_nvundef; eauto. *)

  destruct Hte1 as [Hte1' | Hte1']; subst te1; 
  rewrite H15; 
    destruct Hte2 as [Hte2' | [Hte2' | Hte2']]; subst te2;
    try (
        rewrite Hidtp; 
        rewrite H11; 
        rewrite H14; 
        unfold getoff;  
        simpl; rewrite H13; rewrite H15;
        rewrite Hfdoff; 
        splits; auto;
        [
          eapply mapstoval_load in H; auto;
          simpl; rewrite Int.repr_unsigned;
          rewrite <- mul_sz_decls; auto;
          assert (Hsub: sub x1 m0) by (join_to_sub; eapply sub_trans; eauto);
          eapply lmachLib.load_mem_mono; eauto
        |
          eapply rule_type_val_match_nvundef; eauto]).
Qed.

Lemma pos_rgn_comp: 
  forall i, 
    Int.ltu i ($ 0) = false -> 
    Int.ltu (Int.divs ($ 20) ($ 3)) i = false -> 
    Int.eq i (Int.divs ($ 20) ($ 3)) = false -> 
    Int.unsigned i <= Int.max_signed. 
Proof.
  intros.
  assert (Hdiv: (20 ÷ 3)%Z = 6) by auto with zarith.
  int auto.
Qed.

Lemma pos_rgn_comp': 
  forall i, 
    Int.ltu i ($ 0) = false -> 
    Int.ltu (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) i = false -> 
    Int.eq i (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) = false -> 
    Int.unsigned i <= Int.max_signed. 
Proof.
  intros.
  
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  lets Hrgn': usr_max_evts_rgn'.
  destruct Hrgn' as (Hrgn5 & Hrgn6).
  assert (Hsieq : (Int.signed ($ OS_USER_MAX_EVENTS) / Int.signed ($ 3)) = (OS_USER_MAX_EVENTS / 3)).
  clear -Hrgn5 Hrgn6.
  int auto.
  assert (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3) = $ (OS_USER_MAX_EVENTS / 3)).
  { unfold Int.divs in *.
     rewrite zdiv_equiv in *.
     rewrite Hsieq in *.
     auto.
     clear -Hrgn5 Hrgn6. int auto.
     clear. int auto.
     clear -Hrgn5 Hrgn6. int auto.
     clear. int auto.
     clear -Hrgn5 Hrgn6. int auto.
     clear. int auto.
  }
  rewrite H2 in H0.
  rewrite H2 in H1.
  int auto.
Qed.

Lemma thirty_two_min_max: Int.min_signed <= 32 <= Int.max_signed.
  int auto. Qed.

Lemma pos_add_sub_one:
  forall pos i, 
    Int.ltu pos Int.zero = false ->
    (Int.unsigned pos) +  (Int.unsigned i) <= Int.max_unsigned ->
    Int.unsigned i >= 1 ->
    (pos +ᵢ  Int.one) +ᵢ  (i -ᵢ $ 1) = pos +ᵢ i. 
Proof.
  introv Hlt Hle Hge.
  assert (Int.unsigned pos >= 0).
  {
    apply Intlt_false_is_Zge in Hlt. 
    rewrite Int.unsigned_zero in Hlt.
    auto.
  }
  int auto.
  int auto.
Qed.

Lemma pos_add_i_neq: 
  forall pos i, 
    Int.unsigned i >= 1 ->
    Int.ltu pos Int.zero = false ->
    Int.unsigned pos + Int.unsigned i <= Int.max_unsigned ->
    pos <> pos +ᵢ i.
Proof.
  introv Hige Hpos Hadd.
  assert (Int.unsigned pos >= 0).
  {
    apply Intlt_false_is_Zge in Hpos. 
    rewrite Int.unsigned_zero in Hpos.
    auto.
  }
  intro Hf.
  unfold Int.add in Hf. 
  assert (Int.unsigned pos = Int.unsigned ($ (Int.unsigned pos + Int.unsigned i))).
  { rewrite Hf at 1. auto. }
  erewrite int_usign_eq in H0; eauto.
  auto with zarith.
  auto with zarith.
Qed. 

Lemma i_ge1_i_sub1_ge0: 
  forall i, Int.unsigned i >= 1 -> Int.ltu (i -ᵢ $ 1) Int.zero = false.
Proof.
  introv Hi. int auto. int auto.
Qed.

Lemma int_comp:
  forall v, Int.unsigned Int.zero <= Int.unsigned v ->
            v <> Int.zero ->
            Int.ltu (Int.zero) v = true. 
Proof.
  introv Hle Hne.
  int auto.
  assert (Int.unsigned v = 0).
  int auto.
  false.
  apply Hne. mauto.
Qed.



Lemma eval_type_ederef_eq :
 forall e ge le m t, evaltype (e) (ge, le, m) = Some (Tptr t) 
    -> evaltype (ederef e) (ge, le, m) = Some t.
Proof.
  intros.
  simpl in *;destruct e;tryfalse;auto.
  destruct (evaltype v ′ (ge, le, m)); tryfalse.
  inversion H;auto.
    inversion H;auto.
  destruct (evaltype (eunop u e) (ge, le, m)); tryfalse.
  inversion H;auto.
  destruct (evaltype (ebinop b e1 e2) (ge, le, m));tryfalse.
  inversion H;auto.
  destruct (evaltype (∗ e) (ge, le, m));tryfalse.
  inversion H;auto.
  destruct (evaltype (&ₐ e) (ge, le, m));tryfalse.
  inversion H;auto.
  destruct (evaltype (efield e i) (ge, le, m));tryfalse.
  inversion H;auto.
  destruct (evaltype (〈 t0 〉 e) (ge, le, m));tryfalse.
  inversion H;auto.
  destruct (evaltype (e1 [e2]) (ge, le, m));tryfalse.
  inversion H;auto.
Qed.


Lemma struct_member_e_rv':
  forall s t b o' vl tid decl n id t' v P e,
    (forall ids dl, t' <> Tstruct ids dl) ->
    (forall ids dl, t' <> Tunion ids dl) ->
    (forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
    rule_type_val_match t' v =true->
    (*v<> Vundef ->*)
    good_decllist decl = true ->
    s |= Rv e @ t∗  == Vptr (b, o') ->
    s |= Astruct (b, o') t vl ** P ->
(*     s |= LV x @ (Tptr t) |=> Vptr l @ perm ** Astruct l t vl ** P-> *)
    t = Tstruct tid decl ->
    nth_id n decl = Some id ->
    ftype id decl = Some t' ->
    nth_val n vl = Some v ->
    s |= Rv (efield (ederef (e)) id) @ t' == v.
Proof.
  introv Hnstr.
  introv Hnuni.
  introv Hnarr.
  introv Htv.
  assert (v<> Vundef) as Hvn.
  eapply rule_type_val_match_nvundef; eauto.
  introv Hgooddecl.
  intros.
  destruct s as ((o&O)&aop).
  unfold sat in *;fold sat in *;mytac.
  unfold substmo in *.
  destruct o as [[[[[]]]]].
  unfold substaskst in *.
  unfold getsmem in *.
  unfold getmem in *.
  unfold get_smem in *.
  unfold get_mem in *.
  simpl in *;mytac.
  (* Check (STRUCT tid ­{ decl }­). *)
  rewrite H.
  rewrite H5.
  rewrite H3.
  splits.
  unfold getoff.
  (* Print eval_type_addr_eq. *)
  lets: eval_type_ederef_eq H5.
  rewrite H0.
  lets Hoff: nth_id_exists_off H2.
  destruct Hoff.
  rewrite H1.
  unfold addrval_to_addr.
  rewrite struct_asrt_eq with (n:=n) in H10;eauto.
  unfold sat in H10;fold sat in H10;mytac.
  simpl in H14.
  rewrite Int.repr_unsigned.
  simpl in H10.
  assert (join x4 (merge x5 x0) m).
  {
    eapply join_merge23'.
    apply H10. apply H7.
  }
  eapply load_local. apply H8.
  eapply mapstoval_load;eauto.
  simpl;eauto.
  destruct H14; eauto.
  eauto.
  eauto.
Qed.

Theorem struct_member_e_rv'':
  forall s t b o' vl tid decl n id t' v P e,
    s |= Rv e @ t∗  == Vptr (b, o') ->
    s |= Astruct (b, o') t vl ** P->
    t = Tstruct tid decl ->
    good_decllist decl = true ->
    ftype id decl = Some t' ->
    (forall ids dl, t' <> Tunion ids dl) ->
    (forall ids dl, t' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
    id_nth id decl = Some n ->
    nth_val n vl = Some v ->
    (*v <> Vundef ->*)
    rule_type_val_match t' v = true ->    
    s |= Rv (efield (ederef (e)) id) @ t' == v.
Proof.
  intros.
  eapply struct_member_e_rv';eauto.
  eapply id_nth_eq;eauto.
Qed.


Lemma struct_member_e_rv:
forall (s : RstateOP)  (t : type) (* (l : addrval)  *)
         (vl : list val) (tid : ident) (decl : decllist) 
         (n : nat) (id : ident) (t' : type) (v : val) 
         (P : asrt) e b o,
       s |= Rv e @ t∗ == Vptr (b, o) ->
       s |= Astruct (b, o) t vl ** P ->
       t = STRUCT tid ­{ decl }­ ->
       good_decllist decl = true ->
       ftype id decl = Some t' ->
       (forall ids dl, t' <> Tunion ids dl) ->
       (forall (ids : ident) (dl : decllist), t' <> STRUCT ids ­{ dl }­) ->
       (forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
       id_nth id decl = Some n ->
       (n < length vl)%nat ->
       struct_type_vallist_match t vl ->
       nth_val' n vl = v -> s |= Rv (efield (ederef (e)) id) @ t' == v.
Proof.
  intros.
  subst v.
  assert (rule_type_val_match t' (nth_val' n vl) = true).
  subst t.
  unfold struct_type_vallist_match in H9.
  clear  s H H0 P tid. 
  gen vl decl n id t'.
  induction vl,decl, n; intros; simpl in *; tryfalse.
  apply id_nth_eq_0 in H7; subst.
  rewrite H7 in H3.
  inverts H3.
  destruct t'; intuition auto.
  false.
  exact (H6 t' n eq_refl).
  false.
  eapply H5; eauto.
  false.
  eapply H4; eauto.
  eapply IHvl; eauto.
  4 : instantiate (1 := decl).
  4 : instantiate (1 := id).
  apply andb_true_iff in H2; mytac; auto.
  destruct t; intuition auto.
  lia.
  apply id_nth_ueq_0 in H7; intuition auto.
  apply id_nth_ueq_0 in H7; mytac.
  rewrite H in H3.
  auto.
  eapply struct_member_e_rv''; eauto.
  apply nth_val_imp_nth_val'_2; auto.
Qed.

Lemma sem_rv: 
  forall s e x vl P, 
    s |= Rv e @ Tptr long == Vptr (x, Int.zero) -> 
    s |= Astruct (x, Int.zero) gjb_pos_blk_t vl ** P ->
    struct_type_vallist_match gjb_pos_blk_t vl -> 
    s |= Rv ∗e @ long == nth_val' 0 vl. 
Proof.
  introv Hrv Hstr Hmt.
  unfold Astruct in Hstr. 
  unfold gjb_pos_blk_t in Hstr. 
  simpl_sat Hstr. simpljoin1.
  lets Hlen: astruct_dls_vl_len H3.
  simpl in Hlen.
  destruct vl. simpl in Hlen. inverts Hlen.
  change (nth_val' 0 (v :: vl)) with v.
  erewrite struct_asrt_eq with (v:=v) (n:=0%nat) (t:=long) (id:=posval) (off:=Int.zero) in H3; 
    try (intros; pure_auto; fail); try (simpl; auto; fail).
  destruct s as [[[[[[[]]]]]]]. (* changed *)
  destruct H3.  simpljoin1.
  simp_mem_abst. change_smo_hyps.
  eapply deref_rv; eauto.
  2: {
    unfold struct_type_vallist_match in Hmt.
    unfold gjb_pos_blk_t in Hmt.
    simpl in Hmt.
    mytac.
  }
  instantiate (2:=true).
  assert (Hadd: Int.zero +ᵢ  Int.zero = Int.zero).
  { int auto. }
  rewrite Hadd in H6.
  remember (PV (x, Int.zero) @ long |-> v) as X.
  simpl_sat_goal.
  subst.
  exists x2. exists (merge x5 x1).
  exists m.
  exists x7. exists (merge x8 x4).
  exists o.
  splits; auto.
  simpl in H1. simpl in H5.
  eapply perm_map_lemmas_part1.join_merge23; eauto.
  eapply perm_map_lemmas_part1.join_merge23; eauto.
  instantiate (1:=
                 Astruct_rm (x, Int.zero) ⌞ posval @ long; nextpblk @ STRUCT gjb_pos_blk ⋆ ⌟ 
                                                             (v :: vl) posval ** P).
  remember (Astruct_rm (x, Int.zero) ⌞ posval @ long; nextpblk @ STRUCT gjb_pos_blk ⋆ ⌟ 
                                                        (v :: vl) posval) as X.
  simpl_sat_goal.
  exists x5. exists x1. eexists.
  exists x8. exists x4. eexists.
  splits; eauto.
  simpl in H1. simpl in H5.
  eapply perm_map_lemmas_part1.join_join_merge; eauto.
  eapply perm_map_lemmas_part1.join_join_merge; eauto.
Qed.

Ltac mytac :=
  heat; jeauto2.

Ltac mytac_getret_l :=
   match goal with
   | |- _ ==> (_ \\// _ ) => intros; eapply adisj_intro; left
   | |- _ |= _ -> _ |= _ ** _ => try eapply astar_mono; try mytac_getret_l
   | |- _ ==> _ ** _ => try eapply astar_mono; try mytac_getret_l; try eauto
   | _ => idtac
 end.

Ltac mytac_getret_r :=
   match goal with
   | |- _ ==> (_ \\// _ ) => intros; eapply adisj_intro; right
   | |- _ |= _ -> _ |= _ ** _ => try eapply astar_mono; try mytac_getret_r
   | |- _ ==> _ ** _ => try eapply astar_mono; try mytac_getret_r; try eauto
   | _ => idtac
 end.

 Ltac mytac_getret_l' :=
 match goal with
 | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
        eapply r_conseq_rule;
        introv; mytac_getret_l; eauto
 | _ => idtac
 end.

 Ltac mytac_getret_r' :=
 match goal with
 | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
        eapply r_conseq_rule;
        introv; mytac_getret_r; eauto
 | _ => idtac
 end.

Ltac mytac_getret n :=
match n with
| 0%nat => fail
| 1%nat => mytac_getret_l'
| S ?n' => mytac_getret_r'; mytac_getret n'
 end.

Lemma nth_vallist_get_idx:
forall v'3 v'2 v'4,
nth_vallist (length v'3) (v'3 ++ v'2 :: v'4) = Some v'2.
Proof.
induction v'3; intros.
simpl. auto.
simpl.
auto.
Qed.


Theorem cast_rv_tint8_tint32 :
  forall s e v v',
    s |= Rv e @ Tint8 == (Vint32 v) ->
    cast_eval v Tint8 Tint32 = Some v' ->
    s |= Rv (ecast e (Tint32)) @ (Tint32) == (Vint32 v').
Proof.
  intros.
  unfold sat;fold sat.
  destruct_s s.
  simpl in H.
  destructs H.
  splits;auto.
  simpl.
  rewrite H1.
  simpl.
  rewrite H.
  simpl in H0.
  inverts H0.
  auto.
  simpl.
  rewrite H1.
  auto.
Qed.

Lemma ecast_intlemma1: 
forall x, Int.unsigned x <= 65535 ->  (Int.modu x ($ Int16.modulus)) = x.
Proof.
  intros.
  unfold Int.modu.
  unfold Int16.max_unsigned.
  unfold Int16.modulus.
  unfold Int16.wordsize.
  unfold Wordsize_16.wordsize.
  unfold two_power_nat.
  unfold shift_nat.
  simpl.
  repeat ur_rewriter.
  fold Int16.modulus.
  rewrite <- Int16.unsigned_repr_eq.
  assert (0 <= Int.unsigned x <= Int16.max_unsigned).
  change (Int16.max_unsigned) with 65535.
  int auto.
  eapply Int16.unsigned_repr in H0.
  rewrite H0.
  rewrite Int.repr_unsigned. auto.
Qed.

Lemma int_ltu_zero_eq_false:
forall x, Int.ltu x Int.zero = false.
Proof.
intros.
rewrite math_rewrite.Intlt_false_is_Zge.
int auto.
Qed.

Lemma nat_of_Z_eq_succ:
forall n i, ∘ i = S n -> n = ∘ (i - 1).
Proof.
unfold nat_of_Z.
intros.
assert (Z.to_nat (i - 1) = (Z.to_nat i - Z.to_nat 1)%nat).
eapply Z2Nat.inj_sub. auto with zarith.
rewrite H0.
rewrite H.
auto with zarith.
Qed.

Lemma nat_of_Z_eq:
forall n i, ∘ i = n -> 0 <= i -> i = Z.of_nat n.
Proof.
unfold nat_of_Z.
intros.
eapply Z2Nat.id in H0.
subst n.
auto.
Qed.

Lemma list_vallist_split_lem:
  forall semvl: list vallist,
    (semvl <> nil) -> exists vll1 vl vll2, semvl = vll1 ++ vl :: vll2.
Proof.
induction semvl; intros.
false.
destruct semvl.
exists (nil: list vallist).
simpl. eauto.
assert (v :: semvl <> nil ) by eauto.
eapply IHsemvl in H0.
do 3 destruct H0.
rewrite H0.
exists (a :: x : list vallist).
simpl.
eauto.
Qed.

Lemma list_vallist_split_idx:
  forall (semvl: list vallist) i,
    (i < length semvl)%nat ->
    (semvl <> nil) ->
    exists vll1 vl vll2, semvl = vll1 ++ vl :: vll2 /\ length vll1 = i .
Proof.
induction semvl; intros.
false.
destruct semvl.
exists (nil: list vallist).
simpl.
simpl in H.
do 2 eexists. split;eauto.
auto with zarith.
assert (v :: semvl <> nil ) by eauto.
simpl in *.
destruct i.
exists (nil: list vallist).
simpl.
do 2 eexists. splits; eauto.
assert ((i < S (length semvl))%nat) by auto with zarith.
lets He: IHsemvl H2 H1.
destruct He. do 3 destruct H3.
rewrite H3.
exists (a :: x). simpl.
do 2 eexists. splits; eauto.
Qed.

Lemma seminfo_get_lv_pevent:
  forall s b i idx P, 
    0 <= idx < OS_USER_MAX_EVENTS / 3 ->
    s |= GV Sem_info @ sem_info_t ∗ |-> Vptr (b, i) ** 
           LV os_code_defs.pos @ long |-> (V$ idx) **
           A_dom_lenv
           ((value, long)
              :: (sem, (long) ∗)
              :: (os_code_defs.pos, long)
              :: (os_code_defs.x, char_t) :: (y, char_t) :: nil) ** P ->
    s |= Lv efield (Sem_info ′ [os_code_defs.pos ′]) pevent @ OS_EVENT ∗ == 
           (b, (i +ᵢ  $ Z.of_nat (Z.to_nat idx * typelen sem_info_t)) +ᵢ ($ 4 +ᵢ ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  Int.zero)))))))). 
Proof.
introv Hr H.
destruct Hr as (Hr1 & Hr2).
(* do 2 (apply aexists_intro; eexists). *)
destruct_s s.
destruct H. simpljoin. simpl in H0,H2,H3. simpljoin1.
destruct H4. simpljoin. simpl in H1,H3,H4. simpljoin1.
simpl substmo in H5.
simpl. unfold getoff.
simpl.
rewrite H6. rewrite H9.
unfold get in *. unfold EnvMap in *.
destruct H5. simpljoin. destruct H5. simpl in H2,H4,H,H3.
assert (He: EnvMod.get e0 Sem_info = None).
unfold eq_dom_env in H.
eapply EnvMod.nindom_get.
unfold EnvMod.indom.
pure_auto.
destruct H5. destruct x5.
assert (~(exists l, get e0 Sem_info = Some (l, t))).
rewrite <- H.
simpl.
repeat (eapply Classical_Prop.and_not_or; split; [pure_auto | idtac]).
tauto.
pure_auto.
rewrite He.
change (Int.unsigned Int.zero) with 0 in *.
 eapply mapstoval_load in H7.
eapply mapstoval_load in H10.
lets Hle: load_local H0 H7.
lets Hlp': load_local H1 H10.
eapply map_join_comm in H0.
lets Hlp: load_local H0 Hlp'.
rewrite Hle,Hlp.
simpl.
split; auto.
clear -Hr1 Hr2.
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
(* change (OS_USER_MAX_EVENTS / 3) with 6 in Hr2. *)
rewrite Nat2Z.inj_mul.
eapply Z2Nat.id in Hr1.
rewrite Hr1.
assert ($ Int.unsigned (i +ᵢ  Int.mul ($ 60) ($ idx)) = (i +ᵢ  $ idx * Z.of_nat 60)).
int auto.
split; int auto.
rewrite H. auto.
simpl; auto.
simpl; auto.
Qed.

Lemma Info_get_lv_general:
  forall s b i idx P id decls off tp tp1 sid lenv (gident:ident) lident, 
    var_notin_dom gident lenv = true ->
    tp = Tstruct sid decls ->
    ftype id decls = Some tp1 ->
    field_offset id decls = Some off ->
    0 <= idx ->
    idx <= Int.max_signed ->
    Int.min_signed <= Z.of_nat (typelen tp) -> 
    Z.of_nat (typelen tp) <= Int.max_signed -> 
    s |= GV gident @ tp ∗ |-> Vptr (b, i) ** 
      LV lident @ long |-> (V$ idx) **
      A_dom_lenv lenv ** P ->
    s |= Lv efield (gident ′ [lident ′]) id @ tp1 ==
      (b, (i +ᵢ  $ Z.of_nat (Z.to_nat idx * typelen tp)) +ᵢ off).
Proof.
introv Hgl Ht Hid Hoff Hr1 Hr2 Hl1 Hl2 H.
destruct_s s.
destruct H. simpljoin. simpl in H0,H2,H3. simpljoin1.
destruct H4. simpljoin. simpl in H1,H3,H4. simpljoin1.
simpl substmo in H5.
simpl. unfold getoff.
simpl.
rewrite H6. rewrite H9.
unfold get in *. unfold EnvMap in *.
assert (He: EnvMod.get e0 gident = None).
eapply EnvMod.nindom_get.
lets Hs: dom_lenv_imp_notin_lenv Hgl H5.
eapply astar_l_anotinlenv_elim in Hs.
simpl in Hs.
destruct Hs. auto.
rewrite He.
change (Int.unsigned Int.zero) with 0 in *.
eapply mapstoval_load in H7.
eapply mapstoval_load in H10.
lets Hle: load_local H0 H7.
lets Hlp': load_local H1 H10.
eapply map_join_comm in H0.
lets Hlp: load_local H0 Hlp'.
rewrite Hle,Hlp.
rewrite Hoff.
rewrite Hid.
simpl. split; auto.
assert (Hi: Int.unsigned ($ idx) = idx).
change (Int.max_signed) with 2147483647 in Hr2.
int auto.
assert ($ Z.of_nat (Z.to_nat (Int.unsigned ($ idx)) * szstruct decls) =
    Int.mul ($ Z.of_nat (szstruct decls)) ($idx)).
eapply mul_sz_decls; eauto.
rewrite int_ltu_zero_eq_false; auto.
rewrite Hi. auto.
rewrite Hi in H.
rewrite H.
rewrite Int.repr_unsigned. auto.
simpl; auto.
simpl; auto.
Qed.

Lemma struct_rm_update_eq_imp:
  forall s b i decl vl id v vi n,
    good_decllist decl =true -> 
    nth_id n decl = Some id -> nth_val n vl = Some vi -> 
    s |= Astruct_rm (b,i) decl (update_nth_val n vl v) id ->
    s |= Astruct_rm (b,i) decl vl id.
Proof.
  intros.
  generalize dependent s.
  generalize dependent b.
  generalize dependent i.
  generalize dependent vi.
  generalize dependent n.
  generalize dependent vl.
  generalize dependent id.
  generalize dependent v.
  induction decl.
  intros.
  destruct n;tryfalse.
  intros.
  destruct vl.
  destruct n;tryfalse.
  destruct n.
  simpl.
  simpl in H.
  inverts H.
  simpl in H0;inverts H0.
  assert (Zbool.Zeq_bool id id=true).
  apply Zbool.Zeq_is_eq_bool;auto.
  rewrite H.
  simpl in H1.
  inverts H1.
  simpl in H2.
  rewrite H in H2.
  auto.
  simpl.
  assert (Zbool.Zeq_bool id i = false).
  eapply gooddecl_neq;eauto.
  rewrite H3.
  simpl in H2.
  rewrite H3 in H2.
  inverts H0.
  inverts H1.
  destruct t;sep_auto;
  simpl in H;
  apply Bool.andb_true_iff  in H;
  destruct H;
  lets IH: IHdecl H0;clear IHdecl;
  lets IH':IH H5 H4;
  eapply IH' in H2;eauto.
Qed.

Lemma assign_rule_array_struct_aop_general:
  forall Spec I r ri p p' e2 v1 v2 tp1 tp2 aop sc li tid decls sid off n vl vl' gident lident lenv b i idx tp id,  
    p <==>  GV gident @ tp ∗ |-> Vptr (b, i) ** LV lident @ long |-> (V$ idx) **
                    A_dom_lenv lenv ** 
                    Astruct (b, (i +ᵢ  $ Z.of_nat (Z.to_nat idx * typelen tp))) tp vl ** p' ->
    tp = Tstruct sid decls ->
    ftype id decls = Some tp1 ->
    field_offset id decls = Some off ->
    (forall ids dl, tp1 <> Tunion ids dl) ->
    (forall ids dl, tp1 <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), tp1 <> Tarray t'0 n0) ->
    good_decllist decls = true ->
    id_nth id decls = Some n ->
    (n < length vl)%nat ->
    nth_val n vl = Some v1 ->
    update_nth_val n vl v2 =  vl' ->
    assign_type_match tp1 tp2 ->  
    p ==> Lv efield (gident ′ [lident ′]) id @ tp1 == (b, (i +ᵢ  $ Z.of_nat (Z.to_nat idx * typelen tp)) +ᵢ off) ->
    p ==>  Rv e2 @ tp2 == v2 ->
    GV gident @ tp ∗ |-> Vptr (b, i) ** LV lident @ long |-> (V$ idx) ** A_dom_lenv lenv ** 
    Astruct (b, (i +ᵢ  $ Z.of_nat (Z.to_nat idx * typelen tp))) tp vl' ** p' ==>  EX lg, p_local li tid lg ** Atrue 
    ->
    {| Spec, sc, li, I, r, ri |} |-tid 
                                     {{ <|| aop ||> ** p }} 
                                     (sassign (efield (gident ′ [lident ′]) id) e2) 
                                     {{ <|| aop ||> ** GV gident @ tp ∗ |-> Vptr (b, i) ** LV lident @ long |-> (V$ idx) ** A_dom_lenv lenv ** 
                                          Astruct (b, (i +ᵢ  $ Z.of_nat (Z.to_nat idx * typelen tp))) tp vl' ** p'  }}.
Proof.
intros.
rewrite H0.
simpl Astruct.
assert (Hs1: Astruct' (b, i +ᵢ  $ Z.of_nat (Z.to_nat idx * szstruct decls)) decls vl 
                <==> PV (b, (i +ᵢ  $ Z.of_nat (Z.to_nat idx * szstruct decls)) +ᵢ  off) @ tp1 |-> v1 
                            ** Astruct_rm (b, i +ᵢ  $ Z.of_nat (Z.to_nat idx * szstruct decls)) decls vl id).
eapply struct_asrt_eq;eauto.
eapply id_nth_eq;eauto.
assert (Hs2: Astruct' (b, i +ᵢ  $ Z.of_nat (Z.to_nat idx * szstruct decls)) decls vl' 
                <==> PV (b, (i +ᵢ  $ Z.of_nat (Z.to_nat idx * szstruct decls)) +ᵢ  off) @ tp1 |-> v2 
                            ** Astruct_rm (b, i +ᵢ  $ Z.of_nat (Z.to_nat idx * szstruct decls)) decls vl' id).
eapply struct_asrt_eq;eauto.
eapply id_nth_eq;eauto.
rewrite <- H10.
eapply update_nth;eauto.
eapply conseq_rule. eauto.
do 4 (eapply astar_mono; [eauto | idtac]).
eapply astar_mono; [idtac | eauto].
intros.
destruct Hs2 with s.
eapply H17.
eapply H15.
hoare lifts (1:: 5 :: 6 :: nil)%nat post.
eapply assign_rule_general'; eauto.
rewrite H0 in H12.
simpl typelen in H11.
auto.
eapply asrt_eq_trans; eauto.
instantiate (1:= v1).
split; intros; sep pauto; sep cancel A_dom_lenv.
destruct Hs1 with s.
eapply H0 in H15.
clear H0 H10.
sep cancel 1%nat 1%nat.
eapply struct_rm_update_eq; eauto.
eapply id_nth_eq;eauto.
destruct Hs1 with s.
eapply H10.
clear H0 H10.
sep cancel 1%nat 1%nat.
eapply struct_rm_update_eq_imp; eauto.
eapply id_nth_eq;eauto.
intros.
eapply H14.
sep pauto. sep cancel A_dom_lenv.
destruct Hs2 with s.
eapply H10; auto.
Qed.

Lemma assign_rule_array_struct_aop_general':
  forall Spec I r ri p p' e2 v1 v2 tp1 tp2 aop sc li tid decls sid off n vl vl' gident lident lenv b i idx tp id tp',
    tp' = Tint32 \/ tp' = Tint16 \/ tp' = Tint8 ->
    p <==>  GV gident @ tp ∗ |-> Vptr (b, i) ** LV lident @ tp' |-> (V$ idx) **
                    A_dom_lenv lenv ** 
                    Astruct (b, (i +ᵢ  $ Z.of_nat (Z.to_nat idx * typelen tp))) tp vl ** p' ->
    tp = Tstruct sid decls ->
    ftype id decls = Some tp1 ->
    field_offset id decls = Some off ->
    (forall ids dl, tp1 <> Tunion ids dl) ->
    (forall ids dl, tp1 <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), tp1 <> Tarray t'0 n0) ->
    good_decllist decls = true ->
    id_nth id decls = Some n ->
    (n < length vl)%nat ->
    nth_val n vl = Some v1 ->
    update_nth_val n vl v2 =  vl' ->
    assign_type_match tp1 tp2 ->  
    p ==> Lv efield (gident ′ [lident ′]) id @ tp1 == (b, (i +ᵢ  $ Z.of_nat (Z.to_nat idx * typelen tp)) +ᵢ off) ->
    p ==>  Rv e2 @ tp2 == v2 ->
    GV gident @ tp ∗ |-> Vptr (b, i) ** LV lident @ tp' |-> (V$ idx) ** A_dom_lenv lenv ** 
    Astruct (b, (i +ᵢ  $ Z.of_nat (Z.to_nat idx * typelen tp))) tp vl' ** p' ==>  EX lg, p_local li tid lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-tid 
                                     {{ <|| aop ||> ** p }} 
                                     (sassign (efield (gident ′ [lident ′]) id) e2) 
                                     {{ <|| aop ||> ** GV gident @ tp ∗ |-> Vptr (b, i) ** LV lident @ tp' |-> (V$ idx) ** A_dom_lenv lenv ** 
                                          Astruct (b, (i +ᵢ  $ Z.of_nat (Z.to_nat idx * typelen tp))) tp vl' ** p'  }}.
Proof.
introv Hint.
intros.
rewrite H0.
simpl Astruct.
assert (Hs1: Astruct' (b, i +ᵢ  $ Z.of_nat (Z.to_nat idx * szstruct decls)) decls vl 
                <==> PV (b, (i +ᵢ  $ Z.of_nat (Z.to_nat idx * szstruct decls)) +ᵢ  off) @ tp1 |-> v1 
                            ** Astruct_rm (b, i +ᵢ  $ Z.of_nat (Z.to_nat idx * szstruct decls)) decls vl id).
eapply struct_asrt_eq;eauto.
eapply id_nth_eq;eauto.
assert (Hs2: Astruct' (b, i +ᵢ  $ Z.of_nat (Z.to_nat idx * szstruct decls)) decls vl' 
                <==> PV (b, (i +ᵢ  $ Z.of_nat (Z.to_nat idx * szstruct decls)) +ᵢ  off) @ tp1 |-> v2 
                            ** Astruct_rm (b, i +ᵢ  $ Z.of_nat (Z.to_nat idx * szstruct decls)) decls vl' id).
eapply struct_asrt_eq;eauto.
eapply id_nth_eq;eauto.
rewrite <- H10.
eapply update_nth;eauto.
eapply conseq_rule. eauto.
do 4 (eapply astar_mono; [eauto | idtac]).
eapply astar_mono; [idtac | eauto].
intros.
destruct Hs2 with s.
eapply H17.
eapply H15.
hoare lifts (1:: 5 :: 6 :: nil)%nat post.
eapply assign_rule_general'; eauto.
rewrite H0 in H12.
simpl typelen in H12.
auto.
eapply asrt_eq_trans; eauto.
instantiate (1:= v1).
split; intros; sep pauto; sep cancel A_dom_lenv.
destruct Hs1 with s.
eapply H0 in H15.
clear H0 H10.
sep cancel 1%nat 1%nat.
eapply struct_rm_update_eq; eauto.
eapply id_nth_eq;eauto.
destruct Hs1 with s.
eapply H10.
clear H0 H10.
sep cancel 1%nat 1%nat.
eapply struct_rm_update_eq_imp; eauto.
eapply id_nth_eq;eauto.
intros.
eapply H14.
sep pauto. sep cancel A_dom_lenv.
destruct Hs2 with s.
eapply H10; auto.
Qed.


Lemma Info_get_lv_general_int8:
  forall s b i idx P id decls off tp tp1 sid lenv (gident:ident) lident,
    var_notin_dom gident lenv = true ->
    tp = Tstruct sid decls ->
    ftype id decls = Some tp1 ->
    field_offset id decls = Some off ->
    0 <= idx ->
    idx <= Byte.max_unsigned ->
    Byte.min_signed <= Z.of_nat (typelen tp) -> 
    Z.of_nat (typelen tp) <= Byte.max_unsigned -> 
    s |= GV gident @ tp ∗ |-> Vptr (b, i) ** 
      LV lident @ Tint8 |-> (V$ idx) **
      A_dom_lenv lenv ** P ->
    s |= Lv efield (gident ′ [lident ′]) id @ tp1 ==
      (b, (i +ᵢ  $ Z.of_nat (Z.to_nat idx * typelen tp)) +ᵢ off).
Proof.
introv Hgl Ht Hid Hoff Hr1 Hr2 Hl1 Hl2 H.
destruct_s s.
destruct H. simpljoin. simpl in H0,H2,H3. simpljoin1.
destruct H4. simpljoin. simpl in H1,H3,H4. simpljoin1.
simpl substmo in H5.
simpl. unfold getoff.
simpl.
rewrite H6. rewrite H9.
unfold get in *. unfold EnvMap in *.
assert (He: EnvMod.get e0 gident = None).
eapply EnvMod.nindom_get.
lets Hs: dom_lenv_imp_notin_lenv Hgl H5.
eapply astar_l_anotinlenv_elim in Hs.
simpl in Hs.
destruct Hs. auto.
rewrite He.
change (Int.unsigned Int.zero) with 0 in *.
eapply mapstoval_load in H7.
eapply mapstoval_load in H10.
lets Hle: load_local H0 H7.
lets Hlp': load_local H1 H10.
eapply map_join_comm in H0.
lets Hlp: load_local H0 Hlp'.
rewrite Hle,Hlp.
rewrite Hoff.
rewrite Hid.
simpl. split; auto.
assert (Hi: Int.unsigned ($ idx) = idx).
change (Byte.max_unsigned) with 255 in Hr2.
int auto.
assert ($ Z.of_nat (Z.to_nat (Int.unsigned ($ idx)) * szstruct decls) =
    Int.mul ($ Z.of_nat (szstruct decls)) ($idx)).
eapply mul_sz_decls; eauto.
rewrite int_ltu_zero_eq_false; auto.
rewrite Hi. change (Byte.max_unsigned) with 255 in Hr2. clear -Hr2.  int auto.
clear -Hl1.
int_auto.
clear -Hl2.
change (Byte.max_unsigned) with 255 in Hl2.
int_auto. simpl in Hl2.
int_auto.
rewrite Hi in H.
rewrite H.
rewrite Int.repr_unsigned. auto.
simpl.
assert(Int.unsigned ($ idx) <=? Byte.max_unsigned = true).
{
  rewrite int_usign_eq;eauto.
clear -Hr2.
int_auto.
change (Byte.max_unsigned) with 255 in Hr2.
int_auto. 
}
rewrite H. eauto.
simpl; auto.
Qed.

Lemma new_array_type_vallist_match_compose2: 
  forall vll1 vll2 t, 
    new_array_type_vallist_match t vll1 ->
    new_array_type_vallist_match t vll2 ->
    new_array_type_vallist_match t (vll1 ++ vll2).
Proof.
induction vll1; intros.
simpl; auto.
simpl in *.
destruct t; destruct H; split; auto.
Qed.

Lemma new_array_type_vallist_match_compose_struct: 
  forall vll1 vll2 vl t, 
    new_array_type_vallist_match t vll1 ->
    new_array_type_vallist_match t vll2 ->
    struct_type_vallist_match t vl ->
    new_array_type_vallist_match t (vll1 ++ (vl::vll2)).
Proof.
  intros.
  eapply new_array_type_vallist_match_compose2; auto.
  simpl.
  destruct t; simpl in H1; tryfalse.
  simpl; split;auto.
Qed.

(* common *)

Lemma RHL_EINFO_P_get_pevent:
forall vl x vhold,
RHL_EINFO_P vl x vhold ->
exists v, V_OSSINFOPevent vl = Some v.
Proof.
intros.
funfold H.
destruct x as ((eop & tp) & sc).
specialize (H _ _ _ (eq_refl _)).
destructs H.
destruct H0 as [H' | [ H' | H']]; mytac.
Qed.

Lemma EmbMod_get_join_sig_set:
  forall  qls qid a qls1 b,
    EmbMod.join (EmbMod.sig qid b) qls1 qls ->
    EmbMod.get qls1 qid = None ->
    EmbMod.join (EmbMod.sig qid a) qls1 (EmbMod.set qls qid a).
Proof.
  intros.
  unfold EmbMod.join.
  intros.
  rewrite EmbMod.sig_sem.
  rewrite EmbMod.set_sem.
  assert (qid = a0 \/ qid <> a0) by tauto.
  destruct H1.
  subst.
  rewrite EmbMod.beq_refl.
  rewrite H0. auto.
  eapply idxspec.neq_beq_false in H1.
  rewrite H1.
  destruct (EmbMod.get qls1 a0) eqn: eq2.
  lets Htg: EmbMod.join_get_r H  eq2.
  rewrite Htg.
  auto.
  assert (EmbMod.get qls a0 = EmbMod.get qls1 a0).
  eapply EmbMod.map_join_get_none; try eauto.
  rewrite EmbMod.sig_sem.
  rewrite H1. auto.
  rewrite H2. rewrite eq2. auto.
Qed.

Lemma EmbMod_join_get_none_r :
  forall ma mb mc x a, 
    EmbMod.get ma x = Some a -> 
    EmbMod.join ma mb mc -> 
    EmbMod.get mb x = None.
Proof.
  intros.
  unfolds in H0.
  lets adf : H0 x.
  destruct (EmbMod.get ma x).
  destruct (EmbMod.get mb x).
  tryfalse.
  auto.
  destruct (EmbMod.get mb x).
  tryfalse.
  auto.
Qed.

(*move from gjb_mutex_common.v*)
Lemma MibMod_get_join_sig_set:
forall  qls qid a qls1 b,
  MibMod.join (MibMod.sig qid b) qls1 qls ->
  MibMod.get qls1 qid = None ->
  MibMod.join (MibMod.sig qid a) qls1 (MibMod.set qls qid a).
Proof.
  intros.
  unfold MibMod.join.
  intros.
  rewrite MibMod.sig_sem.
  rewrite MibMod.set_sem.
  assert (qid = a0 \/ qid <> a0) by tauto.
  destruct H1.
  subst.
  rewrite MibMod.beq_refl.
  rewrite H0. auto.
  eapply idxspec.neq_beq_false in H1.
  rewrite H1.
  destruct (MibMod.get qls1 a0) eqn: eq2.
  lets Htg: MibMod.join_get_r H  eq2.
  rewrite Htg.
  auto.
  assert (MibMod.get qls a0 = MibMod.get qls1 a0).
  eapply MibMod.map_join_get_none; try eauto.
  rewrite MibMod.sig_sem.
  rewrite H1. auto.
  rewrite H2. rewrite eq2. auto.
Qed.

Lemma MibMod_join_get_none_r :
 forall ma mb mc x a, 
      MibMod.get ma x = Some a -> 
      MibMod.join ma mb mc -> 
      MibMod.get mb x = None.
Proof.
  intros.
  unfolds in H0.
  lets adf : H0 x.
  destruct (MibMod.get ma x).
  destruct (MibMod.get mb x).
  tryfalse.
  auto.
  destruct (MibMod.get mb x).
  tryfalse.
  auto.
Qed.

(* move from gjb_q_common.v *)
Lemma MqattrMod_get_join_sig_set:
  forall  qls qid a qls1 b,
    MqattrMod.join (MqattrMod.sig qid b) qls1 qls ->
    MqattrMod.get qls1 qid = None ->
    MqattrMod.join (MqattrMod.sig qid a) qls1 (MqattrMod.set qls qid a).
Proof.
  intros.
  unfold MqattrMod.join.
  intros.
  rewrite MqattrMod.sig_sem.
  rewrite MqattrMod.set_sem.
  assert (qid = a0 \/ qid <> a0) by tauto.
  destruct H1.
  subst.
  rewrite MqattrMod.beq_refl.
  rewrite H0. auto.
  eapply idxspec.neq_beq_false in H1. 
(*   eapply posspec.neq_beq_false in H1. *)
  rewrite H1.
  destruct (MqattrMod.get qls1 a0) eqn: eq2.
  lets Htg: MqattrMod.join_get_r H  eq2.
  rewrite Htg.
  auto.
  assert (MqattrMod.get qls a0 = MqattrMod.get qls1 a0).
  eapply MqattrMod.map_join_get_none; try eauto.
  rewrite MqattrMod.sig_sem.
  rewrite H1. auto.
  rewrite H2. rewrite eq2. auto.
Qed.

Lemma MqattrMod_join_get_none_r :
  forall ma mb mc x a, 
    MqattrMod.get ma x = Some a -> 
    MqattrMod.join ma mb mc -> 
    MqattrMod.get mb x = None.
Proof.
  intros.
  unfolds in H0.
  lets adf : H0 x.
  destruct (MqattrMod.get ma x).
  destruct (MqattrMod.get mb x).
  tryfalse.
  auto.
  destruct (MqattrMod.get mb x).
  tryfalse.
  auto.
Qed.




Lemma Z_add_le_trans:
  forall a b c,
    0 <= a -> 0 <= b -> a + b <= c -> (a <= c /\ b <= c).
Proof.
intros.
assert (a <= c \/ ~(a <= c)) by tauto.
destruct H2.
split; auto.
auto with zarith.
auto with zarith.
Qed.

Lemma Int8u_not_array_struct:
~ array_struct Int8u.
Proof.
unfold array_struct.
repeat ( try eapply Classical_Prop.and_not_or; split); 
repeat (try eapply Classical_Pred_Type.all_not_not_ex ; intros);
pure_auto.
Qed.

Lemma ecb_neq_vhold
: forall ptbl rtbl tcbls vhold ectrl msgql ecbls n wls pid s P ptls ,
get ecbls pid = Some (abssem n, wls) ->
s |= AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold **
        AECBList ectrl msgql ecbls  tcbls ** HECBList ecbls ** P ->
pid <> vhold.
Proof.
unfold AECBList, AOSTCBPrioTbl.
intros.
sep normal in H0.
destruct H0 as (z & z0 & H0).
sep split in H0.
rename H5 into Hrh_ptls. (* new add *)
assert (pid <> vhold \/ pid = vhold) by tauto.
destruct H5; auto.
false.
subst pid.
lets Hget_ectr: ECBList_P_get_ectr_some H H1.
destruct Hget_ectr as (et & etbl & petbl & Hget_ectr). (* add petbl *)
sep lift 2%nat in H0.
eapply get_ectr_decompose in H0; eauto.
do 6 destruct H0.
sep split in H0.
mytac.
unfold AEventNode in H0.
unfold AOSEvent in H0.
unfold node in H0.
sep normal in H0.
do (* 3 *) 5 destruct H0.
sep split in H0.
mytac.
inverts H6.
lets Hsp: struct_type_vallist_match_os_event H18. (* change H15 -> H18 *)
destruct Hsp. do (* 5  *) 7 destruct H6. subst et.
simpl Astruct in H0.
sep normal in H0.
sep lifts (1 :: 13 :: nil)%nat in H0.
(* sep lifts (1 :: 11 :: nil)%nat in H0. *)
eapply pv_false in H0.
tryfalse.
apply Int8u_not_array_struct.
apply Int8u_not_array_struct.
Qed.

Fixpoint Set_struct' (l: (list (addrval * type * (list val))))(a: addrval) (id : ident ) (b: val)
     :  (list (addrval * type * (list val))):=
  match l with 
  | nil => nil  
  | (ad, t, vl ) :: l' => match (beq_tid ad a) with
                                   | true  =>match t with 
                                                    | Tstruct sid decls =>  match id_nth id decls  with
                                                                                               | None =>  (ad, t, vl ) :: l'
                                                                                               | Some n => ((ad, t, update_nth_val n vl b) :: l')
                                                                                                end
                                                    | _ =>  (ad, t, vl ) :: l'
                                                    end
                                   | false => ((ad, t, vl ) :: (Set_struct' l' a id b))
                                   end
end.  

(* Fixpoint Get_struct (l: (list (addrval * type * (list val))))(a: addrval) :  (option (addrval * type * (list val))) :=
  match l with 
  | nil => None
  | (ad, t, vl ) :: l' => match (beq_tid ad a) with
                                   | true  => Some (a, t, vl )
                                   | false => Get_struct l' a 
                                   end  
end.  
 *)

Lemma AEvStructHeap_unfold: 
  forall s evheap x vl P,
    s |= AEvStructHeap evheap **
            LV attr @ pthread_mutexattr_t ∗ |-> Vptr x ** P->
            Get_struct evheap x = Some (x, pthread_mutexattr_t, vl) ->
    s |= EX evh1 evh2,
                 Astruct x pthread_mutexattr_t vl ** 
                [|struct_type_vallist_match pthread_mutexattr_t vl|] **
                [|R_MutexAttr_P pthread_mutexattr_t vl|] ** (* new add *)
                LV attr @ pthread_mutexattr_t ∗ |-> Vptr x **
                [| evheap =(evh1 ++ (x, pthread_mutexattr_t, vl) :: evh2) |] **
                AEvStructHeap evh1 ** AEvStructHeap evh2 ** 
                [|Get_struct evh1 x = None|] **
                P.
Proof.
  introv Hsat Hget.
(*   sep pauto. *)
  inductions evheap. tryfalse. 
  destruct a. destruct p.
  rename evheap into evheap'.
  destruct t;
  try eapply astar_l_afalse_elim in Hsat;  tryfalse.
  unfold Get_struct in Hget.

  destruct (os_inv.beq_addrval a x) eqn: eq1.
  eexists. instantiate (1:= nil).
  exists evheap'.
  sep normal in Hsat.
  change (nil ++ (x, pthread_mutexattr_t, vl) :: evheap') with ((x, pthread_mutexattr_t, vl) :: evheap').

    sep pauto.
  eapply beq_tid_true_eq in eq1.
  inverts Hget.
  fold AEvStructHeap in Hsat.
  sep pauto.
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  sep pauto.
  inverts Hget. 
  eapply beq_tid_true_eq in eq1. subst a.
  auto. 
  (* new add about R_MutexAttr_P *)
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  inverts Hget. sep pauto.
  (* end of new add *)
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  inverts Hget. sep pauto.
  fold Get_struct in Hget.
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  sep normal in Hsat.
  sep lifts (4::5::nil)%nat in Hsat.
(*   sep lifts (3::4::nil)%nat in Hsat. *)
  eapply IHevheap in Hsat; eauto.
  sep pauto.
  3:{
  change((a, STRUCT i ­{ d }­, l) :: ( x0 ++ (x, pthread_mutexattr_t, vl) :: x1)) with
 (((a, STRUCT i ­{ d }­, l) :: x0 ) ++ (x, pthread_mutexattr_t, vl) :: x1).
  eauto. }
  simpl AEvStructHeap at 1.
  sep pauto.
  unfold Get_struct; fold Get_struct.
  rewrite eq1, H2. (* change H1 into H2 *)
  auto.
Qed.

Lemma AEvStructHeap_succ_imp_alt :
  forall s a vll P, 
    s |= AEvStructHeap (a :: vll) ** P ->
    s |= AEvStructHeap (a::nil) ** AEvStructHeap vll ** P.
Proof.
  intros.
  sep pauto.
  simpl AEvStructHeap in *;
  destruct a. destruct p. destruct t;
  try(eapply astar_l_afalse_intro; sep pauto).
  sep pauto.
 Qed.

Lemma AEvStructHeap_succ :
  forall s a vll, 
    s |= AEvStructHeap (a::nil) ** AEvStructHeap vll -> 
    s |= AEvStructHeap (a :: vll).
Proof.
  intros.
  simpl AEvStructHeap in *;
  destruct a. destruct p. destruct t;
  try(eapply astar_l_afalse_elim in H; sep pauto).
  sep pauto.
Qed.

Lemma AEvStructHeap_compose :
  forall vll1 vll2 s, 
    s |= AEvStructHeap vll1 ** AEvStructHeap vll2 -> 
    s |= AEvStructHeap (vll1 ++ vll2).
Proof.
  induction vll1; intros.
  simpl AEvStructHeap in H.
  sep pauto.
  eapply AEvStructHeap_succ_imp_alt in H.
  change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)).
  eapply AEvStructHeap_succ.
  sep pauto.
Qed.

Lemma AEvStructHeap_fold: 
  forall s x evheap P,
     s |= EX   vl evh1 evh2,
                Astruct x pthread_mutexattr_t vl ** 
                [|struct_type_vallist_match pthread_mutexattr_t vl|] **
                [|R_MutexAttr_P pthread_mutexattr_t vl|] ** (* new add *)
                LV attr @ pthread_mutexattr_t ∗ |-> Vptr x **
                [| evheap =(evh1 ++ (x, pthread_mutexattr_t, vl) :: evh2) |] **
                AEvStructHeap evh1 ** AEvStructHeap evh2 ** P->
    s |=    AEvStructHeap evheap **
               LV attr @ pthread_mutexattr_t ∗ |-> Vptr x ** P.
Proof.
  intros.
  unfold AEvStructHeap.
  sep pauto.
  fold AEvStructHeap.
  apply AEvStructHeap_compose.
  sep pauto.
  unfold AEvStructHeap.
  fold AEvStructHeap.
  destruct pthread_mutexattr_t; tryfalse.
  sep pauto.
Qed.

Lemma struct_type_vallist_match_muxattr_hold:
forall vl v n,
 ( n< length vl )%nat ->
struct_type_vallist_match pthread_mutexattr_t vl->
struct_type_vallist_match pthread_mutexattr_t
  (update_nth_val n vl (Vint32 v)).
Proof. 
  intros.
  lets Hsp: struct_type_vallist_match_elim_7 H0.
  destruct Hsp.
  do (* 8 *) 6 destruct  H1.
  substs. 
  simpl in *.
  mytac.
  do (* 9 *) 7 (try destruct n); simpl; try splits; eauto.
Qed.

Lemma llsegevaux_tcbvl_tcb_linked_list_same_next_preserve:
  forall vll tcbh tn vll' locmp ptrmp s P, 
    s |= llsegevaux tcbh tn vll locmp ptrmp V_OSTCBNext ** P ->
    tcb_linked_list_same_next vll vll' -> 
    s |= llsegevaux tcbh tn vll' locmp ptrmp V_OSTCBNext ** P.   
Proof.
  inductions vll.
  intros.
  unfold llsegevaux in H.
  sep split in H.
  simpljoin1.
  unfold tcb_linked_list_same_next in H0.
  destruct vll'.
  unfold llsegevaux.
  sep split; eauto.
  tryfalse.

  introv Hsat Hsamenext.
  unfold llsegevaux in Hsat.
  fold llsegevaux in Hsat. 
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  destruct vll'. simpl in Hsamenext. tryfalse.
  simpl in Hsamenext.
  rewrite H0 in Hsamenext.
  destruct (V_OSTCBNext v) eqn: E.
  2: tryfalse.
  simpljoin1.
  unfold llsegevaux. fold llsegevaux.
  sep pauto.
  sep cancel evaux_node.
  eapply astar_r_aemp_elim; eauto. 
  eapply IHvll; eauto.
  sep cancel llsegevaux.
  auto.
  auto.
  auto.
  auto.
Qed.   

Lemma tcbllsegevaux_tcbvl_tcb_linked_list_same_next_preserve: 
  forall tcblh tcbvl tcbvl' locmp ptrmp s P, 
    s |= tcbllsegevaux tcblh tcbvl locmp ptrmp ** P ->
    tcb_linked_list_same_next tcbvl tcbvl' -> 
    s |= tcbllsegevaux tcblh tcbvl' locmp ptrmp ** P. 
Proof.
  introv Hsat Hsn.
  unfold tcbllsegevaux in *.
  eapply llsegevaux_tcbvl_tcb_linked_list_same_next_preserve; eauto.
Qed.

Lemma tcb_linked_list_same_next_self:
  forall vll v rtbl tcbls, 
    TCBList_P v vll rtbl tcbls -> 
    tcb_linked_list_same_next vll vll. 
Proof.
  inductions vll.
  simpl. auto.
  introv Htlp.
  unfold TCBList_P in Htlp.
  fold TCBList_P in Htlp.
  simpljoin1.
  unfold tcb_linked_list_same_next.
  fold tcb_linked_list_same_next.
  rewrite H0. 
  splits; auto.
  eapply IHvll; eauto. 
Qed. 

Lemma tcb_linked_list_same_next_mid: 
  forall vll1 vll2 vnxt vprev veptr vmsg vdly vstat vprio vx vy vbx vby
         vprev' veptr' vmsg' vdly' vstat' vprio' vx' vy' vbx' vby'
         v rtbl tcbls,
    TCBList_P v
              (vll1 ++ ((vnxt :: vprev :: veptr :: vmsg :: vdly :: vstat :: vprio :: vx :: vy :: vbx :: vby) :: vll2))
              rtbl tcbls -> 
    tcb_linked_list_same_next
      (vll1 ++ ((vnxt :: vprev :: veptr :: vmsg :: vdly :: vstat :: vprio :: vx :: vy :: vbx :: vby) :: vll2))
      (vll1 ++ ((vnxt :: vprev' :: veptr' :: vmsg' :: vdly' :: vstat' :: vprio' :: vx' :: vy' :: vbx' :: vby') :: vll2)). 
Proof.
  inductions vll1.
  intros.
  do 2 rewrite app_nil_l.
  unfold tcb_linked_list_same_next.
  fold tcb_linked_list_same_next.
  unfold V_OSTCBNext.
  simpl nth_val.
  simpl.
  splits; auto.
  rewrite app_nil_l in H.
  unfold TCBList_P in H.
  fold TCBList_P in H.
  simpljoin1. 
  eapply tcb_linked_list_same_next_self; eauto.
  
  introv Htlp.
  change ((a :: vll1) ++
                      (vnxt :: vprev :: veptr :: vmsg :: vdly :: vstat :: vprio :: vx :: vy :: vbx :: vby) :: vll2) with
      (a :: (vll1 ++ (vnxt :: vprev :: veptr :: vmsg :: vdly :: vstat :: vprio :: vx :: vy :: vbx :: vby) :: vll2))
    in Htlp.
  change ((a :: vll1) ++
                      (vnxt :: vprev :: veptr :: vmsg :: vdly :: vstat :: vprio :: vx :: vy :: vbx :: vby) :: vll2) with
      (a :: (vll1 ++ (vnxt :: vprev :: veptr :: vmsg :: vdly :: vstat :: vprio :: vx :: vy :: vbx :: vby) :: vll2)).
  change ((a :: vll1) ++
                      (vnxt :: vprev' :: veptr' :: vmsg' :: vdly' :: vstat' :: vprio' :: vx' :: vy' :: vbx' :: vby') :: vll2) with
      (a :: (vll1 ++ (vnxt :: vprev' :: veptr' :: vmsg' :: vdly' :: vstat' :: vprio' :: vx' :: vy' :: vbx' :: vby') :: vll2)).
  unfold tcb_linked_list_same_next.
  fold tcb_linked_list_same_next.
  unfold TCBList_P in Htlp.
  fold TCBList_P in Htlp.
  simpljoin1.
  rewrite H0.
  splits; auto.
  eapply IHvll1; eauto. 
Qed.

Lemma evtinv_set_tcbvl_mid_preserve:
  forall v rtbl tcbls vll1 vll2 els vhold tcblh 
         scapl mcapl qcapl
         vnxt vprev veptr vmsg vdly vstat vprio vx vy vbx vby
         vprev' veptr' vmsg' vdly' vstat' vprio' vx' vy' vbx' vby'
         s P tcbls',  
    TCBList_P v
              (vll1 ++ ((vnxt :: vprev :: veptr :: vmsg :: vdly :: vstat :: vprio :: vx :: vy :: vbx :: vby) :: vll2))
              rtbl tcbls -> 
    s |= EvtInv  els tcblh (vll1 ++ ((vnxt :: vprev :: veptr :: vmsg :: vdly :: vstat :: vprio :: vx :: vy :: vbx :: vby) :: vll2)) tcbls' vhold scapl mcapl qcapl
             ** P ->
    s |= EvtInv els tcblh (vll1 ++ ((vnxt :: vprev' :: veptr' :: vmsg' :: vdly' :: vstat' :: vprio' :: vx' :: vy' :: vbx' :: vby') :: vll2)) tcbls' vhold scapl mcapl qcapl
            ** P.  
Proof.
  introv Htlp Hsat.
  unfold EvtInv in *.
  sep pauto; eauto.
  sep cancel AOSEventFreeList.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AECBList.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  apply astar_r_aemp_elim.
  eapply tcbllsegevaux_tcbvl_tcb_linked_list_same_next_preserve; eauto. 
  sep cancel tcbllsegevaux.
  auto.
  eapply tcb_linked_list_same_next_mid; eauto. 
Qed.

Lemma tcb_linked_list_same_next_split:
forall vl1 vl1' vl2 vl2',
    tcb_linked_list_same_next vl1 vl1' ->
    tcb_linked_list_same_next vl2 vl2' ->
    tcb_linked_list_same_next (vl1 ++ vl2) (vl1' ++ vl2').
Proof.
induction vl1; induction vl1'; intros.
simpl; auto.
simpl in *. tryfalse.
simpl in *. tryfalse.
simpl.
simpl in H.
destruct (V_OSTCBNext a) eqn: eq1;
destruct (V_OSTCBNext a0) eqn: eq2;
tryfalse.
destruct H.
subst.
split; auto.
Qed.

(* used for create sem/mutex/mq  *)

Lemma sum_int_31:
     ($ 1 +ᵢ
     ($ 4 +ᵢ 
      ($ 1 +ᵢ
       ($ 1 +ᵢ
        ($ 1 +ᵢ
         ($ 1 +ᵢ
          ($ 1 +ᵢ
           ($ 1 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ ($ 4 +ᵢ Int.zero)))))))))))))) = $31. 
Proof.
  asserts_rewrite ($ 4 +ᵢ  Int.zero = $4). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 4 = $8). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 8 = $12). int auto.
   asserts_rewrite ($ 4 +ᵢ  $ 12 = $16). int auto.
  asserts_rewrite ($ 2 +ᵢ  $ 16 = $18). int auto.
  asserts_rewrite ($ 2 +ᵢ  $ 18 = $20). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 20 = $21). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 21 = $22). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 22 = $23). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 23 = $24). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 24 = $25). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 25 = $26). int auto.
   asserts_rewrite ($ 4 +ᵢ  $ 26 = $30). int auto.
  int auto.
Qed.

Lemma sum_int_30:
($ 4 +ᵢ 
  ($ 1 +ᵢ
     ($ 1 +ᵢ
      ($ 1 +ᵢ
       ($ 1 +ᵢ
        ($ 1 +ᵢ
         ($ 1 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  Int.zero))))))))))))) = $30. 
Proof.
  asserts_rewrite ($ 4 +ᵢ  Int.zero = $4). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 4 = $8). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 8 = $12). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 12 = $16). int auto.
  asserts_rewrite ($ 2 +ᵢ  $ 16 = $18). int auto.
  asserts_rewrite ($ 2 +ᵢ  $ 18 = $20). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 20 = $21). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 21 = $22). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 22 = $23). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 23 = $24). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 24 = $25). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 25 = $26). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 26 = $30). int auto.
  auto.
Qed.

Lemma RH_SEM_EINFO_ECB_P_semcre_preserve: 
  forall ecbls sid embls absem, 
    get ecbls sid = None -> 
    RH_SEM_EINFO_ECB_P ecbls embls -> 
    RH_SEM_EINFO_ECB_P (set ecbls sid absem) embls.  
Proof.
  introv Hnone Hrh.
  unfold RH_SEM_EINFO_ECB_P in *.
  introv Hget.
  apply Hrh in Hget.
  assert (eid = sid \/ eid <> sid) by tauto.
  destruct H.
  subst.
  unfold get in Hnone, Hget.
  unfold EcbMap in Hnone, Hget.
  rewrite Hnone in Hget.
  simpljoin1. tryfalse.
  rewrite set_a_get_a'; eauto.
Qed.   

Lemma ASemEIBs_set_els_preserve: 
  forall s ecbls sid infol scapl embls vhold absem, 
    get ecbls sid = None -> 
    s |= ASemEIBs infol scapl embls ecbls vhold -> 
    s |= ASemEIBs infol scapl embls (set ecbls sid absem) vhold. 
Proof.
  introv Hnone Haei.
  unfold ASemEIBs in *.
  sep destruct Haei.
  eexists.
  
  sep split in Haei.
  sep split; auto.
  sep pauto.
  eapply RH_SEM_EINFO_ECB_P_semcre_preserve; eauto.
Qed. 

Lemma RH_ECBlk_EIBlk_Mux_P_semcre_preserve: 
  forall muxeibs ecbls sid absem, 
    get ecbls sid = None -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs (set ecbls sid absem).  
Proof.
  introv Hnone Hrh.
  unfold RH_ECBlk_EIBlk_Mux_P in *.
  introv Hget Htp.
  lets H00: Hrh Hget Htp.
  assert (Hor: sid = eid \/ sid <> eid) by tauto.
  destruct Hor.
  subst.
  rewrite Hnone in H00.
  simpljoin1. tryfalse.
  rewrite set_a_get_a'; eauto. 
Qed.

Lemma AMuxEIBs_set_els_preserve:
  forall s ecbls sid minfol mcapl muxeibs vhold absem, 
    get ecbls sid = None -> 
    s |= AMuxEIBs minfol mcapl muxeibs ecbls vhold -> 
    s |= AMuxEIBs minfol mcapl muxeibs (set ecbls sid absem) vhold.  
Proof.
  introv Hnone Haeiba.
  unfold AMuxEIBs in *.
  destruct Haeiba.
  eexists.
  sep split in H.

  sep split; auto.
  sep pauto.
  eapply RH_ECBlk_EIBlk_Mux_P_semcre_preserve; eauto.
Qed.  

Lemma RH_EIBlk_ECBlk_Q_P_preserve: 
  forall ecbls sid qeibs absem, 
    get ecbls sid = None -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    RH_EIBlk_ECBlk_Q_P (set ecbls sid absem) qeibs.  
Proof.
  introv Hnone Hrh.
  unfold RH_EIBlk_ECBlk_Q_P in *.
  introv Hget.
  apply Hrh in Hget.
  assert (Hor: sid = eid \/ sid <> eid) by tauto.
  destruct Hor.
  subst.
  rewrite Hnone in Hget.
  simpljoin1. tryfalse.
  rewrite set_a_get_a'; eauto.
Qed.

Lemma AMqEIBs_set_els_preserve: 
  forall s ecbls sid qattrl qcapl qeibs vhold absem, 
    get ecbls sid = None -> 
    s |= AMqEIBs qattrl qcapl qeibs ecbls vhold -> 
    s |= AMqEIBs qattrl qcapl qeibs (set ecbls sid absem) vhold.  
Proof.
  introv Hnone Hsat.
  unfold AMqEIBs in *.
  sep destruct Hsat.
  eexists.
  sep split in Hsat.
  sep split; auto.
  sep pauto.
  eapply RH_EIBlk_ECBlk_Q_P_preserve; eauto.
Qed. 

Lemma update_nth_val_eq_same:
forall vl n x,
nth_val' n vl = x ->
update_nth_val n vl x = vl.
Proof.
induction vl.
simpl.
auto.
intros.
simpl.
destruct n.
simpl in *.
subst; auto.
simpl in *.
eapply IHvl in H.
rewrite H; auto.
Qed.

Lemma update_nth_val_eq_same_doble:
forall vl n x y,
nth_val' n vl = x ->
update_nth_val n (update_nth_val n vl y) x = vl.
Proof.
induction vl.
simpl.
auto.
intros.
simpl.
destruct n.
simpl in *.
subst; auto.
simpl in *.
eapply IHvl in H.
rewrite H; auto.
Qed.

Lemma RHL_PrioTbl_P_ex_nth:
forall i vhold_addr ptbl ptls,
  0 <= Int.unsigned i < 64 ->
  RHL_PrioTbl_P ptbl ptls vhold_addr ->
  exists v, nth_val (Z.to_nat (Int.unsigned i)) ptbl = Some v /\ isptr v.
Proof.
intros.
destruct (get ptls i) eqn: eq1;
try destruct e;
eapply H0 in eq1; tryfalse;
simpljoin1;
unfold isptr; eauto.
Qed.

(* copy from OSMutexCommon.v *)
Lemma neq_imp_neqq :
  forall x y,
    x <> y  -> 
    Z.to_nat (Int.unsigned x) <>  (Z.to_nat (Int.unsigned y)).
Proof.
  intros.
  introv Hf.
  apply H.
  lets Heqx :  Z2Nat.inj Hf;
    try
      eapply Int.unsigned_range; eauto.
  eapply unsigned_inj; auto.
Qed.
(* end copy *)

Lemma RH_PrioTbl_P_update_vhold:
forall i vhold_addr ptbl ptls,
  0 <= Int.unsigned i < 64 ->
  RH_PrioTbl_P ptbl ptls vhold_addr ->
  RH_PrioTbl_P
  (update_nth_val (Z.to_nat (Int.unsigned i)) ptbl (Vptr vhold_addr))
  (set ptls i Holder) vhold_addr.
Proof.
intros.
funfold H0.
unfolds.
split; unfolds; [funfold H0 | idtac];
splits; introv Hp; try introv Hnth; try introv Hneq; rewrite PtbMod.set_sem in *;
destruct (idxspec.beq i prio) eqn: eq1; auto;
try (eapply idxspec.beq_true_eq in eq1; subst);
try eapply idxspec.beq_false_neq in eq1;
try (eapply nth_upd_eq in Hnth; tryfalse);
try (eapply nth_upd_neq in Hnth; try eapply neq_imp_neqq; eauto);
try (false; eapply Hp; split; auto);
try eapply H1 in Hp; tryfalse;
simpljoin1; splits; auto.
eapply nth_upd_neqrev; try eapply neq_imp_neqq; eauto.
eapply RHL_PrioTbl_P_ex_nth in H1; eauto.
simpljoin1.
eapply update_nth; eauto.
eapply nth_upd_neqrev; try eapply neq_imp_neqq; eauto.
eapply nth_upd_neqrev; try eapply neq_imp_neqq; eauto.
Qed.

Lemma priotbl_null_no_tcb' :
forall v'5 v'14 v'17 i,
   R_PrioTbl_P v'5 v'14 v'17 ->
   nth_val (Z.to_nat (Int.unsigned i)) v'5 = Some (Vptr v'17) ->
 (~ exists x st msg sus, TcbMod.get v'14 x = Some ( i, st, msg, sus)).
Proof.
  intros.
  unfolds in H.
  destruct H as (H & H' & H'').
  intro.
  destruct H1 as (tid & st & msg & sus & Hget).
  lets aaa: H' Hget.
  destruct aaa as (Hnth & Hneq).
  unfold nat_of_Z in Hnth.
  rewrite H0 in Hnth; inverts Hnth.
  tryfalse.
Qed.

Lemma RH_ECBlk_EIBlk_Mux_P_null_preserve:
  forall ecbls muxeibs  pos ow tp rcnt prot prioc wq cnsa mc, 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls ->
    RH_ECBlk_EIBlk_Mux_P (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) ecbls.
Proof.
  intros.
  unfold RH_ECBlk_EIBlk_Mux_P in *.
  introv Hget He.
  casetac pos pos0 Ht Hf.
  subst.
  rewrite set_a_get_a in Hget. inverts Hget.
  rewrite set_a_get_a' in Hget; eauto. 
Qed.

Lemma RH_ECBlk_EIBlk_Mux_P_ptr_preserve:
  forall ecbls muxeibs  pos ow tp rcnt prot prioc wq cnsa mc eid, 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls ->
    is_mux ecbls eid -> 
    RH_ECBlk_EIBlk_Mux_P (set muxeibs pos (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) ecbls. 
Proof.
  introv Hrh Hmux.
  unfold RH_ECBlk_EIBlk_Mux_P in *.
  introv Hget He.
  casetac pos pos0 Heq Hne.
  subst.
  rewrite set_a_get_a in Hget. inverts Hget.
  unfold is_mux in Hmux. eauto.
  rewrite set_a_get_a' in Hget; eauto.
Qed.   

Lemma RH_ECBlk_EIBlk_Mux_P_set_preserve_gen:
forall embls els pos ei o z n pro pip w c o' z' n' pro' pip' w' c' mc mc',
  get embls pos = Some (ei, o, z, n, pro, pip, w, c, mc) ->
  RH_ECBlk_EIBlk_Mux_P embls els ->
  RH_ECBlk_EIBlk_Mux_P (set embls pos (ei, o', z', n', pro', pip', w', c', mc')) els.
Proof.
introv Hget Hrh.
unfold RH_ECBlk_EIBlk_Mux_P in *.
introv Hget' Hed.
casetac pos pos0 Heq Hneq.
subst.
rewrite set_a_get_a in Hget'.
inverts Hget'.
eapply Hrh; eauto.
rewrite set_a_get_a' in Hget'; eauto.
Qed.

Lemma Get_struct_some_eq:
forall evheap addr a t vl,
Get_struct evheap addr = Some (a, t , vl) ->
a = addr.
Proof.
induction evheap; simpl; intros.
tryfalse.
destruct a.
destruct p.
destruct (os_inv.beq_addrval a addr) eqn: eq1.
eapply OSTimeTickPure.beq_tid_true_eq in eq1; subst.
inverts H; auto.
eapply IHevheap; eauto.
Qed.

(* used for destroy *)

Lemma pos_rgn_ok_impl: 
  forall x, 
    (
      (val_inj
         (bool_or
            (val_inj
               (if Int.ltu x ($ 0)
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))
            (val_inj
               (bool_or
                  (val_inj
                     (if Int.ltu (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) x
                      then Some (Vint32 Int.one)
                      else Some (Vint32 Int.zero)))
                  (val_inj
                     (if Int.eq x (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))
                      then Some (Vint32 Int.one)
                      else Some (Vint32 Int.zero)))))) = 
       Vint32 Int.zero) \/
      (val_inj
         (bool_or
            (val_inj
               (if Int.ltu x ($ 0)
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))
            (val_inj
               (bool_or
                  (val_inj
                     (if Int.ltu (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) x
                      then Some (Vint32 Int.one)
                      else Some (Vint32 Int.zero)))
                  (val_inj
                     (if Int.eq x (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))
                      then Some (Vint32 Int.one)
                      else Some (Vint32 Int.zero)))))) = Vnull)
    ) -> 
    (Int.eq x ($0) = true \/ Int.ltu ($0) x = true) /\ Int.ltu x (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) = true.  
Proof.
  introv H00. 
  destruct H00.
    2: {
      destruct (Int.ltu x ($ 0));
      destruct (Int.ltu (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) x);
      destruct (Int.eq x (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))).
      simpl in H.
      change ( Int.ltu Int.zero Int.one || Int.ltu Int.zero Int.one) with true in H.
      simpl in H.
      change ( Int.ltu Int.zero Int.one || Int.ltu Int.zero Int.one) with true in H.
      simpl in H. inverts H.
      simpl in H. 
      change ( Int.ltu Int.zero Int.one || Int.ltu Int.zero Int.zero) with true in H.
      simpl in H.
      change ( Int.ltu Int.zero Int.one || Int.ltu Int.zero Int.one) with true in H.
      simpl in H.
      inverts H.
      simpl in H. 
      change ( Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.one) with true in H.
      simpl in H.
      change ( Int.ltu Int.zero Int.one || Int.ltu Int.zero Int.one) with true in H.
      simpl in H.
      inverts H.
      simpl in H. 
      change ( Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.zero) with false in H.
      simpl in H.
      change ( Int.ltu Int.zero Int.one || Int.ltu Int.zero Int.zero) with true in H.
      simpl in H.
      inverts H.
      simpl in H. 
      change ( Int.ltu Int.zero Int.one || Int.ltu Int.zero Int.one) with true in H.
      simpl in H.
      change ( Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.one) with true in H.
      simpl in H.
      inverts H.
      simpl in H. 
      change ( Int.ltu Int.zero Int.one || Int.ltu Int.zero Int.zero) with true in H.
      simpl in H.
      change ( Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.one) with true in H.
      simpl in H.
      inverts H.
      simpl in H. 
      change ( Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.one) with true in H.
      simpl in H.
      change ( Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.one) with true in H.
      simpl in H.
      inverts H.
      simpl in H. 
      change ( Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.zero) with false in H.
      simpl in H.
      change ( Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.zero) with false in H.
      simpl in H.
      inverts H.
    }
    simpl in H. 
    destruct (Int.ltu x ($ 0)) eqn: E1; 
      destruct (Int.ltu (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) x) eqn: E2;
      destruct (Int.eq x (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))) eqn: E3; 
      (* change (Int.divs ($ 20) ($ 3)) with ($6) in E2, E3; *) 
      lets Hrgn: usr_max_evts_rgn;
      destruct Hrgn as (Hrgn3 & Hrgn4).
      (* change (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) with ($6) in H. *)
    apply ltu_eq_false in E2. tryfalse.
    lets Hf: int_lt_gt_false E1 E2. inv Hf.
    lets Hf: int_lt_eq_false E1 E3. inv Hf.
    2: { apply ltu_eq_false in E2. tryfalse. }
    pure_auto_try_false.
    pure_auto_try_false.
    pure_auto_try_false. 
    clear -E1 E2 E3.
    rewrite Intlt_false_is_Zge in E1.
    rewrite Intlt_false_is_Zge in E2.
    apply Inteq_false_is_Zneq in E3.
    split.
    clear -E1.
    int auto.
    eapply Intlt_true_is_Zlt; eauto.
    clear -E2 E3.
    auto with zarith.
Qed. 

(* Lemma struct_type_vallist_match_sem_info_t_vl:
  forall vl, 
    struct_type_vallist_match sem_info_t vl ->
    exists v0 v1 v2 v3 v4 v5 v6 v7,
      vl = v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: nil.
Proof. *)

Lemma struct_type_vallist_match_sem_info_t_vl:
  forall vl, 
    struct_type_vallist_match sem_info_t vl ->
    exists v0 v1 v2 v3 v4 v5 v6 v7 v8,
      vl = v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: nil.
Proof.
  introv Hsmt.
  destruct vl.
  simpl in Hsmt. tryfalse.
  simpl in Hsmt.
  simpl in Hsmt.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl. 
  simpl in H0. tryfalse.
  destruct vl. simpl in H0. 
  repeat eexists.
  simpl in H0. simpljoin1. tryfalse.
Qed.

Lemma struct_type_vallist_match_sem_info_t_ptr:
  forall vl, 
  struct_type_vallist_match sem_info_t vl ->
  isptr (nth_val' 7 vl).
Proof.
  introv Hsmt.
  destruct vl.
  simpl in Hsmt. tryfalse.
  simpl in Hsmt.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  destruct v6; simpl in H0; simpljoin1; tryfalse.
  simpl. unfold isptr. auto.
  simpl. unfold isptr. right. eexists; eauto.
Qed.

Lemma evsllseg_aux:
  forall l1 s a b l2 P,
    s |= evsllseg a b l1 l2 ** P ->
    (a = b /\ l1 = nil \/ get_last_ptr l1 = Some b) /\ length l1 = length l2.
Proof.
  inductions l1.
  intros.
  simpl in H.
  mytac.
  swallow.
  left.
  auto.
  auto.
  intros.
  unfold evsllseg in H.
  fold evsllseg in H.
  destruct l2.
  simpl in H.
  mytac; tryfalse.
  destruct a.
  destruct p. (* new add *)
  sep normal in H.
  sep destruct H.
  sep lift 3%nat in H.
  lets Hxax: IHl1 H.
  mytac.
  swallow.
  2: simpl; auto.
  destruct H0.
  mytac.
  right.
  unfolds.
  simpl.
  sep split in H.
  auto.
  right.
  unfolds.
  simpl.
  destruct l1.
  unfolds in H0.
  simpl in H0.
  unfolds in H0.
  unfold nth_val in H0.
  tryfalse.
  simpl.
  auto.
Qed.

(* from certiucos/proof/task/taskdelete.v *)
Lemma ecblistp_evsllseg_tlsame:
  forall ls1 hd tl tl' ls2 hls tcbls P s,
       ECBList_P hd tl ls1 ls2 hls tcbls ->
       s |= evsllseg hd tl' ls1 ls2 ** P ->
       tl  = tl'.
Proof.
  induction ls1.
  intros.
  simpl in H.
  simpljoin.
  unfold evsllseg in H0.
  sep split in H0.
  tauto.
  intros.
  unfold1 ECBList_P in H.
  simpljoin.
  destruct ls2; tryfalse.
  destruct a; simpljoin.
  rename H2 into Hpetbl; rename H3 into H2. (* new add *)
  destruct p; simpljoin. (* new add *)
  unfold1 evsllseg in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0.
  rewrite H in H5.
  inverts H5.
  eapply IHls1.
  eauto.
  sep lift 2%nat in H0.
  eauto.
Qed.

Goal forall ls x, (x< length ls)%nat -> exists t, nth_val x ls = Some t.
Proof.
  intro.
  induction ls.
  intros.
  inversion H.
  intro.
  induction x.
  intros.
  simpl.
  eauto.
  intros.
  simpl.
  apply IHls.
  simpl in H.
  lia.
Save ls_has_nth_val.

Lemma int_ltu_prop:
  forall x y, Int.ltu x y = false ->
              x <> y ->
              Int.ltu y x = true.
Proof.
  intros.
  int auto.
  false.
  apply H0.
  assert (Int.unsigned x = Int.unsigned y) by lia.
  eapply unsigned_inj; eauto.
Qed.

(* end of copy *)

Lemma RH_PrioTbl_P_update_null:
forall i vhold_addr ptbl ptls,
  0 <= Int.unsigned i < 64 ->
  RH_PrioTbl_P ptbl ptls vhold_addr ->
  RH_PrioTbl_P
  (update_nth_val (Z.to_nat (Int.unsigned i)) ptbl Vnull)
  (set ptls i Null) vhold_addr.
Proof.
intros.
funfold H0.
unfolds.
split; unfolds; [funfold H0 | idtac];
splits; introv Hp; try introv Hnth; try introv Hneq; rewrite PtbMod.set_sem in *;
destruct (idxspec.beq i prio) eqn: eq1; auto;
try (eapply idxspec.beq_true_eq in eq1; subst);
 try eapply PtbMod.beq_sym in eq1;
try eapply idxspec.beq_false_neq in eq1;
try (eapply nth_upd_eq in Hnth; tryfalse);
try (eapply nth_upd_neq in Hnth; try eapply neq_imp_neqq; eauto);
try (false; eapply Hp; split; auto);
try eapply H1 in Hp; tryfalse;
simpljoin1; try splits; auto.
eapply RHL_PrioTbl_P_ex_nth in H1; eauto.
simpljoin1.
eapply update_nth; eauto.
eapply nth_upd_neqrev; try eapply neq_imp_neqq; eauto.
eapply nth_upd_neqrev; try eapply neq_imp_neqq; eauto.
eapply nth_upd_neqrev; try eapply neq_imp_neqq; eauto.
Qed.


Lemma RH_PrioTbl_P_prio_available:
forall pip vhold_addr ptbl ptls tls,
  RH_PrioTbl_P ptbl ptls vhold_addr ->
  get ptls pip = Some Holder ->
  R_PrioTbl_P ptbl tls vhold_addr ->
  prio_available pip tls.
Proof.
 intros.
 eapply H in H0.
 destruct H0.
 funfold H1.
 unfolds.
 intros.
 casetac pip p Heq Hneq.
 subst.
 eapply H3 in H6.
 simpljoin1.
 rewrite H2 in H6; inverts H6; tryfalse.
 eapply Int.eq_false; auto.
Qed.

Lemma R_Prio_Tbl_P_hold_for_del_gen :
  forall v'29 v'38 v'50 v'37 v'40 x x0 v'66 o ptls,
    prio_available x v'38 -> 
    RHL_PrioTbl_P v'29 ptls v'50 ->
    EcbMod.join x0 (EcbMod.sig (v'66, Int.zero) (absmutexsem x o, nil)) v'37 ->
    0<= Int.unsigned x <64 -> 
    length v'29 = 64%nat ->  
    R_PrioTbl_P v'29 v'38 v'50 ->
    RH_TCBList_ECBList_P v'37 v'38 v'40 -> 
    R_PrioTbl_P (update_nth_val (Z.to_nat (Int.unsigned x)) v'29 Vnull) v'38 v'50.
Proof.
  introv HHH Hrh.
  intros.
  assert (HHH': nth_val (Z.to_nat (Int.unsigned x)) v'29 =Some (Vptr v'50) \/ 
                                nth_val (Z.to_nat (Int.unsigned x)) v'29 =Some Vnull).
 { eapply RHL_PrioTbl_P_ex_nth in Hrh; eauto.
    simpljoin1.
    destruct H5 as [Heq | (tid & Heq)]; subst x1; auto.
    casetac tid v'50 Heq Hneq.
    subst; auto.
    eapply H2 in H4; eauto.
    simpljoin1.
    eapply HHH in H4; eauto.
    rewrite Int.eq_true in H4; tryfalse.
  }
  unfold R_PrioTbl_P in *.
  assert (Z.to_nat (Int.unsigned x) < length v'29)%nat.
  clear H2 H3.
  rewrite H1.
  mauto.
  split; intros; elim H2; intros.
  apply H8; auto.
  unfold nat_of_Z in *.
  assert (Z.to_nat (Int.unsigned prio) = Z.to_nat (Int.unsigned x) \/ Z.to_nat (Int.unsigned prio) <> Z.to_nat (Int.unsigned x)).
  tauto.
  elim H10; intros.
  rewrite H11 in H6.
  lets xxx: ls_has_nth_val H4.
  mytac.

  erewrite  update_nth in H6.
  inversion H6.
  eauto.
  eapply nth_upd_neq.
  eauto.
  eauto.

  split.
  intros.
  assert (Z.to_nat (Int.unsigned prio) = Z.to_nat (Int.unsigned x) \/ Z.to_nat (Int.unsigned prio) <> Z.to_nat (Int.unsigned x)).
  tauto.
  elim H8; intros.
  2:{
  split.
  elim H6; intros.
  lets fff: H10 H7.
  mytac.

  apply  nth_upd_neqrev.
  auto.
  auto.

  elim H6; intros.
  lets fff: H10 H7.
  mytac. }
  auto.
  destruct H3.
  mytac. rename H14 into Hport.
  destruct H13.
  assert (EcbMod.get v'37 (v'66, Int.zero) = Some (absmutexsem x o, nil)).
  eapply EcbMod.join_get_r; eauto.
  apply EcbMod.get_a_sig_a.
  go.
  lets aa: H6 H7.
  apply Z2Nat.inj in H9.
  apply unsigned_inj in H9.
  mytac.
  unfold nat_of_Z in H19.
  rewrite H19 in HHH'.
  destruct HHH' as [HHH' | HHH'];
  inverts HHH'.

  tryfalse.
  int auto.
  int auto.
(*   lets fffff: H14 H7. *)
(*   mytac. *)
(*   auto. *)
  
  elim H6; intros.
  auto.
Qed.

Lemma RL_RTbl_PrioTbl_P_hold_for_del_gen:
 forall v'29 v'38 v'50 v'37 v'40 x x0 v'66 v'35 o ptls,
  prio_available x v'38 ->
  RHL_PrioTbl_P v'29 ptls v'50 ->
  EcbMod.join x0 (EcbMod.sig (v'66, Int.zero) (absmutexsem x o, nil)) v'37 ->
  0<= Int.unsigned x <64 ->
  length v'29 = 64%nat ->
  R_PrioTbl_P v'29 v'38 v'50 ->
  RH_TCBList_ECBList_P v'37 v'38 v'40 ->
  RL_RTbl_PrioTbl_P v'35 v'29 v'50->
  RL_RTbl_PrioTbl_P v'35 (update_nth_val (Z.to_nat (Int.unsigned x )) v'29 Vnull) v'50.
Proof.
  introv HHH Hrh.
  intros.
  assert (HHH': nth_val (Z.to_nat (Int.unsigned x)) v'29 =Some (Vptr v'50) \/ 
                                nth_val (Z.to_nat (Int.unsigned x)) v'29 =Some Vnull).
 { eapply RHL_PrioTbl_P_ex_nth in Hrh; eauto.
    simpljoin1.
    destruct H6 as [Heq | (tid & Heq)]; subst x1; auto.
    casetac tid v'50 Heq Hneq.
    subst; auto.
    eapply H2 in H5; eauto.
    simpljoin1.
    eapply HHH in H5; eauto.
    rewrite Int.eq_true in H5; tryfalse.
  }
  unfold RL_RTbl_PrioTbl_P in *.
  intros.
  assert (Z.to_nat (Int.unsigned p) = Z.to_nat (Int.unsigned x) \/ Z.to_nat (Int.unsigned p) <> Z.to_nat (Int.unsigned x)).
  tauto.
  elim H7; intros.
  Focus 2.
  lets aa: H4 H5 H6.
  mytac.
  eexists.
  splits; eauto.
  
  apply  nth_upd_neqrev.
  auto.
  auto.

  lets bb: H4 H5 H6.
  false.
  mytac.
  apply Z2Nat.inj in H8.
  apply unsigned_inj in H8. (* new add *)
  inverts H8.
  rewrite H11 in HHH'.
  destruct HHH' as [HHH' | HHH']; 
  inverts HHH'; tryfalse.
  auto.
  auto.
Qed.

Lemma RH_PrioTbl_P_update_tcb:
forall i vhold_addr ptbl ptls tid,
  0 <= Int.unsigned i < 64 ->
  tid <> vhold_addr ->
  RH_PrioTbl_P ptbl ptls vhold_addr ->
  RH_PrioTbl_P
  (update_nth_val (Z.to_nat (Int.unsigned i)) ptbl (Vptr tid))
  (set ptls i (Valid_Addr tid)) vhold_addr.
Proof.
intros.
funfold H1.
unfolds.
split; unfolds; [funfold H1 | idtac];
splits; introv Hp; try introv Hnth; try introv Hneq; rewrite PtbMod.set_sem in *;
destruct (idxspec.beq i prio) eqn: eq1; auto;
try (eapply idxspec.beq_true_eq in eq1; subst);
 try eapply PtbMod.beq_sym in eq1;
try eapply idxspec.beq_false_neq in eq1;
try (eapply nth_upd_eq in Hnth; tryfalse);
try (eapply nth_upd_neq in Hnth; try eapply neq_imp_neqq; eauto);
try (false; eapply Hp; split; auto);
try (inverts Hnth; auto);
try eapply H2 in Hp; tryfalse; try tauto;
simpljoin1; try splits; auto;
try (inverts Hp; auto).
eapply nth_upd_neqrev; try eapply neq_imp_neqq; eauto.
eapply nth_upd_neqrev; try eapply neq_imp_neqq; eauto.
eapply RHL_PrioTbl_P_ex_nth in H2; eauto.
simpljoin1.
eapply update_nth; eauto.
eapply nth_upd_neqrev; try eapply neq_imp_neqq; eauto.
Qed.

(* used for pthread_mutex_info_t *)

(* Lemma struct_type_vallist_match_mutex_info_t_imp :
  forall vl, struct_type_vallist_match pthread_mutex_info_t vl ->
            exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10,
            vl = Vint32 v1 :: Vint32 v2 :: Vint32 v3 :: Vint32 v4 :: Vint32 v5 :: Vint32 v6 :: Vint32 v7 :: Vint32 v8 :: v9 :: v10::nil
             /\ isptr v9.
Proof. *)

Lemma struct_type_vallist_match_mutex_info_t_imp :
  forall vl, struct_type_vallist_match pthread_mutex_info_t vl ->
            exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10,
            vl = Vint32 v1 :: Vint32 v2 :: Vint32 v3 :: Vint32 v4 :: Vint32 v5 :: Vint32 v6 :: Vint32 v7 :: Vint32 v8 :: v9 :: v10 :: nil
             /\ isptr v9.
Proof.
  intros.
  unfold pthread_mutex_info_t in H.
  struct_type_vallist_match_elim.
  repeat eexists; eauto.
Qed.

Theorem assign_rule_lvar_array_struct :
  forall Spec I r ri p p' x v1 v2 tp1 tp2 aop sc li tid gident lident b i idx lenv vl decls sid n tp id p'',
    p <==>  LV x @ tp1|-> v1 ** p' ->
    p ==>  GV gident @ tp ∗ |-> Vptr (b, i) ** LV lident @ long |-> (V$ idx) **
                A_dom_lenv lenv ** 
                Astruct (b, (i +ᵢ  $ Z.of_nat (Z.to_nat (Int.unsigned ($ idx)) * typelen tp))) tp vl ** p'' ->
     tp = Tstruct sid decls ->
    ftype id decls = Some tp2 ->
    ~(exists ids dl, tp2 = Tunion ids dl) ->
    ~(exists ids dl, tp2 = Tstruct ids dl) ->
    ~(exists (t'0 : type) (n0 : nat), tp2 = Tarray t'0 n0) ->
    good_decllist decls = true ->
    id_nth id decls = Some n ->
     nth_val n vl = Some v2 ->
     struct_type_vallist_match tp vl -> 
     var_notin_dom gident lenv = true ->
     Int.unsigned ($ idx) <= Int.max_signed ->
     Int.min_signed <= Z.of_nat (szstruct decls) <= Int.max_signed ->
    assign_type_match tp1 tp2 ->
    LV x @ tp1|-> v2 ** p' ==>
       EX lg : list logicvar, p_local li tid lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-tid {{ <|| aop ||> ** p}} 
                                              (sassign (evar x) (efield (gident′ [lident′]) id)) {{ <|| aop ||> ** LV x @ tp1|-> v2 ** p' }}.
Proof.
  intros.
  eapply assign_rule_lvar; eauto.
  introv Hsat.
  eapply H0 in Hsat.
  eapply struct_array_member_rv; eauto.
  eapply gvar_rv; eauto.
  sep cancel A_dom_lenv.
  sep cancel (Agvarmapsto).
  eauto.
  eapply lvar_rv; eauto.
  sep cancel (Alvarmapsto).
  eauto.
  sep cancel Astruct.
 eauto.
 rewrite int_ltu_zero_eq_false; auto.
 eapply new_inv.nth_val_nth_val'_some_eq; eauto.
Unshelve.
exact 0%nat.
Qed.

Theorem assign_rule_lvar_array_struct_info :
  forall Spec I r ri p p' x v1 v2 tp1 tp2 aop sc li tid gident lident idx lenv decls sid tp id p'' vll len vl n,
    p <==>  LV x @ tp1|-> v1 ** p' ->
    p ==>  (EX l : addrval,
                  GV gident @ tp ∗ |-> Vptr l **
                  Aarray_new l (Tarray tp len) vll **
                  [|new_array_type_vallist_match tp vll /\ length vll = len |]) **
                LV lident @ long |-> (Vint32 idx) ** A_dom_lenv lenv ** p'' ->
     tp = Tstruct sid decls ->
     ftype id decls = Some tp2 ->
    ~(exists ids dl, tp2 = Tunion ids dl) ->
    ~(exists ids dl, tp2 = Tstruct ids dl) ->
    ~(exists (t'0 : type) (n0 : nat), tp2 = Tarray t'0 n0) ->
     good_decllist decls = true ->
     var_notin_dom gident lenv = true ->
     (Z.to_nat (Int.unsigned idx) < length vll)%nat ->
     vll <> nil ->
      nth_vallist (Z.to_nat (Int.unsigned idx)) vll = Some vl ->
     id_nth id decls = Some n ->
     nth_val n vl = Some v2 ->
     Z.of_nat (S (Z.to_nat (Int.unsigned idx)) * typelen tp) <= Int.max_unsigned ->
     Int.unsigned idx <= Int.max_signed ->
     Int.min_signed <= Z.of_nat (szstruct decls) <= Int.max_signed ->
    assign_type_match tp1 tp2 ->
    LV x @ tp1|-> v2 ** p' ==>
       EX lg : list logicvar, p_local li tid lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-tid {{ <|| aop ||> ** p}} 
                                              (sassign (evar x) (efield (gident′ [lident′]) id)) {{ <|| aop ||> ** LV x @ tp1|-> v2 ** p' }}.
Proof.
  intros.
  eapply assign_rule_lvar; eauto.
  introv Hsat.
  eapply H0 in Hsat.
  sep normal in Hsat.
  destruct Hsat as ((b & i) & Hsat).
  sep lift 3%nat in Hsat.
  eapply astar_l_apure_elim in Hsat.
  destruct Hsat as ((Hmatch & Hlen_vll) & Hsat).
  lets Hsplit: list_vallist_split_idx H8 H9.
  destruct Hsplit as (vll1 & vl' & vll2 & Hvll_eq & Hlen).
  subst vll.
  lets Hvl_eq: H10.
  rewrite <- Hlen in Hvl_eq.
  rewrite nth_vallist_get_idx in Hvl_eq.
  inverts Hvl_eq. rewrite <- Hlen_vll in Hsat.
  rewrite app_length in Hsat.
  sep lift 2%nat in Hsat.
  eapply Aarray_new_split_strong_frm in Hsat; try rewrite Hlen; eauto.
  simpl length in Hsat.
  subst tp.
  simpl Aarray_new at 2 in Hsat.
  eapply struct_array_member_rv; eauto.
  eapply gvar_rv; eauto.
  sep cancel A_dom_lenv.
  sep cancel (Agvarmapsto).
  eauto.
  eapply lvar_rv; eauto.
  sep cancel (Alvarmapsto).
  eauto.
  simpl Astruct.
  rewrite <- Hlen.
  sep cancel Astruct'.
  eauto.
  rewrite int_ltu_zero_eq_false; auto.
  eapply new_array_type_vallist_match_split2 in Hmatch; eauto.
  destruct Hmatch as (_ & Hmat).
  simpl new_array_type_vallist_match in Hmat.
  destruct Hmat as (Hmat & _).
  simpl struct_type_vallist_match; auto.
  eapply new_inv.nth_val_nth_val'_some_eq; eauto.
  Unshelve.
  exact 0%nat.
Qed.

(* Lemma pos_le_lemma
: forall posv (vll: list vallist), 
Int.ltu ($ 6) posv = false ->
posv <> $ 6 ->
length vll = ∘ (OS_USER_MAX_EVENTS / 3) ->
(Z.to_nat (Int.unsigned posv) < length vll)%nat /\ vll <> nil.
Proof.
intros.
split.
rewrite H1.
eapply int_ltu_prop in H; eauto.
eapply Int.ltu_inv in H.
change (Int.unsigned ($ 6)) with 6 in *.
change (∘ (OS_USER_MAX_EVENTS / 3)) with 6%nat.
auto with zarith.
pure_auto.
subst.
simpl in *.
auto with zarith.
Qed. *)

Lemma pos_le_lemma
: forall posv (vll: list vallist), 
Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) posv = false ->
posv <> $ (OS_USER_MAX_EVENTS / 3) ->
length vll = ∘ (OS_USER_MAX_EVENTS / 3) ->
(Z.to_nat (Int.unsigned posv) < length vll)%nat /\ vll <> nil.
Proof.
intros.
split.
rewrite H1.
eapply int_ltu_prop in H; eauto.
eapply Int.ltu_inv in H.
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
(* change (Int.unsigned ($ (OS_USER_MAX_EVENTS / 3))) with 6 in *.
change (∘ (OS_USER_MAX_EVENTS / 3)) with 6%nat. *)
unfold nat_of_Z.
assert (Int.unsigned ($ OS_USER_MAX_EVENTS / 3) = OS_USER_MAX_EVENTS / 3).
int auto.
rewrite H2 in H.
auto with zarith.
pure_auto.
subst.
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
simpl in *.
unfold nat_of_Z in H1.
clear -H1 Hrgn3 Hrgn4.
auto with zarith.
Qed.

Lemma tcbjoin_ejoin_ex_join:
  forall x x2 x1 tcbls'' tcbx tcbls,
    TcbJoin x x2 x1 tcbls'' ->
    EcbMod.join tcbls'' tcbx tcbls ->
    exists y, EcbMod.join x1 tcbx y /\ TcbJoin x x2 y tcbls.
Proof.
  intros.
  unfold TcbJoin in *.
  unfold Maps.join in *.
  unfold Maps.sig in *.
  simpl in *.
  exists (EcbMod.minus tcbls (EcbMod.sig x x2)).
  split.
  unfolds; intro.
  pose proof H a.
  pose proof H0 a.
  rewrite EcbMod.minus_sem.
  destruct(tidspec.beq x a) eqn:eq1.
  pose proof tidspec.beq_true_eq x a eq1; substs.
  rewrite EcbMod.get_sig_some.
  rewrite EcbMod.get_sig_some in H1.
  destruct(EcbMod.get tcbls'' a);
  destruct(EcbMod.get tcbx a);
  destruct(EcbMod.get tcbls a);
  destruct(EcbMod.get x1 a);
  tryfalse; auto.

  pose proof tidspec.beq_false_neq x a eq1.
  rewrite EcbMod.get_sig_none; auto.
  rewrite EcbMod.get_sig_none in H1; auto.
  destruct(EcbMod.get tcbls'' a);
  destruct(EcbMod.get tcbx a);
  destruct(EcbMod.get tcbls a);
  destruct(EcbMod.get x1 a);
  tryfalse; substs; auto.

  unfolds; intro.
  pose proof H a.
  pose proof H0 a.
  rewrite EcbMod.minus_sem.
  destruct(tidspec.beq x a) eqn:eq1.
  pose proof tidspec.beq_true_eq x a eq1; substs.
  rewrite EcbMod.get_sig_some.
  rewrite EcbMod.get_sig_some in H1.
  destruct(EcbMod.get tcbls'' a);
  destruct(EcbMod.get tcbx a);
  destruct(EcbMod.get tcbls a);
  destruct(EcbMod.get x1 a);
  tryfalse; substs; auto.

  
  pose proof tidspec.beq_false_neq x a eq1.
  rewrite EcbMod.get_sig_none; auto.
  rewrite EcbMod.get_sig_none in H1; auto.
  destruct(EcbMod.get tcbls'' a);
  destruct(EcbMod.get tcbx a);
  destruct(EcbMod.get tcbls a);
  destruct(EcbMod.get x1 a);
  tryfalse; substs; auto.
Qed.

Lemma tcbjoin_eget_my:
  forall x1 v1 m' m v2,
    TcbJoin x1 v1 m' m ->
    EcbMod.get m x1 = Some v2 -> v1 = v2.
Proof.
  unfold TcbJoin.
  intros.
  apply EcbMod.join_sig_get in H.
  rewrite H in H0.
  inversion H0.
  trivial.
Qed.

Lemma sum_int_35:
    ($ 4 +ᵢ
     ($ 1 +ᵢ
      ($ 4 +ᵢ
      ($ 1 +ᵢ
       ($ 1 +ᵢ
        ($ 1 +ᵢ
         ($ 1 +ᵢ
          ($ 1 +ᵢ
           ($ 1 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  Int.zero))))))))))))))) = $35. 
Proof.
  asserts_rewrite ($ 4 +ᵢ  Int.zero = $4). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 4 = $8). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 8 = $12). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 12 = $16). int auto.
  asserts_rewrite ($ 2 +ᵢ  $ 16 = $18). int auto.
  asserts_rewrite ($ 2 +ᵢ  $ 18 = $20). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 20 = $21). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 21 = $22). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 22 = $23). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 23 = $24). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 24 = $25). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 25 = $26). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 26 = $30). int auto.
  int auto. int auto.
Qed.

(* qptr_off *)
Lemma sum_int_39:
   ($ 4 +ᵢ
    ($ 4 +ᵢ
     ($ 1 +ᵢ
      ($ 4 +ᵢ
      ($ 1 +ᵢ
       ($ 1 +ᵢ
        ($ 1 +ᵢ
         ($ 1 +ᵢ
          ($ 1 +ᵢ
           ($ 1 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  Int.zero)))))))))))))))) = $39. 
Proof.
  asserts_rewrite ($ 4 +ᵢ  Int.zero = $4). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 4 = $8). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 8 = $12). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 12 = $16). int auto.
  asserts_rewrite ($ 2 +ᵢ  $ 16 = $18). int auto.
  asserts_rewrite ($ 2 +ᵢ  $ 18 = $20). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 20 = $21). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 21 = $22). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 22 = $23). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 23 = $24). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 24 = $25). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 25 = $26). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 26 = $30). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 30 = $31). int auto.
  int auto. int auto.
Qed.

(* add by xta *)

Lemma AEvStructHeap_unfold_mq_info_t: 
  forall s evheap x vl P,
    s |= AEvStructHeap evheap **
            LV mq_info @ mq_info_t ∗ |-> Vptr x ** P->
            Get_struct evheap x = Some (x, mq_info_t, vl) ->
    s |= EX evh1 evh2,
                 Astruct x mq_info_t vl ** 
                [|struct_type_vallist_match mq_info_t vl|] **
                [|R_MutexAttr_P mq_info_t vl|] ** (* new add *)
                LV mq_info @ mq_info_t ∗ |-> Vptr x **
                [| evheap =(evh1 ++ (x, mq_info_t, vl) :: evh2) |] **
                AEvStructHeap evh1 ** AEvStructHeap evh2 ** 
                [|Get_struct evh1 x = None|] **
                P.
Proof.
  introv Hsat Hget.
(*   sep pauto. *)
  inductions evheap. tryfalse. 
  destruct a. destruct p.
  rename evheap into evheap'.
  destruct t;
  try eapply astar_l_afalse_elim in Hsat;  tryfalse.
  unfold Get_struct in Hget.

  destruct (os_inv.beq_addrval a x) eqn: eq1.
  eexists. instantiate (1:= nil).
  exists evheap'.
  sep normal in Hsat.
  change (nil ++ (x, pthread_mutexattr_t, vl) :: evheap') with ((x, pthread_mutexattr_t, vl) :: evheap').

    sep pauto.
  eapply beq_tid_true_eq in eq1.
  inverts Hget.
  fold AEvStructHeap in Hsat.
  sep pauto.
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  sep pauto.
  inverts Hget. 
  eapply beq_tid_true_eq in eq1. subst a.
  auto. 
  (* new add about R_MutexAttr_P *)
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  inverts Hget. sep pauto.
  (* end of new add *)
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  inverts Hget. sep pauto.
  fold Get_struct in Hget.
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  sep normal in Hsat.
  sep lifts (4::5::nil)%nat in Hsat.
(*   sep lifts (3::4::nil)%nat in Hsat. *)
  eapply IHevheap in Hsat; eauto.
  sep pauto.
  3:{
  change((a, STRUCT i ­{ d }­, l) :: ( x0 ++ (x, mq_info_t, vl) :: x1)) with
 (((a, STRUCT i ­{ d }­, l) :: x0 ) ++ (x,  mq_info_t, vl) :: x1).
  eauto. }
  simpl AEvStructHeap at 1.
  sep pauto.
  unfold Get_struct; fold Get_struct.
  rewrite eq1, H2. (* change H1 into H2 *)
  auto.
Qed.

Lemma AEvStructHeap_fold_mq_info_t: 
  forall s x evheap P,
     s |= EX   vl evh1 evh2,
                Astruct x mq_info_t vl ** 
                [|struct_type_vallist_match mq_info_t vl|] **
                [|R_MutexAttr_P mq_info_t vl|] ** (* new add *)
                LV mq_info @ mq_info_t ∗ |-> Vptr x **
                [| evheap =(evh1 ++ (x, mq_info_t, vl) :: evh2) |] **
                AEvStructHeap evh1 ** AEvStructHeap evh2 ** P->
    s |=    AEvStructHeap evheap **
               LV mq_info @ mq_info_t ∗ |-> Vptr x ** P.
Proof.
  intros.
  unfold AEvStructHeap.
  sep pauto.
  fold AEvStructHeap.
  apply AEvStructHeap_compose.
  sep pauto.
  unfold AEvStructHeap.
  fold AEvStructHeap.
  destruct mq_info_t; tryfalse.
  sep pauto.
Qed.

Lemma AEvStructHeap_fold_mq_info_t': 
  forall s x evheap P vl evh1 evh2,
    s |=  Astruct x mq_info_t vl ** 
          LV mq_info @ mq_info_t ∗ |-> Vptr x **
          AEvStructHeap evh1 ** AEvStructHeap evh2 ** P->
    struct_type_vallist_match mq_info_t vl ->
    evheap =(evh1 ++ (x, mq_info_t, vl) :: evh2) ->
    R_MutexAttr_P mq_info_t vl ->
    s |=    AEvStructHeap evheap **
               LV mq_info @ mq_info_t ∗ |-> Vptr x ** P.
Proof.
  intros.
  unfold AEvStructHeap.
  sep pauto.
  fold AEvStructHeap.
  apply AEvStructHeap_compose.
  sep pauto.
  unfold AEvStructHeap.
  fold AEvStructHeap.
  destruct mq_info_t; tryfalse.
  sep pauto.
Qed.


Lemma struct_type_vallist_match_mqinfo_hold1:
forall vl v n,
 ( n <  5)%nat ->
struct_type_vallist_match mq_info_t vl->
struct_type_vallist_match mq_info_t
  (update_nth_val n vl (Vint32 v)).
Proof. 
  intros.
  lets Hsp: struct_type_vallist_match_elim_7 H0.
  destruct Hsp.
  do 6 destruct  H1.
  substs. 
  simpl in *.
   heat; jeauto2.
  do 7 (try destruct n); simpl; try splits; eauto.
  clear - H.
  int_auto.
Qed.

Lemma struct_type_vallist_match_mqinfo_hold2:
forall vl v ,
(Int.unsigned v <=? Byte.max_unsigned)%Z  = true ->
struct_type_vallist_match mq_info_t vl->
struct_type_vallist_match mq_info_t
  (update_nth_val 5 vl (Vint32 v)).
Proof. 
  intros.
  lets Hsp: struct_type_vallist_match_elim_7 H0.
  destruct Hsp.
  do 6 destruct  H1.
  substs. 
  simpl in *.
   heat; jeauto2.
  do 7 (try destruct n); simpl; try splits; eauto.
  rewrite H.
  auto.
Qed.  

Lemma AEvStructHeap_unfold_OS_Q_DATA: 
  forall s evheap x vl P,
    s |= AEvStructHeap evheap **
            LV os_code_defs.pdata @ OS_Q_DATA ∗ |-> Vptr x ** P->
            Get_struct evheap x = Some (x, OS_Q_DATA, vl) ->
    s |= EX evh1 evh2,
                 Astruct x OS_Q_DATA vl ** 
                [|struct_type_vallist_match OS_Q_DATA vl|] **
                [|R_MutexAttr_P OS_Q_DATA vl|] ** (* new add *)
                LV os_code_defs.pdata @ OS_Q_DATA ∗ |-> Vptr x **
                [| evheap =(evh1 ++ (x, OS_Q_DATA, vl) :: evh2) |] **
                AEvStructHeap evh1 ** AEvStructHeap evh2 ** 
                [|Get_struct evh1 x = None|] **
                P.
Proof.
  introv Hsat Hget.
(*   sep pauto. *)
  inductions evheap. tryfalse. 
  destruct a. destruct p.
  rename evheap into evheap'.
  destruct t;
  try eapply astar_l_afalse_elim in Hsat;  tryfalse.
  unfold Get_struct in Hget.

  destruct (os_inv.beq_addrval a x) eqn: eq1.
  eexists. instantiate (1:= nil).
  exists evheap'.
  sep normal in Hsat.
  change (nil ++ (x, OS_Q_DATA, vl) :: evheap') with ((x, OS_Q_DATA, vl) :: evheap').
    sep pauto.
  eapply beq_tid_true_eq in eq1.
  inverts Hget.
  fold AEvStructHeap in Hsat.
  sep pauto.
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  sep pauto.
  inverts Hget. 
  eapply beq_tid_true_eq in eq1. subst a.
  auto. 
  (* new add about R_MutexAttr_P *)
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  inverts Hget. sep pauto.
  (* end of new add *)
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  inverts Hget. sep pauto.
  fold Get_struct in Hget.
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  sep normal in Hsat.
  sep lifts (4::5::nil)%nat in Hsat.
(*   sep lifts (3::4::nil)%nat in Hsat. *)
  eapply IHevheap in Hsat; eauto.
  sep pauto.
  3:{
  change((a, STRUCT i ­{ d }­, l) :: ( x0 ++ (x, OS_Q_DATA, vl) :: x1)) with
 (((a, STRUCT i ­{ d }­, l) :: x0 ) ++ (x,  OS_Q_DATA, vl) :: x1).
  eauto. }
  simpl AEvStructHeap at 1.
  sep pauto.
  unfold Get_struct; fold Get_struct.
  rewrite eq1, H2. (* change H1 into H2 *)
  auto.
Qed.

Lemma AEvStructHeap_fold_OS_Q_DATA: 
  forall s x evheap P,
     s |= EX   vl evh1 evh2,
                Astruct x OS_Q_DATA vl ** 
                [|struct_type_vallist_match OS_Q_DATA vl|] **
                [|R_MutexAttr_P OS_Q_DATA vl|] ** (* new add *)
                LV os_code_defs.pdata @ OS_Q_DATA ∗ |-> Vptr x **
                [| evheap =(evh1 ++ (x, OS_Q_DATA, vl) :: evh2) |] **
                AEvStructHeap evh1 ** AEvStructHeap evh2 ** P->
    s |=    AEvStructHeap evheap **
               LV os_code_defs.pdata @ OS_Q_DATA ∗ |-> Vptr x ** P.
Proof.
  intros.
  unfold AEvStructHeap.
  sep pauto.
  fold AEvStructHeap.
  apply AEvStructHeap_compose.
  sep pauto.
  unfold AEvStructHeap.
  fold AEvStructHeap.
  destruct OS_Q_DATA; tryfalse.
  sep pauto.
Qed.

Lemma AEvArrayHeap_unfold: 
  forall s evheap x vl P,
    s |= AEvArrayHeap evheap **
            LV pdest @ Int8u ∗ |-> Vptr x ** P->
            Get_array evheap x = Some (x, Z.to_nat OS_EVENT_TBL_SIZE, vl) ->
    s |= EX evh1 evh2,
                 Aarray x (Tarray Int8u (Pos.to_nat 8)) vl ** 
                LV pdest @ Int8u ∗ |-> Vptr x **
                [|array_type_vallist_match Tint8 vl |] **
                [| evheap =(evh1 ++ (x, Z.to_nat OS_EVENT_TBL_SIZE, vl) :: evh2) |] **
                AEvArrayHeap evh1 ** AEvArrayHeap evh2 ** 
                [|Get_array evh1 x = None|] **
                P.
Proof.
  introv Hsat Hget.
  inductions evheap. tryfalse. 
  destruct a. destruct p.
  rename evheap into evheap'.
  unfold Get_array in Hget.
  destruct (os_inv.beq_addrval a x) eqn: eq1.
  eexists. instantiate (1:= nil).
  exists evheap'.
  sep normal in Hsat.
  change (nil ++ (x, Z.to_nat OS_EVENT_TBL_SIZE, vl) :: evheap') with ((x, Z.to_nat OS_EVENT_TBL_SIZE, vl) :: evheap').
    sep pauto.
  eapply beq_tid_true_eq in eq1.
  inverts Hget.
  fold AEvArrayHeap in Hsat.
  sep pauto.
  unfold AEvArrayHeap in Hsat.
  fold AEvArrayHeap in Hsat.
  sep pauto.
  inverts Hget. 
  eapply beq_tid_true_eq in eq1. subst a.
  auto. 
  unfold AEvArrayHeap in Hsat.
  fold AEvArrayHeap in Hsat.
  inverts Hget. sep pauto.
  fold Get_array in Hget. unfold AEvArrayHeap in Hsat.
  fold AEvArrayHeap in Hsat.
  sep normal in Hsat.
  
  sep lifts (3::4::nil)%nat in Hsat.
  eapply IHevheap in Hsat; eauto.
  sep pauto.
  3:{
  instantiate (1:= x1).
  instantiate (1:= (a, n, l) :: x0 ).
  eauto.
  }
  simpl AEvArrayHeap at 1.
  sep pauto.
  unfold Get_array; fold Get_array.
  rewrite eq1, H1.
  auto.
Qed.

Lemma AEvArrayHeap_succ_imp_alt :
  forall s a vll P, 
    s |= AEvArrayHeap (a :: vll) ** P ->
    s |= AEvArrayHeap (a::nil) ** AEvArrayHeap vll ** P.
Proof.
  intros.
  sep pauto.
  simpl AEvArrayHeap in *;
  destruct a. destruct p;
  try(eapply astar_l_afalse_intro; sep pauto).
  sep pauto.
 Qed.

Lemma AEvArrayHeap_succ :
  forall s a vll, 
    s |= AEvArrayHeap (a::nil) ** AEvArrayHeap vll -> 
    s |= AEvArrayHeap (a :: vll).
Proof.
  intros.
  simpl AEvArrayHeap in *;
  destruct a. destruct p;
  try(eapply astar_l_afalse_elim in H; sep pauto).
  sep pauto.
Qed.

Lemma AEvArrayHeap_compose :
  forall vll1 vll2 s, 
    s |= AEvArrayHeap vll1 ** AEvArrayHeap vll2 -> 
    s |= AEvArrayHeap (vll1 ++ vll2).
Proof.
  induction vll1; intros.
  change (nil ++ vll2) with (vll2).
  sep pauto.
  eapply AEvArrayHeap_succ_imp_alt in H.
  change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)).
  eapply AEvArrayHeap_succ.
  sep pauto.
Qed.

Lemma AEvArrayHeap_fold: 
  forall s x evheap P,
     s |= EX  vl evh1 evh2,
                 Aarray x (Tarray Int8u (Pos.to_nat 8)) vl ** 
                 [| array_type_vallist_match Tint8 vl |] **
                 [| evheap =(evh1 ++ (x, Z.to_nat OS_EVENT_TBL_SIZE, vl) :: evh2) |] **
                AEvArrayHeap evh1 ** AEvArrayHeap evh2 ** P->
    s |=    AEvArrayHeap evheap  ** P.
Proof.
  intros.
  unfold AEvArrayHeap.
  sep pauto.
  fold AEvArrayHeap.
  apply AEvArrayHeap_compose.
  sep pauto.
  unfold AEvArrayHeap.
  fold AEvArrayHeap.
  sep pauto.
Qed.

Lemma struct_type_vallist_match_mq_attr_t_vl:
  forall vl, 
    struct_type_vallist_match mq_attr_t vl ->
    exists v0 v1 v2 v3 v4 v5 v6,
      vl = v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: nil.
Proof.
  introv Hsmt.
  destruct vl.
  simpl in Hsmt. tryfalse.
  simpl in Hsmt.
  simpl in Hsmt.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  destruct vl. simpl in H0. 

  repeat eexists.
  simpl in H0. simpljoin1. tryfalse.
Qed.

Lemma struct_type_vallist_match_mq_attr_t_ptr:
  forall vl, 
  struct_type_vallist_match mq_attr_t vl ->
  isptr (nth_val' 5 vl).
Proof.
  introv Hsmt.
  destruct vl.
  simpl in Hsmt. tryfalse.
  simpl in Hsmt.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  simpljoin1. clear H.
  destruct vl.
  simpl in H0. tryfalse.
  simpl in H0.
  destruct v4; simpl in H0; simpljoin1; tryfalse.
  simpl. unfold isptr. auto.
  simpl. unfold isptr. right. eexists; eauto.
Qed.

Lemma RH_Q_NOT_IN_CORE_P_hold_neid:
forall mqeibs idx d',
RH_Q_NOT_IN_CORE_P mqeibs ->
~(exists eid wtype flag maxm msize curm mqc, d' = (Valid_Addr eid,wtype, flag, maxm, msize, curm, mqc)) ->
RH_Q_NOT_IN_CORE_P (MqattrMod.set mqeibs idx d').
Proof.
introv Hnq Hnex2.
unfold RH_Q_NOT_IN_CORE_P in *.
introv Hgetp.
casetac idx pos Heq Hneq.
- subst.
   rewrite set_a_get_a in *.
   inverts Hgetp.
   false. eapply Hnex2.
   repeat eexists; eauto.
- rewrite set_a_get_a' in *; eauto.
Qed.

Lemma nsem_not_in_core_sem:
forall eid els,
   ~(is_sem els eid) ->
   CORESEM_INECB_P els ->
   ~ In eid OSIPCSem_val /\ ~ In eid OSSendSem_val /\ eid <> OSSemShared_val.
Proof.
intros.
funfold H0.
casetac eid OSSemShared_val Heq Hneq.
subst.
tryfalse.
assert(Hc1: In eid OSIPCSem_val \/ ~ In eid OSIPCSem_val) by tauto.
destruct Hc1 as [Hf | Hc1].
eapply H0 in Hf; tryfalse.
assert(Hc2: In eid OSSendSem_val \/ ~ In eid OSSendSem_val) by tauto.
destruct Hc2 as [Hf | Hc2].
eapply H1 in Hf; tryfalse.
auto.
Qed.

Lemma RH_Q_NOT_IN_CORE_P_hold_eid_nref:
forall els semeibs muxeibs mqeibs idx  eid wtype flag maxm msize curm mqc,
RH_Q_NOT_IN_CORE_P mqeibs ->
~ eib_ref semeibs muxeibs mqeibs eid ->
is_que els eid ->
eid <> dynrefcmsgQ_addr ->
CORESEM_INECB_P els ->
RH_Q_NOT_IN_CORE_P (MqattrMod.set mqeibs idx (Valid_Addr eid,wtype, flag, maxm, msize, curm, mqc)).
Proof.
introv Hnq Hnref Hq Hndyn Hcs.
unfold RH_Q_NOT_IN_CORE_P in *.
introv Hgetp.
casetac idx pos Heq Hneq.
- subst.
   rewrite set_a_get_a in *.
   inverts Hgetp.
   eapply nsem_not_in_core_sem with (eid := eid0) in Hcs.
   2:{ unfold is_que, is_sem in *.
         introv Hf; simpljoin. tryfalse. }
   simpljoin.
   unfold notIncoreSemQ; auto.
- rewrite set_a_get_a' in *; eauto.
Qed.

Lemma RH_Q_NOT_IN_CORE_P_hold_same_ptr:
forall mqeibs idx eo wtype flag maxm msize curm mc wtype' flag' maxm' msize' curm' mc',
RH_Q_NOT_IN_CORE_P mqeibs ->
get mqeibs idx = Some (eo,wtype, flag, maxm, msize, curm, mc) ->
RH_Q_NOT_IN_CORE_P (MqattrMod.set mqeibs idx (eo,wtype', flag', maxm', msize', curm', mc')).
Proof.
introv Hr Hgetp.
unfold RH_Q_NOT_IN_CORE_P in *.
introv Hgetp'.
casetac idx pos Heq Hneq.
- subst.
   rewrite set_a_get_a in *.
   inverts Hgetp'.
   eapply Hr; eauto.
- rewrite set_a_get_a' in *; eauto.
Qed.

Lemma RH_SEM_NOT_IN_CORE_P_hold_neid:
forall eibs idx d',
RH_SEM_NOT_IN_CORE_P eibs ->
~(exists eid tp sc, d' = (infotid eid, tp, sc)) ->
RH_SEM_NOT_IN_CORE_P (set eibs idx d').
Proof.
introv Hns Hnex2.
unfold RH_SEM_NOT_IN_CORE_P in *.
introv Hgetp.
casetac idx pos Heq Hneq.
- subst.
   rewrite set_a_get_a in *.
   inverts Hgetp.
   false. eapply Hnex2.
   repeat eexists; eauto.
- rewrite set_a_get_a' in *; eauto.
Qed.

Lemma RH_SEM_NOT_IN_CORE_P_hold_eid_nref:
forall semeibs idx  eid tp sc,
RH_SEM_NOT_IN_CORE_P semeibs ->
notIncoreSemQ eid ->
RH_SEM_NOT_IN_CORE_P (set semeibs idx (infotid eid,tp,sc)).
Proof.
introv Hns Hnin.
unfold RH_SEM_NOT_IN_CORE_P in *.
introv Hgetp.
casetac idx pos Heq Hneq.
- subst.
   rewrite set_a_get_a in *.
   inverts Hgetp.
   auto.
- rewrite set_a_get_a' in *; eauto.
Qed.

Lemma RH_SEM_NOT_IN_CORE_P_hold_same_ptr:
forall semeibs idx eo tp tp' cap_tp cap_tp',
RH_SEM_NOT_IN_CORE_P semeibs ->
get semeibs idx = Some (eo,tp,cap_tp) ->
RH_SEM_NOT_IN_CORE_P (set semeibs idx (eo,tp',cap_tp')).
Proof.
introv Hr Hgetp.
unfold RH_SEM_NOT_IN_CORE_P in *.
introv Hgetp'.
casetac idx pos Heq Hneq.
- subst.
   rewrite set_a_get_a in *.
   inverts Hgetp'.
   eapply Hr; eauto.
- rewrite set_a_get_a' in *; eauto.
Qed.


Lemma SemCapArray_P_hold:
  forall vll v embls posv eo tp sc eo' tp',
  SemCapArray_P v vll embls ->
  get embls posv = Some (eo, tp, sc) ->
  SemCapArray_P v vll (set embls posv (eo', tp', sc)).
Proof.
  induction vll;
  simpl;
  intros;
  simpljoin.
  tryfalse.

  assert (posv = x \/ posv <> x) by tauto.
  destruct H as [ Heq | Hneq ].
  (* posv = x *)
  subst.
  lets Hget: EmbMod.join_sig_get H2.
  unfold get in H0.
  simpl in H0.
  rewrite H0 in Hget.
  inverts Hget.
  exists x x0 (eo', tp', sc). 
  eexists.
  splits; eauto.
  subst.
  eapply EmbMod_get_join_sig_set; eauto.
  eapply EmbMod_join_get_none_r with (ma := (sig x (eo, tp, sc))); eauto.
  eapply EmbMod.map_get_sig.
  unfold RHL_EINFO_CAP_P in *.
  simpljoin1.
  exists eo' tp' x3.
  splits; eauto.
  (* posv <> x *)
  assert (get embls posv = EmbMod.get x0 posv).
  eapply EmbMod.map_join_get_none; eauto.
  eapply EmbMod.map_get_sig'; eauto.
  unfold get in H0, H.
  simpl in H0, H.
  rewrite H in H0.
  exists x (set x0 posv (eo', tp', sc)) x1. 
  eexists.
  splits; eauto.
  eapply EmbMod.join_set_r; eauto.
  unfold EmbMod.indom.
  eauto.
Qed.

Lemma MuxCapArray_P_hold:
  forall vll v minfo posv eo ow tp rcnt prot prioc wq cnsa mc eo' ow' tp' rcnt' prot' prioc' wq' cnsa',
  MuxCapArray_P v vll minfo ->
  MibMod.get minfo posv = Some (eo, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) ->
  MuxCapArray_P v vll (set minfo posv (eo', ow', tp', rcnt', prot', prioc', wq', cnsa', mc)).
Proof.
  induction vll;
  simpl;
  intros;
  simpljoin.
  tryfalse.

  assert (posv = x \/ posv <> x) by tauto.
  destruct H as [ Heq | Hneq ].
  (* posv = x *)
  subst.
  lets Hget: MibMod.join_sig_get H2.
  rewrite H0 in Hget.
  inverts Hget.
  exists x x0 (eo', ow', tp', rcnt', prot', prioc', wq', cnsa', mc). 
  eexists.
  splits; eauto.
  subst.
  eapply MibMod_get_join_sig_set; eauto.
  eapply MibMod_join_get_none_r with (ma := (sig x (eo, ow, tp, rcnt, prot, prioc, wq, cnsa, mc))); eauto.
  eapply MibMod.map_get_sig.
  unfold RHL_MUX_CAP_P in *.
  simpljoin1.
  exists eo' ow' tp' rcnt' prot' prioc'.
  exists  wq' cnsa' x9.
  splits; eauto.
  (* posv <> x *)
  assert (MibMod.get minfo posv = MibMod.get x0 posv).
  eapply MibMod.map_join_get_none; eauto.
  eapply MibMod.map_get_sig'; eauto.
  rewrite H in H0.
  exists x (set x0 posv (eo', ow', tp', rcnt', prot', prioc', wq', cnsa', mc)) x1. 
  eexists.
  splits; eauto.
  eapply MibMod.join_set_r; eauto.
  unfold MibMod.indom.
  eauto.
Qed.

Lemma MqCapArray_P_hold:
  forall vll v qattrs posv eo wtype flag maxm msize curm mqc eo' wtype' flag' maxm' msize' curm',
  MqCapArray_P v vll qattrs ->
  MqattrMod.get qattrs posv = Some (eo, wtype, flag, maxm, msize, curm, mqc) ->
  MqCapArray_P v vll (set qattrs posv (eo', wtype', flag', maxm', msize', curm', mqc)).
Proof.
  induction vll;
  simpl;
  intros;
  simpljoin.
  tryfalse.

  assert (posv = x \/ posv <> x) by tauto.
  destruct H as [ Heq | Hneq ].
  (* posv = x *)
  subst.
  lets Hget: MqattrMod.join_sig_get H2.
  rewrite H0 in Hget.
  inverts Hget.
  exists x x0 (eo', wtype', flag', maxm', msize', curm', mqc). 
  eexists.
  splits; eauto.
  subst.
  eapply MqattrMod_get_join_sig_set; eauto.
  eapply MqattrMod_join_get_none_r with (ma := (sig x (eo, wtype, flag, maxm, msize, curm, mqc))); eauto.
  eapply MqattrMod.map_get_sig.
  unfold RHL_MQ_CAP_P in *.
  simpljoin1.
  exists eo' wtype' flag' maxm' msize' curm'.
  exists x7.
  splits; eauto.
  (* posv <> x *)
  assert (MqattrMod.get qattrs posv = MqattrMod.get x0 posv).
  eapply MqattrMod.map_join_get_none; eauto.
  eapply MqattrMod.map_get_sig'; eauto.
  rewrite H in H0.
  exists x (set x0 posv (eo', wtype', flag', maxm', msize', curm', mqc)) x1. 
  eexists.
  splits; eauto.
  eapply MqattrMod.join_set_r; eauto.
  unfold MqattrMod.indom.
  eauto.
Qed.

(* new lemmas used in getFreePos *)

Lemma Int_divu_eq_divs :
forall x y,
 Int.unsigned x <= Int.max_signed ->
 Int.unsigned y <= Int.max_signed ->
 Int.divu x y = Int.divs x y.
Proof.
int auto.
rewrite Zquot.Zquot_Zdiv_pos;
unfold Int.signed;
change (Int.half_modulus) with 2147483648;
try destruct (zlt (Int.unsigned x) 2147483648) eqn:eq1;
try destruct (zlt (Int.unsigned y) 2147483648) eqn:eq2;
auto with zarith.
apply Int.unsigned_range_2.
apply Int.unsigned_range_2.
Qed.

Lemma Int_divu_eq_divs':
forall x y,
 Int.unsigned x <= 2147483647 ->
 Int.unsigned y <= 2147483647 ->
 Int.divu x y = Int.divs x y.
Proof.
int auto.
rewrite Zquot.Zquot_Zdiv_pos;
unfold Int.signed;
change (Int.half_modulus) with 2147483648;
try destruct (zlt (Int.unsigned x) 2147483648) eqn:eq1;
try destruct (zlt (Int.unsigned y) 2147483648) eqn:eq2;
auto with zarith.
apply Int.unsigned_range_2.
apply Int.unsigned_range_2.
Qed.

Lemma user_max_evts_div_cpn_rgn:
forall cpn,
    1 <= Int.unsigned cpn ->
     Int.unsigned cpn <= 8 ->
     1 <= Int.unsigned (Int.divu ($ OS_USER_MAX_EVENTS / 3) cpn) ->
     1 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn <= 79.
Proof.
pose proof usr_max_evts_rgn.
intros.
unfold Int.divu in *.
rewrite Int.unsigned_repr in *; auto;
try solve_usr_max_evts_rgn; try conv_max_unsigned.
rewrite Int.unsigned_repr in *; auto;
try solve_usr_max_evts_rgn.
split; auto with zarith.
eapply Z.le_trans with (m:= 79 / Int.unsigned cpn).
eapply Z.div_le_mono; auto with zarith.
eapply Z.le_trans with (m:= 79 / 1).
eapply Z.div_le_compat_l; auto with zarith.
rewrite Z.div_1_r; auto with zarith.
rewrite Int.unsigned_repr ; auto; try solve_usr_max_evts_rgn.
split.
eapply Z.div_pos; auto with zarith.
eapply Z.le_trans with (m:= 79 / Int.unsigned cpn).
eapply Z.div_le_mono; auto with zarith.
eapply Z.le_trans with (m:= 79 / 1).
eapply Z.div_le_compat_l; auto with zarith.
rewrite Z.div_1_r; auto with zarith.
Qed.

Lemma Z_div_mul_lt:
forall  x y z, 0 <= z < y -> 0 < x / y -> x / y * z < x.
Proof.
intros.
eapply Z.lt_le_trans; [ | eapply Z.mul_div_le with (b:= y)]; auto with zarith.
rewrite Z.mul_comm.
eapply Zmult_lt_compat_r; auto with zarith.
Qed.

Lemma Z_div_mul_le:
forall  x y z, 0 < z <= y -> 0 < x / y -> x / y * z <= x.
Proof.
intros.
eapply Z.le_trans; [ | eapply Z.mul_div_le with (b:= y)]; auto with zarith.
rewrite Z.mul_comm.
eapply Zmult_le_compat_r; auto with zarith.
Qed.

Lemma Int_unsigned_add_eq:
forall x y : int32,
       Int.unsigned x + Int.unsigned y <= Int.max_unsigned ->
       Int.unsigned (x +ᵢ  y) = Int.unsigned x + Int.unsigned y.
Proof.
int auto.
split; auto.
eapply Ztac.add_le; apply Int.unsigned_range_2.
Qed.

Lemma user_max_evts_part_succ_rgn:
forall cpn idx,
    1 <= Int.unsigned cpn ->
     Int.unsigned cpn <= 8 ->
     1 <= Int.unsigned (Int.divu ($ OS_USER_MAX_EVENTS / 3) cpn) ->
      Int.unsigned idx < Int.unsigned cpn ->
     1 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned idx + 1) <=  OS_USER_MAX_EVENTS / 3.
Proof.
pose proof usr_max_evts_rgn.
intros.
pose proof (Int.unsigned_range_2 idx).
unfold Int.divu in *.
rewrite Int.unsigned_repr in *; auto;
try solve_usr_max_evts_rgn; try conv_max_unsigned.
rewrite Int.unsigned_repr in *; auto;
try solve_usr_max_evts_rgn.
split; auto with zarith.
eapply Z_div_mul_le; auto with zarith.
rewrite Int.unsigned_repr ; auto; try solve_usr_max_evts_rgn.
split.
eapply Z.div_pos; auto with zarith.
eapply Z.le_trans with (m:= 79 / Int.unsigned cpn).
eapply Z.div_le_mono; auto with zarith.
eapply Z.le_trans with (m:= 79 / 1).
eapply Z.div_le_compat_l; auto with zarith.
rewrite Z.div_1_r; auto with zarith.
Qed.



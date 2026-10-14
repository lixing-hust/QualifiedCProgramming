Require Import ucos_include.
Require Import os_ucos_h.
Require Import symbolic_lemmas.
Require Import Aarray_new_common.
Require Import gjb_common.
Require Import tv_match.
Require Import seplog_trm_tacs.
Require Import evt_spec_defs.
Require Import Lia.

Open Scope code_scope.
Open Scope int_scope.
Open Scope Z_scope.

(* Definition Qattr_full_P mqvl :=
forall i vl1, (0 <= i /\ i < Z.of_nat (length mqvl)) ->
                        nth_vallist (nat_of_Z i) mqvl = Some vl1 ->
                        ~(V_QATTRpevent vl1 = Some Vnull). 

Definition nth_Qattr_free_P i mqvl :=
exists vl1, 0 <= i /\ i < Z.of_nat (length mqvl) /\ 
                      nth_vallist (nat_of_Z i) mqvl = Some vl1 /\
                      V_QATTRpevent vl1 = Some Vnull.  *)

(* Lemma amqattr_len: 
  forall s l vl, s |= AMqAttr l vl -> length vl = ∘ (OS_USER_MAX_EVENTS / 3).
Proof.  
  introv Hsat.
  destruct Hsat.
  simpl_sat H. simpljoin1.
  auto.
Qed.  *)

Lemma amqattr_len: 
  forall s b i vl, s |= AMqAttr (b, i) vl -> length vl = ∘ (OS_USER_MAX_EVENTS / 3).
Proof.  
  introv Hsat.
  destruct Hsat.
  simpl_sat H. simpljoin1.
  auto.
Qed. 

(* Lemma AMqAttr_unfold_any_idx: 
  forall s l mqvl idx,
    s |= AMqAttr l mqvl ->
    (idx < length mqvl)%nat ->
    s |= EX vll1 vll2 b i vl ,
        GV Mq_Attr @ mq_attr_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray mq_attr_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen mq_attr_t))) mq_attr_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen mq_attr_t))))
          (Tarray mq_attr_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match mq_attr_t mqvl |] **
          [| length mqvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
          [| mqvl = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 |].  
Proof. 
  introv Hsat.
  assert (Hlengt: Z.of_nat (length mqvl * typelen mq_attr_t) <= Int.max_unsigned). 
  { erewrite amqattr_len; eauto.  simpl. mauto. }
  introv Hlenle. 
  unfold AMqAttr in Hsat.
  simpl_sat Hsat. 
  simpljoin1.
  rewrite <- H11 in *.
  assert (Hlen: (length mqvl = idx + (length mqvl - idx))%nat) 
    by auto with arith.
  lets Hsplit: (firstn_skipn idx mqvl). 
  rewrite <- Hsplit in H8 at 2.
  rewrite Hlen in H8. 
  destruct l.
  lets Harrs0: Aarray_new_split_strong H8.
  assert (HSidx: (S idx <= length mqvl)%nat) by auto with arith.
  assert (Harith: Z.of_nat (S idx * typelen mq_attr_t) <= Int.max_unsigned). 
  {
    apply Z.le_trans with (m:=Z.of_nat (length mqvl * typelen mq_attr_t));
      auto.
    apply inj_le. 
    apply NPeano.Nat.mul_le_mono_r; auto.
  }
  lets Harrs00: Harrs0 Harith.
  clear Harrs0.
  assert (Hlens: length (firstn idx mqvl) = idx /\ length (skipn idx mqvl) = (length mqvl - idx)%nat).
  {
    split. 
    apply firstn_length_le. auto with arith.
    apply skipn_length.
  }
  lets Harrs: Harrs00 Hlens.
  clear Harrs00.
  destruct Harrs.
  simpljoin1.
  destruct s as [[[[[[[]]]]]]].
  change_smo H12.
  change_smo H13.
  change_smo H3.

  assert (HlenS: (length mqvl - idx = S (length mqvl - (S idx)))%nat).
  {
    rewrite NPeano.Nat.sub_succ_r.
    rewrite Nat.lt_succ_pred with (z:=0%nat); auto.
    rewrite <- Nat.lt_add_lt_sub_r. simpl. auto.
  }
  rewrite HlenS in H13.
  assert (Hln: (length (skipn idx mqvl) > 0)%nat).
  {
    rewrite skipn_length.  
    cut (0 < length mqvl - idx)%nat.
    auto with arith.
    rewrite <- NPeano.Nat.lt_add_lt_sub_l.
    rewrite Nat.add_0_r. auto.
  }
  apply length_exists in Hln.
  destruct Hln as (vh & vlt & Hlst). rewrite Hlst in H13.
  apply Aarray_new'_succ_imp in H13.
  assert (Hsimp: $ Z.of_nat (idx * typelen mq_attr_t) +ᵢ  $ Z.of_nat (typelen mq_attr_t) =
                   $ Z.of_nat (S idx * typelen mq_attr_t)).
  {
    rewrite <- Nat.add_1_r.
    rewrite NPeano.Nat.mul_add_distr_r. 
    rewrite Nat2Z.inj_add.
    change (1 * typelen mq_attr_t)%nat with (typelen mq_attr_t).
    simpl. 
    assert (Ha: Z.of_nat (idx * 52) = Int.unsigned ($ (Z.of_nat (idx * 52)))). 
    {
      rewrite int_usign_eq; auto. auto with zarith.
      rewrite H11 in Hlen. unfold_usr_max_evts_in H11.
      simpl in H11.
      rewrite pos_to_nat_6 in H11. 
      rewrite H11 in Hlengt.
      apply lt_imply_le.
      apply Z.lt_le_trans with (m:=416). auto. 
      mauto. mauto.
    }
    assert (Hb: 52 = Int.unsigned ($52)) by auto.
    rewrite Ha at 2. rewrite Hb at 2.
    rewrite <- Int.add_unsigned. auto.
  }
  rewrite Int.add_assoc in H13. rewrite Hsimp in H13.
  assert (Hc: (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) = length mqvl - S idx)%nat).
  {
    rewrite H11.
    rewrite sub_Z_nat; auto. 
    rewrite <- H11. 
    auto.
  }
  rewrite Hc. 
  destruct H13.
  simpljoin1.
  change_smo H17.
  change_smo H18.
  unfold Aarray_new' in H17. unfold mq_attr_t in H17. fold mq_attr_t in H17.
  apply step_prop.StarEmpER in H17.

  simpl_sat_goal.

  exists (firstn idx mqvl). exists vlt. exists b. exists i.
  exists vh. exists x. exists x0. exists m. exists x2. eexists. exists o.
  splits; eauto.
  
  simpl in H10. simpl in H5. 
  destruct H10 as (Hx6emp & Hx9emp).
  subst x6. unfold emposabst in Hx9emp. subst x9. 
  assert (x5 = x0). { apply map_join_emp' in H5. auto. }
  subst x5.
  simpl in H7. simpl in H2.
  assert (x8 = x3). { apply map_join_emp' in H7. auto. }
  subst x8.
  simpl in H6. 
  simpl in H1.

  exists x1. do 5 eexists. splits; eauto.
  eexists x7. do 2 eexists. exists x14. do 2 eexists. 
  splits; eauto.

  unfold Aarray_new.
  exists x12. do 2 eexists. exists x15. do 2 eexists.
  splits; eauto.
  instantiate (1:=empenv). join auto.
  instantiate (1:=emp). join auto.

  do 6 eexists. splits; eauto.
  join auto. join auto.
  split; auto. simpl. split; auto. unfolds. auto.

  do 6 eexists. splits; eauto. 
  join auto. join auto.
  split; auto. simpl. split; auto. unfolds. eauto.

  do 6 eexists. splits; eauto.
  join auto. join auto.
  split. 
  rewrite <- Hsplit at 1. rewrite Hlst. auto.
  simpl. split; auto. unfolds. auto.

  do 6 eexists. splits; eauto.
  join auto. join auto.
  split. split; auto.
  rewrite Hlst in H15. simpl in H15. 
  eapply sub_eq_succ; eauto.
  simpl. split; auto. unfolds. auto.
  rewrite H11 in HSidx.
  apply inj_le in HSidx. simpl in HSidx.
  unfold_usr_max_evts. simpl. 
  asserts_rewrite (20/3 = 6). { auto. }
  auto.
  simpl. split; auto. unfolds. auto.

Qed.
 *)
 
 Lemma AMqAttr_unfold_any_idx: 
  forall s b i mqvl idx,
    s |= AMqAttr (b, i) mqvl ->
    (idx < length mqvl)%nat ->
    s |= EX vll1 vll2 (* b i  *)vl ,
        GV Mq_Attr @ mq_attr_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray mq_attr_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen mq_attr_t))) mq_attr_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen mq_attr_t))))
          (Tarray mq_attr_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match mq_attr_t mqvl |] **
          [| length mqvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
          [| mqvl = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 |].  
Proof. 
  introv Hsat.
  assert (Hlengt: Z.of_nat (length mqvl * typelen mq_attr_t) <= Int.max_unsigned). 
    { erewrite amqattr_len; eauto.
    lets Hrgn: usr_max_evts_rgn.
    destruct Hrgn as (Hrgn3 & Hrgn4).
    unfold nat_of_Z.
    simpl.
    int auto. }
  introv Hlenle. 
  unfold AMqAttr in Hsat.
  simpl_sat Hsat. 
  simpljoin1.
  rewrite <- H11 in *.
  assert (Hlen: (length mqvl = idx + (length mqvl - idx))%nat) 
    by auto with arith.
  lets Hsplit: (firstn_skipn idx mqvl). 
  rewrite <- Hsplit in H8 at 2.
  rewrite Hlen in H8. 
  (* destruct l. *)
  lets Harrs0: Aarray_new_split_strong H8.
  assert (HSidx: (S idx <= length mqvl)%nat) by auto with arith.
  assert (Harith: Z.of_nat (S idx * typelen mq_attr_t) <= Int.max_unsigned). 
  {
    apply Z.le_trans with (m:=Z.of_nat (length mqvl * typelen mq_attr_t));
      auto.
    apply inj_le. 
    apply NPeano.Nat.mul_le_mono_r; auto.
  }
  lets Harrs00: Harrs0 Harith.
  clear Harrs0.
  assert (Hlens: length (firstn idx mqvl) = idx /\ length (skipn idx mqvl) = (length mqvl - idx)%nat).
  {
    split. 
    apply firstn_length_le. auto with arith.
    apply skipn_length.
  }
  lets Harrs: Harrs00 Hlens.
  clear Harrs00.
  destruct Harrs.
  simpljoin1.
  destruct s as [[[[[[[]]]]]]].
  change_smo H12.
  change_smo H13.
  change_smo H3.

  assert (HlenS: (length mqvl - idx = S (length mqvl - (S idx)))%nat).
  {
    rewrite NPeano.Nat.sub_succ_r.
    rewrite Nat.lt_succ_pred with (z:=0%nat); auto.
    rewrite <- Nat.lt_add_lt_sub_r. simpl. auto.
  }
  rewrite HlenS in H13.
  assert (Hln: (length (skipn idx mqvl) > 0)%nat).
  {
    rewrite skipn_length.  
    cut (0 < length mqvl - idx)%nat.
    auto with arith.
    rewrite <- NPeano.Nat.lt_add_lt_sub_l.
    rewrite Nat.add_0_r. auto.
  }
  apply length_exists in Hln.
  destruct Hln as (vh & vlt & Hlst). rewrite Hlst in H13.
  apply Aarray_new'_succ_imp in H13.
  assert (Hsimp: $ Z.of_nat (idx * typelen mq_attr_t) +ᵢ  $ Z.of_nat (typelen mq_attr_t) =
                   $ Z.of_nat (S idx * typelen mq_attr_t)).
  {
    rewrite <- Nat.add_1_r.
    rewrite NPeano.Nat.mul_add_distr_r. 
    rewrite Nat2Z.inj_add.
    change (1 * typelen mq_attr_t)%nat with (typelen mq_attr_t).
    simpl. 
    assert (Ha: Z.of_nat (idx * 52) = Int.unsigned ($ (Z.of_nat (idx * 52)))). 
    {
      rewrite int_usign_eq; auto. auto with zarith.
      rewrite H11 in Hlen. 
      (* unfold_usr_max_evts_in H11. *)
      lets Hrgn: usr_max_evts_rgn.
      destruct Hrgn as (Hrgn3 & Hrgn4).
      unfold nat_of_Z in *.
      (* simpl in H11.
      rewrite pos_to_nat_6 in H11.  *)
      rewrite H11 in Hlengt.
      rewrite H11 in Hlenle.
      clear - Hlengt Hlenle Hrgn3 Hrgn4.
      simpl in Hlengt.
      int auto.
    }
    assert (Hb: 52 = Int.unsigned ($52)) by auto.
    rewrite Ha at 2. rewrite Hb at 2.
    rewrite <- Int.add_unsigned. auto.
  }
  rewrite Int.add_assoc in H13. rewrite Hsimp in H13.
  assert (Hc: (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) = length mqvl - S idx)%nat).
  {
    rewrite H11.
    rewrite sub_Z_nat; auto. 
    rewrite <- H11. 
    auto.
  }
  rewrite Hc. 
  destruct H13.
  simpljoin1.
  change_smo H17.
  change_smo H18.
  unfold Aarray_new' in H17. unfold mq_attr_t in H17. fold mq_attr_t in H17.
  apply step_prop.StarEmpER in H17.

  simpl_sat_goal.

  exists (firstn idx mqvl). exists vlt. (* exists b. exists i. *)
  exists vh. exists x. exists x0. exists m. exists x2. eexists. exists o.
  splits; eauto.
  
  simpl in H10. simpl in H5. 
  destruct H10 as (Hx6emp & Hx9emp).
  subst x6. unfold emposabst in Hx9emp. subst x9. 
  assert (x5 = x0). { apply map_join_emp' in H5. auto. }
  subst x5.
  simpl in H7. simpl in H2.
  assert (x8 = x3). { apply map_join_emp' in H7. auto. }
  subst x8.
  simpl in H6. 
  simpl in H1.

  exists x1. do 5 eexists. splits; eauto.
  eexists x7. do 2 eexists. exists x14. do 2 eexists. 
  splits; eauto.

  unfold Aarray_new.
  exists x12. do 2 eexists. exists x15. do 2 eexists.
  splits; eauto.
  instantiate (1:=empenv). join auto.
  instantiate (1:=emp). join auto.

  do 6 eexists. splits; eauto.
  join auto. join auto.
  split; auto. simpl. split; auto. unfolds. auto.

  do 6 eexists. splits; eauto. 
  join auto. join auto.
  split; auto. simpl. split; auto. unfolds. eauto.

  do 6 eexists. splits; eauto.
  join auto. join auto.
  split. 
  rewrite <- Hsplit at 1. rewrite Hlst. auto.
  simpl. split; auto. unfolds. auto.

  do 6 eexists. splits; eauto.
  join auto. join auto.
  split. split; auto.
  rewrite Hlst in H15. simpl in H15. 
  eapply sub_eq_succ; eauto.
  simpl. split; auto. unfolds. auto.
  rewrite H11 in HSidx.
  apply inj_le in HSidx. simpl in HSidx.
  unfold nat_of_Z in HSidx.
  int auto.
  simpl. split; auto. unfolds. auto.
Qed.

 
(* Lemma AMqAttr_unfold_any_idx_frm: 
  forall s l mqvl idx P,
    s |= AMqAttr l mqvl  ** P ->
    (idx < length mqvl)%nat ->
    s |= (EX vll1 vll2 b i vl ,
        GV Mq_Attr @ mq_attr_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray mq_attr_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen mq_attr_t))) mq_attr_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen mq_attr_t))))
            (Tarray mq_attr_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match mq_attr_t mqvl |] **
          [| length mqvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
          [| mqvl = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 |]) ** P.   
Proof. 
  introv Hsat Hlenle. 
  sep cancel 2%nat 2%nat.
  eapply AMqAttr_unfold_any_idx; eauto.
Qed. *)

Lemma AMqAttr_unfold_any_idx_frm: 
  forall s b i mqvl idx P,
    s |= AMqAttr (b, i) mqvl  ** P ->
    (idx < length mqvl)%nat ->
    s |= (EX vll1 vll2 (* b i *) vl ,
        GV Mq_Attr @ mq_attr_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray mq_attr_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen mq_attr_t))) mq_attr_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen mq_attr_t))))
            (Tarray mq_attr_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match mq_attr_t mqvl |] **
          [| length mqvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
          [| mqvl = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 |]) ** P.   
Proof. 
  introv Hsat Hlenle. 
  sep cancel 2%nat 2%nat.
  eapply AMqAttr_unfold_any_idx; eauto.
Qed.

Lemma new_array_type_vallist_match_split2': 
  forall mqvl vll1 vll2 t, 
    new_array_type_vallist_match t mqvl ->
    mqvl = vll1 ++ vll2 ->
    new_array_type_vallist_match t vll1 /\
      new_array_type_vallist_match t vll2.
Proof.
  inductions mqvl.
  -  intros.
     symmetry in H0.
     apply app_eq_nil in H0. 
     destruct H0. subst vll1 vll2. 
     simpl. auto.
  - introv Hmt1 Hlst.
    destruct vll1.
    simpl in Hlst.
    destruct vll2; inverts Hlst.
    split; simpl; auto.
    rewrite <- app_comm_cons in Hlst.
    inverts Hlst.
    simpl in Hmt1.
    destruct t;
      (destruct Hmt1 as (Hmta & Hmtb);
       specialize (IHmqvl vll1 vll2 _ Hmtb (eq_refl _));
       split; [simpl; mytac | mytac]).
Qed.

Lemma new_array_type_vallist_match_split': 
  forall mqvl vll1 vll2 vl, 
    new_array_type_vallist_match mq_attr_t mqvl ->
    mqvl = vll1 ++ (vl::vll2) ->
    new_array_type_vallist_match mq_attr_t vll1 /\
      new_array_type_vallist_match mq_attr_t vll2 /\ 
      struct_type_vallist_match mq_attr_t vl.   
Proof.
  introv Hmatch Hlst.
  lets Hsp2 : new_array_type_vallist_match_split2' Hmatch Hlst.
  destruct Hsp2.
  split; auto.
  simpl in H0.
  destruct H0.
  split; auto.
Qed.

Lemma new_array_type_vallist_match_que_getp:
  forall vll1 vl vll2,
    new_array_type_vallist_match mq_attr_t (vll1 ++ (vl :: vll2)) ->
    exists v, V_QATTRpevent vl = Some v /\ isptr v. 
Proof.
  intros.
  eapply new_array_type_vallist_match_split' in H; eauto. 
  destruct H as (_ & _ & Hsp).
  unfold struct_type_vallist_match in Hsp.
  unfold mq_attr_t in Hsp.
  lets Hvl: struct_type_vallist_match_elim_7 Hsp.
  destruct Hvl. do 6 destruct H.
  subst vl.
  simpl in Hsp.
  simpljoin1.
  exists x3.
  unfold V_OSSINFOPevent. unfold isptr.
  simpl. split; auto.
  destruct x3; tryfalse; pure_auto.
Qed.

Lemma AMqAttr_select_sn_strong :
  forall vll1 n vll2 b i s vl P, 
    Z.of_nat(S n) <= OS_USER_MAX_EVENTS / 3 ->
    s |= GV Mq_Attr @ mq_attr_t ∗ |-> Vptr (b,i) **
      Aarray_new (b, i) (Tarray mq_attr_t n) vll1 **
      Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen mq_attr_t)))) mq_attr_t vl **
      Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen mq_attr_t))))
        (Tarray mq_attr_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)))) vll2 ** P ->
    new_array_type_vallist_match mq_attr_t (vll1 ++ (vl::vll2)) ->
    length (vll1 ++ (vl::vll2)) = ∘ (OS_USER_MAX_EVENTS / 3) ->
    s |= AMqAttr (b, i) (vll1 ++ (vl::vll2)) ** P.
Proof.
  intros.
  assert (Hrgn: Z.of_nat (S n * typelen mq_attr_t) <= Int.max_unsigned).
  {
    remember (typelen mq_attr_t) as X. 
    unfold mq_attr_t in HeqX. simpl in HeqX. 
    rewrite HeqX.
    lets Hrgn: usr_max_evts_rgn.
    destruct Hrgn as (Hrgn3 & Hrgn4).
    int auto.
  }
  unfold AMqAttr.
  sep pauto.
  assert (Heq: ∘ (OS_USER_MAX_EVENTS / 3) 
               =  Nat.add n (S (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n))) )).
  unfold nat_of_Z.
  assert (Heq1: Z.to_nat (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S n)) 
              = Nat.sub (Z.to_nat (OS_USER_MAX_EVENTS / 3))  (Z.to_nat (Z.of_nat (S n))) ).
  apply Z2Nat.inj_sub.
  eauto with zarith.
  rewrite Heq1.
  eauto with zarith.
  rewrite Heq.
  eapply Aarray_new_compose_strong; eauto.

  sep pauto.
  eapply Aarray_new_succ.
  rewrite Int.add_assoc.
  asserts_rewrite ($ Z.of_nat (n * typelen mq_attr_t) +ᵢ  $ Z.of_nat (typelen mq_attr_t) 
                   = $ Z.of_nat (S n * typelen mq_attr_t)).
  { int auto. }
  sep pauto.
  unfold mq_attr_t.
  unfold Aarray_new.
  unfold Aarray_new'.
  fold mq_attr_t.
  sep pauto.
Qed.

Lemma AMqAttr_select_sn_ex_strong:
  forall s P b i mqvl,
     s |= EX vll1 n vll2 (* b i *) vl ,
             GV Mq_Attr @ mq_attr_t ∗ |-> Vptr (b,i) **
             Aarray_new (b, i) (Tarray mq_attr_t n) vll1 **
             Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen mq_attr_t)))) mq_attr_t vl **
             Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen mq_attr_t))))
               (Tarray mq_attr_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)))) vll2 **
             [| new_array_type_vallist_match mq_attr_t mqvl |] **
             [| length mqvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
             [| mqvl = vll1 ++ (vl::vll2) |] ** 
             [| length vll1 = n /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)) |] **
             [| Z.of_nat(S n) <= OS_USER_MAX_EVENTS / 3 |] **
             (* [| 0 <= Int.unsigned i + (OS_USER_MAX_EVENTS / 3) * (Z.of_nat (typelen sem_info_t)) <= Int.max_unsigned |] ** *)
              P ->
    s |= AMqAttr (b, i) mqvl ** P.
Proof.
  intros.
  do 4 destruct H.
  sep split in H.
  subst.
  eapply AMqAttr_select_sn_strong.
  eauto.
  eauto.
  sep pauto.
  eauto.
Qed.


Lemma mqattr_corr':
  forall vl vll1 vll2 qattrb hld v i, 
    MqEIBAarray_P v (vll1 ++ vl :: vll2) qattrb hld ->
    Int.ltu i Int.zero = false -> 
    length vll1 = Z.to_nat (Int.unsigned i) -> 
    (forall j, v = Vint32 j ->
               Int.ltu j Int.zero = false /\ Int.unsigned j + Int.unsigned i <= Int.max_unsigned) ->  
    exists j eid_t waittype flags maxmsg msgsize curmsgs mqc, 
      v = Vint32 j /\
      get qattrb (j +ᵢ i) = Some (eid_t, waittype, flags, maxmsg, msgsize, curmsgs, mqc) /\
      ( ( (eid_t=Null /\ V_QATTRpevent vl =Some (Vnull))  \/  
                 (eid_t = Holder /\ V_QATTRpevent vl =Some  (Vptr hld))  \/ 
                 (exists eid , eid_t = (Valid_Addr eid) /\ V_QATTRpevent vl =Some (Vptr eid)/\eid <>hld) )   /\ 
                 V_QATTRmq_waittype vl = Some (Vint32 waittype)  /\ 
                 V_QATTRmq_flags vl = Some (Vint32 flags)  /\ 
                 V_QATTRmq_maxmsg vl = Some (Vint32 maxmsg)   /\ 
                 V_QATTRmq_msgsize vl = Some (Vint32 msgsize)   /\  
                 V_QATTRmq_curmsgs vl = Some (Vint32 curmsgs)).

Proof.
  inductions vll1.

  introv Harrp Hi Hlen Hsumrgn.
  simpl in Harrp.
  assert (Hiz: i = Int.zero).
  { 
    simpl in Hlen. destruct (Int.unsigned i) eqn: E.
    apply Int.unsigned_eq_zero; auto.
    int auto. int auto.
  }
  destruct Harrp as (v' & qattrb' & absqattrb & pos & Hv & Hv' & Hjo & HP & H').
  unfold RHL_EIBlk_Q_P in HP.
  destruct absqattrb as [[[[[[et i1] i2] i3] i4] i5] i6].
  specialize (HP et i1 i2 i3 i4 i5 i6 (eq_refl _)).
  destruct v eqn: E; try inverts Hv.
  exists pos.
  exists et i1 i2 i3 i4 i5.
  exists i6.
  splits; auto.
  assert (Heq: pos +ᵢ  i = pos). { rewrite Hiz. int auto. }
  rewrite Heq.
  eapply join_sig_get; eauto.
  destructs HP. auto.
  destructs HP. auto. 
  destructs HP. auto. 
  destructs HP. auto. 
  destructs HP. auto. 
  destructs HP. auto. 
  
  introv Harrp Hi Hlen Hsumrgn.
  simpl in Harrp.
  simpl in Hlen.
  assert (Hige: Int.unsigned i >= 1). { auto with zarith. }
  destruct Harrp as (v' & qattrb' & absqattrb & pos & Hv & Hv' & Hjo & HP & H').
  eapply IHvll1 with (qattrb:=qattrb') (i:=Int.sub i ($1)) in H'; eauto.
  destruct H' as (j & et & i1 & i2 & i3 & i4 & i5 & i6 & H').
  exists pos et i1 i2 i3 i4. 
  exists i5 i6.
  simpljoin1. splits; auto.
  inverts H.
  rewrite pos_add_sub_one in H0; auto.
  (* Print map_join_get_none'. *)
  eapply join_lib.map_join_get_none' with (m2:=qattrb'); eauto.
  apply get_a_sig_a'.
  specialize (Hsumrgn pos (eq_refl _)). 
  destruct Hsumrgn. apply pos_add_i_neq; auto.
  specialize (Hsumrgn pos (eq_refl _)).
  mytac.
  specialize (Hsumrgn pos (eq_refl _)).
  mytac.
  apply i_ge1_i_sub1_ge0. auto.
  int auto. int auto. 
  introv H_v'.
  subst v. subst v'. inverts H_v'.
  specialize (Hsumrgn pos (eq_refl _)).
  destruct Hsumrgn as (Hpos & Hadd).
  split. int auto. int auto.
  int auto. int auto. int auto.
Qed. 

Lemma mqattr_corr: 
  forall vl vll1 vll2 qattrb hld i, 
    MqEIBAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) qattrb hld ->
    length vll1 = Z.to_nat (Int.unsigned i) -> 
    Int.ltu i Int.zero = false -> 
    Int.unsigned i <= Int.max_unsigned ->  
    exists eid_t waittype flags maxmsg msgsize curmsgs mqc, 
      get qattrb i= Some (eid_t, waittype, flags, maxmsg, msgsize, curmsgs, mqc) /\
      (((eid_t=Null /\ V_QATTRpevent vl =Some (Vnull))  \/  
        (eid_t = Holder /\ V_QATTRpevent vl =Some  (Vptr hld)) \/ 
        (exists eid , eid_t = (Valid_Addr eid) /\ V_QATTRpevent vl =Some (Vptr eid) /\ eid <> hld )) /\ 
         V_QATTRmq_waittype vl = Some (Vint32 waittype) /\ 
         V_QATTRmq_flags vl = Some (Vint32 flags) /\ 
         V_QATTRmq_maxmsg vl = Some (Vint32 maxmsg) /\ 
         V_QATTRmq_msgsize vl = Some (Vint32 msgsize) /\  
         V_QATTRmq_curmsgs vl = Some (Vint32 curmsgs)).
Proof.
  introv HP Hvll1 Hlt Hle.
  eapply mqattr_corr' with (i:=i) in HP; eauto.
  2: {
    introv Hj0. 
    split. inv Hj0. int auto. inverts Hj0. int auto.
  }
  rewrite <- (Int.add_zero_l i).
  simpljoin1.
  do 7 eexists. splits; eauto.
  instantiate (1:=x6).
  inverts H.
  auto.
Qed.

Lemma RHL_EIBlk_Q_P_get_pevent:
  forall vl x vhold,
    RHL_EIBlk_Q_P vl x vhold ->
    exists v, V_QATTRpevent vl = Some v. 
Proof.
  intros.
  funfold H.
  destruct x as [[[[[[]]]]]].
  specialize (H _ _ _ _ _ _ _ (eq_refl _)). 
  destructs H. 
  destruct H as [H' | [ H' | H']]; mytac.
Qed.

Lemma RHL_EIBlk_Q_P_set_to_hold:
forall vl v wtp flg mm ms cm vhold mqc,
  V_QATTRpevent vl = Some v -> 
  V_QATTRmq_waittype vl = Some (Vint32 wtp) -> 
  V_QATTRmq_flags vl = Some (Vint32 flg) -> 
  V_QATTRmq_maxmsg vl = Some (Vint32 mm) -> 
  V_QATTRmq_msgsize vl = Some (Vint32 ms) -> 
  V_QATTRmq_curmsgs vl = Some (Vint32 cm) -> 
(*   V_OSMUXINFOMuxCap vl = List.map Vint32 mqc -> *)
 RHL_EIBlk_Q_P (update_nth_val 5 vl (Vptr vhold)) (Holder, wtp, flg, mm, ms, cm, mqc)  vhold.
Proof.
unfold RHL_EIBlk_Q_P.
intros.
inverts H5.
unfold V_QATTRmq_waittype in *.
unfold V_QATTRmq_flags in *.
unfold V_QATTRmq_maxmsg in *.
unfold V_QATTRmq_msgsize in *.
unfold V_QATTRmq_curmsgs in *.
splits; auto.
2: eapply nth_upd_neqrev; auto. 
2: eapply nth_upd_neqrev; auto. 
2: eapply nth_upd_neqrev; auto. 
2: eapply nth_upd_neqrev; auto. 
2: eapply nth_upd_neqrev; auto. 
right. left.
unfold V_QATTRpevent in *.
splits; auto.
eapply update_nth. eauto.
Qed.

Lemma RH_EIBlk_ECBlk_Q_P_set_to_hold:
  forall els qattrb pos wtype flag maxm msize curm mqc,
    RH_EIBlk_ECBlk_Q_P els qattrb ->
    RH_EIBlk_ECBlk_Q_P els (set qattrb pos (Holder, wtype, flag, maxm, msize, curm, mqc)). 
Proof.
  unfold RH_EIBlk_ECBlk_Q_P.
  intros.
  rewrite MqattrMod.set_sem in H0.
  
  destruct (idxspec.beq pos pos0) eqn: eq1; tryfalse.
  eapply H in H0; eauto.
Qed.

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



Lemma RHL_EIBlk_Q_P_null_constr: 
forall vl v wtp flg mm ms cm mqc vhold, 
  V_QATTRpevent vl = Some v -> 
  V_QATTRmq_waittype vl = Some (Vint32 wtp) -> 
  V_QATTRmq_flags vl = Some (Vint32 flg) -> 
  V_QATTRmq_maxmsg vl = Some (Vint32 mm) -> 
  V_QATTRmq_msgsize vl = Some (Vint32 ms) -> 
  V_QATTRmq_curmsgs vl = Some (Vint32 cm) ->
  RHL_EIBlk_Q_P (update_nth_val 5 vl Vnull) (Null, wtp, flg, mm, ms, cm, mqc) vhold. 
Proof.
  introv Hp Hwtp Hflg Hmm Hms Hcm.
  unfold RHL_EIBlk_Q_P.
  introv Heq.
  inverts Heq.
  splits; auto.
  -
    left.
    split; auto.
    unfold V_QATTRpevent.
    erewrite update_nth; eauto.
  -
    unfold V_QATTRmq_waittype in *.
    eapply nth_upd_neqrev; eauto.
  -
    unfold V_QATTRmq_flags in *.
    eapply nth_upd_neqrev; eauto.
  -
    unfold V_QATTRmq_maxmsg in *.
    eapply nth_upd_neqrev; eauto.
  -
    unfold V_QATTRmq_msgsize in *.
    eapply nth_upd_neqrev; eauto.
  -
    unfold V_QATTRmq_curmsgs in *. 
    eapply nth_upd_neqrev; eauto.
    
Qed.

Lemma MqEIBArray_P_set_null_preserve: 
  forall vll1 vl vll2 qeibs vhold pos j wtp flg mm ms cm mqc,
    pos = Int.repr (Z.of_nat (length vll1)) ->
    Z.of_nat (length vll1) <= Int.max_unsigned ->
    Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
    (* V_OSSINFOType vl = Some (Vint32 t) ->  *)
    V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) -> 
    MqEIBAarray_P (Vint32 j) (vll1 ++ vl :: vll2) qeibs vhold ->
    MqEIBAarray_P (Vint32 j)  
                  (vll1 ++ (update_nth_val 5 vl Vnull) :: vll2) 
                  (set qeibs (Int.add pos j) (Null, wtp, flg, mm, ms, cm, mqc)) vhold.  
Proof.
  induction vll1; intros.
  -
    simpl in *.
    mytac.
    inverts H7.
    do 4 eexists.
    destruct x1 as [[[[[[]]]]]].
    lets Hcp: H10.
    eapply RHL_EIBlk_Q_P_get_pevent in Hcp.
    destruct Hcp.
    splits; eauto. 
    change ($ 0) with Int.zero.
    instantiate (1:= (Null, wtp, flg, mm, ms, cm, mqc)). 
    2: { eapply RHL_EIBlk_Q_P_null_constr; eauto. }
    rewrite Int.add_zero_l.
    assert (sig x2 (Null, wtp, flg, mm, ms, cm, mqc) = set (sig x2 (e, q, q0, q1, q2, q3, m)) x2 (Null, wtp, flg, mm, ms, cm, mqc)).
    eapply sig_set_sig.
    assert (join (sig x2 (Null, wtp, flg, mm, ms, cm, mqc)) x0
                 (set qeibs x2 (Null, wtp, flg, mm, ms, cm, mqc))).
    {
      rewrite H7.
      eapply join_set_l; eauto.
      apply get_indom. eexists. rewrite get_a_sig_a; auto.
    }
    auto.
  -
    assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))). 
    { eapply int_usign_eq; simpl length in *; auto with zarith. }
    assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
    { eapply int_usign_eq; simpl length in *; auto with zarith. }
    simpl in H7. simpl.
    mytac.
    inverts H7.
    do 4 eexists.
    splits; eauto.
    instantiate (1:= set x0 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) (Null, wtp, flg, mm, ms, cm, mqc)). 
    eapply MqattrMod.join_comm.
    eapply MqattrMod.map_join_set_none.
    eapply MqattrMod.join_comm. auto.
    eapply MqattrMod.get_sig_none.
    rewrite Int.add_commut.
    eapply pos_add_i_neq. rewrite Heq1.
    simpl length in *; auto with zarith.
    rewrite int_ltu_zero_eq_false; auto.
    auto.
    assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
    rewrite Int.add_permut.
    rewrite Int.add_commut.
    int auto; simpl length in *; auto with zarith.
    int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
    rewrite Heq.
    eapply IHvll1; eauto.
    simpl length in *; auto with zarith.
    rewrite Heq1 in H1.
    simpl length in H1.
    assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
    auto with zarith.
    rewrite H in H1.
    assert (0 <= Int.unsigned x2 + 1).
    pose proof (Int.unsigned_range_2 x2).
    auto with zarith.
    lets Hcp: H1.
    eapply Z_add_le_trans in Hcp; auto with zarith.
    assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
    int auto;simpl length in *; auto with zarith.
    rewrite H8. rewrite Heq2. auto.
Qed. 

Lemma MqEIBAarray_P_set_null_preserve_zero: 
  forall vll1 vl vll2 qeibs vhold i wtp flg mm ms cm mqc,
    length vll1 = Z.to_nat (Int.unsigned i) ->
    Int.unsigned i <= Int.max_unsigned ->
    V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) -> 
    MqEIBAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) qeibs vhold ->
    MqEIBAarray_P (Vint32 Int.zero) 
                  (vll1 ++ (update_nth_val 5 vl Vnull) :: vll2) 
                  (set qeibs i (Null, wtp, flg, mm, ms, cm, mqc)) vhold.   
Proof.
  introv Hlen Hrgn Hwtp Hflg Hmm Hms Hcm Hearr.
  assert (Hi: i = Int.add i Int.zero). 
  {  int auto. rewrite Z.add_0_r. rewrite Int.repr_unsigned. auto. }
  rewrite Hi.
  eapply MqEIBArray_P_set_null_preserve; eauto.
  rewrite Hlen.
  rewrite Z2Nat.id; auto.
  rewrite Int.repr_unsigned. auto.
  clear. int auto. 
  rewrite Hlen.
  rewrite Z2Nat.id; auto.
  int auto.
Qed.

Lemma Qattr_full_imp_no_free: 
  forall qattrl,
    Qattr_full_P qattrl ->
    ~(exists i, nth_Qattr_free_P i qattrl). 
Proof.
  unfold nth_Qattr_free_P.
  unfold Qattr_full_P.
  intros.
  do 2 (eapply Classical_Pred_Type.all_not_not_ex; intros).
  pure_auto.
Qed.

Lemma Qattr_free_imp_no_full:
  forall semvl,
    (exists i, nth_Qattr_free_P i semvl) ->
    ~(Qattr_full_P semvl). 
Proof.
  unfold nth_Qattr_free_P.
  unfold Qattr_full_P. 
  intros.
  pure_auto.
  do 3 destruct H.
  destruct H1.
  destruct H2.
  eapply H0; eauto.
Qed.


Lemma Qattr_free_dec: 
  forall semvl,
    (exists i, nth_Qattr_free_P i semvl) \/ Qattr_full_P semvl. 
Proof.
  intros.
  assert (Ht: (Qattr_full_P semvl) \/ ~(Qattr_full_P semvl)) by tauto. 
  destruct Ht. pure_auto.
  left.
  unfold nth_Qattr_free_P in *.
  unfold Qattr_full_P in *.
  eapply Classical_Pred_Type.not_all_ex_not in H.
  destruct H.
  eapply Classical_Pred_Type.not_all_ex_not in H.
  destruct H.
  eapply Classical_Prop.imply_to_and in H; destruct H.
  eapply Classical_Prop.imply_to_and in H0; destruct H0.
  destruct H.
  repeat eexists; eauto.
  tauto.
Qed.

Lemma Qattr_full_P_nil: Qattr_full_P nil. 
Proof.
  unfold Qattr_full_P.
  simpl.
  auto with zarith. 
Qed.

Lemma Qattr_full_P_succ : 
  forall a vl, Qattr_full_P (a :: vl) <-> (Qattr_full_P (a::nil) /\ Qattr_full_P vl).  
Proof.
  unfold Qattr_full_P. 
  (* simpl. *)
  split; intros.
  simpl in *.
  split; intros.
  eapply H. instantiate (1:= i). int auto.
  destruct (∘ i); tryfalse. auto.
  eapply H. instantiate (1:= (i + 1)). int auto.
  assert (Hi: (∘ (i + 1)) = ((∘ i) + (∘ 1))%nat).
  eapply nat_of_Z_plus; auto with zarith.
  rewrite Hi.
  change (∘ 1) with 1%nat.
  assert (Hi': (∘ i + 1)%nat = S (∘ i)).
  auto with zarith.
  rewrite Hi'. auto.
  destruct H.
  destruct H0.
  assert (Hi: i= 0 \/ i <> 0) by tauto.
  (* simpl in *. *)
  destruct Hi.
  eapply H. simpl in *. eauto with zarith. subst i. auto.
  eapply H2. instantiate (1:= i - 1). simpl in *. eauto with zarith.
  assert (Hsub: i = i - 1 +1).
  rewrite Z.sub_add. auto.
  rewrite Hsub in H1.
  assert (Hi: ∘ (i - 1 + 1) = ((∘ (i - 1)) + (∘ 1))%nat).
  eapply nat_of_Z_plus; auto with zarith.
  rewrite Hi in H1.
  change (∘ 1) with 1%nat in H1.
  assert (Hi': (∘ (i - 1) + 1)%nat = S (∘ (i - 1))) by auto with zarith.
  rewrite Hi' in H1.
  simpl in H1. auto.
Qed.

Lemma Qattr_full_P_split: 
  forall vl1 vl2, (Qattr_full_P vl1 /\ Qattr_full_P vl2)  <-> Qattr_full_P (vl1 ++ vl2). 
Proof.
  induction vl1; intros.
  simpl. split; try pure_auto. apply Qattr_full_P_nil. 
  simpl.
  rewrite Qattr_full_P_succ.
  rewrite Qattr_full_P_succ with (vl:= vl1 ++ vl2). 
  rewrite <- IHvl1.
  tauto.
Qed.

Lemma app_cons_inv:
  forall (l1 l2: list vallist) v l1' l2' v', 
    l1 ++ v :: l2 = l1' ++ v' :: l2' ->
    length l1 = length l1' -> 
    l1 = l1' /\ v = v' /\ l2 = l2'.
Proof.
  induction l1.
  intros.
  simpl in H0.
  destruct l1'.
  simpl in H.
  inverts H.
  splits; eauto.
  simpl in H0. inverts H0.

  introv Heq Hleneq.
  destruct l1'.
  simpl in Hleneq. inverts Hleneq.
  simpl in Hleneq.
  inverts Hleneq.
  simpl in Heq.
  inverts Heq.
  eapply IHl1 in H2; eauto.
  simpljoin1.
  splits; auto. 
Qed.

(* Lemma AMqAttr_split_frm: 
  forall s l vll1 vl vll2 P,
    s |= AMqAttr l (vll1 ++ (vl :: vll2)) ** P ->
    s |= EX idx b i,
              GV Mq_Attr @ mq_attr_t ∗ |-> Vptr (b, i) ** 
              Aarray_new (b, i) (Tarray mq_attr_t idx) vll1 **
              Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen mq_attr_t))) mq_attr_t vl **
              Aarray_new (b, (i+ᵢ  $ Z.of_nat ((S idx) * (typelen mq_attr_t)))) 
              (Tarray mq_attr_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)))) vll2 ** 
              [| new_array_type_vallist_match mq_attr_t (vll1 ++ (vl :: vll2)) |] **
              [| length (vll1 ++ (vl :: vll2)) = ∘ (OS_USER_MAX_EVENTS / 3) |] **
              [| length vll1 = idx /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) |] **
              [| Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 |] ** P. 
Proof.
  introv Hsat.
  assert (Hsat':=Hsat).
  sep destroy Hsat'.
  apply amqattr_len in H.
  clear H0.
  rename H into Hlen.
  assert (Hlenlt: (length vll1 < length (vll1++vl::vll2))%nat).
  {
    rewrite app_length.
    simpl.
    assert (He: (length vll1 = length vll1 + 0)%nat).
    {
      auto with arith.
    }
    rewrite He at 1. 
    apply plus_lt_compat_l.
    auto with arith.
  }
  lets H00: AMqAttr_unfold_any_idx_frm Hsat Hlenlt.
  sep normal in H00.
  sep destruct H00.
  sep split in H00.
  simpljoin1.
  apply app_cons_inv in H1; eauto.
  simpljoin1.
  exists (length x1). 
  do 2 eexists. 
  sep pauto.
Qed.  *)

Lemma AMqAttr_split_frm: 
  forall s b i vll1 vl vll2 P,
    s |= AMqAttr (b, i) (vll1 ++ (vl :: vll2)) ** P ->
    s |= EX idx (* b i *),
              GV Mq_Attr @ mq_attr_t ∗ |-> Vptr (b, i) ** 
              Aarray_new (b, i) (Tarray mq_attr_t idx) vll1 **
              Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen mq_attr_t))) mq_attr_t vl **
              Aarray_new (b, (i+ᵢ  $ Z.of_nat ((S idx) * (typelen mq_attr_t)))) 
              (Tarray mq_attr_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)))) vll2 ** 
              [| new_array_type_vallist_match mq_attr_t (vll1 ++ (vl :: vll2)) |] **
              [| length (vll1 ++ (vl :: vll2)) = ∘ (OS_USER_MAX_EVENTS / 3) |] **
              [| length vll1 = idx /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) |] **
              [| Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 |] ** P. 
Proof.
  introv Hsat.
  assert (Hsat':=Hsat).
  sep destroy Hsat'.
  apply amqattr_len in H.
  clear H0.
  rename H into Hlen.
  assert (Hlenlt: (length vll1 < length (vll1++vl::vll2))%nat).
  {
    rewrite app_length.
    simpl.
    assert (He: (length vll1 = length vll1 + 0)%nat).
    {
      auto with arith.
    }
    rewrite He at 1. 
    apply plus_lt_compat_l.
    auto with arith.
  }
  lets H00: AMqAttr_unfold_any_idx_frm Hsat Hlenlt.
  sep normal in H00.
  sep destruct H00.
  sep split in H00.
  simpljoin1.
  apply app_cons_inv in H1; eauto.
  simpljoin1.
  exists (length x1). 
  (* do 2 eexists. *) 
  sep pauto.
Qed. 

Lemma aqattr_len_frm: 
  forall s l vl P, s |= AMqAttr l vl ** P -> length vl = ∘ (OS_USER_MAX_EVENTS / 3).
Proof.  
  introv Hsat.
  destruct Hsat.
  simpl_sat H. simpljoin1.
  destruct H3.
  simpl_sat H. simpljoin1.
  auto.
Qed. 

Lemma nth_QAttr_free_P_range: 
  forall s l vl P i, s |= AMqAttr l vl ** P -> nth_Qattr_free_P i vl -> 0 <= i < OS_USER_MAX_EVENTS / 3.
Proof. 
  intros.
  funfold H0.
  apply aqattr_len_frm in H.
  rewrite H in *.
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  unfold nat_of_Z in H1.
  int auto.
Qed. 

Lemma qb_getnull:
  forall vl vll1 vll2 qattrb hld i,
    MqEIBAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) qattrb hld ->
    nth_Qattr_free_P i (vll1 ++ vl :: vll2) ->
    length vll1 = Z.to_nat i ->
    length (vll1 ++ vl :: vll2) = ∘ (OS_USER_MAX_EVENTS / 3) ->
    exists wtype flag maxm msize curm mqc,
      get qattrb (Int.repr i) = Some (Null, wtype, flag, maxm, msize, curm, mqc) /\
      V_QATTRpevent vl = Some Vnull.
Proof.
  introv He Hf Hl1 Hl2.
  funfold Hf.
  rewrite Hl2 in H0.
  (* change (Z.of_nat ∘ (OS_USER_MAX_EVENTS / 3)) with (OS_USER_MAX_EVENTS / 3) in H0. *)
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  unfold nat_of_Z in H0.
  assert (Z.of_nat (Z.to_nat (OS_USER_MAX_EVENTS / 3)) = (OS_USER_MAX_EVENTS / 3)).
  int auto.
  rewrite H3 in H0.
  assert (Hi_ran: Int.ltu ($ i) Int.zero = false /\ Int.unsigned ($ i) <= Int.max_unsigned).
  (* change (OS_USER_MAX_EVENTS / 3) with 6 in H0. *)
  int auto.
  destruct Hi_ran as (Hi1 & Hi2).
  assert (Hi: Int.unsigned (Int.repr i) = i).
  eapply int_usign_eq; auto.
  (* change (OS_USER_MAX_EVENTS / 3) with 6 in H0. *)
  int auto.
  unfold nat_of_Z in H1.
  rewrite <- Hl1 in H1.
  rewrite nth_vallist_get_idx in H1.
  inverts H1.
  rewrite <- Hi in Hl1.
  lets Hq: mqattr_corr He Hl1 Hi1 Hi2.
  mytac.
  unfold V_QATTRpevent in *.
  rewrite Hi in Hl1.
  rewrite H2 in H4.
  do 2 destruct H4; mytac; tryfalse.
  repeat eexists.
  apply H1.
  auto.
Qed.

Lemma qb_corr_alt: 
  forall i mqvl qattrb hld, 
    MqEIBAarray_P (Vint32 Int.zero) mqvl qattrb hld ->
    (i < (length mqvl))%nat ->
    length mqvl = ∘ (OS_USER_MAX_EVENTS / 3) ->
    exists vl et wtype flag maxm msize curm mqc, 
      nth_vallist i mqvl = Some vl /\
        get qattrb ($ (Z.of_nat i)) = Some (et, wtype, flag, maxm, msize, curm, mqc) /\
        (((et=Null /\ V_QATTRpevent vl =Some (Vnull)) \/  
          (et = Holder /\ V_QATTRpevent vl =Some (Vptr hld)) \/ 
          (exists eid , et = (Valid_Addr eid) /\ 
                 V_QATTRpevent vl = Some (Vptr eid) /\ eid <> hld)) /\ 
                 V_QATTRmq_waittype vl = Some (Vint32 wtype) /\ 
                 V_QATTRmq_flags vl = Some (Vint32 flag) /\ 
                 V_QATTRmq_maxmsg vl = Some (Vint32 maxm)  /\ 
                 V_QATTRmq_msgsize vl = Some (Vint32 msize) /\  
                 V_QATTRmq_curmsgs vl = Some (Vint32 curm)). 
Proof.
introv He Hi Hl.
destruct mqvl.
simpl in *. false.
auto with zarith.
assert (v :: mqvl <> nil ) by eauto.
lets Hsp: list_vallist_split_idx Hi H.
destruct Hsp. do 3 destruct H0.
rewrite H0 in *.
eapply mqattr_corr in He.
instantiate (1:= ($ Z.of_nat i)) in He.
destruct He. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2.
do 8 eexists. 
splits; pauto. 
subst i.
rewrite nth_vallist_get_idx. auto.
subst i.
(* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in Hl. *)
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
unfold nat_of_Z in Hl.
rewrite Hl in Hi.
int auto.
rewrite int_ltu_zero_eq_false; auto.
(* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in Hl. *)
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
unfold nat_of_Z in Hl.
rewrite Hl in Hi.
int auto.
Qed.

Lemma qb_corr_alt': 
  forall i mqvl qattrb hld, 
    MqEIBAarray_P (Vint32 Int.zero) mqvl qattrb hld ->
    (Int.unsigned i) < Z.of_nat (length mqvl) ->
    length mqvl = ∘ (OS_USER_MAX_EVENTS / 3) ->
    exists vl et wtype flag maxm msize curm mqc, 
      nth_vallist ∘ (Int.unsigned i) mqvl = Some vl /\
        get qattrb i = Some (et, wtype, flag, maxm, msize, curm, mqc) /\
        (((et = Null /\ V_QATTRpevent vl = Some (Vnull)) \/  
          (et = Holder /\ V_QATTRpevent vl =Some (Vptr hld)) \/ 
          (exists eid , et = (Valid_Addr eid) /\ 
                 V_QATTRpevent vl = Some (Vptr eid) /\ eid <> hld))/\ 
                 V_QATTRmq_waittype vl = Some (Vint32 wtype) /\ 
                 V_QATTRmq_flags vl = Some (Vint32 flag) /\ 
                 V_QATTRmq_maxmsg vl = Some (Vint32 maxm) /\ 
                 V_QATTRmq_msgsize vl = Some (Vint32 msize) /\  
                 V_QATTRmq_curmsgs vl = Some (Vint32 curm)). 
Proof.
introv He Hi Hl.
eapply qb_corr_alt in He.
instantiate (1:= ∘ (Int.unsigned i)) in He.
assert (($ Z.of_nat ∘ (Int.unsigned i)) = i).
(* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in Hl. *)
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
(* unfold nat_of_Z in Hl. *)
rewrite Hl in Hi.
unfold nat_of_Z in *.
assert (Z.of_nat (Z.to_nat (Int.unsigned i)) = Int.unsigned i).
apply Z2Nat.id.
int auto.
rewrite H.
apply Int.repr_unsigned.
rewrite H in He.
auto.
unfold nat_of_Z in *.
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
(* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in Hl. *)
rewrite Hl in *.
int auto.
auto.
Qed.

Lemma qb_get_not_null: 
  forall mqvl qattrb hld, 
    MqEIBAarray_P (Vint32 Int.zero) mqvl qattrb hld ->
    Qattr_full_P mqvl ->
    length mqvl = ∘ (OS_USER_MAX_EVENTS / 3) ->
    ~(exists i wtype flag maxm msize curm mqc,
          get qattrb i = Some (Null, wtype, flag, maxm, msize, curm, mqc) /\ 0 <= (Int.unsigned i) < Z.of_nat (length mqvl)).
Proof.
introv He Hf Hl.
funfold Hf.
introv H. 
do 7 destruct H.
eapply qb_corr_alt' in He; eauto.
instantiate (1:= x) in He.
destruct He. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
destruct H. destruct H0. destruct H0. destruct H2. destruct H3.
unfold get in H, H2.
unfold MqattrMap in H, H2.
rewrite H2 in H. inverts H. 
destruct H3.
destruct H. eapply Hf; eauto.
destruct H. destruct H. tryfalse. 
destruct H. destruct H. tryfalse.
destruct H. destruct H0. 
auto.
Qed.

Lemma new_array_type_vallist_match_split_mqattr: 
  forall mqvl vll1 vll2 vl, 
    new_array_type_vallist_match mq_attr_t mqvl ->
    mqvl = vll1 ++ (vl::vll2) ->
    new_array_type_vallist_match mq_attr_t vll1 /\
      new_array_type_vallist_match mq_attr_t vll2 /\ 
      struct_type_vallist_match mq_attr_t vl.   
Proof.
  introv Hmatch Hlst.
  lets Hsp2 : new_array_type_vallist_match_split2 Hmatch Hlst.
  destruct Hsp2.
  split; auto.
  simpl in H0.
  destruct H0.
  split; auto.
Qed.

Lemma MqEIBAarray_P_hold_for_update_to_hold:
forall vll1 vl vll2 qattrb vhold pos j wtp flg mm ms cm mqc,
    pos = Int.repr (Z.of_nat (length vll1)) ->
    Z.of_nat (length vll1) <= Int.max_unsigned ->
    Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
    V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) -> 
    MqEIBAarray_P (Vint32 j) (vll1 ++ vl :: vll2) qattrb vhold ->
    MqEIBAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 5 vl (Vptr vhold)) :: vll2)
                        (set qattrb (Int.add pos j) (Holder,wtp, flg, mm, ms, cm, mqc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H7.
do 4 eexists.
destruct x1 as [et' mqc'].
destruct et' as [et' cm']. destruct et' as [et' ms'].
destruct et' as [et' mm']. destruct et' as [et' flg'].
destruct et' as [et' wtp']. 
lets Hcp: H10.
eapply RHL_EIBlk_Q_P_get_pevent in Hcp.
destruct Hcp.
splits; eauto.
change ($ 0) with Int.zero.
instantiate (1:= (Holder,wtp, flg, mm, ms, cm, mqc)).
2: { eapply RHL_EIBlk_Q_P_set_to_hold; eauto.  }
rewrite Int.add_zero_l.
eapply MqattrMod_get_join_sig_set; eauto.
eapply MqattrMod_join_get_none_r; [idtac | eauto].
eapply MqattrMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H7. simpl.
mytac.
inverts H7.
do 4 eexists.
splits; eauto.
instantiate (1:= set x0 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) (Holder, wtp, flg, mm, ms, cm, mqc)).
eapply MqattrMod.join_comm.
eapply MqattrMod.map_join_set_none.
eapply MqattrMod.join_comm. auto.
eapply MqattrMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H8. rewrite Heq2. auto.
Qed.

Lemma MqEIBAarray_P_hold_for_update_to_hold':
forall vll1 vl vll2 qattrb vhold pos wtp flg mm ms cm mqc,
length vll1 = Z.to_nat pos ->
0 <= pos <= Int.max_unsigned ->
  V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) -> 
MqEIBAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) qattrb vhold ->
MqEIBAarray_P (Vint32 Int.zero) 
                        (vll1 ++ (update_nth_val 5 vl (Vptr vhold)) :: vll2)
                        (set qattrb (Int.repr pos) (Holder,wtp, flg, mm, ms, cm, mqc)) vhold.
Proof.
intros.
lets Hr: Int.unsigned_repr H0.
destruct H0.
eapply MqEIBAarray_P_hold_for_update_to_hold in H6.
rewrite Int.add_zero in H6.
eauto.
eapply Z2Nat.id in H0.
rewrite <- H0.  rewrite H. auto.
eapply Z2Nat.id in H0.
rewrite H.  rewrite H0. auto.
rewrite Int.unsigned_zero. 
auto with zarith.
auto. auto. auto. auto. auto.
Qed.

Lemma RHL_EIBlk_Q_P_set_to_null:
forall vl vhold v wtp flg mm ms cm mqc,
    V_QATTRpevent vl = Some v ->
    V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) ->
RHL_EIBlk_Q_P (update_nth_val 5 vl Vnull) (Null ,wtp, flg, mm, ms, cm, mqc) vhold.
Proof.
unfold RHL_EIBlk_Q_P.
intros.
inverts H5.
splits.
2 :{ eapply nth_upd_neqrev; auto. }
2 :{ eapply nth_upd_neqrev; auto. }
2 :{ eapply nth_upd_neqrev; auto. }
2 :{ eapply nth_upd_neqrev; auto. }
2 :{ eapply nth_upd_neqrev; auto. }
left. unfold V_QATTRpevent in *.
splits;auto.
eapply update_nth. eauto.

Qed.

Lemma RHL_EIBlk_Q_P_set_to_tid:
forall vl vhold v pid wtp flg mm ms cm mqc,
    V_QATTRpevent vl = Some v ->
    V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) ->
  pid <> vhold ->
  RHL_EIBlk_Q_P (update_nth_val 5 vl (Vptr pid)) (Valid_Addr pid,wtp, flg, mm, ms, cm, mqc) vhold.
Proof.
unfold RHL_EIBlk_Q_P.
intros.
inverts H6.
splits.
2 :{ eapply nth_upd_neqrev; auto. }
2 :{ eapply nth_upd_neqrev; auto. }
2 :{ eapply nth_upd_neqrev; auto. }
2 :{ eapply nth_upd_neqrev; auto. }
2 :{ eapply nth_upd_neqrev; auto. }

right;right.
unfold V_QATTRpevent in *.
unfold V_QATTRmq_waittype in *.
unfold V_QATTRmq_flags in *.
unfold V_QATTRmq_maxmsg in *.
unfold V_QATTRmq_msgsize in *.
unfold V_QATTRmq_curmsgs in *.
eexists.
splits; auto.
eapply update_nth. eauto.
Qed.

Lemma RHL_EIBlk_Q_P_set_mq_maxm:
forall vl vhold et wtp flg mm ms cm mqc mm',
RHL_EIBlk_Q_P vl (et,wtp,flg,mm,ms,cm,mqc) vhold ->
RHL_EIBlk_Q_P (update_nth_val 2 vl (Vint32 mm')) (et,wtp,flg,mm',ms,cm,mqc) vhold.
Proof.
unfold RHL_EIBlk_Q_P.
intros.
inverts H0.
unfold V_QATTRpevent in *;
unfold V_QATTRmq_waittype in*;
unfold V_QATTRmq_flags in*;
unfold V_QATTRmq_maxmsg in*;
unfold V_QATTRmq_msgsize in*;
unfold V_QATTRmq_curmsgs in *.

specialize (H _ _ _ _ _ _  _ (eq_refl _)).
destructs H.
splits; (try (eapply nth_upd_neqrev; auto; fail)).
2:{ eapply update_nth. eauto. }

destruct H as [H' | [H' | H']]; mytac; [left | right; left | do 2 right].

splits; eauto.
eapply nth_upd_neqrev; eauto.
splits; eauto.
eapply nth_upd_neqrev; eauto.
eexists.
splits; eauto.
eapply nth_upd_neqrev; eauto.
Qed.

Lemma RHL_EIBlk_Q_P_set_mq_ms:
forall vl vhold et wtp flg mm ms cm mqc ms',
RHL_EIBlk_Q_P vl (et,wtp,flg,mm,ms,cm,mqc) vhold ->
RHL_EIBlk_Q_P (update_nth_val 3 vl (Vint32 ms')) (et,wtp,flg,mm,ms',cm,mqc) vhold.
Proof.
unfold RHL_EIBlk_Q_P.
intros.
inverts H0.
unfold V_QATTRpevent in *;
unfold V_QATTRmq_waittype in*;
unfold V_QATTRmq_flags in*;
unfold V_QATTRmq_maxmsg in*;
unfold V_QATTRmq_msgsize in*;
unfold V_QATTRmq_curmsgs in *.

specialize (H _ _ _ _ _ _ _ (eq_refl _)).
destructs H.
splits; (try (eapply nth_upd_neqrev; auto; fail)).
2:{ eapply update_nth. eauto. }

destruct H as [H' | [H' | H']]; mytac; [left | right; left | do 2 right].

splits; eauto.
eapply nth_upd_neqrev; eauto.
splits; eauto.
eapply nth_upd_neqrev; eauto.
eexists.
splits; eauto.
eapply nth_upd_neqrev; eauto.
Qed.

Lemma RHL_EIBlk_Q_P_set_mq_flg:
forall vl vhold et wtp flg mm ms cm mqc flg',
RHL_EIBlk_Q_P vl (et,wtp,flg,mm,ms,cm,mqc) vhold ->
RHL_EIBlk_Q_P (update_nth_val 1 vl (Vint32 flg')) (et,wtp,flg',mm,ms,cm,mqc) vhold.
Proof.
unfold RHL_EIBlk_Q_P.
intros.
inverts H0.
unfold V_QATTRpevent in *;
unfold V_QATTRmq_waittype in*;
unfold V_QATTRmq_flags in*;
unfold V_QATTRmq_maxmsg in*;
unfold V_QATTRmq_msgsize in*;
unfold V_QATTRmq_curmsgs in *.

specialize (H _ _ _ _ _ _ _ (eq_refl _)).
destructs H.
splits; (try (eapply nth_upd_neqrev; auto; fail)).
2:{ eapply update_nth. eauto. }

destruct H as [H' | [H' | H']]; mytac; [left | right; left | do 2 right].

splits; eauto.
eapply nth_upd_neqrev; eauto.
splits; eauto.
eapply nth_upd_neqrev; eauto.
eexists.
splits; eauto.
eapply nth_upd_neqrev; eauto.
Qed.

Lemma RHL_EIBlk_Q_P_set_mq_wtp:
forall vl vhold et wtp flg mm ms cm mqc wtp',
RHL_EIBlk_Q_P vl (et,wtp,flg,mm,ms,cm, mqc) vhold ->
RHL_EIBlk_Q_P (update_nth_val 0 vl (Vint32 wtp')) (et,wtp',flg,mm,ms,cm,mqc) vhold.
Proof.
unfold RHL_EIBlk_Q_P.
intros.
inverts H0.
unfold V_QATTRpevent in *;
unfold V_QATTRmq_waittype in*;
unfold V_QATTRmq_flags in*;
unfold V_QATTRmq_maxmsg in*;
unfold V_QATTRmq_msgsize in*;
unfold V_QATTRmq_curmsgs in *.

specialize (H _ _ _ _ _ _ _ (eq_refl _)).
destructs H.
splits; (try (eapply nth_upd_neqrev; auto; fail)).
2:{ eapply update_nth. eauto. }

destruct H as [H' | [H' | H']]; mytac; [left | right; left | do 2 right].

splits; eauto.
eapply nth_upd_neqrev; eauto.
splits; eauto.
eapply nth_upd_neqrev; eauto.
eexists.
splits; eauto.
eapply nth_upd_neqrev; eauto.
Qed.

Lemma MqEIBAarray_P_hold_for_update_to_null:
forall vll1 vl vll2 qattrb vhold pos j wtp flg mm ms cm mqc,
    pos = Int.repr (Z.of_nat (length vll1)) ->
    Z.of_nat (length vll1) <= Int.max_unsigned ->
    Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
    V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) -> 
    MqEIBAarray_P (Vint32 j) (vll1 ++ vl :: vll2) qattrb vhold ->
    MqEIBAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 5 vl Vnull) :: vll2)
                        (set qattrb (Int.add pos j) (Null ,wtp, flg, mm, ms, cm, mqc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H7.
do 4 eexists.
destruct x1 as [et' mqc'].
destruct et' as [et' cm']. destruct et' as [et' ms'].
destruct et' as [et' mm']. destruct et' as [et' flg'].
destruct et' as [et' wtp']. 
lets Hcp: H10.
eapply RHL_EIBlk_Q_P_get_pevent in Hcp.
destruct Hcp.
splits; eauto.
change ($ 0) with Int.zero.
instantiate (1:= (Null,wtp, flg, mm, ms, cm, mqc)).
2: { eapply RHL_EIBlk_Q_P_set_to_null; eauto.  }
rewrite Int.add_zero_l.
eapply MqattrMod_get_join_sig_set; eauto.
eapply MqattrMod_join_get_none_r; [idtac | eauto].
eapply MqattrMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H7. simpl.
mytac.
inverts H7.
do 4 eexists.
splits; eauto.
instantiate (1:= set x0 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) (Null,wtp, flg, mm, ms, cm,mqc)).
eapply MqattrMod.join_comm.
eapply MqattrMod.map_join_set_none.
eapply MqattrMod.join_comm. auto.
eapply MqattrMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H8. rewrite Heq2. auto.
Qed.

Lemma MqEIBAarray_P_hold_for_update_to_null':
forall vll1 vl vll2 qattrb vhold pos wtp flg mm ms cm mqc,
length vll1 = Z.to_nat pos ->
0 <= pos <= Int.max_unsigned ->
  V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) -> 
MqEIBAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) qattrb vhold ->
MqEIBAarray_P (Vint32 Int.zero) 
                        (vll1 ++ (update_nth_val 5 vl Vnull) :: vll2)
                        (set qattrb (Int.repr pos) (Null,wtp, flg, mm, ms, cm, mqc)) vhold.
Proof.
intros.
lets Hr: Int.unsigned_repr H0.
destruct H0.
eapply MqEIBAarray_P_hold_for_update_to_null in H6.
rewrite Int.add_zero in H6.
eauto.
eapply Z2Nat.id in H0.
rewrite <- H0.  rewrite H. auto.
eapply Z2Nat.id in H0.
rewrite H.  rewrite H0. auto.
rewrite Int.unsigned_zero. 
auto with zarith.
auto. auto. auto. auto. auto.
Qed.

Lemma MqEIBAarray_P_hold_for_update_to_tid:
forall vll1 vl vll2 qattrb vhold pos j pid wtp flg mm ms cm mqc,
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
    V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) -> 
pid <> vhold ->
MqEIBAarray_P (Vint32 j) (vll1 ++ vl :: vll2) qattrb vhold ->
MqEIBAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 5 vl (Vptr pid)) :: vll2)
                        (set qattrb (Int.add pos j) (Valid_Addr pid,wtp, flg, mm, ms, cm, mqc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H8.
do 4 eexists.
destruct x1 as [et' mqc'].
destruct et' as [et' cm']. destruct et' as [et' ms'].
destruct et' as [et' mm']. destruct et' as [et' flg'].
destruct et' as [et' wtp']. 
lets Hcp: H11.
eapply RHL_EIBlk_Q_P_get_pevent in Hcp.
destruct Hcp.
splits; eauto.
change ($ 0) with Int.zero.
instantiate (1:= (Valid_Addr pid,wtp, flg, mm, ms, cm, mqc)).
2: { eapply RHL_EIBlk_Q_P_set_to_tid; eauto. }
rewrite Int.add_zero_l.
eapply MqattrMod_get_join_sig_set; eauto.
eapply MqattrMod_join_get_none_r; [idtac | eauto].
eapply MqattrMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H8. simpl.
mytac.
inverts H8.
do 4 eexists.
splits; eauto.
instantiate (1:= set x0 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) (Valid_Addr pid,wtp, flg, mm, ms, cm, mqc)).
eapply MqattrMod.join_comm.
eapply MqattrMod.map_join_set_none.
eapply MqattrMod.join_comm. auto.
eapply MqattrMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H9. rewrite Heq2. auto.
Qed.

Lemma MqEIBAarray_P_hold_for_update_to_tid':
forall vll1 vl vll2 qattrb vhold pos pid wtp flg mm ms cm mqc,
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned pos <= Int.max_unsigned ->
    V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) -> 
pid <> vhold ->
MqEIBAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) qattrb vhold ->
MqEIBAarray_P (Vint32 Int.zero) 
                        (vll1 ++ (update_nth_val 5 vl (Vptr pid)) :: vll2)
                        (set qattrb pos (Valid_Addr pid,wtp, flg, mm, ms, cm, mqc)) vhold.
Proof.
intros.
lets Hnew: MqEIBAarray_P_hold_for_update_to_tid H H0.
instantiate (9:= Int.zero) in Hnew.
change (Int.unsigned Int.zero) with 0 in Hnew.
rewrite Int.add_commut in Hnew.
rewrite Int.add_zero_l in Hnew.
rewrite Z.add_0_l in Hnew.
eapply Hnew;eauto.
Qed.


Lemma MqEIBAarray_P_hold_for_update_mq_maxm:
forall vll1 vl vll2 qattrb vhold pos j et wtp flg mm ms cm mqc mm',
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
MqattrMod.get qattrb (Int.add pos j) = Some (et,wtp, flg, mm, ms, cm, mqc) ->
    V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) -> 
MqEIBAarray_P (Vint32 j) (vll1 ++ vl :: vll2) qattrb vhold ->
MqEIBAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 2 vl (Vint32 mm')) :: vll2)
                        (set qattrb (Int.add pos j) (et,wtp, flg, mm', ms, cm, mqc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H8.
do 4 eexists.
destruct x1 as [et0 mqc0].
destruct et0 as [et0 cm0]. destruct et0 as [et0 ms0].
destruct et0 as [et0 mm0]. destruct et0 as [et0 flg0].
destruct et0 as [et0 wtp0]. 
lets Hget: MqattrMod.join_sig_get H10.
change ($ 0) with Int.zero in *.
rewrite Int.add_zero_l in H2.
rewrite H2 in Hget.
inverts Hget.
lets Hcp: H11.
eapply RHL_EIBlk_Q_P_get_pevent in Hcp.
destruct Hcp.
splits; eauto.
(* change ($ 0) with Int.zero. *)
instantiate (1:= (et,wtp, flg, mm', ms, cm, mqc)).
2: { eapply RHL_EIBlk_Q_P_set_mq_maxm; eauto. }
rewrite Int.add_zero_l.
eapply MqattrMod_get_join_sig_set; eauto.
eapply MqattrMod_join_get_none_r; [idtac | eauto].
eapply MqattrMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H8. simpl.
mytac.
inverts H8.
do 4 eexists.
splits; eauto.
instantiate (1:= set x0 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) (et,wtp, flg, mm', ms, cm, mqc)).
eapply MqattrMod.join_comm.
eapply MqattrMod.map_join_set_none.
eapply MqattrMod.join_comm. auto.
eapply MqattrMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H9. rewrite Heq2. auto.
eapply MqattrMod.map_join_get_none in H10.
erewrite H2 in H10.
rewrite H10.
rewrite Heq. auto. 
eapply MqattrMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
Qed.

Lemma MqEIBAarray_P_hold_for_update_mq_maxm':
forall vll1 vl vll2 qattrb vhold pos et wtp flg mm ms cm mqc mm',
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned pos <= Int.max_unsigned ->
MqattrMod.get qattrb pos = Some (et,wtp, flg, mm, ms, cm, mqc) ->
    V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) -> 
MqEIBAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) qattrb vhold ->
MqEIBAarray_P (Vint32 Int.zero) 
                        (vll1 ++ (update_nth_val 2 vl (Vint32 mm')) :: vll2)
                        (set qattrb pos (et,wtp, flg, mm', ms, cm, mqc)) vhold.
Proof.
intros.
lets Hnew: MqEIBAarray_P_hold_for_update_mq_maxm H H0.
instantiate (9:= Int.zero) in Hnew.
change (Int.unsigned Int.zero) with 0 in Hnew.
rewrite Int.add_commut in Hnew.
rewrite Int.add_zero_l in Hnew.
rewrite Z.add_0_l in Hnew.
eapply Hnew;eauto. 
Qed.

Lemma MqEIBAarray_P_hold_for_update_mq_msgs:
forall vll1 vl vll2 qattrb vhold pos j et wtp flg mm ms cm mqc ms',
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
MqattrMod.get qattrb (Int.add pos j) = Some (et,wtp, flg, mm, ms, cm, mqc) ->
    V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) -> 
MqEIBAarray_P (Vint32 j) (vll1 ++ vl :: vll2) qattrb vhold ->
MqEIBAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 3 vl (Vint32 ms')) :: vll2)
                        (set qattrb (Int.add pos j) (et,wtp, flg, mm, ms', cm, mqc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H8.
do 4 eexists.
destruct x1 as [et0 mqc0].
destruct et0 as [et0 cm0]. destruct et0 as [et0 ms0].
destruct et0 as [et0 mm0]. destruct et0 as [et0 flg0].
destruct et0 as [et0 wtp0]. 
lets Hget: MqattrMod.join_sig_get H10.
change ($ 0) with Int.zero in *.
rewrite Int.add_zero_l in H2.
rewrite H2 in Hget.
inverts Hget.
lets Hcp: H11.
eapply RHL_EIBlk_Q_P_get_pevent in Hcp.
destruct Hcp.
splits; eauto.
(* change ($ 0) with Int.zero. *)
instantiate (1:= (et,wtp, flg, mm, ms', cm, mqc)).
2: { eapply RHL_EIBlk_Q_P_set_mq_ms; eauto. }
rewrite Int.add_zero_l.
eapply MqattrMod_get_join_sig_set; eauto.
eapply MqattrMod_join_get_none_r; [idtac | eauto].
eapply MqattrMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H8. simpl.
mytac.
inverts H8.
do 4 eexists.
splits; eauto.
instantiate (1:= set x0 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) (et,wtp, flg, mm, ms', cm, mqc)).
eapply MqattrMod.join_comm.
eapply MqattrMod.map_join_set_none.
eapply MqattrMod.join_comm. auto.
eapply MqattrMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H9. rewrite Heq2. auto.
eapply MqattrMod.map_join_get_none in H10.
erewrite H2 in H10.
rewrite H10.
rewrite Heq. auto. 
eapply MqattrMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
Qed.

Lemma MqEIBAarray_P_hold_for_update_mq_mgs':
forall vll1 vl vll2 qattrb vhold pos et wtp flg mm ms cm mqc ms',
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned pos <= Int.max_unsigned ->
MqattrMod.get qattrb pos = Some (et,wtp, flg, mm, ms, cm, mqc) ->
    V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) -> 
MqEIBAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) qattrb vhold ->
MqEIBAarray_P (Vint32 Int.zero) 
                        (vll1 ++ (update_nth_val 3 vl (Vint32 ms')) :: vll2)
                        (set qattrb pos (et,wtp, flg, mm, ms', cm, mqc)) vhold.
Proof.
intros.
lets Hnew: MqEIBAarray_P_hold_for_update_mq_msgs H H0.
instantiate (9:= Int.zero) in Hnew.
change (Int.unsigned Int.zero) with 0 in Hnew.
rewrite Int.add_commut in Hnew.
rewrite Int.add_zero_l in Hnew.
rewrite Z.add_0_l in Hnew.
eapply Hnew;eauto. 
Qed.

Lemma MqEIBAarray_P_hold_for_update_mq_flg:
forall vll1 vl vll2 qattrb vhold pos j et wtp flg mm ms cm mqc flg',
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
MqattrMod.get qattrb (Int.add pos j) = Some (et,wtp, flg, mm, ms, cm, mqc) ->
    V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) -> 
MqEIBAarray_P (Vint32 j) (vll1 ++ vl :: vll2) qattrb vhold ->
MqEIBAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 1 vl (Vint32 flg')) :: vll2)
                        (set qattrb (Int.add pos j) (et,wtp, flg', mm, ms, cm, mqc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H8.
do 4 eexists.
destruct x1 as [et0 mqc0].
destruct et0 as [et0 cm0]. destruct et0 as [et0 ms0].
destruct et0 as [et0 mm0]. destruct et0 as [et0 flg0].
destruct et0 as [et0 wtp0]. 
lets Hget: MqattrMod.join_sig_get H10.
change ($ 0) with Int.zero in *.
rewrite Int.add_zero_l in H2.
rewrite H2 in Hget.
inverts Hget.
lets Hcp: H11.
eapply RHL_EIBlk_Q_P_get_pevent in Hcp.
destruct Hcp.
splits; eauto.
(* change ($ 0) with Int.zero. *)
instantiate (1:= (et,wtp, flg', mm, ms, cm, mqc)).
2: { eapply RHL_EIBlk_Q_P_set_mq_flg; eauto. }
rewrite Int.add_zero_l.
eapply MqattrMod_get_join_sig_set; eauto.
eapply MqattrMod_join_get_none_r; [idtac | eauto].
eapply MqattrMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H8. simpl.
mytac.
inverts H8.
do 4 eexists.
splits; eauto.
instantiate (1:= set x0 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) (et,wtp, flg', mm, ms, cm, mqc)).
eapply MqattrMod.join_comm.
eapply MqattrMod.map_join_set_none.
eapply MqattrMod.join_comm. auto.
eapply MqattrMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H9. rewrite Heq2. auto.
eapply MqattrMod.map_join_get_none in H10.
erewrite H2 in H10.
rewrite H10.
rewrite Heq. auto. 
eapply MqattrMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
Qed.

Lemma MqEIBAarray_P_hold_for_update_mq_flg':
forall vll1 vl vll2 qattrb vhold pos et wtp flg mm ms cm mqc flg',
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned pos <= Int.max_unsigned ->
MqattrMod.get qattrb pos = Some (et,wtp, flg, mm, ms, cm, mqc) ->
    V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) -> 
MqEIBAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) qattrb vhold ->
MqEIBAarray_P (Vint32 Int.zero) 
                        (vll1 ++ (update_nth_val 1 vl (Vint32 flg')) :: vll2)
                        (set qattrb pos (et,wtp, flg', mm, ms, cm, mqc)) vhold.
Proof.
intros.
lets Hnew: MqEIBAarray_P_hold_for_update_mq_flg H H0.
instantiate (9:= Int.zero) in Hnew.
change (Int.unsigned Int.zero) with 0 in Hnew.
rewrite Int.add_commut in Hnew.
rewrite Int.add_zero_l in Hnew.
rewrite Z.add_0_l in Hnew.
eapply Hnew;eauto. 
Qed.

Lemma MqEIBAarray_P_hold_for_update_mq_wtp:
forall vll1 vl vll2 qattrb vhold pos j et wtp flg mm ms cm mqc wtp',
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
MqattrMod.get qattrb (Int.add pos j) = Some (et,wtp, flg, mm, ms, cm, mqc) ->
    V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) -> 
MqEIBAarray_P (Vint32 j) (vll1 ++ vl :: vll2) qattrb vhold ->
MqEIBAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 0 vl (Vint32 wtp')) :: vll2)
                        (set qattrb (Int.add pos j) (et,wtp', flg, mm, ms, cm, mqc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H8.
do 4 eexists.
destruct x1 as [et0 mqc0].
destruct et0 as [et0 cm0]. destruct et0 as [et0 ms0].
destruct et0 as [et0 mm0]. destruct et0 as [et0 flg0].
destruct et0 as [et0 wtp0]. 
lets Hget: MqattrMod.join_sig_get H10.
change ($ 0) with Int.zero in *.
rewrite Int.add_zero_l in H2.
rewrite H2 in Hget.
inverts Hget.
lets Hcp: H11.
eapply RHL_EIBlk_Q_P_get_pevent in Hcp.
destruct Hcp.
splits; eauto.
(* change ($ 0) with Int.zero. *)
instantiate (1:= (et,wtp', flg, mm, ms, cm, mqc)).
2: { eapply RHL_EIBlk_Q_P_set_mq_wtp; eauto. }
rewrite Int.add_zero_l.
eapply MqattrMod_get_join_sig_set; eauto.
eapply MqattrMod_join_get_none_r; [idtac | eauto].
eapply MqattrMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H8. simpl.
mytac.
inverts H8.
do 4 eexists.
splits; eauto.
instantiate (1:= set x0 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) (et,wtp', flg, mm, ms, cm, mqc)).
eapply MqattrMod.join_comm.
eapply MqattrMod.map_join_set_none.
eapply MqattrMod.join_comm. auto.
eapply MqattrMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H9. rewrite Heq2. auto.
eapply MqattrMod.map_join_get_none in H10.
erewrite H2 in H10.
rewrite H10.
rewrite Heq. auto. 
eapply MqattrMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
Qed.

Lemma MqEIBAarray_P_hold_for_update_mq_wtp':
forall vll1 vl vll2 qattrb vhold pos et wtp flg mm ms cm mqc wtp',
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned pos <= Int.max_unsigned ->
MqattrMod.get qattrb pos = Some (et,wtp, flg, mm, ms, cm, mqc) ->
    V_QATTRmq_waittype vl = Some (Vint32 wtp) ->
    V_QATTRmq_flags vl = Some (Vint32 flg) ->
    V_QATTRmq_maxmsg vl = Some (Vint32 mm) ->
    V_QATTRmq_msgsize vl = Some (Vint32 ms) ->
    V_QATTRmq_curmsgs vl = Some (Vint32 cm) -> 
MqEIBAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) qattrb vhold ->
MqEIBAarray_P (Vint32 Int.zero) 
                        (vll1 ++ (update_nth_val 0 vl (Vint32 wtp')) :: vll2)
                        (set qattrb pos (et,wtp', flg, mm, ms, cm, mqc)) vhold.
Proof.
intros.
lets Hnew: MqEIBAarray_P_hold_for_update_mq_wtp H H0.
instantiate (9:= Int.zero) in Hnew.
change (Int.unsigned Int.zero) with 0 in Hnew.
rewrite Int.add_commut in Hnew.
rewrite Int.add_zero_l in Hnew.
rewrite Z.add_0_l in Hnew.
eapply Hnew;eauto. 
Qed.

(* preperation about OSQ *)

Lemma RH_EIB_ECB_Q_P_mq_set_preserve: 
  forall els qeibs sid  ml n pwl wl ml' n' pwl' wl', 
    RH_EIBlk_ECBlk_Q_P els qeibs -> 
    get els sid = Some (absmsgq ml n pwl ,wl) ->
    RH_EIBlk_ECBlk_Q_P (set els sid (absmsgq ml' n' pwl' ,wl')) qeibs. 
Proof.
  introv Hrh Hget.
  unfold RH_EIBlk_ECBlk_Q_P in *.
  introv Hget'.
  casetac sid eid Ht Hf.
  - subst.
    lets H00: Hrh Hget'.
    simpljoin1.
     rewrite join_lib.set_a_get_a; eauto.
  - rewrite join_lib.set_a_get_a'; eauto. 
Qed.

Lemma RH_SEM_EINFO_ECB_P_mq_set_preserve : 
  forall els sid embls ml n pwl wl ml' n' pwl' wl', 
    RH_SEM_EINFO_ECB_P els embls ->
    EcbMod.get els sid = Some (absmsgq ml n pwl ,wl) ->
    RH_SEM_EINFO_ECB_P (set els sid (absmsgq ml' n' pwl' ,wl')) embls.
Proof.
  introv Hrh Hget.
  unfold RH_SEM_EINFO_ECB_P in *.
  introv Hget'.
  casetac sid eid Ht Hf.
  - subst.
    lets H00: Hrh Hget'.
    simpljoin1.
    unfold get in *; unfold EcbMap,EmbMap in*.
    rewrite Hget in H.
    inverts H.
  - rewrite join_lib.set_a_get_a'; eauto. 
Qed.

Lemma RH_MUX_EIB_ECB_P_mq_set_preserve:
  forall muxeibs els sid ml n pwl wl ml' n' pwl' wl', 
    RH_ECBlk_EIBlk_Mux_P muxeibs els ->
    EcbMod.get els sid = Some (absmsgq ml n pwl ,wl) ->
    RH_ECBlk_EIBlk_Mux_P muxeibs (set els sid (absmsgq ml' n' pwl' ,wl')). 
Proof.
  introv Hrh Hget.
  unfold RH_ECBlk_EIBlk_Mux_P in *.
  introv Hget' Htpeq.
  subst eid_tp.
  casetac sid eid Ht Hf.
  -
    subst.
    lets H00: Hrh Hget'.
     specialize (H00 (eq_refl _)).
    simpljoin1.
    unfold get in *; unfold EcbMap,EmbMap in*.
    rewrite Hget in H.
    inverts H.
  - rewrite join_lib.set_a_get_a'; eauto. 
Qed.

Lemma sem_eib_ecb_del_q_preserve: 
  forall semeibs els msgs maxlen pwl wl els' eid, 
    RH_SEM_EINFO_ECB_P els semeibs ->
    join els' (sig eid (absmsgq msgs maxlen pwl, wl)) els ->
    ~semeib_ref semeibs eid ->
    RH_SEM_EINFO_ECB_P els' semeibs. 
Proof.
  introv Heibecb Hjo Hnref.
  unfold RH_SEM_EINFO_ECB_P in *.
  introv Hgetpos.
  casetac eid0 eid Heq Hneq.
  subst.
  unfold semeib_ref in Hnref.
  false. apply Hnref. repeat eexists. eauto.
  lets H00: Heibecb Hgetpos. clear Heibecb.
  simpljoin1.
  exists x x0.
  assert (join (sig eid (absmsgq msgs maxlen pwl, wl)) els' els).
  join auto.
  eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
Qed.

Lemma asemeib_del_q_preserve:
  forall infol scapl semeibs els vhold els' eid msgs maxlen pwl wl s P, 
    s |= ASemEIBs infol scapl semeibs els vhold ** P ->
    join els' (sig eid (absmsgq msgs maxlen pwl, wl)) els ->
    ~semeib_ref semeibs eid ->
    s |= ASemEIBs infol scapl semeibs els' vhold ** P. 
Proof.
  introv Hsat Hjo Hnref.
  unfold ASemEIBs in *.
  sep pauto.
  eapply sem_eib_ecb_del_q_preserve; eauto. 
Qed.

Lemma mux_eib_ecb_del_q_preserve: 
  forall muxeibs els els' eid msgs maxlen pwl wl, 
    RH_ECBlk_EIBlk_Mux_P muxeibs els ->
    join els' (sig eid (absmsgq msgs maxlen pwl, wl)) els ->
    ~muxeib_ref muxeibs eid ->
    RH_ECBlk_EIBlk_Mux_P muxeibs els'. 
Proof.
  introv Heibecb Hjo Hnref.
  unfold RH_ECBlk_EIBlk_Mux_P in *.
  introv Hgetpos Htp.
  casetac eid0 eid Heq Hneq.
  subst.
  unfold muxeib_ref in Hnref.
  false. apply Hnref. repeat eexists. eauto.
  lets H00: Heibecb Hgetpos Htp. clear Heibecb.
  simpljoin1.
  exists x x0 x1.
  assert (join (sig eid (absmsgq msgs maxlen pwl, wl)) els' els).
  join auto.
  eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
Qed.

Lemma amuxeib_del_q_preserve: 
  forall s els els' eid msgs maxlen pwl wl minfol mcapl muxeibs vhold P, 
    s |= AMuxEIBs minfol mcapl muxeibs els vhold ** P -> 
    join els' (sig eid (absmsgq msgs maxlen pwl, wl)) els ->
    ~muxeib_ref muxeibs eid ->
    s |= AMuxEIBs minfol mcapl muxeibs els' vhold ** P.   
Proof.
  introv Hsat Hjo Hnref.
  unfold AMuxEIBs in *.
  sep pauto.
  eapply mux_eib_ecb_del_q_preserve; eauto.
Qed.

Lemma mq_eib_ecb_del_q_preserve: 
  forall mqeibs els els' eid msgs maxlen pwl wl, 
    RH_EIBlk_ECBlk_Q_P els mqeibs ->
    join els' (sig eid (absmsgq msgs maxlen pwl, wl)) els ->
    ~mqeib_ref mqeibs eid ->
    RH_EIBlk_ECBlk_Q_P els' mqeibs. 
Proof.
  introv Heibecb Hjo Hnref.
  unfold RH_EIBlk_ECBlk_Q_P in *.
  introv Hgetpos.
  casetac eid0 eid Heq Hneq.
  subst.
  unfold mqeib_ref in Hnref.
  false. apply Hnref. repeat eexists. eauto.
  lets H00: Heibecb Hgetpos. clear Heibecb.
  simpljoin1.
  exists x x0 x1 x2.
  assert (join (sig eid (absmsgq msgs maxlen pwl, wl)) els' els).
  join auto.
  eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
Qed.

Lemma amqeib_del_q_preserve: 
  forall s els els' eid msgs maxlen pwl wl minfol qcapl muxeibs vhold P, 
    s |= AMqEIBs minfol qcapl muxeibs els vhold ** P -> 
    join els' (sig eid (absmsgq msgs maxlen pwl, wl)) els ->
    ~mqeib_ref muxeibs eid ->
    s |= AMqEIBs minfol qcapl muxeibs els' vhold ** P.   
Proof.
  introv Hsat Hjo Hnref.
  unfold AMqEIBs in *.
  sep pauto.
  eapply mq_eib_ecb_del_q_preserve; eauto.
Qed.

Lemma get_struct_vl:
 forall vl1 x vl2 sid decls l l',
 Get_struct (vl1 ++ (x, (Tstruct sid decls), l)  :: vl2) x = Some (x,  (Tstruct sid decls), l) -> 
 Get_struct vl1 x = None ->
 Get_struct (vl1 ++ (x, (Tstruct sid decls), l')  :: vl2) x = Some (x,  (Tstruct sid decls), l').
Proof.
  intros.
  inductions vl1.
  simpl. 
  rewrite OSTimeTickPure.beq_tid_true. auto.
  destruct a. destruct p.
  change (((a, t, l0) :: vl1) ++
   (x, STRUCT sid ­{ decls }­, l') :: vl2) with ((a, t, l0) :: (vl1 ++
   (x, STRUCT sid ­{ decls }­, l') :: vl2)) in *.
  unfold Get_struct in *. fold Get_struct in *.
  destruct (os_inv.beq_addrval a x) eqn: eq1.
  inverts H0.
  change (((a, t, l0) :: vl1) ++
       (x, STRUCT sid ­{ decls }­, l) :: vl2) with ((a, t, l0) :: (vl1 ++
       (x, STRUCT sid ­{ decls }­, l) :: vl2)) in H.
  unfold Get_struct in H. fold Get_struct in H.
  rewrite eq1 in H.
  auto.
  eapply IHvl1; eauto.
Qed.

Lemma set_array_update_nth_val:
  forall vl1 vl2 x n l l',
  Get_array vl1 x = None ->
  Get_array (vl1 ++(x, n, l) :: vl2) x = Some (x, n, l) ->
  Set_array' (vl1 ++(x, n, l) :: vl2) x l' = (vl1 ++(x, n, l') :: vl2).
Proof.
  intros.
  inductions vl1.
  simpl. 
  rewrite OSTimeTickPure.beq_tid_true. auto.
  destruct a. destruct p.
  change (((a, n0, l0) :: vl1) ++ (x, n, l) :: vl2) with ((a, n0, l0) :: (vl1 ++ (x, n, l) :: vl2)) in *.
  unfold Set_array'. fold Set_array'.
  unfold Get_array in H, H0. fold Get_array in H, H0.
  destruct (os_inv.beq_addrval a x) eqn: eq1.
  inverts H.
  change (((a, n0, l0) :: vl1) ++ (x, n, l') :: vl2) with ((a, n0, l0) :: (vl1 ++ (x, n, l') :: vl2)).
  lets Hset: IHvl1 H H0. 
  instantiate(1:= l') in Hset.
  rewrite Hset; auto.
Qed.

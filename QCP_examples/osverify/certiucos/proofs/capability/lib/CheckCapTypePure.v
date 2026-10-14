Require Import gjb_common.
Require Import Aarray_new_common.
Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_int.
Require Import ios_cap_defs.
Require Import Lia.
Require Import seplog_trm_tacs.
Require Import CapSpec.
Import DeprecatedTactic.
Open Scope code_scope.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope int_scope.
Set Nested Proofs Allowed.

Lemma ecast_long2long:
  forall s id v p,
  rule_type_val_match long v = true ->
  s |= LV id @ long |-> v   ** p
  ->
  s |= Rv 〈 long 〉 (evar id) @ long == v .
Proof.
  introv H0 H.
  destruct_s s.
  destruct H.  simpljoin.
  simpl in H1, H3, H4. simpljoin1.
  simpl.  rewrite H7.
  unfold is_int_type. 
  eapply mapstoval_load in H8.
  lets Hx: load_local H1 H8.
  rewrite Int.unsigned_zero in Hx.
  rewrite Hx. destruct v. simpl in H0. tryfalse.
  simpl in H0. tryfalse. unfold cast_eval. auto.
  simpl in H0. tryfalse. auto.
Qed.




Lemma retpost_GetObjSlotPost: 
    retpost Get_Obj_SlotPost.
Proof.
  unfolds.
  intros.
  unfold getasrt in H.
  unfold Get_Obj_SlotPost in H. 
  unfold Get_Obj_SlotPost' in H. 
  sep normal in H. sep destruct H. 
  sep lift 16%nat in H. 
  eapply disj_split in H. 
  destruct H. 
  sep split in H. 
  sep normal in H.  sep destruct H. 
  eapply disj_split in H. 
  destruct H.  sep split in H. 
  sep normal in H. sep destruct H. 
  sep split in H.  
   subst v. auto.
  sep normal in H. sep destruct H. 
  sep lift 2%nat in H.
  eapply disj_split in H.
  destruct H. 
  sep normal in H. sep destruct H. 
  sep split in H. destruct H17. 
  subst v. auto.
  sep normal in H. sep destruct H. 
  sep split in H. subst v. auto.
  sep split in H. subst v. auto.
Qed.


Lemma new_array_type_vallist_match_split1: 
  forall muxvl vll1 vll2 vl, 
    new_array_type_vallist_match pthread_mutex_info_t muxvl ->
    muxvl = vll1 ++ (vl::vll2) ->
    new_array_type_vallist_match pthread_mutex_info_t vll1 /\
      new_array_type_vallist_match pthread_mutex_info_t vll2 /\ 
      struct_type_vallist_match pthread_mutex_info_t vl.   
Proof.
  introv Hmatch Hlst.
  lets Hsp2 : new_array_type_vallist_match_split2 Hmatch Hlst.
  destruct Hsp2.
  split; auto.
  simpl in H0.
  destruct H0.
  split; auto.
Qed.


Lemma amqattr_len: 
  forall s b i vl, s |= AMqAttr (b, i)vl -> length vl = ∘ (OS_USER_MAX_EVENTS / 3).
Proof.  
  introv Hsat.
  destruct Hsat.
  simpl_sat H. simpljoin1.
  auto.
Qed. 

Lemma usr_max_evts_rgn:
1 <= OS_USER_MAX_EVENTS / 3 <= 79.
Proof.
  lets Hrgn: OS_MAX_EVENTS_range.
  unfold OS_USER_MAX_EVENTS.
  unfold CORENUM in *.
  destruct Hrgn as (Hrgn1 & Hrgn2).
  rewrite Z.sub_le_mono_r with (p:= 8 * 2) in Hrgn1, Hrgn2.
  rewrite Z.add_simpl_l in Hrgn1.
  eapply Z.div_le_mono with (c:= 3) in Hrgn2; auto with zarith.
  eapply Z.div_le_mono with (c:= 3) in Hrgn1; auto with zarith.
Qed.

Lemma AMqAttr_unfold_any_idx: 
  forall s b i mqvl idx,
    s |= AMqAttr (b, i) mqvl ->
    (idx < length mqvl)%nat ->
    s |= EX vll1 vll2 vl ,
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
  { 
    erewrite amqattr_len; eauto.  simpl.
    lets Hx: usr_max_evts_rgn.
    destruct Hx.
    rewrite max_unsigned_val.
    rewrite Nat2Z.inj_mul.
    unfold nat_of_Z. rewrite Z2Nat.id. 
    assert(OS_USER_MAX_EVENTS / 3 * Z.of_nat 52 <= 79 * 52).
    eapply Z.mul_le_mono_nonneg_r; auto. lia.
    lia. lia.
  }
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
      rewrite H11 in Hlen. rewrite H11 in HSidx.
      rewrite H11 in Hlenle.
      lets Hx: usr_max_evts_rgn.
      destruct Hx. 
      clear -H4  H Hlenle.
      rewrite Nat2Z.inj_mul.
      unfold nat_of_Z in Hlenle.
      eapply Nat2Z.inj_lt in Hlenle.
      rewrite Z2Nat.id in Hlenle.
      rewrite max_unsigned_val. lia.
      lia.
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

  exists (firstn idx mqvl). exists vlt.
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

  exists x1.  do 5 eexists. splits; eauto.
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
  clear -HSidx.
  rewrite Zpos_P_of_succ_nat in HSidx.
  rewrite <- Nat2Z.inj_succ in HSidx.
  rewrite Z2Nat.id in HSidx. auto. 
  lets Hx: usr_max_evts_rgn.
  destruct Hx. lia. 
  simpl. split; auto. unfolds. auto.

Qed.

Lemma AMqAttr_unfold_any_idx_frm: 
  forall s b i mqvl idx P,
    s |= AMqAttr (b, i)mqvl  ** P ->
    (idx < length mqvl)%nat ->
    s |= (EX vll1 vll2 vl ,
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
       split; [destruct IHmqvl; simpl; auto; auto | mytac; auto]).    
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
    s |= AMqAttr (b,i) (vll1 ++ (vl::vll2)) ** P.
Proof.
  intros.
  assert (Hrgn: Z.of_nat (S n * typelen mq_attr_t) <= Int.max_unsigned).
  {
    remember (typelen mq_attr_t) as X. 
    unfold mq_attr_t in HeqX. simpl in HeqX. 
    rewrite HeqX.
    rewrite Nat2Z.inj_mul.
    unfold nat_of_Z.
    clear -H. 
    lets Hx: usr_max_evts_rgn.
    destruct Hx.
    rewrite max_unsigned_val. lia.
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


Lemma if_imply_true: 
forall v'1 z, 
0 <= z < 255 ->
val_inj
(bop_eval (Vint32 v'1)
   (V$ z) char_t
   long oeq) <> Vint32 Int.zero /\
val_inj
(bop_eval (Vint32 v'1)
   (V$ z) char_t
   long oeq) <> Vnull /\
val_inj
(bop_eval (Vint32 v'1)
   (V$ z) char_t
   long oeq) <> Vundef -> Int.unsigned v'1 = z. 
Proof.
  introv Hlt. intros.
  unfold val_inj, bop_eval, val_eq in H. 
  destruct (Int.eq v'1 ($ z)) eqn: Heq; destruct H; tryfalse.
  eapply Inteq_true_is_Zeq in Heq.
  rewrite Int.unsigned_repr in Heq. auto.
  rewrite max_unsigned_val. lia.
Qed.

Lemma if_imply_false:
    forall v x,
    val_inj
    (bop_eval (Vint32 v) (V$ x)
       char_t long oeq) = Vint32 Int.zero \/
  val_inj
    (bop_eval (Vint32 v) (V$ x)
       char_t long oeq) = Vnull ->
  Int.eq v ($x) = false.
Proof.
  intros.
  unfold val_inj, bop_eval, val_eq in H.
  destruct (Int.eq v ($ x)). destruct H; tryfalse.
  auto.
Qed.


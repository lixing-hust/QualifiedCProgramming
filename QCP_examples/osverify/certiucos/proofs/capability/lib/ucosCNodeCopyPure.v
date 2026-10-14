Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_int.
Require Import ios_cap_defs.
Require Import ios_cap.
Require Import include_frm.
Require Import sep_auto.
Require Import CapPure.
Require Import CapSpec.
Require Import math_auto.
Require Import ACSpace_defs.
Require Import Lia.

Import DeprecatedTactic.
Open Scope code_scope.
Open Scope list_scope.
Open Scope int_scope.
Open Scope Z_scope.
Set Nested Proofs Allowed.
Set Keyed Unification.
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
    inverts H14. auto.
    sep normal in H. sep destruct H.
    sep lift 2%nat in H. eapply disj_split in H.
    eapply disj_split in H. sep destruct H.

    sep normal in H. sep destruct H. 
    eapply disj_split in H. destruct H.
    sep normal in H. sep destruct H.
    sep split in H. destruct H17.
    subst v. auto.
    sep normal in H. sep destruct H. 
    sep split in H. subst v. auto.
    sep split in H. subst v. auto.
Qed.
Lemma list_map_eq5:
  forall t (l1 l2 l3 l4 l5 l6: list t) (a1 a2 a3 a4 : t),
    length l1 = length l4 ->
    length l2 = length l5 ->
    length l3 = length l6 ->
    (l1 ++ a1 :: l2) ++ a2 :: l3 = l4 ++ (a3 :: l5) ++ a4 :: l6 ->
    l1 = l4 /\ a1 = a3 /\ l2 = l5 /\ a2 = a4 /\ l3 = l6.
Proof.
  intros.
  simpl in H2.  rewrite app_assoc_reverse in H2.
  assert(l1 = l4).
  eapply same_lenth_list_first_eq; eauto.
  subst l1.
  eapply app_inv_head in H2.
  simpl in H2. inverts H2.
  assert(l2 = l5).
  eapply same_lenth_list_first_eq; eauto.
  subst l2. 
  eapply app_inv_head in H5.
  inverts H5.
  split; auto.
Qed.

Lemma list_map_eq3:
  forall t (l1 l2  l4 l5 : list t) (a1 a2 : t),
    length l1 = length l4 ->
    length l2 = length l5 ->
    l1 ++ a1 :: l2 = l4 ++ a2 :: l5 ->
    l1 = l4 /\ a1 = a2 /\ l2 = l5.
Proof.
    intros.
    assert(l1 = l4).
    eapply same_lenth_list_first_eq; eauto.
    subst l1.
    eapply app_inv_head in H1. inverts H1.
    splits; auto.
Qed.


Lemma eq_sym:
forall (t: Type)(a : t)(b: t),
  a = b -> b = a.
  Proof. 
  auto.
Qed.

Lemma objectpointer_add_1_keep:
forall v'28 v'36 x,
(Z.to_nat(Int.unsigned v'28) < length v'36)%nat ->
objectpointer v'36 ->
nth_val'
    (Z.to_nat (Int.unsigned v'28)) v'36 =
  Vint32 x ->
(Int.unsigned x < 255) ->
objectpointer
(update_nth_val
 (Z.to_nat (Int.unsigned v'28)) v'36
 (val_inj
    (add (Vint32 x) (V$ 1) long long))).
Proof.
  intros.
  unfold objectpointer in *.
  intros.
  assert( i = Z.to_nat(Int.unsigned v'28) \/ i <> Z.to_nat(Int.unsigned v'28)) by lia.
  destruct H5.
  {
    rewrite <- H5 in *.
    assert(Hr:( 0 <= i < length v'36)%nat) by lia.
    eapply inline_bittblfunctions.nth_val'2nth_val in H1.
    lets Htmp: H0 Hr H1.
    assert(Ht: (Z.to_nat OBJ_POSITION <=
    Z.to_nat (Int.unsigned x) <
    255)%nat) by lia.
    eapply nth_upd_eq in H4.
    unfold val_inj, add in H4.
    inverts H4.
    split.
    eapply Z2Nat.inj_le.
    unfold OBJ_POSITION. lia.
    lets Hx: unsigned_ge0 (x +ᵢ  $ 1).
    lia.
    destruct Htmp.
    assert(Int.unsigned (x +ᵢ  $ 1) > Int.unsigned x).
    int auto. rewrite Int.unsigned_repr.
    clear -H2. splits. 
    assert(Int.unsigned x >= 0).
    eapply unsigned_ge0. lia. lia.
    rewrite max_unsigned_val. lia.
    assert(Int.unsigned x >= OBJ_POSITION).
    int auto.
    rewrite Int.unsigned_repr. 
    assert(Int.unsigned x >= 0).
    eapply unsigned_ge0. lia. 
    rewrite max_unsigned_val. lia.
    lia.
    int auto.
    rewrite Int.unsigned_repr.
    assert(Int.unsigned x >= 0).
    eapply unsigned_ge0. lia. 
    rewrite max_unsigned_val. lia.
  }
  lets Hx: nth_upd_neq H5 H4.
  rewrite update_nth_val_len_eq in H3.
  lets Hy: H0 H3 Hx.
  auto.
  
Qed.
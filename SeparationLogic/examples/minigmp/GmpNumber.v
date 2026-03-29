Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import CommonAssertion Mem SeparationLogic IntLib.
Require Import GmpAux. Import Aux.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.
Import naive_C_Rules.
Local Open Scope sac.

Lemma uint_array_undef_seg_align4 : forall ptr size cap,
  UIntArray.undef_seg ptr size cap |-- store_align4_n (cap - size).
Proof.
  intros.
  unfold UIntArray.undef_seg.
  destruct (Z_le_dec size cap).
  - set (n := Z.to_nat (cap - size)).
    replace (cap - size) with (Z.of_nat n) by lia.
    replace (cap) with (size + Z.of_nat n) by lia.
    clearbody n. clear l cap.
    revert ptr size.
    induction n ; simpl in * ; intros.
    + unfold store_align4_n. Exists nil.
      entailer!.
      constructor.
    + replace (size + Z.pos (Pos.of_succ_nat n)) with (size + 1 + Z.of_nat n) by lia.
      sep_apply IHn.
      sep_apply undef_store_uint_align4.
      sep_apply (store_align4_merge 1 (Z.of_nat n)).
      replace (Z.pos (Pos.of_succ_nat n)) with (1 + Z.of_nat n) by lia.
      entailer!.
  - replace (Z.to_nat (cap - size)) with 0%nat by lia.
    simpl. Intros.
    lia.
Qed.

Lemma uint_array_undef_full_align4 : forall ptr size,
  UIntArray.undef_full ptr size |-- store_align4_n size.
Proof.
  intros.
  sep_apply UIntArray.undef_full_to_undef_seg.
  sep_apply uint_array_undef_seg_align4.
  replace (size - 0) with size by lia.
  entailer!.
Qed.
  
Lemma uint_array_full_align4 : forall ptr size data,
  UIntArray.full ptr size data |-- store_align4_n size.
Proof.
  intros.
  sep_apply UIntArray.full_to_undef_full.
  sep_apply uint_array_undef_full_align4.
  entailer!.
Qed.



Section Internal.
  
Variable Base : Z.
Variable Base_pos: 0 < Base.

Definition mpd_store_list (ptr: addr) (data: list Z): Assertion :=
  UIntArray.full ptr (Zlength data) data.

Fixpoint list_to_Z (data: list Z): Z :=
  match data with
    | nil => 0
    | a :: l0 => (list_to_Z l0) * Base + a
  end.

Fixpoint list_within_bound (data: list Z): Prop :=
  match data with
   | nil => True
   | a :: l0 => 0 <= a < Base /\ (list_within_bound l0)
  end.

Definition mpd_store_Z (ptr: addr) (n: Z) (size: Z) : Assertion :=
  EX data,
    [| list_to_Z data = n /\ list_within_bound data |] && [| size = Zlength data |] && mpd_store_list ptr data.

Definition mpd_store_Z_compact (ptr: addr) (n size: Z): Assertion :=
  EX data,
    [| list_to_Z data = n /\ last data 1 >= 1 /\ list_within_bound data |] && [| size = Zlength data |] && mpd_store_list ptr data.

Definition is_compact_Z (n: Z) (size: Z) : Prop :=
exists data, 
  list_to_Z data = n /\
  Zlength data = size /\ 
  list_within_bound data /\
  last data 1 >= 1.

Lemma list_to_Z_injection: forall l1 l2 n1 n2,
  list_to_Z l1 = n1 ->
  list_to_Z l2 = n2 ->
  l1 = l2 -> n1 = n2.
Proof.
  intros.
  subst.
  lia.
Qed.

Lemma list_to_Z_app : forall l1 l2,
  list_to_Z (l1 ++ l2) = list_to_Z l1 + list_to_Z l2 * (Base ^ (Zlength l1)).
Proof.
  intros l1.
  induction l1 ; intros ; simpl in * ; try lia.
  rewrite IHl1.
  rewrite Zlength_cons. 
  replace (Z.succ (Zlength l1)) with (1 + Zlength l1) by lia.
  rewrite Z.pow_add_r ; try lia.
  apply Zlength_nonneg.
Qed. 

Lemma list_to_Z_zeros : forall m,
  list_to_Z (zeros m) = 0.
Proof.
  intros.
  unfold zeros.
  induction (Z.to_nat m) ; simpl ; try lia.
Qed.

Lemma zeros_list_within_bound : forall n,
  list_within_bound (zeros n).
Proof.
  intros.
  unfold zeros.
  induction (Z.to_nat n) ; simpl ; try tauto.
  split ; try lia.
  auto.
Qed.

Lemma __list_within_bound_concat_r: forall (l1: list Z) (a: Z),
  list_within_bound l1 ->
  0 <= a < Base ->
  list_within_bound (l1 ++ [a]).
Proof.
  intros.
  induction l1.
  + rewrite app_nil_l.
    simpl.
    lia.
  + simpl in *; repeat split; try tauto.
Qed.

Lemma list_within_bound_concat: forall (l1 l2: list Z),
  list_within_bound l1 ->
  list_within_bound l2 ->
  list_within_bound (l1 ++ l2).
Proof.
  intros.
  revert l1 H.
  induction l2.
  + intros.
    rewrite app_nil_r.
    tauto.
  + intros.
    simpl in H0.
    destruct H0.
    rewrite Aux.list_app_cons.
    pose proof (__list_within_bound_concat_r l1 a H H0).
    specialize (IHl2 H1 (app l1 [a]) H2).
    tauto.
Qed.

Lemma list_within_bound_Znth_bound: forall (l: list Z) (i: Z),
  0 <= i < Zlength l ->
  list_within_bound l ->
  0 <= Znth i l 0 < Base.
Proof.
  intros.
  revert i H.
  induction l; intros.
  + rewrite Zlength_nil in H.
    lia.
  + assert (i = 0 \/ i > 0). { lia. }
    destruct H1.
    - rewrite H1.
      rewrite (Znth0_cons a l 0).
      simpl in H0.
      lia.
    - rewrite Znth_cons; try lia.
      simpl in H0; destruct H0.
      rewrite Zlength_cons in H; unfold Z.succ in H.
      specialize (IHl H2 (i - 1) ltac:(lia)).
      lia.
Qed.

Lemma list_within_bound_Znth: forall (l: list Z) (i: Z),
  0 <= i ->
  list_within_bound l ->
  0 <= Znth i l 0 < Base.
Proof.
  intros.
  destruct (Z_lt_dec i (Zlength l)).
  - apply list_within_bound_Znth_bound; try tauto.
  - rewrite <- (app_nil_r l).
    rewrite app_Znth2 ; try lia.
    assert (i - Zlength l >= 0) by lia.
    unfold Znth.
    destruct (Z.to_nat (i - Zlength l)) ; simpl; lia.
Qed.

Lemma list_within_bound_sublist : forall (l: list Z) (lo hi: Z),
  0 <= lo <= hi -> hi <= Zlength l ->
  list_within_bound l ->
  list_within_bound (sublist lo hi l).
Proof.
  intros.
  generalize dependent lo. 
  generalize dependent hi.
  revert H1.
  induction l; intros.
  - rewrite Zlength_nil in H0.
    rewrite sublist_nil  ; try lia.
    tauto.
  - destruct (Z.eq_dec hi lo).
    + subst. rewrite sublist_nil ; try lia.
      simpl. tauto.
    + simpl in H1. 
      destruct (Z.eq_dec lo 0).
      * subst lo. 
        rewrite sublist_cons1 ; try lia.
        rewrite Zlength_cons in H0.
        split ; try tauto. 
        apply IHl ; try tauto ; try lia.
      * rewrite sublist_cons2 ; try lia.
        rewrite Zlength_cons in H0.
        apply IHl ; try tauto ; try lia.  
Qed.
    

Lemma __list_within_bound_split_r: forall (l1: list Z) (a: Z),
  list_within_bound (l1 ++ [a]) ->
  list_within_bound l1 /\ 0 <= a < Base.
Proof.
  intros.
  induction l1.
  + rewrite app_nil_l in H.
    simpl in *.
    tauto.
  + simpl in *.
    destruct H.
    specialize (IHl1 H0).
    tauto.
Qed.

Lemma list_within_bound_split: forall (l1 l2: list Z),
  list_within_bound (l1 ++ l2) ->
  list_within_bound l1 /\ list_within_bound l2.
Proof.
  intros.
  revert l1 H.
  induction l2.
  + intros.
    simpl.
    rewrite app_nil_r in H.
    tauto.
  + intros.
    simpl.
    rewrite Aux.list_app_cons in H.
    specialize (IHl2 (app l1 [a]) H).
    destruct IHl2.
    apply __list_within_bound_split_r in H0.
    tauto.
Qed.

Lemma list_to_Z_Leading_zeros_equiv : forall l m,
  0 < Base ->
  list_to_Z l = list_to_Z (l ++ zeros m).
Proof.
  intros.
  rewrite list_to_Z_app.
  rewrite list_to_Z_zeros.
  lia.
Qed.

Lemma list_to_Z_pos : forall l,
  list_within_bound l ->
  list_to_Z l >= 0.
Proof.
  intros. 
  induction l ; simpl in * ; try lia.
  destruct H.
  specialize (IHl H0).
  nia.
Qed.

Lemma list_to_Z_zero : forall l,
  list_within_bound l ->
  list_to_Z l = 0 -> l = zeros (Zlength l).
Proof.
  intros.
  induction l ; intros.
  - reflexivity.
  - simpl in *.
    destruct H.
    pose proof (list_to_Z_pos l H1).
    assert (a = 0) by lia.
    assert (list_to_Z l = 0) by lia.
    rewrite IHl at 1 ; try tauto.
    subst a.
    rewrite Zlength_cons. 
    unfold zeros.
    pose proof (Zlength_nonneg l). 
    replace (Z.to_nat (Z.succ (Zlength l))) with (S (Z.to_nat (Zlength l))) ; try lia.
    reflexivity.
Qed.
    

Lemma list_to_Z_reverse_injection: forall l1 l2,
  list_to_Z l1 = list_to_Z l2 -> list_within_bound l1 ->
  list_within_bound l2 ->
  exists n m, n >= 0 /\ m >= 0 /\ (l1 ++ zeros n)%list = (l2 ++ zeros m)%list.
Proof.
  intros l1.
  induction l1 ; intros.
  - simpl in *. 
    symmetry in H.
    apply list_to_Z_zero in H ; try auto.
    exists (Zlength l2), 0. 
    rewrite <- H.
    unfold zeros. simpl. rewrite app_nil_r.
    repeat split ; try lia.
    pose proof Zlength_nonneg l2. lia.
  - simpl in *. 
    destruct H0.
    pose proof (list_to_Z_pos l1 H2).
    destruct l2 ; simpl in *.
    + assert (a = 0) by lia.
      assert (list_to_Z l1 = 0) by lia.
      apply list_to_Z_zero in H5 ; try auto.
      exists 0, (Zlength l1 + 1).
      subst.
      pose proof (Zlength_nonneg l1). 
      repeat split ; try lia.
      unfold zeros.
      simpl.
      rewrite app_nil_r.
      replace (Z.to_nat (Zlength l1 + 1)) with (S (Z.to_nat (Zlength l1))) ; try lia.
      simpl. rewrite H5 at 1. unfold zeros. reflexivity.
    + destruct H1. 
      assert (a = z).
      {
        assert (z = (list_to_Z l1 * Base + a) mod Base).
        {
          apply (Zmod_unique _ _ (list_to_Z l2) _ ) ; try lia.
        }
        assert (a = (list_to_Z l1 * Base + a) mod Base).
        {
          apply (Zmod_unique _ _ (list_to_Z l1) _ ) ; try lia.
        }
        lia.
      }
      assert (list_to_Z l1 = list_to_Z l2) by nia.
      specialize (IHl1 _ H6 H2 H4).
      destruct IHl1 as [n [m ?]].
      exists n, m. 
      subst a. simpl. 
      destruct H7 as [? [ ? ?]].
      rewrite H8. 
      repeat split ; try lia.
Qed.

Lemma Zlength_zeros: forall n,
  0 <= n ->
  Zlength (zeros n) = n.
Proof.
  intros.
  unfold zeros.
  set (nat_n := Z.to_nat n).
  replace n with (Z.of_nat nat_n) by lia.
  clearbody nat_n. clear n H. rename nat_n into n.
  induction n ; simpl repeat ; try lia.
  - rewrite Zlength_nil.
    lia.
  - rewrite Zlength_cons.
    rewrite IHn.
    lia.
Qed.


Lemma list_to_Z_reverse_same_length_injection: forall l1 l2,
  list_to_Z l1 = list_to_Z l2 -> list_within_bound l1 ->
  list_within_bound l2 ->
  Zlength l1 = Zlength l2 ->
  l1 = l2.
Proof.
  intros.
  pose proof (list_to_Z_reverse_injection l1 l2 H H0 H1).
  destruct H3 as [n [m [? [? ?]]]].
  assert (Zlength (l1 ++ zeros n) = Zlength (l2 ++ zeros m)). {
    rewrite H5.
    reflexivity.
  }
  do 2 rewrite Zlength_app in H6.
  do 2 rewrite Zlength_zeros in H6; try lia.
  assert (n = m) by lia.
  subst n.
  apply app_inv_tail in H5. auto.
Qed.

Lemma list_to_Z_concat_r: forall (l1: list Z) (a: Z),
  0 <= a < Base ->
  list_to_Z (l1 ++ [a]) = a * (Base ^ (Zlength l1)) + list_to_Z l1.
Proof.
  induction l1; intros.
  + rewrite app_nil_l.
    unfold Zlength, Zlength_aux.
    rewrite Z.pow_0_r.
    simpl in *. lia.
  + simpl in *.
    rewrite IHl1 ; try lia.
    rewrite Zlength_cons; unfold Z.succ.
    pose proof (Zlength_nonneg l1).
    rewrite Aux.Zpow_add_1; try lia.
Qed.

Lemma list_to_Z_concat: forall (l1 l2: list Z),
  list_within_bound l1 ->
  list_within_bound l2 ->
  list_to_Z (l1 ++ l2) = list_to_Z l1 + (list_to_Z l2) * (Base ^ (Zlength l1)).
Proof.
  intros.
  revert H H0. revert l1.
  induction l2 ; intros ; simpl in *.
  + rewrite app_nil_r.
    nia.
  + destruct H0.
    rewrite Aux.list_app_cons.
    rewrite IHl2 ; try auto.
    2 : {
      apply list_within_bound_concat ; try tauto.
      simpl. lia.
    }
    rewrite Zlength_app; rewrite Zlength_cons; simpl.
    rewrite list_to_Z_concat_r; try lia.
    pose proof (Zlength_nonneg l1).
    rewrite Aux.Zpow_add_1; try lia.
Qed.

Lemma list_to_Z_bound: forall (l1: list Z),
  list_within_bound l1 ->
  0 <= list_to_Z l1 < Base ^ (Zlength l1).
Proof.
  induction l1; intros ; simpl in * ; try lia.
  rewrite Zlength_cons; unfold Z.succ.
  destruct H.
  specialize (IHl1 H0). 
  pose proof (Zlength_nonneg l1).
  rewrite Aux.Zpow_add_1; try nia.
Qed.

Lemma list_to_Z_list_append: forall (l: list Z) (i: Z),
  0 <= i < Zlength l ->
  list_within_bound l ->
  list_to_Z (sublist 0 (i + 1) l) = list_to_Z (sublist 0 i l) + Znth i l 0 * (Base ^ i).
Proof.
  intros.
  rewrite Zlength_correct in H.
  rewrite (sublist_split 0 (i + 1) i l); try lia.
  rewrite (sublist_single i l 0) ; try lia.
  pose proof list_within_bound_Znth l i (ltac:(lia)) H0.
  rewrite list_to_Z_concat_r ; try lia.
  rewrite <- Zlength_correct in H.
  rewrite Zlength_sublist ; try lia.
  replace (i - 0) with i by lia.
  nia.
Qed.

Lemma list_to_Z_split: forall (l1 l2: list Z),
  list_within_bound (l1 ++ l2) ->
  list_to_Z l1 = list_to_Z (l1 ++ l2) mod (Base ^ (Zlength l1)) /\
  list_to_Z l2 = list_to_Z (l1 ++ l2) / (Base ^ (Zlength l1)).
Proof.
  intros.
  induction l1; split ; simpl in *.
  + rewrite Z.mod_1_r. lia.
  + rewrite Z.div_1_r. lia.
  + rewrite Zlength_cons; unfold Z.succ.
    specialize (IHl1 (ltac:(tauto))).
    destruct IHl1.
    rewrite Zplus_mod.
    pose proof (Zlength_nonneg l1).
    pose proof (list_to_Z_pos (l1 ++ l2) (ltac:(tauto))).
    rewrite Aux.Zmul_mod_cancel; try lia.
    rewrite <- H0.
    rewrite Aux.Zpow_add_1; try nia.
    rewrite (Z.mod_small a) ; try nia.
    pose proof (list_within_bound_split l1 l2 (ltac:(tauto))).
    pose proof (list_to_Z_bound l1 (ltac:(tauto))).
    rewrite Z.mod_small ; try nia.
  + pose proof (list_within_bound_split l1 l2 ltac:(tauto)).
    rewrite Zlength_cons; unfold Z.succ.
    specialize (IHl1 (ltac:(tauto))).
    destruct IHl1.
    pose proof (Zlength_nonneg l1).
    rewrite Aux.Zpow_add_1; try lia.
    rewrite (Z.mul_comm (Base ^ Zlength l1)).
    rewrite <-Zdiv_Zdiv; try lia.
    rewrite <- (Zdiv_unique_full (list_to_Z (l1 ++ l2) * Base + a) Base (list_to_Z (l1 ++ l2)) a) ; try nia.
    unfold Remainder; lia.
Qed.

Lemma list_to_Z_compact_bound: forall (l1: list Z),
  list_within_bound l1 -> last l1 1 >= 1 ->
  Base ^ ((Zlength l1) - 1) <= list_to_Z l1 < Base ^ (Zlength l1).
Proof.
  intros.
  destruct l1.
  + rewrite Zlength_nil.
    simpl. lia.
  + pose proof (list_to_Z_bound (z :: l1) H).
    split ; try lia.
    pose proof (@app_removelast_last Z (z :: l1) 1 ltac:(congruence)).
    pose proof (list_to_Z_split (removelast (z :: l1)) ([last (z :: l1) 1])%list).
    rewrite Aux.Zlength_removelast in H3 ; try congruence.
    rewrite Zlength_cons in *. 
    replace (Z.succ (Zlength l1) - 1) with (Zlength l1) in * by lia.
    rewrite H2 in H.
    specialize (H3 H).
    destruct H3.
    rewrite <- H2 in H3 , H4.
    unfold list_to_Z at 1 in H4.
    replace (0 * Base + last (z :: l1) 1) with (last (z :: l1) 1) in H4 by lia.
    rewrite H4 in H0.
    pose proof (Zlength_nonneg l1).
    assert (Base ^ (Zlength l1) >= 1) by nia.
    pose proof (Zdiv_ge_1_larger (list_to_Z (z :: l1)) (Base ^ Zlength l1) (ltac:(lia)) (ltac:(lia)) (ltac:(lia))).
    nia.
Qed.

Lemma list_to_Z_nth: forall (l: list Z) (n: Z) (i: Z),
  0 <= i < Zlength l -> list_within_bound l -> 
  Znth i l 0 = (list_to_Z l / (Base ^ i)) mod Base.
Proof.
  intros.
  revert i H H0.
  induction l; intros ; simpl in *.
  + rewrite Zlength_nil in H.
    lia.
  + rewrite Zlength_cons in H; unfold Z.succ in H.
    assert (i = 0 \/ i > 0). { lia. }
    destruct H1.
    - subst i.
      simpl. rewrite Znth0_cons.
      rewrite Z.div_1_r.
      rewrite Zplus_mod.
      rewrite Z_mod_mult.
      rewrite (Z.mod_small a) ; try lia.
      rewrite Z.mod_small ; try lia.
    - rewrite Znth_cons; [ | lia ].
      pose proof (list_to_Z_split [a] l H0).
      destruct H2.
      rewrite IHl ; [ | lia | tauto].
      simpl list_to_Z in *.
      rewrite Zlength_cons, Zlength_nil in *.
      replace (Base ^ Z.succ 0) with Base in * by lia.
      rewrite H3 at 1.
      rewrite Zdiv_Zdiv ; try lia.
      replace (Base * Base ^ (i - 1)) with (Base ^ i).
      lia.
      replace i with (i - 1 + 1) at 1 by lia.
      rewrite Z.pow_add_r ; try lia.
Qed.

Lemma list_to_Z_cmp_same_length: forall l1 l2 i,
  0 <= i < Zlength l1 ->
  Zlength l1 = Zlength l2 ->
  sublist (i + 1) (Zlength l1) l1 = sublist (i + 1) (Zlength l2) l2 ->
  list_within_bound l1 ->
  list_within_bound l2 ->
  Znth i l1 0 < Znth i l2 0 ->
  list_to_Z l1 < list_to_Z l2.
Proof.
  intros.
  assert (Zlength l1 = Z.of_nat (Datatypes.length l1)). { apply Zlength_correct. }
  pose proof (sublist_split 0 (Zlength l1) i l1 ltac:(lia) ltac:(lia)).
  assert (Zlength l2 = Z.of_nat (Datatypes.length l2)). { apply Zlength_correct. }
  pose proof (sublist_split 0 (Zlength l2) i l2 ltac:(lia) ltac:(lia)).
  rewrite (sublist_self l1 (Zlength l1) ltac:(lia)) in H6.
  rewrite (sublist_self l2 (Zlength l2) ltac:(lia)) in H8.
  rewrite H6, H8.
  rewrite H6 in H2.
  rewrite H8 in H3.
  apply list_within_bound_split in H2.
  apply list_within_bound_split in H3.
  do 2 (rewrite list_to_Z_concat ; try tauto).
  pose proof (list_to_Z_bound (sublist 0 i l1) (ltac:(tauto))).
  pose proof (list_to_Z_bound (sublist 0 i l2) (ltac:(tauto))).
  do 2 (rewrite Zlength_sublist in * ; try lia).
  replace (i - 0) with i in * by lia.
  rewrite (sublist_split i (Zlength l1) (i + 1)) ; try lia.
  rewrite (sublist_split i (Zlength l2) (i + 1)) ; try lia.
  rewrite (sublist_single i l1 0) ; try lia.
  rewrite (sublist_single i l2 0) ; try lia.
  simpl.
  rewrite H1.
  nia.
Qed.

Lemma list_to_Z_cmp_diff_length: forall l1 l2,
  Zlength l1 < Zlength l2 ->
  list_within_bound l1 -> list_within_bound l2 ->
  last l1 1 >= 1 -> last l2 1 >= 1 ->
  list_to_Z l1 < list_to_Z l2.
Proof.
  intros.
  pose proof (list_to_Z_compact_bound l1 H0 H2).
  pose proof (list_to_Z_compact_bound l2 H1 H3).
  assert (Base ^ (Zlength l1) <= Base ^ (Zlength l2 - 1)). {
    pose proof (Zlength_nonneg l1).
    pose proof (Zlength_nonneg l2).
    apply Z.pow_le_mono_r ; try lia.
  }
  lia.
Qed.

Lemma mpd_store_Z_zero : forall ptr n,
  mpd_store_Z ptr n 0 |-- [| n = 0 |].
Proof.
  intros.
  unfold mpd_store_Z.
  Intros data.
  symmetry in H0.
  apply Zlength_nil_inv in H0.
  subst data.
  simpl in *.
  entailer!.
Qed.

Lemma mpd_store_Z_compact_pos : forall ptr n size,
  size > 0 ->
  mpd_store_Z_compact ptr n size |-- [| n > 0 |].
Proof.
  intros.
  unfold mpd_store_Z_compact , mpd_store_list.
  Intros data.
  subst size. destruct H0 as [? [? ?]].
  subst n.
  entailer!.
  induction data ; simpl in *.
  - rewrite Zlength_nil in *.
    lia.
  - entailer!.
    pose proof (list_to_Z_pos data (ltac:(tauto))).
    destruct data ; try lia.
    rewrite Zlength_cons in IHdata.
    pose proof (Zlength_nonneg data).
    specialize (IHdata (ltac:(lia)) H1 (ltac:(tauto))).
    lia.
Qed.

Lemma mpd_store_Z_compact_zero : forall ptr n,
  mpd_store_Z_compact ptr n 0 |-- [| n = 0 |].
Proof.
  intros.
  unfold mpd_store_Z_compact.
  Intros data.
  symmetry in H0.
  apply Zlength_nil_inv in H0.
  subst data.
  simpl in *.
  entailer!.
Qed.


Lemma mpd_store_Z_compact_align4 : forall ptr n size,
  mpd_store_Z_compact ptr n size |-- store_align4_n size.
Proof.
  intros.
  unfold mpd_store_Z_compact , mpd_store_list.
  Intros data.
  rewrite <- H0.
  sep_apply uint_array_full_align4.
  entailer!.
Qed.

(* Convert a number to its digit list representation *)
Fixpoint Z_to_list (n: Z) (size: nat) : list Z :=
  match size with
  | O => nil
  | S size' => (n mod Base) :: Z_to_list (n / Base) size'
  end.

Lemma Z_to_list_length : forall n size,
  Zlength (Z_to_list n size) = Z.of_nat size.
Proof.
  intros. revert n.
  induction size; simpl.
  - rewrite Zlength_nil. lia.
  - intros. rewrite Zlength_cons. rewrite IHsize. lia.
Qed.

Lemma Z_to_list_within_bound : forall n size,
  0 <= n ->
  list_within_bound (Z_to_list n size).
Proof.
  intros.
  revert n H.
  induction size; intros; simpl.
  - tauto.
  - split.
    + pose proof (Z.mod_pos_bound n Base Base_pos). lia.
    + apply IHsize. apply Z_div_pos; lia.
Qed.

Lemma Z_to_list_correct : forall n size,
  0 <= n ->
  list_to_Z (Z_to_list n size) = n mod (Base ^ (Z.of_nat size)).
Proof.
  intros.
  revert n H.
  induction size; intros.
  - rewrite Z.mod_1_r. simpl. lia.
  - simpl.
  change (n mod Z.pow_pos Base (Pos.of_succ_nat size)) with (n mod Base ^ Z.of_nat (S size)).
   rewrite IHsize; [ | apply Z_div_pos; lia].
    pose proof Nat2Z.inj_succ size. rewrite H0.
    pose proof Z.pow_succ_r Base (Z.of_nat size) ltac:(lia).
    rewrite H1.
    rewrite Z.rem_mul_r.
    + lia.
    + lia.
    + lia.
Qed.

Lemma Z_to_list_exact : forall n size,
  0 <= n < Base ^ (Z.of_nat size) ->
  list_to_Z (Z_to_list n size) = n.
Proof.
  intros.
  rewrite Z_to_list_correct; try lia.
  rewrite Z.mod_small; lia.
Qed.

Lemma Z_to_list_last : forall n size,
  0 <= n < Base ^ (Z.of_nat size) ->
  Base ^ (Z.of_nat size - 1) <= n ->
  last (Z_to_list n size) 1 >= 1.
Proof.
  intros.
  revert n H H0.
  induction size; intros.
  - simpl. lia.
  - simpl. pose proof IHsize (n / Base).
  assert (Hcond1: 0 <= n / Base < Base ^ Z.of_nat size).
  {
    split.
    - apply Z_div_pos; lia.
    - apply Z.div_lt_upper_bound; try lia.
    rewrite <- Z.pow_succ_r; try lia.
  }
  assert (Hcond2: Base ^ (Z.of_nat size - 1) <= n / Base). {
    apply Z.div_le_lower_bound; try lia.
    destruct (Nat.eq_dec size 0) as [Hsize0 | Hsize_pos].
    -- subst. simpl in *. lia.
    -- rewrite <- Z.pow_succ_r; try lia.
      replace (Z.succ (Z.of_nat size - 1)) with (Z.of_nat size) by lia.
      (* 现在目标是 Base ^ Z.of_nat size <= n *)
      (* 从 H0: Base ^ (Z.of_nat (S size) - 1) <= n *)
      replace (Z.of_nat (S size) - 1) with (Z.of_nat size) in H0 by lia.
      exact H0. 
  }
  pose proof H1 Hcond1 Hcond2.
  destruct size.
    + simpl.
      rewrite Nat2Z.inj_succ in H, H0.
      simpl in H, H0.
      pose proof (Z.mod_pos_bound n Base Base_pos).
      pose proof Z.mod_small. rewrite H4; lia.
    + remember (S size) as size'.
      assert (Z_to_list (n / Base) size' <> nil). {
        subst size'.
        simpl. congruence.
      }
      destruct (Z_to_list (n / Base) size').
      -- contradiction.
      -- lia. 
Qed.

(* Simpler lemma: if we know the exact bounds, the compact representation exists *)
Lemma is_compact_Z_from_bounds : forall n size,
  size >= 0 ->
  (size = 0 /\ n = 0) \/ (size > 0 /\ Base ^ (size - 1) <= n < Base ^ size) ->
  is_compact_Z n size.
Proof.
  intros.
  destruct H0.
  - (* size = 0, n = 0 case *)
    destruct H0; subst.
    unfold is_compact_Z.
    exists nil.
    simpl. repeat split; lia.
  - (* size > 0, proper bounds *)
    destruct H0 as [Hsize [Hlo Hhi]].
    unfold is_compact_Z.
    destruct (Z.to_nat size) eqn:Hnat.
    + lia.
    + exists (Z_to_list n (S n0)).
      repeat split.
      * rewrite Z_to_list_exact; try lia.
        replace (Z.of_nat (S n0)) with size by lia. lia.
      * rewrite Z_to_list_length. lia.
      * apply Z.mod_pos_bound. lia.
      * apply Z.mod_pos_bound. lia.
      * apply Z_to_list_within_bound. apply Z_div_pos; lia.
      * apply Z_to_list_last.
        -- replace (Z.of_nat (S n0)) with size by lia. lia.
        -- replace (Z.of_nat (S n0)) with size by lia. lia.
Qed.

(* Compact representation properties from is_compact_Z *)
Lemma is_compact_Z_bounds : forall n size,
  is_compact_Z n size ->
  size >= 0 /\
  ((size = 0 /\ n = 0) \/ (size > 0 /\ Base ^ (size - 1) <= n < Base ^ size)).
Proof.
  intros.
  unfold is_compact_Z in H.
  destruct H as [data [Heq [Hlen [Hbound Hlast]]]].
  split.
  - pose proof (Zlength_nonneg data). lia.
  - destruct data.
    + left. simpl in *. rewrite Zlength_nil in Hlen.
     split; lia.
    + right.
      simpl in Hlast.
      pose proof (list_to_Z_compact_bound (z :: data) Hbound Hlast).
      rewrite Zlength_cons in Hlen.
      pose proof (Zlength_nonneg data).
      split; try lia.
      rewrite Zlength_cons in H.
      subst. lia.
Qed.

Lemma is_compact_Z_add_helper_1 : forall n m size,
  Base>2 ->
  size >= 0 ->
  0 <= n -> 0 <= m ->
  Base ^ size <= n + m < 2 * Base ^ size ->
  is_compact_Z (n + m) (size + 1).
Proof.
  intros.
  apply is_compact_Z_from_bounds; try lia.
  right.
  split; try lia.
  split.
  - replace (size + 1 - 1) with size by lia. lia.
  - rewrite Aux.Zpow_add_1; try lia.
    rewrite Z.mul_comm.
    pose proof Z.pow_pos_nonneg.
    nia.
Qed.

End Internal.


Definition UINT_MOD := (4294967296).

Theorem UINT_MOD_pos : 0 < UINT_MOD.
Proof.
  unfold UINT_MOD.
  lia.
Qed.

(* same_sign: two integers have the same sign *)
Definition same_sign (a b: Z) : Prop :=
  (a >= 0 /\ b >= 0) \/ (a < 0 /\ b < 0).

Lemma same_sign_refl : forall a, same_sign a a.
Proof.
  intros. unfold same_sign. lia.
Qed.

Lemma same_sign_sym : forall a b, same_sign a b -> same_sign b a.
Proof.
  intros. unfold same_sign in *. lia.
Qed.

Record bigint_ent: Type := {
    cap: Z;
    data: list Z;
    sign: Prop;
}.

Definition store_Z (x: addr) (n: Z): Assertion :=
  EX (ptr: addr) (size cap: Z),
    [| Zabs size <= cap |] && 
    (([| size < 0 |] && [| n < 0 |] && mpd_store_Z_compact UINT_MOD ptr (-n) (-size) ** UIntArray.undef_seg ptr (-size) cap) ||
      ([| size >= 0 |] && [| n >= 0 |] && mpd_store_Z_compact UINT_MOD ptr n size ** UIntArray.undef_seg ptr size cap)) **
    &(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> size **
    &(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap **
    &(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr.

Definition store_Z_with_size (x: addr) (n: Z) (size: Z): Assertion :=
  EX (ptr: addr) (cap: Z),
    [| Zabs size <= cap |] && 
    (([| size < 0 |] && [| n < 0 |] && mpd_store_Z_compact UINT_MOD ptr (-n) (-size) ** UIntArray.undef_seg ptr (-size) cap) ||
      ([| size >= 0 |] && [| n >= 0 |] && mpd_store_Z_compact UINT_MOD ptr n size ** UIntArray.undef_seg ptr size cap)) **
    &(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> size **
    &(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap **
    &(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr.

Lemma store_Z_with_size_range: forall x n size,
  store_Z_with_size x n size |-- [| Zabs size + 1 <= INT_MAX |].
Proof.
  intros.
  unfold store_Z, store_Z_with_size.
  Intros ptr cap.
  Split ; Intros;
  do 2 sep_apply store_int_align4;
  sep_apply store_ptr_align4;
  sep_apply uint_array_undef_seg_align4;
  sep_apply mpd_store_Z_compact_align4;
  [ sep_apply (store_align4_merge (-size) (cap - (-size)));
    replace (- size + (cap - (-size))) with cap by lia |
    sep_apply (store_align4_merge size (cap - size));
    replace (size + (cap - size)) with cap by lia ];
  sep_apply (store_align4_merge cap 1);
  sep_apply (store_align4_merge (cap + 1) 1);
  sep_apply (store_align4_merge (cap + 1 + 1) 1);
  prop_apply store_align4_n_valid;
  Intros;
  entailer!;
  replace (Int.max_unsigned / 4) with 1073741823 in H2 by reflexivity;
  lia.
Qed.

Definition store_Z_remain_size (x: addr) (n: Z) (old_size: Z) (real_size: Z): Assertion :=
  EX (ptr: addr) (cap: Z),
    [| Zabs real_size <= cap |] && 
    (([| real_size < 0 |] && [| n < 0 |] && mpd_store_Z_compact UINT_MOD ptr (-n) (-real_size) ** UIntArray.undef_seg ptr (-real_size) cap) ||
      ([| real_size >= 0 |] && [| n >= 0 |] && mpd_store_Z_compact UINT_MOD ptr n real_size ** UIntArray.undef_seg ptr real_size cap)) **
    &(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> old_size **
    &(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap **
    &(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr.

Lemma store_Z_remain_size_range: forall x n old_size real_size,
  store_Z_remain_size x n old_size real_size |-- 
  [| Zabs real_size + 1 <= INT_MAX |].
Proof.
  intros.
  unfold store_Z_remain_size.
  Intros ptr cap.
  Split ; Intros;
  do 2 sep_apply store_int_align4;
  sep_apply store_ptr_align4;
  sep_apply uint_array_undef_seg_align4;
  sep_apply mpd_store_Z_compact_align4;
  [ sep_apply (store_align4_merge (-real_size) (cap - (-real_size)));
    replace (- real_size + (cap - (-real_size))) with cap by lia |
    sep_apply (store_align4_merge real_size (cap - real_size));
    replace (real_size + (cap - real_size)) with cap by lia ];
  sep_apply (store_align4_merge cap 1);
  sep_apply (store_align4_merge (cap + 1) 1);
  sep_apply (store_align4_merge (cap + 1 + 1) 1);
  prop_apply store_align4_n_valid;
  Intros;
  entailer!;
  replace (Int.max_unsigned / 4) with 1073741823 in H2 by reflexivity;
  lia.
Qed.

Lemma mpd_store_Z_bound: forall ptr n size,
  mpd_store_Z UINT_MOD ptr n size |-- 
  [| 0 <= n < UINT_MOD ^ size |].
Proof.
  intros.
  unfold mpd_store_Z.
  Intros data.
  pose proof list_to_Z_bound UINT_MOD.
  unfold UINT_MOD in  H1,H.
  pose proof H1 ltac:(lia) as H1.
  pose proof H1 data as H1. destruct H.
  pose proof H1 H2 as H1.
  subst. 
  entailer!.
Qed.

Lemma mpd_store_Z_compact_bound: forall ptr n size,
  mpd_store_Z_compact UINT_MOD ptr n size |--
  [| 0 <= n < UINT_MOD ^ size |].
Proof.
  intros.
  unfold mpd_store_Z_compact.
  Intros data.
  pose proof list_to_Z_bound UINT_MOD.
  unfold UINT_MOD in  H1,H.
  pose proof H1 ltac:(lia) as H1.
  pose proof H1 data as H1. destruct H.
  destruct H2.
  pose proof H1 H3 as H1.
  subst. 
  entailer!.
Qed.

Lemma mpn_add_ret_0_or_1: forall ap bp rp val_a val_b val_r an bn ret_val,
  val_r + ret_val * UINT_MOD ^ an = val_a + val_b -> an >= bn ->
  ( mpd_store_Z UINT_MOD ap val_a an ) **
  ( mpd_store_Z UINT_MOD bp val_b bn ) **
  ( mpd_store_Z UINT_MOD rp val_r an ) |--
    [| ret_val = 0 \/ ret_val = 1 |].
Proof.
  intros.
  prop_apply mpd_store_Z_bound.
  prop_apply mpd_store_Z_bound.
  Intros.
  prop_apply (mpd_store_Z_bound rp val_r an).
  Intros.
  entailer!.
  assert (UINT_MOD ^ an >= UINT_MOD ^ bn).
  { unfold UINT_MOD in *. 
  pose proof Z.pow_le_mono_r 4294967296 bn an as Hpow.
  pose proof Hpow ltac:(lia) ltac:(lia) as Hpow.
  lia. }
  assert (0 <= val_b < UINT_MOD ^ an) by lia.
  clear H2.
  clear H4.
  assert ( ret_val < 2).
  { destruct (Z_lt_le_dec ret_val 2) as [? | Hge2]; auto.
    exfalso.
    assert (val_a+val_b < 2 * UINT_MOD ^ an) by lia.
    assert (ret_val * UINT_MOD ^an >= 2 * UINT_MOD ^an).
    { pose proof Z.mul_le_mono_nonneg_r 2 ret_val (UINT_MOD ^ an).
    lia. }
    assert (val_r + ret_val * UINT_MOD ^ an >= 2 * UINT_MOD ^ an) by lia.
    assert (val_r + ret_val * UINT_MOD ^ an > val_a + val_b) by lia.
    lia.
  }
  assert (ret_val >=0).
  {
      destruct (Z_lt_le_dec ret_val 0) as [Hneg | ?]; auto.
      exfalso.
      - assert (ret_val * UINT_MOD ^ an <= -1 * UINT_MOD ^ an).
      {
          pose proof Z.mul_le_mono_nonneg_r ret_val (-1) (UINT_MOD ^ an).
          unfold UINT_MOD in H4 at 1.
          pose proof H4 ltac:(lia) ltac:(lia) as H4.
          lia.
      }
      assert (val_r + ret_val * UINT_MOD ^ an < 0) by lia.
      lia.
      -lia.
  }
  lia.
Qed.

Lemma mpn_sub_ret_0: forall ap bp rp val_a val_b val_r an bn rn ret_val ,
  val_r - ret_val * UINT_MOD ^ an = val_a - val_b -> 
  an >= bn ->
  bn >= 0 ->
  val_a >= val_b ->
  rn <= an ->
  ( mpd_store_Z UINT_MOD ap val_a an ) **
  ( mpd_store_Z UINT_MOD bp val_b bn ) **
  ( mpd_store_Z_compact UINT_MOD rp val_r rn ) |--
    [| ret_val = 0 |].
Proof.
  intros.
  prop_apply mpd_store_Z_bound.
  prop_apply mpd_store_Z_bound.
  Intros.
  prop_apply (mpd_store_Z_compact_bound rp val_r rn).
  Intros.
  entailer!.
  assert (UINT_MOD ^ an >= UINT_MOD ^ bn).
  { unfold UINT_MOD in *. 
  pose proof Z.pow_le_mono_r 4294967296 bn an as Hpow.
  pose proof Hpow ltac:(lia) ltac:(lia) as Hpow.
  lia. }
  assert (0 <= val_b < UINT_MOD ^ an) by lia.
  assert (0 <= val_r < UINT_MOD ^ rn) by lia.
  assert (0 <= val_a - val_b < UINT_MOD ^ an) by lia.
  assert (UINT_MOD ^ rn <= UINT_MOD ^ an).
  {
    unfold UINT_MOD in *. 
    pose proof Z.pow_le_mono_r 4294967296 rn an as Hpow.
    pose proof Hpow ltac:(lia) ltac:(lia) as Hpow. lia.
  }
  assert (0 <= val_r < UINT_MOD ^ an) by lia.
  clear H6 H7 H9 H11 H5.
  assert ( ret_val < 1).
  { destruct (Z_lt_le_dec ret_val 1) as [? | Hge1]; auto.
    exfalso.
    assert (-ret_val * UINT_MOD ^an <= (-1) * UINT_MOD ^an).
    { pose proof Z.mul_le_mono_nonneg_r (-ret_val) (-1) (UINT_MOD ^ an). unfold UINT_MOD in H5 at 1.
    pose proof H5 ltac:(lia) ltac:(lia) as H5. lia.  }
    assert (val_r - ret_val * UINT_MOD ^ an <= 0) by lia.
    lia.
  }
  assert (ret_val >= 0).
  {
      destruct (Z_lt_le_dec ret_val 0) as [Hneg | ?]; auto.
      exfalso.
      - assert (-ret_val * UINT_MOD ^ an >=   UINT_MOD ^ an).
      {
          pose proof Z.mul_le_mono_nonneg_r 1 (-ret_val) (UINT_MOD ^ an).
          unfold UINT_MOD in H6 at 1.
          pose proof H6 ltac:(lia) ltac:(lia) as H6.
          rewrite Z.mul_1_l in H6.
          pose proof Z.le_ge (UINT_MOD ^ an) (- ret_val * UINT_MOD ^ an).
          lia.
      }
      assert (val_r - ret_val * UINT_MOD ^ an > UINT_MOD ^ an) by lia.
      lia.
      -lia.
  }
  lia.
Qed.

Lemma mpd_store_Z_to_mpd_store_Z_compact: forall ptr n size,
    is_compact_Z UINT_MOD n size ->
    (mpd_store_Z UINT_MOD ptr n size) |--
    (mpd_store_Z_compact UINT_MOD ptr n size).
Proof.
    intros.
    unfold mpd_store_Z, mpd_store_Z_compact.
    Intros data.
    Exists data. entailer!.
    unfold is_compact_Z in H.
    destruct H.
    pose proof list_to_Z_reverse_same_length_injection UINT_MOD.
    unfold UINT_MOD in H2 at 1.
    pose proof H2 ltac:(lia) data x as H2.
    destruct H.
    rewrite H in H2.
    pose proof H2 ltac:(lia) as H2.
    destruct H0.
    destruct H3.
    destruct H5.
    pose proof H2 H4 H5 ltac:(lia) as H2.
    rewrite H2.
    tauto.
Qed.

Lemma is_compact_Z_add_0: forall n m size1 size2,
  is_compact_Z UINT_MOD n size1 ->
  is_compact_Z UINT_MOD m size2 ->
  n + m < UINT_MOD ^ (Z.max size1 size2) ->
  is_compact_Z UINT_MOD (n + m) (Z.max size1 size2).
Proof.
  intros n m size1 size2 H1 H2 Hbound.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos n size1 H1) as [Hs1 Hn].
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos m size2 H2) as [Hs2 Hm].
  apply is_compact_Z_from_bounds; unfold UINT_MOD; try lia.
  destruct Hn as [[Hn1 Hn2] | [Hn1 [Hn2 Hn3]]];
  destruct Hm as [[Hm1 Hm2] | [Hm1 [Hm2 Hm3]]].
  - (* size1 = 0, n = 0, size2 = 0, m = 0 *)
    left. subst. simpl. lia.
  - (* size1 = 0, n = 0, size2 > 0 *)
    subst n. rewrite Z.add_0_l.
    right. split.
    + rewrite Z.max_r; lia.
    + rewrite Z.max_r; try lia.
      split; unfold UINT_MOD in *; try lia. 
  - (* size1 > 0, size2 = 0, m = 0 *)
    subst m. rewrite Z.add_0_r.
    right. split.
    + rewrite Z.max_l; lia.
    + rewrite Z.max_l; try lia. unfold UINT_MOD in *.
      split; try lia.
  - (* size1 > 0, size2 > 0 *)
    right. split.
    + lia.
    + split.
      * destruct (Z.max_spec size1 size2) as [[Hle Heq] | [Hlt Heq]]; rewrite Heq.
        -- assert (UINT_MOD ^ (size2 - 1) <= m) by lia.
           assert (0 <= n) by (unfold UINT_MOD in *; lia).
           unfold UINT_MOD in *.
           lia.
        -- assert (UINT_MOD ^ (size1 - 1) <= n) by lia.
           unfold UINT_MOD in *; lia.
      * unfold UINT_MOD in *. lia.
Qed.


Lemma is_compact_Z_add_1: forall n m size1 size2,
  is_compact_Z UINT_MOD n size1 ->
  is_compact_Z UINT_MOD m size2 ->
  n + m >= UINT_MOD ^ (Z.max size1 size2) ->
  n + m < 2 * UINT_MOD ^ (Z.max size1 size2) ->
  is_compact_Z UINT_MOD (n + m) ((Z.max size1 size2)+1).
Proof.
  intros n m size1 size2 H1 H2 Hlo Hhi.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos n size1 H1) as [Hs1 Hn].
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos m size2 H2) as [Hs2 Hm].
  apply is_compact_Z_add_helper_1; unfold UINT_MOD in *; try lia.
Qed.

Lemma mpd_store_Z_to_is_compact_Z: forall ptr n size,
  (mpd_store_Z_compact UINT_MOD ptr n size) |--
  [|is_compact_Z UINT_MOD n size|].
Proof.
  intros.
  unfold mpd_store_Z_compact, is_compact_Z.
  Intros data.
  entailer!. exists data.
  rewrite H0. tauto.
Qed.

Lemma mpd_store_Z_compact_to_mpd_store_Z: 
forall (ptr: Z) (size: Z) (l: Z) ,
  mpd_store_Z_compact UINT_MOD ptr l size  |--
  mpd_store_Z UINT_MOD ptr l size .
Proof.
  intros.
  unfold mpd_store_Z_compact, mpd_store_Z. Intros data. Exists data. entailer!.
Qed.

Lemma mpd_store_Z_compact_mono_size: forall ap bp n m size1 size2,
  n>m ->
  mpd_store_Z_compact UINT_MOD ap n size1 **
  mpd_store_Z_compact UINT_MOD bp m size2 |--
  [|size1 >= size2|].
Proof.
  intros.
  unfold mpd_store_Z_compact.
  Intros data_a data_b.
  entailer!.
  subst size1 size2.
  destruct H0 as [Hn [Hlast_a Hbound_a]].
  destruct H2 as [Hm [Hlast_b Hbound_b]].
  subst n m.
  (* data_b = nil 的情况 *)
  destruct data_b as [ | z data_b'].
  - rewrite Zlength_nil.
    pose proof (Zlength_nonneg data_a). lia.
  - (* data_b 非空，使用 compact bound *)
    pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos (z :: data_b') Hbound_b Hlast_b) as Hb.
    pose proof (list_to_Z_pos UINT_MOD UINT_MOD_pos data_a Hbound_a) as Hpos_a.
    (* data_a 也必须非空，因为 list_to_Z data_a > list_to_Z (z::data_b') > 0 *)
    destruct data_a as [ | y data_a'].
    + simpl in *. lia. (* 矛盾：list_to_Z nil = 0 *)
    + pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos (y :: data_a') Hbound_a Hlast_a) as Ha.
      (* 反证：如果 Zlength data_a < Zlength data_b *)
      destruct (Z_lt_dec (Zlength (y :: data_a')) (Zlength (z :: data_b'))).
      * exfalso.
        (* n < UINT_MOD^size1 <= UINT_MOD^(size2-1) <= m，矛盾 *)
        assert (UINT_MOD ^ (Zlength (y :: data_a')) <= UINT_MOD ^ (Zlength (z :: data_b') - 1)).
        { apply Z.pow_le_mono_r.
          - unfold UINT_MOD. lia.
          - pose proof (Zlength_nonneg data_a').
            pose proof (Zlength_nonneg data_b').
            rewrite !Zlength_cons in *. lia. }
        lia.
      * lia.
Qed.

Lemma store_Z_with_size_2_store_Z: forall x n size,
  store_Z_with_size x n size |--
  store_Z x n.
Proof.
  intros.
  unfold store_Z_with_size, store_Z.
  Intros ptr cap.
  Exists ptr size cap. entailer!.
  apply derivable1_orp_elim.
  - Left. entailer!.
  - Right. entailer!.
Qed.

Lemma lxor_negative_implies_opposite_signs_simple:
  forall x y : Z,
    Z.lxor x y < 0 ->
    (x < 0 /\ y >= 0) \/ (x >= 0 /\ y < 0).
Proof.
    intros x y Hlxor.
    destruct (Z_lt_ge_dec x 0) as [Hx_neg | Hx_nonneg].
    -   left.
        split.
        * lia.
        * destruct (Z_lt_ge_dec y 0) as [Hy_neg | Hy_nonneg].
        + 
        exfalso.
        assert (H: 0 <= Z.lxor x y).
        {
            rewrite Z.lxor_nonneg.
            split; intro; lia.
        }
        lia.
        + 
        exact Hy_nonneg.
    -   right.
        split; [lia| ].
        destruct (Z_lt_ge_dec y 0) as [Hy_neg | Hy_nonneg].
        + 
        exact Hy_neg.
        + 
        exfalso.
        assert (H: 0 <= Z.lxor x y).
        {
            rewrite Z.lxor_nonneg.
            split; intro; lia.
        }
        lia.
Qed.

Lemma lxor_nonneg_implies_same_sign:
  forall x y : Z,
    Z.lxor x y >= 0 ->
    (x >= 0 /\ y >= 0) \/ (x < 0 /\ y < 0).
Proof.
  intros x y Hlxor.
  pose proof (proj1 (Z.lxor_nonneg x y) ltac:(lia)) as Hsame.
  destruct (Z_lt_ge_dec x 0); destruct (Z_lt_ge_dec y 0);
    try (left; lia); try (right; lia).
Qed.

Lemma store_Z_with_size_2_same_sign: forall x n size,
  store_Z_with_size x n size |--
  [|same_sign n size|].
Proof.
  intros.
  unfold store_Z_with_size, same_sign.
  Intros ptr cap.
  apply derivable1_orp_elim.
  - entailer!.
  - entailer!.
Qed.

Lemma store_Z_remain_size_2_same_sign: forall x n old_size real_size,
  store_Z_remain_size x n old_size real_size |--
  [|same_sign n real_size|].
Proof.
  intros.
  unfold store_Z_remain_size, same_sign.
  Intros ptr cap.
  apply derivable1_orp_elim; entailer!.
Qed.
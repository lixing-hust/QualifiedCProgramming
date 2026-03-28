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

End Internal.


Definition UINT_MOD := (4294967296).

Theorem UINT_MOD_pos : 0 < UINT_MOD.
Proof.
  unfold UINT_MOD.
  lia.
Qed.

Record bigint_ent: Type := {
    cap: Z;
    data: list Z;
    sign: Prop;
}.

Definition store_Z (x: addr) (n: Z): Assertion :=
  EX (ptr: addr) (size cap: Z),
    [| Zabs size <= cap |] && 
    (([| size < 0 |] && [| n < 0 |] && mpd_store_Z_compact UINT_MOD ptr (-n) (-size) ** UIntArray.undef_ceil ptr (-size) cap) ||
      ([| size >= 0 |] && [| n >= 0 |] && mpd_store_Z_compact UINT_MOD ptr n size ** UIntArray.undef_ceil ptr size cap)) **
    &(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> size **
    &(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap **
    &(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr.
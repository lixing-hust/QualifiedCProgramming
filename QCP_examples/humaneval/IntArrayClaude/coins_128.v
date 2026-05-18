Load "../spec/128".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import naive_C_Rules.
Import ListNotations.
Local Open Scope Z_scope.

Definition sum_abs_prefix (i : Z) (l : list Z) : Z :=
  fold_right Z.add 0 (map Z.abs (sublist 0 i l)).

Definition prod_sgn_prefix (i : Z) (l : list Z) : Z :=
  fold_right Z.mul 1 (map Z.sgn (sublist 0 i l)).

Definition prod_signs_prefix (i : Z) (l : list Z) (sum prods : Z) : Prop :=
  0 <= i <= Zlength l /\
  sum = sum_abs_prefix i l /\
  prods = prod_sgn_prefix i l.

Definition prod_signs_int_range (l : list Z) : Prop :=
  (forall i,
      0 <= i < Zlength l ->
      INT_MIN < Znth i l 0 <= INT_MAX) /\
  (forall i,
      0 <= i <= Zlength l ->
      0 <= sum_abs_prefix i l <= INT_MAX).

Definition problem_128_pre_z (l : list Z) : Prop :=
  problem_128_pre l.

Definition problem_128_spec_z (l : list Z) (out : Z) : Prop :=
  match l with
  | nil => out = -32768
  | _ :: _ => problem_128_spec l (Some out)
  end.

Lemma fold_right_add_app_single : forall (xs : list Z) (x : Z),
  fold_right Z.add 0 (xs ++ [x]) = fold_right Z.add 0 xs + x.
Proof.
  induction xs; intros x; simpl.
  - lia.
  - rewrite IHxs. lia.
Qed.

Lemma fold_right_mul_app_single : forall (xs : list Z) (x : Z),
  fold_right Z.mul 1 (xs ++ [x]) = fold_right Z.mul 1 xs * x.
Proof.
  induction xs; intros x; simpl.
  - rewrite Z.mul_comm.
    destruct x; reflexivity.
  - rewrite IHxs. rewrite Z.mul_assoc. reflexivity.
Qed.

Lemma sublist_snoc_Znth_128 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  intros.
  rewrite (sublist_split 0 (i + 1) i l).
  - replace (sublist i (i + 1) l) with [Znth i l 0].
    + reflexivity.
    + symmetry. apply sublist_single.
      rewrite <- Zlength_correct. lia.
  - lia.
  - rewrite <- Zlength_correct. lia.
Qed.

Lemma sum_abs_prefix_snoc : forall l i,
  0 <= i < Zlength l ->
  sum_abs_prefix (i + 1) l =
    sum_abs_prefix i l + Z.abs (Znth i l 0).
Proof.
  intros.
  unfold sum_abs_prefix.
  rewrite sublist_snoc_Znth_128 by lia.
  rewrite map_app.
  simpl.
  rewrite fold_right_add_app_single.
  reflexivity.
Qed.

Lemma prod_sgn_prefix_snoc : forall l i,
  0 <= i < Zlength l ->
  prod_sgn_prefix (i + 1) l =
    prod_sgn_prefix i l * Z.sgn (Znth i l 0).
Proof.
  intros.
  unfold prod_sgn_prefix.
  rewrite sublist_snoc_Znth_128 by lia.
  rewrite map_app.
  simpl.
  rewrite fold_right_mul_app_single.
  reflexivity.
Qed.

Lemma prod_sgn_prefix_bound : forall i l,
  0 <= i <= Zlength l ->
  -1 <= prod_sgn_prefix i l <= 1.
Proof.
  intros i l Hi.
  unfold prod_sgn_prefix.
  remember (sublist 0 i l) as xs.
  clear Heqxs l i Hi.
  induction xs; simpl.
  - lia.
  - pose proof (Z.sgn_spec a) as Hsgn.
    lia.
Qed.

Lemma prod_signs_prefix_init : forall l,
  0 <= Zlength l ->
  prod_signs_prefix 0 l 0 1.
Proof.
  intros.
  unfold prod_signs_prefix, sum_abs_prefix, prod_sgn_prefix.
  rewrite sublist_nil by lia.
  simpl.
  repeat split; lia.
Qed.

Lemma prod_signs_prefix_zero : forall i l sum prods x,
  prod_signs_prefix i l sum prods ->
  0 <= i < Zlength l ->
  x = Znth i l 0 ->
  x = 0 ->
  prod_signs_prefix (i + 1) l (sum + Z.abs x) 0.
Proof.
  intros i l sum prods x Hpref Hi Hx Hz.
  subst x.
  unfold prod_signs_prefix in *.
  destruct Hpref as [Hbounds [Hsum Hprod]].
  repeat split; try lia.
  - rewrite sum_abs_prefix_snoc by lia. lia.
  - rewrite prod_sgn_prefix_snoc by lia. simpl. lia.
Qed.

Lemma prod_signs_prefix_neg : forall i l sum prods x,
  prod_signs_prefix i l sum prods ->
  0 <= i < Zlength l ->
  x = Znth i l 0 ->
  x < 0 ->
  prod_signs_prefix (i + 1) l (sum + Z.abs x) (- prods).
Proof.
  intros i l sum prods x Hpref Hi Hx Hneg.
  subst x.
  unfold prod_signs_prefix in *.
  destruct Hpref as [Hbounds [Hsum Hprod]].
  repeat split; try lia.
  - rewrite sum_abs_prefix_snoc by lia. lia.
  - rewrite prod_sgn_prefix_snoc by lia.
    rewrite Z.sgn_neg by lia.
    lia.
Qed.

Lemma prod_signs_prefix_pos : forall i l sum prods x,
  prod_signs_prefix i l sum prods ->
  0 <= i < Zlength l ->
  x = Znth i l 0 ->
  0 < x ->
  prod_signs_prefix (i + 1) l (sum + Z.abs x) prods.
Proof.
  intros i l sum prods x Hpref Hi Hx Hpos.
  subst x.
  unfold prod_signs_prefix in *.
  destruct Hpref as [Hbounds [Hsum Hprod]].
  repeat split; try lia.
  - rewrite sum_abs_prefix_snoc by lia. lia.
  - rewrite prod_sgn_prefix_snoc by lia.
    rewrite Z.sgn_pos by lia.
    lia.
Qed.

Lemma prod_signs_prefix_sum_range : forall i l sum prods,
  prod_signs_prefix i l sum prods ->
  prod_signs_int_range l ->
  0 <= sum <= INT_MAX.
Proof.
  intros i l sum prods Hpref [_ Hrange].
  unfold prod_signs_prefix in Hpref.
  destruct Hpref as [Hbounds [Hsum _]].
  subst sum.
  apply Hrange.
  exact Hbounds.
Qed.

Lemma prod_signs_prefix_prod_bound : forall i l sum prods,
  prod_signs_prefix i l sum prods ->
  -1 <= prods <= 1.
Proof.
  intros i l sum prods Hpref.
  unfold prod_signs_prefix in Hpref.
  destruct Hpref as [Hbounds [_ Hprod]].
  subst prods.
  apply prod_sgn_prefix_bound.
  exact Hbounds.
Qed.

Lemma prod_signs_input_int_range : forall l i,
  prod_signs_int_range l ->
  0 <= i < Zlength l ->
  INT_MIN < Znth i l 0 <= INT_MAX.
Proof.
  intros l i [Hrange _] Hi.
  apply Hrange.
  exact Hi.
Qed.

Lemma prod_signs_next_sum_range : forall i l sum prods x mag,
  prod_signs_prefix i l sum prods ->
  prod_signs_int_range l ->
  0 <= i < Zlength l ->
  x = Znth i l 0 ->
  mag = Z.abs x ->
  INT_MIN <= sum + mag <= INT_MAX.
Proof.
  intros i l sum prods x mag Hpref Hrange Hi Hx Hmag.
  subst x mag.
  destruct Hrange as [_ Hsum_range].
  unfold prod_signs_prefix in Hpref.
  destruct Hpref as [_ [Hsum _]].
  subst sum.
  pose proof (Hsum_range (i + 1)) as Hnext.
  rewrite sum_abs_prefix_snoc in Hnext by lia.
  lia.
Qed.

Lemma prod_signs_prefix_full_spec : forall l sum prods,
  l <> nil ->
  prod_signs_prefix (Zlength l) l sum prods ->
  problem_128_spec l (Some (sum * prods)).
Proof.
  intros l sum prods Hnonempty Hpref.
  unfold prod_signs_prefix in Hpref.
  destruct Hpref as [Hbounds [Hsum Hprod]].
  unfold problem_128_spec.
  destruct l.
  - contradiction.
  - rewrite Hsum, Hprod.
    unfold sum_abs_prefix, prod_sgn_prefix.
    repeat rewrite sublist_self by lia.
    reflexivity.
Qed.

Lemma problem_128_spec_z_empty : forall l,
  Zlength l = 0 ->
  problem_128_spec_z l (-32768).
Proof.
  intros l Hlen.
  destruct l; simpl; auto.
  rewrite Zlength_cons in Hlen.
  pose proof (Zlength_nonneg l).
  lia.
Qed.

Lemma problem_128_spec_z_nonempty : forall l sum prods,
  Zlength l > 0 ->
  prod_signs_prefix (Zlength l) l sum prods ->
  problem_128_spec_z l (sum * prods).
Proof.
  intros l sum prods Hlen Hpref.
  destruct l.
  - rewrite Zlength_nil in Hlen. lia.
  - apply prod_signs_prefix_full_spec; [discriminate | exact Hpref].
Qed.

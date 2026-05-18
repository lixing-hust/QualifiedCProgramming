Load "../spec/152".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Fixpoint compare_list (game guess : list Z) : list Z :=
  match game, guess with
  | g :: gs, q :: qs => Z.abs (g - q) :: compare_list gs qs
  | _, _ => nil
  end.

Definition compare_prefix_list (i : Z) (game guess : list Z) : list Z :=
  compare_list (sublist 0 i game) (sublist 0 i guess).

Definition compare_prefix (i : Z) (game guess output : list Z) : Prop :=
  0 <= i <= Zlength game /\
  i <= Zlength guess /\
  output = compare_prefix_list i game guess.

Definition problem_152_pre_z (game guess : list Z) : Prop :=
  problem_152_pre game guess.

Definition problem_152_spec_z (game guess output : list Z) : Prop :=
  problem_152_spec game guess output.

Definition compare_int_range (game guess : list Z) : Prop :=
  forall i,
    0 <= i < Zlength game ->
    INT_MIN < Znth i game 0 - Znth i guess 0 <= INT_MAX.

Lemma compare_list_length : forall game guess,
  length game = length guess ->
  length (compare_list game guess) = length game.
Proof.
  induction game as [|g gs IH]; intros guess Hlen.
  - reflexivity.
  - destruct guess as [|q qs]; simpl in *; [lia|].
    f_equal.
    apply IH.
    lia.
Qed.

Lemma compare_prefix_0 : forall game guess,
  0 <= Zlength game ->
  0 <= Zlength guess ->
  compare_prefix 0 game guess nil.
Proof.
  intros.
  unfold compare_prefix, compare_prefix_list.
  rewrite !sublist_nil by lia.
  repeat split; try lia; reflexivity.
Qed.

Lemma compare_prefix_Zlength : forall i game guess output,
  compare_prefix i game guess output ->
  problem_152_pre_z game guess ->
  Zlength output = i.
Proof.
  intros i game guess output [Hbounds [Hguess Hout]] Hpre.
  subst output.
  unfold compare_prefix_list.
  unfold problem_152_pre_z, problem_152_pre in Hpre.
  rewrite Zlength_correct.
  rewrite compare_list_length.
  - assert (Hsub : length (sublist 0 i game) = Z.to_nat i).
    {
      rewrite sublist_length.
      - replace (i - 0) with i by lia. reflexivity.
      - lia.
      - destruct Hbounds as [_ Hile].
        rewrite <- Zlength_correct.
        exact Hile.
    }
    rewrite Hsub.
    rewrite Z2Nat.id by lia.
    reflexivity.
  - assert (Hg : length (sublist 0 i game) = Z.to_nat i).
    {
      rewrite sublist_length.
      - replace (i - 0) with i by lia. reflexivity.
      - lia.
      - destruct Hbounds as [_ Hile].
        rewrite <- Zlength_correct.
        exact Hile.
    }
    assert (Hq : length (sublist 0 i guess) = Z.to_nat i).
    {
      rewrite sublist_length.
      - replace (i - 0) with i by lia. reflexivity.
      - lia.
      - rewrite <- Zlength_correct.
        exact Hguess.
    }
    rewrite Hg, Hq.
    reflexivity.
Qed.

Lemma compare_prefix_snoc : forall i game guess output diff value,
  compare_prefix i game guess output ->
  0 <= i < Zlength game ->
  i < Zlength guess ->
  diff = Znth i game 0 - Znth i guess 0 ->
  value = Z.abs diff ->
  compare_prefix (i + 1) game guess (output ++ [value]).
Proof.
  intros i game guess output diff value [Hbounds [Hguess Hout]] Hi Higuess Hdiff Hvalue.
  subst output diff value.
  unfold compare_prefix, compare_prefix_list in *.
  repeat split; try lia.
  rewrite (sublist_split 0 (i + 1) i game)
    by (try rewrite <- Zlength_correct; lia).
  rewrite (sublist_split 0 (i + 1) i guess)
    by (try rewrite <- Zlength_correct; lia).
  rewrite (sublist_single i game 0) by (rewrite <- Zlength_correct; lia).
  rewrite (sublist_single i guess 0) by (rewrite <- Zlength_correct; lia).
  clear Hbounds Hguess.
  remember (sublist 0 i game) as gs.
  remember (sublist 0 i guess) as qs.
  assert (Hlen : length gs = length qs).
  {
    subst gs qs.
    assert (Hg : length (sublist 0 i game) = Z.to_nat i).
    {
      rewrite sublist_length.
      - replace (i - 0) with i by lia. reflexivity.
      - lia.
      - rewrite <- Zlength_correct. lia.
    }
    assert (Hq : length (sublist 0 i guess) = Z.to_nat i).
    {
      rewrite sublist_length.
      - replace (i - 0) with i by lia. reflexivity.
      - lia.
      - rewrite <- Zlength_correct. lia.
    }
    rewrite Hg, Hq.
    reflexivity.
  }
  clear Heqgs Heqqs.
  revert qs Hlen.
  induction gs as [|g gs IH]; intros qs Hlen; destruct qs as [|q qs]; simpl in *; try lia.
  - reflexivity.
  - f_equal.
    apply IH.
    lia.
Qed.

Lemma compare_prefix_snoc_Zlength : forall i game guess output diff value,
  compare_prefix i game guess output ->
  problem_152_pre_z game guess ->
  0 <= i < Zlength game ->
  diff = Znth i game 0 - Znth i guess 0 ->
  value = Z.abs diff ->
  Zlength (output ++ [value]) = i + 1.
Proof.
  intros.
  rewrite Zlength_app.
  rewrite (compare_prefix_Zlength i game guess output); try assumption.
  change (Zlength [value]) with 1.
  lia.
Qed.

Lemma compare_int_range_at : forall game guess i,
  compare_int_range game guess ->
  0 <= i < Zlength game ->
  INT_MIN < Znth i game 0 - Znth i guess 0 <= INT_MAX.
Proof.
  intros.
  apply H; assumption.
Qed.

Lemma compare_prefix_full_spec : forall game guess output,
  compare_prefix (Zlength game) game guess output ->
  problem_152_pre_z game guess ->
  problem_152_spec_z game guess output.
Proof.
  intros game guess output Hpref Hpre.
  unfold problem_152_spec_z, problem_152_spec.
  unfold problem_152_pre_z, problem_152_pre in Hpre.
  split; [assumption|].
  split.
  - apply Nat2Z.inj.
    repeat rewrite <- Zlength_correct.
    rewrite (compare_prefix_Zlength (Zlength game) game guess output); try assumption.
    reflexivity.
  - intros n Hn.
    destruct Hpref as [_ [_ Hout]].
    subst output.
    unfold compare_prefix_list.
    rewrite sublist_self by reflexivity.
    rewrite (sublist_self guess) by (rewrite !Zlength_correct; lia).
    revert game guess Hpre Hn.
    induction n; intros game guess Hlen Hn.
    + destruct game as [|g gs], guess as [|q qs]; simpl in *; try lia; reflexivity.
    + destruct game as [|g gs], guess as [|q qs]; simpl in *; try lia.
      apply IHn; lia.
Qed.

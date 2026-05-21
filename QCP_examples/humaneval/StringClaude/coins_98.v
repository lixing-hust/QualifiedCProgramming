Load "../spec/98".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition is_upper_vowel_z (x : Z) : bool :=
  Z.eqb x 65 || Z.eqb x 69 || Z.eqb x 73 || Z.eqb x 79 || Z.eqb x 85.

Definition is_even_index_z (i : Z) : bool :=
  Z.eqb (Z.rem i 2) 0.

Fixpoint count_upper_even_upto_nat (n : nat) (l : list Z) : Z :=
  match n with
  | O => 0
  | S n' =>
      let s := count_upper_even_upto_nat n' l in
      let i := Z.of_nat n' in
      if andb (is_even_index_z i) (is_upper_vowel_z (Znth i l 0))
      then s + 1
      else s
  end.

Definition count_upper_even_upto (i : Z) (l : list Z) : Z :=
  count_upper_even_upto_nat (Z.to_nat i) l.

Definition problem_98_pre_z (s : list Z) : Prop :=
  problem_98_pre (string_of_list_z s).

Definition problem_98_spec_z (s : list Z) (output : Z) : Prop :=
  problem_98_spec (string_of_list_z s) (Z.to_nat output).

Lemma count_upper_even_upto_0 : forall l,
  count_upper_even_upto 0 l = 0.
Proof.
  intros l.
  unfold count_upper_even_upto.
  reflexivity.
Qed.

Lemma is_upper_vowel_z_true : forall x,
  x = 65 \/ x = 69 \/ x = 73 \/ x = 79 \/ x = 85 ->
  is_upper_vowel_z x = true.
Proof.
  intros x Hx.
  unfold is_upper_vowel_z.
  destruct Hx as [-> | [-> | [-> | [-> | ->]]]];
    repeat rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma is_upper_vowel_z_false : forall x,
  x <> 65 -> x <> 69 -> x <> 73 -> x <> 79 -> x <> 85 ->
  is_upper_vowel_z x = false.
Proof.
  intros x H65 H69 H73 H79 H85.
  unfold is_upper_vowel_z.
  repeat match goal with
  | |- context[Z.eqb ?a ?b] =>
      replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; lia)
  end.
  reflexivity.
Qed.

Lemma is_even_index_z_true : forall i,
  Z.rem i 2 = 0 ->
  is_even_index_z i = true.
Proof.
  intros i Hi.
  unfold is_even_index_z.
  rewrite Hi, Z.eqb_refl.
  reflexivity.
Qed.

Lemma is_even_index_z_false : forall i,
  Z.rem i 2 <> 0 ->
  is_even_index_z i = false.
Proof.
  intros i Hi.
  unfold is_even_index_z.
  apply Z.eqb_neq.
  exact Hi.
Qed.

Lemma is_even_index_z_nat : forall n,
  is_even_index_z (Z.of_nat n) = Nat.even n.
Proof.
  assert (Hpair : forall n,
    is_even_index_z (Z.of_nat n) = Nat.even n /\
    is_even_index_z (Z.of_nat (S n)) = Nat.even (S n)).
  {
    induction n as [| n [IHn IHSn]].
    - split; reflexivity.
    - split.
      + exact IHSn.
      + unfold is_even_index_z in *.
        replace (Z.of_nat (S (S n))) with (Z.of_nat n + 1 * 2) by lia.
        rewrite Z.rem_add by lia.
        rewrite Nat.even_succ_succ.
        exact IHn.
  }
  intro n.
  apply Hpair.
Qed.

Lemma count_upper_even_upto_nat_nonneg : forall n l,
  0 <= count_upper_even_upto_nat n l.
Proof.
  induction n as [| n IH]; intros l; simpl.
  - lia.
  - destruct (is_even_index_z (Z.of_nat n) && is_upper_vowel_z (Znth (Z.of_nat n) l 0));
      pose proof (IH l); lia.
Qed.

Lemma count_upper_even_upto_step_hit : forall i l,
  0 <= i ->
  Z.rem i 2 = 0 ->
  (Znth i l 0 = 65 \/ Znth i l 0 = 69 \/ Znth i l 0 = 73 \/
   Znth i l 0 = 79 \/ Znth i l 0 = 85) ->
  count_upper_even_upto (i + 1) l =
  count_upper_even_upto i l + 1.
Proof.
  intros i l Hi Heven Hhit.
  unfold count_upper_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  rewrite is_even_index_z_true by exact Heven.
  rewrite is_upper_vowel_z_true by exact Hhit.
  reflexivity.
Qed.

Lemma count_upper_even_upto_step_even_miss : forall i l,
  0 <= i ->
  Z.rem i 2 = 0 ->
  Znth i l 0 <> 65 -> Znth i l 0 <> 69 -> Znth i l 0 <> 73 ->
  Znth i l 0 <> 79 -> Znth i l 0 <> 85 ->
  count_upper_even_upto (i + 1) l =
  count_upper_even_upto i l.
Proof.
  intros i l Hi Heven H65 H69 H73 H79 H85.
  unfold count_upper_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  rewrite is_even_index_z_true by exact Heven.
  rewrite is_upper_vowel_z_false by auto.
  reflexivity.
Qed.

Lemma count_upper_even_upto_step_odd : forall i l,
  0 <= i ->
  Z.rem i 2 <> 0 ->
  count_upper_even_upto (i + 1) l =
  count_upper_even_upto i l.
Proof.
  intros i l Hi Hodd.
  unfold count_upper_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  rewrite is_even_index_z_false by exact Hodd.
  reflexivity.
Qed.

Lemma is_upper_vowel_z_correct : forall x,
  0 <= x < 256 ->
  is_upper_vowel_z x = is_uppercase_vowel_bool (ascii_of_z x).
Proof.
  intros x Hrange.
  remember (ascii_of_z x) as c eqn:Hc.
  pose proof (nat_of_ascii_ascii_of_z x Hrange) as Hnat.
  rewrite <- Hc in Hnat.
  assert (Hx : x = Z.of_nat (nat_of_ascii c)).
  {
    rewrite <- (Z2Nat.id x) by lia.
    rewrite <- Hnat.
    reflexivity.
  }
  subst x.
  destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7; vm_compute; reflexivity.
Qed.

Lemma count_upper_even_upto_nat_correct : forall n l,
  (n <= List.length l)%nat ->
  ascii_range_z l ->
  Z.to_nat (count_upper_even_upto_nat n l) =
  List.length
    (filter
       (fun i : nat =>
          match String.get i (string_of_list_z l) with
          | Some c => Nat.even i && is_uppercase_vowel_bool c
          | None => false
          end)
       (seq 0 n)).
Proof.
  induction n as [| n IH]; intros l Hn Hrange.
  - reflexivity.
  - cbn [count_upper_even_upto_nat].
    rewrite seq_S.
    rewrite filter_app.
    rewrite length_app.
    simpl.
    rewrite <- IH by (lia || exact Hrange).
    assert (Hnlt : (n < List.length l)%nat) by lia.
    rewrite string_get_string_of_list_z by exact Hnlt.
    replace (Znth (Z.of_nat n) l 0) with (nth n l 0).
    2:{ unfold Znth. rewrite Nat2Z.id. reflexivity. }
    assert (Hchar : 0 <= nth n l 0 < 256).
    {
      specialize (Hrange (Z.of_nat n)).
      unfold Znth in Hrange.
      rewrite Nat2Z.id in Hrange.
      apply Hrange.
      rewrite Zlength_correct.
      lia.
    }
    rewrite is_even_index_z_nat.
    rewrite is_upper_vowel_z_correct by exact Hchar.
    destruct (Nat.even n && is_uppercase_vowel_bool (ascii_of_z (nth n l 0))) eqn:Hhit.
    + rewrite Z2Nat.inj_add by
        (pose proof (count_upper_even_upto_nat_nonneg n l); lia).
      simpl. lia.
    + simpl. rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma problem_98_spec_z_intro : forall s output,
  ascii_range_z s ->
  output = count_upper_even_upto (Zlength s) s ->
  problem_98_spec_z s output.
Proof.
  intros s output Hrange Hout.
  unfold problem_98_spec_z, problem_98_spec, count_upper_impl.
  rewrite Hout.
  unfold count_upper_even_upto.
  rewrite z_to_nat_Zlength.
  rewrite string_of_list_z_length.
  apply count_upper_even_upto_nat_correct.
  - lia.
  - exact Hrange.
Qed.

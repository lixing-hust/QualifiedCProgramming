Load "../spec/66".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition is_upper_z (x : Z) : bool :=
  (Z.leb 65 x) && (Z.leb x 90).

Fixpoint sum_upper_list_z (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if is_upper_z x then x else 0) + sum_upper_list_z xs
  end.

Definition sum_upper_upto (i : Z) (l : list Z) : Z :=
  sum_upper_list_z (firstn (Z.to_nat i) l).

Definition problem_66_pre_z (s : list Z) : Prop :=
  problem_66_pre (string_of_list_z s).

Definition problem_66_spec_z (s : list Z) (output : Z) : Prop :=
  problem_66_spec (string_of_list_z s) (Z.to_nat output).

Definition digit_sum_int_range (s : list Z) : Prop :=
  forall i,
    0 <= i ->
    i < Zlength s ->
    INT_MIN <= sum_upper_upto i s <= INT_MAX /\
    INT_MIN <= sum_upper_upto i s + Znth i s 0 <= INT_MAX.

Lemma sum_upper_upto_0 : forall l,
  sum_upper_upto 0 l = 0.
Proof.
  intros l.
  unfold sum_upper_upto.
  reflexivity.
Qed.

Lemma sum_upper_list_z_app : forall l1 l2,
  sum_upper_list_z (l1 ++ l2) =
  sum_upper_list_z l1 + sum_upper_list_z l2.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma sum_upper_list_z_nonneg : forall l,
  0 <= sum_upper_list_z l.
Proof.
  induction l as [| x xs IH]; simpl.
  - lia.
  - destruct (is_upper_z x) eqn:Hupper.
    + unfold is_upper_z in Hupper.
      apply andb_true_iff in Hupper.
      destruct Hupper as [Hlo _].
      apply Z.leb_le in Hlo.
      lia.
    + lia.
Qed.

Lemma firstn_succ_snoc : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.

Lemma firstn_succ_Znth : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  List.app (firstn (Z.to_nat i) l) [Znth i l 0].
Proof.
  intros l i H.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc with (d := 0) by (rewrite <- z_to_nat_Zlength; lia).
  reflexivity.
Qed.

Lemma sum_upper_upto_step_upper : forall i l,
  0 <= i ->
  i < Zlength l ->
  65 <= Znth i l 0 ->
  Znth i l 0 <= 90 ->
  sum_upper_upto (i + 1) l =
  sum_upper_upto i l + Znth i l 0.
Proof.
  intros i l Hi Hlt Hlo Hhi.
  unfold sum_upper_upto.
  rewrite firstn_succ_Znth by lia.
  rewrite sum_upper_list_z_app.
  simpl.
  unfold is_upper_z.
  replace (Z.leb 65 (Znth i l 0)) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb (Znth i l 0) 90) with true by (symmetry; apply Z.leb_le; lia).
  simpl. lia.
Qed.

Lemma sum_upper_upto_step_not_upper : forall i l,
  0 <= i ->
  i < Zlength l ->
  (Znth i l 0 < 65 \/ 90 < Znth i l 0) ->
  sum_upper_upto (i + 1) l =
  sum_upper_upto i l.
Proof.
  intros i l Hi Hlt Hnot.
  unfold sum_upper_upto.
  rewrite firstn_succ_Znth by lia.
  rewrite sum_upper_list_z_app.
  simpl.
  unfold is_upper_z.
  destruct Hnot as [Hlo | Hhi].
  - replace (Z.leb 65 (Znth i l 0)) with false by (symmetry; apply Z.leb_gt; lia).
    simpl. lia.
  - replace (Z.leb 65 (Znth i l 0)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.leb (Znth i l 0) 90) with false by (symmetry; apply Z.leb_gt; lia).
    simpl. lia.
Qed.

Lemma is_upper_z_correct : forall x,
  0 <= x < 256 ->
  is_upper_z x = is_uppercase (ascii_of_z x).
Proof.
  intros x Hrange.
  unfold is_upper_z, is_uppercase.
  rewrite nat_of_ascii_ascii_of_z by lia.
  destruct (Z.leb_spec 65 x);
  destruct (Z.leb_spec x 90);
  destruct (Nat.leb_spec 65 (Z.to_nat x));
  destruct (Nat.leb_spec (Z.to_nat x) 90);
  simpl; try reflexivity; lia.
Qed.

Lemma sum_upper_list_z_correct : forall l,
  ascii_range_z l ->
  Z.to_nat (sum_upper_list_z l) = sum_uppercase_ascii (string_of_list_z l).
Proof.
  induction l as [| x xs IH]; intros Hrange; simpl.
  - reflexivity.
  - assert (Hxrange : 0 <= x < 256).
    { pose proof (Zlength_nonneg xs) as Hxslen.
      pose proof (Hrange 0 ltac:(rewrite Zlength_cons; lia)) as Hxrange.
      change (Znth 0 (x :: xs) 0) with x in Hxrange.
      lia. }
    assert (Hxsrange : ascii_range_z xs).
    {
      unfold ascii_range_z in *.
      intros i Hi.
      specialize (Hrange (i + 1)).
      replace (Znth i xs 0) with (Znth (i + 1) (x :: xs) 0).
      - apply Hrange. rewrite Zlength_cons. lia.
      - unfold Znth.
        replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
        reflexivity.
    }
    rewrite <- IH by exact Hxsrange.
    rewrite <- is_upper_z_correct by exact Hxrange.
    rewrite nat_of_ascii_ascii_of_z by exact Hxrange.
    destruct (is_upper_z x) eqn:Hupper.
    + assert (0 <= x) by lia.
      rewrite Z2Nat.inj_add by (pose proof (sum_upper_list_z_nonneg xs); lia).
      reflexivity.
    + reflexivity.
Qed.

Lemma problem_66_spec_z_intro : forall s output,
  ascii_range_z s ->
  output = sum_upper_upto (Zlength s) s ->
  problem_66_spec_z s output.
Proof.
  intros s output Hrange Hout.
  unfold problem_66_spec_z, problem_66_spec, digitSum_impl.
  rewrite Hout.
  unfold sum_upper_upto.
  rewrite z_to_nat_Zlength.
  rewrite firstn_all.
  apply sum_upper_list_z_correct.
  exact Hrange.
Qed.

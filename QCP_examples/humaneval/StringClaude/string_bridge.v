Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition ascii_of_z (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z c) (string_of_list_z rest)
  end.

Fixpoint list_ascii_of_string_z (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: list_ascii_of_string_z rest
  end.

Definition char_list_string (l : list Z) (s : string) : Prop :=
  s = string_of_list_z l.

Definition bool_of_z (z : Z) : bool :=
  Z.eqb z 1.

Definition nat_of_z (z : Z) : nat :=
  Z.to_nat z.

Definition ascii_range_z (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 < 256.

Definition ascii_range_7bit_z (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 <= 127.

Lemma string_of_list_z_length : forall (l : list Z),
  String.length (string_of_list_z l) = List.length l.
Proof.
  induction l; simpl; auto.
Qed.

Lemma string_of_list_z_length_z : forall (l : list Z),
  Z.of_nat (String.length (string_of_list_z l)) = Zlength l.
Proof.
  intros l.
  rewrite string_of_list_z_length.
  symmetry.
  apply Zlength_correct.
Qed.

Lemma list_ascii_of_string_z_string_of_list_z : forall (l : list Z),
  list_ascii_of_string_z (string_of_list_z l) = map ascii_of_z l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma list_ascii_of_string_string_of_list_z : forall (l : list Z),
  list_ascii_of_string (string_of_list_z l) = map ascii_of_z l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma string_get_string_of_list_z : forall (l : list Z) i,
  (i < List.length l)%nat ->
  String.get i (string_of_list_z l) = Some (ascii_of_z (nth i l 0)).
Proof.
  induction l as [| c rest IH]; intros i Hi; simpl in *.
  - lia.
  - destruct i as [| i].
    + reflexivity.
    + apply IH. lia.
Qed.

Lemma string_get_string_of_list_z_z : forall (l : list Z) k,
  0 <= k < Zlength l ->
  String.get (Z.to_nat k) (string_of_list_z l) =
    Some (ascii_of_z (Znth k l 0)).
Proof.
  intros l k Hk.
  unfold Znth.
  apply string_get_string_of_list_z.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct.
  lia.
Qed.

Lemma z_to_nat_Zlength : forall (l : list Z),
  Z.to_nat (Zlength l) = List.length l.
Proof.
  intros l.
  rewrite Zlength_correct.
  lia.
Qed.

Lemma nat_of_z_Zlength : forall (l : list Z),
  nat_of_z (Zlength l) = String.length (string_of_list_z l).
Proof.
  intros l.
  unfold nat_of_z.
  rewrite z_to_nat_Zlength.
  symmetry.
  apply string_of_list_z_length.
Qed.

Lemma nat_of_ascii_ascii_of_z : forall z,
  0 <= z < 256 ->
  nat_of_ascii (ascii_of_z z) = Z.to_nat z.
Proof.
  intros z Hz.
  unfold ascii_of_z.
  rewrite nat_ascii_embedding by lia.
  reflexivity.
Qed.

Lemma ascii_of_z_eq_ascii_of_nat : forall z n,
  z = Z.of_nat n ->
  ascii_of_z z = ascii_of_nat n.
Proof.
  intros z n ->.
  unfold ascii_of_z.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

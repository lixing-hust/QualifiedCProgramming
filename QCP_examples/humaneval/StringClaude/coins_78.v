Load "../spec/78".

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

Definition is_prime_hex_z (x : Z) : bool :=
  Z.eqb x 50 || Z.eqb x 51 || Z.eqb x 53 ||
  Z.eqb x 55 || Z.eqb x 66 || Z.eqb x 68.

Fixpoint count_prime_hex_list_z (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if is_prime_hex_z x then 1 else 0) + count_prime_hex_list_z xs
  end.

Definition count_prime_hex_upto (i : Z) (l : list Z) : Z :=
  count_prime_hex_list_z (firstn (Z.to_nat i) l).

Definition problem_78_pre_z (s : list Z) : Prop :=
  problem_78_pre (string_of_list_z s).

Definition problem_78_spec_z (s : list Z) (output : Z) : Prop :=
  problem_78_spec (string_of_list_z s) (Z.to_nat output).

Lemma count_prime_hex_upto_0 : forall l,
  count_prime_hex_upto 0 l = 0.
Proof.
  intros l.
  unfold count_prime_hex_upto.
  reflexivity.
Qed.

Lemma count_prime_hex_list_z_app : forall l1 l2,
  count_prime_hex_list_z (l1 ++ l2) =
  count_prime_hex_list_z l1 + count_prime_hex_list_z l2.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma count_prime_hex_list_z_nonneg : forall l,
  0 <= count_prime_hex_list_z l.
Proof.
  induction l as [| x xs IH]; simpl.
  - lia.
  - destruct (is_prime_hex_z x); lia.
Qed.

Lemma firstn_succ_snoc_78 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.

Lemma firstn_succ_Znth_78 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  List.app (firstn (Z.to_nat i) l) [Znth i l 0].
Proof.
  intros l i H.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_78 with (d := 0) by (rewrite <- z_to_nat_Zlength; lia).
  reflexivity.
Qed.

Lemma is_prime_hex_z_true : forall x,
  x = 50 \/ x = 51 \/ x = 53 \/ x = 55 \/ x = 66 \/ x = 68 ->
  is_prime_hex_z x = true.
Proof.
  intros x Hx.
  unfold is_prime_hex_z.
  destruct Hx as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    repeat rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma is_prime_hex_z_false : forall x,
  x <> 50 -> x <> 51 -> x <> 53 -> x <> 55 -> x <> 66 -> x <> 68 ->
  is_prime_hex_z x = false.
Proof.
  intros x H50 H51 H53 H55 H66 H68.
  unfold is_prime_hex_z.
  repeat match goal with
  | |- context[Z.eqb ?a ?b] =>
      replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; lia)
  end.
  reflexivity.
Qed.

Lemma count_prime_hex_upto_step_hit : forall i l,
  0 <= i ->
  i < Zlength l ->
  (Znth i l 0 = 50 \/ Znth i l 0 = 51 \/ Znth i l 0 = 53 \/
   Znth i l 0 = 55 \/ Znth i l 0 = 66 \/ Znth i l 0 = 68) ->
  count_prime_hex_upto (i + 1) l =
  count_prime_hex_upto i l + 1.
Proof.
  intros i l Hi Hlt Hhit.
  unfold count_prime_hex_upto.
  rewrite firstn_succ_Znth_78 by lia.
  rewrite count_prime_hex_list_z_app.
  simpl.
  rewrite is_prime_hex_z_true by exact Hhit.
  simpl. lia.
Qed.

Lemma count_prime_hex_upto_step_miss : forall i l,
  0 <= i ->
  i < Zlength l ->
  Znth i l 0 <> 50 ->
  Znth i l 0 <> 51 ->
  Znth i l 0 <> 53 ->
  Znth i l 0 <> 55 ->
  Znth i l 0 <> 66 ->
  Znth i l 0 <> 68 ->
  count_prime_hex_upto (i + 1) l =
  count_prime_hex_upto i l.
Proof.
  intros i l Hi Hlt H50 H51 H53 H55 H66 H68.
  unfold count_prime_hex_upto.
  rewrite firstn_succ_Znth_78 by lia.
  rewrite count_prime_hex_list_z_app.
  simpl.
  rewrite is_prime_hex_z_false by auto.
  simpl. lia.
Qed.

Lemma is_prime_hex_z_correct : forall x,
  0 <= x < 256 ->
  is_prime_hex_z x = is_prime_hex_digit (ascii_of_z x).
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

Lemma count_prime_hex_list_z_correct : forall l,
  ascii_range_z l ->
  Z.to_nat (count_prime_hex_list_z l) = count_prime_hex (string_of_list_z l).
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
      - apply Hrange. rewrite Zlength_cons. pose proof (Zlength_nonneg xs); lia.
      - unfold Znth.
        replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
        reflexivity.
    }
    rewrite <- IH by exact Hxsrange.
    rewrite <- is_prime_hex_z_correct by exact Hxrange.
    destruct (is_prime_hex_z x) eqn:Hprime.
    + rewrite Z2Nat.inj_add by (pose proof (count_prime_hex_list_z_nonneg xs); lia).
      reflexivity.
    + reflexivity.
Qed.

Lemma problem_78_spec_z_intro : forall s output,
  ascii_range_z s ->
  output = count_prime_hex_upto (Zlength s) s ->
  problem_78_spec_z s output.
Proof.
  intros s output Hrange Hout.
  unfold problem_78_spec_z, problem_78_spec, hex_key_impl.
  rewrite Hout.
  unfold count_prime_hex_upto.
  rewrite z_to_nat_Zlength.
  rewrite firstn_all.
  apply count_prime_hex_list_z_correct.
  exact Hrange.
Qed.

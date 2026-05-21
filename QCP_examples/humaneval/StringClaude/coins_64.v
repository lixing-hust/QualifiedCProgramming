Load "../spec/64".

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

Definition is_regular_vowel_z (x : Z) : bool :=
  Z.eqb x 97 || Z.eqb x 101 || Z.eqb x 105 || Z.eqb x 111 || Z.eqb x 117 ||
  Z.eqb x 65 || Z.eqb x 69 || Z.eqb x 73 || Z.eqb x 79 || Z.eqb x 85.

Definition is_y_z (x : Z) : bool :=
  Z.eqb x 121 || Z.eqb x 89.

Fixpoint count_regular_vowels_list_z (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if is_regular_vowel_z x then 1 else 0) + count_regular_vowels_list_z xs
  end.

Definition count_regular_vowels_upto (i : Z) (l : list Z) : Z :=
  count_regular_vowels_list_z (firstn (Z.to_nat i) l).

Definition last_y_add (l : list Z) : Z :=
  let n := Zlength l in
  if Z.eqb n 0 then 0
  else if is_y_z (Znth (n - 1) l 0) then 1 else 0.

Definition problem_64_pre_z (s : list Z) : Prop :=
  problem_64_pre (string_of_list_z s).

Definition problem_64_spec_z (s : list Z) (output : Z) : Prop :=
  problem_64_spec (string_of_list_z s) (Z.to_nat output).

Lemma count_regular_vowels_upto_0 : forall l,
  count_regular_vowels_upto 0 l = 0.
Proof.
  intros l.
  unfold count_regular_vowels_upto.
  reflexivity.
Qed.

Lemma count_regular_vowels_list_z_app : forall l1 l2,
  count_regular_vowels_list_z (l1 ++ l2) =
  count_regular_vowels_list_z l1 + count_regular_vowels_list_z l2.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma count_regular_vowels_list_z_nonneg : forall l,
  0 <= count_regular_vowels_list_z l.
Proof.
  induction l as [| x xs IH]; simpl.
  - lia.
  - destruct (is_regular_vowel_z x); lia.
Qed.

Lemma firstn_succ_snoc_64 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.

Lemma firstn_succ_Znth_64 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  List.app (firstn (Z.to_nat i) l) [Znth i l 0].
Proof.
  intros l i H.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_64 with (d := 0) by (rewrite <- z_to_nat_Zlength; lia).
  reflexivity.
Qed.

Lemma is_regular_vowel_z_true : forall x,
  x = 97 \/ x = 101 \/ x = 105 \/ x = 111 \/ x = 117 \/
  x = 65 \/ x = 69 \/ x = 73 \/ x = 79 \/ x = 85 ->
  is_regular_vowel_z x = true.
Proof.
  intros x Hx.
  unfold is_regular_vowel_z.
  destruct Hx as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    repeat rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma is_regular_vowel_z_false : forall x,
  x <> 97 -> x <> 101 -> x <> 105 -> x <> 111 -> x <> 117 ->
  x <> 65 -> x <> 69 -> x <> 73 -> x <> 79 -> x <> 85 ->
  is_regular_vowel_z x = false.
Proof.
  intros x H97 H101 H105 H111 H117 H65 H69 H73 H79 H85.
  unfold is_regular_vowel_z.
  repeat match goal with
  | |- context[Z.eqb ?a ?b] =>
      replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; lia)
  end.
  reflexivity.
Qed.

Lemma count_regular_vowels_upto_step_hit : forall i l,
  0 <= i ->
  i < Zlength l ->
  (Znth i l 0 = 97 \/ Znth i l 0 = 101 \/ Znth i l 0 = 105 \/
   Znth i l 0 = 111 \/ Znth i l 0 = 117 \/
   Znth i l 0 = 65 \/ Znth i l 0 = 69 \/ Znth i l 0 = 73 \/
   Znth i l 0 = 79 \/ Znth i l 0 = 85) ->
  count_regular_vowels_upto (i + 1) l =
  count_regular_vowels_upto i l + 1.
Proof.
  intros i l Hi Hlt Hhit.
  unfold count_regular_vowels_upto.
  rewrite firstn_succ_Znth_64 by lia.
  rewrite count_regular_vowels_list_z_app.
  simpl.
  rewrite is_regular_vowel_z_true by exact Hhit.
  simpl. lia.
Qed.

Lemma count_regular_vowels_upto_step_miss : forall i l,
  0 <= i ->
  i < Zlength l ->
  Znth i l 0 <> 97 -> Znth i l 0 <> 101 -> Znth i l 0 <> 105 ->
  Znth i l 0 <> 111 -> Znth i l 0 <> 117 ->
  Znth i l 0 <> 65 -> Znth i l 0 <> 69 -> Znth i l 0 <> 73 ->
  Znth i l 0 <> 79 -> Znth i l 0 <> 85 ->
  count_regular_vowels_upto (i + 1) l =
  count_regular_vowels_upto i l.
Proof.
  intros i l Hi Hlt H97 H101 H105 H111 H117 H65 H69 H73 H79 H85.
  unfold count_regular_vowels_upto.
  rewrite firstn_succ_Znth_64 by lia.
  rewrite count_regular_vowels_list_z_app.
  simpl.
  rewrite is_regular_vowel_z_false by auto.
  simpl. lia.
Qed.

Lemma last_y_add_zero : forall l,
  Zlength l = 0 ->
  last_y_add l = 0.
Proof.
  intros l Hlen.
  unfold last_y_add.
  rewrite Hlen, Z.eqb_refl.
  reflexivity.
Qed.

Lemma last_y_add_hit : forall l n,
  Zlength l = n ->
  n > 0 ->
  (Znth (n - 1) l 0 = 121 \/ Znth (n - 1) l 0 = 89) ->
  last_y_add l = 1.
Proof.
  intros l n Hlen Hpos Hy.
  unfold last_y_add.
  rewrite Hlen.
  replace (Z.eqb n 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold is_y_z.
  destruct Hy as [Hy | Hy]; rewrite Hy.
  - rewrite Z.eqb_refl. reflexivity.
  - replace (Z.eqb 89 121) with false by reflexivity.
    rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma last_y_add_miss : forall l n,
  Zlength l = n ->
  n > 0 ->
  Znth (n - 1) l 0 <> 121 ->
  Znth (n - 1) l 0 <> 89 ->
  last_y_add l = 0.
Proof.
  intros l n Hlen Hpos H121 H89.
  unfold last_y_add.
  rewrite Hlen.
  replace (Z.eqb n 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold is_y_z.
  replace (Z.eqb (Znth (n - 1) l 0) 121) with false by
    (symmetry; apply Z.eqb_neq; lia).
  replace (Z.eqb (Znth (n - 1) l 0) 89) with false by
    (symmetry; apply Z.eqb_neq; lia).
  reflexivity.
Qed.

Lemma is_regular_vowel_z_correct : forall x,
  0 <= x < 256 ->
  is_regular_vowel_z x = is_vowel_char (ascii_of_z x).
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

Lemma is_y_z_correct : forall x,
  0 <= x < 256 ->
  is_y_z x = is_y (ascii_of_z x).
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

Lemma regular_vowel_not_y : forall c,
  is_regular_vowel_z c = true ->
  is_y_z c = true ->
  False.
Proof.
  intros c Hreg Hy.
  unfold is_regular_vowel_z, is_y_z in *.
  repeat match goal with
  | H : context[Z.eqb ?x ?y] |- _ => destruct (Z.eqb_spec x y); simpl in H
  end; try discriminate; lia.
Qed.

Lemma last_y_add_nonneg : forall l,
  0 <= last_y_add l.
Proof.
  intros l.
  unfold last_y_add.
  destruct (Z.eqb (Zlength l) 0);
  destruct (is_y_z (Znth (Zlength l - 1) l 0)); lia.
Qed.

Lemma last_y_add_cons_nonempty : forall c rest,
  rest <> [] ->
  last_y_add (c :: rest) = last_y_add rest.
Proof.
  intros c rest Hnonempty.
  destruct rest as [| r rs]; [contradiction |].
  pose proof (Zlength_nonneg rs) as Hrslen.
  unfold last_y_add.
  rewrite !Zlength_cons.
  replace (Z.eqb (Z.succ (Z.succ (Zlength rs))) 0) with false by
    (symmetry; apply Z.eqb_neq; lia).
  replace (Z.eqb (Z.succ (Zlength rs)) 0) with false by
    (symmetry; apply Z.eqb_neq; lia).
  replace (Znth (Z.succ (Z.succ (Zlength rs)) - 1) (c :: r :: rs) 0)
    with (Znth (Z.succ (Zlength rs) - 1) (r :: rs) 0).
  - reflexivity.
  - unfold Znth.
    replace (Z.to_nat (Z.succ (Z.succ (Zlength rs)) - 1))
      with (S (Z.to_nat (Z.succ (Zlength rs) - 1))) by
      (pose proof (Zlength_nonneg rs); lia).
    reflexivity.
Qed.

Lemma last_y_add_single : forall c,
  last_y_add [c] = if is_y_z c then 1 else 0.
Proof.
  intros c.
  unfold last_y_add.
  rewrite Zlength_cons, Zlength_nil.
  replace (Z.eqb (1 + 0) 0) with false by reflexivity.
  change (Znth (1 + 0 - 1) [c] 0) with c.
  reflexivity.
Qed.

Lemma z_to_nat_one_plus : forall z,
  0 <= z ->
  Z.to_nat (1 + z) = S (Z.to_nat z).
Proof.
  intros z Hz.
  replace (1 + z) with (Z.succ z) by lia.
  apply Z2Nat.inj_succ.
  exact Hz.
Qed.

Lemma ascii_range_z_tail : forall c rest,
  ascii_range_z (c :: rest) ->
  ascii_range_z rest.
Proof.
  unfold ascii_range_z.
  intros c rest Hrange i Hi.
  specialize (Hrange (i + 1)).
  replace (Znth i rest 0) with (Znth (i + 1) (c :: rest) 0).
  - apply Hrange. rewrite Zlength_cons. pose proof (Zlength_nonneg rest); lia.
  - unfold Znth.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    reflexivity.
Qed.

Lemma ascii_range_z_head : forall c rest,
  ascii_range_z (c :: rest) ->
  0 <= c < 256.
Proof.
  intros c rest Hrange.
  pose proof (Zlength_nonneg rest) as Hlen.
  pose proof (Hrange 0 ltac:(rewrite Zlength_cons; lia)) as Hc.
  change (Znth 0 (c :: rest) 0) with c in Hc.
  lia.
Qed.

Lemma vowels_count_model_correct : forall s,
  ascii_range_z s ->
  Z.to_nat (count_regular_vowels_list_z s + last_y_add s) =
  vowels_count_func (string_of_list_z s).
Proof.
  induction s as [| c rest IH]; intros Hrange.
  - reflexivity.
  - pose proof (ascii_range_z_head c rest Hrange) as Hcrange.
    pose proof (ascii_range_z_tail c rest Hrange) as Hrestrange.
    cbn [string_of_list_z vowels_count_func].
    rewrite <- is_regular_vowel_z_correct by exact Hcrange.
    rewrite <- is_y_z_correct by exact Hcrange.
    change (count_regular_vowels_list_z (c :: rest))
      with ((if is_regular_vowel_z c then 1 else 0) + count_regular_vowels_list_z rest).
    destruct rest as [| r rs].
    + rewrite last_y_add_single.
      simpl.
      destruct (is_regular_vowel_z c) eqn:Hreg;
      destruct (is_y_z c) eqn:Hy; simpl; try reflexivity.
      exfalso. eapply regular_vowel_not_y; eauto.
    + rewrite last_y_add_cons_nonempty by discriminate.
      destruct (is_regular_vowel_z c) eqn:Hreg.
      * replace (1 + count_regular_vowels_list_z (r :: rs) + last_y_add (r :: rs))
          with (1 + (count_regular_vowels_list_z (r :: rs) + last_y_add (r :: rs))) by lia.
        rewrite z_to_nat_one_plus by
          (pose proof (count_regular_vowels_list_z_nonneg (r :: rs));
           pose proof (last_y_add_nonneg (r :: rs)); lia).
        rewrite IH by exact Hrestrange.
        reflexivity.
      * match goal with
        | |- context[Z.to_nat ?lhs] =>
            replace lhs with (count_regular_vowels_list_z (r :: rs) + last_y_add (r :: rs))
              by reflexivity
        end.
        rewrite IH by exact Hrestrange.
        replace ((string_of_list_z (r :: rs) =? "")%string) with false by reflexivity.
        destruct (is_y_z c); reflexivity.
Qed.

Lemma problem_64_spec_z_intro : forall s output,
  ascii_range_z s ->
  output = count_regular_vowels_upto (Zlength s) s + last_y_add s ->
  problem_64_spec_z s output.
Proof.
  intros s output Hrange Hout.
  unfold problem_64_spec_z, problem_64_spec, vowels_count_impl.
  rewrite Hout.
  unfold count_regular_vowels_upto.
  rewrite z_to_nat_Zlength.
  rewrite firstn_all.
  apply vowels_count_model_correct.
  exact Hrange.
Qed.

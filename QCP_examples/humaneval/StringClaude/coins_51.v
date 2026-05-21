Load "../spec/51".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope Z_scope.

Definition problem_51_pre_z (s : list Z) : Prop :=
  problem_51_pre (string_of_list_z s).

Definition char_range_z (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition is_vowel_z (c : Z) : bool :=
  orb (Z.eqb c 65)
  (orb (Z.eqb c 69)
  (orb (Z.eqb c 73)
  (orb (Z.eqb c 79)
  (orb (Z.eqb c 85)
  (orb (Z.eqb c 97)
  (orb (Z.eqb c 101)
  (orb (Z.eqb c 105)
  (orb (Z.eqb c 111) (Z.eqb c 117))))))))).

Fixpoint remove_vowels_list_z (s : list Z) : list Z :=
  match s with
  | [] => []
  | c :: rest =>
      if is_vowel_z c
      then remove_vowels_list_z rest
      else c :: remove_vowels_list_z rest
  end.

Definition remove_vowels_prefix_z (i : Z) (s : list Z) : list Z :=
  remove_vowels_list_z (firstn (Z.to_nat i) s).

Definition problem_51_spec_z (input output : list Z) : Prop :=
  problem_51_spec (string_of_list_z input) (string_of_list_z output).

Lemma remove_vowels_prefix_0 : forall s,
  remove_vowels_prefix_z 0 s = [].
Proof.
  intros s.
  unfold remove_vowels_prefix_z.
  reflexivity.
Qed.

Lemma remove_vowels_list_z_app : forall l1 l2,
  remove_vowels_list_z (l1 ++ l2) =
  remove_vowels_list_z l1 ++ remove_vowels_list_z l2.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - reflexivity.
  - destruct (is_vowel_z x); simpl; rewrite IH; reflexivity.
Qed.

Lemma firstn_succ_snoc_51 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.

Lemma firstn_succ_Znth_51 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  List.app (firstn (Z.to_nat i) l) [Znth i l 0].
Proof.
  intros l i H.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_51 with (d := 0) by (rewrite <- z_to_nat_Zlength; lia).
  reflexivity.
Qed.

Lemma remove_vowels_prefix_step : forall i s,
  0 <= i ->
  i < Zlength s ->
  remove_vowels_prefix_z (i + 1) s =
    let prev := remove_vowels_prefix_z i s in
    let c := Znth i s 0 in
    if is_vowel_z c then prev else prev ++ [c].
Proof.
  intros i s Hi Hlt.
  unfold remove_vowels_prefix_z.
  rewrite firstn_succ_Znth_51 by lia.
  rewrite remove_vowels_list_z_app.
  simpl.
  destruct (is_vowel_z (Znth i s 0)); simpl; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma remove_vowels_list_z_length_bound : forall s,
  Zlength (remove_vowels_list_z s) <= Zlength s.
Proof.
  induction s as [| x xs IH]; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite !Zlength_cons.
    destruct (is_vowel_z x); simpl; try rewrite Zlength_cons; lia.
Qed.

Lemma remove_vowels_prefix_length_bound : forall i s,
  0 <= i ->
  Zlength (remove_vowels_prefix_z i s) <= i.
Proof.
  intros i s Hi.
  unfold remove_vowels_prefix_z.
  eapply Z.le_trans.
  - apply remove_vowels_list_z_length_bound.
  - rewrite Zlength_correct, length_firstn.
    pose proof (Nat.le_min_l (Z.to_nat i) (Datatypes.length s)) as Hmin.
    apply Nat2Z.inj_le in Hmin.
    rewrite Z2Nat.id in Hmin by lia.
    exact Hmin.
Qed.

Lemma is_vowel_z_correct : forall c,
  0 <= c <= 127 ->
  is_vowel_z c = is_vowel (ascii_of_z c).
Proof.
  intros c Hrange.
  remember (ascii_of_z c) as a eqn:Ha.
  pose proof (nat_of_ascii_ascii_of_z c ltac:(lia)) as Hnat.
  rewrite <- Ha in Hnat.
  assert (Hc : c = Z.of_nat (nat_of_ascii a)).
  {
    rewrite <- (Z2Nat.id c) by lia.
    rewrite <- Hnat.
    reflexivity.
  }
  subst c.
  destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7; vm_compute; reflexivity.
Qed.

Lemma remove_vowels_list_z_correct : forall s,
  char_range_z s ->
  string_of_list_z (remove_vowels_list_z s) =
  filter_string (fun c => negb (is_vowel c)) (string_of_list_z s).
Proof.
  induction s as [| c rest IH]; intros Hrange; simpl.
  - reflexivity.
  - assert (Hcrange : 0 <= c <= 127).
    { pose proof (Zlength_nonneg rest) as Hlen.
      pose proof (Hrange 0 ltac:(rewrite Zlength_cons; lia)) as Hc.
      change (Znth 0 (c :: rest) 0) with c in Hc.
      lia. }
    assert (Hrestrange : char_range_z rest).
    {
      unfold char_range_z in *.
      intros i Hi.
      specialize (Hrange (i + 1)).
      replace (Znth i rest 0) with (Znth (i + 1) (c :: rest) 0).
      - apply Hrange. rewrite Zlength_cons. pose proof (Zlength_nonneg rest); lia.
      - unfold Znth.
        replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
        reflexivity.
    }
    rewrite <- is_vowel_z_correct by exact Hcrange.
    destruct (is_vowel_z c); simpl.
    + apply IH. exact Hrestrange.
    + rewrite IH by exact Hrestrange. reflexivity.
Qed.

Lemma char_range_z_firstn_all : forall s,
  char_range_z s ->
  char_range_z (firstn (Z.to_nat (Zlength s)) s).
Proof.
  intros s Hrange.
  rewrite z_to_nat_Zlength.
  rewrite firstn_all.
  exact Hrange.
Qed.

Lemma problem_51_spec_z_intro : forall input output,
  char_range_z input ->
  output = remove_vowels_prefix_z (Zlength input) input ->
  problem_51_spec_z input output.
Proof.
  intros input output Hrange Hout.
  unfold problem_51_spec_z, problem_51_spec.
  rewrite Hout.
  unfold remove_vowels_prefix_z.
  rewrite z_to_nat_Zlength.
  rewrite firstn_all.
  apply remove_vowels_list_z_correct.
  exact Hrange.
Qed.

Load "../spec/161".

Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.BinNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Import string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition ascii_range_z (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition is_lower_zb (c : Z) : bool :=
  (Z.leb 97 c) && (Z.leb c 122).

Definition is_upper_zb (c : Z) : bool :=
  (Z.leb 65 c) && (Z.leb c 90).

Definition is_letter_zb (c : Z) : bool :=
  is_lower_zb c || is_upper_zb c.

Definition flip_char_z (c : Z) : Z :=
  if is_lower_zb c then c - 32
  else if is_upper_zb c then c + 32
  else c.

Fixpoint contains_letter_list_z (l : list Z) : bool :=
  match l with
  | [] => false
  | c :: rest => is_letter_zb c || contains_letter_list_z rest
  end.

Lemma contains_letter_list_z_app : forall a b,
  contains_letter_list_z (a ++ b) =
  contains_letter_list_z a || contains_letter_list_z b.
Proof.
  induction a as [| x xs IH]; intros b; simpl.
  - reflexivity.
  - rewrite IH. destruct (is_letter_zb x), (contains_letter_list_z xs); reflexivity.
Qed.

Definition contains_letter_prefix_z (i : Z) (l : list Z) : Z :=
  if contains_letter_list_z (firstn (Z.to_nat i) l) then 1 else 0.

Definition contains_letter_z (l : list Z) : Z :=
  if contains_letter_list_z l then 1 else 0.

Lemma contains_letter_prefix_z_bool : forall i l,
  contains_letter_prefix_z i l = 0 \/ contains_letter_prefix_z i l = 1.
Proof.
  intros i l.
  unfold contains_letter_prefix_z.
  destruct (contains_letter_list_z (firstn (Z.to_nat i) l)); auto.
Qed.

Lemma contains_letter_z_bool : forall l,
  contains_letter_z l = 0 \/ contains_letter_z l = 1.
Proof.
  intros l.
  unfold contains_letter_z.
  destruct (contains_letter_list_z l); auto.
Qed.

Definition problem_161_pre_z (s : list Z) : Prop :=
  problem_161_pre (string_of_list_z s).

Definition problem_161_spec_z (input output : list Z) : Prop :=
  problem_161_spec (string_of_list_z input) (string_of_list_z output).

Lemma flip_char_range_z : forall c,
  0 <= c <= 127 ->
  0 <= flip_char_z c <= 127.
Proof.
  unfold flip_char_z, is_lower_zb, is_upper_zb.
  intros c Hrange.
  repeat match goal with
  | |- context[Z.leb ?x ?y] =>
      destruct (Z.leb_spec x y); simpl
  end; lia.
Qed.

Lemma contains_letter_prefix_z_0 : forall l,
  contains_letter_prefix_z 0 l = 0.
Proof.
  reflexivity.
Qed.

Lemma firstn_succ_snoc_161 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.

Lemma firstn_succ_Znth_161 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  List.app (firstn (Z.to_nat i) l) [Znth i l 0].
Proof.
  intros l i H.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_161 with (d := 0) by (rewrite <- z_to_nat_Zlength; lia).
  reflexivity.
Qed.

Lemma contains_letter_prefix_z_step : forall i l,
  0 <= i < Zlength l ->
  contains_letter_prefix_z (i + 1) l =
    if is_letter_zb (Znth i l 0)
    then 1
    else contains_letter_prefix_z i l.
Proof.
  intros i l Hi.
  unfold contains_letter_prefix_z.
  rewrite firstn_succ_Znth_161 by lia.
  rewrite contains_letter_list_z_app.
  simpl.
  destruct (contains_letter_list_z (firstn (Z.to_nat i) l));
    destruct (is_letter_zb (Znth i l 0)); reflexivity.
Qed.

Lemma contains_letter_prefix_z_full : forall l,
  contains_letter_prefix_z (Zlength l) l = contains_letter_z l.
Proof.
  intros l.
  unfold contains_letter_prefix_z, contains_letter_z.
  rewrite firstn_all2; [reflexivity |].
  rewrite z_to_nat_Zlength.
  lia.
Qed.

Lemma is_lower_alpha_ascii_of_z : forall c,
  0 <= c <= 127 ->
  is_lower_alpha (ascii_of_z c) = is_lower_zb c.
Proof.
  intros c Hc.
  unfold is_lower_alpha, is_lower_zb, ascii_of_z.
  unfold Ascii.leb, Ascii.compare.
  repeat rewrite <- N.leb_compare.
  change (N_of_ascii "a"%char) with 97%N.
  change (N_of_ascii "z"%char) with 122%N.
  assert (HN: N_of_ascii (ascii_of_nat (Z.to_nat c)) = N.of_nat (Z.to_nat c)).
  {
    apply Nnat.N2Nat.inj.
    rewrite Nnat.Nat2N.id.
    change (N.to_nat (N_of_ascii (ascii_of_nat (Z.to_nat c))))
      with (nat_of_ascii (ascii_of_nat (Z.to_nat c))).
    rewrite nat_ascii_embedding by lia.
    reflexivity.
  }
  rewrite HN.
  destruct (Z.leb_spec 97 c); destruct (Z.leb_spec c 122); simpl;
    repeat match goal with
    | |- context[(?a <=? ?b)%N] => destruct (N.leb_spec0 a b); simpl
    end; try reflexivity; lia.
Qed.

Lemma is_upper_alpha_ascii_of_z : forall c,
  0 <= c <= 127 ->
  is_upper_alpha (ascii_of_z c) = is_upper_zb c.
Proof.
  intros c Hc.
  unfold is_upper_alpha, is_upper_zb, ascii_of_z.
  unfold Ascii.leb, Ascii.compare.
  repeat rewrite <- N.leb_compare.
  change (N_of_ascii "A"%char) with 65%N.
  change (N_of_ascii "Z"%char) with 90%N.
  assert (HN: N_of_ascii (ascii_of_nat (Z.to_nat c)) = N.of_nat (Z.to_nat c)).
  {
    apply Nnat.N2Nat.inj.
    rewrite Nnat.Nat2N.id.
    change (N.to_nat (N_of_ascii (ascii_of_nat (Z.to_nat c))))
      with (nat_of_ascii (ascii_of_nat (Z.to_nat c))).
    rewrite nat_ascii_embedding by lia.
    reflexivity.
  }
  rewrite HN.
  destruct (Z.leb_spec 65 c); destruct (Z.leb_spec c 90); simpl;
    repeat match goal with
    | |- context[(?a <=? ?b)%N] => destruct (N.leb_spec0 a b); simpl
    end; try reflexivity; lia.
Qed.

Lemma is_letter_dec_ascii_of_z : forall c,
  0 <= c <= 127 ->
  is_letter_dec (ascii_of_z c) = is_letter_zb c.
Proof.
  intros c Hc.
  unfold is_letter_dec, is_letter_zb.
  rewrite is_lower_alpha_ascii_of_z by lia.
  rewrite is_upper_alpha_ascii_of_z by lia.
  reflexivity.
Qed.

Lemma change_case_ascii_of_z : forall c,
  0 <= c <= 127 ->
  change_case (ascii_of_z c) = ascii_of_z (flip_char_z c).
Proof.
  intros c Hc.
  unfold change_case, my_uppercase, my_lowercase, flip_char_z.
  rewrite is_lower_alpha_ascii_of_z by lia.
  rewrite is_upper_alpha_ascii_of_z by lia.
  destruct (is_lower_zb c) eqn:Hlow; simpl.
  - unfold ascii_of_z.
    rewrite nat_ascii_embedding by lia.
    unfold is_lower_zb in Hlow.
    apply andb_true_iff in Hlow as [H1 H2].
    apply Z.leb_le in H1; apply Z.leb_le in H2.
    replace (Z.to_nat (c - 32)) with (Z.to_nat c - 32)%nat by lia.
    reflexivity.
  - destruct (is_upper_zb c) eqn:Hup; simpl.
    + unfold ascii_of_z.
      rewrite nat_ascii_embedding by lia.
      unfold is_upper_zb in Hup.
      apply andb_true_iff in Hup as [H1 H2].
      apply Z.leb_le in H1; apply Z.leb_le in H2.
      replace (Z.to_nat (c + 32)) with (Z.to_nat c + 32)%nat by lia.
      reflexivity.
    + reflexivity.
Qed.

Lemma contains_letter_list_z_correct : forall l,
  (forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 <= 127) ->
  contains_letter_dec (map ascii_of_z l) = contains_letter_list_z l.
Proof.
  induction l as [| c rest IH]; intros Hrange; simpl.
  - reflexivity.
  - rewrite is_letter_dec_ascii_of_z.
    + rewrite IH; [reflexivity |].
      intros i Hi.
      specialize (Hrange (i + 1)).
      simpl in Hrange.
      rewrite Znth_cons in Hrange by lia.
      replace (i + 1 - 1) with i in Hrange by lia.
      apply Hrange.
      rewrite Zlength_cons; lia.
    + specialize (Hrange 0).
      simpl in Hrange.
      rewrite Znth0_cons in Hrange.
      apply Hrange.
      split; [lia | rewrite Zlength_correct; simpl; lia].
Qed.

Lemma map_change_case_ascii_of_z : forall l,
  (forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 <= 127) ->
  map change_case (map ascii_of_z l) = map ascii_of_z (map flip_char_z l).
Proof.
  induction l as [| c rest IH]; intros Hrange; simpl.
  - reflexivity.
  - rewrite change_case_ascii_of_z.
    + rewrite IH; [reflexivity |].
      intros i Hi.
      specialize (Hrange (i + 1)).
      simpl in Hrange.
      rewrite Znth_cons in Hrange by lia.
      replace (i + 1 - 1) with i in Hrange by lia.
      apply Hrange.
      rewrite Zlength_cons; lia.
    + specialize (Hrange 0).
      simpl in Hrange.
      rewrite Znth0_cons in Hrange.
      apply Hrange.
      split; [lia | rewrite Zlength_correct; simpl; lia].
Qed.

Lemma string_of_list_z_map_ascii : forall l,
  string_of_list_z l = string_of_list_ascii (map ascii_of_z l).
Proof.
  induction l; simpl; congruence.
Qed.

Lemma string_of_list_z_map_flip : forall l,
  ascii_range_z l ->
  string_of_list_z (map flip_char_z l) =
  string_of_list_ascii (map change_case (map ascii_of_z l)).
Proof.
  intros l Hrange.
  rewrite string_of_list_z_map_ascii.
  f_equal.
  symmetry.
  apply map_change_case_ascii_of_z; exact Hrange.
Qed.

Lemma map_flip_length : forall l,
  Zlength (map flip_char_z l) = Zlength l.
Proof.
  intros l.
  rewrite !Zlength_correct, map_length.
  reflexivity.
Qed.

Lemma list_eq_Znth_161 : forall (a b : list Z),
  Zlength a = Zlength b ->
  (forall k, 0 <= k < Zlength a -> Znth k a 0 = Znth k b 0) ->
  a = b.
Proof.
  induction a as [| x xs IH]; destruct b as [| y ys]; intros Hlen Hnth; simpl in *.
  - reflexivity.
  - repeat rewrite Zlength_correct in Hlen. simpl in Hlen. lia.
  - repeat rewrite Zlength_correct in Hlen. simpl in Hlen. lia.
  - assert (Hx : x = y).
    {
      specialize (Hnth 0).
      repeat rewrite Znth0_cons in Hnth.
      apply Hnth.
      rewrite Zlength_correct. simpl. lia.
    }
    subst y.
    f_equal.
    apply IH.
    + repeat rewrite Zlength_correct in Hlen. simpl in Hlen.
      rewrite !Zlength_correct. lia.
    + intros k Hk.
      specialize (Hnth (k + 1)).
      repeat rewrite Znth_cons in Hnth by lia.
      replace (k + 1 - 1) with k in Hnth by lia.
      apply Hnth.
      rewrite Zlength_correct in *.
      simpl.
      lia.
Qed.

Lemma Znth_map_flip_161 : forall l k,
  0 <= k < Zlength l ->
  Znth k (map flip_char_z l) 0 = flip_char_z (Znth k l 0).
Proof.
  induction l as [| x xs IH]; intros k Hk.
  - rewrite Zlength_correct in Hk. simpl in Hk. lia.
  - destruct (Z.eq_dec k 0) as [-> | Hnz].
    + simpl. repeat rewrite Znth0_cons. reflexivity.
    + simpl.
      rewrite Znth_cons by lia.
      rewrite Znth_cons by lia.
      apply IH.
      rewrite Zlength_cons in Hk.
      lia.
Qed.

Lemma Zlength_rev_161 : forall (l : list Z),
  Zlength (rev l) = Zlength l.
Proof.
  intros l.
  rewrite !Zlength_correct, rev_length.
  reflexivity.
Qed.

Lemma Znth_rev_161 : forall l k,
  0 <= k < Zlength l ->
  Znth k (rev l) 0 = Znth (Zlength l - 1 - k) l 0.
Proof.
  intros l k Hk.
  unfold Znth.
  rewrite rev_nth by (rewrite <- z_to_nat_Zlength; lia).
  f_equal.
  rewrite Zlength_correct in Hk |- *.
  lia.
Qed.

Lemma output_is_map_flip_161 : forall input output,
  Zlength output = Zlength input ->
  (forall k, 0 <= k < Zlength input ->
    Znth k output 0 = flip_char_z (Znth k input 0)) ->
  output = map flip_char_z input.
Proof.
  intros input output Hlen Hpoint.
  apply list_eq_Znth_161.
  - rewrite map_flip_length. exact Hlen.
  - intros k Hk.
    rewrite Hpoint by lia.
    rewrite Znth_map_flip_161 by lia.
    reflexivity.
Qed.

Lemma output_is_rev_161 : forall input output,
  Zlength output = Zlength input ->
  (forall k, 0 <= k < Zlength input ->
    Znth k output 0 = Znth (Zlength input - 1 - k) input 0) ->
  output = rev input.
Proof.
  intros input output Hlen Hpoint.
  apply list_eq_Znth_161.
  - rewrite Zlength_rev_161. exact Hlen.
  - intros k Hk.
    rewrite Hpoint by lia.
    rewrite Znth_rev_161 by lia.
    reflexivity.
Qed.

Lemma problem_161_spec_z_intro_flip : forall input output,
  ascii_range_z input ->
  contains_letter_z input = 1 ->
  output = map flip_char_z input ->
  problem_161_spec_z input output.
Proof.
  intros input output Hrange Hhas ->.
  unfold problem_161_spec_z, problem_161_spec, solve_impl.
  rewrite list_ascii_of_string_string_of_list_z.
  unfold contains_letter_z in Hhas.
  rewrite contains_letter_list_z_correct by exact Hrange.
  destruct (contains_letter_list_z input); [| discriminate].
  rewrite string_of_list_z_map_flip by exact Hrange.
  reflexivity.
Qed.

Lemma problem_161_spec_z_intro_rev : forall input output,
  ascii_range_z input ->
  contains_letter_z input = 0 ->
  output = rev input ->
  problem_161_spec_z input output.
Proof.
  intros input output Hrange Hhas ->.
  unfold problem_161_spec_z, problem_161_spec, solve_impl.
  rewrite list_ascii_of_string_string_of_list_z.
  unfold contains_letter_z in Hhas.
  rewrite contains_letter_list_z_correct by exact Hrange.
  destruct (contains_letter_list_z input); [discriminate |].
  rewrite string_of_list_z_map_ascii.
  rewrite map_rev.
  reflexivity.
Qed.

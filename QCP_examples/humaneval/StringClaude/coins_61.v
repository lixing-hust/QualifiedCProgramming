Load "../spec/61".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition problem_61_pre_z (brackets : list Z) : Prop :=
  problem_61_pre (string_of_list_z brackets).

Definition paren_delta (x : Z) : Z :=
  if Z.eqb x 40 then 1 else if Z.eqb x 41 then -1 else 0.

Fixpoint paren_level_upto_nat (n : nat) (l : list Z) : Z :=
  match n with
  | O => 0
  | S n' => paren_level_upto_nat n' l + paren_delta (Znth (Z.of_nat n') l 0)
  end.

Definition paren_level_upto (i : Z) (l : list Z) : Z :=
  paren_level_upto_nat (Z.to_nat i) l.

Definition paren_nonnegative_prefix (i : Z) (l : list Z) : Prop :=
  forall k, 0 <= k < i -> 0 <= paren_level_upto (k + 1) l.

Definition paren_balanced_z (l : list Z) : Prop :=
  paren_level_upto (Zlength l) l = 0 /\
  paren_nonnegative_prefix (Zlength l) l.

Definition problem_61_spec_z (brackets : list Z) (output : Z) : Prop :=
  problem_61_spec (string_of_list_z brackets) (bool_of_z output).

Lemma Znth_In_range_61 : forall (l : list Z) k d,
  0 <= k < Zlength l ->
  In (Znth k l d) l.
Proof.
  intros l k d Hk.
  unfold Znth.
  apply nth_In.
  rewrite <- z_to_nat_Zlength.
  lia.
Qed.

Lemma paren_level_upto_0 : forall l,
  paren_level_upto 0 l = 0.
Proof.
  intros l.
  unfold paren_level_upto.
  reflexivity.
Qed.

Lemma paren_nonnegative_prefix_0 : forall l,
  paren_nonnegative_prefix 0 l.
Proof.
  unfold paren_nonnegative_prefix.
  intros l k Hk.
  lia.
Qed.

Lemma paren_level_upto_step_open : forall i l,
  0 <= i ->
  Znth i l 0 = 40 ->
  paren_level_upto (i + 1) l = paren_level_upto i l + 1.
Proof.
  intros i l Hi Hx.
  unfold paren_level_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  unfold paren_delta.
  rewrite Hx.
  rewrite Z.eqb_refl.
  reflexivity.
Qed.

Lemma paren_level_upto_step_close : forall i l,
  0 <= i ->
  Znth i l 0 = 41 ->
  paren_level_upto (i + 1) l = paren_level_upto i l - 1.
Proof.
  intros i l Hi Hx.
  unfold paren_level_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  unfold paren_delta.
  rewrite Hx.
  replace (Z.eqb 41 40) with false by reflexivity.
  replace (Z.eqb 41 41) with true by reflexivity.
  lia.
Qed.

Lemma paren_nonnegative_prefix_step : forall i l level,
  paren_nonnegative_prefix i l ->
  paren_level_upto (i + 1) l = level ->
  0 <= level ->
  paren_nonnegative_prefix (i + 1) l.
Proof.
  unfold paren_nonnegative_prefix.
  intros i l level Hprefix Hlevel Hnonneg k Hk.
  destruct (Z_lt_ge_dec k i).
  - apply Hprefix. lia.
  - assert (k = i) by lia.
    subst k.
    rewrite Hlevel.
    lia.
Qed.

Fixpoint check_paren_aux_z (l : list Z) (depth : Z) : bool :=
  match l with
  | [] => Z.eqb depth 0
  | c :: rest =>
      let depth' := depth + paren_delta c in
      if Z.ltb depth' 0 then false else check_paren_aux_z rest depth'
  end.

Lemma paren_level_upto_nat_cons : forall n c rest,
  paren_level_upto_nat (S n) (c :: rest) =
  paren_delta c + paren_level_upto_nat n rest.
Proof.
  induction n as [| n IH]; intros c rest.
  - simpl. rewrite Z.add_0_r. reflexivity.
  - change (paren_level_upto_nat (S n) (c :: rest) +
            paren_delta (Znth (Z.of_nat (S n)) (c :: rest) 0) =
            paren_delta c + paren_level_upto_nat (S n) rest).
    rewrite IH.
    rewrite Znth_cons by lia.
    replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
    rewrite <- Z.add_assoc.
    reflexivity.
Qed.

Lemma paren_level_upto_cons_succ : forall c rest k,
  0 <= k ->
  paren_level_upto (k + 1) (c :: rest) =
  paren_delta c + paren_level_upto k rest.
Proof.
  intros c rest k Hk.
  unfold paren_level_upto.
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  rewrite paren_level_upto_nat_cons.
  reflexivity.
Qed.

Lemma paren_level_upto_Zlength_cons : forall c rest,
  paren_level_upto (Zlength (c :: rest)) (c :: rest) =
  paren_delta c + paren_level_upto (Zlength rest) rest.
Proof.
  intros c rest.
  rewrite Zlength_cons.
  replace (Z.succ (Zlength rest)) with (Zlength rest + 1) by lia.
  rewrite paren_level_upto_cons_succ by (pose proof (Zlength_nonneg rest); lia).
  replace (Zlength rest + 1 - 1) with (Zlength rest) by lia.
  reflexivity.
Qed.

Lemma check_paren_aux_z_true : forall l depth,
  0 <= depth ->
  (forall k, 0 <= k < Zlength l ->
    0 <= depth + paren_level_upto (k + 1) l) ->
  depth + paren_level_upto (Zlength l) l = 0 ->
  check_paren_aux_z l depth = true.
Proof.
  induction l as [| c rest IH]; intros depth Hdepth Hprefix Hfinal.
  - rewrite Zlength_nil in Hfinal.
    rewrite paren_level_upto_0 in Hfinal.
    replace depth with 0 by lia.
    reflexivity.
  - simpl.
    pose proof (Hprefix 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg rest); lia))
      as Hfirst.
    rewrite paren_level_upto_cons_succ in Hfirst by lia.
    replace (0 + 1 - 1) with 0 in Hfirst by lia.
    rewrite paren_level_upto_0 in Hfirst.
    destruct (Z.ltb_spec (depth + paren_delta c) 0); try lia.
    apply IH.
    + lia.
    + intros k Hk.
      specialize (Hprefix (k + 1)).
      rewrite paren_level_upto_cons_succ in Hprefix by lia.
      replace (k + 1 + 1 - 1) with (k + 1) in Hprefix by lia.
      specialize (Hprefix ltac:(rewrite Zlength_cons; lia)).
      lia.
    + rewrite paren_level_upto_Zlength_cons in Hfinal.
      lia.
Qed.

Lemma check_paren_aux_z_sound_final : forall l depth,
  check_paren_aux_z l depth = true ->
  depth + paren_level_upto (Zlength l) l = 0.
Proof.
  induction l as [| c rest IH]; intros depth Hcheck.
  - simpl in Hcheck.
    apply Z.eqb_eq in Hcheck.
    unfold paren_level_upto.
    simpl.
    lia.
  - simpl in Hcheck.
    destruct (Z.ltb_spec (depth + paren_delta c) 0); try discriminate.
    specialize (IH (depth + paren_delta c) Hcheck).
    rewrite paren_level_upto_Zlength_cons.
    lia.
Qed.

Lemma check_paren_aux_z_sound_prefix : forall l depth k,
  check_paren_aux_z l depth = true ->
  0 <= k < Zlength l ->
  0 <= depth + paren_level_upto (k + 1) l.
Proof.
  induction l as [| c rest IH]; intros depth k Hcheck Hk.
  - rewrite Zlength_nil in Hk. lia.
  - simpl in Hcheck.
    destruct (Z.ltb_spec (depth + paren_delta c) 0); try discriminate.
    destruct (Z.eq_dec k 0) as [-> | Hk0].
    + rewrite paren_level_upto_cons_succ by lia.
      replace (0 + 1 - 1) with 0 by lia.
      rewrite paren_level_upto_0.
      lia.
    + rewrite paren_level_upto_cons_succ by lia.
      replace (k + 1 - 1) with k by lia.
      specialize (IH (depth + paren_delta c) (k - 1) Hcheck).
      replace (k - 1 + 1) with k in IH by lia.
      replace (depth + (paren_delta c + paren_level_upto k rest))
        with (depth + paren_delta c + paren_level_upto k rest) by lia.
      apply IH.
      rewrite Zlength_cons in Hk.
      lia.
Qed.

Lemma ascii_eqb_ascii_of_z_const_61 : forall x n,
  0 <= x < 256 ->
  (n < 256)%nat ->
  Ascii.eqb (ascii_of_z x) (ascii_of_nat n) = Z.eqb x (Z.of_nat n).
Proof.
  intros x n Hx Hn.
  destruct (Ascii.eqb_spec (ascii_of_z x) (ascii_of_nat n)) as [Heq | Hneq];
  destruct (Z.eqb_spec x (Z.of_nat n)) as [Hz | Hnz]; try reflexivity.
  - exfalso.
    apply Hnz.
    apply (f_equal nat_of_ascii) in Heq.
    rewrite nat_of_ascii_ascii_of_z in Heq by exact Hx.
    rewrite nat_ascii_embedding in Heq by lia.
    lia.
  - subst x.
    exfalso.
    apply Hneq.
    apply ascii_of_z_eq_ascii_of_nat.
    reflexivity.
Qed.

Lemma correct_bracketing_aux_check_paren : forall l depth,
  ascii_range_z l ->
  0 <= depth ->
  correct_bracketing_aux (string_of_list_z l) (Z.to_nat depth) =
  check_paren_aux_z l depth.
Proof.
  induction l as [| c rest IH]; intros depth Hrange Hdepth.
  - simpl.
    destruct (Z.eqb_spec depth 0) as [-> | Hneq].
    + reflexivity.
    + destruct (Z.to_nat depth) eqn:Hnat.
      * rewrite <- (Z2Nat.id depth) in Hneq by lia.
        rewrite Hnat in Hneq.
        lia.
      * reflexivity.
  - simpl.
    assert (Hc : 0 <= c < 256).
    {
      specialize (Hrange 0).
      rewrite Znth0_cons in Hrange.
      apply Hrange.
      rewrite Zlength_cons. pose proof (Zlength_nonneg rest). lia.
    }
    assert (Htail : ascii_range_z rest).
    {
      intros i Hi.
      specialize (Hrange (i + 1)).
      rewrite Znth_cons in Hrange by lia.
      replace (i + 1 - 1) with i in Hrange by lia.
      apply Hrange.
      rewrite Zlength_cons. lia.
    }
    change "("%char with (ascii_of_nat 40).
    change ")"%char with (ascii_of_nat 41).
    rewrite ascii_eqb_ascii_of_z_const_61 by lia.
    destruct (Z.eqb_spec c 40) as [Hopen | Hnot_open].
    + subst c.
      change (paren_delta 40) with 1.
      destruct (Z.ltb_spec (depth + 1) 0); try lia.
      replace (S (Z.to_nat depth)) with (Z.to_nat (depth + 1)) by lia.
      apply IH; try lia; exact Htail.
    + rewrite ascii_eqb_ascii_of_z_const_61 by lia.
      destruct (Z.eqb_spec c 41) as [Hclose | Hnot_close].
      * subst c.
        change (paren_delta 41) with (-1).
        destruct (Z.to_nat depth) eqn:Hdepth_nat.
        -- assert (depth = 0) by lia.
           subst depth.
           reflexivity.
        -- destruct (Z.ltb_spec (depth + -1) 0).
           ++ assert (depth = 0) by lia. subst depth. discriminate.
           ++ replace n with (Z.to_nat (depth - 1)) by lia.
              replace (depth + -1) with (depth - 1) by lia.
              apply IH; try lia; exact Htail.
      * unfold paren_delta.
        destruct (Z.eqb c 40) eqn:Hc40; [apply Z.eqb_eq in Hc40; contradiction|].
        destruct (Z.eqb c 41) eqn:Hc41; [apply Z.eqb_eq in Hc41; contradiction|].
        destruct (Z.ltb_spec (depth + 0) 0); try lia.
        replace (depth + 0) with depth by lia.
        change (Z.of_nat 40) with 40.
        change (Z.of_nat 41) with 41.
        rewrite Hc40, Hc41.
        apply IH; try lia; exact Htail.
Qed.

Lemma problem_61_pre_z_char : forall l k,
  ascii_range_z l ->
  problem_61_pre_z l ->
  0 <= k < Zlength l ->
  Znth k l 0 = 40 \/ Znth k l 0 = 41.
Proof.
  intros l k Hrange Hpre Hk.
  unfold problem_61_pre_z, problem_61_pre in Hpre.
  rewrite list_ascii_of_string_string_of_list_z in Hpre.
  rewrite Forall_forall in Hpre.
  specialize (Hpre (ascii_of_z (Znth k l 0))).
  assert (Hin : In (ascii_of_z (Znth k l 0)) (map ascii_of_z l)).
  {
    apply in_map.
    apply Znth_In_range_61.
    lia.
  }
  specialize (Hpre Hin).
  assert (Hchar_range : 0 <= Znth k l 0 < 256) by (apply Hrange; exact Hk).
  destruct Hpre as [Hlt | Hgt].
  - left.
    apply (f_equal nat_of_ascii) in Hlt.
    rewrite nat_of_ascii_ascii_of_z in Hlt by exact Hchar_range.
    change (nat_of_ascii "("%char) with 40%nat in Hlt.
    lia.
  - right.
    apply (f_equal nat_of_ascii) in Hgt.
    rewrite nat_of_ascii_ascii_of_z in Hgt by exact Hchar_range.
    change (nat_of_ascii ")"%char) with 41%nat in Hgt.
    lia.
Qed.

Lemma problem_61_spec_z_true : forall l,
  ascii_range_z l ->
  paren_level_upto (Zlength l) l = 0 ->
  paren_nonnegative_prefix (Zlength l) l ->
  problem_61_spec_z l 1.
Proof.
  intros l Hrange Hlevel Hprefix.
  unfold problem_61_spec_z, problem_61_spec, correct_bracketing, bool_of_z.
  simpl.
  symmetry.
  change 0%nat with (Z.to_nat 0).
  rewrite correct_bracketing_aux_check_paren by (try exact Hrange; lia).
  apply check_paren_aux_z_true; try lia.
  intros k Hk.
  apply Hprefix.
  exact Hk.
Qed.

Lemma problem_61_spec_z_false_negative : forall l i,
  ascii_range_z l ->
  0 <= i ->
  i < Zlength l ->
  paren_level_upto (i + 1) l < 0 ->
  problem_61_spec_z l 0.
Proof.
  intros l i Hrange Hi Hbound Hneg.
  unfold problem_61_spec_z, problem_61_spec, correct_bracketing, bool_of_z.
  simpl.
  symmetry.
  change 0%nat with (Z.to_nat 0).
  rewrite correct_bracketing_aux_check_paren by (try exact Hrange; lia).
  destruct (check_paren_aux_z l 0) eqn:Hcheck; try reflexivity.
  pose proof (check_paren_aux_z_sound_prefix l 0 i Hcheck ltac:(lia)).
  lia.
Qed.

Lemma problem_61_spec_z_false_final : forall l level,
  ascii_range_z l ->
  paren_level_upto (Zlength l) l = level ->
  level <> 0 ->
  problem_61_spec_z l 0.
Proof.
  intros l level Hrange Hlevel Hneq.
  unfold problem_61_spec_z, problem_61_spec, correct_bracketing, bool_of_z.
  simpl.
  symmetry.
  change 0%nat with (Z.to_nat 0).
  rewrite correct_bracketing_aux_check_paren by (try exact Hrange; lia).
  destruct (check_paren_aux_z l 0) eqn:Hcheck; try reflexivity.
  pose proof (check_paren_aux_z_sound_final l 0 Hcheck).
  rewrite Hlevel in H.
  lia.
Qed.

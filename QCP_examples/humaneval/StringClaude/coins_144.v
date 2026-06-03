Load "../spec/144".

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
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_144_pre_z (x n : list Z) : Prop :=
  problem_144_pre (string_of_list_z x) (string_of_list_z n).

Definition problem_144_spec_z (x n : list Z) (output : Z) : Prop :=
  problem_144_spec (string_of_list_z x) (string_of_list_z n) (bool_of_z output).

Definition digit_char_z (c : Z) : Prop :=
  48 <= c <= 57.

Definition digit_value_z (c : Z) : Z :=
  c - 48.

Fixpoint parse_digits_z_aux (l : list Z) (acc : Z) : Z :=
  match l with
  | [] => acc
  | c :: rest => parse_digits_z_aux rest (acc * 10 + digit_value_z c)
  end.

Definition parse_digits_z (l : list Z) : Z :=
  parse_digits_z_aux l 0.

Definition fraction_parts_z (s : list Z) (slash num den : Z) : Prop :=
  0 < slash < Zlength s /\
  Znth slash s 0 = 47 /\
  (forall k, 0 <= k < slash -> digit_char_z (Znth k s 0)) /\
  (forall k, slash < k < Zlength s -> digit_char_z (Znth k s 0)) /\
  num = parse_digits_z (sublist 0 slash s) /\
  den = parse_digits_z (sublist (slash + 1) (Zlength s) s) /\
  (forall i, 0 <= i <= slash ->
     0 <= parse_digits_z (sublist 0 i s) <= num) /\
  (forall i, slash + 1 <= i <= Zlength s ->
     0 <= parse_digits_z (sublist (slash + 1) i s) <= den) /\
  0 < num /\ 0 < den.

Definition fraction_values_safe_z (a b c d : Z) : Prop :=
  1 <= a <= 46340 /\
  1 <= b <= 46340 /\
  1 <= c <= 46340 /\
  1 <= d <= 46340.

Lemma parse_digits_z_aux_app_single : forall l c acc,
  parse_digits_z_aux (l ++ [c]) acc =
  parse_digits_z_aux l acc * 10 + digit_value_z c.
Proof.
  induction l as [| x xs IH]; intros c acc; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma parse_digits_z_snoc : forall l c,
  parse_digits_z (l ++ [c]) =
  parse_digits_z l * 10 + digit_value_z c.
Proof.
  intros l c.
  unfold parse_digits_z.
  apply parse_digits_z_aux_app_single.
Qed.

Lemma parse_digits_z_empty : forall l i,
  parse_digits_z (sublist i i l) = 0.
Proof.
  intros.
  rewrite sublist_nil by lia.
  reflexivity.
Qed.

Lemma Znth_app_left_z : forall (l1 l2 : list Z) i d,
  0 <= i < Zlength l1 ->
  Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros l1 l2 i d Hi.
  unfold Znth.
  rewrite app_nth1.
  - reflexivity.
  - rewrite Zlength_correct in Hi.
    assert ((Z.to_nat i < Datatypes.length l1)%nat).
    { apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by lia.
      lia. }
    lia.
Qed.

Lemma parse_digits_z_step_sublist : forall l lo i,
  0 <= lo <= i ->
  i < Zlength l ->
  parse_digits_z (sublist lo (i + 1) l) =
    parse_digits_z (sublist lo i l) * 10 + digit_value_z (Znth i l 0).
Proof.
  intros l lo i Hlo Hi.
  rewrite Zlength_correct in Hi.
  rewrite (sublist_split lo (i + 1) i l) by lia.
  rewrite (sublist_single i l 0) by lia.
  apply parse_digits_z_snoc.
Qed.

Lemma fraction_parts_z_num_digit : forall s slash num den i,
  fraction_parts_z s slash num den ->
  0 <= i < slash ->
  digit_char_z (Znth i s 0).
Proof.
  intros s slash num den i Hparts Hi.
  unfold fraction_parts_z in Hparts.
  destruct Hparts as (_ & _ & Hdigits & _).
  apply Hdigits; lia.
Qed.

Lemma fraction_parts_z_slash_char : forall s slash num den,
  fraction_parts_z s slash num den ->
  Znth slash s 0 = 47.
Proof.
  intros s slash num den Hparts.
  unfold fraction_parts_z in Hparts.
  tauto.
Qed.

Lemma fraction_parts_z_den_digit : forall s slash num den i,
  fraction_parts_z s slash num den ->
  slash < i < Zlength s ->
  digit_char_z (Znth i s 0).
Proof.
  intros s slash num den i Hparts Hi.
  unfold fraction_parts_z in Hparts.
  destruct Hparts as (_ & _ & _ & Hdigits & _).
  apply Hdigits; lia.
Qed.

Lemma fraction_parts_z_num_value : forall s slash num den,
  fraction_parts_z s slash num den ->
  num = parse_digits_z (sublist 0 slash s).
Proof.
  intros s slash num den Hparts.
  unfold fraction_parts_z in Hparts.
  tauto.
Qed.

Lemma fraction_parts_z_den_value : forall s slash num den,
  fraction_parts_z s slash num den ->
  den = parse_digits_z (sublist (slash + 1) (Zlength s) s).
Proof.
  intros s slash num den Hparts.
  unfold fraction_parts_z in Hparts.
  tauto.
Qed.

Lemma fraction_parts_z_prefix_num_bound : forall s slash num den i,
  fraction_parts_z s slash num den ->
  0 <= i <= slash ->
  0 <= parse_digits_z (sublist 0 i s) <= num.
Proof.
  intros s slash num den i Hparts Hi.
  unfold fraction_parts_z in Hparts.
  destruct Hparts as (_ & _ & _ & _ & _ & _ & Hprefix & _).
  apply Hprefix; lia.
Qed.

Lemma fraction_parts_z_prefix_den_bound : forall s slash num den i,
  fraction_parts_z s slash num den ->
  slash + 1 <= i <= Zlength s ->
  0 <= parse_digits_z (sublist (slash + 1) i s) <= den.
Proof.
  intros s slash num den i Hparts Hi.
  unfold fraction_parts_z in Hparts.
  destruct Hparts as (_ & _ & _ & _ & _ & _ & _ & Hprefix & _).
  apply Hprefix; lia.
Qed.

Lemma fraction_parts_z_slash_char_app : forall s slash num den,
  fraction_parts_z s slash num den ->
  Znth slash (s ++ [0]) 0 = 47.
Proof.
  intros s slash num den Hparts.
  rewrite Znth_app_left_z by (unfold fraction_parts_z in Hparts; lia).
  apply fraction_parts_z_slash_char with (num := num) (den := den).
  exact Hparts.
Qed.

Lemma fraction_parts_z_num_loop_lt : forall s slash num den i,
  fraction_parts_z s slash num den ->
  0 <= i <= slash ->
  Znth i (s ++ [0]) 0 <> 47 ->
  i < slash.
Proof.
  intros s slash num den i Hparts Hi Hneq.
  destruct (Z_lt_ge_dec i slash) as [Hlt | Hge]; [exact Hlt |].
  assert (i = slash) by lia.
  subst.
  exfalso.
  apply Hneq.
  apply fraction_parts_z_slash_char_app with (num := num) (den := den).
  exact Hparts.
Qed.

Lemma fraction_parts_z_num_digit_app : forall s slash num den i,
  fraction_parts_z s slash num den ->
  0 <= i < slash ->
  digit_char_z (Znth i (s ++ [0]) 0).
Proof.
  intros s slash num den i Hparts Hi.
  rewrite Znth_app_left_z by (unfold fraction_parts_z in Hparts; lia).
  exact (fraction_parts_z_num_digit s slash num den i Hparts Hi).
Qed.

Lemma fraction_parts_z_den_digit_app : forall s slash num den i,
  fraction_parts_z s slash num den ->
  slash < i < Zlength s ->
  digit_char_z (Znth i (s ++ [0]) 0).
Proof.
  intros s slash num den i Hparts Hi.
  rewrite Znth_app_left_z by (unfold fraction_parts_z in Hparts; lia).
  exact (fraction_parts_z_den_digit s slash num den i Hparts Hi).
Qed.

Lemma fraction_parts_z_num_step_bound : forall s slash num den i,
  fraction_parts_z s slash num den ->
  0 <= i < slash ->
  0 <= parse_digits_z (sublist 0 (i + 1) s) <= num.
Proof.
  intros s slash num den i Hparts Hi.
  exact (fraction_parts_z_prefix_num_bound s slash num den (i + 1) Hparts ltac:(lia)).
Qed.

Lemma fraction_parts_z_den_step_bound : forall s slash num den i,
  fraction_parts_z s slash num den ->
  slash + 1 <= i < Zlength s ->
  0 <= parse_digits_z (sublist (slash + 1) (i + 1) s) <= den.
Proof.
  intros s slash num den i Hparts Hi.
  exact (fraction_parts_z_prefix_den_bound s slash num den (i + 1) Hparts ltac:(lia)).
Qed.

Lemma fraction_parts_z_den_done : forall s slash num den i d,
  fraction_parts_z s slash num den ->
  i >= Zlength s ->
  i <= Zlength s ->
  d = parse_digits_z (sublist (slash + 1) i s) ->
  d = den.
Proof.
  intros s slash num den i d Hparts Hge Hle Hd.
  assert (i = Zlength s) by lia.
  subst i.
  rewrite Hd.
  symmetry.
  apply fraction_parts_z_den_value with (slash := slash) (num := num).
  exact Hparts.
Qed.

Lemma fraction_parts_z_num_step_value : forall s slash num den i,
  fraction_parts_z s slash num den ->
  0 <= i < slash ->
  parse_digits_z (sublist 0 (i + 1) s) =
    parse_digits_z (sublist 0 i s) * 10 + (Znth i (s ++ [0]) 0 - 48).
Proof.
  intros s slash num den i Hparts Hi.
  rewrite Znth_app_left_z by (unfold fraction_parts_z in Hparts; lia).
  unfold digit_value_z.
  rewrite parse_digits_z_step_sublist by (unfold fraction_parts_z in Hparts; lia).
  reflexivity.
Qed.

Lemma fraction_parts_z_den_step_value : forall s slash num den i,
  fraction_parts_z s slash num den ->
  slash + 1 <= i < Zlength s ->
  parse_digits_z (sublist (slash + 1) (i + 1) s) =
    parse_digits_z (sublist (slash + 1) i s) * 10 + (Znth i (s ++ [0]) 0 - 48).
Proof.
  intros s slash num den i Hparts Hi.
  rewrite Znth_app_left_z by (unfold fraction_parts_z in Hparts; lia).
  unfold digit_value_z.
  rewrite parse_digits_z_step_sublist by (unfold fraction_parts_z in Hparts; lia).
  reflexivity.
Qed.

Lemma fraction_parts_z_slash_index : forall s slash num den i,
  fraction_parts_z s slash num den ->
  0 <= i <= slash ->
  Znth i (s ++ [0]) 0 = 47 ->
  i = slash.
Proof.
  intros s slash num den i Hparts Hi Hchar.
  destruct (Z_lt_ge_dec i slash) as [Hlt | Hge]; [| lia].
  rewrite Znth_app_left_z in Hchar by (unfold fraction_parts_z in Hparts; lia).
  pose proof (fraction_parts_z_num_digit s slash num den i Hparts ltac:(lia)) as Hdigit.
  unfold digit_char_z in Hdigit.
  lia.
Qed.

Lemma digit_ascii_value : forall c,
  digit_char_z c ->
  Z.of_nat (char_to_digit (ascii_of_z c)) = digit_value_z c.
Proof.
  intros c Hc.
  unfold char_to_digit, digit_char_z, digit_value_z in *.
  rewrite nat_of_ascii_ascii_of_z by lia.
  change (nat_of_ascii "0") with 48%nat.
  lia.
Qed.

Lemma list_ascii_to_nat_aux_parse_digits_z_aux : forall l acc,
  (forall k, 0 <= k < Zlength l -> digit_char_z (Znth k l 0)) ->
  0 <= acc ->
  Z.of_nat (list_ascii_to_nat_aux (map ascii_of_z l) (Z.to_nat acc)) =
  parse_digits_z_aux l acc.
Proof.
  induction l as [| c rest IH]; intros acc Hdigits Hacc; simpl.
  - rewrite Z2Nat.id by lia. reflexivity.
  - replace (Z.to_nat acc * 10 + char_to_digit (ascii_of_z c))%nat
      with (Z.to_nat (acc * 10 + digit_value_z c)).
    + apply IH.
      * intros k Hk.
        specialize (Hdigits (k + 1)).
        rewrite Znth_cons in Hdigits by lia.
        replace (k + 1 - 1) with k in Hdigits by lia.
        apply Hdigits.
        rewrite Zlength_cons in *.
        lia.
      * unfold digit_char_z, digit_value_z in *.
        assert (Hc : (48 <= c <= 57)%Z).
        { assert (H0 : (0 <= 0 < Zlength (c :: rest))%Z) by (rewrite Zlength_correct; simpl; lia).
          specialize (Hdigits 0 H0).
          change (Znth 0 (c :: rest) 0) with c in Hdigits.
          exact Hdigits. }
        lia.
    + assert (Hc : digit_char_z c).
      { assert (H0 : (0 <= 0 < Zlength (c :: rest))%Z) by (rewrite Zlength_correct; simpl; lia).
        specialize (Hdigits 0 H0).
        change (Znth 0 (c :: rest) 0) with c in Hdigits.
        exact Hdigits. }
      replace (char_to_digit (ascii_of_z c)) with (Z.to_nat (digit_value_z c)).
      replace 10%nat with (Z.to_nat 10) by reflexivity.
      rewrite <- Z2Nat.inj_mul by lia.
      rewrite <- Z2Nat.inj_add by (unfold digit_char_z, digit_value_z in *; lia).
      reflexivity.
      apply Nat2Z.inj.
      rewrite digit_ascii_value by exact Hc.
      rewrite Z2Nat.id by (unfold digit_char_z, digit_value_z in *; lia).
      reflexivity.
Qed.

Lemma list_ascii_to_nat_parse_digits_z : forall l,
  (forall k, 0 <= k < Zlength l -> digit_char_z (Znth k l 0)) ->
  Z.of_nat (list_ascii_to_nat (map ascii_of_z l)) = parse_digits_z l.
Proof.
  intros l Hdigits.
  unfold list_ascii_to_nat, parse_digits_z.
  change 0%nat with (Z.to_nat 0).
  apply list_ascii_to_nat_aux_parse_digits_z_aux.
  - exact Hdigits.
  - lia.
Qed.

Lemma fraction_parts_z_parse_fraction : forall s slash num den,
  fraction_parts_z s slash num den ->
  Parse_Fraction (list_ascii_of_string (string_of_list_z s))
    (Z.to_nat num) (Z.to_nat den).
Proof.
  intros s slash num den Hparts.
  unfold fraction_parts_z in Hparts.
  destruct Hparts as (Hslash & Hslash_char & Hnum_digits & Hden_digits & Hnum & Hden & Hpos).
  rewrite list_ascii_of_string_string_of_list_z.
  exists (map ascii_of_z (sublist 0 slash s)).
  exists (map ascii_of_z (sublist (slash + 1) (Zlength s) s)).
  split.
  - replace ["/"%char] with (map ascii_of_z [47]) by reflexivity.
    repeat rewrite <- map_app.
    f_equal.
    assert (Hsdecomp :
      s = sublist 0 slash s ++ [47] ++ sublist (slash + 1) (Zlength s) s).
    {
      transitivity (sublist 0 (Zlength s) s).
      - symmetry. apply sublist_self. reflexivity.
      - 
      rewrite (sublist_split 0%Z (Zlength s) (slash + 1)%Z s)
        by (rewrite Zlength_correct in *; lia).
      rewrite (sublist_split 0%Z (slash + 1)%Z slash s)
        by (rewrite Zlength_correct in *; lia).
      rewrite (sublist_single slash s 0) by (rewrite Zlength_correct in *; lia).
      rewrite Hslash_char.
      rewrite app_assoc.
      reflexivity.
    }
    exact Hsdecomp.
  - split.
    + apply Nat2Z.inj.
      rewrite list_ascii_to_nat_parse_digits_z.
      * rewrite Z2Nat.id by lia.
        exact Hnum.
      * intros k Hk.
        rewrite Zlength_sublist in Hk by (rewrite Zlength_correct in *; lia).
        rewrite Znth_sublist by lia.
        apply Hnum_digits.
        lia.
    + apply Nat2Z.inj.
      rewrite list_ascii_to_nat_parse_digits_z.
      * rewrite Z2Nat.id by lia.
        exact Hden.
      * intros k Hk.
        rewrite Zlength_sublist in Hk by (rewrite Zlength_correct in *; lia).
        rewrite Znth_sublist by lia.
        apply Hden_digits.
        lia.
Qed.

Lemma problem_144_spec_z_intro : forall x n sx sn a b c d output,
  fraction_parts_z x sx a b ->
  fraction_parts_z n sn c d ->
  fraction_values_safe_z a b c d ->
  output = (if Z.eqb (Z.rem (a * c) (b * d)) 0 then 1 else 0) ->
  problem_144_spec_z x n output.
Proof.
  intros x n sx sn a b c d output Hx Hn Hsafe Hout.
  unfold problem_144_spec_z, problem_144_spec, bool_of_z.
  exists (Z.to_nat a), (Z.to_nat b), (Z.to_nat c), (Z.to_nat d).
  pose proof (fraction_parts_z_parse_fraction _ _ _ _ Hx) as Hpx.
  pose proof (fraction_parts_z_parse_fraction _ _ _ _ Hn) as Hpn.
  destruct Hsafe as ((Ha_lo & Ha_hi) & (Hb_lo & Hb_hi) & (Hc_lo & Hc_hi) & (Hd_lo & Hd_hi)).
  repeat split; try assumption; try lia.
  rewrite Hout.
  destruct (Z.eqb_spec (Z.rem (a * c) (b * d)) 0) as [Hrem | Hrem].
  - replace (Z.eqb 1 1) with true by reflexivity.
    replace ((Z.to_nat a * Z.to_nat c) mod (Z.to_nat b * Z.to_nat d) =? 0)%nat
      with true.
    + reflexivity.
    + symmetry. apply Nat.eqb_eq.
      apply Nat2Z.inj.
      rewrite Nat2Z.inj_mod by nia.
      rewrite !Nat2Z.inj_mul.
      rewrite !Z2Nat.id by lia.
      rewrite <- Z.rem_mod_nonneg by nia.
      exact Hrem.
  - replace (Z.eqb 0 1) with false by reflexivity.
    replace ((Z.to_nat a * Z.to_nat c) mod (Z.to_nat b * Z.to_nat d) =? 0)%nat
      with false.
    + reflexivity.
    + symmetry. apply Nat.eqb_neq.
      intros Hnat.
      apply Hrem.
      apply (f_equal Z.of_nat) in Hnat.
      rewrite Nat2Z.inj_mod in Hnat by nia.
      rewrite !Nat2Z.inj_mul in Hnat.
      rewrite !Z2Nat.id in Hnat by lia.
      rewrite <- Z.rem_mod_nonneg in Hnat by nia.
      exact Hnat.
Qed.

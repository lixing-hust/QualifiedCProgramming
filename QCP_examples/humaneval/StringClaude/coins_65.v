Load "../spec/65".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.
Require Import Recdef.
From AUXLib Require Import Axioms List_lemma ListLib.
From SimpleC.SL Require Import IntLib.
From SimpleC.EE Require Import coins_44.
From SimpleC.EE Require Import string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Lemma Zlength_map_65 : forall {A B} (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros.
  repeat rewrite Zlength_correct.
  rewrite length_map.
  reflexivity.
Qed.

Lemma Znth_map_65 : forall {A B} (f : A -> B) l i da db,
  0 <= i < Zlength l ->
  Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l i da db Hi.
  unfold Znth.
  rewrite nth_indep with (d' := f da).
  - rewrite map_nth.
    reflexivity.
  - rewrite length_map.
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
Qed.

Lemma Znth_Zseq_65 : forall start len i,
  0 <= i < Z.of_nat len ->
  Znth i (Zseq start len) 0 = start + i.
Proof.
  intros start len i Hi.
  unfold Znth.
  rewrite Zseq_nth.
  - rewrite Z2Nat.id by lia.
    reflexivity.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    lia.
Qed.

Definition problem_65_pre_z (x shift : Z) : Prop :=
  problem_65_pre (Z.to_nat x) (Z.to_nat shift).

Definition problem_65_spec_z (x shift : Z) (output : list Z) : Prop :=
  problem_65_spec (Z.to_nat x) (Z.to_nat shift) (string_of_list_z output).

Definition decimal_digits_z (x : Z) : list Z :=
  map (fun d => 48 + Z.of_nat d) (to_digits (Z.to_nat x)).

Lemma to_digits_fuel_enough_65 : forall fuel n,
  (0 < n)%nat ->
  (n <= fuel)%nat ->
  to_digits_fuel n fuel = to_digits n.
Proof.
  assert (Hmain : forall n fuel,
    (0 < n)%nat ->
    (n <= fuel)%nat ->
    to_digits_fuel n fuel = to_digits n).
  { induction n as [n IH] using lt_wf_ind.
    intros fuel Hpos Hle.
    destruct fuel as [|fuel]; [lia|].
    simpl.
    destruct (n <? 10)%nat eqn:Hsmall.
    - unfold to_digits.
      replace (n =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      destruct n as [|n']; [lia|].
      simpl.
      rewrite Hsmall.
      reflexivity.
    - unfold to_digits.
      replace (n =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      destruct n as [|n']; [lia|].
      simpl.
      rewrite Hsmall.
      f_equal.
      transitivity (to_digits (S n' / 10)%nat).
      + apply IH.
        * apply Nat.ltb_ge in Hsmall.
          apply Nat.div_lt; lia.
        * apply Nat.ltb_ge in Hsmall.
          apply Nat.div_str_pos; lia.
        * apply Nat.ltb_ge in Hsmall.
          assert ((S n' / 10 < S n')%nat) by (apply Nat.div_lt; lia).
          lia.
      + symmetry.
        apply IH.
        * apply Nat.ltb_ge in Hsmall.
          apply Nat.div_lt; lia.
        * apply Nat.ltb_ge in Hsmall.
          apply Nat.div_str_pos; lia.
        * apply Nat.ltb_ge in Hsmall.
          assert ((S n' / 10 < S n')%nat) by (apply Nat.div_lt; lia).
          lia. }
  intros fuel n Hpos Hle.
  apply Hmain; assumption.
Qed.

Lemma decimal_digits_z_zero : decimal_digits_z 0 = [48].
Proof.
  reflexivity.
Qed.

Lemma decimal_digits_z_step : forall x,
  10 <= x ->
  decimal_digits_z x =
    decimal_digits_z (x / 10) ++ [48 + x mod 10].
Proof.
  intros x Hx.
  unfold decimal_digits_z.
  unfold to_digits at 1.
  replace (Z.to_nat x =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  destruct (Z.to_nat x) as [|xn] eqn:Hxnat; [lia|].
  simpl.
  replace (S xn <? 10)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  rewrite map_app.
  f_equal.
  - rewrite to_digits_fuel_enough_65.
    + replace (Z.to_nat (x / 10)) with (S xn / 10)%nat.
      * reflexivity.
      * rewrite <- Hxnat.
        symmetry.
        apply Z2Nat.inj_div; lia.
    + change (0 < S xn / 10)%nat.
      apply Nat.div_str_pos; lia.
    + change (S xn / 10 <= xn)%nat.
      assert (S xn / 10 < S xn)%nat by (apply Nat.div_lt; lia).
      lia.
  - replace (x mod 10) with (Z.of_nat (Z.to_nat (x mod 10))).
    + rewrite Z2Nat.inj_mod by lia.
      rewrite Hxnat.
      reflexivity.
    + rewrite Z2Nat.id; [reflexivity|].
      pose proof (Z.mod_pos_bound x 10 ltac:(lia)).
      lia.
Qed.

Lemma base_digits_z_10_decimal_digits_z : forall x,
  0 <= x ->
  base_digits_z x 10 = decimal_digits_z x.
Proof.
  intros x Hx.
  remember 10 as b eqn:Hb.
  change (base_digits_z x b = decimal_digits_z x).
  functional induction (base_digits_z x b); subst.
  - apply Z.leb_le in e. lia.
  - apply Z.leb_le in e0.
    assert (n = 0) by lia. subst n.
    apply decimal_digits_z_zero.
  - apply Z.leb_gt in e0.
    apply Z.ltb_lt in e1.
    unfold decimal_digits_z, to_digits.
    replace (Z.to_nat n =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    destruct (Z.to_nat n) as [|xn] eqn:Hxnat; [lia|].
    simpl.
    replace (S xn <? 10)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    change ([48 + n] = [48 + Z.of_nat (S xn)]).
    f_equal. f_equal.
    apply Z2Nat.inj.
    + lia.
    + lia.
    + rewrite Hxnat. rewrite Nat2Z.id. reflexivity.
  - apply Z.leb_gt in e0.
    apply Z.ltb_ge in e1.
    rewrite decimal_digits_z_step by lia.
    rewrite IHl by (try reflexivity; apply Z.div_pos; lia).
    reflexivity.
Qed.

Lemma base_fill_full_state_step_10 : forall orig x digits out_l,
  0 < x ->
  0 <= digits ->
  base_fill_full_state_z orig 10 x (digits + 1) out_l ->
  base_fill_full_state_z orig 10 (x / 10) digits
    (replace_Znth digits (signed_last_nbits (48 + x mod 10) 8) out_l).
Proof.
  intros orig x digits out_l Hx Hdigits [suffix [Hstate Hout]].
  exists ((48 + x mod 10) :: suffix).
  split.
  - pose proof (base_fill_state_step orig 10 x (digits + 1) suffix
      Hx ltac:(lia) Hstate) as Hstep.
    replace (digits + 1 - 1) with digits in Hstep by lia.
    exact Hstep.
  - rewrite Hout.
    rewrite (signed_last_nbits_eq (48 + x mod 10) 8)
      by (pose proof (Z.mod_pos_bound x 10 ltac:(lia)); lia).
    apply replace_Znth_repeat_suffix. lia.
Qed.

Definition circular_shift_index_z (len shift i : Z) : Z :=
  if Z.ltb len shift then len - 1 - i else (len - shift + i) mod len.

Definition circular_shift_output_z (x shift : Z) : list Z :=
  let digits := decimal_digits_z x in
  let len := Zlength digits in
  if Z.ltb len shift then
    rev digits
  else
    sublist (len - shift) len digits ++ sublist 0 (len - shift) digits.

Definition circular_shift_prefix_z
  (x shift i : Z) (out_l : list Z) : Prop :=
  out_l = sublist 0 i (circular_shift_output_z x shift).

Lemma circular_shift_output_z_length : forall x shift,
  0 <= shift ->
  Zlength (circular_shift_output_z x shift) = Zlength (decimal_digits_z x).
Proof.
  intros x shift Hshift.
  unfold circular_shift_output_z.
  destruct (Z.ltb (Zlength (decimal_digits_z x)) shift) eqn:Hcase.
  - repeat rewrite Zlength_correct.
    rewrite length_rev.
    reflexivity.
  - apply Z.ltb_ge in Hcase.
    rewrite Zlength_app.
    destruct (Z_lt_le_dec shift (Zlength (decimal_digits_z x))).
    + rewrite !Zlength_sublist by lia.
      lia.
    + replace shift with (Zlength (decimal_digits_z x)) by lia.
      rewrite Zlength_sublist by lia.
      rewrite Zlength_sublist by lia.
      lia.
Qed.

Lemma circular_shift_prefix_z_length : forall x shift i out_l,
  0 <= shift ->
  0 <= i <= Zlength (circular_shift_output_z x shift) ->
  circular_shift_prefix_z x shift i out_l ->
  Zlength out_l = i.
Proof.
  intros x shift i out_l Hshift Hi Hout.
  unfold circular_shift_prefix_z in Hout.
  subst out_l.
  rewrite Zlength_sublist; lia.
Qed.

Lemma circular_shift_prefix_z_full : forall x shift out_l,
  0 <= shift ->
  circular_shift_prefix_z x shift (Zlength (decimal_digits_z x)) out_l ->
  out_l = circular_shift_output_z x shift.
Proof.
  intros x shift out_l Hshift Hout.
  unfold circular_shift_prefix_z in Hout.
  subst out_l.
  rewrite <- (circular_shift_output_z_length x shift) by lia.
  replace (circular_shift_output_z x shift) with
    (circular_shift_output_z x shift ++ nil) at 2 by apply app_nil_r.
  rewrite sublist_app_exact1.
  reflexivity.
Qed.

Lemma circular_shift_prefix_z_snoc : forall x shift i out_l,
  0 <= shift ->
  0 <= i < Zlength (circular_shift_output_z x shift) ->
  circular_shift_prefix_z x shift i out_l ->
  circular_shift_prefix_z x shift (i + 1)
    (out_l ++ Znth i (circular_shift_output_z x shift) 0 :: nil).
Proof.
  intros x shift i out_l Hshift Hi Hout.
  unfold circular_shift_prefix_z in *.
  subst out_l.
  assert (Hlo : 0 <= 0 <= i) by lia.
  assert (Hhi : i <= i + 1 <= Z.of_nat (List.length (circular_shift_output_z x shift))).
  { rewrite <- Zlength_correct. lia. }
  rewrite (sublist_split 0 (i + 1) i
             (circular_shift_output_z x shift) Hlo Hhi).
  rewrite (@sublist_single Z i (circular_shift_output_z x shift) 0) by lia.
  reflexivity.
Qed.

Lemma Znth_rev_65 : forall {A : Type} (l : list A) (d : A) i,
  0 <= i < Zlength l ->
  Znth i (rev l) d = Znth (Zlength l - 1 - i) l d.
Proof.
  intros A l d i Hi.
  unfold Znth.
  rewrite rev_nth.
  - assert (Hnat :
      Z.to_nat (Zlength l - 1 - i) =
      (List.length l - S (Z.to_nat i))%nat).
    { apply Nat2Z.inj.
      rewrite Z2Nat.id by lia.
      rewrite Nat2Z.inj_sub by (rewrite Zlength_correct in Hi; lia).
      rewrite Nat2Z.inj_succ.
      rewrite Z2Nat.id by lia.
      rewrite Zlength_correct.
      lia. }
    rewrite Hnat.
    reflexivity.
  - rewrite Zlength_correct in Hi.
    lia.
Qed.

Lemma circular_shift_output_z_reverse_char : forall x shift i,
  0 <= x ->
  Zlength (decimal_digits_z x) < shift ->
  0 <= i < Zlength (decimal_digits_z x) ->
  Znth i (circular_shift_output_z x shift) 0 =
  Znth (Zlength (decimal_digits_z x) - 1 - i) (decimal_digits_z x) 0.
Proof.
  intros x shift i Hx Hshift Hi.
  unfold circular_shift_output_z.
  replace (Z.ltb (Zlength (decimal_digits_z x)) shift) with true
    by (symmetry; apply Z.ltb_lt; lia).
  apply Znth_rev_65.
  lia.
Qed.

Lemma circular_shift_output_z_rot_char : forall x shift i,
  0 <= x ->
  0 <= shift <= Zlength (decimal_digits_z x) ->
  0 <= i < Zlength (decimal_digits_z x) ->
  Znth i (circular_shift_output_z x shift) 0 =
  Znth ((Zlength (decimal_digits_z x) - shift + i) mod
        Zlength (decimal_digits_z x)) (decimal_digits_z x) 0.
Proof.
  intros x shift i Hx Hshift Hi.
  unfold circular_shift_output_z.
  replace (Z.ltb (Zlength (decimal_digits_z x)) shift) with false
    by (symmetry; apply Z.ltb_ge; lia).
  assert (Hlen_pos : 0 < Zlength (decimal_digits_z x)) by lia.
  destruct (Z_lt_le_dec i shift) as [Hfirst | Hsecond].
  - rewrite app_Znth1.
    2:{ rewrite Zlength_sublist by lia. lia. }
    rewrite Znth_sublist by lia.
    replace (i + (Zlength (decimal_digits_z x) - shift))
      with (Zlength (decimal_digits_z x) - shift + i) by lia.
    rewrite Z.mod_small by lia.
    reflexivity.
  - rewrite app_Znth2.
    2:{ rewrite Zlength_sublist by lia. lia. }
    rewrite Zlength_sublist by lia.
    rewrite Znth_sublist by lia.
    replace (i - (Zlength (decimal_digits_z x) - (Zlength (decimal_digits_z x) - shift)))
      with (i - shift) by lia.
    replace (i - shift + 0) with (i - shift) by lia.
    replace ((Zlength (decimal_digits_z x) - shift + i) mod
             Zlength (decimal_digits_z x))
      with (i - shift) by (apply Z.mod_unique with (q := 1); lia).
    reflexivity.
Qed.

Lemma string_append_assoc_65 : forall a b c,
  ((a ++ b) ++ c = a ++ (b ++ c))%string.
Proof.
  induction a; intros b c; simpl.
  - reflexivity.
  - rewrite IHa. reflexivity.
Qed.

Lemma string_of_list_z_app_65 : forall a b,
  string_of_list_z (a ++ b) = (string_of_list_z a ++ string_of_list_z b)%string.
Proof.
  induction a; intros b; simpl.
  - reflexivity.
  - rewrite IHa.
    reflexivity.
Qed.

Lemma from_digits_to_string_app_65 : forall a b,
  from_digits_to_string (a ++ b) =
  (from_digits_to_string a ++ from_digits_to_string b)%string.
Proof.
  induction a; intros b; simpl.
  - reflexivity.
  - rewrite IHa.
    rewrite string_append_assoc_65.
    reflexivity.
Qed.

Lemma digit_to_string_ascii_of_z_65 : forall d,
  (d <= 9)%nat ->
  string_of_list_z [48 + Z.of_nat d] = digit_to_string d.
Proof.
  intros d Hd.
  repeat
    (destruct d as [|d]; [reflexivity| simpl in Hd]).
  lia.
Qed.

Lemma to_digits_fuel_digit_range_65 : forall fuel n,
  Forall (fun d => (d <= 9)%nat) (to_digits_fuel n fuel).
Proof.
  induction fuel as [|fuel IH]; intros n; simpl.
  - constructor.
  - destruct (n <? 10)%nat eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      constructor; [lia|constructor].
    + apply Forall_app.
      split.
      * apply IH.
      * constructor.
        -- change ((n mod 10 <= 9)%nat).
           pose proof (Nat.mod_upper_bound n 10 ltac:(lia)).
           lia.
        -- constructor.
Qed.

Lemma to_digits_digit_range_65 : forall n,
  Forall (fun d => (d <= 9)%nat) (to_digits n).
Proof.
  intros n.
  unfold to_digits.
  destruct (n =? 0)%nat.
  - constructor; [lia|constructor].
  - apply to_digits_fuel_digit_range_65.
Qed.

Lemma string_of_decimal_digits_nat_65 : forall digits,
  Forall (fun d => (d <= 9)%nat) digits ->
  string_of_list_z (map (fun d => 48 + Z.of_nat d) digits) =
  from_digits_to_string digits.
Proof.
  induction digits as [|d rest IH]; intros Hrange.
  - reflexivity.
  - inversion Hrange as [|? ? Hd Hrest]; subst.
    change (string_of_list_z ([48 + Z.of_nat d] ++
              map (fun d0 : nat => 48 + Z.of_nat d0) rest) =
            (digit_to_string d ++ from_digits_to_string rest)%string).
    rewrite string_of_list_z_app_65.
    rewrite IH by exact Hrest.
    rewrite digit_to_string_ascii_of_z_65 by exact Hd.
    reflexivity.
Qed.

Lemma string_of_decimal_digits_z_65 : forall x,
  string_of_list_z (decimal_digits_z x) =
  from_digits_to_string (to_digits (Z.to_nat x)).
Proof.
  intros x.
  unfold decimal_digits_z.
  apply string_of_decimal_digits_nat_65.
  apply to_digits_digit_range_65.
Qed.

Lemma string_of_decimal_digits_rev_z_65 : forall x,
  string_of_list_z (rev (decimal_digits_z x)) =
  from_digits_to_string (rev (to_digits (Z.to_nat x))).
Proof.
  intros x.
  unfold decimal_digits_z.
  rewrite <- map_rev.
  apply string_of_decimal_digits_nat_65.
  apply Forall_forall.
  intros d Hd.
  pose proof (to_digits_digit_range_65 (Z.to_nat x)) as Hrange.
  rewrite Forall_forall in Hrange.
  apply Hrange.
  apply in_rev. exact Hd.
Qed.

Lemma sublist_map_tail_65 : forall {A B : Type} (f : A -> B) (l : list A) k,
  0 <= k <= Zlength (map f l) ->
  sublist k (Zlength (map f l)) (map f l) = map f (skipn (Z.to_nat k) l).
Proof.
  intros A B f l k Hk.
  unfold sublist.
  rewrite Zlength_correct.
  rewrite length_map.
  rewrite Nat2Z.id.
  rewrite firstn_all2 by (rewrite length_map; lia).
  rewrite skipn_map.
  reflexivity.
Qed.

Lemma sublist_map_head_65 : forall {A B : Type} (f : A -> B) (l : list A) k,
  0 <= k <= Zlength l ->
  sublist 0 k (map f l) = map f (firstn (Z.to_nat k) l).
Proof.
  intros A B f l k Hk.
  unfold sublist.
  rewrite skipn_O.
  rewrite firstn_map.
  reflexivity.
Qed.

Lemma Forall_firstn_65 : forall {A : Type} (P : A -> Prop) n l,
  Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n.
  induction n as [|n IH]; intros l Hall; simpl.
  - constructor.
  - destruct l as [|a l]; simpl; [constructor|].
    inversion Hall; subst.
    constructor; auto.
Qed.

Lemma Forall_skipn_65 : forall {A : Type} (P : A -> Prop) n l,
  Forall P l -> Forall P (skipn n l).
Proof.
  intros A P n.
  induction n as [|n IH]; intros l Hall; simpl.
  - exact Hall.
  - destruct l as [|a l]; simpl; [constructor|].
    inversion Hall; subst.
    apply IH. assumption.
Qed.

Lemma string_of_rotated_decimal_digits_65 : forall x shift,
  0 <= shift <= Zlength (decimal_digits_z x) ->
  string_of_list_z
    (sublist (Zlength (decimal_digits_z x) - shift)
       (Zlength (decimal_digits_z x)) (decimal_digits_z x) ++
     sublist 0 (Zlength (decimal_digits_z x) - shift) (decimal_digits_z x)) =
  from_digits_to_string
    (skipn (Z.to_nat (Zlength (decimal_digits_z x) - shift))
       (to_digits (Z.to_nat x)) ++
     firstn (Z.to_nat (Zlength (decimal_digits_z x) - shift))
       (to_digits (Z.to_nat x))).
Proof.
  intros x shift Hshift.
  rewrite string_of_list_z_app_65.
  unfold decimal_digits_z.
  rewrite (@sublist_map_tail_65 nat Z
    (fun d => 48 + Z.of_nat d) (to_digits (Z.to_nat x))
    (Zlength (map (fun d => 48 + Z.of_nat d) (to_digits (Z.to_nat x))) - shift)).
  2:{ unfold decimal_digits_z in Hshift; lia. }
  rewrite (@sublist_map_head_65 nat Z
    (fun d => 48 + Z.of_nat d) (to_digits (Z.to_nat x))
    (Zlength (map (fun d => 48 + Z.of_nat d) (to_digits (Z.to_nat x))) - shift)).
  2:{ rewrite Zlength_map_65.
      unfold decimal_digits_z in Hshift.
      rewrite Zlength_map_65 in Hshift.
      lia. }
  rewrite from_digits_to_string_app_65.
  rewrite !string_of_decimal_digits_nat_65.
  - reflexivity.
  - apply Forall_firstn_65. apply to_digits_digit_range_65.
  - apply Forall_skipn_65. apply to_digits_digit_range_65.
Qed.

Lemma circular_shift_output_z_string_65 : forall x shift,
  0 <= x ->
  0 <= shift ->
  string_of_list_z (circular_shift_output_z x shift) =
  circular_shift_impl (Z.to_nat x) (Z.to_nat shift).
Proof.
  intros x shift Hx Hshift.
  unfold circular_shift_impl.
  destruct (Z.to_nat x =? 0)%nat eqn:Hx0.
  - apply Nat.eqb_eq in Hx0.
    assert (x = 0) by lia. subst x.
    unfold circular_shift_output_z, decimal_digits_z, to_digits.
    simpl.
    change (Zlength [48]) with 1.
    destruct (Z.ltb 1 shift) eqn:Hcase.
    + reflexivity.
    + apply Z.ltb_ge in Hcase.
      assert (shift = 0 \/ shift = 1) by lia.
      destruct H as [-> | ->]; reflexivity.
  - apply Nat.eqb_neq in Hx0.
    set (digits := to_digits (Z.to_nat x)).
    assert (Hlen :
      Zlength (decimal_digits_z x) = Z.of_nat (List.length digits)).
    { subst digits.
      unfold decimal_digits_z.
      rewrite Zlength_map_65.
      apply Zlength_correct. }
    destruct (List.length digits <? Z.to_nat shift)%nat eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      unfold circular_shift_output_z.
      replace (Z.ltb (Zlength (decimal_digits_z x)) shift) with true
        by (symmetry; apply Z.ltb_lt; rewrite Hlen; lia).
      subst digits.
      apply string_of_decimal_digits_rev_z_65.
    + apply Nat.ltb_ge in Hlt.
      unfold circular_shift_output_z.
      replace (Z.ltb (Zlength (decimal_digits_z x)) shift) with false
        by (symmetry; apply Z.ltb_ge; rewrite Hlen; lia).
      assert (Hshift_len : 0 <= shift <= Zlength (decimal_digits_z x)).
      { rewrite Hlen. lia. }
      rewrite string_of_rotated_decimal_digits_65 by exact Hshift_len.
      destruct ((Z.to_nat shift mod List.length digits) =? 0)%nat eqn:Heff.
      * apply Nat.eqb_eq in Heff.
        assert (Z.to_nat shift = 0%nat \/ Z.to_nat shift = List.length digits).
        { pose proof (Nat.mod_upper_bound (Z.to_nat shift) (List.length digits)) as Hmod.
          assert (List.length digits <> 0)%nat.
          { subst digits.
            unfold to_digits.
            destruct (Z.to_nat x) as [|xn] eqn:Hxnat.
            - contradiction.
            - simpl.
              destruct (S xn <? 10)%nat.
              + simpl. discriminate.
              + rewrite length_app. simpl. lia. }
          specialize (Hmod H).
          assert (Z.to_nat shift <= List.length digits)%nat by lia.
          destruct (Z.to_nat shift) eqn:Hs; [left; reflexivity|right].
          apply Nat.mod_divide in Heff; try lia.
          destruct Heff as [q Hq].
          destruct q; lia. }
        destruct H as [Hzero | Hfull].
        -- replace (Zlength (decimal_digits_z x) - shift)
             with (Zlength (decimal_digits_z x)) by lia.
           rewrite Hlen.
           rewrite Nat2Z.id.
           rewrite skipn_all, firstn_all.
           reflexivity.
        -- replace (Zlength (decimal_digits_z x) - shift) with 0 by lia.
           simpl.
           rewrite app_nil_r.
           reflexivity.
      * apply Nat.eqb_neq in Heff.
        assert (Hdigits_nonzero : List.length digits <> 0%nat).
        { subst digits.
          unfold to_digits.
          destruct (Z.to_nat x) as [|xn] eqn:Hxnat.
          - contradiction.
          - simpl.
            destruct (S xn <? 10)%nat.
            + simpl. discriminate.
            + rewrite length_app. simpl. lia. }
        assert (Hshift_lt_nat : (Z.to_nat shift < List.length digits)%nat).
        { assert (Z.to_nat shift <= List.length digits)%nat by lia.
          destruct (Nat.eq_dec (Z.to_nat shift) (List.length digits)) as [Heq | Hneq].
          - rewrite Heq in Heff.
            rewrite Nat.mod_same in Heff by exact Hdigits_nonzero.
            contradiction.
          - lia. }
        replace ((Z.to_nat shift) mod (List.length digits))%nat with (Z.to_nat shift)
          by (symmetry; apply Nat.mod_small; lia).
        replace (Z.to_nat (Zlength (decimal_digits_z x) - shift))
          with (List.length digits - Z.to_nat shift)%nat by (rewrite Hlen; lia).
        subst digits.
        reflexivity.
Qed.

Lemma problem_65_spec_z_intro : forall x shift,
  0 <= x ->
  0 <= shift ->
  problem_65_spec_z x shift (circular_shift_output_z x shift).
Proof.
  intros x shift Hx Hshift.
  unfold problem_65_spec_z, problem_65_spec.
  apply circular_shift_output_z_string_65; assumption.
Qed.

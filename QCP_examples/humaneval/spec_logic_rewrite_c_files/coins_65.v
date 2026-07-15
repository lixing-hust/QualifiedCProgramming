Load "../spec/65".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.
Require Import Recdef.
From AUXLib Require Import Axioms List_lemma ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Definition repeat_Z {A : Type} (a : A) (n : Z) : list A :=
  repeat a (Z.to_nat n).

Lemma repeat_Z_tail_65 : forall {A : Type} (a : A) n,
  0 <= n ->
  repeat_Z a (n + 1) = repeat_Z a n ++ [a].
Proof.
  intros A a n Hn.
  unfold repeat_Z.
  replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  rewrite <- repeat_cons.
  reflexivity.
Qed.

Lemma Zlength_repeat_Z_65 : forall {A : Type} (a : A) n,
  0 <= n ->
  Zlength (repeat_Z a n) = n.
Proof.
  intros A a n Hn.
  unfold repeat_Z.
  rewrite Zlength_correct, repeat_length.
  lia.
Qed.

Lemma replace_Znth_boundary_app_65 : forall {A : Type} (prefix tail : list A) x y,
  replace_Znth (Zlength prefix) x (prefix ++ y :: tail) =
  prefix ++ x :: tail.
Proof.
  intros A prefix.
  induction prefix as [|a prefix IH]; intros tail x y.
  - reflexivity.
  - rewrite Zlength_cons.
    change (replace_Znth (Z.succ (Zlength prefix)) x
              (a :: (prefix ++ y :: tail)) =
            a :: prefix ++ x :: tail).
    unfold replace_Znth at 1.
    simpl.
    replace (Z.to_nat (Z.succ (Zlength prefix))) with
      (S (Z.to_nat (Zlength prefix))) by (rewrite Zlength_correct; lia).
    simpl.
    fold (@replace_Znth A (Zlength prefix) x (prefix ++ y :: tail)).
    rewrite (IH tail x y).
    reflexivity.
Qed.

Lemma replace_Znth_repeat_suffix_65 : forall d suffix v,
  0 <= d ->
  replace_Znth d v (repeat_Z 0 (d + 1) ++ suffix) =
  repeat_Z 0 d ++ v :: suffix.
Proof.
  intros d suffix v Hd.
  rewrite repeat_Z_tail_65 by lia.
  rewrite <- app_assoc.
  change ([0] ++ suffix) with (0 :: suffix).
  assert (Hlen : Zlength (repeat_Z 0 d) = d)
    by (rewrite Zlength_repeat_Z_65; lia).
  rewrite <- Hlen at 1.
  rewrite replace_Znth_boundary_app_65.
  reflexivity.
Qed.

Lemma Zlength_map_65 : forall {A B : Type} (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros A B f l.
  repeat rewrite Zlength_correct.
  rewrite map_length.
  reflexivity.
Qed.

Lemma Znth_map_65 : forall {A B : Type} (f : A -> B) l i da db,
  0 <= i < Zlength l ->
  Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l i da db Hi.
  unfold Znth.
  rewrite nth_indep with (d' := f da).
  - rewrite map_nth.
    reflexivity.
  - rewrite map_length.
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
Qed.

Definition ascii_of_z_65 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_65 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_65 c) (string_of_list_z_65 rest)
  end.

Definition problem_65_pre_z (x shift : Z) : Prop :=
  problem_65_pre (Z.to_nat x) (Z.to_nat shift).

Definition problem_65_spec_z (x shift : Z) (out_l : list Z) : Prop :=
  problem_65_spec (Z.to_nat x) (Z.to_nat shift) (string_of_list_z_65 out_l).

Definition digit_value_65 (c : Z) : Z := c - 48.

Definition digit_values_65 (l : list Z) : list Z :=
  map digit_value_65 l.

Lemma digit_value_plus_65 : forall d,
  digit_value_65 (48 + d) = d.
Proof.
  unfold digit_value_65. lia.
Qed.

Lemma digit_values_app_65 : forall l1 l2,
  digit_values_65 (l1 ++ l2) = digit_values_65 l1 ++ digit_values_65 l2.
Proof.
  intros l1 l2.
  unfold digit_values_65.
  rewrite map_app.
  reflexivity.
Qed.

Lemma digit_values_single_65 : forall d,
  digit_values_65 [48 + d] = [d].
Proof.
  intros d.
  change (digit_values_65 [48 + d]) with [digit_value_65 (48 + d)].
  rewrite digit_value_plus_65.
  reflexivity.
Qed.

Lemma digit_values_zero_65 :
  digit_values_65 [48] = [0].
Proof.
  change [48] with [48 + 0].
  apply digit_values_single_65.
Qed.

Lemma ascii_of_z_digit_value_65 : forall c,
  ascii_of_z_65 c = digit_ascii (digit_value_65 c).
Proof.
  intros c.
  unfold ascii_of_z_65, digit_ascii, digit_value_65.
  replace (48 + (c - 48)) with c by lia.
  reflexivity.
Qed.

Lemma string_of_list_z_digit_values_65 : forall l,
  string_of_list_z_65 l = digits_to_string (digit_values_65 l).
Proof.
  induction l as [|c rest IH].
  - reflexivity.
  - unfold digits_to_string in *.
    change (string_of_list_z_65 (c :: rest)) with
      (String (ascii_of_z_65 c) (string_of_list_z_65 rest)).
    change (digit_values_65 (c :: rest)) with
      (digit_value_65 c :: digit_values_65 rest).
    simpl.
    rewrite <- IH.
    rewrite ascii_of_z_digit_value_65.
    reflexivity.
Qed.

Function base_digits_z_65 (n base : Z) {measure Z.to_nat n} : list Z :=
  if Z.leb base 1 then [48]
  else if Z.leb n 0 then [48]
  else if Z.ltb n base then [48 + n]
  else base_digits_z_65 (n / base) base ++ [48 + (n mod base)].
Proof.
  intros n base Hbase Hnpos Hnotlt.
  apply Z.leb_gt in Hbase.
  apply Z.leb_gt in Hnpos.
  apply Z.ltb_ge in Hnotlt.
  apply Z2Nat.inj_lt.
  - apply Z.div_pos; lia.
  - lia.
  - apply Z.div_lt; lia.
Defined.

Definition base_digits_pos_z_65 (n base : Z) : list Z :=
  if Z.leb n 0 then [] else base_digits_z_65 n base.

Definition decimal_digits_z_65 (x : Z) : list Z :=
  base_digits_z_65 x 10.

Definition base_count_state_z_65 (orig base t digits : Z) : Prop :=
  0 <= t /\
  0 <= digits /\
  digits + Zlength (base_digits_pos_z_65 t base) =
    Zlength (base_digits_pos_z_65 orig base).

Definition base_fill_state_z_65
  (orig base x digits : Z) (suffix : list Z) : Prop :=
  0 <= x /\
  0 <= digits /\
  digits = Zlength (base_digits_pos_z_65 x base) /\
  base_digits_z_65 orig base = base_digits_pos_z_65 x base ++ suffix.

Definition base_fill_full_state_z_65
  (orig base x digits : Z) (out_l : list Z) : Prop :=
  exists suffix,
    base_fill_state_z_65 orig base x digits suffix /\
    out_l = repeat_Z 0 digits ++ suffix.

Definition circular_shift_output_z_65 (x shift : Z) : list Z :=
  let digits := decimal_digits_z_65 x in
  let len := Zlength digits in
  if Z.ltb len shift then
    rev digits
  else
    sublist (len - shift) len digits ++ sublist 0 (len - shift) digits.

Definition circular_shift_prefix_z_65
    (x shift i : Z) (out_l : list Z) : Prop :=
  out_l = sublist 0 i (circular_shift_output_z_65 x shift).

Lemma decimal_digits_z_65_zero : decimal_digits_z_65 0 = [48].
Proof.
  unfold decimal_digits_z_65.
  rewrite base_digits_z_65_equation.
  reflexivity.
Qed.

Lemma base_digits_z_65_nonempty : forall n base,
  base_digits_z_65 n base <> [].
Proof.
  intros n base.
  functional induction (base_digits_z_65 n base); simpl; try discriminate.
  intro H.
  apply app_eq_nil in H.
  destruct H as [_ Hnil].
  discriminate Hnil.
Qed.

Lemma Zlength_replace_Znth_65 : forall {A : Type} (l : list A) n (v : A),
  0 <= n < Zlength l ->
  Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v Hrange.
  revert n Hrange.
  induction l as [|a l IH]; intros n Hrange; simpl.
  - rewrite Zlength_nil in Hrange. lia.
  - unfold replace_Znth in *.
    destruct (Z.to_nat n) eqn:Hn; simpl.
    + repeat rewrite Zlength_cons. reflexivity.
    + repeat rewrite Zlength_cons.
      specialize (IH (Z.of_nat n0)).
      unfold replace_Znth in IH.
      rewrite Nat2Z.id in IH.
      rewrite IH by (rewrite Zlength_cons in Hrange; lia).
      reflexivity.
Qed.

Lemma base_digits_pos_step_65 : forall n base,
  0 < n ->
  2 <= base ->
  base_digits_pos_z_65 n base =
    base_digits_pos_z_65 (n / base) base ++ [48 + n mod base].
Proof.
  intros n base Hn Hbase.
  unfold base_digits_pos_z_65 at 1.
  replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite base_digits_z_65_equation.
  replace (base <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
  replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (Z.ltb_spec n base) as [Hlt | Hge].
  - replace (n <? base) with true by (symmetry; apply Z.ltb_lt; lia).
    unfold base_digits_pos_z_65.
    replace (n / base <=? 0) with true.
    + rewrite app_nil_l. rewrite Z.mod_small by lia. reflexivity.
    + symmetry. apply Z.leb_le.
      rewrite Z.div_small by lia. lia.
  - replace (n <? base) with false by (symmetry; apply Z.ltb_ge; lia).
    unfold base_digits_pos_z_65 at 1.
    assert (0 < n / base).
    { assert (1 <= n / base) by (apply Z.div_le_lower_bound; lia).
      lia. }
    replace (n / base <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
    reflexivity.
Qed.

Lemma base_count_state_init_65 : forall x base,
  0 < x ->
  base_count_state_z_65 x base x 0.
Proof.
  intros x base Hx.
  unfold base_count_state_z_65.
  lia.
Qed.

Lemma base_count_state_step_65 : forall orig base t digits,
  0 < t ->
  2 <= base ->
  base_count_state_z_65 orig base t digits ->
  base_count_state_z_65 orig base (t / base) (digits + 1).
Proof.
  intros orig base t digits Ht Hbase [Ht0 [Hd Hlen]].
  unfold base_count_state_z_65.
  split; [apply Z.div_pos; lia | split; [lia |]].
  rewrite (base_digits_pos_step_65 t base) in Hlen by lia.
  rewrite Zlength_app in Hlen.
  change (Zlength [48 + t mod base]) with 1 in Hlen.
  lia.
Qed.

Lemma base_count_state_done_65 : forall orig base digits,
  0 < orig ->
  base_count_state_z_65 orig base 0 digits ->
  digits = Zlength (base_digits_z_65 orig base).
Proof.
  intros orig base digits Horig [_ [Hd Hlen]].
  unfold base_digits_pos_z_65 in Hlen.
  replace (0 <=? 0) with true in Hlen by (symmetry; apply Z.leb_le; lia).
  replace (orig <=? 0) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
  change (Zlength (@nil Z)) with 0 in Hlen.
  lia.
Qed.

Lemma base_fill_state_init_65 : forall orig base,
  0 < orig ->
  base_fill_state_z_65 orig base orig
    (Zlength (base_digits_z_65 orig base)) [].
Proof.
  intros orig base Horig.
  unfold base_fill_state_z_65, base_digits_pos_z_65.
  replace (orig <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  repeat split; try lia.
  - apply Zlength_nonneg.
  - rewrite app_nil_r. reflexivity.
Qed.

Lemma base_fill_state_step_65 : forall orig base x digits suffix,
  0 < x ->
  2 <= base ->
  base_fill_state_z_65 orig base x digits suffix ->
  base_fill_state_z_65 orig base (x / base) (digits - 1)
    ((48 + x mod base) :: suffix).
Proof.
  intros orig base x digits suffix Hx Hbase [Hx0 [Hd [Hdigits Hsplit]]].
  unfold base_fill_state_z_65.
  rewrite (base_digits_pos_step_65 x base) in Hsplit by lia.
  rewrite (base_digits_pos_step_65 x base) in Hdigits by lia.
  rewrite Zlength_app in Hdigits.
  change (Zlength [48 + x mod base]) with 1 in Hdigits.
  assert (Hdiv_nonneg : 0 <= x / base) by (apply Z.div_pos; lia).
  assert (Hprefix_len : 0 <= Zlength (base_digits_pos_z_65 (x / base) base))
    by apply Zlength_nonneg.
  split; [exact Hdiv_nonneg | split; [lia | split; [|]]].
  - rewrite Hdigits. lia.
  - rewrite Hsplit.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma base_fill_state_done_65 : forall orig base suffix,
  base_fill_state_z_65 orig base 0 0 suffix ->
  suffix = base_digits_z_65 orig base.
Proof.
  intros orig base suffix [_ [_ [_ Hsplit]]].
  unfold base_digits_pos_z_65 in Hsplit.
  replace (0 <=? 0) with true in Hsplit by (symmetry; apply Z.leb_le; lia).
  simpl in Hsplit.
  symmetry. exact Hsplit.
Qed.

Lemma base_fill_full_state_init_65 : forall orig base,
  0 < orig ->
  base_fill_full_state_z_65 orig base orig
    (Zlength (base_digits_z_65 orig base))
    (repeat_Z 0 (Zlength (base_digits_z_65 orig base))).
Proof.
  intros orig base Horig.
  exists [].
  split.
  - apply base_fill_state_init_65. lia.
  - rewrite app_nil_r. reflexivity.
Qed.

Lemma base_fill_full_state_step_65 : forall orig x digits out_l,
  0 < x ->
  base_fill_full_state_z_65 orig 10 x (digits + 1) out_l ->
  base_fill_full_state_z_65 orig 10 (x / 10) digits
    (replace_Znth digits (signed_last_nbits (48 + x mod 10) 8) out_l).
Proof.
  intros orig x digits out_l Hx [suffix [Hstate Hout]].
  exists ((48 + x mod 10) :: suffix).
  split.
  - pose proof (base_fill_state_step_65 orig 10 x (digits + 1) suffix
      Hx ltac:(lia) Hstate) as Hstep.
    replace (digits + 1 - 1) with digits in Hstep by lia.
    exact Hstep.
  - rewrite Hout.
    rewrite (signed_last_nbits_eq (48 + x mod 10) 8)
      by (pose proof (Z.mod_pos_bound x 10 ltac:(lia)); lia).
    assert (0 <= digits).
    { destruct Hstate as [_ [_ [Hdigits _]]].
      rewrite (base_digits_pos_step_65 x 10) in Hdigits by lia.
      rewrite Zlength_app in Hdigits.
      change (Zlength [48 + x mod 10]) with 1 in Hdigits.
      pose proof (Zlength_nonneg (base_digits_pos_z_65 (x / 10) 10)).
      lia. }
    apply replace_Znth_repeat_suffix_65. lia.
Qed.

Lemma base_fill_full_state_done_65 : forall orig base out_l,
  base_fill_full_state_z_65 orig base 0 0 out_l ->
  out_l = base_digits_z_65 orig base.
Proof.
  intros orig base out_l [suffix [Hstate Hout]].
  pose proof (base_fill_state_done_65 orig base suffix Hstate) as Hsuffix.
  subst suffix.
  rewrite Hout.
  reflexivity.
Qed.

Lemma base_fill_full_state_positive_digits_65 : forall orig base x digits out_l,
  0 < x ->
  2 <= base ->
  base_fill_full_state_z_65 orig base x digits out_l ->
  1 <= digits.
Proof.
  intros orig base x digits out_l Hx Hbase [suffix [[_ [_ [Hdigits _]]] _]].
  rewrite Hdigits.
  unfold base_digits_pos_z_65.
  replace (x <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (base_digits_z_65 x base) eqn:Hbd.
  - exfalso. apply (base_digits_z_65_nonempty x base). exact Hbd.
  - rewrite Zlength_cons.
    pose proof (Zlength_nonneg l). lia.
Qed.

Lemma circular_shift_output_z_65_length : forall x shift,
  0 <= shift ->
  Zlength (circular_shift_output_z_65 x shift) = Zlength (decimal_digits_z_65 x).
Proof.
  intros x shift Hshift.
  unfold circular_shift_output_z_65.
  destruct (Z.ltb (Zlength (decimal_digits_z_65 x)) shift) eqn:Hcase.
  - repeat rewrite Zlength_correct.
    rewrite length_rev.
    reflexivity.
  - apply Z.ltb_ge in Hcase.
    rewrite Zlength_app.
    destruct (Z_lt_le_dec shift (Zlength (decimal_digits_z_65 x))).
    + rewrite !Zlength_sublist by lia.
      lia.
    + replace shift with (Zlength (decimal_digits_z_65 x)) by lia.
      rewrite Zlength_sublist by lia.
      rewrite Zlength_sublist by lia.
      lia.
Qed.

Lemma circular_shift_prefix_z_65_length : forall x shift i out_l,
  0 <= shift ->
  0 <= i <= Zlength (circular_shift_output_z_65 x shift) ->
  circular_shift_prefix_z_65 x shift i out_l ->
  Zlength out_l = i.
Proof.
  intros x shift i out_l Hshift Hi Hout.
  unfold circular_shift_prefix_z_65 in Hout.
  subst out_l.
  rewrite Zlength_sublist; lia.
Qed.

Lemma circular_shift_prefix_z_65_full : forall x shift out_l,
  0 <= shift ->
  circular_shift_prefix_z_65 x shift (Zlength (decimal_digits_z_65 x)) out_l ->
  out_l = circular_shift_output_z_65 x shift.
Proof.
  intros x shift out_l Hshift Hout.
  unfold circular_shift_prefix_z_65 in Hout.
  subst out_l.
  rewrite <- (circular_shift_output_z_65_length x shift) by lia.
  replace (circular_shift_output_z_65 x shift) with
    (circular_shift_output_z_65 x shift ++ nil) at 2 by apply app_nil_r.
  rewrite sublist_app_exact1.
  reflexivity.
Qed.

Lemma circular_shift_prefix_z_65_snoc : forall x shift i out_l,
  0 <= shift ->
  0 <= i < Zlength (circular_shift_output_z_65 x shift) ->
  circular_shift_prefix_z_65 x shift i out_l ->
  circular_shift_prefix_z_65 x shift (i + 1)
    (out_l ++ Znth i (circular_shift_output_z_65 x shift) 0 :: nil).
Proof.
  intros x shift i out_l Hshift Hi Hout.
  unfold circular_shift_prefix_z_65 in *.
  subst out_l.
  assert (Hlo : 0 <= 0 <= i) by lia.
  assert (Hhi : i <= i + 1 <= Zlength (circular_shift_output_z_65 x shift)) by lia.
  rewrite (@sublist_split Z 0 (i + 1) i
             (circular_shift_output_z_65 x shift) Hlo Hhi).
  rewrite (@sublist_single Z 0 i (circular_shift_output_z_65 x shift)) by lia.
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

Lemma circular_shift_output_z_65_reverse_char : forall x shift i,
  0 <= x ->
  Zlength (decimal_digits_z_65 x) < shift ->
  0 <= i < Zlength (decimal_digits_z_65 x) ->
  Znth i (circular_shift_output_z_65 x shift) 0 =
  Znth (Zlength (decimal_digits_z_65 x) - 1 - i) (decimal_digits_z_65 x) 0.
Proof.
  intros x shift i Hx Hshift Hi.
  unfold circular_shift_output_z_65.
  replace (Z.ltb (Zlength (decimal_digits_z_65 x)) shift) with true
    by (symmetry; apply Z.ltb_lt; lia).
  apply Znth_rev_65.
  lia.
Qed.

Lemma circular_shift_output_z_65_rot_char : forall x shift i,
  0 <= x ->
  0 <= shift <= Zlength (decimal_digits_z_65 x) ->
  0 <= i < Zlength (decimal_digits_z_65 x) ->
  Znth i (circular_shift_output_z_65 x shift) 0 =
  Znth ((Zlength (decimal_digits_z_65 x) - shift + i) mod
        Zlength (decimal_digits_z_65 x)) (decimal_digits_z_65 x) 0.
Proof.
  intros x shift i Hx Hshift Hi.
  unfold circular_shift_output_z_65.
  replace (Z.ltb (Zlength (decimal_digits_z_65 x)) shift) with false
    by (symmetry; apply Z.ltb_ge; lia).
  assert (Hlen_pos : 0 < Zlength (decimal_digits_z_65 x)) by lia.
  destruct (Z_lt_le_dec i shift) as [Hfirst | Hsecond].
  - rewrite app_Znth1.
    2:{ rewrite Zlength_sublist by lia. lia. }
    rewrite Znth_sublist by lia.
    replace (i + (Zlength (decimal_digits_z_65 x) - shift))
      with (Zlength (decimal_digits_z_65 x) - shift + i) by lia.
    rewrite Z.mod_small by lia.
    reflexivity.
  - rewrite app_Znth2.
    2:{ rewrite Zlength_sublist by lia. lia. }
    rewrite Zlength_sublist by lia.
    rewrite Znth_sublist by lia.
    replace (i - (Zlength (decimal_digits_z_65 x) - (Zlength (decimal_digits_z_65 x) - shift)))
      with (i - shift) by lia.
    replace (i - shift + 0) with (i - shift) by lia.
    replace ((Zlength (decimal_digits_z_65 x) - shift + i) mod
             Zlength (decimal_digits_z_65 x))
      with (i - shift) by (apply Z.mod_unique with (q := 1); lia).
    reflexivity.
Qed.

Lemma base_digits_z_65_decimal_general : forall n base,
  0 <= n ->
  2 <= base ->
  list_within_bound base (rev (digit_values_65 (base_digits_z_65 n base))) /\
  list_to_Z base (rev (digit_values_65 (base_digits_z_65 n base))) = n /\
  ((n = 0 /\ digit_values_65 (base_digits_z_65 n base) = [0]) \/
   (n <> 0 /\
    digit_values_65 (base_digits_z_65 n base) <> [] /\
    hd 0 (digit_values_65 (base_digits_z_65 n base)) <> 0)).
Proof.
  intros n base Hn Hbase.
  functional induction (base_digits_z_65 n base); subst.
  - apply Z.leb_le in e. lia.
  - apply Z.leb_le in e0.
    assert (n = 0) by lia. subst n.
    rewrite digit_values_zero_65.
    simpl.
    repeat split; try lia.
    left. split; reflexivity.
  - apply Z.leb_gt in e0. apply Z.ltb_lt in e1.
    rewrite digit_values_single_65.
    split.
    + unfold list_within_bound. simpl. lia.
    + split.
      * change (rev [n]) with [n].
        rewrite list_to_Z_single.
        lia.
      * right. split; [lia|].
        split; [discriminate|simpl; lia].
  - apply Z.leb_gt in e0. apply Z.ltb_ge in e1.
    destruct (IHl ltac:(apply Z.div_pos; lia) ltac:(lia))
      as [IHbound [IHvalue IHshape]].
    rewrite digit_values_app_65, digit_values_single_65, rev_app_distr.
    split.
    + simpl. split.
      * pose proof (Z.mod_pos_bound n base ltac:(lia)); lia.
      * exact IHbound.
    + split.
      * change (list_to_Z base
            ((n mod base) :: rev (digit_values_65 (base_digits_z_65 (n / base) base))) = n).
        rewrite list_to_Z_cons, IHvalue.
        pose proof (Z.div_mod n base ltac:(lia)).
        lia.
      * right.
        assert (Hqpos : n / base <> 0).
        { assert (1 <= n / base) by (apply Z.div_le_lower_bound; lia).
          lia. }
        destruct IHshape as [[Hzero _] | [Hnz [Hne Hhd]]].
        -- lia.
        -- repeat split; try lia.
           ++ intro Hnil.
              apply app_eq_nil in Hnil.
              destruct Hnil as [Hnil _].
              contradiction.
           ++ destruct (digit_values_65 (base_digits_z_65 (n / base) base))
                as [|a rest] eqn:Hdigits.
              ** contradiction.
              ** simpl in Hhd |- *. exact Hhd.
Qed.

Lemma decimal_digits_z_65_decimal : forall x,
  0 <= x ->
  decimal_digits (Z.to_nat x) (digit_values_65 (decimal_digits_z_65 x)).
Proof.
  intros x Hx.
  unfold decimal_digits_z_65.
  pose proof (base_digits_z_65_decimal_general x 10 Hx ltac:(lia))
    as [Hbound [Hvalue Hshape]].
  unfold decimal_digits.
  rewrite Z2Nat.id by lia.
  repeat split; auto.
  destruct Hshape as [[Hzero Hdigits] | [Hnz [Hne Hhd]]].
  - left. split; [lia|exact Hdigits].
  - right. repeat split; try lia; assumption.
Qed.

Lemma circular_shift_digits_z_65 : forall x shift,
  0 <= x ->
  0 <= shift ->
  circular_shift_digits
    (digit_values_65 (decimal_digits_z_65 x))
    (Z.to_nat shift)
    (digit_values_65 (circular_shift_output_z_65 x shift)).
Proof.
  intros x shift Hx Hshift.
  unfold circular_shift_digits.
  unfold digit_values_65.
  rewrite !Zlength_map_65.
  rewrite circular_shift_output_z_65_length by lia.
  split; [reflexivity|].
  intros i Hi.
  rewrite Z2Nat.id by lia.
  destruct (Z.ltb (Zlength (decimal_digits_z_65 x)) shift) eqn:Hcase.
  - apply Z.ltb_lt in Hcase.
    rewrite Znth_map_65 with (da := 0) by
      (rewrite circular_shift_output_z_65_length by lia; lia).
    rewrite Znth_map_65 with (da := 0) by lia.
    f_equal.
    apply circular_shift_output_z_65_reverse_char; lia.
  - apply Z.ltb_ge in Hcase.
    assert (Hlen_pos : 0 < Zlength (decimal_digits_z_65 x)).
    { pose proof (base_digits_z_65_nonempty x 10) as Hnonempty.
      destruct (decimal_digits_z_65 x) as [|d ds] eqn:Hdigits.
      - unfold decimal_digits_z_65 in Hdigits. contradiction.
      - rewrite Zlength_cons. pose proof (Zlength_nonneg ds). lia. }
    assert (Hshift_len : 0 <= shift <= Zlength (decimal_digits_z_65 x)) by lia.
    rewrite Znth_map_65 with (da := 0) by
      (rewrite circular_shift_output_z_65_length by lia; lia).
    assert (Hidx_eq :
      (Zlength (decimal_digits_z_65 x) - (shift mod Zlength (decimal_digits_z_65 x)) + i)
        mod Zlength (decimal_digits_z_65 x) =
      (Zlength (decimal_digits_z_65 x) - shift + i)
        mod Zlength (decimal_digits_z_65 x)).
    { destruct (Z.eq_dec shift (Zlength (decimal_digits_z_65 x))) as [-> | Hneq].
      - rewrite Z.mod_same by lia.
        replace (Zlength (decimal_digits_z_65 x) - 0 + i)
          with (i + 1 * Zlength (decimal_digits_z_65 x)) by lia.
        rewrite Z.mod_add by lia.
        rewrite Z.mod_small by lia.
        replace (Zlength (decimal_digits_z_65 x) - Zlength (decimal_digits_z_65 x) + i)
          with i by lia.
        rewrite Z.mod_small by lia.
        reflexivity.
      - assert (Hshift_small : 0 <= shift < Zlength (decimal_digits_z_65 x)) by lia.
        rewrite (Z.mod_small shift (Zlength (decimal_digits_z_65 x))) by exact Hshift_small.
        reflexivity. }
    rewrite Hidx_eq.
    rewrite Znth_map_65 with (da := 0).
    + f_equal.
      apply circular_shift_output_z_65_rot_char; lia.
    + pose proof (Z.mod_pos_bound
        (Zlength (decimal_digits_z_65 x) - shift + i)
        (Zlength (decimal_digits_z_65 x)) ltac:(lia)).
      lia.
Qed.

Lemma problem_65_spec_z_intro : forall x shift,
  0 <= x ->
  0 <= shift ->
  problem_65_spec_z x shift (circular_shift_output_z_65 x shift).
Proof.
  intros x shift Hx Hshift.
  unfold problem_65_spec_z, problem_65_spec.
  exists (digit_values_65 (decimal_digits_z_65 x)).
  exists (digit_values_65 (circular_shift_output_z_65 x shift)).
  split.
  - apply decimal_digits_z_65_decimal. exact Hx.
  - split.
    + apply circular_shift_digits_z_65; assumption.
    + unfold digits_string.
      apply string_of_list_z_digit_values_65.
Qed.

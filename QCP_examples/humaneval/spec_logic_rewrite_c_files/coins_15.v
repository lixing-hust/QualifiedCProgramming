Load "../spec/15".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Numbers.DecimalNat.
Require Import Coq.micromega.Lia.
Require Import Recdef.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Definition ascii_of_z (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z c) (string_of_list_z rest)
  end.

Definition repeat_Z {A: Type} (a: A) (n: Z): list A :=
  repeat a (Z.to_nat n).

Lemma repeat_Z_tail : forall {A: Type} (a: A) n,
  0 <= n ->
  repeat_Z a (n + 1) = repeat_Z a n ++ [a].
Proof.
  intros A a n Hn.
  unfold repeat_Z.
  replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  rewrite <- repeat_cons.
  reflexivity.
Qed.

Lemma Zlength_repeat_Z : forall {A: Type} (a: A) n,
  0 <= n ->
  Zlength (repeat_Z a n) = n.
Proof.
  intros A a n Hn.
  unfold repeat_Z.
  rewrite Zlength_correct, repeat_length.
  lia.
Qed.

Function base_digits_z (n base : Z) {measure Z.to_nat n} : list Z :=
  if Z.leb base 1 then [48]
  else if Z.leb n 0 then [48]
  else if Z.ltb n base then [48 + n]
  else base_digits_z (n / base) base ++ [48 + (n mod base)].
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

Definition base_digits_pos_z (n base : Z) : list Z :=
  if Z.leb n 0 then [] else base_digits_z n base.

Definition decimal_digits_z (x : Z) : list Z :=
  base_digits_z x 10.

Definition decimal_uint_cons_z (d : Z) (tail : Decimal.uint) : Decimal.uint :=
  match d with
  | 0 => Decimal.D0 tail
  | 1 => Decimal.D1 tail
  | 2 => Decimal.D2 tail
  | 3 => Decimal.D3 tail
  | 4 => Decimal.D4 tail
  | 5 => Decimal.D5 tail
  | 6 => Decimal.D6 tail
  | 7 => Decimal.D7 tail
  | 8 => Decimal.D8 tail
  | 9 => Decimal.D9 tail
  | _ => Decimal.Nil
  end.

Definition decimal_uint_cons_char_z (c : Z) (tail : Decimal.uint) : Decimal.uint :=
  match c with
  | 48 => Decimal.D0 tail
  | 49 => Decimal.D1 tail
  | 50 => Decimal.D2 tail
  | 51 => Decimal.D3 tail
  | 52 => Decimal.D4 tail
  | 53 => Decimal.D5 tail
  | 54 => Decimal.D6 tail
  | 55 => Decimal.D7 tail
  | 56 => Decimal.D8 tail
  | 57 => Decimal.D9 tail
  | _ => Decimal.Nil
  end.

Fixpoint decimal_uint_of_digits_z (digits : list Z) : Decimal.uint :=
  match digits with
  | [] => Decimal.Nil
  | c :: rest => decimal_uint_cons_char_z c (decimal_uint_of_digits_z rest)
  end.

Definition decimal_char_z (d : Z) : ascii :=
  ascii_of_z (48 + d).

Lemma decimal_char_z_cases_15 : forall d,
  0 <= d <= 9 ->
  decimal_char_z d =
    match d with
    | 0 => "0"%char
    | 1 => "1"%char
    | 2 => "2"%char
    | 3 => "3"%char
    | 4 => "4"%char
    | 5 => "5"%char
    | 6 => "6"%char
    | 7 => "7"%char
    | 8 => "8"%char
    | 9 => "9"%char
    | _ => "0"%char
    end.
Proof.
  intros d Hd.
  assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/
          d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) by lia.
  repeat (destruct H as [H | H]; [subst; reflexivity |]); subst; reflexivity.
Qed.

Lemma decimal_uint_cons_acc_15 : forall d tail acc,
  0 <= d <= 9 ->
  Nat.of_uint_acc (decimal_uint_cons_z d tail) acc =
    Nat.of_uint_acc tail (acc * 10 + Z.to_nat d)%nat.
Proof.
  intros d tail acc Hd.
  assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/
          d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) by lia.
  repeat (destruct H as [H | H];
    [subst; simpl; try rewrite PeanoNat.Nat.tail_mul_spec; f_equal; lia |]);
    subst; simpl; try rewrite PeanoNat.Nat.tail_mul_spec; f_equal; lia.
Qed.

Lemma decimal_uint_cons_char_acc_15 : forall c tail acc,
  48 <= c <= 57 ->
  Nat.of_uint_acc (decimal_uint_cons_char_z c tail) acc =
    Nat.of_uint_acc tail (acc * 10 + Z.to_nat (c - 48))%nat.
Proof.
  intros c tail acc Hc.
  assert (c = 48 \/ c = 49 \/ c = 50 \/ c = 51 \/ c = 52 \/
          c = 53 \/ c = 54 \/ c = 55 \/ c = 56 \/ c = 57) by lia.
  repeat (destruct H as [H | H];
    [subst; simpl; try rewrite PeanoNat.Nat.tail_mul_spec; f_equal; lia |]);
    subst; simpl; try rewrite PeanoNat.Nat.tail_mul_spec; f_equal; lia.
Qed.

Lemma decimal_uint_of_digits_append_digit_acc_15 : forall digits d acc,
  Forall (fun c => 48 <= c <= 57) digits ->
  0 <= d <= 9 ->
  Nat.of_uint_acc (decimal_uint_of_digits_z (digits ++ [48 + d])) acc =
    (Nat.of_uint_acc (decimal_uint_of_digits_z digits) acc * 10 +
      Z.to_nat d)%nat.
Proof.
  induction digits as [|c rest IH]; intros d acc Hdigits Hd.
  - cbn [decimal_uint_of_digits_z app].
    assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/
            d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) by lia.
    repeat (destruct H as [H | H];
      [subst; simpl; try rewrite PeanoNat.Nat.tail_mul_spec; lia |]);
      subst; simpl; try rewrite PeanoNat.Nat.tail_mul_spec; lia.
  - inversion Hdigits as [|? ? Hc Hrest]; subst.
    cbn [decimal_uint_of_digits_z app].
    rewrite !decimal_uint_cons_char_acc_15 by assumption.
    rewrite (IH d (acc * 10 + Z.to_nat (c - 48))%nat) by assumption.
    lia.
Qed.

Lemma decimal_uint_of_digits_append_digit_15 : forall digits d,
  Forall (fun c => 48 <= c <= 57) digits ->
  0 <= d <= 9 ->
  Nat.of_uint (decimal_uint_of_digits_z (digits ++ [48 + d])) =
    (Nat.of_uint (decimal_uint_of_digits_z digits) * 10 + Z.to_nat d)%nat.
Proof.
  intros digits d Hdigits Hd.
  unfold Nat.of_uint.
  apply decimal_uint_of_digits_append_digit_acc_15; assumption.
Qed.

Lemma base_digits_z_chars_le_10_15 : forall n base,
  2 <= base <= 10 ->
  Forall (fun c => 48 <= c <= 57) (base_digits_z n base).
Proof.
  intros n base Hbase.
  functional induction (base_digits_z n base).
  - constructor; [lia | constructor].
  - constructor; [lia | constructor].
  - apply Z.leb_gt in e.
    apply Z.leb_gt in e0.
    apply Z.ltb_lt in e1.
    constructor; [lia | constructor].
  - apply Forall_app.
    split; [apply IHl; lia |].
    constructor; [pose proof (Z.mod_pos_bound n base ltac:(lia)); lia | constructor].
Qed.

Lemma decimal_digits_z_chars_10_15 : forall n,
  Forall (fun c => 48 <= c <= 57) (base_digits_z n 10).
Proof.
  intro n.
  apply base_digits_z_chars_le_10_15; lia.
Qed.

Lemma base_digits_z_head_nonzero_15 : forall n base,
  0 < n ->
  2 <= base ->
  exists d rest,
    base_digits_z n base = (48 + d) :: rest /\ 1 <= d <= base - 1.
Proof.
  intros n base Hn Hbase.
  functional induction (base_digits_z n base).
  - apply Z.leb_le in e. lia.
  - apply Z.leb_le in e0. lia.
  - apply Z.leb_gt in e.
    apply Z.leb_gt in e0.
    apply Z.ltb_lt in e1.
    exists n, (@nil Z). repeat split; lia.
  - assert (0 < n / base).
    { assert (1 <= n / base) by (apply Z.div_le_lower_bound; lia).
      lia. }
    destruct (IHl H ltac:(lia)) as [d [rest [Hdigits Hd]]].
    exists d, (rest ++ [48 + n mod base]).
    rewrite Hdigits.
    repeat split; lia.
Qed.

Lemma decimal_digits_z_head_nonzero_10_15 : forall n,
  0 < n ->
  exists d rest,
    base_digits_z n 10 = (48 + d) :: rest /\ 1 <= d <= 9.
Proof.
  intros n Hn.
  destruct (base_digits_z_head_nonzero_15 n 10 Hn ltac:(lia))
    as [d [rest [Hdigits Hd]]].
  exists d, rest. split; [exact Hdigits | lia].
Qed.

Lemma decimal_uint_of_digits_unorm_head_15 : forall c rest,
  49 <= c <= 57 ->
  Decimal.unorm (decimal_uint_of_digits_z (c :: rest)) =
    decimal_uint_of_digits_z (c :: rest).
Proof.
  intros c rest Hc.
  assert (c = 49 \/ c = 50 \/ c = 51 \/ c = 52 \/ c = 53 \/
          c = 54 \/ c = 55 \/ c = 56 \/ c = 57) by lia.
  repeat (destruct H as [H | H]; [subst; reflexivity |]); subst; reflexivity.
Qed.

Lemma decimal_uint_of_base_digits_unorm_10_15 : forall n,
  0 <= n ->
  Decimal.unorm (decimal_uint_of_digits_z (base_digits_z n 10)) =
    decimal_uint_of_digits_z (base_digits_z n 10).
Proof.
  intros n Hn.
  destruct (Z.eq_dec n 0) as [Hz | Hnz].
  - subst. reflexivity.
  - destruct (decimal_digits_z_head_nonzero_10_15 n ltac:(lia))
      as [d [rest [Hdigits Hd]]].
    rewrite Hdigits.
    apply decimal_uint_of_digits_unorm_head_15.
    lia.
Qed.

Lemma nil_empty_uint_of_string_digits_15 : forall digits,
  Forall (fun c => 48 <= c <= 57) digits ->
  DecimalString.NilEmpty.uint_of_string (string_of_list_z digits) =
    Some (decimal_uint_of_digits_z digits).
Proof.
  induction digits as [|c rest IH]; intros Hdigits.
  - reflexivity.
  - inversion Hdigits as [|? ? Hc Hrest]; subst.
    simpl.
    replace (ascii_of_z c) with (decimal_char_z (c - 48)).
    2:{ unfold decimal_char_z, ascii_of_z. replace (48 + (c - 48)) with c by lia.
        reflexivity. }
    rewrite decimal_char_z_cases_15 by lia.
    rewrite IH by assumption.
    assert (c = 48 \/ c = 49 \/ c = 50 \/ c = 51 \/ c = 52 \/
            c = 53 \/ c = 54 \/ c = 55 \/ c = 56 \/ c = 57) by lia.
    repeat (destruct H as [H | H]; [subst; reflexivity |]); subst; reflexivity.
Qed.

Lemma decimal_uint_of_base_digits_value_10_15 : forall n,
  0 <= n ->
  Nat.of_uint (decimal_uint_of_digits_z (base_digits_z n 10)) = Z.to_nat n.
Proof.
  intros n Hn.
  remember (Z.to_nat n) as m eqn:Hm.
  revert n Hn Hm.
  induction m as [m IH] using lt_wf_ind; intros n Hn Hm.
  rewrite base_digits_z_equation.
  replace (10 <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (Z.leb_spec n 0) as [Hn0 | Hnpos].
  - assert (n = 0) by lia. subst. reflexivity.
  - destruct (Z.ltb_spec n 10) as [Hlt | Hge].
    + assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/
              n = 6 \/ n = 7 \/ n = 8 \/ n = 9) by lia.
      repeat (destruct H as [H | H]; [subst; reflexivity |]); subst; reflexivity.
    + rewrite decimal_uint_of_digits_append_digit_15.
      * rewrite (IH (Z.to_nat (n / 10))).
        -- replace (Z.to_nat (n / 10) * 10 + Z.to_nat (n mod 10))%nat
             with (Z.to_nat ((n / 10) * 10 + n mod 10)).
           ++ replace ((n / 10) * 10 + n mod 10) with n.
              ** symmetry. exact Hm.
              ** pose proof (Z.div_mod n 10 ltac:(lia)); lia.
           ++ rewrite Z2Nat.inj_add.
              ** rewrite Z2Nat.inj_mul.
                 --- replace (Z.to_nat 10) with 10%nat by reflexivity.
                     lia.
                 --- apply Z.div_pos; lia.
                 --- lia.
              ** apply Z.mul_nonneg_nonneg.
                 --- apply Z.div_pos; lia.
                 --- lia.
              ** apply Z.mod_pos_bound; lia.
        -- rewrite Hm.
           apply Z2Nat.inj_lt.
           ++ apply Z.div_pos; lia.
           ++ lia.
           ++ apply Z.div_lt; lia.
        -- apply Z.div_pos; lia.
        -- reflexivity.
      * apply decimal_digits_z_chars_10_15.
      * pose proof (Z.mod_pos_bound n 10 ltac:(lia)); lia.
Qed.

Lemma base_digits_z_nonempty_early_15 : forall n base,
  base_digits_z n base <> [].
Proof.
  intros n base.
  functional induction (base_digits_z n base); simpl; try discriminate.
  intro Hnil.
  apply app_eq_nil in Hnil.
  destruct Hnil as [_ Hlast].
  discriminate Hlast.
Qed.

Lemma string_of_list_z_decimal_digits_z_15 : forall n,
  0 <= n ->
  string_of_list_z (decimal_digits_z n) = string_of_nat (Z.to_nat n).
Proof.
  intros n Hn.
  unfold decimal_digits_z, string_of_nat.
  set (digits := base_digits_z n 10).
  set (u := decimal_uint_of_digits_z digits).
  assert (Hparse :
    DecimalString.NilZero.uint_of_string (string_of_list_z digits) = Some u).
  { subst u digits.
    unfold DecimalString.NilZero.uint_of_string.
    destruct (base_digits_z n 10) as [|c rest] eqn:Hdigits.
    - exfalso. apply (base_digits_z_nonempty_early_15 n 10). exact Hdigits.
    - change (DecimalString.NilEmpty.uint_of_string (string_of_list_z (c :: rest)) =
        Some (decimal_uint_of_digits_z (c :: rest))).
      apply nil_empty_uint_of_string_digits_15.
      rewrite <- Hdigits. apply decimal_digits_z_chars_10_15. }
  pose proof (DecimalString.NilZero.sus _ _ Hparse) as Hsus.
  assert (Hu : u = Nat.to_uint (Z.to_nat n)).
  { subst u digits.
    rewrite <- decimal_uint_of_base_digits_unorm_10_15 by lia.
    rewrite <- Unsigned.to_of.
    f_equal.
    apply decimal_uint_of_base_digits_value_10_15; lia. }
  rewrite <- Hu.
  symmetry.
  exact Hsus.
Qed.

Lemma decimal_digits_z_zero_15 :
  decimal_digits_z 0 = [48].
Proof.
  reflexivity.
Qed.

Definition base_count_state_z (orig base t digits : Z) : Prop :=
  0 <= t /\
  0 <= digits /\
  digits + Zlength (base_digits_pos_z t base) =
    Zlength (base_digits_pos_z orig base).

Definition base_fill_state_z
  (orig base x digits : Z) (suffix : list Z) : Prop :=
  0 <= x /\
  0 <= digits /\
  digits = Zlength (base_digits_pos_z x base) /\
  base_digits_z orig base = base_digits_pos_z x base ++ suffix.

Definition base_fill_full_state_z
  (orig base x digits : Z) (out_l : list Z) : Prop :=
  exists suffix,
    base_fill_state_z orig base x digits suffix /\
    out_l = repeat_Z 0 digits ++ suffix.

Lemma base_digits_z_step : forall n base,
  0 < n ->
  2 <= base ->
  base <= n ->
  base_digits_z n base =
    base_digits_z (n / base) base ++ [48 + n mod base].
Proof.
  intros n base Hn Hbase Hle.
  rewrite base_digits_z_equation.
  replace (base <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
  replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  replace (n <? base) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

Lemma base_digits_pos_step : forall n base,
  0 < n ->
  2 <= base ->
  base_digits_pos_z n base =
    base_digits_pos_z (n / base) base ++ [48 + n mod base].
Proof.
  intros n base Hn Hbase.
  unfold base_digits_pos_z at 1.
  replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (Z.ltb_spec n base) as [Hlt | Hge].
  - rewrite base_digits_z_equation.
    replace (base <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
    replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
    replace (n <? base) with true by (symmetry; apply Z.ltb_lt; lia).
    unfold base_digits_pos_z.
    replace (n / base <=? 0) with true.
    + rewrite app_nil_l. rewrite Z.mod_small by lia. reflexivity.
    + symmetry. apply Z.leb_le.
      rewrite Z.div_small by lia. lia.
  - rewrite base_digits_z_step by lia.
    unfold base_digits_pos_z at 1.
    assert (0 < n / base).
    { assert (1 <= n / base) by (apply Z.div_le_lower_bound; lia).
      lia. }
    replace (n / base <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
    reflexivity.
Qed.

Lemma base_digits_z_length_pos_le : forall n base,
  0 < n ->
  2 <= base ->
  Zlength (base_digits_z n base) <= n.
Proof.
  intros n base Hn Hbase.
  functional induction (base_digits_z n base).
  - lia.
  - apply Z.leb_le in e0. lia.
  - rewrite Zlength_cons, Zlength_nil.
    lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    assert (0 < n / base).
    { assert (1 <= n / base) by (apply Z.div_le_lower_bound; lia). lia. }
    pose proof (IHl ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt n base ltac:(lia) ltac:(lia)).
    lia.
Qed.

Lemma base_digits_z_nonempty : forall n base,
  base_digits_z n base <> [].
Proof.
  intros n base.
  functional induction (base_digits_z n base); simpl; try discriminate.
  intro H.
  apply app_eq_nil in H.
  destruct H as [_ Hnil].
  discriminate Hnil.
Qed.

Lemma decimal_digits_z_length_pos_15 : forall x,
  1 <= Zlength (decimal_digits_z x).
Proof.
  intros x.
  unfold decimal_digits_z.
  destruct (base_digits_z x 10) eqn:Hdigits.
  - exfalso. apply (base_digits_z_nonempty x 10). exact Hdigits.
  - rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
Qed.

Lemma base_count_state_init : forall x base,
  0 < x ->
  base_count_state_z x base x 0.
Proof.
  intros x base Hx.
  unfold base_count_state_z.
  lia.
Qed.

Lemma base_count_state_step : forall orig base t digits,
  0 < t ->
  2 <= base ->
  base_count_state_z orig base t digits ->
  base_count_state_z orig base (t / base) (digits + 1).
Proof.
  intros orig base t digits Ht Hbase [Ht0 [Hd Hlen]].
  unfold base_count_state_z.
  split; [apply Z.div_pos; lia | split; [lia |]].
  rewrite (base_digits_pos_step t base) in Hlen by lia.
  rewrite Zlength_app in Hlen.
  change (Zlength [48 + t mod base]) with 1 in Hlen.
  lia.
Qed.

Lemma base_count_state_done : forall orig base digits,
  0 < orig ->
  base_count_state_z orig base 0 digits ->
  digits = Zlength (base_digits_z orig base).
Proof.
  intros orig base digits Horig [_ [Hd Hlen]].
  unfold base_digits_pos_z in Hlen.
  replace (0 <=? 0) with true in Hlen by (symmetry; apply Z.leb_le; lia).
  replace (orig <=? 0) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
  change (Zlength (@nil Z)) with 0 in Hlen.
  lia.
Qed.

Lemma base_fill_state_init : forall orig base,
  0 < orig ->
  base_fill_state_z orig base orig (Zlength (base_digits_z orig base)) [].
Proof.
  intros orig base Horig.
  unfold base_fill_state_z, base_digits_pos_z.
  replace (orig <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  repeat split; try lia.
  - apply Zlength_nonneg.
  - rewrite app_nil_r. reflexivity.
Qed.

Lemma base_fill_state_step : forall orig base x digits suffix,
  0 < x ->
  2 <= base ->
  base_fill_state_z orig base x digits suffix ->
  base_fill_state_z orig base (x / base) (digits - 1)
    ((48 + x mod base) :: suffix).
Proof.
  intros orig base x digits suffix Hx Hbase [Hx0 [Hd [Hdigits Hsplit]]].
  unfold base_fill_state_z.
  rewrite (base_digits_pos_step x base) in Hsplit by lia.
  rewrite (base_digits_pos_step x base) in Hdigits by lia.
  rewrite Zlength_app in Hdigits.
  change (Zlength [48 + x mod base]) with 1 in Hdigits.
  assert (Hdiv_nonneg : 0 <= x / base) by (apply Z.div_pos; lia).
  assert (Hprefix_nonneg : 0 <= Zlength (base_digits_pos_z (x / base) base))
    by apply Zlength_nonneg.
  split; [exact Hdiv_nonneg | split; [lia | split; [|]]].
  - rewrite Hdigits. lia.
  - rewrite Hsplit.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma base_fill_full_state_init : forall orig base,
  0 < orig ->
  base_fill_full_state_z orig base orig
    (Zlength (base_digits_z orig base))
    (repeat_Z 0 (Zlength (base_digits_z orig base))).
Proof.
  intros orig base Horig.
  exists [].
  split.
  - apply base_fill_state_init; lia.
  - rewrite app_nil_r. reflexivity.
Qed.

Lemma base_fill_full_state_done : forall orig base out_l,
  base_fill_full_state_z orig base 0 0 out_l ->
  out_l = base_digits_z orig base.
Proof.
  intros orig base out_l [suffix [[_ [_ [Hdigits Hsplit]]] Hout]].
  unfold base_digits_pos_z in Hdigits, Hsplit.
  replace (0 <=? 0) with true in Hdigits by (symmetry; apply Z.leb_le; lia).
  replace (0 <=? 0) with true in Hsplit by (symmetry; apply Z.leb_le; lia).
  change (Zlength (@nil Z)) with 0 in Hdigits.
  simpl in Hsplit.
  rewrite Hout.
  unfold repeat_Z.
  simpl.
  symmetry.
  exact Hsplit.
Qed.

Lemma replace_Znth_boundary_app : forall {A: Type} (prefix tail : list A) x y,
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

Lemma replace_Znth_repeat_suffix : forall d suffix v,
  0 <= d ->
  replace_Znth d v (repeat_Z 0 (d + 1) ++ suffix) =
  repeat_Z 0 d ++ v :: suffix.
Proof.
  intros d suffix v Hd.
  rewrite repeat_Z_tail by lia.
  rewrite <- app_assoc.
  change ([0] ++ suffix) with (0 :: suffix).
  assert (Hlen : Zlength (repeat_Z 0 d) = d)
    by (rewrite Zlength_repeat_Z; lia).
  rewrite <- Hlen at 1.
  rewrite replace_Znth_boundary_app.
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

Definition problem_15_pre_z (n : Z) : Prop :=
  problem_15_pre (Z.to_nat n).

Definition problem_15_spec_z (n : Z) (output : list Z) : Prop :=
  problem_15_spec (Z.to_nat n) (string_of_list_z output).

Definition decimal_count_state_z (orig t digits : Z) : Prop :=
  base_count_state_z orig 10 t digits.

Definition decimal_fill_full_state_z
  (orig x digits : Z) (out_l : list Z) : Prop :=
  base_fill_full_state_z orig 10 x digits out_l.

Definition sequence_indices_z (count : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat count)).

Definition sequence_piece_z (i : Z) : list Z :=
  if Z.eqb i 0 then decimal_digits_z 0 else [32] ++ decimal_digits_z i.

Definition string_sequence_prefix_z (count : Z) : list Z :=
  List.concat (map sequence_piece_z (sequence_indices_z count)).

Definition sequence_len_z (n : Z) : Z :=
  Zlength (string_sequence_prefix_z (n + 1)).

Lemma sequence_indices_succ_15 : forall i,
  0 <= i ->
  sequence_indices_z (i + 1) = sequence_indices_z i ++ [i].
Proof.
  intros i Hi.
  unfold sequence_indices_z.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite seq_S.
  rewrite map_app.
  simpl.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma sequence_piece_pos_len_15 : forall i,
  1 <= i ->
  Zlength (sequence_piece_z i) = 1 + Zlength (decimal_digits_z i).
Proof.
  intros i Hi.
  unfold sequence_piece_z.
  replace (i =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite Zlength_app.
  change (Zlength [32]) with 1.
  lia.
Qed.

Lemma sequence_piece_pos_15 : forall i,
  1 <= i ->
  sequence_piece_z i = [32] ++ decimal_digits_z i.
Proof.
  intros i Hi.
  unfold sequence_piece_z.
  replace (i =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  reflexivity.
Qed.

Lemma string_sequence_prefix_succ_15 : forall i,
  0 <= i ->
  string_sequence_prefix_z (i + 1) =
    string_sequence_prefix_z i ++ sequence_piece_z i.
Proof.
  intros i Hi.
  unfold string_sequence_prefix_z.
  rewrite sequence_indices_succ_15 by lia.
  rewrite map_app.
  rewrite concat_app.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma string_sequence_prefix_succ_len_15 : forall i,
  0 <= i ->
  Zlength (string_sequence_prefix_z (i + 1)) =
    Zlength (string_sequence_prefix_z i) + Zlength (sequence_piece_z i).
Proof.
  intros i Hi.
  rewrite string_sequence_prefix_succ_15 by lia.
  rewrite Zlength_app.
  reflexivity.
Qed.

Lemma string_sequence_prefix_len_le_15 : forall a b,
  0 <= a ->
  a <= b ->
  Zlength (string_sequence_prefix_z a) <=
    Zlength (string_sequence_prefix_z b).
Proof.
  intros a b Ha Hab.
  unfold string_sequence_prefix_z, sequence_indices_z.
  replace (Z.to_nat b) with
    (Z.to_nat a + Z.to_nat (b - a))%nat.
  - rewrite seq_app.
    rewrite map_app.
    rewrite map_app.
    rewrite concat_app.
    rewrite Zlength_app.
    pose proof (Zlength_nonneg
      (List.concat (map sequence_piece_z
        (map Z.of_nat (seq (0 + Z.to_nat a) (Z.to_nat (b - a))))))).
    lia.
  - rewrite <- Z2Nat.inj_add by lia.
    replace (a + (b - a)) with b by lia.
    reflexivity.
Qed.

Lemma string_sequence_next_len_le_15 : forall n i,
  0 <= n ->
  1 <= i ->
  i <= n ->
  Zlength (string_sequence_prefix_z i) + 1 +
    Zlength (decimal_digits_z i) <= sequence_len_z n.
Proof.
  intros n i Hn Hi Hin.
  unfold sequence_len_z.
  replace (Zlength (string_sequence_prefix_z i) + 1 +
    Zlength (decimal_digits_z i)) with
    (Zlength (string_sequence_prefix_z i) +
      (1 + Zlength (decimal_digits_z i))) by lia.
  rewrite <- (sequence_piece_pos_len_15 i) by lia.
  rewrite <- (string_sequence_prefix_succ_len_15 i) by lia.
  apply string_sequence_prefix_len_le_15; lia.
Qed.

Lemma string_sequence_prefix_one_15 :
  string_sequence_prefix_z 1 = [48].
Proof.
  unfold string_sequence_prefix_z.
  replace 1 with (0 + 1) by lia.
  rewrite sequence_indices_succ_15 by lia.
  simpl.
  apply decimal_digits_z_zero_15.
Qed.

Lemma string_sequence_prefix_one_len_15 :
  Zlength (string_sequence_prefix_z 1) = 1.
Proof.
  rewrite string_sequence_prefix_one_15.
  reflexivity.
Qed.

Lemma sequence_len_pos_15 : forall n,
  0 <= n ->
  1 <= sequence_len_z n.
Proof.
  intros n Hn.
  unfold sequence_len_z.
  rewrite <- string_sequence_prefix_one_len_15.
  apply (string_sequence_prefix_len_le_15 1 (n + 1)); lia.
Qed.

Lemma string_of_list_z_app_15 : forall l1 l2,
  string_of_list_z (l1 ++ l2) =
    String.append (string_of_list_z l1) (string_of_list_z l2).
Proof.
  induction l1 as [|c rest IH]; intros l2.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma string_append_assoc_15 : forall a b c,
  String.append (String.append a b) c =
    String.append a (String.append b c).
Proof.
  induction a as [|ch rest IH]; intros b c.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma string_concat_snoc_nonempty_15 : forall sep l x,
  l <> [] ->
  String.concat sep (l ++ [x]) =
    String.append (String.append (String.concat sep l) sep) x.
Proof.
  intros sep l.
  induction l as [|a l IH]; intros x Hne.
  - contradiction.
  - destruct l as [|b l].
    + cbn [app String.concat]. rewrite string_append_assoc_15. reflexivity.
    + change (String.concat sep ((a :: b :: l) ++ [x]))
        with (String.append a
          (String.append sep (String.concat sep ((b :: l) ++ [x])))).
      change (String.concat sep (a :: b :: l))
        with (String.append a (String.append sep (String.concat sep (b :: l)))).
      rewrite IH by discriminate.
      repeat rewrite string_append_assoc_15.
      reflexivity.
Qed.

Lemma string_of_list_z_sequence_piece_pos_15 : forall i,
  1 <= i ->
  string_of_list_z (sequence_piece_z i) =
    String.append " " (string_of_nat (Z.to_nat i)).
Proof.
  intros i Hi.
  rewrite sequence_piece_pos_15 by lia.
  rewrite string_of_list_z_app_15.
  simpl.
  rewrite string_of_list_z_decimal_digits_z_15 by lia.
  reflexivity.
Qed.

Lemma string_of_list_z_sequence_prefix_nat_15 : forall m,
  string_of_list_z (string_sequence_prefix_z (Z.of_nat (S m))) =
    String.concat " " (map string_of_nat (seq 0 (S m))).
Proof.
  induction m as [|m IH].
  - change (Z.of_nat (S 0)) with 1.
    rewrite string_sequence_prefix_one_15.
    reflexivity.
  - replace (Z.of_nat (S (S m))) with (Z.of_nat (S m) + 1) by lia.
    rewrite string_sequence_prefix_succ_15 by lia.
    rewrite string_of_list_z_app_15.
    rewrite IH.
    rewrite string_of_list_z_sequence_piece_pos_15 by lia.
    rewrite Nat2Z.id.
    replace (seq 0 (S (S m))) with (seq 0 (S m) ++ [S m])
      by (symmetry; apply seq_S).
    rewrite map_app.
    cbn [map].
    rewrite string_concat_snoc_nonempty_15.
    + repeat rewrite string_append_assoc_15. reflexivity.
    + destruct m; discriminate.
Qed.

Lemma problem_15_spec_z_sequence_prefix_15 : forall n,
  0 <= n ->
  problem_15_spec_z n (string_sequence_prefix_z (n + 1)).
Proof.
  intros n Hn.
  unfold problem_15_spec_z, problem_15_spec.
  replace (n + 1) with (Z.of_nat (S (Z.to_nat n))) by lia.
  apply string_of_list_z_sequence_prefix_nat_15.
Qed.

Lemma decimal_count_state_init_15 : forall x,
  0 < x ->
  decimal_count_state_z x x 0.
Proof.
  intros x Hx.
  unfold decimal_count_state_z.
  apply base_count_state_init; lia.
Qed.

Lemma decimal_count_state_step_15 : forall orig t digits,
  0 < t ->
  decimal_count_state_z orig t digits ->
  decimal_count_state_z orig (t / 10) (digits + 1).
Proof.
  intros orig t digits Ht Hstate.
  unfold decimal_count_state_z in *.
  apply base_count_state_step; lia || exact Hstate.
Qed.

Lemma decimal_count_state_done_15 : forall orig digits,
  0 < orig ->
  decimal_count_state_z orig 0 digits ->
  digits = Zlength (decimal_digits_z orig).
Proof.
  intros orig digits Horig Hstate.
  unfold decimal_count_state_z in Hstate.
  apply base_count_state_done with (base := 10); lia || exact Hstate.
Qed.

Lemma decimal_count_state_next_lt_int_15 : forall orig t digits,
  0 < orig ->
  orig < INT_MAX ->
  0 < t ->
  decimal_count_state_z orig t digits ->
  digits + 1 < INT_MAX.
Proof.
  intros orig t digits Horig Horig_int Ht Hstate.
  unfold decimal_count_state_z, base_count_state_z in Hstate.
  destruct Hstate as [_ [_ Hlen]].
  unfold base_digits_pos_z in Hlen.
  replace (orig <=? 0) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
  replace (t <=? 0) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
  assert (Ht_len_pos : 1 <= Zlength (base_digits_z t 10)).
  { destruct (base_digits_z t 10) eqn:Hdigits.
    - exfalso. apply (base_digits_z_nonempty t 10). exact Hdigits.
    - rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia. }
  pose proof (base_digits_z_length_pos_le orig 10 Horig ltac:(lia)).
  lia.
Qed.

Lemma decimal_fill_full_state_init_15 : forall orig,
  0 < orig ->
  decimal_fill_full_state_z orig orig
    (Zlength (decimal_digits_z orig))
    (repeat_Z 0 (Zlength (decimal_digits_z orig))).
Proof.
  intros orig Horig.
  unfold decimal_fill_full_state_z.
  apply base_fill_full_state_init; lia.
Qed.

Lemma decimal_fill_full_state_step_15 : forall orig x digits out_l,
  0 < x ->
  0 <= digits ->
  decimal_fill_full_state_z orig x (digits + 1) out_l ->
  decimal_fill_full_state_z orig (x / 10) digits
    (replace_Znth digits (signed_last_nbits (48 + x mod 10) 8) out_l).
Proof.
  intros orig x digits out_l Hx Hdigits Hstate.
  unfold decimal_fill_full_state_z in *.
  apply base_fill_full_state_step_10; assumption.
Qed.

Lemma decimal_fill_full_state_done_15 : forall orig out_l,
  0 < orig ->
  decimal_fill_full_state_z orig 0 0 out_l ->
  out_l = decimal_digits_z orig.
Proof.
  intros orig out_l Horig Hstate.
  unfold decimal_fill_full_state_z in Hstate.
  apply base_fill_full_state_done; lia || exact Hstate.
Qed.

Lemma decimal_fill_full_state_fill_pos_15 : forall orig x fill out_l,
  0 < x ->
  decimal_fill_full_state_z orig x fill out_l ->
  1 <= fill.
Proof.
  intros orig x fill out_l Hx [suffix [[_ [_ [Hfill _]]] _]].
  unfold base_digits_pos_z in Hfill.
  replace (x <=? 0) with false in Hfill by (symmetry; apply Z.leb_gt; lia).
  rewrite Hfill.
  apply decimal_digits_z_length_pos_15.
Qed.

Lemma decimal_fill_full_state_zero_done_15 : forall orig fill out_l,
  decimal_fill_full_state_z orig 0 fill out_l ->
  out_l = decimal_digits_z orig.
Proof.
  intros orig fill out_l Hstate.
  unfold decimal_fill_full_state_z in Hstate.
  destruct Hstate as [suffix [[_ [_ [Hfill Hsplit]]] Hout]].
  unfold base_digits_pos_z in Hfill, Hsplit.
  replace (0 <=? 0) with true in Hfill by (symmetry; apply Z.leb_le; lia).
  replace (0 <=? 0) with true in Hsplit by (symmetry; apply Z.leb_le; lia).
  change (Zlength (@nil Z)) with 0 in Hfill.
  assert (fill = 0) by lia; subst fill.
  simpl in Hsplit.
  rewrite Hout.
  unfold repeat_Z.
  simpl.
  symmetry.
  exact Hsplit.
Qed.

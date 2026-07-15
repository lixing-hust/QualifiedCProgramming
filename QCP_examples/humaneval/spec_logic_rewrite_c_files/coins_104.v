Load "../spec/104".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.DecimalNat.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
Require Import Recdef.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_104_pre_z (l : list Z) : Prop :=
  problem_104_pre (map Z.to_nat l).

Definition problem_104_spec_z (input output : list Z) : Prop :=
  problem_104_spec (map Z.to_nat input) (map Z.to_nat output).

Definition unique_digits_safe_104 (l : list Z) : Prop :=
  Forall (fun n => 0 < n < INT_MAX) l.

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then True else Sorted le (map Z.to_nat l).

Definition only_odd_digits_z_104 (n : Z) : Prop :=
  has_only_odd_digits_bool (Z.to_nat n) = true.

Definition has_even_digit_z_104 (n : Z) : Prop :=
  has_only_odd_digits_bool (Z.to_nat n) = false.

Fixpoint filter_odd_digits_z_104 (l : list Z) : list Z :=
  match l with
  | nil => nil
  | h :: t =>
      if has_only_odd_digits_bool (Z.to_nat h) then
        h :: filter_odd_digits_z_104 t
      else
        filter_odd_digits_z_104 t
  end.

Definition unique_digits_prefix_104 (input : list Z) (i : Z) (output : list Z) : Prop :=
  0 <= i <= Zlength input /\
  output = filter_odd_digits_z_104 (sublist 0 i input).

Function base_digits_z_104 (n base : Z) {measure Z.to_nat n} : list Z :=
  if Z.leb base 1 then [48]
  else if Z.leb n 0 then [48]
  else if Z.ltb n base then [48 + n]
  else base_digits_z_104 (n / base) base ++ [48 + (n mod base)].
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

Definition base_digits_pos_z_104 (n base : Z) : list Z :=
  if Z.leb n 0 then [] else base_digits_z_104 n base.

Definition decimal_digit_char_to_nat_104 (c : Z) : nat :=
  Z.to_nat (c - 48).

Definition decimal_uint_cons_char_z_104 (c : Z) (tail : Decimal.uint) : Decimal.uint :=
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

Fixpoint decimal_uint_of_digits_z_104 (digits : list Z) : Decimal.uint :=
  match digits with
  | [] => Decimal.Nil
  | c :: rest => decimal_uint_cons_char_z_104 c (decimal_uint_of_digits_z_104 rest)
  end.

Definition decimal_chars_all_odd_104 (digits : list Z) : bool :=
  forallb (fun c => Z.odd (c - 48)) digits.

Definition decimal_chars_to_nat_digits_104 (digits : list Z) : list nat :=
  map decimal_digit_char_to_nat_104 digits.

Lemma decimal_uint_cons_char_acc_104 : forall c tail acc,
  48 <= c <= 57 ->
  Nat.of_uint_acc (decimal_uint_cons_char_z_104 c tail) acc =
    Nat.of_uint_acc tail (acc * 10 + Z.to_nat (c - 48))%nat.
Proof.
  intros c tail acc Hc.
  assert (c = 48 \/ c = 49 \/ c = 50 \/ c = 51 \/ c = 52 \/
          c = 53 \/ c = 54 \/ c = 55 \/ c = 56 \/ c = 57) by lia.
  repeat (destruct H as [H | H];
    [subst; simpl; try rewrite PeanoNat.Nat.tail_mul_spec; f_equal; lia |]);
    subst; simpl; try rewrite PeanoNat.Nat.tail_mul_spec; f_equal; lia.
Qed.

Lemma decimal_uint_of_digits_append_digit_acc_104 : forall digits d acc,
  Forall (fun c => 48 <= c <= 57) digits ->
  0 <= d <= 9 ->
  Nat.of_uint_acc (decimal_uint_of_digits_z_104 (digits ++ [48 + d])) acc =
    (Nat.of_uint_acc (decimal_uint_of_digits_z_104 digits) acc * 10 +
      Z.to_nat d)%nat.
Proof.
  induction digits as [|c rest IH]; intros d acc Hdigits Hd.
  - cbn [decimal_uint_of_digits_z_104 app].
    assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/
            d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) by lia.
    repeat (destruct H as [H | H];
      [subst; simpl; try rewrite PeanoNat.Nat.tail_mul_spec; lia |]);
      subst; simpl; try rewrite PeanoNat.Nat.tail_mul_spec; lia.
  - inversion Hdigits as [|? ? Hc Hrest]; subst.
    cbn [decimal_uint_of_digits_z_104 app].
    rewrite !decimal_uint_cons_char_acc_104 by assumption.
    rewrite (IH d (acc * 10 + Z.to_nat (c - 48))%nat) by assumption.
    lia.
Qed.

Lemma decimal_uint_of_digits_append_digit_104 : forall digits d,
  Forall (fun c => 48 <= c <= 57) digits ->
  0 <= d <= 9 ->
  Nat.of_uint (decimal_uint_of_digits_z_104 (digits ++ [48 + d])) =
    (Nat.of_uint (decimal_uint_of_digits_z_104 digits) * 10 + Z.to_nat d)%nat.
Proof.
  intros digits d Hdigits Hd.
  unfold Nat.of_uint.
  apply decimal_uint_of_digits_append_digit_acc_104; assumption.
Qed.

Lemma base_digits_z_chars_le_10_104 : forall n base,
  2 <= base <= 10 ->
  Forall (fun c => 48 <= c <= 57) (base_digits_z_104 n base).
Proof.
  intros n base Hbase.
  functional induction (base_digits_z_104 n base).
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

Lemma decimal_digits_z_chars_104 : forall n,
  Forall (fun c => 48 <= c <= 57) (base_digits_z_104 n 10).
Proof.
  intro n.
  apply base_digits_z_chars_le_10_104; lia.
Qed.

Lemma base_digits_z_104_nonempty : forall n base,
  base_digits_z_104 n base <> [].
Proof.
  intros n base.
  functional induction (base_digits_z_104 n base); simpl; try discriminate.
  intro Hnil.
  apply app_eq_nil in Hnil.
  destruct Hnil as [_ Hlast].
  discriminate Hlast.
Qed.

Lemma base_digits_z_head_nonzero_104 : forall n base,
  0 < n ->
  2 <= base ->
  exists d rest,
    base_digits_z_104 n base = (48 + d) :: rest /\ 1 <= d <= base - 1.
Proof.
  intros n base Hn Hbase.
  functional induction (base_digits_z_104 n base).
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

Lemma decimal_uint_of_digits_unorm_head_104 : forall c rest,
  49 <= c <= 57 ->
  Decimal.unorm (decimal_uint_of_digits_z_104 (c :: rest)) =
    decimal_uint_of_digits_z_104 (c :: rest).
Proof.
  intros c rest Hc.
  assert (c = 49 \/ c = 50 \/ c = 51 \/ c = 52 \/ c = 53 \/
          c = 54 \/ c = 55 \/ c = 56 \/ c = 57) by lia.
  repeat (destruct H as [H | H]; [subst; reflexivity |]); subst; reflexivity.
Qed.

Lemma decimal_uint_of_base_digits_unorm_104 : forall n,
  0 <= n ->
  Decimal.unorm (decimal_uint_of_digits_z_104 (base_digits_z_104 n 10)) =
    decimal_uint_of_digits_z_104 (base_digits_z_104 n 10).
Proof.
  intros n Hn.
  destruct (Z.eq_dec n 0) as [Hz | Hnz].
  - subst. reflexivity.
  - destruct (base_digits_z_head_nonzero_104 n 10 ltac:(lia) ltac:(lia))
      as [d [rest [Hdigits Hd]]].
    rewrite Hdigits.
    apply decimal_uint_of_digits_unorm_head_104.
    lia.
Qed.

Lemma decimal_uint_of_base_digits_value_104 : forall n,
  0 <= n ->
  Nat.of_uint (decimal_uint_of_digits_z_104 (base_digits_z_104 n 10)) = Z.to_nat n.
Proof.
  intros n Hn.
  remember (Z.to_nat n) as m eqn:Hm.
  revert n Hn Hm.
  induction m as [m IH] using lt_wf_ind; intros n Hn Hm.
  rewrite base_digits_z_104_equation.
  replace (10 <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (Z.leb_spec n 0) as [Hn0 | Hnpos].
  - assert (n = 0) by lia. subst. reflexivity.
  - destruct (Z.ltb_spec n 10) as [Hlt | Hge].
    + assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/
              n = 6 \/ n = 7 \/ n = 8 \/ n = 9) by lia.
      repeat (destruct H as [H | H]; [subst; reflexivity |]); subst; reflexivity.
    + rewrite decimal_uint_of_digits_append_digit_104.
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
      * apply decimal_digits_z_chars_104.
      * pose proof (Z.mod_pos_bound n 10 ltac:(lia)); lia.
Qed.

Lemma decimal_uint_digits_of_digits_z_104 : forall digits,
  Forall (fun c => 48 <= c <= 57) digits ->
  decimal_uint_digits (decimal_uint_of_digits_z_104 digits) =
    decimal_chars_to_nat_digits_104 digits.
Proof.
  induction digits as [|c rest IH]; intros Hdigits.
  - reflexivity.
  - inversion Hdigits as [|? ? Hc Hrest]; subst.
    assert (c = 48 \/ c = 49 \/ c = 50 \/ c = 51 \/ c = 52 \/
            c = 53 \/ c = 54 \/ c = 55 \/ c = 56 \/ c = 57) by lia.
    repeat (destruct H as [H | H];
      [subst; simpl; rewrite IH by assumption; reflexivity |]);
      subst; simpl; rewrite IH by assumption; reflexivity.
Qed.

Lemma decimal_nat_digits_base_digits_104 : forall n,
  0 <= n ->
  decimal_nat_digits (Z.to_nat n) =
    decimal_chars_to_nat_digits_104 (base_digits_z_104 n 10).
Proof.
  intros n Hn.
  unfold decimal_nat_digits.
  assert (Hu :
    Nat.to_uint (Z.to_nat n) =
    decimal_uint_of_digits_z_104 (base_digits_z_104 n 10)).
  { rewrite <- decimal_uint_of_base_digits_unorm_104 by lia.
    rewrite <- Unsigned.to_of.
    f_equal.
    symmetry. apply decimal_uint_of_base_digits_value_104; lia. }
  rewrite Hu.
  rewrite decimal_uint_digits_of_digits_z_104 by apply decimal_digits_z_chars_104.
  destruct (decimal_chars_to_nat_digits_104 (base_digits_z_104 n 10)) eqn:Hdigits.
  - exfalso.
    apply map_eq_nil in Hdigits.
    exact (base_digits_z_104_nonempty n 10 Hdigits).
  - reflexivity.
Qed.

Lemma decimal_chars_all_odd_nat_digits_104 : forall digits,
  Forall (fun c => 48 <= c <= 57) digits ->
  forallb Nat.odd (decimal_chars_to_nat_digits_104 digits) =
    decimal_chars_all_odd_104 digits.
Proof.
  induction digits as [|c rest IH]; intros Hdigits.
  - reflexivity.
  - inversion Hdigits as [|? ? Hc Hrest]; subst.
    simpl.
    rewrite IH by assumption.
    assert (0 <= c - 48 <= 9) by lia.
    unfold decimal_digit_char_to_nat_104.
    replace (Nat.odd (Z.to_nat (c - 48))) with (Z.odd (c - 48)).
    + reflexivity.
    + assert (c - 48 = 0 \/ c - 48 = 1 \/ c - 48 = 2 \/ c - 48 = 3 \/
              c - 48 = 4 \/ c - 48 = 5 \/ c - 48 = 6 \/
              c - 48 = 7 \/ c - 48 = 8 \/ c - 48 = 9) by lia.
      repeat (destruct H0 as [H0 | H0]; [rewrite H0; reflexivity |]);
        rewrite H0; reflexivity.
Qed.

Lemma has_only_odd_digits_bool_base_digits_104 : forall n,
  0 <= n ->
  has_only_odd_digits_bool (Z.to_nat n) =
    decimal_chars_all_odd_104 (base_digits_z_104 n 10).
Proof.
  intros n Hn.
  unfold has_only_odd_digits_bool.
  rewrite decimal_nat_digits_base_digits_104 by lia.
  apply decimal_chars_all_odd_nat_digits_104.
  apply decimal_digits_z_chars_104.
Qed.

Lemma base_digits_pos_step_104 : forall n base,
  0 < n ->
  2 <= base ->
  base_digits_pos_z_104 n base =
    base_digits_pos_z_104 (n / base) base ++ [48 + n mod base].
Proof.
  intros n base Hn Hbase.
  unfold base_digits_pos_z_104 at 1.
  replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite base_digits_z_104_equation.
  replace (base <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
  replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (Z.ltb_spec n base) as [Hlt | Hge].
  - unfold base_digits_pos_z_104.
    replace (n / base <=? 0) with true.
    + rewrite app_nil_l.
      replace (n mod base) with n by (symmetry; apply Z.mod_small; lia).
      reflexivity.
    + symmetry. apply Z.leb_le.
      pose proof (Z.div_small n base ltac:(lia)).
      lia.
  - unfold base_digits_pos_z_104.
    replace (n / base <=? 0) with false.
    + reflexivity.
    + symmetry. apply Z.leb_gt.
      assert (1 <= n / base) by (apply Z.div_le_lower_bound; lia).
      lia.
Qed.

Lemma decimal_chars_all_odd_cons_even_104 : forall d suffix,
  d mod 2 = 0 ->
  decimal_chars_all_odd_104 ((48 + d) :: suffix) = false.
Proof.
  intros d suffix Heven.
  unfold decimal_chars_all_odd_104.
  cbn [forallb].
  replace (48 + d - 48) with d by lia.
  assert (Z.odd d = false).
  { destruct (Z.odd d) eqn:Hodd; [| reflexivity].
    rewrite Zmod_odd in Heven.
    rewrite Hodd in Heven.
    lia. }
  rewrite H. reflexivity.
Qed.

Lemma decimal_chars_all_odd_cons_odd_104 : forall d suffix,
  d mod 2 <> 0 ->
  0 <= d < 10 ->
  decimal_chars_all_odd_104 suffix = true ->
  decimal_chars_all_odd_104 ((48 + d) :: suffix) = true.
Proof.
  intros d suffix Hodd Hd Hsuffix.
  unfold decimal_chars_all_odd_104 in *.
  cbn [forallb].
  replace (48 + d - 48) with d by lia.
  assert (Z.odd d = true).
  { assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/
            d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) by lia.
    repeat (destruct H as [H | H];
      [subst; cbn in Hodd; try lia; reflexivity |]);
      subst; cbn in Hodd; try lia; reflexivity. }
  rewrite H, Hsuffix. reflexivity.
Qed.

Definition odd_digit_scan_state_104 (original : Z) (num : Z) (u : Z) : Prop :=
  exists suffix,
    0 < original /\
    0 <= num /\
    num <= original /\
    base_digits_z_104 original 10 =
      base_digits_pos_z_104 num 10 ++ suffix /\
    (u = 0 \/ u = 1) /\
    (u = 1 -> decimal_chars_all_odd_104 suffix = true) /\
    (u = 0 -> decimal_chars_all_odd_104 suffix = false).

Lemma odd_scan_init_104 :
  forall original,
    0 < original ->
    odd_digit_scan_state_104 original original 1.
Proof.
  intros original Horig.
  exists (@nil Z).
  unfold base_digits_pos_z_104.
  replace (original <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  repeat split; try lia.
  rewrite app_nil_r. reflexivity.
Qed.

Lemma odd_scan_even_104 :
  forall original num,
    odd_digit_scan_state_104 original num 1 ->
    0 < num ->
    num mod 2 = 0 ->
    odd_digit_scan_state_104 original (num / 10) 0.
Proof.
  intros original num Hstate Hnum Heven.
  destruct Hstate as [suffix [Horig [Hnum0 [Hle [Hdigits [Hu [Hodd _]]]]]]].
  exists ((48 + num mod 10) :: suffix).
  rewrite base_digits_pos_step_104 in Hdigits by lia.
  repeat split.
  - exact Horig.
  - apply Z.div_pos; lia.
  - assert (num / 10 <= num).
    { apply Z.div_le_upper_bound; lia. }
    lia.
  - rewrite Hdigits. rewrite <- app_assoc. reflexivity.
  - left. reflexivity.
  - intros Hbad; lia.
  - intros _. apply decimal_chars_all_odd_cons_even_104.
    assert (Hdivides : (2 | 10)%Z) by (exists 5; reflexivity).
    pose proof (Znumtheory.Zmod_div_mod 2 10 num ltac:(lia) ltac:(lia) Hdivides)
      as Hmod.
    rewrite <- Hmod.
    exact Heven.
Qed.

Lemma odd_scan_odd_104 :
  forall original num,
    odd_digit_scan_state_104 original num 1 ->
    0 < num ->
    num mod 2 <> 0 ->
    odd_digit_scan_state_104 original (num / 10) 1.
Proof.
  intros original num Hstate Hnum Hoddnum.
  destruct Hstate as [suffix [Horig [Hnum0 [Hle [Hdigits [Hu [Hsuffix _]]]]]]].
  exists ((48 + num mod 10) :: suffix).
  rewrite base_digits_pos_step_104 in Hdigits by lia.
  repeat split.
  - exact Horig.
  - apply Z.div_pos; lia.
  - assert (num / 10 <= num).
    { apply Z.div_le_upper_bound; lia. }
    lia.
  - rewrite Hdigits. rewrite <- app_assoc. reflexivity.
  - right. reflexivity.
  - intros _. apply decimal_chars_all_odd_cons_odd_104.
    + assert (Hdivides : (2 | 10)%Z) by (exists 5; reflexivity).
      pose proof (Znumtheory.Zmod_div_mod 2 10 num ltac:(lia) ltac:(lia) Hdivides)
        as Hmod.
      rewrite <- Hmod.
      exact Hoddnum.
    + pose proof (Z.mod_pos_bound num 10 ltac:(lia)); lia.
    + apply Hsuffix; reflexivity.
  - intros Hbad; lia.
Qed.

Lemma odd_digit_scan_state_104_accept : forall original num,
  odd_digit_scan_state_104 original num 1 ->
  num <= 0 ->
  only_odd_digits_z_104 original.
Proof.
  intros original num Hstate Hnum.
  destruct Hstate as [suffix [Horig [Hnum0 [Hle [Hdigits [Hu [Hsuffix _]]]]]]].
  assert (num = 0) by lia. subst num.
  unfold only_odd_digits_z_104.
  rewrite has_only_odd_digits_bool_base_digits_104 by lia.
  unfold base_digits_pos_z_104 in Hdigits.
  replace (0 <=? 0) with true in Hdigits by reflexivity.
  simpl in Hdigits.
  rewrite Hdigits.
  apply Hsuffix. reflexivity.
Qed.

Lemma odd_digit_scan_state_104_reject : forall original num,
  odd_digit_scan_state_104 original num 0 ->
  has_even_digit_z_104 original.
Proof.
  intros original num Hstate.
  destruct Hstate as [suffix [Horig [Hnum0 [Hle [Hdigits [Hu [_ Hsuffix]]]]]]].
  unfold has_even_digit_z_104.
  rewrite has_only_odd_digits_bool_base_digits_104 by lia.
  rewrite Hdigits.
  unfold decimal_chars_all_odd_104 in *.
  rewrite forallb_app.
  rewrite Hsuffix by reflexivity.
  destruct (forallb (fun c : Z => Z.odd (c - 48))
    (base_digits_pos_z_104 num 10)); reflexivity.
Qed.

Lemma unique_digits_safe_104_Znth : forall l i,
  unique_digits_safe_104 l ->
  0 <= i < Zlength l ->
  0 < Znth i l 0 < INT_MAX.
Proof.
  intros l i Hsafe Hi.
  unfold unique_digits_safe_104 in Hsafe.
  rewrite Forall_forall in Hsafe.
  apply Hsafe.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma odd_digit_scan_state_104_bounds : forall original num u,
  0 <= original ->
  odd_digit_scan_state_104 original num u ->
  0 <= num <= original /\ (u = 0 \/ u = 1).
Proof.
  intros original num u Horig Hstate.
  destruct Hstate as [suffix [Hpos [Hnum0 [Hle [Hdigits [Hu _]]]]]].
  split; lia.
Qed.

Lemma odd_scan_even_quot_104 : forall original num,
  odd_digit_scan_state_104 original num 1 ->
  0 < num ->
  num % 2 = 0 ->
  odd_digit_scan_state_104 original (num ÷ 10) 0.
Proof.
  intros original num Hstate Hpos Heven.
  replace (num ÷ 10) with (num / 10).
  - apply odd_scan_even_104 with (num := num); try assumption.
    rewrite Z.rem_mod_nonneg in Heven by lia.
    exact Heven.
  - symmetry. apply Z.quot_div_nonneg; lia.
Qed.

Lemma odd_scan_odd_quot_104 : forall original num,
  odd_digit_scan_state_104 original num 1 ->
  0 < num ->
  num % 2 <> 0 ->
  odd_digit_scan_state_104 original (num ÷ 10) 1.
Proof.
  intros original num Hstate Hpos Hodd.
  replace (num ÷ 10) with (num / 10).
  - apply odd_scan_odd_104 with (num := num); try assumption.
    intro Hmod.
    apply Hodd.
    rewrite Z.rem_mod_nonneg by lia.
    exact Hmod.
  - symmetry. apply Z.quot_div_nonneg; lia.
Qed.

Lemma filter_odd_digits_z_104_snoc_true : forall l x,
  has_only_odd_digits_bool (Z.to_nat x) = true ->
  filter_odd_digits_z_104 (l ++ [x]) = filter_odd_digits_z_104 l ++ [x].
Proof.
  induction l; intros x Hx; simpl.
  - rewrite Hx. reflexivity.
  - destruct (has_only_odd_digits_bool (Z.to_nat a)); simpl; rewrite IHl; auto.
Qed.

Lemma filter_odd_digits_z_104_snoc_false : forall l x,
  has_only_odd_digits_bool (Z.to_nat x) = false ->
  filter_odd_digits_z_104 (l ++ [x]) = filter_odd_digits_z_104 l.
Proof.
  induction l; intros x Hx; simpl.
  - rewrite Hx. reflexivity.
  - destruct (has_only_odd_digits_bool (Z.to_nat a)); simpl; rewrite IHl; auto.
Qed.

Lemma map_filter_odd_digits_z_104 : forall l,
  map Z.to_nat (filter_odd_digits_z_104 l) =
  filter_odd_digits (map Z.to_nat l).
Proof.
  induction l; simpl.
  - reflexivity.
  - destruct (has_only_odd_digits_bool (Z.to_nat a)); simpl; rewrite IHl; reflexivity.
Qed.

Lemma unique_digits_prefix_104_add_step : forall input i output,
  0 <= i < Zlength input ->
  unique_digits_prefix_104 input i output ->
  only_odd_digits_z_104 (Znth i input 0) ->
  unique_digits_prefix_104 input (i + 1) (output ++ [Znth i input 0]).
Proof.
  intros input i output Hi Hprefix Hodd.
  unfold unique_digits_prefix_104 in *.
  destruct Hprefix as [Hbounds Hout].
  split.
  - lia.
  - rewrite Hout.
    rewrite (sublist_split 0 (i + 1) i input)
      by (try rewrite <- Zlength_correct; lia).
    rewrite (sublist_single 0 i input) by lia.
    symmetry.
    apply filter_odd_digits_z_104_snoc_true.
    exact Hodd.
Qed.

Lemma unique_digits_prefix_104_skip_step : forall input i output,
  0 <= i < Zlength input ->
  unique_digits_prefix_104 input i output ->
  has_even_digit_z_104 (Znth i input 0) ->
  unique_digits_prefix_104 input (i + 1) output.
Proof.
  intros input i output Hi Hprefix Heven.
  unfold unique_digits_prefix_104 in *.
  destruct Hprefix as [Hbounds Hout].
  split.
  - lia.
  - rewrite Hout.
    rewrite (sublist_split 0 (i + 1) i input)
      by (try rewrite <- Zlength_correct; lia).
    rewrite (sublist_single 0 i input) by lia.
    symmetry.
    apply filter_odd_digits_z_104_snoc_false.
    exact Heven.
Qed.

Lemma problem_104_spec_z_of_sorted_104 : forall input filtered output,
  unique_digits_prefix_104 input (Zlength input) filtered ->
  sorted_int_list_by 1 output ->
  Permutation filtered output ->
  problem_104_spec_z input output.
Proof.
  intros input filtered output Hprefix Hsorted Hperm.
  unfold problem_104_spec_z, problem_104_spec.
  split.
  - unfold unique_digits_prefix_104 in Hprefix.
    destruct Hprefix as [Hbounds Hfiltered].
    replace (filter_odd_digits (map Z.to_nat input)) with (map Z.to_nat filtered).
    + symmetry. apply Permutation_map. exact Hperm.
    + rewrite Hfiltered.
      rewrite sublist_self by lia.
      rewrite map_filter_odd_digits_z_104.
      reflexivity.
  - unfold sorted_int_list_by in Hsorted.
    change (Z.eqb 1 0) with false in Hsorted.
    exact Hsorted.
Qed.

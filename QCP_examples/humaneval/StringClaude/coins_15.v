Load "../spec/15".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.
From SimpleC.EE Require Import string_bridge.
From SimpleC.EE Require Import coins_44.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_15_pre_z (n : Z) : Prop :=
  problem_15_pre (Z.to_nat n).

Definition problem_15_spec_z (n : Z) (output : list Z) : Prop :=
  problem_15_spec (Z.to_nat n) (string_of_list_z output).

Fixpoint sequence_prefix_nat (count : nat) : list Z :=
  match count with
  | O => []
  | S O => base_digits_z 0 10
  | S count' => sequence_prefix_nat count' ++ [32] ++ base_digits_z (Z.of_nat count') 10
  end.

Definition sequence_prefix_z (i : Z) : list Z :=
  sequence_prefix_nat (Z.to_nat i).

Definition sequence_output_z (n : Z) : list Z :=
  sequence_prefix_z (n + 1).

Definition sequence_output_bound_z (n : Z) : Prop :=
  Zlength (sequence_output_z n) + 1 <= 12 * (n + 1) + 1.

Lemma sequence_prefix_nat_length_mono : forall a b,
  (a <= b)%nat ->
  Zlength (sequence_prefix_nat a) <= Zlength (sequence_prefix_nat b).
Proof.
  intros a b Hab.
  repeat rewrite Zlength_correct.
  apply Nat2Z.inj_le.
  revert a Hab.
  induction b as [| b IH]; intros a Hab.
  - assert (a = O) by lia. subst. lia.
  - destruct (Nat.eq_dec a (S b)) as [Heq | Hneq].
    + subst. lia.
    + assert (Ha : (a <= b)%nat) by lia.
      specialize (IH a Ha).
      assert (Hstep : (List.length (sequence_prefix_nat b) <=
                       List.length (sequence_prefix_nat (S b)))%nat).
      { destruct b as [| b']; simpl.
        - destruct (base_digits_z 0 10); simpl; lia.
        - repeat rewrite app_length. simpl.
          lia. }
      lia.
Qed.

Lemma sequence_prefix_z_length_le_output : forall i n,
  0 <= i <= n + 1 ->
  Zlength (sequence_prefix_z i) <= Zlength (sequence_output_z n).
Proof.
  intros i n Hi.
  unfold sequence_prefix_z, sequence_output_z.
  apply sequence_prefix_nat_length_mono.
  lia.
Qed.

Lemma base_count_state_digits_le_orig_15 : forall orig t digits,
  0 < orig ->
  base_count_state_z orig 10 t digits ->
  digits <= orig.
Proof.
  intros orig t digits Horig [_ [Hdigits Hlen]].
  unfold base_digits_pos_z in Hlen.
  replace (Z.leb orig 0) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
  assert (Htail : 0 <= Zlength (if Z.leb t 0 then [] else base_digits_z t 10))
    by apply Zlength_nonneg.
  pose proof (base_digits_z_length_pos_le orig 10 Horig ltac:(lia)) as Hle.
  lia.
Qed.

Lemma base_digits_z_len_le_orig_15 : forall orig,
  0 < orig ->
  Zlength (base_digits_z orig 10) <= orig.
Proof.
  intros orig Horig.
  apply base_digits_z_length_pos_le; lia.
Qed.

Lemma base_fill_full_state_step_rem_15 : forall orig x digits out_l,
  0 < x ->
  0 <= digits ->
  base_fill_full_state_z orig 10 x (digits + 1) out_l ->
  base_fill_full_state_z orig 10 (x / 10) digits
    (replace_Znth digits (signed_last_nbits (48 + Z.rem x 10) 8) out_l).
Proof.
  intros orig x digits out_l Hx Hdigits [suffix [Hstate Hout]].
  replace (Z.rem x 10) with (x mod 10)
    by (symmetry; apply Z.rem_mod_nonneg; lia).
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

Lemma sequence_prefix_z_1 :
  sequence_prefix_z 1 = [48].
Proof.
  unfold sequence_prefix_z.
  simpl.
  rewrite base_digits_z_zero by lia.
  reflexivity.
Qed.

Lemma sequence_prefix_z_step : forall i,
  1 <= i ->
  sequence_prefix_z (i + 1) =
    sequence_prefix_z i ++ [32] ++ base_digits_z i 10.
Proof.
  intros i Hi.
  unfold sequence_prefix_z.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (Z.to_nat i) as [| k] eqn:Hk; [lia |].
  assert (i = Z.of_nat (S k)) as -> by lia.
  simpl.
  reflexivity.
Qed.

Lemma sequence_prefix_step_length_bound_15 : forall n i out_l k digits cap,
  cap = 12 * (n + 1) + 1 ->
  sequence_output_bound_z n ->
  1 <= i <= n ->
  k = Zlength out_l ->
  out_l = sequence_prefix_z i ->
  digits = Zlength (base_digits_z i 10) ->
  k + 1 + digits < cap.
Proof.
  intros n i out_l k digits cap Hcap Hbound Hi Hk Hout Hdigits.
  pose proof (sequence_prefix_z_length_le_output (i + 1) n ltac:(lia)) as Hle.
  rewrite sequence_prefix_z_step in Hle by lia.
  rewrite <- Hout in Hle.
  rewrite !Zlength_app, !Zlength_cons, !Zlength_nil in Hle.
  unfold sequence_output_bound_z in Hbound.
  lia.
Qed.

Lemma sequence_output_z_unfold : forall n,
  0 <= n ->
  sequence_output_z n = sequence_prefix_z (n + 1).
Proof.
  intros n _.
  reflexivity.
Qed.

Lemma string_append_assoc_15 : forall a b c,
  ((a ++ b) ++ c = a ++ (b ++ c))%string.
Proof.
  induction a; intros b c; simpl.
  - reflexivity.
  - rewrite IHa. reflexivity.
Qed.

Lemma string_of_list_z_app_15 : forall a b,
  string_of_list_z (a ++ b) =
  (string_of_list_z a ++ string_of_list_z b)%string.
Proof.
  induction a; intros b; simpl.
  - reflexivity.
  - rewrite IHa. reflexivity.
Qed.

Lemma ascii_of_nat_ascii_of_z_15 : forall n,
  Ascii.ascii_of_nat n = ascii_of_z (Z.of_nat n).
Proof.
  intros n.
  unfold ascii_of_z.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

Fixpoint digits_rev_aux_15 (m fuel : nat) : list ascii :=
  match fuel with
  | O => []
  | S fuel' =>
      if Nat.ltb m 10 then [Ascii.ascii_of_nat (48 + m)]
      else Ascii.ascii_of_nat (48 + (Nat.modulo m 10)) ::
           digits_rev_aux_15 (Nat.div m 10) fuel'
  end.

Definition string_of_nat_model_15 (n : nat) : string :=
  match n with
  | O => "0"
  | _ =>
      fold_right (fun a acc => String a acc) EmptyString
        (rev (digits_rev_aux_15 n n))
  end.

Lemma string_of_nat_model_15_eq : forall n,
  string_of_nat n = string_of_nat_model_15 n.
Proof.
  destruct n; reflexivity.
Qed.

Lemma digits_rev_aux_15_correct : forall fuel m,
  (0 < m)%nat ->
  (m <= fuel)%nat ->
  rev (digits_rev_aux_15 m fuel) =
  map ascii_of_z (base_digits_z (Z.of_nat m) 10).
Proof.
  induction fuel as [| fuel IH]; intros m Hm Hfuel.
  - lia.
  - simpl.
    destruct (Nat.ltb_spec m 10) as [Hlt | Hge].
    + rewrite base_digits_z_small by lia.
      simpl.
      f_equal.
      symmetry. apply ascii_of_z_eq_ascii_of_nat.
      change (48 + Z.of_nat m = Z.of_nat (48 + m)).
      rewrite Nat2Z.inj_add. reflexivity.
    + rewrite base_digits_z_step by lia.
      rewrite map_app.
      simpl.
      simpl.
      f_equal.
      * replace (Z.of_nat m / 10) with (Z.of_nat (Nat.div m 10)).
        2:{ rewrite Nat2Z.inj_div; lia. }
        apply IH.
        -- apply Nat.div_str_pos; lia.
        -- apply Nat.div_le_upper_bound; lia.
      * f_equal.
        symmetry. apply ascii_of_z_eq_ascii_of_nat.
        change (48 + Z.of_nat m mod 10 =
                Z.of_nat (48 + Nat.modulo m 10)).
        rewrite Nat2Z.inj_add.
        rewrite Nat2Z.inj_mod by lia.
        reflexivity.
Qed.

Lemma string_of_list_z_base_digits_10 : forall n,
  string_of_list_z (base_digits_z (Z.of_nat n) 10) = string_of_nat n.
Proof.
  intros n.
  rewrite string_of_nat_model_15_eq.
  destruct n as [| n].
  - unfold string_of_nat_model_15.
    rewrite base_digits_z_zero by lia.
    reflexivity.
  - unfold string_of_nat_model_15.
    rewrite digits_rev_aux_15_correct by lia.
    induction (base_digits_z (Z.of_nat (S n)) 10) as [| c rest IH]; simpl.
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.

Fixpoint sequence_range_string_15 (start count : nat) : string :=
  match count with
  | O => EmptyString
  | S O => string_of_nat start
  | S count' =>
      (sequence_range_string_15 start count' ++
       " " ++ string_of_nat (start + count')%nat)%string
  end.

Lemma sequence_range_string_15_append_last : forall start limit,
  ((seq_string start limit) ++ " " ++
   string_of_nat (start + S limit))%string =
  seq_string start (S limit).
Proof.
  intros start limit.
  revert start.
  induction limit as [| limit IH]; intros start.
  - cbn [seq_string].
    replace (start + 1)%nat with (S start) by lia.
    reflexivity.
  - change (seq_string start (S limit) ++ " " ++
              string_of_nat (start + S (S limit)) =
            seq_string start (S (S limit)))%string.
    change (seq_string start (S limit)) with
      (string_of_nat start ++ " " ++ seq_string (S start) limit)%string.
    change (seq_string start (S (S limit))) with
      (string_of_nat start ++ " " ++ seq_string (S start) (S limit))%string.
    replace (start + S (S limit))%nat with (S start + S limit)%nat by lia.
    rewrite <- (IH (S start)).
    repeat rewrite string_append_assoc_15.
    reflexivity.
Qed.

Lemma sequence_range_string_15_correct : forall start limit,
  sequence_range_string_15 start (S limit) = seq_string start limit.
Proof.
  intros start limit.
  revert start.
  induction limit as [| limit IH]; intros start.
  - cbn [seq_string sequence_range_string_15]. reflexivity.
  - change (sequence_range_string_15 start (S limit) ++
              " " ++ string_of_nat (start + S limit) =
            seq_string start (S limit))%string.
    rewrite IH.
    apply sequence_range_string_15_append_last.
Qed.

Lemma sequence_prefix_string_15_correct : forall count,
  string_of_list_z (sequence_prefix_nat count) =
  sequence_range_string_15 0 count.
Proof.
  induction count as [| count IH].
  - reflexivity.
  - destruct count as [| count].
    + simpl.
      reflexivity.
    + change (string_of_list_z
                (sequence_prefix_nat (S count) ++ [32] ++
                 base_digits_z (Z.of_nat (S count)) 10) =
              (sequence_range_string_15 0 (S count) ++
               " " ++ string_of_nat (0 + S count))%string).
      rewrite !string_of_list_z_app_15.
      rewrite IH.
      rewrite string_of_list_z_base_digits_10.
      reflexivity.
Qed.

Lemma problem_15_spec_z_sequence_output : forall n,
  0 <= n ->
  problem_15_spec_z n (sequence_output_z n).
Proof.
  intros n Hn.
  unfold problem_15_spec_z, problem_15_spec, string_sequence_impl.
  unfold sequence_output_z, sequence_prefix_z.
  replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  rewrite sequence_prefix_string_15_correct.
  apply sequence_range_string_15_correct.
Qed.

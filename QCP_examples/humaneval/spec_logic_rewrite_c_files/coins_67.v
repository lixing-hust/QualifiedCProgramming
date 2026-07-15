Load "../spec/67".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition int_max_67 : Z := 2147483647.

Definition ascii_of_z_67 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_67 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_67 c) (string_of_list_z_67 rest)
  end.

Definition string_length (s : list Z) : Z :=
  Zlength s.

Definition problem_67_pre_z (s : list Z) (n : Z) : Prop :=
  problem_67_pre (string_of_list_z_67 s) (Z.to_nat n).

Definition problem_67_spec_z (s : list Z) (n ret : Z) : Prop :=
  problem_67_spec (string_of_list_z_67 s) (Z.to_nat n) (Z.to_nat ret).

Definition is_digit_z_67 (c : Z) : Prop :=
  48 <= c <= 57.

Definition digit_value_z_67 (c : Z) : Z :=
  c - 48.

Definition bounded_parse_value_67 (z : Z) : Prop :=
  -1 <= z <= int_max_67.

Definition fruit_scan_state_67
    (s : list Z) (n i num1 num2 cur : Z) : Prop :=
  0 <= n <= int_max_67 /\
  0 <= i <= Zlength s /\
  bounded_parse_value_67 num1 /\
  bounded_parse_value_67 num2 /\
  bounded_parse_value_67 cur /\
  (i < Zlength s -> 0 <= Znth i (c_string s) 0 <= 127) /\
  (i < Zlength s -> is_digit_z_67 (Znth i (c_string s) 0) ->
    0 <= (if Z.ltb cur 0 then 0 else cur) * 10 +
          digit_value_z_67 (Znth i (c_string s) 0) <= int_max_67).

Record fruit_safe_input_67 (s : list Z) (n : Z) : Prop := {
  fruit_safe_initial_field_67 :
    fruit_scan_state_67 s n 0 (-1) (-1) (-1);
  fruit_safe_digit_reset_field_67 : forall i num1 num2 cur,
    fruit_scan_state_67 s n i num1 num2 cur ->
    i < Zlength s ->
    is_digit_z_67 (Znth i (c_string s) 0) ->
    cur < 0 ->
    fruit_scan_state_67 s n i num1 num2 0;
  fruit_safe_digit_accum_field_67 : forall i num1 num2 cur,
    fruit_scan_state_67 s n i num1 num2 cur ->
    i < Zlength s ->
    is_digit_z_67 (Znth i (c_string s) 0) ->
    0 <= cur ->
    fruit_scan_state_67 s n (i + 1) num1 num2
      (cur * 10 + digit_value_z_67 (Znth i (c_string s) 0));
  fruit_safe_nondigit_skip_field_67 : forall i num1 num2 cur,
    fruit_scan_state_67 s n i num1 num2 cur ->
    i < Zlength s ->
    ~ is_digit_z_67 (Znth i (c_string s) 0) ->
    cur < 0 ->
    fruit_scan_state_67 s n (i + 1) num1 num2 cur;
  fruit_safe_nondigit_commit_first_field_67 : forall i num1 num2 cur,
    fruit_scan_state_67 s n i num1 num2 cur ->
    i < Zlength s ->
    ~ is_digit_z_67 (Znth i (c_string s) 0) ->
    0 <= cur ->
    num1 < 0 ->
    fruit_scan_state_67 s n (i + 1) cur num2 (-1);
  fruit_safe_nondigit_commit_second_field_67 : forall i num1 num2 cur,
    fruit_scan_state_67 s n i num1 num2 cur ->
    i < Zlength s ->
    ~ is_digit_z_67 (Znth i (c_string s) 0) ->
    0 <= cur ->
    0 <= num1 ->
    num2 < 0 ->
    fruit_scan_state_67 s n (i + 1) num1 cur (-1);
  fruit_safe_nondigit_drop_extra_field_67 : forall i num1 num2 cur,
    fruit_scan_state_67 s n i num1 num2 cur ->
    i < Zlength s ->
    ~ is_digit_z_67 (Znth i (c_string s) 0) ->
    0 <= cur ->
    0 <= num1 ->
    0 <= num2 ->
    fruit_scan_state_67 s n (i + 1) num1 num2 (-1);
  fruit_safe_tail_commit_first_field_67 : forall num1 num2 cur,
    fruit_scan_state_67 s n (Zlength s) num1 num2 cur ->
    0 <= cur ->
    num1 < 0 ->
    fruit_scan_state_67 s n (Zlength s) cur num2 (-1);
  fruit_safe_tail_commit_second_field_67 : forall num1 num2 cur,
    fruit_scan_state_67 s n (Zlength s) num1 num2 cur ->
    0 <= cur ->
    0 <= num1 ->
    num2 < 0 ->
    fruit_scan_state_67 s n (Zlength s) num1 cur (-1);
  fruit_safe_tail_drop_extra_field_67 : forall num1 num2 cur,
    fruit_scan_state_67 s n (Zlength s) num1 num2 cur ->
    0 <= cur ->
    0 <= num1 ->
    0 <= num2 ->
    fruit_scan_state_67 s n (Zlength s) num1 num2 (-1);
  fruit_safe_default_num1_zero_field_67 : forall num1 num2 cur,
    fruit_scan_state_67 s n (Zlength s) num1 num2 cur ->
    num1 < 0 ->
    fruit_scan_state_67 s n (Zlength s) 0 num2 cur;
  fruit_safe_default_num2_zero_field_67 : forall num1 num2 cur,
    fruit_scan_state_67 s n (Zlength s) num1 num2 cur ->
    num2 < 0 ->
    fruit_scan_state_67 s n (Zlength s) num1 0 cur;
  fruit_safe_final_spec_field_67 : forall num1 num2 cur,
    fruit_scan_state_67 s n (Zlength s) num1 num2 cur ->
    0 <= num1 ->
    0 <= num2 ->
    0 <= n - num1 - num2 <= int_max_67 /\
    problem_67_spec_z s n (n - num1 - num2)
}.

Lemma fruit_scan_initial_67 : forall s n,
  fruit_safe_input_67 s n ->
  fruit_scan_state_67 s n 0 (-1) (-1) (-1).
Proof.
  intros s n Hsafe.
  apply fruit_safe_initial_field_67; exact Hsafe.
Qed.

Lemma fruit_digit_reset_67 : forall s n i num1 num2 cur,
  fruit_safe_input_67 s n ->
  fruit_scan_state_67 s n i num1 num2 cur ->
  i < Zlength s ->
  is_digit_z_67 (Znth i (c_string s) 0) ->
  cur < 0 ->
  fruit_scan_state_67 s n i num1 num2 0.
Proof.
  intros s n i num1 num2 cur Hsafe Hstate Hi Hdigit Hcur.
  eapply fruit_safe_digit_reset_field_67; eauto.
Qed.

Lemma fruit_digit_accum_67 : forall s n i num1 num2 cur,
  fruit_safe_input_67 s n ->
  fruit_scan_state_67 s n i num1 num2 cur ->
  i < Zlength s ->
  is_digit_z_67 (Znth i (c_string s) 0) ->
  0 <= cur ->
  fruit_scan_state_67 s n (i + 1) num1 num2
    (cur * 10 + digit_value_z_67 (Znth i (c_string s) 0)).
Proof.
  intros s n i num1 num2 cur Hsafe Hstate Hi Hdigit Hcur.
  eapply fruit_safe_digit_accum_field_67; eauto.
Qed.

Lemma fruit_nondigit_skip_67 : forall s n i num1 num2 cur,
  fruit_safe_input_67 s n ->
  fruit_scan_state_67 s n i num1 num2 cur ->
  i < Zlength s ->
  ~ is_digit_z_67 (Znth i (c_string s) 0) ->
  cur < 0 ->
  fruit_scan_state_67 s n (i + 1) num1 num2 cur.
Proof.
  intros s n i num1 num2 cur Hsafe Hstate Hi Hnondigit Hcur.
  eapply fruit_safe_nondigit_skip_field_67; eauto.
Qed.

Lemma fruit_nondigit_commit_first_67 : forall s n i num1 num2 cur,
  fruit_safe_input_67 s n ->
  fruit_scan_state_67 s n i num1 num2 cur ->
  i < Zlength s ->
  ~ is_digit_z_67 (Znth i (c_string s) 0) ->
  0 <= cur ->
  num1 < 0 ->
  fruit_scan_state_67 s n (i + 1) cur num2 (-1).
Proof.
  intros s n i num1 num2 cur Hsafe Hstate Hi Hnondigit Hcur Hnum1.
  eapply fruit_safe_nondigit_commit_first_field_67; eauto.
Qed.

Lemma fruit_nondigit_commit_second_67 : forall s n i num1 num2 cur,
  fruit_safe_input_67 s n ->
  fruit_scan_state_67 s n i num1 num2 cur ->
  i < Zlength s ->
  ~ is_digit_z_67 (Znth i (c_string s) 0) ->
  0 <= cur ->
  0 <= num1 ->
  num2 < 0 ->
  fruit_scan_state_67 s n (i + 1) num1 cur (-1).
Proof.
  intros s n i num1 num2 cur Hsafe Hstate Hi Hnondigit Hcur Hnum1 Hnum2.
  eapply fruit_safe_nondigit_commit_second_field_67; eauto.
Qed.

Lemma fruit_nondigit_drop_extra_67 : forall s n i num1 num2 cur,
  fruit_safe_input_67 s n ->
  fruit_scan_state_67 s n i num1 num2 cur ->
  i < Zlength s ->
  ~ is_digit_z_67 (Znth i (c_string s) 0) ->
  0 <= cur ->
  0 <= num1 ->
  0 <= num2 ->
  fruit_scan_state_67 s n (i + 1) num1 num2 (-1).
Proof.
  intros s n i num1 num2 cur Hsafe Hstate Hi Hnondigit Hcur Hnum1 Hnum2.
  eapply fruit_safe_nondigit_drop_extra_field_67; eauto.
Qed.

Lemma fruit_tail_no_cur_67 : forall s n num1 num2 cur,
  fruit_safe_input_67 s n ->
  fruit_scan_state_67 s n (Zlength s) num1 num2 cur ->
  cur < 0 ->
  fruit_scan_state_67 s n (Zlength s) num1 num2 cur.
Proof.
  intros; assumption.
Qed.

Lemma fruit_tail_commit_first_67 : forall s n num1 num2 cur,
  fruit_safe_input_67 s n ->
  fruit_scan_state_67 s n (Zlength s) num1 num2 cur ->
  0 <= cur ->
  num1 < 0 ->
  fruit_scan_state_67 s n (Zlength s) cur num2 (-1).
Proof.
  intros s n num1 num2 cur Hsafe Hstate Hcur Hnum1.
  eapply fruit_safe_tail_commit_first_field_67; eauto.
Qed.

Lemma fruit_tail_commit_second_67 : forall s n num1 num2 cur,
  fruit_safe_input_67 s n ->
  fruit_scan_state_67 s n (Zlength s) num1 num2 cur ->
  0 <= cur ->
  0 <= num1 ->
  num2 < 0 ->
  fruit_scan_state_67 s n (Zlength s) num1 cur (-1).
Proof.
  intros s n num1 num2 cur Hsafe Hstate Hcur Hnum1 Hnum2.
  eapply fruit_safe_tail_commit_second_field_67; eauto.
Qed.

Lemma fruit_tail_drop_extra_67 : forall s n num1 num2 cur,
  fruit_safe_input_67 s n ->
  fruit_scan_state_67 s n (Zlength s) num1 num2 cur ->
  0 <= cur ->
  0 <= num1 ->
  0 <= num2 ->
  fruit_scan_state_67 s n (Zlength s) num1 num2 (-1).
Proof.
  intros s n num1 num2 cur Hsafe Hstate Hcur Hnum1 Hnum2.
  eapply fruit_safe_tail_drop_extra_field_67; eauto.
Qed.

Lemma fruit_default_num1_zero_67 : forall s n num1 num2 cur,
  fruit_safe_input_67 s n ->
  fruit_scan_state_67 s n (Zlength s) num1 num2 cur ->
  num1 < 0 ->
  fruit_scan_state_67 s n (Zlength s) 0 num2 cur.
Proof.
  intros s n num1 num2 cur Hsafe Hstate Hnum1.
  eapply fruit_safe_default_num1_zero_field_67; eauto.
Qed.

Lemma fruit_default_num1_keep_67 : forall s n num1 num2 cur,
  fruit_safe_input_67 s n ->
  fruit_scan_state_67 s n (Zlength s) num1 num2 cur ->
  0 <= num1 ->
  fruit_scan_state_67 s n (Zlength s) num1 num2 cur.
Proof.
  intros; assumption.
Qed.

Lemma fruit_default_num2_zero_67 : forall s n num1 num2 cur,
  fruit_safe_input_67 s n ->
  fruit_scan_state_67 s n (Zlength s) num1 num2 cur ->
  num2 < 0 ->
  fruit_scan_state_67 s n (Zlength s) num1 0 cur.
Proof.
  intros s n num1 num2 cur Hsafe Hstate Hnum2.
  eapply fruit_safe_default_num2_zero_field_67; eauto.
Qed.

Lemma fruit_default_num2_keep_67 : forall s n num1 num2 cur,
  fruit_safe_input_67 s n ->
  fruit_scan_state_67 s n (Zlength s) num1 num2 cur ->
  0 <= num2 ->
  fruit_scan_state_67 s n (Zlength s) num1 num2 cur.
Proof.
  intros; assumption.
Qed.

Lemma fruit_final_spec_67 : forall s n num1 num2 cur,
  fruit_safe_input_67 s n ->
  fruit_scan_state_67 s n (Zlength s) num1 num2 cur ->
  0 <= num1 ->
  0 <= num2 ->
  0 <= n - num1 - num2 <= int_max_67 /\
  problem_67_spec_z s n (n - num1 - num2).
Proof.
  intros s n num1 num2 cur Hsafe Hstate Hnum1 Hnum2.
  eapply fruit_safe_final_spec_field_67; eauto.
Qed.

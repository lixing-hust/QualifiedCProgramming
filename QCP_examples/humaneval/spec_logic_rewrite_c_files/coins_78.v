Load "../spec/78".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib Mem SeparationLogic.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Parameter LitMap : string -> addr.

Definition ascii_of_z_78 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_78 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_78 c) (string_of_list_z_78 rest)
  end.

Definition problem_78_pre_z (s : list Z) : Prop :=
  problem_78_pre (string_of_list_z_78 s).

Definition problem_78_spec_z (s : list Z) (output : Z) : Prop :=
  problem_78_spec (string_of_list_z_78 s) (Z.to_nat output).

Definition key_literal_78 : string := "2357BD"%string.

Definition all_key_literals_78 : list string :=
  [key_literal_78].

Definition key_payload_78 : list Z :=
  [50; 51; 53; 55; 66; 68].

Definition key_ptr_78 (LM : string -> Z) : Z :=
  LM key_literal_78.

Definition key_payload_safe_78 : Prop :=
  string_lib.valid_string key_payload_78 /\
  all_ascii key_payload_78 /\
  string_length key_payload_78 < INT_MAX.

Definition key_literal_heap_78 (LM : string -> Z) : Assertion :=
  string_lib.store_string (key_ptr_78 LM) key_payload_78 **
  GlobalStrings_missing LM all_key_literals_78.

Definition is_prime_hex_z_78 (c : Z) : bool :=
  is_prime_hex_digit (ascii_of_z_78 c).

Definition prime_hex_code_78 (c : Z) : Prop :=
  is_prime_hex_z_78 c = true.

Fixpoint count_prime_hex_list_z_78 (l : list Z) : Z :=
  match l with
  | [] => 0
  | c :: rest =>
      (if is_prime_hex_z_78 c then 1 else 0) +
      count_prime_hex_list_z_78 rest
  end.

Definition hex_count_upto_78 (i : Z) (s : list Z) : Z :=
  count_prime_hex_list_z_78 (firstn (Z.to_nat i) (c_string s)).

Definition hex_count_state_78 (s : list Z) (i count : Z) : Prop :=
  0 <= i <= string_length s /\
  count = hex_count_upto_78 i s /\
  0 <= count <= i.

Definition hex_hit_step_78 (s : list Z) (i count : Z) : Prop :=
  0 <= i < string_length s /\
  prime_hex_code_78 (Znth i (c_string s) 0) /\
  hex_count_state_78 s (i + 1) count.

Definition hex_miss_step_78 (s : list Z) (i count : Z) : Prop :=
  0 <= i < string_length s /\
  ~ prime_hex_code_78 (Znth i (c_string s) 0) /\
  hex_count_state_78 s (i + 1) count.

Definition hex_final_78 (s : list Z) (count : Z) : Prop :=
  hex_count_state_78 s (string_length s) count /\
  problem_78_spec_z s count.

Definition hex_count_safe_78 (s : list Z) : Prop :=
  hex_count_state_78 s 0 0 /\
  (forall i count,
      hex_count_state_78 s i (count - 1) ->
      0 <= i < string_length s ->
      prime_hex_code_78 (Znth i (c_string s) 0) ->
      hex_hit_step_78 s i count) /\
  (forall i count,
      hex_count_state_78 s i count ->
      0 <= i < string_length s ->
      ~ prime_hex_code_78 (Znth i (c_string s) 0) ->
      hex_miss_step_78 s i count) /\
  (forall count,
      hex_count_state_78 s (string_length s) count ->
      hex_final_78 s count).

Lemma list_ascii_of_string_of_list_z_78 : forall l,
  list_ascii_of_string (string_of_list_z_78 l) =
  map ascii_of_z_78 l.
Proof.
  induction l as [| c rest IH]; simpl; congruence.
Qed.

Lemma count_prime_hex_list_z_nonneg_78 : forall l,
  0 <= count_prime_hex_list_z_78 l.
Proof.
  induction l as [| c rest IH]; simpl.
  - lia.
  - destruct (is_prime_hex_z_78 c); lia.
Qed.

Lemma firstn_succ_snoc_78 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.

Lemma firstn_succ_Znth_78 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  firstn (Z.to_nat i) l ++ [Znth i l 0].
Proof.
  intros l i H.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_78 with (d := 0)
    by (rewrite Zlength_correct in H; lia).
  reflexivity.
Qed.

Lemma count_prime_hex_list_z_app_78 : forall l1 l2,
  count_prime_hex_list_z_78 (l1 ++ l2) =
  count_prime_hex_list_z_78 l1 + count_prime_hex_list_z_78 l2.
Proof.
  induction l1 as [| c rest IH]; intros l2; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma hex_count_upto_step_hit_78 : forall s i,
  0 <= i < string_length s ->
  prime_hex_code_78 (Znth i (c_string s) 0) ->
  hex_count_upto_78 (i + 1) s =
  hex_count_upto_78 i s + 1.
Proof.
  intros s i Hi Hprime.
  unfold hex_count_upto_78.
  rewrite firstn_succ_Znth_78
    by (unfold string_length, c_string in *; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  rewrite count_prime_hex_list_z_app_78.
  simpl.
  rewrite Hprime.
  lia.
Qed.

Lemma hex_count_upto_step_miss_78 : forall s i,
  0 <= i < string_length s ->
  ~ prime_hex_code_78 (Znth i (c_string s) 0) ->
  hex_count_upto_78 (i + 1) s =
  hex_count_upto_78 i s.
Proof.
  intros s i Hi Hmiss.
  unfold hex_count_upto_78.
  rewrite firstn_succ_Znth_78
    by (unfold string_length, c_string in *; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  rewrite count_prime_hex_list_z_app_78.
  simpl.
  destruct (is_prime_hex_z_78 (Znth i (c_string s) 0)) eqn:Hprime; [| lia].
  exfalso.
  apply Hmiss.
  exact Hprime.
Qed.

Lemma count_prime_hex_list_z_length_filter_78 : forall l,
  Z.to_nat (count_prime_hex_list_z_78 l) =
  List.length (filter is_prime_hex_digit (map ascii_of_z_78 l)).
Proof.
  induction l as [| c rest IH]; simpl.
  - reflexivity.
  - destruct (is_prime_hex_z_78 c) eqn:Hc; unfold is_prime_hex_z_78 in Hc; rewrite Hc; simpl.
    + change (Z.to_nat (1 + count_prime_hex_list_z_78 rest) =
              S (List.length (filter is_prime_hex_digit (map ascii_of_z_78 rest)))).
      rewrite Z2Nat.inj_add by (pose proof (count_prime_hex_list_z_nonneg_78 rest); lia).
      rewrite IH. reflexivity.
    + exact IH.
Qed.

Lemma filter_prime_hex_digits_78 : forall s,
  prime_hex_digits
    s
    (filter is_prime_hex_digit (list_ascii_of_string s)).
Proof.
  intros s.
  unfold prime_hex_digits, prime_hex_digit.
  split.
  - intros c Hin.
    apply filter_In in Hin.
    tauto.
  - intros c Hin Hprime.
    apply filter_In.
    tauto.
Qed.

Lemma problem_78_spec_z_intro : forall s output,
  output = count_prime_hex_list_z_78 s ->
  problem_78_spec_z s output.
Proof.
  intros s output Hout.
  unfold problem_78_spec_z, problem_78_spec.
  exists (filter is_prime_hex_digit (list_ascii_of_string (string_of_list_z_78 s))).
  split.
  - apply filter_prime_hex_digits_78.
  - rewrite Hout.
    rewrite list_ascii_of_string_of_list_z_78.
    rewrite count_prime_hex_list_z_length_filter_78.
    reflexivity.
Qed.

Lemma hex_count_initial_78 : forall s,
  hex_count_state_78 s 0 0.
Proof.
  intros s.
  unfold hex_count_state_78, hex_count_upto_78.
  split; [unfold string_length; rewrite Zlength_correct; lia |].
  split; [reflexivity | lia].
Qed.

Lemma hex_hit_step_intro_78 : forall s i count,
  hex_count_state_78 s i (count - 1) ->
  0 <= i < string_length s ->
  prime_hex_code_78 (Znth i (c_string s) 0) ->
  hex_hit_step_78 s i count.
Proof.
  intros s i count Hstate Hi Hprime.
  unfold hex_hit_step_78.
  split; [exact Hi | split; [exact Hprime |]].
  unfold hex_count_state_78 in *.
  destruct Hstate as [_ [Hcount Hbound]].
  split; [lia | split].
  - rewrite hex_count_upto_step_hit_78 by assumption. lia.
  - lia.
Qed.

Lemma hex_miss_step_intro_78 : forall s i count,
  hex_count_state_78 s i count ->
  0 <= i < string_length s ->
  ~ prime_hex_code_78 (Znth i (c_string s) 0) ->
  hex_miss_step_78 s i count.
Proof.
  intros s i count Hstate Hi Hmiss.
  unfold hex_miss_step_78.
  split; [exact Hi | split; [exact Hmiss |]].
  unfold hex_count_state_78 in *.
  destruct Hstate as [_ [Hcount Hbound]].
  split; [lia | split].
  - rewrite hex_count_upto_step_miss_78 by assumption. lia.
  - lia.
Qed.

Lemma hex_final_intro_78 : forall s count,
  hex_count_state_78 s (string_length s) count ->
  hex_final_78 s count.
Proof.
  intros s count Hstate.
  unfold hex_final_78.
  split; [exact Hstate |].
  unfold hex_count_state_78 in Hstate.
  destruct Hstate as [_ [Hcount _]].
  unfold hex_count_upto_78 in Hcount.
  unfold c_string in Hcount.
  replace (Z.to_nat (string_length s)) with (List.length s) in Hcount
    by (unfold string_length; rewrite Zlength_correct; lia).
  rewrite firstn_app in Hcount.
  rewrite firstn_all in Hcount.
  replace (List.length s - List.length s)%nat with 0%nat in Hcount by lia.
  simpl in Hcount.
  rewrite List.app_nil_r in Hcount.
  apply problem_78_spec_z_intro.
  exact Hcount.
Qed.

Lemma hex_count_safe_intro_78 : forall s,
  hex_count_safe_78 s.
Proof.
  intro s.
  unfold hex_count_safe_78.
  split.
  - apply hex_count_initial_78.
  - split.
    + intros i count Hstate Hi Hprime.
      apply hex_hit_step_intro_78; assumption.
    + split.
      * intros i count Hstate Hi Hmiss.
        apply hex_miss_step_intro_78; assumption.
      * intros count Hstate.
        apply hex_final_intro_78; assumption.
Qed.

Lemma all_ascii_c_string_inside_78 : forall s i,
  all_ascii s ->
  0 <= i < string_length s ->
  0 <= Znth i (c_string s) 0 <= 127.
Proof.
  intros s i Hascii Hi.
  rewrite c_string_Znth_inside by exact Hi.
  apply Hascii.
  unfold string_length in Hi.
  exact Hi.
Qed.

Lemma c_string_nonzero_inside_78 : forall s i,
  string_lib.valid_string s ->
  0 <= i < string_length s ->
  Znth i (c_string s) 0 <> 0.
Proof.
  intros s i Hvalid Hi.
  rewrite c_string_Znth_inside by exact Hi.
  destruct Hvalid as [_ Hno].
  apply Hno.
  unfold string_length in Hi.
  exact Hi.
Qed.

Lemma key_lit_to_store_78 : forall LM,
  store_stringLit (LM key_literal_78) key_literal_78 |--
  string_lib.store_string (key_ptr_78 LM) key_payload_78.
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold key_ptr_78, key_payload_78, key_literal_78.
  simpl.
  entailer!.
Qed.

Lemma key_payload_safe_proof_78 : key_payload_safe_78.
Proof.
  unfold key_payload_safe_78, string_lib.valid_string, string_lib.all_ascii,
    string_lib.no_inner_nul, all_ascii, no_inner_nul, string_length,
    key_payload_78, key_literal_78.
  assert (Hascii :
    forall i : Z,
      0 <= i < Zlength [50; 51; 53; 55; 66; 68] ->
      0 <= Znth i [50; 51; 53; 55; 66; 68] 0 <= 127).
  {
    intros i Hi.
    change (Zlength [50; 51; 53; 55; 66; 68]) with 6 in Hi.
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
    destruct H as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    try change (Znth 0 [50; 51; 53; 55; 66; 68] 0) with 50;
    try change (Znth 1 [50; 51; 53; 55; 66; 68] 0) with 51;
    try change (Znth 2 [50; 51; 53; 55; 66; 68] 0) with 53;
    try change (Znth 3 [50; 51; 53; 55; 66; 68] 0) with 55;
    try change (Znth 4 [50; 51; 53; 55; 66; 68] 0) with 66;
    try change (Znth 5 [50; 51; 53; 55; 66; 68] 0) with 68;
    lia.
  }
  assert (Hnonzero :
    forall i : Z,
      0 <= i < Zlength [50; 51; 53; 55; 66; 68] ->
      Znth i [50; 51; 53; 55; 66; 68] 0 <> 0).
  {
    intros i Hi.
    change (Zlength [50; 51; 53; 55; 66; 68]) with 6 in Hi.
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
    destruct H as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    try change (Znth 0 [50; 51; 53; 55; 66; 68] 0) with 50;
    try change (Znth 1 [50; 51; 53; 55; 66; 68] 0) with 51;
    try change (Znth 2 [50; 51; 53; 55; 66; 68] 0) with 53;
    try change (Znth 3 [50; 51; 53; 55; 66; 68] 0) with 55;
    try change (Znth 4 [50; 51; 53; 55; 66; 68] 0) with 66;
    try change (Znth 5 [50; 51; 53; 55; 66; 68] 0) with 68;
    lia.
  }
  assert (Hlen : Zlength [50; 51; 53; 55; 66; 68] < 2147483647) by
    (change (Zlength [50; 51; 53; 55; 66; 68]) with 6; lia).
  split.
  - split; [exact Hascii | exact Hnonzero].
  - split; [exact Hascii | exact Hlen].
Qed.

Lemma prime_hex_code_range_cases_78 : forall c,
  0 <= c <= 127 ->
  prime_hex_code_78 c ->
  c = 50 \/ c = 51 \/ c = 53 \/ c = 55 \/ c = 66 \/ c = 68.
Proof.
  intros c Hrange Hprime.
  unfold prime_hex_code_78, is_prime_hex_z_78, ascii_of_z_78 in Hprime.
  assert (Hc : Z.of_nat (Z.to_nat c) = c) by (apply Z2Nat.id; lia).
  remember (Z.to_nat c) as n eqn:Hn.
  do 128
    (destruct n as [| n];
     cbn in Hprime;
     try (assert (c = 50 \/ c = 51 \/ c = 53 \/ c = 55 \/ c = 66 \/ c = 68) by lia; tauto);
     try discriminate).
Qed.

Lemma prime_hex_code_key_index_78 : forall i c,
  0 <= i < string_length key_payload_78 ->
  Znth i key_payload_78 0 = c ->
  prime_hex_code_78 c.
Proof.
  intros i c Hi Hc.
  unfold key_payload_78, string_length in Hi, Hc.
  rewrite Zlength_correct in Hi.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by (cbn in Hi; lia).
  destruct H as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    cbn in Hc; subst c; reflexivity.
Qed.

Lemma strchr_result_key_hit_prime_78 : forall c ret base,
  c <> 0 ->
  strchr_result key_payload_78 c ret base ->
  ret <> 0 ->
  prime_hex_code_78 c.
Proof.
  intros c ret base Hc0 Hres Hret.
  unfold strchr_result in Hres.
  destruct Hres as [Hhit | Hmiss].
  - destruct Hhit as [i [Hi [Hci [_ [_ _]]]]].
    eapply prime_hex_code_key_index_78; eauto.
  - destruct Hmiss as [_ [[Hz _] | [_ Hzero]]].
    + contradiction.
    + lia.
Qed.

Lemma strchr_result_key_miss_not_prime_78 : forall c base,
  0 <= c <= 127 ->
  strchr_result key_payload_78 c 0 base ->
  ~ prime_hex_code_78 c.
Proof.
  intros c base Hrange Hres Hprime.
  unfold strchr_result in Hres.
  destruct Hres as [[i [_ [_ [_ [_ Hret]]]]] | [Hnone _]].
  - contradiction.
  - pose proof (prime_hex_code_range_cases_78 c Hrange Hprime) as Hcases.
    unfold key_payload_78, string_length in Hnone.
    destruct Hcases as [-> | [-> | [-> | [-> | [-> | ->]]]]].
    + specialize (Hnone 0 ltac:(cbn; lia)); vm_compute in Hnone; lia.
    + specialize (Hnone 1 ltac:(cbn; lia)); vm_compute in Hnone; lia.
    + specialize (Hnone 2 ltac:(cbn; lia)); vm_compute in Hnone; lia.
    + specialize (Hnone 3 ltac:(cbn; lia)); vm_compute in Hnone; lia.
    + specialize (Hnone 4 ltac:(cbn; lia)); vm_compute in Hnone; lia.
    + specialize (Hnone 5 ltac:(cbn; lia)); vm_compute in Hnone; lia.
Qed.

Lemma hex_final_from_safe_78 : forall s count,
  hex_count_safe_78 s ->
  hex_count_state_78 s (string_length s) count ->
  hex_final_78 s count.
Proof.
  intros s count Hsafe Hstate.
  unfold hex_count_safe_78 in Hsafe.
  destruct Hsafe as [_ [_ [_ Hfinal]]].
  apply Hfinal; assumption.
Qed.

Lemma hex_hit_from_safe_78 : forall s i count,
  hex_count_safe_78 s ->
  hex_count_state_78 s i (count - 1) ->
  0 <= i < string_length s ->
  prime_hex_code_78 (Znth i (c_string s) 0) ->
  hex_hit_step_78 s i count.
Proof.
  intros s i count Hsafe Hstate Hi Hprime.
  unfold hex_count_safe_78 in Hsafe.
  destruct Hsafe as [_ [Hhit _]].
  apply Hhit; assumption.
Qed.

Lemma hex_miss_from_safe_78 : forall s i count,
  hex_count_safe_78 s ->
  hex_count_state_78 s i count ->
  0 <= i < string_length s ->
  ~ prime_hex_code_78 (Znth i (c_string s) 0) ->
  hex_miss_step_78 s i count.
Proof.
  intros s i count Hsafe Hstate Hi Hmiss.
  unfold hex_count_safe_78 in Hsafe.
  destruct Hsafe as [_ [_ [Hmiss_step _]]].
  apply Hmiss_step; assumption.
Qed.

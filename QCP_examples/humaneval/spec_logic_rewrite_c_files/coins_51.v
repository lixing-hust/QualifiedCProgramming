Load "../spec/51".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
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

Definition ascii_of_z_51 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_51 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_51 c) (string_of_list_z_51 rest)
  end.

Definition problem_51_pre_z (input : list Z) : Prop :=
  problem_51_pre (string_of_list_z_51 input).

Definition problem_51_spec_z (input output : list Z) : Prop :=
  problem_51_spec (string_of_list_z_51 input) (string_of_list_z_51 output).

Definition vowel_literal_51 : string := "AEIOUaeiou"%string.

Definition all_vowel_literals_51 : list string := [vowel_literal_51].

Definition vowel_payload_51 : list Z :=
  [65; 69; 73; 79; 85; 97; 101; 105; 111; 117].

Definition vowel_ptr_51 (LM : string -> Z) : Z := LM vowel_literal_51.

Definition vowel_payload_safe_51 : Prop :=
  string_lib.valid_string vowel_payload_51 /\
  string_lib.all_ascii vowel_payload_51 /\
  string_lib.string_length vowel_payload_51 < INT_MAX.

Definition keep_char_z_51 (c : Z) : bool :=
  negb (is_vowel (ascii_of_z_51 c)).

Definition filter_prefix_51 (input : list Z) (i : Z) (output : list Z) : Prop :=
  0 <= i <= string_lib.string_length input /\
  output = filter keep_char_z_51 (firstn (Z.to_nat i) input).

Lemma list_ascii_of_string_of_list_z_51 : forall l,
  list_ascii_of_string (string_of_list_z_51 l) = map ascii_of_z_51 l.
Proof.
  induction l as [| c rest IH]; simpl; congruence.
Qed.

Lemma filter_prefix_nil_51 : forall input,
  filter_prefix_51 input 0 [].
Proof.
  intros input. unfold filter_prefix_51, string_lib.string_length.
  split; [pose proof (Zlength_nonneg input); lia | reflexivity].
Qed.

Lemma firstn_succ_snoc_51 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.

Lemma firstn_succ_Znth_51 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  firstn (Z.to_nat i) l ++ [Znth i l 0].
Proof.
  intros l i Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_51 with (d := 0)
    by (rewrite Zlength_correct in Hi; lia).
  reflexivity.
Qed.

Lemma Znth_c_string_51 : forall input i,
  0 <= i < string_lib.string_length input ->
  Znth i (string_lib.c_string input) 0 = Znth i input 0.
Proof.
  intros input i Hi. unfold string_lib.c_string, string_lib.string_length in *.
  apply app_Znth1. exact Hi.
Qed.

Lemma filter_prefix_hit_51 : forall input i output,
  filter_prefix_51 input i output ->
  0 <= i < string_lib.string_length input ->
  keep_char_z_51 (Znth i input 0) = false ->
  filter_prefix_51 input (i + 1) output.
Proof.
  intros input i output [Hi Hout] Hbound Hkeep.
  unfold filter_prefix_51. split; [lia |].
  rewrite firstn_succ_Znth_51 by (unfold string_lib.string_length in Hbound; exact Hbound).
  rewrite filter_app. simpl. rewrite Hkeep. simpl. rewrite app_nil_r. exact Hout.
Qed.

Lemma filter_prefix_miss_51 : forall input i output,
  filter_prefix_51 input i output ->
  0 <= i < string_lib.string_length input ->
  keep_char_z_51 (Znth i input 0) = true ->
  filter_prefix_51 input (i + 1) (output ++ [Znth i input 0]).
Proof.
  intros input i output [Hi Hout] Hbound Hkeep.
  unfold filter_prefix_51. split; [lia |].
  rewrite firstn_succ_Znth_51 by (unfold string_lib.string_length in Hbound; exact Hbound).
  rewrite filter_app. simpl. rewrite Hkeep. simpl. now rewrite Hout.
Qed.

Lemma vowel_payload_index_51 : forall i c,
  0 <= i < string_lib.string_length vowel_payload_51 ->
  Znth i vowel_payload_51 0 = c ->
  is_vowel (ascii_of_z_51 c) = true.
Proof.
  intros i c Hi Hc.
  unfold vowel_payload_51, string_lib.string_length in Hi, Hc.
  rewrite Zlength_correct in Hi.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
          i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by (cbn in Hi; lia).
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    cbn in Hc; subst c; reflexivity.
Qed.

Lemma strchr_vowel_hit_51 : forall c ret base,
  c <> 0 ->
  string_lib.strchr_result vowel_payload_51 c ret base ->
  ret <> 0 ->
  keep_char_z_51 c = false.
Proof.
  intros c ret base Hc0 Hres Hret.
  unfold string_lib.strchr_result in Hres.
  destruct Hres as [[i [Hi [Hc [_ [_ _]]]]] | [_ [[Hzerochar _] | [_ Hzero]]]].
  - unfold keep_char_z_51. rewrite (vowel_payload_index_51 i c Hi Hc). reflexivity.
  - contradiction.
  - contradiction.
Qed.

Lemma vowel_code_in_payload_51 : forall c,
  0 <= c <= 127 ->
  is_vowel (ascii_of_z_51 c) = true ->
  c = 65 \/ c = 69 \/ c = 73 \/ c = 79 \/ c = 85 \/
  c = 97 \/ c = 101 \/ c = 105 \/ c = 111 \/ c = 117.
Proof.
  intros c Hrange Hvowel.
  unfold ascii_of_z_51 in Hvowel.
  remember (Z.to_nat c) as n eqn:Hn.
  do 128
    (destruct n as [| n];
     cbn in Hvowel;
     try (assert (c = 65 \/ c = 69 \/ c = 73 \/ c = 79 \/ c = 85 \/
                  c = 97 \/ c = 101 \/ c = 105 \/ c = 111 \/ c = 117) by lia;
          tauto);
     try discriminate).
Qed.

Lemma strchr_vowel_miss_51 : forall c base,
  0 <= c <= 127 ->
  string_lib.strchr_result vowel_payload_51 c 0 base ->
  keep_char_z_51 c = true.
Proof.
  intros c base Hrange Hres.
  unfold keep_char_z_51.
  destruct (is_vowel (ascii_of_z_51 c)) eqn:Hvowel; [| reflexivity].
  exfalso.
  pose proof (vowel_code_in_payload_51 c Hrange Hvowel) as Hcases.
  unfold string_lib.strchr_result in Hres.
  destruct Hres as [[i [_ [_ [_ [_ Hret]]]]] | [Hnone _]]; [contradiction |].
  unfold vowel_payload_51, string_lib.string_length in Hnone.
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
  - specialize (Hnone 0 ltac:(cbn; lia)); vm_compute in Hnone; lia.
  - specialize (Hnone 1 ltac:(cbn; lia)); vm_compute in Hnone; lia.
  - specialize (Hnone 2 ltac:(cbn; lia)); vm_compute in Hnone; lia.
  - specialize (Hnone 3 ltac:(cbn; lia)); vm_compute in Hnone; lia.
  - specialize (Hnone 4 ltac:(cbn; lia)); vm_compute in Hnone; lia.
  - specialize (Hnone 5 ltac:(cbn; lia)); vm_compute in Hnone; lia.
  - specialize (Hnone 6 ltac:(cbn; lia)); vm_compute in Hnone; lia.
  - specialize (Hnone 7 ltac:(cbn; lia)); vm_compute in Hnone; lia.
  - specialize (Hnone 8 ltac:(cbn; lia)); vm_compute in Hnone; lia.
  - specialize (Hnone 9 ltac:(cbn; lia)); vm_compute in Hnone; lia.
Qed.

Lemma signed_last_nbits_ascii_51 : forall c,
  0 <= c <= 127 -> IntLib.signed_last_nbits c 8 = c.
Proof.
  intros c Hc. rewrite IntLib.signed_last_nbits_eq; cbn; lia.
Qed.

Lemma all_ascii_c_string_inside_51 : forall s i,
  string_lib.all_ascii s ->
  0 <= i < string_lib.string_length s ->
  0 <= Znth i (string_lib.c_string s) 0 <= 127.
Proof.
  intros s i Hascii Hi.
  rewrite c_string_Znth_inside by exact Hi.
  apply Hascii.
  unfold string_lib.string_length in Hi. exact Hi.
Qed.

Lemma c_string_nonzero_inside_51 : forall s i,
  string_lib.valid_string s ->
  0 <= i < string_lib.string_length s ->
  Znth i (string_lib.c_string s) 0 <> 0.
Proof.
  intros s i Hvalid Hi.
  rewrite c_string_Znth_inside by exact Hi.
  apply (proj2 Hvalid).
  unfold string_lib.string_length in Hi. exact Hi.
Qed.

Lemma vowel_lit_to_store_51 : forall LM,
  store_stringLit (LM vowel_literal_51) vowel_literal_51 |--
  string_lib.store_string (vowel_ptr_51 LM) vowel_payload_51.
Proof.
  intros LM.
  unfold store_stringLit, string_lib.store_string,
    vowel_ptr_51, vowel_payload_51, vowel_literal_51.
  simpl. entailer!.
Qed.

Lemma vowel_payload_safe_proof_51 : vowel_payload_safe_51.
Proof.
  unfold vowel_payload_safe_51, string_lib.valid_string,
    string_lib.all_ascii, string_lib.no_inner_nul,
    string_lib.string_length, vowel_payload_51.
  assert (Hascii : forall i : Z,
    0 <= i < Zlength [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] ->
    0 <= Znth i [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0 <= 127).
  {
    intros i Hi. change (Zlength [65; 69; 73; 79; 85; 97; 101; 105; 111; 117]) with 10 in Hi.
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
            i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
    destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
      try change (Znth 0 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 65;
      try change (Znth 1 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 69;
      try change (Znth 2 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 73;
      try change (Znth 3 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 79;
      try change (Znth 4 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 85;
      try change (Znth 5 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 97;
      try change (Znth 6 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 101;
      try change (Znth 7 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 105;
      try change (Znth 8 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 111;
      try change (Znth 9 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 117;
      lia.
  }
  assert (Hnonzero : forall i : Z,
    0 <= i < Zlength [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] ->
    Znth i [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0 <> 0).
  {
    intros i Hi. change (Zlength [65; 69; 73; 79; 85; 97; 101; 105; 111; 117]) with 10 in Hi.
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
            i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
    destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
      try change (Znth 0 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 65;
      try change (Znth 1 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 69;
      try change (Znth 2 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 73;
      try change (Znth 3 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 79;
      try change (Znth 4 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 85;
      try change (Znth 5 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 97;
      try change (Znth 6 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 101;
      try change (Znth 7 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 105;
      try change (Znth 8 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 111;
      try change (Znth 9 [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] 0) with 117;
      lia.
  }
  assert (Hlen :
    Zlength [65; 69; 73; 79; 85; 97; 101; 105; 111; 117] < INT_MAX).
  { change (Zlength [65; 69; 73; 79; 85; 97; 101; 105; 111; 117]) with 10. lia. }
  split; [split; assumption |].
  split; [exact Hascii | exact Hlen].
Qed.

Lemma filter_prefix_hit_c_51 : forall input i output,
  filter_prefix_51 input i output ->
  0 <= i < string_lib.string_length input ->
  keep_char_z_51 (Znth i (string_lib.c_string input) 0) = false ->
  filter_prefix_51 input (i + 1) output.
Proof.
  intros input i output Hprefix Hi Hkeep.
  rewrite Znth_c_string_51 in Hkeep by exact Hi.
  now apply filter_prefix_hit_51.
Qed.

Lemma filter_prefix_miss_c_51 : forall input i output,
  string_lib.valid_string input ->
  filter_prefix_51 input i output ->
  0 <= i < string_lib.string_length input ->
  keep_char_z_51 (Znth i (string_lib.c_string input) 0) = true ->
  filter_prefix_51 input (i + 1)
    (output ++ [IntLib.signed_last_nbits (Znth i (string_lib.c_string input) 0) 8]).
Proof.
  intros input i output Hvalid Hprefix Hi Hkeep.
  rewrite Znth_c_string_51 in Hkeep by exact Hi.
  rewrite Znth_c_string_51 by exact Hi.
  pose proof (proj1 Hvalid) as Hascii.
  rewrite signed_last_nbits_ascii_51 by
    (apply Hascii; unfold string_lib.string_length in Hi; exact Hi).
  now apply filter_prefix_miss_51.
Qed.

Lemma filter_prefix_full_spec_51 : forall input output,
  filter_prefix_51 input (string_lib.string_length input) output ->
  problem_51_spec_z input output.
Proof.
  intros input output [_ Hout].
  unfold problem_51_spec_z, problem_51_spec, filter_string.
  rewrite list_ascii_of_string_of_list_z_51.
  unfold string_lib.string_length in Hout.
  rewrite Zlength_correct, Nat2Z.id in Hout.
  rewrite firstn_all in Hout.
  subst output.
  f_equal.
  induction input as [| c rest IH]; simpl; [reflexivity |].
  unfold keep_char_z_51 at 1.
  destruct (is_vowel (ascii_of_z_51 c)) eqn:Hvowel;
    simpl; congruence.
Qed.

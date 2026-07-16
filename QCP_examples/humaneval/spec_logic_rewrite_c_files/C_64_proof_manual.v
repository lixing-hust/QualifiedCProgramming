Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_64_goal.
From SimpleC.EE Require Import C_64_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_64.
Local Open Scope sac.

Ltac c64_char_bounds :=
  match goal with
  | |- 0 <= Znth ?k (c_string ?s) 0 =>
      pose proof (c_string_char_bound s k ltac:(assumption) ltac:(lia));
      lia
  | |- Znth ?k (c_string ?s) 0 <= 127 =>
      pose proof (c_string_char_bound s k ltac:(assumption) ltac:(lia));
      lia
  end.

Ltac c64_finish :=
  entailer!; eauto; try c64_char_bounds; try lia.

Lemma proof_of_vowels_count_entail_wit_1 : vowels_count_entail_wit_1.
Proof.
  right.
  pre_process_default.
  pose proof vowel_payload_safe_proof_64.
  sep_apply_l_atomic (GlobalStrings_split LitMap vowel_literal_64).
  sep_apply_l_atomic (vowel_lit_to_store_64 LitMap).
  unfold all_vowel_literals_64, vowel_ptr_64, vowel_literal_64,
    vowel_payload_64, string_lib.store_string.
  simpl.
  replace (LitMap "aeiouAEIOU" + 0) with (LitMap "aeiouAEIOU") by lia.
  entailer!.
Qed.

Lemma proof_of_vowels_count_entail_wit_2 : vowels_count_entail_wit_2.
Proof.
  right.
  pre_process_default.
  entailer!.
  - subst retval. apply string_length_nonneg.
  - apply vowel_count_initial_64.
Qed.

Lemma proof_of_vowels_count_entail_wit_3 : vowels_count_entail_wit_3.
Proof.
  right.
  pre_process_default.
  assert (Hi : 0 <= i < string_length str_l) by (subst n; lia).
  assert (Hnz : Znth i (c_string str_l) 0 <> 0) by
    (apply c_string_nonzero_inside_64; [exact PreH12 | exact Hi]).
  assert (Hreg : regular_vowel_code_64 (Znth i (c_string str_l) 0)) by
    (eapply vowel_payload_contains_regular_64; eauto).
  assert (Hstep : vowel_regular_step_64 str_l i (count + 1)).
  {
    eapply vowel_regular_step_intro_64; eauto.
    replace ((count + 1) - 1) with count by lia.
    exact PreH17.
  }
  assert (Hstate : vowel_count_state_64 str_l (i + 1) (count + 1)) by
    (destruct Hstep as [_ [_ Hstate]]; exact Hstate).
  c64_finish.
Qed.

Lemma proof_of_vowels_count_entail_wit_4 : vowels_count_entail_wit_4.
Proof.
  right.
  pre_process_default.
  assert (Hi : 0 <= i < string_length str_l) by (subst n; lia).
  assert (Hmiss : ~ regular_vowel_code_64 (Znth i (c_string str_l) 0)) by
    (subst retval; eapply vowel_payload_miss_not_regular_64; eauto).
  assert (Hstep : vowel_miss_step_64 str_l i count) by
    (eapply vowel_miss_step_intro_64; eauto).
  assert (Hstate : vowel_count_state_64 str_l (i + 1) count) by
    (destruct Hstep as [_ [_ Hstate]]; exact Hstate).
  c64_finish.
Qed.

Lemma proof_of_vowels_count_entail_wit_6_1 : vowels_count_entail_wit_6_1.
Proof.
  right.
  pre_process_default.
  assert (Hi_eq : i = n) by lia.
  assert (Hy :
    y_code_64
      (Znth (naive_C_Rules.string_length str_l - 1)
         (naive_C_Rules.c_string str_l) 0)).
  {
    unfold naive_C_Rules.string_length, naive_C_Rules.c_string,
      string_lib.string_length, string_lib.c_string in *.
    replace (Zlength str_l - 1) with (n - 1) by lia.
    unfold y_code_64.
    rewrite PreH3.
    tauto.
  }
  assert (Hstate :
    vowel_count_state_64 str_l
      (naive_C_Rules.string_length str_l) ((count + 1) - 1)).
  {
    unfold naive_C_Rules.string_length, string_lib.string_length in *.
    replace (Zlength str_l) with i by lia.
    replace ((count + 1) - 1) with count by lia.
    exact PreH18.
  }
  assert (Hstate_n :
    vowel_count_state_64 str_l n ((count + 1) - 1)).
  {
    replace n with (naive_C_Rules.string_length str_l) by
      (unfold naive_C_Rules.string_length, string_lib.string_length in *; lia).
    exact Hstate.
  }
  assert (Hfinal : vowel_final_y_64 str_l (count + 1)) by
    (eapply vowel_final_y_intro_64;
     [exact PreH14 | exact Hstate |
      unfold naive_C_Rules.string_length, string_lib.string_length in *; lia |
      exact Hy]).
  pose proof Hfinal as [_ [_ Hspec]].
  c64_finish.
Qed.

Lemma proof_of_vowels_count_entail_wit_6_2 : vowels_count_entail_wit_6_2.
Proof.
  right.
  pre_process_default.
  assert (Hi_eq : i = n) by lia.
  assert (Hy :
    y_code_64
      (Znth (naive_C_Rules.string_length str_l - 1)
         (naive_C_Rules.c_string str_l) 0)).
  {
    unfold naive_C_Rules.string_length, naive_C_Rules.c_string,
      string_lib.string_length, string_lib.c_string in *.
    replace (Zlength str_l - 1) with (n - 1) by lia.
    unfold y_code_64.
    rewrite PreH3.
    tauto.
  }
  assert (Hstate :
    vowel_count_state_64 str_l
      (naive_C_Rules.string_length str_l) ((count + 1) - 1)).
  {
    unfold naive_C_Rules.string_length, string_lib.string_length in *.
    replace (Zlength str_l) with i by lia.
    replace ((count + 1) - 1) with count by lia.
    exact PreH17.
  }
  assert (Hstate_n :
    vowel_count_state_64 str_l n ((count + 1) - 1)).
  {
    replace n with (naive_C_Rules.string_length str_l) by
      (unfold naive_C_Rules.string_length, string_lib.string_length in *; lia).
    exact Hstate.
  }
  assert (Hfinal : vowel_final_y_64 str_l (count + 1)) by
    (eapply vowel_final_y_intro_64;
     [exact PreH13 | exact Hstate |
      unfold naive_C_Rules.string_length, string_lib.string_length in *; lia |
      exact Hy]).
  pose proof Hfinal as [_ [_ Hspec]].
  c64_finish.
Qed.

Lemma proof_of_vowels_count_entail_wit_7 : vowels_count_entail_wit_7.
Proof.
  right.
  pre_process_default.
  assert (Hi_eq : i = n) by lia.
  assert (Hnoty :
    ~ y_code_64
        (Znth (naive_C_Rules.string_length str_l - 1)
           (naive_C_Rules.c_string str_l) 0)).
  {
    unfold naive_C_Rules.string_length, naive_C_Rules.c_string,
      string_lib.string_length, string_lib.c_string in *.
    replace (Zlength str_l - 1) with (n - 1) by lia.
    unfold y_code_64.
    intuition congruence.
  }
  assert (Hstate :
    vowel_count_state_64 str_l (naive_C_Rules.string_length str_l) count).
  {
    unfold naive_C_Rules.string_length, string_lib.string_length in *.
    replace (Zlength str_l) with i by lia.
    exact PreH18.
  }
  assert (Hstate_n : vowel_count_state_64 str_l n count).
  {
    replace n with (naive_C_Rules.string_length str_l) by
      (unfold naive_C_Rules.string_length, string_lib.string_length in *; lia).
    exact Hstate.
  }
  assert (Hfinal : vowel_final_not_y_64 str_l count) by
    (eapply vowel_final_not_y_intro_64;
     [exact PreH14 | exact Hstate |
      unfold naive_C_Rules.string_length, string_lib.string_length in *; lia |
      exact Hnoty]).
  pose proof Hfinal as [_ [_ Hspec]].
  c64_finish.
Qed.

Lemma proof_of_vowels_count_entail_wit_8 : vowels_count_entail_wit_8.
Proof.
  right.
  pre_process_default.
  assert (Hn : n = 0) by (subst n; pose proof (string_length_nonneg str_l); lia).
  assert (Hi_eq : i = n) by lia.
  assert (Hcount : count = 0) by lia.
  assert (Hstate :
    vowel_count_state_64 str_l (naive_C_Rules.string_length str_l) count).
  {
    unfold naive_C_Rules.string_length, string_lib.string_length in *.
    replace (Zlength str_l) with i by lia.
    exact PreH16.
  }
  assert (Hstate_n : vowel_count_state_64 str_l n count).
  {
    replace n with (naive_C_Rules.string_length str_l) by
      (unfold naive_C_Rules.string_length, string_lib.string_length in *; lia).
    exact Hstate.
  }
  assert (Hfinal : vowel_final_empty_64 str_l count) by
    (eapply vowel_final_empty_intro_64;
     [exact PreH12 | exact Hstate |
      unfold naive_C_Rules.string_length, string_lib.string_length in *; lia]).
  pose proof Hfinal as [_ [_ Hspec]].
  c64_finish.
Qed.

Lemma proof_of_vowels_count_return_wit_1 : vowels_count_return_wit_1.
Proof.
  left.
  pre_process.
  subst vowels.
  entailer!.
Qed.

Lemma proof_of_vowels_count_return_wit_2 : vowels_count_return_wit_2.
Proof.
  left.
  pre_process.
  subst vowels.
  entailer!.
Qed.

Lemma proof_of_vowels_count_return_wit_3 : vowels_count_return_wit_3.
Proof.
  left.
  pre_process.
  subst vowels.
  entailer!.
Qed.

Lemma proof_of_vowels_count_partial_solve_wit_2_pure :
  vowels_count_partial_solve_wit_2_pure.
Proof.
  right.
  pre_process_default.
  destruct PreH21 as [Hvalid [Hascii_vowels Hlen_vowels]].
  pose proof (c_string_char_bound str_l i PreH18 ltac:(subst n; lia))
    as Hchar.
  entailer!; lia.
Qed.

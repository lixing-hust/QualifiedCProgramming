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
From SimpleC.EE Require Import C_78_goal.
From SimpleC.EE Require Import C_78_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_78.
Local Open Scope sac.

Ltac c78_char_bounds :=
  match goal with
  | |- 0 <= Znth ?k (c_string ?s) 0 =>
      pose proof (all_ascii_c_string_inside_78 s k ltac:(assumption) ltac:(lia));
      lia
  | |- Znth ?k (c_string ?s) 0 <= 127 =>
      pose proof (all_ascii_c_string_inside_78 s k ltac:(assumption) ltac:(lia));
      lia
  end.

Ltac c78_finish :=
  entailer!; eauto; try c78_char_bounds; try lia.

Lemma proof_of_hex_key_entail_wit_1 : hex_key_entail_wit_1.
Proof.
  right.
  pre_process_default.
  pose proof key_payload_safe_proof_78.
  sep_apply_l_atomic (GlobalStrings_split LitMap key_literal_78).
  sep_apply_l_atomic (key_lit_to_store_78 LitMap).
  unfold all_key_literals_78, key_ptr_78, key_literal_78,
    key_payload_78, string_lib.store_string.
  simpl.
  replace (LitMap "2357BD" + 0) with (LitMap "2357BD") by lia.
  entailer!.
Qed. 

Lemma proof_of_hex_key_entail_wit_2 : hex_key_entail_wit_2.
Proof.
  right.
  pre_process_default.
  entailer!.
  - subst retval. apply string_length_nonneg.
  - apply hex_count_initial_78.
Qed. 

Lemma proof_of_hex_key_entail_wit_3 : hex_key_entail_wit_3.
Proof.
  right.
  pre_process_default.
  assert (Hi : 0 <= i < string_length str_l) by (subst n; lia).
  assert (Hrange : 0 <= Znth i (c_string str_l) 0 <= 127) by
    (apply all_ascii_c_string_inside_78; [exact PreH13 | exact Hi]).
  assert (Hnz : Znth i (c_string str_l) 0 <> 0) by
    (apply c_string_nonzero_inside_78; [exact PreH12 | exact Hi]).
  assert (Hprime : prime_hex_code_78 (Znth i (c_string str_l) 0)) by
    (eapply strchr_result_key_hit_prime_78; eauto).
  assert (Hstep : hex_hit_step_78 str_l i (out + 1)).
  {
    eapply hex_hit_step_intro_78; eauto.
    replace ((out + 1) - 1) with out by lia.
    exact PreH18.
  }
  assert (Hstate : hex_count_state_78 str_l (i + 1) (out + 1)) by
    (destruct Hstep as [_ [_ Hstate]]; exact Hstate).
  entailer!; eauto; lia.
Qed. 

Lemma proof_of_hex_key_entail_wit_4 : hex_key_entail_wit_4.
Proof.
  right.
  pre_process_default.
  assert (Hi : 0 <= i < string_length str_l) by (subst n; lia).
  assert (Hrange : 0 <= Znth i (c_string str_l) 0 <= 127) by
    (apply all_ascii_c_string_inside_78; [exact PreH13 | exact Hi]).
  assert (Hmiss : ~ prime_hex_code_78 (Znth i (c_string str_l) 0)) by
    (subst retval; eapply strchr_result_key_miss_not_prime_78; eauto).
  assert (Hstep : hex_miss_step_78 str_l i out) by
    (eapply hex_miss_step_intro_78; eauto).
  assert (Hstate : hex_count_state_78 str_l (i + 1) out) by
    (destruct Hstep as [_ [_ Hstate]]; exact Hstate).
  entailer!; eauto; lia.
Qed. 

Lemma proof_of_hex_key_entail_wit_6 : hex_key_entail_wit_6.
Proof.
  right.
  pre_process_default.
  assert (Hi_eq : i = n) by lia.
  assert (Hstate_len : hex_count_state_78 str_l (string_length str_l) out).
  {
    replace (string_length str_l) with i by lia.
    exact PreH16.
  }
  assert (Hfinal : hex_final_78 str_l out) by
    (eapply hex_final_from_safe_78; [exact PreH13 | exact Hstate_len]).
  pose proof Hfinal as Hfinal_keep.
  destruct Hfinal as [Hstate_final Hspec].
  assert (Hstate_n : hex_count_state_78 str_l n out) by
    (subst n; exact Hstate_final).
  entailer!; eauto.
Qed. 

Lemma proof_of_hex_key_return_wit_1 : hex_key_return_wit_1.
Proof.
  left.
  pre_process.
  subst key.
  entailer!.
Qed. 

Lemma proof_of_hex_key_partial_solve_wit_2_pure : hex_key_partial_solve_wit_2_pure.
Proof.
  right.
  pre_process_default.
  destruct PreH22 as [Hvalid_key [Hascii_key Hlen_key]].
  assert (Hi : 0 <= i < string_length str_l) by (subst n; lia).
  pose proof (all_ascii_c_string_inside_78 str_l i PreH19 Hi) as Hchar.
  entailer!; lia.
Qed. 

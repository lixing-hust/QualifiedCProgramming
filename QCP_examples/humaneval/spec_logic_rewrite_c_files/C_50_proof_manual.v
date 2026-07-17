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
From SimpleC.EE Require Import C_50_goal.
From SimpleC.EE Require Import C_50_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_50.
Local Open Scope sac.

Lemma proof_of_encode_shift_safety_wit_6 : encode_shift_safety_wit_6.
Proof.
  unfold encode_shift_safety_wit_6. left.
  intros s0 l out out_l i n Hlt Hpre Hvalid Hn Hi0 Hin Hout Hprefix.
  pre_process.
  assert (Hidx : 0 <= i < Zlength l) by (unfold string_length in Hn; lia).
  pose proof (lower_input_at_50 l i Hpre Hvalid Hidx) as Hlower.
  rewrite Znth_c_string_50 by exact Hidx.
  pose proof (Z.rem_bound_abs (Znth i l 0 + 5 - 97) 26 ltac:(lia)).
  entailer!; lia.
Qed.

Lemma proof_of_encode_shift_safety_wit_8 : encode_shift_safety_wit_8.
Proof.
  unfold encode_shift_safety_wit_8. left.
  intros s0 l out out_l i n Hlt Hpre Hvalid Hn Hi0 Hin Hout Hprefix.
  pre_process.
  assert (Hidx : 0 <= i < Zlength l) by (unfold string_length in Hn; lia).
  pose proof (lower_input_at_50 l i Hpre Hvalid Hidx) as Hlower.
  rewrite Znth_c_string_50 by exact Hidx.
  entailer!; lia.
Qed.

Lemma proof_of_encode_shift_safety_wit_9 : encode_shift_safety_wit_9.
Proof.
  unfold encode_shift_safety_wit_9. left.
  intros s0 l out out_l i n Hlt Hpre Hvalid Hn Hi0 Hin Hout Hprefix.
  pre_process.
  assert (Hidx : 0 <= i < Zlength l) by (unfold string_length in Hn; lia).
  pose proof (lower_input_at_50 l i Hpre Hvalid Hidx) as Hlower.
  rewrite Znth_c_string_50 by exact Hidx.
  entailer!; lia.
Qed.

Lemma proof_of_encode_shift_entail_wit_1 : encode_shift_entail_wit_1.
Proof.
  unfold encode_shift_entail_wit_1. right.
  intros s_pre s0 l n out Hout1 Hout2 Hn Halloc Hs Hpre Hvalid Hbound.
  subst s0. pre_process.
  pose proof (string_length_nonnegative_50 l) as Hlen.
  pose proof (encode_prefix_nil_50 l) as Hnil.
  entailer!.
Qed.

Lemma proof_of_encode_shift_entail_wit_2 : encode_shift_entail_wit_2.
Proof.
  unfold encode_shift_entail_wit_2. right.
  intros l out_l i n Halloc Hlt Hpre Hvalid Hn Hi0 Hin Hout Hprefix.
  pre_process.
  assert (Hidx : 0 <= i < Zlength l) by (unfold string_length in Hn; lia).
  pose proof (encode_prefix_snoc_50 l out_l i Hpre Hvalid Hprefix Hout Hidx) as Hsnoc.
  entailer!.
  rewrite Zlength_app_cons. lia.
Qed.

Lemma proof_of_encode_shift_return_wit_1 : encode_shift_return_wit_1.
Proof.
  unfold encode_shift_return_wit_1. right.
  intros l out out_l i n Hi1 Halloc Hexit Hpre Hvalid Hn Hi0 Hin Hout Hprefix.
  pre_process.
  Exists out_l.
  unfold store_string, string_length, c_string.
  entailer!.
  - rewrite Hout. entailer!.
  - unfold string_length in Hn. lia.
Qed.

Lemma proof_of_encode_shift_partial_solve_wit_2_pure : encode_shift_partial_solve_wit_2_pure.
Proof.
  unfold encode_shift_partial_solve_wit_2_pure. left.
  intros s_pre s0 l n Hn Halloc Hs Hpre Hvalid Hbound.
  pre_process.
  pose proof (string_length_nonnegative_50 l).
  entailer!; lia.
Qed.

Lemma proof_of_decode_shift_safety_wit_6 : decode_shift_safety_wit_6.
Proof.
  unfold decode_shift_safety_wit_6. left.
  intros s0 l out out_l i n Hlt Hpre Hvalid Hn Hi0 Hin Hout Hprefix.
  pre_process.
  assert (Hidx : 0 <= i < Zlength l) by (unfold string_length in Hn; lia).
  pose proof (lower_input_at_50 l i Hpre Hvalid Hidx) as Hlower.
  rewrite Znth_c_string_50 by exact Hidx.
  pose proof (Z.rem_bound_abs (Znth i l 0 + 21 - 97) 26 ltac:(lia)).
  entailer!; lia.
Qed.

Lemma proof_of_decode_shift_safety_wit_8 : decode_shift_safety_wit_8.
Proof.
  unfold decode_shift_safety_wit_8. left.
  intros s0 l out out_l i n Hlt Hpre Hvalid Hn Hi0 Hin Hout Hprefix.
  pre_process.
  assert (Hidx : 0 <= i < Zlength l) by (unfold string_length in Hn; lia).
  pose proof (lower_input_at_50 l i Hpre Hvalid Hidx) as Hlower.
  rewrite Znth_c_string_50 by exact Hidx.
  entailer!; lia.
Qed.

Lemma proof_of_decode_shift_safety_wit_9 : decode_shift_safety_wit_9.
Proof.
  unfold decode_shift_safety_wit_9. left.
  intros s0 l out out_l i n Hlt Hpre Hvalid Hn Hi0 Hin Hout Hprefix.
  pre_process.
  assert (Hidx : 0 <= i < Zlength l) by (unfold string_length in Hn; lia).
  pose proof (lower_input_at_50 l i Hpre Hvalid Hidx) as Hlower.
  rewrite Znth_c_string_50 by exact Hidx.
  entailer!; lia.
Qed.

Lemma proof_of_decode_shift_entail_wit_1 : decode_shift_entail_wit_1.
Proof.
  unfold decode_shift_entail_wit_1. right.
  intros s_pre s0 l n out Hout1 Hout2 Hn Halloc Hs Hpre Hvalid Hbound.
  subst s0. pre_process.
  pose proof (string_length_nonnegative_50 l) as Hlen.
  pose proof (decode_prefix_nil_50 l) as Hnil.
  entailer!.
Qed.

Lemma proof_of_decode_shift_entail_wit_2 : decode_shift_entail_wit_2.
Proof.
  unfold decode_shift_entail_wit_2. right.
  intros l out_l i n Halloc Hlt Hpre Hvalid Hn Hi0 Hin Hout Hprefix.
  pre_process.
  assert (Hidx : 0 <= i < Zlength l) by (unfold string_length in Hn; lia).
  pose proof (decode_prefix_snoc_50 l out_l i Hpre Hvalid Hprefix Hout Hidx) as Hsnoc.
  entailer!.
  rewrite Zlength_app_cons. lia.
Qed.

Lemma proof_of_decode_shift_return_wit_1 : decode_shift_return_wit_1.
Proof.
  unfold decode_shift_return_wit_1. right.
  intros l out out_l i n Hi1 Halloc Hexit Hpre Hvalid Hn Hi0 Hin Hout Hprefix.
  pre_process.
  assert (Hlen : Zlength out_l = Zlength l)
    by (unfold string_length in Hn; lia).
  pose proof (decode_prefix_full_spec_50 l out_l Hpre Hvalid Hprefix Hlen) as Hspec.
  Exists out_l.
  unfold store_string, string_length, c_string.
  entailer!.
  rewrite Hout. entailer!.
Qed.

Lemma proof_of_decode_shift_partial_solve_wit_2_pure : decode_shift_partial_solve_wit_2_pure.
Proof.
  unfold decode_shift_partial_solve_wit_2_pure. left.
  intros s_pre s0 l n Hn Halloc Hs Hpre Hvalid Hbound.
  pre_process.
  pose proof (string_length_nonnegative_50 l).
  entailer!; lia.
Qed.

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
From SimpleC.EE Require Import C_61_goal.
From SimpleC.EE Require Import C_61_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_61.
Local Open Scope sac.

Lemma proof_of_correct_bracketing_entail_wit_1 : correct_bracketing_entail_wit_1.
Proof.
  left.
  pre_process.
  entailer!.
  apply bracket_safe_initial_61; auto.
  subst retval. unfold string_length. apply Zlength_nonneg.
Qed.

Lemma proof_of_correct_bracketing_entail_wit_2 : correct_bracketing_entail_wit_2.
Proof.
  left.
  pre_process.
  entailer!.
  eapply bracket_safe_open_61; eauto.
  - unfold string_length in *; lia.
  - assert (Hidx : 0 <= i < string_length str_l) by lia.
    pose proof (c_string_Znth_inside str_l i 0 Hidx) as Hcin.
    rewrite <- Hcin.
    exact PreH1.
Qed.

Lemma proof_of_correct_bracketing_entail_wit_3 : correct_bracketing_entail_wit_3.
Proof.
  left.
  pre_process.
  assert (Hlevel0 : level = 0) by lia.
  assert (Hidx : 0 <= i < string_length str_l) by lia.
  assert (Hi_bounds : 0 <= i < Zlength str_l) by (unfold string_length in *; lia).
  pose proof (c_string_Znth_inside str_l i 0 Hidx) as Hcin.
  assert (Hclose : Znth i str_l 0 = 41).
  {
    destruct (bracket_safe_char_61 str_l i PreH14 Hi_bounds) as [Hopen | Hclose].
    - rewrite <- Hcin in Hopen. contradiction.
    - exact Hclose.
  }
  entailer!.
  - eapply bracket_safe_close_negative_61 with (i := i); eauto.
    + rewrite Hlevel0 in PreH16. exact PreH16.
    + unfold string_length in *; lia.
Qed.

Lemma proof_of_correct_bracketing_entail_wit_4 : correct_bracketing_entail_wit_4.
Proof.
  left.
  pre_process.
  assert (Hpos : 0 < level) by lia.
  assert (Hidx : 0 <= i < string_length str_l) by lia.
  assert (Hi_bounds : 0 <= i < Zlength str_l) by (unfold string_length in *; lia).
  pose proof (c_string_Znth_inside str_l i 0 Hidx) as Hcin.
  assert (Hclose : Znth i str_l 0 = 41).
  {
    destruct (bracket_safe_char_61 str_l i PreH14 Hi_bounds) as [Hopen | Hclose].
    - rewrite <- Hcin in Hopen. contradiction.
    - exact Hclose.
  }
  entailer!.
  eapply bracket_safe_close_continue_61; eauto.
  unfold string_length in *; lia.
Qed.

Lemma proof_of_correct_bracketing_entail_wit_6 : correct_bracketing_entail_wit_6.
Proof.
  left.
  pre_process.
  assert (Hi : i = n) by lia.
  subst i.
  entailer!.
  eapply bracket_safe_final_false_61; eauto.
  replace (Zlength str_l) with n by (unfold string_length in *; lia).
  exact PreH15.
Qed.

Lemma proof_of_correct_bracketing_entail_wit_7 : correct_bracketing_entail_wit_7.
Proof.
  left.
  pre_process.
  assert (Hi : i = n) by lia.
  subst i.
  subst level.
  entailer!.
  eapply bracket_safe_final_true_61; eauto.
  replace (Zlength str_l) with n by (unfold string_length in *; lia).
  exact PreH15.
Qed.

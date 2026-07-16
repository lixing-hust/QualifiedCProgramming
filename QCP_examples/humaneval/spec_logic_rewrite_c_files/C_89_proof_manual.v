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
From SimpleC.EE Require Import C_89_goal.
From SimpleC.EE Require Import C_89_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_89.
Local Open Scope sac.

Lemma proof_of_encrypt_safety_wit_6 : encrypt_safety_wit_6.
Proof.
  right.
  pre_process_default.
  assert (Hi : 0 <= i < string_length input) by lia.
  pose proof (lowercase_c_string_code_89 input i PreH6 Hi) as Hcode.
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound
    (Znth i (c_string input) 0 + 4 - 97) 26 ltac:(lia)) as Hmod.
  entailer!; lia.
Qed.

Lemma proof_of_encrypt_safety_wit_8 : encrypt_safety_wit_8.
Proof.
  right.
  pre_process_default.
  assert (Hi : 0 <= i < string_length input) by lia.
  pose proof (lowercase_c_string_code_89 input i PreH6 Hi) as Hcode.
  entailer!; lia.
Qed.

Lemma proof_of_encrypt_safety_wit_9 : encrypt_safety_wit_9.
Proof.
  right.
  pre_process_default.
  assert (Hi : 0 <= i < string_length input) by lia.
  pose proof (lowercase_c_string_code_89 input i PreH6 Hi) as Hcode.
  entailer!; lia.
Qed.

Lemma proof_of_encrypt_entail_wit_1 : encrypt_entail_wit_1.
Proof.
  right.
  pre_process_default.
  entailer!.
  - eapply problem_89_pre_z_lowercase; eauto.
  - subst retval.
    apply string_length_nonneg.
  - apply rotate_prefix_z_89_nil.
Qed.

Lemma proof_of_encrypt_entail_wit_2 : encrypt_entail_wit_2.
Proof.
  right.
  pre_process_default.
  entailer!.
  eapply rotate_prefix_z_89_snoc.
  - subst n.
    exact (conj PreH9 PreH2).
  - exact PreH11.
  - apply c_shift_byte_eq_89; [exact PreH7 |].
    subst n. lia.
Qed.

Lemma proof_of_encrypt_return_wit_1 : encrypt_return_wit_1.
Proof.
  right.
  pre_process_default.
  Exists output_2.
  assert (Hi : i = string_length input) by lia.
  assert (Hspec : problem_89_spec_z input output_2).
  { eapply problem_89_spec_z_intro; eauto.
    unfold string_length in Hi.
    rewrite <- Hi.
    exact PreH12. }
  unfold store_string, c_string, string_length.
  entailer!.
  destruct PreH12 as [Hlen _].
  rewrite Hlen.
  reflexivity.
Qed.

Lemma proof_of_encrypt_partial_solve_wit_2_pure : encrypt_partial_solve_wit_2_pure.
Proof.
  right.
  pre_process_default.
  entailer!.
  subst retval.
  pose proof (string_length_nonneg input).
  lia.
Qed.

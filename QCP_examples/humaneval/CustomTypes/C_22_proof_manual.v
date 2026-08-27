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
From SimpleC.EE Require Import C_22_goal.
From SimpleC.EE Require Import C_22_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_22.
Local Open Scope sac.

Lemma proof_of_filter_integers_entail_wit_1 : filter_integers_entail_wit_1.
Proof.
  unfold filter_integers_entail_wit_1.
  left. intros.
  Exists (@nil Z) 0.
  simpl.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
Qed.

Lemma proof_of_filter_integers_entail_wit_2_1 : filter_integers_entail_wit_2_1.
Proof.
  unfold filter_integers_entail_wit_2_1.
  left. intros.
  assert (Hlen : Zlength types_l = Zlength ints_l) by lia.
  pose proof (filter_tagged_prefix_int types_l ints_l i Hlen ltac:(lia) PreH1) as Hstep.
  rewrite <- PreH12 in Hstep.
  Exists (app output_l_2 (cons (Znth i ints_l 0) nil)) (output_size_2 + 1).
  rewrite Hstep.
  rewrite Zlength_app. simpl.
  entailer!.
  rewrite Zlength_correct in PreH11 |- *.
  simpl.
  replace (Zlength (Znth i ints_l 0 :: nil)) with 1 by reflexivity.
  lia.
Qed.

Lemma proof_of_filter_integers_entail_wit_2_2 : filter_integers_entail_wit_2_2.
Proof.
  unfold filter_integers_entail_wit_2_2.
  left. intros.
  assert (Hlen : Zlength types_l = Zlength ints_l) by lia.
  pose proof (filter_tagged_prefix_nonint types_l ints_l i Hlen ltac:(lia) PreH1) as Hstep.
  rewrite <- PreH12 in Hstep.
  Exists output_l_2 output_size_2.
  rewrite Hstep.
  entailer!.
Qed.

Lemma proof_of_filter_integers_return_wit_1 : filter_integers_return_wit_1.
Proof.
  unfold filter_integers_return_wit_1.
  left. intros.
  assert (Hi : i = values_size_pre) by lia.
  subst i.
  rewrite sublist_self in PreH11 by lia.
  rewrite sublist_self in PreH11 by lia.
  assert (Hspec : problem_22_spec_z input_l output_l_2).
  {
    eapply problem_22_spec_z_of_filter_tagged.
    - exact PreH2.
    - exact PreH3.
    - exact PreH11.
  }
  Exists output_l_2 output_size_2 data_2.
  entailer!.
Qed.

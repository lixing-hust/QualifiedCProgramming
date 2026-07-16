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
From SimpleC.EE Require Import C_140_goal.
From SimpleC.EE Require Import C_140_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_140.
Local Open Scope sac.

Lemma proof_of_fix_spaces_entail_wit_1 : fix_spaces_entail_wit_1.
Proof.
  right; intros.
  entailer!.
  - subst retval. apply string_length_nonneg.
  - apply fix_spaces_state_z_140_init.
Qed.

Lemma proof_of_fix_spaces_entail_wit_2_1 : fix_spaces_entail_wit_2_1.
Proof.
  right; intros.
  assert (spacelen = 0) by lia; subst spacelen.
  pose proof (fix_spaces_state_z_140_char input output_2 i 0
    ltac:(unfold string_length in *; lia) PreH5 PreH14) as Hstep.
  unfold flush_spaces_z_140 in Hstep. simpl in Hstep.
  entailer!.
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_fix_spaces_entail_wit_2_2 : fix_spaces_entail_wit_2_2.
Proof.
  right; intros. subst spacelen.
  pose proof (fix_spaces_state_z_140_char input output_2 i 1
    ltac:(unfold string_length in *; lia) PreH6 PreH15) as Hstep.
  unfold flush_spaces_z_140 in Hstep. simpl in Hstep.
  entailer!.
  - rewrite !Zlength_app, !Zlength_cons, Zlength_nil. lia.
  - rewrite <- app_assoc. exact Hstep.
Qed.

Lemma proof_of_fix_spaces_entail_wit_2_3 : fix_spaces_entail_wit_2_3.
Proof.
  right; intros. subst spacelen.
  pose proof (fix_spaces_state_z_140_char input output_2 i 2
    ltac:(unfold string_length in *; lia) PreH7 PreH16) as Hstep.
  unfold flush_spaces_z_140 in Hstep. simpl in Hstep.
  entailer!.
  - rewrite !Zlength_app, !Zlength_cons, Zlength_nil. lia.
  - repeat rewrite <- app_assoc. exact Hstep.
Qed.

Lemma proof_of_fix_spaces_entail_wit_2_4 : fix_spaces_entail_wit_2_4.
Proof.
  right; intros.
  pose proof (fix_spaces_state_z_140_char input output_2 i spacelen
    ltac:(unfold string_length in *; lia) PreH6 PreH15) as Hstep.
  unfold flush_spaces_z_140 in Hstep.
  destruct (Z.eq_dec spacelen 0); [lia |].
  destruct (Z.eq_dec spacelen 1); [lia |].
  destruct (Z.eq_dec spacelen 2); [lia |].
  entailer!.
  - rewrite !Zlength_app, !Zlength_cons, Zlength_nil. lia.
  - rewrite <- app_assoc. exact Hstep.
Qed.

Lemma proof_of_fix_spaces_entail_wit_2_5 : fix_spaces_entail_wit_2_5.
Proof.
  right; intros.
  pose proof (fix_spaces_state_z_140_space input output_2 i spacelen
    ltac:(unfold string_length in *; lia) PreH2 PreH11) as Hstep.
  entailer!.
Qed.

Lemma proof_of_fix_spaces_entail_wit_4_1 : fix_spaces_entail_wit_4_1.
Proof.
  right; intros.
  assert (i = n) by lia; subst i.
  assert (spacelen = 0) by lia; subst spacelen.
  Exists output_2.
  unfold flush_spaces_z_140. simpl.
  entailer!.
  - rewrite app_nil_r. exact PreH12.
  - rewrite app_nil_r. reflexivity.
Qed.

Lemma proof_of_fix_spaces_entail_wit_4_2 : fix_spaces_entail_wit_4_2.
Proof.
  right; intros.
  assert (i = n) by lia; subst i. subst spacelen.
  Exists output_2.
  unfold flush_spaces_z_140. simpl.
  entailer!.
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_fix_spaces_entail_wit_4_3 : fix_spaces_entail_wit_4_3.
Proof.
  right; intros.
  assert (i = n) by lia; subst i. subst spacelen.
  Exists output_2.
  unfold flush_spaces_z_140. simpl.
  entailer!.
  rewrite !Zlength_app, !Zlength_cons, Zlength_nil. lia.
  symmetry.
  change (output_2 ++ (95 :: nil) ++ (95 :: nil) =
    (output_2 ++ (95 :: nil)) ++ (95 :: nil)).
  apply app_assoc.
Qed.

Lemma proof_of_fix_spaces_entail_wit_4_4 : fix_spaces_entail_wit_4_4.
Proof.
  right; intros.
  assert (i = n) by lia; subst i.
  Exists output_2.
  unfold flush_spaces_z_140.
  destruct (Z.eq_dec spacelen 0); [lia |].
  destruct (Z.eq_dec spacelen 1); [lia |].
  destruct (Z.eq_dec spacelen 2); [lia |].
  entailer!.
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_fix_spaces_return_wit_1 : fix_spaces_return_wit_1.
Proof.
  right; intros.
  Exists output_2.
  assert (Hspec : problem_140_spec_z input output_2).
  { eapply problem_140_spec_z_from_state.
    - exact PreH10.
    - subst n. unfold string_length in PreH9. exact PreH9.
    - exact PreH8. }
  unfold string_length in PreH3.
  subst n. subst k.
  unfold store_string, string_length, c_string.
  entailer!.
Qed.

Lemma proof_of_fix_spaces_partial_solve_wit_2_pure : fix_spaces_partial_solve_wit_2_pure.
Proof.
  right; intros.
  subst retval.
  pose proof (string_length_nonneg input).
  entailer!; lia.
Qed.

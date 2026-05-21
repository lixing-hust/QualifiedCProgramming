Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_140_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_140.
Local Open Scope sac.

Lemma proof_of_fix_spaces_entail_wit_1 : fix_spaces_entail_wit_1.
Proof.
  unfold fix_spaces_entail_wit_1.
  intros.
  pre_process.
  subst retval_2.
  Exists (@nil Z).
  destruct (fix_spaces_state_z_0 l) as [Hp Hpend].
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (len + 1)).
  rewrite (CharArray.undef_seg_empty retval 0).
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  - lia.
Qed.

Lemma proof_of_fix_spaces_entail_wit_2_1 : fix_spaces_entail_wit_2_1.
Proof.
  unfold fix_spaces_entail_wit_2_1.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  Exists out_l_2.
  entailer!.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_space i l ltac:(lia) ltac:(assumption)) as [_ Hpend].
    symmetry; exact Hpend.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_space i l ltac:(lia) ltac:(assumption)) as [Hp _].
    symmetry; exact Hp.
Qed.

Lemma proof_of_fix_spaces_entail_wit_2_2 : fix_spaces_entail_wit_2_2.
Proof.
  unfold fix_spaces_entail_wit_2_2.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  assert (Hsp0 : spacelen = 0) by lia.
  rewrite (signed_last_nbits_eq (Znth i l 0) 8) by
    (pose proof (H7 i ltac:(lia)); lia).
  Exists (out_l_2 ++ cons (Znth i l 0) nil).
  entailer!.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending0 i l ltac:(lia) ltac:(assumption) ltac:(exact Hsp0))
      as [_ Hpend].
    symmetry; exact Hpend.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending0 i l ltac:(lia) ltac:(assumption) ltac:(exact Hsp0))
      as [Hp _].
    symmetry; exact Hp.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_fix_spaces_entail_wit_2_3 : fix_spaces_entail_wit_2_3.
Proof.
  unfold fix_spaces_entail_wit_2_3.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  rewrite (signed_last_nbits_eq (Znth i l 0) 8) by
    (pose proof (H8 i ltac:(lia)); lia).
  Exists ((out_l_2 ++ cons 45 nil) ++ cons (Znth i l 0) nil).
  entailer!.
  - subst out_l_2.
    destruct (fix_spaces_step_nonspace_pending_more i l spacelen ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(lia))
      as [_ Hpend].
    symmetry; exact Hpend.
  - subst out_l_2.
    destruct (fix_spaces_step_nonspace_pending_more i l spacelen ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(lia))
      as [Hp _].
    symmetry; exact Hp.
  - rewrite !Zlength_app, !Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_fix_spaces_entail_wit_2_4 : fix_spaces_entail_wit_2_4.
Proof.
  unfold fix_spaces_entail_wit_2_4.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  rewrite (signed_last_nbits_eq (Znth i l 0) 8) by
    (pose proof (H8 i ltac:(lia)); lia).
  Exists (((out_l_2 ++ cons 95 nil) ++ cons 95 nil) ++ cons (Znth i l 0) nil).
  entailer!.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending2 i l ltac:(lia) ltac:(assumption) ltac:(symmetry; exact H17))
      as [_ Hpend].
    symmetry; exact Hpend.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending2 i l ltac:(lia) ltac:(assumption) ltac:(symmetry; exact H17))
      as [Hp _].
    symmetry; exact Hp.
  - rewrite !Zlength_app, !Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_fix_spaces_entail_wit_2_5 : fix_spaces_entail_wit_2_5.
Proof.
  unfold fix_spaces_entail_wit_2_5.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  rewrite (signed_last_nbits_eq (Znth i l 0) 8) by
    (pose proof (H6 i ltac:(lia)); lia).
  Exists ((out_l_2 ++ cons 95 nil) ++ cons (Znth i l 0) nil).
  entailer!.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending1 i l ltac:(lia) ltac:(assumption) ltac:(symmetry; exact H15))
      as [_ Hpend].
    symmetry; exact Hpend.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending1 i l ltac:(lia) ltac:(assumption) ltac:(symmetry; exact H15))
      as [Hp _].
    symmetry; exact Hp.
  - rewrite !Zlength_app, !Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_fix_spaces_return_wit_1 : fix_spaces_return_wit_1.
Proof.
  unfold fix_spaces_return_wit_1.
  intros.
  pre_process.
  assert (Hsp0 : spacelen = 0) by lia.
  Exists out_l_2 k.
  entailer!.
  - subst out_l_2.
    apply problem_140_spec_z_intro.
    + assumption.
    + 
    replace i with (Zlength l) by lia.
    symmetry.
    apply fix_spaces_output_pending0.
    replace (fix_spaces_pending_z (Zlength l) l)
      with (fix_spaces_pending_z i l) by (replace i with (Zlength l) by lia; reflexivity).
    rewrite <- H15.
    exact Hsp0.
Qed.

Lemma proof_of_fix_spaces_return_wit_2 : fix_spaces_return_wit_2.
Proof.
  unfold fix_spaces_return_wit_2.
  intros.
  pre_process.
  Exists (out_l_2 ++ cons 45 nil) (k + 1).
  entailer!.
  subst out_l_2.
  apply problem_140_spec_z_intro.
  - assumption.
  -
    replace i with (Zlength l) by lia.
    symmetry.
    apply fix_spaces_output_pending_more with (p := spacelen).
    + replace (fix_spaces_pending_z (Zlength l) l)
        with (fix_spaces_pending_z i l) by (replace i with (Zlength l) by lia; reflexivity).
      match goal with
      | H : spacelen = fix_spaces_pending_z i l |- _ => exact H
      end.
    + lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_fix_spaces_return_wit_3 : fix_spaces_return_wit_3.
Proof.
  unfold fix_spaces_return_wit_3.
  intros.
  pre_process.
  Exists ((out_l_2 ++ cons 95 nil) ++ cons 95 nil) ((k + 1) + 1).
  entailer!.
  subst out_l_2 spacelen.
  apply problem_140_spec_z_intro.
  - assumption.
  -
    replace i with (Zlength l) by lia.
    symmetry.
    rewrite fix_spaces_output_pending2.
    2:{
      replace (fix_spaces_pending_z (Zlength l) l)
        with (fix_spaces_pending_z i l) by (replace i with (Zlength l) by lia; reflexivity).
      symmetry; exact H16.
    }
    rewrite <- app_assoc.
    reflexivity.
  - rewrite !Zlength_app, !Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_fix_spaces_return_wit_4 : fix_spaces_return_wit_4.
Proof.
  unfold fix_spaces_return_wit_4.
  intros.
  pre_process.
  Exists (out_l_2 ++ cons 95 nil) (k + 1).
  entailer!.
  subst out_l_2 spacelen.
  apply problem_140_spec_z_intro.
  - assumption.
  -
    replace i with (Zlength l) by lia.
    symmetry.
    apply fix_spaces_output_pending1.
    replace (fix_spaces_pending_z (Zlength l) l)
      with (fix_spaces_pending_z i l) by (replace i with (Zlength l) by lia; reflexivity).
    match goal with
    | H : 1 = fix_spaces_pending_z i l |- _ =>
        symmetry; exact H
    end.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

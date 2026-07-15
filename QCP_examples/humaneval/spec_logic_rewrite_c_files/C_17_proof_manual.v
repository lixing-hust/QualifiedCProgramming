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
From SimpleC.EE Require Import C_17_goal.
From SimpleC.EE Require Import C_17_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_17.
Local Open Scope sac.

Lemma proof_of_parse_music_entail_wit_1 : parse_music_entail_wit_1.
Proof.
  left; intros.
  Exists (@nil Z).
  sep_apply (IntArray.undef_full_split_to_undef_seg retval_3 0 (retval + 1)).
  rewrite IntArray.seg_empty.
  rewrite (IntArray.undef_seg_empty retval_3 0).
  unfold store_string; entailer!.
  - eauto using music_safe_initial_17.
  - subst retval; unfold string_length; apply Zlength_nonneg.
  - subst retval; unfold string_length; pose proof (Zlength_nonneg str_l); lia.
Qed.

Lemma proof_of_parse_music_entail_wit_2 : parse_music_entail_wit_2.
Proof.
  left; intros.
  Exists output_l_2.
  unfold store_string; entailer!.
  eapply music_safe_space_17; eauto.
  unfold string_length in PreH5; lia.
Qed.

Lemma proof_of_parse_music_entail_wit_3 : parse_music_entail_wit_3.
Proof.
  left; intros.
  Exists (output_l_2 ++ (2 :: nil))%list.
  unfold store_string; entailer!.
  - eapply music_safe_half_17; eauto.
    unfold string_length in PreH9; lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_parse_music_entail_wit_4_1 : parse_music_entail_wit_4_1.
Proof.
  right; intros.
  entailer!.
  entailer!.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
  - eapply music_safe_whole_17; eauto.
    + unfold string_length in PreH8; lia.
    + left; unfold string_length in PreH8; lia.
Qed.

Lemma proof_of_parse_music_entail_wit_4_2 : parse_music_entail_wit_4_2.
Proof.
  right; intros.
  assert (Hnext_idx : 0 <= i + 1 /\ i + 1 <= string_length str_l).
  { split; [lia | rewrite <- PreH9; lia]. }
  pose proof (c_string_char_bound str_l (i + 1) PreH22 Hnext_idx) as Hnext_char.
  entailer!.
  entailer!.
  entailer!.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
  - eapply music_safe_whole_17; eauto.
    unfold string_length in PreH9; lia.
Qed.

Lemma proof_of_parse_music_entail_wit_5 : parse_music_entail_wit_5.
Proof.
  right; intros.
  assert (Hi_len : i < Zlength str_l) by (unfold string_length in PreH7; lia).
  pose proof (music_safe_dot_info_17 str_l i output_l_2 PreH23 PreH25 Hi_len PreH3 PreH2)
    as [Hdot [Hnext Hbar]].
  entailer!.
  entailer!.
  - unfold string_length in PreH7; lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
  - eapply music_safe_dot_17; eauto.
Qed.

Lemma proof_of_parse_music_entail_wit_7 : parse_music_entail_wit_7.
Proof.
  left; intros.
  assert (Hfinal : output_l = music_output_17 str_l).
  { eapply music_safe_final_17; eauto.
    unfold string_length in *; lia. }
  subst output_l.
  unfold store_string; entailer!.
  - eauto using music_safe_spec_17.
Qed.

Lemma proof_of_parse_music_return_wit_1 : parse_music_return_wit_1.
Proof.
  left; intros.
  Exists (music_output_17 str_l) data_2.
  subst out_size cap n.
  unfold store_string; entailer!; auto.
Qed.

Lemma proof_of_parse_music_partial_solve_wit_3_pure : parse_music_partial_solve_wit_3_pure.
Proof.
  right; intros.
  pre_process; entailer!.
  subst retval.
  pose proof (Zlength_nonneg str_l).
  unfold string_length in *; lia.
Qed.

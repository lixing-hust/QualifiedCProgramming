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
Require Import SimpleC.EE.C_91_goal.
Require Import SimpleC.EE.C_91_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_91.
Local Open Scope sac.

Lemma proof_of_is_bored_entail_wit_1 : is_bored_entail_wit_1.
Proof.
  unfold is_bored_entail_wit_1; left; intros; subst.
  unfold bored_sum_prefix_z, bored_isstart_prefix_z, bored_isi_prefix_z.
  simpl. entailer!.
  unfold string_length. rewrite Zlength_correct. lia.
Qed.

Lemma proof_of_is_bored_entail_wit_2_1 : is_bored_entail_wit_2_1.
Proof.
  unfold is_bored_entail_wit_2_1; left; intros; subst.
  unfold c_string in *.
  rewrite app_Znth1 in PreH1, PreH2, PreH3, PreH4, PreH5
    by (unfold string_length in *; lia).
  rewrite bored_sum_prefix_step_91 by lia.
  rewrite bored_isstart_prefix_step_91 by lia.
  rewrite bored_isi_prefix_step_91 by lia.
  unfold bored_add_z, bored_next_isstart_z, bored_next_isi_z,
    bored_is_space_z, bored_is_i_z, bored_is_delimiter_z, zbool_91.
  rewrite PreH1. cbn. entailer!.
Qed.

Lemma proof_of_is_bored_entail_wit_2_2 : is_bored_entail_wit_2_2.
Proof.
  unfold is_bored_entail_wit_2_2; left; intros; subst.
  unfold c_string in *.
  rewrite app_Znth1 in PreH1, PreH2, PreH3, PreH4
    by (unfold string_length in *; lia).
  rewrite bored_sum_prefix_step_91 by lia.
  rewrite bored_isstart_prefix_step_91 by lia.
  rewrite bored_isi_prefix_step_91 by lia.
  unfold bored_add_z, bored_next_isstart_z, bored_next_isi_z,
    bored_is_space_z, bored_is_i_z, bored_is_delimiter_z, zbool_91.
  rewrite PreH1. cbn. entailer!.
Qed.

Lemma proof_of_is_bored_entail_wit_2_3 : is_bored_entail_wit_2_3.
Proof.
  unfold is_bored_entail_wit_2_3; left; intros; subst.
  unfold c_string in *.
  rewrite app_Znth1 in PreH1, PreH2, PreH3, PreH4, PreH5, PreH6
    by (unfold string_length in *; lia).
  rewrite bored_sum_prefix_step_91 by lia.
  rewrite bored_isstart_prefix_step_91 by lia.
  rewrite bored_isi_prefix_step_91 by lia.
  unfold bored_add_z, bored_next_isstart_z, bored_next_isi_z,
    bored_is_space_z, bored_is_i_z, bored_is_delimiter_z, zbool_91.
  rewrite PreH1. cbn. entailer!.
Qed.

Lemma proof_of_is_bored_entail_wit_2_4 : is_bored_entail_wit_2_4.
Proof.
  unfold is_bored_entail_wit_2_4; left; intros; subst.
  unfold c_string in *.
  rewrite app_Znth1 in PreH1, PreH2, PreH3, PreH4, PreH6, PreH7
    by (unfold string_length in *; lia).
  rewrite bored_sum_prefix_step_91 by lia.
  rewrite bored_isstart_prefix_step_91 by lia.
  rewrite bored_isi_prefix_step_91 by lia.
  unfold bored_add_z, bored_next_isstart_z, bored_next_isi_z,
    bored_is_space_z, bored_is_i_z, bored_is_delimiter_z, zbool_91.
  rewrite PreH6, <- PreH16. cbn. entailer!.
Qed.

Lemma proof_of_is_bored_entail_wit_2_5 : is_bored_entail_wit_2_5.
Proof.
  unfold is_bored_entail_wit_2_5; left; intros; subst.
  unfold c_string in *.
  rewrite app_Znth1 in PreH1, PreH2, PreH3, PreH4, PreH5, PreH6
    by (unfold string_length in *; lia).
  rewrite bored_sum_prefix_step_91 by lia.
  rewrite bored_isstart_prefix_step_91 by lia.
  rewrite bored_isi_prefix_step_91 by lia.
  unfold bored_add_z, bored_next_isstart_z, bored_next_isi_z,
    bored_is_space_z, bored_is_i_z, bored_is_delimiter_z, zbool_91.
  assert (E33 : Z.eqb (Znth i input 0) 33 = false)
    by (apply Z.eqb_neq; exact PreH1).
  assert (E63 : Z.eqb (Znth i input 0) 63 = false)
    by (apply Z.eqb_neq; exact PreH2).
  assert (E46 : Z.eqb (Znth i input 0) 46 = false)
    by (apply Z.eqb_neq; exact PreH3).
  assert (E32 : Z.eqb (Znth i input 0) 32 = false)
    by (apply Z.eqb_neq; exact PreH4).
  assert (E73 : Z.eqb (Znth i input 0) 73 = false)
    by (apply Z.eqb_neq; exact PreH5).
  rewrite E33, E63, E46, E32, E73. cbn. entailer!.
Qed.

Lemma proof_of_is_bored_entail_wit_2_6 : is_bored_entail_wit_2_6.
Proof.
  unfold is_bored_entail_wit_2_6; left; intros; subst.
  unfold c_string in *.
  rewrite app_Znth1 in PreH1, PreH2, PreH3, PreH4, PreH6, PreH7
    by (unfold string_length in *; lia).
  rewrite bored_sum_prefix_step_91 by lia.
  rewrite bored_isstart_prefix_step_91 by lia.
  rewrite bored_isi_prefix_step_91 by lia.
  unfold bored_add_z, bored_next_isstart_z, bored_next_isi_z,
    bored_is_space_z, bored_is_i_z, bored_is_delimiter_z, zbool_91.
  assert (Es : Z.eqb (bored_isstart_prefix_z i input) 1 = false)
    by (apply Z.eqb_neq; exact PreH5).
  rewrite PreH6, Es. cbn. entailer!.
Qed.

Lemma proof_of_is_bored_entail_wit_2_7 : is_bored_entail_wit_2_7.
Proof.
  unfold is_bored_entail_wit_2_7; left; intros; subst.
  unfold c_string in *.
  rewrite app_Znth1 in PreH1, PreH2, PreH3, PreH4, PreH5, PreH7
    by (unfold string_length in *; lia).
  rewrite bored_sum_prefix_step_91 by lia.
  rewrite bored_isstart_prefix_step_91 by lia.
  rewrite bored_isi_prefix_step_91 by lia.
  unfold bored_add_z, bored_next_isstart_z, bored_next_isi_z,
    bored_is_space_z, bored_is_i_z, bored_is_delimiter_z, zbool_91.
  assert (Ei : Z.eqb (bored_isi_prefix_z i input) 1 = false)
    by (apply Z.eqb_neq; exact PreH6).
  rewrite PreH4, Ei. cbn. entailer!.
Qed.

Lemma proof_of_is_bored_entail_wit_2_8 : is_bored_entail_wit_2_8.
Proof.
  unfold is_bored_entail_wit_2_8; left; intros; subst.
  unfold c_string in *.
  rewrite app_Znth1 in PreH1, PreH2, PreH3, PreH4, PreH5, PreH7
    by (unfold string_length in *; lia).
  rewrite bored_sum_prefix_step_91 by lia.
  rewrite bored_isstart_prefix_step_91 by lia.
  rewrite bored_isi_prefix_step_91 by lia.
  unfold bored_add_z, bored_next_isstart_z, bored_next_isi_z,
    bored_is_space_z, bored_is_i_z, bored_is_delimiter_z, zbool_91.
  rewrite PreH4, <- PreH17. cbn. entailer!.
Qed.

Lemma proof_of_is_bored_return_wit_1 : is_bored_return_wit_1.
Proof.
  unfold is_bored_return_wit_1; left; intros; subst.
  entailer!.
  assert (i = string_length input) by lia. subst i.
  apply problem_91_from_bored_sum_91. exact PreH3.
Qed.

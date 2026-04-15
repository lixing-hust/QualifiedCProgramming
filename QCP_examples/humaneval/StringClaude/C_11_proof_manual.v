Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_11_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_11.
Local Open Scope sac.

Lemma proof_of_string_xor_entail_wit_2 : string_xor_entail_wit_2.
Proof.
  unfold string_xor_entail_wit_2.
  intros.
  Right.
  Exists (@nil Z).
  pre_process.
  subst retval_2 retval_3 nb.
  replace (Zlength l2 + 1) with (na + 1) by lia.
  rewrite <- H14.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (na + 1)).
  rewrite (CharArray.undef_seg_empty retval 0).
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  all: entailer!.
  all: try lia.
Qed.

Lemma proof_of_string_xor_entail_wit_3_1 : string_xor_entail_wit_3_1.
Proof.
  unfold string_xor_entail_wit_3_1.
  intros.
  Right.
  Exists (app out_l_2 (cons 48 nil)).
  pre_process.
  rewrite (Zlength_app_cons out_l_2 48).
  entailer!.
  intros k Hk.
  destruct (Z_lt_ge_dec k i).
  - rewrite app_Znth1 by lia.
    apply H13. lia.
  - assert (k = i) by lia. subst k.
    rewrite app_Znth2 by lia.
    replace (i - Zlength out_l_2) with 0 by lia.
    rewrite Znth0_cons.
    rewrite app_Znth1 in H by lia.
    rewrite app_Znth1 in H by lia.
    left; split; auto.
Qed.

Lemma proof_of_string_xor_entail_wit_3_2 : string_xor_entail_wit_3_2.
Proof.
  unfold string_xor_entail_wit_3_2.
  intros.
  Right.
  Exists (app out_l_2 (cons 49 nil)).
  pre_process.
  rewrite (Zlength_app_cons out_l_2 49).
  entailer!.
  intros k Hk.
  destruct (Z_lt_ge_dec k i).
  - rewrite app_Znth1 by lia.
    apply H13. lia.
  - assert (k = i) by lia. subst k.
    rewrite app_Znth2 by lia.
    replace (i - Zlength out_l_2) with 0 by lia.
    rewrite Znth0_cons.
    rewrite app_Znth1 in H by lia.
    rewrite app_Znth1 in H by lia.
    right; split; auto.
Qed.

Lemma proof_of_string_xor_return_wit_1 : string_xor_return_wit_1.
Proof.
  unfold string_xor_return_wit_1.
  intros.
  Right.
  Exists out_l_2 na.
  pre_process.
  assert (Hi : i = na) by lia.
  subst i.
  assert (Hout_len : Zlength out_l_2 = na) by lia.
  rewrite Hout_len.
  rewrite (CharArray.undef_seg_empty output (na + 1)).
  entailer!.
  apply problem_11_spec_z_intro with (n := na); try lia.
  intros k Hk.
  apply H12. lia.
Qed.

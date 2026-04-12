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
From SimpleC.EE.LLM_friendly_cases Require Import sll_split_while_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.LLM_friendly_cases Require Import sll_lib.
From SimpleC.EE.LLM_friendly_cases Require Import sll_merge_rel_lib.
Local Open Scope monad.
Local Open Scope sac.

Lemma proof_of_split_while_entail_wit_2 : split_while_entail_wit_2.
Proof.
  pre_process.
  sep_apply (sll_not_zero x l_2); [ | auto ].
  Intros x_next x_data l1_new.
  Exists q_v_2.
  Exists p_v_2.
  Exists x_next.
  Exists x_data.
  Exists l1_new.
  Exists l_2.
  Exists l1_2.
  Exists l2_2.
  entailer!.
Qed.

Lemma proof_of_split_while_entail_wit_3 : split_while_entail_wit_3.
Proof.
  pre_process.
  Exists q_v_2.
  Exists p_v_2.
  Exists x.
  Exists l_2.
  Exists l1_new.
  Exists l2_2.
  Exists x_data_2.
  Exists l1_2.
  entailer!.
  apply store_ptr_undef_store_ptr.
  subst l_2.
  unfold split_rec_rel in H.
  rewrite (program_para_equiv (split_rec_rel_unfold)) in H.
  unfold split_rec_rel_f in H.
  unfold split_rec_rel.
  exact H.
Qed.

Lemma proof_of_split_while_entail_wit_4 : split_while_entail_wit_4.
Proof.
  pre_process.
  sep_apply (sll_not_zero x l_new); [ | auto ].
  Intros x_next x_data_2 l1_new.
  Exists x_next.
  Exists q_v_2.
  Exists p_v_2.
  Exists x_data_2.
  Exists l1_new.
  Exists l_new.
  Exists l2_2.
  Exists x_data_3.
  Exists l1_2.
  entailer!.
  sep_apply sllseg_len1; [ | auto ].
  sep_apply sllseg_sll.
  simpl ((_ :: _) ++ _).
  reflexivity.
Qed.

Lemma proof_of_split_while_entail_wit_5 : split_while_entail_wit_5.
Proof.
  pre_process.
  Exists p_v_2.
  Exists q_v_2.
  Exists x.
  Exists l_2.
  Exists l1_new.
  Exists x_data_2.
  Exists l1_2.
  Exists x_data_3.
  Exists l2_2.
  entailer!.
  + apply store_ptr_undef_store_ptr.
  + subst l_2.
    unfold split_rec_rel in H.
    rewrite (program_para_equiv (split_rec_rel_unfold)) in H.
    unfold split_rec_rel_f in H.
    rewrite bind_assoc in H.
    rewrite bind_2_reversepair_equiv_Id in H.
    rewrite bind_ret_right in H.
    unfold split_rec_rel.
    exact H.
Qed.

Lemma proof_of_split_while_entail_wit_6_1 : split_while_entail_wit_6_1.
Proof.
  pre_process.
  sep_apply (sll_zero x l_new); [ | auto ].
  Intros.
  subst.
  Exists q_v_2.
  Exists p_v_2.
  Exists nil.
  Exists (x_data :: l1_2).
  Exists l2_2.
  entailer!.
  + sep_apply sllseg_len1; [ | auto ].
    sep_apply sllseg_sll.
    simpl ((_ :: _) ++ _).
    cancel (sll p_v_2 (x_data :: l1_2)).
    unfold sll.
    entailer!.
  + unfold split_rec_rel in H0 |- *.
    rewrite (program_para_equiv (split_rec_rel_unfold)) in H0 |- *.
    unfold split_rec_rel_f in H0 |- *.
    rewrite bind_ret_left in H0.
    unfold reversepair, maketuple in H0.
    exact H0.
Qed.

Lemma proof_of_split_while_return_wit_1 : split_while_return_wit_1.
Proof.
  pre_process.
  Exists q_v.
  Exists p_v.
  Exists l1.
  Exists l2.
  sep_apply sll_zero; [ | auto ].
  entailer!.
  subst.
  unfold split_rec_rel in H0.
  unfold maketuple.
  eapply highstependret_derive with (P' := fun _ => ATrue); eauto.
  apply split_rec_rel_eval_xnil.
Qed.


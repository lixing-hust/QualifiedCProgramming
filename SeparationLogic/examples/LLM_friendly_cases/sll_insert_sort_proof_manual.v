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
Require Import SimpleC.EE.LLM_friendly_cases.sll_insert_sort_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_friendly_cases.sll_lib.
Require Import SimpleC.EE.LLM_friendly_cases.sll_insert_sort_lib.
Local Open Scope sac.

Lemma upperbound_insert_app:
  forall x l1 l2,
    strict_upperbound x l1 ->
    insert x (l1 ++ l2) = l1 ++ insert x l2.
Proof.
  intros x l1 l2 Hupper.
  revert l2 Hupper.
  induction l1; intros l2 Hupper.
  - reflexivity.
  - simpl in Hupper.
    destruct Hupper.
    simpl.
    destruct (x >? a) eqn:Hgt.
    + f_equal.
      apply IHl1.
      exact H0.
    + lia.
Qed.

Lemma proof_of_insertion_entail_wit_1 : insertion_entail_wit_1.
Proof.
  pre_process.
  Exists nil.
  Exists l.
  split_pure_spatial.
  - cancel (&((node_pre) # "list" ->ₛ "data") # Int |-> a).
    cancel (sll p_pre l).
    cancel (&((node_pre) # "list" ->ₛ "next") # Ptr |->_).
    simpl sllbseg.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      reflexivity.
  - split_pures; try (dump_pre_spatial; auto).
Qed.

Lemma proof_of_insertion_entail_wit_2 : insertion_entail_wit_2.
Proof.
  pre_process.
  Exists y.
  Exists (l1_2 ++ x :: nil)%list.
  Exists l0.
  split_pure_spatial.
  - sep_apply (sllbseg_len1 p2 p2_v_2 x); [ | assumption ].
    sep_apply (sllbseg_sllbseg (&( "res" )) p2 (&((p2_v_2) # "list" ->ₛ "next")) l1_2 (x :: nil)%list).
    cancel.
  - split_pures; try (dump_pre_spatial; apply upperbound_app; try assumption; lia).
    dump_pre_spatial ; auto.
    dump_pre_spatial.
    rewrite H3.
    rewrite H0.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma proof_of_insertion_entail_wit_3_1 : insertion_entail_wit_3_1.
Proof.
  pre_process.
  subst p2_v.
  sep_apply (sll_zero 0 l2); [ | reflexivity ].
  Intros_p Hl2.
  Right.
  Exists l1_3.
  split_pure_spatial.
  - cancel ((&((node_pre) # "list" ->ₛ "data")) # Int |-> a).
    cancel (sllbseg ( &( "res" ) ) p2 l1_3).
    cancel ((p2) # Ptr |-> 0).
    cancel ((&((node_pre) # "list" ->ₛ "next")) # Ptr |->_).
  - split_pures.
    + dump_pre_spatial.
      exact H0.
    + dump_pre_spatial.
      rewrite Hl2 in H1.
      exact H1.
    + dump_pre_spatial.
      exact H2.
Qed.

Lemma proof_of_insertion_entail_wit_4_1 : insertion_entail_wit_4_1.
Proof.
  pre_process.
  Right.
  sep_apply (sllbseg_2_sllseg (&( "res" )) p2 node_pre l1_3).
  Intros resv_2.
  Exists resv_2.
  Exists l1_3.
  split_pure_spatial.
  - cancel ((( &( "res" ) )) # Ptr |-> resv_2).
    cancel (sllseg resv_2 node_pre l1_3).
    cancel ((&((node_pre) # "list" ->ₛ "data")) # Int |-> a).
    cancel ((&((node_pre) # "list" ->ₛ "next")) # Ptr |-> 0).
  - split_pures.
    + dump_pre_spatial.
      exact H.
    + dump_pre_spatial.
      exact H0.
    + dump_pre_spatial.
      exact H1.
Qed.

Lemma proof_of_insertion_entail_wit_4_2 : insertion_entail_wit_4_2.
Proof.
  pre_process.
  Left.
  sep_apply (sllbseg_2_sllseg (&( "res" )) p2 node_pre l1_3).
  Intros resv.
  Exists unext_2.
  Exists resv.
  Exists l1_3.
  Exists l0_2.
  Exists x_2.
  Exists u_2.
  split_pure_spatial.
  - cancel ((( &( "res" ) )) # Ptr |-> resv).
    cancel (sllseg resv node_pre l1_3).
    cancel ((&((node_pre) # "list" ->ₛ "data")) # Int |-> a).
    cancel ((&((node_pre) # "list" ->ₛ "next")) # Ptr |-> u_2).
    cancel ((&((u_2) # "list" ->ₛ "data")) # Int |-> x_2).
    cancel ((&((u_2) # "list" ->ₛ "next")) # Ptr |-> unext_2).
    cancel (sll unext_2 l0_2).
  - split_pures.
    + dump_pre_spatial.
      exact H.
    + dump_pre_spatial.
      exact H0.
    + dump_pre_spatial.
      exact H1.
    + dump_pre_spatial.
      exact H2.
    + dump_pre_spatial.
      exact H3.
Qed.

Lemma proof_of_insertion_return_wit_2 : insertion_return_wit_2.
Admitted.

Lemma proof_of_insertion_return_wit_1 : insertion_return_wit_1.
Admitted.

Lemma proof_of_insertion_sort_entail_wit_1 : insertion_sort_entail_wit_1.
Proof.
  pre_process.
  Exists nil.
  Exists nil.
  Exists l.
  split_pure_spatial.
  - simpl sll.
    split_pure_spatial.
    + cancel (sll x_pre l).
    + dump_pre_spatial.
      reflexivity.
  - split_pures.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_insertion_sort_entail_wit_2 : insertion_sort_entail_wit_2.
Admitted.

Lemma proof_of_insertion_sort_return_wit_1 : insertion_sort_return_wit_1.
Admitted.

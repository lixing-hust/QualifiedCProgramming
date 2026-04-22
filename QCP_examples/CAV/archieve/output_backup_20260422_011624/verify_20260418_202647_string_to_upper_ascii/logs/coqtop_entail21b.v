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
From SimpleC.EE.CAV.verify_20260418_202647_string_to_upper_ascii Require Import string_to_upper_ascii_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import string_to_upper_ascii.
Local Open Scope sac.
Lemma string_to_upper_ascii_spec_length :
  forall (l : list Z),
    Zlength (string_to_upper_ascii_spec l) = Zlength l.
Proof.
  induction l.
  - reflexivity.
  - simpl. rewrite Zlength_cons. rewrite Zlength_cons. rewrite IHl. reflexivity.
Qed.
Lemma string_to_upper_ascii_spec_app :
  forall (l1 l2 : list Z),
    string_to_upper_ascii_spec (l1 ++ l2) =
    string_to_upper_ascii_spec l1 ++ string_to_upper_ascii_spec l2.
Proof.
  induction l1.
  - reflexivity.
  - intros l2. simpl. rewrite IHl1. reflexivity.
Qed.
Goal string_to_upper_ascii_entail_wit_2_1.
Proof.
  unfold string_to_upper_ascii_entail_wit_2_1.
  pre_process.
  destruct l2_2.
  - simpl in H2.
    rewrite app_Znth2 in H2 by (rewrite string_to_upper_ascii_spec_length; lia).
    replace (i - Zlength (string_to_upper_ascii_spec l1_2)) with 0 in H2 by
      (rewrite string_to_upper_ascii_spec_length; lia).
    simpl in H2.
    contradiction.
  - Exists (l1_2 ++ z :: nil).
    Exists l2_2.
    entailer!.
    Show.
Abort.

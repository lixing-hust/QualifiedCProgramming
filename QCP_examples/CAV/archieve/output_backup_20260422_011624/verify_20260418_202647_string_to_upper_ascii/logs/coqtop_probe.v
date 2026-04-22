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
  forall (l : list Z), Zlength (string_to_upper_ascii_spec l) = Zlength l.
Proof. induction l; simpl; try reflexivity. rewrite Zlength_cons. rewrite Zlength_cons. rewrite IHl. reflexivity. Qed.
Lemma replace_nth_length :
  forall {A : Type} (n : nat) (a : A) (l : list A),
    Datatypes.length (replace_nth n a l) = Datatypes.length l.
Proof.
  intros A n a l. revert n. induction l.
  - intros n. destruct n; reflexivity.
  - intros n. destruct n; simpl; try reflexivity. rewrite IHl. reflexivity.
Qed.
Lemma replace_Znth_length :
  forall {A : Type} (n : Z) (a : A) (l : list A),
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros A n a l. unfold replace_Znth. rewrite Zlength_correct. rewrite Zlength_correct. rewrite replace_nth_length. reflexivity.
Qed.
Goal string_to_upper_ascii_entail_wit_2_1.
Proof.
  unfold string_to_upper_ascii_entail_wit_2_1.
  pre_process.
  destruct l2_2.
  - simpl in H2.
    rewrite app_Znth2 in H2 by (rewrite string_to_upper_ascii_spec_length; lia).
    replace (i - Zlength (string_to_upper_ascii_spec l1_2)) with 0 in H2 by (rewrite string_to_upper_ascii_spec_length; lia).
    simpl in H2.
    contradiction.
  - prop_apply CharArray.full_length. Intros.
    Show.
Abort.

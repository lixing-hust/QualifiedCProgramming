Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Require Import String.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

Import naive_C_Rules.
Local Open Scope sac.

Fixpoint increasing_aux (l: list Z) (x: Z): Prop :=
  match l with
  | nil => True
  | y :: l0 => x <= y /\ increasing_aux l0 y
  end.

Definition increasing (l: list Z): Prop :=
  match l with
  | nil => True
  | x :: l0 => increasing_aux l0 x
  end.

Fixpoint strict_upperbound (x: Z) (l: list Z): Prop :=
  match l with
  | nil => True
  | y :: l' => x < y /\ strict_upperbound x l'
  end.

Fixpoint insert (x: Z) (l: list Z): list Z :=
  match l with
  | nil => [x]
  | y :: l' => if x >? y then y :: insert x l' else x :: l
  end.

Lemma upperbound_insert_nil:
  forall x l,
    strict_upperbound x l ->
    insert x l = x :: l.
Proof.
  intros.
  induction l; simpl; try easy.
  simpl in H. destruct H.
  destruct (x >? a) eqn:b; simpl.
  - lia.
  - reflexivity.
Qed.

Lemma upperbound_insert_cons:
  forall x y l,
    y <= x ->
    strict_upperbound x l ->
    insert x (y :: l) = y :: x :: l.
Proof.
  intros.
  simpl.
  destruct (x >? y) eqn:b; simpl.
  - rewrite upperbound_insert_nil; auto.
  - assert (x = y) by lia. subst. reflexivity.
Qed.

Lemma upperbound_app:
  forall x l v,
    strict_upperbound x l ->
    x < v ->
    strict_upperbound x (v :: l).
Proof.
  intros. simpl. tauto.
Qed.

Lemma increasing_aux_insert:
  forall x l start,
    increasing_aux l start ->
    start <= x ->
    increasing_aux (insert x l) start.
Proof.
  intros. revert start H H0.
  induction l; intros; simpl; try easy.
  simpl in H.
  destruct (x >? a) eqn:b; simpl.
  - split; try easy.
    apply IHl; [easy | lia].
  - repeat split; try easy. lia.
Qed.

Lemma increasing_insert:
  forall x l,
    increasing l ->
    increasing (insert x l).
Proof.
  intros. destruct l; simpl; try easy.
  simpl in H.
  destruct (x >? z) eqn:b; simpl.
  - apply increasing_aux_insert; [easy | lia].
  - split; [lia | easy].
Qed.

Lemma increasing_aux_middle:
  forall l y x l2 start,
    increasing_aux (l ++ y :: l2) start ->
    y <= x ->
    strict_upperbound x l2 ->
    increasing_aux (l ++ y :: x :: l2) start.
Proof.
  induction l; intros; simpl in *.
  - destruct l2 eqn:E2; simpl in *.
    + lia.
    + destruct H as [Hsy Hrest].
      destruct H1 as [Hxz Hup].
      split.
      * exact Hsy.
      * split.
        -- lia.
        -- destruct Hrest as [_ Htail].
           split.
           ++ lia.
           ++ exact Htail.
  - destruct H as [Hsa Hrest].
    split.
    + exact Hsa.
    + eapply IHl; eauto.
Qed.

Lemma increasing_middle:
  forall l1 y x l2,
    increasing (l1 ++ y :: l2) ->
    y <= x ->
    strict_upperbound x l2 ->
    increasing (l1 ++ y :: x :: l2).
Proof.
  destruct l1; intros; simpl in *.
  - destruct l2 eqn:E2; simpl in *.
    + lia.
    + destruct H as [Hyz Hrest].
      destruct H1 as [Hxz Hup].
      split.
      * lia.
      * split.
        -- lia.
        -- exact Hrest.
  - eapply increasing_aux_middle; eauto.
Qed.

Lemma perm_insert:
  forall x l,
    Permutation (l ++ [x]) (insert x l).
Proof.
  intros. induction l; simpl; try easy.
  destruct (x >? a).
  - rewrite IHl. reflexivity.
  - rewrite <- Permutation_cons_append. apply perm_swap.
Qed.


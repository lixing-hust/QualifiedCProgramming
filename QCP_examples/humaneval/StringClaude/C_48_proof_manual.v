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
From SimpleC.EE Require Import C_48_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_48.
Local Open Scope sac.

Lemma proof_of_is_palindrome_entail_wit_2 : is_palindrome_entail_wit_2.
Proof.
  unfold is_palindrome_entail_wit_2.
  intros.
  pre_process.
  entailer!.
  intros k Hk.
  destruct (Z_lt_ge_dec k i).
  - match goal with
    | Hchecked : forall k : Z, 0 <= k /\ k < i -> _ |- _ =>
        apply Hchecked; lia
    end.
  - assert (k = i) by lia.
    subst k.
    match goal with
    | Heq : Znth i (app l (cons 0 nil)) 0 =
            Znth j (app l (cons 0 nil)) 0 |- _ =>
        rewrite app_Znth1 in Heq by lia;
        rewrite app_Znth1 in Heq by lia;
        replace (n - 1 - i) with j by lia;
        exact Heq
    end.
Qed.

Lemma proof_of_is_palindrome_return_wit_1 : is_palindrome_return_wit_1.
Proof.
  unfold is_palindrome_return_wit_1.
  intros.
  pre_process.
  entailer!.
  apply problem_48_spec_z_true with (n := n) (i := i) (j := j);
    try lia; auto.
Qed.

Lemma proof_of_is_palindrome_return_wit_2 : is_palindrome_return_wit_2.
Proof.
  unfold is_palindrome_return_wit_2.
  intros.
  pre_process.
  entailer!.
  apply problem_48_spec_z_false with (n := n) (i := i) (j := j);
    try lia; auto.
  match goal with
  | Hneq : Znth i (app l (cons 0 nil)) 0 <>
           Znth j (app l (cons 0 nil)) 0 |- _ =>
      intro Heq;
      apply Hneq;
      rewrite app_Znth1 by lia;
      rewrite app_Znth1 by lia;
      exact Heq
  end.
Qed.

Lemma proof_of_is_palindrome_return_wit_3 : is_palindrome_return_wit_3.
Proof.
  unfold is_palindrome_return_wit_3.
  intros.
  pre_process.
  entailer!.
  apply problem_48_spec_z_empty.
  lia.
Qed.

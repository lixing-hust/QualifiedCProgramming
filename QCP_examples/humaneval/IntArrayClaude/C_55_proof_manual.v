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
From SimpleC.EE Require Import C_55_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_55.
Local Open Scope sac.

Lemma proof_of_fib_safety_wit_4 : fib_safety_wit_4.
Proof.
  pre_process.
  subst a b.
  match goal with
  | H: fib_step_int_range n_pre |- _ =>
      unfold fib_step_int_range in H;
      specialize (H i)
  end.
  assert (Hr : 2 <= i <= n_pre) by lia.
  match goal with
  | H: (2 <= i <= n_pre -> _) |- _ =>
      specialize (H Hr)
  end.
  andp_cancel; lia.
Qed.

Lemma proof_of_fib_entail_wit_1 : fib_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_fib_entail_wit_2 : fib_entail_wit_2.
Proof.
  pre_process.
  assert (Hstep : a + b = fib_seq i).
  {
    subst a b.
    replace (fib_seq i) with (fib_seq (i - 2) + fib_seq (i - 1))
      by (symmetry; apply fib_seq_step; lia).
    reflexivity.
  }
  assert (Hbnext : b = fib_seq (i + 1 - 2)).
  { subst b. replace (i + 1 - 2) with (i - 1) by lia. reflexivity. }
  assert (Hcnext : a + b = fib_seq (i + 1 - 1)).
  { replace (i + 1 - 1) with i by lia. exact Hstep. }
  andp_cancel; auto; try lia.
  sep_apply store_int_undef_store_int.
  andp_cancel.
Qed.

Lemma proof_of_fib_return_wit_1 : fib_return_wit_1.
Proof.
  pre_process.
  subst b.
  andp_cancel; auto.
  apply problem_55_spec_z_of_fib_seq.
  - lia.
  - replace (i - 1) with n_pre by lia.
    reflexivity.
Qed.

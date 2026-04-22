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
From SimpleC.EE Require Import C_46_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_46.
Local Open Scope sac.

Lemma proof_of_fib4_safety_wit_14 : fib4_safety_wit_14.
Proof.
  pre_process.
  subst a b c d.
  unfold fib4_step_int_range in H4.
  assert (Hr : 4 <= i <= n_pre) by lia.
  specialize (H4 i Hr).
  destruct H4 as [_ [_ Hsum]].
  andp_cancel; lia.
Qed.

Lemma proof_of_fib4_safety_wit_15 : fib4_safety_wit_15.
Proof.
  pre_process.
  subst a b c d.
  unfold fib4_step_int_range in H4.
  assert (Hr : 4 <= i <= n_pre) by lia.
  specialize (H4 i Hr).
  destruct H4 as [_ [Hsum _]].
  andp_cancel; lia.
Qed.

Lemma proof_of_fib4_safety_wit_16 : fib4_safety_wit_16.
Proof.
  pre_process.
  subst a b c d.
  unfold fib4_step_int_range in H4.
  assert (Hr : 4 <= i <= n_pre) by lia.
  specialize (H4 i Hr).
  destruct H4 as [Hsum _].
  andp_cancel; lia.
Qed.

Lemma proof_of_fib4_entail_wit_1 : fib4_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_fib4_entail_wit_2 : fib4_entail_wit_2.
Proof.
  pre_process.
  assert (Hstep:
    ((a + b) + c) + d = fib4_z i).
  {
    subst a b c d.
    replace (fib4_z i) with
      (fib4_z (i - 1) + fib4_z (i - 2) +
       fib4_z (i - 3) + fib4_z (i - 4))
      by (symmetry; apply fib4_z_step; lia).
    lia.
  }
  assert (Hbnext : b = fib4_z (i + 1 - 4)).
  { subst b. replace (i + 1 - 4) with (i - 3) by lia. reflexivity. }
  assert (Hcnext : c = fib4_z (i + 1 - 3)).
  { subst c. replace (i + 1 - 3) with (i - 2) by lia. reflexivity. }
  assert (Hdnext : d = fib4_z (i + 1 - 2)).
  { subst d. replace (i + 1 - 2) with (i - 1) by lia. reflexivity. }
  assert (Hnext : ((a + b) + c) + d = fib4_z (i + 1 - 1)).
  { replace (i + 1 - 1) with i by lia. exact Hstep. }
  andp_cancel; auto; try lia.
  sep_apply store_int_undef_store_int.
  andp_cancel.
Qed.

Lemma proof_of_fib4_return_wit_1 : fib4_return_wit_1.
Proof.
  pre_process.
  subst d.
  unfold problem_46_spec_z.
  andp_cancel; auto; try lia.
  split.
  - lia.
  - replace (i - 1) with n_pre by lia.
    reflexivity.
Qed.

Lemma proof_of_fib4_return_wit_2 : fib4_return_wit_2.
Proof.
  pre_process.
  andp_cancel; auto.
  subst n_pre.
  apply problem_46_spec_z_base_3.
Qed.

Lemma proof_of_fib4_return_wit_3 : fib4_return_wit_3.
Proof.
  pre_process.
  andp_cancel; auto.
  subst n_pre.
  apply problem_46_spec_z_base_2.
Qed.

Lemma proof_of_fib4_return_wit_4 : fib4_return_wit_4.
Proof.
  pre_process.
  andp_cancel; auto.
  subst n_pre.
  apply problem_46_spec_z_base_1.
Qed.

Lemma proof_of_fib4_return_wit_5 : fib4_return_wit_5.
Proof.
  pre_process.
  andp_cancel; auto.
  subst n_pre.
  apply problem_46_spec_z_base_0.
Qed.

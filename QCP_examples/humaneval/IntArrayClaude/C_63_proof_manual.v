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
From SimpleC.EE Require Import C_63_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_63.
Local Open Scope sac.

Lemma proof_of_fibfib_safety_wit_11 : fibfib_safety_wit_11.
Proof.
  pre_process.
  subst a b c.
  match goal with
  | Hrange0: fibfib_step_int_range n_pre |- _ =>
      unfold fibfib_step_int_range in Hrange0;
      pose proof (Hrange0 i) as Hrange;
      clear Hrange0
  end.
  assert (Hr : 3 <= i <= n_pre) by lia.
  specialize (Hrange Hr).
  destruct Hrange as [_ Hsum].
  andp_cancel; lia.
Qed.

Lemma proof_of_fibfib_safety_wit_12 : fibfib_safety_wit_12.
Proof.
  pre_process.
  subst a b c.
  match goal with
  | H: fibfib_step_int_range n_pre |- _ =>
      unfold fibfib_step_int_range in H;
      pose proof (H i) as Hrange;
      clear H
  end.
  assert (Hr : 3 <= i <= n_pre) by lia.
  specialize (Hrange Hr).
  destruct Hrange as [Hsum _].
  andp_cancel; lia.
Qed.

Lemma proof_of_fibfib_entail_wit_1 : fibfib_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_fibfib_entail_wit_2 : fibfib_entail_wit_2.
Proof.
  pre_process.
  assert (Hstep : (a + b) + c = fibfib_z i).
  {
    subst a b c.
    replace (fibfib_z i) with
      (fibfib_z (i - 1) + fibfib_z (i - 2) + fibfib_z (i - 3))
      by (symmetry; apply fibfib_z_step; lia).
    lia.
  }
  assert (Hbnext : b = fibfib_z (i + 1 - 3)).
  { subst b. replace (i + 1 - 3) with (i - 2) by lia. reflexivity. }
  assert (Hcnext : c = fibfib_z (i + 1 - 2)).
  { subst c. replace (i + 1 - 2) with (i - 1) by lia. reflexivity. }
  assert (Hnext : (a + b) + c = fibfib_z (i + 1 - 1)).
  { replace (i + 1 - 1) with i by lia. exact Hstep. }
  andp_cancel; auto; try lia.
  sep_apply store_int_undef_store_int.
  andp_cancel.
Qed.

Lemma proof_of_fibfib_return_wit_1 : fibfib_return_wit_1.
Proof.
  pre_process.
  subst c.
  andp_cancel; auto.
  apply problem_63_spec_z_of_fibfib_z.
  - lia.
  - replace (i - 1) with n_pre by lia.
    reflexivity.
Qed.

Lemma proof_of_fibfib_return_wit_2 : fibfib_return_wit_2.
Proof.
  pre_process.
  andp_cancel; auto.
  subst n_pre.
  apply problem_63_spec_z_base_2.
Qed.

Lemma proof_of_fibfib_return_wit_3 : fibfib_return_wit_3.
Proof.
  pre_process.
  andp_cancel; auto.
  subst n_pre.
  apply problem_63_spec_z_base_1.
Qed.

Lemma proof_of_fibfib_return_wit_4 : fibfib_return_wit_4.
Proof.
  pre_process.
  andp_cancel; auto.
  subst n_pre.
  apply problem_63_spec_z_base_0.
Qed.

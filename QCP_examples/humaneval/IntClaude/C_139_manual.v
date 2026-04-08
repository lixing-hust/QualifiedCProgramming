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
From SimpleC.EE.humaneval Require Import C_139_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_139.
Local Open Scope sac.

Lemma proof_of_special_factorial_safety_wit_4 : special_factorial_safety_wit_4.
Proof.
  unfold special_factorial_safety_wit_4.
  intros.
  Intros.
  entailer!.
  all: first
       [ match goal with
         | Hfact : ?f = factorial (?ii - 1) |- _ =>
             assert (Hcases :
               ii = 1 \/ ii = 2 \/ ii = 3 \/ ii = 4 \/ ii = 5 \/ ii = 6 \/ ii = 7 \/ ii = 8) by lia;
             destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
             rewrite Hfact;
             vm_compute; congruence
         end
       | lia ].
Qed.

Lemma proof_of_special_factorial_safety_wit_5 : special_factorial_safety_wit_5.
Proof.
  unfold special_factorial_safety_wit_5.
  intros.
  Intros.
  entailer!.
  all: first
       [ match goal with
         | Hfact : ?f = factorial (?ii - 1),
           Hbfact : ?b = bfact_coq (?ii - 1) |- _ =>
             assert (Hcases :
               ii = 1 \/ ii = 2 \/ ii = 3 \/ ii = 4 \/ ii = 5 \/ ii = 6 \/ ii = 7 \/ ii = 8) by lia;
             destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
             rewrite Hfact;
             rewrite Hbfact;
             vm_compute; congruence
         end
       | lia ].
Qed.

Lemma proof_of_special_factorial_entail_wit_1 : special_factorial_entail_wit_1.
Proof.
  unfold special_factorial_entail_wit_1.
  intros.
  Intros.
  entailer!.
Qed.

Lemma proof_of_special_factorial_entail_wit_2 : special_factorial_entail_wit_2.
Proof.
  unfold special_factorial_entail_wit_2.
  intros.
  Intros.
  entailer!.
  all: first
       [ match goal with
         | Hfact : ?f = factorial (?ii - 1),
           Hbfact : ?b = bfact_coq (?ii - 1) |- _ =>
             rewrite Hfact;
             rewrite Hbfact;
             rewrite (factorial_step ii) by lia;
             rewrite (bfact_coq_step ii) by lia;
             replace (ii + 1 - 1) with ii by lia;
             reflexivity
         end
       | match goal with
         | Hfact : ?f = factorial (?ii - 1) |- _ =>
             rewrite Hfact;
             rewrite (factorial_step ii) by lia;
             replace (ii + 1 - 1) with ii by lia;
             reflexivity
         end
       | lia ].
Qed.

Lemma proof_of_special_factorial_return_wit_1 : special_factorial_return_wit_1.
Proof.
  unfold special_factorial_return_wit_1.
  intros.
  Intros.
  entailer!.
  unfold problem_139_spec_z.
  match goal with
  | Hgt : ?ii > ?np,
    Hle : ?ii <= ?np + 1,
    Hbfact : ?b = bfact_coq (?ii - 1) |- _ =>
      assert (Hieq : ii = np + 1) by lia;
      subst ii;
      replace ((np + 1) - 1) with np in Hbfact by lia;
      exact Hbfact
  end.
Qed.

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
From SimpleC.EE.humaneval Require Import C_76_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.humaneval Require Import coins_76.
Local Open Scope sac.

Lemma proof_of_is_simple_power_safety_wit_5 : is_simple_power_safety_wit_5.
Proof.
  unfold is_simple_power_safety_wit_5.
  intros.
  Intros.
  entailer!.
Qed.

Lemma proof_of_is_simple_power_entail_wit_1 : is_simple_power_entail_wit_1.
Proof.
  unfold is_simple_power_entail_wit_1.
  intros.
  Intros.
  entailer!.
  all: first [apply sp_inv_init | lia].
Qed.

Lemma proof_of_is_simple_power_entail_wit_2 : is_simple_power_entail_wit_2.
Proof.
  unfold is_simple_power_entail_wit_2.
  intros.
  Intros.
  entailer!.
  all: first
       [ match goal with
         | |- 1 <= ?a * ?b =>
             assert (0 < a) by lia;
             assert (0 < b) by lia;
             pose proof (Z.mul_pos_pos a b H H0) as Hpos;
             lia
         end
       | match goal with
         | |- sp_inv _ _ _ _ =>
             eapply sp_inv_step; eauto; lia
         end
       | lia ].
Qed.

Lemma proof_of_is_simple_power_return_wit_1 : is_simple_power_return_wit_1.
Proof.
  unfold is_simple_power_return_wit_1.
  intros.
  Intros.
  entailer!.
  unfold is_simple_power_spec.
  split.
  - intros _.
    eapply sp_inv_hit_witness; eauto; lia.
  - intros _.
    lia.
Qed.

Lemma proof_of_is_simple_power_return_wit_2 : is_simple_power_return_wit_2.
Proof.
  unfold is_simple_power_return_wit_2.
  intros.
  Intros.
  entailer!.
  unfold is_simple_power_spec.
  split.
  - intro Hfalse. lia.
  - intro Hex.
    exfalso.
    apply (no_power_if_cutoff x_pre n_pre count p); try assumption; try lia.
Qed.

Lemma proof_of_is_simple_power_return_wit_3 : is_simple_power_return_wit_3.
Proof.
  unfold is_simple_power_return_wit_3.
  intros.
  Intros.
  entailer!.
  unfold is_simple_power_spec.
  split.
  - intro Hfalse. lia.
  - intro Hex.
    exfalso.
    eapply no_power_if_gt; eauto; lia.
Qed.

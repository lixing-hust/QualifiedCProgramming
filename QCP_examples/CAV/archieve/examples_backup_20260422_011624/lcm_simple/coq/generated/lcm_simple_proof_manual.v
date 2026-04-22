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
From SimpleC.EE.CAV.verify_20260421_043521_lcm_simple Require Import lcm_simple_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import lcm_simple.
Local Open Scope sac.

Lemma lcm_simple_rem_mod_pos :
  forall x a,
    0 <= x ->
    0 < a ->
    Z.rem x a = x mod a.
Proof.
  intros.
  apply Z.rem_mod_nonneg; lia.
Qed.

Lemma lcm_simple_rem_zero_divide_pos :
  forall x a,
    0 <= x ->
    0 < a ->
    Z.rem x a = 0 ->
    (a | x).
Proof.
  intros x a Hx Ha Hrem.
  apply (proj1 (Z.mod_divide x a ltac:(lia))).
  rewrite <- lcm_simple_rem_mod_pos by lia.
  exact Hrem.
Qed.

Lemma lcm_simple_divide_rem_zero_pos :
  forall x a,
    0 <= x ->
    0 < a ->
    (a | x) ->
    Z.rem x a = 0.
Proof.
  intros x a Hx Ha Hdiv.
  rewrite lcm_simple_rem_mod_pos by lia.
  apply (proj2 (Z.mod_divide x a ltac:(lia))).
  exact Hdiv.
Qed.

Lemma lcm_simple_lcm_pos :
  forall a b,
    1 <= a ->
    1 <= b ->
    0 < lcm_simple_value a b.
Proof.
  intros a b Ha Hb.
  unfold lcm_simple_value.
  pose proof (Z.lcm_nonneg a b) as Hnonneg.
  assert (Z.lcm a b <> 0) as Hneq.
  {
    intro Hz.
    apply Z.lcm_eq_0 in Hz.
    lia.
  }
  lia.
Qed.

Lemma lcm_simple_a_le_lcm :
  forall a b,
    1 <= a ->
    1 <= b ->
    a <= lcm_simple_value a b.
Proof.
  intros a b Ha Hb.
  unfold lcm_simple_value.
  apply Z.divide_pos_le.
  - pose proof (lcm_simple_lcm_pos a b Ha Hb).
    unfold lcm_simple_value in H.
    exact H.
  - apply Z.divide_lcm_l.
Qed.

Lemma lcm_simple_lcm_rem_b :
  forall a b,
    1 <= a ->
    1 <= b ->
    Z.rem (lcm_simple_value a b) b = 0.
Proof.
  intros a b Ha Hb.
  apply lcm_simple_divide_rem_zero_pos.
  - pose proof (Z.lcm_nonneg a b). unfold lcm_simple_value. lia.
  - lia.
  - unfold lcm_simple_value. apply Z.divide_lcm_r.
Qed.

Lemma lcm_simple_consecutive_multiple :
  forall a x y,
    1 <= a ->
    0 <= x ->
    0 <= y ->
    Z.rem x a = 0 ->
    Z.rem y a = 0 ->
    x <= y ->
    y < x + a ->
    y = x.
Proof.
  intros a x y Ha Hx Hy Hxrem Hyrem Hle Hlt.
  assert (Hdx : (a | x)) by
    (apply lcm_simple_rem_zero_divide_pos; lia).
  assert (Hdy : (a | y)) by
    (apply lcm_simple_rem_zero_divide_pos; lia).
  assert (Hd : (a | y - x)).
  {
    apply Z.divide_sub_r; assumption.
  }
  destruct (Z.eq_dec (y - x) 0) as [Hz | Hnz].
  - lia.
  - assert (0 < y - x) by lia.
    pose proof (Z.divide_pos_le a (y - x) H Hd).
    lia.
Qed.

Lemma lcm_simple_step_rem_a :
  forall a x,
    1 <= a ->
    1 <= x ->
    Z.rem x a = 0 ->
    Z.rem (x + a) a = 0.
Proof.
  intros a x Ha Hx Hrem.
  apply lcm_simple_divide_rem_zero_pos; try lia.
  apply Z.divide_add_r.
  - apply lcm_simple_rem_zero_divide_pos; lia.
  - apply Z.divide_refl.
Qed.

Lemma lcm_simple_next_within_lcm :
  forall a b x,
    1 <= a ->
    1 <= b ->
    1 <= x ->
    x <= lcm_simple_value a b ->
    Z.rem x a = 0 ->
    Z.rem x b <> 0 ->
    x + a <= lcm_simple_value a b.
Proof.
  intros a b x Ha Hb Hxpos Hxle Hxrem Hxb.
  assert (Hlrem : Z.rem (lcm_simple_value a b) b = 0)
    by (apply lcm_simple_lcm_rem_b; lia).
  assert (Hxlt : x < lcm_simple_value a b).
  {
    destruct (Z.eq_dec x (lcm_simple_value a b)) as [Heq | Hneq].
    - subst x. contradiction.
    - lia.
  }
  assert (Hdl : (a | lcm_simple_value a b)).
  {
    unfold lcm_simple_value. apply Z.divide_lcm_l.
  }
  assert (Hdx : (a | x)) by
    (apply lcm_simple_rem_zero_divide_pos; lia).
  assert (Hd : (a | lcm_simple_value a b - x)).
  {
    apply Z.divide_sub_r; assumption.
  }
  assert (Hpos : 0 < lcm_simple_value a b - x) by lia.
  pose proof (Z.divide_pos_le a (lcm_simple_value a b - x) Hpos Hd).
  lia.
Qed.

Lemma lcm_simple_exit_eq :
  forall a b x,
    1 <= a ->
    1 <= b ->
    1 <= x ->
    x <= lcm_simple_value a b ->
    Z.rem x a = 0 ->
    Z.rem x b = 0 ->
    x = lcm_simple_value a b.
Proof.
  intros a b x Ha Hb Hxpos Hxle Hxrem Hxbrem.
  assert (Hda : (a | x)) by
    (apply lcm_simple_rem_zero_divide_pos; lia).
  assert (Hdb : (b | x)) by
    (apply lcm_simple_rem_zero_divide_pos; lia).
  assert (Hdl : (lcm_simple_value a b | x)).
  {
    unfold lcm_simple_value.
    apply Z.lcm_least; assumption.
  }
  assert (Hl_le_x : lcm_simple_value a b <= x).
  {
    apply Z.divide_pos_le; [lia | exact Hdl].
  }
  lia.
Qed.

Lemma proof_of_lcm_simple_entail_wit_1 : lcm_simple_entail_wit_1.
Proof.
  unfold lcm_simple_entail_wit_1.
  pre_process.
  entailer!.
  - intros y [[Hypos Hylt] Hyrem].
    assert (Hdy : (a_pre | y)) by
      (apply lcm_simple_rem_zero_divide_pos; lia).
    pose proof (Z.divide_pos_le a_pre y ltac:(lia) Hdy).
    lia.
  - intro Harem.
    apply lcm_simple_next_within_lcm; try lia.
    + exact (lcm_simple_a_le_lcm a_pre b_pre H H0).
    + rewrite lcm_simple_rem_mod_pos by lia.
      apply Z.mod_same; lia.
  - rewrite lcm_simple_rem_mod_pos by lia.
    apply Z.mod_same; lia.
  - exact (lcm_simple_a_le_lcm a_pre b_pre H H0).
Qed. 

Lemma proof_of_lcm_simple_entail_wit_2 : lcm_simple_entail_wit_2.
Proof.
  unfold lcm_simple_entail_wit_2.
  pre_process.
  entailer!.
  - intros y [[Hypos Hylt] Hyrem].
    destruct (Z_lt_ge_dec y x) as [Hy_before | Hy_after].
    + apply H6. lia.
    + assert (Hy_eq : y = x).
      {
        apply lcm_simple_consecutive_multiple with (a := a_pre); try lia.
      }
      subst y.
      exact H.
  - intro Hnextrem.
    apply (lcm_simple_next_within_lcm a_pre b_pre (x + a_pre)); try lia.
    apply lcm_simple_step_rem_a; lia.
  - apply lcm_simple_step_rem_a; lia.
Qed. 

Lemma proof_of_lcm_simple_return_wit_1 : lcm_simple_return_wit_1.
Proof.
  unfold lcm_simple_return_wit_1.
  pre_process.
  unfold lcm_simple_spec.
  entailer!.
  apply lcm_simple_exit_eq; assumption.
Qed. 

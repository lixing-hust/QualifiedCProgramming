Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_123_goal.
From SimpleC.EE Require Import C_123_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_123.
Local Open Scope sac.

Ltac solve_123 :=
  pre_process; subst; entailer!;
  match goal with
  | H : ?x % 2 = 1, Hp : 0 < ?x |- _ =>
      let Hm := fresh "Hmod" in
      assert (Hm : x mod 2 = 1) by
        (rewrite <- (Z.rem_mod_nonneg x 2) by lia; exact H)
  | _ => idtac
  end;
  match goal with
  | H : ?x % 2 <> 1, Hp : 0 < ?x |- _ =>
      let Hm := fresh "Hmod" in
      let Hc := fresh "Hcontra" in
      assert (Hm : x mod 2 <> 1) by
        (intro Hc; apply H;
         rewrite (Z.rem_mod_nonneg x 2) by lia; exact Hc)
  | _ => idtac
  end;
  eauto 8 using
    collatz_count_state_init_123,
    collatz_safe_head_bounds_123,
    collatz_count_state_odd_step_123,
    collatz_count_state_even_step_123,
    collatz_final_count_from_state_123,
    collatz_output_state_init_123,
    collatz_output_state_odd_step_123,
    collatz_output_state_even_step_123,
    collatz_output_odd_room_123,
    collatz_output_final_size_123,
    collatz_output_final_spec_123;
  try (unfold collatz_count_state_123, collatz_final_count_123,
              collatz_output_state_123 in *;
       repeat match goal with
       | H : exists _, _ |- _ => destruct H
       | H : _ /\ _ |- _ => destruct H
       end;
       subst; entailer!; eauto 8; try lia).

Lemma proof_of_get_odd_collatz_safety_wit_8_split_goal_1 : get_odd_collatz_safety_wit_8_split_goal_1.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_safety_wit_8_split_goal_2 : get_odd_collatz_safety_wit_8_split_goal_2.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_safety_wit_8 : get_odd_collatz_safety_wit_8.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_safety_wit_9_split_goal_1 : get_odd_collatz_safety_wit_9_split_goal_1.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_safety_wit_9_split_goal_2 : get_odd_collatz_safety_wit_9_split_goal_2.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_safety_wit_9 : get_odd_collatz_safety_wit_9.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_safety_wit_25_split_goal_1 : get_odd_collatz_safety_wit_25_split_goal_1.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_safety_wit_25_split_goal_2 : get_odd_collatz_safety_wit_25_split_goal_2.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_safety_wit_25 : get_odd_collatz_safety_wit_25.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_safety_wit_26_split_goal_1 : get_odd_collatz_safety_wit_26_split_goal_1.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_safety_wit_26_split_goal_2 : get_odd_collatz_safety_wit_26_split_goal_2.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_safety_wit_26 : get_odd_collatz_safety_wit_26.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_entail_wit_1_split_goal_1 : get_odd_collatz_entail_wit_1_split_goal_1.
Proof.
  pre_process; subst; entailer!.
  apply collatz_count_state_init_123; assumption.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_1_split_goal_2 : get_odd_collatz_entail_wit_1_split_goal_2.
Proof.
  pre_process; subst; entailer!.
  pose proof (collatz_safe_head_bounds_123 _ PreH3) as [_ [Hlt _]].
  exact Hlt.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_1_split_goal_3 : get_odd_collatz_entail_wit_1_split_goal_3.
Proof.
  pre_process; subst; entailer!.
  pose proof (collatz_safe_head_bounds_123 _ PreH3) as [Hpos _].
  exact Hpos.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_1 : get_odd_collatz_entail_wit_1.
Proof.
  pre_process; subst; entailer!.
  - apply collatz_count_state_init_123; assumption.
  - pose proof (collatz_safe_head_bounds_123 _ PreH3) as [_ [Hlt _]].
    exact Hlt.
  - pose proof (collatz_safe_head_bounds_123 _ PreH3) as [Hpos _].
    exact Hpos.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_2_1_split_goal_1 : get_odd_collatz_entail_wit_2_1_split_goal_1.
Proof.
  unfold get_odd_collatz_entail_wit_2_1_split_goal_1.
  intros. entailer!.
  assert (Hmod : cur mod 2 = 1).
  { rewrite <- (Z.rem_mod_nonneg cur 2) by lia. exact PreH1. }
  eapply collatz_count_state_odd_step_123.
  - exact PreH5.
  - exact Hmod.
  - exact PreH2.
  - exact PreH9.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_2_1_split_goal_2 : get_odd_collatz_entail_wit_2_1_split_goal_2.
Proof.
  pre_process; subst; entailer!.
  unfold collatz_count_state_123 in PreH9.
  repeat match goal with
  | H : exists _, _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  end.
  lia.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_2_1_split_goal_3 : get_odd_collatz_entail_wit_2_1_split_goal_3.
Proof.
  pre_process; subst; entailer!.
  assert (Hmod : cur mod 2 = 1).
  { rewrite <- (Z.rem_mod_nonneg cur 2) by lia. exact PreH1. }
  pose proof (collatz_count_state_odd_step_123 _ _ _ PreH5 Hmod PreH2 PreH9)
    as Hnew.
  unfold collatz_count_state_123 in Hnew.
  repeat match goal with
  | H : exists _, _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  end.
  lia.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_2_1 : get_odd_collatz_entail_wit_2_1.
Proof.
  pre_process; subst; entailer!.
  - assert (Hmod : cur mod 2 = 1).
    { rewrite <- (Z.rem_mod_nonneg cur 2) by lia. exact PreH1. }
    eapply collatz_count_state_odd_step_123; eauto.
  - unfold collatz_count_state_123 in PreH9.
    repeat match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    end.
    lia.
  - assert (Hmod : cur mod 2 = 1).
    { rewrite <- (Z.rem_mod_nonneg cur 2) by lia. exact PreH1. }
    pose proof (collatz_count_state_odd_step_123 _ _ _ PreH5 Hmod PreH2 PreH9)
      as Hnew.
    unfold collatz_count_state_123 in Hnew.
    repeat match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    end.
    lia.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_2_2_split_goal_1 : get_odd_collatz_entail_wit_2_2_split_goal_1.
Proof.
  unfold get_odd_collatz_entail_wit_2_2_split_goal_1.
  intros. entailer!.
  assert (Hmod : cur mod 2 <> 1).
  { intro Hcontra. apply PreH1.
    rewrite (Z.rem_mod_nonneg cur 2) by lia. exact Hcontra. }
  eapply collatz_count_state_even_step_123; eauto.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_2_2_split_goal_2 : get_odd_collatz_entail_wit_2_2_split_goal_2.
Proof.
  unfold get_odd_collatz_entail_wit_2_2_split_goal_2.
  intros. entailer!.
  assert (Hmod : cur mod 2 <> 1).
  { intro Hcontra. apply PreH1.
    rewrite (Z.rem_mod_nonneg cur 2) by lia. exact Hcontra. }
  pose proof (collatz_count_state_even_step_123 _ _ _ PreH5 Hmod PreH2 PreH9)
    as Hnew.
  unfold collatz_count_state_123 in Hnew.
  repeat match goal with
  | H : exists _, _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  end.
  lia.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_2_2_split_goal_3 : get_odd_collatz_entail_wit_2_2_split_goal_3.
Proof.
  unfold get_odd_collatz_entail_wit_2_2_split_goal_3.
  intros. entailer!.
  assert (Hmod : cur mod 2 <> 1).
  { intro Hcontra. apply PreH1.
    rewrite (Z.rem_mod_nonneg cur 2) by lia. exact Hcontra. }
  pose proof (collatz_count_state_even_step_123 _ _ _ PreH5 Hmod PreH2 PreH9)
    as Hnew.
  unfold collatz_count_state_123 in Hnew.
  repeat match goal with
  | H : exists _, _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  end.
  lia.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_2_2 : get_odd_collatz_entail_wit_2_2.
Proof.
  pre_process; subst; entailer!.
  - assert (Hmod : cur mod 2 <> 1).
    { intro Hcontra. apply PreH1.
      rewrite (Z.rem_mod_nonneg cur 2) by lia. exact Hcontra. }
    eapply collatz_count_state_even_step_123; eauto.
  - assert (Hmod : cur mod 2 <> 1).
    { intro Hcontra. apply PreH1.
      rewrite (Z.rem_mod_nonneg cur 2) by lia. exact Hcontra. }
    pose proof (collatz_count_state_even_step_123 _ _ _ PreH5 Hmod PreH2 PreH9)
      as Hnew.
    unfold collatz_count_state_123 in Hnew.
    repeat match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    end.
    lia.
  - assert (Hmod : cur mod 2 <> 1).
    { intro Hcontra. apply PreH1.
      rewrite (Z.rem_mod_nonneg cur 2) by lia. exact Hcontra. }
    pose proof (collatz_count_state_even_step_123 _ _ _ PreH5 Hmod PreH2 PreH9)
      as Hnew.
    unfold collatz_count_state_123 in Hnew.
    repeat match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    end.
    lia.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_3_split_goal_1 : get_odd_collatz_entail_wit_3_split_goal_1.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_entail_wit_3_split_goal_2 : get_odd_collatz_entail_wit_3_split_goal_2.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_entail_wit_3 : get_odd_collatz_entail_wit_3.
Proof.
  right.
  pre_process; subst; entailer!.
  all: try assumption.
  all: try solve
    [ match goal with
      | H : collatz_count_state_123 _ _ _ |- _ =>
          unfold collatz_count_state_123 in H;
          repeat match goal with
          | Hx : exists _, _ |- _ => destruct Hx
          | Hx : _ /\ _ |- _ => destruct Hx
          end;
          lia
      end ].
  all: try match goal with
    | H : collatz_count_state_123 ?n 1 ?count |- _ =>
        exact (collatz_final_count_from_state_123 n count H)
    | H : collatz_count_state_123 ?n ?cur ?count,
      Heq : 1 = ?cur |- _ =>
        rewrite <- Heq in H;
        exact (collatz_final_count_from_state_123 n count H)
    | H : collatz_count_state_123 ?n ?cur ?count,
      Heq : ?cur = 1 |- _ =>
        rewrite Heq in H;
        exact (collatz_final_count_from_state_123 n count H)
    end.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_4 : get_odd_collatz_entail_wit_4.
Proof.
  right.
  pre_process; subst.
  Exists ((1 :: nil) : list Z).
  sep_apply (IntArray.seg_single retval_2 0 1).
  entailer!.
  all: try solve [apply collatz_output_state_init_123; assumption].
  all: try solve [pose proof (collatz_safe_head_bounds_123 _ PreH6) as [Hpos _]; exact Hpos].
  all: try solve [pose proof (collatz_safe_head_bounds_123 _ PreH6) as [_ [Hlt _]]; exact Hlt].
  all: simpl; lia.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_5_1_split_goal_1 : get_odd_collatz_entail_wit_5_1_split_goal_1.
Proof.
  unfold get_odd_collatz_entail_wit_5_1_split_goal_1.
  intros. entailer!.
  assert (Hmod : cur mod 2 = 1).
  { rewrite <- (Z.rem_mod_nonneg cur 2) by lia. exact PreH1. }
  eapply collatz_output_state_odd_step_123; eauto.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_5_1_split_goal_2 : get_odd_collatz_entail_wit_5_1_split_goal_2.
Proof.
  unfold get_odd_collatz_entail_wit_5_1_split_goal_2.
  intros. entailer!.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_5_1_split_goal_3 : get_odd_collatz_entail_wit_5_1_split_goal_3.
Proof.
  unfold get_odd_collatz_entail_wit_5_1_split_goal_3.
  intros. entailer!.
  assert (Hmod : cur mod 2 = 1).
  { rewrite <- (Z.rem_mod_nonneg cur 2) by lia. exact PreH1. }
  pose proof (collatz_output_odd_room_123 _ _ _ _ PreH2 Hmod PreH16).
  lia.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_5_1_split_goal_4 : get_odd_collatz_entail_wit_5_1_split_goal_4.
Proof.
  unfold get_odd_collatz_entail_wit_5_1_split_goal_4.
  intros. entailer!.
  assert (Hmod : cur mod 2 = 1).
  { rewrite <- (Z.rem_mod_nonneg cur 2) by lia. exact PreH1. }
  pose proof (collatz_output_state_odd_step_123 _ _ _ _ PreH9 Hmod PreH2 PreH16)
    as Hnew.
  unfold collatz_output_state_123 in Hnew.
  repeat match goal with
  | H : exists _, _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  end.
  lia.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_5_1 : get_odd_collatz_entail_wit_5_1.
Proof.
  right.
  pre_process; subst; entailer!.
  all: assert (Hmod : cur mod 2 = 1) by
    (rewrite <- (Z.rem_mod_nonneg cur 2) by lia; exact PreH1).
  all: try solve [eapply collatz_output_state_odd_step_123; eauto].
  all: try solve [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia].
  all: try solve
    [ pose proof (collatz_output_odd_room_123 _ _ _ _ PreH2 Hmod PreH16);
      lia ].
  all: pose proof (collatz_output_state_odd_step_123 _ _ _ _ PreH9 Hmod PreH2 PreH16)
    as Hnew;
    unfold collatz_output_state_123 in Hnew;
    repeat match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    end;
    lia.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_5_2_split_goal_1 : get_odd_collatz_entail_wit_5_2_split_goal_1.
Proof.
  unfold get_odd_collatz_entail_wit_5_2_split_goal_1.
  intros. entailer!.
  assert (Hmod : cur mod 2 <> 1).
  { intro Hcontra. apply PreH1.
    rewrite (Z.rem_mod_nonneg cur 2) by lia. exact Hcontra. }
  eapply collatz_output_state_even_step_123; eauto.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_5_2_split_goal_2 : get_odd_collatz_entail_wit_5_2_split_goal_2.
Proof.
  unfold get_odd_collatz_entail_wit_5_2_split_goal_2.
  intros. entailer!.
  assert (Hmod : cur mod 2 <> 1).
  { intro Hcontra. apply PreH1.
    rewrite (Z.rem_mod_nonneg cur 2) by lia. exact Hcontra. }
  pose proof (collatz_output_state_even_step_123 _ _ _ _ PreH9 Hmod PreH2 PreH16)
    as Hnew.
  unfold collatz_output_state_123 in Hnew.
  repeat match goal with
  | H : exists _, _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  end.
  lia.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_5_2_split_goal_3 : get_odd_collatz_entail_wit_5_2_split_goal_3.
Proof.
  unfold get_odd_collatz_entail_wit_5_2_split_goal_3.
  intros. entailer!.
  assert (Hmod : cur mod 2 <> 1).
  { intro Hcontra. apply PreH1.
    rewrite (Z.rem_mod_nonneg cur 2) by lia. exact Hcontra. }
  pose proof (collatz_output_state_even_step_123 _ _ _ _ PreH9 Hmod PreH2 PreH16)
    as Hnew.
  unfold collatz_output_state_123 in Hnew.
  repeat match goal with
  | H : exists _, _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  end.
  lia.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_5_2 : get_odd_collatz_entail_wit_5_2.
Proof.
  right.
  pre_process; subst; entailer!.
  all: assert (Hmod : cur mod 2 <> 1) by
    (intro Hcontra; apply PreH1;
     rewrite (Z.rem_mod_nonneg cur 2) by lia; exact Hcontra).
  all: try solve [eapply collatz_output_state_even_step_123; eauto].
  all: pose proof (collatz_output_state_even_step_123 _ _ _ _ PreH9 Hmod PreH2 PreH16)
    as Hnew;
    unfold collatz_output_state_123 in Hnew;
    repeat match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    end;
    lia.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_6_split_goal_1 : get_odd_collatz_entail_wit_6_split_goal_1.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_entail_wit_6_split_goal_2 : get_odd_collatz_entail_wit_6_split_goal_2.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_entail_wit_6 : get_odd_collatz_entail_wit_6.
Proof.
  right.
  pre_process; subst; entailer!.
  all: try assumption.
  all: try solve
    [ match goal with
      | H : collatz_output_state_123 ?n ?count 1 ?output |- _ =>
          pose proof (collatz_output_final_size_123 n count output H);
          lia
      end ].
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_7 : get_odd_collatz_entail_wit_7.
Proof.
  unfold get_odd_collatz_entail_wit_7.
  right.
  intros.
  Exists output_l_2.
  entailer!.
  all: try solve [rewrite PreH7; exact PreH1].
  all: try solve [rewrite PreH7; exact PreH8].
  all: try solve [rewrite PreH7; exact PreH9].
  all: try solve [rewrite PreH7; eapply collatz_output_final_spec_123; eauto].
  all: match goal with |- ?G => idtac "wit7-left" G end.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_8 : get_odd_collatz_entail_wit_8.
Proof.
  right.
  intros. entailer!.
  - destruct PreH5 as [? [? [? [? [Hpos _]]]]].
    subst size. exact Hpos.
  - destruct PreH5 as [? [? [? [? [_ Hbound]]]]].
    subst cap. exact Hbound.
Qed.

Lemma proof_of_get_odd_collatz_return_wit_1 : get_odd_collatz_return_wit_1.
Proof.
  unfold get_odd_collatz_return_wit_1.
  left.
  intros.
  Exists data_l_2 output_l_2 cap size data_2.
  entailer!.
Qed.

Lemma proof_of_get_odd_collatz_partial_solve_wit_5_pure_split_goal_1 : get_odd_collatz_partial_solve_wit_5_pure_split_goal_1.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_partial_solve_wit_5_pure_split_goal_2 : get_odd_collatz_partial_solve_wit_5_pure_split_goal_2.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_partial_solve_wit_5_pure_split_goal_3 : get_odd_collatz_partial_solve_wit_5_pure_split_goal_3.
Proof. solve_123. Qed.

Lemma proof_of_get_odd_collatz_partial_solve_wit_5_pure : get_odd_collatz_partial_solve_wit_5_pure.
Proof. solve_123. Qed.

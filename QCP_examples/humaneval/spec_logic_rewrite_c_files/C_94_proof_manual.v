Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
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
From SimpleC.EE Require Import C_94_goal.
From SimpleC.EE Require Import C_94_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_94.
Local Open Scope sac.

Ltac pose_safe_94 :=
  match goal with
  | Hsafe : skjkasdkd_safe_94 ?l,
    Hi : 0 <= ?i,
    Hlt : ?i < Zlength ?l |- context[Znth ?i ?l 0] =>
      let H := fresh "Hsafe_value" in
      pose proof (safe_value_94 l i Hsafe ltac:(lia)) as H
  | Hsafe : skjkasdkd_safe_94 ?l,
    Hi : 0 <= ?i,
    Hlt : ?i < ?n,
    Hlen : ?n = Zlength ?l |- context[Znth ?i ?l 0] =>
      let H := fresh "Hsafe_value" in
      pose proof (safe_value_94 l i Hsafe ltac:(lia)) as H
  | Hsafe : skjkasdkd_safe_94 ?l,
    Hi : 0 <= ?i < Zlength ?l |- context[Znth ?i ?l 0] =>
      let H := fresh "Hsafe_value" in
      pose proof (safe_value_94 l i Hsafe Hi) as H
  | _ => idtac
  end.

Ltac solve_94_pure :=
  pose_safe_94;
  repeat match goal with
  | |- 0 = largest_prime_prefix_94 0 ?l =>
      unfold largest_prime_prefix_94, values_prefix_94, largest_prime_nat_94; simpl
  | |- digit_sum_state_94 ?n ?n 0 =>
      apply digit_sum_state_start_94; try lia
  | H : digit_sum_state_94 ?orig 0 ?sum |- ?sum = sum_digits_z_94 ?orig =>
      apply digit_sum_state_done_94; exact H
  | H : digit_sum_state_94 ?orig ?q ?sum, Hq : 0 < ?q
      |- digit_sum_state_94 ?orig (Z.quot ?q 10) (?sum + Z.rem ?q 10) =>
      apply digit_sum_state_step_94; [lia|exact H]
  | H : digit_sum_state_94 ?orig ?q ?sum, Hq : ?q > 0
      |- digit_sum_state_94 ?orig (Z.quot ?q 10) (?sum + Z.rem ?q 10) =>
      apply digit_sum_state_step_94; [lia|exact H]
  | H : digit_sum_state_94 ?orig ?q ?sum, Hq : 0 < ?q
      |- ?sum + Z.rem ?q 10 <= INT_MAX =>
      eapply digit_sum_state_increment_bound_94; [lia|exact H]
  | H : digit_sum_state_94 ?orig ?q ?sum, Hq : ?q > 0
      |- ?sum + Z.rem ?q 10 <= INT_MAX =>
      eapply digit_sum_state_increment_bound_94; [lia|exact H]
  | H : digit_sum_state_94 ?orig ?q ?sum, Hq : 0 < ?q
      |- ?sum + Z.rem ?q 10 <= 2147483647 =>
      eapply digit_sum_state_increment_bound_94; [lia|exact H]
  | H : digit_sum_state_94 ?orig ?q ?sum, Hq : ?q > 0
      |- ?sum + Z.rem ?q 10 <= 2147483647 =>
      eapply digit_sum_state_increment_bound_94; [lia|exact H]
  | Hq : 0 < ?q |- INT_MIN <= ?sum + Z.rem ?q 10 =>
      pose proof (Z.rem_bound_pos q 10 ltac:(lia) ltac:(lia)); lia
  | Hq : ?q > 0 |- INT_MIN <= ?sum + Z.rem ?q 10 =>
      pose proof (Z.rem_bound_pos q 10 ltac:(lia) ltac:(lia)); lia
  | Hq : 0 < ?q |- 0 <= ?sum + Z.rem ?q 10 =>
      pose proof (Z.rem_bound_pos q 10 ltac:(lia) ltac:(lia)); lia
  | Hq : ?q > 0 |- 0 <= ?sum + Z.rem ?q 10 =>
      pose proof (Z.rem_bound_pos q 10 ltac:(lia) ltac:(lia)); lia
  | Hq : 0 < ?q |- Z.quot ?q 10 <= ?orig =>
      pose proof (zquot10_le_self_94 q ltac:(lia)); lia
  | Hq : ?q > 0 |- Z.quot ?q 10 <= ?orig =>
      pose proof (zquot10_le_self_94 q ltac:(lia)); lia
  | Hq : 0 < ?q |- 0 <= Z.quot ?q 10 =>
      apply zquot10_nonneg_94; lia
  | Hq : ?q > 0 |- 0 <= Z.quot ?q 10 =>
      apply zquot10_nonneg_94; lia
  | |- prime_scan_state_94 ?x 2%Z 1%Z =>
      apply prime_scan_start_94
  | H : prime_scan_state_94 ?x ?j ?flag, Hr : Z.rem ?x ?j = 0
      |- prime_scan_state_94 ?x (?j + 1) 0%Z =>
      eapply prime_scan_step_hit_94; [lia|exact Hr|exact H]
  | H : prime_scan_state_94 ?x ?j ?flag, Hr : Z.rem ?x ?j <> 0
      |- prime_scan_state_94 ?x (?j + 1) ?flag =>
      eapply prime_scan_step_miss_94; [lia|exact Hr|exact H]
  | H : prime_scan_state_94 ?x ?j ?flag
      |- prime_flag_done_94 ?x ?j ?flag =>
      eapply prime_scan_done_94; [lia|lia|lia|lia|exact H]
  | H : prime_flag_done_94 ?x ?j 1%Z |- prime ?x =>
      apply (prime_flag_done_prime_94 x j H)
  | H : prime_flag_done_94 ?x ?j 0%Z |- ~ prime ?x =>
      apply (prime_flag_done_not_prime_94 x j H)
  | Hcur : ?cur = largest_prime_prefix_94 ?i ?l,
    Hx : ?x = Znth ?i ?l 0,
    Hp : prime ?x
      |- largest_prime_prefix_94 (?i + 1) ?l = ?x =>
      eapply largest_prime_prefix_step_prime_94; [lia|exact Hx|exact Hcur|lia|exact Hp|lia]
  | Hcur : ?cur = largest_prime_prefix_94 ?i ?l,
    Hx : ?x = Znth ?i ?l 0,
    Hp : prime ?x
      |- ?x = largest_prime_prefix_94 (?i + 1) ?l =>
      symmetry; eapply largest_prime_prefix_step_prime_94; [lia|exact Hx|exact Hcur|lia|exact Hp|lia]
  | Hcur : ?cur = largest_prime_prefix_94 ?i ?l,
    Hx : ?x = Znth ?i ?l 0,
    Hnp : ~ prime ?x
      |- largest_prime_prefix_94 (?i + 1) ?l = ?cur =>
      eapply largest_prime_prefix_step_not_prime_94; [lia|exact Hx|exact Hcur|lia|exact Hnp|lia]
  | Hcur : ?cur = largest_prime_prefix_94 ?i ?l,
    Hx : ?x = Znth ?i ?l 0,
    Hnp : ~ prime ?x
      |- ?cur = largest_prime_prefix_94 (?i + 1) ?l =>
      symmetry; eapply largest_prime_prefix_step_not_prime_94; [lia|exact Hx|exact Hcur|lia|exact Hnp|lia]
  | Hcur : ?cur = largest_prime_prefix_94 ?i ?l,
    Hx : ?x = Znth ?i ?l 0
      |- largest_prime_prefix_94 (?i + 1) ?l = ?cur =>
      eapply largest_prime_prefix_step_skip_94; [lia|exact Hx|exact Hcur|first [left; lia | right; lia]|lia]
  | Hcur : ?cur = largest_prime_prefix_94 ?i ?l,
    Hx : ?x = Znth ?i ?l 0
      |- ?cur = largest_prime_prefix_94 (?i + 1) ?l =>
      symmetry; eapply largest_prime_prefix_step_skip_94; [lia|exact Hx|exact Hcur|first [left; lia | right; lia]|lia]
  | Hsum : ?sum = sum_digits_z_94 ?largest,
    Hlargest : ?largest = largest_prime_prefix_94 (Zlength ?l) ?l
      |- problem_94_spec_z ?l ?sum =>
      eapply problem_94_spec_z_from_result_94; [lia|exact Hlargest|exact Hsum]
  end;
  unfold PRIME_LOOP_BOUND_94, INT_MIN_94 in *;
  try nia; try lia; try assumption; try reflexivity.

Ltac solve_94_vc :=
  try (right; intros);
  pre_process; entailer!;
  solve_94_pure.

Lemma proof_of_skjkasdkd_safety_wit_12_split_goal_1 : skjkasdkd_safety_wit_12_split_goal_1.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_safety_wit_12_split_goal_2 : skjkasdkd_safety_wit_12_split_goal_2.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_safety_wit_12 : skjkasdkd_safety_wit_12.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_safety_wit_21_split_goal_1 : skjkasdkd_safety_wit_21_split_goal_1.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_safety_wit_21_split_goal_2 : skjkasdkd_safety_wit_21_split_goal_2.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_safety_wit_21 : skjkasdkd_safety_wit_21.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_1_split_goal_1 : skjkasdkd_entail_wit_1_split_goal_1.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_1 : skjkasdkd_entail_wit_1.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_2_split_goal_1 : skjkasdkd_entail_wit_2_split_goal_1.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_2_split_goal_2 : skjkasdkd_entail_wit_2_split_goal_2.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_2_split_goal_3 : skjkasdkd_entail_wit_2_split_goal_3.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_2 : skjkasdkd_entail_wit_2.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_3_split_goal_1 : skjkasdkd_entail_wit_3_split_goal_1.
Proof.
  pre_process; entailer!.
  apply prime_scan_start_94.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_3 : skjkasdkd_entail_wit_3.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_4_1_split_goal_1 : skjkasdkd_entail_wit_4_1_split_goal_1.
Proof.
  pre_process; entailer!.
  eapply prime_scan_step_miss_94; [lia|eassumption|eassumption].
Qed.

Lemma proof_of_skjkasdkd_entail_wit_4_1_split_goal_2 : skjkasdkd_entail_wit_4_1_split_goal_2.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_4_1 : skjkasdkd_entail_wit_4_1.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_4_2_split_goal_1 : skjkasdkd_entail_wit_4_2_split_goal_1.
Proof.
  pre_process; entailer!.
  eapply prime_scan_step_hit_94; [lia|eassumption|eassumption].
Qed.

Lemma proof_of_skjkasdkd_entail_wit_4_2_split_goal_2 : skjkasdkd_entail_wit_4_2_split_goal_2.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_4_2 : skjkasdkd_entail_wit_4_2.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_5_split_goal_1 : skjkasdkd_entail_wit_5_split_goal_1.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_5 : skjkasdkd_entail_wit_5.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_6_split_goal_1 : skjkasdkd_entail_wit_6_split_goal_1.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_6 : skjkasdkd_entail_wit_6.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_7_1_split_goal_1 : skjkasdkd_entail_wit_7_1_split_goal_1.
Proof.
  pre_process; entailer!.
  refine (eq_sym
    (largest_prime_prefix_step_skip_94 i input_l x largest _ PreH10 PreH15 _ _)).
  - split; [exact PreH8|rewrite <- PreH5; exact PreH9].
  - right; exact PreH1.
  - exact PreH11.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_7_1 : skjkasdkd_entail_wit_7_1.
Proof.
  pre_process; entailer!.
  refine (eq_sym
    (largest_prime_prefix_step_skip_94 i input_l x largest _ PreH10 PreH15 _ _)).
  - split; [exact PreH8|rewrite <- PreH5; exact PreH9].
  - right; exact PreH1.
  - exact PreH11.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_7_2_split_goal_1 : skjkasdkd_entail_wit_7_2_split_goal_1.
Proof.
  pre_process; entailer!.
  refine (eq_sym
    (largest_prime_prefix_step_skip_94 i input_l x largest _ PreH9 PreH14 _ _)).
  - split; [exact PreH7|rewrite <- PreH4; exact PreH8].
  - left; exact PreH1.
  - exact PreH10.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_7_2 : skjkasdkd_entail_wit_7_2.
Proof.
  pre_process; entailer!.
  refine (eq_sym
    (largest_prime_prefix_step_skip_94 i input_l x largest _ PreH9 PreH14 _ _)).
  - split; [exact PreH7|rewrite <- PreH4; exact PreH8].
  - left; exact PreH1.
  - exact PreH10.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_7_3_split_goal_1 : skjkasdkd_entail_wit_7_3_split_goal_1.
Proof.
  pre_process; entailer!.
  assert (prime = 0) by lia.
  subst prime.
  pose proof (prime_flag_done_not_prime_94 x j PreH21) as Hnot.
  refine (eq_sym
    (largest_prime_prefix_step_not_prime_94 i input_l x largest _ PreH9 PreH14 PreH13 Hnot _)).
  - split; [exact PreH7|rewrite <- PreH4; exact PreH8].
  - lia.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_7_3 : skjkasdkd_entail_wit_7_3.
Proof.
  pre_process; entailer!.
  assert (prime = 0) by lia.
  subst prime.
  pose proof (prime_flag_done_not_prime_94 x j PreH21) as Hnot.
  refine (eq_sym
    (largest_prime_prefix_step_not_prime_94 i input_l x largest _ PreH9 PreH14 PreH13 Hnot _)).
  - split; [exact PreH7|rewrite <- PreH4; exact PreH8].
  - lia.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_7_4_split_goal_1 : skjkasdkd_entail_wit_7_4_split_goal_1.
Proof.
  pre_process; entailer!.
  subst prime.
  pose proof (prime_flag_done_prime_94 x j PreH21) as Hp.
  refine (eq_sym
    (largest_prime_prefix_step_prime_94 i input_l x largest _ PreH9 PreH14 PreH13 Hp _)).
  - split; [exact PreH7|rewrite <- PreH4; exact PreH8].
  - lia.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_7_4 : skjkasdkd_entail_wit_7_4.
Proof.
  pre_process; entailer!.
  subst prime.
  pose proof (prime_flag_done_prime_94 x j PreH21) as Hp.
  refine (eq_sym
    (largest_prime_prefix_step_prime_94 i input_l x largest _ PreH9 PreH14 PreH13 Hp _)).
  - split; [exact PreH7|rewrite <- PreH4; exact PreH8].
  - lia.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_9_split_goal_1 : skjkasdkd_entail_wit_9_split_goal_1.
Proof.
  pre_process; entailer!.
  destruct PreH6 as [_ Hbound].
  apply digit_sum_state_start_94; [lia|].
  rewrite PreH11.
  replace i with lst_size_pre by lia.
  rewrite PreH4.
  exact Hbound.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_9_split_goal_2 : skjkasdkd_entail_wit_9_split_goal_2.
Proof.
  pre_process; entailer!.
  rewrite PreH11.
  replace i with lst_size_pre by lia.
  reflexivity.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_9 : skjkasdkd_entail_wit_9.
Proof.
  pre_process; entailer!.
  - destruct PreH6 as [_ Hbound].
    apply digit_sum_state_start_94; [lia|].
    rewrite PreH11.
    replace i with lst_size_pre by lia.
    rewrite PreH4.
    exact Hbound.
  - rewrite PreH11.
    replace i with lst_size_pre by lia.
    reflexivity.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_10_split_goal_1 : skjkasdkd_entail_wit_10_split_goal_1.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_10_split_goal_2 : skjkasdkd_entail_wit_10_split_goal_2.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_10_split_goal_3 : skjkasdkd_entail_wit_10_split_goal_3.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_10_split_goal_4 : skjkasdkd_entail_wit_10_split_goal_4.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_10_split_goal_5 : skjkasdkd_entail_wit_10_split_goal_5.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_entail_wit_10 : skjkasdkd_entail_wit_10.
Proof. solve_94_vc. Qed.

Lemma proof_of_skjkasdkd_return_wit_1_split_goal_1 : skjkasdkd_return_wit_1_split_goal_1.
Proof.
  pre_process; entailer!.
  assert (largest = 0) by lia.
  subst largest.
  pose proof (digit_sum_state_done_94 original sum PreH15) as Hsum.
  assert (Horig : original = largest_prime_prefix_94 (Zlength input_l) input_l).
  { rewrite <- PreH4. exact PreH8. }
  eapply problem_94_spec_z_from_result_94; [lia|exact Horig|exact Hsum].
Qed.

Lemma proof_of_skjkasdkd_return_wit_1 : skjkasdkd_return_wit_1.
Proof.
  pre_process; entailer!.
  assert (largest = 0) by lia.
  subst largest.
  pose proof (digit_sum_state_done_94 original sum PreH15) as Hsum.
  assert (Horig : original = largest_prime_prefix_94 (Zlength input_l) input_l).
  { rewrite <- PreH4. exact PreH8. }
  eapply problem_94_spec_z_from_result_94; [lia|exact Horig|exact Hsum].
Qed.

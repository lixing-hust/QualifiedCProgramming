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
From SimpleC.EE.osverify_qcp.cases Require Import user_cnode_mutate_inferred_20260923_goal.
From SimpleC.EE.osverify_qcp.cases Require Import user_cnode_mutate_inferred_20260923_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.osverify_qcp.cases.user_cnode_mutate_inferred_20260923_lib.
Local Open Scope sac.

Lemma proof_of_ucos_CNode_Mutate_return_wit_1_copy_distinct_split_goal_1 : ucos_CNode_Mutate_return_wit_1_copy_distinct_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 pose proof (PreH41 (mu_space before destTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[DS DT] DC] DR].
 pose proof (PreH41 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[SS ST] SC] SR].
 clear PreH41.
 try rewrite <- DT in *; try rewrite <- DC in *; try rewrite <- DR in *;
 try rewrite <- SS in *; try rewrite <- ST in *; try rewrite <- SC in *; try rewrite <- SR in *.
 destruct PreH42 as [BD [BS [BF [BR SAFE]]]].
 unfold mu_core_result; left; split.
 - unfold mu_core_success, mu_core_indices, mu_strict_subrights, mu_type, mu_right.
   unfold mu_u8 in BD, BS.
   rewrite <- mu_mask_guard__success_state by exact BR.
   repeat split; try assumption; try lia.
 - split; [reflexivity|].
   apply mu_five_writes_final__success_state; assumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_1_copy_distinct : ucos_CNode_Mutate_return_wit_1_copy_distinct.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_ucos_CNode_Mutate_return_wit_1_copy_distinct_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_return_wit_2_copy_shared_split_goal_1 : ucos_CNode_Mutate_return_wit_2_copy_shared_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 pose proof (PreH41 (mu_space before destTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[DS DT] DC] DR].
 pose proof (PreH41 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[SS ST] SC] SR].
 clear PreH41.
 try rewrite <- DT in *; try rewrite <- DC in *; try rewrite <- DR in *;
 try rewrite <- SS in *; try rewrite <- ST in *; try rewrite <- SC in *; try rewrite <- SR in *.
 destruct PreH42 as [BD [BS [BF [BR SAFE]]]].
 unfold mu_core_result; left; split.
 - unfold mu_core_success, mu_core_indices, mu_strict_subrights, mu_type, mu_right.
   unfold mu_u8 in BD, BS.
   rewrite <- mu_mask_guard__success_state by exact BR.
   repeat split; try assumption; try lia.
 - split; [reflexivity|].
   apply mu_five_writes_final__success_state; assumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_2_copy_shared : ucos_CNode_Mutate_return_wit_2_copy_shared.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_ucos_CNode_Mutate_return_wit_2_copy_shared_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_return_wit_3_copy_distinct_split_goal_1 : ucos_CNode_Mutate_return_wit_3_copy_distinct_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 pose proof (PreH41 (mu_space before destTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[DS DT] DC] DR].
 pose proof (PreH41 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[SS ST] SC] SR].
 clear PreH41.
 try rewrite <- DT in *; try rewrite <- DC in *; try rewrite <- DR in *;
 try rewrite <- SS in *; try rewrite <- ST in *; try rewrite <- SC in *; try rewrite <- SR in *.
 destruct PreH42 as [BD [BS [BF [BR SAFE]]]].
 unfold mu_core_result; left; split.
 - unfold mu_core_success, mu_core_indices, mu_strict_subrights, mu_type, mu_right.
   unfold mu_u8 in BD, BS.
   rewrite <- mu_mask_guard__success_state by exact BR.
   repeat split; try assumption; try lia.
   all: rewrite <- PreH23; rewrite PreH22; assumption.
 - split; [reflexivity|].
   apply mu_five_writes_final__success_state; assumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_3_copy_distinct : ucos_CNode_Mutate_return_wit_3_copy_distinct.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_ucos_CNode_Mutate_return_wit_3_copy_distinct_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_return_wit_4_copy_shared_split_goal_1 : ucos_CNode_Mutate_return_wit_4_copy_shared_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 pose proof (PreH41 (mu_space before destTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[DS DT] DC] DR].
 pose proof (PreH41 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[SS ST] SC] SR].
 clear PreH41.
 try rewrite <- DT in *; try rewrite <- DC in *; try rewrite <- DR in *;
 try rewrite <- SS in *; try rewrite <- ST in *; try rewrite <- SC in *; try rewrite <- SR in *.
 destruct PreH42 as [BD [BS [BF [BR SAFE]]]].
 unfold mu_core_result; left; split.
 - unfold mu_core_success, mu_core_indices, mu_strict_subrights, mu_type, mu_right.
   unfold mu_u8 in BD, BS.
   rewrite <- mu_mask_guard__success_state by exact BR.
   repeat split; try assumption; try lia.
   all: rewrite <- PreH23; rewrite PreH22; assumption.
 - split; [reflexivity|].
   apply mu_five_writes_final__success_state; assumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_4_copy_shared : ucos_CNode_Mutate_return_wit_4_copy_shared.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_ucos_CNode_Mutate_return_wit_4_copy_shared_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_return_wit_5_source_distinct_split_goal_1 : ucos_CNode_Mutate_return_wit_5_source_distinct_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mu_core_result. right. split; [|split; reflexivity].
  intro Hsuccess.
  destruct Hsuccess as [_ [_ [_ [_ [Hmask _]]]]].
  assert (Hr : mu_u32 rights_pre) by (unfold mu_core_safe in PreH24; tauto).
  pose proof (PreH23 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as Hlayout.
  destruct Hlayout as [[[_ Htype] Hcontent] Hright].
  unfold mu_right in Hmask. rewrite Hright in Hmask.
  rewrite <- mu_mask_guard__rights_rejection in Hmask by exact Hr.
  contradiction.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_5_source_distinct : ucos_CNode_Mutate_return_wit_5_source_distinct.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_5_source_distinct_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_return_wit_6_source_shared_split_goal_1 : ucos_CNode_Mutate_return_wit_6_source_shared_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mu_core_result. right. split; [|split; reflexivity].
  intro Hsuccess.
  destruct Hsuccess as [_ [_ [_ [_ [Hmask _]]]]].
  assert (Hr : mu_u32 rights_pre) by (unfold mu_core_safe in PreH24; tauto).
  pose proof (PreH23 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as Hlayout.
  destruct Hlayout as [[[_ Htype] Hcontent] Hright].
  unfold mu_right in Hmask. rewrite Hright in Hmask.
  rewrite <- PreH5, PreH4 in Hmask.
  rewrite <- mu_mask_guard__rights_rejection in Hmask by exact Hr.
  contradiction.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_6_source_shared : ucos_CNode_Mutate_return_wit_6_source_shared.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_6_source_shared_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_return_wit_7_source_noncat_split_goal_1 : ucos_CNode_Mutate_return_wit_7_source_noncat_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH22 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Hslotaddr Htypeaddr] Hcontentaddr] Hrightaddr].
  unfold mu_core_result. right. split.
  - intros [_ [_ [_ [Htype Hrights]]]]. unfold mu_type in Htype. rewrite Htypeaddr in Htype. contradiction.
  - split; reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_7_source_noncat : ucos_CNode_Mutate_return_wit_7_source_noncat.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_7_source_noncat_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_return_wit_8_source_distinct_split_goal_1 : ucos_CNode_Mutate_return_wit_8_source_distinct_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH24 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Hslotaddr Htypeaddr] Hcontentaddr] Hrightaddr].
  unfold mu_core_result. right. split.
  - intros [_ [_ [_ [Htype Hrights]]]]. unfold mu_strict_subrights, mu_right in Hrights. rewrite Hrightaddr in Hrights. tauto.
  - split; reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_8_source_distinct : ucos_CNode_Mutate_return_wit_8_source_distinct.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_8_source_distinct_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_return_wit_9_source_shared_split_goal_1 : ucos_CNode_Mutate_return_wit_9_source_shared_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH24 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Hslotaddr Htypeaddr] Hcontentaddr] Hrightaddr].
  unfold mu_core_result. right. split.
  - intros [_ [_ [_ [Htype Hrights]]]]. unfold mu_strict_subrights, mu_right in Hrights. rewrite Hrightaddr, <- PreH6, PreH5 in Hrights. tauto.
  - split; reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_9_source_shared : ucos_CNode_Mutate_return_wit_9_source_shared.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_9_source_shared_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_return_wit_10_split_goal_1 : ucos_CNode_Mutate_return_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mu_core_result. right.
  split.
  - unfold mu_core_success, mu_core_indices.
    intros (? & ? & ? & ? & ?). lia.
  - split; reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_10 : ucos_CNode_Mutate_return_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_10_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_return_wit_11_split_goal_1 : ucos_CNode_Mutate_return_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mu_core_result. right.
  split.
  - unfold mu_core_success, mu_core_indices.
    intros (? & ? & ? & ? & ?). lia.
  - split; reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_11 : ucos_CNode_Mutate_return_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_11_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_return_wit_12_split_goal_1 : ucos_CNode_Mutate_return_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mu_core_result. right.
  split.
  - unfold mu_core_success, mu_core_indices.
    intros (? & ? & ? & ? & ?). lia.
  - split; reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_12 : ucos_CNode_Mutate_return_wit_12.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_12_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_return_wit_13_split_goal_1 : ucos_CNode_Mutate_return_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mu_core_result. right.
  split.
  - unfold mu_core_success, mu_core_indices.
    intros (? & ? & ? & ? & ?). lia.
  - split; reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_13 : ucos_CNode_Mutate_return_wit_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_13_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_return_wit_14_split_goal_1 : ucos_CNode_Mutate_return_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mu_core_result. right.
  split.
  - unfold mu_core_success, mu_core_indices.
    intros (? & ? & ? & ? & ?). lia.
  - split; reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_14 : ucos_CNode_Mutate_return_wit_14.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_14_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_return_wit_15_split_goal_1 : ucos_CNode_Mutate_return_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mu_core_result. right.
  split.
  - unfold mu_core_success, mu_core_indices.
    intros (? & ? & ? & ? & ?). lia.
  - split; reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_15 : ucos_CNode_Mutate_return_wit_15.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_15_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_1_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mu_core_safe ?h ?d ?s ?f ?r |- _ =>
    destruct H as [Hd [Hs [Hf [Hr Hsafe]]]];
    assert (Hi : mu_core_indices d s f) by (unfold mu_core_indices, mu_u8 in *; lia);
    specialize (Hsafe Hi)
  end.
  unfold mu_table_addr in Hsafe.
  match goal with H : mu_tb _ = _ |- _ => unfold mu_tb in H; rewrite H in Hsafe end.
  simpl in *.
  tauto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_1_pure : ucos_CNode_Mutate_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_1_pure_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_2_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mu_space, mu_table_addr.
  match goal with H : mu_tb _ = _ |- _ => unfold mu_tb in H; rewrite H end.
  reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_2_pure_split_goal_2 : ucos_CNode_Mutate_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mu_space, mu_table_addr.
  match goal with H : mu_tb _ = _ |- _ => unfold mu_tb in H; rewrite H end.
  reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_2_pure : ucos_CNode_Mutate_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_2_pure_split_goal_2.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_3_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mu_core_safe ?h ?d ?s ?f ?r |- _ =>
    destruct H as [Hd [Hs [Hf [Hr Hsafe]]]];
    assert (Hi : mu_core_indices d s f) by (unfold mu_core_indices, mu_u8 in *; lia);
    specialize (Hsafe Hi)
  end.
  unfold mu_table_addr in Hsafe.
  match goal with H : mu_tb _ = _ |- _ => unfold mu_tb in H; rewrite H in Hsafe end.
  simpl in *.
  tauto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_3_pure : ucos_CNode_Mutate_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_3_pure_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_4_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mu_space, mu_table_addr.
  match goal with H : mu_tb _ = _ |- _ => unfold mu_tb in H; rewrite H end.
  reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_4_pure_split_goal_2 : ucos_CNode_Mutate_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mu_space, mu_table_addr.
  match goal with H : mu_tb _ = _ |- _ => unfold mu_tb in H; rewrite H end.
  reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_4_pure : ucos_CNode_Mutate_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_4_pure_split_goal_2.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_5_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mu_core_safe ?h ?d ?s ?f ?r |- _ =>
    destruct H as [Hd [Hs [Hf [Hr Hsafe]]]];
    assert (Hi : mu_core_indices d s f) by (unfold mu_core_indices, mu_u8 in *; lia);
    specialize (Hsafe Hi)
  end.
  destruct Hsafe as [_ [_ Hsafe]].
  specialize (Hsafe ltac:(split; assumption)).
  match goal with H : forall p f, 0 <= f /\ f < 255 -> _ |- _ =>
    let Hlayout := fresh "Hlayout" in
    pose proof (H (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as Hlayout;
    destruct Hlayout as [[[Hslot Htype] Hcontent] Hright];
    unfold mu_type in Hsafe;
    rewrite Htype, Hright in Hsafe
  end.
  tauto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_5_pure_split_goal_2 : ucos_CNode_Mutate_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mu_core_safe ?h ?d ?s ?f ?r |- _ =>
    destruct H as [Hd [Hs [Hf [Hr Hsafe]]]];
    assert (Hi : mu_core_indices d s f) by (unfold mu_core_indices, mu_u8 in *; lia);
    specialize (Hsafe Hi)
  end.
  destruct Hsafe as [_ [_ Hsafe]].
  specialize (Hsafe ltac:(split; assumption)).
  match goal with H : forall p f, 0 <= f /\ f < 255 -> _ |- _ =>
    let Hlayout := fresh "Hlayout" in
    pose proof (H (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as Hlayout;
    destruct Hlayout as [[[Hslot Htype] Hcontent] Hright];
    unfold mu_type in Hsafe;
    rewrite Htype, Hright in Hsafe
  end.
  tauto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_5_pure : ucos_CNode_Mutate_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_5_pure_split_goal_1.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_5_pure_split_goal_2.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_7_source_shared_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_7_source_shared_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mu_core_safe ?h ?d ?s ?f ?r |- _ =>
    unfold mu_core_safe in H;
    destruct H as [Hd [Hs [Hf [Hr Hsafe]]]];
    assert (Hi : mu_core_indices d s f) by (unfold mu_core_indices, mu_u8 in *; lia);
    destruct (Hsafe Hi) as [_ [_ Hlive]];
    specialize (Hlive ltac:(split; assumption));
    destruct Hlive as [Htype [Hright Hrest]];
    match goal with Hl : forall p f, _ -> _ /\ _ |- _ =>
      specialize (Hl (mu_space h s) f ltac:(lia));
      destruct Hl as [[[Hslot Etype] Econtent] Eright];
      unfold mu_type in Hright;
      rewrite Etype in Htype, Hright;
      rewrite Eright in Hright
    end
  end.
  intuition auto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_7_source_shared_pure_split_goal_2 : ucos_CNode_Mutate_partial_solve_wit_7_source_shared_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mu_core_safe ?h ?d ?s ?f ?r |- _ =>
    unfold mu_core_safe in H;
    destruct H as [Hd [Hs [Hf [Hr Hsafe]]]];
    assert (Hi : mu_core_indices d s f) by (unfold mu_core_indices, mu_u8 in *; lia);
    destruct (Hsafe Hi) as [_ [_ Hlive]];
    specialize (Hlive ltac:(split; assumption));
    destruct Hlive as [Htype [Hright Hrest]];
    match goal with Hl : forall p f, _ -> _ /\ _ |- _ =>
      specialize (Hl (mu_space h s) f ltac:(lia));
      destruct Hl as [[[Hslot Etype] Econtent] Eright];
      unfold mu_type in Hright;
      rewrite Etype in Htype, Hright;
      rewrite Eright in Hright
    end
  end.
  intuition auto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_7_source_shared_pure_split_goal_3 : ucos_CNode_Mutate_partial_solve_wit_7_source_shared_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mu_core_safe ?h ?d ?s ?f ?r |- _ =>
    unfold mu_core_safe in H;
    destruct H as [Hd [Hs [Hf [Hr Hsafe]]]];
    assert (Hi : mu_core_indices d s f) by (unfold mu_core_indices, mu_u8 in *; lia);
    destruct (Hsafe Hi) as [_ [_ Hlive]];
    specialize (Hlive ltac:(split; assumption));
    destruct Hlive as [Htype [Hright Hrest]];
    match goal with Hl : forall p f, _ -> _ /\ _ |- _ =>
      specialize (Hl (mu_space h s) f ltac:(lia));
      destruct Hl as [[[Hslot Etype] Econtent] Eright];
      unfold mu_type in Hright;
      rewrite Etype in Htype, Hright;
      rewrite Eright in Hright
    end
  end.
  intuition auto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_7_source_shared_pure : ucos_CNode_Mutate_partial_solve_wit_7_source_shared_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_7_source_shared_pure_split_goal_1.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_7_source_shared_pure_split_goal_2.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_7_source_shared_pure_split_goal_3.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_8_source_distinct_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_8_source_distinct_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mu_core_safe ?h ?d ?s ?f ?r |- _ =>
    unfold mu_core_safe in H;
    destruct H as [Hd [Hs [Hf [Hr Hsafe]]]];
    assert (Hi : mu_core_indices d s f) by (unfold mu_core_indices, mu_u8 in *; lia);
    destruct (Hsafe Hi) as [_ [_ Hlive]];
    specialize (Hlive ltac:(split; assumption));
    destruct Hlive as [Htype [Hright Hrest]];
    match goal with Hl : forall p f, _ -> _ /\ _ |- _ =>
      specialize (Hl (mu_space h s) f ltac:(lia));
      destruct Hl as [[[Hslot Etype] Econtent] Eright];
      unfold mu_type in Hright;
      rewrite Etype in Htype, Hright;
      rewrite Eright in Hright
    end
  end.
  intuition auto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_8_source_distinct_pure_split_goal_2 : ucos_CNode_Mutate_partial_solve_wit_8_source_distinct_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mu_core_safe ?h ?d ?s ?f ?r |- _ =>
    unfold mu_core_safe in H;
    destruct H as [Hd [Hs [Hf [Hr Hsafe]]]];
    assert (Hi : mu_core_indices d s f) by (unfold mu_core_indices, mu_u8 in *; lia);
    destruct (Hsafe Hi) as [_ [_ Hlive]];
    specialize (Hlive ltac:(split; assumption));
    destruct Hlive as [Htype [Hright Hrest]];
    match goal with Hl : forall p f, _ -> _ /\ _ |- _ =>
      specialize (Hl (mu_space h s) f ltac:(lia));
      destruct Hl as [[[Hslot Etype] Econtent] Eright];
      unfold mu_type in Hright;
      rewrite Etype in Htype, Hright;
      rewrite Eright in Hright
    end
  end.
  intuition auto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_8_source_distinct_pure_split_goal_3 : ucos_CNode_Mutate_partial_solve_wit_8_source_distinct_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mu_core_safe ?h ?d ?s ?f ?r |- _ =>
    unfold mu_core_safe in H;
    destruct H as [Hd [Hs [Hf [Hr Hsafe]]]];
    assert (Hi : mu_core_indices d s f) by (unfold mu_core_indices, mu_u8 in *; lia);
    destruct (Hsafe Hi) as [_ [_ Hlive]];
    specialize (Hlive ltac:(split; assumption));
    destruct Hlive as [Htype [Hright Hrest]];
    match goal with Hl : forall p f, _ -> _ /\ _ |- _ =>
      specialize (Hl (mu_space h s) f ltac:(lia));
      destruct Hl as [[[Hslot Etype] Econtent] Eright];
      unfold mu_type in Hright;
      rewrite Etype in Htype, Hright;
      rewrite Eright in Hright
    end
  end.
  intuition auto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_8_source_distinct_pure : ucos_CNode_Mutate_partial_solve_wit_8_source_distinct_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_8_source_distinct_pure_split_goal_1.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_8_source_distinct_pure_split_goal_2.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_8_source_distinct_pure_split_goal_3.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_9_source_shared_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_9_source_shared_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  assert (Hf : 0 <= func_capability_pre < 255) by lia.
  destruct (PreH28 (mu_space before srcTask_Prio_pre) func_capability_pre Hf) as [[[Hs Ht] Hc] Hr].
  destruct (PreH28 (mu_space before destTask_Prio_pre) func_capability_pre Hf) as [[[Ds Dt] Dc] Dr].
  destruct PreH29 as [Hd [Hsrc [Hfunc [Hrights Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre).
  { unfold mu_core_indices, mu_u8 in *. lia. }
  assert (Htval : mu_type before (mu_space before srcTask_Prio_pre) func_capability_pre = 1).
  { unfold mu_type. rewrite Ht. exact PreH9. }
  assert (Hstrict : mu_strict_subrights (mu_right before (mu_space before srcTask_Prio_pre) func_capability_pre) rights_pre).
  { unfold mu_strict_subrights. rewrite mu_mask_guard__destination_initial_safety by exact Hrights.
     unfold mu_right. rewrite Hr.
     rewrite <- PreH10, PreH9. split; assumption. }
  assert (Hsuccess : mu_core_success before destTask_Prio_pre srcTask_Prio_pre func_capability_pre rights_pre).
  { unfold mu_core_success. split; [exact Hi|]. split; [assumption|]. split; [assumption|]. split; assumption. }
  destruct (Hsafe Hi) as [_ [_ Hsafe2]].
  assert (Hnon : mu_space before destTask_Prio_pre <> 0 /\ mu_space before srcTask_Prio_pre <> 0) by auto.
  destruct (Hsafe2 Hnon) as [_ [_ HsuccessSafe]].
  destruct (HsuccessSafe Hsuccess) as [Hread [Hwt [Hwc Hrest]]].
  rewrite <- Dt. exact Hwt.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_9_source_shared_pure : ucos_CNode_Mutate_partial_solve_wit_9_source_shared_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_9_source_shared_pure_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_10_source_distinct_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_10_source_distinct_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  assert (Hf : 0 <= func_capability_pre < 255) by lia.
  destruct (PreH28 (mu_space before srcTask_Prio_pre) func_capability_pre Hf) as [[[Hs Ht] Hc] Hr].
  destruct (PreH28 (mu_space before destTask_Prio_pre) func_capability_pre Hf) as [[[Ds Dt] Dc] Dr].
  destruct PreH29 as [Hd [Hsrc [Hfunc [Hrights Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre).
  { unfold mu_core_indices, mu_u8 in *. lia. }
  assert (Htval : mu_type before (mu_space before srcTask_Prio_pre) func_capability_pre = 1).
  { unfold mu_type. rewrite Ht. exact PreH9. }
  assert (Hstrict : mu_strict_subrights (mu_right before (mu_space before srcTask_Prio_pre) func_capability_pre) rights_pre).
  { unfold mu_strict_subrights. rewrite mu_mask_guard__destination_initial_safety by exact Hrights.
     unfold mu_right. rewrite Hr.
     split; assumption. }
  assert (Hsuccess : mu_core_success before destTask_Prio_pre srcTask_Prio_pre func_capability_pre rights_pre).
  { unfold mu_core_success. split; [exact Hi|]. split; [assumption|]. split; [assumption|]. split; assumption. }
  destruct (Hsafe Hi) as [_ [_ Hsafe2]].
  assert (Hnon : mu_space before destTask_Prio_pre <> 0 /\ mu_space before srcTask_Prio_pre <> 0) by auto.
  destruct (Hsafe2 Hnon) as [_ [_ HsuccessSafe]].
  destruct (HsuccessSafe Hsuccess) as [Hread [Hwt [Hwc Hrest]]].
  rewrite <- Dt. exact Hwt.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_10_source_distinct_pure : ucos_CNode_Mutate_partial_solve_wit_10_source_distinct_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_10_source_distinct_pure_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_13_source_shared_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_13_source_shared_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  assert (Hf : 0 <= func_capability_pre < 255) by lia.
  destruct (PreH31 (mu_space before srcTask_Prio_pre) func_capability_pre Hf) as [[[Hs Ht] Hc] Hr].
  destruct (PreH31 (mu_space before destTask_Prio_pre) func_capability_pre Hf) as [[[Ds Dt] Dc] Dr].
  destruct PreH32 as [Hd [Hsrc [Hfunc [Hrights Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre).
  { unfold mu_core_indices, mu_u8 in *. lia. }
  assert (Htval : mu_type before (mu_space before srcTask_Prio_pre) func_capability_pre = 1).
  { unfold mu_type. rewrite Ht. exact PreH12. }
  assert (Hstrict : mu_strict_subrights (mu_right before (mu_space before srcTask_Prio_pre) func_capability_pre) rights_pre).
  { unfold mu_strict_subrights. rewrite mu_mask_guard__destination_initial_safety by exact Hrights.
     unfold mu_right. rewrite Hr.
     rewrite <- PreH13, PreH12. split; assumption. }
  assert (Hsuccess : mu_core_success before destTask_Prio_pre srcTask_Prio_pre func_capability_pre rights_pre).
  { unfold mu_core_success. split; [exact Hi|]. split; [assumption|]. split; [assumption|]. split; assumption. }
  destruct (Hsafe Hi) as [_ [_ Hsafe2]].
  assert (Hnon : mu_space before destTask_Prio_pre <> 0 /\ mu_space before srcTask_Prio_pre <> 0) by auto.
  destruct (Hsafe2 Hnon) as [_ [_ HsuccessSafe]].
  destruct (HsuccessSafe Hsuccess) as [Hread [Hwt [Hwc Hrest]]].
  rewrite <- Dt, <- Hc. exact Hread.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_13_source_shared_pure_split_goal_2 : ucos_CNode_Mutate_partial_solve_wit_13_source_shared_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  assert (Hf : 0 <= func_capability_pre < 255) by lia.
  destruct (PreH31 (mu_space before srcTask_Prio_pre) func_capability_pre Hf) as [[[Hs Ht] Hc] Hr].
  destruct (PreH31 (mu_space before destTask_Prio_pre) func_capability_pre Hf) as [[[Ds Dt] Dc] Dr].
  destruct PreH32 as [Hd [Hsrc [Hfunc [Hrights Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre).
  { unfold mu_core_indices, mu_u8 in *. lia. }
  assert (Htval : mu_type before (mu_space before srcTask_Prio_pre) func_capability_pre = 1).
  { unfold mu_type. rewrite Ht. exact PreH12. }
  assert (Hstrict : mu_strict_subrights (mu_right before (mu_space before srcTask_Prio_pre) func_capability_pre) rights_pre).
  { unfold mu_strict_subrights. rewrite mu_mask_guard__destination_initial_safety by exact Hrights.
     unfold mu_right. rewrite Hr.
     rewrite <- PreH13, PreH12. split; assumption. }
  assert (Hsuccess : mu_core_success before destTask_Prio_pre srcTask_Prio_pre func_capability_pre rights_pre).
  { unfold mu_core_success. split; [exact Hi|]. split; [assumption|]. split; [assumption|]. split; assumption. }
  destruct (Hsafe Hi) as [_ [_ Hsafe2]].
  assert (Hnon : mu_space before destTask_Prio_pre <> 0 /\ mu_space before srcTask_Prio_pre <> 0) by auto.
  destruct (Hsafe2 Hnon) as [_ [_ HsuccessSafe]].
  destruct (HsuccessSafe Hsuccess) as [Hread [Hwt [Hwc Hrest]]].
  rewrite <- Dt, <- Dc. apply mu_writable_set__destination_initial_safety. exact Hwc.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_13_source_shared_pure : ucos_CNode_Mutate_partial_solve_wit_13_source_shared_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_13_source_shared_pure_split_goal_1.
  Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_13_source_shared_pure_split_goal_2.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_14_source_distinct_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_14_source_distinct_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  assert (Hf : 0 <= func_capability_pre < 255) by lia.
  destruct (PreH31 (mu_space before srcTask_Prio_pre) func_capability_pre Hf) as [[[Hs Ht] Hc] Hr].
  destruct (PreH31 (mu_space before destTask_Prio_pre) func_capability_pre Hf) as [[[Ds Dt] Dc] Dr].
  destruct PreH32 as [Hd [Hsrc [Hfunc [Hrights Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre).
  { unfold mu_core_indices, mu_u8 in *. lia. }
  assert (Htval : mu_type before (mu_space before srcTask_Prio_pre) func_capability_pre = 1).
  { unfold mu_type. rewrite Ht. exact PreH12. }
  assert (Hstrict : mu_strict_subrights (mu_right before (mu_space before srcTask_Prio_pre) func_capability_pre) rights_pre).
  { unfold mu_strict_subrights. rewrite mu_mask_guard__destination_initial_safety by exact Hrights.
     unfold mu_right. rewrite Hr.
     split; assumption. }
  assert (Hsuccess : mu_core_success before destTask_Prio_pre srcTask_Prio_pre func_capability_pre rights_pre).
  { unfold mu_core_success. split; [exact Hi|]. split; [assumption|]. split; [assumption|]. split; assumption. }
  destruct (Hsafe Hi) as [_ [_ Hsafe2]].
  assert (Hnon : mu_space before destTask_Prio_pre <> 0 /\ mu_space before srcTask_Prio_pre <> 0) by auto.
  destruct (Hsafe2 Hnon) as [_ [_ HsuccessSafe]].
  destruct (HsuccessSafe Hsuccess) as [Hread [Hwt [Hwc Hrest]]].
  rewrite <- Dt, <- Hc. exact Hread.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_14_source_distinct_pure_split_goal_2 : ucos_CNode_Mutate_partial_solve_wit_14_source_distinct_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  assert (Hf : 0 <= func_capability_pre < 255) by lia.
  destruct (PreH31 (mu_space before srcTask_Prio_pre) func_capability_pre Hf) as [[[Hs Ht] Hc] Hr].
  destruct (PreH31 (mu_space before destTask_Prio_pre) func_capability_pre Hf) as [[[Ds Dt] Dc] Dr].
  destruct PreH32 as [Hd [Hsrc [Hfunc [Hrights Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre).
  { unfold mu_core_indices, mu_u8 in *. lia. }
  assert (Htval : mu_type before (mu_space before srcTask_Prio_pre) func_capability_pre = 1).
  { unfold mu_type. rewrite Ht. exact PreH12. }
  assert (Hstrict : mu_strict_subrights (mu_right before (mu_space before srcTask_Prio_pre) func_capability_pre) rights_pre).
  { unfold mu_strict_subrights. rewrite mu_mask_guard__destination_initial_safety by exact Hrights.
     unfold mu_right. rewrite Hr.
     split; assumption. }
  assert (Hsuccess : mu_core_success before destTask_Prio_pre srcTask_Prio_pre func_capability_pre rights_pre).
  { unfold mu_core_success. split; [exact Hi|]. split; [assumption|]. split; [assumption|]. split; assumption. }
  destruct (Hsafe Hi) as [_ [_ Hsafe2]].
  assert (Hnon : mu_space before destTask_Prio_pre <> 0 /\ mu_space before srcTask_Prio_pre <> 0) by auto.
  destruct (Hsafe2 Hnon) as [_ [_ HsuccessSafe]].
  destruct (HsuccessSafe Hsuccess) as [Hread [Hwt [Hwc Hrest]]].
  rewrite <- Dt, <- Dc. apply mu_writable_set__destination_initial_safety. exact Hwc.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_14_source_distinct_pure : ucos_CNode_Mutate_partial_solve_wit_14_source_distinct_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_14_source_distinct_pure_split_goal_1.
  Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_14_source_distinct_pure_split_goal_2.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_21_copy_shared_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_21_copy_shared_pure_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 apply mu_writable_set__destination_right_safety.
 apply mu_writable_set__destination_right_safety.
 pose proof PreH37 as Hsafe.
 destruct Hsafe as [Hd [Hs [Hf [Hr Hsafe]]]].
 assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre).
 { unfold mu_core_indices, mu_u8 in *; lia. }
 destruct (PreH36 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Ls Lt] Lc] Lr].
 destruct (PreH36 (mu_space before destTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Ds Dt] Dc] Dr].
 assert (Hsuccess : mu_core_success before destTask_Prio_pre srcTask_Prio_pre func_capability_pre rights_pre).
 { unfold mu_core_success. split; [exact Hi|].
   split; [exact PreH20|]. split; [exact PreH19|].
   split.
   - unfold mu_type. rewrite Lt. exact PreH17.
   - unfold mu_strict_subrights, mu_right. rewrite Lr.
     rewrite <- PreH18, PreH17.
     split; [apply mu_mask_guard__destination_right_safety; assumption|assumption]. }
 destruct (Hsafe Hi) as [_ [_ Hsafe']].
 destruct (Hsafe' (conj PreH20 PreH19)) as [_ [_ Hsuccess']].
 destruct (Hsuccess' Hsuccess) as [_ [_ [_ [Hw _]]]].
 rewrite Dr in Hw. exact Hw.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_21_copy_shared_pure : ucos_CNode_Mutate_partial_solve_wit_21_copy_shared_pure.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_21_copy_shared_pure_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_22_copy_distinct_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_22_copy_distinct_pure_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 apply mu_writable_set__destination_right_safety.
 apply mu_writable_set__destination_right_safety.
 pose proof PreH37 as Hsafe.
 destruct Hsafe as [Hd [Hs [Hf [Hr Hsafe]]]].
 assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre).
 { unfold mu_core_indices, mu_u8 in *; lia. }
 destruct (PreH36 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Ls Lt] Lc] Lr].
 destruct (PreH36 (mu_space before destTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Ds Dt] Dc] Dr].
 assert (Hsuccess : mu_core_success before destTask_Prio_pre srcTask_Prio_pre func_capability_pre rights_pre).
 { unfold mu_core_success. split; [exact Hi|].
   split; [exact PreH20|]. split; [exact PreH19|].
   split.
   - unfold mu_type. rewrite Lt. exact PreH17.
   - unfold mu_strict_subrights, mu_right. rewrite Lr.
     rewrite <- PreH18, PreH17.
     split; [apply mu_mask_guard__destination_right_safety; assumption|assumption]. }
 destruct (Hsafe Hi) as [_ [_ Hsafe']].
 destruct (Hsafe' (conj PreH20 PreH19)) as [_ [_ Hsuccess']].
 destruct (Hsuccess' Hsuccess) as [_ [_ [_ [Hw _]]]].
 rewrite Dr in Hw. exact Hw.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_22_copy_distinct_pure : ucos_CNode_Mutate_partial_solve_wit_22_copy_distinct_pure.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_22_copy_distinct_pure_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_23_copy_shared_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_23_copy_shared_pure_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 apply mu_writable_set__destination_right_safety.
 apply mu_writable_set__destination_right_safety.
 pose proof PreH37 as Hsafe.
 destruct Hsafe as [Hd [Hs [Hf [Hr Hsafe]]]].
 assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre).
 { unfold mu_core_indices, mu_u8 in *; lia. }
 destruct (PreH36 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Ls Lt] Lc] Lr].
 destruct (PreH36 (mu_space before destTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Ds Dt] Dc] Dr].
 assert (Hsuccess : mu_core_success before destTask_Prio_pre srcTask_Prio_pre func_capability_pre rights_pre).
 { unfold mu_core_success. split; [exact Hi|].
   split; [exact PreH20|]. split; [exact PreH19|].
   split.
   - unfold mu_type. rewrite Lt. exact PreH17.
   - unfold mu_strict_subrights, mu_right. rewrite Lr.
     split; [apply mu_mask_guard__destination_right_safety; assumption|assumption]. }
 destruct (Hsafe Hi) as [_ [_ Hsafe']].
 destruct (Hsafe' (conj PreH20 PreH19)) as [_ [_ Hsuccess']].
 destruct (Hsuccess' Hsuccess) as [_ [_ [_ [Hw _]]]].
 rewrite Dr in Hw. exact Hw.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_23_copy_shared_pure : ucos_CNode_Mutate_partial_solve_wit_23_copy_shared_pure.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_23_copy_shared_pure_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_24_copy_distinct_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_24_copy_distinct_pure_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 apply mu_writable_set__destination_right_safety.
 apply mu_writable_set__destination_right_safety.
 pose proof PreH37 as Hsafe.
 destruct Hsafe as [Hd [Hs [Hf [Hr Hsafe]]]].
 assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre).
 { unfold mu_core_indices, mu_u8 in *; lia. }
 destruct (PreH36 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Ls Lt] Lc] Lr].
 destruct (PreH36 (mu_space before destTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Ds Dt] Dc] Dr].
 assert (Hsuccess : mu_core_success before destTask_Prio_pre srcTask_Prio_pre func_capability_pre rights_pre).
 { unfold mu_core_success. split; [exact Hi|].
   split; [exact PreH20|]. split; [exact PreH19|].
   split.
   - unfold mu_type. rewrite Lt. exact PreH17.
   - unfold mu_strict_subrights, mu_right. rewrite Lr.
     split; [apply mu_mask_guard__destination_right_safety; assumption|assumption]. }
 destruct (Hsafe Hi) as [_ [_ Hsafe']].
 destruct (Hsafe' (conj PreH20 PreH19)) as [_ [_ Hsuccess']].
 destruct (Hsuccess' Hsuccess) as [_ [_ [_ [Hw _]]]].
 rewrite Dr in Hw. exact Hw.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_24_copy_distinct_pure : ucos_CNode_Mutate_partial_solve_wit_24_copy_distinct_pure.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_24_copy_distinct_pure_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_29_copy_shared_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_29_copy_shared_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat apply mu_readable_set__source_right_safety.
  match goal with H : mu_core_safe ?h ?d ?s ?f ?r |- _ =>
    destruct H as [Hd [Hs [Hf [Hr Hsafe]]]];
    assert (Hi : mu_core_indices d s f) by (unfold mu_core_indices, mu_u8 in *; lia);
    destruct (Hsafe Hi) as [_ [_ Hnonzero]];
    destruct (Hnonzero ltac:(split; assumption)) as [_ [Hread _]]
  end.
  match goal with H : forall (p f : Z), _ |- _ =>
    pose proof (H (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as Hl
  end.
  destruct Hl as [[[_ Htype] _] Hright].
  rewrite <- Hright.
  apply Hread.
  unfold mu_type. rewrite Htype. assumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_29_copy_shared_pure : ucos_CNode_Mutate_partial_solve_wit_29_copy_shared_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_29_copy_shared_pure_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_30_copy_distinct_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_30_copy_distinct_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat apply mu_readable_set__source_right_safety.
  match goal with H : mu_core_safe ?h ?d ?s ?f ?r |- _ =>
    destruct H as [Hd [Hs [Hf [Hr Hsafe]]]];
    assert (Hi : mu_core_indices d s f) by (unfold mu_core_indices, mu_u8 in *; lia);
    destruct (Hsafe Hi) as [_ [_ Hnonzero]];
    destruct (Hnonzero ltac:(split; assumption)) as [_ [Hread _]]
  end.
  match goal with H : forall (p f : Z), _ |- _ =>
    pose proof (H (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as Hl
  end.
  destruct Hl as [[[_ Htype] _] Hright].
  rewrite <- Hright.
  apply Hread.
  unfold mu_type. rewrite Htype. assumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_30_copy_distinct_pure : ucos_CNode_Mutate_partial_solve_wit_30_copy_distinct_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_30_copy_distinct_pure_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_31_copy_shared_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_31_copy_shared_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat apply mu_readable_set__source_right_safety.
  match goal with H : mu_core_safe ?h ?d ?s ?f ?r |- _ =>
    destruct H as [Hd [Hs [Hf [Hr Hsafe]]]];
    assert (Hi : mu_core_indices d s f) by (unfold mu_core_indices, mu_u8 in *; lia);
    destruct (Hsafe Hi) as [_ [_ Hnonzero]];
    destruct (Hnonzero ltac:(split; assumption)) as [_ [Hread _]]
  end.
  match goal with H : forall (p f : Z), _ |- _ =>
    pose proof (H (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as Hl
  end.
  destruct Hl as [[[_ Htype] _] Hright].
  rewrite <- Hright.
  apply Hread.
  unfold mu_type. rewrite Htype. assumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_31_copy_shared_pure : ucos_CNode_Mutate_partial_solve_wit_31_copy_shared_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_31_copy_shared_pure_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_32_copy_distinct_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_32_copy_distinct_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat apply mu_readable_set__source_right_safety.
  match goal with H : mu_core_safe ?h ?d ?s ?f ?r |- _ =>
    destruct H as [Hd [Hs [Hf [Hr Hsafe]]]];
    assert (Hi : mu_core_indices d s f) by (unfold mu_core_indices, mu_u8 in *; lia);
    destruct (Hsafe Hi) as [_ [_ Hnonzero]];
    destruct (Hnonzero ltac:(split; assumption)) as [_ [Hread _]]
  end.
  match goal with H : forall (p f : Z), _ |- _ =>
    pose proof (H (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as Hl
  end.
  destruct Hl as [[[_ Htype] _] Hright].
  rewrite <- Hright.
  apply Hread.
  unfold mu_type. rewrite Htype. assumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_32_copy_distinct_pure : ucos_CNode_Mutate_partial_solve_wit_32_copy_distinct_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_32_copy_distinct_pure_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_33_copy_shared_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_33_copy_shared_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mu_land, mu_complement.
  apply mu_clear_mask_bounded_result__clear_mask;
    change (2^32) with 4294967296; lia.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_33_copy_shared_pure_split_goal_2 : ucos_CNode_Mutate_partial_solve_wit_33_copy_shared_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mu_writable.
  match goal with H : mu_readable ?h ?k ?a |- _ =>
    destruct H as [v Hv]; exists (Some v); exact Hv
  end.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_33_copy_shared_pure : ucos_CNode_Mutate_partial_solve_wit_33_copy_shared_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_33_copy_shared_pure_split_goal_1.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_33_copy_shared_pure_split_goal_2.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_34_copy_distinct_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_34_copy_distinct_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mu_land, mu_complement.
  apply mu_clear_mask_bounded_result__clear_mask;
    change (2^32) with 4294967296; lia.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_34_copy_distinct_pure_split_goal_2 : ucos_CNode_Mutate_partial_solve_wit_34_copy_distinct_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mu_writable.
  match goal with H : mu_readable ?h ?k ?a |- _ =>
    destruct H as [v Hv]; exists (Some v); exact Hv
  end.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_34_copy_distinct_pure : ucos_CNode_Mutate_partial_solve_wit_34_copy_distinct_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_34_copy_distinct_pure_split_goal_1.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_34_copy_distinct_pure_split_goal_2.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_35_copy_shared_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_35_copy_shared_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mu_land, mu_complement.
  apply mu_clear_mask_bounded_result__clear_mask;
    change (2^32) with 4294967296; lia.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_35_copy_shared_pure_split_goal_2 : ucos_CNode_Mutate_partial_solve_wit_35_copy_shared_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mu_writable.
  match goal with H : mu_readable ?h ?k ?a |- _ =>
    destruct H as [v Hv]; exists (Some v); exact Hv
  end.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_35_copy_shared_pure : ucos_CNode_Mutate_partial_solve_wit_35_copy_shared_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_35_copy_shared_pure_split_goal_1.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_35_copy_shared_pure_split_goal_2.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_36_copy_distinct_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_36_copy_distinct_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mu_land, mu_complement.
  apply mu_clear_mask_bounded_result__clear_mask;
    change (2^32) with 4294967296; lia.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_36_copy_distinct_pure_split_goal_2 : ucos_CNode_Mutate_partial_solve_wit_36_copy_distinct_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mu_writable.
  match goal with H : mu_readable ?h ?k ?a |- _ =>
    destruct H as [v Hv]; exists (Some v); exact Hv
  end.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_36_copy_distinct_pure : ucos_CNode_Mutate_partial_solve_wit_36_copy_distinct_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_36_copy_distinct_pure_split_goal_1.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_36_copy_distinct_pure_split_goal_2.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_37_source_noncat_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_37_source_noncat_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mu_core_safe ?h ?d ?s ?f ?r |- _ =>
    unfold mu_core_safe in H;
    destruct H as [Hd [Hs [Hf [Hr Hsafe]]]];
    assert (Hi : mu_core_indices d s f) by (unfold mu_core_indices, mu_u8 in *; lia);
    destruct (Hsafe Hi) as [_ [_ Hlive]];
    specialize (Hlive ltac:(split; assumption));
    destruct Hlive as [Htype [Hright Hrest]];
    match goal with Hl : forall p f, _ -> _ /\ _ |- _ =>
      specialize (Hl (mu_space h s) f ltac:(lia));
      destruct Hl as [[[Hslot Etype] Econtent] Eright];
      unfold mu_type in Hright;
      rewrite Etype in Htype, Hright;
      rewrite Eright in Hright
    end
  end.
  intuition auto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_37_source_noncat_pure : ucos_CNode_Mutate_partial_solve_wit_37_source_noncat_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_37_source_noncat_pure_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_38_source_shared_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_38_source_shared_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros.
  destruct PreH30 as [Hd [Hs [Hf [Hr Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre) by
    (unfold mu_core_indices; unfold mu_u8 in Hd, Hs; lia).
  destruct (Hsafe Hi) as [_ [_ Hspaces]].
  destruct (Hspaces ltac:(split; assumption)) as [Htype [Hright _]].
  destruct (PreH29 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Hslot Hty] Hcontent] Hri].
  rewrite Hty in Htype.
  unfold mu_type in Hright.
  rewrite Hty, Hri in Hright.
  first [exact Htype | apply Hright; assumption].
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_38_source_shared_pure_split_goal_2 : ucos_CNode_Mutate_partial_solve_wit_38_source_shared_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros.
  destruct PreH30 as [Hd [Hs [Hf [Hr Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre) by
    (unfold mu_core_indices; unfold mu_u8 in Hd, Hs; lia).
  destruct (Hsafe Hi) as [_ [_ Hspaces]].
  destruct (Hspaces ltac:(split; assumption)) as [Htype [Hright _]].
  destruct (PreH29 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Hslot Hty] Hcontent] Hri].
  rewrite Hty in Htype.
  unfold mu_type in Hright.
  rewrite Hty, Hri in Hright.
  first [exact Htype | apply Hright; assumption].
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_38_source_shared_pure_split_goal_3 : ucos_CNode_Mutate_partial_solve_wit_38_source_shared_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros.
  destruct PreH30 as [Hd [Hs [Hf [Hr Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre) by
    (unfold mu_core_indices; unfold mu_u8 in Hd, Hs; lia).
  destruct (Hsafe Hi) as [_ [_ Hspaces]].
  destruct (Hspaces ltac:(split; assumption)) as [Htype [Hright _]].
  destruct (PreH29 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Hslot Hty] Hcontent] Hri].
  rewrite Hty in Htype.
  unfold mu_type in Hright.
  rewrite Hty, Hri in Hright.
  first [exact Htype | apply Hright; assumption].
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_38_source_shared_pure : ucos_CNode_Mutate_partial_solve_wit_38_source_shared_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_38_source_shared_pure_split_goal_1.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_38_source_shared_pure_split_goal_2.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_38_source_shared_pure_split_goal_3.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_39_source_shared_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_39_source_shared_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros.
  destruct PreH29 as [Hd [Hs [Hf [Hr Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre) by
    (unfold mu_core_indices; unfold mu_u8 in Hd, Hs; lia).
  destruct (Hsafe Hi) as [_ [_ Hspaces]].
  destruct (Hspaces ltac:(split; assumption)) as [Htype [Hright _]].
  destruct (PreH28 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Hslot Hty] Hcontent] Hri].
  rewrite Hty in Htype.
  unfold mu_type in Hright.
  rewrite Hty, Hri in Hright.
  first [exact Htype | apply Hright; assumption].
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_39_source_shared_pure_split_goal_2 : ucos_CNode_Mutate_partial_solve_wit_39_source_shared_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros.
  destruct PreH29 as [Hd [Hs [Hf [Hr Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre) by
    (unfold mu_core_indices; unfold mu_u8 in Hd, Hs; lia).
  destruct (Hsafe Hi) as [_ [_ Hspaces]].
  destruct (Hspaces ltac:(split; assumption)) as [Htype [Hright _]].
  destruct (PreH28 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Hslot Hty] Hcontent] Hri].
  rewrite Hty in Htype.
  unfold mu_type in Hright.
  rewrite Hty, Hri in Hright.
  first [exact Htype | apply Hright; assumption].
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_39_source_shared_pure_split_goal_3 : ucos_CNode_Mutate_partial_solve_wit_39_source_shared_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros.
  destruct PreH29 as [Hd [Hs [Hf [Hr Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre) by
    (unfold mu_core_indices; unfold mu_u8 in Hd, Hs; lia).
  destruct (Hsafe Hi) as [_ [_ Hspaces]].
  destruct (Hspaces ltac:(split; assumption)) as [Htype [Hright _]].
  destruct (PreH28 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Hslot Hty] Hcontent] Hri].
  rewrite Hty in Htype.
  unfold mu_type in Hright.
  rewrite Hty, Hri in Hright.
  first [exact Htype | apply Hright; assumption].
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_39_source_shared_pure : ucos_CNode_Mutate_partial_solve_wit_39_source_shared_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_39_source_shared_pure_split_goal_1.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_39_source_shared_pure_split_goal_2.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_39_source_shared_pure_split_goal_3.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_40_source_distinct_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_40_source_distinct_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros.
  destruct PreH32 as [Hd [Hs [Hf [Hr Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre) by
    (unfold mu_core_indices; unfold mu_u8 in Hd, Hs; lia).
  destruct (Hsafe Hi) as [_ [_ Hspaces]].
  destruct (Hspaces ltac:(split; assumption)) as [Htype [Hright _]].
  destruct (PreH31 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Hslot Hty] Hcontent] Hri].
  rewrite Hty in Htype.
  unfold mu_type in Hright.
  rewrite Hty, Hri in Hright.
  first [exact Htype | apply Hright; assumption].
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_40_source_distinct_pure_split_goal_2 : ucos_CNode_Mutate_partial_solve_wit_40_source_distinct_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros.
  destruct PreH32 as [Hd [Hs [Hf [Hr Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre) by
    (unfold mu_core_indices; unfold mu_u8 in Hd, Hs; lia).
  destruct (Hsafe Hi) as [_ [_ Hspaces]].
  destruct (Hspaces ltac:(split; assumption)) as [Htype [Hright _]].
  destruct (PreH31 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Hslot Hty] Hcontent] Hri].
  rewrite Hty in Htype.
  unfold mu_type in Hright.
  rewrite Hty, Hri in Hright.
  first [exact Htype | apply Hright; assumption].
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_40_source_distinct_pure_split_goal_3 : ucos_CNode_Mutate_partial_solve_wit_40_source_distinct_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros.
  destruct PreH32 as [Hd [Hs [Hf [Hr Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre) by
    (unfold mu_core_indices; unfold mu_u8 in Hd, Hs; lia).
  destruct (Hsafe Hi) as [_ [_ Hspaces]].
  destruct (Hspaces ltac:(split; assumption)) as [Htype [Hright _]].
  destruct (PreH31 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Hslot Hty] Hcontent] Hri].
  rewrite Hty in Htype.
  unfold mu_type in Hright.
  rewrite Hty, Hri in Hright.
  first [exact Htype | apply Hright; assumption].
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_40_source_distinct_pure : ucos_CNode_Mutate_partial_solve_wit_40_source_distinct_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_40_source_distinct_pure_split_goal_1.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_40_source_distinct_pure_split_goal_2.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_40_source_distinct_pure_split_goal_3.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_41_source_distinct_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_41_source_distinct_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros.
  destruct PreH31 as [Hd [Hs [Hf [Hr Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre) by
    (unfold mu_core_indices; unfold mu_u8 in Hd, Hs; lia).
  destruct (Hsafe Hi) as [_ [_ Hspaces]].
  destruct (Hspaces ltac:(split; assumption)) as [Htype [Hright _]].
  destruct (PreH30 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Hslot Hty] Hcontent] Hri].
  rewrite Hty in Htype.
  unfold mu_type in Hright.
  rewrite Hty, Hri in Hright.
  first [exact Htype | apply Hright; assumption].
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_41_source_distinct_pure_split_goal_2 : ucos_CNode_Mutate_partial_solve_wit_41_source_distinct_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros.
  destruct PreH31 as [Hd [Hs [Hf [Hr Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre) by
    (unfold mu_core_indices; unfold mu_u8 in Hd, Hs; lia).
  destruct (Hsafe Hi) as [_ [_ Hspaces]].
  destruct (Hspaces ltac:(split; assumption)) as [Htype [Hright _]].
  destruct (PreH30 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Hslot Hty] Hcontent] Hri].
  rewrite Hty in Htype.
  unfold mu_type in Hright.
  rewrite Hty, Hri in Hright.
  first [exact Htype | apply Hright; assumption].
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_41_source_distinct_pure_split_goal_3 : ucos_CNode_Mutate_partial_solve_wit_41_source_distinct_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros.
  destruct PreH31 as [Hd [Hs [Hf [Hr Hsafe]]]].
  assert (Hi : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre) by
    (unfold mu_core_indices; unfold mu_u8 in Hd, Hs; lia).
  destruct (Hsafe Hi) as [_ [_ Hspaces]].
  destruct (Hspaces ltac:(split; assumption)) as [Htype [Hright _]].
  destruct (PreH30 (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as [[[Hslot Hty] Hcontent] Hri].
  rewrite Hty in Htype.
  unfold mu_type in Hright.
  rewrite Hty, Hri in Hright.
  first [exact Htype | apply Hright; assumption].
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_41_source_distinct_pure : ucos_CNode_Mutate_partial_solve_wit_41_source_distinct_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_41_source_distinct_pure_split_goal_1.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_41_source_distinct_pure_split_goal_2.
  - Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_41_source_distinct_pure_split_goal_3.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_42_copy_shared_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_42_copy_shared_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat apply mu_writable_set__source_slot_safety.
  match goal with H : forall p f, _ -> _ |- _ =>
    pose proof (H (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as Hsrc;
    pose proof (H (mu_space before destTask_Prio_pre) func_capability_pre ltac:(lia)) as Hdst
  end.
  destruct Hsrc as [[[Hss Hst] Hsc] Hsr].
  destruct Hdst as [[[Hds Hdt] Hdc] Hdr].
  rewrite <- Hss, <- Hst, <- Hsr, <- Hdt, <- Hdr in *.
  fold mu_type mu_right in *.
  match goal with H : mu_core_safe _ _ _ _ _ |- _ =>
    unfold mu_core_safe in H; destruct H as [Hd [Hs [Hf [Hr Hsafe]]]]
  end.
  assert (Hidx : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre) by
    (unfold mu_core_indices, mu_u8 in *; lia).
  specialize (Hsafe Hidx).
  destruct Hsafe as [_ [_ Hsafe]].
  specialize (Hsafe ltac:(split; assumption)).
  destruct Hsafe as [_ [_ Hsafe]].
  apply Hsafe.
  unfold mu_core_success, mu_strict_subrights.
  repeat split; try tauto; try (unfold mu_core_indices in Hidx; lia).
  all: try (unfold mu_type, mu_right in *; congruence).
  all: apply mu_mask_guard__source_slot_safety; [exact Hr|].
  all: unfold mu_type, mu_right in *; congruence.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_42_copy_shared_pure : ucos_CNode_Mutate_partial_solve_wit_42_copy_shared_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_42_copy_shared_pure_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_43_copy_distinct_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_43_copy_distinct_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat apply mu_writable_set__source_slot_safety.
  match goal with H : forall p f, _ -> _ |- _ =>
    pose proof (H (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as Hsrc;
    pose proof (H (mu_space before destTask_Prio_pre) func_capability_pre ltac:(lia)) as Hdst
  end.
  destruct Hsrc as [[[Hss Hst] Hsc] Hsr].
  destruct Hdst as [[[Hds Hdt] Hdc] Hdr].
  rewrite <- Hss, <- Hst, <- Hsr, <- Hdt, <- Hdr in *.
  fold mu_type mu_right in *.
  match goal with H : mu_core_safe _ _ _ _ _ |- _ =>
    unfold mu_core_safe in H; destruct H as [Hd [Hs [Hf [Hr Hsafe]]]]
  end.
  assert (Hidx : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre) by
    (unfold mu_core_indices, mu_u8 in *; lia).
  specialize (Hsafe Hidx).
  destruct Hsafe as [_ [_ Hsafe]].
  specialize (Hsafe ltac:(split; assumption)).
  destruct Hsafe as [_ [_ Hsafe]].
  apply Hsafe.
  unfold mu_core_success, mu_strict_subrights.
  repeat split; try tauto; try (unfold mu_core_indices in Hidx; lia).
  all: try (unfold mu_type, mu_right in *; congruence).
  all: apply mu_mask_guard__source_slot_safety; [exact Hr|].
  all: unfold mu_type, mu_right in *; congruence.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_43_copy_distinct_pure : ucos_CNode_Mutate_partial_solve_wit_43_copy_distinct_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_43_copy_distinct_pure_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_44_copy_shared_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_44_copy_shared_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat apply mu_writable_set__source_slot_safety.
  match goal with H : forall p f, _ -> _ |- _ =>
    pose proof (H (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as Hsrc;
    pose proof (H (mu_space before destTask_Prio_pre) func_capability_pre ltac:(lia)) as Hdst
  end.
  destruct Hsrc as [[[Hss Hst] Hsc] Hsr].
  destruct Hdst as [[[Hds Hdt] Hdc] Hdr].
  rewrite <- Hss, <- Hst, <- Hsr, <- Hdt, <- Hdr in *.
  fold mu_type mu_right in *.
  match goal with H : mu_core_safe _ _ _ _ _ |- _ =>
    unfold mu_core_safe in H; destruct H as [Hd [Hs [Hf [Hr Hsafe]]]]
  end.
  assert (Hidx : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre) by
    (unfold mu_core_indices, mu_u8 in *; lia).
  specialize (Hsafe Hidx).
  destruct Hsafe as [_ [_ Hsafe]].
  specialize (Hsafe ltac:(split; assumption)).
  destruct Hsafe as [_ [_ Hsafe]].
  apply Hsafe.
  unfold mu_core_success, mu_strict_subrights.
  repeat split; try tauto; try (unfold mu_core_indices in Hidx; lia).
  all: try (unfold mu_type, mu_right in *; congruence).
  all: apply mu_mask_guard__source_slot_safety; [exact Hr|].
  all: unfold mu_type, mu_right in *; congruence.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_44_copy_shared_pure : ucos_CNode_Mutate_partial_solve_wit_44_copy_shared_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_44_copy_shared_pure_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_45_copy_distinct_pure_split_goal_1 : ucos_CNode_Mutate_partial_solve_wit_45_copy_distinct_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat apply mu_writable_set__source_slot_safety.
  match goal with H : forall p f, _ -> _ |- _ =>
    pose proof (H (mu_space before srcTask_Prio_pre) func_capability_pre ltac:(lia)) as Hsrc;
    pose proof (H (mu_space before destTask_Prio_pre) func_capability_pre ltac:(lia)) as Hdst
  end.
  destruct Hsrc as [[[Hss Hst] Hsc] Hsr].
  destruct Hdst as [[[Hds Hdt] Hdc] Hdr].
  rewrite <- Hss, <- Hst, <- Hsr, <- Hdt, <- Hdr in *.
  fold mu_type mu_right in *.
  match goal with H : mu_core_safe _ _ _ _ _ |- _ =>
    unfold mu_core_safe in H; destruct H as [Hd [Hs [Hf [Hr Hsafe]]]]
  end.
  assert (Hidx : mu_core_indices destTask_Prio_pre srcTask_Prio_pre func_capability_pre) by
    (unfold mu_core_indices, mu_u8 in *; lia).
  specialize (Hsafe Hidx).
  destruct Hsafe as [_ [_ Hsafe]].
  specialize (Hsafe ltac:(split; assumption)).
  destruct Hsafe as [_ [_ Hsafe]].
  apply Hsafe.
  unfold mu_core_success, mu_strict_subrights.
  repeat split; try tauto; try (unfold mu_core_indices in Hidx; lia).
  all: try (unfold mu_type, mu_right in *; congruence).
  all: apply mu_mask_guard__source_slot_safety; [exact Hr|].
  all: unfold mu_type, mu_right in *; congruence.
Qed.

Lemma proof_of_ucos_CNode_Mutate_partial_solve_wit_45_copy_distinct_pure : ucos_CNode_Mutate_partial_solve_wit_45_copy_distinct_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_partial_solve_wit_45_copy_distinct_pure_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_1_split_goal_spatial : ucos_CNode_Mutate_which_implies_wit_1_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 match goal with
 | Hd : mu_distinct ?h, Hr : mu_readable ?h MUptr ?a |- _ =>
   exact (proj1 (mu_ptr_lens__pointer_lenses h a Hd Hr))
 end.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_1 : ucos_CNode_Mutate_which_implies_wit_1.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_2_split_goal_spatial : ucos_CNode_Mutate_which_implies_wit_2_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 match goal with
 | Hd : mu_distinct ?h, Hr : mu_readable ?h MUptr ?a |- _ =>
   exact (proj2 (mu_ptr_lens__pointer_lenses h a Hd Hr))
 end.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_2 : ucos_CNode_Mutate_which_implies_wit_2.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_3_split_goal_spatial : ucos_CNode_Mutate_which_implies_wit_3_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 match goal with
 | Hd : mu_distinct ?h, Hr : mu_readable ?h MUptr ?a |- _ =>
   exact (proj1 (mu_ptr_lens__pointer_lenses h a Hd Hr))
 end.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_3 : ucos_CNode_Mutate_which_implies_wit_3.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_4_split_goal_spatial : ucos_CNode_Mutate_which_implies_wit_4_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 match goal with
 | Hd : mu_distinct ?h, Hr : mu_readable ?h MUptr ?a |- _ =>
   exact (proj2 (mu_ptr_lens__pointer_lenses h a Hd Hr))
 end.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_4 : ucos_CNode_Mutate_which_implies_wit_4.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_4_split_goal_spatial.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_5 : ucos_CNode_Mutate_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H: mu_readable ?h MUword ?a,
    C: mu_value ?h MUword ?a = 1 -> mu_readable ?h MUword ?b |- _ =>
    destruct (Z.eq_dec (mu_value h MUword a) 1) as [V|V];
    [destruct (Z.eq_dec a b) as [E|E]|]
  end.
  - Left. Right.
    match goal with H: mu_readable ?h MUword ?a |- _ =>
      pose proof (proj1 (mu_word_lens__source_word_lenses h a ltac:(assumption) H)) as M
    end.
    rewrite V in M.
    split_pure_spatial; [exact M|]. split_pures; dump_pre_spatial; auto.
  - Left. Left.
    match goal with H: mu_readable ?h MUword ?a,
      C: mu_value ?h MUword ?a = 1 -> mu_readable ?h MUword ?b |- _ =>
      pose proof (proj1 (mu_two_word_lens__source_word_lenses h a b ltac:(assumption) H (C V) E)) as M
    end.
    rewrite V in M.
    split_pure_spatial; [exact M|]. split_pures; dump_pre_spatial; auto.
  - Right.
    match goal with H: mu_readable ?h MUword ?a |- _ =>
      pose proof (proj1 (mu_word_lens__source_word_lenses h a ltac:(assumption) H)) as M
    end.
    split_pure_spatial; [exact M|]. split_pures; dump_pre_spatial; auto.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_6_split_goal_spatial : ucos_CNode_Mutate_which_implies_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H: mu_readable ?h MUword ?a |- _ =>
    pose proof (proj2 (mu_word_lens__source_word_lenses h a ltac:(assumption) H)) as M
  end.
  try match goal with H: mu_value _ MUword _ = 1 |- _ => rewrite H in M end.
  exact M.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_6 : ucos_CNode_Mutate_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_6_split_goal_spatial.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_7_split_goal_spatial : ucos_CNode_Mutate_which_implies_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H: mu_readable ?h MUword ?a,
    C: mu_value ?h MUword ?a = 1 -> mu_readable ?h MUword ?b,
    V: mu_value ?h MUword ?a = 1 |- _ =>
    pose proof (proj2 (mu_two_word_lens__source_word_lenses h a b ltac:(assumption) H (C V) ltac:(assumption))) as M;
    rewrite V in M
  end.
  exact M.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_7 : ucos_CNode_Mutate_which_implies_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_7_split_goal_spatial.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_8 : ucos_CNode_Mutate_which_implies_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - apply mu_word_write_extract__simple_write_lenses; assumption.
  - split_pures; dump_pre_spatial; assumption.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_9_split_goal_1 : ucos_CNode_Mutate_which_implies_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. apply mu_set_distinct__simple_write_lenses. assumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_9_split_goal_spatial : ucos_CNode_Mutate_which_implies_wit_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply mu_word_write_restore__simple_write_lenses; assumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_9 : ucos_CNode_Mutate_which_implies_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_9_split_goal_spatial.
  - Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_9_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_10 : ucos_CNode_Mutate_which_implies_wit_10.
Proof.
 LLM_pre_process ltac:(auto).
 match goal with
 | R: mu_readable ?h MUword ?a, W: mu_writable ?h MUword ?b |- _ =>
   destruct (Z.eq_dec a b) as [EQ|NE]
 end.
 - Right. split_pure_spatial.
   + apply mu_copy_read_lens__content_copy_lenses; assumption.
   + split_pures; dump_pre_spatial; auto.
 - Left. split_pure_spatial.
   + match goal with
     | D:mu_distinct ?h, R:mu_readable ?h MUword ?a, W:mu_writable ?h MUword ?b |- _ =>
       sep_apply_l_atomic (mu_copy_distinct_extract__content_copy_lenses h a b D R W NE)
     end. cancel.
   + split_pures; dump_pre_spatial; auto.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_11_split_goal_1 : ucos_CNode_Mutate_which_implies_wit_11_split_goal_1.
Proof.
 LLM_pre_process ltac:(auto).
 dump_pre_spatial. eapply mu_copy_set_distinct__content_copy_lenses; eassumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_11_split_goal_spatial : ucos_CNode_Mutate_which_implies_wit_11_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(auto).
 match goal with
 | R: mu_readable ?h MUword ?a, W: mu_writable ?h MUword ?b |- _ =>
   assert (b=a) as EQ by auto; rewrite EQ in *
 end.
 apply mu_copy_restore_lens__content_copy_lenses; auto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_11 : ucos_CNode_Mutate_which_implies_wit_11.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_11_split_goal_spatial.
 - Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_11_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_12_split_goal_1 : ucos_CNode_Mutate_which_implies_wit_12_split_goal_1.
Proof.
 LLM_pre_process ltac:(auto).
 dump_pre_spatial. eapply mu_copy_set_distinct__content_copy_lenses; eassumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_12_split_goal_spatial : ucos_CNode_Mutate_which_implies_wit_12_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(auto).
 match goal with
 | D:mu_distinct ?h, R:mu_readable ?h MUword ?a, W:mu_writable ?h MUword ?b |- _ =>
   assert (a<>b) as N by auto;
   sep_apply_l_atomic (mu_copy_distinct_restore__content_copy_lenses h a b (mu_value h MUword a) D R W N)
 end. cancel.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_12 : ucos_CNode_Mutate_which_implies_wit_12.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_12_split_goal_spatial.
 - Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_12_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_13 : ucos_CNode_Mutate_which_implies_wit_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - apply mu_word_write_extract__simple_write_lenses; assumption.
  - split_pures; dump_pre_spatial; assumption.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_14_split_goal_1 : ucos_CNode_Mutate_which_implies_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. apply mu_set_distinct__simple_write_lenses. assumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_14_split_goal_spatial : ucos_CNode_Mutate_which_implies_wit_14_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply mu_word_write_restore__simple_write_lenses; assumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_14 : ucos_CNode_Mutate_which_implies_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_14_split_goal_spatial.
  - Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_14_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_15_split_goal_spatial : ucos_CNode_Mutate_which_implies_wit_15_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply mu_clear_read_lens__right_clear_lenses; assumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_15 : ucos_CNode_Mutate_which_implies_wit_15.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_15_split_goal_spatial.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_16_split_goal_1 : ucos_CNode_Mutate_which_implies_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. apply mu_clear_distinct__right_clear_lenses. assumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_16_split_goal_spatial : ucos_CNode_Mutate_which_implies_wit_16_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply mu_clear_write_restore__right_clear_lenses; assumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_16 : ucos_CNode_Mutate_which_implies_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_16_split_goal_spatial.
  - Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_16_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_17_split_goal_spatial : ucos_CNode_Mutate_which_implies_wit_17_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H: mu_readable ?h MUword ?a |- _ =>
    pose proof (proj2 (mu_word_lens__source_word_lenses h a ltac:(assumption) H)) as M
  end.
  try match goal with H: mu_value _ MUword _ = 1 |- _ => rewrite H in M end.
  exact M.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_17 : ucos_CNode_Mutate_which_implies_wit_17.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_17_split_goal_spatial.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_18_split_goal_spatial : ucos_CNode_Mutate_which_implies_wit_18_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H: mu_readable ?h MUword ?a |- _ =>
    pose proof (proj2 (mu_word_lens__source_word_lenses h a ltac:(assumption) H)) as M
  end.
  try match goal with H: mu_value _ MUword _ = 1 |- _ => rewrite H in M end.
  exact M.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_18 : ucos_CNode_Mutate_which_implies_wit_18.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_18_split_goal_spatial.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_19_split_goal_spatial : ucos_CNode_Mutate_which_implies_wit_19_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H: mu_readable ?h MUword ?a,
    C: mu_value ?h MUword ?a = 1 -> mu_readable ?h MUword ?b,
    V: mu_value ?h MUword ?a = 1 |- _ =>
    pose proof (proj2 (mu_two_word_lens__source_word_lenses h a b ltac:(assumption) H (C V) ltac:(assumption))) as M;
    rewrite V in M
  end.
  exact M.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_19 : ucos_CNode_Mutate_which_implies_wit_19.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_19_split_goal_spatial.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_20 : ucos_CNode_Mutate_which_implies_wit_20.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - apply mu_word_write_extract__simple_write_lenses; assumption.
  - split_pures; dump_pre_spatial; assumption.
Qed. 

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_21_split_goal_1 : ucos_CNode_Mutate_which_implies_wit_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. apply mu_set_distinct__simple_write_lenses. assumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_21_split_goal_spatial : ucos_CNode_Mutate_which_implies_wit_21_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply mu_word_write_restore__simple_write_lenses; assumption.
Qed.

Lemma proof_of_ucos_CNode_Mutate_which_implies_wit_21 : ucos_CNode_Mutate_which_implies_wit_21.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_21_split_goal_spatial.
  - Goal_apply proof_of_ucos_CNode_Mutate_which_implies_wit_21_split_goal_1.
Qed. 

Lemma proof_of_user_cnode_mutate_return_wit_1_guard_present_split_goal_1 : user_cnode_mutate_return_wit_1_guard_present_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH4.
  destruct PreH28 as [Hd [Hs Hsafe]].
  unfold mu_u8 in Hd, Hs.
  rewrite unsigned_last_nbits_eq in PreH20 by (cbn; lia).
  rewrite unsigned_last_nbits_eq in PreH21 by (cbn; lia).
  assert (Hi : mu_user_indices destTask_Prio_pre srcTask_Prio_pre) by (unfold mu_user_indices; lia).
  assert (Ha : mu_authorized before destTask_Prio_pre srcTask_Prio_pre).
  { unfold mu_authorized; split.
    - unfold mu_right. rewrite (proj2 (PreH27 (mu_current_space before) 11 ltac:(lia))). exact PreH5.
    - unfold mu_parent_addr. change (mu_pb before + destTask_Prio_pre) with (mu_parent_base (mu_layout_of before) + destTask_Prio_pre).
      change (mu_parent_base (mu_layout_of before)) with (mu_pb before).
      rewrite PreH24. replace destTask_Prio_pre with (destTask_Prio_pre * sizeof(UCHAR)) by (cbn; lia). exact PreH4. }
  unfold mu_user_result. right; right; right.
  split; [exact Hi|]. split; [exact PreH10|]. split; [exact Ha|].
  destruct PreH2 as [[Hsucc [Hr Hstate]] | [Hfail [Hr Hstate]]]; subst retval.
  - exfalso. apply PreH1. reflexivity.
  - unfold mu_core_result. right. auto.
Qed.

Lemma proof_of_user_cnode_mutate_return_wit_1_guard_present : user_cnode_mutate_return_wit_1_guard_present.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_user_cnode_mutate_return_wit_1_guard_present_split_goal_1.
Qed. 

Lemma proof_of_user_cnode_mutate_return_wit_2_guard_present_split_goal_1 : user_cnode_mutate_return_wit_2_guard_present_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH4.
  destruct PreH28 as [Hd [Hs Hsafe]].
  unfold mu_u8 in Hd, Hs.
  rewrite unsigned_last_nbits_eq in PreH20 by (cbn; lia).
  rewrite unsigned_last_nbits_eq in PreH21 by (cbn; lia).
  assert (Hi : mu_user_indices destTask_Prio_pre srcTask_Prio_pre) by (unfold mu_user_indices; lia).
  assert (Ha : mu_authorized before destTask_Prio_pre srcTask_Prio_pre).
  { unfold mu_authorized; split.
    - unfold mu_right. rewrite (proj2 (PreH27 (mu_current_space before) 11 ltac:(lia))). exact PreH5.
    - unfold mu_parent_addr. change (mu_pb before + destTask_Prio_pre) with (mu_parent_base (mu_layout_of before) + destTask_Prio_pre).
      change (mu_parent_base (mu_layout_of before)) with (mu_pb before).
      rewrite PreH24. replace destTask_Prio_pre with (destTask_Prio_pre * sizeof(UCHAR)) by (cbn; lia). exact PreH4. }
  unfold mu_user_result. right; right; right.
  split; [exact Hi|]. split; [exact PreH10|]. split; [exact Ha|].
  destruct PreH2 as [[Hsucc [Hr Hstate]] | [Hfail [Hr Hstate]]]; subst retval.
  - unfold mu_core_result. left. auto.
  - vm_compute in PreH1. discriminate.
Qed.

Lemma proof_of_user_cnode_mutate_return_wit_2_guard_present : user_cnode_mutate_return_wit_2_guard_present.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_user_cnode_mutate_return_wit_2_guard_present_split_goal_1.
Qed. 

Lemma proof_of_user_cnode_mutate_return_wit_3_guard_absent_split_goal_1 : user_cnode_mutate_return_wit_3_guard_absent_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || nia || int_auto).
destruct PreH25 as [Hd [Hs Hsafe]].
unfold mu_u8 in Hd, Hs.
assert (Ed : unsigned_last_nbits destTask_Prio_pre 32 = destTask_Prio_pre) by (unfold unsigned_last_nbits; apply Z.mod_small; lia).
assert (Es : unsigned_last_nbits srcTask_Prio_pre 32 = srcTask_Prio_pre) by (unfold unsigned_last_nbits; apply Z.mod_small; lia).
try rewrite Ed in *; try rewrite Es in *.
unfold mu_user_result.
right; right; left.
split; [unfold mu_user_indices; lia | ].
split; [assumption | ].
split; [ | split; reflexivity].
unfold mu_authorized.
intros [Hguard Hparent].
unfold mu_right in Hguard.
pose proof (proj2 (PreH24 (mu_current_space before) 11 ltac:(lia))) as Eright.
rewrite Eright in Hguard. contradiction.
Qed.

Lemma proof_of_user_cnode_mutate_return_wit_3_guard_absent : user_cnode_mutate_return_wit_3_guard_absent.
Proof.
aggressive_pre_process.
Goal_apply proof_of_user_cnode_mutate_return_wit_3_guard_absent_split_goal_1.
Qed. 

Lemma proof_of_user_cnode_mutate_return_wit_4_guard_present_split_goal_1 : user_cnode_mutate_return_wit_4_guard_present_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || nia || int_auto).
destruct PreH26 as [Hd [Hs Hsafe]].
unfold mu_u8 in Hd, Hs.
assert (Ed : unsigned_last_nbits destTask_Prio_pre 32 = destTask_Prio_pre) by (unfold unsigned_last_nbits; apply Z.mod_small; lia).
assert (Es : unsigned_last_nbits srcTask_Prio_pre 32 = srcTask_Prio_pre) by (unfold unsigned_last_nbits; apply Z.mod_small; lia).
try rewrite Ed in *; try rewrite Es in *.
unfold mu_user_result.
right; right; left.
split; [unfold mu_user_indices; lia | ].
split; [assumption | ].
split; [ | split; reflexivity].
unfold mu_authorized.
intros [Hguard Hparent].
unfold mu_parent_addr in Hparent.
change (mu_value before MUbyte (mu_pb before + destTask_Prio_pre) = srcTask_Prio_pre) in Hparent.
rewrite PreH22 in Hparent.
change (mu_value before MUbyte (&( "CapParent") + destTask_Prio_pre * 1) <> srcTask_Prio_pre) in PreH2.
rewrite Z.mul_1_r in PreH2. contradiction.
Qed.

Lemma proof_of_user_cnode_mutate_return_wit_4_guard_present : user_cnode_mutate_return_wit_4_guard_present.
Proof.
aggressive_pre_process.
Goal_apply proof_of_user_cnode_mutate_return_wit_4_guard_present_split_goal_1.
Qed. 

Lemma proof_of_user_cnode_mutate_return_wit_5_split_goal_1 : user_cnode_mutate_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH19 as [Hd [Hs Hsafe]].
  unfold mu_u8 in Hd, Hs.
  rewrite unsigned_last_nbits_eq in PreH11 by (cbn; lia).
  rewrite unsigned_last_nbits_eq in PreH12 by (cbn; lia).
  unfold mu_user_result. right; left.
  split; [unfold mu_user_indices; lia|]. auto.
Qed.

Lemma proof_of_user_cnode_mutate_return_wit_5 : user_cnode_mutate_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_user_cnode_mutate_return_wit_5_split_goal_1.
Qed. 

Lemma proof_of_user_cnode_mutate_return_wit_6_split_goal_1 : user_cnode_mutate_return_wit_6_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || nia || int_auto).
destruct PreH8 as [Hd [Hs Hsafe]].
unfold mu_u8 in Hd, Hs.
assert (Ed : unsigned_last_nbits destTask_Prio_pre 32 = destTask_Prio_pre) by (unfold unsigned_last_nbits; apply Z.mod_small; lia).
assert (Es : unsigned_last_nbits srcTask_Prio_pre 32 = srcTask_Prio_pre) by (unfold unsigned_last_nbits; apply Z.mod_small; lia).
try rewrite Ed in *; try rewrite Es in *.
unfold mu_user_result.
left. split; [unfold mu_user_indices; lia | split; reflexivity].
Qed.

Lemma proof_of_user_cnode_mutate_return_wit_6 : user_cnode_mutate_return_wit_6.
Proof.
aggressive_pre_process.
Goal_apply proof_of_user_cnode_mutate_return_wit_6_split_goal_1.
Qed. 

Lemma proof_of_user_cnode_mutate_return_wit_7_split_goal_1 : user_cnode_mutate_return_wit_7_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || nia || int_auto).
destruct PreH9 as [Hd [Hs Hsafe]].
unfold mu_u8 in Hd, Hs.
assert (Ed : unsigned_last_nbits destTask_Prio_pre 32 = destTask_Prio_pre) by (unfold unsigned_last_nbits; apply Z.mod_small; lia).
assert (Es : unsigned_last_nbits srcTask_Prio_pre 32 = srcTask_Prio_pre) by (unfold unsigned_last_nbits; apply Z.mod_small; lia).
try rewrite Ed in *; try rewrite Es in *.
unfold mu_user_result.
left. split; [unfold mu_user_indices; lia | split; reflexivity].
Qed.

Lemma proof_of_user_cnode_mutate_return_wit_7 : user_cnode_mutate_return_wit_7.
Proof.
aggressive_pre_process.
Goal_apply proof_of_user_cnode_mutate_return_wit_7_split_goal_1.
Qed. 

Lemma proof_of_user_cnode_mutate_partial_solve_wit_2_pure_split_goal_1 : user_cnode_mutate_partial_solve_wit_2_pure_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 destruct PreH13 as [Hd [Hs [Hf [Hr Hsafe]]]].
 unfold mu_u8 in Hd, Hs.
 assert (Hi : mu_user_indices destTask_Prio_pre srcTask_Prio_pre).
 { unfold mu_user_indices. unfold unsigned_last_nbits in PreH5, PreH6.
   rewrite Z.mod_small in PreH5 by (change (0 <= destTask_Prio_pre < 4294967296); lia).
   rewrite Z.mod_small in PreH6 by (change (0 <= srcTask_Prio_pre < 4294967296); lia). lia. }
 specialize (Hsafe Hi). rewrite <- PreH10. tauto.
Qed.

Lemma proof_of_user_cnode_mutate_partial_solve_wit_2_pure : user_cnode_mutate_partial_solve_wit_2_pure.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_user_cnode_mutate_partial_solve_wit_2_pure_split_goal_1.
Qed. 

Lemma proof_of_user_cnode_mutate_partial_solve_wit_3_pure_split_goal_1 : user_cnode_mutate_partial_solve_wit_3_pure_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 apply mu_filter_distinct__wrapper_entry_safety. assumption.
Qed.

Lemma proof_of_user_cnode_mutate_partial_solve_wit_3_pure_split_goal_2 : user_cnode_mutate_partial_solve_wit_3_pure_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 destruct PreH15 as [Hd [Hs [Hf [Hr Hsafe]]]].
 unfold mu_u8 in Hd, Hs.
 assert (Hi : mu_user_indices destTask_Prio_pre srcTask_Prio_pre).
 { unfold mu_user_indices. unfold unsigned_last_nbits in PreH7, PreH8.
   rewrite Z.mod_small in PreH7 by (change (0 <= destTask_Prio_pre < 4294967296); lia).
   rewrite Z.mod_small in PreH8 by (change (0 <= srcTask_Prio_pre < 4294967296); lia). lia. }
 specialize (Hsafe Hi).
 destruct Hsafe as [Hg [Hnz [Hb Hrest]]].
 unfold mu_current_tcb in Hb. rewrite PreH12, PreH13 in Hb.
 unfold mu_readable in *. rewrite mu_remove_ptr_byte__wrapper_entry_safety. exact Hb.
Qed.

Lemma proof_of_user_cnode_mutate_partial_solve_wit_3_pure : user_cnode_mutate_partial_solve_wit_3_pure.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_user_cnode_mutate_partial_solve_wit_3_pure_split_goal_1.
 Goal_apply proof_of_user_cnode_mutate_partial_solve_wit_3_pure_split_goal_2.
Qed. 

Lemma proof_of_user_cnode_mutate_partial_solve_wit_4_pure_split_goal_1 : user_cnode_mutate_partial_solve_wit_4_pure_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold mu_current_prio, mu_current_tcb.
 rewrite PreH14, PreH15. unfold mu_value.
 rewrite mu_remove_ptr_byte__wrapper_entry_safety. reflexivity.
Qed.

Lemma proof_of_user_cnode_mutate_partial_solve_wit_4_pure_split_goal_2 : user_cnode_mutate_partial_solve_wit_4_pure_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold mu_current_prio, mu_current_tcb.
 rewrite PreH14, PreH15. unfold mu_value.
 rewrite mu_remove_ptr_byte__wrapper_entry_safety. reflexivity.
Qed.

Lemma proof_of_user_cnode_mutate_partial_solve_wit_4_pure : user_cnode_mutate_partial_solve_wit_4_pure.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_user_cnode_mutate_partial_solve_wit_4_pure_split_goal_1.
 Goal_apply proof_of_user_cnode_mutate_partial_solve_wit_4_pure_split_goal_2.
Qed. 

Lemma proof_of_user_cnode_mutate_partial_solve_wit_6_pure_split_goal_1 : user_cnode_mutate_partial_solve_wit_6_pure_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 destruct PreH19 as [Hd [Hs [Hf [Hr Hsafe]]]].
 unfold mu_u8 in Hd, Hs.
 assert (Hi : mu_user_indices destTask_Prio_pre srcTask_Prio_pre).
 { unfold mu_user_indices. unfold unsigned_last_nbits in PreH11, PreH12.
   rewrite Z.mod_small in PreH11 by (change (0 <= destTask_Prio_pre < 4294967296); lia).
   rewrite Z.mod_small in PreH12 by (change (0 <= srcTask_Prio_pre < 4294967296); lia). lia. }
 specialize (Hsafe Hi).
 destruct Hsafe as [Hg [Hnz [Hb [Hrange [Ht Hrest]]]]].
 unfold mu_table_addr in Ht. unfold mu_tb in PreH14. rewrite PreH14 in Ht. exact Ht.
Qed.

Lemma proof_of_user_cnode_mutate_partial_solve_wit_6_pure : user_cnode_mutate_partial_solve_wit_6_pure.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_user_cnode_mutate_partial_solve_wit_6_pure_split_goal_1.
Qed. 

Lemma proof_of_user_cnode_mutate_partial_solve_wit_7_pure_split_goal_1 : user_cnode_mutate_partial_solve_wit_7_pure_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold mu_current_space, mu_space, mu_table_addr.
 unfold mu_tb in PreH16. rewrite PreH16. reflexivity.
Qed.

Lemma proof_of_user_cnode_mutate_partial_solve_wit_7_pure_split_goal_2 : user_cnode_mutate_partial_solve_wit_7_pure_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold mu_current_space, mu_space, mu_table_addr.
 unfold mu_tb in PreH16. rewrite PreH16. reflexivity.
Qed.

Lemma proof_of_user_cnode_mutate_partial_solve_wit_7_pure : user_cnode_mutate_partial_solve_wit_7_pure.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_user_cnode_mutate_partial_solve_wit_7_pure_split_goal_1.
 Goal_apply proof_of_user_cnode_mutate_partial_solve_wit_7_pure_split_goal_2.
Qed. 

Lemma proof_of_user_cnode_mutate_partial_solve_wit_9_pure_split_goal_1 : user_cnode_mutate_partial_solve_wit_9_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct PreH23 as [Hd [Hs [Hf [Hr Hsafe]]]].
  unfold mu_u8 in Hd, Hs.
  change (destTask_Prio_pre mod 4294967296 < 63) in PreH15.
  change (srcTask_Prio_pre mod 4294967296 < 63) in PreH16.
  rewrite Z.mod_small in PreH15 by lia.
  rewrite Z.mod_small in PreH16 by lia.
  assert (Hi : mu_user_indices destTask_Prio_pre srcTask_Prio_pre) by (unfold mu_user_indices; lia).
  destruct (Hsafe Hi) as [_ [_ [_ [_ [_ HH]]]]].
  destruct (HH PreH5) as [Hword [Hbyte Hcore]].
  destruct (PreH22 (mu_current_space before) 11 ltac:(lia)) as [_ Hright].
  rewrite <- Hright. exact Hword.
Qed.

Lemma proof_of_user_cnode_mutate_partial_solve_wit_9_pure_split_goal_2 : user_cnode_mutate_partial_solve_wit_9_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct PreH23 as [Hd [Hs [Hf [Hr Hsafe]]]].
  unfold mu_u8 in Hd, Hs.
  change (destTask_Prio_pre mod 4294967296 < 63) in PreH15.
  change (srcTask_Prio_pre mod 4294967296 < 63) in PreH16.
  rewrite Z.mod_small in PreH15 by lia.
  rewrite Z.mod_small in PreH16 by lia.
  assert (Hi : mu_user_indices destTask_Prio_pre srcTask_Prio_pre) by (unfold mu_user_indices; lia).
  destruct (Hsafe Hi) as [_ [_ [_ [_ [_ HH]]]]].
  destruct (HH PreH5) as [Hword [Hbyte Hcore]].
  destruct (PreH22 (mu_current_space before) 11 ltac:(lia)) as [_ Hright].
  rewrite <- Hright. fold (mu_right before (mu_current_space before) 11).
  assert (Ep : mu_parent_addr before destTask_Prio_pre = &( "CapParent" ) + destTask_Prio_pre * sizeof(UCHAR)).
  { unfold mu_parent_addr. change (mu_pb before + destTask_Prio_pre = &( "CapParent" ) + destTask_Prio_pre * sizeof(UCHAR)). rewrite PreH19. simpl. lia. }
  rewrite <- Ep. intro Hg. split; [exact (Hbyte Hg)|].
  eapply mu_readable_kind_address_distinct__wrapper_call_safety; eauto; discriminate.
Qed.

Lemma proof_of_user_cnode_mutate_partial_solve_wit_9_pure : user_cnode_mutate_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_user_cnode_mutate_partial_solve_wit_9_pure_split_goal_1.
  Goal_apply proof_of_user_cnode_mutate_partial_solve_wit_9_pure_split_goal_2.
Qed. 

Lemma proof_of_user_cnode_mutate_partial_solve_wit_15_guard_present_pure_split_goal_1 : user_cnode_mutate_partial_solve_wit_15_guard_present_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct PreH30 as [Hd [Hs [Hf [Hr Hsafe]]]].
  unfold mu_u8 in Hd, Hs.
  change (destTask_Prio_pre mod 4294967296 < 63) in PreH22.
  change (srcTask_Prio_pre mod 4294967296 < 63) in PreH23.
  rewrite Z.mod_small in PreH22 by lia.
  rewrite Z.mod_small in PreH23 by lia.
  assert (Hi : mu_user_indices destTask_Prio_pre srcTask_Prio_pre) by (unfold mu_user_indices; lia).
  destruct (Hsafe Hi) as [_ [_ [_ [_ [_ HH]]]]].
  destruct (HH PreH12) as [Hword [Hbyte Hcore]].
  destruct (PreH29 (mu_current_space before) 11 ltac:(lia)) as [_ Hright].
  apply Hcore. unfold mu_authorized, mu_right. rewrite Hright. split; [exact PreH7|].
  unfold mu_parent_addr. change (mu_value before MUbyte (mu_pb before + destTask_Prio_pre) = srcTask_Prio_pre).
  rewrite PreH26. simpl in PreH6. rewrite Z.mul_1_r in PreH6. exact PreH6.
Qed.

Lemma proof_of_user_cnode_mutate_partial_solve_wit_15_guard_present_pure_split_goal_2 : user_cnode_mutate_partial_solve_wit_15_guard_present_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct PreH30 as [Hd [Hs [Hf [Hr Hsafe]]]].
  unfold mu_u8 in Hd, Hs.
  change (destTask_Prio_pre mod 4294967296 < 63) in PreH22.
  change (srcTask_Prio_pre mod 4294967296 < 63) in PreH23.
  rewrite Z.mod_small in PreH22 by lia.
  rewrite Z.mod_small in PreH23 by lia.
  assert (Hi : mu_user_indices destTask_Prio_pre srcTask_Prio_pre) by (unfold mu_user_indices; lia).
  destruct (Hsafe Hi) as [_ [_ [_ [_ [_ HH]]]]].
  destruct (HH PreH12) as [Hword [Hbyte Hcore]].
  destruct (PreH29 (mu_current_space before) 11 ltac:(lia)) as [_ Hright].
  apply Hcore. unfold mu_authorized, mu_right. rewrite Hright. split; [exact PreH7|].
  unfold mu_parent_addr. change (mu_value before MUbyte (mu_pb before + destTask_Prio_pre) = srcTask_Prio_pre).
  rewrite PreH26. simpl in PreH6. rewrite Z.mul_1_r in PreH6. exact PreH6.
Qed.

Lemma proof_of_user_cnode_mutate_partial_solve_wit_15_guard_present_pure_split_goal_3 : user_cnode_mutate_partial_solve_wit_15_guard_present_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_user_cnode_mutate_partial_solve_wit_15_guard_present_pure_split_goal_4 : user_cnode_mutate_partial_solve_wit_15_guard_present_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_user_cnode_mutate_partial_solve_wit_15_guard_present_pure : user_cnode_mutate_partial_solve_wit_15_guard_present_pure.
Proof. aggressive_pre_process.
  - Goal_apply (mu_entail_reassociate__wrapper_call_safety _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mutate_partial_solve_wit_15_guard_present_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre before PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)).
  - Goal_apply (mu_entail_reassociate__wrapper_call_safety _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mutate_partial_solve_wit_15_guard_present_pure_split_goal_2 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre before PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)).
  - Goal_apply (mu_entail_reassociate__wrapper_call_safety _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mutate_partial_solve_wit_15_guard_present_pure_split_goal_3 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre before PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)).
  - Goal_apply (mu_entail_reassociate__wrapper_call_safety _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mutate_partial_solve_wit_15_guard_present_pure_split_goal_4 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre before PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)).
Qed. 

Lemma proof_of_user_cnode_mutate_which_implies_wit_1_split_goal_spatial : user_cnode_mutate_which_implies_wit_1_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 match goal with
 | Hd : mu_distinct ?h, Hr : mu_readable ?h MUptr ?a |- _ =>
   exact (proj1 (mu_ptr_lens__pointer_lenses h a Hd Hr))
 end.
Qed.

Lemma proof_of_user_cnode_mutate_which_implies_wit_1 : user_cnode_mutate_which_implies_wit_1.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_user_cnode_mutate_which_implies_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_user_cnode_mutate_which_implies_wit_2_split_goal_spatial : user_cnode_mutate_which_implies_wit_2_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(auto).
 match goal with Hd : mu_distinct ?h, Hr : mu_readable ?h MUbyte ?a |- _ => exact (proj1 (mu_byte_lens__byte_lenses h a Hd Hr)) end.
Qed.

Lemma proof_of_user_cnode_mutate_which_implies_wit_2 : user_cnode_mutate_which_implies_wit_2.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_user_cnode_mutate_which_implies_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_user_cnode_mutate_which_implies_wit_3_split_goal_spatial : user_cnode_mutate_which_implies_wit_3_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(auto).
 match goal with Hd : mu_distinct ?h, Hr : mu_readable ?h MUbyte ?a |- _ => exact (proj2 (mu_byte_lens__byte_lenses h a Hd Hr)) end.
Qed.

Lemma proof_of_user_cnode_mutate_which_implies_wit_3 : user_cnode_mutate_which_implies_wit_3.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_user_cnode_mutate_which_implies_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_user_cnode_mutate_which_implies_wit_4_split_goal_spatial : user_cnode_mutate_which_implies_wit_4_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 match goal with
 | Hd : mu_distinct ?h, Hr : mu_readable ?h MUptr ?a |- _ =>
   exact (proj2 (mu_ptr_lens__pointer_lenses h a Hd Hr))
 end.
Qed.

Lemma proof_of_user_cnode_mutate_which_implies_wit_4 : user_cnode_mutate_which_implies_wit_4.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_user_cnode_mutate_which_implies_wit_4_split_goal_spatial.
Qed. 

Lemma proof_of_user_cnode_mutate_which_implies_wit_5_split_goal_spatial : user_cnode_mutate_which_implies_wit_5_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 match goal with
 | Hd : mu_distinct ?h, Hr : mu_readable ?h MUptr ?a |- _ =>
   exact (proj1 (mu_ptr_lens__pointer_lenses h a Hd Hr))
 end.
Qed.

Lemma proof_of_user_cnode_mutate_which_implies_wit_5 : user_cnode_mutate_which_implies_wit_5.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_user_cnode_mutate_which_implies_wit_5_split_goal_spatial.
Qed. 

Lemma proof_of_user_cnode_mutate_which_implies_wit_6_split_goal_spatial : user_cnode_mutate_which_implies_wit_6_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 match goal with
 | Hd : mu_distinct ?h, Hr : mu_readable ?h MUptr ?a |- _ =>
   exact (proj2 (mu_ptr_lens__pointer_lenses h a Hd Hr))
 end.
Qed.

Lemma proof_of_user_cnode_mutate_which_implies_wit_6 : user_cnode_mutate_which_implies_wit_6.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_user_cnode_mutate_which_implies_wit_6_split_goal_spatial.
Qed. 

Lemma proof_of_user_cnode_mutate_which_implies_wit_7 : user_cnode_mutate_which_implies_wit_7.
Proof.
 LLM_pre_process ltac:(lia).
 match goal with
 | R : mu_readable ?h MUword ?a |- _ =>
   destruct (Z.eq_dec (Z.land (mu_value h MUword a) 8) 0) as [Hz|Hn]
 end.
 - Right. split_pure_spatial.
   + match goal with H : mu_distinct ?h, R : mu_readable ?h MUword ?a |- _ =>
       exact (proj1 (mu_guard_lens__wrapper_guard_lenses h MUword a H R)) end.
   + split_pures; dump_pre_spatial; auto.
 - Left. split_pure_spatial.
   + match goal with H : mu_distinct ?h, R : mu_readable ?h MUword ?a,
       C : _ -> mu_readable ?h MUbyte ?b /\ _ |- _ =>
       exact (proj1 (mu_guard_pair_lens__wrapper_guard_lenses h a b H R (proj1 (C Hn)))) end.
   + split_pures; dump_pre_spatial; auto.
Qed. 

Lemma proof_of_user_cnode_mutate_which_implies_wit_8_split_goal_spatial : user_cnode_mutate_which_implies_wit_8_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia).
 match goal with
 | H : mu_distinct ?h, R : mu_readable ?h MUword ?a |- _ =>
   exact (proj2 (mu_guard_lens__wrapper_guard_lenses h MUword a H R))
 end.
Qed.

Lemma proof_of_user_cnode_mutate_which_implies_wit_8 : user_cnode_mutate_which_implies_wit_8.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_user_cnode_mutate_which_implies_wit_8_split_goal_spatial.
Qed. 

Lemma proof_of_user_cnode_mutate_which_implies_wit_9_split_goal_spatial : user_cnode_mutate_which_implies_wit_9_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia).
 match goal with
 | H : mu_distinct ?h, R : mu_readable ?h MUword ?a,
   C : _ -> mu_readable ?h MUbyte ?b /\ _, N : Z.land _ 8 <> 0 |- _ =>
   exact (proj2 (mu_guard_pair_lens__wrapper_guard_lenses h a b H R (proj1 (C N))))
 end.
Qed.

Lemma proof_of_user_cnode_mutate_which_implies_wit_9 : user_cnode_mutate_which_implies_wit_9.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_user_cnode_mutate_which_implies_wit_9_split_goal_spatial.
Qed. 

Lemma proof_of_user_cnode_mutate_which_implies_wit_10_split_goal_spatial : user_cnode_mutate_which_implies_wit_10_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia).
 match goal with
 | H : mu_distinct ?h, R : mu_readable ?h MUword ?a,
   C : _ -> mu_readable ?h MUbyte ?b /\ _, N : Z.land _ 8 <> 0 |- _ =>
   exact (proj2 (mu_guard_pair_lens__wrapper_guard_lenses h a b H R (proj1 (C N))))
 end.
Qed.

Lemma proof_of_user_cnode_mutate_which_implies_wit_10 : user_cnode_mutate_which_implies_wit_10.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_user_cnode_mutate_which_implies_wit_10_split_goal_spatial.
Qed. 


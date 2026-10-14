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
From SimpleC.EE.osverify_qcp.cases Require Import user_cnode_mint_inferred_20260923_goal.
From SimpleC.EE.osverify_qcp.cases Require Import user_cnode_mint_inferred_20260923_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.osverify_qcp.cases.user_cnode_mint_inferred_20260923_lib.
Local Open Scope sac.

Lemma proof_of_ucos_CNode_Mint_entail_wit_1_1_split_goal_1 : ucos_CNode_Mint_entail_wit_1_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mint_core_pre _ _ _ _ _ _ |- _ =>
    destruct H as [WF [D [S [F [R Access]]]]] end.
  unfold mint_u8 in D, S.
  unfold unsigned_last_nbits in *.
  repeat match goal with H : context [?x mod 2^32] |- _ =>
    rewrite (Z.mod_small x (2^32)) in H by lia end.
  match goal with H : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as [LD [LS [DT [DC [DR [ST [SC SR]]]]]]] end.
  unfold mint_dst, mint_src in *.
  rewrite LD, LS in *.
  unfold mint_eligible, mint_parameters_valid, mint_dst, mint_src, mint_proper_rights.
  rewrite LD, LS, ST, SR.
  unfold mint_u32 in R.
  repeat split; try assumption; try lia; try congruence.
  rewrite <- mask32__core_rights_transition by (cbn; lia).
  congruence.
Qed.

Lemma proof_of_ucos_CNode_Mint_entail_wit_1_1_split_goal_spatial : ucos_CNode_Mint_entail_wit_1_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : mint_core_pre _ _ _ _ _ _ |- _ =>
    destruct H as [WF [D [S [F [R Access]]]]] end.
  unfold mint_u8 in D, S.
  unfold unsigned_last_nbits in *.
  repeat match goal with H : context [?x mod 2^32] |- _ =>
    rewrite (Z.mod_small x (2^32)) in H by lia end.
  match goal with H : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as [LD [LS [DT [DC [DR [ST [SC SR]]]]]]] end.
  unfold mint_dst, mint_src in *.
  rewrite LD, LS in *.
  unfold mint_core_access in Access.
  unfold mint_dst, mint_src in Access.
  rewrite LD, LS, ST, SR in Access.
  match type of Access with mint_parameters_valid ?d ?s ?f -> _ =>
    assert (HP : mint_parameters_valid d s f) by (unfold mint_parameters_valid; lia) end.
  destruct (Access HP) as [_ [_ A]].
  specialize (A ltac:(split; assumption)).
  destruct A as [RT [RR _]].
  specialize (RR ltac:(assumption)).
  match type of RT with mint_readable ?h 0 ?a =>
    match type of RR with mint_readable _ 0 ?b =>
      pose proof (read_two__core_rights_transition h a b WF RT RR ltac:(assumption)) as G
    end
  end.
  sep_apply_l_atomic G.
  cancel.
Qed.

Lemma proof_of_ucos_CNode_Mint_entail_wit_1_1 : ucos_CNode_Mint_entail_wit_1_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mint_entail_wit_1_1_split_goal_spatial.
  - Goal_apply (associate__core_rights_transition _ _ _ _ (proof_of_ucos_CNode_Mint_entail_wit_1_1_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)).
Qed. 

Lemma proof_of_ucos_CNode_Mint_entail_wit_1_2_split_goal_1 : ucos_CNode_Mint_entail_wit_1_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mint_core_pre _ _ _ _ _ _ |- _ =>
    destruct H as [WF [D [S [F [R Access]]]]] end.
  unfold mint_u8 in D, S.
  unfold unsigned_last_nbits in *.
  repeat match goal with H : context [?x mod 2^32] |- _ =>
    rewrite (Z.mod_small x (2^32)) in H by lia end.
  match goal with H : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as [LD [LS [DT [DC [DR [ST [SC SR]]]]]]] end.
  unfold mint_dst, mint_src in *.
  rewrite LD, LS in *.
  unfold mint_eligible, mint_parameters_valid, mint_dst, mint_src, mint_proper_rights.
  rewrite LD, LS, ST, SR.
  unfold mint_u32 in R.
  repeat split; try assumption; try lia; try congruence.
  rewrite <- mask32__core_rights_transition by (cbn; lia).
  congruence.
Qed.

Lemma proof_of_ucos_CNode_Mint_entail_wit_1_2_split_goal_spatial : ucos_CNode_Mint_entail_wit_1_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : mint_core_pre _ _ _ _ _ _ |- _ =>
    destruct H as [WF [D [S [F [R Access]]]]] end.
  unfold mint_u8 in D, S.
  unfold unsigned_last_nbits in *.
  repeat match goal with H : context [?x mod 2^32] |- _ =>
    rewrite (Z.mod_small x (2^32)) in H by lia end.
  match goal with H : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as [LD [LS [DT [DC [DR [ST [SC SR]]]]]]] end.
  unfold mint_dst, mint_src in *.
  rewrite LD, LS in *.
  unfold mint_core_access in Access.
  unfold mint_dst, mint_src in Access.
  rewrite LD, LS, ST, SR in Access.
  match type of Access with mint_parameters_valid ?d ?s ?f -> _ =>
    assert (HP : mint_parameters_valid d s f) by (unfold mint_parameters_valid; lia) end.
  destruct (Access HP) as [_ [_ A]].
  specialize (A ltac:(split; assumption)).
  destruct A as [RT [RR _]].
  specialize (RR ltac:(assumption)).
  match type of RT with mint_readable ?h 0 ?a =>
    match goal with |- (store_uint ?b ?v ** _) |-- _ =>
      assert (E : b = a) by congruence; rewrite E
    end;
    pose proof (read_factor__core_rights_transition h 0 a WF RT) as G
  end.
  cbn [mint_cell_heap mint_kind mint_initial mint_address] in G.
  exact G.
Qed.

Lemma proof_of_ucos_CNode_Mint_entail_wit_1_2 : ucos_CNode_Mint_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Mint_entail_wit_1_2_split_goal_spatial.
  - Goal_apply (proof_of_ucos_CNode_Mint_entail_wit_1_2_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h).
Qed. 

Lemma proof_of_ucos_CNode_Mint_entail_wit_2_1_split_goal_spatial : ucos_CNode_Mint_entail_wit_2_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || congruence).
  match goal with
  | HP : mint_core_pre ?h ?L ?d ?s ?f ?r, HE : mint_eligible ?h ?L ?d ?s ?f ?r |- _ =>
    pose proof (access_copy__core_copy h L d s f r HP HE) as [WF [RD WR]]
  end.
  match goal with HL : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    unfold mint_core_layout in HL;
    destruct HL as [Hdt [Hst [Hdty [Hdco [Hdri [Hsty [Hsco Hsri]]]]]]]
  end.
  unfold mint_dst, mint_src in Hdty, Hdco, Hdri, Hsty, Hsco, Hsri.
  rewrite Hdt in Hdty, Hdco, Hdri. rewrite Hst in Hsty, Hsco, Hsri.
  rewrite <- Hdty, <- Hdco, <- Hsco in *.
  match goal with E : mint_sco ?L = mint_dco ?L |- _ => rewrite E in * end.
  exact (write_restore__core_copy _ 0 _ _ (proj1 WF) WR).
Qed.

Lemma proof_of_ucos_CNode_Mint_entail_wit_2_1 : ucos_CNode_Mint_entail_wit_2_1.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_ucos_CNode_Mint_entail_wit_2_1_split_goal_spatial.
Qed. 

Lemma proof_of_ucos_CNode_Mint_entail_wit_2_2_split_goal_spatial : ucos_CNode_Mint_entail_wit_2_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || congruence).
  match goal with
  | HP : mint_core_pre ?h ?L ?d ?s ?f ?r, HE : mint_eligible ?h ?L ?d ?s ?f ?r |- _ =>
    pose proof (access_copy__core_copy h L d s f r HP HE) as [WF [RD WR]]
  end.
  match goal with HL : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    unfold mint_core_layout in HL;
    destruct HL as [Hdt [Hst [Hdty [Hdco [Hdri [Hsty [Hsco Hsri]]]]]]]
  end.
  unfold mint_dst, mint_src in Hdty, Hdco, Hdri, Hsty, Hsco, Hsri.
  rewrite Hdt in Hdty, Hdco, Hdri. rewrite Hst in Hsty, Hsco, Hsri.
  rewrite <- Hdty, <- Hdco, <- Hsco in *.
  apply copy_restore__core_copy; assumption.
Qed.

Lemma proof_of_ucos_CNode_Mint_entail_wit_2_2 : ucos_CNode_Mint_entail_wit_2_2.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_ucos_CNode_Mint_entail_wit_2_2_split_goal_spatial.
Qed. 

Lemma proof_of_ucos_CNode_Mint_return_wit_1_split_goal_1 : ucos_CNode_Mint_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mint_core_layout in PreH1.
  destruct PreH1 as [Hdt [Hst [Hdty [Hdco [Hdri [Hsty [Hsco Hsri]]]]]]].
  unfold mint_dst, mint_src in Hdty, Hdco, Hdri, Hsco.
  rewrite <- Hdt, <- Hst.
  rewrite <- Hdty, <- Hdco, <- Hdri, <- Hsco.
  unfold mint_core_result. left. split; [exact PreH3|].
  split; [reflexivity|].
  apply updated_eq__core_success_result.
  destruct PreH2 as [_ [_ [_ [_ [_ Haccess]]]]].
  pose proof PreH3 as Helig.
  destruct Helig as [Hvalid [Hdst [Hsrc _]]].
  destruct (Haccess Hvalid) as [_ [_ Hsuccess]].
  destruct (Hsuccess (conj Hdst Hsrc)) as [_ [_ Hwrites]].
  destruct (Hwrites PreH3) as [_ [Hw _]]. exact Hw.
Qed.

Lemma proof_of_ucos_CNode_Mint_return_wit_1 : ucos_CNode_Mint_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mint_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mint_return_wit_2_split_goal_1 : ucos_CNode_Mint_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_ucos_CNode_Mint_return_wit_2_split_goal_spatial : ucos_CNode_Mint_return_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_ucos_CNode_Mint_return_wit_2 : ucos_CNode_Mint_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH11 as (Edt & Est & Edty & Edco & Edri & Esty & Esco & Esri).
  unfold mint_src in Esty, Esri. rewrite Est in Esty, Esri.
  rewrite <- Esty, <- Esri in *.
  rewrite <- Est in PreH5. rewrite <- Edt in PreH6.
  destruct PreH12 as (Hwf & Hd & Hs & Hf & Hr & Haccess).
  unfold mint_u8 in Hd, Hs.
  rewrite unsigned_last_nbits_eq in PreH7 by (change (0 <= srcTask_Prio_pre < 4294967296); lia).
  rewrite unsigned_last_nbits_eq in PreH8 by (change (0 <= destTask_Prio_pre < 4294967296); lia).
  assert (Hp : mint_parameters_valid destTask_Prio_pre srcTask_Prio_pre func_capability_pre).
  { unfold mint_parameters_valid. lia. }
  specialize (Haccess Hp). destruct Haccess as (_ & _ & Haccess).
  specialize (Haccess (conj PreH6 PreH5)).
  destruct Haccess as (Hty & Hri & _). specialize (Hri PreH2).
  assert (Hbad : ~ mint_eligible h L0 destTask_Prio_pre srcTask_Prio_pre func_capability_pre rights_pre).
  { unfold mint_eligible, mint_proper_rights. intro Hel.
    destruct Hel as (_ & _ & _ & _ & Heq & _).
    unfold mint_u32 in Hr.
    rewrite mask32__core_rights_results in PreH1 by (change (0 <= rights_pre < 4294967296); lia).
    congruence. }
  Exists h. split_pure_spatial.
  - apply restore_two_uint__core_rights_results; assumption.
  - split_pures. dump_pre_spatial.
    unfold mint_core_result. right. auto.
Qed. 

Lemma proof_of_ucos_CNode_Mint_return_wit_3_split_goal_1 : ucos_CNode_Mint_return_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_ucos_CNode_Mint_return_wit_3_split_goal_spatial : ucos_CNode_Mint_return_wit_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_ucos_CNode_Mint_return_wit_3 : ucos_CNode_Mint_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH11 as (Edt & Est & Edty & Edco & Edri & Esty & Esco & Esri).
  unfold mint_src in Esty, Esri. rewrite Est in Esty, Esri.
  rewrite <- Esty, <- Esri in *.
  rewrite <- Est in PreH5. rewrite <- Edt in PreH6.
  destruct PreH12 as (Hwf & Hd & Hs & Hf & Hr & Haccess).
  unfold mint_u8 in Hd, Hs.
  rewrite unsigned_last_nbits_eq in PreH7 by (change (0 <= srcTask_Prio_pre < 4294967296); lia).
  rewrite unsigned_last_nbits_eq in PreH8 by (change (0 <= destTask_Prio_pre < 4294967296); lia).
  assert (Hp : mint_parameters_valid destTask_Prio_pre srcTask_Prio_pre func_capability_pre).
  { unfold mint_parameters_valid. lia. }
  specialize (Haccess Hp). destruct Haccess as (_ & _ & Haccess).
  specialize (Haccess (conj PreH6 PreH5)).
  destruct Haccess as (Hty & Hri & _). specialize (Hri PreH2).
  assert (Hbad : ~ mint_eligible h L0 destTask_Prio_pre srcTask_Prio_pre func_capability_pre rights_pre).
  { unfold mint_eligible, mint_proper_rights. intro Hel.
    destruct Hel as (_ & _ & _ & _ & Heq & _).
    unfold mint_u32 in Hr.
    rewrite mask32__core_rights_results in PreH1 by (change (0 <= rights_pre < 4294967296); lia).
    congruence. }
  Exists h. split_pure_spatial.
  - rewrite <- PreH4. apply restore_uint__core_rights_results; assumption.
  - split_pures. dump_pre_spatial.
    unfold mint_core_result. right. auto.
Qed. 

Lemma proof_of_ucos_CNode_Mint_return_wit_4_split_goal_1 : ucos_CNode_Mint_return_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_ucos_CNode_Mint_return_wit_4_split_goal_spatial : ucos_CNode_Mint_return_wit_4_split_goal_spatial.
Proof. Abort.

Lemma proof_of_ucos_CNode_Mint_return_wit_4 : ucos_CNode_Mint_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with
  | H : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as [Hd [Hs [Hdty [Hdco [Hdri [Hsty [Hsco Hsri]]]]]]]
  end.
  assert (READS : NoDup (map mint_address h) /\
    mint_readable h 0 (mint_sty L0) /\
    (mint_value h (mint_sty L0) = 1 -> mint_readable h 0 (mint_sri L0))).
  { eapply core_reads__core_read_results; try eassumption;
    unfold mint_dst, mint_src; rewrite ?Hd, ?Hs; assumption. }
  destruct READS as [ND [RT RR]].
  unfold mint_src in Hsty, Hsri.
  rewrite Hs in Hsty, Hsri.
  rewrite <- Hsty in *.
  try rewrite <- Hsri in *.
  Exists h.
  split_pure_spatial.
  - exact (restore_read__core_read_results h 0 (mint_sty L0) ND RT).
  - dump_pre_spatial.
    unfold mint_core_result, mint_eligible, mint_proper_rights.
    right; repeat split; try reflexivity; intuition congruence.
Qed. 

Lemma proof_of_ucos_CNode_Mint_return_wit_5_split_goal_1 : ucos_CNode_Mint_return_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_ucos_CNode_Mint_return_wit_5_split_goal_spatial : ucos_CNode_Mint_return_wit_5_split_goal_spatial.
Proof. Abort.

Lemma proof_of_ucos_CNode_Mint_return_wit_5 : ucos_CNode_Mint_return_wit_5.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with
  | H : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as [Hd [Hs [Hdty [Hdco [Hdri [Hsty [Hsco Hsri]]]]]]]
  end.
  assert (READS : NoDup (map mint_address h) /\
    mint_readable h 0 (mint_sty L0) /\
    (mint_value h (mint_sty L0) = 1 -> mint_readable h 0 (mint_sri L0))).
  { eapply core_reads__core_read_results; try eassumption;
    unfold mint_dst, mint_src; rewrite ?Hd, ?Hs; assumption. }
  destruct READS as [ND [RT RR]].
  unfold mint_src in Hsty, Hsri.
  rewrite Hs in Hsty, Hsri.
  rewrite <- Hsty in *.
  try rewrite <- Hsri in *.
  Exists h.
  split_pure_spatial.
  - apply restore_two__core_read_results; auto.
  - dump_pre_spatial.
    unfold mint_core_result, mint_eligible, mint_proper_rights.
    right; repeat split; try reflexivity; intuition congruence.
Qed. 

Lemma proof_of_ucos_CNode_Mint_return_wit_6_split_goal_1 : ucos_CNode_Mint_return_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_ucos_CNode_Mint_return_wit_6_split_goal_spatial : ucos_CNode_Mint_return_wit_6_split_goal_spatial.
Proof. Abort.

Lemma proof_of_ucos_CNode_Mint_return_wit_6 : ucos_CNode_Mint_return_wit_6.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with
  | H : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as [Hd [Hs [Hdty [Hdco [Hdri [Hsty [Hsco Hsri]]]]]]]
  end.
  assert (READS : NoDup (map mint_address h) /\
    mint_readable h 0 (mint_sty L0) /\
    (mint_value h (mint_sty L0) = 1 -> mint_readable h 0 (mint_sri L0))).
  { eapply core_reads__core_read_results; try eassumption;
    unfold mint_dst, mint_src; rewrite ?Hd, ?Hs; assumption. }
  destruct READS as [ND [RT RR]].
  unfold mint_src in Hsty, Hsri.
  rewrite Hs in Hsty, Hsri.
  rewrite <- Hsty in *.
  try rewrite <- Hsri in *.
  Exists h.
  split_pure_spatial.
  - match goal with H : mint_sty L0 = mint_sri L0 |- _ => rewrite <- H end.
    exact (restore_read__core_read_results h 0 (mint_sty L0) ND RT).
  - dump_pre_spatial.
    unfold mint_core_result, mint_eligible, mint_proper_rights.
    right; repeat split; try reflexivity; intuition congruence.
Qed. 

Lemma proof_of_ucos_CNode_Mint_return_wit_7_split_goal_1 : ucos_CNode_Mint_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mint_core_result. right. split.
  - unfold mint_eligible, mint_dst, mint_src.
    unfold mint_core_layout in PreH6.
    destruct PreH6 as [Hd [Hs Hrest]].
    rewrite Hd, Hs. intuition congruence.
  - split; reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mint_return_wit_7 : ucos_CNode_Mint_return_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mint_return_wit_7_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mint_return_wit_8_split_goal_1 : ucos_CNode_Mint_return_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mint_core_result. right. split.
  - unfold mint_eligible, mint_dst, mint_src.
    unfold mint_core_layout in PreH7.
    destruct PreH7 as [Hd [Hs Hrest]].
    rewrite Hd, Hs. intuition congruence.
  - split; reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mint_return_wit_8 : ucos_CNode_Mint_return_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mint_return_wit_8_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mint_return_wit_9_split_goal_1 : ucos_CNode_Mint_return_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mint_core_result. right. split.
  - unfold mint_eligible, mint_parameters_valid.
    unfold mint_core_pre, mint_u8 in PreH5.
    destruct PreH5 as [_ [Hd [Hs Hrest]]].
    assert (unsigned_last_nbits destTask_Prio_pre 32 = destTask_Prio_pre) as Hu.
    { unfold unsigned_last_nbits. apply Z.mod_small. lia. }
    rewrite Hu in PreH1. intuition lia.
  - split; reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mint_return_wit_9 : ucos_CNode_Mint_return_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mint_return_wit_9_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mint_return_wit_10_split_goal_1 : ucos_CNode_Mint_return_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mint_core_result. right. split.
  - unfold mint_eligible, mint_parameters_valid.
    unfold mint_core_pre, mint_u8 in PreH6.
    destruct PreH6 as [_ [Hd [Hs Hrest]]].
    assert (unsigned_last_nbits srcTask_Prio_pre 32 = srcTask_Prio_pre) as Hu.
    { unfold unsigned_last_nbits. apply Z.mod_small. lia. }
    rewrite Hu in PreH1. intuition lia.
  - split; reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mint_return_wit_10 : ucos_CNode_Mint_return_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mint_return_wit_10_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mint_return_wit_11_split_goal_1 : ucos_CNode_Mint_return_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mint_core_pre, mint_u32 in PreH3. intuition lia.
Qed.

Lemma proof_of_ucos_CNode_Mint_return_wit_11 : ucos_CNode_Mint_return_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mint_return_wit_11_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mint_return_wit_12_split_goal_1 : ucos_CNode_Mint_return_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mint_core_result. right. split.
  - unfold mint_eligible, mint_parameters_valid. intuition lia.
  - split; reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Mint_return_wit_12 : ucos_CNode_Mint_return_wit_12.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mint_return_wit_12_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_1_pure_split_goal_1 : ucos_CNode_Mint_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mint_core_pre in *. tauto.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_1_pure_split_goal_2 : ucos_CNode_Mint_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mint_core_pre, mint_u8, mint_u32 in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with H : context [unsigned_last_nbits ?x 32] |- _ =>
    rewrite (unsigned_last_nbits_eq x 32) in H by (change (0 <= x < 4294967296); lia)
  end.
  assert (Hv : mint_parameters_valid destTask_Prio_pre srcTask_Prio_pre func_capability_pre)
    by (unfold mint_parameters_valid; lia).
  match goal with H : mint_core_access _ _ _ _ _ _ |- _ => specialize (H Hv) end.
  unfold mint_core_layout in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  match goal with H : mint_dt _ = _ |- _ => rewrite <- H end.
  assumption.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_1_pure : ucos_CNode_Mint_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (mint_assoc9__core_access _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_1_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)).
  - Goal_apply (mint_assoc9__core_access _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_1_pure_split_goal_2 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)).
Qed. 

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_2_pure_split_goal_1 : ucos_CNode_Mint_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mint_core_pre in *. tauto.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_2_pure_split_goal_2 : ucos_CNode_Mint_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mint_core_pre, mint_u8, mint_u32 in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with H : context [unsigned_last_nbits ?x 32] |- _ =>
    rewrite (unsigned_last_nbits_eq x 32) in H by (change (0 <= x < 4294967296); lia)
  end.
  assert (Hv : mint_parameters_valid destTask_Prio_pre srcTask_Prio_pre func_capability_pre)
    by (unfold mint_parameters_valid; lia).
  match goal with H : mint_core_access _ _ _ _ _ _ |- _ => specialize (H Hv) end.
  unfold mint_core_layout in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  match goal with H : mint_dt _ = _ |- _ => rewrite <- H end.
  assumption.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_2_pure : ucos_CNode_Mint_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (mint_assoc10__core_access _ _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_2_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)).
  - Goal_apply (mint_assoc10__core_access _ _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_2_pure_split_goal_2 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)).
Qed. 

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_3_pure_split_goal_1 : ucos_CNode_Mint_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mint_core_pre in *. tauto.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_3_pure_split_goal_2 : ucos_CNode_Mint_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mint_core_pre, mint_u8, mint_u32 in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with H : context [unsigned_last_nbits ?x 32] |- _ =>
    rewrite (unsigned_last_nbits_eq x 32) in H by (change (0 <= x < 4294967296); lia)
  end.
  assert (Hv : mint_parameters_valid destTask_Prio_pre srcTask_Prio_pre func_capability_pre)
    by (unfold mint_parameters_valid; lia).
  match goal with H : mint_core_access _ _ _ _ _ _ |- _ => specialize (H Hv) end.
  unfold mint_core_layout in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  match goal with H : mint_st _ = _ |- _ => rewrite <- H end.
  assumption.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_3_pure : ucos_CNode_Mint_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (mint_assoc9__core_access _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_3_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)).
  - Goal_apply (mint_assoc9__core_access _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_3_pure_split_goal_2 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)).
Qed. 

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_4_pure_split_goal_1 : ucos_CNode_Mint_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mint_core_pre in *. tauto.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_4_pure_split_goal_2 : ucos_CNode_Mint_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mint_core_pre, mint_u8, mint_u32 in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with H : context [unsigned_last_nbits ?x 32] |- _ =>
    rewrite (unsigned_last_nbits_eq x 32) in H by (change (0 <= x < 4294967296); lia)
  end.
  assert (Hv : mint_parameters_valid destTask_Prio_pre srcTask_Prio_pre func_capability_pre)
    by (unfold mint_parameters_valid; lia).
  match goal with H : mint_core_access _ _ _ _ _ _ |- _ => specialize (H Hv) end.
  unfold mint_core_layout in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  match goal with H : mint_st _ = _ |- _ => rewrite <- H end.
  assumption.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_4_pure : ucos_CNode_Mint_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (mint_assoc10__core_access _ _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_4_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)).
  - Goal_apply (mint_assoc10__core_access _ _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_4_pure_split_goal_2 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)).
Qed. 

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_5_pure_split_goal_1 : ucos_CNode_Mint_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mint_core_pre in *. tauto.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_5_pure_split_goal_2 : ucos_CNode_Mint_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mint_core_pre, mint_u8, mint_u32 in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with H : context [unsigned_last_nbits ?x 32] |- _ =>
    rewrite (unsigned_last_nbits_eq x 32) in H by (change (0 <= x < 4294967296); lia)
  end.
  assert (Hv : mint_parameters_valid destTask_Prio_pre srcTask_Prio_pre func_capability_pre)
    by (unfold mint_parameters_valid; lia).
  match goal with H : mint_core_access _ _ _ _ _ _ |- _ => specialize (H Hv) end.
  unfold mint_core_layout in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  unfold mint_dst, mint_src in *.
  repeat match goal with H : mint_dt _ = _ |- _ => rewrite H in *; clear H
                      | H : mint_st _ = _ |- _ => rewrite H in *; clear H end.
  match goal with H : _ /\ _ -> _ |- _ => specialize (H (conj PreH6 PreH5)) end.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  unfold mint_source_reads.
  match goal with H : mint_sty _ = _ |- _ => rewrite <- H end.
  match goal with H : mint_sri _ = _ |- _ => rewrite <- H end.
  split; assumption.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_5_pure : ucos_CNode_Mint_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (mint_assoc9__core_access _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_5_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)).
  - Goal_apply (mint_assoc9__core_access _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_5_pure_split_goal_2 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)).
Qed. 

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_7_pure_split_goal_1 : ucos_CNode_Mint_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | HP : mint_core_pre ?h ?L ?d ?s ?f ?r,
    HE : mint_eligible ?h ?L ?d ?s ?f ?r |- _ =>
    pose proof (success_access__core_update_access h L d s f r HP HE)
      as [WF [RD [WT [WC WR]]]]
  end.
  match goal with
  | HL : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    unfold mint_core_layout in HL;
    destruct HL as [Hdt [Hst [Hdty [Hdco [Hdri [Hsty [Hsco Hsri]]]]]]]
  end.
  unfold mint_dst, mint_src in *.
  repeat rewrite <- Hdt.
  repeat rewrite <- Hst.
  repeat rewrite <- Hdty.
  repeat rewrite <- Hdco.
  repeat rewrite <- Hdri.
  repeat rewrite <- Hsco.
  eauto using set_wellformed__core_update_access, set_writable__core_update_access.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_7_pure_split_goal_2 : ucos_CNode_Mint_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | HP : mint_core_pre ?h ?L ?d ?s ?f ?r,
    HE : mint_eligible ?h ?L ?d ?s ?f ?r |- _ =>
    pose proof (success_access__core_update_access h L d s f r HP HE)
      as [WF [RD [WT [WC WR]]]]
  end.
  match goal with
  | HL : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    unfold mint_core_layout in HL;
    destruct HL as [Hdt [Hst [Hdty [Hdco [Hdri [Hsty [Hsco Hsri]]]]]]]
  end.
  unfold mint_dst, mint_src in *.
  repeat rewrite <- Hdt.
  repeat rewrite <- Hst.
  repeat rewrite <- Hdty.
  repeat rewrite <- Hdco.
  repeat rewrite <- Hdri.
  repeat rewrite <- Hsco.
  eauto using set_wellformed__core_update_access, set_writable__core_update_access.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_7_pure : ucos_CNode_Mint_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (associate9__core_update_access _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_7_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)).
  - Goal_apply (associate9__core_update_access _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_7_pure_split_goal_2 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)).
Qed. 

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_8_pure_split_goal_1 : ucos_CNode_Mint_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | HP : mint_core_pre ?h ?L ?d ?s ?f ?r,
    HE : mint_eligible ?h ?L ?d ?s ?f ?r |- _ =>
    pose proof (success_access__core_update_access h L d s f r HP HE)
      as [WF [RD [WT [WC WR]]]]
  end.
  match goal with
  | HL : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    unfold mint_core_layout in HL;
    destruct HL as [Hdt [Hst [Hdty [Hdco [Hdri [Hsty [Hsco Hsri]]]]]]]
  end.
  unfold mint_dst, mint_src in *.
  repeat rewrite <- Hdt.
  repeat rewrite <- Hst.
  repeat rewrite <- Hdty.
  repeat rewrite <- Hdco.
  repeat rewrite <- Hdri.
  repeat rewrite <- Hsco.
  eauto using set_wellformed__core_update_access, set_writable__core_update_access.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_8_pure_split_goal_2 : ucos_CNode_Mint_partial_solve_wit_8_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | HP : mint_core_pre ?h ?L ?d ?s ?f ?r,
    HE : mint_eligible ?h ?L ?d ?s ?f ?r |- _ =>
    pose proof (success_access__core_update_access h L d s f r HP HE)
      as [WF [RD [WT [WC WR]]]]
  end.
  match goal with
  | HL : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    unfold mint_core_layout in HL;
    destruct HL as [Hdt [Hst [Hdty [Hdco [Hdri [Hsty [Hsco Hsri]]]]]]]
  end.
  unfold mint_dst, mint_src in *.
  repeat rewrite <- Hdt.
  repeat rewrite <- Hst.
  repeat rewrite <- Hdty.
  repeat rewrite <- Hdco.
  repeat rewrite <- Hdri.
  repeat rewrite <- Hsco.
  eauto using set_wellformed__core_update_access, set_writable__core_update_access.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_8_pure : ucos_CNode_Mint_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (associate10__core_update_access _ _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_8_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)).
  - Goal_apply (associate10__core_update_access _ _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_8_pure_split_goal_2 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)).
Qed. 

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_9_pure_split_goal_1 : ucos_CNode_Mint_partial_solve_wit_9_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | HP : mint_core_pre ?h ?L ?d ?s ?f ?r,
    HE : mint_eligible ?h ?L ?d ?s ?f ?r |- _ =>
    pose proof (success_access__core_update_access h L d s f r HP HE)
      as [WF [RD [WT [WC WR]]]]
  end.
  match goal with
  | HL : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    unfold mint_core_layout in HL;
    destruct HL as [Hdt [Hst [Hdty [Hdco [Hdri [Hsty [Hsco Hsri]]]]]]]
  end.
  unfold mint_dst, mint_src in *.
  repeat rewrite <- Hdt.
  repeat rewrite <- Hst.
  repeat rewrite <- Hdty.
  repeat rewrite <- Hdco.
  repeat rewrite <- Hdri.
  repeat rewrite <- Hsco.
  eauto using set_wellformed__core_update_access, set_writable__core_update_access.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_9_pure_split_goal_2 : ucos_CNode_Mint_partial_solve_wit_9_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | HP : mint_core_pre ?h ?L ?d ?s ?f ?r,
    HE : mint_eligible ?h ?L ?d ?s ?f ?r |- _ =>
    pose proof (success_access__core_update_access h L d s f r HP HE)
      as [WF [RD [WT [WC WR]]]]
  end.
  match goal with
  | HL : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    unfold mint_core_layout in HL;
    destruct HL as [Hdt [Hst [Hdty [Hdco [Hdri [Hsty [Hsco Hsri]]]]]]]
  end.
  unfold mint_dst, mint_src in *.
  repeat rewrite <- Hdt.
  repeat rewrite <- Hst.
  repeat rewrite <- Hdty.
  repeat rewrite <- Hdco.
  repeat rewrite <- Hdri.
  repeat rewrite <- Hsco.
  eauto using set_wellformed__core_update_access, set_writable__core_update_access.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_9_pure_split_goal_3 : ucos_CNode_Mint_partial_solve_wit_9_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | HP : mint_core_pre ?h ?L ?d ?s ?f ?r,
    HE : mint_eligible ?h ?L ?d ?s ?f ?r |- _ =>
    pose proof (success_access__core_update_access h L d s f r HP HE)
      as [WF [RD [WT [WC WR]]]]
  end.
  match goal with
  | HL : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    unfold mint_core_layout in HL;
    destruct HL as [Hdt [Hst [Hdty [Hdco [Hdri [Hsty [Hsco Hsri]]]]]]]
  end.
  unfold mint_dst, mint_src in *.
  repeat rewrite <- Hdt.
  repeat rewrite <- Hst.
  repeat rewrite <- Hdty.
  repeat rewrite <- Hdco.
  repeat rewrite <- Hdri.
  repeat rewrite <- Hsco.
  eauto using set_wellformed__core_update_access, set_writable__core_update_access.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_9_pure : ucos_CNode_Mint_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (associate9__core_update_access _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_9_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)).
  - Goal_apply (associate9__core_update_access _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_9_pure_split_goal_2 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)).
  - Goal_apply (associate9__core_update_access _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_9_pure_split_goal_3 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)).
Qed. 

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_11_pure_split_goal_1 : ucos_CNode_Mint_partial_solve_wit_11_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | HP : mint_core_pre ?h ?L ?d ?s ?f ?r,
    HE : mint_eligible ?h ?L ?d ?s ?f ?r |- _ =>
    pose proof (success_access__core_update_access h L d s f r HP HE)
      as [WF [RD [WT [WC WR]]]]
  end.
  match goal with
  | HL : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    unfold mint_core_layout in HL;
    destruct HL as [Hdt [Hst [Hdty [Hdco [Hdri [Hsty [Hsco Hsri]]]]]]]
  end.
  unfold mint_dst, mint_src in *.
  repeat rewrite <- Hdt.
  repeat rewrite <- Hst.
  repeat rewrite <- Hdty.
  repeat rewrite <- Hdco.
  repeat rewrite <- Hdri.
  repeat rewrite <- Hsco.
  eauto using set_wellformed__core_update_access, set_writable__core_update_access.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_11_pure_split_goal_2 : ucos_CNode_Mint_partial_solve_wit_11_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | HP : mint_core_pre ?h ?L ?d ?s ?f ?r,
    HE : mint_eligible ?h ?L ?d ?s ?f ?r |- _ =>
    pose proof (success_access__core_update_access h L d s f r HP HE)
      as [WF [RD [WT [WC WR]]]]
  end.
  match goal with
  | HL : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    unfold mint_core_layout in HL;
    destruct HL as [Hdt [Hst [Hdty [Hdco [Hdri [Hsty [Hsco Hsri]]]]]]]
  end.
  unfold mint_dst, mint_src in *.
  repeat rewrite <- Hdt.
  repeat rewrite <- Hst.
  repeat rewrite <- Hdty.
  repeat rewrite <- Hdco.
  repeat rewrite <- Hdri.
  repeat rewrite <- Hsco.
  eauto using set_wellformed__core_update_access, set_writable__core_update_access.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_11_pure : ucos_CNode_Mint_partial_solve_wit_11_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (associate9__core_update_access _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_11_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)).
  - Goal_apply (associate9__core_update_access _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_11_pure_split_goal_2 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)).
Qed. 

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_12_pure_split_goal_1 : ucos_CNode_Mint_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | HP : mint_core_pre ?h ?L ?d ?s ?f ?r,
    HE : mint_eligible ?h ?L ?d ?s ?f ?r |- _ =>
    pose proof (success_access__core_update_access h L d s f r HP HE)
      as [WF [RD [WT [WC WR]]]]
  end.
  match goal with
  | HL : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    unfold mint_core_layout in HL;
    destruct HL as [Hdt [Hst [Hdty [Hdco [Hdri [Hsty [Hsco Hsri]]]]]]]
  end.
  unfold mint_dst, mint_src in *.
  repeat rewrite <- Hdt.
  repeat rewrite <- Hst.
  repeat rewrite <- Hdty.
  repeat rewrite <- Hdco.
  repeat rewrite <- Hdri.
  repeat rewrite <- Hsco.
  eauto using set_wellformed__core_update_access, set_writable__core_update_access.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_12_pure_split_goal_2 : ucos_CNode_Mint_partial_solve_wit_12_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | HP : mint_core_pre ?h ?L ?d ?s ?f ?r,
    HE : mint_eligible ?h ?L ?d ?s ?f ?r |- _ =>
    pose proof (success_access__core_update_access h L d s f r HP HE)
      as [WF [RD [WT [WC WR]]]]
  end.
  match goal with
  | HL : mint_core_layout _ _ _ _ _ _ _ _ _ |- _ =>
    unfold mint_core_layout in HL;
    destruct HL as [Hdt [Hst [Hdty [Hdco [Hdri [Hsty [Hsco Hsri]]]]]]]
  end.
  unfold mint_dst, mint_src in *.
  repeat rewrite <- Hdt.
  repeat rewrite <- Hst.
  repeat rewrite <- Hdty.
  repeat rewrite <- Hdco.
  repeat rewrite <- Hdri.
  repeat rewrite <- Hsco.
  eauto using set_wellformed__core_update_access, set_writable__core_update_access.
Qed.

Lemma proof_of_ucos_CNode_Mint_partial_solve_wit_12_pure : ucos_CNode_Mint_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (associate10__core_update_access _ _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_12_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)).
  - Goal_apply (associate10__core_update_access _ _ _ _ _ _ _ _ _ _ _ (proof_of_ucos_CNode_Mint_partial_solve_wit_12_pure_split_goal_2 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)).
Qed. 

Lemma proof_of_ucos_CNode_Mint_which_implies_wit_1_split_goal_spatial : ucos_CNode_Mint_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | Hwf : mint_wellformed ?h, Hr : mint_readable ?h 2 ?a |- _ =>
    exact (proj1 (read_factor__core_pointer_views h 2 a Hwf Hr))
  end.
Qed.

Lemma proof_of_ucos_CNode_Mint_which_implies_wit_1 : ucos_CNode_Mint_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mint_which_implies_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_ucos_CNode_Mint_which_implies_wit_2_split_goal_spatial : ucos_CNode_Mint_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | Hwf : mint_wellformed ?h, Hr : mint_readable ?h 2 ?a |- _ =>
    exact (proj2 (read_factor__core_pointer_views h 2 a Hwf Hr))
  end.
Qed.

Lemma proof_of_ucos_CNode_Mint_which_implies_wit_2 : ucos_CNode_Mint_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mint_which_implies_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_ucos_CNode_Mint_which_implies_wit_3_split_goal_spatial : ucos_CNode_Mint_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | Hwf : mint_wellformed ?h, Hr : mint_readable ?h 2 ?a |- _ =>
    exact (proj1 (read_factor__core_pointer_views h 2 a Hwf Hr))
  end.
Qed.

Lemma proof_of_ucos_CNode_Mint_which_implies_wit_3 : ucos_CNode_Mint_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mint_which_implies_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_ucos_CNode_Mint_which_implies_wit_4_split_goal_spatial : ucos_CNode_Mint_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | Hwf : mint_wellformed ?h, Hr : mint_readable ?h 2 ?a |- _ =>
    exact (proj2 (read_factor__core_pointer_views h 2 a Hwf Hr))
  end.
Qed.

Lemma proof_of_ucos_CNode_Mint_which_implies_wit_4 : ucos_CNode_Mint_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mint_which_implies_wit_4_split_goal_spatial.
Qed. 

Lemma proof_of_ucos_CNode_Mint_which_implies_wit_5 : ucos_CNode_Mint_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(lia).
  assert (forall h k a,
  mint_wellformed h -> mint_readable h k a ->
  naive_C_Rules.derivable1 (mint_heap h)
    (naive_C_Rules.sepcon
      (mint_cell_heap (mint_cell k a (Some (mint_value h a))))
      (mint_heap (mint_remove h a)))) as Factor.
  {
  intro hh; induction hh as [|c t IH]; intros k a [HN HK] [v HF].
  - discriminate HF.
  - inversion HN as [|x xs Hnot Htail]; subst.
    inversion HK as [|x xs Hkind Hkinds]; subst.
    unfold mint_find in HF; simpl in HF.
    destruct (Z.eqb (mint_address c) a) eqn:E.
    + inversion HF; subst c.
      assert (mint_value (mint_cell k a (Some v) :: t) a = v) as V.
      { unfold mint_value, mint_find; simpl. rewrite Z.eqb_refl. reflexivity. }
      rewrite V. unfold mint_remove at 1; simpl.
      rewrite Z.eqb_refl; simpl.
      change (naive_C_Rules.derivable1
        (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some v))) (mint_heap t))
        (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some v)))
          (mint_heap (mint_remove t a)))).
      rewrite remove_absent__core_source_view by exact Hnot.
      unfold naive_C_Rules.derivable1; auto.
    + assert (mint_value (c :: t) a = mint_value t a) as V.
      { unfold mint_value, mint_find; simpl. rewrite E. reflexivity. }
      rewrite V. unfold mint_remove at 1; simpl. rewrite E; simpl.
      change (naive_C_Rules.derivable1
        (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap t))
        (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some (mint_value t a))))
          (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap (mint_remove t a))))).
      pose proof (IH k a (conj Htail Hkinds) (ex_intro _ v HF)) as F.
      sep_apply_l_atomic F.
      
      cancel (mint_cell_heap c).
      cancel (mint_heap (mint_remove t a)).
      cancel (mint_cell_heap (mint_cell k a (Some (mint_value t a)))).
  }
  lazymatch type of PreH2 with
  | mint_source_reads h ?a ?b => set (ty := a) in *; set (ri := b) in *
  end.
  destruct PreH2 as [HT HR].
  pose proof (Factor h 0 ty PreH1 HT) as FT.
  cbn [mint_cell_heap mint_kind mint_address mint_initial] in FT.
  sep_apply_l_atomic FT.
  destruct (Z.eq_dec (mint_value h ty) 1) as [VT|VT].
  - destruct (Z.eq_dec ty ri) as [EA|EA].
    + Left. Right.
      split_pure_spatial.
      * cancel (store_uint ty (mint_value h ty)). cancel (mint_heap (mint_remove h ty)).
      * split_pures; dump_pre_spatial; assumption.
    + Right.
      destruct (remove_reads__core_source_view h 0 ri ty ltac:(lia) (HR VT)) as [RR RV].
      pose proof (Factor (mint_remove h ty) 0 ri (remove_wf__core_source_view h ty PreH1) RR) as FR.
      cbn [mint_cell_heap mint_kind mint_address mint_initial] in FR.
      rewrite RV in FR.
      sep_apply_l_atomic FR.
      split_pure_spatial.
      * cancel (store_uint ty (mint_value h ty)).
        cancel (store_uint ri (mint_value h ri)).
        cancel (mint_heap (mint_remove (mint_remove h ty) ri)).
      * split_pures; dump_pre_spatial; assumption.
  - Left. Left.
    split_pure_spatial.
    + cancel (store_uint ty (mint_value h ty)). cancel (mint_heap (mint_remove h ty)).
    + dump_pre_spatial. exact VT.
Qed. 

Lemma proof_of_ucos_CNode_Mint_which_implies_wit_6 : ucos_CNode_Mint_which_implies_wit_6.
Proof.
  LLM_pre_process ltac:(lia).
  apply write_factor__core_store_views; assumption.
Qed. 

Lemma proof_of_ucos_CNode_Mint_which_implies_wit_7_split_goal_spatial : ucos_CNode_Mint_which_implies_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  apply write_restore__core_store_views; assumption.
Qed.

Lemma proof_of_ucos_CNode_Mint_which_implies_wit_7 : ucos_CNode_Mint_which_implies_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mint_which_implies_wit_7_split_goal_spatial.
Qed. 

Lemma proof_of_ucos_CNode_Mint_which_implies_wit_8 : ucos_CNode_Mint_which_implies_wit_8.
Proof.
 LLM_pre_process ltac:(lia || congruence).
 match goal with R : mint_readable ?h 0 ?s, W : mint_writable ?h 0 ?d |- _ =>
   destruct (Z.eq_dec s d) as [EQ|NE]
 end.
 - Left. split_pure_spatial.
   + apply read_factor__core_copy; assumption.
   + dump_pre_spatial. exact EQ.
 - Right. split_pure_spatial.
   + apply copy_factor__core_copy; assumption.
   + dump_pre_spatial. exact NE.
Qed. 

Lemma proof_of_ucos_CNode_Mint_which_implies_wit_9 : ucos_CNode_Mint_which_implies_wit_9.
Proof.
  LLM_pre_process ltac:(lia).
  apply write_factor__core_store_views; assumption.
Qed. 

Lemma proof_of_ucos_CNode_Mint_which_implies_wit_10_split_goal_spatial : ucos_CNode_Mint_which_implies_wit_10_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  apply write_restore__core_store_views; assumption.
Qed.

Lemma proof_of_ucos_CNode_Mint_which_implies_wit_10 : ucos_CNode_Mint_which_implies_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mint_which_implies_wit_10_split_goal_spatial.
Qed. 

Lemma proof_of_user_cnode_mint_return_wit_1_split_goal_1 : user_cnode_mint_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH11 as [Hwf [Hd [Hs [Hf [Hr Haccess]]]]].
  unfold mint_u8 in Hd, Hs.
  assert (Ed : unsigned_last_nbits destTask_Prio_pre 32 = destTask_Prio_pre).
  { unfold unsigned_last_nbits. apply Z.mod_small. simpl. lia. }
  assert (Es : unsigned_last_nbits srcTask_Prio_pre 32 = srcTask_Prio_pre).
  { unfold unsigned_last_nbits. apply Z.mod_small. simpl. lia. }
  rewrite ?Ed, ?Es in *.
  destruct PreH10 as [Hcp [Hpr [Hct [Har Hpa]]]].
  unfold mint_user_result. right; right; right.
  split; [unfold mint_user_parameters_valid; lia |].
  split.
  - unfold mint_cur. rewrite Hct, Hpr, Hcp. exact PreH6.
  - split.
    + unfold mint_authorized. rewrite Har, Hpa.
      unfold mint_cur. rewrite Hct, Hpr, Hcp. split; assumption.
    + assert (Eret : retval = 5).
      { destruct PreH2 as [[He [Er Ha]] | [He [Er Ha]]]; [|exact Er].
        rewrite Er in PreH1. change (0 <> 0) in PreH1. contradiction. }
      rewrite <- Eret. exact PreH2.
Qed.

Lemma proof_of_user_cnode_mint_return_wit_1 : user_cnode_mint_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_user_cnode_mint_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_user_cnode_mint_return_wit_2_split_goal_1 : user_cnode_mint_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH11 as [Hwf [Hd [Hs [Hf [Hr Haccess]]]]].
  unfold mint_u8 in Hd, Hs.
  assert (Ed : unsigned_last_nbits destTask_Prio_pre 32 = destTask_Prio_pre).
  { unfold unsigned_last_nbits. apply Z.mod_small. simpl. lia. }
  assert (Es : unsigned_last_nbits srcTask_Prio_pre 32 = srcTask_Prio_pre).
  { unfold unsigned_last_nbits. apply Z.mod_small. simpl. lia. }
  rewrite ?Ed, ?Es in *.
  destruct PreH10 as [Hcp [Hpr [Hct [Har Hpa]]]].
  unfold mint_user_result. right; right; right.
  split; [unfold mint_user_parameters_valid; lia |].
  split.
  - unfold mint_cur. rewrite Hct, Hpr, Hcp. exact PreH6.
  - split.
    + unfold mint_authorized. rewrite Har, Hpa.
      unfold mint_cur. rewrite Hct, Hpr, Hcp. split; assumption.
    + assert (Eret : retval = 0).
      { destruct PreH2 as [[He [Er Ha]] | [He [Er Ha]]]; [exact Er|].
        rewrite Er in PreH1. change (5 = 0) in PreH1. discriminate. }
      rewrite <- Eret. exact PreH2.
Qed.

Lemma proof_of_user_cnode_mint_return_wit_2 : user_cnode_mint_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_user_cnode_mint_return_wit_2_split_goal_1.
Qed. 

Lemma proof_of_user_cnode_mint_return_wit_3_split_goal_1 : user_cnode_mint_return_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_user_cnode_mint_return_wit_3_split_goal_spatial : user_cnode_mint_return_wit_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_user_cnode_mint_return_wit_3 : user_cnode_mint_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia).
  destruct PreH8 as [WF [D [S [F [R Access]]]]].
  unfold mint_u8 in D, S.
  rewrite unsigned_last_nbits_eq in PreH4 by (simpl; lia).
  rewrite unsigned_last_nbits_eq in PreH5 by (simpl; lia).
  assert (Valid : mint_user_parameters_valid destTask_Prio_pre srcTask_Prio_pre) by (unfold mint_user_parameters_valid; lia).
  destruct PreH7 as [CP [PR [CT [AR PA]]]].
  rewrite CP in PR. rewrite PR in CT.
  assert (Cur : mint_cur h L0 <> 0) by (unfold mint_cur; rewrite CT; exact PreH3).
  unfold mint_cur in AR. rewrite CT in AR.
  rewrite <- AR in *.
  specialize (Access Valid).
  destruct Access as [RC [NC [RP [PB [RT A]]]]].
  destruct (A Cur) as [RA [ReadParent Core]].
  Exists h.
  split_pure_spatial.
  - exact (read_factor__user_auth_results h 0 (mint_ar L0) WF RA).
  - split_pures. dump_pre_spatial.
    unfold mint_user_result. right; right; left.
    split; [exact Valid|]. split; [exact Cur|].
    split; [unfold mint_authorized; tauto|]. auto.
Qed. 

Lemma proof_of_user_cnode_mint_return_wit_4_split_goal_1 : user_cnode_mint_return_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_user_cnode_mint_return_wit_4_split_goal_spatial : user_cnode_mint_return_wit_4_split_goal_spatial.
Proof. Abort.

Lemma proof_of_user_cnode_mint_return_wit_4 : user_cnode_mint_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia).
  destruct PreH9 as [WF [D [S [F [R Access]]]]].
  unfold mint_u8 in D, S.
  rewrite unsigned_last_nbits_eq in PreH5 by (simpl; lia).
  rewrite unsigned_last_nbits_eq in PreH6 by (simpl; lia).
  assert (Valid : mint_user_parameters_valid destTask_Prio_pre srcTask_Prio_pre) by (unfold mint_user_parameters_valid; lia).
  destruct PreH8 as [CP [PR [CT [AR PA]]]].
  rewrite CP in PR. rewrite PR in CT.
  assert (Cur : mint_cur h L0 <> 0) by (unfold mint_cur; rewrite CT; exact PreH4).
  unfold mint_cur in AR. rewrite CT in AR.
  rewrite <- AR in *.
  specialize (Access Valid).
  destruct Access as [RC [NC [RP [PB [RT A]]]]].
  destruct (A Cur) as [RA [ReadParent Core]].
  Exists h.
  split_pure_spatial.
  - rewrite <- PA.
    pose proof (ReadParent PreH2) as RPa.
    assert (NE : mint_pa L0 <> mint_ar L0).
    { eapply kinds_distinct__user_auth_results; [exact RPa|exact RA|lia]. }
    destruct (remove_reads__user_auth_results h 1 (mint_pa L0) (mint_ar L0) NE RPa) as [RPa2 VP].
    sep_apply_r_atomic (read_factor__user_auth_results h 0 (mint_ar L0) WF RA).
    cbn [mint_cell_heap mint_kind mint_address mint_initial].
    cancel ((mint_ar L0) # UInt |-> mint_value h (mint_ar L0)).
    rewrite <- VP.
    exact (read_factor__user_auth_results (mint_remove h (mint_ar L0)) 1 (mint_pa L0)
      (remove_wf__user_auth_results h (mint_ar L0) WF) RPa2).
  - split_pures. dump_pre_spatial.
    unfold mint_user_result. right; right; left.
    split; [exact Valid|]. split; [exact Cur|].
    split; [unfold mint_authorized; rewrite PA; tauto|]. auto.
Qed. 

Lemma proof_of_user_cnode_mint_return_wit_5_split_goal_1 : user_cnode_mint_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH6 as [Hwf [Hd [Hs [Hf [Hr Haccess]]]]].
  unfold mint_u8 in Hd, Hs.
  assert (Ed : unsigned_last_nbits destTask_Prio_pre 32 = destTask_Prio_pre).
  { unfold unsigned_last_nbits. apply Z.mod_small. simpl. lia. }
  assert (Es : unsigned_last_nbits srcTask_Prio_pre 32 = srcTask_Prio_pre).
  { unfold unsigned_last_nbits. apply Z.mod_small. simpl. lia. }
  rewrite ?Ed, ?Es in *.
  destruct PreH5 as [Hcp [Hpr [Hct [Har Hpa]]]].
  unfold mint_user_result. right; left.
  split; [unfold mint_user_parameters_valid; lia |].
  split.
  - unfold mint_cur. rewrite Hct, Hpr, Hcp. exact PreH1.
  - split; reflexivity.
Qed.

Lemma proof_of_user_cnode_mint_return_wit_5 : user_cnode_mint_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_user_cnode_mint_return_wit_5_split_goal_1.
Qed. 

Lemma proof_of_user_cnode_mint_return_wit_6_split_goal_1 : user_cnode_mint_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH4 as [Hwf [Hd [Hs [Hf [Hr Haccess]]]]].
  unfold mint_u8 in Hd, Hs.
  assert (Ed : unsigned_last_nbits destTask_Prio_pre 32 = destTask_Prio_pre).
  { unfold unsigned_last_nbits. apply Z.mod_small. simpl. lia. }
  assert (Es : unsigned_last_nbits srcTask_Prio_pre 32 = srcTask_Prio_pre).
  { unfold unsigned_last_nbits. apply Z.mod_small. simpl. lia. }
  rewrite ?Ed, ?Es in *.
  unfold mint_user_result. left.
  split; [unfold mint_user_parameters_valid; lia | split; reflexivity].
Qed.

Lemma proof_of_user_cnode_mint_return_wit_6 : user_cnode_mint_return_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_user_cnode_mint_return_wit_6_split_goal_1.
Qed. 

Lemma proof_of_user_cnode_mint_return_wit_7_split_goal_1 : user_cnode_mint_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH5 as [Hwf [Hd [Hs [Hf [Hr Haccess]]]]].
  unfold mint_u8 in Hd, Hs.
  assert (Ed : unsigned_last_nbits destTask_Prio_pre 32 = destTask_Prio_pre).
  { unfold unsigned_last_nbits. apply Z.mod_small. simpl. lia. }
  assert (Es : unsigned_last_nbits srcTask_Prio_pre 32 = srcTask_Prio_pre).
  { unfold unsigned_last_nbits. apply Z.mod_small. simpl. lia. }
  rewrite ?Ed, ?Es in *.
  unfold mint_user_result. left.
  split; [unfold mint_user_parameters_valid; lia | split; reflexivity].
Qed.

Lemma proof_of_user_cnode_mint_return_wit_7 : user_cnode_mint_return_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_user_cnode_mint_return_wit_7_split_goal_1.
Qed. 

Lemma proof_of_user_cnode_mint_partial_solve_wit_1_pure_split_goal_1 : user_cnode_mint_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct PreH9 as [Hwf [Hd [Hs [Hf [Hr Ha]]]]].
  exact Hwf.
Qed.

Lemma proof_of_user_cnode_mint_partial_solve_wit_1_pure_split_goal_2 : user_cnode_mint_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct PreH9 as [Hwf [Hd [Hs [Hf [Hr Ha]]]]].
  unfold mint_u8 in Hd, Hs.
  rewrite unsigned_last_nbits_eq in PreH5 by (change (0 <= destTask_Prio_pre < 4294967296); lia).
  rewrite unsigned_last_nbits_eq in PreH6 by (change (0 <= srcTask_Prio_pre < 4294967296); lia).
  assert (Hvalid : mint_user_parameters_valid destTask_Prio_pre srcTask_Prio_pre)
    by (unfold mint_user_parameters_valid; lia).
  specialize (Ha Hvalid).
  destruct Ha as [Hcp [Hnn [Hpr [Hprb [Hct Hrest]]]]].
  destruct PreH8 as [Ecp [Epr [Ect [Ear Epa]]]].
  rewrite <- Ecp. exact Hcp.
Qed.

Lemma proof_of_user_cnode_mint_partial_solve_wit_1_pure_split_goal_3 : user_cnode_mint_partial_solve_wit_1_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct PreH9 as [Hwf [Hd [Hs [Hf [Hr Ha]]]]].
  unfold mint_u8 in Hd, Hs.
  rewrite unsigned_last_nbits_eq in PreH5 by (change (0 <= destTask_Prio_pre < 4294967296); lia).
  rewrite unsigned_last_nbits_eq in PreH6 by (change (0 <= srcTask_Prio_pre < 4294967296); lia).
  assert (Hvalid : mint_user_parameters_valid destTask_Prio_pre srcTask_Prio_pre)
    by (unfold mint_user_parameters_valid; lia).
  specialize (Ha Hvalid).
  destruct Ha as [Hcp [Hnn [Hpr [Hprb [Hct Hrest]]]]].
  destruct PreH8 as [Ecp [Epr [Ect [Ear Epa]]]].
  rewrite <- Ecp, <- Epr. exact Hpr.
Qed.

Lemma proof_of_user_cnode_mint_partial_solve_wit_1_pure : user_cnode_mint_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (mint_assoc8__user_pointer_access _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mint_partial_solve_wit_1_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)).
  - Goal_apply (mint_assoc8__user_pointer_access _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mint_partial_solve_wit_1_pure_split_goal_2 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)).
  - Goal_apply (mint_assoc8__user_pointer_access _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mint_partial_solve_wit_1_pure_split_goal_3 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)).
Qed. 

Lemma proof_of_user_cnode_mint_partial_solve_wit_2_pure_split_goal_1 : user_cnode_mint_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct PreH9 as [Hwf [Hd [Hs [Hf [Hr Ha]]]]].
  exact Hwf.
Qed.

Lemma proof_of_user_cnode_mint_partial_solve_wit_2_pure_split_goal_2 : user_cnode_mint_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct PreH9 as [Hwf [Hd [Hs [Hf [Hr Ha]]]]].
  unfold mint_u8 in Hd, Hs.
  rewrite unsigned_last_nbits_eq in PreH5 by (change (0 <= destTask_Prio_pre < 4294967296); lia).
  rewrite unsigned_last_nbits_eq in PreH6 by (change (0 <= srcTask_Prio_pre < 4294967296); lia).
  assert (Hvalid : mint_user_parameters_valid destTask_Prio_pre srcTask_Prio_pre)
    by (unfold mint_user_parameters_valid; lia).
  specialize (Ha Hvalid).
  destruct Ha as [Hcp [Hnn [Hpr [Hprb [Hct Hrest]]]]].
  destruct PreH8 as [Ecp [Epr [Ect [Ear Epa]]]].
  rewrite <- Ecp. exact Hcp.
Qed.

Lemma proof_of_user_cnode_mint_partial_solve_wit_2_pure_split_goal_3 : user_cnode_mint_partial_solve_wit_2_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct PreH9 as [Hwf [Hd [Hs [Hf [Hr Ha]]]]].
  unfold mint_u8 in Hd, Hs.
  rewrite unsigned_last_nbits_eq in PreH5 by (change (0 <= destTask_Prio_pre < 4294967296); lia).
  rewrite unsigned_last_nbits_eq in PreH6 by (change (0 <= srcTask_Prio_pre < 4294967296); lia).
  assert (Hvalid : mint_user_parameters_valid destTask_Prio_pre srcTask_Prio_pre)
    by (unfold mint_user_parameters_valid; lia).
  specialize (Ha Hvalid).
  destruct Ha as [Hcp [Hnn [Hpr [Hprb [Hct Hrest]]]]].
  destruct PreH8 as [Ecp [Epr [Ect [Ear Epa]]]].
  rewrite <- Ecp, <- Epr. exact Hpr.
Qed.

Lemma proof_of_user_cnode_mint_partial_solve_wit_2_pure : user_cnode_mint_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (mint_assoc10__user_pointer_access _ _ _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mint_partial_solve_wit_2_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)).
  - Goal_apply (mint_assoc10__user_pointer_access _ _ _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mint_partial_solve_wit_2_pure_split_goal_2 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)).
  - Goal_apply (mint_assoc10__user_pointer_access _ _ _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mint_partial_solve_wit_2_pure_split_goal_3 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)).
Qed. 

Lemma proof_of_user_cnode_mint_partial_solve_wit_3_pure_split_goal_1 : user_cnode_mint_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct PreH9 as [Hwf [Hd [Hs [Hf [Hr Ha]]]]].
  exact Hwf.
Qed.

Lemma proof_of_user_cnode_mint_partial_solve_wit_3_pure_split_goal_2 : user_cnode_mint_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct PreH9 as [Hwf [Hd [Hs [Hf [Hr Ha]]]]].
  unfold mint_u8 in Hd, Hs.
  rewrite unsigned_last_nbits_eq in PreH5 by (change (0 <= destTask_Prio_pre < 4294967296); lia).
  rewrite unsigned_last_nbits_eq in PreH6 by (change (0 <= srcTask_Prio_pre < 4294967296); lia).
  assert (Hvalid : mint_user_parameters_valid destTask_Prio_pre srcTask_Prio_pre)
    by (unfold mint_user_parameters_valid; lia).
  specialize (Ha Hvalid).
  destruct Ha as [Hcp [Hnn [Hpr [Hprb [Hct Hrest]]]]].
  destruct PreH8 as [Ecp [Epr [Ect [Ear Epa]]]].
  rewrite <- Ecp, <- Epr, <- Ect. exact Hct.
Qed.

Lemma proof_of_user_cnode_mint_partial_solve_wit_3_pure : user_cnode_mint_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (mint_assoc8__user_pointer_access _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mint_partial_solve_wit_3_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)).
  - Goal_apply (mint_assoc8__user_pointer_access _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mint_partial_solve_wit_3_pure_split_goal_2 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)).
Qed. 

Lemma proof_of_user_cnode_mint_partial_solve_wit_4_pure_split_goal_1 : user_cnode_mint_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct PreH9 as [Hwf [Hd [Hs [Hf [Hr Ha]]]]].
  exact Hwf.
Qed.

Lemma proof_of_user_cnode_mint_partial_solve_wit_4_pure_split_goal_2 : user_cnode_mint_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct PreH9 as [Hwf [Hd [Hs [Hf [Hr Ha]]]]].
  unfold mint_u8 in Hd, Hs.
  rewrite unsigned_last_nbits_eq in PreH5 by (change (0 <= destTask_Prio_pre < 4294967296); lia).
  rewrite unsigned_last_nbits_eq in PreH6 by (change (0 <= srcTask_Prio_pre < 4294967296); lia).
  assert (Hvalid : mint_user_parameters_valid destTask_Prio_pre srcTask_Prio_pre)
    by (unfold mint_user_parameters_valid; lia).
  specialize (Ha Hvalid).
  destruct Ha as [Hcp [Hnn [Hpr [Hprb [Hct Hrest]]]]].
  destruct PreH8 as [Ecp [Epr [Ect [Ear Epa]]]].
  rewrite <- Ecp, <- Epr, <- Ect. exact Hct.
Qed.

Lemma proof_of_user_cnode_mint_partial_solve_wit_4_pure : user_cnode_mint_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (mint_assoc9__user_pointer_access _ _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mint_partial_solve_wit_4_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)).
  - Goal_apply (mint_assoc9__user_pointer_access _ _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mint_partial_solve_wit_4_pure_split_goal_2 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)).
Qed. 

Lemma proof_of_user_cnode_mint_partial_solve_wit_5_pure_split_goal_1 : user_cnode_mint_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mint_user_pre _ _ _ _ _ _ |- _ =>
    destruct H as [Hwf [Hd [Hs [Hf [Hr Ha]]]]] end.
  exact Hwf.
Qed.

Lemma proof_of_user_cnode_mint_partial_solve_wit_5_pure_split_goal_2 : user_cnode_mint_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mint_user_pre _ _ _ _ _ _ |- _ =>
    destruct H as [Hwf [Hd [Hs [Hf [Hr Ha]]]]] end.
  unfold mint_u8 in Hd, Hs.
  repeat match goal with H : unsigned_last_nbits _ 32 < 63 |- _ =>
    rewrite unsigned_last_nbits_eq in H by (cbn; lia) end.
  match goal with H : mint_user_layout _ _ _ _ _ _ |- _ =>
    destruct H as [Hcp [Hpr [Hct [Har Hpa]]]] end.
  match goal with H : mint_value _ ?addr <> 0 |- _ =>
    assert (Hcur : mint_cur h L0 = mint_value h addr)
      by (unfold mint_cur; rewrite Hct, Hpr, Hcp; reflexivity) end.
  rewrite <- Hcur in *.
  rewrite <- Har, <- Hpa in *.
  unfold mint_user_access in Ha.
  specialize (Ha ltac:(unfold mint_user_parameters_valid; lia)).
  destruct Ha as [Hcpread [Hcpnz [Hprread [Hprbound [Hctread Hguard]]]]].
  specialize (Hguard ltac:(assumption)).
  destruct Hguard as [Hread [Hparent Hcore]].
  unfold mint_auth_reads. split; assumption.
Qed.

Lemma proof_of_user_cnode_mint_partial_solve_wit_5_pure : user_cnode_mint_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (mint_assoc8__user_auth_access _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mint_partial_solve_wit_5_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)).
  - Goal_apply (mint_assoc8__user_auth_access _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mint_partial_solve_wit_5_pure_split_goal_2 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)).
Qed. 

Lemma proof_of_user_cnode_mint_partial_solve_wit_6_pure_split_goal_1 : user_cnode_mint_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mint_user_pre _ _ _ _ _ _ |- _ =>
    destruct H as [Hwf [Hd [Hs [Hf [Hr Ha]]]]] end.
  exact Hwf.
Qed.

Lemma proof_of_user_cnode_mint_partial_solve_wit_6_pure_split_goal_2 : user_cnode_mint_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mint_user_pre _ _ _ _ _ _ |- _ =>
    destruct H as [Hwf [Hd [Hs [Hf [Hr Ha]]]]] end.
  unfold mint_u8 in Hd, Hs.
  repeat match goal with H : unsigned_last_nbits _ 32 < 63 |- _ =>
    rewrite unsigned_last_nbits_eq in H by (cbn; lia) end.
  match goal with H : mint_user_layout _ _ _ _ _ _ |- _ =>
    destruct H as [Hcp [Hpr [Hct [Har Hpa]]]] end.
  match goal with H : mint_value _ ?addr <> 0 |- _ =>
    assert (Hcur : mint_cur h L0 = mint_value h addr)
      by (unfold mint_cur; rewrite Hct, Hpr, Hcp; reflexivity) end.
  rewrite <- Hcur in *.
  rewrite <- Har, <- Hpa in *.
  unfold mint_user_access in Ha.
  specialize (Ha ltac:(unfold mint_user_parameters_valid; lia)).
  destruct Ha as [Hcpread [Hcpnz [Hprread [Hprbound [Hctread Hguard]]]]].
  specialize (Hguard ltac:(assumption)).
  destruct Hguard as [Hread [Hparent Hcore]].
  solve [exact Hread | apply Hparent; assumption].
Qed.

Lemma proof_of_user_cnode_mint_partial_solve_wit_6_pure_split_goal_3 : user_cnode_mint_partial_solve_wit_6_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mint_user_pre _ _ _ _ _ _ |- _ =>
    destruct H as [Hwf [Hd [Hs [Hf [Hr Ha]]]]] end.
  unfold mint_u8 in Hd, Hs.
  repeat match goal with H : unsigned_last_nbits _ 32 < 63 |- _ =>
    rewrite unsigned_last_nbits_eq in H by (cbn; lia) end.
  match goal with H : mint_user_layout _ _ _ _ _ _ |- _ =>
    destruct H as [Hcp [Hpr [Hct [Har Hpa]]]] end.
  match goal with H : mint_value _ ?addr <> 0 |- _ =>
    assert (Hcur : mint_cur h L0 = mint_value h addr)
      by (unfold mint_cur; rewrite Hct, Hpr, Hcp; reflexivity) end.
  rewrite <- Hcur in *.
  rewrite <- Har, <- Hpa in *.
  unfold mint_user_access in Ha.
  specialize (Ha ltac:(unfold mint_user_parameters_valid; lia)).
  destruct Ha as [Hcpread [Hcpnz [Hprread [Hprbound [Hctread Hguard]]]]].
  specialize (Hguard ltac:(assumption)).
  destruct Hguard as [Hread [Hparent Hcore]].
  solve [exact Hread | apply Hparent; assumption].
Qed.

Lemma proof_of_user_cnode_mint_partial_solve_wit_6_pure : user_cnode_mint_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (mint_assoc10__user_auth_access _ _ _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mint_partial_solve_wit_6_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)).
  - Goal_apply (mint_assoc10__user_auth_access _ _ _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mint_partial_solve_wit_6_pure_split_goal_2 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)).
  - Goal_apply (mint_assoc10__user_auth_access _ _ _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mint_partial_solve_wit_6_pure_split_goal_3 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)).
Qed. 

Lemma proof_of_user_cnode_mint_partial_solve_wit_7_pure_split_goal_1 : user_cnode_mint_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : mint_user_pre _ _ _ _ _ _ |- _ =>
    destruct H as [Hwf [Hd [Hs [Hf [Hr Ha]]]]] end.
  unfold mint_u8 in Hd, Hs.
  repeat match goal with H : unsigned_last_nbits _ 32 < 63 |- _ =>
    rewrite unsigned_last_nbits_eq in H by (cbn; lia) end.
  match goal with H : mint_user_layout _ _ _ _ _ _ |- _ =>
    destruct H as [Hcp [Hpr [Hct [Har Hpa]]]] end.
  match goal with H : mint_value _ ?addr <> 0 |- _ =>
    assert (Hcur : mint_cur h L0 = mint_value h addr)
      by (unfold mint_cur; rewrite Hct, Hpr, Hcp; reflexivity) end.
  rewrite <- Hcur in *.
  rewrite <- Har, <- Hpa in *.
  unfold mint_user_access in Ha.
  specialize (Ha ltac:(unfold mint_user_parameters_valid; lia)).
  destruct Ha as [Hcpread [Hcpnz [Hprread [Hprbound [Hctread Hguard]]]]].
  specialize (Hguard ltac:(assumption)).
  destruct Hguard as [Hread [Hparent Hcore]].
  unfold mint_core_pre.
  split; [exact Hwf|].
  split; [exact Hd|].
  split; [exact Hs|].
  split; [exact Hf|].
  split; [exact Hr|].
  apply Hcore. unfold mint_authorized. split; assumption.
Qed.

Lemma proof_of_user_cnode_mint_partial_solve_wit_7_pure : user_cnode_mint_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (mint_assoc8__user_auth_access _ _ _ _ _ _ _ _ _ (proof_of_user_cnode_mint_partial_solve_wit_7_pure_split_goal_1 rights_pre func_capability_pre srcTask_Prio_pre destTask_Prio_pre L0 h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)).
Qed. 

Lemma proof_of_user_cnode_mint_which_implies_wit_1_split_goal_spatial : user_cnode_mint_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  lazymatch goal with
  | W : mint_wellformed ?h, P : mint_readable ?h 2 ?a,
    Q : mint_readable ?h 1 ?b |- _ =>
    assert (D : b <> a) by
      (exact (different_kinds__user_pointer_views h 1 2 b a ltac:(lia) Q P));
    destruct (remove_reads__user_pointer_views h 1 b a D Q) as [Q' V];
    pose proof (remove_wf__user_pointer_views h a W) as W';
    destruct (read_factor__user_pointer_views h 2 a W P) as [F B];
    destruct (read_factor__user_pointer_views (mint_remove h a) 1 b W' Q') as [F' B'];
    rewrite V in F', B';
    cbn [mint_cell_heap mint_kind mint_address mint_initial] in F, B, F', B'
  end.
  sep_apply F. sep_apply F'. cancel.
Qed.

Lemma proof_of_user_cnode_mint_which_implies_wit_1 : user_cnode_mint_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_user_cnode_mint_which_implies_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_user_cnode_mint_which_implies_wit_2_split_goal_spatial : user_cnode_mint_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  lazymatch goal with
  | W : mint_wellformed ?h, P : mint_readable ?h 2 ?a,
    Q : mint_readable ?h 1 ?b |- _ =>
    assert (D : b <> a) by
      (exact (different_kinds__user_pointer_views h 1 2 b a ltac:(lia) Q P));
    destruct (remove_reads__user_pointer_views h 1 b a D Q) as [Q' V];
    pose proof (remove_wf__user_pointer_views h a W) as W';
    destruct (read_factor__user_pointer_views h 2 a W P) as [F B];
    destruct (read_factor__user_pointer_views (mint_remove h a) 1 b W' Q') as [F' B'];
    rewrite V in F', B';
    cbn [mint_cell_heap mint_kind mint_address mint_initial] in F, B, F', B'
  end.
  sep_apply B'. sep_apply B. cancel.
Qed.

Lemma proof_of_user_cnode_mint_which_implies_wit_2 : user_cnode_mint_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_user_cnode_mint_which_implies_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_user_cnode_mint_which_implies_wit_3_split_goal_spatial : user_cnode_mint_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  lazymatch goal with
  | W : mint_wellformed ?h, P : mint_readable ?h 2 ?a |- _ =>
    pose proof (proj1 (read_factor__user_pointer_views h 2 a W P)) as F;
    cbn [mint_cell_heap mint_kind mint_address mint_initial] in F;
    exact F
  end.
Qed.

Lemma proof_of_user_cnode_mint_which_implies_wit_3 : user_cnode_mint_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_user_cnode_mint_which_implies_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_user_cnode_mint_which_implies_wit_4_split_goal_spatial : user_cnode_mint_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  lazymatch goal with
  | W : mint_wellformed ?h, P : mint_readable ?h 2 ?a |- _ =>
    pose proof (proj2 (read_factor__user_pointer_views h 2 a W P)) as F;
    cbn [mint_cell_heap mint_kind mint_address mint_initial] in F;
    exact F
  end.
Qed.

Lemma proof_of_user_cnode_mint_which_implies_wit_4 : user_cnode_mint_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_user_cnode_mint_which_implies_wit_4_split_goal_spatial.
Qed. 

Lemma proof_of_user_cnode_mint_which_implies_wit_5 : user_cnode_mint_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply auth_view__user_auth_views; assumption.
Qed. 

Lemma proof_of_user_cnode_mint_which_implies_wit_6_split_goal_spatial : user_cnode_mint_which_implies_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply auth_restore__user_auth_views; assumption.
Qed.

Lemma proof_of_user_cnode_mint_which_implies_wit_6 : user_cnode_mint_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_user_cnode_mint_which_implies_wit_6_split_goal_spatial.
Qed. 


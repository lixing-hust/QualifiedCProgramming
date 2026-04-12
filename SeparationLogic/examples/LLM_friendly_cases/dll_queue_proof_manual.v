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
From SimpleC.EE.LLM_friendly_cases Require Import dll_queue_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_friendly_cases.dll_queue_lib.
Local Open Scope sac.

Lemma proof_of_enqueue_entail_wit_1 : enqueue_entail_wit_1.
Proof.
	pre_process.
	unfold store_queue.
	Intros qhead qtail.
	Exists qhead qtail.
	change (dllseg qhead NULL NULL qtail l) with (dllseg qhead 0 0 qtail l).
	cancel (&((q_pre)  # "queue" ->ₛ "head") # Ptr  |-> qhead).
	cancel (&((q_pre)  # "queue" ->ₛ "tail") # Ptr  |-> qtail).
	cancel (dllseg qhead 0 0 qtail l).
Qed.

Lemma proof_of_enqueue_entail_wit_2 : enqueue_entail_wit_2.
Proof.
	pre_process.
	assert (Hqhead_neq : qhead_2 <> 0) by lia.
	sep_apply_l_atomic (dllseg_head_neq_destruct_tail qhead_2 0 0 qtail_2 l Hqhead_neq).
	Intros qtailprev l0 qtailv.
	Exists qtailprev.
	Exists 0.
	Exists l0.
	Exists qtailv.
	Exists qhead_2.
	Exists qtail_2.
	split_pure_spatial.
	- cancel ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0).
		cancel ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> 0).
		cancel ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre).
		cancel ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead_2).
		cancel ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail_2).
		cancel (dllseg qhead_2 qtail_2 0 qtailprev l0).
		cancel ((&((qtail_2)  # "list" ->ₛ "data")) # Int  |-> qtailv).
		cancel ((&((qtail_2)  # "list" ->ₛ "next")) # Ptr  |-> 0).
		cancel ((&((qtail_2)  # "list" ->ₛ "prev")) # Ptr  |-> qtailprev).
	- split_pures.
		+ dump_pre_spatial.
			exact H0.
		+ dump_pre_spatial.
			exact H1.
		+ dump_pre_spatial.
			exact H.
		+ dump_pre_spatial.
			exact H2.
		+ dump_pre_spatial.
			reflexivity.
Qed.

Lemma proof_of_enqueue_return_wit_1 : enqueue_return_wit_1.
Proof.
	pre_process.
	unfold store_queue.
	Exists qhead p.
	cancel ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> p).
	cancel ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead).
	assert (Hqtail_neq : qtail <> 0) by lia.
	assert (Hp_neq : p <> 0) by lia.
	sep_apply (dllseg_len1 qtail qtailprev p qtailv Hqtail_neq).
	sep_apply (dllseg_len1 p qtail 0 x_pre Hp_neq).
	sep_apply (dllseg_dllseg qhead).
	sep_apply (dllseg_dllseg qhead).
	replace ((l0 ++ qtailv :: nil) ++ x_pre :: nil) with (l ++ x_pre :: nil).
	2:{ rewrite H2.
		rewrite <- app_assoc.
		reflexivity. }
	change (dllseg qhead NULL NULL p (l ++ x_pre :: nil)) with (dllseg qhead 0 0 p (l ++ x_pre :: nil)).
	cancel (dllseg qhead 0 0 p (l ++ x_pre :: nil)).
Qed.

Lemma proof_of_enqueue_return_wit_2 : enqueue_return_wit_2.
Proof.
	pre_process.
	sep_apply (dllseg_head_zero qhead 0 0 qtail l ltac:(lia)).
	Intros.
	subst.
	unfold store_queue.
	Exists retval retval.
	cancel ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> retval).
	cancel ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> retval).
	sep_apply (dllseg_len1 retval 0 0 x_pre H0).
	change (dllseg retval NULL NULL retval (x_pre :: nil)) with (dllseg retval 0 0 retval (x_pre :: nil)).
	reflexivity.
Qed.

Lemma proof_of_dequeue_entail_wit_1 : dequeue_entail_wit_1.
Proof.
	pre_process.
	unfold store_queue.
	Intros qhead qtail.
	simpl.
	Intros qhead_next.
	Exists qhead_next qtail 0 qhead.
	split_pure_spatial.
	- unfold NULL.
		cancel ((&((qhead)  # "list" ->ₛ "prev")) # Ptr  |-> 0).
		cancel ((&((qhead)  # "list" ->ₛ "data")) # Int  |-> x).
		cancel ((&((qhead)  # "list" ->ₛ "next")) # Ptr  |-> qhead_next).
		cancel (dllseg qhead_next 0 qhead qtail l).
		cancel ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead).
		cancel ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail).
	- split_pures.
		+ dump_pre_spatial.
			unfold NULL in H.
			exact H.
		+ dump_pre_spatial.
			reflexivity.
Qed.

Lemma proof_of_dequeue_entail_wit_2 : dequeue_entail_wit_2.
Proof.
	pre_process.
	assert (Hqhead_next_neq : qhead_next_2 <> 0) by lia.
	sep_apply_l_atomic (dllseg_head_neq qhead_next_2 0 qhead qtail_2 l Hqhead_next_neq).
	Intros qhead_next headv l0.
	Exists qhead_next.
	Exists qtail_2.
	Exists qhead.
	Exists headv.
	Exists l0.
	Exists qhead_next_2.
	split_pure_spatial.
	- cancel ((&((qhead_next_2)  # "list" ->ₛ "prev")) # Ptr  |-> qhead).
		cancel ((&((qhead_next_2)  # "list" ->ₛ "data")) # Int  |-> headv).
		cancel ((&((qhead_next_2)  # "list" ->ₛ "next")) # Ptr  |-> qhead_next).
		cancel (dllseg qhead_next 0 qhead_next_2 qtail_2 l0).
		cancel ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead_next_2).
		cancel ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail_2).
	- split_pures.
		+ dump_pre_spatial.
			exact H.
		+ dump_pre_spatial.
			exact H2.
		+ dump_pre_spatial.
			reflexivity.
Qed.

Lemma proof_of_dequeue_return_wit_1 : dequeue_return_wit_1.
Proof.
	pre_process.
	unfold store_queue.
	Exists qhead qtail.
	split_pure_spatial.
	- cancel ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead).
		cancel ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail).
		assert (Hqhead_neq : qhead <> 0) by lia.
		sep_apply (dllseg_len1 qhead 0 qhead_next headv Hqhead_neq).
		sep_apply (dllseg_dllseg qhead).
		rewrite H0.
		simpl.
		unfold NULL.
		reflexivity.
	- dump_pre_spatial.
		reflexivity.
Qed.

Lemma proof_of_dequeue_return_wit_2 : dequeue_return_wit_2.
Proof.
	pre_process.
	sep_apply (dllseg_head_zero qhead_next 0 qhead qtail l ltac:(lia)).
	Intros.
	subst.
	unfold store_queue.
	Exists 0 0.
	split_pure_spatial.
	- cancel ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> 0).
		cancel ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> 0).
		simpl.
		split_pure_spatial.
		+ reflexivity.
		+ split_pures.
			* dump_pre_spatial.
				unfold NULL.
				reflexivity.
			* dump_pre_spatial.
			unfold NULL.
			reflexivity.
	- dump_pre_spatial.
		reflexivity.
Qed.


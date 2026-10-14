Require Import LibTactics.
Require Import base_tac. 
Require Import memory. 
Require Import if_language.
Require Import if_opsem. 
Require Import mq_apispecs.
Require Import prt_apispecs.
Require Import intspecs.
Require Import osspecs.
Require Import properties.

Require Import data_invs.
Require Import equiv_prop.
Require Import if_assms.
Require Import if_succ_gen.
Require Import if_good_code.

Require Import hasrt_sat_preserve.
Require Import FunctionalExtensionality.

Require Import integrity_lemma.
Set Keyed Unification.
Require Import protect.
Require Import spec_aux_defs.
Require Import mqrecv_dataequiv_integrity_proof.

Require Import confidentiality_tactics.
Require Import if_common_lemmas.


(* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\ *)
Lemma mqtmrecv_nabt_spec_step_data_equiv_tskd_preserve:
forall O cd n vl sd cd' O' act ke ks t T i pr pc cst',
good_task_code T ->
(* good_client_code pc -> *)
reachable (pc, (api_spec, int_spec, get_hprio_d)) T cst' O ->
~flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i)->
task_prio_id O pr t ->
get O curtid = Some (oscurt t)->
get T t = Some (curs (hapi_code cd),(ke, ks))->
mqtimedreceive vl <> ABORT ->
nth_error (get_all_succs (mqtimedreceive vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
i <> dom_for_prio pr ->
O <> O'->
data_equiv_tskd i cst' cst' O O'.
Proof. 
introv Hgtc Hrec Hnflo Htpi Hctid Hgett Hnabt Hnth Hstep.
introv Hi_neq HO_neq.
lets Hasrt: rch_hasrt_sat Hrec Hgett Htpi.
remember vl as recv_vl.
do 11 try (destruct recv_vl; simpl in Hnabt;tryfalse);
try destruct v; simpl in Hnabt; tryfalse;
try destruct v1; simpl in Hnabt; tryfalse;
try destruct v3; simpl in Hnabt; tryfalse;
try destruct v4; simpl in Hnabt; tryfalse;
try destruct v6; simpl in Hnabt; tryfalse.
clear Hnabt.
(* n = 0 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 1 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 2 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 3 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 4 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 5 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 6 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 7 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 8 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 9 *)
lets Hgdcd: Hgtc Hgett.
unfolds in Hgdcd. simpl in Hgdcd.
destruct Hgdcd as (Hgde' & Hgdks').
lets Hstep1: Hstep.
protect Hstep1.
protect Hgde'.
assert(HO:data_equiv_tskd i cst' cst' O O).
eapply data_equiv_tskd_same_preserve; eauto.
unfolds in HO.
destruct HO as (Hctq & Hbusq & Hkenl & Hdata).
destruct n; [ my_succs_solver_same_absdata | idtac].
(*qpend_get_no_pwl_succ_body*)
simpl in Hasrt.
eapply qpend_get_no_pwl_succ_data_equiv_tskd_preserve; eauto.
solve_endabt.

(*qpend_get_ex_pwl_before_sched_body*)
eapply qpend_get_ex_pwl_before_sched_data_equiv_tskd_preserve; eauto.
solve_endabt.

(* qpend_block_body *)
eapply qpend_block_body_data_equiv_tskd_preserve; eauto.
solve_endabt.

(* n = 10 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 11 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 12 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 13 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 14 *)
destruct n; [ my_succs_solver_same_absdata | idtac].

(* qpend_block_get_body *)
eapply qpend_block_get_data_equiv_tskd_preserve; eauto.

(*qpend_to_body_data*)
eapply qpend_to_body_data_equiv_tskd_preserve; eauto.
solve_endabt.

solve_endabt.

(* n = 15 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 16 *)
destruct n; [ my_succs_solver_same_absdata | idtac].

(* qacc_succ_body *)
eapply qacc_succ_body_equiv_tskd_preserve; eauto.
solve_endabt.

(* n = 17 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 18 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
re_err_contra n; try my_succs_solver_same_absdata.
tryfalse.
tryfalse.
Qed.

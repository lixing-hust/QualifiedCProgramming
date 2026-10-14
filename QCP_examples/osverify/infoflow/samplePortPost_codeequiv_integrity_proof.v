Require Import LibTactics.
Require Import base_tac. 
Require Import memory. 
Require Import if_language.
Require Import if_opsem. 
Require Import mq_apispecs.
Require Import prt_apispecs.
Require Import buffer_apispecs.
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
Require Import if_common_lemmas.

Lemma tid_unique_set_ntls2:
forall O O' pr t t' aid abs aid' abs',
task_prio_id O pr t ->
task_prio_id O' pr t' ->
O' = (set(set O aid abs) aid' abs') ->
(aid <> abstcblsid) ->
(aid'<>abstcblsid)->
t = t'.
Proof.
introv Ht1 Ht2 Heq Hneq Hneq2.
simpljoin.
lets Ht: tid_unique t Ht2.
unfold task_prio_id in *.
simpljoin.
rewrite set_a_get_a'; eauto.
repeat eexists; eauto.
rewrite set_a_get_a'; eauto.
auto.
Qed.

Lemma sampleportpost_nabt_spec_step_code_equiv_tskd'_preserve :
forall O cd  n vl sd cd' O' act ke ks t T i pr,
good_task_code T->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
get T t = Some (curs (hapi_code cd), (ke, ks)) ->
sampleportpost vl <> ABORT -> 
nth_error (get_all_succs (sampleportpost vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
i <> dom_for_prio pr ->
O <> O' ->
code_equiv_tskd' i T (set T t (curs (hapi_code cd'), (ke, ks))) O O'.
Proof.
introv Hgtc Htpi Hctid Hgett Hnabt Hnth Hstep Hi_neq HO_neq.
remember vl as qp_vl.
lets Hnn: Hnth.
protect Hnn.
do 11 try (destruct qp_vl; simpl in Hnabt;tryfalse);
try destruct v0; simpl in Hnabt; tryfalse.
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
lets Hgdcd: Hgtc Hgett.
unfolds in Hgdcd. simpl in Hgdcd.
destruct Hgdcd as (Hgde' & Hgdks').
lets Hstep1: Hstep.
protect Hstep1.
destruct n; [ my_succs_solver_same_absdata | idtac].

(* sample_send_to_domain *)
inverts H3; simpljoin.

assert (get O osdomainportid = Some (osdomainport x0)) as Hodp.
eapply join_get_get_l;eauto.

assert (get O oskportid = Some (oskport x8)) as Hokp.
eapply join_get_get_l;eauto.

assert (get O oschannelid = Some (oschannel x14)) as Hosc.
eapply join_get_get_l;eauto.

assert (get O ibufsid = Some (ibufs x19)) as Hibf.
eapply join_get_get_l;eauto.

assert (O' =
        set (set O osdomainportid (osdomainport x23)) ibufsid
           (ibufs (upd_bufmp x19 x20 x22))).
eapply join_get_set_eq_2;eauto. inverts H16. eauto.

remember O as Ox.

unfolds; intros.

lets Hm:tid_unique_set_ntls2 H17 H18 H14; eauto.
destruct Hm; auto.
intro; tryfalse.
intro; tryfalse.
subst i.

assert(Hnpr: pr <> pr0).
clear -Hi_neq.
unfold dom_for_prio in Hi_neq.
intro; subst.
eapply Hi_neq; auto.
splits; auto.
lets Htneq: task_prio_id_tidneq Htpi H17 Hnpr; auto.
unfold get, set in *;simpl in *.
rewrite TasksMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto];auto.
remember ((fun (O : osabst) (pr : priority) =>
                  prt_indom v O pr /\ has_prtpost_cap O pr, nil)
                 # sample_send_to_domain [|v :: nil|];;
                 conditional_semrel v i0;;
                 ret_val (|V$ OS_NO_ERR :: nil|)) as cd.
clear Heqcd.

intros.
lets Hgdcode: Hgtc H15.
unfolds in Hgdcode. simpl in Hgdcode.
destruct Hgdcode as (Hgde & Hgdks).
unfolds in Hgde.

splits.
destruct c.
left; unfolds; left; eauto.
destruct s; 
try solve [ left; unfolds; right; eexists; splits; eauto;
                   intro; simpljoin; tryfalse].
right. eexists. splits; eauto.
unfolds in Hgde.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists sample_port_post.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold sampleportpostapi. eauto.
(*ks0 = kevent*)
intros. subst.
unfolds in Hgdks.
destruct Hgdks as (Hgdel & Hgdks).
unfolds in Hgdel.
unfolds in Hgdel.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists sample_port_post.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold sampleportpostapi. eauto.
(* sample_send_to_domain *)
solve_endabt.

(* n = 5 *)
destruct n; [ my_succs_solver_same_absdata | idtac].

(* n = 6 *)
destruct n; [ my_succs_solver_same_absdata | idtac].

(* n = 7 *)
destruct n; [ my_succs_solver_same_absdata | idtac].

(* n = 8 *)
destruct n; [ my_succs_solver_same_absdata | idtac].

(* n = 9 *)
destruct n; [ my_succs_solver_same_absdata | idtac].

re_err_contra n; try my_succs_solver_same_absdata.
tryfalse.
tryfalse.
Qed.

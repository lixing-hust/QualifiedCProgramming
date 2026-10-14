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
Require Import if_common_lemmas.
(* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\ *)

Lemma qppost_nabt_spec_step_code_equiv_tskd'_preserve :
forall O cd  n vl sd cd' O' act ke ks t T i pr,
good_task_code T->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
get T t = Some (curs (hapi_code cd), (ke, ks)) ->
qportpost vl <> ABORT -> 
nth_error (get_all_succs (qportpost vl)) n = Some cd ->
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

(* q_send_to_domain *)
lets Hgdcd: Hgtc Hgett.
unfolds in Hgdcd. simpl in Hgdcd.
destruct Hgdcd as (Hgde' & Hgdks').
lets Hstep1: Hstep.
protect Hstep1.

destruct n; [ my_succs_solver_same_absdata | idtac].
inverts H3;simpljoin.
inverts H21.
kvextH Hosdp O0 osdomainportid O. 
kvextH Hoskpt O0 oskportid O. 
kvextH Hoscha O0 oschannelid O.
kvextH Hibf O0 ibufsid O.
kvextH Hecb O0 absecblsid O.
kvextH Htcb O0 abtcblsid O.
assert (O'=set
(set
   (set (set O osdomainportid (osdomainport x27)) abtcblsid
      (abstcblist x26)) absecblsid (absecblist x24)) ibufsid
(ibufs (upd_bufmp x19 x20 x22))).
eapply join_get_set_eq_4;eauto.
clear H0 H2 H4 H7 H10 H11.
subst.
unfolds; intros. 

casetac pr pr0 Heq Hp_neq.
rewrite Heq in *.
tryfalse.
lets Hnew : H4.
unfold task_prio_id in  H4.
simpljoin.
do 2 rewrite set_a_get_a' in H4; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H4.
inverts H4.

assert(t1 = t2).
{
unfolds in H2;simpljoin.
l_rew21_inv1 (get O abtcblsid).

unfold tcbl_upd in H18.
lets Heqt1: H18 t2.
destruct Heqt1.
simpljoin.
rewrite H7 in H11.
inverts H11.
eapply tid_unique;
unfolds; do 5 eexists; split ;eauto. 

destruct H4.
rewrite H10 in H7.
eapply tid_unique;
unfolds; do 5 eexists; split ;eauto.
}
subst.
lets Hneq: task_prio_id_tidneq Htpi H2 Hp_neq.
rewrite set_a_get_a' ; eauto.
split;eauto.

remember (Aif | (fun (O : osabst) (pr : priority) =>
prt_indom v O pr /\ has_prtpost_cap O pr, nil)
| (fun O : osabst => has_dst_ports O v)
{q_send_to_domain (|v :: nil|);;
conditional_semrel v i0;;
SCHED;; ret_val (|V$ OS_NO_ERR :: nil|)}
else {Aif (fun O : osabst =>
    exists a dpl pcn pd pid pst pin pout n msgl,
    v = Vptr a /\
    get O osdomainportid = Some (osdomainport dpl) /\
    get dpl a =
    Some
      (pcn, pd, pid, SourceP, pst, pin, pout,
      QueuePort n msgl) /\ (length msgl < n)%nat)
{store_msg (|v :: nil|);;
conditional_semrel v i0;;
ret_val (|V$ OS_NO_ERR :: nil|)}
else {conditional_semrel v i0;;
     ret_val (|V$ OS_NO_ERR :: nil|)}}) as cd.
clear Heqcd.

intros.
lets Hgdcode: Hgtc H0.
unfolds in Hgdcode. 
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
exists q_port_post.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold qportpostapi. eauto.
(*ks0 = kevent*)
intros. subst.
unfolds in Hgdks.
destruct Hgdks as (Hgdel & Hgdks).
unfolds in Hgdel.
unfolds in Hgdel.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists q_port_post.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold qportpostapi. eauto.


(* q_send_to_domain *)
solve_endabt.

(* store_msg *)
inverts H3; simpljoin.
inverts H11.
kvextH Hosdp O0 osdomainportid O. 
kvextH Hibf O0 ibufsid O.
assert (O'=set
(set O osdomainportid
   (osdomainport
      (set x0 x
         (x1, x2, x3, SourceP, x4, x5, x6,
         QueuePort x7 (x8 ++ x11 :: nil))))) ibufsid
(ibufs (upd_bufmp x9 x10 x8))).
eapply join_get_set_eq_2;eauto.
clear H1 H3.
subst.
unfolds; intros. 

casetac pr pr0 Heq Hp_neq.
rewrite Heq in *.
tryfalse.

lets Hnew : H3.
unfold task_prio_id in H3.
simpljoin.
do 2 rewrite set_a_get_a' in H3; try intro ; tryfalse;eauto.

assert(t1 = t2).
{
unfolds in H1;simpljoin.
l_rew21_inv1 (get O abtcblsid).

eapply tid_unique;
unfolds; do 5 eexists; split ;eauto.
}
subst.
lets Hneq: task_prio_id_tidneq Htpi H1 Hp_neq.
rewrite set_a_get_a' ; eauto.
split;eauto.

remember (Aif | (fun (O : osabst) (pr : priority) =>
prt_indom (Vptr x13) O pr /\ has_prtpost_cap O pr, nil)
| (fun O : osabst => has_dst_ports O (Vptr x13))
{q_send_to_domain (|Vptr x13 :: nil|);;
conditional_semrel (Vptr x13) i0;;
SCHED;; ret_val (|V$ OS_NO_ERR :: nil|)}
else {Aif (fun O : osabst =>
    exists a dpl pcn pd pid pst pin pout n msgl,
    Vptr x13 = Vptr a /\
    get O osdomainportid = Some (osdomainport dpl) /\
    get dpl a =
    Some
      (pcn, pd, pid, SourceP, pst, pin, pout,
      QueuePort n msgl) /\ (length msgl < n)%nat)
{store_msg (|Vptr x13 :: nil|);;
conditional_semrel (Vptr x13) i0;;
ret_val (|V$ OS_NO_ERR :: nil|)}
else {conditional_semrel (Vptr x13) i0;;
     ret_val (|V$ OS_NO_ERR :: nil|)}}) as cd.
clear Heqcd.

intros.
lets Hgdcode: Hgtc H0.
unfolds in Hgdcode. 
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
exists q_port_post.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold qportpostapi. eauto.

(*ks0 = kevent*)
intros. subst.
unfolds in Hgdks.
destruct Hgdks as (Hgdel & Hgdks).
unfolds in Hgdel.
unfolds in Hgdel.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists q_port_post.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold qportpostapi. eauto.


(* store_msg *)
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
(* n = 10 *)
destruct n; [ my_succs_solver_same_absdata | idtac].

re_err_contra n; try my_succs_solver_same_absdata.
tryfalse.
tryfalse.
Qed.





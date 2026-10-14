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

Lemma bufpost_nabt_spec_step_code_equiv_tskd'_preserve :
forall O cd  n vl sd cd' O' act ke ks t T i pr,
good_task_code T->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
get T t = Some (curs (hapi_code cd), (ke, ks)) ->
bufferpost vl <> ABORT -> 
nth_error (get_all_succs (bufferpost vl)) n = Some cd ->
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
try destruct v1; simpl in Hnabt; tryfalse.
clear Hnabt.
(* n = 0 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 1 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 2 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 3 *)
lets Hgdcd: Hgtc Hgett.
unfolds in Hgdcd. simpl in Hgdcd.
destruct Hgdcd as (Hgde' & Hgdks').
lets Hstep1: Hstep.
protect Hstep1.
destruct n; [ my_succs_solver_same_absdata | idtac].

(* qpost_nowt_succ_body *)
inverts H3; simpljoin.
destruct H12 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.

assert (get O absecblsid = Some (absecblist x7)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set O absecblsid
           (absecblist (set x7 x (absmsgq (x9 ++ x0 :: nil) x8 x10, nil)))).
eapply join_get_set_eq;eauto.
clear H3.
remember O as Ox.
clear HeqOx.
unfolds; intros.
lets Hm:tid_unique_set_ntls H2 H3 H0; eauto.
destruct Hm; auto.
intro; tryfalse.
subst i.

assert(Hnpr: pr <> pr0).
clear -Hi_neq.
unfold dom_for_prio in Hi_neq.
intro; subst.
eapply Hi_neq; auto.
splits; auto.
lets Htneq: task_prio_id_tidneq Htpi H2 Hnpr; auto.
unfold get, set in *;simpl in *.
rewrite TasksMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto];auto.
remember ((Aif | (buffer_indom (Vptr x3), nil)
| (fun _ : osabst => Vptr x3 = Vnull)
{asrt_and_ret (|Vint32 i0 :: V$ OS_ERR_PEVENT_NULL :: nil|)}
else {Aif (fun _ : osabst =>
           exists qid, Vptr x3 = Vptr qid /\ v0 = Vnull)
      {asrt_and_ret
       (|Vint32 i0 :: V$ OS_ERR_POST_NULL_PTR :: nil|)}
      else {Aif (fun O : osabst =>
                 exists qid els,
                 Vptr x3 = Vptr qid /\
                 v0 <> Vnull /\
                 get O absecblsid = Some (absecblist els) /\
                 ~
                 (exists x y pwl wls,
                  get els qid = Some (absmsgq x y pwl, wls)))
            {asrt_and_ret
             (|Vint32 i0 :: V$ OS_ERR_EVENT_TYPE :: nil|)}
            else {Aif (fun O : osabst =>
                       exists qid qls ml n pwl wl,
                       Vptr x3 = Vptr qid /\
                       v0 <> Vnull /\
                       get O absecblsid =
                       Some (absecblist qls) /\
                       get qls qid =
                       Some (absmsgq ml n pwl, wl) /\
                       Z.of_nat (length ml) >= Int.unsigned n)
                  {asrt_and_ret
                   (|Vint32 i0 :: V$ MSGQ_OVF_ERR :: nil|)}
                  else {Aif (fun O : osabst =>
                             exists qls qid ml n pwl,
                             Vptr x3 = Vptr qid /\
                             v0 <> Vnull /\
                             get O absecblsid =
                             Some (absecblist qls) /\
                             get qls qid =
                             Some (absmsgq ml n pwl, nil) /\
                             Z.of_nat (length ml) <
                             Int.unsigned n)
                        {qpost_nowt_succ_body
                         (|Vptr x3 :: v0 :: Vint32 i0 :: nil|)}
                        else {Aif (fun O : osabst =>
                                   exists qid els,
                                   Vptr x3 = Vptr qid /\
                                   v0 <> Vnull /\
                                   get O absecblsid =
                                   Some (absecblist els) /\
                                   (exists x y pwl wls,
                                   get els qid =
                                   Some
                                   (absmsgq x y pwl, wls) /\
                                   wls <> nil))
                              {qpost_exwt_succ_body
                               (|Vptr x3
                                 :: 
                                 v0 :: Vint32 i0 :: nil|);;
                               SCHED;;
                               asrt_and_ret
                               (|Vint32 i0
                                 :: 
                                 V$ OS_NO_ERR :: nil|)}
                              else {ASSUME 
                              (fun _ : osabst => False)}}}}}});;
(fun (_ : osabst) (_ : priority) => True, Vint32 i0 :: nil)
# ret_val [|Vint32 i0 :: nil|]) as cd.
clear Heqcd.

intros.
lets Hgdcode: Hgtc H1.
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
exists buffer_post.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold bufferpostapi. eauto.
(*ks0 = kevent*)
intros. subst.
unfolds in Hgdks.
destruct Hgdks as (Hgdel & Hgdks).
unfolds in Hgdel.
unfolds in Hgdel.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists buffer_post.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold bufferpostapi. eauto.
(* qpost_nowt_succ_body *)
solve_endabt.

(* qpost_exwt_succ_body *)
inverts H3; simpljoin.
destruct H20 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.

assert (get O absecblsid = Some (absecblist x4)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x9)) as Htcb.
eapply join_get_get_l;eauto.

assert (O'= set
(set O abtcblsid
   (abstcblist (set x9 x8 (x13, rdy, x0, x12, x17))))
absecblsid
(absecblist (set x4 x (absmsgq nil x15 x16, remove_tid x8 x6)))).
eapply join_get_set_eq_2;eauto.
clear H3 H4.
remember O as Ox.
clear HeqOx.
unfolds; intros.
rewrite Hecb in H22; inverts H22.

subst.
assert(Hneq: pr0 <> pr) by (eapply dom_for_prio_neq in Hi_neq; eauto).

 assert(t1 = t2).
{ clear - Htcb Hecb H2 H3 H6 H8 H14 Hneq.
   unfolds in H8; simpljoin.
   unfolds in H2. unfolds in H3. simpljoin.
   rewrite set_a_get_a' in H3; try intro; tryfalse; eauto.
   rewrite set_a_get_a in H3; auto.
   inverts H3.
   rewrite Htcb in H2; inverts H2.
   rewrite H14 in H0; inverts H0.
   casetac x8 t2 He Hn;
   subst;
   [rewrite set_a_get_a in H4; inverts H4 |
   rewrite set_a_get_a' in H4; eauto ];
   eapply tid_unique; eauto;
   unfolds; do 5 eexists; eauto. }

subst.
assert(t <> t2).
{
eapply task_prio_id_tidneq in H2; eauto.
}
splits.
rewrite set_a_get_a'; eauto.
introv Ht2.
lets Hgdcode: Hgtc Ht2.
unfolds in Hgdcode. simpl in Hgdcode.
destruct Hgdcode as (Hgde & Hgdks).
unfolds in Hgde.
remember ((Aif | (buffer_indom (Vptr x2), nil)
| (fun _ : osabst => Vptr x2 = Vnull)
{asrt_and_ret (|Vint32 i0 :: V$ OS_ERR_PEVENT_NULL :: nil|)}
else {Aif (fun _ : osabst =>
           exists qid, Vptr x2 = Vptr qid /\ v0 = Vnull)
      {asrt_and_ret
       (|Vint32 i0 :: V$ OS_ERR_POST_NULL_PTR :: nil|)}
      else {Aif (fun O : osabst =>
                 exists qid els,
                 Vptr x2 = Vptr qid /\
                 v0 <> Vnull /\
                 get O absecblsid = Some (absecblist els) /\
                 ~
                 (exists x y pwl wls,
                  get els qid = Some (absmsgq x y pwl, wls)))
            {asrt_and_ret
             (|Vint32 i0 :: V$ OS_ERR_EVENT_TYPE :: nil|)}
            else {Aif (fun O : osabst =>
                       exists qid qls ml n pwl wl,
                       Vptr x2 = Vptr qid /\
                       v0 <> Vnull /\
                       get O absecblsid = Some (absecblist qls) /\
                       get qls qid =
                       Some (absmsgq ml n pwl, wl) /\
                       Z.of_nat (length ml) >= Int.unsigned n)
                  {asrt_and_ret
                   (|Vint32 i0 :: V$ MSGQ_OVF_ERR :: nil|)}
                  else {Aif (fun O : osabst =>
                             exists qls qid ml n pwl,
                             Vptr x2 = Vptr qid /\
                             v0 <> Vnull /\
                             get O absecblsid =
                             Some (absecblist qls) /\
                             get qls qid =
                             Some (absmsgq ml n pwl, nil) /\
                             Z.of_nat (length ml) <
                             Int.unsigned n)
                        {qpost_nowt_succ_body
                         (|Vptr x2 :: v0 :: Vint32 i0 :: nil|)}
                        else {Aif (fun O : osabst =>
                                   exists qid els,
                                   Vptr x2 = Vptr qid /\
                                   v0 <> Vnull /\
                                   get O absecblsid =
                                   Some (absecblist els) /\
                                   (exists x y pwl wls,
                                    get els qid =
                                    Some (absmsgq x y pwl, wls) /\
                                    wls <> nil))
                              {qpost_exwt_succ_body
                               (|Vptr x2
                                 :: v0 :: Vint32 i0 :: nil|);;
                               SCHED;;
                               asrt_and_ret
                               (|Vint32 i0
                                 :: V$ OS_NO_ERR :: nil|)}
                              else {ASSUME 
                              (fun _ : osabst => False)}}}}}});;
(fun (_ : osabst) (_ : priority) => True, Vint32 i0 :: nil)
# ret_val [|Vint32 i0 :: nil|]) as cd.
clear Heqcd.

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
exists buffer_post.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold bufferpostapi. eauto.
(*ks0 = kevent*)
intros. subst.
unfolds in Hgdks.
destruct Hgdks as (Hgdel & Hgdks).
unfolds in Hgdel.
unfolds in Hgdel.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists buffer_post.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold bufferpostapi. eauto.
(* qpost_exwt_succ_body *)
solve_endabt.

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
destruct n; [ my_succs_solver_same_absdata | idtac].
re_err_contra n; try my_succs_solver_same_absdata.
tryfalse.
tryfalse.
Qed.


























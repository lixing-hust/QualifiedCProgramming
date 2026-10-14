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

Lemma dom_for_prio_neq:
forall pr pr1,
dom_for_prio pr1 <> dom_for_prio pr ->
pr1 <> pr.
Proof.
intros.
intro; subst; tryfalse.
Qed.

Lemma task_prio_id_set_ntls_eq:
forall O O' pr aid abs,
(exists t, task_prio_id O pr t )->
O' = (set O aid abs) ->
(aid <> abstcblsid) ->
(exists t, task_prio_id O' pr t).
Proof.
introv Ht Heq Hneq.
simpljoin.
exists x.
unfold task_prio_id in *.
simpljoin.
rewrite set_a_get_a'; eauto.
rewrite H.
do 5 eexists; eauto.
Qed.

Lemma task_prio_id_set_ntls_eq':
forall O O' pr aid abs,
(exists t, task_prio_id O' pr t )->
O' = (set O aid abs) ->
(aid <> abstcblsid) ->
(exists t, task_prio_id O pr t).
Proof.
introv Ht Heq Hneq.
simpljoin.
exists x.
unfold task_prio_id in *.
simpljoin.
rewrite set_a_get_a' in H; eauto.
rewrite H.
do 5 eexists; eauto.
Qed.


Lemma mqsend_nabt_spec_step_code_equiv_tskd'_preserve :
forall O cd  n vl sd cd' O' act ke ks t T i pr,
good_task_code T ->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
get T t = Some (curs (hapi_code cd), (ke, ks)) ->
mqsend vl <> ABORT -> 
nth_error (get_all_succs (mqsend vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
i <> dom_for_prio pr ->
O <> O' ->
code_equiv_tskd' i T (set T t (curs (hapi_code cd'), (ke, ks))) O O'.
Proof. 
introv Hgdtk Htpi Hctid Hgett Hnabt Hnth Hstep Hi_neq HO_neq.
remember vl as recv_vl.
lets Hnn: Hnth.
protect Hnn.
do 11 try (destruct recv_vl; simpl in Hnabt;tryfalse);
try destruct v; simpl in Hnabt; tryfalse;
try destruct v1; simpl in Hnabt; tryfalse;
try destruct v3; simpl in Hnabt; tryfalse;
try destruct v5; simpl in Hnabt; tryfalse;
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
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 10 *)
lets Hgdcd: Hgdtk Hgett.
unfolds in Hgdcd. simpl in Hgdcd.
destruct Hgdcd as (Hgde' & Hgdks').
lets H': Hstep.
protect H'.
protect Hgde'.
destruct n; [ my_succs_solver_same_absdata | idtac].
(*qtimedpost_nowt_succ_body*)
inverts H3; simpljoin.
destruct H14 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
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

remember ((Aif | (mqdes_dom_qptr i0 (Vptr x3), nil) | (fun _ : osabst => Vptr x3 = Vnull)
               {asrt_and_ret (|Vint32 i4 :: V$ OS_ERR_PEVENT_NULL :: nil|)}
               else {Aif (fun _ : osabst => exists qid, Vptr x3 = Vptr qid /\ v0 = Vnull)
                     {asrt_and_ret (|Vint32 i4 :: V$ OS_ERR_POST_NULL_PTR :: nil|)}
                     else {Aif (fun O1 : osabst =>
                                exists qid els,
                                Vptr x3 = Vptr qid /\
                                v0 <> Vnull /\
                                get O1 absecblsid = Some (absecblist els) /\
                                ~
                                (exists x11 y pwl wls,
                                 get els qid = Some (absmsgq x11 y pwl, wls)))
                           {asrt_and_ret (|Vint32 i4 :: V$ OS_ERR_EVENT_TYPE :: nil|)}
                           else {Aif (fun O1 : osabst =>
                                      exists qid els,
                                      Vptr x3 = Vptr qid /\
                                      v0 <> Vnull /\
                                      get O1 absecblsid = Some (absecblist els) /\
                                      (exists x11 y pwl wls,
                                       get els qid = Some (absmsgq x11 y pwl, wls) /\
                                       wls <> nil))
                                 {qpost_exwt_succ_body (|Vptr x3 :: v0 :: Vint32 i4 :: nil|);;
                                  SCHED;; asrt_and_ret (|Vint32 i4 :: V$ OS_NO_ERR :: nil|)}
                                 else {Aif (fun O1 : osabst =>
                                            task_notrdy_or_idle O1 (Vptr x3) v0)
                                       {ASSERT (fun _ : osabst => False)}
                                       else {Aif (fun O1 : osabst =>
                                                  exists qid qls ml n pwl wl,
                                                  Vptr x3 = Vptr qid /\
                                                  v0 <> Vnull /\
                                                  get O1 absecblsid = Some (absecblist qls) /\
                                                  get qls qid = Some (absmsgq ml n pwl, wl) /\
                                                  Z.of_nat (length ml) >= Int.unsigned n)
                                             {qtimedpost_ovf_block_body
                                              (|Vptr x3 :: v0 :: Vint32 i4 :: nil|);;
                                              sched (mqdes_dom_qptr i0 (Vptr x3), nil);;
                                              (mqdes_dom_qptr i0 (Vptr x3), nil)
                                              # qtimedpost_after_sched
                                              [|Vptr x3 :: v0 :: Vint32 i4 :: nil|];;
                                              (Aif | (mqdes_dom_qptr i0 (Vptr x3), nil)
                                               | (fun O1 : osabst =>
                                                  exists qid pr1 t0 tls p m sus,
                                                  Vptr x3 = Vptr qid /\
                                                  v0 <> Vnull /\
                                                  get O1 curtid = Some (oscurt t0) /\
                                                  get O1 abtcblsid = Some (abstcblist tls) /\
                                                  get tls t0 =
                                                  Some
                                                    (p, wait (os_stat_postq qid) None, m, sus,
                                                    pr1))
                                               {qtimedpost_timeout_err_body
                                                (|Vptr x3 :: v0 :: Vint32 i4 :: nil|)}
                                               else {Aif (fun O1 : osabst =>
                                                          exists qid t0 tls p st m sus pr1,
                                                          Vptr x3 = Vptr qid /\
                                                          v0 <> Vnull /\
                                                          get O1 curtid = Some (oscurt t0) /\
                                                          get O1 abtcblsid =
                                                          Some (abstcblist tls) /\
                                                          get tls t0 =
                                                          Some (p, st, m, sus, pr1) /\
                                                          st = rdy /\ sus = false)
                                                     {asrt_and_ret
                                                      (|Vint32 i4 :: V$ OS_NO_ERR :: nil|)}
                                                     else {ASSUME 
                                                     (fun _ : osabst => False)}})}
                                             else {Aif (fun O1 : osabst =>
                                                        exists qls qid ml n pwl,
                                                        Vptr x3 = Vptr qid /\
                                                        v0 <> Vnull /\
                                                        get O1 absecblsid =
                                                        Some (absecblist qls) /\
                                                        get qls qid =
                                                        Some (absmsgq ml n pwl, nil) /\
                                                        Z.of_nat (length ml) < Int.unsigned n)
                                                   {qpost_nowt_succ_body
                                                    (|Vptr x3 :: v0 :: Vint32 i4 :: nil|)}
                                                   else {ASSUME (fun _ : osabst => False)}}}}}}});;
              mqsend_res i4) as cd.
clear Heqcd.

intros.
lets Hgdcode: Hgdtk H1.
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
exists mq_send.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold mqsendapi. eauto.
(*ks0 = kevent*)
intros. subst.
unfolds in Hgdks.
destruct Hgdks as (Hgdel & Hgdks).
unfolds in Hgdel.
unfolds in Hgdel.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists mq_send.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold mqsendapi. eauto.

(*qtimedpost_exwt_succ_body*)
inverts H3; simpljoin.
destruct H18 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.

assert (get O absecblsid = Some (absecblist x4)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x9)) as Htcb.
eapply join_get_get_l;eauto.

assert (O'=set (set O abtcblsid (abstcblist (set x9 x8 (x13, rdy, x0, x12, x17))))
           absecblsid
           (absecblist (set x4 x (absmsgq nil x15 x16, remove_tid x8 x6)))).
eapply join_get_set_eq_2;eauto.
clear H3 H4.
remember O as Ox.
clear HeqOx.
unfolds; intros.
rewrite Hecb in H20; inverts H20.
subst.
 assert(t1 = t2).
{ clear -Hecb Htcb H2 H3 H6 H8 H12.
   unfolds in H8; simpljoin.
   unfolds in H2. unfolds in H3. simpljoin.
   rewrite set_a_get_a' in H3; try intro; tryfalse; eauto.
   rewrite set_a_get_a in H3; auto.
   inverts H3.
   rewrite Htcb in H2; inverts H2.
   casetac x8 t2 He Hn;
   subst;[
   try rewrite set_a_get_a in H4; inverts H4; auto |
   try rewrite set_a_get_a' in H4; eauto ];
   eapply tid_unique; eauto;
   unfolds; do 5 eexists; eauto. }

subst.
assert(Hneq: pr0 <> pr) by (eapply dom_for_prio_neq in Hi_neq; eauto).
assert(t <> t2).
{
eapply task_prio_id_tidneq in H2; eauto.
}
splits.
rewrite set_a_get_a'; eauto.
introv Ht2.
lets Hgdcode: Hgdtk Ht2.
unfolds in Hgdcode. simpl in Hgdcode.
destruct Hgdcode as (Hgde & Hgdks).
unfolds in Hgde.

remember ((Aif | (mqdes_dom_qptr i0 (Vptr x2), nil)
| (fun _ : osabst => Vptr x2 = Vnull)
{asrt_and_ret
 (|Vint32 i4 :: V$ OS_ERR_PEVENT_NULL :: nil|)}
else {Aif (fun _ : osabst =>
           exists qid, Vptr x2 = Vptr qid /\ v0 = Vnull)
      {asrt_and_ret
       (|Vint32 i4 :: V$ OS_ERR_POST_NULL_PTR :: nil|)}
      else {Aif (fun O : osabst =>
                 exists qid els,
                 Vptr x2 = Vptr qid /\
                 v0 <> Vnull /\
                 get O absecblsid = Some (absecblist els) /\
                 ~
                 (exists x y pwl wls,
                  get els qid =
                  Some (absmsgq x y pwl, wls)))
            {asrt_and_ret
             (|Vint32 i4 :: V$ OS_ERR_EVENT_TYPE :: nil|)}
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
                   (|Vptr x2 :: v0 :: Vint32 i4 :: nil|);;
                   SCHED;;
                   asrt_and_ret
                   (|Vint32 i4 :: V$ OS_NO_ERR :: nil|)}
                  else {Aif (fun O : osabst =>
                             task_notrdy_or_idle O
                               (Vptr x2) v0)
                        {ASSERT (fun _ : osabst => False)}
                        else {Aif (
                              fun O : osabst =>
                              exists qid qls ml n pwl wl,
                              Vptr x2 = Vptr qid /\
                              v0 <> Vnull /\
                              get O absecblsid =
                              Some (absecblist qls) /\
                              get qls qid =
                              Some (absmsgq ml n pwl, wl) /\
                              Z.of_nat (length ml) >=
                              Int.unsigned n)
                              {qtimedpost_ovf_block_body
                               (|
                               Vptr x2
                               :: 
                               v0 :: Vint32 i4 :: nil|);;
                               sched
                                (
                                mqdes_dom_qptr i0
                                (Vptr x2), nil);;
                               (mqdes_dom_qptr i0
                                (Vptr x2), nil)
                               # qtimedpost_after_sched
                               [|
                               Vptr x2
                               :: 
                               v0 :: Vint32 i4 :: nil|];;
                               (Aif | 
                                (
                                mqdes_dom_qptr i0
                                (Vptr x2), nil)
                                | (
                                fun O : osabst =>
                                exists qid pr t tls p m
                                sus,
                                Vptr x2 = Vptr qid /\
                                v0 <> Vnull /\
                                get O curtid =
                                Some (oscurt t) /\
                                get O abtcblsid =
                                Some (abstcblist tls) /\
                                get tls t =
                                Some
                                (p,
                                wait 
                                (os_stat_postq qid) None,
                                m, sus, pr))
                                {
                                qtimedpost_timeout_err_body
                                (|
                                Vptr x2
                                :: 
                                v0 :: Vint32 i4 :: nil|)}
                                else {
                                Aif (
                                fun O : osabst =>
                                exists qid t tls p st m
                                sus pr,
                                Vptr x2 = Vptr qid /\
                                v0 <> Vnull /\
                                get O curtid =
                                Some (oscurt t) /\
                                get O abtcblsid =
                                Some (abstcblist tls) /\
                                get tls t =
                                Some (p, st, m, sus, pr) /\
                                st = rdy /\ sus = false)
                                {
                                asrt_and_ret
                                (|
                                Vint32 i4
                                :: 
                                V$ OS_NO_ERR :: nil|)}
                                else {ASSUME 
                                (fun _ : osabst => False)}})}
                              else {
                              Aif (
                              fun O : osabst =>
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
                               (|
                               Vptr x2
                               :: 
                               v0 :: Vint32 i4 :: nil|)}
                              else {ASSUME 
                              (fun _ : osabst => False)}}}}}}});;
mqsend_res i4) as cd.
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
exists mq_send.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold mqsendapi. eauto.

(*ks0 = kevent*)
intros. subst.
unfolds in Hgdks.
destruct Hgdks as (Hgdel & Hgdks).
unfolds in Hgdel.
unfolds in Hgdel.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists mq_send.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold mqsendapi. eauto.

(*qtimedpost_exwt_succ_body*)
solve_endabt.

(*qtimedpost_ovf_block_body*)
inverts H3; simpljoin.
inverts H21.

assert (get O curtid = Some (oscurt x12)) as Hct.
eapply join_get_get_l; eauto.
assert (get O absecblsid = Some (absecblist x13)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x15)) as Htcb.
eapply join_get_get_l;eauto.

assert (O'=set (set O abtcblsid
              (abstcblist
                 (set x15 x12 (x2, wait (os_stat_postq x) None, x0, x1, x21))))
           absecblsid
           (absecblist (set x13 x (absmsgq x17 x18 (x12 :: x19), x20)))).
eapply join_get_set_eq_2;eauto.
clear H1 H2 H3.
remember O as Ox.
clear HeqOx.
unfolds; intros.
rewrite Hecb in H23; inverts H23.
subst.
 assert(t1 = t2).
{ clear -Hecb Htcb H2 H3 H4 H14 H24 H13.
   unfolds in H2. unfolds in H3. simpljoin.
   rewrite set_a_get_a' in H; try intro; tryfalse; eauto.
   rewrite set_a_get_a in H; auto.
   inverts H.
   rewrite Htcb in H0; inverts H0.
   casetac x12 t2 He Hn;
   subst;[
   try rewrite set_a_get_a in H1; inverts H1; auto |
   try rewrite set_a_get_a' in H1; eauto ];
   eapply tid_unique; eauto;
   unfolds; do 5 eexists; eauto. }

subst.
assert(Hneq: pr0 <> pr) by (eapply dom_for_prio_neq in Hi_neq; eauto).
assert(t <> t2).
{
eapply task_prio_id_tidneq in H2; eauto.
}
splits.
rewrite set_a_get_a'; eauto.
introv Ht2.
lets Hgdcode: Hgdtk Ht2.
unfolds in Hgdcode. simpl in Hgdcode.
destruct Hgdcode as (Hgde & Hgdks).
unfolds in Hgde.

remember ((Aif | (mqdes_dom_qptr i0 (Vptr x6), nil)
| (fun _ : osabst => Vptr x6 = Vnull)
{asrt_and_ret
 (|Vint32 i4 :: V$ OS_ERR_PEVENT_NULL :: nil|)}
else {Aif (fun _ : osabst =>
           exists qid, Vptr x6 = Vptr qid /\ v0 = Vnull)
      {asrt_and_ret
       (|Vint32 i4 :: V$ OS_ERR_POST_NULL_PTR :: nil|)}
      else {Aif (fun O : osabst =>
                 exists qid els,
                 Vptr x6 = Vptr qid /\
                 v0 <> Vnull /\
                 get O absecblsid = Some (absecblist els) /\
                 ~
                 (exists x y pwl wls,
                  get els qid =
                  Some (absmsgq x y pwl, wls)))
            {asrt_and_ret
             (|Vint32 i4 :: V$ OS_ERR_EVENT_TYPE :: nil|)}
            else {Aif (fun O : osabst =>
                       exists qid els,
                       Vptr x6 = Vptr qid /\
                       v0 <> Vnull /\
                       get O absecblsid =
                       Some (absecblist els) /\
                       (exists x y pwl wls,
                        get els qid =
                        Some (absmsgq x y pwl, wls) /\
                        wls <> nil))
                  {qpost_exwt_succ_body
                   (|Vptr x6 :: v0 :: Vint32 i4 :: nil|);;
                   SCHED;;
                   asrt_and_ret
                   (|Vint32 i4 :: V$ OS_NO_ERR :: nil|)}
                  else {Aif (fun O : osabst =>
                             task_notrdy_or_idle O
                               (Vptr x6) v0)
                        {ASSERT (fun _ : osabst => False)}
                        else {Aif (
                              fun O : osabst =>
                              exists qid qls ml n pwl wl,
                              Vptr x6 = Vptr qid /\
                              v0 <> Vnull /\
                              get O absecblsid =
                              Some (absecblist qls) /\
                              get qls qid =
                              Some (absmsgq ml n pwl, wl) /\
                              Z.of_nat (length ml) >=
                              Int.unsigned n)
                              {qtimedpost_ovf_block_body
                               (|
                               Vptr x6
                               :: 
                               v0 :: Vint32 i4 :: nil|);;
                               sched
                                (
                                mqdes_dom_qptr i0
                                (Vptr x6), nil);;
                               (mqdes_dom_qptr i0
                                (Vptr x6), nil)
                               # qtimedpost_after_sched
                               [|
                               Vptr x6
                               :: 
                               v0 :: Vint32 i4 :: nil|];;
                               (Aif | 
                                (
                                mqdes_dom_qptr i0
                                (Vptr x6), nil)
                                | (
                                fun O : osabst =>
                                exists qid pr t tls p m
                                sus,
                                Vptr x6 = Vptr qid /\
                                v0 <> Vnull /\
                                get O curtid =
                                Some (oscurt t) /\
                                get O abtcblsid =
                                Some (abstcblist tls) /\
                                get tls t =
                                Some
                                (p,
                                wait 
                                (os_stat_postq qid) None,
                                m, sus, pr))
                                {
                                qtimedpost_timeout_err_body
                                (|
                                Vptr x6
                                :: 
                                v0 :: Vint32 i4 :: nil|)}
                                else {
                                Aif (
                                fun O : osabst =>
                                exists qid t tls p st m
                                sus pr,
                                Vptr x6 = Vptr qid /\
                                v0 <> Vnull /\
                                get O curtid =
                                Some (oscurt t) /\
                                get O abtcblsid =
                                Some (abstcblist tls) /\
                                get tls t =
                                Some (p, st, m, sus, pr) /\
                                st = rdy /\ sus = false)
                                {
                                asrt_and_ret
                                (|
                                Vint32 i4
                                :: 
                                V$ OS_NO_ERR :: nil|)}
                                else {ASSUME 
                                (fun _ : osabst => False)}})}
                              else {
                              Aif (
                              fun O : osabst =>
                              exists qls qid ml n pwl,
                              Vptr x6 = Vptr qid /\
                              v0 <> Vnull /\
                              get O absecblsid =
                              Some (absecblist qls) /\
                              get qls qid =
                              Some (absmsgq ml n pwl, nil) /\
                              Z.of_nat (length ml) <
                              Int.unsigned n)
                              {qpost_nowt_succ_body
                               (|
                               Vptr x6
                               :: 
                               v0 :: Vint32 i4 :: nil|)}
                              else {ASSUME 
                              (fun _ : osabst => False)}}}}}}});;
mqsend_res i4) as cd.
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
exists mq_send.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold mqsendapi. eauto.

(*ks0 = kevent*)
intros. subst.
unfolds in Hgdks.
destruct Hgdks as (Hgdel & Hgdks).
unfolds in Hgdel.
unfolds in Hgdel.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists mq_send.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold mqsendapi. eauto.


(*qtimedpost_ovf_block_body*)
solve_endabt.

(*qtimedpost_nowt_succ_body*)
solve_endabt.

(*n=11*)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 12 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 13 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 14 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(*n=15*)
destruct n; [ my_succs_solver_same_absdata | idtac].

(*qtimedpost_timeout_err_body*)
inverts H3; simpljoin.
destruct H14 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.

assert (get O curtid = Some (oscurt x9)) as Hct.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x14)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x10)) as Htcb.
eapply join_get_get_l;eauto.

assert (O'= set
           (set O abtcblsid
              (abstcblist (set x10 x9 (x11, rdy, Vnull, false, x20))))
           absecblsid
           (absecblist (set x14 x (absmsgq x18 x17 (remove_tid x9 x16), x19)))).
eapply join_get_set_eq_2;eauto.
clear H2 H6 H3.
remember O as Ox.
clear HeqOx.
unfolds; intros.
rewrite Htcb in H17; inverts H17.
rewrite Hct in H16; inverts H16.
rewrite Hct in Hctid; inverts Hctid.
subst.
assert(Hneq: pr0 <> pr) by (eapply dom_for_prio_neq in Hi_neq; eauto).
rewrite H18 in H4; inverts H4.
 assert(t1 = t2).
{ clear -Hecb Htcb Htpi H2 H3 H8 H9 Hneq H18.
   unfolds in H2. unfolds in H3. unfolds in Htpi. simpljoin.
   rewrite set_a_get_a' in H; try intro; tryfalse; eauto.
   rewrite set_a_get_a in H; auto.
   inverts H.
   rewrite Htcb in H0; inverts H0.
   rewrite Htcb in H1; inverts H1.
   rewrite H4 in H18; inverts H18. 
   casetac t t2 He Hn;
   subst.
   rewrite set_a_get_a in H2; inverts H2; tryfalse.
   rewrite set_a_get_a' in H2; eauto.
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
lets Hgdcode: Hgdtk Ht2.
unfolds in Hgdcode. simpl in Hgdcode.
destruct Hgdcode as (Hgde & Hgdks).
unfolds in Hgde.

remember ((Aif | (mqdes_dom_qptr i0 (Vptr x), nil)
| (fun O : osabst =>
   exists qid pr t tls p m sus,
   Vptr x = Vptr qid /\
   v0 <> Vnull /\
   get O curtid = Some (oscurt t) /\
   get O abtcblsid = Some (abstcblist tls) /\
   get tls t =
   Some (p, wait (os_stat_postq qid) None, m, sus, pr))
{qtimedpost_timeout_err_body
 (|Vptr x :: v0 :: Vint32 i4 :: nil|)}
else {Aif (fun O : osabst =>
           exists qid t tls p st m sus pr,
           Vptr x = Vptr qid /\
           v0 <> Vnull /\
           get O curtid = Some (oscurt t) /\
           get O abtcblsid = Some (abstcblist tls) /\
           get tls t = Some (p, st, m, sus, pr) /\
           st = rdy /\ sus = false)
      {asrt_and_ret (|Vint32 i4 :: V$ OS_NO_ERR :: nil|)}
      else {ASSUME (fun _ : osabst => False)}});;
mqsend_res i4) as cd.
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
exists mq_send.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold mqsendapi. eauto.

(*ks0 = kevent*)
intros. subst.
unfolds in Hgdks.
destruct Hgdks as (Hgdel & Hgdks).
unfolds in Hgdel.
unfolds in Hgdel.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists mq_send.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold mqsendapi. eauto.

(*qtimedpost_timeout_err_body*)
solve_endabt.

(* n = 17 *) 
destruct n; [ my_succs_solver_same_absdata | idtac]. 

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

remember ((Aif | (mqdes_dom_qptr i0 (Vptr x3), nil)
| (fun _ : osabst => Vptr x3 = Vnull)
{asrt_and_ret
 (|Vint32 i4 :: V$ OS_ERR_PEVENT_NULL :: nil|)}
else {Aif (fun _ : osabst =>
           exists qid, Vptr x3 = Vptr qid /\ v0 = Vnull)
      {asrt_and_ret
       (|Vint32 i4 :: V$ OS_ERR_POST_NULL_PTR :: nil|)}
      else {Aif (fun O : osabst =>
                 exists qid els,
                 Vptr x3 = Vptr qid /\
                 v0 <> Vnull /\
                 get O absecblsid = Some (absecblist els) /\
                 ~
                 (exists x y pwl wls,
                  get els qid =
                  Some (absmsgq x y pwl, wls)))
            {asrt_and_ret
             (|Vint32 i4 :: V$ OS_ERR_EVENT_TYPE :: nil|)}
            else {Aif (fun O : osabst =>
                       exists qid qls ml n pwl wl,
                       Vptr x3 = Vptr qid /\
                       v0 <> Vnull /\
                       get O absecblsid =
                       Some (absecblist qls) /\
                       get qls qid =
                       Some (absmsgq ml n pwl, wl) /\
                       Z.of_nat (length ml) >=
                       Int.unsigned n)
                  {asrt_and_ret
                   (|Vint32 i4 :: V$ MSGQ_OVF_ERR :: nil|)}
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
                         (|Vptr x3
                           :: v0 :: Vint32 i4 :: nil|)}
                        else {Aif (
                              fun O : osabst =>
                              exists qid els,
                              Vptr x3 = Vptr qid /\
                              v0 <> Vnull /\
                              get O absecblsid =
                              Some (absecblist els) /\
                              (exists x y pwl wls,
                               get els qid =
                               Some (absmsgq x y pwl, wls) /\
                               wls <> nil))
                              {qpost_exwt_succ_body
                               (|
                               Vptr x3
                               :: 
                               v0 :: Vint32 i4 :: nil|);;
                               SCHED;;
                               asrt_and_ret
                               (|
                               Vint32 i4
                               :: 
                               V$ OS_NO_ERR :: nil|)}
                              else {ASSUME 
                              (fun _ : osabst => False)}}}}}});;
mqsend_res i4) as cd.
clear Heqcd.

intros.
lets Hgdcode: Hgdtk H1.
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
exists mq_send.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold mqsendapi. eauto.
(*ks0 = kevent*)
intros. subst.
unfolds in Hgdks.
destruct Hgdks as (Hgdel & Hgdks).
unfolds in Hgdel.
unfolds in Hgdel.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists mq_send.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold mqsendapi. eauto.

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
lets Hgdcode: Hgdtk Ht2.
unfolds in Hgdcode. simpl in Hgdcode.
destruct Hgdcode as (Hgde & Hgdks).
unfolds in Hgde.

remember ((Aif | (mqdes_dom_qptr i0 (Vptr x2), nil)
| (fun _ : osabst => Vptr x2 = Vnull)
{asrt_and_ret
 (|Vint32 i4 :: V$ OS_ERR_PEVENT_NULL :: nil|)}
else {Aif (fun _ : osabst =>
           exists qid, Vptr x2 = Vptr qid /\ v0 = Vnull)
      {asrt_and_ret
       (|Vint32 i4 :: V$ OS_ERR_POST_NULL_PTR :: nil|)}
      else {Aif (fun O : osabst =>
                 exists qid els,
                 Vptr x2 = Vptr qid /\
                 v0 <> Vnull /\
                 get O absecblsid = Some (absecblist els) /\
                 ~
                 (exists x y pwl wls,
                  get els qid =
                  Some (absmsgq x y pwl, wls)))
            {asrt_and_ret
             (|Vint32 i4 :: V$ OS_ERR_EVENT_TYPE :: nil|)}
            else {Aif (fun O : osabst =>
                       exists qid qls ml n pwl wl,
                       Vptr x2 = Vptr qid /\
                       v0 <> Vnull /\
                       get O absecblsid =
                       Some (absecblist qls) /\
                       get qls qid =
                       Some (absmsgq ml n pwl, wl) /\
                       Z.of_nat (length ml) >=
                       Int.unsigned n)
                  {asrt_and_ret
                   (|Vint32 i4 :: V$ MSGQ_OVF_ERR :: nil|)}
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
                         (|Vptr x2
                           :: v0 :: Vint32 i4 :: nil|)}
                        else {Aif (
                              fun O : osabst =>
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
                               (|
                               Vptr x2
                               :: 
                               v0 :: Vint32 i4 :: nil|);;
                               SCHED;;
                               asrt_and_ret
                               (|
                               Vint32 i4
                               :: 
                               V$ OS_NO_ERR :: nil|)}
                              else {ASSUME 
                              (fun _ : osabst => False)}}}}}});;
mqsend_res i4) as cd.
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
exists mq_send.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold mqsendapi. eauto.
(*ks0 = kevent*)
intros. subst.
unfolds in Hgdks.
destruct Hgdks as (Hgdel & Hgdks).
unfolds in Hgdel.
unfolds in Hgdel.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists mq_send.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold mqsendapi. eauto.

(* qpost_exwt_succ_body *)
solve_endabt.

(* n = 18 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 19 *) 
destruct n; [ my_succs_solver_same_absdata | idtac]. 

destruct n; [ my_succs_solver_same_absdata | idtac].
destruct n; [ my_succs_solver_same_absdata | idtac].  

re_err_contra n; try my_succs_solver_same_absdata.
tryfalse.
tryfalse.
Qed.

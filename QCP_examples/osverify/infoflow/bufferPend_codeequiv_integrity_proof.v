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

Lemma bufferpend_nabt_spec_step_code_equiv_tskd'_preserve :
forall O cd  n vl sd cd' O' act ke ks t T i pr,
good_task_code T->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
get T t = Some (curs (hapi_code cd), (ke, ks)) ->
bufferpend vl <> ABORT -> 
nth_error (get_all_succs (bufferpend vl)) n = Some cd ->
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
lets Hgdcd: Hgtc Hgett.
unfolds in Hgdcd. simpl in Hgdcd.
destruct Hgdcd as (Hgde' & Hgdks').
lets Hstep1: Hstep.
protect Hstep1.
destruct n; [ my_succs_solver_same_absdata | idtac].
(*qpend_get_no_pwl_succ_body*)
inverts H3; simpljoin.
destruct H15 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.

assert (get O curtid = Some (oscurt x7)) as Hcur.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x8)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x9)) as Htcb.
eapply join_get_get_l;eauto.

assert (H6:O'=set O absecblsid
(absecblist (set x8 x (absmsgq x11 x12 nil, x13)))).
eapply join_get_set_eq;eauto.
clear H1 H2 H3.
remember O as Ox.
clear HeqOx.
unfolds; intros.
lets Hm:tid_unique_set_ntls H1 H2 H6; eauto.
destruct Hm; auto.
intro; tryfalse.
subst i.

assert(Hnpr: pr <> pr0).
clear -Hi_neq.
unfold dom_for_prio in Hi_neq.
intro; subst.
eapply Hi_neq; auto.
splits; auto.
lets Htneq: task_prio_id_tidneq Htpi H1 Hnpr; auto.
unfold get, set in *;simpl in *.
rewrite TasksMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto];auto.

remember ((Aif | (buffer_indom (Vptr x1), nil)
| (fun _ : osabst =>
   Vptr x1 = Vnull \/ (exists qid, Vptr x1 = Vptr qid))
{Aif (fun _ : osabst => Vptr x1 = Vnull)
 {asrt_and_ret (|v1 :: Vnull :: nil|)}
 else {Aif (fun O : osabst =>
            exists qls qid,
            Vptr x1 = Vptr qid /\
            get O absecblsid = Some (absecblist qls) /\
            ~
            (exists x y pwls wls,
             get qls qid = Some (absmsgq x y pwls, wls)))
       {asrt_and_ret (|v1 :: Vnull :: nil|)}
       else {Aif (fun O : osabst =>
                  exists tls st msg0 sus t pr,
                  get O curtid = Some (oscurt t) /\
                  get O abtcblsid = Some (abstcblist tls) /\
                  get tls t =
                  Some ($ OS_IDLE_PRIO, st, msg0, sus, pr))
             {ASSERT (fun _ : osabst => False)}
             else {Aif (fun O : osabst =>
                        exists tls prio st msg0 sus t pr,
                        get O curtid = Some (oscurt t) /\
                        get O abtcblsid =
                        Some (abstcblist tls) /\
                        get tls t =
                        Some (prio, st, msg0, sus, pr) /\
                        ~ (st = rdy /\ sus = false))
                   {ASSERT (fun _ : osabst => False)}
                   else {Aif (fun O : osabst =>
                              exists qid qls msg0 ml n wl,
                              Vptr x1 = Vptr qid /\
                              get O absecblsid =
                              Some (absecblist qls) /\
                              get qls qid =
                              Some
                                (absmsgq (msg0 :: ml) n nil,
                                wl))
                         {qpend_get_no_pwl_succ_body
                          (|Vptr x1 :: v1 :: nil|)}
                         else {Aif (
                               fun O : osabst =>
                               exists qid qls msg0 ml n pwl
                               wl,
                               Vptr x1 = Vptr qid /\
                               get O absecblsid =
                               Some (absecblist qls) /\
                               get qls qid =
                               Some
                                 (absmsgq (msg0 :: ml) n pwl,
                                 wl) /\ 
                               pwl <> nil)
                               {qpend_get_ex_pwl_before_sched_body
                                (|Vptr x1 :: v1 :: nil|);;
                                sched
                                  (
                                  fun 
                                  (_ : osabst)
                                  (_ : priority) => True,
                                  v1 :: nil);;
                                (fun 
                                  (_ : osabst)
                                  (_ : priority) => True,
                                v1 :: nil) # ret_val
                                [|v1 :: nil|]}
                               else {
                               Aif (
                               fun O : osabst =>
                               exists qid qls wl n pwl,
                               Vptr x1 = Vptr qid /\
                               get O absecblsid =
                               Some (absecblist qls) /\
                               get qls qid =
                               Some (absmsgq nil n pwl, wl))
                               {qpend_block_body
                                (|Vptr x1
                                  :: 
                                  Vint32 i0 :: nil|);;
                                sched
                                  (
                                  buffer_indom (Vptr x1),
                                  nil);;
                                (buffer_indom (Vptr x1),
                                nil) # qpend_assm_stat
                                [|Vptr x1 :: nil|];;
                                (Aif | 
                                 (buffer_indom (Vptr x1),
                                 nil)
                                 | (
                                 fun O : osabst =>
                                 exists tls prio t qid sus
                                 pr,
                                 Vptr x1 = Vptr qid /\
                                 get O curtid =
                                 Some (oscurt t) /\
                                 get O abtcblsid =
                                 Some (abstcblist tls) /\
                                 get tls t =
                                 Some
                                  (prio,
                                  wait 
                                  (os_stat_q qid)
                                  (Some Int.zero), Vnull,
                                  sus, pr))
                                 {qpend_to_body
                                  (|
                                  Vptr x1 :: v1 :: nil|);;
                                  (
                                  fun 
                                  (_ : osabst)
                                  (_ : priority) => True,
                                  v1 :: nil) # asrt_and_ret
                                  [|
                                  v1 :: Vnull :: nil|]}
                                 else {
                                 Aif (
                                 fun O : osabst =>
                                 exists tls p st m sus t pr,
                                 get O curtid =
                                 Some (oscurt t) /\
                                 get O abtcblsid =
                                 Some (abstcblist tls) /\
                                 get tls t =
                                 Some (p, st, m, sus, pr) /\
                                 m <> Vnull)
                                 {qpend_block_get_body
                                  (|
                                  Vptr x1 :: v1 :: nil|)}
                                 else {ASSUME 
                                 (fun _ : osabst => False)}})}
                               else {ASSUME 
                               (fun _ : osabst => False)}}}}}}}}
else {ASSUME (fun _ : osabst => False)});;
(fun (_ : osabst) (_ : priority) => True, v1 :: nil)
# ret_val [|v1 :: nil|]) as cd.
clear Heqcd.

intros.
lets Hgdcode: Hgtc H0.
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
exists buffer_pend.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold bufferpendapi. eauto.

(*ks0 = kevent*)
intros. subst.
unfolds in Hgdks.
destruct Hgdks as (Hgdel & Hgdks).
unfolds in Hgdel.
unfolds in Hgdel.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists buffer_pend.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold bufferpendapi. eauto.
(* ====== *)
solve_endabt.

(* qpend_get_ex_pwl_before_sched_body *)
inverts H3; simpljoin.
destruct H21 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.

assert (get O absecblsid = Some (absecblist x8)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x9)) as Htcb.
eapply join_get_get_l;eauto.

assert (O'=set
(set O abtcblsid
   (abstcblist (set x9 x19 (x15, rdy, x18, x20, x22)))) absecblsid
(absecblist
   (set x8 x
      (absmsgq (x11 ++ x18 :: nil) x12 (remove_tid x19 x13), x14)))).
eapply join_get_set_eq_2;eauto.
clear H1 H2.
subst.

unfolds; intros.
casetac pr pr0 Heq Hp_neq.
subst.
tryfalse.

assert(t1 = t2).
{ 
  clear - Hecb Htcb H2 H1 Hp_neq H3 H8 H6.
  unfolds in H2. unfolds in H1; simpljoin.
  rewrite Htcb in H0; inverts H0.
  unfolds in H6; simpljoin.
  rewrite H4 in H8; inverts H8.
  rewrite set_a_get_a' in H; try intro; tryfalse; eauto.
  rewrite set_a_get_a in H.
  inverts H.
  casetac x19 t2 He Hne; subst;
  [ rewrite set_a_get_a in H1; inverts H1 |
  rewrite set_a_get_a' in H1; eauto ];
  eapply tid_unique;
  unfolds; do 5 eexists; eauto. 
  }
    subst.
lets Hn: task_prio_id_tidneq Htpi H1 Hp_neq.
rewrite set_a_get_a' ; eauto.
split;eauto. 
remember ((Aif | (buffer_indom (Vptr x1), nil)
| (fun _ : osabst =>
   Vptr x1 = Vnull \/ (exists qid, Vptr x1 = Vptr qid))
{Aif (fun _ : osabst => Vptr x1 = Vnull)
 {asrt_and_ret (|v1 :: Vnull :: nil|)}
 else {Aif (fun O : osabst =>
            exists qls qid,
            Vptr x1 = Vptr qid /\
            get O absecblsid = Some (absecblist qls) /\
            ~
            (exists x y pwls wls,
             get qls qid = Some (absmsgq x y pwls, wls)))
       {asrt_and_ret (|v1 :: Vnull :: nil|)}
       else {Aif (fun O : osabst =>
                  exists tls st msg0 sus t pr,
                  get O curtid = Some (oscurt t) /\
                  get O abtcblsid = Some (abstcblist tls) /\
                  get tls t =
                  Some ($ OS_IDLE_PRIO, st, msg0, sus, pr))
             {ASSERT (fun _ : osabst => False)}
             else {Aif (fun O : osabst =>
                        exists tls prio st msg0 sus t pr,
                        get O curtid = Some (oscurt t) /\
                        get O abtcblsid =
                        Some (abstcblist tls) /\
                        get tls t =
                        Some (prio, st, msg0, sus, pr) /\
                        ~ (st = rdy /\ sus = false))
                   {ASSERT (fun _ : osabst => False)}
                   else {Aif (fun O : osabst =>
                              exists qid qls msg0 ml n wl,
                              Vptr x1 = Vptr qid /\
                              get O absecblsid =
                              Some (absecblist qls) /\
                              get qls qid =
                              Some
                                (absmsgq (msg0 :: ml) n nil,
                                wl))
                         {qpend_get_no_pwl_succ_body
                          (|Vptr x1 :: v1 :: nil|)}
                         else {Aif (
                               fun O : osabst =>
                               exists qid qls msg0 ml n pwl
                               wl,
                               Vptr x1 = Vptr qid /\
                               get O absecblsid =
                               Some (absecblist qls) /\
                               get qls qid =
                               Some
                                 (absmsgq (msg0 :: ml) n pwl,
                                 wl) /\ 
                               pwl <> nil)
                               {qpend_get_ex_pwl_before_sched_body
                                (|Vptr x1 :: v1 :: nil|);;
                                sched
                                  (
                                  fun 
                                  (_ : osabst)
                                  (_ : priority) => True,
                                  v1 :: nil);;
                                (fun 
                                  (_ : osabst)
                                  (_ : priority) => True,
                                v1 :: nil) # ret_val
                                [|v1 :: nil|]}
                               else {
                               Aif (
                               fun O : osabst =>
                               exists qid qls wl n pwl,
                               Vptr x1 = Vptr qid /\
                               get O absecblsid =
                               Some (absecblist qls) /\
                               get qls qid =
                               Some (absmsgq nil n pwl, wl))
                               {qpend_block_body
                                (|Vptr x1
                                  :: 
                                  Vint32 i0 :: nil|);;
                                sched
                                  (
                                  buffer_indom (Vptr x1),
                                  nil);;
                                (buffer_indom (Vptr x1),
                                nil) # qpend_assm_stat
                                [|Vptr x1 :: nil|];;
                                (Aif | 
                                 (buffer_indom (Vptr x1),
                                 nil)
                                 | (
                                 fun O : osabst =>
                                 exists tls prio t qid sus
                                 pr,
                                 Vptr x1 = Vptr qid /\
                                 get O curtid =
                                 Some (oscurt t) /\
                                 get O abtcblsid =
                                 Some (abstcblist tls) /\
                                 get tls t =
                                 Some
                                  (prio,
                                  wait 
                                  (os_stat_q qid)
                                  (Some Int.zero), Vnull,
                                  sus, pr))
                                 {qpend_to_body
                                  (|
                                  Vptr x1 :: v1 :: nil|);;
                                  (
                                  fun 
                                  (_ : osabst)
                                  (_ : priority) => True,
                                  v1 :: nil) # asrt_and_ret
                                  [|
                                  v1 :: Vnull :: nil|]}
                                 else {
                                 Aif (
                                 fun O : osabst =>
                                 exists tls p st m sus t pr,
                                 get O curtid =
                                 Some (oscurt t) /\
                                 get O abtcblsid =
                                 Some (abstcblist tls) /\
                                 get tls t =
                                 Some (p, st, m, sus, pr) /\
                                 m <> Vnull)
                                 {qpend_block_get_body
                                  (|
                                  Vptr x1 :: v1 :: nil|)}
                                 else {ASSUME 
                                 (fun _ : osabst => False)}})}
                               else {ASSUME 
                               (fun _ : osabst => False)}}}}}}}}
else {ASSUME (fun _ : osabst => False)});;
(fun (_ : osabst) (_ : priority) => True, v1 :: nil)
# ret_val [|v1 :: nil|]) as cd.
clear Heqcd.
intros.
lets Hgdcode: Hgtc H0.
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
exists buffer_pend.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold bufferpendapi. eauto.

intros. subst.
unfolds in Hgdks.
destruct Hgdks as (Hgdel & Hgdks).
unfolds in Hgdel.
unfolds in Hgdel.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists buffer_pend.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold bufferpendapi. eauto.

(* qpend_get_ex_pwl_before_sched_body *)
solve_endabt.

(* qpend_block_body *)
inverts H3; simpljoin.
inverts H19.

assert (get O curtid = Some (oscurt x16)) as Hcur.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x10)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x8)) as Htcb.
eapply join_get_get_l;eauto.

assert (O'=set
(set O abtcblsid
   (abstcblist
      (set x8 x16 (x13, wait (os_stat_q x) x17, x1, x2, x19))))
absecblsid
(absecblist (set x10 x (absmsgq nil x15 x18, x16 :: x12)))).
eapply join_get_set_eq_2;eauto.
clear H1 H2 H6.
subst.

unfolds; intros.
casetac pr pr0 Heq Hp_neq.
subst.
tryfalse.
assert(t1 = t2).
{ 
  clear - Hcur Hecb Htcb H2 H1 Hp_neq H3 H8 .
  unfolds in H2. unfolds in H1; simpljoin.
  rewrite Htcb in H0; inverts H0.

  rewrite set_a_get_a' in H; try intro; tryfalse; eauto.
  rewrite set_a_get_a in H.
  inverts H.
  casetac x16 t2 He Hne; subst;
  [ rewrite set_a_get_a in H1; inverts H1 |
  rewrite set_a_get_a' in H1; eauto ];
  eapply tid_unique;
  unfolds; do 5 eexists; eauto. 
  }
    subst.
lets Hn: task_prio_id_tidneq Htpi H1 Hp_neq.
rewrite set_a_get_a' ; eauto.
split;eauto. 
remember ((Aif | (buffer_indom (Vptr x3), nil)
| (fun _ : osabst =>
   Vptr x3 = Vnull \/ (exists qid, Vptr x3 = Vptr qid))
{Aif (fun _ : osabst => Vptr x3 = Vnull)
 {asrt_and_ret (|v1 :: Vnull :: nil|)}
 else {Aif (fun O : osabst =>
            exists qls qid,
            Vptr x3 = Vptr qid /\
            get O absecblsid = Some (absecblist qls) /\
            ~
            (exists x y pwls wls,
             get qls qid = Some (absmsgq x y pwls, wls)))
       {asrt_and_ret (|v1 :: Vnull :: nil|)}
       else {Aif (fun O : osabst =>
                  exists tls st msg0 sus t pr,
                  get O curtid = Some (oscurt t) /\
                  get O abtcblsid = Some (abstcblist tls) /\
                  get tls t =
                  Some ($ OS_IDLE_PRIO, st, msg0, sus, pr))
             {ASSERT (fun _ : osabst => False)}
             else {Aif (fun O : osabst =>
                        exists tls prio st msg0 sus t pr,
                        get O curtid = Some (oscurt t) /\
                        get O abtcblsid =
                        Some (abstcblist tls) /\
                        get tls t =
                        Some (prio, st, msg0, sus, pr) /\
                        ~ (st = rdy /\ sus = false))
                   {ASSERT (fun _ : osabst => False)}
                   else {Aif (fun O : osabst =>
                              exists qid qls msg0 ml n wl,
                              Vptr x3 = Vptr qid /\
                              get O absecblsid =
                              Some (absecblist qls) /\
                              get qls qid =
                              Some
                                (absmsgq (msg0 :: ml) n nil,
                                wl))
                         {qpend_get_no_pwl_succ_body
                          (|Vptr x3 :: v1 :: nil|)}
                         else {Aif (
                               fun O : osabst =>
                               exists qid qls msg0 ml n pwl
                               wl,
                               Vptr x3 = Vptr qid /\
                               get O absecblsid =
                               Some (absecblist qls) /\
                               get qls qid =
                               Some
                                 (absmsgq (msg0 :: ml) n pwl,
                                 wl) /\ 
                               pwl <> nil)
                               {qpend_get_ex_pwl_before_sched_body
                                (|Vptr x3 :: v1 :: nil|);;
                                sched
                                  (
                                  fun 
                                  (_ : osabst)
                                  (_ : priority) => True,
                                  v1 :: nil);;
                                (fun 
                                  (_ : osabst)
                                  (_ : priority) => True,
                                v1 :: nil) # ret_val
                                [|v1 :: nil|]}
                               else {
                               Aif (
                               fun O : osabst =>
                               exists qid qls wl n pwl,
                               Vptr x3 = Vptr qid /\
                               get O absecblsid =
                               Some (absecblist qls) /\
                               get qls qid =
                               Some (absmsgq nil n pwl, wl))
                               {qpend_block_body
                                (|Vptr x3
                                  :: 
                                  Vint32 i0 :: nil|);;
                                sched
                                  (
                                  buffer_indom (Vptr x3),
                                  nil);;
                                (buffer_indom (Vptr x3),
                                nil) # qpend_assm_stat
                                [|Vptr x3 :: nil|];;
                                (Aif | 
                                 (buffer_indom (Vptr x3),
                                 nil)
                                 | (
                                 fun O : osabst =>
                                 exists tls prio t qid sus
                                 pr,
                                 Vptr x3 = Vptr qid /\
                                 get O curtid =
                                 Some (oscurt t) /\
                                 get O abtcblsid =
                                 Some (abstcblist tls) /\
                                 get tls t =
                                 Some
                                  (prio,
                                  wait 
                                  (os_stat_q qid)
                                  (Some Int.zero), Vnull,
                                  sus, pr))
                                 {qpend_to_body
                                  (|
                                  Vptr x3 :: v1 :: nil|);;
                                  (
                                  fun 
                                  (_ : osabst)
                                  (_ : priority) => True,
                                  v1 :: nil) # asrt_and_ret
                                  [|
                                  v1 :: Vnull :: nil|]}
                                 else {
                                 Aif (
                                 fun O : osabst =>
                                 exists tls p st m sus t pr,
                                 get O curtid =
                                 Some (oscurt t) /\
                                 get O abtcblsid =
                                 Some (abstcblist tls) /\
                                 get tls t =
                                 Some (p, st, m, sus, pr) /\
                                 m <> Vnull)
                                 {qpend_block_get_body
                                  (|
                                  Vptr x3 :: v1 :: nil|)}
                                 else {ASSUME 
                                 (fun _ : osabst => False)}})}
                               else {ASSUME 
                               (fun _ : osabst => False)}}}}}}}}
else {ASSUME (fun _ : osabst => False)});;
(fun (_ : osabst) (_ : priority) => True, v1 :: nil)
# ret_val [|v1 :: nil|]) as cd.
clear Heqcd.

intros.
lets Hgdcode: Hgtc H0.
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
exists buffer_pend.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold bufferpendapi. eauto.
intros. subst.
unfolds in Hgdks.
destruct Hgdks as (Hgdel & Hgdks).
unfolds in Hgdel.
unfolds in Hgdel.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists buffer_pend.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold bufferpendapi. eauto.

(* qpend_block_body  *)
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
(* qpend_block_get_body *)
inverts H3; simpljoin.
destruct H10 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.

assert (get O curtid = Some (oscurt x13)) as Hcur.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x8)) as Htcb.
eapply join_get_get_l;eauto.

assert (O'=set O abtcblsid
(abstcblist (set x8 x13 (x9, rdy, Vnull, false, x15)))).
eapply join_get_set_eq;eauto.
clear H1 H2.
subst.

unfolds; intros.
casetac pr pr0 Heq Hp_neq.
subst.
tryfalse.

assert(Heqt: t1 = t2).
{
  rewrite Hcur in H0; inverts H0.
  rewrite Htcb in H11; inverts H11.
  rewrite H3 in H12; inverts H12.
  eapply tid_unique; eauto.
  unfolds in H4.
  simpljoin.
  rewrite set_a_get_a in H0; eauto.
  inverts H0.
  casetac x6 t2 Hy Hn.
  subst.
  rewrite set_a_get_a in H4; eauto.
  inverts H4.
  unfolds.
  do 5 eexists.
  split;eauto.
  rewrite set_a_get_a' in H4; eauto.
  unfolds.
  do 5 eexists.
  split;eauto.
}
subst.
lets Hn: task_prio_id_tidneq Htpi H2 Hp_neq.
rewrite set_a_get_a' ; eauto.
split;eauto. 
remember ((Aif | (buffer_indom v, nil)
| (fun O : osabst =>
   exists tls prio t qid sus pr,
   v = Vptr qid /\
   get O curtid = Some (oscurt t) /\
   get O abtcblsid = Some (abstcblist tls) /\
   get tls t =
   Some
     (prio, wait (os_stat_q qid) (Some Int.zero), Vnull,
     sus, pr))
{qpend_to_body (|v :: v1 :: nil|);;
 (fun (_ : osabst) (_ : priority) => True, v1 :: nil)
 # asrt_and_ret [|v1 :: Vnull :: nil|]}
else {Aif (fun O : osabst =>
           exists tls p st m sus t pr,
           get O curtid = Some (oscurt t) /\
           get O abtcblsid = Some (abstcblist tls) /\
           get tls t = Some (p, st, m, sus, pr) /\
           m <> Vnull)
      {qpend_block_get_body (|v :: v1 :: nil|)}
      else {ASSUME (fun _ : osabst => False)}});;
(fun (_ : osabst) (_ : priority) => True, v1 :: nil)
# ret_val [|v1 :: nil|]) as cd.

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
exists buffer_pend.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold bufferpendapi. eauto.

intros. subst.
unfolds in Hgdks.
destruct Hgdks as (Hgdel & Hgdks).
unfolds in Hgdel.
unfolds in Hgdel.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists buffer_pend.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold bufferpendapi. eauto.

(* qpend_to_body *)
inverts H3; simpljoin.
destruct H12 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.
assert (get O curtid = Some (oscurt x9)) as Hcur.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x10)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x7)) as Htcb.
eapply join_get_get_l;eauto.
assert (O'=set
(set O abtcblsid
   (abstcblist (set x7 x9 (x8, rdy, Vnull, false, x17))))
absecblsid
(absecblist
   (set x10 x (absmsgq x12 x13 x14, remove_tid x9 x15)))).
eapply join_get_set_eq_2;eauto.
clear H1 H2 H4.
subst.
unfolds; intros.
casetac pr pr0 Heq Hp_neq.
subst.
tryfalse.
assert(t1 = t2).
{ 
  clear - Hcur Hecb Htcb H2 H1 H3 H6 H15 H16 H17 .
  unfolds in H2; unfolds in H1; simpljoin.
  rewrite Htcb in H0; inverts H0.
  rewrite Htcb in H16; inverts H16.
  rewrite Hcur in H15; inverts H15.
  rewrite H17 in H3; inverts H3.

  rewrite set_a_get_a' in H; try intro; tryfalse; eauto.
  rewrite set_a_get_a in H.
  inverts H.

  casetac x3 t2 He Hne; subst;
  [ rewrite set_a_get_a in H1; inverts H1 |
  rewrite set_a_get_a' in H1; eauto ];
  eapply tid_unique;
  unfolds; do 5 eexists; eauto. 
  }
    subst.
lets Hn: task_prio_id_tidneq Htpi H1 Hp_neq.
rewrite set_a_get_a' ; eauto.
split;eauto. 
remember ((Aif | (buffer_indom (Vptr x4), nil)
| (fun O : osabst =>
   exists tls prio t qid sus pr,
   Vptr x4 = Vptr qid /\
   get O curtid = Some (oscurt t) /\
   get O abtcblsid = Some (abstcblist tls) /\
   get tls t =
   Some
     (prio, wait (os_stat_q qid) (Some Int.zero), Vnull,
     sus, pr))
{qpend_to_body (|Vptr x4 :: v1 :: nil|);;
 (fun (_ : osabst) (_ : priority) => True, v1 :: nil)
 # asrt_and_ret [|v1 :: Vnull :: nil|]}
else {Aif (fun O : osabst =>
           exists tls p st m sus t pr,
           get O curtid = Some (oscurt t) /\
           get O abtcblsid = Some (abstcblist tls) /\
           get tls t = Some (p, st, m, sus, pr) /\
           m <> Vnull)
      {qpend_block_get_body (|Vptr x4 :: v1 :: nil|)}
      else {ASSUME (fun _ : osabst => False)}});;
(fun (_ : osabst) (_ : priority) => True, v1 :: nil)
# ret_val [|v1 :: nil|]) as cd.
clear Heqcd.
intros.
lets Hgdcode: Hgtc H0.
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
exists buffer_pend.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold bufferpendapi . eauto.
intros. subst.
unfolds in Hgdks.
destruct Hgdks as (Hgdel & Hgdks).
unfolds in Hgdel.
unfolds in Hgdel.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists buffer_pend.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold bufferpendapi. eauto.

solve_endabt.
solve_endabt.

destruct n; [ my_succs_solver_same_absdata | idtac].
destruct n; [ my_succs_solver_same_absdata | idtac].
destruct n; [ my_succs_solver_same_absdata | idtac].
destruct n; [ my_succs_solver_same_absdata | idtac].
re_err_contra n; try my_succs_solver_same_absdata.
tryfalse.
tryfalse.
Qed.













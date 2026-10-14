
Require Import sem_common.
Require Import OSTimeTickPure.
Require Import OSTimeDlyPure. (* new add *)
Require Import OSQPostPure.
Require Import Mbox_common.

Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

(* new add *)
Lemma struct_type_vallist_match_os_tcb_flag_imp :
  forall vl, struct_type_vallist_match OS_TCB_flag vl ->
            exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10, exists v11, 
            vl = v1 :: v2 :: v3 :: v4 :: Vint32 v5 :: Vint32 v6 :: Vint32 v7 :: Vint32 v8 :: Vint32 v9 :: Vint32 v10 :: Vint32 v11 :: nil
             /\ isptr v1 /\ isptr v2 /\ isptr v3 /\ isptr v4
             /\ Int.unsigned v5 <= 65535 /\ Int.unsigned v6 <= 65535 /\ Int.unsigned v7 <= 255 /\ Int.unsigned v8 <= 255
             /\ Int.unsigned v9 <= 255 /\ Int.unsigned v10 <= 255 /\ Int.unsigned v11 <= 255.
Proof.
  intros.
  unfold OS_TCB_flag in H.
  struct_type_vallist_match_elim.
  repeat eexists; eauto.
Qed.

Lemma struct_type_vallist_match_os_tcb_flag_getdly :
  forall vl, struct_type_vallist_match OS_TCB_flag vl ->
              exists time, V_OSTCBDly vl = Some (Vint32 time) /\ Int.unsigned time <= 65535.
Proof.
  intros.
  apply struct_type_vallist_match_os_tcb_flag_imp in H.
  do 11 destruct H. destruct H. subst vl. destruct H0 as (_ & _ & _ & _ & Ht & _).
  unfold V_OSTCBDly. simpl. eexists. split; auto.
Qed.

Lemma TCBListP_head_in_tcb':
  forall tcbls tcur tcurl tcblist rtbl prio msg,
    TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
    V_OSTCBMsg tcurl = Some msg ->
     exists st sus, TcbMod.get tcbls tcur = Some (prio, st, msg, sus).
Proof.
intros.
funfold H.
fold TCBList_P in H5.
inverts H.
funfold H4.
destruct x2.
destruct p.
destruct p.
 mytac.
unfold V_OSTCBPrio, V_OSTCBMsg in *.
rewrite H in H7. inverts H7.
rewrite H0 in H6. inverts H6.
unfold TcbJoin in H3.
unfold join in H3; unfold sig in H3; simpl in H3.
do 2 eexists.
eapply TcbMod.join_get_l.
eauto.
eapply TcbMod.get_a_sig_a.
apply CltEnvMod.beq_refl.
Qed.

Lemma low_stat_impl_high_stat_sem
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     prio_not_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBDly tcurl = Some (Vint32 wt) ->
     V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_SEM)) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
    Int.eq wt Int.zero = false -> (* new add *)
     exists msg,
       TcbMod.get tcbls tcur = Some (prio, wait (os_stat_sem sid) (Some wt), msg, false).
Proof.
  introv Ht Hp Hvp Hvt Hvs Hvn Hneq.
  simpl in Ht.
  mytac.
  inverts H.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  apply tcbjoin_get_a in H1.
  destruct H9 as (_ & _ & _ & _ & Hrts & _).
  funfold Hrts.
  funfold H10.
  unfold WaitTCBblk in H10.
  unfold V_OSTCBPrio, V_OSTCBDly, V_OSTCBStat, V_OSTCBEventPtr in H10.
  rewrite H4,H5,H6,H7 in H10.
  rewrite H1.
  assert (exists m0, wt <> Int.zero /\ (p, t, m, s) = (prio, wait (os_stat_sem sid) (Some wt), m0, false) \/
      wt = Int.zero /\ (p, t, m, s) = (prio, wait (os_stat_sem sid) None, m0, false)).
  eapply H10; try auto.
  destruct H.
  destruct H as [ (_ & H) | (Hf & _)].
  rewrite H.
  eauto.
  subst.
  rewrite Int.eq_true in Hneq; tryfalse.
Qed.

(* new add *)
Lemma low_stat_impl_high_stat_sem_sus
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     prio_not_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBDly tcurl = Some (Vint32 wt) ->
     V_OSTCBStat tcurl = Some (Vint32 (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND))) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
    Int.eq wt Int.zero = false ->
     exists msg,
       TcbMod.get tcbls tcur = Some (prio, wait (os_stat_sem sid) (Some wt), msg, true).
Proof.
  introv Ht Hp Hvp Hvt Hvs Hvn Hneq.
  simpl in Ht.
  mytac.
  inverts H.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  apply tcbjoin_get_a in H1.
  destruct H9 as (_ & _ & _ & _ & Hrts & _).
  funfold Hrts.
  funfold H19.
  unfold WaitTCBblk in H19.
  unfold V_OSTCBPrio, V_OSTCBDly, V_OSTCBStat, V_OSTCBEventPtr in H19.
  rewrite H4,H5,H6,H7 in H19.
  rewrite H1.
  assert (exists m0 t_opt, (p, t, m, s) = (prio, wait (os_stat_sem sid) t_opt, m0, true) /\
                                                     (wt = Int.zero /\ (t_opt = Some Int.zero \/ t_opt = None) \/
                                                       wt <> Int.zero /\ t_opt = Some wt)).
  eapply H19; try auto.
  destruct H as (m0 & t_opt & Heq & H).
  inverts Heq.
  destruct H as [ (Hf & _) | (_ & H)].
  subst.
  rewrite Int.eq_true in Hneq; tryfalse.
  rewrite H.
  eauto.
Qed.

(* new add *)
Lemma low_stat_impl_high_stat_sem_zero
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     prio_not_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBDly tcurl = Some (Vint32 wt) ->
     V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_SEM)) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
    Int.eq wt Int.zero = true ->
     exists msg,
       TcbMod.get tcbls tcur = Some (prio, wait (os_stat_sem sid) None, msg, false).
Proof.
  introv Ht Hp Hvp Hvt Hvs Hvn Heq.
  simpl in Ht.
  mytac.
  inverts H.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  apply tcbjoin_get_a in H1.
  destruct H9 as (_ & _ & _ & _ & Hrts & _).
  funfold Hrts.
  funfold H10.
  unfold WaitTCBblk in H10.
  unfold V_OSTCBPrio, V_OSTCBDly, V_OSTCBStat, V_OSTCBEventPtr in H10.
  rewrite H4,H5,H6,H7 in H10.
  rewrite H1.
  assert (exists m0, wt <> Int.zero /\ (p, t, m, s) = (prio, wait (os_stat_sem sid) (Some wt), m0, false) \/
      wt = Int.zero /\ (p, t, m, s) = (prio, wait (os_stat_sem sid) None, m0, false)).
  eapply H10; try auto.
  destruct H.
  destruct H as [ (Hneq & H) | (Hf & H)].
  eapply semacc_int_eq_true in Heq; subst; tryfalse.
  rewrite H.
  eauto.
Qed.

(* new add *)
Lemma low_stat_impl_high_stat_sem_zero_sus
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     prio_not_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBDly tcurl = Some (Vint32 wt) ->
     V_OSTCBStat tcurl = Some (Vint32 (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND))) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
    Int.eq wt Int.zero = true ->
     exists msg t_opt,
       TcbMod.get tcbls tcur = Some (prio, wait (os_stat_sem sid) t_opt, msg, true) /\
        (t_opt = (Some wt) \/ t_opt = None).
Proof.
  introv Ht Hp Hvp Hvt Hvs Hvn Hneq.
  simpl in Ht.
  mytac.
  inverts H.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  apply tcbjoin_get_a in H1.
  destruct H9 as (_ & _ & _ & _ & Hrts & _).
  funfold Hrts.
  funfold H19.
  unfold WaitTCBblk in H19.
  unfold V_OSTCBPrio, V_OSTCBDly, V_OSTCBStat, V_OSTCBEventPtr in H19.
  rewrite H4,H5,H6,H7 in H19.
  rewrite H1.
  eapply semacc_int_eq_true in Hneq; subst.
  assert (exists m0 t_opt, (p, t, m, s) = (prio, wait (os_stat_sem sid) t_opt, m0, true) /\
                                                     (Int.zero = Int.zero /\ (t_opt = Some Int.zero \/ t_opt = None) \/
                                                       Int.zero <> Int.zero /\ t_opt = Some Int.zero)).
  eapply H19; try auto.
  destruct H as (m0 & t_opt & Heq & H).
  inverts Heq.
  destruct H as [(_ & H) |  (Hf & _) ].
  eauto.
  tryfalse.
Qed.

Lemma low_stat_impl_high_stat_sem'
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid st msg sus,
      Int.eq wt Int.zero = false -> (* new add *)
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     prio_not_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBDly tcurl = Some (Vint32 wt) ->
     V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_SEM)) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
     TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
     st = wait (os_stat_sem sid) (Some wt).
Proof.
introv Hneq.
intros.
  lets Hget : low_stat_impl_high_stat_sem H H0 H1 H2 H3.
  lets Hget': Hget H4.
  clear Hget. destruct Hget'.
  auto.
  rewrite H5 in H6.
  inverts H6.
  auto.
Qed.

(* new add *)
Lemma low_stat_impl_high_stat_sem_zero'
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid st msg sus,
      Int.eq wt Int.zero = true ->
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     prio_not_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBDly tcurl = Some (Vint32 wt) ->
     V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_SEM)) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
     TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
     st = wait (os_stat_sem sid) None.
Proof.
introv Heq.
intros.
  lets Hget : low_stat_impl_high_stat_sem_zero H H0 H1 H2 H3.
  lets Hget': Hget H4.
  clear Hget. destruct Hget'.
  auto.
  rewrite H5 in H6.
  inverts H6.
  auto.
Qed.

(* new add *)
Lemma low_stat_impl_high_stat_sem_zero_some
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     prio_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
(*      V_OSTCBDly tcurl = Some (Vint32 wt) -> *)
     V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_SEM)) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
    Int.eq wt Int.zero = true ->
     exists msg,
       TcbMod.get tcbls tcur = Some (prio, wait (os_stat_sem sid) (Some Int.zero), msg, false).
Proof.
  introv Ht Hp Hvp (* Hvt *) Hvs Hvn Heq.
  simpl in Ht.
  mytac.
  inverts H.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  apply tcbjoin_get_a in H1.
  destruct H8 as (_ & _ & _ & _ & Hrts & _).
  funfold Hrts.
  funfold H10.
  unfold RdyTCBblk in H10.
  unfold V_OSTCBPrio, V_OSTCBDly, V_OSTCBStat, V_OSTCBEventPtr in H10.
  rewrite H4,H5,H6 in H10.
  rewrite H1.
  assert (exists m0,  (p, t, m, s) = (prio, wait (os_stat_sem sid) (Some Int.zero), m0, false)).
  eapply H10; try auto.
  destruct H.
  rewrite H.
  eauto.
Qed.

(* new add *)
Lemma low_stat_impl_high_stat_sem_zero_some'
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid st msg sus,
      Int.eq wt Int.zero = true ->
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     prio_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
(*      V_OSTCBDly tcurl = Some (Vint32 wt) -> *)
     V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_SEM)) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
     TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
     st = wait (os_stat_sem sid) (Some Int.zero).
Proof.
introv Heq.
intros.
  lets Hget : low_stat_impl_high_stat_sem_zero_some H H0 H1 H2 H3.
  destruct Hget.
  eauto.
  rewrite H4 in H5.
  inverts H5.
  auto.
Qed.

Lemma low_stat_impl_high_stat_neq_sem
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) st prio msg,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     V_OSTCBStat tcurl <> Some (Vint32 ($ OS_STAT_SEM)) ->
     V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBMsg tcurl = Some msg ->
     TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
     ~(exists sid wt, st =wait (os_stat_sem sid) wt).
Proof.
  introv Ht.
  pure_auto.
  apply H.
  simpl in Ht.
  mytac.
  inverts H4.
  funfold H7.
  destruct x4.
  destruct p.
  destruct p.
  mytac.
    apply tcbjoin_get_a in H6.
    rewrite H6 in *.
  destruct H9 as (_ & _ & _ & _ & _ & Hrts).
  funfold Hrts.
  funfold H10.
  inverts H2.
  specialize (H10 _ _ _ _ (eq_refl _)).
  pauto.
Qed.

Lemma low_stat_impl_high_stat_neq_sem'
 : forall tcur tcurl tcblist2 rtbl tls1 tls2 tcbls st prio msg,
    TcbMod.join tls1 tls2 tcbls ->
     TCBList_P (Vptr tcur) (tcurl :: tcblist2) rtbl tls2 ->
     V_OSTCBStat tcurl <> Some (Vint32 ($ OS_STAT_SEM)) ->
     V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBMsg tcurl = Some msg ->
     TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
     ~(exists sid wt, st =wait (os_stat_sem sid) wt).
Proof.
  intros.
  lets Hget: TCBListP_head_in_tcb' H0 H2 H3.
  destruct Hget as [st' [sus]]. 
  lets Heq: TcbMod.join_get_r H H5.
  rewrite H4 in Heq; inverts Heq.
  lets Hget : low_stat_impl_high_stat_neq_sem H0 H1 H2 H3 H5.
  pure_auto.
Qed.


Lemma low_stat_impl_high_stat_wait
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     prio_not_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBDly tcurl = Some (Vint32 wt) ->
     V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_RDY)) ->
     exists msg,
       TcbMod.get tcbls tcur = Some (prio, wait os_stat_time (Some wt), msg, false).
Proof.
  introv Ht Hp Hvp Hvt Hvs.
  simpl in Ht.
  mytac.
  inverts H.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  apply tcbjoin_get_a in H1.
  destruct H8 as (_ & _ & _ & _ & Hrts & _).
  funfold Hrts.
  funfold H8.
  unfold WaitTCBblk in H8.
  unfold V_OSTCBPrio, V_OSTCBDly, V_OSTCBStat in H8.
  rewrite H4,H5,H6 in H8.
  rewrite H1.
  assert (exists m0, (p, t, m, s) = (prio, wait os_stat_time (Some wt), m0, false)).
  eapply H8; try auto.
  destruct H.
  rewrite H.
  eauto.
Qed.

Lemma low_stat_impl_high_stat_wait_sus
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     prio_not_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBDly tcurl = Some (Vint32 wt) ->
     V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_SUSPEND)) ->
     exists msg,
       TcbMod.get tcbls tcur = Some (prio, (if Int.eq wt Int.zero then rdy else wait os_stat_time (Some wt)), msg, true).
Proof.
  introv Ht Hp Hvp Hvt Hvs.
  simpl in Ht.
  mytac.
  inverts H.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  apply tcbjoin_get_a in H1.
  destruct H8 as (_ & _ & Hrts & _).
  funfold Hrts.
  rewrite H1.
  destruct (Int.eq wt Int.zero) eqn: eq1.
  eapply semacc_int_eq_true in eq1; subst.
  eapply H8 in H4.
  destruct H4; inverts H; eauto.
  repeat eexists; eauto.
  change Int.zero with ($ 0) in *.
  eapply int_eq_false_ltu in eq1.
  eapply H9 in eq1; eauto.
  destruct eq1; inverts H; eauto.
  repeat eexists; eauto.
Qed.

Lemma low_stat_rdy_impl_high_stat
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
      array_type_vallist_match Int8u rtbl ->
      length rtbl = ∘ OS_RDY_TBL_SIZE ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBDly tcurl = Some (Vint32 wt) ->
     V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_RDY)) ->
     (exists msg, TcbMod.get tcbls tcur = Some (prio, wait os_stat_time (Some wt), msg, false)) \/
     (exists msg, TcbMod.get tcbls tcur = Some (prio, rdy, msg, false) ).
Proof.
  introv Ht Ha Hl Hvp Hvt Hvs.
  assert (Hpt: prio_in_tbl prio rtbl \/ prio_not_in_tbl prio rtbl).
  {
    eapply prio_rtbl_dec.
   simpl in Ht.
  mytac.
  inverts H.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  funfold H2.
  rewrite H10 in H6.
  inverts H6.
  eauto.
  auto.
  auto.
  }
  destruct Hpt.
  2 : { left. eapply low_stat_impl_high_stat_wait; eauto. }
  simpl in Ht.
  mytac.
  inverts H0.
  funfold H3.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  apply tcbjoin_get_a in H2.
   rewrite H2.
  destruct H9 as (Hrts & _ & _ & _).
  unfold V_OSTCBPrio in H1.
  rewrite H7 in H1; inverts H1.
  assert (Hrdy: RdyTCBblk tcurl rtbl p).
  unfolds. splits; auto.
  eapply Hrts in Hrdy.
  destruct Hrdy as (Hdly & Hrdy).
  unfold V_OSTCBStat in *.
  destruct Hrdy as  [(Hst & Habs) | [(Hst & Habs) | [ (Hst & Habs) | [ (Hst & Habs) | (Hst & Habs) ] ] ]]; rewrite H5 in Hst; inverts Hst.
  destruct Habs as (m0 & Habs).
  rewrite Habs.
  eauto.
Qed.

Lemma low_stat_rdy_impl_high_stat'
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt st msg sus,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
      array_type_vallist_match Int8u rtbl ->
      length rtbl = ∘ OS_RDY_TBL_SIZE ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBDly tcurl = Some (Vint32 wt) ->
     V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_RDY)) ->
      TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
     (st = wait os_stat_time (Some wt) \/ st = rdy).
Proof.
intros.
lets He: low_stat_rdy_impl_high_stat H H0 H1 H2 H3.
lets He': He H4.
clear He.
rewrite H5 in He'.
destruct He'; destruct H6; inverts H6; auto.
Qed.

Lemma get_tcb_stat_rdy
: forall tcur tcurl tcblist rtbl tcbls prio st msg,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
  (st = rdy \/ (exists wt, st = wait os_stat_time wt)) ->
  V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_RDY)) /\
  V_OSTCBEventPtr tcurl = Some Vnull.
Proof.
intros.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H6.
rename H6 into Hsus1; rename H10 into Hsus2;
rename H11 into H6; rename H12 into H10.
funfold H10.
rename H15 into Hrhl_postq.
funfold H4.
funfold  H10.
funfold H2.
destruct H1.
subst t;assert(RdyTCBblk tcurl rtbl p /\
     V_OSTCBStat tcurl = Some (V$ OS_STAT_RDY) /\
     V_OSTCBDly tcurl = Some (V$ 0)) by (eapply H2; eauto);
unfold V_OSTCBStat,V_OSTCBEventPtr in *;
mytac.
rewrite H30 in *;
rewrite H29;inverts H4;
split; try pauto.
destruct H34; auto.
destruct H1; subst t.
specialize (H10 _ _ _ (eq_refl _)).
destruct H10 as (t & eq & Hw & Hlt & Hst).
splits; eauto.
unfold V_OSTCBStat,V_OSTCBEventPtr in *;
mytac;
rewrite H30 in *;
inverts Hst;inverts H29.
destruct H34; eauto.
Qed.

(* new add *)
Lemma get_tcb_stat_rdy_sus
: forall tcur tcurl tcblist rtbl tcbls prio st msg sus,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
  (st = rdy \/ (exists wt, st = wait os_stat_time wt)) ->
  V_OSTCBStat tcurl = Some (Vint32 (if sus then ($ OS_STAT_SUSPEND) else ($ OS_STAT_RDY))) /\
  V_OSTCBEventPtr tcurl = Some Vnull.
Proof.
intros.
destruct sus.
2: eapply get_tcb_stat_rdy; eauto.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H6.
assert (Hst: V_OSTCBStat tcurl = Some (V$ OS_STAT_SUSPEND)).
{  destruct H10 as (Hrdy & Hwt).
   destruct H1; simpljoin; subst.
   eapply Hrdy; eauto.
   specialize (Hwt _ _ _ (eq_refl _)).
   simpljoin; auto.
 }
split; auto.
funfold H4.
unfold V_OSTCBEventPtr.
rewrite H20 in H22; inverts H22.
rewrite H21.
destruct H25; auto.
Qed.

Lemma get_tcb_stat_sem
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid wt,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
  st = wait (os_stat_sem sid) (Some wt) ->
  wt <> Int.zero -> (* new add *)
  V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_SEM)) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 wt) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
rename H2 into Hneq.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p. destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H4.
rename H4 into Hsus1; rename H9 into Hsus2;
rename H10 into H4; rename H11 into H9.
funfold H9.
funfold  H10.
specialize (H10 _ _ _ _ (eq_refl _)).
simpljoin.
unfold WaitTCBblk in *.
destruct H10 as [ (Heq & Hcase) | (Hf & Hwait)]; tryfalse.
inverts Heq.
destruct Hcase as [Hnz | (Hz & _)]; try subst; tryfalse.
simpljoin.
splits; auto.
Qed.

Lemma get_tcb_stat_sem_sus
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid wt sus,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
  st = wait (os_stat_sem sid) (Some wt) ->
  wt <> Int.zero ->
  V_OSTCBStat tcurl = Some (Vint32 (if sus then (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)) else ($ OS_STAT_SEM))) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 wt) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
destruct sus.
2: eapply get_tcb_stat_sem; eauto.
funfold H.
fold TCBList_P in H6.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H4.
rewrite H0 in Hget.
inverts Hget.
funfold H5.
funfold H5.
funfold H12.
specialize (H18 _ _ _ _ (eq_refl _)).
simpljoin.
destruct H18 as [ (t & Heq & Hwt(*  & Hneq *)) | (Heq & _)]; inverts Heq.
funfold Hwt.
splits; auto.
Qed.

Lemma get_tcb_stat_sem_zero
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid wt,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
  st = wait (os_stat_sem sid) (Some wt) ->
  wt = Int.zero ->
  V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_SEM)) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 wt) /\
  prio_in_tbl prio rtbl.
Proof.
intros.
rename H2 into Hwt.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p. destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H4.
rename H4 into Hsus1; rename H9 into Hsus2;
rename H10 into H4; rename H11 into H9.
funfold H9.
funfold  H10.
specialize (H10 _ _ _ _ (eq_refl _)).
simpljoin.
unfold RdyTCBblk in *.
destruct H10 as [ (Heq & Hcase) | (Hf & Hwait)]; tryfalse.
inverts Heq.
destruct Hcase as [(Hnz & _) | (_ & Hz)]; tryfalse.
simpljoin.
splits; auto.
Qed.

Lemma get_tcb_stat_sem_zero_sus
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid wt,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, true) ->
  wt = Int.zero ->
  st = wait (os_stat_sem sid) (Some wt) ->
  V_OSTCBStat tcurl = Some (Vint32 (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND))) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 wt) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
funfold H.
fold TCBList_P in H6.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H4.
rewrite H0 in Hget.
inverts Hget.
funfold H5.
funfold H5.
funfold H11.
specialize (H17 _ _ _ _ (eq_refl _)).
simpljoin.
destruct H17 as [ (t & Heq & Hwt (* & Hneq *)) | (Heq & _)]; inverts Heq.
funfold Hwt.
splits; auto.
Qed.

Lemma get_tcb_stat_sem_simpl
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid wt,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
  st = wait (os_stat_sem sid) (wt) ->
  V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_SEM)) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid).
Proof.
intros.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H4.
rename H4 into Hsus1; rename H9 into Hsus2;
rename H10 into H4; rename H11 into H9.
funfold H9.
funfold  H10.
specialize (H10 _ _ _ _ (eq_refl _)).
simpljoin.
unfold WaitTCBblk in *.
destruct H10 as [ (Heq & Hcase) | (Hf & Hwait)]; tryfalse.
destruct Hcase. simpljoin1;splits;eauto.
simpljoin1;splits;eauto.
simpljoin1;splits;eauto.
Qed.

Lemma get_tcb_stat_sem_none
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
  st = wait (os_stat_sem sid) None ->
  V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_SEM)) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 Int.zero) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H4.
rename H4 into Hsus1; rename H9 into Hsus2;
rename H10 into H4; rename H11 into H9.
funfold H9.
funfold  H10.
specialize (H10 _ _ _ _ (eq_refl _)).
simpljoin.
unfold WaitTCBblk in *.
destruct H10 as [ (Hf & _) | (_ & Hwait)]; tryfalse.
simpljoin.
splits; auto.
Qed.

Lemma get_tcb_stat_sem_none_sus
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid sus,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
  st = wait (os_stat_sem sid) None ->
  V_OSTCBStat tcurl = Some (Vint32 (if sus then (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)) else ($ OS_STAT_SEM))) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 Int.zero) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
destruct sus.
2: eapply get_tcb_stat_sem_none; eauto.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H4.
funfold H11.
specialize (H17 _ _ _ _ (eq_refl _)).
simpljoin.
destruct H17 as [ (t & Heq & Hwt) | (Heq & Hwt)]; inverts Heq.
funfold Hwt.
splits; auto.
Qed.

Lemma RL_TCBblk_P_hold_for_update :
forall tcurl,
RL_TCBblk_P tcurl ->
RL_TCBblk_P (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY)).
Proof.
intros.
funfold H.
unfold RL_TCBblk_P.
unfold V_OSTCBX,V_OSTCBPrio,V_OSTCBY,V_OSTCBBitX,V_OSTCBBitY,V_OSTCBStat,V_OSTCBEventPtr in *.
repeat eexists; 
try (eapply update_nth); try (eapply nth_upd_neqrev; try pauto);
try (eapply update_nth); try (eapply nth_upd_neqrev; try pauto); try eauto.
Qed.

Lemma RdyTCBblk_hold_update:
forall tcurl rtbl abstcb,
RdyTCBblk tcurl rtbl abstcb ->
RdyTCBblk  (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY)) rtbl abstcb.
Proof.
unfold RdyTCBblk.
unfold V_OSTCBPrio.
intros.
splits; 
try (eapply nth_upd_neqrev; try pauto);
try (eapply nth_upd_neqrev; try pauto); try pauto.
Qed.

Lemma RdyTCBblk_hold_update':
forall tcurl rtbl abstcb,
RdyTCBblk  (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY)) rtbl abstcb ->
RdyTCBblk tcurl rtbl abstcb.
Proof.
unfold RdyTCBblk.
unfold V_OSTCBPrio.
intros.
destruct H.
splits; try auto;
eapply nth_upd_neq; try eapply nth_upd_neq.
3 : { eauto. } pauto. pauto.
Qed.

(* Lemma RLH_rdyI_P_hold_update:
forall tcurl rtbl abstcb,
RLH_RdyI_P tcurl rtbl abstcb ->
RLH_RdyI_P  (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY)) rtbl abstcb.
Proof.
unfold RLH_RdyI_P.
unfold V_OSTCBStat,V_OSTCBDly.
intros.
apply RdyTCBblk_hold_update' in H0.
eapply H in H0.
simpljoin.
split.
eapply nth_upd_neqrev; try pauto.
eapply nth_upd_neqrev; try pauto.
destruct H1 as [(Hst & Habs) | [ (Hst & Habs) | [ (Hst & Habs) | (Hst & Habs) ] ] ];
[ left | right; left | do 2 right; left | do 3 right];
simpljoin; subst;
splits; eauto.
eapply update_nth; try eapply nth_upd_neqrev; eauto.
eapply update_nth.
eapply nth_upd_neqrev; eauto.
try (eapply update_nth); try (eapply nth_upd_neqrev; try pauto).
try (eapply update_nth); try (eapply nth_upd_neqrev; try pauto); try pauto.
Qed.

Lemma RHL_rdyI_P_hold_update:
forall tcurl rtbl abstcb,
RHL_RdyI_P tcurl rtbl abstcb ->
RHL_RdyI_P  (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY)) rtbl abstcb.
Proof.
unfold RHL_RdyI_P.
unfold V_OSTCBStat,V_OSTCBDly.
intros.
eapply H in H0.
splits; try apply RdyTCBblk_hold_update; 
try eapply update_nth;
try eapply nth_upd_neqrev;
try eapply nth_upd_neqrev; try pauto.
Qed. *)

Lemma WaitTCBblk_hold_update:
forall tcurl rtbl prio t,
WaitTCBblk tcurl rtbl prio t ->
WaitTCBblk  (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY)) rtbl prio t.
Proof.
unfold WaitTCBblk.
unfold V_OSTCBPrio,V_OSTCBDly.
intros.
splits; 
try (eapply nth_upd_neqrev; try pauto);
try (eapply nth_upd_neqrev; try pauto); try pauto.
Qed.

Lemma WaitTCBblk_hold_update':
forall tcurl rtbl prio t,
WaitTCBblk  (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY)) rtbl prio t ->
WaitTCBblk tcurl rtbl prio t.
Proof.
unfold WaitTCBblk.
unfold V_OSTCBPrio,V_OSTCBDly.
intros.
destruct H as (H1 & H2 & H3).
splits; try auto;
eapply nth_upd_neq; try eapply nth_upd_neq.
3 : { eauto. } pauto. pauto.
3 : { eauto. } pauto. pauto.
Qed.

Lemma TCBList_P_hold_for_update_wait :
forall tcbls tcur tcurl tcblist rtbl time prio st msg sus,
TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
  0 <= Int.unsigned prio < 64 ->
  array_type_vallist_match char_t rtbl ->
  length rtbl = ∘ OS_RDY_TBL_SIZE ->
V_OSTCBDly tcurl = Some (Vint32 time) ->
Int.ltu Int.zero time = true ->
TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
TCBList_P (Vptr tcur) 
                      ((update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY))::tcblist) 
                      rtbl
(TcbMod.set tcbls tcur (prio, wait os_stat_time (Some time), msg, false)).
Proof.
simpl TCBList_P.
intros.
destruct H as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
destruct asbs'.
destruct p.
destruct p.
exists td' vv' tcblss' (prio, wait os_stat_time (Some time), msg, false).
inverts Hveq'.
unfold sig in *. unfold TcbMap in *.
assert (Heq1: (prio, st, msg, sus) = (p, t, m, s)).
eapply TcbMod.map_get_unique.
eauto.
eapply TcbMod.join_sig_get. eauto.
inverts Heq1.
splits; try auto.
unfold V_OSTCBNext in *;
try (eapply nth_upd_neqrev; try pauto);
try (eapply nth_upd_neqrev; try pauto).
unfold TcbMod.join in *.
intros.
specialize Htcj' with (a:= a).
erewrite TcbMod.sig_sem in *.
rewrite TcbMod.set_sem in *.
pure_auto.
(*TCBNode_P (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY))
  rtbl (p, wait os_stat_time time, m) *)
destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
unfold TCBNode_P.
unfold V_OSTCBMsg,V_OSTCBPrio in *.
splits;
try (eapply nth_upd_neqrev; try pauto);
try (eapply nth_upd_neqrev; try pauto).
apply RL_TCBblk_P_hold_for_update; auto.
  lets Hp: prio_rtbl_dec H0 H1 H2.
  funfold Hrtsl'.
  rename H8 into Hsus1; rename H9 into Hsus2;
  rename H10 into H8; rename H11 into H9.
  unfold R_TCB_Status_P.
  splits. unfold RLH_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  assert (Hneq1: 6%nat <> 5%nat /\ 6%nat <> 2%nat /\ 4%nat <> 5%nat /\ 4%nat <> 2%nat) by pauto.
  destruct Hneq1 as (nq1 & nq2 & nq3 & nq4).
  destruct H3.
  lets Heq1: nth_upd_neq nq1 H3.
  lets Heq2: nth_upd_neq nq2 Heq1.
  assert (Heq: nth_val 6 tcurl = Some (Vint32 prio) /\ prio_in_tbl prio rtbl) by auto.
  eapply H6 in Heq.
  destruct Heq as (Heq & _).
  rewrite Heq in H13; inverts H13.
  change ($ 0) with Int.zero in *.
  rewrite sempend_ltu_ass1 in H4; tryfalse.
  unfold RHL_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  tryfalse.

  (* RLH_Suspend_P *)
  unfolds.
  split; introv Hwt Hst;
  eapply nth_upd_eq in Hst; inverts Hst.
 (* RHL_Suspend_P *)
  unfolds.
  split; introv Hst; inverts Hst.

  unfolds.
  splits; try solve [unfolds; introv Hwt Hst; eapply nth_upd_eq in Hst; inverts Hst].

  unfolds; introv Hwt Hst; eapply nth_upd_eq in Hst; inverts Hst.
  funfold Hwt.
  eapply nth_upd_neq in H15; eauto.
  eapply nth_upd_neq in H15; eauto.
  eapply nth_upd_neq in H14; eauto.
  eapply nth_upd_neq in H14; eauto.
  rewrite H14 in Hvp; inverts Hvp.
  rewrite H15 in H13; inverts H13.
  eauto.

  splits; try solve [unfolds; introv Hwt Hst; eapply nth_upd_eq in Hst; inverts Hst].
  splits; try solve [unfolds; introv Hwt Hst; eapply nth_upd_eq in Hst; inverts Hst].
  splits; try solve [unfolds; introv Hst; inverts Hst].
  unfolds; introv Hst; inverts Hst.
  exists time.
  splits; auto.
  eapply WaitTCBblk_hold_update.
  unfold WaitTCBblk.
  destruct Hp as [Hin | Hnin].
  unfold RLH_RdyI_P in *.
  unfold RdyTCBblk in *.
  unfold V_OSTCBDly in *.
  assert (Heq: V_OSTCBPrio tcurl = Some (Vint32 prio) /\ prio_in_tbl prio rtbl ) by auto.
  eapply H6 in Heq.
  destruct Heq as (Heq & _).
  rewrite Heq in H13; inverts H13.
  change ($ 0) with Int.zero in *.
  rewrite sempend_ltu_ass1 in H4; tryfalse.
  splits; auto.
  funfold Hrsl'.
  unfold V_OSTCBStat in *.
  eapply update_nth; eapply nth_upd_neqrev; try pauto.

  splits; try solve [unfolds; introv Hst; inverts Hst].
Qed.

Lemma prio_in_tbl_imp :
forall p rtbl,
0 <= Int.unsigned p < 64 ->
  array_type_vallist_match char_t rtbl ->
  length rtbl = ∘ OS_RDY_TBL_SIZE ->
prio_in_tbl p rtbl -> 
~(prio_not_in_tbl p rtbl).
Proof.
introv Hr Harr Hlen Hp.
unfold prio_in_tbl, prio_not_in_tbl in *.
lets Hex :   int_usigned_tcb_range Hr.
  destruct Hex as (He1 & He2).
  simpl in Hlen.
  unfold Pos.to_nat in Hlen.
  simpl in Hlen.
  assert ( 0<=Z.to_nat(Int.unsigned (Int.shru p ($ 3))) <8)%nat.
  eapply int8_range_nat; auto.
  lets Hes : n07_arr_len_ex H Harr Hlen.
  destruct Hes as (v & Hes & Hneq).
  assert ( 0 <=Int.unsigned v <256).
  clear -Hneq.
  int auto.
  lets Hea: prio_int_disj H0 He1.
  assert (Himp: forall P Q:Prop, (P /\ ~Q) -> ~(P -> Q) ).
tauto.
eapply Classical_Pred_Type.ex_not_not_all; exists (p&ᵢ$ 7).
eapply Classical_Pred_Type.ex_not_not_all; exists (p >>ᵢ $ 3).
eapply Classical_Pred_Type.ex_not_not_all; exists v.
eapply Himp.
split; try auto.
eapply Himp.
split; try auto.
eapply Himp.
split; try auto.
assert (v&ᵢ($ 1<<ᵢ(p&ᵢ$ 7)) = $ 1<<ᵢ(p&ᵢ$ 7)).
eapply Hp; try eauto.
rewrite H1.
eapply math_prop_neq_zero2.
eauto.
Qed.

Lemma prio_not_in_tbl_imp :
forall p rtbl,
0 <= Int.unsigned p < 64 ->
  array_type_vallist_match char_t rtbl ->
  length rtbl = ∘ OS_RDY_TBL_SIZE ->
prio_not_in_tbl p rtbl -> 
~(prio_in_tbl p rtbl).
Proof.
introv Hr Harr Hlen Hp.
unfold prio_in_tbl, prio_not_in_tbl in *.
lets Hex :   int_usigned_tcb_range Hr.
  destruct Hex as (He1 & He2).
  simpl in Hlen.
  unfold Pos.to_nat in Hlen.
  simpl in Hlen.
  assert ( 0<=Z.to_nat(Int.unsigned (Int.shru p ($ 3))) <8)%nat.
  eapply int8_range_nat; auto.
  lets Hes : n07_arr_len_ex H Harr Hlen.
  destruct Hes as (v & Hes & Hneq).
  assert ( 0 <=Int.unsigned v <256).
  clear -Hneq.
  int auto.
  lets Hea: prio_int_disj H0 He1.
  assert (Himp: forall P Q:Prop, (P /\ ~Q) -> ~(P -> Q) ).
tauto.
eapply Classical_Pred_Type.ex_not_not_all; exists (p&ᵢ$ 7).
eapply Classical_Pred_Type.ex_not_not_all; exists (p >>ᵢ $ 3).
eapply Classical_Pred_Type.ex_not_not_all; exists v.
eapply Himp.
split; try auto.
eapply Himp.
split; try auto.
eapply Himp.
split; try auto.
assert (v&ᵢ($ 1<<ᵢ(p&ᵢ$ 7)) = $ 0).
eapply Hp; try eauto.
rewrite H1.
apply not_eq_comm.
eapply math_prop_neq_zero2.
eauto.
Qed.


Lemma TCBList_P_hold_for_update_rdy :
forall tcbls tcur tcurl tcblist rtbl prio st msg sus,
TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
  0 <= Int.unsigned prio < 64 ->
  array_type_vallist_match char_t rtbl ->
  length rtbl = ∘ OS_RDY_TBL_SIZE ->
V_OSTCBDly tcurl = Some (Vint32 Int.zero) ->
(* isptr (val_inj (V_OSTCBEventPtr tcurl)) -> *)
prio_in_tbl prio rtbl ->
TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
TCBList_P (Vptr tcur) 
                      ((update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY))::tcblist) 
                      rtbl
(TcbMod.set tcbls tcur (prio, rdy, msg, false)).
Proof.
simpl TCBList_P.
intros.
destruct H as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
destruct asbs'.
destruct p.
destruct p.
exists td' vv' tcblss' (prio, rdy, msg, false).
inverts Hveq'.
unfold sig in *. unfold TcbMap in *.
assert (Heq1: (prio, st, msg, sus) = (p, t, m, s)).
eapply TcbMod.map_get_unique.
eauto.
eapply TcbMod.join_sig_get. eauto.
inverts Heq1.
splits; try auto.
unfold V_OSTCBNext in *;
try (eapply nth_upd_neqrev; try pauto);
try (eapply nth_upd_neqrev; try pauto).
unfold TcbMod.join in *.
intros.
specialize Htcj' with (a:= a).
erewrite TcbMod.sig_sem in *.
rewrite TcbMod.set_sem in *.
pure_auto.
(*TCBNode_P (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY))
  rtbl (p, rdy, m) *)
  assert (Hwt: ~(WaitTCBblk tcurl rtbl p Int.zero)).
  unfold WaitTCBblk.
  lets Hnp: prio_in_tbl_imp H0 H1 H2 H4.
  pauto.
destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
unfold TCBNode_P.
unfold V_OSTCBMsg,V_OSTCBPrio in *.
splits;
try (eapply nth_upd_neqrev; try pauto);
try (eapply nth_upd_neqrev; try pauto).
apply RL_TCBblk_P_hold_for_update; auto.
    funfold Hrtsl'.
  unfold R_TCB_Status_P.
  assert (Hneq1: 6%nat <> 5%nat /\ 6%nat <> 2%nat /\ 4%nat <> 5%nat /\ 4%nat <> 2%nat) by pauto.
  destruct Hneq1 as (nq1 & nq2 & nq3 & nq4).
  assert (Heq: nth_val 6 tcurl = Some (Vint32 p) /\ prio_in_tbl p rtbl) by auto.
  eapply H6 in Heq.
  destruct Heq as (Heq & Hcase).
  splits. unfold RLH_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  destruct H3.
  lets Heq1: nth_upd_neq nq1 H3.
  lets Heq2: nth_upd_neq nq2 Heq1.
  rewrite Hvp in Heq2; inverts Heq2.
  split.
  eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto.
  left.
  split.
  destruct Hcase as  [Hc | [Hc | [Hc | [Hc | Hc]]]]; simpljoin;
  eapply update_nth; try eapply nth_upd_neqrev; eauto.
  eauto.

  unfold RHL_RdyI_P,RLH_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  inverts H3.
  destruct Hcase as  [Hc | [Hc | [Hc | [Hc | Hc]]]]; simpljoin;
  splits; try splits; try eapply update_nth; try eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto.

  (* RLH_Suspend_P *)
  unfolds.
  split; introv Hwt' Hst';
  eapply nth_upd_eq in Hst'; inverts Hst'.
 (* RHL_Suspend_P *)
  unfolds.
  split; introv Hst'; inverts Hst'.

   unfolds.
   assert (Hnp: ~(prio_not_in_tbl p rtbl)) by (eapply prio_in_tbl_imp; eauto).
   splits; try unfolds; try introv Hif Hst; try introv Hptr; 
   try (eapply WaitTCBblk_hold_update' in Hif; 
           unfold WaitTCBblk in Hif; destruct Hif as (Hprio & Hnin & Hdly);
           unfold V_OSTCBPrio in Hprio; rewrite Hprio in Hvp; inverts Hvp; tryfalse);
   try ( unfold V_OSTCBStat in Hst; eapply nth_upd_eq in Hst; inverts Hst).
   splits; try unfolds; try introv Hif Hst; try introv Hptr; 
   try (eapply WaitTCBblk_hold_update' in Hif; 
           unfold WaitTCBblk in Hif; destruct Hif as (Hprio & Hnin & Hdly);
           unfold V_OSTCBPrio in Hprio; rewrite Hprio in Hvp; inverts Hvp; tryfalse);
   try ( unfold V_OSTCBStat in Hst; eapply nth_upd_eq in Hst; inverts Hst).
   splits; try unfolds; try introv Hif Hst; try introv Hptr; 
   try (eapply WaitTCBblk_hold_update' in Hif; 
           unfold WaitTCBblk in Hif; destruct Hif as (Hprio & Hnin & Hdly);
           unfold V_OSTCBPrio in Hprio; rewrite Hprio in Hvp; inverts Hvp; tryfalse);
   try ( unfold V_OSTCBStat in Hst; eapply nth_upd_eq in Hst; inverts Hst).

  unfolds.
  splits; try solve [unfolds; introv Hst; inverts Hst].
  splits; try solve [unfolds; introv Hst; inverts Hst].
Qed.

Lemma TCBList_P_hold_for_update_rdy' :
forall tcbls tcur tcurl tcblist rtbl prio st msg ptbl tcbls' tcbls'' head tcblist' vhold sus,
  0 <= Int.unsigned prio < 64 ->
  array_type_vallist_match char_t rtbl ->
  length rtbl = ∘ OS_RDY_TBL_SIZE ->
V_OSTCBDly tcurl = Some (Vint32 Int.zero) ->
TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
R_PrioTbl_P ptbl tcbls'' vhold ->
TcbMod.join tcbls' tcbls tcbls'' ->
TCBList_P head tcblist' rtbl tcbls' ->
TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
TCBList_P (Vptr tcur) 
                      ((update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY))::tcblist) 
                       (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                                (val_inj
                                 (or (nth_val' (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl) (Vint32 ($ 1<<ᵢ(prio &ᵢ$ 7)))))
                             )
(TcbMod.set tcbls tcur (prio, rdy, msg, false)).
Proof.
simpl TCBList_P.
intros.
destruct H7 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
destruct asbs'.
destruct p.
destruct p.
exists td' vv' tcblss' (prio, rdy, msg, false).
inverts Hveq'.
  unfold sig in *. unfold TcbMap in *.
assert (Heq1: (prio, st, msg, sus) = (p, t, m, s)).
eapply TcbMod.map_get_unique.
eauto.
eapply TcbMod.join_sig_get. eauto.
inverts Heq1.
lets Hex :   int_usigned_tcb_range H.
  destruct Hex as (He1 & He2).
  assert (He1': 0 <= Int.unsigned (p >>ᵢ $ 3) <= 7) by auto with zarith.
    lets Hgrp: array_type_match_get_value He1' H0 H1.
    destruct Hgrp as [grp]. rename H7 into Hgrp.
splits; try auto.
unfold V_OSTCBNext in *;
try (eapply nth_upd_neqrev; try pauto);
try (eapply nth_upd_neqrev; try pauto).
unfold TcbMod.join in *.
intros.
specialize Htcj' with (a:= a).
erewrite TcbMod.sig_sem in *.
rewrite TcbMod.set_sem in *.
pure_auto.
  Focus 2.
  eapply TCBList_P_rtbl_add_lemma_2; try pauto.
  auto with zarith.
  fold nat_of_Z.
  eapply TCBList_P_rtbl_add_simpl_version; try eauto.
  lets Hget: TcbMod.join_get_r H5 H3.
  lets Hjs: TcbMod.map_join_get_sig Hget.
destruct Hjs as [x'].
  apply TcbMod.map_join_comm in H5.
  apply TcbMod.map_join_comm in Htcj'.
  lets Hjoin: join_join_merge H5 Htcj'.
  apply TcbMod.map_join_comm in Hjoin.
  eapply TCBList_P_rtbl_add_lemma_1.
  eauto.
  apply TcbMod.map_join_comm.
  apply TcbMod.join_merge_disj.
  eapply TcbMod.join_join_disj_r. eauto. eauto.
  unfold TcbJoin.
  auto with jdb. 
  unfold TcbJoin.
  unfold join. unfold sig. unfold TcbMap. eauto.
  funfold H4. auto.
(*TCBNode_P *)
destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
unfold TCBNode_P.
unfold V_OSTCBMsg,V_OSTCBPrio in *.
splits;
try (eapply nth_upd_neqrev; try pauto);
try (eapply nth_upd_neqrev; try pauto).
apply RL_TCBblk_P_hold_for_update; auto.

    funfold Hrtsl'.
    lets Hgrp': nth_val_nth_val'_some_eq Hgrp.
  rewrite Hgrp'.
  unfold or. simpl val_inj.

  unfold R_TCB_Status_P.
  splits. unfold RLH_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  assert (Hneq1: 6%nat <> 5%nat /\ 6%nat <> 2%nat /\ 4%nat <> 5%nat /\ 4%nat <> 2%nat) by pauto.
  destruct Hneq1 as (nq1 & nq2 & nq3 & nq4).
  destruct H2.
  lets Heq1: nth_upd_neq nq1 H2.
  lets Heq2: nth_upd_neq nq2 Heq1.
  rewrite Heq2 in Hvp.
  inverts Hvp.   funfold Hrsl'.
  split. try eapply update_nth; try eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto.
  (*new_add*)
  left.
  splits. eapply update_nth; eauto.
  eapply nth_upd_neqrev; eauto. exists m; eauto.

  unfold RHL_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  inverts H2.
  funfold Hrsl'.
  splits; try splits; try eapply update_nth; try eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto.
  eapply prio_in_tbl_orself.

  (* RLH_Suspend_P *)
  unfolds.
  split; introv Hwt Hst;
  eapply nth_upd_eq in Hst; inverts Hst.
 (* RHL_Suspend_P *)
  unfolds.
  split; introv Hst; inverts Hst.

  lets Hnotp: prio_notin_tbl_orself H19 Hgrp.

  unfolds.
  splits; try solve [unfolds; introv Hwt Hst; eapply nth_upd_eq in Hst; inverts Hst].

  unfolds.
  introv Hwt Hst.
  unfolds in Hwt.
  destruct Hwt as (Hp & Hf & Hdly).
  eapply nth_upd_neq in Hp; eauto.
  eapply nth_upd_neq in Hp; eauto.
  rewrite Hvp in Hp; inverts Hp.
  tryfalse.

  splits; try solve [unfolds; introv Hwt Hst; eapply nth_upd_eq in Hst; inverts Hst].
  splits; try solve [unfolds; introv Hwt Hst; eapply nth_upd_eq in Hst; inverts Hst].
  splits; try solve [unfolds; introv Hst; inverts Hst].
  splits; try solve [unfolds; introv Hst; inverts Hst].
Qed.

Lemma TCBList_P_hold_for_update_rdy'' :
forall tcbls tcur tcurl tcblist rtbl prio st msg ptbl tcbls' tcbls'' head tcblist' vhold sus,
  0 <= Int.unsigned prio < 64 ->
  array_type_vallist_match char_t rtbl ->
  length rtbl = ∘ OS_RDY_TBL_SIZE ->
V_OSTCBDly tcurl = Some (Vint32 Int.zero) ->
TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
R_PrioTbl_P ptbl tcbls'' vhold ->
TcbMod.join tcbls' tcbls tcbls'' ->
TCBList_P head tcblist' rtbl tcbls' ->
TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
prio_in_tbl prio rtbl ->
TCBList_P (Vptr tcur) 
                      ((update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY))::tcblist) 
                       rtbl
(TcbMod.set tcbls tcur (prio, rdy, msg, false)).
Proof.
simpl TCBList_P.
intros.
rename H8 into Hin.
destruct H7 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
destruct asbs'.
destruct p.
destruct p.
exists td' vv' tcblss' (prio, rdy, msg, false).
inverts Hveq'.
  unfold sig in *. unfold TcbMap in *.
assert (Heq1: (prio, st, msg, sus) = (p, t, m, s)).
eapply TcbMod.map_get_unique.
eauto.
eapply TcbMod.join_sig_get. eauto.
inverts Heq1.
lets Hex :   int_usigned_tcb_range H.
  destruct Hex as (He1 & He2).
  assert (He1': 0 <= Int.unsigned (p >>ᵢ $ 3) <= 7) by auto with zarith.
    lets Hgrp: array_type_match_get_value He1' H0 H1.
    destruct Hgrp as [grp]. rename H7 into Hgrp.
splits; try auto.
unfold V_OSTCBNext in *;
try (eapply nth_upd_neqrev; try pauto);
try (eapply nth_upd_neqrev; try pauto).
unfold TcbMod.join in *.
intros.
specialize Htcj' with (a:= a).
erewrite TcbMod.sig_sem in *.
rewrite TcbMod.set_sem in *.
pure_auto.

destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
unfold TCBNode_P.
unfold V_OSTCBMsg,V_OSTCBPrio in *.
splits;
try (eapply nth_upd_neqrev; try pauto);
try (eapply nth_upd_neqrev; try pauto).
apply RL_TCBblk_P_hold_for_update; auto.

    funfold Hrtsl'.
    lets Hgrp': nth_val_nth_val'_some_eq Hgrp.
    
  unfold R_TCB_Status_P.
  
(*   rewrite Hgrp'. *)
  unfold or. simpl val_inj.

  unfold R_TCB_Status_P.
  splits. unfold RLH_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  assert (Hneq1: 6%nat <> 5%nat /\ 6%nat <> 2%nat /\ 4%nat <> 5%nat /\ 4%nat <> 2%nat) by pauto.
  destruct Hneq1 as (nq1 & nq2 & nq3 & nq4).
  destruct H2.
  lets Heq1: nth_upd_neq nq1 H2.
  lets Heq2: nth_upd_neq nq2 Heq1.
  rewrite Heq2 in Hvp.
  inverts Hvp.   funfold Hrsl'.
  split.
  eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto.
  left.
  split.
  eapply update_nth; try eapply nth_upd_neqrev; eauto.
  eauto.

  unfold RHL_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  inverts H2.
  funfold Hrsl'.
  splits; try splits; try eapply update_nth; try eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto.

  (* RLH_Suspend_P *)
  unfolds.
  split; introv Hwt Hst;
  eapply nth_upd_eq in Hst; inverts Hst.
 (* RHL_Suspend_P *)
  unfolds.
  split; introv Hst; inverts Hst.

  lets Hnotp: prio_notin_tbl_orself H19 Hgrp.
  unfolds.
   splits; try unfolds; try introv Hif Hst; try introv Hptr; 
   try (eapply WaitTCBblk_hold_update' in Hif; 
           unfold WaitTCBblk in Hif; destruct Hif as (Hprio & Hnin & Hdly);
           unfold V_OSTCBPrio in Hprio; rewrite Hprio in Hvp; inverts Hvp; tryfalse);
   try ( unfold V_OSTCBStat in Hst; eapply nth_upd_eq in Hst; inverts Hst).
   assert (0 <= Int.unsigned p < 64).
   {
    clear - H H19.
    int_auto.
   }
   lets Hnin' : prio_in_tbl_imp H2 H0 H1 Hin.
   tryfalse.

   splits; try unfolds; try introv Hif Hst; try introv Hptr; 
   try (eapply WaitTCBblk_hold_update' in Hif; 
           unfold WaitTCBblk in Hif; destruct Hif as (Hprio & Hnin & Hdly);
           unfold V_OSTCBPrio in Hprio; rewrite Hprio in Hvp; inverts Hvp; tryfalse);
   try ( unfold V_OSTCBStat in Hst; eapply nth_upd_eq in Hst; inverts Hst).
   splits; try unfolds; try introv Hif Hst; try introv Hptr; 
   try (eapply WaitTCBblk_hold_update' in Hif; 
           unfold WaitTCBblk in Hif; destruct Hif as (Hprio & Hnin & Hdly);
           unfold V_OSTCBPrio in Hprio; rewrite Hprio in Hvp; inverts Hvp; tryfalse);
   try ( unfold V_OSTCBStat in Hst; eapply nth_upd_eq in Hst; inverts Hst).
   unfolds.
   splits; try solve [unfolds; introv Hst; inverts Hst].
   splits; try solve [unfolds; introv Hst; inverts Hst].

Qed.

Lemma TCBList_P_hold_for_update_eventto :
forall tcbls tcur tcurl tcblist rtbl time prio st msg ptbl tcbls' tcbls'' head tcblist' vhold sus,
  0 <= Int.unsigned prio < 64 ->
  array_type_vallist_match char_t rtbl ->
  length rtbl = ∘ OS_RDY_TBL_SIZE ->
V_OSTCBDly tcurl = Some (Vint32 time) ->
TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
R_PrioTbl_P ptbl tcbls'' vhold ->
TcbMod.join tcbls' tcbls tcbls'' ->
TCBList_P head tcblist' rtbl tcbls' ->
TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
(TCBList_P (Vptr tcur) 
                      ((update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY))::tcblist) 
                      rtbl
(TcbMod.set tcbls tcur (prio, wait os_stat_time (Some time), msg, false)) \/ 
TCBList_P (Vptr tcur) 
                      ((update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY))::tcblist) 
                      (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                                (val_inj
                                 (or (nth_val' (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl) (Vint32 ($ 1<<ᵢ(prio &ᵢ$ 7)))))
                             )
(TcbMod.set tcbls tcur (prio, rdy, msg, false))).
Proof.
intros.
assert(Ht: Int.ltu Int.zero time = true \/ Int.ltu Int.zero time = false) by int auto.
destruct Ht.
left.
eapply TCBList_P_hold_for_update_wait; eauto.
apply ltu_zero_false_imp_eq_zero in H8.
inverts H8.
right.
eapply TCBList_P_hold_for_update_rdy'; try eauto.
Qed.

Lemma RH_TCBList_ECBList_P_hold_for_sem_to_wait
: forall tcbls ct p qid wt msg ecbls n wls sus sus',
  TcbMod.get tcbls ct = Some (p, wait (os_stat_sem qid) wt, msg, sus) ->
  EcbMod.get ecbls qid = Some (abssem n, wls) ->
  In ct wls ->
  RH_TCBList_ECBList_P ecbls tcbls ct ->
  RH_TCBList_ECBList_P (EcbMod.set ecbls qid (abssem n, remove_tid ct wls)) 
                                                    (TcbMod.set tcbls ct (p, wait os_stat_time wt, msg, sus')) ct.
Proof.
introv Htg Heg Hi Hrte.
destruct Hrte as (Hr1 & Hr2 & Hr3 & Hr4 & Hr5).
unfolds;
splits;
unfolds;
[ funfold Hr1;
  rename H0 into Hpostq1; rename H1 into H0; rename H2 into Hpostq2
 | funfold Hr2 | funfold Hr3 | funfold Hr4; rename H2 into Hownp | funfold Hr5];
try splits;
intros;
try (assert (eid = qid \/ eid <> qid) by tauto;
 rewrite EcbMod.set_sem in H1;
destruct H2;
try (subst;
rewrite EcbMod.beq_refl in H1;
destruct H1;
inverts H1);
try (rewrite tidspec.neq_beq_false in H1; try auto;
try eapply H in H1;
try eapply Hpostq1 in H1;
(* simpljoin; *)
do 4 destruct H1;
rewrite TcbMod.set_sem;
assert (Ht: tid = ct \/ tid <> ct) by tauto;
destruct Ht;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Htg in H1;
inverts H1);
rewrite tidspec.neq_beq_false; try eauto)).
2 : { (* new add about postq *)
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H2;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H1; try auto;
try (eapply Hpostq2 in H1;
do 4 destruct H1;
 assert (eid = qid \/ eid <> qid) by tauto;
destruct H3;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Heg in H1;
destruct H1;
tryfalse);
rewrite tidspec.neq_beq_false; try eauto).
}
Focus 5.
{
  assert (eid = qid \/ eid <> qid) by tauto;
 rewrite EcbMod.set_sem in H2;
destruct H3;
try (subst;
rewrite EcbMod.beq_refl in H2;
destruct H2;
inverts H2);
try (rewrite tidspec.neq_beq_false in H2; try auto;
eapply H in H2;
do 4 destruct H2;
rewrite TcbMod.set_sem;
assert (tid = ct \/ tid <> ct) by tauto;
destruct H4;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Htg in H2;
inverts H2);
rewrite tidspec.neq_beq_false; try eauto).
}
Unfocus.
Focus 2.
{
  rewrite TcbMod.set_sem.
  assert (ct = tid \/ ct <> tid) by tauto.
  destruct H1.
  subst. eapply in_remove_tid_false in H2. tryfalse.
  rewrite tidspec.neq_beq_false; try auto.
  eapply H.
  split; try eauto.
  eapply tidneq_inwt_in with (x1:= wls) in H1.
  rewrite H1 in H2. auto.
}
Unfocus.
{
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H2;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H1; try auto;
try (eapply H0 in H1;
do 4 destruct H1;
 assert (eid = qid \/ eid <> qid) by tauto;
destruct H3;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Heg in H1;
destruct H1;
tryfalse);
rewrite tidspec.neq_beq_false; try eauto).
}
{
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H2;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H1; try auto.
eapply H0 in H1.
do 2 destruct H1.
 assert (eid = qid \/ eid <> qid) by tauto.
destruct H3.
subst.
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Heg in H1.
destruct H1; inverts H1.
rewrite EcbMod.beq_refl.
exists x (remove_tid ct x0).
split; auto.
eapply tidneq_inwt_in with (x1:= x0) in H2.
rewrite <- H2 in H3. auto.
rewrite tidspec.neq_beq_false; try eauto.
}
{
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H2;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H1; try auto;
try (eapply H0 in H1;
do 2 destruct H1;
 assert (eid = qid \/ eid <> qid) by tauto;
destruct H3;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Heg in H1;
destruct H1;
tryfalse);
rewrite tidspec.neq_beq_false; try eauto).
}
{
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H3;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H2; try auto;
try (eapply H0 in H2;
do 3 destruct H2;
 assert (eid = qid \/ eid <> qid) by tauto;
destruct H4;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Heg in H2;
destruct H2;
tryfalse);
rewrite tidspec.neq_beq_false; try eauto).
}
eapply rh_tcblist_ecblist_mutex_owner_set'; eauto.
apply Mutex_owner_hold_for_set_tcb; auto.
(* new add about RH_TCBList_ECBList_MUTEX_OWNER_P *)
    eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_ecb;
    try eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
    intro Hf.
    destruct Hf as (vpip & vo & Hf).
    inverts Hf.
{ (* new add os_stat_port *)
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H2;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H1; try auto.
eapply H0 in H1.
destruct H1.
 assert (eid = qid \/ eid <> qid) by tauto.
destruct H3.
subst.
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Heg in H1.
destruct H1; inverts H1.
rewrite tidspec.neq_beq_false; try eauto.
}
Qed.

(* new add *)
Lemma R_ECB_PETbl_P_high_tcb_block_hold':
  forall  l vl etbl petbl vl' etbl' petbl' tcbls prio st ptcb m' sus',
  ~( V_OSEventType vl = Some (Vint32 (Int.repr OS_EVENT_TYPE_Q))) ->
  ~( V_OSEventType vl' = Some (Vint32 (Int.repr OS_EVENT_TYPE_Q))) ->
  R_ECB_PETbl_P l (vl, etbl, petbl) tcbls ->
  ~(exists qid time, st = wait (os_stat_postq qid) time) ->
  R_ECB_PETbl_P l (vl', etbl', petbl') (TcbMod.set tcbls ptcb (prio, st, m', sus')).
Proof.
introv Hneq. intros.
funfold H0.
unfolds; splits; unfolds; intros.
rewrite H4 in H; tryfalse.
unfold get in *; unfold TcbMap in *.
assert (Hc: ptcb = tid \/ ptcb <> tid) by tauto.
destruct Hc.
subst.
rewrite TcbMod.map_get_set in H3.
inverts H3.
false. eapply H1; eauto.
rewrite TcbMod.map_get_set' in H3; auto.
eapply H2 in H3.
destruct H3 as (H3 & Hf).
rewrite Hf in Hneq; tryfalse.
Qed.

Lemma R_ECB_PETbl_P_high_tcb_block_hold'':
  forall  l vl etbl petbl etbl' tcbls prio st ptcb m' p st0 m0 sus sus',
  TcbMod.get tcbls ptcb = Some (p, st0, m0, sus) ->
  ~(exists qid time, st0 = wait (os_stat_postq qid) time) ->
  R_ECB_PETbl_P l (vl, etbl, petbl) tcbls ->
  ~(exists qid time, st = wait (os_stat_postq qid) time) ->
  R_ECB_PETbl_P l (vl, etbl', petbl) (TcbMod.set tcbls ptcb (prio, st, m', sus')).
Proof.
introv Hget. intros.
funfold H0.
unfolds; splits; unfolds; intros.
eapply H0 in H4; eauto.
simpljoin.
assert (Hc: ptcb = x \/ ptcb <> x) by tauto.
destruct Hc.
subst.
unfold get in *; unfold TcbMap in *.
rewrite Hget in H4; inverts H4.
false. eapply H; eauto.
repeat eexists.
eapply TcbMod.map_get_set' in H5; eauto.
rewrite H5; eauto.
unfold get in *; unfold TcbMap in *.
assert (Hc: ptcb = tid \/ ptcb <> tid) by tauto.
destruct Hc.
subst.
rewrite TcbMod.map_get_set in H3.
inverts H3.
false. eapply H1; eauto.
rewrite TcbMod.map_get_set' in H3; auto.
eapply H2 in H3.
destruct H3 as (H3 & Hf).
split; auto.
Qed.

Lemma ECBList_P_high_tcb_block_hold_sem_to_wait:
  forall  ectrl head tail msgql ecbls tcbls ptcb prio  m qid time sus sus',
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, wait (os_stat_sem qid) time, m, sus) ->
    EcbMod.get ecbls qid = None ->
    ECBList_P head tail ectrl msgql ecbls 
              (TcbMod.set tcbls ptcb (prio, wait os_stat_time time, m, sus')).
Proof.
  inductions ectrl.
  intros.
  simpl.
  simpl in H.
  auto.
  intros.
  simpl in H.
  mytac.
  destruct msgql; tryfalse.
  destruct a.
  destruct p. (* new add *)
  rename H3 into Hpetbl; rename H4 into H3. (* new add *)
  mytac.
  simpl.
  exists x.
  splits; auto.
  unfolds.
  destruct H2 as (Hr1 & Hr2 & Hr3).
  destruct Hr1 as (Hra3 & Hra1 & Hra2 & Hra4 & Hra5).
  destruct Hr2 as (Hrb3 & Hrb1 & Hrb2 & Hrb4 & Hrb5).
  simpl in Hr3.
  splits.
  unfolds.
  
  splits;
  unfolds;
  intros;
  [eapply Hra3 in H6 | eapply Hra1 in H6 | eapply Hra2 in H6 | eapply Hra4 in H6 | eapply Hra5 in H6];
  mytac;
   assert (x3 = ptcb \/ x3 <> ptcb) by tauto;
  destruct H7;
  try (subst;
    unfold get in H6; simpl in H6;
    rewrite H0 in H6;
    inverts H6;
    eapply EcbMod.join_sig_get in H3;
    rewrite H3 in H1;
    inverts H1);
    try (subst;
    unfold get in H6; simpl in H6;
    rewrite H0 in H6;
    inverts H6);
    repeat eexists;
    rewrite TcbMod.set_sem;
    rewrite tidspec.neq_beq_false; eauto.
  unfolds;
  splits;
  unfolds;
  intros;
  assert (tid = ptcb \/ tid <> ptcb) by tauto;
    destruct H6;
    try subst;
    rewrite TcbMod.set_sem in H2;
    try (rewrite TcbMod.beq_refl in H2; inverts H2);
    rewrite tidspec.neq_beq_false in H2; eauto.
    simpl; auto.
    (* new add about petbl *)
    eapply R_ECB_PETbl_P_high_tcb_block_hold''; eauto.
  introv Hf. destruct Hf as (qd & wt & Hf). inverts Hf.
   introv Hf. destruct Hf as (qd & wt & Hf). inverts Hf.
  (* end of new add *)
  do 3 eexists; splits; eauto.
  eapply IHectrl; eauto.
  eapply  ecbmod_joinsig_get_none; eauto.
Qed.

Lemma get_ectr_sing:
  forall qid head (els1: list os_inv.EventCtr) osevent etbl petbl,
    els1 <> nil ->
    get_ectr (Vptr qid) head els1  = None ->
    get_ectr (Vptr qid) head (els1 ++ ((osevent,etbl,petbl) :: nil))  = Some (osevent,etbl,petbl) ->
    get_last_ptr els1 = Some (Vptr qid).
Proof.
induction els1.
intros.
tryfalse.
induction els1.
unfold get_last_ptr.
simpl.
intros.
destruct a.
destruct p. (* new add *)
destruct head;
try inverts H1.
destruct (beq_addrval qid a); try tryfalse.
destruct (V_OSEventListPtr v0 ); try tryfalse. (* v -> v0 *)
destruct v2; try tryfalse. (* v1 -> v2 *)
destruct (beq_addrval qid a0) eqn: eq1.
apply beq_addrval_eq in eq1.
subst. auto.
destruct (V_OSEventListPtr osevent); try tryfalse.
destruct v2; try tryfalse.  (* v1 -> v2 *)
intros.
destruct a.
destruct p. (* new add *)
assert (Hn: (a0 :: els1) <> nil) by pauto.
eapply (Mbox_common.get_last_prop) in Hn.
erewrite Hn.
destruct a0.
destruct p. (* new add *)
eapply IHels1; try pauto;
clear IHels0 IHels1 Hn;
simpl in *;
destruct head; try tryfalse; try auto;
destruct (beq_addrval qid a) eqn: eq1; try tryfalse;
destruct (V_OSEventListPtr v3); try auto; try tryfalse; (* v1 -> v3 *)
destruct (V_OSEventListPtr v0); try tryfalse;  (* v -> v0 *)
destruct v6; try tryfalse;  (* v4 -> v6 *)
destruct (beq_addrval qid a0) eqn: eq2; try tryfalse; try eauto.
Qed.

Lemma RLH_ECB_ETbl_P_hold_for_update_sem_to_st
: forall tcbls ct p qid wt msg osevent etbl ey egrp' st petbl sus sus',
    Int.unsigned p < 64 ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_sem qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey ->
    RLH_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls ->
    RLH_ECB_ETbl_P qid
     (update_nth_val 1 osevent (Vint32 egrp'),
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))),petbl)
      (TcbMod.set tcbls ct (p, st, msg, sus')).
Proof.
introv Hpr Htg Hey Hre.
destruct Hre as (Hra1 & Hra2 & Hra3 & Hra4 & Hra5).
unfolds;
splits;
unfolds;
[ funfold Hra1 | funfold Hra2 | funfold Hra3 | funfold Hra4 | funfold Hra5];
unfold V_OSEventType in *;
intros;
assert (Hpr1: 0 <= prio /\ prio <= Int.max_unsigned) by (funfold H; clear -H H5; int auto);
destruct Hpr1 as (Hpr1 & Hpr2);
lets Hvp: int_usign_eq Hpr1 Hpr2;
rewrite <- Hvp in H;
pose proof prio_wt_inq_tid_neq;
specialize H1 with (prio':= $ prio);
lets Hpi: H1 Hey Hpr;
rewrite Hpi in H;
clear H1 Hpi;
rewrite Hvp in H;
destruct H;
assert (nq1: 0%nat <> 1%nat) by pauto;
lets Heq1: nth_upd_neq nq1 H0;
[ lets Hst: Hra1 H Heq1| lets Hst: Hra2 H Heq1 | lets Hst: Hra3 H Heq1 | lets Hst: Hra4 H Heq1 | lets Hst: Hra5 H Heq1];
destruct Hst as [tid]; do 3 destruct H2;
unfold get in *; unfold TcbMap in *;
exists tid x x0;
assert (tid = ct \/ tid <> ct) by tauto;
destruct H3;
try (subst;
rewrite Htg in H2;
inverts H2);
rewrite TcbMod.set_sem;
rewrite tidspec.neq_beq_false; eauto.
Qed.

Lemma RHL_ECB_ETbl_P_hold_for_update_sem_to_wait
: forall tcbls ct p qid wt msg osevent etbl ey egrp' ptbl vhold petbl sus sus',
    Int.unsigned p < 64 ->
    R_PrioTbl_P ptbl tcbls vhold ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_sem qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey ->
    RHL_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls ->
    RHL_ECB_ETbl_P qid
     (update_nth_val 1 osevent (Vint32 egrp'),
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))),petbl)
      (TcbMod.set tcbls ct (p, wait os_stat_time wt, msg, sus')).
Proof.
introv Hpr Hrpt Htg Hey Hre.
destruct Hre as (Hrb1 & Hrb2 & Hrb3 & Hrb4 & Hrb5).
unfolds;
splits;
unfolds;
[ funfold Hrb1 | funfold Hrb2 | funfold Hrb3 | funfold Hrb4 | funfold Hrb4];
unfold V_OSEventType in *;
destruct Hrpt as (_ & _ & Hrpt);
funfold Hrpt;
intros;
unfold get in *; unfold TcbMap in *;
assert (tid = ct \/ tid <> ct) by tauto;
destruct H0;
rewrite TcbMod.set_sem in H;
try (subst;
rewrite TcbMod.beq_refl in H;
inverts H);
rewrite tidspec.neq_beq_false in H; try auto;
pose proof prio_wt_inq_tid_neq;
specialize H1 with (prio':= prio);
lets Hpi: H1 Hey Hpr;
rewrite Hpi;
clear Hpi;
lets Hnp: Hrpt H0 H Htg;
[ try eapply Hrb1 in H | try eapply Hrb2 in H | try eapply Hrb3 in H | try eapply Hrb4 in H | try eapply Hrb5 in H];
splits; try eapply nth_upd_neqrev; try pauto.
Qed.

Lemma Event_Type_P_hold_for_update
: forall osevent v n,
    n <> 0%nat ->
    Event_Type_P osevent ->
    Event_Type_P (update_nth_val n osevent (Vint32 v)).
Proof.
unfold Event_Type_P.
unfold V_OSEventType.
intros.
destruct H0 as [H1 | [H1 | [H1 | [H1 | H1]]]];
[left | right; left | do 2 right; left | do 3 right; left | do 4 right];
eapply nth_upd_neqrev; try pauto.
Qed.


Lemma R_ECB_ETbl_P_hold_for_update_sem_to_wait
: forall tcbls ct p qid wt msg osevent etbl y ey egrp' bitx ptbl vhold petbl sus sus',
      Int.unsigned p < 64 ->
      y = p >>ᵢ $ 3 ->
      bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
      R_PrioTbl_P ptbl tcbls vhold ->
      TcbMod.get tcbls ct = Some (p, wait (os_stat_sem qid) wt, msg, sus) ->
      R_ECB_ETbl_P qid (osevent, etbl,petbl) tcbls ->
      nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 ey ->
      R_ECB_ETbl_P qid
       (update_nth_val 1 osevent (Vint32 egrp'),
         update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (ey&ᵢInt.not bitx)),petbl)
       (TcbMod.set tcbls ct (p, wait os_stat_time wt, msg, sus')).
Proof.
introv Hpr Hy Hbitx Hrpt Htg Hre Hey.
funfold Hre.
unfolds.
splits.
eapply RLH_ECB_ETbl_P_hold_for_update_sem_to_st; try eauto.
eapply RHL_ECB_ETbl_P_hold_for_update_sem_to_wait; try eauto.
simpl in *.
eapply Event_Type_P_hold_for_update; try auto.
Qed.

Lemma EcbMod_get_join_sig_set:
forall  qls qid a qls1 b,
  EcbMod.join (EcbMod.sig qid b) qls1 qls ->
  EcbMod.get qls1 qid = None ->
  EcbMod.join (EcbMod.sig qid a) qls1 (EcbMod.set qls qid a).
Proof.
  intros.
  unfold EcbMod.join.
  intros.
  rewrite EcbMod.sig_sem.
  rewrite EcbMod.set_sem.
  assert (qid = a0 \/ qid <> a0) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.beq_refl.
  rewrite H0. auto.
  eapply tidspec.neq_beq_false in H1.
  rewrite H1.
  destruct (EcbMod.get qls1 a0) eqn: eq2.
  lets Htg: EcbMod.join_get_r H  eq2.
  rewrite Htg.
  auto.
  assert (EcbMod.get qls a0 = EcbMod.get qls1 a0).
  eapply EcbMod.map_join_get_none; try eauto.
  rewrite EcbMod.sig_sem.
  rewrite H1. auto.
  rewrite H2. rewrite eq2. auto.
Qed.

Lemma RLH_ECBData_P_hold_sem
: forall n ct w ecbcurl,
  RLH_ECBData_P ecbcurl (abssem n, w) ->
RLH_ECBData_P ecbcurl (abssem n, remove_tid ct w).
Proof.
intros.
unfolds.
unfolds in H.
destruct ecbcurl; try tryfalse.
split; pauto.
simpl in *.
mytac.
split; intros.
apply H0 in H.
subst.
simpl. auto.
eapply H1.
pure_auto.
subst.
simpl in *.
tryfalse.
Qed.

Lemma R_ECB_PETbl_upd_hold_gen :
  forall x1 v v0 v0' v'36 x8 petbl n,
    n <> 0%nat ->
    R_ECB_PETbl_P x1 (v, v0, petbl) v'36 ->
    R_ECB_PETbl_P x1 (ifun_spec.update_nth val n v x8, v0', petbl) v'36.
Proof.
  introv Hneq Hr.
  unfolds in Hr.
  destruct Hr.
  unfolds.
  splits; unfolds; intros.
  eapply H; eauto.
  eapply nth_val_upd_prop with (m:= n); eauto.
  eapply H0 in H1.
  simpljoin1.
  splits; auto.
  eapply nth_val_upd_prop; eauto.
Qed.

Lemma R_ECB_PETbl_upd_hold_gen' :
  forall x1 v v0 v0' v'36 x8 petbl n,
    n <> 0%nat ->
    R_ECB_PETbl_P x1 (v, v0, petbl) v'36 ->
    R_ECB_PETbl_P x1 (update_nth_val n v x8, v0', petbl) v'36.
Proof.
  introv Hneq Hr.
  unfolds in Hr.
  destruct Hr.
  unfolds.
  splits; unfolds; intros.
  eapply H; eauto.
  eapply nth_upd_neq with (m:= n); eauto.
  eapply H0 in H1.
  simpljoin1.
  splits; auto.
  eapply nth_upd_neqrev with (m:= n); eauto.
Qed.

Lemma ECBList_P_hold_for_update_sem_to_wait
: forall head (els1 els2: list os_inv.EventCtr) osevent etbl osevent' etbl' ecblist1 ecblist2 ecbcurl ecbls 
              tcbls ct p wt msg ey egrp' y bitx qid ptbl vhold n wls petbl sus sus',
    Int.unsigned p < 64 ->
   y = p >>ᵢ $ 3 ->
   bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
  R_PrioTbl_P ptbl tcbls vhold ->
  length els1 = length ecblist1 ->
  RH_TCBList_ECBList_P ecbls tcbls ct ->
  TcbMod.get tcbls ct = Some (p, wait (os_stat_sem qid) wt, msg, sus) ->
  EcbMod.get ecbls qid = Some (abssem n, wls) ->
  In ct wls ->
  get_ectr (Vptr qid) head els1  = None ->
  get_ectr (Vptr qid) head (els1 ++ ((osevent,etbl,petbl) :: nil))  = Some (osevent,etbl,petbl) ->
  ECBList_P head Vnull (els1 ++ ((osevent,etbl,petbl) :: nil) ++ els2) 
                        (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2) ecbls tcbls ->
  nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 ey ->
  osevent' = update_nth_val 1 osevent (Vint32 egrp') ->
  etbl' = update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (ey&ᵢInt.not bitx)) ->
  ECBList_P head Vnull (els1 ++ ((osevent',etbl',petbl) :: nil) ++ els2) 
                        (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2)
                         (EcbMod.set ecbls qid (abssem n, remove_tid ct wls))
                        (TcbMod.set tcbls ct (p, wait os_stat_time wt, msg, sus'))
.
Proof.
introv Hpr Hy Hbitx Hrpt Hl Hrte Htg Heg Hi Hgptr1.
introv Hgptr2 Hep Hey Het' Hetbl'.
assert (Hels1: els1 = nil \/ els1 <> nil) by tauto.
destruct Hels1.
subst els1.
assert (ecblist1 = nil) by (eapply length_zero_nil; simpl in *; auto).
subst ecblist1.
simpl in *.
mytac.
destruct (beq_addrval qid x) eqn: eq1.
Focus 2.
destruct (V_OSEventListPtr osevent); try tryfalse; destruct v; try tryfalse.
apply beq_addrval_eq in eq1.
subst x.
exists qid.
splits; try auto.
eapply R_ECB_ETbl_P_hold_for_update_sem_to_wait; try eauto.
eapply R_ECB_PETbl_upd_hold_gen'; eauto.
eapply R_ECB_PETbl_P_high_tcb_block_hold''; eauto.
introv Hf. destruct Hf as (qd0 & wt0 & Hf). inverts Hf.
introv Hf. destruct Hf as (qd0 & wt0 & Hf). inverts Hf.
exists (abssem n, remove_tid ct wls) x1 x2.
splits; try auto.
unfold V_OSEventListPtr in *.
eapply nth_upd_neqrev; try pauto.
unfold sig. unfold EcbMap.
eapply EcbMod_get_join_sig_set; try eauto.
eapply ejoin_get_none_r; [idtac | eauto].
eapply EcbMod.map_get_sig.
lets Heg': EcbMod.join_sig_get H3.
destruct x0.
rewrite Heg in Heg'.
inverts Heg'.
eapply RLH_ECBData_P_hold_sem; auto.
eapply ECBList_P_high_tcb_block_hold_sem_to_wait; try eauto.
eapply ejoin_get_none_r; [idtac | eauto].
eapply EcbMod.map_get_sig.
(* els1 <> nil *)
lets Hsp: Mbox_common.ecblist_p_decompose Hl Hep.
simpl in *.
mytac.
lets Hx2: get_ectr_sing H Hgptr1 Hgptr2.
destruct H3; rewrite H1 in Hx2; inverts Hx2.
eapply ecblist_p_compose; try eauto.
Focus 2.
eapply ECBList_P_high_tcb_block_hold_sem_to_wait; try eauto.
eapply ejoin_get_none_l; [idtac | eauto].
eapply EcbMod.join_sig_get; eauto.
eapply EcbMod.my_joinsig_join_set; try eauto.
simpl.
exists qid.
splits; try auto.
eapply R_ECB_ETbl_P_hold_for_update_sem_to_wait; try eauto.
eapply R_ECB_PETbl_upd_hold_gen'; eauto.
eapply R_ECB_PETbl_P_high_tcb_block_hold''; eauto.
introv Hf. destruct Hf as (qd0 & wt0 & Hf). inverts Hf.
introv Hf. destruct Hf as (qd0 & wt0 & Hf). inverts Hf.
exists (abssem n, remove_tid ct wls) x4 x5.
splits; try auto.
unfold V_OSEventListPtr in *.
eapply nth_upd_neqrev; try pauto.
unfold sig. unfold EcbMap.
eapply EcbMod_get_join_sig_set; try eauto.
eapply ejoin_get_none_r; [idtac | eauto].
eapply EcbMod.map_get_sig.
lets Heg': EcbMod.join_sig_get H7.
destruct x3.
lets Heg2: EcbMod.join_get_r H2 Heg'.
rewrite Heg in Heg2.
inverts Heg2.
eapply RLH_ECBData_P_hold_sem; auto.
eapply ECBList_P_high_tcb_block_hold_sem_to_wait; try eauto.
eapply ejoin_get_none_r; [idtac | eauto].
eapply EcbMod.map_get_sig.
Unshelve.
exact nil.
exact nil.
Qed.

Lemma RHL_ECB_ETbl_P_hold_for_update_sem_to_rdy
: forall tcbls ct p qid wt msg osevent etbl ey egrp' ptbl vhold petbl sus sus',
    Int.unsigned p < 64 ->
    R_PrioTbl_P ptbl tcbls vhold ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_sem qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey ->
    RHL_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls ->
    RHL_ECB_ETbl_P qid
     (update_nth_val 1 osevent (Vint32 egrp'),
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))),petbl)
      (TcbMod.set tcbls ct (p, rdy, msg, sus')).
Proof.
introv Hpr Hrpt Htg Hey Hre.
destruct Hre as (Hrb1 & Hrb2 & Hrb3 & Hrb4 & Hrb5).
unfolds;
splits;
unfolds;
[ funfold Hrb1 | funfold Hrb2 | funfold Hrb3 | funfold Hrb4 | funfold Hrb5];
unfold V_OSEventType in *;
destruct Hrpt as (_ & _ & Hrpt);
funfold Hrpt;
intros;
unfold get in *; unfold TcbMap in *;
assert (tid = ct \/ tid <> ct) by tauto;
destruct H0;
rewrite TcbMod.set_sem in H;
try (subst;
rewrite TcbMod.beq_refl in H;
inverts H);
rewrite tidspec.neq_beq_false in H; try auto;
pose proof prio_wt_inq_tid_neq;
specialize H1 with (prio':= prio);
lets Hpi: H1 Hey Hpr;
rewrite Hpi;
clear Hpi;
lets Hnp: Hrpt H0 H Htg;
[ try eapply Hrb1 in H | try eapply Hrb2 in H | try eapply Hrb3 in H | try eapply Hrb4 in H | try eapply Hrb5 in H];
splits; try eapply nth_upd_neqrev; try pauto.
Qed.


Lemma R_ECB_ETbl_P_hold_for_update_sem_to_rdy
: forall tcbls ct p qid wt msg osevent etbl y ey egrp' bitx ptbl vhold petbl sus sus',
      Int.unsigned p < 64 ->
      y = p >>ᵢ $ 3 ->
      bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
      R_PrioTbl_P ptbl tcbls vhold ->
      TcbMod.get tcbls ct = Some (p, wait (os_stat_sem qid) wt, msg, sus) ->
      R_ECB_ETbl_P qid (osevent, etbl,petbl) tcbls ->
      nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 ey ->
      R_ECB_ETbl_P qid
       (update_nth_val 1 osevent (Vint32 egrp'),
         update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (ey&ᵢInt.not bitx)), petbl)
       (TcbMod.set tcbls ct (p, rdy, msg, sus')).
Proof.
introv Hpr Hy Hbitx Hrpt Htg Hre Hey.
funfold Hre.
unfolds.
splits.
eapply RLH_ECB_ETbl_P_hold_for_update_sem_to_st; try eauto.
eapply RHL_ECB_ETbl_P_hold_for_update_sem_to_rdy; try eauto.
simpl in *.
eapply Event_Type_P_hold_for_update; try auto.
Qed.

Lemma ECBList_P_high_tcb_block_hold_sem_to_rdy:
  forall  ectrl head tail msgql ecbls tcbls ptcb prio  m qid time sus sus',
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, wait (os_stat_sem qid) time, m, sus) ->
    EcbMod.get ecbls qid = None ->
    ECBList_P head tail ectrl msgql ecbls 
              (TcbMod.set tcbls ptcb (prio, rdy, m, sus')).
Proof.
  inductions ectrl.
  intros.
  simpl.
  simpl in H.
  auto.
  intros.
  simpl in H.
  mytac.
  destruct msgql; tryfalse.
  destruct a.
  destruct p. (* new add *)
  rename H3 into Hpetbl; rename H4 into H3. (* new add *)
  mytac.
  simpl.
  exists x.
  splits; auto.
  unfolds.
  destruct H2 as (Hr1 & Hr2 & Hr3).
  destruct Hr1 as (Hra3 & Hra1 & Hra2 & Hra4 & Hra5).
  destruct Hr2 as (Hrb3 & Hrb1 & Hrb2 & Hrb4 & Hrb5).
  simpl in Hr3.
  splits.
  unfolds.
  splits;
  unfolds;
  intros;
  [eapply Hra3 in H6 | eapply Hra1 in H6 | eapply Hra2 in H6 | eapply Hra4 in H6 | eapply Hra5 in H6];
  mytac;
   assert (x3 = ptcb \/ x3 <> ptcb) by tauto;
  destruct H7;
  try (subst;
    unfold get in H6; simpl in H6;
    rewrite H0 in H6;
    inverts H6;
    eapply EcbMod.join_sig_get in H3;
    rewrite H3 in H1;
    inverts H1);
    try (subst;
    unfold get in H6; simpl in H6;
    rewrite H0 in H6;
    inverts H6);
    repeat eexists;
    rewrite TcbMod.set_sem;
    rewrite tidspec.neq_beq_false; eauto.
  unfolds;
  splits;
  unfolds;
  intros;
  assert (tid = ptcb \/ tid <> ptcb) by tauto;
    destruct H6;
    try subst;
    rewrite TcbMod.set_sem in H2;
    try (rewrite TcbMod.beq_refl in H2; inverts H2);
    rewrite tidspec.neq_beq_false in H2; eauto.
    simpl; auto.
    eapply R_ECB_PETbl_P_hold_for_set_rdy; eauto.
    introv Hf. destruct Hf as (qd & wt & Hf). inverts Hf.
  do 3 eexists; splits; eauto.
  eapply IHectrl; eauto.
  eapply  ecbmod_joinsig_get_none; eauto.
Qed.

Lemma ECBList_P_hold_for_update_sem_to_rdy
: forall head (els1 els2: list os_inv.EventCtr) osevent etbl osevent' etbl' ecblist1 ecblist2 ecbcurl ecbls 
              tcbls ct p wt msg ey egrp' y bitx qid ptbl vhold n wls petbl sus sus',
    Int.unsigned p < 64 ->
   y = p >>ᵢ $ 3 ->
   bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
  R_PrioTbl_P ptbl tcbls vhold ->
  length els1 = length ecblist1 ->
  RH_TCBList_ECBList_P ecbls tcbls ct ->
  TcbMod.get tcbls ct = Some (p, wait (os_stat_sem qid) wt, msg, sus) ->
  EcbMod.get ecbls qid = Some (abssem n, wls) ->
  In ct wls ->
  get_ectr (Vptr qid) head els1  = None ->
  get_ectr (Vptr qid) head (els1 ++ ((osevent,etbl,petbl) :: nil))  = Some (osevent,etbl,petbl) ->
  ECBList_P head Vnull (els1 ++ ((osevent,etbl,petbl) :: nil) ++ els2) 
                        (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2) ecbls tcbls ->
  nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 ey ->
  osevent' = update_nth_val 1 osevent (Vint32 egrp') ->
  etbl' = update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (ey&ᵢInt.not bitx)) ->
  ECBList_P head Vnull (els1 ++ ((osevent',etbl',petbl) :: nil) ++ els2) 
                        (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2)
                         (EcbMod.set ecbls qid (abssem n, remove_tid ct wls))
                        (TcbMod.set tcbls ct (p, rdy, msg, sus'))
.
Proof.
introv Hpr Hy Hbitx Hrpt Hl Hrte Htg Heg Hi Hgptr1.
introv Hgptr2 Hep Hey Het' Hetbl'.
assert (Hels1: els1 = nil \/ els1 <> nil) by tauto.
destruct Hels1.
subst els1.
assert (ecblist1 = nil) by (eapply length_zero_nil; simpl in *; auto).
subst ecblist1.
simpl in *.
mytac.
destruct (beq_addrval qid x) eqn: eq1.
Focus 2.
destruct (V_OSEventListPtr osevent); try tryfalse; destruct v; try tryfalse.
apply beq_addrval_eq in eq1.
subst x.
exists qid.
splits; try auto.
eapply R_ECB_ETbl_P_hold_for_update_sem_to_rdy; try eauto.
eapply R_ECB_PETbl_upd_hold_gen'; eauto.
eapply R_ECB_PETbl_P_high_tcb_block_hold''; eauto.
introv Hf. destruct Hf as (qd0 & wt0 & Hf). inverts Hf.
introv Hf. destruct Hf as (qd0 & wt0 & Hf). inverts Hf.
exists (abssem n, remove_tid ct wls) x1 x2.
splits; try auto.
unfold V_OSEventListPtr in *.
eapply nth_upd_neqrev; try pauto.
unfold sig. unfold EcbMap.
eapply EcbMod_get_join_sig_set; try eauto.
eapply ejoin_get_none_r; [idtac | eauto].
eapply EcbMod.map_get_sig.
lets Heg': EcbMod.join_sig_get H3.
destruct x0.
rewrite Heg in Heg'.
inverts Heg'.
eapply RLH_ECBData_P_hold_sem; auto.
eapply ECBList_P_high_tcb_block_hold_sem_to_rdy; try eauto.
eapply ejoin_get_none_r; [idtac | eauto].
eapply EcbMod.map_get_sig.
(* els1 <> nil *)
lets Hsp: Mbox_common.ecblist_p_decompose Hl Hep.
simpl in *.
mytac.
lets Hx2: get_ectr_sing H Hgptr1 Hgptr2.
destruct H3; rewrite H1 in Hx2; inverts Hx2.
eapply ecblist_p_compose; try eauto.
Focus 2.
eapply ECBList_P_high_tcb_block_hold_sem_to_rdy; try eauto.
eapply ejoin_get_none_l; [idtac | eauto].
eapply EcbMod.join_sig_get; eauto.
eapply EcbMod.my_joinsig_join_set; try eauto.
simpl.
exists qid.
splits; try auto.
eapply R_ECB_ETbl_P_hold_for_update_sem_to_rdy; try eauto.
eapply R_ECB_PETbl_upd_hold_gen'; eauto.
eapply R_ECB_PETbl_P_high_tcb_block_hold''; eauto.
introv Hf. destruct Hf as (qd0 & wt0 & Hf). inverts Hf.
introv Hf. destruct Hf as (qd0 & wt0 & Hf). inverts Hf.
exists (abssem n, remove_tid ct wls) x4 x5.
splits; try auto.
unfold V_OSEventListPtr in *.
eapply nth_upd_neqrev; try pauto.
unfold sig. unfold EcbMap.
eapply EcbMod_get_join_sig_set; try eauto.
eapply ejoin_get_none_r; [idtac | eauto].
eapply EcbMod.map_get_sig.
lets Heg': EcbMod.join_sig_get H7.
destruct x3.
lets Heg2: EcbMod.join_get_r H2 Heg'.
rewrite Heg in Heg2.
inverts Heg2.
eapply RLH_ECBData_P_hold_sem; auto.
eapply ECBList_P_high_tcb_block_hold_sem_to_rdy; try eauto.
eapply ejoin_get_none_r; [idtac | eauto].
eapply EcbMod.map_get_sig.
Unshelve.
exact nil.
exact nil.
Qed.

Lemma RH_TCBList_ECBList_P_hold_for_sem_to_rdy
: forall tcbls ct p qid wt msg ecbls n wls sus sus',
  TcbMod.get tcbls ct = Some (p, wait (os_stat_sem qid) wt, msg, sus) ->
  EcbMod.get ecbls qid = Some (abssem n, wls) ->
  In ct wls ->
  RH_TCBList_ECBList_P ecbls tcbls ct ->
  RH_TCBList_ECBList_P (EcbMod.set ecbls qid (abssem n, remove_tid ct wls)) 
                                                    (TcbMod.set tcbls ct (p, rdy, msg, sus')) ct.
Proof.
introv Htg Heg Hi Hrte.
destruct Hrte as (Hr1 & Hr2 & Hr3 & Hr4 & Hr5).
unfolds;
splits;
unfolds;
[ funfold Hr1;
  rename H0 into Hpostq1; rename H1 into H0; rename H2 into Hpostq2
 | funfold Hr2 | funfold Hr3 | funfold Hr4; rename H2 into Hownp | funfold Hr5];
try splits;
intros;
try (assert (eid = qid \/ eid <> qid) by tauto;
 rewrite EcbMod.set_sem in H1;
destruct H2;
try (subst;
rewrite EcbMod.beq_refl in H1;
destruct H1;
inverts H1);
try (rewrite tidspec.neq_beq_false in H1; try auto;
try eapply H in H1;
try eapply Hpostq1 in H1;
do 4 destruct H1;
rewrite TcbMod.set_sem;
assert (Ht: tid = ct \/ tid <> ct) by tauto;
destruct Ht;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Htg in H1;
inverts H1);
rewrite tidspec.neq_beq_false; try eauto)).
2 : { (* new add about postq *)
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H2;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H1; try auto;
try (eapply Hpostq2 in H1;
do 4 destruct H1;
 assert (eid = qid \/ eid <> qid) by tauto;
destruct H3;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Heg in H1;
destruct H1;
tryfalse);
rewrite tidspec.neq_beq_false; try eauto).
}
Focus 5.
{
  assert (eid = qid \/ eid <> qid) by tauto;
 rewrite EcbMod.set_sem in H2;
destruct H3;
try (subst;
rewrite EcbMod.beq_refl in H2;
destruct H2;
inverts H2);
try (rewrite tidspec.neq_beq_false in H2; try auto;
eapply H in H2;
do 4 destruct H2;
rewrite TcbMod.set_sem;
assert (tid = ct \/ tid <> ct) by tauto;
destruct H4;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Htg in H2;
inverts H2);
rewrite tidspec.neq_beq_false; try eauto).
}
Unfocus.
Focus 2.
{
  rewrite TcbMod.set_sem.
  assert (ct = tid \/ ct <> tid) by tauto.
  destruct H1.
  subst. eapply in_remove_tid_false in H2. tryfalse.
  rewrite tidspec.neq_beq_false; try auto.
  eapply H.
  split; try eauto.
  eapply tidneq_inwt_in with (x1:= wls) in H1.
  rewrite H1 in H2. auto.
}
Unfocus.
{
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H2;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H1; try auto;
try (eapply H0 in H1;
do (* 3 *) 4 destruct H1;
 assert (eid = qid \/ eid <> qid) by tauto;
destruct H3;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Heg in H1;
destruct H1;
tryfalse);
rewrite tidspec.neq_beq_false; try eauto).
}
{
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H2;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H1; try auto.
eapply H0 in H1.
do 2 destruct H1.
 assert (eid = qid \/ eid <> qid) by tauto.
destruct H3.
subst.
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Heg in H1.
destruct H1; inverts H1.
rewrite EcbMod.beq_refl.
exists x (remove_tid ct x0).
split; auto.
eapply tidneq_inwt_in with (x1:= x0) in H2.
rewrite <- H2 in H3. auto.
rewrite tidspec.neq_beq_false; try eauto.
}
{
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H2;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H1; try auto;
try (eapply H0 in H1;
do 2 destruct H1;
 assert (eid = qid \/ eid <> qid) by tauto;
destruct H3;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Heg in H1;
destruct H1;
tryfalse);
rewrite tidspec.neq_beq_false; try eauto).
}
{
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H3;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H2; try auto;
try (eapply H0 in H2;
do 3 destruct H2;
 assert (eid = qid \/ eid <> qid) by tauto;
destruct H4;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Heg in H2;
destruct H2;
tryfalse);
rewrite tidspec.neq_beq_false; try eauto).
}
eapply rh_tcblist_ecblist_mutex_owner_set'; eauto.
apply Mutex_owner_hold_for_set_tcb; auto.
(* new add about RH_TCBList_ECBList_MUTEX_OWNER_P *)
    eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_ecb;
    try eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
    intro Hf.
    destruct Hf as (vpip & vo & Hf).
    inverts Hf.
{ (* new add os_stat_port *)
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H2;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H1; try auto.
eapply H0 in H1.
destruct H1.
 assert (eid = qid \/ eid <> qid) by tauto.
destruct H3.
subst.
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Heg in H1.
destruct H1; inverts H1.
rewrite tidspec.neq_beq_false; try eauto.
}
Qed.

Lemma ecblist_p_decompose_new:
  forall l1 ll1 l2 ll2 head ecbls tcbls eptr curl ecbcurl,
    length l1 = length ll1 ->
    get_ectr (Vptr eptr) head l1  = None ->
    get_ectr (Vptr eptr) head (l1 ++ (curl :: nil))  = Some curl ->
    ECBList_P head Vnull
              (l1++ (curl :: nil) ++ l2) (ll1 ++ (ecbcurl :: nil) ++ ll2) ecbls tcbls ->
    exists ecbls1 ecbls2,
      ECBList_P head (Vptr eptr) l1 ll1 ecbls1 tcbls /\
      ECBList_P (Vptr eptr) Vnull ((curl :: nil) ++ l2) ((ecbcurl :: nil) ++ ll2) ecbls2 tcbls /\
      EcbMod.join ecbls1 ecbls2 ecbls /\ 
      (get_last_ptr l1 = None \/ get_last_ptr l1 = Some (Vptr eptr)).
Proof.
introv Hl Hgptr1 Hgptr2 Hep.
assert (Hl1: l1 = nil \/ l1 <> nil) by tauto.
destruct Hl1.
subst l1.
assert (ll1 = nil) by (eapply length_zero_nil; simpl in *; auto).
subst ll1.
simpl in *.
destruct curl.
destruct p. (* new add *)
mytac.
destruct (beq_addrval eptr x) eqn: eq1.
Focus 2.
destruct (V_OSEventListPtr v0); try tryfalse; destruct v2; try tryfalse. (*v,v1 -> v0, v2 *)
apply beq_addrval_eq in eq1.
subst x.
do 2 eexists.
splits; try eauto.
exists eptr. splits; try auto.
do 3 eexists. splits; eauto.
apply EcbMod.map_join_comm.
apply EcbMod.map_join_emp.
lets Hsp: Mbox_common.ecblist_p_decompose Hl Hep.
simpl in *.
destruct curl.
destruct p. (* new add *)
mytac.
lets Hx2: get_ectr_sing H Hgptr1 Hgptr2.
destruct H3; rewrite H1 in Hx2; inverts Hx2.
do 2 eexists. splits; try eauto.
exists eptr. splits; try auto.
do 3 eexists. splits; eauto.
Qed.

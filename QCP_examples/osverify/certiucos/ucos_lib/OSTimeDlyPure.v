Require Import ucos_include. 
Require Import Lia.
Require Import os_inv.

(**Lemmas for OSTimeDelay**)
(*
Lemma Gooda_timedly :
  Gooda timedly.
Proof.
  unfold Gooda.
  intros.
  unfold timedly in *.
  destruct H0.
  unfolds in H0.
  destruct H0 as (v0 & Hvl & Hv & Heq & Ho).
  subst.
  splits; auto.
  branch 1.
  eexists; mytac; auto.
  destruct H0.
  unfolds in H0.
  mytac.
  branch 2.
  do 4 eexists; mytac; auto.
  do 3 eexists; splits; eauto.
  eapply abs_disj_get_merge; eauto.
  eapply abst_disj_merge_set_eqq; eauto.
  eapply OSAbstMod.disj_sym; auto.
  apply OSAbstMod.disj_sym.
  eapply abst_get_set_disj;eauto.
  eapply OSAbstMod.disj_sym; auto.
  destruct H0.
  unfolds in H0.
  mytac;auto.
  branch 3.
  unfolds.
  eexists.
  splits; eauto.
  do 4 eexists; splits; eauto.
  eapply abs_disj_get_merge; eauto.
  unfolds in H0.
  mytac;auto.
  branch 4.
  unfolds.
  do 6 eexists;splits; eauto.
  eapply abs_disj_get_merge; eauto.
Qed.
*)


Lemma R_PrioTbl_P_hold1:
  forall vl tcb tid prio st msg sus st' adrv,
    R_PrioTbl_P vl tcb adrv ->
    TcbMod.get tcb tid = Some (prio, st, msg, sus) ->
    R_PrioTbl_P vl (TcbMod.set tcb tid (prio, st', msg, sus)) adrv.
Proof.
  intros.
  unfold R_PrioTbl_P in *.
  simpljoin;try splits.
  intros.
  lets H100 : H H3 H4 H5.
  simpljoin;try splits.
  rewrite TcbMod.set_sem.
  unfold get in H6; simpl in H6.
  rewrite H6.
  remember (tidspec.beq tid tcbid) as bool; destruct bool.
  symmetry in Heqbool; apply tidspec.beq_true_eq in Heqbool.
  subst.
  rewrite H0 in H6.  
  inverts H6.
  eauto.
  eauto.
  intros.
  rewrite TcbMod.set_sem in H3.
  remember (tidspec.beq tid tcbid) as bool; destruct bool.
  inverts H3.
  symmetry in Heqbool; apply tidspec.beq_true_eq in Heqbool.
  subst.
  eapply H1; eauto.
  eapply H1; eauto.
  eapply R_Prio_NoChange_Prio_hold; eauto.
Qed.

(* new add by csy *)

Lemma prio_available_hold_same_prio:
forall tls pip tid p st sus m st' m' sus',
TcbMod.get tls tid = Some (p, st, m, sus) ->
prio_available pip tls ->
prio_available pip (TcbMod.set tls tid (p, st', m', sus')).
Proof.
unfold prio_available.
intros.
rewrite TcbMod.set_sem in *.
destruct (tidspec.beq tid t) eqn: eq1;
eapply H0; eauto.
inverts H1.
eauto.
Qed.

Lemma prio_available_hold_gen:
forall tls pip tid p st m sus,
Int.eq pip p = false ->
prio_available pip tls ->
prio_available pip (TcbMod.set tls tid (p, st, m, sus)).
Proof.
unfold prio_available.
intros.
rewrite TcbMod.set_sem in *.
destruct (tidspec.beq tid t) eqn: eq1.
inverts H1; auto.
eapply H0; eauto.
Qed.

Lemma RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb:
forall ecbls tcbls tid prio st sus m st' m' sus',
TcbMod.get tcbls tid = Some (prio, st, m, sus) ->
RH_TCBList_ECBList_MUTEX_OWNER_P ecbls tcbls ->
RH_TCBList_ECBList_MUTEX_OWNER_P ecbls (TcbMod.set tcbls tid (prio, st', m', sus')).
Proof.
intros.
funfold H0.
unfolds.
splits; intros.
eapply prio_available_hold_same_prio; eauto.
eapply prio_available_hold_same_prio; eauto.
rewrite TcbMod.set_sem in *.
destruct (tidspec.beq tid tid0) eqn: eq1.
eapply tidspec.beq_true_eq in eq1.
subst. inverts H4.
eapply H1; eauto.
eapply H1; eauto.
eapply H2;eauto.
(* eapply H3; eauto. *)
Qed.

Lemma RH_TCBList_ECBList_MUTEX_OWNER_P_hold_ecb:
forall ecbls tcbls eid st wl,
~ (exists pip o, st = absmutexsem pip o) ->
RH_TCBList_ECBList_MUTEX_OWNER_P ecbls tcbls ->
RH_TCBList_ECBList_MUTEX_OWNER_P (EcbMod.set ecbls eid (st,wl)) tcbls.
Proof.
intros.
funfold H0.
unfolds.
splits; intros;
try rewrite EcbMod.set_sem in *;
try destruct (tidspec.beq eid eid0) eqn: eq1;
try destruct (tidspec.beq eid eid1) eqn: eq1;
try (eapply tidspec.beq_true_eq in eq1;
subst; inverts H3;
destruct H; eauto).
eapply H0; eauto.
eapply H1; eauto.
destruct (tidspec.beq eid eid2) eqn: eq2.
eapply tidspec.beq_true_eq in eq2.
subst. inverts H4.
destruct H. eauto.
eapply H2; eauto.
Qed.

(* end new add by csy *)

Lemma RH_TCBList_ECBList_P_hold1:
  forall tid ecbls tcbls prio st msg sus i,
    RH_TCBList_ECBList_P ecbls tcbls tid ->
    TcbMod.get tcbls tid = Some (prio, st, msg, sus) ->
    (st = rdy \/ exists n, st = wait os_stat_time n) ->
    RH_TCBList_ECBList_P ecbls (TcbMod.set tcbls tid (prio, wait os_stat_time i, msg, sus)) tid.
Proof.
  introv  Hst Hget Hr .
  unfolds in Hst.
  destruct Hst  as (Hr1 & Hr2 & Hr3 & Hr4 & Hr5).
  unfolds; splits; auto.
  unfolds in Hr1.
  destruct Hr1 as (Hrr1 & Hrr2 & Hrr3& Hrr4).
(*   destruct Hr1 as (Hrr1 & Hrr2). *)
  unfolds.
  splits.
  introv Hpr.
  apply Hrr1 in Hpr.
  simpljoin;try splits.
  assert (tid = tid0  \/ tid <> tid0) by tauto.
  destruct H0.
  subst tid0.
  unfold get in H; simpl in H.
  rewrite Hget in H.
  inverts H.
  destruct Hr;simpljoin;try splits; tryfalse.
  exists x0 x1 x2.
  erewrite tcbmod_neq_set_get; eauto.
  (* Hrr2*)
  introv Hpr.
  apply Hrr2 in Hpr.
  simpljoin;try splits.
  assert (tid = tid0  \/ tid <> tid0) by tauto.
  destruct H0. 
  subst tid0.
  unfold get in H; simpl in H.
  rewrite Hget in H.
  inverts H.
  destruct Hr;simpljoin;try splits; tryfalse.
  exists x0 x1 x2.
  erewrite tcbmod_neq_set_get; eauto.
 (* Hrr3*)
  intros.
  assert (tid = tid0  \/ tid <> tid0) by tauto.
  destruct H0.
  subst tid.
  rewrite TcbMod.set_sem in H.
  assert (tidspec.beq tid0 tid0 = true).
  eapply tidspec.eq_beq_true;  eauto.
  rewrite H0 in H.
  inverts H.
  rewrite tcbmod_neq_set_get in H; eauto.
 (* Hrr4*)
  intros.
  assert (tid = tid0  \/ tid <> tid0) by tauto.
  destruct H0.
  subst tid.
  rewrite TcbMod.set_sem in H.
  assert (tidspec.beq tid0 tid0 = true).
  eapply tidspec.eq_beq_true;  eauto.
  rewrite H0 in H.
  inverts H.
  rewrite tcbmod_neq_set_get in H; eauto.
  unfolds.
  destruct Hr2 as (Hra & Hrb).
  split.
  intros.
  apply Hra in H.
   simpljoin;try splits.
  assert (tid = tid0  \/ tid <> tid0) by tauto.
  destruct H0.
  subst tid0.
  unfold get in H; simpl in H.
  rewrite Hget in H.
  inverts H.
  destruct Hr;simpljoin;try splits; tryfalse.
  do 3 eexists.
  erewrite tcbmod_neq_set_get; eauto.
  intros.
  assert (tid = tid0  \/ tid <> tid0) by tauto.
  destruct H0.
  subst tid.
  rewrite TcbMod.set_sem in H.
  assert (tidspec.beq tid0 tid0 = true).
  eapply tidspec.eq_beq_true;  eauto.
  rewrite H0 in H.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hrb in H.
  eauto.
   unfolds.
  destruct Hr3 as (Hra & Hrb).
  split.
  intros.
  apply Hra in H.
   simpljoin;try splits.
  assert (tid = tid0  \/ tid <> tid0) by tauto.
  destruct H0.
  subst tid0.
  unfold get in H; simpl in H.
  rewrite Hget in H.
  inverts H.
  destruct Hr;simpljoin;try splits; tryfalse.
  do 3 eexists.
  erewrite tcbmod_neq_set_get; eauto.
  intros.
  assert (tid = tid0  \/ tid <> tid0) by tauto.
  destruct H0.
  subst tid.
  rewrite TcbMod.set_sem in H.
  assert (tidspec.beq tid0 tid0 = true).
  eapply tidspec.eq_beq_true;  eauto.
  rewrite H0 in H.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hrb in H.
  eauto.
  destruct Hr4 as (Hra & Hrb).
  split.
  intros.
  apply Hra in H.
   simpljoin;try splits.
  assert (tid = tid0  \/ tid <> tid0) by tauto.
  destruct H3. (* change: H2 -> H3 *)
  subst tid0.
  unfold get in H; simpl in H.
  rewrite Hget in H.
  inverts H.
  destruct Hr;simpljoin;try splits; tryfalse.
  do 3 eexists.
  erewrite tcbmod_neq_set_get; eauto.
  split.
  intros.
  assert (tid = tid0  \/ tid <> tid0) by tauto.
  destruct H0.
  subst tid.
  rewrite TcbMod.set_sem in H.
  assert (tidspec.beq tid0 tid0 = true).
  eapply tidspec.eq_beq_true;  eauto.
  rewrite H0 in H.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hrb in H.
  eauto.
 
  split. (* new add *)
  unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
  intros.
  destruct Hrb as (Hrb&Hx).
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0; intros.
  subst tid.
  rewrite TcbMod.set_a_get_a.
  apply Hx in H.
  simpljoin;try splits.
  unfold get in H; simpl in H.
  rewrite H in Hget;inverts Hget.
  do 3 eexists;eauto.
  auto. (* new add *)
  apply CltEnvMod.beq_refl.
  rewrite TcbMod.set_a_get_a' .
  eapply Hx;eauto.
  apply tidspec.neq_beq_false; auto.

  (* new add about RH_TCBList_ECBList_MUTEX_OWNER_P *)
   destruct Hrb as (_ & _ & Hrb).
  eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
  (* new add about RH_TCBList_ECBList_PORT_P *)
  destruct Hr5.
  split.
  { intros. destruct H1.
    specialize (H _ _ _ (Logic.conj H1 H2)) as [? [? [? [? ?]]]].
    assert (tid = tid0  \/ tid <> tid0) by tauto.
    destruct H3. (* change: H2 -> H3 *)
    subst tid0.
    unfold get in H; simpl in H.
    rewrite Hget in H.
    inverts H.
    destruct Hr;simpljoin;try splits; tryfalse.
    do 4 eexists.
    erewrite tcbmod_neq_set_get; eauto. }
  { intros.
    simpljoin1.
    assert (tid0 = tid \/ tid0 <> tid) as [ | ] by tauto.
    + subst. erewrite get_set_eq in H1. inverts H1.
    + erewrite get_set_neq in H1;eauto. }
Qed.

Lemma ecb_etbl_prop:
  forall st  b prio msg sus x v v0 tcbls i,
    st = rdy \/ (exists n, st = wait os_stat_time n) ->
    TcbMod.get tcbls (b, Int.zero) = Some (prio, st, msg, sus) ->
    R_ECB_ETbl_P x (v, v0) tcbls ->
    R_ECB_ETbl_P x (v, v0)
                 (TcbMod.set tcbls (b, Int.zero)
                             (prio, wait os_stat_time i, msg, sus)).
Proof.
  introv  Hst Hget Hr .
  destruct v. (* new add *)
  unfolds in Hr.
  unfolds.
  destruct Hr as (Hr1 & Hr2 & Hr3).
  unfolds in Hr1.
  unfolds in Hr2.
  destruct Hr1 as (Hr11 & Hr12 & Hr13 & Hr14 & Hrl5).
  destruct Hr2 as (Hr22 & Hr23 & Hr33 & Hr43 & Hr5).
  splits;unfolds.
  splits.
  introv Hpr Hpr1.
  lets Hres : Hr11 Hpr Hpr1.
  simpljoin;try splits.
  assert (x0 = (b, Int.zero)  \/ x0 <> (b, Int.zero) ) by tauto.
  destruct H0.
  subst x0.
  unfold get in H; simpl in H.
  rewrite Hget in H.
  inverts H.
  destruct Hst;simpljoin;try splits; tryfalse.
  exists x0 x1 x2.
  erewrite tcbmod_neq_set_get; eauto.
  introv Hpr Hpr1.
  lets Hres : Hr12 Hpr Hpr1.
  simpljoin;try splits.
  assert (x0 = (b, Int.zero)  \/ x0 <> (b, Int.zero) ) by tauto.
  destruct H0.
  subst x0.
  unfold get in H; simpl in H.
  rewrite Hget in H.
  inverts H.
  destruct Hst;simpljoin;try splits; tryfalse.
  exists x0 x1 x2.
  erewrite tcbmod_neq_set_get; eauto.
  introv Hpr Hpr1.
  lets Hres : Hr13 Hpr Hpr1.
  simpljoin;try splits.
  assert (x0 = (b, Int.zero)  \/ x0 <> (b, Int.zero) ) by tauto.
  destruct H0.
  subst x0.
  unfold get in H; simpl in H.
  rewrite Hget in H.
  inverts H.
  destruct Hst;simpljoin;try splits; tryfalse.
  exists x0 x1 x2.
  erewrite tcbmod_neq_set_get; eauto.
  introv Hpr Hpr1.
  lets Hres : Hr14 Hpr Hpr1.
  simpljoin;try splits.
  assert (x0 = (b, Int.zero)  \/ x0 <> (b, Int.zero) ) by tauto.
  destruct H0.
  subst x0.
  unfold get in H; simpl in H.
  rewrite Hget in H.
  inverts H.
  destruct Hst;simpljoin;try splits; tryfalse.
  exists x0 x1 x2.
  erewrite tcbmod_neq_set_get; eauto.
  (* new add *)
  { introv Hpr Hpr1. 
    lets Hres : Hrl5 Hpr Hpr1.
    simpljoin;try splits.
    assert (x0 = (b, Int.zero)  \/ x0 <> (b, Int.zero) ) by tauto.
    destruct H0.
    subst x0.
    unfold get in H; simpl in H.
    rewrite Hget in H.
    inverts H.
    destruct Hst;simpljoin;try splits; tryfalse.
    exists x0 x1 x2 x3.
    erewrite tcbmod_neq_set_get; eauto. }
  splits.
  unfolds.
  intros.
  assert (tid = (b, Int.zero)  \/ tid <> (b, Int.zero) ) by tauto.
  destruct H0.
  subst tid.
  rewrite TcbMod.set_sem in H.
  assert (tidspec.beq(b, Int.zero) (b, Int.zero)= true).
  eapply tidspec.eq_beq_true;  eauto.
  rewrite H0 in H.
  inverts H.
  rewrite tcbmod_neq_set_get in H; eauto.
  unfolds.
  intros.
  assert (tid = (b, Int.zero)  \/ tid <> (b, Int.zero) ) by tauto.
  destruct H0.
  subst tid.
  rewrite TcbMod.set_sem in H.
  assert (tidspec.beq(b, Int.zero) (b, Int.zero)= true).
  eapply tidspec.eq_beq_true;  eauto.
  rewrite H0 in H.
  inverts H.
  rewrite tcbmod_neq_set_get in H; eauto.
  unfolds.
  intros.
  assert (tid = (b, Int.zero)  \/ tid <> (b, Int.zero) ) by tauto.
  destruct H0.
  subst tid.
  rewrite TcbMod.set_sem in H.
  assert (tidspec.beq(b, Int.zero) (b, Int.zero)= true).
  eapply tidspec.eq_beq_true;  eauto.
  rewrite H0 in H.
  inverts H.
  rewrite tcbmod_neq_set_get in H; eauto.
  unfolds.
  intros.
  assert (tid = (b, Int.zero)  \/ tid <> (b, Int.zero) ) by tauto.
  destruct H0.
  subst tid.
  rewrite TcbMod.set_sem in H.
  assert (tidspec.beq(b, Int.zero) (b, Int.zero)= true).
  eapply tidspec.eq_beq_true;  eauto.
  rewrite H0 in H.
  inverts H.
  rewrite tcbmod_neq_set_get in H; eauto.
  (* new add *)
  { unfolds.
  intros.
  assert (tid = (b, Int.zero)  \/ tid <> (b, Int.zero) ) by tauto.
  destruct H0.
  subst tid.
  rewrite TcbMod.set_sem in H.
  assert (tidspec.beq(b, Int.zero) (b, Int.zero)= true).
  eapply tidspec.eq_beq_true;  eauto.
  rewrite H0 in H.
  inverts H.
  rewrite tcbmod_neq_set_get in H; eauto. }
  unfolds in Hr3;auto.
Qed.

Lemma ecb_petbl_prop:
  forall st  b prio msg sus x v v0 tcbls i,
    st = rdy \/ (exists n, st = wait os_stat_time n) ->
    TcbMod.get tcbls (b, Int.zero) = Some (prio, st, msg, sus) ->
    R_ECB_PETbl_P x (v, v0) tcbls ->
    R_ECB_PETbl_P x (v, v0)
                 (TcbMod.set tcbls (b, Int.zero)
                             (prio, wait os_stat_time i, msg, sus)).
Proof.
  destruct v.
  introv  Hst Hget Hr .
  unfolds in Hr.
  unfolds.
  destruct Hr as (Hr1 & Hr2).
  unfolds in Hr1.
  unfolds in Hr2.
  splits;unfolds.
  introv Hpr Hpr1.
  lets Hres : Hr1 Hpr Hpr1.
  simpljoin;try splits.
  assert (x0 = (b, Int.zero)  \/ x0 <> (b, Int.zero) ) by tauto.
  destruct H0.
  subst x0.
  unfold get in H; simpl in H.
  rewrite Hget in H.
  inverts H.
  destruct Hst;simpljoin;try splits; tryfalse.
  exists x0 x1 x2.
  erewrite tcbmod_neq_set_get; eauto.

  intros.
  assert (tid = (b, Int.zero)  \/ tid <> (b, Int.zero) ) by tauto.
  destruct H0.
  subst tid.
  rewrite TcbMod.set_sem in H.
  assert (tidspec.beq(b, Int.zero) (b, Int.zero)= true).
  eapply tidspec.eq_beq_true;  eauto.
  rewrite H0 in H.
  inverts H.
  rewrite tcbmod_neq_set_get in H; eauto.
Qed.

Open Scope int_scope.
Open Scope Z_scope.

Lemma ECBList_P_hold1:
  forall l v ecbls mqls tcbls b i prio st msg sus,
    ECBList_P v Vnull l ecbls mqls tcbls ->
    TcbMod.get tcbls (b, Int.zero) = Some (prio, st, msg, sus) ->
    (st = rdy \/ exists n, st = wait os_stat_time n) ->
    Int.unsigned i <= 65535 ->
    Int.ltu ($ 0) i = true ->
    ECBList_P v Vnull l ecbls mqls (TcbMod.set tcbls (b, Int.zero) (prio, wait os_stat_time (Some i), msg, sus)).
Proof.
  introv Hep Hget Hst Hi Hint.
  inductions l.
  simpl.
  simpl in Hep.
  auto.
  unfold ECBList_P; fold ECBList_P.
  destruct ecbls.
  simpl in Hep.
  simpljoin;try splits; tryfalse.
  unfolds in Hep; fold ECBList_P in Hep.
  simpljoin;try splits.
  destruct a.
  destruct p. (* new add *)
  simpljoin;try splits.
  exists x.
  split; auto.
  split.
  eapply ecb_etbl_prop; eauto.
  split.
  eapply ecb_petbl_prop; eauto. (*add*)
  exists x0.
  eexists.
  exists x2.
  splits; eauto.
Qed.

Lemma RH_CurTCB_hold1 :
  forall tid tcbls prio st msg sus i,
    RH_CurTCB tid tcbls ->
    TcbMod.get tcbls tid = Some (prio, st, msg, sus) ->
    RH_CurTCB tid (TcbMod.set tcbls tid (prio, wait os_stat_time  i, msg, sus)).
Proof.
  intros.
  unfold RH_CurTCB in *.
  simpljoin;try splits.
  unfold get ; simpl.
  unfold get in H; simpl in H.
  rewrite H in H0.
  inverts H0.
  do 4 eexists.
  rewrite TcbMod.set_sem.
  rewrite TcbMod.beq_refl.
  auto.
Qed.

Open Scope code_scope.

Lemma event_wait_rl_tbl_grp':
  forall x10 x9 x8 x7 i10 i6 i5 i4 i3 i2 i1 i0 v'1 x,
    RL_TCBblk_P
      (x10
         :: x9
         :: x8
         :: x7
         :: Vint32 i10
         :: Vint32 i6
         :: Vint32 i5
         :: Vint32 i4
         :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: nil) ->
    array_type_vallist_match Int8u v'1 ->
    Int.eq (x&ᵢInt.not i2) ($ 0) = true ->
    RL_Tbl_Grp_P v'1 (Vint32 i0) ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned i3)) v'1 (Vint32 (x&ᵢInt.not i2)))
      (Vint32 (i0&ᵢInt.not i1)).
Proof.
  introv Hrl Harr  Hint Hrll.
  assert (if Int.eq (x&ᵢInt.not i2) ($ 0) then
            (x&ᵢInt.not i2)  = $ 0 else   (x&ᵢInt.not i2)  <> $ 0  ) by (apply Int.eq_spec).
  rewrite Hint in H.
  rewrite H.
  unfolds in Hrl.
  funfold Hrl.
  funfold Hrll.
  unfolds.
  introv Hn Hnth Hvin.
  assert (n <> (Z.to_nat (Int.unsigned (Int.shru x0 ($ 3)))) \/
          n = (Z.to_nat (Int.unsigned (Int.shru x0 ($ 3))))) by tauto.
  destruct H0.
  lets Hex : nth_upd_neq H0 Hnth.
  assert (Vint32 i0 = Vint32 i0) by auto.
  lets Hes : Hrll Hn Hex H1.
  destruct Hes.
  inverts Hvin.
  lets Hzx : math_prop_and H0; try lia; auto.
  splits.
  destruct H2.
  split.
  intros.
  apply H2.
  rewrite Int.and_assoc in H5. 
  rewrite Hzx in H5.
  auto.
  intros.
  apply H4 in H5.
  rewrite Int.and_assoc.
  rewrite Hzx ; auto.
  split.
  intros.
  destruct H3.
  rewrite Int.and_assoc in H4.
  rewrite Hzx in H4.
  apply H3; auto.  
  intros.
  rewrite Int.and_assoc.
  rewrite Hzx.
  apply H3; auto.
  subst n.
  lets Hdx : nth_upd_eq Hnth.
  inverts Hdx.
  inverts Hvin.
  assert ( 0 <= Int.unsigned x0 < 64) by lia.
  lets Hdd : math_prop_eq0 H0.
  split.
  split; auto.
  intros.
  rewrite Int.and_assoc.
  rewrite Hdd.
  rewrite Int.and_zero.
  auto.
  rewrite Int.and_assoc.
  rewrite Hdd.
  rewrite Int.and_zero.
  split.
  intros.
  apply math_lshift_neq_zero in H0.
  tryfalse.
  intros.
  clear -H1.
  false.
Qed.



Lemma event_wait_rl_tbl_grp:
  forall x10 x9 x8 x7 i10 i6 i5 i4 i3 i2 v'5 x0 i i1,
    RL_TCBblk_P
      (x10
         :: x9
         :: x8
         :: x7
         :: Vint32 i10
         :: Vint32 i6
         :: Vint32 i5
         :: Vint32 i4
         :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: nil) ->
    array_type_vallist_match Int8u v'5 ->
    nth_val' (Z.to_nat (Int.unsigned i3)) v'5 = Vint32 x0 ->
    RL_Tbl_Grp_P v'5 (Vint32 i) ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned i3)) v'5 (Vint32 (Int.or x0 i2)))
      (Vint32 (Int.or i i1)).
Proof.
  introv Hrl Harr Hnth Hrt.
  funfold Hrl.
  funfold Hrt.
  assert ( 0 <= Int.unsigned x < 64) as Hran by lia.
  clear H5 H13.
  unfolds.
  introv Hn Hnv Hvi.
  inverts Hvi.
  assert (n <> (Z.to_nat (Int.unsigned (Int.shru x ($ 3)))) \/
          n = (Z.to_nat (Int.unsigned (Int.shru x ($ 3))))) by tauto.
  destruct H.
  lets Hex : nth_upd_neq H Hnv.
  assert (Vint32 i = Vint32 i) by auto.
  lets Hexz : Hrt Hn Hex H0.
  destruct Hexz as (He1 & He2).
  split.
  split.
  intros.
  apply He1.
  rewrite Int.and_commut in H1.
  rewrite Int.and_or_distrib in H1.
  
  lets Hc : math_and_zero Hran Hn H.
  rewrite Hc in H1.
  rewrite Int.or_zero in H1.
  rewrite Int.and_commut.
  auto.
  intros.
  lets Hc : math_and_zero Hran Hn H.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib .
  rewrite Hc.
  rewrite Int.or_zero.
  rewrite Int.and_commut.
  apply He1; auto.
  lets Hc : math_and_zero Hran Hn H.
  split.
  intros.
  apply He2.
  rewrite Int.and_commut in H1.
  rewrite Int.and_or_distrib in H1.
  rewrite Hc in H1.
  rewrite Int.or_zero in H1.
  rewrite Int.and_commut.
  auto.
  intros.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib .
  rewrite Hc.
  rewrite Int.or_zero.
  rewrite Int.and_commut.
  apply He2; auto.
  subst n.
  lets Hins : nth_upd_eq  Hnv.
  inverts Hins.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib .
  split.
  split.
  intros.
  apply int_or_zero_split in H.
  destruct H.
  lets Hf : math_prop_neq_zero Hran.
  tryfalse.
  intros.
  apply int_or_zero_split in H.
  destruct H.
  apply math_prop_neq_zero2 in H0.
  tryfalse.
  auto.
  split.
  intros.
  apply int_ltu_true; auto.
  intros.
  rewrite math_prop_eq; auto.
  rewrite Int.and_idem.
  rewrite Int.or_commut.
  rewrite Int.or_and_absorb.
  auto.
Qed.

Lemma event_wait_rl_tbl_grp'':
  forall x10 x9 x8 x7 i10 i6 i5 i4 i3 i2 i1 i0 v'1 x,
    RL_TCBblk_P
      (x10
         :: x9
         :: x8
         :: x7
         :: Vint32 i10
         :: Vint32 i6
         :: Vint32 i5
         :: Vint32 i4
         :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: nil) ->
    array_type_vallist_match Int8u v'1 ->
    nth_val' (Z.to_nat (Int.unsigned i3)) v'1 = Vint32 x ->
    Int.eq (x&ᵢInt.not i2) ($ 0) = false ->
    RL_Tbl_Grp_P v'1 (Vint32 i0) ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned i3)) v'1 (Vint32 (x&ᵢInt.not i2)))
      (Vint32 i0).
Proof.
  introv Hrl Harr Htt Hnth Hrt.
  funfold Hrl.
  funfold Hrt.
  assert ( 0 <= Int.unsigned x0 < 64) as Hran by lia.
  clear H5 H13.
  unfolds.
  introv Hn Hnv Hvi.
  inverts Hvi.
  assert (n <> (Z.to_nat (Int.unsigned (Int.shru x0 ($ 3)))) \/
          n = (Z.to_nat (Int.unsigned (Int.shru x0 ($ 3))))) by tauto.
  destruct H.
  lets Hex : nth_upd_neq H Hnv.
  assert (Vint32 v' = Vint32 v') by auto.
  lets Hexz : Hrt Hn Hex H0.
  destruct Hexz as (He1 & He2).
  auto.
  subst n.
  lets Hins : nth_upd_eq  Hnv.
   apply nth_val'_imp_nth_val_int in Htt.
   assert (Vint32 v' = Vint32 v') by auto.
  lets Hdx : Hrt Hn Htt H.
  inverts Hins.
  split.
  split.
  destruct Hdx.
  intros.
  apply H0 in H2.
  subst.
  rewrite Int.and_commut.
  rewrite Int.and_zero.
  auto.
  intros.
  rewrite H0 in Hnth.
  rewrite Int.eq_true in Hnth.
  tryfalse.
  split.
  intros.
  destruct Hdx.
  apply H2 in H0.
  apply int_eq_false_ltu; eauto.
  intros.
  destruct Hdx.
  apply H2.
  apply int_eq_false_ltu; eauto.
  apply Int.eq_false.
  assert (   x <> $ 0  \/  x = $ 0) by tauto.
  destruct H3; auto.
  subst x.
  rewrite Int.and_commut in Hnth.
  rewrite Int.and_zero in Hnth.
  unfold Int.zero in Hnth.
  rewrite Int.eq_true in Hnth.
  tryfalse.
Qed.


Lemma low_stat_rdy_imp_high:
  forall a b c d e f g h i j k l st rtbl p t m sus,
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    RL_TCBblk_P  (a
                    :: b
                    :: c
                    :: d
                    :: Vint32 e
                    :: Vint32 st
                    :: Vint32 f
                    :: g
                    :: h :: i :: j :: k :: l :: nil)
    ->
    R_TCB_Status_P
      (a
         :: b
         :: c
         :: d
         :: Vint32 e
         :: Vint32 st
         :: Vint32 f
         :: g
         :: h :: i :: j :: k :: l :: nil)
      rtbl (p, t, m, sus) -> Int.eq st ($ OS_STAT_RDY) = true ->
    Int.eq e ($ 0) = true ->
    t = rdy .
Proof.
  introv Hz Hlen  Ht  Hr Heq Heqq.
  funfold Ht.
  unfolds in Hr.
  simpljoin;try splits.
  clear H0 H1 H2 H4.
  unfolds in H.
  unfolds in H3.
  simpljoin;try splits.
  unfolds in H0.
  unfolds in H1.
  unfolds in H2.
  unfolds in H3.
  unfolds in H4.
  unfold RdyTCBblk in *.
  unfold V_OSTCBStat in *; simpl in *.
  unfold WaitTCBblk in *; simpl in *.
  unfold V_OSTCBPrio,  V_OSTCBDly , V_OSTCBEventPtr in *; simpl in *.
  assert (Some (Vint32 x) = Some (Vint32 x)).
  auto.
  unfold Pos.to_nat in Hlen.
  simpl in Hlen.
  assert ( 0 <= Int.unsigned x < 64 ) by lia.
  lets Hdis : prio_rtbl_dec  Hz Hlen; eauto.
  assert (if Int.eq x4 ($ OS_STAT_RDY) then  x4  =($ OS_STAT_RDY)
          else x4 <> ($ OS_STAT_RDY)).
  apply Int.eq_spec.
  rewrite Heq in H24.
  subst.
  destruct Hdis as [Hd1 | Hd2].
  assert (Some (Vint32 x) = Some (Vint32 x) /\
          prio_in_tbl x rtbl). 
  split;eauto.
  eapply H in H24.
  destruct H24 as ( Had & H24).
  destruct H24.
  destruct H24.
  rename H25 into Hzd.
  (* destruct Hzd. inverts H9. *)
  destruct Hzd as (m0 & H25).
  (* eapply H3 in H9. *)
  inverts H25; auto.
  assert (Some (Vint32 e) = Some (Vint32 e)).
  auto.
  
  destruct H24.
  destruct H24.
  tryfalse.
  destruct H24.
  destruct H24.
  tryfalse.
  destruct H24.
  destruct H24.
  tryfalse.
  destruct H24.
  tryfalse.
  
  assert (Some (Vint32 x) = Some (Vint32 x) /\
          prio_not_in_tbl x  rtbl/\Some (Vint32 e) = Some (Vint32 e)).   
  splits; auto.
  eapply H0 in H24;auto.
  simpljoin;try splits.
  eapply ltu_eq_false in H24.
  unfold Int.zero in H24.
  rewrite Heqq in H24.
  tryfalse.
Qed.


Lemma low_stat_nordy_imp_high:
  forall a b c d e f g h i j st rtbl p t m sus,
    R_TCB_Status_P
      (a
         :: b
         :: c
         :: d
         :: Vint32 e
         :: Vint32 st
         :: f
         :: g
         :: h :: i :: j :: nil)
      rtbl (p, t, m, sus) -> (Int.eq st ($ OS_STAT_RDY) = false \/ Int.eq e ($ 0) = false) ->
    ~(t = rdy /\ sus = false).
Proof.
  introv Hr Heq.
  unfolds in Hr.
  simp join.
  introv Hf.
  clear H H1.
  destruct Hf.
  subst t.
  assert ( (p, rdy, m, sus) = (p, rdy, m, false)).
  rewrite H1;auto.
  apply H0 in H.
  simpljoin;try splits.
  unfolds in H.
  simpl in H.
  inverts H.
  simpl_hyp.
  repeat rewrite Int.eq_true in Heq.
  destruct Heq; tryfalse.
Qed.


Lemma RLH_Rdy_prioneq_prop_hold:
  forall p prio a rtbl t m grp sus,
    p <> prio ->
    0 <= Int.unsigned prio < 64 ->
    0 <= Int.unsigned p < 64 ->
    V_OSTCBPrio a = Some (Vint32 p) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RLH_RdyI_P a rtbl (p, t, m, sus)  ->
    RLH_RdyI_P a
               (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                               (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) (p, t, m, sus).
Proof.
  introv Hpneq Hr1 Hr2 Hvp  Hnth Hrl.
  unfolds in Hrl.
  unfolds.
  intros.
  eapply Hrl; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_in_tbl with (prio0 := prio0) (prio := prio); eauto.
Qed.


Lemma RHL_Rdy_prioneq_prop_hold:
  forall p prio a rtbl t m grp sus,
    p <> prio ->
    0 <= Int.unsigned prio < 64 ->
    0 <= Int.unsigned p < 64 ->
    V_OSTCBPrio a = Some (Vint32 p) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_RdyI_P a rtbl (p, t, m, sus)  ->
    RHL_RdyI_P a
               (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                               (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) (p, t, m, sus).
Proof.
  introv Hpneq Hr1 Hr2 Hvp  Hnth Hrl.
  unfolds in Hrl.
  unfolds.
  intros.
  lets Hs : Hrl H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  inverts Hvp.
  eapply prio_neq_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
Qed.

Lemma RLH_Suspend_prioneq_prop_hold:
  forall p prio a rtbl t m grp sus,
    p <> prio ->
    0 <= Int.unsigned prio < 64 ->
    0 <= Int.unsigned p < 64 ->
    V_OSTCBPrio a = Some (Vint32 p) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RLH_Suspend_P  a rtbl (p, t, m, sus)  ->
    RLH_Suspend_P  a
               (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                               (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) (p, t, m, sus).
Proof.
  introv Hpneq Hr1 Hr2 Hvp  Hnth Hrl.
  unfolds in Hrl.
  destruct Hrl as (Hrl1 & Hrl2).
  unfolds.
  split.
  intros.
  eapply Hrl1; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  intros.
  eapply Hrl2; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
Qed.

Lemma RHL_Suspend_prioneq_prop_hold:
  forall p prio a rtbl t m grp sus,
    p <> prio ->
    0 <= Int.unsigned prio < 64 ->
    0 <= Int.unsigned p < 64 ->
    V_OSTCBPrio a = Some (Vint32 p) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_Suspend_P a rtbl (p, t, m, sus)  ->
    RHL_Suspend_P a
               (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                               (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) (p, t, m, sus).
Proof.
  introv Hpneq Hr1 Hr2 Hvp  Hnth Hrl.
  unfolds in Hrl.
  destruct Hrl as (Hrl1 & Hrl2).
  unfolds.
  splits.
  intros.
  lets Hs : Hrl1 H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  inverts Hvp.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  intros.
  lets Hs : Hrl2 H.
  destruct Hs as (t0 & Hs).
  destruct Hs.
  exists t0.
  split.
  eauto.
  inverts H0.
  simpljoin;try splits; auto.
  unfolds in H0.
  unfolds.
  simpljoin;try splits; auto.
  inverts Hvp.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
Qed.


Lemma RLH_Wait_prioneq_prop_hold:
  forall p prio a rtbl t m sus grp,
    p <> prio ->
    0 <= Int.unsigned prio < 64 ->
    0 <= Int.unsigned p < 64 ->
    V_OSTCBPrio a = Some (Vint32 p) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RLH_TCB_Status_Wait_P a rtbl (p, t, m, sus) ->
    RLH_TCB_Status_Wait_P a
                          (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                          (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) (p, t, m, sus).
Proof.
  introv Hpneq Hr1 Hr2 Hvp  Hnth Hrl.
  unfolds in Hrl.
  unfolds.
  destruct Hrl as (Hrl1 & Hrl2 & Hrl2' & Hrl3 & Hrl3' & Hrl4 & Hrl4' & Hrl5 & Hrl5' & Hrl6' & Hrl7' & Hrl8' & Hrl9' & Hrl10' & Hrl11' & Hrl12' & Hrl13' & Hrl14').
  repeat match goal with 
  | |- _ /\ _ => split end.
  unfolds in Hrl1.
  unfolds.
  intros.
  eapply Hrl1; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  unfolds in Hrl2.
  unfolds.
  intros.
  eapply Hrl2; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  (* new add *)
  unfolds in Hrl2'.
  unfolds.
  intros.
  eapply Hrl2'; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_in_tbl with (prio0:= prio0) (prio:= prio); eauto.
  (* end of new add *)
  unfolds in Hrl3.
  unfolds.
  intros.
  eapply Hrl3; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
    (* new add *)
  unfolds in Hrl3'.
  unfolds.
  intros.
  eapply Hrl3'; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_in_tbl with (prio0:= prio0) (prio:= prio); eauto.
  (* end of new add *)
  unfolds in Hrl4.
  unfolds.
  intros.
  eapply Hrl4; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
    (* new add *)
  unfolds in Hrl4'.
  unfolds.
  intros.
  eapply Hrl4'; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_in_tbl with (prio0:= prio0) (prio:= prio); eauto.
  (* end of new add *)
  unfolds in Hrl5.
  unfolds.
  intros.
  eapply Hrl5; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
    (* new add *)
  unfolds in Hrl5'.
  unfolds.
  intros.
  eapply Hrl5'; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_in_tbl with (prio0:= prio0) (prio:= prio); eauto.
  (* end of new add *)
  unfolds in Hrl6'.
  unfolds.
  intros.
  eapply Hrl6'; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  (* new add by sus*)
  unfolds in Hrl7'.
  unfolds.
  intros.
  eapply Hrl7'; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  (* new add by sus*)
  unfolds in Hrl8'.
  unfolds.
  intros.
  eapply Hrl8'; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  (* new add by sus*)
  unfolds in Hrl9'.
  unfolds.
  intros.
  eapply Hrl9'; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  (* new add by sus*)
  unfolds in Hrl10'.
  unfolds.
  intros.
  eapply Hrl10'; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  (* new add by sus*)
  unfolds in Hrl11'.
  unfolds.
  intros.
  eapply Hrl11'; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  (* new add by port*)
  unfolds in Hrl12'.
  unfolds.
  intros.
  eapply Hrl12'; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  (* new add by port*)
  unfolds in Hrl13'.
  unfolds.
  intros.
  eapply Hrl13'; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  (* new add by port*)
  unfolds in Hrl14'.
  unfolds.
  intros.
  eapply Hrl14'; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
Qed.

Lemma RHL_Wait_prioneq_prop_hold:
  forall p prio a rtbl t m grp sus,
    p <> prio ->
    0 <= Int.unsigned prio < 64 ->
    0 <= Int.unsigned p < 64 ->
    V_OSTCBPrio a = Some (Vint32 p) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_TCB_Status_Wait_P a rtbl (p, t, m, sus) ->
    RHL_TCB_Status_Wait_P a
                          (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                          (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) (p, t, m, sus).
Proof.
  introv Hpneq Hr1 Hr2 Hvp  Hnth Hrl.
  unfolds in Hrl.
  unfolds.
  destruct Hrl as (Hrl1 & Hrl2 & Hrl3 & Hrl4 & Hrl5 & Hrl6 & Hrl7 & Hrl8 & Hrl9 & Hrl10 & Hrl11 & Hrl12 & Hrl13).
  splits.
  unfolds in Hrl1.
  unfolds.
  intros.
  lets Hex : Hrl1 H.
  inverts H.
  destruct Hex as (t_opt' & H_t & H & Hex). (* new add *)
  eexists. (* new add *)
  simpljoin;try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  unfolds in Hrl2.
  unfolds.
  intros.
  lets Hex : Hrl2 H.
  inverts H.
  (*   simpljoin;try splits; auto. *)
  (* new add *)
  destruct Hex as ((t_opt' & Hex) & Hptr & Hstat).
  splits; auto.
  exists t_opt'.
  destruct Hex as [ (Heq & [(Heq1 & H) | (Heq1 & H)]) | (Heq & H)];
  [ left; split; auto; left  | left; split; auto; right | right]; 
  simpljoin; try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_in_tbl_rev with (prio0:= prio0) (prio:= prio); eauto.
  (* end of new add *)
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  unfolds in Hrl3.
  unfolds.
  intros.
  lets Hex : Hrl3 H.
  inverts H.
    (*   simpljoin;try splits; auto. *)
  (* new add *)
  destruct Hex as ((t_opt' & Hex) & Hptr & Hstat).
  splits; auto.
  exists t_opt'.
  destruct Hex as [ (Heq & [(Heq1 & H) | (Heq1 & H)]) | (Heq & H)];
  [ left; split; auto; left  | left; split; auto; right | right]; 
  simpljoin; try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_in_tbl_rev with (prio0:= prio0) (prio:= prio); eauto.
  (* end of new add *)
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
   unfolds in Hrl4.
  unfolds.
  intros.
  lets Hex : Hrl4 H.
  inverts H.
    (*   simpljoin;try splits; auto. *)
  (* new add *)
  destruct Hex as ((t_opt' & Hex) & Hptr & Hstat).
  splits; auto.
  exists t_opt'.
  destruct Hex as [ (Heq & [(Heq1 & H) | (Heq1 & H)]) | (Heq & H)];
  [ left; split; auto; left  | left; split; auto; right | right]; 
  simpljoin; try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_in_tbl_rev with (prio0:= prio0) (prio:= prio); eauto.
  (* end of new add *)
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
   unfolds in Hrl5.
  unfolds.
  intros.
  lets Hex : Hrl5 H.
  inverts H.
   (*   simpljoin;try splits; auto. *)
  (* new add *)
  destruct Hex as ((t_opt' & Hex) & Hptr & Hstat).
  splits; auto.
  exists t_opt'.
  destruct Hex as [ (Heq & [(Heq1 & H) | (Heq1 & H)]) | (Heq & H)];
  [ left; split; auto; left  | left; split; auto; right | right]; 
  simpljoin; try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_in_tbl_rev with (prio0:= prio0) (prio:= prio); eauto.
  (* end of new add *)
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  unfolds in Hrl6.
  unfolds.
  intros.
  lets Hex : Hrl6 H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H0.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  (* new add by sus*)
  unfolds.
  intros.
  unfolds in Hrl7.
  lets Hex : Hrl7 H.
  destruct Hex as (Hex & Hps).
  destruct Hex.

  destruct H0 as (t_opt' & Hex).
  inverts H.
  simpljoin;try splits; auto.
  left.
  unfolds in H2.
  exists t_opt'.
  split;auto.
(*   splits. *)
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
(*   auto. *)
  inverts H.
  simpljoin;try splits; auto.
  right.
  unfolds in H2.
  eexists.
  split;auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.

  splits;unfolds;intros;[unfolds in Hrl8 | unfolds in Hrl9 | unfolds in Hrl10 | unfolds in Hrl11 | unfolds in Hrl12 | unfolds in Hrl13 ];
  [lets Hex : Hrl8 H | lets Hex : Hrl9 H | lets Hex : Hrl10 H | lets Hex : Hrl11 H | lets Hex : Hrl12 H | lets Hex : Hrl13 H].
  
  destruct Hex as ([Hex1 | Hex2] & Hps).
  destruct Hex1 as (t_opt' & Hex).

  inverts H.
  simpljoin;try splits; auto.
  left.
  unfolds in H2.
  exists t_opt'.
  split;auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  inverts H.
  simpljoin;try splits; auto.
  right.
  unfolds in H2.
  eexists.
  split;auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  destruct Hex as (t_opt' & Hex).
  inverts H.
  simpljoin;try splits; auto.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  inverts H;destruct H7 as (Hp & Hd);auto.
  inverts H;destruct H7 as (Hp & Hd);auto.

  destruct Hex as ([Hex1 | Hex2] & Hps).
  destruct Hex1 as (t_opt' & Hex).
  inverts H.
  simpljoin;try splits; auto.
  left.
  unfolds in H2.
  exists t_opt'.
  split;auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  inverts H.
  simpljoin;try splits; auto.
  right.
  unfolds in H2.
  eexists.
  split;auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.

  destruct Hex as ([Hex1 | Hex2] & Hps).
  destruct Hex1 as (t_opt' & Hex).
  inverts H.
  simpljoin;try splits; auto.
  left.
  unfolds in H2.
  exists t_opt'.
  split;auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  inverts H.
  simpljoin;try splits; auto.
  right.
  unfolds in H2.
  eexists.
  split;auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.

  destruct Hex as ([Hex1 | Hex2] & Hps).
  destruct Hex1 as (t_opt' & Hex).
  inverts H.
  simpljoin;try splits; auto.
  destruct H2 as [[? ?] | [? [? ?]]].
  left.
  unfolds in  H2.
  exists t_opt'.
  split;auto. 
  left.
  split;auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  left.
  unfolds in  H2.
  exists t_opt'.
  split;auto.
  right.
  splits;auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  inverts H.
  simpljoin;try splits; auto.
  right.
  unfolds in H2.
  split;auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.

  destruct Hex as ([Hex1 | Hex2] & Hps).
  destruct Hex1 as (t_opt' & Hex).
  inverts H.
  simpljoin;try splits; auto.
  left.
  unfolds in H2.
  exists t_opt'.
  split;auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  inverts H.
  simpljoin;try splits; auto.
  right.
  unfolds in H2.
  eexists.
  split;auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
Qed.

Lemma update_rtbl_tcblist_hold:
  forall vl vptr rtbl tcbls prio grp,
    0<= Int.unsigned prio < 64 ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    (forall tid a b c sus, TcbMod.get tcbls tid  = Some (a,b,c,sus) -> a <> prio
    ) ->
    TCBList_P vptr vl rtbl tcbls ->
    TCBList_P vptr vl
              (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                              (Vint32 (grp &ᵢInt.not ($ 1<<ᵢ(prio &ᵢ$ 7))))) tcbls.
Proof.
  inductions vl.
  intros; simpl in *.
  auto.
  intros.
  unfold TCBList_P in *; fold TCBList_P in *.
  simpljoin;try splits.
  exists x x0 x1 x2.
  splits; auto.
  unfolds in H5.
  unfolds.
  destruct x2.
  destruct p.
  destruct p.
  simpljoin;try splits; auto.
  lets Hds : tcbjoin_get_a H4. 
  apply H1 in Hds.
  unfolds in H7.
  unfolds.
  lets Hran : tcbblk_prio_range H8 H5.
  unfolds in H9.
  simpljoin;try splits.
  eapply RLH_Rdy_prioneq_prop_hold; eauto.
  eapply  RHL_Rdy_prioneq_prop_hold; eauto.
  eapply RLH_Suspend_prioneq_prop_hold;eauto.
  eapply RHL_Suspend_prioneq_prop_hold;eauto.
  eapply RLH_Wait_prioneq_prop_hold; eauto.
  eapply  RHL_Wait_prioneq_prop_hold; eauto.
  eauto.
  eapply IHvl; auto.
  intros; eapply H1.  
  eapply tcbjoin_get_get; eauto.
Qed.



Lemma TCBList_P_tcb_dly_hold :
  forall ptcb v1 v2 v3  v5 v6 v8 v9 v10 v11 rtbl vl
         tcbls prio st m  time ry sus,
    Int.unsigned time <= 65535 ->
    Int.ltu ($ 0) time = true ->
    TCBList_P (Vptr ptcb) ((v1::v2::v3::m::v5::(Vint32 v6)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    (st = rdy /\ sus = false)  \/ ((exists n, st = wait os_stat_time n) /\ sus = false) \/ ((exists n, st = wait os_stat_time n) /\ sus = true) ->
    prio_neq_cur tcbls ptcb  prio ->
    nth_val (nat_of_Z (Int.unsigned v9)) rtbl = Some (Vint32 ry) ->
    TCBList_P (Vptr ptcb) ((v1::v2::v3::m::(Vint32 time)::(Vint32 v6)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) 
              (update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (Int.and ry (Int.not v10)))) 
              (TcbMod.set tcbls ptcb (prio, wait os_stat_time  (Some time), m, sus)).
Proof.
  introv Htim Hltu Htcb Htm Hst Hprio Hnth.
  unfolds in Htcb;fold TCBList_P in Htcb.
  simpljoin;try splits.
  inverts H.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds.
  fold TCBList_P.
  exists x x0.
  exists x1.
  exists (prio, wait os_stat_time (Some time), m, sus).
  splits; eauto.
  eapply tcbjoin_set; eauto.
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  simpljoin.
  unfolds in H0.
  simpl in H0.
  apply eq_sym in H0; inverts H0.
  funfold H2.
  unfolds.
  split.  
  unfolds.
  simpl.
  auto.
  split.
  unfolds; simpl;auto.
  split.
  unfolds.
  do 6 eexists; splits; try unfolds; simpl; eauto.
  splits; auto.
  eexists;  splits.
  unfolds; simpl; eauto.
  auto.  
  lets Hexa : tcbjoin_get H1 Htm.
  inverts Hexa.
  unfolds.
  splits.
  unfolds.
  intros.
  unfolds in H.
  destruct H.
  unfolds in H; simpl in H; inverts H.
  assert (prio&ᵢ$ 7 = prio&ᵢ$ 7) by auto.
  assert (Int.shru ( prio) ($ 3) =Int.shru (prio) ($ 3)) by auto.
  assert ( nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3)))
         (update_nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3))) rtbl
            (Vint32 (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
           Some (Vint32  (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth; eauto.
  lets Hr: H0 H H2 H5.
  rewrite Int.and_assoc in Hr.
  assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
  rewrite Int.and_commut.
  rewrite Int.and_not_self.
  auto.
  rewrite H6  in Hr.
  rewrite Int.and_zero in Hr.
  assert ( $ 1<<ᵢ(prio&ᵢ$ 7) <> $ 0) by (apply  math_prop_neq_zero2; try lia).
  unfold Int.zero in Hr.
  tryfalse.
  (* reprove by sus *)
  split.
  {
    unfolds.
    inverts H.
  }
  inverts H.
  (* RLH_Suspend_P. *)
  split.
  {
    intros.
    simpl_hyp.
    unfolds in H.
    destruct H as (Hv & Hpr & Hvo).
    simpl_hyp.
    tryfalse.
  }
  {
    intros.
    simpl_hyp.
    unfolds in H.
    destruct H as (Hv & Hpr & Hvo).
    simpl_hyp.
    eexists (x := m0).
    destruct Hst.
    (* st = rdy /\ sus = false *)
    destruct H.
    subst.
    unfolds in H4.
    simpljoin.
    assert ((prio,rdy,m0,false)=(prio,rdy,m0,false)) by auto.
    apply H0 in H8.
    simpljoin.
    simpl_hyp.
    destruct H.
    (* (exists n, st = wait os_stat_time n) /\ sus = false *)
    destruct H.
    subst.
    unfolds in H4.
    simpljoin.
    assert ((prio,wait os_stat_time x2,m0,false)=(prio,wait os_stat_time x2,m0,false)) by auto.
    apply H8 in H.
    simpljoin.
    simpl_hyp.
    (* (exists n, st = wait os_stat_time n) /\ sus = true *)
    destruct H.
    subst.
    eauto.
  }
  (* RHL_Suspend_P *)
  splits.
  {
    intros.
    inverts H.
  }
  {
    intros.
    inverts H.
    eexists.
    split.
    auto.
    splits.
    - destruct Hst.
      destruct H.
      subst.
      tryfalse.
      destruct H.
      + destruct H.
        tryfalse.
      + destruct H.
        unfolds in H4.
        unfolds;splits.
        auto.
        unfolds.
        intros.
        subst.
        apply nth_upd_eq in H6.
        inverts H6.
        rewrite Int.and_assoc.
        assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
        rewrite Int.and_commut.
        rewrite Int.and_not_self.
        auto.
        rewrite H2.
        rewrite Int.and_zero.
        auto.
        auto.
    - auto.
    - unfolds in H4.
      simpljoin.
      destruct Hst.
      destruct H7.
      subst.
      tryfalse.
      destruct H7.
      destruct H7.
      tryfalse.
      destruct H7.
      simpljoin.
      assert ((prio, wait os_stat_time x2, m, true)=(prio, wait os_stat_time x2, m, true)) by auto.
      eapply H4 in H7.
      simpljoin.
      auto.
  }
  splits.
  (* RLH_Wait_P *)
  {
    unfolds.
    intros.
    simpl_hyp.
    unfolds in H.
    destruct H as (Hv & Hpr & Hvo).
    simpl_hyp.
    splits;auto.
    eexists (x:=m0).
    destruct Hst.
    - destruct H.
      subst;auto.
    - destruct H.
      + destruct H.
        subst;auto.
      + destruct H.
        subst.
        simpljoin.
        unfolds in H4;simpljoin.
        assert ((prio, wait os_stat_time x2, m0, true)=(prio, wait os_stat_time x2, m0, true)) by auto.
        apply H4 in H7.
        simpljoin;try splits; simpl_hyp.
  } 
  (* RLH_WaitS_P *)
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin;try splits.
    simpl_hyp.
    destruct Hst.
    - destruct H.
      subst.
      unfolds in H4.
      destruct H4 as [H_RLH_RdyI H4].
      destruct H4 as [RHL_RdyI_P H4].
      destruct H4 as [RLH_TCB_Status_Wait_P H4].
      destruct H4 as [RHL_TCB_Status_Wait_P H_rRH_RdySus_P].
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply RHL_RdyI_P in H.
      simpljoin;try splits.
      simpl_hyp.
    - destruct H.
      destruct H.
      subst.
      unfolds in H4.
      simpljoin;try splits.
      assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto.
      apply H8 in H.
      simpljoin;try splits;simpl_hyp. 
      destruct H.
      subst.
      unfolds in H4.
      simpljoin;try splits.
      assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto.
      apply H6 in H.
      simpljoin;try splits; simpl_hyp.
  }
  (* RLH_WaitS_TO_P *)
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin;try splits.
    simpl_hyp.
    destruct Hst.
    - destruct H.
      subst.
      unfolds in H4.
      destruct H4 as [H_RLH_RdyI H4].
      destruct H4 as [RHL_RdyI_P H4].
      destruct H4 as [RLH_TCB_Status_Wait_P H4].
      destruct H4 as [RHL_TCB_Status_Wait_P H_rRH_RdySus_P].
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply RHL_RdyI_P in H.
      simpljoin;try splits.
      simpl_hyp.
    - destruct H.
      destruct H.
      subst.
      unfolds in H4.
      simpljoin;try splits.
      assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto.
      apply H8 in H.
      simpljoin;try splits;simpl_hyp. 
      destruct H.
      subst.
      unfolds in H4.
      simpljoin;try splits.
      assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto.
      apply H6 in H.
      simpljoin;try splits; simpl_hyp.
  }
  (* RLH_WaitQ_P *)
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin;try splits.
    simpl_hyp.
    destruct Hst.
    - destruct H.
      subst.
      unfolds in H4.
      destruct H4 as (H_RLH_RdyI & H_RHL_RdyI_P & _).
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply H_RHL_RdyI_P in H.
      simpljoin;try splits; simpl_hyp.
    - destruct H.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto. 
        apply H8 in H.
        simpljoin;try splits; simpl_hyp.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto. 
        apply H6 in H.
        simpljoin;try splits; simpl_hyp.
  }
  (* RLH_WaitQ_TO_P *)
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin;try splits.
    simpl_hyp.
    destruct Hst.
    - destruct H.
      subst.
      unfolds in H4.
      destruct H4 as (H_RLH_RdyI & H_RHL_RdyI_P & _).
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply H_RHL_RdyI_P in H.
      simpljoin;try splits; simpl_hyp.
    - destruct H.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto. 
        apply H8 in H.
        simpljoin;try splits; simpl_hyp.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto. 
        apply H6 in H.
        simpljoin;try splits; simpl_hyp.
  }
  (* RLH_WaitMB_P *)
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin;try splits.
    simpl_hyp.
    destruct Hst.
    - destruct H.
      subst.
      unfolds in H4.
      destruct H4 as (H_RLH_RdyI & H_RHL_RdyI_P & _).
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply H_RHL_RdyI_P in H.
      simpljoin;try splits; simpl_hyp.
    - destruct H.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto.
        apply H8 in H.
        simpljoin;try splits; simpl_hyp.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto.
        apply H6 in H.
        simpljoin;try splits; simpl_hyp.
  }
  (* RLH_WaitMB_TO_P *)
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin;try splits.
    simpl_hyp.
    destruct Hst.
    - destruct H.
      subst.
      unfolds in H4.
      destruct H4 as (H_RLH_RdyI & H_RHL_RdyI_P & _).
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply H_RHL_RdyI_P in H.
      simpljoin;try splits; simpl_hyp.
    - destruct H.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto.
        apply H8 in H.
        simpljoin;try splits; simpl_hyp.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto.
        apply H6 in H.
        simpljoin;try splits; simpl_hyp.
  }
  splits.
  (* RLH_WaitMS_P *)
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin;try splits.
    simpl_hyp.
    destruct Hst.
    - destruct H.
      subst.
      unfolds in H4.
      destruct H4 as (H_RLH_RdyI & H_RHL_RdyI_P & _).
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply H_RHL_RdyI_P in H.
      simpljoin;try splits; simpl_hyp.
    - destruct H.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto.
        apply H8 in H.
        simpljoin;try splits; simpl_hyp.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto.
        apply H6 in H.
        simpljoin;try splits; simpl_hyp.
  }
  (* RLH_WaitMS_TO_P *)
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin;try splits.
    simpl_hyp.
    destruct Hst.
    - destruct H.
      subst.
      unfolds in H4.
      destruct H4 as (H_RLH_RdyI & H_RHL_RdyI_P & _).
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply H_RHL_RdyI_P in H.
      simpljoin;try splits; simpl_hyp.
    - destruct H.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto.
        apply H8 in H.
        simpljoin;try splits; simpl_hyp.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto.
        apply H6 in H.
        simpljoin;try splits; simpl_hyp.
  }
  (* RLH_WaitPostQ_P *)
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin;try splits.
    simpl_hyp.
    destruct Hst.
    - destruct H.
      subst.
      unfolds in H4.
      destruct H4 as (H_RLH_RdyI & H_RHL_RdyI_P & _).
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply H_RHL_RdyI_P in H.
      simpljoin;try splits; simpl_hyp.
    - destruct H.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto.
        apply H8 in H.
        simpljoin;try splits; simpl_hyp.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto.
        apply H6 in H.
        simpljoin;try splits; simpl_hyp.
    - exists x8.
      inverts H2.
      inverts H0.
      inverts H6.
      inverts H.
      destruct Hst.
      * destruct H.
        subst.
        unfolds in H4.
        (* destruct H4 as (_&_&_&_&_&Hsw&_). *)
        (* unfolds in Hsw. *)
        simpljoin.
        assert (((prio, rdy, m0, false) = (prio, rdy, m0, false))) by auto.
        apply H0 in H8;simpljoin.
        inverts H10.
      * destruct H.
        destruct H as (He & Hs).
        destruct He.
        subst.
        unfolds in H4;simpljoin.
        unfolds in H7;simpljoin.
        assert (((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false))) by auto.
        apply H7 in H24;simpljoin.
        inverts H27.
        destruct H as (He & Hs).
        subst.
        unfolds in H4;simpljoin.
        unfolds in H7;simpljoin.
        assert (((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true))) by auto.
        destruct H6 as (H6a & H6b).
        apply H6b in H29;simpljoin.
        inverts H31.
  }
  (* RLH_WaitS_Suspend_P *)
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin;try splits.
    simpl_hyp.
    destruct Hst.
    - destruct H.
      subst.
      unfolds in H4.
      destruct H4 as (H_RLH_RdyI & H_RHL_RdyI_P & _).
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply H_RHL_RdyI_P in H.
      simpljoin;try splits; simpl_hyp.
    - destruct H.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto.
        apply H8 in H.
        simpljoin;try splits; simpl_hyp.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto.
        apply H6 in H.
        simpljoin;try splits; simpl_hyp.
  }
  (* RLH_WaitQ_Suspend_P *)
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin;try splits.
    simpl_hyp.
    destruct Hst.
    - destruct H.
      subst.
      unfolds in H4.
      destruct H4 as (H_RLH_RdyI & H_RHL_RdyI_P & _).
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply H_RHL_RdyI_P in H.
      simpljoin;try splits; simpl_hyp.
    - destruct H.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto.
        apply H8 in H.
        simpljoin;try splits; simpl_hyp.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto.
        apply H6 in H.
        simpljoin;try splits; simpl_hyp.
  }
  (* RLH_WaitPostQ_Suspend_P *)
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin;try splits.
    simpl_hyp.
    destruct Hst.
    - destruct H.
      subst.
      unfolds in H4.
      destruct H4 as (H_RLH_RdyI & H_RHL_RdyI_P & _).
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply H_RHL_RdyI_P in H.
      simpljoin;try splits; simpl_hyp.
    - destruct H.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto.
        apply H8 in H.
        simpljoin;try splits; simpl_hyp.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto.
        apply H6 in H.
        simpljoin;try splits; simpl_hyp.
    - eexists.
      auto.
      inverts H6.
      inverts H.
      inverts H0.
      inverts H2.
      destruct Hst.
      destruct a;subst.
      unfolds in H4;simpljoin.
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply r0 in H;simpljoin.
      inverts H0.
      destruct o.
      destruct H as (He & Hs).
      destruct He;subst.
      unfolds in H4;simpljoin.
      destruct r4;simpljoin.
      assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto.
      apply r4 in H;simpljoin.
      inverts H4.
      destruct H as (He & Hs).
      destruct He;subst.
      unfolds in H4;simpljoin.
      destruct r2;simpljoin.
      assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto.
      apply e in H;simpljoin.
      inverts H4.
  }
  (* RLH_WaitMB_Suspend_P *)
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin;try splits.
    simpl_hyp.
    destruct Hst.
    - destruct H.
      subst.
      unfolds in H4.
      destruct H4 as (H_RLH_RdyI & H_RHL_RdyI_P & _).
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply H_RHL_RdyI_P in H.
      simpljoin;try splits; simpl_hyp.
    - destruct H.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto.
        apply H8 in H.
        simpljoin;try splits; simpl_hyp.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto.
        apply H6 in H.
        simpljoin;try splits; simpl_hyp.
  }
  split.
  (* RLH_WaitMS_Suspend_P *)
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin;try splits.
    simpl_hyp.
    destruct Hst.
    - destruct H.
      subst.
      unfolds in H4.
      destruct H4 as (H_RLH_RdyI & H_RHL_RdyI_P & _).
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply H_RHL_RdyI_P in H.
      simpljoin;try splits; simpl_hyp.
    - destruct H.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto.
        apply H8 in H.
        simpljoin;try splits; simpl_hyp.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto.
        apply H6 in H.
        simpljoin;try splits; simpl_hyp.
  }
  splits.
  (* RLH_WaitPort_P *)
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin;try splits.
    simpl_hyp.
    destruct Hst.
    - destruct H.
      subst.
      unfolds in H4.
      destruct H4 as [H_RLH_RdyI H4].
      destruct H4 as [RHL_RdyI_P H4].
      destruct H4 as [RLH_TCB_Status_Wait_P H4].
      destruct H4 as [RHL_TCB_Status_Wait_P H_rRH_RdySus_P].
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply RHL_RdyI_P in H.
      simpljoin;try splits.
      simpl_hyp.
    - destruct H.
      destruct H.
      subst.
      unfolds in H4.
      simpljoin;try splits.
      assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto.
      apply H8 in H.
      simpljoin;try splits;simpl_hyp. 
      destruct H.
      subst.
      unfolds in H4.
      simpljoin;try splits.
      assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto.
      apply H6 in H.
      simpljoin;try splits; simpl_hyp.
  }
  (* RLH_WaitPort_TO_P *)
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin;try splits.
    simpl_hyp.
    destruct Hst.
    - destruct H.
      subst.
      unfolds in H4.
      destruct H4 as [H_RLH_RdyI H4].
      destruct H4 as [RHL_RdyI_P H4].
      destruct H4 as [RLH_TCB_Status_Wait_P H4].
      destruct H4 as [RHL_TCB_Status_Wait_P H_rRH_RdySus_P].
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply RHL_RdyI_P in H.
      simpljoin;try splits.
      simpl_hyp.
    - destruct H.
      destruct H.
      subst.
      unfolds in H4.
      simpljoin;try splits.
      assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto.
      apply H8 in H.
      simpljoin;try splits;simpl_hyp. 
      destruct H.
      subst.
      unfolds in H4.
      simpljoin;try splits.
      assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto.
      apply H6 in H.
      simpljoin;try splits; simpl_hyp.
  }
  (* RLH_WaitPort_Suspend_P *)
  {
    unfolds.
    intros.
    unfolds in H.
    simpljoin;try splits.
    simpl_hyp.
    destruct Hst.
    - destruct H.
      subst.
      unfolds in H4.
      destruct H4 as (H_RLH_RdyI & H_RHL_RdyI_P & _).
      assert ((prio, rdy, m0, false) = (prio, rdy, m0, false)) by auto.
      apply H_RHL_RdyI_P in H.
      simpljoin;try splits; simpl_hyp.
    - destruct H.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, false) = (prio, wait os_stat_time x2, m0, false)) by auto.
        apply H8 in H.
        simpljoin;try splits; simpl_hyp.
      + destruct H.
        subst.
        unfolds in H4.
        simpljoin.
        assert ((prio, wait os_stat_time x2, m0, true) = (prio, wait os_stat_time x2, m0, true)) by auto.
        apply H6 in H.
        simpljoin;try splits; simpl_hyp.
  }
  (* RHL_TCB_Status_Wait_P *)
  {
    destruct Hst.
    (* st = rdy /\ sus = false *)
    + destruct H.
      subst.
      unfolds.
      split.
      (* RHL_Wait_P *)
      unfolds.
      intros.
      inverts H.
      destruct H4 as (Hr1 & Hr2 & _).
      unfolds in Hr2.
      assert ((prio, rdy, m, false) = (prio, rdy, m, false)) by auto.
      apply Hr2 in H.
      destruct H as (Hrdy & Hv1 & Hv2).
      simpl_hyp.
      eexists.
      split;auto.
      split; auto.
      unfolds.
      splits;auto.
      unfolds.
      intros.
      subst.
      apply nth_upd_eq in H2.
      inverts H2.
      rewrite Int.and_assoc.
      assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
      rewrite Int.and_commut.
      rewrite Int.and_not_self.
      auto.
      rewrite H.
      rewrite  Int.and_zero.
      auto.
      (* the rest *)
      splits;try unfolds;intros;tryfalse.
      splits;try unfolds;intros;tryfalse.
    + destruct H.
      (* (exists n, st = wait os_stat_time n) /\ sus = false *)
      destruct H.
      subst.
      split.
      unfolds.
      intros.
      inverts H.
      destruct H4 as ( _ & _ & _ & _ & _ & Hw).
      unfolds in Hw.
      destruct Hw as (Hw & _).
      unfolds in Hw.
      assert ((x2, wait os_stat_time x3, m0, false) = (x2, wait os_stat_time x3, m0, false)) by auto.
      apply Hw in H.
      destruct H as (t & He & Hww & Hv).
      inverts H0.
      eexists;auto.
      splits; auto.
      simpl_hyp.
      unfolds.
      unfolds in Hww.
      destruct Hww as (Hwt1 & Hwt2 & Hwt3).
      simpl_hyp.
      splits; auto.
      unfolds.
      intros.
      subst.
      apply nth_upd_eq in H2.
      inverts H2.
      rewrite Int.and_assoc.
      assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
      rewrite Int.and_commut.
      rewrite Int.and_not_self.
      auto.
      rewrite H.
      apply Int.and_zero.
      destruct Hv.
      simpl_hyp.
      unfolds; simpl; auto.
      splits;try unfolds;try intros; tryfalse.
      splits;try unfolds;try intros; tryfalse.
      (* (exists n, st = wait os_stat_time n) /\ sus = true *)
      destruct H.
      subst.
      split.

      unfolds;intros;inverts H;destruct H4 as ( _ & _ & _& Hw & _ & _ );
      assert ((x2, wait os_stat_time x3, m0, true) = (x2, wait os_stat_time x3, m0, true)) by auto;
      apply Hw in H;
      destruct H as (t & He & Hww & Hv);
      inverts He;
      inverts H0.

      splits.

      unfolds;intros;inverts H;destruct H4 as ( _ & _ & _& Hw & _ & _ );
      assert ((x2, wait os_stat_time x3, m0, true) = (x2, wait os_stat_time x3, m0, true)) by auto;
      apply Hw in H;
      destruct H as (t & He & Hww & Hv);
      inverts He;
      inverts H0.

      unfolds;intros;inverts H;destruct H4 as ( _ & _ & _& Hw & _ & _ );
      assert ((x2, wait os_stat_time x3, m0, true) = (x2, wait os_stat_time x3, m0, true)) by auto;
      apply Hw in H;
      destruct H as (t & He & Hww & Hv);
      inverts He;
      inverts H0.

      unfolds;intros;inverts H;destruct H4 as ( _ & _ & _& Hw & _ & _ );
      assert ((x2, wait os_stat_time x3, m0, true) = (x2, wait os_stat_time x3, m0, true)) by auto;
      apply Hw in H;
      destruct H as (t & He & Hww & Hv);
      inverts He;
      inverts H0.

      unfolds;intros;inverts H;destruct H4 as ( _ & _ & _& Hw & _ & _ );
      assert ((x2, wait os_stat_time x3, m0, true) = (x2, wait os_stat_time x3, m0, true)) by auto;
      apply Hw in H;
      destruct H as (t & He & Hww & Hv);
      inverts He;
      inverts H0.

      unfolds;intros;inverts H;destruct H4 as ( _ & _ & _& Hw & _ & _ );
      assert ((x2, wait os_stat_time x3, m0, true) = (x2, wait os_stat_time x3, m0, true)) by auto;
      apply Hw in H;
      destruct H as (t0 & He & Hww & Hv);
      inverts He;
      inverts H0.
      
      unfolds;intros;inverts H;destruct H4 as ( _ & _ & _& Hw & _ & _ );
      assert ((x2, wait os_stat_time x3, m0, true) = (x2, wait os_stat_time x3, m0, true)) by auto;
      apply Hw in H;
      destruct H as (t0 & He & Hww & Hv);
      inverts He;
      inverts H0.

      unfolds;intros;inverts H;destruct H4 as ( _ & _ & _& Hw & _ & _ );
      assert ((x2, wait os_stat_time x3, m0, true) = (x2, wait os_stat_time x3, m0, true)) by auto;
      apply Hw in H;
      destruct H as (t0 & He & Hww & Hv);
      inverts He;
      inverts H0.

      splits.

      unfolds;intros;inverts H;destruct H4 as ( _ & _ & _& Hw & _ & _ );
      assert ((x2, wait os_stat_time x3, m0, true) = (x2, wait os_stat_time x3, m0, true)) by auto;
      apply Hw in H;
      destruct H as (t0 & He & Hww & Hv);
      inverts He;
      inverts H0.

      unfolds;intros;inverts H;destruct H4 as ( _ & _ & _& Hw & _ & _ );
      assert ((x2, wait os_stat_time x3, m0, true) = (x2, wait os_stat_time x3, m0, true)) by auto;
      apply Hw in H;
      destruct H as (t0 & He & Hww & Hv);
      inverts He;
      inverts H0.

      unfolds;intros;inverts H;destruct H4 as ( _ & _ & _& Hw & _ & _ );
      assert ((x2, wait os_stat_time x3, m0, true) = (x2, wait os_stat_time x3, m0, true)) by auto;
      apply Hw in H;
      destruct H as (t0 & He & Hww & Hv);
      inverts He;
      inverts H0.

      unfolds;intros;inverts H;destruct H4 as ( _ & _ & _& Hw & _ & _ );
      assert ((x2, wait os_stat_time x3, m0, true) = (x2, wait os_stat_time x3, m0, true)) by auto;
      apply Hw in H;
      destruct H as (t & He & Hww & Hv);
      inverts He;
      inverts H0.

      unfolds;intros;inverts H;destruct H4 as ( _ & _ & _& Hw & _ & _ );
      assert ((x2, wait os_stat_time x3, m0, true) = (x2, wait os_stat_time x3, m0, true)) by auto;
      apply Hw in H;
      destruct H as (t & He & Hww & Hv);
      inverts He;
      inverts H0.
  }
  unfolds;intros;tryfalse.
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  simpljoin;try splits; simpl_hyp.
  funfold H2.
  eapply update_rtbl_tcblist_hold; eauto.
  unfolds in Hprio.
  intros.
  lets Has : tcbjoin_get_getneq H1 H.
  destruct Has.
  eapply Hprio; eauto.
  Unshelve. all: auto.
Qed.


Lemma TCBList_P_tcb_dly_hold' :
  forall v ptcb rtbl vl y bitx
         tcbls prio ry x1 tcs tcs' t m sus,
    0 <= Int.unsigned prio < 64 ->
    TcbMod.join (TcbMod.sig ptcb (prio, t, m, sus)) x1 tcs ->
    TcbMod.join tcbls tcs tcs' -> 
    TCBList_P v vl rtbl tcbls ->
    y = Int.shru prio ($ 3) ->
    bitx = ($ 1) <<ᵢ (Int.and prio ($ 7)) ->
    prio_neq_cur tcbls ptcb  prio ->
    nth_val (nat_of_Z (Int.unsigned y)) rtbl = Some (Vint32 ry) ->
    TCBList_P v vl (update_nth_val ∘(Int.unsigned y) rtbl (Vint32 (Int.and ry (Int.not bitx)))) tcbls.
Proof.
  intros.
  subst.
  eapply update_rtbl_tcblist_hold;eauto.
  unfolds in H5.
  intros.
  eapply H5;eauto.
  eapply tcbjoin_join_get_neq; eauto.
Qed.


Lemma rtbl_remove_RL_RTbl_PrioTbl_P_hold :
  forall prio y bitx rtbl ry ptbl vhold,
    0 <= Int.unsigned prio < 64 ->
    y = Int.shru (prio) ($ 3) ->
    bitx = ($ 1) <<ᵢ (Int.and (prio) ($ 7)) ->
    nth_val ∘(Int.unsigned y) rtbl = Some (Vint32 ry) ->
    RL_RTbl_PrioTbl_P rtbl ptbl vhold->
    RL_RTbl_PrioTbl_P
     (update_nth_val ∘(Int.unsigned y) rtbl (Vint32 (ry&ᵢInt.not bitx))) ptbl vhold.
Proof.
  introv Hpr Hy Hbit Hnth Hrl.
  subst.
  unfolds. 
  unfolds in Hrl.
  intros.
  assert (p = prio \/ p <> prio) by tauto.
  destruct H1.
  subst.
  unfolds in H0.
  assert ( prio&ᵢ$ 7  =  prio&ᵢ$ 7 ) by auto.
  assert (Int.shru prio ($ 3)  =  Int.shru prio ($ 3)) by auto.
  lets Hf : H0  (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))) H1 H2.
  assert ( (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7)))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 1<<ᵢ(prio&ᵢ$ 7)).
  apply Hf.
  eapply update_nth; eauto.
  rewrite Int.and_assoc in H3.
  assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
  rewrite Int.and_commut. 
  rewrite Int.and_not_self; auto.
  rewrite H4 in H3.
  rewrite Int.and_zero in H3.
  assert ($ 1<<ᵢ(prio&ᵢ$ 7) <> $ 0) by (apply math_prop_neq_zero2; eauto).
  unfold Int.zero in H3.
  tryfalse.
  eapply Hrl; auto.
  eapply prio_neq_in_tbl with (prio0 :=p)(prio:=prio); eauto.
Qed.  

Close Scope Z_scope.
Close Scope code_scope.
Close Scope int_scope.










Require Import ucos_include.
Require Import Lia.
Require Import aux_pureLib.
Require Import corecommu_tactics.
Require Import sem_common.
Require Import OSQPostPure.
Require Import OSTimeDlyPure.
Require Import OSTimeTickPure.
Require Import partition_rules.


Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope code_scope.


Lemma RL_RTbl_PrioTbl_P_update_rtbl : forall rtbl ptbl vhold prio x y z ,
  0 <= Int.unsigned prio < 64 ->
  x = prio &ᵢ ($ 7) -> y = Int.shru prio  ($ 3) ->
  nth_val (nat_of_Z (Int.unsigned y)) rtbl = Some (Vint32 z) -> 
  RL_RTbl_PrioTbl_P rtbl ptbl vhold ->
  RL_RTbl_PrioTbl_P (update_nth_val ∘ (Int.unsigned y) rtbl
     (Vint32 (z &ᵢInt.not ($ 1<<ᵢ x)))) ptbl vhold.
Proof.
  unfold RL_RTbl_PrioTbl_P;intros.
  assert (p <> prio \/ p = prio) as [ | ] by tauto. 
  - eapply H3;eauto.
    subst x y.   eapply prio_neq_in_tbl with (prio := prio);eauto.
  - subst. 
    false. eapply prio_update_self_not_in;eauto.
Qed.


Lemma RH_TCBList_ECBList_P_update_rdy2port : forall ecbls tcbls tid pri m sus p_v wt tm,
  RH_TCBList_ECBList_P ecbls tcbls tid  ->
  get tcbls tid = Some (pri, rdy, m, sus) ->
  get ecbls p_v = Some (absport, wt) ->
  RH_TCBList_ECBList_P (set ecbls p_v (absport, tid :: wt)) 
          (set tcbls tid  (pri, wait (os_stat_port p_v) tm, m, sus)) tid.
Proof.
  unfold RH_TCBList_ECBList_P, RH_TCBList_ECBList_PORT_P;intros * [? [? [? ?]]]. intros.
  splits.
  - unfold RH_TCBList_ECBList_Q_P in * .  intros.
    simpljoin1. 
    splits;intro a.
    + intros. simpljoin1.
      assert (a = p_v \/ a <> p_v) as [ | ] by tauto.
      * subst.
        rewrite get_set_eq in H10. inverts H10. 
      * erewrite get_set_neq in H10;eauto.
        specialize (H _ _ _  _ _ _ (Logic.conj H10 H11)) as [? [? [? [? ?]]]].
        assert (tid0 = tid \/ tid0 <> tid) as [ | ] by tauto.
        subst. rewrite H in H3. inverts H3.  
        do 4 eexists.
        erewrite get_set_neq;eauto.
    + intros. simpljoin1.
      assert (a = p_v \/ a <> p_v) as [ | ] by tauto.
      * subst.
        rewrite get_set_eq in H10. inverts H10. 
      * erewrite get_set_neq in H10;eauto.
        specialize (H7 _ _ _  _ _ _ (Logic.conj H10 H11)) as [? [? [? [? ?]]]].
        assert (tid0 = tid \/ tid0 <> tid) as [ | ] by tauto.
        subst. rewrite H7 in H3. inverts H3.  
        do 4 eexists.
        erewrite get_set_neq;eauto.
    + intros. simpljoin1.
      assert (tid0 = tid \/ tid0 <> tid) as [ | ] by tauto.
      * subst.
        rewrite get_set_eq in H10. inverts H10.
      * erewrite get_set_neq in H10;eauto.
        specialize (H8 _ _ _  _ _ _ H10) as [? [? [? [? [? ?]]]]].
        assert (eid = p_v \/ eid <> p_v) as [ | ] by tauto.
        subst. rewrite H8 in H4. inverts H4.  
        do 4 eexists.
        erewrite get_set_neq;eauto.
    + intros. simpljoin1.
      assert (tid0 = tid \/ tid0 <> tid) as [ | ] by tauto.
      * subst.
        rewrite get_set_eq in H10. inverts H10.
      * erewrite get_set_neq in H10;eauto.
        specialize (H9 _ _ _  _ _ _ H10) as [? [? [? [? [? ?]]]]].
        assert (eid = p_v \/ eid <> p_v) as [ | ] by tauto.
        subst. unfold waitset, eid, Modules.tid in *. rewrite H9 in H4. inverts H4.  
        do 4 eexists.
        erewrite get_set_neq;eauto.
  - unfold RH_TCBList_ECBList_SEM_P in * .  intros.
    simpljoin1. 
    splits;intro a.
    + intros. simpljoin1.
      assert (a = p_v \/ a <> p_v) as [ | ] by tauto.
      * subst.
        rewrite get_set_eq in H8. inverts H8. 
      * erewrite get_set_neq in H8;eauto.
        specialize (H0 _ _ _  _  (Logic.conj H8 H9)) as [? [? [? [? ?]]]].
        assert (tid0 = tid \/ tid0 <> tid) as [ | ] by tauto.
        subst. rewrite H0 in H3. inverts H3.  
        do 4 eexists.
        erewrite get_set_neq;eauto.
    + intros. simpljoin1.
      assert (tid0 = tid \/ tid0 <> tid) as [ | ] by tauto.
      * subst.
        rewrite get_set_eq in H8. inverts H8.
      * erewrite get_set_neq in H8;eauto.
        specialize (H7 _ _ _ _ _ _ H8) as [? [? [? ?]]].
        assert (eid = p_v \/ eid <> p_v) as [ | ] by tauto.
        subst. unfold waitset, eid, Modules.tid in *.  rewrite H7 in H4. inverts H4.  
        do 2 eexists.
        erewrite get_set_neq;eauto.
  - unfold RH_TCBList_ECBList_MBOX_P in * .  intros.
    simpljoin1. 
    splits;intro a.
    + intros. simpljoin1.
      assert (a = p_v \/ a <> p_v) as [ | ] by tauto.
      * subst.
        rewrite get_set_eq in H8. inverts H8. 
      * erewrite get_set_neq in H8;eauto.
        specialize (H1 _ _ _  _  (Logic.conj H8 H9)) as [? [? [? [? ?]]]].
        assert (tid0 = tid \/ tid0 <> tid) as [ | ] by tauto.
        subst. rewrite H1 in H3. inverts H3.  
        do 4 eexists.
        erewrite get_set_neq;eauto.
    + intros. simpljoin1.
      assert (tid0 = tid \/ tid0 <> tid) as [ | ] by tauto.
      * subst.
        rewrite get_set_eq in H8. inverts H8.
      * erewrite get_set_neq in H8;eauto.
        specialize (H7 _ _ _ _ _ _ H8) as [? [? [? ?]]].
        assert (eid = p_v \/ eid <> p_v) as [ | ] by tauto.
        subst. unfold waitset, eid, Modules.tid in *.  rewrite H7 in H4. inverts H4.  
        do 2 eexists.
        erewrite get_set_neq;eauto.
  - unfold RH_TCBList_ECBList_MUTEX_P, RH_TCBList_ECBList_MUTEX_OWNER, RH_TCBList_ECBList_MUTEX_OWNER_P,os_inv.prio_available in * .  intros.
    simpljoin1. 
    splits;intro a.
    + intros. simpljoin1.
      assert (a = p_v \/ a <> p_v) as [ | ] by tauto.
      * subst.
        rewrite get_set_eq in H12. inverts H12. 
      * erewrite get_set_neq in H12;eauto.
        specialize (H2 _ _ _ _ _  (Logic.conj H12 H13)) as [? [? [? [? ?]]]].
        assert (tid0 = tid \/ tid0 <> tid) as [ | ] by tauto.
        subst. rewrite H2 in H3. inverts H3.  
        do 4 eexists.
        erewrite get_set_neq;eauto.
    + intros. simpljoin1.
      assert (tid0 = tid \/ tid0 <> tid) as [ | ] by tauto.
      * subst.
        rewrite get_set_eq in H12. inverts H12.
      * erewrite get_set_neq in H12;eauto.
        specialize (H7 _ _ _ _ _ _ H12) as [? [? [? [? ?]]]].
        assert (eid = p_v \/ eid <> p_v) as [ | ] by tauto.
        subst. unfold waitset, eid, Modules.tid in *.  rewrite H7 in H4. inverts H4.  
        do 3 eexists.
        erewrite get_set_neq;eauto.
    + intros. simpljoin1.
      assert (a = p_v \/ a <> p_v) as [ | ] by tauto.
      * subst.
        rewrite get_set_eq in H12. inverts H12. 
      * erewrite get_set_neq in H12;eauto.
        specialize (H8 _ _ _ _ _  H12) as [[? [? [? [? ?]]]] ?].
        split;auto.
        assert (tid0 = tid \/ tid0 <> tid) as [ | ] by tauto.
        subst. erewrite get_set_eq. do 4 eexists. eauto.
        do 4 eexists.
        erewrite get_set_neq;eauto.
    + intros. 
      assert (a = p_v \/ a <> p_v) as [ | ] by tauto.
      * subst.
        rewrite get_set_eq in H12. inverts H12. 
      * erewrite get_set_neq in H12;eauto.
        specialize (H9 _ _ _   H12).
        assert (t = tid \/ t <> tid) as [ | ] by tauto.
        subst. erewrite get_set_eq in H13. inverts H13. eapply H9;eauto.
        erewrite get_set_neq in H13;eauto.
    + intros. 
      assert (a = p_v \/ a <> p_v) as [ | ] by tauto.
      * subst.
        rewrite get_set_eq in H12. inverts H12. 
      * erewrite get_set_neq in H12;eauto.
        assert (tid0 = tid \/ tid0 <> tid) as [ | ] by tauto.
        ** subst. erewrite get_set_eq in H13. inverts H13.
           specialize (H10 _ _ _ _ _ _ _ _ _ H12 H3 H14 H15).
           assert (t = tid \/ t <> tid) as [ | ] by tauto.
           subst. erewrite get_set_eq in H16. inverts H16.
           eapply H10;eauto.
           erewrite get_set_neq in H16;eauto.
        ** erewrite get_set_neq in H13;eauto. 
           specialize (H10 _ _ _ _ _ _ _ _ _ H12 H13 H14 H15).
           assert (t = tid \/ t <> tid) as [ | ] by tauto.
           subst. erewrite get_set_eq in H16. inverts H16.  eapply H10;eauto.
           eapply H10;eauto.
           erewrite get_set_neq in H16;eauto.
    + intros.
      assert (a = p_v \/ a <> p_v) as [ | ] by tauto.
      * subst.
        rewrite get_set_eq in H12. inverts H12.
      * erewrite get_set_neq in H12;eauto.
        assert (eid2 = p_v \/ eid2 <> p_v) as [ | ] by tauto.
        ** subst.
          rewrite get_set_eq in H13. inverts H13.
        ** subst.
          eapply H11 with (eid1 :=a) (eid2 := eid2);eauto.
          erewrite get_set_neq in H13;eauto.
  - simpljoin1. 
    intros a. intros. simpljoin1.
    assert (a = p_v \/ a <> p_v) as [ | ] by tauto.
    + subst. erewrite get_set_eq in H7. inverts H7.
      assert (tid0 = tid \/ tid0 <> tid) as [ | ] by tauto.
      ** subst. do 4 eexists. erewrite get_set_eq;eauto.
      ** inversion H8. congruence. 
        specialize (H5 _ _ _ (Logic.conj H4 H9)) as [? [? [? [? ?]]]].
        do 4 eexists. erewrite get_set_neq;eauto.
    + erewrite get_set_neq in H7;eauto.
      specialize (H5 _ _ _ (Logic.conj H7 H8)) as [? [? [? [? ?]]]].
      assert (tid0 = tid \/ tid0 <> tid) as [ | ] by tauto.
      ** subst. rewrite H5 in H3. inverts H3. 
      **  do 4 eexists. erewrite get_set_neq;eauto.
  - simpljoin1. intros. simpljoin1.
    assert (tid0 = tid \/ tid0 <> tid) as [ | ] by tauto.
    + subst. erewrite get_set_eq in H7. inverts H7.
      eexists. erewrite get_set_eq. split;eauto. simpl. auto.
    + erewrite get_set_neq in H7;eauto.
      specialize (H6 _ _ _ _ _ _ H7) as [? [? ?]].
      assert (eid = p_v \/ eid <> p_v) as [ | ] by tauto.
      * subst. rewrite H6 in H4. inverts H4. eexists.  erewrite get_set_eq. splits;eauto. simpl;auto.
      * eexists. erewrite get_set_neq;eauto. 
Qed.


Lemma  TCBNode_P_update_rdy2port: forall tcbcur rtbl prio m x y z p_v tm_v t_opt,
  ((t_opt = Some tm_v /\ tm_v <> Int.zero) \/ (t_opt = None /\ tm_v = Int.zero)) ->
  V_OSTCBBitX tcbcur = Some (Vint32 x) ->
  V_OSTCBY tcbcur = Some (Vint32 y)  -> 
  nth_val (nat_of_Z (Int.unsigned y)) rtbl = Some (Vint32 z) -> 
  TCBNode_P tcbcur rtbl (prio, rdy, m, false) ->
  TCBNode_P (update_nth_val 2 (update_nth_val 4 (update_nth_val 5 tcbcur (val_inj (or (nth_val' 5 tcbcur) (Vint32 ($ OS_STAT_PORT)))) ) (Vint32 tm_v)) (Vptr p_v))
            (update_nth_val ∘ (Int.unsigned y) rtbl (Vint32 (z &ᵢInt.not  x))) 
            (prio, wait (os_stat_port p_v) t_opt, m, false).
Proof.
  intros * Htopt.
  unfold TCBNode_P, RL_TCBblk_P, V_OSTCBPrio, R_TCB_Status_P; intros.
  simpljoin1.
  rewrite H4 in H3. inverts H3.
  rewrite H in H13. inverts H13.  
  rewrite H0 in H12. inverts H12.
  specialize (H6 prio m (ltac:(reflexivity))) as [? [? ?]].
  rewrite H15 in H6. inverts H6. clear H21 H23.
  unfold V_OSTCBMsg, V_OSTCBX, V_OSTCBY, V_OSTCBStat, V_OSTCBBitX, V_OSTCBBitY, V_OSTCBEventPtr in *.
  splits;
  repeat
  match goal with 
  | |- nth_val ?x (update_nth_val ?y _ _ ) = Some _ => assert (x <> y) by lia; erewrite nth_upd_neqrev;eauto
  end.
  - do 6 eexists.
    splits;
    repeat
    match goal with 
    | |- nth_val ?x (update_nth_val ?y _ _ ) = Some _ => assert (x <> y) by lia; erewrite nth_upd_neqrev;eauto
    | |- nth_val ?x (update_nth_val ?y _ _ ) = Some _ => assert (x = y) by lia; erewrite update_nth;eauto
    end;auto.
    erewrite nth_val_nth_val'_some_eq;eauto.
    cbn. eauto.
    splits;auto.
    right;right;right;right;right;right;right;left. clear. unfold OS_STAT_RDY, OS_STAT_PORT. mauto.
    eexists. 
    split.
    repeat match goal with 
    | |- nth_val ?x (update_nth_val ?y _ _ ) = Some _ => assert (x <> y) by lia; erewrite nth_upd_neqrev;eauto
    | |- nth_val ?x (update_nth_val ?y _ _ ) = Some _ => assert (x = y) by lia; erewrite update_nth;eauto
    end;auto.
    intros. clear - H6. unfold OS_STAT_RDY, OS_STAT_PORT, OS_STAT_SUSPEND in *. 
    destruct H6; mauto.
  - unfold RLH_RdyI_P, RdyTCBblk in *.
    intros. clear - H1 H6 H4 H24 H16. false. destruct H6. unfold V_OSTCBPrio in H.
    erewrite nth_upd_neqrev in H;[ | lia| ].
    2: do 2 (erewrite nth_upd_neqrev;eauto).
    inverts H.
    eapply prio_update_self_not_in;eauto.
  - unfold RHL_RdyI_P. intros.
    inverts H6.
  - unfold RLH_Suspend_P, WaitTCBblk.
    split.
    + intros.
      unfold V_OSTCBStat in *.
      erewrite nth_val_nth_val'_some_eq in H13;eauto.
      erewrite nth_upd_neqrev in H13;[ | lia| ].
      2: { erewrite nth_upd_neqrev;eauto. erewrite update_nth;eauto. }
      clear - H13. false.
    + intros. 
      unfold V_OSTCBStat in *.
      erewrite nth_val_nth_val'_some_eq in H13;eauto.
      erewrite nth_upd_neqrev in H13;[ | lia| ].
      2: { erewrite nth_upd_neqrev;eauto. erewrite update_nth;eauto. }
      clear - H13. false.
  - unfold RHL_Suspend_P. split;intros.
    inverts H6. inverts H6. 
  - unfold RLH_TCB_Status_Wait_P. splits.
    + Ltac waitfalse := 
    unfold V_OSTCBStat in *;
    match goal with 
    | H13 : nth_val 5 (update_nth_val _ _ _ ) = _ |- _ =>
      erewrite nth_val_nth_val'_some_eq in H13;eauto;
      erewrite nth_upd_neqrev in H13;[ | lia| erewrite nth_upd_neqrev;eauto; erewrite update_nth;eauto ];
      solve [clear - H13; false] end.
    unfold RLH_Wait_P,RLH_WaitS_P,RLH_WaitS_TO_P,RLH_WaitQ_P,RLH_WaitQ_TO_P,RLH_WaitMB_P,RLH_WaitMB_TO_P,RLH_WaitMS_P,RLH_WaitMS_TO_P,
    RLH_WaitPostQ_P, RLH_WaitS_Suspend_P, RLH_WaitQ_Suspend_P, RLH_WaitPostQ_Suspend_P, RLH_WaitMB_Suspend_P, 
    RLH_WaitMS_Suspend_P, RLH_WaitPort_P, RLH_WaitPort_TO_P, RLH_WaitPort_Suspend_P.
    repeat match goal with 
    | |- _ /\ _ => split 
    | |- _ => intros; waitfalse 
    end.
    { unfold WaitTCBblk. intros. exists m.
      unfold V_OSTCBPrio, V_OSTCBEventPtr, V_OSTCBDly in *.
      destruct H6 as [? [? ?]].
      erewrite nth_upd_neqrev in H6;[ | lia| erewrite nth_upd_neqrev;eauto; erewrite nth_upd_neqrev;eauto ].
      inverts H6.
      erewrite update_nth in H17;[ | erewrite nth_upd_neqrev;eauto; erewrite nth_upd_neqrev;eauto ].
      inverts H17.
      erewrite nth_upd_neqrev in H19;[ | lia| erewrite update_nth;eauto; erewrite nth_upd_neqrev;eauto ].
      inverts H19.
      destruct Htopt as [[? ?] | [? ?]].
      subst. left. auto.
      subst. right. auto. }
    { unfold RdyTCBblk. intros. exfalso. 
      destruct H6 as [? ?].
      unfold V_OSTCBPrio in *.
      erewrite nth_upd_neqrev in H6;[ | lia| erewrite nth_upd_neqrev;eauto; erewrite nth_upd_neqrev;eauto ].
      inverts H6.
      eapply prio_update_self_not_in;eauto. }
    + unfold RHL_TCB_Status_Wait_P.
      repeat match goal with 
      | |- _ /\ _ => split 
      | |- ?f _ _ _ => unfold f; intros * Hf;inversion Hf
      end.
      { subst.
        destruct Htopt as [[? ?] | [? ?]].
        * subst. left. exists tm_v.  split;auto.
          left. split;auto. 
          unfold WaitTCBblk.
          splits.
          unfold V_OSTCBPrio. do 3 (erewrite nth_upd_neqrev;eauto).
          unfold prio_not_in_tbl in *. intros.
          subst y.
          erewrite update_nth in H18;eauto. 
          inverts H18.
          rewrite <- H6.
          rewrite Int.and_assoc. 
          rewrite inline_bittblfunctions.and_not_zero. 
          apply Int.and_zero.
          rewrite H6.  clear - H16 H24. mauto.
          unfold V_OSTCBDly.
          erewrite nth_upd_neqrev;eauto. 
          erewrite update_nth;eauto.
          erewrite nth_upd_neqrev;eauto. 
        * subst. right. split;auto.
          unfold WaitTCBblk.
          splits.
          unfold V_OSTCBPrio. do 3 (erewrite nth_upd_neqrev;eauto).
          unfold prio_not_in_tbl in *. intros.
          subst y.
          erewrite update_nth in H17;eauto. 
          inverts H17.
          rewrite <- H6.
          rewrite Int.and_assoc. 
          rewrite inline_bittblfunctions.and_not_zero. 
          apply Int.and_zero.
          rewrite H6.  clear - H16 H24. mauto.
          unfold V_OSTCBDly.
          erewrite nth_upd_neqrev;eauto. 
          erewrite update_nth;eauto.
          erewrite nth_upd_neqrev;eauto. }
      { unfold V_OSTCBEventPtr. erewrite update_nth;eauto.
        do 2 (erewrite nth_upd_neqrev;eauto). } 
      { subst. unfold V_OSTCBStat in *.
        do 2 (erewrite nth_upd_neqrev;eauto).
        erewrite update_nth;eauto.
        erewrite nth_val_nth_val'_some_eq;eauto.
        clear. unfold OS_STAT_RDY, OS_STAT_PORT. mauto. }
Qed.

Lemma RL_TCBblk_P_hold_update_2rdy :
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

Lemma TCBNode_P_hold_update_2rdy :
forall tcbls tcur tcurl rtbl prio st msg ptbl tcbls' tcbls'' y z head tcblist' vhold sus,
V_OSTCBY tcurl = Some (Vint32 y)  -> 
nth_val (nat_of_Z (Int.unsigned y)) rtbl = Some (Vint32 z) -> 
V_OSTCBDly tcurl = Some (Vint32 Int.zero) ->
TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
R_PrioTbl_P ptbl tcbls'' vhold ->
TcbMod.join tcbls' tcbls tcbls'' ->
TCBList_P head tcblist' rtbl tcbls' ->
TCBNode_P tcurl rtbl  (prio, st, msg, sus) ->
prio_in_tbl prio rtbl ->
TCBNode_P (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY))
                       rtbl (prio, rdy, msg, false).
Proof.
  intros.
  rename H7 into Hin.
  rename H6 into Htp'.
  rename H0 into Hgrp.

  destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
  unfold TCBNode_P.

  unfold V_OSTCBMsg,V_OSTCBPrio in *.
  splits;
  try (eapply nth_upd_neqrev; try pauto);
  try (eapply nth_upd_neqrev; try pauto).
  apply RL_TCBblk_P_hold_update_2rdy; auto.

  assert ( 0 <= Int.unsigned prio < 64 /\ y = (prio >>ᵢ ($ 3))). {
  unfold RL_TCBblk_P in *. simpljoin1. unfold V_OSTCBPrio in *. 
  rewrite H0 in Hvp. inverts Hvp.  rewrite H7 in H. inverts H. auto. }

 
  funfold Hrtsl'.
  lets Hgrp': nth_val_nth_val'_some_eq Hgrp.
      
  unfold R_TCB_Status_P.
    
  (*   rewrite Hgrp'. *)
  unfold or. simpl val_inj.

  unfold R_TCB_Status_P.
  splits. 
  { unfold RLH_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  assert (Hneq1: 6%nat <> 5%nat /\ 6%nat <> 2%nat /\ 4%nat <> 5%nat /\ 4%nat <> 2%nat) by pauto.
  destruct Hneq1 as (nq1 & nq2 & nq3 & nq4).
  destruct H.
  lets Heq1: nth_upd_neq nq1 H.
  lets Heq2: nth_upd_neq nq2 Heq1.
  rewrite Heq2 in Hvp.
  inverts Hvp.   funfold Hrsl'.
  split.
  eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto.
  left.
  split.
  eapply update_nth; try eapply nth_upd_neqrev; eauto.
  eauto. }

  { unfold RHL_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  inverts H.
  funfold Hrsl'.
  splits; try splits; try eapply update_nth; try eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto. }

  (* RLH_Suspend_P *)
  { unfolds.
  split; introv Hwt Hst;
  eapply nth_upd_eq in Hst; inverts Hst. }
  (* RHL_Suspend_P *)
  { unfolds.
  split; introv Hst; inverts Hst. }
  
  
 
  lets Hnotp: prio_notin_tbl_orself H7 Hgrp.
  unfolds.
  splits; try unfolds; try introv Hif Hst; try introv Hptr;
  try (eapply WaitTCBblk_hold_update' in Hif; 
          unfold WaitTCBblk in Hif; destruct Hif as (Hprio & Hnin & Hdly);
          unfold V_OSTCBPrio in Hprio; rewrite Hprio in Hvp; inverts Hvp; tryfalse);
  try ( unfold V_OSTCBStat in Hst; eapply nth_upd_eq in Hst; inverts Hst).
  { exfalso.
    clear - H0 H7 Hin Hnin Hgrp'.
    unfold prio_in_tbl , prio_not_in_tbl in *.
    eapply inline_bittblfunctions.nth_val'2nth_val in Hgrp'.
    specialize (Hin _ _ z (eq_refl _) (eq_refl _) Hgrp').
    specialize (Hnin _ _ z (eq_refl _) (eq_refl _) Hgrp').
    rewrite Hnin in Hin.
    clear - Hin H0 H7.
    mauto. }

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

Lemma array_type_match_get_value:
  forall rtbl Zpy,
    0<=Zpy <= 7 ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    (exists v, nth_val (Z.to_nat Zpy) rtbl = Some (Vint32 v)).
Proof.
  intros.
  assert ( (exists v, nth_val (Z.to_nat Zpy) rtbl = Some (Vint32 v) /\ Int.unsigned v <=255)).
  eapply n07_arr_len_ex; eauto.
  clear -H.
  mauto.
  simp join.
  eexists; eauto.
Qed.

Lemma RH_TCBList_ECBList_P_hold_for_port_to_rdy
: forall tcbls ct p qid wt msg ecbls wls sus sus',
  get tcbls ct = Some (p, wait (os_stat_port qid) wt, msg, sus) ->
  get ecbls qid = Some (absport, wls) ->
  In ct wls ->
  RH_TCBList_ECBList_P ecbls tcbls ct ->
  RH_TCBList_ECBList_P (EcbMod.set ecbls qid (absport, remove_tid ct wls)) 
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
  splits;
  intros;
  match goal with 
  | H1: get (_ ecbls qid (absport, remove_tid ct wls)) ?eid = Some _ /\ 
        In ?tid ?qwaitset |- _ =>
    assert (He : qid = eid \/ qid <> eid ) by tauto; 
    destruct He;[subst; rewrite get_set_eq in H1;destruct H1 as [H1 _]; inverts H1 | ];
    erewrite get_set_neq in H1 by eauto;
    (eapply H in H1 || eapply Hpostq1 in H1); simpljoin1;
    assert (Ht: tid = ct \/ tid <> ct) by tauto;
    destruct Ht;[subst; rewrite Htg in H1;inverts H1 | ];
    erewrite get_set_neq;eauto
  | H1: get (_ tcbls ct (p, rdy, msg, sus')) ?tid = Some _  |- _ =>
    assert (Ht: tid = ct \/ tid <> ct) by tauto;
    destruct Ht;[subst;erewrite get_set_eq in H1;inverts H1 | ];
    erewrite get_set_neq in H1 by eauto;
    (eapply H0 in H1 || eapply Hpostq2 in H1 );simpljoin1;
    assert (He : qid = eid \/ qid <> eid ) by tauto; 
    destruct He;[subst;unfold waitset in Heg, H1; rewrite Heg in H1;inverts H1 | ];
    erewrite get_set_neq by eauto;
    repeat match goal with 
    | |- exists _ , _ => eexists end;auto
  |  |- _ => idtac
    end.

  eapply rh_tcblist_ecblist_mutex_owner_set'; eauto.
  apply Mutex_owner_hold_for_set_tcb; auto.
  (* new add about RH_TCBList_ECBList_MUTEX_OWNER_P *)
  eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_ecb.
  intro Hf.
  destruct Hf as (vpip & vo & Hf).
  inverts Hf.
  eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
  

  (* new about port *)
  { assert (He : qid = eid \/ qid <> eid ) by tauto; 
    destruct He;[subst; rewrite get_set_eq in H1 | erewrite get_set_neq in H1 by eauto].
    { destruct H1 as [H1 H2].
      inversion H1.
      subst wls0.
      assert (Ht: tid = ct \/ tid <> ct) by tauto.
      destruct Ht.
      { subst. apply in_remove_tid_false in H2. tryfalse. }
      apply in_remove_tid in H2.
      specialize (H _ _ _ (Logic.conj Heg H2)).
      simpljoin1.
      erewrite get_set_neq;eauto. }
      (eapply H in H1 ); simpljoin1.
      assert (Ht: tid = ct \/ tid <> ct) by tauto;
      destruct Ht;[subst | ].
      { eapply H0 in H1;eauto. destruct H1.
        specialize (H _ _ _ H1). simpljoin1.
        rewrite Htg in H. inversion H. subst. contradiction. }
      erewrite get_set_neq by eauto.
      do 4 eexists. eauto. }
  assert (Ht : tid = ct \/ tid <> ct ) by tauto; 
  destruct Ht;[subst; rewrite get_set_eq in H1;inversion H1 | erewrite get_set_neq in H1 by eauto].
  eapply H0 in H1 as [? H1].
  assert (He : qid = eid \/ qid <> eid ) by tauto; 
  destruct He;[subst | ].
  { erewrite get_set_eq by eauto. simpljoin1.
    rewrite H1 in Heg. inversion Heg. subst x.
    eexists. split;eauto. apply in_neq_remove_in;eauto. }
  erewrite get_set_neq by eauto.
  eexists. eauto.
Qed.

Lemma RH_SEM_EINFO_ECB_P_port_set' :
  forall qls sid  wls embls  wls',
    EcbMod.get qls sid = Some (absport, wls) ->
    RH_SEM_EINFO_ECB_P qls embls ->
    RH_SEM_EINFO_ECB_P (set qls sid (absport, wls')) embls.
Proof.
  unfold RH_SEM_EINFO_ECB_P.
  intros.
  assert (Hi: eid = sid \/ eid <> sid) by tauto.
  destruct Hi.
  eapply H0 in H1.
(*   2 :{ eauto. } *)
  rewrite H2 in H1. 
  do 2 destruct H1.
  unfold get in  H1.
  unfold EcbMap in H1.
  rewrite H1 in H.
  tryfalse.

  eapply H0 in H1.
(*   2 :{ eauto. } *)
  do 2 destruct H1.
  exists x. exists x0.
  erewrite get_set_neq;eauto.
Qed.

Lemma RH_ECBlk_EIBlk_Mux_P_port_set' :
  forall qls sid  wls embls  wls',
    EcbMod.get qls sid = Some (absport, wls) ->
    RH_ECBlk_EIBlk_Mux_P embls qls ->
    RH_ECBlk_EIBlk_Mux_P embls (set qls sid (absport, wls')).
Proof.
  unfold RH_ECBlk_EIBlk_Mux_P.
  intros.
  assert (Hi: eid = sid \/ eid <> sid) by tauto.
  destruct Hi.
  eapply H0 in H1.
(*   2 :{ eauto. } *)
  rewrite H3 in H1. 
  do 3 destruct H1.
  unfold get in  H1.
  unfold EcbMap in H1.
  rewrite H1 in H.
  tryfalse.
  auto.
  eapply H0 in H1.
(*   2 :{ eauto. } *)
  do 3 destruct H1.
  exists x. exists x0. exists x1.
  erewrite neq_set_get;eauto.
  auto.
Qed.


Lemma RH_EIBlk_ECBlk_Q_P_port_set' :
  forall qls sid  wls embls  wls',
    EcbMod.get qls sid = Some (absport, wls) ->
    RH_EIBlk_ECBlk_Q_P qls embls->
    RH_EIBlk_ECBlk_Q_P (set qls sid (absport, wls'))  embls.
Proof.
  unfold RH_EIBlk_ECBlk_Q_P.
  intros.
  assert (Hi: eid = sid \/ eid <> sid) by tauto.
  destruct Hi.
  eapply H0 in H1.
  subst.
(*   2 :{ eauto. } *)
  do 4 destruct H1.
  unfold get in  H1.
  unfold EcbMap in H1.
  rewrite H1 in H.
  tryfalse.
  auto.
  eapply H0 in H1.
(*   2 :{ eauto. } *)
  do 4 destruct H1.
  exists x. exists x0. exists x1. exists x2.
  erewrite neq_set_get;eauto.
Qed.

Lemma ASemEIBs_port_set_ecbls_preserve: 
  forall infol scapl  embls ecbls vhold  eid   wl wl' s P, 
    get ecbls eid = Some (absport, wl) ->
    s |= ASemEIBs infol scapl embls ecbls vhold ** P-> 
    s |= ASemEIBs infol scapl embls (set ecbls eid (absport, wl')) vhold ** P.  
Proof. 
  introv Hget Hsat.
  unfold ASemEIBs in *.
  sep pauto.
  clear Hsat.
  eapply RH_SEM_EINFO_ECB_P_port_set'; eauto. 
Qed.  

Lemma AMuxEIBs_port_set_ecbls_preserve: 
    forall minfol capl minfob ecbls vhold  eid  wl wl' s P, 
    get ecbls eid = Some (absport, wl) ->
    s |= AMuxEIBs minfol capl minfob ecbls vhold ** P -> 
    s |= AMuxEIBs minfol capl minfob (set ecbls eid (absport, wl')) vhold **P.  
Proof. 
  introv Hget Hsat.
  unfold AMuxEIBs in *.
  sep pauto.
  clear Hsat.
  eapply RH_ECBlk_EIBlk_Mux_P_port_set'; eauto. 
Qed.

Lemma AMqEIBs_port_set_ecbls_preserve: 
    forall minfol capl minfob ecbls vhold  eid  wl wl' s P, 
    get ecbls eid = Some (absport, wl) ->
    s |= AMqEIBs minfol capl minfob ecbls vhold ** P -> 
    s |= AMqEIBs minfol capl minfob (set ecbls eid (absport, wl')) vhold **P.  
Proof. 
  introv Hget Hsat.
  unfold AMqEIBs in *.
  sep pauto.
  clear Hsat.
  eapply RH_EIBlk_ECBlk_Q_P_port_set'; eauto. 
Qed.

Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by (clear; tauto);
  destruct h as [Ht | Hf].

Lemma mq_ecb_p_sem_set_ecbls_port_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs wls wls' sid,  
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    get els sid = Some (absport, wls) -> 
    Q_ECB_P locmp ptrmp (set els sid (absport, wls')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hqep Hget.
  unfold Q_ECB_P in *.
  introv Hgetp.
  lets H00: Hqep Hgetp.
  clear Hqep.
  destruct H00 as (Hor3 & Hdel).
  split. 
  destruct Hor3 as [Hcre1 | [Hcre2 | Hnm]].
  - 
    simpljoin1.
    left. splits; auto.
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    right; left.
    simpljoin1.
    splits; auto.
    casetac sid eptr Ht hf.
    subst.
    unfold is_que in H1.
    simpljoin1.
    rewrite Hget in H1.
    inverts H1.
    unfold is_que.
    rewrite set_a_get_a'; eauto.
  -
    right;right.
    simpljoin1.
    splits; auto.
    destruct H0.
    2: { right; auto. }
    casetac sid eptr Ht Hf.
    subst.
    unfold is_evt in H0.
    unfold is_sem, is_mux, is_que in H0.
    destruct H0 as [ | [ | ]];simpljoin1;
    rewrite Hget in H0;
    inverts H0.
    left.
    unfold is_evt in *.
    unfold is_sem, is_mux, is_que in *.
    destruct H0 as [ | [ | ]];simpljoin1.
    left. 
    erewrite get_set_neq; eauto.
    right;left. 
    erewrite get_set_neq; eauto.
    right;right. 
    erewrite get_set_neq; eauto.
  -
    introv Hdel'.
    specialize (Hdel Hdel').
    simpljoin1.
    splits; auto.
    casetac sid eptr Ht Hf.
    subst.
    unfold is_que in H.
    simpljoin1.
    rewrite Hget in H.
    inverts H.
    unfold is_que.
    rewrite set_a_get_a'; eauto.
Qed.

Lemma mux_ecb_p_port_set_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs wls wls' sid, 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
     get els sid = Some (absport, wls) -> 
    MUX_ECB_P locmp ptrmp (set els sid (absport, wls')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hmep Hget.
  unfold MUX_ECB_P in *.
  introv Hgetp.
  lets H00: Hmep Hgetp.
  clear Hmep.
  destruct H00 as [Hcre1 | [Hcre2 | Hnm]].
  - 
    simpljoin1.
    left. splits; auto.
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    right; left.
    simpljoin1.
    splits; auto.
    casetac sid eptr Ht hf.
    subst.
    unfold is_mux in H1.
    simpljoin1.
    rewrite Hget in H1.
    inverts H1.
    unfold is_mux.
    rewrite set_a_get_a'; eauto.
  -
    right;right.
    simpljoin1.
    splits; auto.
    destruct H0.
    2: { right; auto. }
    casetac sid eptr Ht Hf.
    subst.
    unfold is_evt in H0.
    unfold is_sem, is_mux, is_que in H0.
    destruct H0 as [ | [ | ]];simpljoin1;
    rewrite Hget in H0;
    inverts H0.
    left.
    unfold is_evt in *.
    unfold is_sem, is_mux, is_que in *.
    destruct H0 as [ | [ | ]];simpljoin1.
    left. 
    erewrite get_set_neq; eauto.
    right;left. 
    erewrite get_set_neq; eauto.
    right;right. 
    erewrite get_set_neq; eauto.
Qed.

Lemma sem_ecb_p_mutex_set_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs wls wls' sid, 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    get els sid = Some (absport, wls) -> 
    SEM_ECB_P locmp ptrmp (set els sid (absport, wls')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hsep Hget.
  unfold SEM_ECB_P in *.
  introv Hgetp.
  lets H00: Hsep Hgetp.
  clear Hsep.
  destruct H00 as [Hcre1 | [Hcre2 | Hnm]].
  -
    simpljoin1.
    left. splits; auto. 
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    right; left.
    simpljoin1.
    splits; auto.
    unfold is_sem in *.
    casetac sid eptr Ht Hf.
    subst.
    rewrite Hget in H1.
    simpljoin. inverts H1.
    rewrite set_a_get_a'; eauto. 
  -
    right;right.
    simpljoin1.
    splits; auto.
    destruct H0.
    2: { right; auto. }
    casetac sid eptr Ht Hf.
    subst.
    unfold is_evt in H0.
    unfold is_sem, is_mux, is_que in H0.
    destruct H0 as [ | [ | ]];simpljoin1;
    rewrite Hget in H0;
    inverts H0.
    left.
    unfold is_evt in *.
    unfold is_sem, is_mux, is_que in *.
    destruct H0 as [ | [ | ]];simpljoin1.
    left. 
    erewrite get_set_neq; eauto.
    right;left. 
    erewrite get_set_neq; eauto.
    right;right. 
    erewrite get_set_neq; eauto.
Qed. 


Lemma RLH_ECB_ETbl_P_hold_for_update_port_to_st
: forall tcbls ct p qid wt msg osevent etbl ey egrp' st petbl sus sus',
    Int.unsigned p < 64 ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_port qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey ->
    RLH_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls ->
    RLH_ECB_ETbl_P qid
     (update_nth_val 1 osevent (Vint32 egrp'),
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))), petbl)
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

Lemma RHL_ECB_ETbl_P_hold_for_update_port_to_rdy
: forall tcbls ct p qid wt msg osevent etbl ey egrp' ptbl vhold petbl sus sus',
    Int.unsigned p < 64 ->
    R_PrioTbl_P ptbl tcbls vhold ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_port qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey ->
    RHL_ECB_ETbl_P qid (osevent,etbl, petbl) tcbls ->
    RHL_ECB_ETbl_P qid
     (update_nth_val 1 osevent (Vint32 egrp'),
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))), petbl)
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
  [left | right; left | do 2 right; left | do 3 right;left | do 4 right];
  eapply nth_upd_neqrev; try pauto.
Qed.

Lemma RLH_ECBData_P_hold_port
: forall  ct w ecbcurl,
  RLH_ECBData_P ecbcurl (absport, w) ->
RLH_ECBData_P ecbcurl (absport, remove_tid ct w).
Proof.
  intros.
  unfolds.
  unfolds in H.
  destruct ecbcurl; try tryfalse.
  split; pauto.
Qed.

(* copy from other event files *)
Lemma R_ECB_PETbl_P_set_tcb_wait_hold:
forall tcbls ptcb prio m st m' x v0 v1 v prio' sus sus',
~(exists qid time, st = wait (os_stat_postq qid) time) ->
TcbMod.get tcbls ptcb = Some (prio, rdy, m, sus) ->
R_ECB_PETbl_P x (v0, v1, v) tcbls ->
R_ECB_PETbl_P x (v0, v1, v)
  (TcbMod.set tcbls ptcb (prio', st, m', sus')).
Proof.
intros.
funfold H1.
unfolds; splits; unfolds; intros.
eapply H1 in H4; eauto.
mytac.
unfold get in *; unfold TcbMap in *.
assert (Hc: ptcb = x0 \/ ptcb <> x0) by tauto.
destruct Hc.
subst.
rewrite H0 in H4; inverts H4.
repeat eexists.
rewrite TcbMod.set_a_get_a'; eauto.
eapply tidspec.neq_beq_false; eauto.
unfold get in *; unfold TcbMap in *.
assert (Hc: ptcb = tid \/ ptcb <> tid) by tauto.
destruct Hc.
subst.
rewrite TcbMod.map_get_set in H3.
inverts H3.
false. eapply H; eauto.
rewrite TcbMod.map_get_set' in H3; auto.
eapply H2; eauto.
Qed.

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

Lemma get_last_prop:
  forall (l : list EventCtr)  x v y,
    l <> nil -> 
    (get_last_ptr ((x, v) :: l)  =   y <->
     get_last_ptr  l =  y).
Proof.
  destruct l.
  intros.
  tryfalse.
  intros.
  unfolds get_last_ptr.
  simpl.
  destruct l; splits;auto.
Qed.
Lemma Mbox_common_ecblist_p_decompose :
  forall  y1 z1  x y2 z2 t z ,
    length y1 = length y2 ->
    ECBList_P x Vnull (y1++z1) (y2++z2) t z ->
    exists x1 t1 t2,
      ECBList_P x x1 y1 y2 t1 z /\ ECBList_P x1 Vnull z1 z2 t2 z /\
      EcbMod.join t1 t2 t /\  (get_last_ptr y1 = None \/ get_last_ptr y1  = Some x1).
Proof.
  inductions y1; inductions y2.
  simpl.
  intros.
  do 3 eexists; splits; eauto.
  eapply EcbMod.join_emp; eauto.
  intros.
  simpl in H.
  tryfalse.
  intros.
  simpl in H; tryfalse.
  intros.
  simpl in H.
  inverts H.
  simpl in H0.
  mytac.
  rename H1 into Hpetbl; rename H3 into H1. (* new add *)
  destruct a.
  destruct p. (* new add *)
  mytac.
  lets Hx : IHy1 H2 H4.
  mytac.
  lets Hex : joinsig_join_ex H1 H7.
  mytac.
  do 3 eexists.
  splits.
  simpl.
  eexists; splits; eauto.
  do 3 eexists; splits.
  eauto.
  2: eauto.
  3: eauto.
  2 : eauto.
  eauto.
  eauto.
  assert (y1 = nil \/ y1 <> nil) by tauto.
  destruct H11.
  subst y1.  
  right.
  simpl in H2.
  apply eq_sym in H2.
  apply length_zero_nil in H2.
  subst y2.
  simpl in H5.
  mytac.

  destruct H8.
  left.
  eapply  get_last_prop in H11.
  eapply H11; eauto.
  eapply  get_last_prop in H11.
  right.
  eapply H11; eauto.
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
eapply (get_last_prop) in Hn.
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
  2:{
  destruct (V_OSEventListPtr v0); try tryfalse; destruct v2; try tryfalse. } (*v,v1 -> v0, v2 *)
  apply beq_addrval_eq in eq1.
  subst x.
  do 2 eexists.
  splits; try eauto.
  exists eptr. splits; try auto.
  do 3 eexists. splits; eauto.
  apply EcbMod.map_join_comm.
  apply EcbMod.map_join_emp.
  lets Hsp: Mbox_common_ecblist_p_decompose Hl Hep.
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

Lemma  ecb_etbl_set_hold:
  forall x y tcbls prio st m ptcb m' sus sus',
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    R_ECB_ETbl_P x y tcbls  ->
    R_ECB_ETbl_P x y  (TcbMod.set tcbls ptcb (prio, st, m', sus')).
Proof.
  introv Htc Hr.
  unfolds in Hr.
  destruct Hr as (Hr1 & Hr2 & Hr3).
  destruct Hr1 as (Hra1 & Hra2 & Hra3 & Hra4 & Hra5).
  destruct Hr2 as (Hrb1 & Hrb2 & Hrb3 & Hrb4 & Hrb5).
  unfolds.
  splits.
  unfolds.
  splits.

  { unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  eapply Hra1 in H0; eauto.
  mytac.
  assert (ptcb = x0 \/ ptcb <> x0) by tauto.
  destruct H1.
  subst.
  unfold get in *; simpl in *.

  rewrite H0 in Htc.
  inverts Htc.
  exists x0.
  exists x1 m' sus'.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  exists x0.
  exists x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto. }
  { 
  unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  eapply Hra2 in H0; eauto.
  mytac.
  assert (ptcb = x0 \/ ptcb <> x0) by tauto.
  destruct H1.
  subst.
  unfold get in *; simpl in *.
  rewrite H0 in Htc.
  inverts Htc.
  exists x0.
  exists x1 m' sus'.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  exists x0.
  exists x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto. }
  {
  unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  eapply Hra3 in H0; eauto.
  mytac.
  assert (ptcb = x0 \/ ptcb <> x0) by tauto.
  destruct H1.
  subst.
  unfold get in *; simpl in *.
  rewrite H0 in Htc.
  inverts Htc.
  exists x0.
  exists x1 m' sus'.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  exists x0.
  exists x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto. }
  { unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  eapply Hra4 in H0; eauto.
  mytac.
  assert (ptcb = x0 \/ ptcb <> x0) by tauto.
  destruct H1.
  subst.
  unfold get in *; simpl in *.
  rewrite H0 in Htc.
  inverts Htc.
  exists x0.
  exists x1 m' sus'.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  exists x0.
  exists x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto. }
  { unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  eapply Hra5 in H0; eauto.
  mytac.
  assert (ptcb = x0 \/ ptcb <> x0) by tauto.
  destruct H1.
  subst.
  unfold get in *; simpl in *.
  rewrite H0 in Htc.
  inverts Htc.
  exists x0.
  exists x1 m' sus'.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  exists x0.
  exists x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto. }
  unfolds.
  splits.
  { unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto. 
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrb1; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto. }
  { unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto. 
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrb2; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto. }
  { unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto. 
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrb3; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto. }
  { unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto. 
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrb4; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto. } 
  { unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto. 
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrb5; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto. } 
  auto.
Qed.

Lemma  ecb_petbl_set_hold:
  forall x y tcbls prio st m ptcb m' sus sus',
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    R_ECB_PETbl_P x y tcbls  ->
    R_ECB_PETbl_P x y  (TcbMod.set tcbls ptcb (prio, st, m', sus')).
Proof.
  introv Htc Hr.
  unfolds in Hr.
  destruct Hr as (Hr1 & Hr2).
  unfolds.
  splits.
  unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  eapply Hr1 in H0; eauto.
  mytac.
  assert (ptcb = x0 \/ ptcb <> x0) by tauto.
  destruct H1.
  subst.
  unfold get in *; simpl in *.

  rewrite H0 in Htc.
  inverts Htc.
  exists x0.
  exists x1 m' sus'.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  exists x0.
  exists x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
   assert (ptcb = tid \/ ptcb <> tid) by tauto. 
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hr2; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
Qed.


Lemma ECBList_P_high_tcb_get_msg_hold:
  forall  ectrl head tail msgql ecbls tcbls ptcb prio st m m' sus sus',
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    ECBList_P head tail ectrl msgql ecbls 
              (TcbMod.set tcbls ptcb (prio, st, m', sus')).
Proof.
  inductions ectrl.
  intros.
  simpl in H.
  mytac.
  simpl; splits; auto.
  intros.
  simpl in H.
  mytac.
  destruct msgql; tryfalse.
  destruct a.
  destruct p. (* new add *)
  mytac.
  simpl.
  eexists.
  splits; eauto.


  eapply ecb_etbl_set_hold; eauto.
  eapply ecb_petbl_set_hold; eauto. (* new add *)
  do 3 eexists; splits; eauto.
Qed.
(* copy end *)

Lemma TCBList_P_tcb_msg2vnull_hold :
    forall ptcb v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 rtbl vl
           tcbls prio m,
    TCBList_P (Vptr ptcb) ((v1::v2::v3::v4::v5::v6::v7::v8::v9::v10::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, rdy, m, false) ->
    TCBList_P (Vptr ptcb) ((v1::v2::Vnull::Vnull::v5::V$ OS_STAT_RDY::v7::v8::v9::v10::v11::nil)::vl) rtbl
                       (TcbMod.set tcbls ptcb (prio, rdy, Vnull, false)).
Proof.
  introv Htc Hget.
  cbn in Htc.
  simpljoin1.
  inverts H.
  cbn.
  do 4 eexists; splits; eauto.
  unfolds; simpl; auto.
  instantiate (1:=(prio,rdy,Vnull, false)).
  eapply tcbjoin_set; eauto.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
   lets Heq : tcbjoin_get H1 Hget.
  inverts Heq. inverts H0.
  simpljoin1.
  simpl_hyp.
  unfold RL_TCBblk_P in H2.
  simpljoin1.
  cbn in *. 
  inverts H. inverts H0. inverts H2. inverts H5. inverts H6. inverts H7.
  assert (x7 = $ OS_STAT_RDY).
  { funfold H4. specialize (H0 _ _  (eq_refl _ )). cbn in H0. simpljoin1. inverts H7. auto. }
  subst x7.

  splits; try unfolds. simpl; auto.
  simpl; auto. 
  exists x2 (x2&ᵢ$ 7) (x2 >>ᵢ $ 3) ($ 1<<ᵢ(x2&ᵢ$ 7)) ($ 1<<ᵢ(x2 >>ᵢ $ 3))  ($ OS_STAT_RDY).
  splits;auto.
  splits;auto.

  eexists. cbn. 
  splits;eauto.

  rename x2 into prio.
  splits.
  { funfold H4.
  clear - H.
  funfold H.
  unfolds.
  intros.
   assert (RdyTCBblk
        (x0
         :: v2
            :: v3
               :: m
                  :: v5 :: V$ OS_STAT_RDY :: Vint32 prio :: Vint32 (prio&ᵢ$ 7) :: Vint32 (prio >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(prio&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(prio >>ᵢ $ 3)) :: nil)
        rtbl prio0).
  unfolds.
  funfold H0; simpl; auto.
  apply H in H1.
  destruct H1 as (Hdly & H2).
  split;auto.
  destruct H2 as [ Hfirst | Hend ].
  left;split;auto.
  destruct Hfirst as (Hst & Heq).
  destruct Heq.
  inverts H1.
  eexists; eauto.
  
  destruct Hend as [ Hfirst | Hend ].
  right;left.
  destruct Hfirst as (Hst & Heq).
  inverts Hst.
  destruct Hend as [ Hfirst | Hend ].
  right;right;left.
  destruct Hfirst as (Hst & Heq).
  inverts Hst.

  destruct Hend as [ Hfirst | Hend ].
  right;right;right.
  destruct Hfirst as (Hst & Heq).
  inverts Hst.

  destruct Hend as (Hst & Heq).
  inverts Hst. }
  
  {
  destruct H4 as (_ & Hhl & _).
  unfolds in Hhl.
  unfolds.
  intros.
  inverts H.
  assert ( (prio0, rdy, m, false) = (prio0, rdy, m, false)) by auto. 
  apply Hhl in H.
  simpljoin1; try unfolds;simpl; auto.
  }

  (* new add about suspend *)
  { destruct H4 as (_ & _ & Hsus & _).
  unfolds in Hsus.
  destruct Hsus as (Hrdy & Hwt).
  unfolds.
  split; intros.
  simpl_hyp.
  assert (WaitTCBblk
         (x0
          :: v2
             :: v3
                :: m :: v5 :: V$ OS_STAT_RDY :: Vint32 prio :: Vint32 (prio&ᵢ$ 7) :: Vint32 (prio >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(prio&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(prio >>ᵢ $ 3)) :: nil)
         rtbl prio0 Int.zero).
  funfold H.
  simpl_hyp. } 
  
  { (* RHL_Suspend_P *)
  destruct H4 as (_ & _ & _ & Hsus & _).
  unfolds in Hsus.
  destruct Hsus as (Hrdy & Hwt).
  unfolds.
  split; introv Heq; inverts Heq. }
  (* end of new add *)

  { destruct H4 as (_ & _ & _ & _ & Hhl & _).
  unfolds in Hhl.
  unfolds.
  simpljoin1; splits; try unfolds;simpl; auto;
  try solve [intros; simpl_hyp].
  
  { intros.
  simpl_hyp.
  unfolds in H.
  assert (Hwt: WaitTCBblk
  (x0
  :: v2
     :: v3
        :: m :: v5 :: V$ OS_STAT_RDY :: Vint32 prio :: Vint32 (prio&ᵢ$ 7) :: Vint32 (prio >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(prio&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(prio >>ᵢ $ 3)) :: nil)
         rtbl prio0 t).
(*   funfold H7. *)
  unfolds; simpl; auto.
  apply H in Hwt.
  destruct Hwt.
  splits; eauto.
  simpljoin1; eexists; eauto.
  unfolds; simpl; auto. }

  splits; try solve [unfolds; intros; simpl_hyp].
  splits; try solve [unfolds; intros; simpl_hyp]. }

  unfolds.
  splits;
  try (unfolds;
  intros;
  inverts H);
  try (eapply H4; eauto).
  splits;
  try (unfolds;
  intros;
  inverts H);
  try (eapply H4; eauto).
Qed.


Lemma RH_TCBList_ECBList_P_high_changem_hold :
  forall ecbls tcbls pcur  m  prio  m' sus sus',
    RH_TCBList_ECBList_P ecbls tcbls pcur ->
    TcbMod.get tcbls pcur = Some (prio, rdy, m', sus) ->
    RH_TCBList_ECBList_P ecbls (TcbMod.set tcbls pcur (prio, rdy, m, sus')) pcur. 
Proof.
  introv Hr He.
  unfolds in Hr.
  destruct Hr as (Hr1 & Hr2 & Hr3 & Hr4 & Hr5).
  unfolds.
  splits.

  { splits.  
  
    { intros.
    assert (tid = pcur \/ tid <> pcur) by tauto.
    destruct H0.
    subst.
    apply Hr1 in H.
    simpljoin1.
    unfold get in H; unfold TcbMap in H.
    rewrite H in He. inverts He.
    rewrite TcbMod.set_sem ;
      rewrite tidspec.neq_beq_false; auto.
    apply Hr1 in H.
    simpljoin1.
    do 3 eexists; eauto. }

    { intros.
    assert (tid = pcur \/ tid <> pcur) by tauto.
    destruct H0.
    subst.
    apply Hr1 in H.
    simpljoin1.
    unfold get in H; unfold TcbMap in H.
    rewrite H in He. inverts He.
    rewrite TcbMod.set_sem ;
      rewrite tidspec.neq_beq_false; auto.
    apply Hr1 in H.
    simpljoin1.
    do 3 eexists; eauto. }
  
    { intros.
    assert (tid = pcur \/ tid <> pcur) by tauto.
    destruct H0.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; auto.
    inverts H.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; auto.
    apply Hr1 in H.
    eauto. }

    { intros.
    assert (tid = pcur \/ tid <> pcur) by tauto.
    destruct H0.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; auto.
    inverts H.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; auto.
    apply Hr1 in H.
    eauto. }  }
  
  { splits.
    { intros.
    assert (tid = pcur \/ tid <> pcur) by tauto.
    destruct H0.
    subst.
    apply Hr2 in H.
    simpljoin1.
    unfold get in H; unfold TcbMap in H.
    rewrite H in He. inverts He.
    rewrite TcbMod.set_sem ;
      rewrite tidspec.neq_beq_false; auto.
    apply Hr2 in H.
    simpljoin1.
    do 3 eexists; eauto. }
  
    { intros.
    assert (tid = pcur \/ tid <> pcur) by tauto.
    destruct H0.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; auto.
    inverts H.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; auto.
    apply Hr2 in H.
    eauto. } }

  { splits.
    { intros.
    assert (tid = pcur \/ tid <> pcur) by tauto.
    destruct H0.
    subst.
    apply Hr3 in H.
    simpljoin1.
    unfold get in H; unfold TcbMap in H.
    rewrite H in He. inverts He.
    rewrite TcbMod.set_sem ;
      rewrite tidspec.neq_beq_false; auto.
    apply Hr3 in H.
    simpljoin1.
    do 3 eexists; eauto. }
  
    { intros.
    assert (tid = pcur \/ tid <> pcur) by tauto.
    destruct H0.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; auto.
    inverts H.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; auto.
    apply Hr3 in H.
    eauto. } }
  
  { splits.
    intros.
    assert (tid = pcur \/ tid <> pcur) by tauto.
    destruct H0.
    subst.
    apply Hr4 in H.
    simpljoin1.
    unfold get in H; unfold TcbMap in H.
    rewrite H in He. inverts He.
    rewrite TcbMod.set_sem ;
      rewrite tidspec.neq_beq_false; auto.
    apply Hr4 in H.
    simpljoin1.
    do 3 eexists; eauto.
  
    intros.
    assert (tid = pcur \/ tid <> pcur) by tauto.
    destruct H0.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; auto.
    inverts H.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; auto.
    apply Hr4 in H.
    eauto.

    apply Mutex_owner_hold_for_set_tcb.
    unfold RH_TCBList_ECBList_MUTEX_P in Hr4.
    simpljoin1.
    eauto.
    (* new add about RH_TCBList_ECBList_MUTEX_OWNER_P *)
    destruct Hr4 as (_ & _ & _ & Hrb).
    eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.   } 

  { splits.  
  
    { intros.
    assert (tid = pcur \/ tid <> pcur) by tauto.
    destruct H0.
    subst.
    apply Hr5 in H.
    simpljoin1.
    unfold get in H; unfold TcbMap in H.
    rewrite H in He. inverts He.
    rewrite TcbMod.set_sem ;
      rewrite tidspec.neq_beq_false; auto.
    apply Hr5 in H.
    simpljoin1.
    do 3 eexists; eauto. }
  
    { intros.
    assert (tid = pcur \/ tid <> pcur) by tauto.
    destruct H0.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; auto.
    inverts H.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; auto.
    apply Hr5 in H.
    eauto. } }
Qed.


Lemma ECBList_P_high_tcb_block_hold_port:
  forall  ectrl head tail msgql ecbls tcbls ptcb prio  m qid time sus sus',
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, rdy, m, sus) ->
    EcbMod.get ecbls qid = None ->
    ECBList_P head tail ectrl msgql ecbls 
              (TcbMod.set tcbls ptcb (prio, wait (os_stat_port qid) time, m, sus')).
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
  splits.
  2:
  {
    unfolds.
    intros.
    eapply Hra1 in H6;eauto.
    mytac.
    assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
    destruct H7.
    subst.
    unfold get in H6; simpl in H6.
    rewrite H0 in H6.
    inverts H6.
    exists x3 x4 x5.
    rewrite TcbMod.set_sem.
    rewrite tidspec.neq_beq_false; eauto.
  }
  2:
  {
    unfolds.
    intros.
    eapply Hra2 in H6;eauto.
    mytac.
    assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
    destruct H7.
    subst.
    unfold get in H6; simpl in H6.
    rewrite H0 in H6.
    inverts H6.
    exists x3 x4 x5.
    rewrite TcbMod.set_sem.
    rewrite tidspec.neq_beq_false; eauto.
  }
  {
    unfolds.
    intros.
    eapply Hra3 in H6;eauto.
    mytac.
    assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
    destruct H7.
    subst.
    unfold get in H6; simpl in H6.
    rewrite H0 in H6.
    inverts H6.
    exists x3 x4 x5.
    rewrite TcbMod.set_sem.
    rewrite tidspec.neq_beq_false; eauto.
  }
  {
    unfolds.
    intros.
    eapply Hra4 in H6;eauto.
    mytac.
    assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
    destruct H7.
    subst.
    unfold get in H6; simpl in H6.
    rewrite H0 in H6.
    inverts H6.
    exists x3 x4 x5.
    rewrite TcbMod.set_sem.
    rewrite tidspec.neq_beq_false; eauto.
  }
  {
    unfolds.
    intros.
    eapply Hra5 in H6;eauto.
    mytac.
    assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
    destruct H7.
    subst.
    unfold get in H6; simpl in H6.
    rewrite H0 in H6.
    inverts H6.
    exists x3 x4 x5.
    rewrite TcbMod.set_sem.
    rewrite tidspec.neq_beq_false; eauto.
  }
  unfolds.
  splits.
  5:
  {
    unfolds.
    intros.
    assert (tid = ptcb \/ tid <> ptcb) by tauto.
    destruct H6.
    subst.
    rewrite TcbMod.set_sem in H2.
    rewrite tidspec.eq_beq_true in H2; eauto.
    inverts H2.
    apply ecbmod_joinsig_get in H3.
    rewrite H3 in H1.
    tryfalse.
    rewrite TcbMod.set_sem in H2.
    rewrite tidspec.neq_beq_false in H2; eauto.
  }

  { unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto. }
  { unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto. }
  { unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto. }
  { unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto. }
  simpl; auto.
  (* new add about petbl *)
  eapply R_ECB_PETbl_P_set_tcb_wait_hold; eauto.
  introv Hf. destruct Hf as (qd & wt & Hf). inverts Hf.
  (* end of new add *)
  do 3 eexists; splits; eauto.
  eapply IHectrl; eauto.
  eapply  ecbmod_joinsig_get_none; eauto.
Qed.

Lemma R_ECB_ETbl_P_high_tcb_block_hold_port:
  forall (l : addrval) (vl : vallist) et (etbl : vallist) (tcbls : TcbMod.map)
    (ptcb : tidspec.A) (prio : int32) (st : taskstatus) 
    (m : msg) sus sus' (y bity bitx ey : int32) time (av : addrval) petbl egrp,
  V_OSEventType et = Some (V$ OS_EVENT_TYPE_PORT) ->
  V_OSEventGrp et = Some (Vint32 egrp) ->
  Int.unsigned prio < 64 ->
  R_PrioTbl_P vl tcbls av ->
  R_ECB_ETbl_P l (et, etbl, petbl) tcbls ->
  TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
  y = Int.shru prio ($ 3) ->
  bity = Int.shl ($ 1) y ->
  bitx = Int.shl ($ 1) (prio &ᵢ $ 7) ->
  nth_val ∘(Int.unsigned y) etbl = Some (Vint32 ey) ->
  R_ECB_ETbl_P l
    (update_nth_val 1 et (Vint32 (Int.or egrp bity)),
    update_nth_val ∘(Int.unsigned y) etbl (Vint32 (Int.or ey bitx)), petbl)
    (TcbMod.set tcbls ptcb (prio, wait (os_stat_port l) time, m, sus')).
Proof.
  introv Htp Hegrp Hran Hrs  Hre Htc Hy Hb1 Hb2 Hnth.
  subst.
  unfolds in Hre.
  destruct Hre as (Hre1 & Hre2 & Het).
  unfolds.
  splits.
  unfolds.
  splits.
  5:{
    unfolds.
    intros.
    destruct Hre1 as (_ & _ & _ & _ & Hre1).
    destruct Hre2 as (_ & _ & _ & _ & Hre2).
    unfolds in Hre1.
    unfolds in Hre2.
    assert (prio = $ prio0 \/ prio <> $ prio0) by tauto.
    destruct H1.
    { subst.
    exists ptcb time m sus'.
    rewrite TcbMod.set_sem.
    erewrite tidspec.eq_beq_true; eauto. }
    lets Hres : prio_wt_inq_keep Hran H1 Hnth .
    destruct Hres.
    apply H2 in H.
    apply Hre1 in H.
    mytac.
    exists x x0 x1 x2.
    assert (x = ptcb \/ x <> ptcb) by tauto.
    destruct H4.
    subst.
    unfold get in H; simpl in H.
    rewrite Htc in H.
    inverts H.
    tryfalse.
    rewrite TcbMod.set_sem.
    erewrite tidspec.neq_beq_false; eauto.
    unfolds. 
    simpl; auto.
  }

  {
    unfolds.
    intros.
    usimpl H0. 
    erewrite nth_upd_neqrev in H2 by eauto. tryfalse.
  }
  {
    unfolds.
    intros.
    usimpl H0.
    erewrite nth_upd_neqrev in H2 by eauto. tryfalse.
  }
  {
    unfolds.
    intros.
    usimpl H0.
    erewrite nth_upd_neqrev in H2 by eauto. tryfalse.
  }
  {
    unfolds.
    intros.
    usimpl H0.
    erewrite nth_upd_neqrev in H2 by eauto. tryfalse.
  }
  unfolds.
  splits.
  5:
  {
    unfolds.
    intros.
    assert (tid = ptcb \/ tid <> ptcb) by tauto.  
    destruct H0.
    subst.
    splits.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.eq_beq_true in H; eauto.
    inverts H.
    unfolds.
    rewrite Int.repr_unsigned.
    exists ( prio0 &ᵢ $ 7).
    exists (Int.shru prio0 ($3)).
    exists ((Int.or ey ($ 1<<ᵢ(prio0 &ᵢ $ 7)))).
    splits; eauto.
    clear - Hran.
    int auto.
    eapply pure_lib.update_nth; eauto.
    rewrite Int.and_commut.
    rewrite Int.or_commut.
    unfold Int.one.
    rewrite Int.and_or_absorb.
    auto.
    unfolds. erewrite nth_upd_neqrev by eauto. auto.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.neq_beq_false in H; eauto.
    unfolds in Hre2.
    destruct Hre2 as (_ & _ & _ & _ & Hre2).
    lets Hasd : Hre2  H.
    destruct Hasd as (Has1 & Has2).
    splits.
    eapply prio_wt_inq_keep; eauto.
    rewrite Int.repr_unsigned.
    unfolds  in Hrs.
    destruct Hrs.
    destruct H2.
    unfolds in H3.
    lets Hdd : H3 H0 H Htc.
    eauto.
    unfolds. erewrite nth_upd_neqrev by eauto. auto.
  }
  {
    unfolds.
    intros.
    assert (tid = ptcb \/ tid <> ptcb) by tauto.  
    destruct H0.
    subst.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.eq_beq_true in H; eauto.
    inverts H.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.neq_beq_false in H; eauto.
    destruct Hre2 as (Hre2&_).
    apply Hre2 in H.
    destruct H.
    usimpl H1.
    unfolds V_OSEventType. rewrite Htp in H3.
    tryfalse.
  }
  {
    unfolds.
    intros.
    assert (tid = ptcb \/ tid <> ptcb) by tauto.  
    destruct H0.
    subst.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.eq_beq_true in H; eauto.
    inverts H.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.neq_beq_false in H; eauto.
    destruct Hre2 as (_&Hre2&_).
    apply Hre2 in H.
    destruct H.
    usimpl H1.
    unfolds V_OSEventType. rewrite Htp in H3.
    tryfalse.
  }
  {
    unfolds.
    intros.
    assert (tid = ptcb \/ tid <> ptcb) by tauto.  
    destruct H0.
    subst.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.eq_beq_true in H; eauto.
    inverts H.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.neq_beq_false in H; eauto.
    destruct Hre2 as (_&_ & Hre2&_).
    apply Hre2 in H.
    destruct H.
    usimpl H1.
    unfolds V_OSEventType. rewrite Htp in H3.
    tryfalse.
  }

  {
    unfolds.
    intros.
    assert (tid = ptcb \/ tid <> ptcb) by tauto.  
    destruct H0.
    subst.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.eq_beq_true in H; eauto.
    inverts H.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.neq_beq_false in H; eauto.
    destruct Hre2 as (_&_&_&Hre2&_).
    apply Hre2 in H.
    destruct H.
    usimpl H1.
    unfolds V_OSEventType. rewrite Htp in H3.
    tryfalse.
  }

  simpl.
  unfolds.
  branch 5.
  unfolds; simpl; auto.
  erewrite nth_upd_neqrev by eauto. auto.
Qed.

Lemma ECBList_P_high_tcb_block_hold_port_to_rdy:
  forall  ectrl head tail msgql ecbls tcbls ptcb prio  m qid time sus sus',
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, wait (os_stat_port qid) time, m, sus) ->
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
  (* new add about petbl *)
  eapply R_ECB_PETbl_P_hold_for_set_rdy; eauto.
  introv Hf. destruct Hf as (qd & wt & Hf). inverts Hf.
  (* end of new add *)
  do 3 eexists; splits; eauto.
  eapply IHectrl; eauto.
  eapply  ecbmod_joinsig_get_none; eauto.
Qed.

Lemma R_ECB_ETbl_P_hold_for_update_port_to_rdy
: forall tcbls ct p qid wt msg osevent etbl y ey egrp' bitx ptbl vhold petbl sus sus',
      Int.unsigned p < 64 ->
      y = p >>ᵢ $ 3 ->
      bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
      R_PrioTbl_P ptbl tcbls vhold ->
      TcbMod.get tcbls ct = Some (p, wait (os_stat_port qid) wt, msg, sus) ->
      R_ECB_ETbl_P qid (osevent, etbl, petbl) tcbls ->
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
  eapply RLH_ECB_ETbl_P_hold_for_update_port_to_st; try eauto.
  eapply RHL_ECB_ETbl_P_hold_for_update_port_to_rdy; try eauto.
  simpl in *.
  eapply Event_Type_P_hold_for_update; try auto.
Qed.

Lemma ECBList_P_hold_for_update_port_to_rdy
: forall head (els1 els2: list os_inv.EventCtr) osevent etbl osevent' etbl' ecblist1 ecblist2 ecbcurl ecbls 
              tcbls ct p wt msg ey egrp' y bitx qid ptbl vhold wls petbl sus sus',
   Int.unsigned p < 64 ->
   y = p >>ᵢ $ 3 ->
   bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
  R_PrioTbl_P ptbl tcbls vhold ->
  length els1 = length ecblist1 ->
  RH_TCBList_ECBList_P ecbls tcbls ct ->
  get tcbls ct = Some (p, wait (os_stat_port qid) wt, msg, sus) ->
  get ecbls qid = Some (absport, wls) ->
  In ct wls ->
  get_ectr (Vptr qid) head els1  = None ->
  get_ectr (Vptr qid) head (els1 ++ ((osevent,etbl, petbl) :: nil))  = Some (osevent,etbl, petbl) ->
  ECBList_P head Vnull (els1 ++ ((osevent,etbl, petbl) :: nil) ++ els2) 
                        (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2) ecbls tcbls ->
  nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 ey ->
  osevent' = update_nth_val 1 osevent (Vint32 egrp') ->
  etbl' = update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (ey&ᵢInt.not bitx)) ->
  V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_PORT)) -> (* new add *)
  ECBList_P head Vnull (els1 ++ ((osevent',etbl', petbl) :: nil) ++ els2) 
                        (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2)
                         (set ecbls qid (absport, remove_tid ct wls))
                        (set tcbls ct (p, rdy, msg, sus'))
.
Proof.
  introv Hpr Hy Hbitx Hrpt Hl Hrte Htg Heg Hi Hgptr1.
  introv Hgptr2 Hep Hey Het' Hetbl' Htp.
  assert (Hels1: els1 = nil \/ els1 <> nil) by tauto.
  destruct Hels1.
  subst els1.
  assert (ecblist1 = nil) by (eapply length_zero_nil; simpl in *; auto).
  subst ecblist1.
  simpl in *.
  mytac.
  destruct (beq_addrval qid x) eqn: eq1.
  2: { destruct (V_OSEventListPtr osevent); try tryfalse; destruct v; try tryfalse. }
  apply beq_addrval_eq in eq1.
  subst x.
  exists qid.
  splits; try auto.
  eapply R_ECB_ETbl_P_hold_for_update_port_to_rdy; try eauto.
  (* new add about petbl *)
  { eapply R_ECB_PETbl_P_high_tcb_block_hold'; eauto.
  rewrite Htp; introv Hf; tryfalse.
  eapply nth_upd_neqrev with (m:= 1%nat) in Htp.
  rewrite Htp.
  introv Hf; tryfalse.
  auto with zarith.
  introv Hf. destruct Hf as (qd & qwt & Hf). inverts Hf. }
  (* end of new add *)
  exists (absport, remove_tid ct wls) x1 x2.
  splits; try auto.
  { unfold V_OSEventListPtr in *.
  eapply nth_upd_neqrev; try pauto. }
  { assert (join (sig qid (absport, remove_tid ct wls)) x1 (set ecbls qid (absport, remove_tid ct wls))).
    eapply join_sig_set;eauto. 
    unfold join in H. unfold EcbMap in H. auto. }
  { lets Heg': EcbMod.join_sig_get H3. (* H2 -> H3 *)
    unfold get, EcbMap in Heg.
    rewrite Heg in Heg'.
    inverts Heg'.
    eapply RLH_ECBData_P_hold_port; auto. } 
  { eapply ECBList_P_high_tcb_block_hold_port_to_rdy; try eauto.
    assert (get x1 qid = None).
    { eapply map_join_get_no_perm1;eauto. eapply map_get_sig. }
    unfold get, EcbMap in H. auto. }
  (* els1 <> nil *)
  lets Hsp: Mbox_common_ecblist_p_decompose Hl Hep.
  simpl in *.
  mytac.
  lets Hx2: get_ectr_sing H Hgptr1 Hgptr2.
  destruct H3; rewrite H1 in Hx2; inverts Hx2.
  eapply ecblist_p_compose; try eauto.
  2:{ eapply ECBList_P_high_tcb_block_hold_port_to_rdy; try eauto.
    assert (get x0 qid = None).
    { assert (join x1 x0 ecbls).  eapply map_join_comm. unfold join, EcbMap. auto.
      eapply map_join_get_no_perm1;eauto. eapply join_sig_get;eauto. }
    unfold get, EcbMap in H. auto. }
  { eapply EcbMod.my_joinsig_join_set; try eauto. }
  simpl.
  exists qid.
  splits; try auto.
  eapply R_ECB_ETbl_P_hold_for_update_port_to_rdy; try eauto.
  (* new add about petbl *)
  { eapply R_ECB_PETbl_P_high_tcb_block_hold'; eauto.
  rewrite Htp; introv Hf; tryfalse.
  eapply nth_upd_neqrev with (m:= 1%nat) in Htp.
  rewrite Htp.
  introv Hf; tryfalse.
  auto with zarith.
  introv Hf. destruct Hf as (qd & qwt & Hf). inverts Hf. }
  (* end of new add *)
  exists (absport, remove_tid ct wls) x4 x5.
  splits; try auto.
  unfold V_OSEventListPtr in *.
  eapply nth_upd_neqrev; try pauto.
  { assert (join (sig qid (absport, remove_tid ct wls)) x4 (set x1 qid (absport, remove_tid ct wls))).
  eapply join_sig_set;eauto. 
  unfold join in H. unfold EcbMap in H. auto. }
  { lets Heg': EcbMod.join_sig_get H7.  (* H6 -> H7 *)
    lets Heg2: EcbMod.join_get_r H2 Heg'.
    unfold get, EcbMap in Heg.
    rewrite Heg in Heg2.
    inverts Heg2.
    eapply RLH_ECBData_P_hold_port; auto. } 
  eapply ECBList_P_high_tcb_block_hold_port_to_rdy; try eauto.
  assert (get x4 qid = None).
  { eapply map_join_get_no_perm1;eauto. eapply map_get_sig. }
  unfold get, EcbMap in H3. auto.
Qed.

Require Import gjb_common.
Require Import sem_corecommu.
Import DeprecatedTactic.
(* Ltac mytac is replaced here *)

Lemma rh_tcblist_ecblist_p_post_exwt_aux_port
: forall (v'8 tid0 : tid) (v'11 : EcbMod.map) 
         (v'7 : TcbMod.map) (v'9 v'10 : EcbMod.map) 
         (eid : tidspec.A)  (x1 : waitset) (v'6 : EcbMod.map) 
         (prio : priority) (msg0 : msg) sus
         (st : taskstatus),
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig eid (absport, x1) v'6 v'10 ->
    In tid0 x1 ->
    TcbMod.get v'7 tid0 = Some (prio, st, msg0, sus) ->
    exists xl, st = wait (os_stat_port eid) xl
.
Proof.
  intros.
  unfolds in H.
  destruct H as (Hexaa & Hex & Hexa & Hexaaa&Hexaaaa).
  lets Hget : EcbMod.join_joinsig_get H0 H1.
  assert (EcbMod.get v'11 eid = Some (absport, x1) /\ In tid0 x1).
  split; auto.
  apply Hexaaaa in H.
  simpljoin.
  setoid_rewrite H3 in H.
  inverts H.
  eexists. eauto.
Qed.

Lemma GetHWait_in_wt: 
  forall t tls wt,
    GetHWait tls wt t ->
    In t wt.
Proof.
  intros.
  unfolds in H. 
  tauto.
Qed.

Lemma statport_and_not_statport_eq_rdy : Int.eq ($ OS_STAT_PORT&ᵢInt.not ($ OS_STAT_PORT)) ($ OS_STAT_RDY) = true.
Proof.
  unfold OS_STAT_PORT, OS_STAT_RDY.
  unfold Int.not.
  unfold Int.xor.
  unfold Z.lxor.
  int auto.
  compute.
  split; intros; tryfalse.
  int auto.
  compute.
  intro; tryfalse.
  compute.
  intro; tryfalse.
  compute.
  split; intros; tryfalse.
Qed.

Lemma tcblist_get_inj:
forall vltcb head p vl vl',
  tcblist_get p head vltcb = Some vl ->
  tcblist_get p head vltcb = Some vl' ->
  vl = vl'.
Proof.
  inductions vltcb; intros.
  simpl in H; tryfalse.
  unfold tcblist_get in H; unfold tcblist_get in H0.
  destruct (beq_val p head) eqn : eq1; destruct (V_OSTCBNext a) eqn : eq2; tryfalse.
  inverts H; inverts H0; auto.
  inverts H; inverts H0; auto.
  fold tcblist_get in H; fold tcblist_get in H0.
  eauto.
Qed.

Lemma ptr_in_tcbdllseg_ptr_in_tcbdllseg1:
  ptr_in_tcbdllseg = new_inv.ptr_in_tcbdllseg1.
Proof.
  reflexivity.
Qed.

Lemma tcblist_get_tcbdllseg1_get_node:
  tcblist_get = new_inv.tcbdllseg1_get_node.
Proof.
  reflexivity.
Qed.

Lemma tcblist_get_TCBNode_P:
forall l tcbls head rtbl t x vl,
  get tcbls t = Some x ->
  tcblist_get (Vptr t) head l = Some vl ->
  TCBList_P head l rtbl tcbls ->
  TCBNode_P vl rtbl x.
Proof.
  induction l; intros.
  + simpl in H0; tryfalse.
  + lets Hnre: H1.
    simpl in H1, H0.
    simpljoin.
    rewrite H2 in H0.
    destruct (os_inv.beq_addrval t x0 ) eqn : eq1.
    ++  inverts H0.
        apply beq_tid_true_eq in eq1; inverts eq1.
        apply tcbjoin_get_a in H3.
        setoid_rewrite H in H3.
        inverts H3. auto.
    ++  assert ((nil++a::nil)++l = a::l) by reflexivity.
        rewrite <- H1 in Hnre.
        eapply TCBList_P_decompose in Hnre; eauto.
        simpljoin.
        simpl app in H7.
        simpl in H6.
        simpljoin.
        inverts H6.
        rewrite H2 in H9.
        inverts H9.
        apply joinsig_emp in H10. subst x4.
        eapply TcbMod.join_sig_get in H8 as ?.
        eapply TcbMod.join_sig_get in H3 as ?.
        rewrite H6 in H9.
        inverts H9.
        lets Hx: TcbMod.map_join_cancel H3 H8.
        subst.
        eapply IHl.
        2: eauto.
        2: eauto.
        destruct (addrval_eq_dec t x6).
        subst. rewrite beq_tid_true in eq1. tryfalse.
        erewrite <-TcbMod.map_join_get_none; eauto.
        unfold TcbMod.get. simpl.
        destruct (tidspec.beq t x6) eqn:E; auto.
        apply tidspec.beq_true_eq in E; tryfalse.
Qed.

Lemma rh_tcblist_ecblist_p_post_exwt_port
: forall (v'8 tid : tid) (v'11 : EcbMod.map) 
         (v'7 : TcbMod.map) (v'9 v'10 : EcbMod.map) 
         (eid : tidspec.A) 
          (x1 : waitset) (v'6 : EcbMod.map) 
         (prio : priority) (msg0 : msg) sus sus'
         (x00 : addrval) xl,
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig eid (absport , x1) v'6 v'10 ->
    In tid x1 ->
    TcbMod.get v'7 tid = Some (prio, wait (os_stat_port eid) xl, msg0, sus) ->
    RH_TCBList_ECBList_P
      (EcbMod.set v'11 eid (absport, remove_tid tid x1))
      (TcbMod.set v'7 tid (prio, rdy, Vptr x00, sus')) v'8
.
Proof.
  intros.
  unfolds.
  splits.
  Focus 5.
  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (Hy&Hx&Hf&Hz&H).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H7.
  subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  assert (EcbMod.get v'11 eid = Some (absport, x1)/\ In tid0 x1 ).
  splits; auto.
  lets Hsa : H H7.
  mytac.
  unfold get in *; simpl in *.

  rewrite H3 in H8.
  inverts H8.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8.
  subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.
  apply  OSQPostPure.in_wtset_rm_notin in H9.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (absport, wls) /\ In tid0 wls ).
  splits; auto.
  lets Hsc : H H10.
  mytac.
  rewrite H3 in H11.
  inverts H11.
  tryfalse.
  rewrite TcbMod.set_sem .
  rewrite tidspec.neq_beq_false; auto.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8.
  subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.
  lets Hbss :OSQPostPure.tidneq_inwt_in  x1 H7.
  destruct Hbss as (Hbss & _).
  lets Hbssc : Hbss H5.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  assert ( EcbMod.get v'11 eid0 = Some (absport, x1) /\ In tid0 x1 ).
  splits; auto.
  apply H in H4.
  mytac.
  do 3 eexists; eauto.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert ( EcbMod.get v'11 eid0 = Some (absport, wls)/\ In tid0 wls ).
  splits; auto.
  apply H in H9.
  mytac.
  do 3 eexists; eauto .
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H5.
  subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  
  unfolds in H.
  destruct H as (H6 & H7 & H100 & H8 &H).
  destruct H.
  apply H9 in H4.
  mytac.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H11.
  subst.
  unfold get in *; simpl in *.
  rewrite H4 in Hget.
  inverts Hget.
  lets Hbss :OSQPostPure.tidneq_inwt_in  x1 H5.
  destruct Hbss as (_ & Hbss).
  lets Hbssc : Hbss H10.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  eexists; splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eexists; splits; eauto.

  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (H&_).
  destruct H.
  destruct H6 as (Hpostq1 & H6 & Hpostq2). (* new add *)
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H7;subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (absmsgq x y pqwaitset, qwaitset) /\ In tid0 qwaitset).
  split;auto.
  apply H in H8.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H9;subst.
  unfold get in *; simpl in *.
  rewrite H3 in H8;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eauto.

  (* new add about postq *)
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H5;subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  destruct H4.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply H in H4.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  unfold get in *; simpl in *.
  rewrite H3 in H4;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eauto.
  (* end of new add *)

  unfolds in H.
  destruct H as (H&_).
  destruct H.
  destruct H5 as (Hpostq1 & H5 & Hpostq2). (* new add *)
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.

  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply H5 in H4.
  mytac.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8;subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in *; simpl in *.
  rewrite H4 in Hget;tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do (* 3 *) 4 eexists;split;eauto.

   (* new add about postq *)
  unfolds in H.
  destruct H as (H&_).
  destruct H.
  destruct H5 as (Hpostq1 & H5 & Hpostq2). (* new add *)
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.

  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply Hpostq2 in H4.
  mytac.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8;subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in *; simpl in *.
  rewrite H4 in Hget;tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do (* 3 *) 4 eexists;split;eauto.
  (* end of new add *)
  
  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (Hh&H&_).
  destruct H.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H7;subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (abssem n, wls) /\ In tid0 wls).
  split;auto.
  apply H in H8.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H9;subst.
  unfold get in *; simpl in *.
  rewrite H3 in H8;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eauto.

  unfolds in H.
  destruct H as (Hh&H&_).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.

  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply H5 in H4.
  mytac.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8;subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in *; simpl in *.
  rewrite H4 in Hget;tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists;split;eauto.
  
  
  Focus 2.
  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (Hh&Hhh&Hx&H&HHH).
  destruct H.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H7;subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (absmutexsem n1 n2, wls) /\ In tid0 wls).
  split;auto.
  apply H in H8.
  destruct H6 as (H6 & HHHHH).
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H11;subst. (* change H9 -> H11 *)
  unfold get in *; simpl in *.
  rewrite H3 in H8;tryfalse.
  do 4 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eauto.

  unfolds in H.
  destruct H as (Hh&Hx&Hhh&H&HH).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.

  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply H5 in H4.
  destruct H5 as (H5 & HHHHH).
  mytac.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H10;subst. (* change H8 -> H10 *)
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in *; simpl in *.
  rewrite H4 in Hget;tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists;split;eauto.

  apply sem_common.Mutex_owner_hold_for_set_tcb.
  eapply sem_common.Mutex_owner_set; eauto.
  intro; mytac.
  unfolds in H.
  mytac.
  unfolds in H6; mytac.
  auto.

  (* new add about RH_TCBList_ECBList_MUTEX_OWNER_P *)
  destruct H as (_ & _ & _ & H &_).
  destruct H as (_ & _ & _ & Hrb).
  eapply sem_common.RH_TCBList_ECBList_MUTEX_OWNER_P_hold_ecb;
  try eapply OSTimeDlyPure.RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
  pure_auto.
  do 2 destruct H.
  inverts H.

  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (Hh&Hhh&H&Hx&Hport).
  destruct H.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H7;subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (absmbox n, wls) /\ In tid0 wls).
  split;auto.
  apply H in H8.
  simpljoin1.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H9;subst.
  unfold get in H8; simpl in H8.
  rewrite H3 in H8;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eauto.

  unfolds in H.
  destruct H as (Hh&Hhh&H&Hx&Hport).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.

  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply H5 in H4.
  simpljoin1.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8;subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in H4; simpl in H4.
  rewrite H4 in Hget;tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists;split;eauto.
Qed.

Lemma TCBNode_P_set_rdy :
  forall next prev p_event st msg msg' sus msg1 dly stat stat' prio prio1 tcbx tcby tcbbitx tcbbity rtbl row y bitx,
    0 <= Int.unsigned prio < 64 ->
    nth_val (Z.to_nat (Int.unsigned (prio>>ᵢ$ 3))) rtbl = Some (Vint32 row) ->
    Int.unsigned row <= 255 ->
    stat' = Int.zero ->
    y = (prio >>ᵢ $ 3) ->
    bitx = ($ 1<<ᵢ(prio&ᵢ$ 7)) ->
    TCBNode_P
      (     next
              :: prev
              :: p_event
              :: msg1
              :: dly
              :: Vint32 stat
              :: prio1
              :: tcbx :: tcby :: tcbbitx :: tcbbity :: nil)
      rtbl (prio, st, msg, sus) ->
    TCBNode_P
      (    next
             :: prev
             :: Vnull
             :: msg'
             :: Vint32 Int.zero
             :: Vint32 stat'
             :: prio1
             :: tcbx :: tcby :: tcbbitx :: tcbbity :: nil)
      (update_nth_val (Z.to_nat (Int.unsigned y)) rtbl
                      (Vint32 (Int.or row bitx)))
      (prio, rdy, msg', false).
Proof.
  introv.
  do 4 intro.
  intros Hy Hbitx.
  rewrite Hy in *; clear Hy.
  rewrite Hbitx in *; clear Hbitx.
  intro.
  unfolds in H3.
  unfolds.
  simpljoin.
  splits; eauto.

  unfolds in H5; simpljoin.
  unfolds.
  do 6 eexists.
  splits; eauto.
  unfolds; simpl; eauto.
  splits; eauto.
  unfold V_OSTCBEventPtr; simpl.
  eexists; splits; eauto.

  unfolds in H4; simpl in H4; inverts H4.
  unfolds in H6; simpljoin.
  rename H6 into Hlh_sus; rename H8 into Hhl_sus;
  rename H9 into H6; rename H10 into H8.
  unfolds; splits.

  clear - H2.
  unfolds; intros.
  unfolds in H.
  simpljoin.
  unfolds in H; simpl in H; inverts H.
  splits; try solve [unfolds; simpl; auto].
  eauto.

  unfolds; intros.
  inverts H9.
  splits; try solve [unfolds; simpl; auto].
  unfolds.
  splits; try solve [unfolds; simpl; auto].
  apply OSQPostPure.prio_in_tbl_orself ; auto.

  (* new add *)
  unfolds.
  split; introv Hwt Hstat; inverts Hstat.
  unfolds.
  split; introv Hstat; inverts Hstat.
  (* end of new add *)

  unfolds in H6; simpljoin.
  rename H10 into Hsemto; rename H11 into H10; rename H12 into Hqto;
  rename H13 into H11; rename H14 into Hmbto;
  rename H15 into H12; rename H16 into Hmsto; rename H17 into H13. (* new add *)
  rename H13 into Hpostq1.
  unfolds.
  splits; try solve [unfolds; intros; inverts H14].
  unfolds; intros.
  unfolds in H13; simpljoin.
  inverts H13.
  lets Hfs :  OSQPostPure.prio_notin_tbl_orself H7 H0.
  tryfalse.
  splits; try solve [unfolds; intros; inverts H14].
  splits; try solve [unfolds; introv Hf Hff; inverts Hff].
  unfolds. 
  splits; try solve [unfolds; introv Hf Hff; inverts Hff].
  1-7: unfolds; introv Hf; inverts Hf.
  splits; try solve [unfolds; introv Hf Hff; inverts Hff].
  all: unfolds; introv Hf; inverts Hf.
Qed.

Lemma tcblist_get_set_node_split :
  forall vltcb head p vl vl',
    tcblist_get p head vltcb = Some vl ->
    exists vltcb1 vltcb2,
      vltcb = vltcb1++vl::vltcb2 /\
      set_node p vl' head vltcb = vltcb1++vl'::vltcb2.
Proof.
  inductions vltcb; intros.
  simpl in H; tryfalse.
  unfold tcblist_get in H; fold tcblist_get in H.
  unfold set_node; fold set_node.
  destruct(beq_val p head) eqn : eq1.
  inverts H.
  do 2 eexists.
  rewrite app_nil_l; eauto.

  destruct(V_OSTCBNext a) eqn : eq2; tryfalse.
  lets Hx : IHvltcb v p vl vl' H. 
  destruct Hx; destruct H0; destruct H0.
  substs.
  exists (a::x) x0.
  rewrite <- app_comm_cons; split; auto.
  unfolds in eq2.
  apply nth_val_nth_val'_some_eq in eq2.
  rewrite eq2.
  rewrite H1.
  rewrite <- app_comm_cons; auto.
Qed.

Lemma tcblist_get_TCBList_P_get_tcbls:
forall vltcb tcbls head rtbl tid vl,
  tcblist_get (Vptr tid) head vltcb = Some vl ->
  TCBList_P head vltcb rtbl tcbls ->
  exists prio st m sus, get tcbls tid = Some (prio, st, m, sus).
Proof.
  inductions vltcb; intros.
  simpl in H; tryfalse.

  unfold tcblist_get in H; fold tcblist_get in H.
  destruct (beq_val (Vptr tid) head) eqn : eq1.
  inverts H.
  unfold TCBList_P in H0; fold TCBList_P in H0.
  simpljoin.
  Require Import new_inv.
  apply beq_val_true_eq in eq1; inverts eq1.
  destruct x2; destruct p.
  destruct p.
  unfolds in H2; simpljoin.
  join auto.

  destruct (V_OSTCBNext a) eqn: eq2; tryfalse.
  unfold TCBList_P in H0; fold TCBList_P in H0; simpljoin.
  rewrite eq2 in H1; inverts H1.
  lets Hx: IHvltcb H H4.
  clear - H2 Hx.
  simpljoin.
  repeat eexists.
  (*   destruct Hx; destruct H. *)
  (*   exists x0 x3. *)
  eapply join_get_r; eauto.
Qed.

Definition rtbl_set_one_bit rtbl rtbl' prio :=
  exists row bitx,
    0 <= Int.unsigned prio < 64 /\
(*    array_type_vallist_match Int8u rtbl /\ length rtbl = ∘ OS_RDY_TBL_SIZE /\
    array_type_vallist_match Int8u rtbl' /\ length rtbl' = ∘ OS_RDY_TBL_SIZE /\ *)
    nth_val' (Z.to_nat (Int.unsigned (prio>>ᵢ$ 3))) rtbl = Vint32 row /\
    nth_val' (Z.to_nat (Int.unsigned (prio&ᵢ$ 7))) OSMapVallist = Vint32 bitx /\
    rtbl' = update_nth_val (Z.to_nat (Int.unsigned(prio>>ᵢ$ 3))) rtbl (Vint32 (Int.or row bitx)).

(* important lemma *)
Lemma set_node_elim : 
  forall tid tcbls vltcb P s head tail t_rdy vl vl' prio st st' m m' sus sus' rtbl rtbl',
    ptr_in_tcbdllseg (Vptr tid) head (set_node (Vptr t_rdy) vl' head vltcb) ->
    tcblist_get (Vptr t_rdy) head vltcb = Some vl ->
    TCBList_P head vltcb rtbl tcbls ->
    get tcbls t_rdy = Some (prio, st, m, sus) -> (*prove this*)
    TCBNode_P vl' rtbl' (prio, st', m', sus') -> (*prove this*)
    rtbl_set_one_bit rtbl rtbl' prio -> (*prove this*)
    R_Prio_No_Dup tcbls ->
    same_prev_next vl vl' ->
    s |= tcbdllseg head Vnull tail Vnull (set_node (Vptr t_rdy) vl' head vltcb) ** P ->
    s |= EX (l1 l2 : list vallist) (tcb_cur:vallist) (tail1 : val) (tcbls1 tcbls2 : TcbMod.map),
         tcbdllseg head Vnull tail1 (Vptr tid) l1 **
         tcbdllseg (Vptr tid) tail1 tail Vnull (tcb_cur::l2) **
         [| (set_node (Vptr t_rdy) vl' head vltcb) = l1 ++ (tcb_cur :: l2)|] **
         [|TcbMod.join tcbls1 tcbls2 (TcbMod.set tcbls t_rdy (prio, st', m', sus'))|] **
         [|TCBList_P head l1 rtbl' tcbls1|] **
         [|TCBList_P (Vptr tid) (tcb_cur :: l2) rtbl' tcbls2|] ** P.
Proof.
  intros.
  assert(TCBList_P head  (set_node (Vptr t_rdy) vl' head vltcb) rtbl' (TcbMod.set tcbls t_rdy (prio, st', m', sus'))).
  lets Hx: tcblist_get_set_node_split H0.
  instantiate (1:=vl') in Hx.
  simpljoin.
  rewrite H9.
  lets Hx: OSQPostPure.TCBList_P_Split H1; simpljoin.
  assert(x1 = (Vptr t_rdy)).
  rewrite H9 in H7.    
  lets Hx: OSQPostPure.tcbdllseg_distinct_tcbdllseg_next_ptr_vnull H7.

  eapply OSQPostPure.distinct_tcbdllseg_next_ptr_preserve with (vl':=vl) in Hx.
  eapply OSQPostPure.distinct_tcbdllseg_next_ptr_vnull_tcblist_get_get_last_tcb_ptr; eauto.
  apply new_inv.same_prev_next_sym; auto.
  substs.

  assert(TcbMod.get x3 t_rdy = Some (prio, st, m, sus)) as tcbls2_get_prio.
  unfold TCBList_P in H12; fold TCBList_P in H12; simpljoin.
  inverts H12.
  clear - H10 H14 H2.
  unfold get in H2; simpl in H2.
  assert(get x3 x1 = Some x6).
  clear -H14.
  eapply join_sig_get; eauto.
  assert (get tcbls x1 = Some x6).
  assert (join x2 x3 tcbls) by eauto.
  clear - H H0.
  jeat.
  unfold get in H0; simpl in H0.
  rewrite H2 in H0; inverts H0.
  unfold get in H; simpl in H; auto.
  
  assert(TCBList_P head x rtbl' x2).
  clear -H4 H5 H10 H11 tcbls2_get_prio.
  unfolds in H4; simpljoin.
  assert(x1 = ($ 1<<ᵢ(prio&ᵢ$ 7))).
  eapply math_mapval_core_prop; auto.
  clear - H H3.
  mauto.
  substs.
  eapply OSQPostPure.TCBList_P_rtbl_add_simpl_version; eauto.
  eapply nth_val'_imp_nth_val_int; auto.
  clear - H5 tcbls2_get_prio H10.
  intros.
  unfolds in H5.
  assert(tid <> t_rdy).
  intro; substs.
  pose proof H10 t_rdy.
  destruct(TcbMod.get x2 t_rdy);
    destruct(TcbMod.get x3 t_rdy);
    destruct(TcbMod.get tcbls t_rdy); tryfalse.
  assert(TcbMod.get tcbls t_rdy = Some (prio, st, m, sus)).
  eapply TcbMod.join_get_r; eauto.
  assert(TcbMod.get tcbls tid = Some(p, s, m0, sus0)).
  eapply TcbMod.join_get_l; eauto.
  eapply H5; eauto.

  assert(TCBList_P (Vptr t_rdy) (vl'::x0) rtbl' (set x3 t_rdy (prio, st', m', sus'))).
  unfold TCBList_P in *; fold TCBList_P in *.
  simpljoin.
  inverts H12.
  unfolds in H6.
  rewrite H14 in H6.
  destruct (V_OSTCBNext vl'); tryfalse.
  do 4 eexists.
  splits; eauto.
  instantiate (1:=x5).
  clear - H15.
  eapply joinsig_set; eauto.

  destruct H6; substs.
  clear - H10 H15 H17 tcbls2_get_prio H4 H5.
  unfolds in H4; simpljoin.

  assert(x4 = ($ 1<<ᵢ(prio&ᵢ$ 7))).
  eapply math_mapval_core_prop; auto.
  clear - H H3.
  mauto.
  substs.
  eapply OSQPostPure.TCBList_P_rtbl_add_simpl_version; eauto.
  eapply nth_val'_imp_nth_val_int; auto.
  assert(get x3 x1 = Some x6).
  clear - H15.
  join auto.
  unfold get in H2; simpl in H2.
  rewrite tcbls2_get_prio in H2; inverts H2.
  clear - H5 tcbls2_get_prio H15 H10.
  intros.
  unfolds in H5.
  assert(tid <> x1).
  intro; substs.
  pose proof H15 x1.
  rewrite TcbMod.get_sig_some in H0.
  rewrite H in H0; tryfalse.
  assert(TcbMod.get tcbls x1 = Some (prio, st, m, sus)).
  eapply TcbMod.join_get_r; eauto.
  assert(TcbMod.get tcbls tid = Some(p, s, m0, sus0)).
  eapply TcbMod.join_get_r; eauto.
  clear - H15 H.
  unfold TcbJoin in H15.
  unfold join, sig in H15; simpl in H15.
  eapply TcbMod.join_get_r; eauto.
  eapply H5; eauto.
  
  assert(join x2 (set x3 t_rdy (prio, st', m', sus')) (set tcbls t_rdy (prio, st', m', sus'))).
  clear - H10 tcbls2_get_prio.
  eapply join_set_r; eauto.
  unfold indom.
  eauto.
  
  eapply OSQPostPure.TCBList_P_Combine; eauto.
  eapply new_inv.tcbdllseg_split' in H7; eauto.
  do 5 destruct H7.
  destruct x0.
  unfold tcbdllseg in H7.
  simpl dllseg in H7.
  sep split in H7; tryfalse.
  sep auto; eauto.
Qed.

Lemma port_compose_EcbList_P:
  forall p qid a b c tcbls i n x2 x3 vn msgq mq ectrl1 msgqls1 mqls1 ectrl2 msgqls2 mqls2 mqls' mqls pegrp petbl_addr,
    R_ECB_ETbl_P qid ((a,b),c) tcbls ->
    R_ECB_PETbl_P qid ((a,b),c) tcbls ->
    a = (V$OS_EVENT_TYPE_PORT :: Vint32 i :: Vint32 n :: x2 :: x3 :: vn :: Vint32 pegrp :: petbl_addr :: nil) ->
    RLH_ECBData_P msgq mq ->
    ECBList_P p (Vptr qid) ectrl1 msgqls1 mqls1 tcbls ->
    ECBList_P vn Vnull ectrl2 msgqls2 mqls2 tcbls ->
    EcbMod.joinsig qid mq mqls2 mqls' ->
    EcbMod.join mqls1 mqls' mqls ->
    ECBList_P p Vnull (ectrl1 ++ (((a,b),c)::nil) ++ ectrl2) 
              (msgqls1 ++ (msgq::nil) ++ msgqls2)
              mqls tcbls.
  intros.
  subst.
  eapply ecblist_p_compose; eauto.
  simpl.
  eexists; splits; eauto.
  do 3 eexists; splits; eauto.
  unfolds; simpl; auto.
Qed.

Lemma ECBList_P_Set_Rdy_hold_port
: forall (a : list EventCtr) (tcbls : TcbMod.map) 
         (tid : tidspec.A) (prio : priority) (msg0 msg' : msg) sus sus'
         (x y : val) (b : list EventData) (c : EcbMod.map) 
         (eid : ecbid) nl,
    TcbMod.get tcbls tid = Some (prio, wait (os_stat_port eid) nl, msg0, sus) ->
    EcbMod.get c eid = None ->
    ECBList_P x y a b c tcbls ->
    ECBList_P x y a b c (TcbMod.set tcbls tid (prio, rdy, msg', sus')).
Proof.
  inductions a; intros.
  simpl in *; auto.
  simpl in H1.
  mytac.
  rename H3 into Hpetbl; rename H4 into H3. (* new add *)
  destruct b; tryfalse.
  destruct a.
  destruct p. (* new add *)
  mytac.
  simpl.
  eexists.
  splits; eauto.
  unfolds.
  unfolds in H2.

  splits.
  
  destructs H2.
  unfolds in H2.
  mytac.
  unfolds.
  splits; unfolds;intros.

  apply H2 in H12.
  apply H12 in H13.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H14.
  subst tid.
  unfold get in *; simpl in *.
  rewrite H13 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  do 4 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  apply H8 in H12.
  apply H12 in H13.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H14.
  subst tid.
  unfold get in *; simpl in *.
  rewrite H13 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  do 4 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  apply H9 in H12.
  apply H12 in H13.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H14.
  subst tid.
  unfold get in *; simpl in *.
  rewrite H13 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  do 4 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  apply H10 in H12.
  apply H12 in H13.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H14.
  subst tid.
  unfold get in *; simpl in *.
  rewrite H13 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  do 4 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  apply H11 in H12.
  apply H12 in H13.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H14.
  subst tid.
  unfold get in *; simpl in *.
  rewrite H13 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  do 4 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  unfolds.
  destructs H2;unfolds in H6;destructs H6.
  splits;intros prio' mg ng x3 sus0 Hti;
  assert (tid = x3
          \/ tid <> x3) by tauto.
  destruct H12.
  subst tid.
  unfold get in *; simpl in *.
  unfold get in *; simpl in *.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H6; eauto.

  destruct H12.
  subst tid.
  unfold get in *; simpl in *.
  unfold get in *; simpl in *.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H8; eauto.
  
  destruct H12.
  subst tid.
  unfold get in *; simpl in *.
  unfold get in *; simpl in *.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H9; eauto.

  destruct H12.
  subst tid.
  unfold get in *; simpl in *.
  unfold get in *; simpl in *.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H10; eauto.

  destruct H12.
  subst tid.
  unfold get in *; simpl in *.
  unfold get in *; simpl in *.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.eq_beq_true in Hti; auto.
  inverts Hti.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H11; eauto.

  mytac;auto.
  
  eapply R_ECB_PETbl_P_hold_for_set_rdy; eauto.
  introv Hf. destruct Hf as (qd & qwt & Hf). inverts Hf.

  do 3 eexists; splits; eauto.
  eapply IHa; eauto.
  eapply ecbmod_joinsig_get_none; eauto.
Qed.

Lemma ecblist_p_post_exwt_hold_port_lemma
: forall (v'36 : vallist) (v'12 : int32) (v'13 : vallist)
         (v'38 v'69 v'39 : int32) (v'58 : block) (v'40 : int32)
         v'32 (v'15 : int32) (v'24 : val)
         (v'35 : val) (x1 : waitset) 
         (v'0 : val) (v'1 : list EventCtr) (v'5 : list EventData)
         (v'6 : EcbMod.map) (v'7 : TcbMod.map) 
         (v'11 : EcbMod.map) (v'31 : list EventData) 
         (v'30 : list EventCtr) (v'29 : val) (v'10 v'9 : EcbMod.map)
         (prio : priority) (v'62 : TcbMod.map) (st : taskstatus)
         (msg0 msg1: msg) sus (y : int32) (vhold : addrval) petbl pegrp petbl_addr,
    Int.unsigned v'15 <= 65535 ->
    True ->
    v'12 <> Int.zero ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 =
    Vptr (v'58, Int.zero) ->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    R_ECB_ETbl_P v'32
                 (V$OS_EVENT_TYPE_PORT
                   :: Vint32 v'12
                   :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: Vint32 pegrp :: petbl_addr :: nil,
                  v'13,petbl) v'7 ->
    RLH_ECBData_P
      (DPort) (absport, x1) ->
    ECBList_P v'0 Vnull v'1 v'5 v'6 v'7 ->
    ECBList_P v'29 (Vptr v'32) v'30 v'31 v'9 v'7 ->
    EcbMod.joinsig v'32 (absport, x1) v'6 v'10 ->
    EcbMod.join v'9 v'10 v'11 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg0, sus) v'62 v'7 ->
    R_PrioTbl_P v'36 v'7 vhold ->
    x1 <> nil ->
    R_ECB_PETbl_P v'32
                 (V$OS_EVENT_TYPE_PORT
                   :: Vint32 v'12
                   :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: Vint32 pegrp :: petbl_addr :: nil,
                  v'13,petbl) v'7 -> (* new add *)
    ECBList_P v'29 Vnull
              (v'30 ++
                    ((V$OS_EVENT_TYPE_PORT
                       :: Vint32 y
                       :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: Vint32 pegrp :: petbl_addr :: nil,
                      update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                                     (Vint32 (v'69&ᵢInt.not v'40)),petbl) :: nil) ++ v'1)
              (v'31 ++
                    (DPort ::nil)
                    ++ v'5)
              (EcbMod.set v'11 v'32
                          (absport, remove_tid (v'58, Int.zero) x1))
              (TcbMod.set v'7 (v'58, Int.zero) (prio, rdy, msg1, sus))
.
Proof.
  introv Hcnt.
  intros.
  rename H23 into Hpetbl. (* new add *)
  unfolds in H21.
  destruct H21 as (Ha1 & Ha2 & Ha3).
  assert ( 0 <= Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < 64).
  clear -H5 H9.
  mauto.
  unfold nat_of_Z in Ha1.
  eapply nth_val'_imp_nth_val_vptr in H10.
  lets Hps : Ha1 H21 H10.
  apply tcbjoin_get_a in H20.
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  apply Ha2 in H20.
  destruct H20;auto.
  destruct Hps as (sts & mg & sus0 & Hget);auto.
  unfold get in *; simpl in *.
  rewrite Hget in H20.
  inverts H20.
  remember ((v'38<<ᵢ$ 3)) as px.
  remember (v'39) as py.
  clear Heqpy.
  remember (px+ᵢpy) as prio.
  remember ( (v'58, Int.zero)) as tid.
  unfolds in H14.
  destruct H14 as (Ha & Hb & Hc).
  destruct Ha as (Ha''&Ha''''&Ha'&Ha'''&Ha).
  destruct Hb as (Hb''&Hb''''&Hb'&Hb'''&Hb).
  lets Hz : math_unmap_get_y H1 H4.
  lets Heq1 :  math_mapval_core_prop H11; eauto.
  lia.
  subst v'40.
  assert (v'38 = Int.shru prio ($3)).
  subst.
  clear -Hz H9.
  mauto.
  assert (py = prio &ᵢ $ 7).
  subst prio. 
  rewrite Heqpx.
  clear -Hz H9.
  mauto.
  rewrite H14 in H6.
  assert (PrioWaitInQ (Int.unsigned prio) v'13) as Hcp.
  unfolds.
  do 3 eexists; splits; eauto.
  rewrite Int.repr_unsigned.
  eapply nth_val'_imp_nth_val_int; eauto.
  rewrite Int.repr_unsigned.
  rewrite <- H20.
  unfold Int.one.
  eapply math_8_255_eq; eauto.
  
  unfold Int.zero in H0.
  rewrite <-H14 in *.
  lets Hneq :  OSQPostPure.rl_tbl_grp_neq_zero H1 H0  H4 H6 H13.
  lia.
  auto.
  lets Hecp : Ha Hcp.
  unfold V_OSEventType in Hecp.
  simpl nth_val in Hecp.
  assert (Some (V$OS_EVENT_TYPE_PORT) = Some (V$OS_EVENT_TYPE_PORT)) by auto.
  apply Hecp in H23.
  clear Hecp.
  rename H23 into Hecp.
  destruct Hecp as (ct & nl & mg & sus0 & Hcg).
  assert (ct = tid) as Hed.
  assert (ct = tid \/ ct <> tid)  by tauto.
  destruct H23; auto.
  lets Heqs : Ha3 H23 Hcg Hget.
  rewrite Int.repr_unsigned in Heqs.
  tryfalse.
  subst ct.
  unfold get in Hcg; simpl in Hcg.
  rewrite Hget in Hcg.
  inversion Hcg.
  subst mg st sus0.
  clear Hcg.
  
  lets Hsds : ecb_set_join_join  (absport, remove_tid tid x1)  H18  H19.
  destruct Hsds as ( vv & Hsj1 & Hsj2).

  eapply port_compose_EcbList_P.
  instantiate (1:= v'32).
  unfolds.
  splits.
  unfolds.
  splits;unfolds.
  Focus 5.
  
  introv Hprs Hxx.
  clear Hxx.
  apply OSQPostPure.prio_wt_inq_convert in Hprs.
  destruct Hprs as (Hprs1 & Hprs2).
  rewrite H14 in Hprs1.
  rewrite H20 in Hprs1.
  lets Hrs : OSQPostPure.prio_wt_inq_tid_neq  H6 H21 .
  destruct Hrs as (Hrs & _).
  apply Hrs in Hprs1.
  destruct Hprs1 as (Hpq & Hneq).
  unfolds in Ha.
  lets Hxs : Ha Hpq.
  rewrite Int.repr_unsigned in Hxs.
  destruct Hxs as (tid' & nn & mm & sus0 & Htg).
  unfolds;simpl;auto.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H23.
  subst tid'.
  unfold get in Htg; simpl in Htg.
  rewrite Hget in Htg.
  inversion Htg.
  tryfalse.
  exists tid' nn mm.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  intros.
  unfolds in H25;simpl in H25;tryfalse.
  intros.
  unfolds in H25;simpl in H25;tryfalse.
  intros.
  unfolds in H25;simpl in H25;tryfalse.
  intros.
  unfolds in H25;simpl in H25;tryfalse.
  
  2:eauto.

  unfolds.
  splits;
    intros prio' mm nn tid'.
  Focus 5.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H23.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb.
  lets Hga : Hb Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H23 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.

  lets Hrs : OSQPostPure.prio_wt_inq_tid_neq  H6 H21 .
  destruct Hrs as (_ & Hrs).
  apply Hrs in H25.
  rewrite H20.
  rewrite H14.
  auto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H23.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb''.
  lets Hga : Hb'' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H23 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H23.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb''''.
  lets Hga : Hb'''' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H23 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H23.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'.
  lets Hga : Hb' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H23 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H23.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in Hb'''.
  lets Hga : Hb''' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H23 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  simpl fst in Hc;simpl;auto.
  (* new add about petbl *)
  eapply R_ECB_PETbl_P_high_tcb_block_hold'; eauto.
  unfold V_OSEventType; simpl. pure_auto.
  introv Hf. destruct Hf as (qd & wt & Hf). inverts Hf.
  unfold V_OSEventType; simpl. pure_auto.
  (* end of new add *)

  5:eauto.
  4:eauto.
  unfolds.
  auto.
  
  eapply ECBList_P_Set_Rdy_hold_port;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply joinsig_join_getnone; eauto.
  eapply ECBList_P_Set_Rdy_hold_port;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply  joinsig_get_none; eauto.
Qed.


Lemma ecblist_p_post_exwt_hold_port: forall (v'36 : vallist) (v'12 : int32) (v'13 : vallist)
         (v'38 v'69 v'39 : int32) (v'58 : block) (v'40 : int32)
        (x1 : waitset) 
         v'0 v'32 (v'1 : list EventCtr) (v'5 : list EventData)
         (v'6 : EcbMod.map) (v'7 : TcbMod.map) 
         (v'11 : EcbMod.map) (v'31 : list EventData) 
         (v'30 : list EventCtr) (v'29 : val) (v'10 v'9 : EcbMod.map)
         (prio : priority) (v'62 : TcbMod.map) (st : taskstatus)
         (msg0 msg1: msg) sus (y : int32) (vhold : addrval) petbl  et et',
    struct_type_vallist_match OS_EVENT et ->
    et' = update_nth_val (1)%nat et (Vint32 y) ->
    V_OSEventType et = Some (V$OS_EVENT_TYPE_PORT) ->
    V_OSEventGrp et = Some (Vint32 v'12) ->
    V_OSEventListPtr et = Some v'0 ->
    v'12 <> Int.zero ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 =
    Vptr (v'58, Int.zero) ->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    R_ECB_ETbl_P v'32
                 (et,v'13,petbl) v'7 ->
    RLH_ECBData_P
      (DPort) (absport, x1) ->
    ECBList_P v'0 Vnull v'1 v'5 v'6 v'7 ->
    ECBList_P v'29 (Vptr v'32) v'30 v'31 v'9 v'7 ->
    EcbMod.joinsig v'32 (absport, x1) v'6 v'10 ->
    EcbMod.join v'9 v'10 v'11 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg0, sus) v'62 v'7 ->
    R_PrioTbl_P v'36 v'7 vhold ->
    x1 <> nil ->
    R_ECB_PETbl_P v'32
                 (et,
                  v'13,petbl) v'7 -> (* new add *)
    ECBList_P v'29 Vnull
              (v'30 ++
                    ((et',
                      update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                                     (Vint32 (v'69&ᵢInt.not v'40)),petbl) :: nil) ++ v'1)
              (v'31 ++
                    (DPort ::nil)
                    ++ v'5)
              (EcbMod.set v'11 v'32
                          (absport, remove_tid (v'58, Int.zero) x1))
              (TcbMod.set v'7 (v'58, Int.zero) (prio, rdy, msg1, sus))
.
Proof.
  intros. struct_type_vallist_match_elim.
  simpl update_nth_val.
  invertsr H2.
  invertsr H3.
  invertsr H1.
  eapply ecblist_p_post_exwt_hold_port_lemma; eauto.
Qed.

Lemma pos_to_nat_range_0_7:
  forall z, 0<=z -> z<=7 -> (0<=Z.to_nat z<=7)%nat.
Proof.
  intros.
  split.
  mauto.
  assert (Z.to_nat 7 = 7)%nat.
  clear -z.
  mauto.
  rewrite <- H1.
  eapply Z2Nat.inj_le; lia.
Qed.

Lemma osmapvallist_prop:forall x, (Int.unsigned x <=7) -> exists i, nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 i /\ Int.unsigned i <= 128.
Proof.
  intros.
  lets Hx:Int.unsigned_range x.
  destruct Hx.
  clear H1.
  remember (Int.unsigned x) as z.
  clear Heqz.
  lets Hx: pos_to_nat_range_0_7 H0 H.
  destruct Hx.
  clear H H0.
  remember (Z.to_nat z) as n.
  clear Heqn.
  do 8 (
       destruct n;
       [ 
         simpl;
         eexists;split;eauto;
         rewrite Int.unsigned_repr;
         try solve [lia];
         rewrite max_unsigned_val;lia | ]).
  lia.
Qed.

Lemma set_node_eq_dllflag :
  forall tcbl ptr  v'82 v'83 v'84 v'85 v'86 v'87 v'88 v'89 v'90 v'91 v'92 v'83' v'84' v'85' v'86' v'87' v'88' v'89' v'90' v'91' head,
    tcblist_get ptr head tcbl = 
    Some
      (v'82 :: v'83 :: v'84 :: v'85 :: v'86 :: v'87 :: v'88
            :: v'89 :: v'90 :: v'91 :: v'92 :: nil) ->
    eq_dllflag tcbl (set_node ptr (v'82 :: v'83' :: v'84' :: v'85' :: v'86' :: v'87' :: v'88'
                                        :: v'89' :: v'90' :: v'91' :: v'92 :: nil) head tcbl).
Proof.
  induction tcbl.
  intros.
  simpl.
  auto.
  intros.
  simpl.
  remember (beq_val ptr head).
  destruct b.
  unfold tcblist_get in H.
  rewrite <- Heqb in H.
  simpl in H.
  inverts H.
  splits; auto.
  Focus 2.
  splits; auto.
  eapply IHtcbl.
  unfolds in H.
  rewrite <- Heqb in H.
  destruct a.
  simpl in H.
  inversion H.
  simpl in H.
  fold tcblist_get in H.
  exact H.

  apply eq_dllflag_refl.
Qed.
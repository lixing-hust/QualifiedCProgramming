Require Import ucos_include.
Require Import os_ucos_h.
Require Import sep_lemmas_ext.
Require Import sem_common.
Require Import new_inv.
Require Import linv_solver.
Require Import inline_definitions.
Require Import inline_bittblfunctions.
Require Import inline_tactics.
Require Import symbolic_lemmas.
Require Import Lia.
Require Import protect.
Require Import OSTimeDlyPure.
Require Import abs_op.

Require Export include_frm.

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.

(* Definition OSTaskSuspend_impl := 
  Int8u ·OSTaskSuspend·(⌞prio @ Int8u⌟)··{
    ⌞
    pevent @ OS_EVENT∗;
    ptcb @ OS_TCB∗;
    x @ OS_TCB∗
    ⌟;

    If (prio′ ==ₑ ′OS_IDLE_PRIO) {
      RETURN ′OS_TASK_SUSPEND_IDLE
    };ₛ

    If (prio′ ≥ ′OS_LOWEST_PRIO){
      RETURN ′OS_PRIO_INVALID
    };ₛ

    ENTER_CRITICAL;ₛ

    ptcb′ =ₑ OSTCBPrioTbl′[prio′];ₛ
    If (ptcb′ ==ₑ NULL){
      EXIT_CRITICAL;ₛ
      RETURN ′OS_TASK_SUSPEND_PRIO
    };ₛ

    inline_call inline_bittbl_clearbit ((OSRdyGrp′):: (OSRdyTbl′)::(ptcb′→OSTCBBitX)::(ptcb′→OSTCBBitY)::(ptcb′→OSTCBY)::nil);ₛ
    ptcb′→OSTCBStat =ₑ ptcb′→OSTCBStat |ₑ ′OS_STAT_SUSPEND;ₛ
    EXIT_CRITICAL;ₛ

    OS_Sched(­)
    RETURN ′OS_NO_ERR
}·.*)

Definition OS_TASK_SUSPEND_IDLE := 91%Z.

Lemma absimp_tasksus_prio_idle:
  forall P v1 sch,
    can_change_aop P ->
    Int.eq (Int.repr OS_IDLE_PRIO) v1 = true ->
    absinfer sch ( <|| tasksuspendcode ((Vint32 v1) :: nil) ||> ** P)
             ( <|| END (Some (Vint32 (Int.repr OS_TASK_SUSPEND_IDLE))) ||> ** P).
Proof.

  infer_solver 0%nat.
  
Admitted.

Lemma absimp_tasksus_prio_invalid:
  forall P v1 sch,
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v1 = true ->
    absinfer sch ( <|| tasksuspendcode ((Vint32 v1) :: nil) ||> ** P)
             ( <|| END (Some (Vint32 (Int.repr OS_PRIO_INVALID))) ||> ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma absimp_tasksus_no_such_tcb:
  forall P v1 sch (ecbls : EcbMod.map) (tcbls : TcbMod.map),
    can_change_aop P ->
    (~exists tid st msg sus, TcbMod.get tcbls tid = Some (v1, st, msg, sus)) ->
    absinfer sch ( <|| tasksuspendcode ((Vint32 v1) :: nil) ||> **
                       HECBList ecbls **
                       HTCBList tcbls ** P)
             ( <|| END (Some (Vint32 (Int.repr OS_TASK_SUSPEND_PRIO))) ||> **
                       HECBList ecbls **
                       HTCBList tcbls ** P).
Proof.
  infer_solver 2%nat.
Qed.

Lemma abs_imp_tasksus_succ:
  forall P v1 sch (ecbls : EcbMod.map) (tcbls : TcbMod.map) tid st msg sus,
    can_change_aop P ->
    TcbMod.get tcbls tid = Some (v1, st, msg, sus) ->
    absinfer sch
      ( <|| tasksuspendcode ((Vint32 v1) :: nil) ||> **
            HECBList ecbls ** HTCBList tcbls ** P )
      ( <|| isched;; END (Some (Vint32 (Int.repr OS_NO_ERR))) ||> **
            HECBList ecbls ** HTCBList (TcbMod.set tcbls tid (v1, st, msg, true)) ** P).
Proof.
  infer_solver 3%nat.
Qed.

Lemma OSTCBflag_des:
forall v'11,
  struct_type_vallist_match OS_TCB_flag v'11 ->
  exists a1 a2 a3 a4 a5 a6 a7 a8 a9 a10,
    exists a11,
    v'11 = (a1::a2::a3::a4::a5::a6::Vint32 a7::a8::a9::a10::a11::nil).
Proof.
  intros.
  destruct v'11; simpl in H; tryfalse.
  destruct v'11; simpl in H; simpljoin; tryfalse.
  destruct v'11; simpl in H; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v5; tryfalse.
  repeat tri_exists_and_solver1.
Qed.

Lemma nv'2nv:
  forall vl n x,
    nth_val' n vl = x ->
    x <> Vundef ->
    nth_val n vl = Some x.
Proof.
  induction vl.
  induction n.
  intros.
  simpl in H.
  tryfalse.
  intros.
  simpl in H.
  tryfalse.

  induction n.
  intros.
  simpl in H.
  simpl.
  inverts H.
  auto.
  intros.
  simpl.
  simpl in H.
  apply IHvl.
  auto.
  auto.
Qed.

Lemma ECBList_P_preserve:
  forall ls x mqls ecbls tcbls prio b st0 m0,
    ECBList_P x Vnull ls mqls ecbls tcbls ->
    (exists sus0, TcbMod.get tcbls (b, Int.zero) = Some (prio, st0, m0, sus0)) -> 
    ECBList_P x Vnull ls mqls ecbls
      (TcbMod.set tcbls (b, Int.zero) (prio, st0, m0, true)).
Proof.
  induction ls.
  * intros. unfolds. unfolds in H. auto.
  * intros. unfold1 ECBList_P. unfold1 ECBList_P in H.
    simpljoin. exists x1. split. auto. split.
    unfolds R_ECB_ETbl_P. destruct H1. destruct H1.
    split. unfold RLH_ECB_ETbl_P in *.
    destruct H as [Q_P [SEM_P [MBOX_P MUTEX_P]]].

    split. {
      unfold RLH_ECB_ETbl_Q_P in *.
      destruct a. destruct p. intros. lets temp: Q_P prio0 H H5.
      simpljoin.
      eexists x.
      unfold join,get,sig in *; simpl in *.
      assert (x = (b, Int.zero) \/ x <> (b, Int.zero)) as choice by tauto.
      destruct choice.
      + inverts H7.
        rewrite H0 in H6. inverts H6.
        rewrite TcbMod.map_get_set. eauto.
      + simpl. rewrite TcbMod.map_get_set'. eauto. auto.
    }
    
    split. {
      unfold RLH_ECB_ETbl_SEM_P in *.
      destruct a. destruct p. intros. lets temp: SEM_P prio0 H H5.
      simpljoin.
      eexists x.
      unfold join,get,sig in *; simpl in *.
      assert (x = (b, Int.zero) \/ x <> (b, Int.zero)) as choice by tauto.
      destruct choice.
      + inverts H7.
        rewrite H0 in H6. inverts H6.
        rewrite TcbMod.map_get_set. eauto.
      + simpl. rewrite TcbMod.map_get_set'. eauto. auto.
    }

    split. {
      unfold RLH_ECB_ETbl_MBOX_P in *.
      destruct a. destruct p. intros. lets temp: MBOX_P prio0 H H5.
      simpljoin.
      eexists x.
      unfold join,get,sig in *; simpl in *.
      assert (x = (b, Int.zero) \/ x <> (b, Int.zero)) as choice by tauto.
      destruct choice.
      + inverts H7.
        rewrite H0 in H6. inverts H6.
        rewrite TcbMod.map_get_set. eauto.
      + simpl. rewrite TcbMod.map_get_set'. eauto. auto.
    }

    {
      unfold RLH_ECB_ETbl_MUTEX_P.
      destruct a. destruct p. intros. lets temp: MUTEX_P prio0 H H5.
      simpljoin.
      eexists x.
      unfold join,get,sig in *; simpl in *.
      assert (x = (b, Int.zero) \/ x <> (b, Int.zero)) as choice by tauto.
      destruct choice.
      + inverts H7.
        rewrite H0 in H6. inverts H6.
        rewrite TcbMod.map_get_set. eauto.
      + simpl. rewrite TcbMod.map_get_set'. eauto. auto.
    }

    unfold RHL_ECB_ETbl_P in *.
    split. 2: auto.
    destruct H1 as [Q_P [SEM_P [MBOX_P MUTEX_P]]].

    split. {
      unfold RHL_ECB_ETbl_Q_P in *.
      destruct a. destruct p. intros.
      assert (tid = (b, Int.zero) \/ tid <> (b, Int.zero)) as choice by tauto.
      unfold join,get,sig in *; simpl in *.
      destruct choice.
      + eapply Q_P. inverts H5.
        rewrite TcbMod.map_get_set in H1.
        inverts H1. eauto.
      + eapply Q_P. rewrite TcbMod.map_get_set' in H1.
        eauto. auto.
    }

    split. {
      unfold RHL_ECB_ETbl_SEM_P in *.
      destruct a. destruct p. intros.
      assert (tid = (b, Int.zero) \/ tid <> (b, Int.zero)) as choice by tauto.
      unfold join,get,sig in *; simpl in *.
      destruct choice.
      + eapply SEM_P. inverts H5.
        rewrite TcbMod.map_get_set in H1.
        inverts H1. eauto.
      + eapply SEM_P. rewrite TcbMod.map_get_set' in H1.
        eauto. auto.
    }

    split. {
      unfold RHL_ECB_ETbl_MBOX_P in *.
      destruct a. destruct p. intros.
      assert (tid = (b, Int.zero) \/ tid <> (b, Int.zero)) as choice by tauto.
      unfold join,get,sig in *; simpl in *.
      destruct choice.
      + eapply MBOX_P. inverts H5.
        rewrite TcbMod.map_get_set in H1.
        inverts H1. eauto.
      + eapply MBOX_P. rewrite TcbMod.map_get_set' in H1.
        eauto. auto.
    }

    {
      unfold RHL_ECB_ETbl_MUTEX_P in *.
      destruct a. destruct p. intros.
      assert (tid = (b, Int.zero) \/ tid <> (b, Int.zero)) as choice by tauto.
      unfold join,get,sig in *; simpl in *.
      destruct choice.
      + eapply MUTEX_P. inverts H5.
        rewrite TcbMod.map_get_set in H1.
        inverts H1. eauto.
      + eapply MUTEX_P. rewrite TcbMod.map_get_set' in H1.
        eauto. auto.
    }

    split. {
      destruct H2 as (Hetbl & Hpetbl).
      unfold R_ECB_PETbl_P; unfold RLH_ECB_PETbl_Q_P; unfold RHL_ECB_PETbl_Q_P; destruct a; destruct p.
      split.
      {
        intros.
        unfold RLH_ECB_PETbl_Q_P in Hetbl.
        unfold RHL_ECB_PETbl_Q_P in Hpetbl.
        pose proof Hetbl prio0.
        lets Hget: H4 H H2.
        destruct Hget as (tid & n & m & sus & Hget).
        eexists.
        assert (tid = (b, Int.zero) \/ tid <> (b, Int.zero)) as choice by tauto.
        unfold join,get,sig in *; simpl in *.
        destruct choice.
        + inverts H5.
          rewrite H0 in Hget. inverts Hget.
          rewrite TcbMod.map_get_set.
          eauto.
        + rewrite TcbMod.map_get_set'. eauto. auto.
      }
      {
        intros.
        assert (tid = (b, Int.zero) \/ tid <> (b, Int.zero)) as choice by tauto.
        destruct choice.
        + eapply Hpetbl.
          inverts H2.
          rewrite TcbMod.map_get_set in H.
          inverts H.
          eauto.
        + eapply Hpetbl. rewrite TcbMod.map_get_set' in H.
          eauto. auto.
      }
    }

    destruct mqls. tryfalse.
    destruct a. destruct p. destruct H3 as [x [mqls' [v' [P1 [P2 [P3]]]]]].
    eexists x. eexists mqls'. eexists v'.
    repeat split; auto.
    apply IHls.
    auto. eauto.
Qed.

Lemma eq_dllflag_set:
  forall l1 l2 x x',
    V_OSTCBNext x = V_OSTCBNext x' ->
    V_OSTCBflag x = V_OSTCBflag x' ->
    eq_dllflag (l1 ++ x :: l2) (l1 ++ x' :: l2).
Proof.
  intros. induction l1.
  simpl. splits; auto. apply eq_dllflag_refl.
  simpl. splits; auto.
Qed.

Lemma prio_rtbl_dec':
forall x rtbl,
  0 <= Int.unsigned x < 64 ->
  array_type_vallist_match Int8u rtbl ->
  length rtbl = ∘OS_RDY_TBL_SIZE ->
  prio_in_tbl x rtbl -> prio_not_in_tbl x rtbl -> False.
Proof.
  intros.
  unfolds in H2. unfolds in H3.
  assert (exists z, nth_val ∘ (Int.unsigned (x >>ᵢ $ 3)) rtbl =
  Some (Vint32 z)). {
    apply array_type_match_get_value.
    mauto. auto. auto.
  }
  destruct H4.
  assert (x0 &ᵢ($ 1<<ᵢ (x&ᵢ$ 7)) = $ 1<<ᵢ (x&ᵢ$ 7)). {
    eapply H2; auto.
  }
  assert (x0&ᵢ($ 1<<ᵢ(x&ᵢ$ 7)) = $0). {
    eapply H3; auto.
  }
  rewrite H5 in H6.
  assert ($ 1<<ᵢ(x&ᵢ$ 7) <> $ 0). {
    apply math_prop_neq_zero2; auto.
  }
  auto.
Qed.

Lemma Some_Vint32_invert:
  forall a b, Some (Vint32 a) = Some (Vint32 b) -> a = b.
Proof.
  intros. invert H. auto.
Qed.

Lemma RL_TCBblk_P_suspend:
forall next prev eptr msg dly stat prio x y bitx bity,
  RL_TCBblk_P
  (next :: prev :: eptr :: msg :: dly :: Vint32 stat
  :: prio :: x :: y :: bitx :: bity :: nil) ->
  RL_TCBblk_P
  (next :: prev :: eptr :: msg :: dly
  :: Vint32 (Int.or stat ($ OS_STAT_SUSPEND))
  :: prio :: x :: y :: bitx :: bity :: nil).
Proof.
  intros. unfold RL_TCBblk_P in *.
  simpljoin. inverts H; inverts H0; inverts H1; inverts H2.
  inverts H3; inverts H4; inverts H11.
  do 6 eexists. splits.
  unfolds; simpl; eauto.
  unfolds; simpl; eauto.
  unfolds; simpl; eauto.
  unfolds; simpl; eauto.
  unfolds; simpl; eauto.
  unfolds; simpl; eauto.
  auto.
  splits; auto.
  unfold OS_STAT_RDY, OS_STAT_SUSPEND, OS_STAT_SEM, OS_STAT_Q,
        OS_STAT_MBOX, OS_STAT_MUTEX, OS_STAT_POSTQ in *.
  destruct H10. rewrite H; auto.
  destruct H. rewrite H; auto.
  destruct H. rewrite H. do 7 apply or_intror. apply or_introl. reflexivity.
  destruct H. rewrite H. do 8 apply or_intror. apply or_introl. reflexivity.
  destruct H. rewrite H. do 10 apply or_intror. apply or_introl. reflexivity.
  destruct H. rewrite H. do 11 apply or_intror. reflexivity.
  destruct H. rewrite H. do 9 apply or_intror. apply or_introl. reflexivity.
  destruct H. rewrite H, Int.or_assoc, Int.or_idem. do 7 apply or_intror; apply or_introl; reflexivity.
  destruct H. rewrite H, Int.or_assoc, Int.or_idem. do 8 apply or_intror; apply or_introl; reflexivity.
  destruct H. rewrite H, Int.or_assoc, Int.or_idem. do 9 apply or_intror; apply or_introl; reflexivity.
  destruct H. rewrite H, Int.or_assoc, Int.or_idem. do 10 apply or_intror; apply or_introl; reflexivity.
  rewrite H, Int.or_assoc, Int.or_idem. do 11 apply or_intror; reflexivity.
  unfold V_OSTCBEventPtr. simpl. exists x6.
  split. auto. unfold OS_STAT_SUSPEND, OS_STAT_RDY.
  intro pred. destruct H10. {
    rewrite H in H12;destruct H12. left;reflexivity. reflexivity.
  }
  destruct H. {
    rewrite H in H12;destruct H12. right;reflexivity. reflexivity.
  }
  destruct H. {
    rewrite H in pred;destruct pred. tryfalse. tryfalse.
  }
  destruct H. {
    rewrite H in pred;destruct pred. tryfalse. tryfalse.
  }
  destruct H. {
    rewrite H in pred;destruct pred. tryfalse. tryfalse.
  }
  destruct H. {
    rewrite H in pred;destruct pred. tryfalse. tryfalse.
  }
  destruct H. {
    rewrite H in pred;destruct pred. tryfalse. tryfalse.
  }
  destruct H. {
    rewrite H in pred;destruct pred. tryfalse. tryfalse.
  }
  destruct H. {
    rewrite H in pred;destruct pred. tryfalse. tryfalse.
  }
  destruct H. {
    rewrite H in pred;destruct pred. tryfalse. tryfalse.
  }
  destruct H. {
    rewrite H in pred;destruct pred. tryfalse. tryfalse.
  }
  {
    rewrite H in pred;destruct pred. tryfalse. tryfalse.
  }
Qed.


Lemma R_TCB_Status_P_suspend:
  forall rtbl x y row bitx bity prio rtbl' next prev eptr msg dly stat p t0 m0 i,
    0 <= Int.unsigned prio < 64 ->
    array_type_vallist_match Int8u rtbl' ->
    length rtbl' = ∘OS_RDY_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned y)) rtbl = Vint32 row ->
    prio_not_in_tbl prio rtbl' ->
    RL_TCBblk_P
    (next :: prev :: eptr :: msg :: dly :: Vint32 stat
      :: Vint32 prio :: Vint32 x :: Vint32 y
      :: Vint32 bitx :: Vint32 bity :: nil) ->
    R_TCB_Status_P
    (next :: prev :: eptr  :: msg :: dly :: Vint32 stat
      :: Vint32 prio :: Vint32 x :: Vint32 y
      :: Vint32 bitx :: Vint32 bity :: nil) rtbl (p, t0, m0, i) ->
    R_TCB_Status_P
    (next :: prev :: eptr  :: msg :: dly
      :: Vint32 (Int.or stat ($ OS_STAT_SUSPEND))
      :: Vint32 prio :: Vint32 x :: Vint32 y
      :: Vint32 bitx :: Vint32 bity :: nil) rtbl' (p, t0, m0, true).
Proof.
  intros.
  rename H4 into RLtcbblk.
  rename H5 into H4.
  unfold R_TCB_Status_P in H4.
  destruct H4 as [RLHrdy [RHLrdy [RLHsus [RHLsus [RLHstwait RHLstwait]]]]].
  unfold R_TCB_Status_P.
  splits.
  * unfold RLH_RdyI_P in *.
    intros. unfold RdyTCBblk in H4. simpljoin.
    inverts H4. false. eapply prio_rtbl_dec'; eauto.
  * unfold RHL_RdyI_P in *.
    intros. discriminate H4.
  * unfold RLH_Suspend_P in *.
    split.
    {
      intros.
      destruct t0.
      {
        destruct i.
        2: {
          unfold RHL_RdyI_P in RHLrdy.
          pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
          destruct RHLrdy as [Hblk [Hstat Hdly]].
          unfold RdyTCBblk in Hblk. destruct Hblk as [Hprio _]. unfolds in Hprio.
          simpl in Hprio. invert Hprio.
          unfold WaitTCBblk in H4. destruct H4.
          unfolds in H4. simpl in H4. invert H4.
          intros. rewrite H7. eauto. 
        }
        {
          unfold RHL_Suspend_P in RHLsus.
          destruct RHLsus as [RHLsus1 RHLsus2].
          pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
          destruct RHLsus1 as [Hblk Hstat].
          unfolds in Hblk. destruct Hblk as [Hprio _].
          unfolds in Hprio. simpl in Hprio. invert Hprio.
          unfold WaitTCBblk in H4. destruct H4.
          unfolds in H4. simpl in H4. invert H4.
          intros. rewrite <- H7. eauto.
        }
      }
      unfold RHL_TCB_Status_Wait_P in RHLstwait.
      destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
      [RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLpostqsus [RHLwaitmbsus RHLwaitmssus]]]]]]]]]].
      destruct t.
      {
        destruct i.
        2: {
          unfold RHL_WaitS_P in RHLwaits.
          pose proof (RHLwaits p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, false))) as RHLwaits. 
          destruct RHLwaits as [Hwait [Heptr Hstat]].
          inverts Hstat.
          clear - H5. unfold OS_STAT_SEM, OS_STAT_SUSPEND in H5.
          int auto.
        }
        {
          unfold RHL_WaitS_Suspend_P in RHLwaitssus.
          pose proof (RHLwaitssus p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, true))) as RHLwaitssus. 
          destruct RHLwaitssus as [Hwait [Heptr Hstat]].
          inverts Hstat.
          clear - H5. unfold OS_STAT_SEM, OS_STAT_SUSPEND in H5.
          rewrite Int.or_assoc, Int.or_idem in H5.
          int auto.
        }
      }
      
      {
        destruct i.
        2: {
          unfold RHL_WaitQ_P in RHLwaitq.
          pose proof (RHLwaitq p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, false))) as RHLwaitq. 
          destruct RHLwaitq as [Hwait [Heptr Hstat]].
          inverts Hstat.
          clear - H5. unfold OS_STAT_Q, OS_STAT_SUSPEND in H5.
          int auto.
        }
        {
          unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
          pose proof (RHLwaitqsus p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, true))) as RHLwaitqsus. 
          destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
          inverts Hstat.
          clear - H5. unfold OS_STAT_Q, OS_STAT_SUSPEND in H5.
          rewrite Int.or_assoc, Int.or_idem in H5.
          int auto.
        }
      }

      {
        destruct i.
        2: {
          unfold RHL_WaitPostQ_P in RHLwaitpostq.
          pose proof (RHLwaitpostq p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, false))) as RHLwaitpostq.
          destruct RHLwaitpostq as [Hwait [Hwtbl [Heptr Hstat]]].
          inverts Hstat.
          clear - H5. unfold OS_STAT_POSTQ, OS_STAT_SUSPEND in H5.
          int auto.
        }
        {
          unfold RHL_WaitPostQ_Suspend_P in RHLpostqsus.
          pose proof (RHLpostqsus p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, true))) as RHLpostqsus.
          destruct RHLpostqsus as [Ho [Hwait [Heptr Hstat]]].
          inverts Hstat.
          clear - H5. unfold OS_STAT_POSTQ, OS_STAT_SUSPEND in H5.
          rewrite Int.or_assoc, Int.or_idem in H5.
          int auto.
        }
      }

      {
        destruct i.
        2: {
          unfold RHL_Wait_P in RHLwait.
          pose proof (RHLwait p o m0 (eq_refl (p, wait os_stat_time o, m0, false))) as RHLwait. 
          destruct RHLwait as [t [Ho [Hwait [Hdly Hstat]]]].
          inverts Hwait. destruct H7. inverts H8.
          inverts H4. destruct H9. unfolds in H9. simpl in H9.
          apply Some_Vint32_invert in H9. rewrite H9 in Hdly.
          clear - Hdly. int auto.
        }
        {
          unfold RHL_Suspend_P in RHLsus.
          destruct RHLsus as [RHLsus1 RHLsus2].
          pose proof (RHLsus2 p o m0 (eq_refl (p, wait os_stat_time o, m0, true))) as RHLsus2. 
          destruct RHLsus2 as [t [Ho [Hwait [Hdly Hstat]]]].
          inverts Hwait. destruct H7. inverts H8.
          inverts H4. destruct H9. unfolds in H9. simpl in H9.
          apply Some_Vint32_invert in H9. rewrite H9 in Hdly.
          clear - Hdly. int auto.
        }
      }
      {
        destruct i.
        2: {
          unfold RHL_WaitMB_P in RHLwaitmb.
          pose proof (RHLwaitmb p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, false))) as RHLwaitmb. 
          destruct RHLwaitmb as [Hwait [Heptr Hstat]].
          inverts Hstat.
          clear - H5. unfold OS_STAT_MBOX, OS_STAT_SUSPEND in H5.
          int auto.
        }
        {
          unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
          pose proof (RHLwaitmbsus p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, true))) as RHLwaitmbsus. 
          destruct RHLwaitmbsus as [Hwait [Heptr Hstat]].
          inverts Hstat.
          clear - H5. unfold OS_STAT_MBOX, OS_STAT_SUSPEND in H5.
          rewrite Int.or_assoc, Int.or_idem in H5.
          int auto.
        }
      }
      {
        destruct i.
        2: {
          unfold RHL_WaitMS_P in RHLwaitms.
          pose proof (RHLwaitms p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, false))) as RHLwaitms. 
          destruct RHLwaitms as [Hwait [Heptr Hstat]].
          inverts Hstat.
          clear - H5. unfold OS_STAT_MUTEX, OS_STAT_SUSPEND in H5.
          int auto.
        }
        {
          unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
          pose proof (RHLwaitmssus p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, true))) as RHLwaitmssus. 
          destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
          inverts Hstat.
          clear - H5. unfold OS_STAT_MUTEX, OS_STAT_SUSPEND in H5.
          rewrite Int.or_assoc, Int.or_idem in H5.
          int auto.
        }
      }
    }
    {
      intros.
      destruct t0.
      {
        destruct i.
        2: {
          unfold RHL_RdyI_P in RHLrdy.
          pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
          destruct RHLrdy as [Hblk [Hstat Hdly]].
          inverts Hdly. unfolds in H4. destructs H4.
          inverts H8. clear - H6. tryfalse.
        }
        {
          unfold RHL_Suspend_P in RHLsus.
          destruct RHLsus as [RHLsus1 RHLsus2].
          pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
          destruct RHLsus1 as [Hblk Hstat].
          unfolds in Hblk. destruct Hblk as [Hprio [_ Hdly]].
          inverts Hdly. unfolds in H4. destructs H4.
          inverts H8. clear - H6. tryfalse.
        }
      }
      unfold RHL_TCB_Status_Wait_P in RHLstwait.
      destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
      [RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLwaitpostqsus [RHLwaitmbsus RHLwaitmssus]]]]]]]]]].
      destruct t0.
      {
        destruct i.
        2: {
          unfold RHL_WaitS_P in RHLwaits.
          pose proof (RHLwaits p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, false))) as RHLwaits. 
          destruct RHLwaits as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H5.
        }
        {
          unfold RHL_WaitS_Suspend_P in RHLwaitssus.
          pose proof (RHLwaitssus p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, true))) as RHLwaitssus. 
          destruct RHLwaitssus as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H5.
        }
      }
      {
        destruct i.
        2: {
          unfold RHL_WaitQ_P in RHLwaitq.
          pose proof (RHLwaitq p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, false))) as RHLwaitq. 
          destruct RHLwaitq as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H5.
        }
        {
          unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
          pose proof (RHLwaitqsus p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, true))) as RHLwaitqsus. 
          destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H5.
        }
      }
      {
        destruct i.
        2: {
          unfold RHL_WaitPostQ_P in RHLwaitpostq.
          pose proof (RHLwaitpostq p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, false))) as RHLwaitpostq. 
          destruct RHLwaitpostq as [Ho [Hwait [Heptr Hstat]]].
          inverts Hwait. destruct H8. inverts H9.
          inverts H4. destruct H10. unfolds in H10. simpl in H10.
          apply Some_Vint32_invert in H10. inverts H7. inverts H9.
          inverts Hstat.
          unfold OS_STAT_POSTQ, OS_STAT_SUSPEND in H5.
          int auto.
        }
        {
          unfold RHL_WaitPostQ_Suspend_P in RHLwaitpostqsus.
          pose proof (RHLwaitpostqsus p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, true))) as RHLwaitpostqsus. 
          destruct RHLwaitpostqsus as [Ho [Hwait [Heptr Hstat]]].
          inverts Hwait. destruct H8. inverts H9.
          inverts H4. destruct H10. unfolds in H10. simpl in H10.
          apply Some_Vint32_invert in H10. inverts H7. inverts H9.
          inverts Hstat.
          clear - H5. unfold OS_STAT_POSTQ, OS_STAT_SUSPEND in H5.
          rewrite Int.or_assoc, Int.or_idem in H5.
          int auto.
        }
      }
      {
        destruct i.
        2: {
          unfold RHL_Wait_P in RHLwait.
          pose proof (RHLwait p o m0 (eq_refl (p, wait os_stat_time o, m0, false))) as RHLwait.
          destruct RHLwait as [t0 RHLwait].
          destruct RHLwait as [Ho [Hwait [Hdly Hstat]]].
          inverts Hwait. destruct H8. inverts H9.
          inverts H4. destruct H10. unfolds in H10. simpl in H10.
          apply Some_Vint32_invert in H10. inverts H7. inverts H9. inverts H10.
          rewrite Ho.
          eauto.
        }
        {
          unfold RHL_Suspend_P in RHLsus.
          destruct RHLsus as [RHLsus1 RHLsus2].
          pose proof (RHLsus2 p o m0 (eq_refl (p, wait os_stat_time o, m0, true))) as RHLsus2. 
          destruct RHLsus2 as [t0 [Ho [Hwait [Hdly Hstat]]]].
          inverts Hwait. destruct H8. inverts H9.
          inverts H4. destruct H10. unfolds in H10. simpl in H10.
          apply Some_Vint32_invert in H10. inverts H7. inverts H9.
          rewrite H10 in Ho. rewrite Ho. eauto.
        }
      }
      {
        destruct i.
        2: {
          unfold RHL_WaitMB_P in RHLwaitmb.
          pose proof (RHLwaitmb p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, false))) as RHLwaitmb. 
          destruct RHLwaitmb as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H5.
        }
        {
          unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
          pose proof (RHLwaitmbsus p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, true))) as RHLwaitmbsus. 
          destruct RHLwaitmbsus as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H5.
        }
      }
      {
        destruct i.
        2: {
          unfold RHL_WaitMS_P in RHLwaitms.
          pose proof (RHLwaitms p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, false))) as RHLwaitms. 
          destruct RHLwaitms as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H5.
        }
        {
          unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
          pose proof (RHLwaitmssus p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, true))) as RHLwaitmssus. 
          destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H5.
        }
      }
    }
  * unfold RHL_Suspend_P.
    split.
    {
      intros. inverts H4.
      destruct i.
      2: {
        unfolds in RHLrdy.
        pose proof (RHLrdy prio0 m (eq_refl ((prio0, rdy, m, false)))) as RHLrdy.
        destruct RHLrdy as [[Hprio _] [Hstat Hdly]].
        inverts Hprio. inverts Hstat. inverts Hdly.
        split. unfold WaitTCBblk. splits; auto.
        unfolds. simpl. unfold OS_STAT_RDY, OS_STAT_SUSPEND; int auto.
      }
      {
        unfolds in RHLsus.
        destruct RHLsus as [RHLsus1 RHLsus2].
        pose proof (RHLsus1 prio0 m (eq_refl (prio0, rdy, m, true))) as RHLsus.
        destruct RHLsus as [Hwait Hstat].
        unfold WaitTCBblk in Hwait.
        destruct Hwait as [Hprio [_ Hdly]].
        inverts Hprio. inverts Hdly. inverts Hstat.
        split. unfolds. splits; auto.
        unfolds. simpl. unfold OS_STAT_SUSPEND; int auto.
      }
    }
    {
      intros. inverts H4.
      destruct i.
      2: {
        unfolds in RHLstwait. destruct RHLstwait as [RHLwait _].
        unfolds in RHLwait.
        pose proof (RHLwait prio0 t_opt m (eq_refl (prio0, wait os_stat_time t_opt, m, false))) as RHLwait.
        destruct RHLwait as [t0 [Ht [Hblk [Hlt Hstat]]]].
        unfolds in Hblk.
        destruct Hblk as [Hprio [_ Hdly]].
        inverts Hprio. inverts Hdly. inverts Hstat.
        unfold WaitTCBblk. eexists. splits; eauto.
      }
      {
        unfolds in RHLsus.
        destruct RHLsus as [RHLsus1 RHLsus2].
        pose proof (RHLsus2 prio0 t_opt m (eq_refl (prio0, wait os_stat_time t_opt, m, true))) as RHLsus2.
        destruct RHLsus2 as [t0 [Ht [Hblk [Hlt Hstat]]]].
        unfolds in Hblk.
        destruct Hblk as [Hprio [_ Hdly]].
        inverts Hprio. inverts Hdly. inverts Hstat.
        unfold WaitTCBblk. eexists. splits; eauto.
      }
    }
  * unfold RLH_TCB_Status_Wait_P in *.
    simpljoin. splits.
    + unfolds RLH_Wait_P. intros. unfolds in H21. simpl in H21.
      unfold OS_STAT_SUSPEND, OS_STAT_RDY in H21.
      apply Some_Vint32_invert in H21.
      clear - H21. unfold OS_STAT_RDY, OS_STAT_SUSPEND in H21.
      apply int_or_zero_split in H21. int auto.
    + unfolds RLH_WaitS_P. intros. 
      unfolds in H21. simpl in H21.
      apply Some_Vint32_invert in H21.
      unfold OS_STAT_SUSPEND, OS_STAT_SEM in H21.
      clear - RLtcbblk H21.
      unfold RL_TCBblk_P in RLtcbblk. simpljoin.
      inverts H4. destruct H10. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      rewrite H4 in H21; inverts H21.
    + unfolds RLH_WaitS_TO_P. intros. 
      unfolds in H21. simpl in H21.
      apply Some_Vint32_invert in H21.
      unfold OS_STAT_SUSPEND, OS_STAT_SEM in H21.
      clear - RLtcbblk H21.
      unfold RL_TCBblk_P in RLtcbblk. simpljoin.
      inverts H4. destruct H10. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      rewrite H4 in H21; inverts H21.
    + unfolds RLH_WaitQ_P. intros.
      unfolds in H21. simpl in H21.
      apply Some_Vint32_invert in H21.
      unfold OS_STAT_SUSPEND, OS_STAT_Q in H21.
      clear - RLtcbblk H21.
      unfold RL_TCBblk_P in RLtcbblk. simpljoin.
      inverts H4. destruct H10. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      rewrite H4 in H21; inverts H21.
      + unfolds RLH_WaitQ_TO_P. intros.
        unfolds in H21. simpl in H21.
        apply Some_Vint32_invert in H21.
        unfold OS_STAT_SUSPEND, OS_STAT_Q in H21.
        clear - RLtcbblk H21.
        unfold RL_TCBblk_P in RLtcbblk. simpljoin.
        inverts H4. destruct H10. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        rewrite H4 in H21; inverts H21.
    + unfolds RLH_WaitMB_P. intros.
      unfolds in H21. simpl in H21.
      unfold OS_STAT_SUSPEND, OS_STAT_MBOX in H21.
      clear - RLtcbblk H21.
      unfold RL_TCBblk_P in RLtcbblk. simpljoin.
      inverts H4. destruct H10. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      destruct H4. rewrite H4 in H21; inverts H21.
      rewrite H4 in H21; inverts H21.
      + unfolds RLH_WaitMB_TO_P. intros.
        unfolds in H21. simpl in H21.
        unfold OS_STAT_SUSPEND, OS_STAT_MBOX in H21.
        clear - RLtcbblk H21.
        unfold RL_TCBblk_P in RLtcbblk. simpljoin.
        inverts H4. destruct H10. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        rewrite H4 in H21; inverts H21.
    + splits.
      - unfolds RLH_WaitMS_P. intros.
        unfolds in H21. simpl in H21.
        unfold OS_STAT_SUSPEND, OS_STAT_MUTEX in H21.
        clear - RLtcbblk H21.
        unfold RL_TCBblk_P in RLtcbblk. simpljoin.
        inverts H4. destruct H10. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        rewrite H4 in H21; inverts H21.
      - unfolds RLH_WaitMS_TO_P. intros.
        unfolds in H21. simpl in H21.
        unfold OS_STAT_SUSPEND, OS_STAT_SEM in H21.
        destruct t0.
        {
          destruct i.
          {
            unfolds in RHLsus.
            destruct RHLsus as [RHLsus1 RHLsus2].
            pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
            destruct RHLsus1 as [Hwait Hstat].
            inverts Hstat. 
            clear - H21; unfold OS_STAT_SUSPEND in H21; int auto.
          }
          {
            unfolds in RHLrdy.
            pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
            destruct RHLrdy as [Hblk [Hstat Hdly]].
            inverts Hstat.
            clear - H21; unfold OS_STAT_RDY in H21; int auto.
          }
        }
        unfold OS_STAT_MUTEX in H21.
        apply Some_Vint32_invert in H21.
        clear -RLtcbblk H21.
        unfold RL_TCBblk_P in RLtcbblk;simpljoin.
        inverts H4. destruct H10. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        rewrite H4 in H21; inverts H21.
      - unfolds RLH_WaitPostQ_P. intros.
        unfolds in H21. simpl in H21.
        unfold OS_STAT_SUSPEND, OS_STAT_SEM in H21.
        destruct t0.
        {
          destruct i.
          {
            unfolds in RHLsus.
            destruct RHLsus as [RHLsus1 RHLsus2].
            pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
            destruct RHLsus1 as [Hwait Hstat].
            inverts Hstat. 
            clear - H21; unfold OS_STAT_SUSPEND in H21; int auto.
          }
          {
            unfolds in RHLrdy.
            pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
            destruct RHLrdy as [Hblk [Hstat Hdly]].
            inverts Hstat.
            clear - H21; unfold OS_STAT_RDY in H21; int auto.
          }
        }
        apply Some_Vint32_invert in H21.
        clear -RLtcbblk H21.
        unfold RL_TCBblk_P in RLtcbblk;simpljoin.
        inverts H4. destruct H10. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        destruct H4. rewrite H4 in H21; inverts H21.
        rewrite H4 in H21; inverts H21.
      - unfold RLH_WaitS_Suspend_P. intros.
        unfolds in H21. simpl in H21.
        unfold OS_STAT_SUSPEND, OS_STAT_SEM in H21.
        destruct t0.
        {
          destruct i.
          {
            unfolds in RHLsus.
            destruct RHLsus as [RHLsus1 RHLsus2].
            pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
            destruct RHLsus1 as [Hwait Hstat].
            inverts Hstat. 
            clear - H21; unfold OS_STAT_SUSPEND in H21; int auto.
          }
          {
            unfolds in RHLrdy.
            pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
            destruct RHLrdy as [Hblk [Hstat Hdly]].
            inverts Hstat.
            clear - H21; unfold OS_STAT_RDY in H21; int auto.
          }
        }
        unfold RHL_TCB_Status_Wait_P in RHLstwait.
        destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
        [RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLwaitpostqsus [RHLwaitmbsus RHLwaitmssus]]]]]]]]]].
        destruct t0.
        {
          destruct i.
          2: {
            unfold RHL_WaitS_P in RHLwaits.
            pose proof (RHLwaits p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, false))) as RHLwaits. 
            destruct RHLwaits as [Hwait [Heptr Hstat]].
            inverts Heptr. unfolds in H20.
            destructs H20. inverts H20. inverts H22.
            destruct Hwait.
            destruct H20.
            * destruct H20 as [Ho Hwrd].
              destruct Hwrd.
              ** destruct H20 as [Hneq Hwait].
                 unfolds in Hwait.
                 destructs Hwait. inverts H20. inverts H25. inverts H24.
                 do 2 eexists.
                 eauto.
              ** destruct H20 as [Heq [Hrdy Hdly]].
                 inverts Heq. inverts Ho. inverts Hstat.
                 apply Some_Vint32_invert in H21. inverts H24.
                 unfolds in Hrdy.
                 destruct Hrdy as [Hprio Hpintbl].
                 inverts Hprio. inverts Hdly.
                 do 2 eexists.
                 eauto.
            * destruct H20 as [Ho Hwait].
              unfolds in Hwait.
              destruct Hwait as [Hprio [Hpintbl Hdly]].
              inverts Hprio. inverts Hdly. inverts H24.
              do 2 eexists.
              eauto.
          }
          {
            unfold RHL_WaitS_Suspend_P in RHLwaitssus.
            pose proof (RHLwaitssus p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, true))) as RHLwaitssus. 
            destruct RHLwaitssus as [Hwait [Heptr Hstat]].
            destruct Hwait.
            * destruct H23 as [t0 H23].
              destruct H23 as (Ho & Hwt & Hneq).
              inverts Heptr. unfolds in H20.
              destructs H20.
              inverts H20. inverts H22. inverts H24. unfolds in Hwt.
              destruct Hwt as [Hprio [Hpintbl Hdly]].
              inverts Ho. inverts Hprio. inverts Hdly. inverts Hstat.
              do 2 eexists.
              splits.
              eauto.
              right.
              eauto.
            * destruct H23 as [Ho Hwt].
              unfolds in Hwt.
              destruct Hwt as (Hprio & Htbl & Hdly).
              inverts Heptr. unfolds in H20.
              destructs H20.
              inverts H20. inverts H22. inverts H24.
              inverts Ho. inverts Hprio. inverts Hdly. inverts Hstat.
              do 2 eexists.
              splits.
              eauto.
              left.
              eauto.
          }
        }
        {
          destruct i.
          2: {
            unfold RHL_WaitQ_P in RHLwaitq.
            pose proof (RHLwaitq p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, false))) as RHLwaitq. 
            destruct RHLwaitq as [Hwait [Heptr Hstat]].
            inverts Hstat. inverts H21.
          }
          {
            unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
            pose proof (RHLwaitqsus p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, true))) as RHLwaitqsus. 
            destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
            inverts Hstat. inverts H21.
          }
        }
        {
          destruct i.
          2: {
            unfold RHL_WaitPostQ_P in RHLwaitpostq.
            pose proof (RHLwaitpostq p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, false))) as RHLwaitpostq. 
            destruct RHLwaitpostq as [Ho [Hwt [Heptr Hstat]]].
            inverts Hstat. inverts H21.
          }
          {
            unfold RHL_WaitPostQ_Suspend_P in RHLwaitpostqsus.
            pose proof (RHLwaitpostqsus p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, true))) as RHLwaitpostqsus. 
            destruct RHLwaitpostqsus as [Ho [Hwt [Heptr Hstat]]].
            inverts Hstat. inverts H21. 
          }
        }
        {
          destruct i.
          2: {
            unfold RHL_Wait_P in RHLwait.
            pose proof (RHLwait p o m0 (eq_refl (p, wait os_stat_time o, m0, false))) as RHLwait. 
            destruct RHLwait as [t0 [Ho [Hwt [Htu Hstat]]]].
            inverts Hstat. inverts H21.
          }
          {
            unfold RHL_Suspend_P in RHLsus.
            destruct RHLsus as (RHLsus1 & RHLsus2).
            pose proof (RHLsus2 p o m0 (eq_refl (p, wait os_stat_time o, m0, true))) as RHLsus2. 
            destruct RHLsus2 as [t0 [Ho [Hwt [Htu Hstat]]]].
            inverts Hstat. inverts H21.
          }
        }
        {
          destruct i.
          2: {
            unfold RHL_WaitMB_P in RHLwaitmb.
            pose proof (RHLwaitmb p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, false))) as RHLwaitmb. 
            destruct RHLwaitmb as [RHLwaitmb [Heptr Hstat]].
            inverts Hstat. inverts H21.
          }
          {
            unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
            pose proof (RHLwaitmbsus p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, true))) as RHLwaitmbsus. 
            destruct RHLwaitmbsus as [_ [Heptr Hstat]].
            inverts Hstat. inverts H21.
          }
        }
        {
          destruct i.
          2: {
            unfold RHL_WaitMS_P in RHLwaitms.
            pose proof (RHLwaitms p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, false))) as RHLwaitms. 
            destruct RHLwaitms as [Hwait [Heptr Hstat]].
            inverts Hstat. inverts H21.
          }
          {
            unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
            pose proof (RHLwaitmssus p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, true))) as RHLwaitmssus. 
            destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
            inverts Hstat. inverts H21.
          }
        }
      - unfolds RLH_WaitQ_Suspend_P. intros.
        unfolds in H21. simpl in H21.
        unfold OS_STAT_SUSPEND, OS_STAT_Q in H21.
        destruct t0.
        {
          destruct i.
          {
            unfolds in RHLsus.
            destruct RHLsus as [RHLsus1 RHLsus2].
            pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
            destruct RHLsus1 as [Hwait Hstat].
            inverts Hstat. 
            clear - H21; unfold OS_STAT_SUSPEND in H21; int auto.
          }
          {
            unfolds in RHLrdy.
            pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
            destruct RHLrdy as [Hblk [Hstat Hdly]].
            inverts Hstat.
            clear - H21; unfold OS_STAT_RDY in H21; int auto.
          }
        }
        unfold RHL_TCB_Status_Wait_P in RHLstwait.
        destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
        [RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLwaitpostqsus [RHLwaitmbsus RHLwaitmssus]]]]]]]]]].
        destruct t0.
        {
          destruct i.
          {
            unfold RHL_WaitS_Suspend_P in RHLwaitssus.
            pose proof (RHLwaitssus p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, true))) as RHLwaitssus. 
            destruct RHLwaitssus as [Hwait [Heptr Hstat]].
            inverts Hstat. inverts H21.
          }
          {
            unfold RHL_WaitS_P in RHLwaits.
            pose proof (RHLwaits p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, false))) as RHLwaits. 
            destruct RHLwaits as [Hwait [Heptr Hstat]].
            inverts Hstat. inverts H21.
          }
        }
        {
          destruct i.
          {
            unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
            pose proof (RHLwaitqsus p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, true))) as RHLwaitqsus. 
            destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
            inverts Hstat. inverts H22. inverts Heptr.
            unfolds in H20.
            destruct H20 as (Hprio & Hntbl & Hdly).
            inverts Hprio. inverts Hdly.
            destruct Hwait.
            destruct H20 as (t0 & Ho & Hwt).
            inverts Ho; destruct Hwt as (Hprio & Hn & Hdly).
            inverts Hprio. inverts Hdly.
            do 2 eexists.
            splits;eauto.
            right. splits;eauto.
            int auto.
          }
        }
        unfold RHL_TCB_Status_Wait_P in RHLstwait.
        destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
        [RHLwaitms [RHLwaitssus [RHLwaitqsus [RHLwaitmbsus RHLwaitmssus]]]]]]]].
        destruct t0.
        {
          destruct i.
          2: {
            unfold RHL_WaitS_P in RHLwaits.
            pose proof (RHLwaits p e o m0 (eq_refl (p, wait (os_stat_sem e) i0, m0, false))) as RHLwaits. 
            destruct RHLwaits as [Hwait [Heptr Hstat]].
            inverts Hstat. inverts H21.
          }
          {
            unfold RHL_WaitS_Suspend_P in RHLwaitssus.
            pose proof (RHLwaitssus p e o m0 (eq_refl (p, wait (os_stat_sem e) i0, m0, true))) as RHLwaitssus. 
            destruct RHLwaitssus as [Hwait [Heptr Hstat]].
            inverts Hstat. inverts H21.
          }
        }
        {
          destruct i.
          2: {
            unfold RHL_WaitQ_P in RHLwaitq.
            pose proof (RHLwaitq p e o m0 (eq_refl (p, wait (os_stat_q e) i0, m0, false))) as RHLwaitq. 
            destruct RHLwaitq as [Hwait [Heptr Hstat]].
            inverts Heptr. unfolds in H14.
            destructs H14. inverts H14. inverts H16. unfolds in Hwait.
            destructs Hwait. inverts H14. inverts H19. inverts H18.
            eauto.
          }
          {
            unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
            pose proof (RHLwaitqsus p e o m0 (eq_refl (p, wait (os_stat_q e) i0, m0, true))) as RHLwaitqsus. 
            destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
            inverts Heptr. unfolds in H14.
            destructs H14. inverts H14. inverts H16. unfolds in Hwait.
            destructs Hwait. inverts H14. inverts H19. inverts H18.
            eauto.
          }
        }
        {
          destruct i.
          2: {
            unfold RHL_Wait_P in RHLwait.
            pose proof (RHLwait p i0 m0 (eq_refl (p, wait os_stat_time i0, m0, false))) as RHLwait. 
            destruct RHLwait as [Hwait [Hdly Hstat]].
            inverts Hstat. inverts H21.
          }
          {
            unfold RHL_Suspend_P in RHLsus.
            destruct RHLsus as [RHLsus1 RHLsus2].
            pose proof (RHLsus2 p i0 m0 (eq_refl (p, wait os_stat_time i0, m0, true))) as RHLsus2. 
            destruct RHLsus2 as [Hwait [Hdly Hstat]].
            inverts Hstat. inverts H21. 
          }
        }
        {
          destruct i.
          2: {
            unfold RHL_WaitMB_P in RHLwaitmb.
            pose proof (RHLwaitmb p e o m0 (eq_refl (p, wait (os_stat_mbox e) i0, m0, false))) as RHLwaitmb. 
            destruct RHLwaitmb as [Hwait [Heptr Hstat]].
            inverts Hstat. inverts H21.
          }
          {
            unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
            pose proof (RHLwaitmbsus p e o m0 (eq_refl (p, wait (os_stat_mbox e) i0, m0, true))) as RHLwaitmbsus. 
            destruct RHLwaitmbsus as [Hwait [Heptr Hstat]].
            inverts Hstat. inverts H21.
          }
        }
        {
          destruct i.
          2: {
            unfold RHL_WaitMS_P in RHLwaitms.
            pose proof (RHLwaitms p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) i0, m0, false))) as RHLwaitms. 
            destruct RHLwaitms as [Hwait [Heptr Hstat]].
            inverts Hstat. inverts H21.
          }
          {
            unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
            pose proof (RHLwaitmssus p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) i0, m0, true))) as RHLwaitmssus. 
            destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
            inverts Hstat. inverts H21.
          }
        }
    + split.
    - unfolds RLH_WaitMB_Suspend_P. intros.
      unfolds in H15. simpl in H15.
      unfold OS_STAT_SUSPEND, OS_STAT_MBOX in H15.
      destruct t0.
      {
        destruct i.
        {
          unfolds in RHLsus.
          destruct RHLsus as [RHLsus1 RHLsus2].
          pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
          destruct RHLsus1 as [Hwait Hstat].
          inverts Hstat. 
          clear - H15; unfold OS_STAT_SUSPEND in H15; int auto.
        }
        {
          unfolds in RHLrdy.
          pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
          destruct RHLrdy as [Hblk [Hstat Hdly]].
          inverts Hstat.
          clear - H15; unfold OS_STAT_RDY in H15; int auto.
        }
      }
      unfold RHL_TCB_Status_Wait_P in RHLstwait.
      destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
      [RHLwaitms [RHLwaitssus [RHLwaitqsus [RHLwaitmbsus RHLwaitmssus]]]]]]]].
      destruct t0.
      {
        destruct i.
        2: {
          unfold RHL_WaitS_P in RHLwaits.
          pose proof (RHLwaits p e i0 m0 (eq_refl (p, wait (os_stat_sem e) i0, m0, false))) as RHLwaits. 
          destruct RHLwaits as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H15.
        }
        {
          unfold RHL_WaitS_Suspend_P in RHLwaitssus.
          pose proof (RHLwaitssus p e i0 m0 (eq_refl (p, wait (os_stat_sem e) i0, m0, true))) as RHLwaitssus. 
          destruct RHLwaitssus as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H15.
        }
      }
      {
        destruct i.
        2: {
          unfold RHL_WaitQ_P in RHLwaitq.
          pose proof (RHLwaitq p e i0 m0 (eq_refl (p, wait (os_stat_q e) i0, m0, false))) as RHLwaitq. 
          destruct RHLwaitq as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H15.
        }
        {
          unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
          pose proof (RHLwaitqsus p e i0 m0 (eq_refl (p, wait (os_stat_q e) i0, m0, true))) as RHLwaitqsus. 
          destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H15.
        }
      }
      {
        destruct i.
        2: {
          unfold RHL_Wait_P in RHLwait.
          pose proof (RHLwait p i0 m0 (eq_refl (p, wait os_stat_time i0, m0, false))) as RHLwait. 
          destruct RHLwait as [Hwait [Hdly Hstat]].
          inverts Hstat. inverts H15.
        }
        {
          unfold RHL_Suspend_P in RHLsus.
          destruct RHLsus as [RHLsus1 RHLsus2].
          pose proof (RHLsus2 p i0 m0 (eq_refl (p, wait os_stat_time i0, m0, true))) as RHLsus2. 
          destruct RHLsus2 as [Hwait [Hdly Hstat]].
          inverts Hstat. inverts H15. 
        }
      }
      {
        destruct i.
        2: {
          unfold RHL_WaitMB_P in RHLwaitmb.
          pose proof (RHLwaitmb p e i0 m0 (eq_refl (p, wait (os_stat_mbox e) i0, m0, false))) as RHLwaitmb. 
          destruct RHLwaitmb as [Hwait [Heptr Hstat]].
          inverts Heptr. unfolds in H14.
          destructs H14. inverts H14. inverts H16. unfolds in Hwait.
          destructs Hwait. inverts H14. inverts H19. inverts H18.
          eauto.
        }
        {
          unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
          pose proof (RHLwaitmbsus p e i0 m0 (eq_refl (p, wait (os_stat_mbox e) i0, m0, true))) as RHLwaitmbsus. 
          destruct RHLwaitmbsus as [Hwait [Heptr Hstat]].
          inverts Heptr. unfolds in H14.
          destructs H14. inverts H14. inverts H16. unfolds in Hwait.
          destructs Hwait. inverts H14. inverts H19. inverts H18.
          eauto.
        }
      }
      {
        destruct i.
        2: {
          unfold RHL_WaitMS_P in RHLwaitms.
          pose proof (RHLwaitms p e i0 m0 (eq_refl (p, wait (os_stat_mutexsem e) i0, m0, false))) as RHLwaitms. 
          destruct RHLwaitms as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H15.
        }
        {
          unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
          pose proof (RHLwaitmssus p e i0 m0 (eq_refl (p, wait (os_stat_mutexsem e) i0, m0, true))) as RHLwaitmssus. 
          destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H15.
        }
      }
    - unfolds RLH_WaitMS_Suspend_P. intros.
      unfolds in H15. simpl in H15.
      unfold OS_STAT_SUSPEND, OS_STAT_MBOX in H15.
      destruct t0.
      {
        destruct i.
        {
          unfolds in RHLsus.
          destruct RHLsus as [RHLsus1 RHLsus2].
          pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
          destruct RHLsus1 as [Hwait Hstat].
          inverts Hstat. inverts H15.
        }
        {
          unfolds in RHLrdy.
          pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
          destruct RHLrdy as [Hblk [Hstat Hdly]].
          inverts Hstat. inverts H15.
        }
      }
      unfold RHL_TCB_Status_Wait_P in RHLstwait.
      destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
      [RHLwaitms [RHLwaitssus [RHLwaitqsus [RHLwaitmbsus RHLwaitmssus]]]]]]]].
      destruct t0.
      {
        destruct i.
        2: {
          unfold RHL_WaitS_P in RHLwaits.
          pose proof (RHLwaits p e i0 m0 (eq_refl (p, wait (os_stat_sem e) i0, m0, false))) as RHLwaits. 
          destruct RHLwaits as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H15.
        }
        {
          unfold RHL_WaitS_Suspend_P in RHLwaitssus.
          pose proof (RHLwaitssus p e i0 m0 (eq_refl (p, wait (os_stat_sem e) i0, m0, true))) as RHLwaitssus. 
          destruct RHLwaitssus as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H15.
        }
      }
      {
        destruct i.
        2: {
          unfold RHL_WaitQ_P in RHLwaitq.
          pose proof (RHLwaitq p e i0 m0 (eq_refl (p, wait (os_stat_q e) i0, m0, false))) as RHLwaitq. 
          destruct RHLwaitq as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H15.
        }
        {
          unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
          pose proof (RHLwaitqsus p e i0 m0 (eq_refl (p, wait (os_stat_q e) i0, m0, true))) as RHLwaitqsus. 
          destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H15.
        }
      }
      {
        destruct i.
        2: {
          unfold RHL_Wait_P in RHLwait.
          pose proof (RHLwait p i0 m0 (eq_refl (p, wait os_stat_time i0, m0, false))) as RHLwait. 
          destruct RHLwait as [Hwait [Hdly Hstat]].
          inverts Hstat. inverts H15.
        }
        {
          unfold RHL_Suspend_P in RHLsus.
          destruct RHLsus as [RHLsus1 RHLsus2].
          pose proof (RHLsus2 p i0 m0 (eq_refl (p, wait os_stat_time i0, m0, true))) as RHLsus2. 
          destruct RHLsus2 as [Hwait [Hdly Hstat]].
          inverts Hstat. inverts H15. 
        }
      }
      {
        destruct i.
        2: {
          unfold RHL_WaitMB_P in RHLwaitmb.
          pose proof (RHLwaitmb p e i0 m0 (eq_refl (p, wait (os_stat_mbox e) i0, m0, false))) as RHLwaitmb. 
          destruct RHLwaitmb as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H15.
        }
        {
          unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
          pose proof (RHLwaitmbsus p e i0 m0 (eq_refl (p, wait (os_stat_mbox e) i0, m0, true))) as RHLwaitmbsus. 
          destruct RHLwaitmbsus as [Hwait [Heptr Hstat]].
          inverts Hstat. inverts H15.
        }
      }
      {
        destruct i.
        2: {
          unfold RHL_WaitMS_P in RHLwaitms.
          pose proof (RHLwaitms p e i0 m0 (eq_refl (p, wait (os_stat_mutexsem e) i0, m0, false))) as RHLwaitms. 
          destruct RHLwaitms as [Hwait [Heptr Hstat]].
          inverts Heptr. unfolds in H14.
          destructs H14. inverts H14. inverts H16. unfolds in Hwait.
          destructs Hwait. inverts H14. inverts H19. inverts H18.
          eauto.
        }
        {
          unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
          pose proof (RHLwaitmssus p e i0 m0 (eq_refl (p, wait (os_stat_mutexsem e) i0, m0, true))) as RHLwaitmssus. 
          destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
          inverts Heptr. unfolds in H14.
          destructs H14. inverts H14. inverts H16. unfolds in Hwait.
          destructs Hwait. inverts H14. inverts H19. inverts H18.
          eauto.
        }
      }
  * unfold RHL_TCB_Status_Wait_P in *.
    simpljoin. splits.
    + unfolds RHL_Wait_P. intros. inverts H14.
    + unfolds RHL_WaitS_P. intros. inverts H14.
    + unfolds RHL_WaitQ_P. intros. inverts H14.
    + unfolds RHL_WaitMB_P. intros. inverts H14.
    + unfolds RHL_WaitMS_P. intros. inverts H14.
    + unfolds RHL_WaitS_Suspend_P. intros.
      inverts H14.
      destruct i.
      2: {
        unfolds in H5.
        pose proof (H5 prio0 eid t m (eq_refl (prio0, wait (os_stat_sem eid) t, m, false))) as H5.
        destruct H5 as [Hblk [Heptr Hstat]].
        unfolds in Hblk. destruct Hblk as [Hprio [_ Hdly]].
        inverts Hprio; inverts Hdly; inverts Heptr; inverts Hstat.
        unfold WaitTCBblk. splits; auto.
      }
      {
        pose proof (H9 prio0 eid t m (eq_refl (prio0, wait (os_stat_sem eid) t, m, true))) as H9.
        destruct H9 as [Hblk [Heptr Hstat]].
        unfolds in Hblk. destruct Hblk as [Hprio [_ Hdly]].
        inverts Hprio; inverts Hdly; inverts Heptr; inverts Hstat.
        unfold WaitTCBblk. splits; auto.
      }
    + unfolds RHL_WaitQ_Suspend_P. intros.
      inverts H14.
      destruct i.
      2: {
        unfolds in H6.
        pose proof (H6 prio0 eid t m (eq_refl (prio0, wait (os_stat_q eid) t, m, false))) as H6.
        destruct H6 as [Hblk [Heptr Hstat]].
        unfolds in Hblk. destruct Hblk as [Hprio [_ Hdly]].
        inverts Hprio; inverts Hdly; inverts Heptr; inverts Hstat.
        unfold WaitTCBblk. splits; auto.
      }
      {
        pose proof (H10 prio0 eid t m (eq_refl (prio0, wait (os_stat_q eid) t, m, true))) as H10.
        destruct H10 as [Hblk [Heptr Hstat]].
        unfolds in Hblk. destruct Hblk as [Hprio [_ Hdly]].
        inverts Hprio; inverts Hdly; inverts Heptr; inverts Hstat.
        unfold WaitTCBblk. splits; auto.
      }
    + split.
    - unfolds RHL_WaitMB_Suspend_P. intros.
      inverts H14.
      destruct i.
      2: {
        unfolds in H7.
        pose proof (H7 prio0 eid t m (eq_refl (prio0, wait (os_stat_mbox eid) t, m, false))) as H7.
        destruct H7 as [Hblk [Heptr Hstat]].
        unfolds in Hblk. destruct Hblk as [Hprio [_ Hdly]].
        inverts Hprio; inverts Hdly; inverts Heptr; inverts Hstat.
        unfold WaitTCBblk. splits; auto.
      }
      {
        pose proof (H11 prio0 eid t m (eq_refl (prio0, wait (os_stat_mbox eid) t, m, true))) as H11.
        destruct H11 as [Hblk [Heptr Hstat]].
        unfolds in Hblk. destruct Hblk as [Hprio [_ Hdly]].
        inverts Hprio; inverts Hdly; inverts Heptr; inverts Hstat.
        unfold WaitTCBblk. splits; auto.
      }
    - unfolds RHL_WaitMS_Suspend_P. intros.
      inverts H14.
      destruct i.
      2: {
        unfolds in H8.
        pose proof (H8 prio0 eid t m (eq_refl (prio0, wait (os_stat_mutexsem eid) t, m, false))) as H8.
        destruct H8 as [Hblk [Heptr Hstat]].
        unfolds in Hblk. destruct Hblk as [Hprio [_ Hdly]].
        inverts Hprio; inverts Hdly; inverts Heptr; inverts Hstat.
        unfold WaitTCBblk. splits; auto.
      }
      {
        pose proof (H12 prio0 eid t m (eq_refl (prio0, wait (os_stat_mutexsem eid) t, m, true))) as H12.
        destruct H12 as [Hblk [Heptr Hstat]].
        unfolds in Hblk. destruct Hblk as [Hprio [_ Hdly]].
        inverts Hprio; inverts Hdly; inverts Heptr; inverts Hstat.
        unfold WaitTCBblk. splits; auto.
      }
Qed.


Lemma R_PrioTbl_P_suspend:
  forall vl tcb tid prio st msg adrv sus,
    R_PrioTbl_P vl tcb adrv ->
    TcbMod.get tcb tid = Some (prio, st, msg, sus) ->
    R_PrioTbl_P vl (TcbMod.set tcb tid (prio, st, msg, true)) adrv.
Proof.
  intros.
  unfold R_PrioTbl_P in *.
  simpljoin. splits.
  * clear - H H0.
    intros. pose proof (H prio0 tcbid H1 H2 H3) as H.
    do 3 destruct H.
    assert (tid = tcbid \/ tid <> tcbid) as choice by tauto.
    destruct choice.
    + rewrite H4. rewrite TcbMod.map_get_set.
      rewrite <- H4 in H. unfold get in H; simpl in H.
      rewrite H in H0. inverts H0. eauto.
    + rewrite TcbMod.map_get_set'.
      unfold get in H; simpl in H. eauto. auto.
  * clear - H H0 H1.
    intros.
    assert (tid = tcbid \/ tid <> tcbid) as choice by tauto.
    destruct choice.
    + eapply H1. rewrite H3 in H0.
      unfold get; simpl. rewrite H3 in H2. rewrite TcbMod.map_get_set in H2.
      inverts H2. eauto.
    + eapply H1. rewrite TcbMod.map_get_set' in H2.
      unfold get; simpl. eauto. auto.
  * eapply R_Prio_NoChange_Prio_hold; eauto.
Qed.

Lemma RH_TCBList_ECBList_P_suspend:
  forall ecbls tcb tid prio st msg tid' sus,
    RH_TCBList_ECBList_P ecbls tcb tid' ->
    TcbMod.get tcb tid = Some (prio, st, msg, sus) ->
    RH_TCBList_ECBList_P ecbls (TcbMod.set tcb tid (prio, st, msg, true)) tid'.
Proof.
  intros.
  unfold RH_TCBList_ECBList_P in *. simpljoin. splits.
  * unfold RH_TCBList_ECBList_Q_P in *.
    destruct H. split.
    + intros.
      pose proof (H eid x y qwaitset tid0 H5) as H.
      simpljoin.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice.
      - rewrite H7. rewrite TcbMod.map_get_set.
        unfold get in H; simpl in H. rewrite H7 in H0.
        rewrite H in H0. inverts H0. eauto.
      - rewrite TcbMod.map_get_set'. eauto. auto.
    + intros.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice.
      - eapply H4. rewrite H6 in H5. rewrite TcbMod.map_get_set in H5.
        inverts H5. unfold get in H0; simpl in H0.
        rewrite H6 in H0. eauto.
      - eapply H4. rewrite TcbMod.map_get_set' in H5.
        unfold get; simpl. eauto. auto.
  * unfold RH_TCBList_ECBList_SEM_P in *.
    destruct H1. split.
    + intros.
      pose proof (H1 eid n wls tid0 H5) as H1.
      simpljoin.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice.
      - rewrite H7. rewrite TcbMod.map_get_set.
        unfold get in H1; simpl in H1. rewrite H7 in H0.
        rewrite H1 in H0. inverts H0. eauto.
      - rewrite TcbMod.map_get_set'. eauto. auto.
    + intros.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice.
      - eapply H4. rewrite H6 in H5. rewrite TcbMod.map_get_set in H5.
        inverts H5. unfold get in H0; simpl in H0.
        rewrite H6 in H0. eauto.
      - eapply H4. rewrite TcbMod.map_get_set' in H5.
        unfold get; simpl. eauto. auto.
  * unfold RH_TCBList_ECBList_MBOX_P in *.
    destruct H2. split.
    + intros.
      pose proof (H2 eid n wls tid0 H5) as H2.
      simpljoin.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice.
      - rewrite H7. rewrite TcbMod.map_get_set.
        unfold get in H2; simpl in H2. rewrite H7 in H0.
        rewrite H2 in H0. inverts H0. eauto.
      - rewrite TcbMod.map_get_set'. eauto. auto.
    + intros.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice.
      - eapply H4. rewrite H6 in H5. rewrite TcbMod.map_get_set in H5.
        inverts H5. unfold get in H0; simpl in H0.
        rewrite H6 in H0. eauto.
      - eapply H4. rewrite TcbMod.map_get_set' in H5.
        unfold get; simpl. eauto. auto.
  * unfold RH_TCBList_ECBList_MUTEX_P in *.
    destruct H3. split.
    + intros.
      pose proof (H3 eid n1 n2 wls tid0 H5) as H3.
      simpljoin.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice.
      - rewrite H8. rewrite TcbMod.map_get_set.
        unfold get in H3; simpl in H3. rewrite H8 in H0.
        rewrite H3 in H0. inverts H0. eauto.
      - rewrite TcbMod.map_get_set'. eauto. auto.
    + split. intros.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice. destruct H4.
      - eapply H4. rewrite H6 in H5. rewrite TcbMod.map_get_set in H5.
        inverts H5. unfold get in H0; simpl in H0.
        rewrite H6 in H0. eauto.
      - eapply H4. rewrite TcbMod.map_get_set' in H5.
        unfold get; simpl. eauto. auto.
    - destruct H4. unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
      intros.
      pose proof (H5 eid pr wls opr tid0 H6) as H5.
      simpljoin.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice. rewrite H7. rewrite TcbMod.map_get_set.
      eauto. rewrite TcbMod.map_get_set'. eauto. auto.
Qed.

Ltac sep_get_rv1:=
  match goal with
  | H: ?s |= ?P |- ?s |= Rv (evar ?x) @ _ == _ =>
  match find_lvarmapsto P x with
    | some ?m =>
      eapply lvar_rv;
        [ sep lift m in H; exact H
        (*| auto*)
        | simpl; auto ]
    | none _ =>
      match find_dom_lenv P with
        | (none _, _) => fail 1
        | (some ?m, Some ?l) =>
          let ret1 := constr:(var_notin_dom x l) in
          let ret2 := (eval compute in ret1) in
          match ret2 with
            | true =>
              match find_gvarmapsto P x with
                | none _ => fail 2
                | some ?n =>
                  eapply gvar_rv;
                    [ sep lifts (m::n::nil)%list in H; exact H
                    | simpl; auto
                    (*| auto*)
                    | simpl; auto ]
              end
            | false => fail 3
          end
      end
  end
end.

Lemma TaskSuspendProof:
    forall  vl p r tid, 
      Some p =
      BuildPreA' os_api OSTaskSuspend tasksuspendapi vl OSLInv tid init_lg->
      Some r =
      BuildRetA' os_api OSTaskSuspend tasksuspendapi vl OSLInv tid init_lg->
      exists t d1 d2 s,
        os_api OSTaskSuspend = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|- tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  
  (* If (prio′ ==ₑ ′OS_IDLE_PRIO) { *)
  lzh_hoare_if; pure_auto.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_tasksus_prio_idle.
  can_change_aop_solver.
  rewrite Int.eq_sym in LHift_true.
  auto.
  hoare forward.

  (* If (prio′ ≥ ′OS_LOWEST_PRIO) { *)
  lzh_hoare_if; pure_auto.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_tasksus_prio_invalid.
  can_change_aop_solver.
  pure_auto.
  hoare forward.

  (* ENTER_CRITICAL;ₛ *)
  hoare forward prim.
  unfold AOSTCBList.
  hoare_split_pure_all.

  hoare unfold.

  (* ptcb ′ =ₑ OSTCBPrioTbl ′ [prio ′];ₛ *)
  rename v'7 into ptbl.
  rename v'13 into rtbl.
  rename v'15 into ecbls.
  rename v'16 into tcbls.
  rename v'18 into vhold.
  assert (Int.unsigned i < 64)%Z. {
    destruct Hif_false0; 
    repeat match goal with
    | H : context [if ?x then _ else _ ] |- _ =>
      let y := fresh in  remember x as y ; destruct y; simpl in H; tryfalse
    end.
    clear - HeqH11.
    unfold OS_LOWEST_PRIO in HeqH11.
    int auto.
  }
  assert (rule_type_val_match OS_TCB ∗
  (nth_val' (Z.to_nat (Int.unsigned i)) ptbl) = true). {
    apply array_type_vallist_match_imp_rule_type_val_match.
    rewrite H9.
    clear - H10; handle_z2n_lt_nat.
    auto.
  }

  clear Hif_false0.

  hoare forward.
  pure_auto.
  auto.

  unfold1 tcbdllseg.
  unfold1 dllseg.
  unfold node.
  hoare normal pre.
  hoare_split_pure_all.
  simpljoin.
  inverts H12.
  
  lets bb: OSTCBflag_des H16.
  simpljoin.
  
  (* The currently running task is in TCB list. *)
  assert (
    exists t sus, TcbMod.get tcbls (v'9, Int.zero) =
    Some (x5, t, x2, sus)
  ). {
    unfold1 TCBList_P in H3.
    simpljoin.
    unfolds in H18.
    destruct x13. destruct p. destruct p.
    simpljoin.
    inverts H20.
    unfolds in H22. simpl in H22.
    inverts H18.
    inverts H3.
    eexists. eexists.
    unfold join,sig,get in *; simpl in *.
    unfold join,sig,get in *; simpl in *.
    go.
  }

  destruct H12 as (st & sus & tcbmod_get).

  (* If (ptcb ′ ==ₑ NULL) *)
  hoare forward.
  destruct (nth_val' (Z.to_nat (Int.unsigned i)) ptbl); auto.
  simpl val_eq.
  destruct a.
  simpl val_inj.
  auto.

  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_tasksus_no_such_tcb.
  can_change_aop_solver.
  {
    intro.
    apply H12.
    destruct H11.
    2: {
      simpljoin.
      rewrite H11.
      simpl.
      destruct x12.
      reflexivity.
    }
    false.
    simpljoin.
    unfolds in H8.
    simpljoin.
    lets bb: H14 H13.
    simpljoin.
    unfold nat_of_Z in H21.
    apply nv'2nv in H11.
    rewrite H11 in H21.
    inverts H21.
    intro; tryfalse.
  }
  
  (* EXIT_CRITICAL;ₛ *)
  hoare forward prim.
  unfold AOSTCBList.
  sep pauto; eauto.
  sep cancel tcbdllflag.
  unfold tcbdllseg.
  unfold1 dllseg.
  sep pauto.
  sep cancel dllseg.
  sep cancel dllseg.
  unfold node.
  sep pauto.
  sep cancel Astruct.
  unfold AOSTCBPrioTbl.
  sep pauto.
  instantiate (1:=
  LV ptcb @ OS_TCB ∗ |-> nth_val' (Z.to_nat (Int.unsigned i)) ptbl **
  LV x @ OS_TCB ∗ |-> v'1 **
        LV pevent @ OS_EVENT ∗ |-> v' **
        LV prio @ Int8u |-> Vint32 i **
        A_dom_lenv
          ((prio, Int8u)
           :: (pevent, OS_EVENT ∗)
              :: (ptcb, OS_TCB ∗) :: (x, OS_TCB ∗) :: nil)).
  sep auto.
  pauto.
  go.
  go.
  go.
  go.

  (* RETURN ′ OS_TASK_SUSPEND_PRIO *)
  hoare forward.
  hoare forward.
  hoare_split_pure_all.

  hoare unfold.
  assert (exists p, nth_val' (Z.to_nat (Int.unsigned i)) ptbl = Vptr p). {
    destruct (nth_val' (Z.to_nat (Int.unsigned i)) ptbl); eauto.
    destruct H12. discriminate.
    destruct H12. discriminate.
    destruct H12. discriminate.
    simpl in H11. destruct H11.
    discriminate. discriminate.
  }
  clear H11 H12.
  simpljoin.
  rewrite H11.
  eapply seq_rule.
  {
    eapply ift_rule''.
    intros.
    eapply symbolic_lemmas.bop_rv.
    sep_get_rv1.
    eapply symbolic_lemmas.addrof_gvar_rv.
    gen_notin_lenv H12 OSPlaceHolder.
    eapply symbolic_lemmas.dom_lenv_imp_notin_lenv.
    eauto.
    sep cancel A_dom_lenv.
    sep cancel Agvarenv'.
    eauto.
    eauto.
    simpl.
    destruct x10. destruct vhold.
    destruct ( Int.eq i0 i1 ); destruct (peq b b0); simpl; intro; tryfalse.
    simpl.
    eauto.
    hoare unfold.
    instantiate (1:=Afalse).
    hoare abscsq.
    apply noabs_oslinv.
    eapply absimp_tasksus_no_such_tcb.
    go.
    {
      intro.
      apply H12.
      assert (x10 <> vhold \/ x10 = vhold).
      tauto.
      destruct H14.
      simpl.
      destruct x10; destruct vhold.
      remember (peq b b0).
      destruct s.
      subst.
      rewrite Int.eq_false.
      reflexivity.
      intro; tryfalse.
      reflexivity.
      subst x10.
      simpl.
      false.
      simpljoin.
      unfolds in H8.
      simpljoin.
      lets bb: H14 H13.
      simpljoin.
      unfold nat_of_Z in H21.
      apply nv'2nv in H11.
      rewrite H11 in H21.
      inverts H21.
      apply H22; reflexivity.
      intro; tryfalse.
    }

    hoare forward prim.
    unfold AOSTCBPrioTbl.
    unfold AOSTCBList.
    sep pauto.
    sep cancel tcbdllflag.
    unfold tcbdllseg.
    sep cancel 5%nat 1%nat.
    
    unfold1 dllseg.
    unfold node.
    sep pauto.
    sep cancel Astruct.
    sep cancel dllseg.
    sep cancel 2%nat 1%nat .
    sep cancel 2%nat 1%nat.
    eauto.
    go.
    go.
    go.
    go.
    go.
    go.
    go.
    hoare forward.
  }

  hoare forward.
  hoare unfold.

  Set Nested Proofs Allowed.

  (* In taskdelete.v *)
  Lemma valinjbopevallemma:
  forall x v'19, val_inj (bop_eval (Vptr x) (Vptr v'19) OS_TCB ∗ (Int8u) ∗ oeq) =
      Vint32 Int.zero \/
      val_inj (bop_eval (Vptr x) (Vptr v'19) OS_TCB ∗ (Int8u) ∗ oeq) =
      Vnull -> x <> v'19.
  Proof.
    intros.
    destruct H.
    simpl in H.
    destruct x; destruct v'19.
    intro.
    inverts H0.
    rewrite peq_true in H.
    rewrite Int.eq_true in H.
    inverts H.
    simpl in H.
    destruct x; destruct v'19.
    destruct (peq b b0); destruct (Int.eq i i0); tryfalse.
  Qed.

  apply valinjbopevallemma in H12.
  
  (* OSRdyTbl ′ [ptcb ′ → OSTCBY] &= ∼ ptcb ′ → OSTCBBitX *)
  rename v'9 into cur_tcb_blk.
  rename x10 into tosusptr.
  
  assert (
  exists st0 m sus0, TcbMod.get tcbls tosusptr = Some (i, st0, m, sus0)). {
    unfolds in H8.
    simpljoin.
    apply H8.
    splits.
    clear; int auto.
    lia.
    unfold nat_of_Z.
    eapply nv'2nv.
    assumption.
    intro; tryfalse.
    assumption.
  }
  simpljoin.
  rename x into st0.
  rename x0 into m0.
  rename x10 into sus0.
  rename v'10 into l1.
  rename v'12 into l2.

  remember (v'7 :: v'21 :: x1 :: x2
           :: x3 :: x4 :: Vint32 x5 :: x6 :: x7 :: x8 :: x9 :: nil) as tcbcur.
  protect Heqtcbcur.

  eapply backward_rule1.
  intros.
  instantiate (1 := (
    [|ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'8 (l1++tcbcur::l2)|] **
    tcbdllseg v'8 Vnull v'22 Vnull (l1++tcbcur::l2) **
    [|TCBList_P v'8 (l1++tcbcur::l2) rtbl tcbls|] **

    <|| tasksuspendcode (Vint32 i :: nil) ||>  **
    LV ptcb @ OS_TCB ∗ |-> Vptr tosusptr **
    PV vhold @ Int8u |-> v'25 **
    GV OSTCBList @ OS_TCB ∗ |-> v'8 **
    GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
    AOSEventFreeList v'2 **
    AOSQFreeList v'3 **
    AOSQFreeBlk v'4 **
    AECBList v'6 v'5 ecbls tcbls **
    AOSMapTbl **
    AOSUnMapTbl **
    GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) ptbl **
    G& OSPlaceHolder @ Int8u == vhold **
    AOSIntNesting **
    AOSTCBFreeList v'19 v'20 **
    GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE) rtbl **
    AOSRdyGrp v'14 **
    AOSTime (Vint32 v'17) **
    HECBList ecbls **
    HTCBList tcbls **
    HTime v'17 **
    HCurTCB (cur_tcb_blk, Int.zero) **
    AGVars **
    A_isr_is_prop **
    tcbdllflag v'8
      (l1 ++ tcbcur :: l2) **
    p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
    Aisr empisr **
    Aie false **
    Ais nil **
    Acs (true :: nil) **
    atoy_inv' **
    LV x @ OS_TCB ∗ |-> v'1 **
    LV pevent @ OS_EVENT ∗ |-> v' **
    LV prio @ Int8u |-> Vint32 i **
    A_dom_lenv
      ((prio, Int8u)
       :: (pevent, OS_EVENT ∗)
          :: (ptcb, OS_TCB ∗) :: (x, OS_TCB ∗) :: nil)    
  )).

  eapply tcbdllseg_combine.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep pauto.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 2%nat.
  sep cancel 1%nat 1%nat.
  sep pauto.
  go.
  go.
  go.
  unprotect Heqtcbcur; rewrite Heqtcbcur; eauto.
  unprotect Heqtcbcur; rewrite Heqtcbcur; eauto.
  
  hoare_split_pure_all.
  assert (ptr_in_tcbdllseg (Vptr tosusptr) v'8 (l1++tcbcur ::l2)).

  (* In taskdelete.v *)
  Lemma tcbget_ptr_in_tcblist:
     forall tcblst head rtbl tcbmap x xx,
      TCBList_P head tcblst rtbl tcbmap ->
      get tcbmap x = Some xx ->
      ptr_in_tcbdllseg (Vptr x) head tcblst.
  Proof.
    induction tcblst.
    intros.
    simpl in H.
    subst tcbmap.
    rewrite map_emp_get in H0.
    inverts H0.
    intros.
    unfold1 ptr_in_tcbdllseg.
    remember (beq_val (Vptr x) head).
    destruct b.
    auto.
    unfold1 TCBList_P in H.
    simpljoin.
    rewrite H1.
    eapply IHtcblst.
    exact H4.
    assert ( x <> x0).
    intro.
    subst x0.
    rewrite beq_val_true in Heqb.
    tryfalse.
    unfold join,get,sig in *; simpl in *.
    eapply TcbMod.join_get_or in H2.
    destruct H2; eauto.
    rewrite TcbMod.get_a_sig_a' in H2.
    inverts H2.
    go.
    eauto.
  Qed.

  eapply tcbget_ptr_in_tcblist.
  eauto.
  eauto.

  eapply backward_rule1.
  intros.
  eapply tcbdllseg_split' in H24.
  eauto.
  exact H23.
  eauto.
  clear Heqtcbcur.
  remember (l1  ++ tcbcur :: l2) as tcblst.
  protect Heqtcblst.
  hoare unfold.

  (* Remove the original splitting *)
  clear dependent v'23.
  clear dependent v'24.

  destruct v'10.
  {
    unfold tcbdllseg.
    simpl.
    hoare unfold.
    inverts H0.
  }

  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  hoare_split_pure_all.
  simpljoin.
  inverts H0.
  rename v'16 into tosusblock.
  hoare unfold.

  lets backup : H27.
  unfold1 TCBList_P in H27.
  simpljoin.
  unfold TCBNode_P in H49.
  destruct x11; destruct p; destruct p.
  simpljoin.
  unfold RL_TCBblk_P in H52.
  simpljoin.
  inverts H52; inverts H54; inverts H55; inverts H56;
  inverts H57; inverts H58; inverts H65.

  change ((OSRdyTbl ′ [ptcb ′ → OSTCBY] &= ∼ ptcb ′ → OSTCBBitX;ₛ
  If(OSRdyTbl ′ [ptcb ′ → OSTCBY] ==ₑ ′ 0)
  {OSRdyGrp ′ &= ∼ ptcb ′ → OSTCBBitY})) with (
    inline_call inline_bittbl_clearbit
    ((OSRdyGrp ′) :: (OSRdyTbl ′) :: (ptcb ′ → OSTCBBitX) ::
    (ptcb ′ → OSTCBBitY) :: (ptcb ′ → OSTCBY) :: nil)).

  unfold GAarray.
  unfold AOSRdyGrp.
  unfold Agvarmapsto at 3.
  hoare unfold.

  Ltac inline_forward :=
    match goal with
      | |- {| _ , _ , _, _, _, _|} |- _ {{ _ }} inline_call ?inline_record _ {{ _ }} => eapply backward_rule2; [eapply (inl_proof inline_record)  | intro;intros;inline_pre_unfolder inline_record |idtac..]
    end.
  eapply seq_rule.

  inline_forward.
  2: {
    sep pauto.
    sep cancel Aop.
    sep cancel (2%nat) (1%nat).
    sep cancel (3%nat) (1%nat).
    eauto.

    instantiate (1 := p).
    lia.
    go.
    math simpls.
    go.
    go.
    clear - H67.
    mauto.

    2: go.

    intros.
    lrv_solver.
    go.
    go.
    go.
  }
  1: {
    intros.
    linv_solver.
  }

  inline_post_unfolder inline_bittbl_clearbit.
  hoare unfold.
  inverts H2.
  eapply backward_rule1.
  intros.
  sep lift 2%nat in H2.
  sep lift 5%nat in H2.
  eapply GrefArray in H2.
  sep lift 3%nat in H2.
  sep lift 4%nat in H2.
  apply GrefPV in H2.
  sep lift 5%nat in H2.
  sep lift 5%nat in H2.
  eapply GrefArray in H2.
  eauto.
  hoare unfold.

  (* ptcb ′ → OSTCBStat =ₑ ptcb ′ → OSTCBStat |ₑ ′ OS_STAT_SUSPEND;ₛ*)
  hoare forward.
  go.

  (* Now we must recover the split according to the current task *)
  remember (
    Vint32 v'39
      :: Vint32 (Int.and v'39 (Int.repr 7))
        :: Vint32 (Int.shru v'39 (Int.repr 3))
          :: Vint32 (Int.shl (Int.repr 1) (Int.and v'39 (Int.repr 7)))
            :: Vint32 (Int.shl (Int.repr 1) (Int.shru v'39 (Int.repr 3)))
              :: nil) as susblk.

  rename v'9 into l1'.
  rename v'10 into l2'.
  rename v'26 into rtbl.

  remember (update_nth_val
  (Z.to_nat (Int.unsigned (Int.shru v'39 (Int.repr 3)))) rtbl
  (val_inj
     (and (Vint32 v'37)
        (Vint32
           (Int.not
              (Int.shl (Int.repr 1) (Int.and v'39 (Int.repr 7)))))))) as rtbl'.
  protect Heqrtbl'.

  remember (TcbMod.set tcbls (tosusblock, Int.zero) (i, st0, m0, true))
  as tcbls'.
  protect Heqtcbls'.

  assert ((v'39, t, m, s) = (i, st0, m0, sus0)) as abstcbeq. {
    clear - H27 H25 H13.
    assert (TcbMod.get v'13 (tosusblock, Int.zero) = Some (v'39, t, m, s)). {
      unfolds in H27.
      unfold join, sig in H27. simpl in H27.
      apply TcbMod.join_sig_get in H27; eauto.
    }
    assert (TcbMod.get tcbls (tosusblock, Int.zero) = Some (v'39, t, m, s)). {
      eapply TcbMod.join_get_get_r; eauto.
    }
    rewrite H0 in H13.
    invert H13.
    auto.
  }

  assert (prio_neq_cur tcbls (tosusblock, Int.zero) v'39) as Hprio. {
    eapply R_PrioTbl_P_impl_prio_neq_cur.
    auto. eauto.
    inverts abstcbeq. eauto.
  }

  assert (prio_neq_cur v'13 (tosusblock, Int.zero) v'39) as Hprio1. {
    unfolds. unfolds in Hprio.
    intros. eapply Hprio; eauto.
    clear - H51 H25.
    eapply TcbMod.join_get_r; eauto.
  }

  assert (prio_neq_cur v'12 (tosusblock, Int.zero) v'39) as Hprio2. {
    unfolds. unfolds in Hprio.
    intros. eapply Hprio; eauto.
    clear - H51 H25.
    eapply TcbMod.join_get_l; eauto.
  }

  assert (TCBList_P (Vptr (tosusblock, Int.zero))
    ((x0 :: v'11 :: x23 :: m :: Vint32 i13 :: Vint32 (Int.or x22 ($ OS_STAT_SUSPEND))
      :: susblk) :: l2') rtbl'
      (TcbMod.set v'13 (tosusblock, Int.zero) (i, st0, m0, true))).
  {
    unfold1 TCBList_P.
    do 4 eexists. splits. auto.
    unfolds. simpl. auto.
    eapply tcbjoin_set. eauto.
    rewrite Heqsusblk.
    inverts abstcbeq.
    unfolds.
    unfold1 TCBList_P in backup.
    simpljoin. unfolds in H63. destruct x13; destruct p; destruct p.
    destructs H63.
    splits; auto.
    apply RL_TCBblk_P_suspend; auto. 
    eapply R_TCB_Status_P_suspend; eauto.
    rewrite Heqrtbl'.
    apply update_rtbl_tcblist_hold; eauto.
    apply nv'2nv; auto.
    unfolds in Hprio1.
    intros.
    lets Has : tcbjoin_get_getneq H27 H2.
    destruct Has.
    eapply Hprio1; eauto.
  }

  assert (TCBList_P v'8 l1' rtbl' v'12). {
    rewrite Heqrtbl'.
    apply update_rtbl_tcblist_hold; eauto.
    apply nv'2nv; auto.
    intros.
    unfolds in Hprio2.
    eapply Hprio2. 2: apply H51.
    eapply tcbjoin_join_get_neq; eauto.
  }

  assert (TcbMod.join v'12 (TcbMod.set v'13 (tosusblock, Int.zero) (i, st0, m0, true))
  tcbls'). {
    unprotect Heqtcbls'.
    rewrite Heqtcbls'.
    eapply TcbMod.join_set_r. auto.
    clear - H27.
    unfold TcbMod.indom. eexists.
    unfolds in H27.
    unfold join, sig in H27; simpl in H27.
    apply TcbMod.join_sig_get in H27. eauto.
  }

  (* Recombine the tcbdllseg *)
  eapply backward_rule1.
  intros.
  instantiate (1 := (
    [|ptr_in_tcbdllseg (Vptr (tosusblock, Int.zero)) v'8 (l1'++(x0
    :: v'11
       :: x23
          :: m
             :: Vint32 i13
                :: Vint32 (Int.or x22 (Int.repr OS_STAT_SUSPEND))
                   :: susblk)::l2')|] **
    tcbdllseg v'8 Vnull v'22 Vnull (l1'++(x0
    :: v'11
       :: x23
          :: m
             :: Vint32 i13
                :: Vint32 (Int.or x22 (Int.repr OS_STAT_SUSPEND))
                   :: susblk)::l2') **
    [|TCBList_P v'8 (l1'++(x0
    :: v'11
       :: x23
          :: m
             :: Vint32 i13
                :: Vint32 (Int.or x22 (Int.repr OS_STAT_SUSPEND))
                   :: susblk)::l2') rtbl' tcbls'|] **

    <|| tasksuspendcode (Vint32 i :: nil) ||>  **
    LV ptcb @ OS_TCB ∗ |-> Vptr (tosusblock, Int.zero) **
    GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) ptbl **
    GV OSRdyGrp @ Int8u |-> Vint32 v'36 **
    GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE) rtbl' **
    PV vhold @ Int8u |-> v'25 **
    GV OSTCBList @ OS_TCB ∗ |-> v'8 **
    GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
    AOSEventFreeList v'2 **
    AOSQFreeList v'3 **
    AOSQFreeBlk v'4 **
    AECBList v'6 v'5 ecbls tcbls' **
    AOSMapTbl **
    AOSUnMapTbl **
    G& OSPlaceHolder @ Int8u == vhold **
    AOSIntNesting **
    AOSTCBFreeList v'19 v'20 **
    AOSTime (Vint32 v'17) **
    HECBList ecbls **
    HTCBList tcbls **
    HTime v'17 **
    HCurTCB (cur_tcb_blk, Int.zero) **
    AGVars **
    A_isr_is_prop **
    tcbdllflag v'8
      (l1' ++
      (x0 :: v'11 :: x23 :: m :: Vint32 i13 :: Vint32 x22 :: susblk) :: l2') **
    p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
    Aisr empisr **
    Aie false **
    Ais nil **
    Acs (true :: nil) **
    atoy_inv' **
    LV x @ OS_TCB ∗ |-> v'1 **
    LV pevent @ OS_EVENT ∗ |-> v' **
    LV prio @ Int8u |-> Vint32 i **
    A_dom_lenv
      ((prio, Int8u)
      :: (pevent, OS_EVENT ∗) :: (ptcb, OS_TCB ∗) :: (x, OS_TCB ∗) :: nil)  )).

  eapply tcbdllseg_combine.
  sep pauto.
  sep cancel tcbdllflag.
  sep cancel Aop.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep pauto.
  sep cancel Astruct.
  sep cancel dllseg.
  sep cancel dllseg.
  unfold AECBList.
  unfold AECBList in H63.
  sep pauto.
  {
    unprotect Heqtcbls'. rewrite Heqtcbls'.
    apply ECBList_P_preserve; eauto.
  }
  auto.
  auto.
  
  Open Scope Z_scope.
  Open Scope int_scope.
  assert ((Int.unsigned (Int.or x22 (Int.repr OS_STAT_SUSPEND))) <= 255). {
    apply int_unsigned_or_prop.
    auto. unfold OS_STAT_SUSPEND; clear; int auto.
  }
  go.

  eauto.
  eauto.
  auto.

  protect Heqsusblk.
  hoare unfold.

  (* tcbcur is still in the new array *)
  assert (ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'8
    (l1'++(x0
    :: v'11
       :: x23
          :: m0
             :: Vint32 i13
                :: Vint32 (Int.or x22 (Int.repr OS_STAT_SUSPEND))
                   :: susblk)::l2')).
  eapply ptr_in_tcbdllseg_preserve.
  apply H14.
  unfolds; simpl; auto.
  
  eapply backward_rule1.
  intros.
  eapply tcbdllseg_split' in H69.
  eauto.
  eauto.
  instantiate (1 := tcbls').
  instantiate (1 := rtbl').
  assumption.

  hoare unfold.
  destruct v'10.
  {
    unfold tcbdllseg.
    simpl.
    hoare unfold.
    inverts H73.
  }

  (* Fix abstract operation *)
  hoare abscsq.
  apply noabs_oslinv.
  eapply abs_imp_tasksus_succ.
  go.
  apply H13.
  
  (* EXIT_CRITICAL;ₛ *)
  hoare forward prim.

  unfold AOSTCBPrioTbl.
  sep pauto.
  unfold AOSTCBList.
  sep pauto.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  sep cancel (4%nat) (1%nat).
  sep cancel (5%nat) (2%nat).
  unfold AOSRdyTblGrp.
  sep pauto.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  sep pauto.
  unfold AECBList.
  unfold AECBList in H73.
  sep pauto.
  sep cancel evsllseg.

  instantiate (1 := 
  LV ptcb @ OS_TCB ∗ |-> Vptr (tosusblock, Int.zero) **
         LV os_code_defs.x @ OS_TCB ∗ |-> v'1 **
         LV pevent @ OS_EVENT ∗ |-> v' **
         LV prio @ Int8u |-> Vint32 i **
         A_dom_lenv
           ((prio, Int8u)
            :: (pevent, OS_EVENT ∗)
               :: (ptcb, OS_TCB ∗) :: (os_code_defs.x, OS_TCB ∗) :: nil)).
  sep pauto.
  {
    eapply tcbdllflag_hold.
    2: eauto.
    rewrite <- H69. rewrite Heqsusblk.
    apply eq_dllflag_set.
    unfold V_OSTCBNext; simpl; auto.
    unfold V_OSTCBflag; simpl; auto.
  }

  {
    unprotect Heqtcbls'.
    rewrite Heqtcbls' in H74.
    auto.
  }

  split.
  auto.
  apply H57; auto.
  rewrite Int.eq_sym. assumption.
  eauto.
  eauto.
  {
    unfold join; simpl.
    rewrite Heqtcbls' in H70.
    auto.
  }

  eapply R_PrioTbl_P_suspend; eauto.

  {
    unprotect Heqrtbl'.
    rewrite Heqrtbl'.
    eapply rtbl_remove_RL_RTbl_PrioTbl_P_hold; eauto.
    clear - H49. apply nv'2nv. auto. auto.
  }

  {
    clear - H5.
    unfold RH_CurTCB in *.
    simpljoin.
    assert ((tosusblock, Int.zero) = (cur_tcb_blk, Int.zero) \/
            (tosusblock, Int.zero) <> (cur_tcb_blk, Int.zero)) as choice by tauto.
    destruct choice.
    do 4 eexists. rewrite H0. rewrite TcbMod.map_get_set. eauto.
    do 4 eexists. rewrite TcbMod.map_get_set'.
    unfold get in H; simpl in H. eauto. auto. 
  }

  eapply RH_TCBList_ECBList_P_suspend; eauto.
  go.

  hoare forward.
  sep cancel Aop.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel p_local.
  eauto.
  unfold isflag. auto.
  go.
  {
    intros.
    exists init_lg.
    sep pauto.
  }
  {
    intros.
    sep destruct H73.
    exists (logic_val x11 :: nil).
    sep pauto.
  }

  unfold OS_SchedPost.
  unfold getasrt.
  unfold OS_SchedPost'.
  hoare unfold.
  hoare forward.
  inverts H73.
  auto.
Qed.

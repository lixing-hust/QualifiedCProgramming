Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import include_frm.
Require Import NPeano.

Require Import os_q_cap.
Require Import abs_op.
Require Import ifun_spec.


Require Import include_frm.
Require Import os_inv.
Require Import ucos_frmaop.
Require Import abs_step.
Require Import init_spec.

Require Import hoare_tactics.
Require Import pure_auto.
Require Import ucos_pauto.
Require Import sep_auto.
Require Import seplog_tactics.
Require Import seplog_lemmas.
Require Import sep_cancel_ext.
Require Import derived_rules.
Require Import hoare_conseq.
Require Import ucos_forward.
Require Import math_auto.

Require Import partition_common.
Require Import part_pos_rgn_spec.
Require Import part_pos_rgn_proof.
Require Import partinv_lemmas.
Require Import protect.

Require Import sem_lab.
Require Import symbolic_lemmas.
Require Import Aarray_new_common.
Require Import pos_list_common.
Require Import ev_aux_code.
Require Import sem_common.
Require Import gjb_common.
Require Import gjb_q_common.
Require Import evauxvar_lemmas.
Require Import evaux_pure.

Require Import abs_infer_abt.
Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Open Scope int_scope.
Open Scope Z_scope.
Open Scope code_scope.
Open Scope list_scope.

Lemma mqcreate_absimp_max_msgs_err_abt:
  forall max_msgs rv P sch v1 v3 v4 v5 v6  vr_temp_dom vr_temp_num,
   Int.ltu max_msgs Int.zero = true ->
    rv <> (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqcreate ( v1 :: Vint32 max_msgs :: v3 :: v4:: v5:: v6 ::  rv :: vr_temp_dom :: vr_temp_num :: nil)  ||> ** P) 
      (<|| ABORT ||> ** P). 
Proof.
  introv Hneq Hrv Hcaop. 
  eapply absinfer_trans.
  eapply absinfer_choice1. try eauto. 
  instantiate (1:= P). can_change_aop_solver. auto.
  eapply absinfer_abt;pure_auto.
  absimp_abt_solver.
Qed.

Lemma mqcreate_absimp_max_msgs_err:
  forall max_msgs rv P sch v1 v3 v4 v5 v6 vr_temp_dom vr_temp_num ,
   Int.ltu max_msgs Int.zero = true -> 
    rv = (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqcreate ( v1 :: Vint32 max_msgs :: v3 :: v4:: v5:: v6 ::  rv :: vr_temp_dom :: vr_temp_num :: nil)  ||> ** P) 
      (<|| END (Some (Vint32 (Int.mone))) ||> ** P). 
Proof.
  infer_solver 0%nat. 
Qed.


Lemma mqcreate_absimp_msg_size_err_abt:
  forall msg_size rv P sch v1 v2 v4 v5 v6 vr_temp_dom vr_temp_num,
   Int.ltu msg_size Int.zero = true -> 
    rv <> (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqcreate (v1 :: v2:: Vint32 msg_size :: v4 :: v5 :: v6 ::  rv :: vr_temp_dom :: vr_temp_num :: nil) ||> ** P) 
      (<|| ABORT ||> ** P). 
Proof.
  introv Hneq Hrv Hcaop. 
  do 1 (eapply absinfer_trans; try (eapply absinfer_choice2; try eauto)).
  do 1 (eapply absinfer_trans; try (eapply absinfer_choice1; try eauto)).
  eapply absinfer_abt;pure_auto.
  absimp_abt_solver.
Qed.

Lemma mqcreate_absimp_msg_size_err:
  forall msg_size rv P sch v1 v2 v4 v5 v6 vr_temp_dom vr_temp_num,
   Int.ltu msg_size Int.zero = true -> 
    rv = (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqcreate (v1 :: v2:: Vint32 msg_size :: v4 :: v5 :: v6 ::  rv :: vr_temp_dom :: vr_temp_num :: nil) ||> ** P) 
      (<|| END (Some (Vint32 (Int.mone))) ||> ** P). 
Proof. 
  infer_solver 1%nat.  
Qed.

Lemma mqcreate_absimp_mq_blockflag_err_abt:
  forall mq_blockflag rv P sch  v2 v3 v4 v5 v6 vr_temp_dom vr_temp_num,
   ( Int.eq mq_blockflag Int.zero = false /\ Int.eq mq_blockflag (Int.repr O_NONBLOCK) = false) -> 
    rv <> (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqcreate (Vint32 mq_blockflag ::v2::v3  :: v4 :: v5 :: v6 ::rv :: vr_temp_dom :: vr_temp_num :: nil)  ||> ** P) 
      (<|| ABORT ||> ** P). 
Proof.
  introv Hneq Hrv Hcaop. 
  do 2 (eapply absinfer_trans; try (eapply absinfer_choice2; try eauto)).
  do 1 (eapply absinfer_trans; try (eapply absinfer_choice1; try eauto)).
  eapply absinfer_abt;pure_auto.
  absimp_abt_solver.
Qed.

Lemma mqcreate_absimp_mq_blockflag_err:
  forall mq_blockflag rv P sch  v2 v3 v4 v5 v6 vr_temp_dom vr_temp_num,
   ( Int.eq mq_blockflag Int.zero = false /\ Int.eq mq_blockflag (Int.repr O_NONBLOCK) = false) -> 
    rv = (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqcreate (Vint32 mq_blockflag ::v2::v3  :: v4 :: v5 :: v6 ::rv :: vr_temp_dom :: vr_temp_num :: nil)  ||> ** P) 
      (<|| END (Some (Vint32 (Int.mone))) ||> ** P). 
Proof. 
  infer_solver 2%nat.  
Qed.

Lemma mqcreate_absimp_waitq_type_err_abt:
  forall waitq_type rv P sch v1 v2 v3  v5 v6 vr_temp_dom vr_temp_num,
    Int.eq waitq_type (Int.repr PTHREAD_WAITQ_PRIO) = false -> 
    rv <> (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqcreate (v1::v2::v3::Vint32 waitq_type ::v5 :: v6::  rv :: vr_temp_dom :: vr_temp_num :: nil)  ||> ** P) 
      (<|| ABORT ||> ** P). 
Proof.
  introv Hneq Hrv Hcaop. 
  do 3 (eapply absinfer_trans; try (eapply absinfer_choice2; try eauto)).
  do 1 (eapply absinfer_trans; try (eapply absinfer_choice1; try eauto)).
  eapply absinfer_abt;pure_auto.
  absimp_abt_solver.
Qed.

Lemma mqcreate_absimp_waitq_type_err:
  forall waitq_type rv P sch v1 v2 v3  v5 v6 vr_temp_dom vr_temp_num,
    Int.eq waitq_type (Int.repr PTHREAD_WAITQ_PRIO) = false -> 
    rv = (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqcreate (v1::v2::v3::Vint32 waitq_type ::v5 :: v6::  rv :: vr_temp_dom :: vr_temp_num :: nil)  ||> ** P) 
      (<|| END (Some (Vint32 (Int.mone))) ||> ** P). 
Proof. 
  infer_solver 3%nat.  
Qed.

Lemma mqcreate_absimp_iserr:
forall sch P v1 v2 v3 v4 v5 v6 rv vr_temp_dom vr_temp_num,
    can_change_aop P -> 
    absinfer sch 
      (<|| mqcreate (v1::v2::v3::v4 ::v5 :: v6::  rv :: vr_temp_dom :: vr_temp_num :: nil)  ||>  ** P)
      (<|| END (Some  (Vint32 (Int.mone))) ||> ** P).
Proof.
 infer_solver 4%nat.  
Qed. 

Lemma mqcreate_absimp_pos_abt:
  forall sch P qtls posv left right s cpn idx,
    can_change_aop P ->
    left = OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned idx ->
    right = OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned idx + 1) ->
    (~(exists pos wtype flag maxm msize curm mqc, get qtls pos = Some ( Null, wtype, flag, maxm, msize, curm, mqc) /\ 
                                             left <= (Int.unsigned pos) < right) /\
          posv <> Vint32 (Int.repr 255) \/
       (exists pos wtype flag maxm msize curm mqc, get qtls pos = Some ( Null, wtype, flag, maxm, msize, curm, mqc) /\
         posv <> Vint32 pos )) ->
    absinfer sch 
       (<|| mqcreate_pos (|posv :: Vint32 idx :: Vint32 cpn :: nil|);; s  ||> ** HQAttr qtls  ** P) 
       (<|| ABORT ||> ** HQAttr qtls ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HQAttr qtls ** P)) by can_change_aop_solver.
  eapply absinfer_trans;
  try eapply absinfer_seq;
  try (eapply absinfer_seq_abt; try eauto);
  try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
  Unshelve.
  exact None.
  trivial. trivial.
Qed.

Lemma mqcreate_absimp_pos_cons:
  forall sch P qtls posv cpn idx s left right,
    can_change_aop P ->
    left = OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned idx ->
    right = OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned idx + 1) ->
    (~(exists pos wtype flag maxm msize curm mqc, get qtls pos = Some ( Null, wtype, flag, maxm, msize, curm, mqc) /\ 
                                             left <= (Int.unsigned pos) < right) /\
          posv = Vint32 (Int.repr 255) \/
       (exists pos wtype flag maxm msize curm mqc, get qtls pos = Some ( Null, wtype, flag, maxm, msize, curm, mqc) /\
         posv = Vint32 pos )) ->
    absinfer sch 
       (<|| mqcreate_pos (|posv :: Vint32 idx :: Vint32 cpn :: nil|);; s  ||> ** HQAttr qtls  ** P) 
             (<|| s ||> ** HQAttr qtls ** P).
Proof.
  infer_solver 0%nat.
  exists posv qtls. do 4 eexists.
  left. splits; eauto.
  destruct s0 as [[[[[]]]]].
  destruct H3. simpljoin1.
  simpl in *.
  destruct H7.
  subst x. subst x2.
  eapply OSAbstMod.join_sig_get in H6.
  auto.
  Unshelve.
  exact None.
Qed.

Lemma mqcreate_absimp_poserr:
  forall sch P posv s,
    can_change_aop P ->
    Int.eq posv (Int.repr 255) = true ->
    absinfer sch 
            (<|| mqcreate_poserr (| Vint32 posv ::nil |) ?? s ||>  ** P)
             (<|| END (Some (Vint32 Int.mone)) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mqcreate_absimp_set_placeholder: 
  forall sch pos qtls s0 P wtype flag maxm msize curm mqc,
    can_change_aop P ->
    Int.eq pos (Int.repr 255) = false ->
    get qtls pos = Some ( Null, wtype, flag, maxm, msize, curm, mqc) -> 
    absinfer sch 
             (<||mqcreate_poserr (|Vint32 pos :: nil|) ?? (mqcreate_set_placeholder (|Vint32 pos :: nil|) ;; s0) ||> ** 
                 HQAttr qtls ** P)
             (<|| s0 ||> ** HQAttr (set qtls pos ( Holder, wtype, flag, maxm, msize, curm, mqc)) ** P). 
Proof.
  intros.
  infer_solver 1%nat. 
Qed. 

Lemma mqcreate_absimp_set_ecb_ptr_null:
  forall sch P s0 pos et wtype flag maxm msize curm mqc qtls qtls' locmp ptrmp locmp' ptrmp' ct muxp semp qp, 
    can_change_aop P -> 
    Int.eq pos (Int.repr 255) = false -> 
    get qtls pos = Some (et, wtype, flag, maxm, msize, curm, mqc) -> 
    locmp' = set locmp ct (Vint32 (Int.repr __EvLoc_normal)) ->
    get ptrmp ct = Some (muxp, semp, qp) -> 
    ptrmp' = set ptrmp ct (muxp, semp, Vnull) -> 
    qtls' = set qtls pos(Null, wtype, flag, maxm, msize, curm, mqc) -> 
    absinfer sch 
             (<|| (mqcreate_set_ecb_ptr (|Vint32 pos :: Vnull :: nil|) ?? mqcreate_holder_abt (| Vnull :: nil |)) ;; s0 ||> ** 
              HQAttr qtls ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P) 
             (<|| s0 ||> ** HQAttr qtls' ** HEvLoc locmp' ** HEvPtr ptrmp' ** HCurTCB ct ** P).   
Proof.
  introv Hcop Hrgn Heib0 Hlmp' Hpmp Hpmp' Heibs'.
  eapply absinfer_trans.
  eapply absinfer_seq. pure_auto. 
  instantiate (1:= HQAttr qtls' ** HEvLoc locmp' ** HEvPtr ptrmp' ** HCurTCB ct ** P).
  pure_auto.
  instantiate (1:=END None).
  infer_solver 0%nat.
  unfold tidsame.
  repeat (rewrite set_a_get_a'; eauto).
  eapply absinfer_seq_end; pure_auto.
Qed.

Lemma mqcreate_absimp_set_ecb_ptr_n_null: 
  forall sch P s0 pos eid et wtype flag maxm msize curm mqc qtls qtls' locmp ptrmp locmp' ptrmp' ct muxp semp qp, 
    can_change_aop P -> 
    Int.eq pos (Int.repr 255) = false -> 
    get qtls pos = Some (et, wtype, flag, maxm, msize, curm, mqc) -> 
    locmp' = set locmp ct (Vint32 (Int.repr __EvLoc_normal)) ->
    get ptrmp ct = Some (muxp, semp, qp) -> 
    ptrmp' = set ptrmp ct (muxp, semp, Vnull) -> 
    qtls' = set qtls pos (Valid_Addr eid, wtype, flag, maxm, msize, curm, mqc) ->     
    eid <> vhold_addr -> 
    absinfer sch 
             (<|| (mqcreate_set_ecb_ptr (|Vint32 pos :: Vptr eid :: nil|) ?? mqcreate_holder_abt (| Vptr eid :: nil |));; s0 ||> **
              HQAttr qtls ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P) 
             (<|| s0 ||> ** HQAttr qtls' ** HEvLoc locmp' ** HEvPtr ptrmp' ** HCurTCB ct ** P).   
Proof.
  introv Hcop Hrgn Heib0 Hlmp' Hpmp Hpmp' Heibs' Hnhold.
  eapply absinfer_trans.
  eapply absinfer_seq. pure_auto. 
  instantiate (1:= HQAttr qtls' ** HEvLoc locmp' ** HEvPtr ptrmp' ** HCurTCB ct ** P).
  pure_auto.
  instantiate (1:=END None).
  subst.
  infer_solver 0%nat.
  unfold tidsame.
  repeat (rewrite set_a_get_a'; eauto).
  eapply absinfer_seq_end; pure_auto.
Qed.

Lemma mqcreate_absimp_set_ecb_holder_abt: 
  forall sch P s0 pos,
    can_change_aop P -> 
    absinfer sch 
             (<|| (mqcreate_set_ecb_ptr (|Vint32 pos :: Vptr vhold_addr :: nil|) ??
                      mqcreate_holder_abt (| Vptr vhold_addr :: nil |));; s0 ||> ** P)
             (<|| ABORT ||> ** P).   
Proof.
  introv Hcop.
  eapply absinfer_trans; try eapply absinfer_seq_abt; eauto.
  eapply absinfer_seq; eauto.
  eapply absinfer_trans; try eapply absinfer_choice2; eauto.
  eapply absinfer_abt; can_change_aop_solver.
  absimp_abt_solver. 
  Unshelve.
  exact None.
Qed.

Lemma mqcreate_absimp_create_error:
  forall pos s0 sch P, 
    can_change_aop P ->
    Int.eq pos (Int.repr 255) = false -> 
    absinfer sch 
             (<|| mqcreate_create_err (|Vint32 pos :: Vnull :: nil|) ?? s0 ||> ** P) 
             (<|| END (Some (Vint32 Int.mone)) ||> ** P). 
Proof.
  introv Hcop. 
  infer_solver 0%nat. 
Qed.

Lemma mqcreate_absimp_set_maxmsg: 
  forall sch P pos max_msgs et wtype flag maxm msize curm mqc qtls qtls' vr_b vr_i s0, 
    can_change_aop P ->
    get qtls pos = Some (et, wtype, flag, maxm, msize, curm, mqc) ->
    qtls' = set qtls pos (et, wtype, flag, max_msgs, msize, curm, mqc) ->
    absinfer sch
             (<|| mqcreate_create_err (|Vint32 pos :: Vptr (vr_b, vr_i) :: nil|)
                  ?? (mqcreate_set_maxmsg (|Vint32 pos :: Vint32 max_msgs :: nil|);; s0) ||>  **  HQAttr qtls ** P)
             (<|| s0 ||> ** HQAttr qtls' ** P). 
Proof.
  introv Hcop Hget H'.
  subst.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver.
  2: { intros; eauto. }
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate (1:=HQAttr ( set qtls pos (et, wtype, flag, max_msgs, msize, curm, mqc)) ** P). 
  can_change_aop_solver.
  instantiate (1 := END None). 
  infer_solver 0%nat. 
  eapply absinfer_seq_end; can_change_aop_solver.
  intros; auto.
Qed.

Lemma mqcreate_absimp_set_msgsize: 
  forall sch P pos msg_size et wtype flag maxm msize curm mqc qtls qtls'  s0, 
    can_change_aop P ->
    get qtls pos = Some (et, wtype, flag, maxm, msize, curm, mqc) ->
    qtls' = set qtls pos (et, wtype, flag, maxm, msg_size, curm, mqc) ->
    absinfer sch
             (<|| mqcreate_set_msgsize (|Vint32 pos :: Vint32 msg_size :: nil|);; s0 ||>  **  HQAttr qtls ** P)
             (<|| s0 ||> ** HQAttr qtls' ** P). 
Proof.
  introv Hcop Hget H'.
  subst.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate (1:=HQAttr ( set qtls pos (et, wtype, flag, maxm, msg_size, curm, mqc)) ** P). 
  can_change_aop_solver.
  instantiate (1 := END None). 
  infer_solver 0%nat. 
  eapply absinfer_seq_end; can_change_aop_solver.
  intros; auto.
Qed.

Lemma mqcreate_absimp_set_flgs: 
  forall sch P pos mq_blockflag et wtype flag maxm msize curm mqc qtls qtls'  s0, 
    can_change_aop P ->
    get qtls pos = Some (et, wtype, flag, maxm, msize, curm, mqc) ->
    qtls' = set qtls pos (et, wtype, mq_blockflag, maxm, msize, curm, mqc) ->
    absinfer sch
             (<|| mqcreate_set_flags (|Vint32 pos :: Vint32 mq_blockflag :: nil|);; s0 ||>  **  HQAttr qtls ** P)
             (<|| s0 ||> ** HQAttr qtls' ** P). 
Proof.
  infer_solver 0%nat. 
Qed.

Lemma mqcreate_absimp_set_wtp: 
  forall sch P pos  et wtype flag maxm msize curm mqc qtls qtls' s0, 
    can_change_aop P ->
    get qtls pos = Some (et, wtype, flag, maxm, msize, curm, mqc) ->
    qtls' = set qtls pos (et, (Int.repr PTHREAD_WAITQ_PRIO), flag, maxm, msize, curm, mqc) ->
    absinfer sch
             (<|| mqcreate_set_waittype (|Vint32 pos :: nil|) ;; s0 ||>  **  HQAttr qtls ** P)
             (<|| s0 ||> ** HQAttr qtls' ** P). 
Proof.
  infer_solver 0%nat. 
Qed.

Lemma mqcreate_absimp_rv_pos:
  forall rv P sch pos,
    can_change_aop P -> 
    rv = Vint32 pos ->
    absinfer sch
      (<|| mqcreate_rv_pos (| Vint32 pos :: rv :: nil|) ||> ** P)
      (<|| END (Some (Vint32 pos)) ||> ** P). 
Proof.
  infer_solver 0%nat.
Qed.

Lemma mqcreate_absimp_rv_pos_abt:
  forall rv P sch pos,
    can_change_aop P -> 
    rv <> Vint32 pos ->
    absinfer sch
      (<|| mqcreate_rv_pos (| Vint32 pos :: rv :: nil|) ||> ** P)
      (<|| ABORT ||> ** P). 
Proof.
  intros.
  apply absinfer_abt.
  pure_auto. pure_auto.
  absimp_abt_solver.
Qed.


Open Scope Z_scope.
Open Scope int_scope.
Open Scope code_scope.

Ltac casetacn trm1 trm2 Ht Hf Eq := 
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by tauto;
  destruct h as [Ht | Hf] eqn: Eq.

Lemma evref_same_type_preserve:
  forall eptr semeibs muxeibs mqeibs pos wtype flag maxm msize curm mqc, 
    evref_same_type eptr semeibs muxeibs mqeibs ->
    get mqeibs pos = Some (Null, wtype, flag, maxm, msize, curm, mqc) -> 
    evref_same_type eptr semeibs muxeibs (set mqeibs pos (Holder, wtype, flag, maxm, msize, curm, mqc)). 
Proof.
  introv Hest Hget.
  unfold evref_same_type in *.
  destructs Hest.
  splits.
  3:{
    introv Hq.
    unfold mqeib_ref in *.
    simpljoin1.
    casetac pos x Ht Hf.
    subst. rewrite set_a_get_a in H2. inverts H2.
    apply H1. 
    rewrite set_a_get_a' in H2. do 6 eexists. eauto. eauto.
    }
  -
    introv Hs.
    lets H00: H Hs. destructs H00. splits; auto.
    introv Hq. apply H3.
    unfold mqeib_ref in Hq. unfold mqeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst. rewrite set_a_get_a in H4. inverts H4.
    rewrite set_a_get_a' in H4. do 6 eexists. eauto.  eauto.
  -  
    introv Hm.
    lets H00: H0 Hm. destructs H00. splits; auto.
    introv Hq. apply H3.
    unfold mqeib_ref in Hq. unfold mqeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst. rewrite set_a_get_a in H4. inverts H4.
    rewrite set_a_get_a' in H4. do 6 eexists. eauto. eauto. 
Qed.
  
Lemma eibref_distinct_null_holder_preserve: 
  forall wtype flag maxm msize curm mqc pos semeibs muxeibs mqeibs, 
    eibref_distinct semeibs muxeibs mqeibs ->
    get mqeibs pos = Some (Null, wtype, flag, maxm, msize, curm, mqc) -> 
    eibref_distinct semeibs muxeibs (set mqeibs pos (Holder, wtype, flag, maxm, msize, curm, mqc)). 
Proof. 
  introv Hed Hget.
  unfold eibref_distinct in *.
  intros.
  specialize (Hed eptr).
  mytac. splits; auto.
  eapply evref_same_type_preserve; eauto.
  unfold semref_distinct in *.
  introv Hget1 Hget2.
  casetac pos pos1 Heq1 Hneq1.
  subst. rewrite set_a_get_a in Hget1. inverts Hget1.
  casetac pos pos2 Heq2 Hneq2.
  subst. rewrite set_a_get_a in Hget2. inverts Hget2.
  rewrite set_a_get_a' in Hget1; eauto.
  rewrite set_a_get_a' in Hget2; eauto.
Qed.  

Lemma SEM_ECB_P_null_holder_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos wtype flag maxm msize curm mqc, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get mqeibs pos = Some (Null, wtype, flag, maxm, msize, curm, mqc) -> 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs (set mqeibs pos (Holder, wtype, flag, maxm, msize, curm, mqc)).
Proof.
  introv Hsep Hget.
  unfold SEM_ECB_P in *.
  introv Hptr.
  lets H00: Hsep Hptr. clear Hsep.
  destruct H00.
  - 
    left.
    simpljoin1.
    splits; auto.
    introv Href. apply H1.
    unfold eib_ref in *.
    destruct Href. left;auto.
    destruct H3. right;left. auto.
   right;right. unfold mqeib_ref in *. simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H3. inverts H3.
    rewrite set_a_get_a' in H3; eauto. do 6 eexists;eauto.
  -
    destruct H.
    +
      right; left.
      simpljoin1.
      splits; auto.
      introv Href.
      apply H0.
      unfold eib_ref in Href. unfold eib_ref.
      destruct Href. left;eauto.
      destruct H2. right;left;eauto. right;right.
      unfold mqeib_ref in *.
      simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H2. inverts H2.
      rewrite set_a_get_a' in H2; eauto. do 6 eexists;eauto.
    +    
      simpljoin1.
      right. right.
      splits; auto.
Qed.

Lemma MUX_ECB_P_null_holder_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos wtype flag maxm msize curm mqc, 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get mqeibs pos = Some (Null, wtype, flag, maxm, msize, curm, mqc) -> 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs (set mqeibs pos (Holder, wtype, flag, maxm, msize, curm, mqc)).
Proof.
  introv Hmep Hget.
  unfold MUX_ECB_P in *.
  introv Hptr.
  lets H00: Hmep Hptr. clear Hmep.
  destruct H00.
  - 
    left.
    simpljoin1.
    splits; auto.
    introv Href. apply H1.
    unfold eib_ref in *.
    destruct Href. left;auto.
    destruct H3. right;left;auto.
    right;right. unfold mqeib_ref in *. simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H3. inverts H3.
    rewrite set_a_get_a' in H3; eauto. do 6 eexists;eauto.
  -
    destruct H.
    +
      right; left.
      simpljoin1.
      splits; auto.
      introv Href.
      apply H0.
      unfold eib_ref in Href. unfold eib_ref.
      destruct Href. left;auto.
      destruct H2. right;left;auto.
      right;right. unfold mqeib_ref in *.
      simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H2. inverts H2.
      rewrite set_a_get_a' in H2; eauto. do 6 eexists;eauto.
    +    
      simpljoin1.
      right. right.
      splits; auto.
Qed.

Lemma Q_ECB_P_null_holder_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos wtype flag maxm msize curm mqc, 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get mqeibs pos = Some (Null, wtype, flag, maxm, msize, curm, mqc) -> 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs (set mqeibs pos (Holder, wtype, flag, maxm, msize, curm, mqc)).
Proof.
  introv Hqep Hget.
  unfold Q_ECB_P in *.
  introv Hptr.
  lets H00: Hqep Hptr. clear Hqep.
  destruct H00 as (Hor & Hdel).
  split.
  - (* part 1 *)
    destruct Hor.
    + 
      left.
      simpljoin1.
      splits; auto.
      introv Href. apply H1.
      unfold eib_ref in *.
      destruct Href. left;auto. destruct H3. right;left;auto.
      right;right. unfold mqeib_ref in *. simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H3. inverts H3.
      rewrite set_a_get_a' in H3; eauto. do 6 eexists;eauto.
    +
      destruct H.
      *
        right; left.
        simpljoin1.
        splits; auto.
        introv Href.
        apply H0.
        unfold eib_ref in Href. unfold eib_ref.
        destruct Href. left;auto.
        destruct H2. right;left;auto.
        right;right.
        unfold mqeib_ref in *.
        simpljoin1.
        casetac pos x Heq Hneq.
        subst. rewrite set_a_get_a in H2. inverts H2.
        rewrite set_a_get_a' in H2; eauto. do 6 eexists;eauto.
      *    
        simpljoin1.
        right. right.
        splits; auto.
  - (* part 2 *)
    clear Hor.
    introv Hgetl.
    specialize (Hdel Hgetl).
    simpljoin1.
    splits; auto.
    introv Href.
    apply H1.
    unfold eib_ref in Href. unfold eib_ref.
    destruct Href. auto. destruct H2. auto.
    right;right.
    unfold mqeib_ref in *.
    simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H2. inverts H2.
    rewrite set_a_get_a' in H2; eauto.
   do 6 eexists ;eauto.
Qed.

Lemma RH_EIBlk_ECBlk_Q_P_null_preserve:
  forall ecbls mqeibs pos wtype flag maxm msize curm mqc, 
    RH_EIBlk_ECBlk_Q_P ecbls mqeibs ->
    RH_EIBlk_ECBlk_Q_P ecbls (set mqeibs pos (Null, wtype, flag, maxm, msize, curm, mqc)). 
Proof.
  intros.
  unfold RH_EIBlk_ECBlk_Q_P in *.
  introv Hget.
  casetac pos pos0 Ht Hf.
  subst.
  rewrite set_a_get_a in Hget. inverts Hget.
  rewrite set_a_get_a' in Hget; eauto. 
Qed.

Lemma RH_EIBlk_ECBlk_Q_P_ptr_preserve: 
  forall ecbls mqeibs pos wtype flag maxm msize curm mqc eid, 
    RH_EIBlk_ECBlk_Q_P ecbls mqeibs ->
    is_que ecbls eid -> 
    RH_EIBlk_ECBlk_Q_P ecbls (set mqeibs pos (Valid_Addr eid, wtype, flag, maxm, msize, curm, mqc)). 
Proof.
  introv Hrh Hsem.
  unfold RH_EIBlk_ECBlk_Q_P in *.
  introv Hget.
  casetac pos pos0 Heq Hne.
  subst.
  rewrite set_a_get_a in Hget. inverts Hget.
  unfold is_sem in Hsem. eauto.
  rewrite set_a_get_a' in Hget; eauto.
Qed.   

Lemma evref_same_type_infonull_preserve:
  forall semeibs muxeibs mqeibs eptr pos wtype flag maxm msize curm mqc,
    evref_same_type eptr semeibs muxeibs mqeibs ->
    evref_same_type eptr semeibs muxeibs (set mqeibs pos (Null,wtype, flag, maxm, msize, curm, mqc)). 
Proof.
  introv Hst.
  unfold evref_same_type in *.
  simpljoin1.
  splits; auto.
  3:{
    introv Hq.
    apply H1.
    unfold mqeib_ref in Hq. unfold mqeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst. rewrite set_a_get_a in H2. inverts H2.
    rewrite set_a_get_a' in H2; eauto. do 6 eexists;eauto. }
  -
    introv Hs.
    lets H00: H  Hs.
    simpljoin1. splits; auto.
    introv Hq. apply H3.
    unfold mqeib_ref in Hq. unfold mqeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst. rewrite set_a_get_a in H4. inverts H4.
    rewrite set_a_get_a' in H4; eauto. do 6 eexists;eauto.
  -
    introv Hm.
    lets H00: H0 Hm.
    simpljoin1. splits; auto.
    introv Hq. apply H3.
    unfold mqeib_ref in Hq. unfold mqeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst. rewrite set_a_get_a in H4. inverts H4.
    rewrite set_a_get_a' in H4; eauto. do 6 eexists;eauto.
Qed.

Lemma mqeib_ref_infonull_preserve:
  forall qeibs pos wtype flag maxm msize curm mqc eptr, 
    mqeib_ref (set qeibs pos (Null, wtype, flag, maxm, msize, curm, mqc)) eptr ->
    mqeib_ref qeibs eptr.
Proof.
  introv Hsr.
  unfold mqeib_ref in *.
  simpljoin1.
  casetac pos x He Hne.
  subst.
  rewrite set_a_get_a in H. inverts H.
  rewrite set_a_get_a' in H; eauto. do 6 eexists;eauto.
Qed.

Lemma eibref_infonull_preserve:
  forall semeibs pos wtype flag maxm msize curm mqc muxeibs qeibs eptr, 
    eib_ref semeibs muxeibs (set qeibs pos (Null, wtype, flag, maxm, msize, curm, mqc)) eptr -> 
    eib_ref semeibs muxeibs qeibs eptr. 
Proof.
  introv Her.
  unfold eib_ref in *.
  destruct Her . left ;auto. destruct H . right;left ;auto.
  right. right.  eapply mqeib_ref_infonull_preserve; eauto.
Qed.

Lemma sem_ecb_p_infonull_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs pos wtype flag maxm msize curm mqc tid, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    get ptrmp tid = Some (Vnull, Vnull, Vnull) -> 
    SEM_ECB_P (set locmp tid (V$ __EvLoc_normal)) ptrmp ecbls fecbh fecbvl
              semeibs muxeibs (set qeibs pos (Null, wtype, flag, maxm, msize, curm, mqc)).
Proof.
  introv Hsep.
  unfold SEM_ECB_P in *.
  introv Hnull Hgetp.
  casetac tid t Heq Hneq.
  -
    subst.
    rewrite Hnull in Hgetp.
    inverts Hgetp.
  -
    rewrite set_a_get_a'; eauto.
    clear Hnull.
    lets H00: Hsep Hgetp.
    destruct H00.
    left.
    simpljoin1. splits; auto.
    introv Hf. apply H1.
    eapply eibref_infonull_preserve; eauto.

    destruct H.
    right. left.
    simpljoin1.
    splits; auto.
    introv Hf; apply H0. 
    eapply eibref_infonull_preserve; eauto.

    right. right.
    simpljoin1.
    splits; auto.
Qed.

Lemma mux_ecb_p_infonull_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs pos wtype flag maxm msize curm mqc tid, 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    get ptrmp tid = Some (Vnull, Vnull, Vnull) -> 
    MUX_ECB_P (set locmp tid (V$ __EvLoc_normal)) ptrmp ecbls fecbh fecbvl
              semeibs muxeibs (set qeibs pos (Null, wtype, flag, maxm, msize, curm, mqc)).
Proof.
  introv Hmep. 
  unfold MUX_ECB_P in *.
  introv Hnull Hgetp.
  casetac tid t Heq Hneq.
  -
    subst.
    rewrite Hnull in Hgetp.
    inverts Hgetp.
  -
    rewrite set_a_get_a'; eauto.
    clear Hnull.
    lets H00: Hmep Hgetp.
    destruct H00.
    left.
    simpljoin1. splits; auto.
    introv Hf. apply H1.
    eapply eibref_infonull_preserve; eauto.

    destruct H.
    right. left.
    simpljoin1.
    splits; auto.
    introv Hf; apply H0. 
    eapply eibref_infonull_preserve; eauto.

    right. right.
    simpljoin1.
    splits; auto.
Qed.

Lemma q_ecb_p_infonull_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs pos wtype flag maxm msize curm mqc tid, 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    get ptrmp tid = Some (Vnull, Vnull, Vnull) -> 
    Q_ECB_P (set locmp tid (V$ __EvLoc_normal)) ptrmp ecbls fecbh fecbvl
              semeibs muxeibs (set qeibs pos (Null, wtype, flag, maxm, msize, curm, mqc)).
Proof.
  introv Hqep. 
  unfold Q_ECB_P in *.
  introv Hnull Hgetp.
  casetac tid t Heq Hneq.
  -
    subst.
    rewrite Hnull in Hgetp.
    inverts Hgetp.
  -
    rewrite set_a_get_a'; eauto.
    clear Hnull.
    lets H00: Hqep Hgetp.
    destruct H00 as (Hor3 & Hdel).
    split.
    destruct Hor3.
    left.
    simpljoin1. splits; auto.
    introv Hf. apply H1.
    eapply eibref_infonull_preserve; eauto.

    destruct H.
    right. left.
    simpljoin1.
    splits; auto.
    introv Hf; apply H0. 
    eapply eibref_infonull_preserve; eauto.

    right. right.
    simpljoin1.
    splits; auto.
    introv Hget.
    lets H00: Hdel Hget.
    simpljoin1. splits; auto.
    2: {
      introv Hf; apply H1.
      eapply eibref_infonull_preserve; eauto.
    }
    introv Hex; apply H0.
    destruct Hex as (t' & Hcre12 & Hevptr).
    casetac tid t' Heq' Hneq'.
    subst.
    rewrite set_a_get_a in Hcre12. destruct Hcre12; tryfalse. 
    rewrite set_a_get_a' in Hcre12;eauto. 
Qed.
  
Lemma mqref_distinct_infonull_preserve:
  forall mqeibs ep pos wtype flag maxm msize curm mqc, 
    mqref_distinct mqeibs ep->
    mqref_distinct (set mqeibs pos (Null, wtype, flag, maxm, msize, curm, mqc)) ep.  
Proof.
  introv Hdis.
  unfold mqref_distinct in *.
  introv Hget1 Hget2.
  casetac pos pos1 Ht Hf.
  subst. rewrite set_a_get_a in Hget1. inverts Hget1.
  rewrite set_a_get_a' in Hget1; eauto.
  casetac pos pos2 Ht' Hf'.
  subst. rewrite set_a_get_a in Hget2. inverts Hget2.
  rewrite set_a_get_a' in Hget2; eauto.
Qed.  
  
Lemma eibref_distinct_infonull_preserve: 
  forall semeibs muxeibs mqeibs pos wtype flag maxm msize curm mqc, 
    eibref_distinct semeibs muxeibs mqeibs ->
    eibref_distinct semeibs muxeibs (set mqeibs pos (Null, wtype, flag, maxm, msize, curm, mqc)).
Proof.
  introv Hed.
  unfold eibref_distinct in *.
  intros.
  specialize (Hed eptr).
  simpljoin1. splits; auto.
  eapply evref_same_type_infonull_preserve; eauto.
  unfold mqref_distinct.
  introv Hget1 Hget2.
  eapply mqref_distinct_infonull_preserve; eauto.
Qed.

Lemma evdel_nodup_normal_preserve: 
  forall locmp ptrmp ct, 
    evdel_nodup locmp ptrmp ->
    evdel_nodup (set locmp ct (V$ __EvLoc_normal)) ptrmp.  
Proof.
  introv Hdnp.
  unfold evdel_nodup in *.
  introv Hneqt Hget1 Hget2 Hp1 Hp2.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  subst t1.
  rewrite set_a_get_a in Hget1.
  inverts Hget1.
  assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst t2.
  rewrite set_a_get_a in Hget2.
  inverts Hget2.
  rewrite set_a_get_a' in Hget1, Hget2; eauto.
Qed.   

Lemma evdel_nodup_normal_null_preserve:
  forall locmp ptrmp ct,
    evdel_nodup locmp ptrmp -> 
    evdel_nodup (set locmp ct (V$ __EvLoc_normal)) (set ptrmp ct (Vnull, Vnull, Vnull)). 
Proof.
  introv Hdnp.
  unfold evdel_nodup in *.
  introv Hneqt Hget1 Hget2 Hp1 Hp2.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  subst t1.
  rewrite set_a_get_a in Hget1.
  inverts Hget1.
  assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst t2.
  rewrite set_a_get_a in Hget2.
  inverts Hget2.
  rewrite set_a_get_a' in Hget1, Hget2; eauto.
  unfold evptr_of_tsk in Hp1, Hp2.
  rewrite set_a_get_a' in Hp1, Hp2; eauto.
Qed.   

Lemma evcre_nodup_normal_preserve:  
  forall locmp ptrmp ct, 
    evcre_nodup locmp ptrmp ->
    evcre_nodup (set locmp ct (V$ __EvLoc_normal)) ptrmp.   
Proof.
  introv Hdnp.
  unfold evcre_nodup in *.
  introv Hneqt Hget1 Hget2 Hp1 Hp2.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  subst t1.
  rewrite set_a_get_a in Hget1.
  inverts Hget1; tryfalse.
  assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst t2.
  rewrite set_a_get_a in Hget2.
  inverts Hget2; tryfalse.
  rewrite set_a_get_a' in Hget1, Hget2; eauto.
Qed.   

Lemma evcre_nodup_normal_null_preserve:
  forall locmp ptrmp ct,
    evcre_nodup locmp ptrmp -> 
    evcre_nodup (set locmp ct (V$ __EvLoc_normal)) (set ptrmp ct (Vnull, Vnull, Vnull)). 
Proof.
  introv Hdnp.
  unfold evcre_nodup in *.
  introv Hneqt Hget1 Hget2 Hp1 Hp2.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  subst t1.
  rewrite set_a_get_a in Hget1.
  inverts Hget1; tryfalse.
  assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst t2.
  rewrite set_a_get_a in Hget2.
  inverts Hget2; tryfalse.
  rewrite set_a_get_a' in Hget1, Hget2; eauto.
  unfold evptr_of_tsk in Hp1, Hp2.
  rewrite set_a_get_a' in Hp1, Hp2; eauto.
Qed.

Lemma eibref_distinct_noref_eid_preserve: 
  forall semeibs muxeibs mqeibs eid pos wtype flag maxm msize curm mqc, 
    eibref_distinct semeibs muxeibs mqeibs ->  
    ~ eib_ref semeibs muxeibs mqeibs eid -> 
    eibref_distinct semeibs muxeibs (set mqeibs pos (Valid_Addr eid, wtype, flag, maxm, msize, curm, mqc)).  
Proof. 
  introv Hed Hnref.
  unfold eibref_distinct in *.
  intro.
  specialize (Hed eptr).
  simpljoin1.
  splits; auto.
  -
    unfold evref_same_type.
    splits.
    +
      introv Hsref.
      unfold semeib_ref in Hsref.
      simpljoin1.
      split.
      {unfold evref_same_type in H.
        simpljoin1.
        assert (HH: semeib_ref semeibs eptr).
        unfold semeib_ref. do 2 eexists. eauto.
        apply H  in HH. simpljoin1. auto.
       }
       {unfold mqeib_ref.
        introv Hex. simpljoin1.
        casetac pos x2 He Hne.
        subst. rewrite set_a_get_a in H4. inverts H4.
        apply Hnref.
        unfold eib_ref.
        left.
        unfold semeib_ref. repeat eexists; eauto.
        rewrite set_a_get_a' in H4; eauto.
        unfold evref_same_type in H.
        simpljoin1.
        assert (HH: semeib_ref semeibs eptr).
        unfold semeib_ref. do 2 eexists; eauto.
        apply H  in HH.
        simpljoin1. apply H8.
        unfold mqeib_ref. do 6 eexists; eauto.
       }
    +
      introv Hmref.
      unfold muxeib_ref in Hmref. 
      simpljoin1.
      split.
      {
        unfold evref_same_type in H.
        simpljoin1.
        assert (HH: muxeib_ref muxeibs eptr).
        unfold muxeib_ref. do 8 eexists. eauto.
        apply H4 in HH. simpljoin1. auto.
      }
      unfold mqeib_ref.
      introv Hex. simpljoin1.
      casetac pos x8 He Hne.
      subst. rewrite set_a_get_a in H4. inverts H4.
      apply Hnref.
      unfold eib_ref.
      right. left.
      unfold muxeib_ref. repeat eexists; eauto.
      rewrite set_a_get_a' in H4; eauto.
      unfold evref_same_type in H.
      simpljoin1.
      assert (HH: muxeib_ref muxeibs eptr).
      unfold muxeib_ref. do 8 eexists; eauto.
      apply H5 in HH.
      simpljoin1. apply H8. 
      unfold mqeib_ref. do 6 eexists; eauto.
    +
      introv Hqref.
      unfold mqeib_ref in Hqref.
      simpljoin1.
      casetac pos x Heq Hne.
      subst. rewrite set_a_get_a in H3. inverts H3.
      unfold eib_ref in Hnref.
      clear -Hnref. intuition.
      rewrite set_a_get_a' in H3; eauto.
      unfold evref_same_type in H.
      simpljoin1.
      apply H5; auto.
      unfold mqeib_ref. do 6 eexists; eauto.
  -
    unfold mqref_distinct in H2. unfold mqref_distinct.
    introv Hget1 Hget2.
    casetac pos pos1 He Hne.
    subst. rewrite set_a_get_a in Hget1. inverts Hget1.
    casetac pos1 pos2 He' Hne'.
    subst. rewrite set_a_get_a in Hget2. inverts Hget2.
    auto.
    rewrite set_a_get_a' in Hget2; eauto.
    false. apply Hnref.
    unfold eib_ref. right;right.
    unfold mqeib_ref. do 6 eexists; eauto.
    rewrite set_a_get_a' in Hget1; eauto.
    casetac pos pos2 He' Hne'.
    subst. 
    rewrite set_a_get_a in Hget2; eauto.
    inverts Hget2.

    false. apply Hnref.
    unfold eib_ref. right;right.
    unfold mqeib_ref. do 6 eexists.  eauto.
    rewrite set_a_get_a' in Hget2; eauto.
Qed. 

Lemma evcre_nodup_cre1_cre2_contra: 
  forall t tid eid locmp ptrmp, 
    evcre_nodup locmp ptrmp -> 
    t <> tid -> 
    tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid ->
    get locmp tid = Some (V$ __EvLoc_ecbcre2) ->
    get ptrmp tid = Some (Vnull, Vnull, Vptr eid) ->  
    False. 
Proof.
  introv Hcrendp Htne Htle Hgetl Hgetp.
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hgetl' & (mq & sp & qp & (Hgetp' & Hor3))).
  unfold evcre_nodup in Hcrendp.
  specialize (Hcrendp t tid eid eid Htne (or_introl Hgetl') (or_intror Hgetl)).
  cut (eid <> eid).
  intro Hf. tryfalse.
  apply Hcrendp.
  unfold evptr_of_tsk.
  destruct Hor3.
  subst. left. do 2 eexists; eauto.
  destruct H.
  subst. right; left. do 2 eexists; eauto.
  subst. right; right. do 2 eexists; eauto.
  unfold evptr_of_tsk.
  right; right. eauto.
Qed.

Lemma evcre_nodup_cre2_cre2_contra: 
  forall t tid eid locmp ptrmp, 
    evcre_nodup locmp ptrmp -> 
    t <> tid -> 
    tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid ->
    get locmp tid = Some (V$ __EvLoc_ecbcre2) ->
    get ptrmp tid = Some (Vnull,Vnull , Vptr eid) ->  
    False. 
Proof.
  introv Hcrendp Htne Htle Hgetl Hgetp.
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hgetl' & (mq & sp & qp & (Hgetp' & Hor3))).
  unfold evcre_nodup in Hcrendp.
  specialize (Hcrendp t tid eid eid Htne (or_intror Hgetl') (or_intror Hgetl)).
  cut (eid <> eid).
  intro Hf. tryfalse.
  apply Hcrendp.
  unfold evptr_of_tsk.
  destruct Hor3.
  subst. left. do 2 eexists; eauto.
  destruct H.
  subst. right; left. do 2 eexists; eauto.
  subst. right; right. do 2 eexists; eauto.
  unfold evptr_of_tsk.
  right; right. eauto.
Qed.

Lemma ecbdel_que_contra:  
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs t tid  eid, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs -> 
    tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel eid ->
    t <> tid ->
    get ptrmp tid = Some (Vnull, Vnull, Vptr eid) ->
    get locmp tid = Some (V$ __EvLoc_ecbcre2) ->
    False.
Proof.
  introv Hsep Hmep Hqep Htle Htneq Hgtideid Hgtidcre2.
  unfold tsk_loc_ev in Htle.

  destruct Htle as (Hgetl & (mp & sp & qp & (Hgetp & Hor3))).
  destruct Hor3.
  -
    subst.
    unfold MUX_ECB_P in Hmep.
    lets H00: Hmep Hgetp.
    rewrite Hgetl in H00.
    destruct H00.  simpljoin1. tryfalse. destruct H. simpljoin1. tryfalse. simpljoin1. tryfalse.
  -
    destruct H; subst.
    +
      unfold SEM_ECB_P in Hsep.
      lets H00: Hsep Hgetp.
      rewrite Hgetl in H00.
      inverts H00.
      simpljoin1. tryfalse. inverts H. simpljoin1. tryfalse. simpljoin1. tryfalse.
    +
      unfold Q_ECB_P in Hqep.
      lets H00: Hqep Hgetp. 
      destruct H00 as (Hor3 & Hdel). 
      apply Hdel in Hgetl.
      simpljoin1.
      destruct H0.
      exists tid.
      split.
      right;eauto.
      unfold evptr_of_tsk.
      right;right.
      exists Vnull Vnull.
      auto.
Qed.

Lemma n_eibref_diff_ptr_preserve_que: 
  forall semeibs muxeibs mqeibs eptr eid pos wtype flag maxm msize curm mqc, 
    ~ eib_ref semeibs muxeibs mqeibs eptr ->
    eptr <> eid ->
    ~ eib_ref semeibs muxeibs (set mqeibs pos (Valid_Addr eid, wtype, flag, maxm, msize, curm, mqc)) eptr. 
Proof.
  introv Hnref Hneq Heibref.
  apply Hnref.
  unfold eib_ref in *.
  inverts Heibref. left;auto.
  inverts H. right;left;auto. 
  right;right.
  unfold mqeib_ref in *.
  simpljoin1.
  casetac pos x He Hne.
  subst. rewrite set_a_get_a in H. inverts H.
  tryfalse.
  rewrite set_a_get_a' in H; eauto.  do 6 eexists;eauto.
Qed.
  
Lemma SEM_ECB_P_normal_null_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs tid eid wtype flag maxm msize curm mqc pos, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid) -> 
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid) -> 
    SEM_ECB_P (set locmp tid (V$ __EvLoc_normal)) (set ptrmp tid (Vnull, Vnull, Vnull)) ecbls
              fecbh fecbvl semeibs muxeibs (set mqeibs pos (Valid_Addr eid, wtype, flag, maxm, msize, curm, mqc)).
Proof. 
  introv Hsep Hncre1 Hncre2.
  unfold SEM_ECB_P in *.
  introv Hgetp'.
  casetac tid t Hteq Htne.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hsep Hgetp'.
    clear Hsep.
    rewrite set_a_get_a'; eauto.
    destruct H00.
    +
      destruct H as (Hgetl & Hnin & Hnref & Hnone).
      casetac eptr eid He Hne.
      * 
        subst.
        false.
        apply Hncre1.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.
      *
        left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve_que; eauto.
    +
      destruct H.
      *
        destruct H as (Hgetl & Hnin & Hnref & Hnone).
        casetac eptr eid He Hne.
        subst.
        false.
        apply Hncre2.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.

        right. left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve_que; eauto.
        unfold is_sem. eauto.
      *
        destruct H as (Hgetl & Hor2).
        right; right.
        splits; auto.
Qed.

Lemma MUX_ECB_P_normal_null_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs tid eid wtype flag maxm msize curm mqc pos, 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid) -> 
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid) -> 
    MUX_ECB_P (set locmp tid (V$ __EvLoc_normal)) (set ptrmp tid (Vnull, Vnull, Vnull)) ecbls
              fecbh fecbvl semeibs muxeibs (set mqeibs pos (Valid_Addr eid, wtype, flag, maxm, msize, curm, mqc)).
Proof. 
  introv Hmep Hncre1 Hncre2.
  unfold MUX_ECB_P in *.
  introv Hgetp'.
  casetac tid t Hteq Htne.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hmep Hgetp'.
    clear Hmep.
    rewrite set_a_get_a'; eauto.
    destruct H00.
    +
      destruct H as (Hgetl & Hnin & Hnref & Hnone).
      casetac eptr eid He Hne.
      * 
        subst.
        false.
        apply Hncre1.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.
      *
        left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve_que; eauto.
    +
      destruct H.
      *
        destruct H as (Hgetl & Hnin & Hnref & Hnone).
        casetac eptr eid He Hne.
        subst.
        false.
        apply Hncre2.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.

        right. left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve_que; eauto.
        unfold is_mux. eauto.
      *
        destruct H as (Hgetl & Hor2).
        right; right.
        splits; auto.
Qed.

Lemma Q_ECB_P_normal_null_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs tid eid wtype flag maxm msize curm mqc pos, 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid) -> 
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid) -> 
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel eid) ->  
    Q_ECB_P (set locmp tid (V$ __EvLoc_normal)) (set ptrmp tid (Vnull, Vnull, Vnull)) ecbls
              fecbh fecbvl semeibs muxeibs (set mqeibs pos (Valid_Addr eid, wtype, flag, maxm, msize, curm, mqc)).
Proof. 
  introv Hqep Hncre1 Hncre2 Hndel.
  unfold Q_ECB_P in *. 
  introv Hgetp'. 
  casetac tid t Hteq Htne.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hqep Hgetp'.
    clear Hqep.
    rewrite set_a_get_a'; eauto.
    destruct H00 as (Hor3 & Hdel).
    split.
    destruct Hor3.
    +
      destruct H as (Hgetl & Hnin & Hnref & Hnone).
      casetac eptr eid He Hne.
      * 
        subst.
        false.
        apply Hncre1.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.
      *
        left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve_que; eauto.
    +
      destruct H.
      *
        destruct H as (Hgetl & Hnin & Hnref & Hnone).
        casetac eptr eid He Hne.
        subst.
        false.
        apply Hncre2.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.

        right. left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve_que; eauto.
        unfold is_que. eauto.
      *
        destruct H as (Hgetl & Hor2).
        right; right.
        splits; auto.
    +
      introv Hgetl'.
      specialize (Hdel Hgetl').
      simpljoin1. splits; auto.
      introv Hex. apply H0.
      destruct Hex as (t' & Hcre12 & Hep).
      casetac tid t' Ht Hf.
      subst. rewrite set_a_get_a in Hcre12. destruct Hcre12; tryfalse.
      rewrite set_a_get_a' in Hcre12; eauto. 
      exists t'. splits; auto.
      unfold evptr_of_tsk in Hep. rewrite set_a_get_a' in Hep; eauto.
      eapply n_eibref_diff_ptr_preserve_que; eauto.
      casetac eptr eid Ht' Hf'.
      subst.
      false. apply Hndel. exists t. splits; auto.
      unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.
      auto.
Qed. 

Lemma RH_EIBlk_ECBlk_Q_P_set_mq_maxm_preserve: 
  forall ecbls mqeibs pos et wtype flag maxm msize curm mqc maxm', 
    RH_EIBlk_ECBlk_Q_P ecbls mqeibs ->
    get mqeibs pos = Some (et, wtype, flag, maxm, msize, curm, mqc) -> 
    RH_EIBlk_ECBlk_Q_P ecbls (set mqeibs pos (et, wtype, flag, maxm', msize, curm, mqc)). 
Proof.
  introv Hrh Hget.
  unfold RH_EIBlk_ECBlk_Q_P in *.
  introv Hget'.
  casetac pos pos0 Heq Hneq.
  subst.
  rewrite set_a_get_a in Hget'.
  inverts Hget'.
  eapply Hrh; eauto.
  rewrite set_a_get_a' in Hget'; eauto.
Qed.

Lemma RH_EIBlk_ECBlk_Q_P_set_mq_all_preserve: 
  forall ecbls mqeibs pos et wtype flag maxm msize curm mqc wtype' flag' maxm' msize' curm' mqc', 
    RH_EIBlk_ECBlk_Q_P ecbls mqeibs ->
    get mqeibs pos = Some (et, wtype, flag, maxm, msize, curm, mqc) -> 
    RH_EIBlk_ECBlk_Q_P ecbls (set mqeibs pos (et, wtype', flag', maxm', msize', curm', mqc')). 
Proof.
  introv Hrh Hget.
  unfold RH_EIBlk_ECBlk_Q_P in *.
  introv Hget'.
  casetac pos pos0 Heq Hneq.
  subst.
  rewrite set_a_get_a in Hget'.
  inverts Hget'.
  eapply Hrh; eauto.
  rewrite set_a_get_a' in Hget'; eauto.
Qed.

Lemma eibref_distinct_set_mq_all_mqeibs: 
  forall semeibs muxeibs mqeibs pos et wtype flag maxm msize curm mqc wtype' flag' maxm' msize' curm' mqc', 
    eibref_distinct semeibs muxeibs mqeibs ->
    get mqeibs pos = Some (et, wtype, flag, maxm, msize, curm, mqc) -> 
    eibref_distinct semeibs muxeibs (set mqeibs pos (et, wtype', flag', maxm', msize', curm', mqc')). 
Proof.
  introv Hed Hget.
  unfold eibref_distinct in *.
  intro.
  specialize (Hed eptr).
  simpljoin1.
  splits; auto.
  -
    unfold evref_same_type in *.
    simpljoin1.
    splits; auto.
    introv Hse.
    apply H in Hse.
    simpljoin1. splits; auto.
    introv H_. apply H6. 
    unfold mqeib_ref in H_. unfold mqeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst.
    rewrite set_a_get_a in H7.
    inverts H7.
    do 6 eexists; eauto.
    rewrite set_a_get_a' in H7; eauto.  do 6 eexists; eauto.
    
    introv Hme.
    apply H3 in Hme.
    simpljoin1. splits; auto.
    introv H_. apply H6. 
    unfold mqeib_ref in H_. unfold mqeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst.
    rewrite set_a_get_a in H7.
    inverts H7.
    do 6 eexists; eauto. 
    rewrite set_a_get_a' in H7; eauto. do 6 eexists; eauto.
    
    intro Hqe.
    apply H4.
    unfold mqeib_ref in Hqe . unfold mqeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst.
    rewrite set_a_get_a in H5.
    inverts H5.
    do 6 eexists; eauto.
    rewrite set_a_get_a' in H5; eauto.
    do 6 eexists; eauto.
  -
    unfold mqref_distinct in *.
    introv Hget1 Hget2.
    casetac pos pos1 Ht Hf.
    subst. rewrite set_a_get_a in Hget1. inverts Hget1.
    casetac pos1 pos2 Ht' Hf'.
    subst. rewrite set_a_get_a in Hget2. inverts Hget2. auto.    
    rewrite set_a_get_a' in Hget2; eauto.
    rewrite set_a_get_a' in Hget1; eauto.
    casetac pos pos2 Ht' Hf'.
    subst.
    rewrite set_a_get_a in Hget2.
    inverts Hget2.
    eapply H2; eauto.
    rewrite set_a_get_a' in Hget2; eauto.
Qed.

Lemma n_eibref_set_mq_maxm_preserve: 
  forall semeibs muxeibs mqeibs eptr pos et wtype flag maxm msize curm mqc maxm', 
    ~ eib_ref semeibs muxeibs mqeibs eptr -> 
    get mqeibs pos = Some (et, wtype, flag, maxm, msize, curm, mqc) ->
    ~ eib_ref semeibs muxeibs (set mqeibs pos (et, wtype, flag, maxm', msize, curm, mqc)) eptr. 
Proof.
  introv Hnr Hget.
  introv Hf. apply Hnr.
  unfold eib_ref in Hf. unfold eib_ref.
  destruct Hf. left;auto.
  destruct H. right;left;auto.
  right;right.
  unfold mqeib_ref in *.
  simpljoin1.
  casetac pos x Ht Hf.
  subst. rewrite set_a_get_a in H. inverts H.
  do 6 eexists; eauto.
  rewrite set_a_get_a' in H; eauto.   do 6 eexists; eauto.
Qed. 

Lemma n_eibref_set_mq_all_preserve: 
  forall semeibs muxeibs mqeibs eptr pos et wtype flag maxm msize curm mqc wtype' flag' maxm' msize' curm' mqc', 
    ~ eib_ref semeibs muxeibs mqeibs eptr -> 
    get mqeibs pos = Some (et, wtype, flag, maxm, msize, curm, mqc) ->
    ~ eib_ref semeibs muxeibs (set mqeibs pos (et, wtype', flag', maxm', msize', curm', mqc')) eptr. 
Proof.
  introv Hnr Hget.
  introv Hf. apply Hnr.
  unfold eib_ref in Hf. unfold eib_ref.
  destruct Hf. left;auto.
  destruct H. right;left;auto.
  right;right.
  unfold mqeib_ref in *.
  simpljoin1.
  casetac pos x Ht Hf.
  subst. rewrite set_a_get_a in H. inverts H.
  do 6 eexists; eauto.
  rewrite set_a_get_a' in H; eauto.   do 6 eexists; eauto.
Qed. 

Lemma SEM_ECB_P_set_mq_maxm_preserve:  
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos et wtype flag maxm msize curm mqc maxm', 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get mqeibs pos = Some (et, wtype, flag, maxm, msize, curm, mqc) ->
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs (set mqeibs pos (et, wtype, flag, maxm', msize, curm, mqc)).
Proof.
  introv Hsep Hget.
  unfold SEM_ECB_P in *.
  introv Hget'.
  lets H00: Hsep Hget'. clear Hsep.
  destruct H00.
  left.
  simpljoin1. splits; auto.
  eapply n_eibref_set_mq_maxm_preserve; eauto.
  destruct H.
  simpljoin1.
  right; left.
  splits; auto.
  eapply n_eibref_set_mq_maxm_preserve; eauto.
  simpljoin1.
  right; right.
  splits; eauto.
Qed.

Lemma SEM_ECB_P_set_mq_all_preserve:  
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos et wtype flag maxm msize curm mqc wtype' flag' maxm' msize' curm' mqc', 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get mqeibs pos = Some (et, wtype, flag, maxm, msize, curm, mqc) ->
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs (set mqeibs pos (et, wtype', flag', maxm', msize', curm', mqc')).
Proof.
  introv Hsep Hget.
  unfold SEM_ECB_P in *.
  introv Hget'.
  lets H00: Hsep Hget'. clear Hsep.
  destruct H00.
  left.
  simpljoin1. splits; auto.
  eapply n_eibref_set_mq_all_preserve; eauto.
  destruct H.
  simpljoin1.
  right; left.
  splits; auto.
  eapply n_eibref_set_mq_all_preserve; eauto.
  simpljoin1.
  right; right.
  splits; eauto.
Qed.

Lemma MUX_ECB_P_set_mq_maxm_preserve:  
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos et wtype flag maxm msize curm mqc maxm', 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get mqeibs pos = Some (et, wtype, flag, maxm, msize, curm, mqc) ->
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs (set mqeibs pos (et, wtype, flag, maxm', msize, curm, mqc)).
Proof.
  introv Hmep Hget.
  unfold MUX_ECB_P in *.
  introv Hget'.
  lets H00: Hmep Hget'. clear Hmep.
  destruct H00.
  left.
  simpljoin1. splits; auto.
  eapply n_eibref_set_mq_maxm_preserve; eauto.
  destruct H.
  simpljoin1.
  right; left.
  splits; auto.
  eapply n_eibref_set_mq_maxm_preserve; eauto.
  simpljoin1.
  right; right.
  splits; eauto.
Qed.

Lemma MUX_ECB_P_set_mq_all_preserve:  
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos et wtype flag maxm msize curm mqc wtype' flag' maxm' msize' curm' mqc', 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get mqeibs pos = Some (et, wtype, flag, maxm, msize, curm, mqc) ->
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs (set mqeibs pos (et, wtype', flag', maxm', msize', curm', mqc')).
Proof.
  introv Hmep Hget.
  unfold MUX_ECB_P in *.
  introv Hget'.
  lets H00: Hmep Hget'. clear Hmep.
  destruct H00.
  left.
  simpljoin1. splits; auto.
  eapply n_eibref_set_mq_all_preserve; eauto.
  destruct H.
  simpljoin1.
  right; left.
  splits; auto.
  eapply n_eibref_set_mq_all_preserve; eauto.
  simpljoin1.
  right; right.
  splits; eauto.
Qed.

Lemma Q_ECB_P_set_mq_maxm_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos et wtype flag maxm msize curm mqc maxm', 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get mqeibs pos = Some (et, wtype, flag, maxm, msize, curm, mqc) ->
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs (set mqeibs pos (et, wtype, flag, maxm', msize, curm, mqc)).
Proof.
  introv Hsep Hget.
  unfold Q_ECB_P in *.
  introv Hget'.
  lets H00: Hsep Hget'. clear Hsep.
  destruct H00 as (Hor & Hdel).
  split.
  - (*part1*)
    destruct Hor.
    left.
    simpljoin1. splits; auto.
    eapply n_eibref_set_mq_maxm_preserve; eauto.
    destruct H.
    simpljoin1.
    right; left.
    splits; auto.
    eapply n_eibref_set_mq_maxm_preserve; eauto.
    simpljoin1.
    right; right.
    splits; eauto.
  -(*part2*)
    clear Hor.
    introv Hgetl.
    specialize (Hdel Hgetl).
    simpljoin1.
    splits; auto.
     eapply n_eibref_set_mq_maxm_preserve; eauto.
Qed.

Lemma Q_ECB_P_set_mq_all_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos et wtype flag maxm msize curm mqc wtype' flag' maxm' msize' curm' mqc', 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get mqeibs pos = Some (et, wtype, flag, maxm, msize, curm, mqc) ->
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs (set mqeibs pos (et, wtype', flag', maxm', msize', curm', mqc')).
Proof.
  introv Hsep Hget.
  unfold Q_ECB_P in *.
  introv Hget'.
  lets H00: Hsep Hget'. clear Hsep.
  destruct H00 as (Hor & Hdel).
  split.
  - (*part1*)
    destruct Hor.
    left.
    simpljoin1. splits; auto.
    eapply n_eibref_set_mq_all_preserve; eauto.
    destruct H.
    simpljoin1.
    right; left.
    splits; auto.
    eapply n_eibref_set_mq_all_preserve; eauto.
    simpljoin1.
    right; right.
    splits; eauto.
  -(*part2*)
    clear Hor.
    introv Hgetl.
    specialize (Hdel Hgetl).
    simpljoin1.
    splits; auto.
     eapply n_eibref_set_mq_all_preserve; eauto.
Qed.

Ltac forward_qp_assg_null ct :=
  combine_evaux (get_off_addr ct qptr_off);
  forward_evaux_null ct ltac:(eapply eq_tnull).

Lemma sum_int_30:
    ($ 4 +ᵢ
     ($ 1 +ᵢ
      ($ 1 +ᵢ
       ($ 1 +ᵢ
        ($ 1 +ᵢ
         ($ 1 +ᵢ
          ($ 1 +ᵢ
           ($ 1 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  Int.zero)))))))))))))) = $31. 
Proof.
  asserts_rewrite ($ 4 +ᵢ  Int.zero = $4). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 4 = $8). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 8 = $12). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 12 = $16). int auto.
  asserts_rewrite ($ 2 +ᵢ  $ 16 = $18). int auto.
  asserts_rewrite ($ 2 +ᵢ  $ 18 = $20). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 20 = $21). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 21 = $22). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 22 = $23). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 23 = $24). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 24 = $25). int auto.
  int auto. int auto. int auto. int auto.
Qed.

Lemma sum_int_25:
  ($ 1 +ᵢ
     ($ 1 +ᵢ
      ($ 1 +ᵢ
       ($ 1 +ᵢ
        ($ 1 +ᵢ
         ($ 1 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  Int.zero)))))))))))) = $26. 
Proof.
  asserts_rewrite ($ 4 +ᵢ  Int.zero = $4). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 4 = $8). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 8 = $12). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 12 = $16). int auto.
  asserts_rewrite ($ 2 +ᵢ  $ 16 = $18). int auto.
  asserts_rewrite ($ 2 +ᵢ  $ 18 = $20). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 20 = $21). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 21 = $22). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 22 = $23). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 23 = $24). int auto.
    asserts_rewrite ($ 1 +ᵢ  $ 24 = $25). int auto.
  int auto.
Qed.


Lemma int16_modu_le : 
  forall x,  (if Int.unsigned (Int.modu x ($ Int16.modulus)) <=?
                                     Int16.max_unsigned
                                  then true
                                  else false) = true.
Proof.
  intros.
  assert ( Int.unsigned (Int.modu x ($ Int16.modulus)) <=? Int16.max_unsigned = true).
  unfold Int.modu.
  unfold Int16.max_unsigned.
  change Int16.modulus with 65536.
  repeat ur_rewriter.
  apply Zle_imp_le_bool.
  simpl.
  lets bb: @Z_mod_lt (Int.unsigned x) 65536.
  mauto.
  lets bb: @Z_mod_lt (Int.unsigned x) 65536.
  change Int.max_unsigned with (65536*65536-1).
  mauto.
  rewrite H.
  auto.
Qed.

Lemma qb_get_not_null':
  forall mqvl qattrb hld vll1 vll2 idx cpn,
    MqEIBAarray_P (Vint32 Int.zero) mqvl qattrb hld ->
    Qattr_full_P' vll1 idx cpn ->
    vll1 ++ vll2 = mqvl ->
    length vll1 = ∘ (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) * (Int.unsigned idx + 1)) ->
    length mqvl = ∘ (OS_USER_MAX_EVENTS / 3) ->
   ~(exists i wtype flag maxm msize curm mqc,
          get qattrb i = Some (Null, wtype, flag, maxm, msize, curm, mqc) /\ OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned idx <= (Int.unsigned i) < Z.of_nat (length vll1)).
Proof.
introv He Hf Heq Hl1 Hl.
funfold Hf.
introv H. 
simpljoin.
eapply qb_corr_alt' in He; eauto.
instantiate (1:= x) in He.
simpljoin.
unfold get in *.
unfold MqattrMap in *.
match goal with H: MqattrMod.get _ _ = _, H': MqattrMod.get _ _ = _ |- _ => rewrite H' in H; inverts H end.
destruct H4 as [ | [ | ]]; simpljoin; tryfalse.
eapply Hf; eauto.
erewrite <- nth_error_eq_nth_vallist in *.
unfold nat_of_Z in *.
match goal with H: nth_error (_ ++ _) _ = _ |- _ => rewrite nth_error_app1 in H; auto with zarith end.
eapply ge0_z_nat_le; auto with zarith.
apply Int.unsigned_range_2.
rewrite app_length.
auto with zarith.
Qed.

Lemma qb_getnull':
  forall vl vll1 vll2 qattrb hld i idx cpn,
    MqEIBAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) qattrb hld ->
    nth_Qattr_free_P' i (vll1 ++ vl :: vll2) idx cpn ->
    length vll1 = Z.to_nat i ->
    length (vll1 ++ vl :: vll2) = ∘ (OS_USER_MAX_EVENTS / 3) ->
     exists wtype flag maxm msize curm mqc,
      get qattrb (Int.repr i) = Some (Null, wtype, flag, maxm, msize, curm, mqc) /\
      V_QATTRpevent vl = Some Vnull.
Proof.
  introv He Hf Hl1 Hl2.
  funfold Hf.
  unfold nat_of_Z in *.
  rewrite <- Hl1 in H0.
  rewrite nth_vallist_get_idx in H0; inverts H0.
  rewrite app_length in Hl2.
  simpl in Hl2.
  rewrite Hl1 in Hl2.
  assert (Hi: ( i < (OS_USER_MAX_EVENTS / 3))).
  auto with zarith.
  assert (Hi': 0 <= i <= Int.max_unsigned).
  split.
  eapply Z.le_trans; eauto.
  eapply Ztac.mul_le; try apply Int.unsigned_range_2.
  assert (Hc: Int.unsigned cpn = 0 \/ Int.unsigned cpn <> 0) by tauto.
  destruct Hc as [Hc | Hc].
  rewrite Hc.
  rewrite Zdiv_0_r; auto with zarith.
  eapply Z.div_pos; try solve_usr_max_evts_rgn.
  pose proof (Int.unsigned_range_2 cpn).
  auto with zarith.
  solve_usr_max_evts_rgn.
  eapply mqattr_corr with (i:= Int.repr i) in He; auto with zarith.
  simpljoin.
  unfold V_QATTRpevent in *.
  unfold get in *; simpl in *.
  match goal with H: MqattrMod.get _ _ = _ |- _ => rewrite H end.
  match goal with H: _ \/ _ \/ _ |- _ => destruct H as [ ? | [ ? | ? ]]; simpljoin;
  match goal with
  H: nth_val ?n _ = _ , H': nth_val ?n _ = _ |- _ => rewrite H in H'; inverts H'; try rewrite H end
  end.
  repeat eexists; eauto.
  rewrite Int.unsigned_repr; auto with zarith.
  rewrite int_ltu_zero_eq_false; auto.
  rewrite Int.unsigned_repr; auto with zarith.
Qed.

Lemma OSMqCreateProof: 
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api mq_create
              (mqcreate, (Tint32, Tint32 :: Tint32 :: Tint32 :: Tint32 ::nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api mq_create
              (mqcreate, (Tint32, Tint32 :: Tint32 :: Tint32 :: Tint32 ::nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api mq_create = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}.
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  do 6 (destruct v'; try apply absabort_rule).
  rename v2 into vr_temp_dom.
  rename v3 into vr_temp_num.

  lzh_hoare_if;
  pure_auto. 

  assert (Hdisj: v1 <> Vint32 (Int.mone) \/ v1 = Vint32 (Int.mone)) by tauto.
  destruct Hdisj.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqcreate_absimp_max_msgs_err_abt;eauto.
  pure_auto.
  apply absinfer_eq.
  apply absabort_rule.
  
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqcreate_absimp_max_msgs_err;eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare forward.

  lzh_hoare_if;
  pure_auto.

  assert (Hdisj: v1 <> Vint32 (Int.mone) \/ v1 = Vint32 (Int.mone)) by tauto.
  destruct Hdisj.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqcreate_absimp_msg_size_err_abt;eauto.
  pure_auto.
  apply absinfer_eq.
  apply absabort_rule.
  
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqcreate_absimp_msg_size_err;eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare forward.

  lzh_hoare_if;
  pure_auto.

  destruct LHift_true as (LH1 & LH2 & LH3).
  assert (Hdisj: v1 <> Vint32 (Int.mone) \/ v1 = Vint32 (Int.mone)) by tauto.
  destruct Hdisj.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqcreate_absimp_mq_blockflag_err_abt;eauto.
  clear - LH1 LH2 LH3. pure_auto.
  pure_auto.
  apply absinfer_eq.
  apply absabort_rule.
  
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqcreate_absimp_mq_blockflag_err;eauto.
  clear - LH1 LH2 LH3. pure_auto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare forward.

  lzh_hoare_if;
  pure_auto.
  
  assert (Hdisj: v1 <> Vint32 (Int.mone) \/ v1 = Vint32 (Int.mone)) by tauto.
  destruct Hdisj.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqcreate_absimp_waitq_type_err_abt;eauto.
  pure_auto.
  apply absinfer_eq.
  apply absabort_rule.
  
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqcreate_absimp_waitq_type_err;eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare forward.
  clear  Hif_false Hif_false0 Hif_false1 Hif_false2.

  (*OSIntNesting start *)
  hoare forward prim.
  unfold AGVars.
  hoare unfold.
  assert (Hit: Int.ltu ($ 0) v'34 = true \/ Int.ltu ($ 0) v'34 = false)by int auto.
  destruct Hit as [Hit | Hit].
  hoare forward; rewrite Hit. simpl; pure_auto.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mqcreate_absimp_iserr; try pure_auto.
  hoare forward prim.
  unfold AGVars.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep pauto.
  auto.
  pure_auto.
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  simpl in H3. destruct H3; tryfalse.
  hoare forward; rewrite Hit. simpl; pure_auto.
  hoare unfold. simpl in H3; tryfalse.
  instantiate (1:= Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  hoare forward prim.
  unfold AGVars.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep pauto.
  auto.
  pure_auto.
  clear.
  (* end add *)

  (*ENTER_CRITICAL;ₛ*)
  hoare forward prim.
  unfold EvtInv.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre ( R_Q_Data_P).
  eapply pure_split_rule'; introv Hrqdata.
  hoare unfold.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat PartitionInv.
  eapply unfold_PartitionInv_frm; eauto.
  unfold PartitionInv_part2.
  hoare normal pre.
  hoare_ex_intro.
  hoare_lifts_trms_pre R_Cpartnum_Dom2idx_P.
  eapply pure_split_rule'; introv Hrcpn0.
  hoare_lifts_trms_pre (AMuxEIBs, ASemEIBs, AMqEIBs).
  unfold ASemEIBs.
  unfold AMqEIBs.
  unfold AMuxEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (AMqCap, AMuxCap, ASemCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ AMqCap ?l1 ?vl1 ** AMuxCap ?l2 ?vl2 ** ASemCap ?l3 ?vl3 ** _ }} _ {{ _ }} =>
  rename l1 into lmq; rename l2 into lmux; rename l3 into lsem;
  rename vl1 into mqcapvl; rename vl2 into muxcapvl; rename vl3 into semcapvl end.
  hoare_lifts_trms_pre ( MqCapArray_P, length  mqcapvl, MuxCapArray_P, length muxcapvl,
                                              SemCapArray_P, length semcapvl).
  eapply pure_split_rule'; introv Hmqcap_vl.
  eapply pure_split_rule'; introv Hmqcap_len.
  eapply pure_split_rule'; introv Hmuxcap_vl.
  eapply pure_split_rule'; introv Hmuxcap_len.
  eapply pure_split_rule'; introv Hsemcap_vl.
  eapply pure_split_rule'; introv Hsemcap_len.
  hoare_lifts_trms_pre ( RH_SEM_NOT_IN_CORE_P, RH_Q_NOT_IN_CORE_P ).
  eapply pure_split_rule'; introv Hs_nc.
  eapply pure_split_rule'; introv Hq_nc.
  hoare unfold.
  unfold Adomain2index.
  unfold Adomain2index'.
  unfold AKsCurDomain.
  unfold ACorepartnum.
  hoare_lifts_trms_pre (array_type_vallist_match, RLH_Dom2idx_P, RHL_Dom2idx_P, Int.mone).
  eapply pure_split_rule'; introv Hdom_mat; destruct Hdom_mat as (Hdom_mat & Hlen_dom).
  eapply pure_split_rule'; introv Hlh_dom.
  eapply pure_split_rule'; introv Hhl_dom.
  eapply pure_split_rule'; introv Hcd_cases.
  hoare_lifts_trms_pre (Aisr, Ais).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).

    (*y ′ =ᶠ getFreePos (·′ 2·);ₛ*)

  hoare_lifts_trms_pre (Aop, kscurdom).
  match goal with
  | |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** HKsCurDomain ?idx ** _ }} _ {{ _ }} =>
     rename idx into vcurd
  end.
  assert(Hvcurd : vcurd = Int.mone \/ vcurd <> Int.mone) by tauto.
  destruct Hvcurd as [Habt | Hvcurd].
  eapply abscsq_rule.
  apply noabs_oslinv.
  do 5 try (eapply absinfer_trans; [ eapply absinfer_choice2; eauto; try can_change_aop_solver | idtac]).
  eapply absinfer_kscurdom_ext_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.
  eapply abscsq_rule.
  apply noabs_oslinv.
  do 5 try (eapply absinfer_trans; [ eapply absinfer_choice2; eauto; try can_change_aop_solver | idtac]).
  eapply absinfer_kscurdom_ext; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  destruct Hcd_cases as [Hcd_rgn | Hf]; try subst; tryfalse; auto.

  hoare_lifts_trms_pre (Aop, Domain2Index, ksCurDomain).
  match goal with
  | H: length ?vl = ?len
    |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** _ Domain2Index _ ?vl ** GV ksCurDomain @ _ |-> Vint32 ?idx ** _ }} _ {{ _ }} =>
     assert (Hle_len: (Z.to_nat (Int.unsigned idx) < len)%nat)
  end.
  solve_part_int_rgn.
  lets Hnth: Hle_len.
  eapply pure_lib.nthval'_has_value in Hnth; eauto.
  destruct Hnth as (rv_dom & Hnth & Hmat).
  hoare_lifts_trms_pre (Aop, kscurdom, domindexlist).
  match goal with
    H: RLH_Dom2idx_P _ _ |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** _ ** HDomain2index ?absdomls ** _ }} _ {{ _ }} =>
     rename absdomls into domls
  end.
  assert (Hget_dom:get domls  vcurd = Some rv_dom).
  eapply Hlh_dom; eauto.
  eapply inline_bittblfunctions.nth_val'2nth_val; eauto.

  assert (Hrv_dom: vr_temp_dom <> Vint32 rv_dom \/ vr_temp_dom = Vint32 rv_dom) by tauto.
  destruct Hrv_dom as [Habt | Hrv_dom].
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_get_temp_dom_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_get_temp_dom_succ; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  subst vr_temp_dom.

  hoare_lifts_trms_pre (Aop, cpartnum).
  match goal with
    | |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** Hcorepartnum ?cpn ** _ }} _ {{ _ }} =>
     rename cpn into rv_cpn
  end.
  assert (Hrv_num: vr_temp_num <> Vint32 rv_cpn \/ vr_temp_num = Vint32 rv_cpn) by tauto.
  destruct Hrv_num as [Habt | Hrv_num].
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_get_temp_num_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_get_temp_num_succ; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  subst vr_temp_num.

   eapply seq_rule.
  hoare_lifts_trms_pre Aop.
  eapply calle_rule_lvar'; 
            [ intuition eauto  | 
              intros; do 5 try 
                         (apply rvl_elim;[ symbolic_execution | ]);
              first [apply rvl_nil | simpl;auto] | 
              intros;  unfold_spec |
              idtac |
              idtac |
              simpl;eauto | 
              sep_unfold_funpost |
              sep_unfold_funpre 
              ].
(*   hoare forward. *)
  unfold Adomain2index.
  unfold Adomain2index'.
  unfold AKsCurDomain.
  unfold ACorepartnum.
  sep normal. sep eexists.
  sep cancel Domain2Index.
  sep cancel ksCurDomain.
  sep cancel ACorepartnum'.
  sep cancel domindexlist.
  sep cancel cpartnum.
  sep cancel AMqAttr.
  sep cancel ASeminfo.
  sep cancel APthreadMutex.
  sep cancel p_local.
  trycancel.
  sep cancel A_isr_is_prop.
  sep cancel Aier.
  sep cancel Aop.
  sep cancel y.
  sep split; eauto.

  simpl. eauto.
  pure_auto.
(*   pure_auto. *)
  unfold retpost. introv Hsat.
  inverts Hsat; sep pauto.
  get_hsat Hsat;
  do 5 try (get_hsat Hsat; destruct Hsat; sep pauto).

  introv Hsat. 
  sep destruct Hsat.
  destruct Hsat as [Hsat | Hsat];
  do 5 (try destruct Hsat as [Hsat | Hsat];
   try (sep destruct Hsat;
  eexists; sep cancel p_local; simpl; auto)).
  
  introv Hsat. 
  sep destruct Hsat.
  eexists; sep cancel p_local; simpl; auto.

  hoare unfold.
  eapply backward_rule1. 
  introv Hsat; 
  do 4 (eapply disj_split in Hsat;
  destruct Hsat as [Hsat | Hsat];
  [ sep normal in Hsat; sep destruct Hsat;
                   sep split in Hsat; tryfalse| idtac]).
  eapply disj_split in Hsat; eapply adisj_intro;
    destruct Hsat as [Hsat | Hsat]; [left; eauto | right].
  eapply disj_split in Hsat; eapply adisj_intro;
    destruct Hsat as [Hsat | Hsat]; [left; eauto | right].
  eauto.
  rename H0 into Hsem_p; rename H10 into Hrh_sem;
(*   rename H11 into Hsem_nc; *)
  rename H1 into Hmux_p; rename H12 into Hrh_mux.
    hoare forward; [idtac | hoare forward];
  [ | | hoare unfold; tryfalse ];
  hoare normal pre;
  [ do 7 try (eapply ex_intro_rule; intros) | do 6 try (eapply ex_intro_rule; intros)];
  eapply ex_intro_rule; intro dom2index;
  eapply ex_intro_rule; intro domls';
  eapply ex_intro_rule; intro kscurd;
  eapply ex_intro_rule; intro cpn;
  eapply ex_intro_rule; intro idx;
[ eapply ex_intro_rule; intro lsem';
    eapply ex_intro_rule; intro lmux';
    eapply ex_intro_rule; intro lmq'
   | eapply ex_intro_rule; intro mqvll1;
     eapply ex_intro_rule; intro mqvll2;
     eapply ex_intro_rule; intro lsem';
     eapply ex_intro_rule; intro lmux';
     eapply ex_intro_rule; intro lmq'];
  hoare_lifts_trms_pre (DOMAIN_SIZE, R_Cpartnum_Dom2idx_P, nth_val');
  try (eapply pure_split_rule'; introv Hvcd_rgn;
           destruct Hvcd_rgn as (Hvcd_rgn1 & Hvcd_rgn2);
          eapply pure_split_rule'; introv Hrcpn;
          eapply pure_split_rule'; introv Hnth_dom);
  try (hoare_lifts_trms_pre ( mqvll2, length mqvll1);
           eapply pure_split_rule'; introv Hmq_eq;
           eapply pure_split_rule'; introv Hlen_mqvll1;
           protect Hmq_eq);
  hoare unfold; try inverts H12; (* eq. on logicl *) 
  rewrite Hnth_dom in Hnth; inverts Hnth.

  (* start QAttr_full_P *)
  2: {
    (* pos ′ =ₑ 〈 long 〉 y ′;ₛ *)
    hoare forward.
    hoare_lifts_trms_pre Aop.
    eapply assign_rule_lvar.
    split; sep pauto.
    intros.
    eapply cast_rv_tint8_tint32.
    symbolic_execution.
    simpl; auto.
    apply assign_type_match_true; simpl; auto.

    intros.
    sep pauto. sep cancel p_local. sep pauto.

    (* If (pos ′ ==ₑ ′ 255) *)
    lets Hrgn: usr_max_evts_rgn.
    destruct Hrgn as (Hrgn3 & Hrgn4).
    lets Hrgn': usr_max_evts_rgn'.
    destruct Hrgn' as (Hrgn5 & Hrgn6).
    hoare forward.
    rewrite Int.eq_true.
    hoare unfold.
    hoare_lifts_trms_pre (AMqAttr).
    match goal with | |- {| _ , _, _, _, _, _ |} |- _ {{ AMqAttr _ ?vl ** _ }} _ {{ _ }} =>
    hoare_assert_pure (length vl = ∘ (OS_USER_MAX_EVENTS / 3))
    end.
    {
      get_hsat Hsat.
      sep_lifts_trms_in Hsat AMqAttr.
      eapply aqattr_len_frm in Hsat.
      auto.
    }
    hoare_split_pure_all.
    lets Hget_full: qb_get_not_null' H H1 Hmq_eq Hlen_mqvll1 H15.
    rewrite Hlen_mqvll1 in Hget_full.
    unfold nat_of_Z in Hget_full.
    rewrite Z2Nat.id in Hget_full; auto with zarith.
    2:{ pose proof (Int.unsigned_range_2 rv_dom).
           eapply Ztac.mul_le; auto with zarith.
           assert (Hc: Int.unsigned cpn = 0 \/ Int.unsigned cpn <> 0) by tauto.
           destruct Hc as [Hc | Hc].
            rewrite Hc.
            rewrite Zdiv_0_r; auto with zarith.
            eapply Z.div_pos; try solve_usr_max_evts_rgn.
            pose proof (Int.unsigned_range_2 cpn).
            auto with zarith. }
    hoare_lifts_trms_pre (Aop, absmqattr).
    assert (Hv: v = V$ 255 \/ v <> V$ 255) by tauto.
    destruct Hv as [Hv | Hv].
    (* v <> V$ 255 *)
    2: {
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mqcreate_absimp_pos_abt.
      can_change_aop_solver.
      eauto. eauto.
      left. splits; auto.
      eapply absinfer_eq.
      apply absabort_rule.
    }
    (* v = V$ 255 *)
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mqcreate_absimp_pos_cons.
    can_change_aop_solver.
    eauto. eauto.
    left. splits; auto.
    eapply absinfer_eq.
    instantiate (1:= Afalse).
    subst v.

    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mqcreate_absimp_poserr.
    can_change_aop_solver. rewrite Int.eq_true; auto.
    eapply absinfer_eq.

    (*EXIT_CRITICAL;ₛ*)
    hoare_lifts_trms_pre (Aisr,Ais,Aier).
    transform_pre add_aemp_isr_is_prop ltac:(sep cancel Aisr; sep cancel Ais; sep cancel Aier).
    hoare forward prim.
    unfold EvtInv.
    unfold AMqEIBs.
    sep normal; sep eexists.
    sep cancel AMqCap.
    sep pauto;eauto.
    trycancel.
    sep cancel Aier.
    sep cancel AMqAttr.
    sep cancel p_local.
    unfold ASemEIBs.
    unfold AMuxEIBs.
    sep normal; sep eexists.
    sep cancel ASemCap.
    sep cancel AMuxCap.
    sep cancel ASeminfo.
    sep cancel APthreadMutex.
    sep cancel APthreadAttr.
    sep split; eauto.
    eapply fold_PartitionInv_frm.
    unfold PartitionInv_part2.
    sep normal; sep eexists.
    trycancel_PartitionInv.
    sep cancel CapabilityInv.
    sep pauto; eauto.
    auto.
    pure_auto.
    hoare forward. (*RETURN *)

    eapply hoare_disj_afalseP_l_pre.
    rewrite Int.eq_true. hoare_split_pure_all.
    match goal with H: val_inj _ = _ \/ _ |- _ => simpl in H; destruct H; tryfalse end.
  }
  (* end QAttr_full_P *)
  
  (* start nth_Qattr_free_P *)
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  lets Hrgn': usr_max_evts_rgn'.
  destruct Hrgn' as (Hrgn5 & Hrgn6).
  match goal with
   H: nth_Qattr_free_P' ?vy _ ?vidx ?vcpn |- _ =>
   assert (Hpos_range: 
                  (OS_USER_MAX_EVENTS / 3 / Int.unsigned vcpn * Int.unsigned vidx <= vy <
                  OS_USER_MAX_EVENTS / 3 / Int.unsigned vcpn * (Int.unsigned vidx + 1))%Z) by
   (funfold H; auto);
   rename vy into posv;
   hoare_assert_pure (1 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned vcpn * (Int.unsigned vidx + 1) 
                                        <= OS_USER_MAX_EVENTS / 3)
   end.
   { get_hsat Hsat.
      unfold ACorepartnum, ACorepartnum' in Hsat.
      sep split in Hsat. simpljoin.
      eapply user_max_evts_part_succ_rgn; auto with zarith.
      eapply Hrcpn0; eauto.
      eapply inline_bittblfunctions.nth_val'2nth_val; eauto.
    }
   eapply pure_split_rule'; introv Hpos_range'.
   destruct Hpos_range' as (Hpos_rgn1 & Hpos_rgn2).
   assert (Hdiv_rgn: 0 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn
                                                * Int.unsigned rv_dom).
  {
     eapply Ztac.mul_le; auto with zarith.
     apply Int.unsigned_range_2.
  }
  hoare forward.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_lvar.
  split; sep pauto.
  intros.
  eapply cast_rv_tint8_tint32. 
  symbolic_execution.
  clear -Hpos_range Hpos_rgn2 Hdiv_rgn Hrgn3 Hrgn4.
  change (Byte.max_unsigned) with 255.
  simpljoin.
  rewrite Int.unsigned_repr; try (split; solve_usr_max_evts_rgn).
  match goal with | |- (if ?p then _ else _) = _ => destruct p eqn:eq1; auto with zarith end.
  simpl; auto.
  apply assign_type_match_true; simpl; auto.

  intros.
  sep pauto. sep cancel p_local. sep pauto. 

  assert (Hif_false: Int.eq ($ posv) ($ 255) = false). 
  {
    clear -Hpos_range Hpos_rgn2 Hdiv_rgn Hrgn3 Hrgn4.
    int auto.
  }

  hoare forward.
  pure_auto.
  rewrite Hif_false.
  hoare unfold.
  simpl val_inj in *. tryfalse.
  instantiate (1:=Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare_split_pure_all.
  match goal with H: val_inj _ = _ \/ _  |- _ => clear H end. (* val_inj ... = ... \/ ...*)
  (*split AMqAttr*)
  destruct lmq' as (lmq_b & lmq_i).
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat AMqAttr.
  eapply AMqAttr_unfold_any_idx_frm with (idx:= Z.to_nat posv) in Hsat.
  eauto.
  lets Hl: aqattr_len_frm Hsat.
  clear -Hl Hpos_range Hpos_rgn2 Hdiv_rgn.
  rewrite Hl.
  unfold nat_of_Z.
  eapply Z2Nat.inj_lt;  auto with zarith.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  mytac.
  match goal with H: MqEIBAarray_P _ (_ ++ ?vl :: _) ?abs _ |- _ =>
  rename abs into mqls; rename vl into mqvl end.
  assert (Hget_null:
            exists wtype flag maxm msize curm mqc,
                                   get mqls ($ posv) = Some (Null, wtype, flag, maxm, msize, curm, mqc) 
                                   /\ V_QATTRpevent mqvl = Some Vnull). 
  {
    eapply qb_getnull'; eauto. 
  }
  destruct Hget_null as (wtype &flag &maxm &msize& curm& mqc & Hget_null & Hvnull).
  hoare_lifts_trms_pre (Aop, absmqattr).
  assert (Hv: v = Vint32 ($ posv) \/ v <> Vint32 ($ posv)) by tauto.  
  destruct Hv as [Hv | Hv].
  (* v <> Vint32 ($ v'33) *)
  2: {
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mqcreate_absimp_pos_abt.
    can_change_aop_solver.
    eauto. eauto.
    right. do 7 eexists. splits; eauto. 
    eapply absinfer_eq.
    apply absabort_rule.
  }
  (* v = Vint32 ($ v'33) *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqcreate_absimp_pos_cons.
  can_change_aop_solver.
  eauto. eauto.
  right. do 7 eexists. splits; eauto.
  eapply absinfer_eq.
  subst v.

  (*efield (Mq_Attr ′ [os_code_defs.pos ′]) pevent =ₑ 〈 OS_EVENT ∗ 〉 PlaceHolder;ₛ *)
  (* unfold the vallist of  efield (Mq_Attr ′ [pos ′]) *)
  lets Hsplit : H0.
  eapply new_array_type_vallist_match_split_mqattr in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_7 Hsp.
  repeat try (destruct Hvl as (? & Hvl)). subst.

  unfold AOSTCBPrioTbl.
  hoare normal pre.
  hoare_ex_intro.
  hoare forward.
  auto with zarith.
  {
    introv Hsat.
    unfold PlaceHolder.
    eapply cast_rv_tptr.
    eapply addrof_gvar_rv.
    apply astar_l_anotinlenv_intro.
    sep cancel (Agvarenv' OSPlaceHolder).
    eauto.
    sep_lifts_trms_in Hsat A_dom_lenv.
    apply astar_l_adomlenv_elim in Hsat.
    destruct Hsat.
    match goal with H: eq_dom_env _ _ |- _ => clear -H; unfolds in H; rename H into Henv end.
    unfold EnvMod.indom.
    pure_auto.
    destruct H as [[]].
    assert (~ (ListSet.set_In (OSPlaceHolder, t)
                              ((waitq_type, long)
         :: (msg_size, long)
            :: (max_msgs, long)
               :: (mq_blockflag, long)
                  :: (os_code_defs.pos, long)
                     :: (x, char_t) :: (y, char_t) :: (p, OS_EVENT ∗) :: nil))).
    simpl. 
    repeat (eapply Classical_Prop.and_not_or; split; [pure_auto | idtac]).
    auto.
    pure_auto.
    eapply H0. rewrite Henv. pure_auto.
    simpl; auto.
  }
  (* end of assign PlaceHolder *)

  hoare unfold.
  hoare_lifts_trms_pre (Aop, absmqattrid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqcreate_absimp_set_placeholder; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq.

  (* EXIT_CRITICAL;ₛ *)
  hoare_lifts_trms_pre (Aisr,Ais,Aier).
  transform_pre add_aemp_isr_is_prop ltac:(sep cancel Aisr; sep cancel Ais; sep cancel Aier).
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel Aier.
  sep cancel CoreCommuInv.
  unfold AOSTCBPrioTbl.
  unfold EvtInv.
  unfold AMqEIBs.
  assert (Hup: (x5 :: x :: x0 :: x1 :: x2 :: Vptr vhold_addr :: x4 :: nil) =
               update_nth_val 5 (x5 :: x :: x0 :: x1 :: x2 :: x3 :: x4 :: nil)  (Vptr vhold_addr))
  by (simpl; auto).
  sep normal; sep eexists.
  sep cancel AMqCap.
  sep pauto;eauto.
  trycancel.
  sep cancel (Aptrmapsto).
  unfold ASemEIBs; unfold AMuxEIBs.
  sep normal; sep eexists.
  sep cancel AMuxCap. sep cancel ASemCap.
  sep cancel ASeminfo. sep cancel APthreadMutex.
  sep split; eauto.
  sep cancel OSPlaceHolder.
  sep cancel p_local.
  sep cancel APthreadAttr.
  eapply AMqAttr_select_sn_ex_strong.
  eexists. exists (Z.to_nat posv). eexists.
  exists (x5 :: x :: x0 :: x1 :: x2 :: Vptr vhold_addr :: x4 :: nil).
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep_lifts_trms PartitionInv.
  eapply fold_PartitionInv_frm.
  unfold PartitionInv_part2.
  sep normal; sep eexists.
  trycancel_PartitionInv.
  sep pauto; eauto.
  sep cancel CapabilityInv.
  eauto.
  match goal with H: length (_ ++ _ :: _) = ∘ (OS_USER_MAX_EVENTS / 3) |- _ =>
  rewrite <- H end.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  clear -Hsp Hup.
  simpl in Hsp. destruct Hsp as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & _).
  simpl. splits; auto.

  eapply eibref_distinct_null_holder_preserve; eauto.
  3: {
    eapply SEM_ECB_P_null_holder_preserve; eauto.
  }
  2: {
    eapply MUX_ECB_P_null_holder_preserve; eauto.
  }
  eapply Q_ECB_P_null_holder_preserve; eauto.
  eapply RH_Q_NOT_IN_CORE_P_hold_neid; eauto.
  introv Hf; simpljoin; tryfalse.
  eapply RH_EIBlk_ECBlk_Q_P_set_to_hold; eauto.
  eapply MqCapArray_P_hold; eauto.
  {
    assert (Hur: posv = Int.unsigned (Int.repr posv)).
    {
      rewrite Int.unsigned_repr; auto.
       split; auto with zarith.  try solve_usr_max_evts_rgn.
    }
    rewrite Hur in H15.
    lets H00: mqattr_corr H (* EIBArray_P*) H15.
    match type of H00 with _ -> _ -> ?R => assert R; [apply H00 | ] end.
    rewrite int_ltu_zero_eq_false; auto.
    apply Int.unsigned_range_2.
    simpljoin1.
    match goal with H: get mqls _ = _, H': get mqls _ = _ |- _ => unfold get in H,H'; simpl in H,H'; rewrite H in H'; inverts H' end.
    rewrite Hup. rewrite Hur.
    eapply MqEIBAarray_P_hold_for_update_to_hold'; eauto.
    apply Int.unsigned_range_2.
  }
  auto.
  pure_auto.
  (* end of EXIT_CRITICAL;ₛ *)

  (*p ′ =ᶠ OSQCreate (·max_msgs ′·);ₛ*)
  change (cast_res (Vint32 i0) :: v0 :: nil) with ((cast_res (Vint32 i0) :: nil) ++ (v0 :: nil)).
  hoare forward.
  2:{  instantiate (3:= v0). instantiate (3:= (cast_res (Vint32 i0) :: nil)).
          sep cancel Aop.
          unfold init_lg.
          sep cancel p_local.
          eauto. }
  {
  destruct_s s.
  simpl.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat (Alvarmapsto max_msgs).
  sep remember (1 :: nil)%nat in Hsat.
  clear -Hsat.
  simpl in Hsat. simpljoin1.
  match goal with H: get e0 max_msgs = _ |- _ => rewrite H end.
  rewrite Int.unsigned_zero in *.
  match goal with H: mapstoval _ _ _ _ _ |- _ =>
  eapply mapstoval_load in H; eauto;
  try eapply load_local in H; eauto;
  try rewrite H end.
  simpl.
  splits; auto.
  }
  pure_auto.

  unfold retpost. introv Hsat.
  inverts Hsat; sep pauto.
  get_hsat Hsat. sep destruct Hsat.
  sep split in Hsat. simpljoin1. pure_auto.
  simpl.
  rewrite int16_modu_le; auto. 

  introv Hsat. sep destruct Hsat.
  sep pauto. sep cancel p_local. simpl; auto.

  introv Hsat. sep destruct Hsat. 
  sep pauto. sep cancel p_local. simpl; auto.

  hoare unfold.
  match goal with H: _ = Vnull /\ _ \/ _, H': _ :: _ = _ :: _ |- _ =>
  rename H into Hretor; inverts H' end. (* logic_val ... = logic_val ... *)

(* ENTER_CRITICAL;ₛ *)
  hoare forward prim.
  unfold EvtInv.
  unfold AMqEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (AMqCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ AMqCap ?l ?vl ** _ }} _ {{ _ }} =>
  rename l into lmq; rename vl into mqcapvl' end.
  hoare_lifts_trms_pre (MqCapArray_P, length mqcapvl').
  eapply pure_split_rule'; introv Hmqcap_vl'.
  eapply pure_split_rule'; introv Hmqcap_len'.
  hoare unfold.
  destruct lmq as (lmq_b' & lmq_i').
  hoare_lifts_trms_pre (AMqAttr).
  match goal with | |- {| _ , _, _, _, _, _ |} |- _ {{ AMqAttr _ ?vl ** _ }} _ {{ _ }} =>
  hoare_assert_pure (length vl = ∘ (OS_USER_MAX_EVENTS / 3))
  end.
  {   get_hsat Hsat. sep_lifts_trms_in Hsat AMqAttr.  eapply aqattr_len_frm; eauto.  }
  eapply pure_split_rule'; introv Hl.

  (*efield (Mq_Attr ′ [pos ′]) pevent =ₑ p ′;ₛ*)
  (*split AMqAttr*)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat AMqAttr. 
  eapply AMqAttr_unfold_any_idx_frm with (idx := Z.to_nat posv) in Hsat; eauto.
  rewrite Hl.
  unfold nat_of_Z.
  auto with zarith.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  mytac.
  (*assign rule*)
  (* unfold the vallist of  efield (Mq_Attr ′ [pos ′]) *)  
  match goal with H: new_array_type_vallist_match _ _ |- _ => 
  lets Hsplit : H end. (* new_array_type_vallist_match ... *)
  eapply new_array_type_vallist_match_split_mqattr in Hsplit; eauto.
  clear Hsp1 Hsp2 Hsp.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_7 Hsp.
  simpljoin.

  assert (Hpos_ge: 0 <= posv).
  { auto with zarith. }
  hoare forward.
  pure_auto.
  (* end of assign *)

  hoare_lifts_trms_pre (tcbllsegevaux, AOSTCBList, p_local).
  eapply backward_rule1. 
  introv Hsat.
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  match goal with H: SEM_ECB_P ?loc ?ptr ?ecb ?fecbh ?fecbvl ?sem ?mux ?mq |- _ =>
  rename loc into locmp; rename ptr into ptrmp; rename ecb into ecbls;
  rename sem into semeibs; rename mux into muxeibs; rename mq into mqeibs
  end.
  match goal with H: join (sig _ (_, _, ?vp)) _ _ |- _ => rename vp into cur_evp end.
  match goal with H : join (sig tid ?vt) _ ?abs, H' : join _ ?abs locmp |- _ => rename vt into vct end.
  assert (Hevptr: get ptrmp tid = Some (Vnull, Vnull, cur_evp)).  
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  assert (Hloc: get locmp tid = Some vct).
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  assert (Heid: forall eid, cur_evp = Vptr eid -> (~ eib_ref semeibs muxeibs mqeibs eid) /\ is_que ecbls eid).  
  {
    introv Hevp.
    subst cur_evp.
    destruct Hretor as [Hnull | Heptr].
    destruct Hnull; tryfalse.
    destruct Heptr as (_ & Hcre2 & Hq_nc').
    subst .
    eapply q_ecb_cre2; eauto.
  } 
  assert (Hncre1: forall eid,
             cur_evp = Vptr eid ->
             ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid)). 
  {
    introv Hcp Hex. subst cur_evp.
    destruct Hex as (t & Htneq & Htle).
    destruct Hretor as [Hnull | Heptr].
    destruct Hnull. tryfalse.
    destruct Heptr. simpljoin. subst. 
    eapply evcre_nodup_cre1_cre2_contra; eauto.
  }
  assert (Hncre2: forall eid,
             cur_evp = Vptr eid ->
             ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid)).
  {
    introv Hcp Hex. subst cur_evp.
    destruct Hex as (t & Htneq & Htle).
    destruct Hretor as [Hnull | Heptr].
    destruct Hnull. tryfalse.
    destruct Heptr. simpljoin. subst.
    eapply evcre_nodup_cre2_cre2_contra; eauto.
  }
  assert (Hndel: forall eid,
             cur_evp = Vptr eid ->
             ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel eid)).  
  {
    introv Hcp Hex. subst cur_evp.
    destruct Hex as (t & Htneq & Htle).
    destruct Hretor as [Hnull | Heptr].
    destruct Hnull. tryfalse.
    destruct Heptr. simpljoin. subst.
    specialize (Heid eid (eq_refl _)). destruct Heid.
    eapply ecbdel_que_contra; eauto.    
  }
  hoare_assign_evaux.
  hoare_assign_evaux.
  unfold isevloc; eauto.
  fold_evaux_q_loc (V$ os_code_defs.__EvLoc_normal) Vnull.
  (* end of assign evaux *)

  assert (Hv: posv = Int.unsigned (Int.repr posv)).
  {
    rewrite int_usign_eq; auto with zarith.
    solve_usr_max_evts_rgn.
  }
  rewrite Hv in H40.
  lets H00: mqattr_corr H24 H40.
  match type of H00 with _ -> _ -> ?R => assert (R); [apply H00 | ] end.
  rewrite int_ltu_zero_eq_false; auto.
  apply Int.unsigned_range_2.
  clear H00.
  destruct H48 as (eid_t & waittype & flags & maxmsg & msgsize & curmsgs & mqc' &
                                 (Hget & Heidor &Hwtype & Hflags& Hmmsg& Hmsize& Hcmsgs )).

  rewrite <- Hv in H40.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Astruct).
  match goal with H: _ |= Astruct _ mq_attr_t ?vl ** _ |- _ =>
  eapply AMqAttr_select_sn_ex_strong;
  eexists; exists (Z.to_nat posv); eexists;
  exists vl end.
  sep cancel Astruct.
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep pauto.
  rewrite <- H38.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  clear -Hsp H27.
  simpl in Hsp. destruct Hsp as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & _).
  simpl. splits; auto.
  pure_auto.

  match goal with
   H: V_QATTRmq_flags ?vl = _ 
   |- {| _, _, _, _, _, _ |} |- _ {{ AMqAttr _ (_ ++ (?v1 :: ?v2 :: ?v3 :: ?v4 :: ?v5 :: ?v6 :: ?v7 :: nil ) :: _) ** _ }} _ {{ _ }} =>
      assert (Hup: (v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: nil )  = update_nth_val 5 vl v6) 
    by (simpl; auto) end.
  hoare_lifts_trms_pre (Aop, absmqattrid, evlocid, evptrid, curtid).
  destruct H27 as [Hnull | (eid & Hvp)]; subst.
  (* p is null *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqcreate_absimp_set_ecb_ptr_null; eauto.
  unfold CurTid. can_change_aop_solver.
  eapply absinfer_eq.
  (* EXIT_CRITICAL *)
  lets Hset: EvAuxPtrMod.get_set_same Hevptr.
  rewrite Hup.
  unfold set. unfold EvAuxLocMap, EvAuxPtrMap,MqattrMap. rewrite Hset.
  hoare forward prim.
  sep cancel CoreCommuInv.
  sep cancel Aier.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep normal.
  sep eexists.
  sep split; eauto.
  sep cancel CurTid.
  sep cancel flag_off.
  try_cancel_evaux_asst.
  2: { unfold isevloc. splits; eauto. }
  unfold EvtInv.
  unfold AMqEIBs.
  unfold tcbllsegevaux.
  sep normal. sep eexists.
  sep cancel AMqCap.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqAttr.
  sep cancel llsegevaux.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.
  eapply eibref_distinct_infonull_preserve; eauto.
  eapply evdel_nodup_normal_preserve; eauto.
  eapply evcre_nodup_normal_preserve; eauto.
  3: { eapply sem_ecb_p_infonull_preserve; eauto. }
  2: { eapply mux_ecb_p_infonull_preserve; eauto. }
  eapply q_ecb_p_infonull_preserve; eauto.
  eapply RH_Q_NOT_IN_CORE_P_hold_neid; eauto.
  introv Hf; simpljoin; tryfalse.
  eapply RH_EIBlk_ECBlk_Q_P_null_preserve; eauto.
  eapply MqCapArray_P_hold; eauto.
  eapply MqEIBAarray_P_hold_for_update_to_null'; eauto.
  rewrite Hv. apply Int.unsigned_range_2.
  auto.
  pure_auto.

  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqcreate_absimp_create_error; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  (* If (p ′ ==ₑ NULL){RETURN ′ (-1)};ₛ *) 
  hoare forward.
  hoare unfold.
  hoare forward.
  clear.
  eapply hoare_disj_afalseP_l_pre.
  hoare_split_pure_all.
  destruct H; tryfalse.
  (* p <> Vnull *)
  casetac eid vhold_addr Habt Hvp.
  (* eid = vhold_addr *)
  subst.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqcreate_absimp_set_ecb_holder_abt; eauto.
  unfold CurTid. can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.
  (* eid <> vhold_addr *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqcreate_absimp_set_ecb_ptr_n_null; eauto.
  unfold CurTid. can_change_aop_solver.
  eapply absinfer_eq.
  (* EXIT_CRITICAL *)
  specialize (Heid eid (eq_refl _)).
  specialize (Hncre1 eid (eq_refl _)).
  specialize (Hncre2 eid (eq_refl _)).
  specialize (Hndel eid (eq_refl _)).
  rewrite Hup.
  hoare_assert_pure (CORESEM_INECB_P ecbls).
  { get_hsat Hsat.
     unfold CoreCommuInv in Hsat.
     sep normal in Hsat; sep destruct Hsat; sep split in Hsat.
     simpljoin; auto.
  }
  eapply pure_intro_rule'; introv Hcsem.
  destruct Hretor as [ (Hnull & _) | (_ & Heq & (ptr & Heq2 & Hq_nc')) ]; tryfalse.
  inverts Heq2. subst.
  hoare forward prim.
  sep cancel CoreCommuInv.
  sep cancel Aier.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep normal.
  sep eexists.
  sep split; eauto.
  sep cancel CurTid.
  sep cancel flag_off.
  try_cancel_evaux_asst.
  2: { unfold isevloc. splits; eauto. }
  unfold EvtInv.
  unfold AMqEIBs.
  unfold tcbllsegevaux.
  sep normal; sep eexists.
  sep cancel AMqCap.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqAttr.
  sep cancel llsegevaux.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.
  eapply eibref_distinct_noref_eid_preserve; eauto.
  eapply evdel_nodup_normal_null_preserve; eauto.
  eapply evcre_nodup_normal_null_preserve; eauto.
  3: {
    eapply SEM_ECB_P_normal_null_preserve; eauto. 
  }
  2: {
    eapply MUX_ECB_P_normal_null_preserve; eauto.
  }
  eapply Q_ECB_P_normal_null_preserve; eauto.
  eapply RH_Q_NOT_IN_CORE_P_hold_eid_nref; eauto.
  clear -Hq_nc'. unfolds in Hq_nc'; simpljoin. auto.
  eapply RH_EIBlk_ECBlk_Q_P_ptr_preserve; eauto.
  eapply MqCapArray_P_hold; eauto.
  eapply MqEIBAarray_P_hold_for_update_to_tid'; auto.
  {
    match goal with H: length ?vl = _ |- _ = $ Z.of_nat (length ?vl) => rewrite H end.
    rewrite Z2Nat.id; auto.
  }
  {
    match goal with H: length ?vl = _ |- Z.of_nat (length ?vl) <= _ => rewrite H end.
    solve_usr_max_evts_rgn.
  }
  apply Int.unsigned_range_2.
  auto.
  pure_auto.
  destruct ptr as (vr_b, vr_i).
  (* false If (p ′ ==ₑ NULL){RETURN ′ (-1)};ₛ *) 
  hoare forward.
  hoare unfold. tryfalse.
  eapply hoare_disj_afalseP_l_pre.
  hoare_split_pure_all.
  rename H18 into Hrgn1; rename H19 into Hrgn2.
  clear -Hrgn1 Hrgn2 Hpos_rgn1 Hpos_rgn2 Hdiv_rgn Hpos_ge.
  (*ENTER_CRITICAL;ₛ*)
  hoare forward prim.
  unfold EvtInv.
  unfold AMqEIBs.
  hoare normal pre.
  hoare_ex_intro.
  hoare_lifts_trms_pre (RH_Q_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hq_nc.
  hoare_lifts_trms_pre (AMqCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ AMqCap ?l ?vl ** _ }} _ {{ _ }} =>
  rename l into lmq; rename vl into mqcapvl end.
  hoare_lifts_trms_pre (MqCapArray_P, length mqcapvl).
  eapply pure_split_rule'; introv Hmqcap_vl.
  eapply pure_split_rule'; introv Hmqcap_len.
  hoare unfold.
  destruct lmq as (lmq_b & lmq_i).
  match goal with H: MqEIBAarray_P _ ?vl _ _ |- _ =>
  hoare_assert_pure (length vl = (∘ (OS_USER_MAX_EVENTS / 3)))
  end.
  {  get_hsat Hsat. sep_lifts_trms_in Hsat AMqAttr.  eapply aqattr_len_frm; eauto.  }
  eapply pure_split_rule'; introv Hl.

  (*efield (Mq_Attr′[pos′]) mq_maxmsg =ₑ max_msgs′;ₛ*)
  (*split AMqAttr*)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat AMqAttr. 
  eapply AMqAttr_unfold_any_idx_frm with (idx := Z.to_nat posv) in Hsat; eauto.
  rewrite Hl.
  unfold nat_of_Z.
  auto with zarith.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  simpljoin.

  (* unfold the vallist of  efield (Mq_Attr ′ [pos ′]) *)
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  lets Hsplit : H2.
  eapply new_array_type_vallist_match_split_mqattr in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_7 Hsp.
  simpljoin.
  hoare forward.
  assert (Hv: posv = Int.unsigned ($ posv)).
  {
    rewrite Int.unsigned_repr; try solve_usr_max_evts_rgn.
  }
  rewrite Hv in H13.
  assert (Hltuf: Int.ltu ($posv) Int.zero = false).
  {
    rewrite int_ltu_zero_eq_false; auto.
  }
  assert (Hle: Int.unsigned ($ posv) <= Int.max_unsigned).
  {
    apply Int.unsigned_range_2.
  }
  lets H00: mqattr_corr H H13 Hltuf Hle.
  simpljoin1.

  hoare_lifts_trms_pre (Aop, absmqattrid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqcreate_absimp_set_maxmsg; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  (* EXIT_CRITICAL;ₛ *)
  hoare forward prim.
  sep cancel Aier.
  sep cancel CoreCommuInv.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  unfold AMqEIBs.
  assert (Hup: (x5 :: x :: Vint32 i0 :: x1 :: x2 :: x3 :: x4 :: nil)  = 
               update_nth_val 2 (x5 :: x :: x0 :: x1 :: x2 :: x3 :: x4 :: nil) (Vint32 i0)).
  simpl;eauto.
  sep normal; sep eexists.
  sep cancel AMqCap.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs. 
  sep cancel APthreadAttr.
  eapply AMqAttr_select_sn_ex_strong.
  eexists. exists (Z.to_nat posv). eexists.
  exists (x5 :: x :: Vint32 i0 :: x1 :: x2 :: x3 :: x4 :: nil).
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel CapabilityInv.
  sep pauto; eauto.
  rewrite Hv.
  splits; auto. congruence.
  rewrite <- Hl.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  simpl.
  simpl in Hsp. simpljoin. splits; auto.
  eapply eibref_distinct_set_mq_all_mqeibs; eauto.
  3: { eapply SEM_ECB_P_set_mq_all_preserve; eauto. }
  2: { eapply MUX_ECB_P_set_mq_all_preserve; eauto. } 
  eapply Q_ECB_P_set_mq_all_preserve; eauto.
  eapply RH_Q_NOT_IN_CORE_P_hold_same_ptr; eauto.
  eapply RH_EIBlk_ECBlk_Q_P_set_mq_all_preserve; eauto.
  eapply MqCapArray_P_hold; eauto.
  rewrite Hup.
  eapply MqEIBAarray_P_hold_for_update_mq_maxm'; eauto.
  {
        match goal with H: length ?vl = _ |- _ = $ Z.of_nat (length ?vl) => rewrite H end.
        rewrite Z2Nat.id; auto with zarith. rewrite Int.repr_unsigned; auto.
  }
  {
    match goal with H: length ?vl = _ |- Z.of_nat (length ?vl) <= _ => rewrite H end.
    solve_usr_max_evts_rgn.
  }
  auto.
  pure_auto.
  (* end of EXIT_CRITICAL *)
   clear -Hrgn1 Hrgn2 Hv Hltuf Hle Hpos_rgn1 Hpos_rgn2 Hdiv_rgn Hpos_ge.
  (*ENTER_CRITICAL;ₛ*)
  hoare forward prim.
  unfold EvtInv.
  unfold AMqEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (AMqCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ AMqCap ?l ?vl ** _ }} _ {{ _ }} =>
  rename l into lmq; rename vl into mqcapvl' end.
  hoare_lifts_trms_pre (MqCapArray_P, length mqcapvl').
  eapply pure_split_rule'; introv Hmqcap_vl'.
  eapply pure_split_rule'; introv Hmqcap_len'.
  hoare unfold.
  destruct lmq as (lmq_b' & lmq_i').
  hoare_lifts_trms_pre (AMqAttr).
  match goal with | |- {| _ , _, _, _, _, _ |} |- _ {{ AMqAttr _ ?vl ** _ }} _ {{ _ }} =>
  hoare_assert_pure (length vl = ∘ (OS_USER_MAX_EVENTS / 3))
  end.
  {   get_hsat Hsat. sep_lifts_trms_in Hsat AMqAttr.  eapply aqattr_len_frm; eauto.  }
  eapply pure_split_rule'; introv Hl.

  (*efield (Mq_Attr′[pos′]) mq_msgsize *)
  (*split AMqAttr*)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat AMqAttr. 
  eapply AMqAttr_unfold_any_idx_frm with (idx := Z.to_nat posv) in Hsat; eauto.
  rewrite Hl.
  unfold nat_of_Z.
  auto with zarith.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  simpljoin.

  (* unfold the vallist of  efield (Mq_Attr ′ [pos ′]) *)
  lets Hsplit : H3.
  eapply new_array_type_vallist_match_split_mqattr in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_7 Hsp.
  simpljoin.
  hoare forward.
  rewrite Hv in H14.
  lets H00: mqattr_corr H H14 Hltuf Hle.
  simpljoin1.

  hoare_lifts_trms_pre (Aop, absmqattrid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqcreate_absimp_set_msgsize; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  (* EXIT_CRITICAL;ₛ *)
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  hoare forward prim.
  sep cancel Aier.
  sep cancel CoreCommuInv.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  unfold AMqEIBs.
  assert (Hup: (x5 :: x :: x0 :: Vint32 i1 :: x2 :: x3 :: x4 :: nil)  = 
               update_nth_val 3 (x5 :: x :: x0 :: x1 :: x2 :: x3 :: x4 :: nil) (Vint32 i1)).
  simpl;eauto.
  sep normal; sep eexists.
  sep cancel AMqCap.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs. 
  sep cancel APthreadAttr.
  eapply AMqAttr_select_sn_ex_strong.
  eexists. exists (Z.to_nat posv). eexists.
  exists (x5 :: x :: x0 :: Vint32 i1 :: x2 :: x3 :: x4 :: nil).
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel CapabilityInv.
  sep pauto; eauto.
  rewrite Hv.
  splits; auto. congruence.
  rewrite <- Hl.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  simpl.
  simpl in Hsp. simpljoin. splits; auto.
  eapply eibref_distinct_set_mq_all_mqeibs; eauto.
  3: { eapply SEM_ECB_P_set_mq_all_preserve; eauto. }
  2: { eapply MUX_ECB_P_set_mq_all_preserve; eauto. }
  eapply Q_ECB_P_set_mq_all_preserve; eauto.
  eapply RH_Q_NOT_IN_CORE_P_hold_same_ptr; eauto.
  eapply RH_EIBlk_ECBlk_Q_P_set_mq_all_preserve; eauto.
  eapply MqCapArray_P_hold; eauto.
  rewrite Hup.
  eapply MqEIBAarray_P_hold_for_update_mq_mgs'; eauto.
  {
     match goal with H: length ?vl = _ |- _ = $ Z.of_nat (length ?vl) => rewrite H end.
        rewrite Z2Nat.id; auto with zarith. rewrite Int.repr_unsigned; auto.
  }
  {
    match goal with H: length ?vl = _ |- Z.of_nat (length ?vl) <= _ => rewrite H end.
    solve_usr_max_evts_rgn.
  }
  auto.
  pure_auto.

  clear -Hrgn1 Hrgn2 Hv Hltuf Hle Hpos_rgn1 Hpos_rgn2 Hdiv_rgn Hpos_ge.
  (*ENTER_CRITICAL;ₛ*)
  hoare forward prim.
  unfold EvtInv.
  unfold AMqEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (AMqCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ AMqCap ?l ?vl ** _ }} _ {{ _ }} =>
  rename l into lmq; rename vl into mqcapvl' end.
  hoare_lifts_trms_pre (MqCapArray_P, length mqcapvl').
  eapply pure_split_rule'; introv Hmqcap_vl'.
  eapply pure_split_rule'; introv Hmqcap_len'.
  hoare unfold.
  destruct lmq as (lmq_b' & lmq_i').
  hoare_lifts_trms_pre (AMqAttr).
  match goal with | |- {| _ , _, _, _, _, _ |} |- _ {{ AMqAttr _ ?vl ** _ }} _ {{ _ }} =>
  hoare_assert_pure (length vl = ∘ (OS_USER_MAX_EVENTS / 3))
  end.
  {   get_hsat Hsat. sep_lifts_trms_in Hsat AMqAttr.  eapply aqattr_len_frm; eauto.  }
  eapply pure_split_rule'; introv Hl.

  (*efield (Mq_Attr′[pos′]) mq_flags *)
  (*split AMqAttr*)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat AMqAttr. 
  eapply AMqAttr_unfold_any_idx_frm with (idx := Z.to_nat posv) in Hsat; eauto.
  rewrite Hl.
  unfold nat_of_Z.
  auto with zarith.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  simpljoin.

  (* unfold the vallist of  efield (Mq_Attr ′ [pos ′]) *)
  lets Hsplit : H3.
  eapply new_array_type_vallist_match_split_mqattr in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_7 Hsp.
  simpljoin.
  hoare forward.
  rewrite Hv in H14.
  lets H00: mqattr_corr H H14 Hltuf Hle.
  simpljoin1.

  hoare_lifts_trms_pre (Aop, absmqattrid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqcreate_absimp_set_flgs; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  (* EXIT_CRITICAL;ₛ *)
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  hoare forward prim.
  sep cancel Aier.
  sep cancel CoreCommuInv.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  unfold AMqEIBs.
  assert (Hup: (x5 :: Vint32 i :: x0 :: x1 :: x2 :: x3 :: x4 :: nil)  = 
               update_nth_val 1 (x5 :: x :: x0 :: x1 :: x2 :: x3 :: x4 :: nil) (Vint32 i)).
  simpl;eauto.
  sep normal; sep eexists.
  sep cancel AMqCap.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs. 
  sep cancel APthreadAttr.
  eapply AMqAttr_select_sn_ex_strong.
  eexists. exists (Z.to_nat posv). eexists.
  exists (x5 :: Vint32 i :: x0 :: x1 :: x2 :: x3 :: x4 :: nil).
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel CapabilityInv.
  sep pauto; eauto.
  rewrite Hv.
  splits; auto. congruence.
  rewrite <- Hl.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  simpl.
  simpl in Hsp. simpljoin. splits; auto.
  eapply eibref_distinct_set_mq_all_mqeibs; eauto.
  3: { eapply SEM_ECB_P_set_mq_all_preserve; eauto. }
  2: { eapply MUX_ECB_P_set_mq_all_preserve; eauto. }
  eapply Q_ECB_P_set_mq_all_preserve; eauto.
  eapply RH_Q_NOT_IN_CORE_P_hold_same_ptr; eauto.
  eapply RH_EIBlk_ECBlk_Q_P_set_mq_all_preserve; eauto.
  eapply MqCapArray_P_hold; eauto.
  rewrite Hup.
  eapply MqEIBAarray_P_hold_for_update_mq_flg'; eauto.
  {
     match goal with H: length ?vl = _ |- _ = $ Z.of_nat (length ?vl) => rewrite H end.
        rewrite Z2Nat.id; auto with zarith. rewrite Int.repr_unsigned; auto.
  }
  {
    match goal with H: length ?vl = _ |- Z.of_nat (length ?vl) <= _ => rewrite H end.
    solve_usr_max_evts_rgn.
  }
  auto.
  pure_auto.

   clear -Hrgn1 Hrgn2 Hv Hltuf Hle Hpos_rgn1 Hpos_rgn2 Hdiv_rgn Hpos_ge.
  (*ENTER_CRITICAL;ₛ*)
  hoare forward prim.
  unfold EvtInv.
  unfold AMqEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (AMqCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ AMqCap ?l ?vl ** _ }} _ {{ _ }} =>
  rename l into lmq; rename vl into mqcapvl' end.
  hoare_lifts_trms_pre (MqCapArray_P, length mqcapvl').
  eapply pure_split_rule'; introv Hmqcap_vl'.
  eapply pure_split_rule'; introv Hmqcap_len'.
  hoare unfold.
  destruct lmq as (lmq_b' & lmq_i').
  hoare_lifts_trms_pre (AMqAttr).
  match goal with | |- {| _ , _, _, _, _, _ |} |- _ {{ AMqAttr _ ?vl ** _ }} _ {{ _ }} =>
  hoare_assert_pure (length vl = ∘ (OS_USER_MAX_EVENTS / 3))
  end.
  {   get_hsat Hsat. sep_lifts_trms_in Hsat AMqAttr.  eapply aqattr_len_frm; eauto.  }
  eapply pure_split_rule'; introv Hl.

  (*efield (Mq_Attr′[pos′]) mq_waittype *)
  (*split AMqAttr*)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat AMqAttr. 
  eapply AMqAttr_unfold_any_idx_frm with (idx := Z.to_nat posv) in Hsat; eauto.
  rewrite Hl.
  unfold nat_of_Z.
  auto with zarith.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  simpljoin.

  (* unfold the vallist of  efield (Mq_Attr ′ [pos ′]) *)
  lets Hsplit : H3.
  eapply new_array_type_vallist_match_split_mqattr in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_7 Hsp.
  simpljoin.
  hoare forward.
  rewrite Hv in H14.
  lets H00: mqattr_corr H H14 Hltuf Hle.
  simpljoin1.

  hoare_lifts_trms_pre (Aop, absmqattrid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqcreate_absimp_set_wtp; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  (* EXIT_CRITICAL;ₛ *)
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  hoare forward prim.
  sep cancel Aier.
  sep cancel CoreCommuInv.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  unfold AMqEIBs.
  assert (Hup: (V$ PTHREAD_WAITQ_PRIO :: x :: x0 :: x1 :: x2 :: x3 :: x4 :: nil)  = 
               update_nth_val 0 (x5 :: x :: x0 :: x1 :: x2 :: x3 :: x4 :: nil) (V$ PTHREAD_WAITQ_PRIO)).
  simpl;eauto.
  sep normal; sep eexists.
  sep cancel AMqCap.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs. 
  sep cancel APthreadAttr.
  eapply AMqAttr_select_sn_ex_strong.
  eexists. exists (Z.to_nat posv). eexists.
  exists (V$ PTHREAD_WAITQ_PRIO :: x :: x0 :: x1 :: x2 :: x3 :: x4 :: nil).
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel CapabilityInv.
  sep pauto; eauto.
  rewrite Hv.
  splits; auto. congruence.
  rewrite <- Hl.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  simpl.
  simpl in Hsp. simpljoin. splits; auto.
  eapply eibref_distinct_set_mq_all_mqeibs; eauto.
  3: { eapply SEM_ECB_P_set_mq_all_preserve; eauto. }
  2: { eapply MUX_ECB_P_set_mq_all_preserve; eauto. }
  eapply Q_ECB_P_set_mq_all_preserve; eauto.
  eapply RH_Q_NOT_IN_CORE_P_hold_same_ptr; eauto.
  eapply RH_EIBlk_ECBlk_Q_P_set_mq_all_preserve; eauto.
  eapply MqCapArray_P_hold; eauto.
  rewrite Hup.
  eapply MqEIBAarray_P_hold_for_update_mq_wtp'; eauto.
  {
     match goal with H: length ?vl = _ |- _ = $ Z.of_nat (length ?vl) => rewrite H end.
        rewrite Z2Nat.id; auto with zarith. rewrite Int.repr_unsigned; auto.
  }
  {
    match goal with H: length ?vl = _ |- Z.of_nat (length ?vl) <= _ => rewrite H end.
    solve_usr_max_evts_rgn.
  }
  auto.
  pure_auto.

  assert (Hc: v1 <>V$ posv \/ v1 =V$ posv ) by tauto.
  destruct Hc.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqcreate_absimp_rv_pos_abt; eauto. 
  go. 
  eapply absinfer_eq. 
  eapply absabort_rule.

  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqcreate_absimp_rv_pos; eauto.
  go. 
  eapply absinfer_eq.

   (* return pos *) 
  hoare forward.
Qed.


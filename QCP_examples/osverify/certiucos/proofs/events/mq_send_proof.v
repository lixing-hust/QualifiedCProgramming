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

Require Import part_pos_rgn_spec.
Require Import part_pos_rgn_proof.
Require Import partinv_lemmas.

Require Import abs_infer_abt.
Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Open Scope int_scope.
Open Scope Z_scope.
Open Scope code_scope.
Open Scope list_scope.

Lemma mqsend_absimp_mqdeserr:
  forall mqdes rv P sch s,
    (Int.ltu mqdes Int.zero = true \/
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) mqdes = true \/ 
       mqdes = Int.repr (OS_USER_MAX_EVENTS / 3)) ->
    rv = (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_mqdes_err (|Vint32 mqdes :: rv :: nil|) ?? s ||> ** P) 
      (<|| END (Some (Vint32 (Int.mone))) ||> ** P). 
Proof. 
  infer_solver 0%nat.  
Qed.

Lemma mqsend_absimp_mqdeserr_abt:
  forall mqdes rv P sch s,
    (Int.ltu mqdes Int.zero = true \/
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) mqdes = true \/ 
       mqdes = Int.repr (OS_USER_MAX_EVENTS / 3)) ->
    rv <> (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_mqdes_err (|Vint32 mqdes :: rv :: nil|) ?? s ||> ** P) 
      (<|| ABORT ||> ** P). 
Proof.
  introv Hdes Hrv Hcaop. 
  eapply absinfer_trans.
  eapply absinfer_choice1. try eauto. 
  instantiate (1:= P). can_change_aop_solver. auto.
  eapply absinfer_abt; try can_change_aop_solver.
  unfolds. intros.
  eexists; exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.
  unfolds.
  do 2 eexists. 
  splits; try eauto.
  apply map_join_emp.
  repeat hmstep_call_consturctor.
  simpl in *.
  simpljoin.
  do 6 eexists.
  splits ; try eauto.
  eapply change_aop_rule; eauto.
Qed.

Lemma i_ge_z: 
  forall i, 
    Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\
    i <> Int.repr (OS_USER_MAX_EVENTS / 3) ->
    i = Int.zero \/ Int.ltu Int.zero i = true. 
Proof.
  intros.
  mytac.
  apply Intlt_false_is_Zge in H.
  rewrite Intlt_true_is_Zlt.
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  int auto.
  assert (Hi0:Int.unsigned Int.zero = 0) by int auto.
  assert (Heq: i = Int.zero <-> Int.unsigned i = 0).
  {
    split; intros.
    rewrite <- Hi0.
    rewrite ZInteq_imp_Zeq; eauto.
    eapply Int.unsigned_eq_zero; eauto.
  }
  rewrite Heq.
  mauto.
Qed.

Lemma i_lt_user_max_event:
  forall i, 
    Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ 
    i <> Int.repr (OS_USER_MAX_EVENTS / 3) -> 
    Int.ltu i (Int.repr (OS_USER_MAX_EVENTS / 3)) = true.
Proof.
  intros. mytac.
  apply Intlt_false_is_Zge in H0. 
  rewrite Intlt_true_is_Zlt. 
  assert (Int.unsigned i <> Int.unsigned (Int.repr (OS_USER_MAX_EVENTS / 3))).
  { intro Hf. apply H1. eapply ZInteq_imp_Zeq in Hf; eauto. }
  mauto.
Qed.

Lemma mqsend_absimp_mqdesok_choice:
  forall mqdes rv P sch s,
    (Int.ltu mqdes Int.zero = false /\
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) mqdes = false /\ 
       mqdes <> Int.repr (OS_USER_MAX_EVENTS / 3)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_mqdes_err (|Vint32 mqdes :: rv :: nil|) ?? s ||> ** P) 
      (<|| s ||> ** P). 
Proof.
  introv Hrgn Hcaop.
  apply absinfer_choice2; can_change_aop_solver.
  auto.
Qed.

Lemma mqsend_absimp_if_msgsizelt_yes_abt:
  forall msize msg_len rv P sch s len,
    Int.ltu msize msg_len = true -> 
    rv <> (Vint32 (Int.mone)) -> 
    len = Vint32 msg_len ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_if_msgsizelt_yes (| len :: Vint32 msize ::  rv :: nil|) ?? s ||> ** P) 
      (<|| ABORT ||> ** P). 
Proof.
  introv Hlt Hrv Hlen Hcaop. 
  eapply absinfer_trans.
  eapply absinfer_choice1. try eauto. 
  instantiate (1:= P). can_change_aop_solver. auto.
  eapply absinfer_abt;pure_auto.
  absimp_abt_solver.
Qed.

Lemma mqsend_absimp_if_msgsizelt_yes:
  forall msize msg_len rv P sch s,
    Int.ltu msize msg_len = true -> 
    rv = (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_if_msgsizelt_yes (|Vint32 msg_len :: Vint32 msize ::  rv :: nil|) ?? s ||> ** P) 
      (<|| END (Some (Vint32 (Int.mone))) ||> ** P). 
Proof. 
  infer_solver 0%nat.  
Qed.

Lemma mqsend_absimp_if_msgsizelt_no:
  forall msize msg_len  P sch s,
    Int.ltu msize msg_len = false -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_if_msgsizelt_no (|Vint32 msg_len :: Vint32 msize  :: nil|) ;; s ||> ** P) 
      (<|| s||> ** P). 
Proof. 
  infer_solver 0%nat.
Qed.

Lemma mqsend_absimp_get_msgsize:
  forall mqdes P sch s qattrb et i1' i2 i3 ms i5 i6,
    (Int.ltu mqdes Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) mqdes = false /\ 
    mqdes <> Int.repr (OS_USER_MAX_EVENTS / 3)) -> 
    get qattrb mqdes = Some (et, i1', i2, i3, ms, i5, i6) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_get_msgsize (|(Vint32 mqdes) :: (Vint32 ms) :: nil|) ;; s ||> ** HQAttr qattrb ** P) 
      (<|| s ||> ** HQAttr qattrb ** P). 
Proof.
  introv Hmqdes Hget  Hcaop.
  infer_solver 0%nat.
  destruct s0 as [[[[]]]].
  destruct H. simpljoin1. 
  destruct H3.
  simp_mem_abst.
  change_smo_hyps.
  simpl in H. simpl in H1.
  do 10 eexists.
  splits; eauto.
  split. 
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  subst x2.
  eapply join_sig_get; eauto.

  Unshelve. 
  exact None.
Qed.

Lemma mqsend_absimp_get_msgsize_abt:
  forall mqdes rv P sch s qattrb et i1' i2 i3 ms i5 i6,
    (Int.ltu mqdes Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) mqdes = false /\ 
    mqdes <> Int.repr (OS_USER_MAX_EVENTS / 3)) -> 
    get qattrb mqdes = Some (et, i1', i2, i3, ms, i5, i6) -> 
    rv <> (Vint32 ms) ->  
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_get_msgsize (|(Vint32 mqdes) :: rv :: nil|) ;; s ||> ** HQAttr qattrb ** P) 
      (<|| ABORT ||> ** HQAttr qattrb ** P). 
Proof.
  introv Hmqdes Hget Hrv Hcaop.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto.
  instantiate (1:= HQAttr qattrb ** P).
  pure_auto.
  instantiate (1:=ABORT).
  apply absinfer_abt. pure_auto. pure_auto.
  absimp_abt_solver.
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  can_change_aop_solver.
  eapply absinfer_seq_abt; auto.
  pure_auto.
  pure_auto.
  Unshelve.
  exact None.
Qed.

Lemma mqsend_absimp_msg_ptr_null_abt:
  forall  rv  P sch s  ,
    rv <> (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_msgptr_err (|Vnull :: rv :: nil|) ?? s ||>  ** P) 
      (<|| ABORT ||>  ** P). 
Proof.
  introv  Hrv Hcaop.
  eapply absinfer_trans.
  eapply absinfer_choice1; try eauto.
  eapply absinfer_abt. pure_auto. pure_auto.
  unfolds; intros.
  eexists; exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.
  unfolds.
  do 2 eexists. 
  splits; try eauto.
  apply map_join_emp.
  repeat hmstep_call_consturctor.
  simpl in *.
  simpljoin.
  do 6 eexists.
  splits ; try eauto.
  eapply change_aop_rule; eauto.
Qed.

Lemma mqsend_absimp_msg_ptr_abt:
  forall  rv msg_ptr  P sch s  ,
   ( cmpaddr Cle msg_ptr userAddrStart = true \/ cmpaddr Clt userAddrEnd msg_ptr = true) ->
    rv <> (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_msgptr_err (|Vptr msg_ptr :: rv :: nil|) ?? s ||>  ** P) 
      (<|| ABORT ||>  ** P). 
Proof.
  introv Hmptr Hrv Hcaop.
  eapply absinfer_trans.
  eapply absinfer_choice1; try eauto.
  eapply absinfer_abt. pure_auto. pure_auto.
  unfolds; intros.
  eexists; exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.
  unfolds.
  do 2 eexists. 
  splits; try eauto.
  apply map_join_emp.
  repeat hmstep_call_consturctor.
  simpl in *.
  simpljoin.
  do 6 eexists.
  splits ; try eauto.
  eapply change_aop_rule; eauto.
Qed.

Lemma mqsend_absimp_msg_ptr_err:
  forall  rv  msg_ptr P sch s  ,
  ( msg_ptr = Vnull \/    exists a,   msg_ptr = Vptr a /\ 
         (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true) ) -> 
    rv = (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_msgptr_err (|msg_ptr :: rv :: nil|) ?? s ||>  ** P) 
      (<|| END (Some (Vint32 (Int.mone))) ||>  ** P). 
Proof.
  infer_solver 0%nat.
Qed.

Lemma mqsend_absimp_msg_ptr_ok:
  forall  rv  msg_ptr P sch s  ,
      ( exists a,
             msg_ptr = Vptr a /\ 
               (cmpaddr Clt userAddrStart a  = true \/ cmpaddr Cle a userAddrEnd  = true)
        ) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_msgptr_err (|msg_ptr :: rv :: nil|) ?? s ||>  ** P) 
      (<|| s ||>  ** P). 
Proof.
  introv Hrgn Hcaop.
  apply absinfer_choice2; can_change_aop_solver.
  auto.
Qed.

Lemma mqsend_absimp_get_eid_hold_abt:
  forall mqdes v P sch s qattrb  i1' i2 i3 i4 i5 i6,
    get qattrb mqdes = Some (Holder, i1', i2, i3, i4, i5, i6) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_get_ecb_ptr (|(Vint32 mqdes) :: v :: nil|) ;; s ||> ** HQAttr qattrb ** P) 
      (<|| ABORT ||> ** HQAttr qattrb ** P). 
Proof.
  introv Hget Hcaop.
  eapply absinfer_trans.
  eapply absinfer_seq. pure_auto.
  instantiate (1:= HQAttr qattrb ** P).
  pure_auto.
  instantiate (1:= ABORT).
  eapply absinfer_abt. pure_auto. pure_auto.
  absimp_abt_solver.
  right. split; auto.
  left. split. intro. destruct H0. inv H0. intro. inv H0.
  pure_auto.
  eapply absinfer_seq_abt;eauto.
  pure_auto. pure_auto.
  Unshelve. 
  exact None.
Qed.

Lemma mqsend_absimp_get_eid_abt:
  forall mqdes v P sch s qattrb et i1' i2 i3 i4 i5 i6,
    get qattrb mqdes = Some (et, i1', i2, i3, i4, i5, i6) -> 
    ((exists eid, et = Valid_Addr eid /\ v <> Vptr eid) \/ et = Null /\ v <> Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_get_ecb_ptr (|(Vint32 mqdes) :: v :: nil|) ;; s ||> ** HQAttr qattrb ** P) 
      (<|| ABORT ||> ** HQAttr qattrb ** P). 
Proof.
  introv  Hget Heid Hcaop.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto.
  instantiate (1:= HQAttr qattrb ** P).
  pure_auto.
  instantiate (1:= ABORT).
  apply absinfer_abt.
  pure_auto.
  pure_auto.
  absimp_abt_solver.
  pure_auto.
  apply absinfer_seq_abt.
  pure_auto.
  pure_auto.
  auto.
  Unshelve. 
  exact None.
Qed.

Lemma mqsend_absimp_get_eid_ok:
  forall mqdes v P sch s qattrb et i1' i2 i3 i4 i5 i6,
    get qattrb mqdes = Some (et, i1', i2, i3, i4, i5, i6) -> 
    ((exists eid, et = Valid_Addr eid /\ v = Vptr eid) \/ et = Null /\ v = Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_get_ecb_ptr (|(Vint32 mqdes) :: v :: nil|) ;; s ||> ** HQAttr qattrb ** P) 
      (<|| s ||> ** HQAttr qattrb ** P). 
Proof.
  infer_solver 0%nat.
  Unshelve. 
  exact None.
Qed.

Lemma mqsend_absimp_if_null_yes_abt:
  forall  v rv P sch s ,
    v = Vnull ->
    rv <> Vint32 (Int.mone) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_if_null_yes (| v ::  rv :: nil|) ?? s ||> ** P) 
      (<|| ABORT ||> ** P). 
Proof.
  introv Hv Hrv Hcaop. 
  eapply absinfer_trans.
  eapply absinfer_choice1. try eauto. 
  instantiate (1:= P). can_change_aop_solver. auto.
  eapply absinfer_abt;pure_auto.
  absimp_abt_solver.
Qed.

Lemma mqsend_absimp_if_null_yes:
  forall  v rv P sch s ,
    v = Vnull ->
    rv = Vint32 (Int.mone) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_if_null_yes (|v ::  rv :: nil|) ?? s ||> ** P) 
      (<|| END (Some (Vint32 (Int.mone))) ||> ** P). 
Proof. 
  introv Hv Hrv Hcop.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto.
  instantiate (1:=P). pure_auto.
  pure_auto.
  infer_solver 0%nat.
  eexists. splits; eauto.
  subst v. auto.
Qed.

Lemma mqsend_absimp_if_null_no:
  forall rv v P sch s,
    (exists eid, v =Vptr eid) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_if_null_yes (|v ::  rv :: nil|) ?? 
             mqsend_if_null_no  (|v :: nil|) ;; s ||> ** P) 
      (<|| s||> ** P). 
Proof. 
  introv Hv Hcaop.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  eauto.
  instantiate (1:=P). pure_auto. 
  pure_auto.
  infer_solver 0%nat.  
  destruct Hv. exists x.
  splits; eauto. 
  subst v. auto.
Qed.

Lemma mqsend_absimp_get_mqflags:
  forall mqdes  P sch s qattrb et i1' i2 i3 i4 i5 i6,
    get qattrb mqdes = Some (et, i1', i2, i3, i4, i5, i6) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_get_mqflags (|(Vint32 mqdes) :: (Vint32 i2) :: nil|) ;; s ||> ** HQAttr qattrb ** P) 
      (<|| s ||> ** HQAttr qattrb ** P). 
Proof.
  introv  Hget  Hcaop.
  infer_solver 0%nat.
  Unshelve. 
  exact None.
Qed.

Lemma mqsend_absimp_get_mqflags_abt:
  forall mqdes rv P sch s qattrb et i1' i2 i3 i4 i5 i6,
    get qattrb mqdes = Some (et, i1', i2, i3, i4, i5, i6) -> 
    rv <> (Vint32 i2) ->  
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_get_mqflags (|(Vint32 mqdes) :: rv :: nil|) ;; s ||> ** HQAttr qattrb ** P) 
      (<|| ABORT ||> ** HQAttr qattrb ** P). 
Proof.
  introv Hget Hrv Hcaop.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto.
  instantiate (1:= HQAttr qattrb ** P).
  pure_auto.
  instantiate (1:=ABORT).
  apply absinfer_abt. pure_auto. pure_auto.
  absimp_abt_solver.
  can_change_aop_solver.
  eapply absinfer_seq_abt; auto.
  pure_auto.
  pure_auto.
  Unshelve.
  exact None.
Qed.

Lemma mqsend_absimp_mqflags_noteq_yes_abt:
  forall flag rv P sch s ,
   ( Int.eq flag Int.zero = false /\ Int.eq flag (Int.repr O_NONBLOCK) = false) -> 
    rv <> (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_mqflags_noteq_yes (| Vint32 flag ::  rv :: nil|) ?? s ||> ** P) 
      (<|| ABORT ||> ** P). 
Proof.
  introv Hneq Hrv Hcaop. 
  eapply absinfer_trans.
  eapply absinfer_choice1. try eauto. 
  instantiate (1:= P). can_change_aop_solver. auto.
  eapply absinfer_abt;pure_auto.
  absimp_abt_solver.
Qed.

Lemma mqsend_absimp_mqflags_noteq_yes:
  forall flag rv P sch s ,
   ( Int.eq flag Int.zero = false /\ Int.eq flag (Int.repr O_NONBLOCK) = false) ->
    rv = (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_mqflags_noteq_yes (|Vint32 flag ::  rv :: nil|) ?? s ||> ** P) 
      (<|| END (Some (Vint32 (Int.mone))) ||> ** P). 
Proof. 
  infer_solver 0%nat.  
Qed.

Lemma mqsend_absimp_mqflags_noteq_no:
  forall flag  P sch s ,
   ( flag = Int.zero  \/  flag = (Int.repr O_NONBLOCK)) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_mqflags_noteq_no (|Vint32 flag  :: nil|) ;; s ||> ** P) 
      (<|| s||> ** P). 
Proof. 
  infer_solver 0%nat.
  exists flag.
  split;auto.
  split;auto. destruct H. left. rewrite H. auto.
  right. rewrite H. auto.
Qed.

Lemma mqsend_absimp_mqflags_eqzero_beforepost:
  forall flag P sch s s1 ,
    Int.eq flag Int.zero = true ->
    can_change_aop P -> 
    absinfer sch 
      (<|| (mqsend_mqflags_eqzero_beforepost (|Vint32 flag :: nil|) ;; s) ?? s1 ||> ** P) 
      (<|| s ||> ** P). 
Proof. 
  introv Heq Hcaop.
  eapply absinfer_trans.
  eapply absinfer_choice1. 
  pure_auto. 
  instantiate (1:=P). pure_auto. auto.
  infer_solver 0%nat.
Qed.

Lemma mqsend_absimp_mqflags_noteqzero_beforepost:
  forall flag P sch s,
    Int.eq flag Int.zero = false ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_mqflags_noteqzero_beforepost (|Vint32 flag :: nil|) ;; s ||> ** P) 
      (<|| s ||> ** P). 
Proof. 
  infer_solver 0%nat.
Qed.

Lemma mqsend_absimp_ret_eqfull_yes_abt:
  forall post_rv rv P sch s ,
    Int.eq post_rv  (Int.repr OS_Q_FULL)= true ->
    rv <> (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_ret_eqfull (| Vint32 post_rv ::  rv :: nil|) ?? s ||> ** P) 
      (<|| ABORT ||> ** P). 
Proof.
  introv Heq Hrv  Hcaop. 
  eapply absinfer_trans.
  eapply absinfer_choice1. try eauto. 
  instantiate (1:= P). can_change_aop_solver. auto.
  eapply absinfer_abt;pure_auto.
  absimp_abt_solver.
Qed.

Lemma mqsend_absimp_ret_eqfull_yes:
  forall post_rv rv P sch s ,
    Int.eq post_rv  (Int.repr OS_Q_FULL)= true ->
    rv = (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_ret_eqfull (| Vint32 post_rv ::  rv :: nil|) ?? s ||> ** P) 
      (<|| END (Some (Vint32 (Int.mone))) ||> ** P). 
Proof. 
  infer_solver 0%nat.  
Qed.

Lemma mqsend_absimp_ret_eqfull_no:
  forall post_rv P sch s,
    Int.eq post_rv  (Int.repr OS_Q_FULL) = true ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_ret_eqfull (|Vint32 post_rv ::  nil|) ?? s ||> ** P) 
      (<|| s||> ** P). 
Proof.
  introv Heq Hcaop.
  eapply absinfer_choice2;pure_auto. 
Qed.

Lemma mqsend_absimp_ret_eqnoerr_yes_abt:
  forall post_rv rv P sch ,
    Int.eq post_rv  (Int.repr OS_NO_ERR)= true ->
    Int.eq post_rv  (Int.repr OS_Q_FULL)= false->
    rv <> (Vint32 (Int.zero)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_ret_eqnoerr_yes (| Vint32 post_rv ::  rv :: nil|) ||> ** P) 
      (<|| ABORT ||> ** P). 
Proof.
  introv Heq1 Heq2 Hrv Hcaop. 
    eapply absinfer_abt. pure_auto. pure_auto.
  unfolds; intros.
  eexists; exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.
  unfolds.
  do 2 eexists. 
  splits; try eauto.
  apply map_join_emp.
  repeat hmstep_call_consturctor.
  simpl in *.
  simpljoin.
  do 6 eexists.
  splits ; try eauto.
  eapply change_aop_rule; eauto.
Qed.

Lemma mqsend_absimp_ret_eqnoerr_yes_end:
  forall post_rv rv P sch ,
    Int.eq post_rv  (Int.repr OS_NO_ERR)= true ->
    Int.eq post_rv  (Int.repr OS_Q_FULL)= false->
    rv = (Vint32 (Int.zero)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_ret_eqnoerr_yes (| Vint32 post_rv ::  rv :: nil|)  ||> ** P) 
      (<|| END (Some (Vint32 (Int.zero))) ||> ** P). 
Proof.
  infer_solver 0%nat.  
Qed.

Lemma mqsend_absimp_ret_eqnoerr_no_abt:
  forall post_rv rv P sch ,
    Int.eq post_rv  (Int.repr OS_NO_ERR)= false ->
    Int.eq post_rv  (Int.repr OS_Q_FULL)= false->
    rv <> (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_ret_eqnoerr_no (| Vint32 post_rv ::  rv :: nil|) ||> ** P) 
      (<|| ABORT ||> ** P). 
Proof.
  introv Heq1 Heq2 Hrv Hcaop. 
  eapply absinfer_abt. pure_auto. pure_auto.
  unfolds; intros.
  eexists; exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.
  unfolds.
  do 2 eexists. 
  splits; try eauto.
  apply map_join_emp.
  repeat hmstep_call_consturctor.
  simpl in *.
  simpljoin.
  do 6 eexists.
  splits ; try eauto.
  eapply change_aop_rule; eauto.
Qed.

Lemma mqsend_absimp_ret_eqnoerr_no_end:
  forall post_rv rv P sch ,
    Int.eq post_rv  (Int.repr OS_NO_ERR)= false ->
    Int.eq post_rv  (Int.repr OS_Q_FULL)= false->
    rv = (Vint32 (Int.mone)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqsend_ret_eqnoerr_no (| Vint32 post_rv ::  rv :: nil|)  ||> ** P) 
      (<|| END (Some (Vint32 (Int.mone))) ||> ** P). 
Proof.
  infer_solver 0%nat.  
Qed.

Lemma mqsend_absimp_set_evloc_ptr:
  forall V_pevt s P sch ptrmp ct,
    can_change_aop P -> 
    absinfer sch 
      (<||  mqsend_set_evloc_ptr (| V_pevt :: nil |) ;; s ||> ** HEvPtr ptrmp ** HCurTCB ct ** P)
      (<|| s ||> ** HEvPtr (set ptrmp ct (Vnull, Vnull, V_pevt)) ** HCurTCB ct ** P). 
Proof.
infer_solver 0%nat.
Unshelve.
exact None.
Qed.

Lemma OSMqSendProof: 
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api mq_send
              (mqsend, (Tint32, mqd_t :: Tptr char :: size_t :: unsigned ::nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api mq_send
              (mqsend, (Tint32, mqd_t :: Tptr char :: size_t :: unsigned ::nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api mq_send = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}.
Proof.
  init_spec.

  hoare_lifts_trms_pre Aop. 
  do 12 try (destruct v'; try apply absabort_rule).
  hoare lifts (1::2::3::4::5::6::8::9::10::11::nil)%nat pre.
  
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  assert (Heqf: Int.eq ($ OS_USER_MAX_EVENTS) ($ Int.min_signed) = false).
  eapply int_min_neq_maxevents.
  lets Hrgn': usr_max_evts_rgn'.
  destruct Hrgn' as (Hrgn5 & Hrgn6).
  assert (Hsieq : (Int.signed ($ OS_USER_MAX_EVENTS) / Int.signed ($ 3)) = (OS_USER_MAX_EVENTS / 3)).
  clear -Hrgn5 Hrgn6.
  int auto.
  assert (Hdiveq: (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3) = $ (OS_USER_MAX_EVENTS / 3))).
  { unfold Int.divs in *.
     rewrite zdiv_equiv in *.
     rewrite Hsieq in *.
     auto.
     clear -Hrgn5 Hrgn6. int auto.
     clear. int auto.
  }
  
  assert (Hchg: Int.eq ($ 3) Int.zero ||
                Int.eq ($ OS_USER_MAX_EVENTS) ($ Int.min_signed) && 
                Int.eq ($ 3) Int.mone = false).
  { rewrite Heqf.
     change (Int.eq ($ 3) Int.zero || false && Int.eq ($ 3) Int.mone) with false.
     auto.
  }
  lzh_hoare_if; try rewrite Hchg in *; try solve [simpl; pure_auto].
  assert (Hposv_cond: Int.ltu i Int.zero = true \/ Int.ltu ($ OS_USER_MAX_EVENTS / 3) i = true \/ i = $ OS_USER_MAX_EVENTS / 3).
  {
    change ($ 0) with Int.zero in *.
    destruct (Int.ltu i Int.zero) eqn:eq1;
    simpl in *; auto.
    rewrite Hdiveq in LHift_true.
    destruct (Int.ltu ($ OS_USER_MAX_EVENTS / 3) i) eqn: eq2;
    simpl in *; auto.
    destruct (Int.eq i ($ OS_USER_MAX_EVENTS / 3)) eqn: eq3;
    simpl in *; try (apply semacc_int_eq_true in eq3; subst; auto).
    repeat (try change (Int.ltu Int.zero Int.zero) with false in *; simpl in * ).
    simpljoin.
    tryfalse.
  }
  simpl in LHift_true.
  destruct LHift_true as (Ha & Hb & Hc). clear Hb Hc.
  destruct (Int.ltu i ($ 0)) eqn: E1;
  destruct (Int.ltu ($ OS_USER_MAX_EVENTS / 3) i) eqn: E2;
  destruct (Int.eq i ($ OS_USER_MAX_EVENTS / 3)) eqn: E3.
  rewrite Hdiveq in Ha.
  rewrite E2 in Ha.
  simpl in Ha.
  apply ltu_eq_false in E2. tryfalse.
  rewrite Hdiveq in Ha.
  rewrite E2 in Ha.
  lets Hf: int_lt_gt_false' E1 E2. inv Hf.
  lets Hf: int_lt_eq_false' E1 E3. inv Hf.

  (* i < 0 *)
  2: { apply ltu_eq_false in E2. tryfalse. }
  (* i > OS_USER_MAX_EVENTS / 3 *)
  (* i = OS_USER_MAX_EVENTS / 3 *) 
  4: { pure_auto_try_false. } 
  
  (* i < 0 *) 
  clear E2. clear E3. clear Ha.
  {
  assert (Hdisj: v5 = Vint32 (Int.mone) \/ v5 <> Vint32 (Int.mone)) by tauto.
  destruct Hdisj as [Hv1eq | Hv1ne].
  (* v5 = Vint32 (Int.mone) *) 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_mqdeserr; eauto.
  can_change_aop_solver.  
  instantiate (1 := Afalse).
  apply absinfer_eq. 
  hoare forward.
  (* v5 <> Vint32 (Int.mone) *)  
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_mqdeserr_abt; eauto.
  can_change_aop_solver.
  instantiate (1 := Afalse).
  apply absinfer_eq. 
  apply absabort_rule.
  }
  (* i > 6 *) 
  clear E1. clear E3. clear Ha.
  {
  assert (Hdisj: v5 = Vint32 (Int.mone) \/ v5 <> Vint32 (Int.mone)) by tauto.
  destruct Hdisj as [Hv1eq | Hv1ne].
  (* v5 = Vint32 (Int.mone) *) 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_mqdeserr; eauto.
  can_change_aop_solver.  
  instantiate (1 := Afalse).
  apply absinfer_eq. 
  hoare forward.
  (* v5 <> Vint32 (Int.mone) *)  
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_mqdeserr_abt; eauto.
  can_change_aop_solver.
  instantiate (1 := Afalse).
  apply absinfer_eq. 
  apply absabort_rule.
  }
  (* i = 6 *)
  clear E1. clear E2. clear Ha.
  {
  assert (Hdisj: v5 = Vint32 (Int.mone) \/ v5 <> Vint32 (Int.mone)) by tauto.
  destruct Hdisj as [Hv1eq | Hv1ne].
  (* v5 = Vint32 (Int.mone) *) 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_mqdeserr; eauto.
  right.
  right.
  eapply semacc_int_eq_true in E3. eauto. 
  can_change_aop_solver.  
  instantiate (1 := Afalse).
  apply absinfer_eq. 
  hoare forward.
  (* v5 <> Vint32 (Int.mone) *)  
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_mqdeserr_abt; eauto.
  right.
  right.
  eapply semacc_int_eq_true in E3.
  eauto.
  can_change_aop_solver.
  instantiate (1 := Afalse).
  apply absinfer_eq. 
  apply absabort_rule.
  }

  assert (Hposv_range: Int.ltu i Int.zero = false /\ Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3)).
  { rename Hif_false into H.
     simpl val_inj in*.
    change ($ 0) with Int.zero in *.
    rewrite Hdiveq in H.
    destruct (Int.ltu i Int.zero) eqn:eq1;
    destruct (Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) i) eqn: eq2;
    destruct (Int.eq i ($ (OS_USER_MAX_EVENTS / 3))) eqn: eq3;
    try (apply semacc_int_eq_true in eq3; subst);
    simpl in *; auto;
    repeat (try change (Int.ltu Int.zero Int.zero) with false in *; 
                  try change (Int.ltu Int.zero Int.one) with true in *; simpl in * );
    try destruct H;
    tryfalse.
    splits; try apply sem_lab.semacc_int_eq_false; auto.
  }
  
  clear Hif_false Hchg.
  destruct Hposv_range as (E1 & E2 & E3).
  lets Hposv_neq: Int.eq_false E3.

  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqsend_absimp_mqdesok_choice.
  splits; eauto.
  apply semacc_int_eq_false in Hposv_neq.
  auto. can_change_aop_solver.
  apply absinfer_eq.

    (* new code about part_pos_rgn *)
   hoare_lifts_trms_pre (Aop, mqdes, temp_dom, temp_num, Aisr, Aie, Ais, Acs, Aier, p_local, A_dom_lenv).
   eapply part_pos_rgn_proof.
   introv Hsat; sep auto.
   pure_auto.
   can_change_aop_solver.
   simpl; auto.
   simpl; auto.
   simpl;auto.
   hoare normal pre.
   eapply ex_intro_rule; intro vtemp_num.
   eapply ex_intro_rule; intro vtemp_dom.
   clear v'6 v'7; rename v'8 into v'6.
   (* end of new code *)

 (*ENTER_CRITICAL;ₛ*)
  hoare forward prim. 
  hoare unfold.
  unfold EvtInv.
  hoare unfold.
  unfold AMqEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (RH_Q_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hq_nc.
  hoare_assert_pure (length v'37 = ∘ (OS_USER_MAX_EVENTS / 3)).
  { destruct v'17. get_hsat Hsat. sep_rmb_trms_in Hsat AMqAttr.  clear HeqH2. sep destroy Hsat.
    eapply amqattr_len with (s:= x); eauto. } 
  eapply pure_split_rule'; introv Hl.
  destruct v'17.
  eapply backward_rule1.
  introv Hsat.
  eapply AMqAttr_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned i)).
  sep cancel AMqAttr.
  eauto.
  rewrite Hl.
  unfold nat_of_Z.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.

  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  hoare forward.

  eapply assign_rule_lvar with ( v2:=nth_val' 3%nat v'46).
  split; intros.
  sep cancel (Alvarmapsto y). eauto.
  sep_lifts_trms (Alvarmapsto y).
  auto.
  Optimize Proof.
  Optimize Heap.
  instantiate(1:= (Tint32)).
  2: { apply eq_int. split; right; right; auto. }
  2: { sep pauto. instantiate (1:=init_lg). sep cancel p_local. sep pauto. }
  introv Hsat.
  sep_lifts_trms_in Hsat Astruct.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  eapply new_array_type_vallist_match_split' in H2; eauto.
  mytac.

  subst v'37.
  destruct H12.
  assert (Hlemu: Int.unsigned i <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
  lets H00: mqattr_corr H14 H11 E1 Hlemu.
  destruct H00 as (et & wty & fl & maxm & ms & cm &  mqc & Hget & H').
  destruct H' as ( Hcs & Hwaittype & Hflags & Hmaxmsg & Hmsgsize & Hcurmsgs). 
  assert (Hmsize: nth_val' 3%nat v'46 = Vint32 ms).
  {
    unfolds in Hmsgsize.
    eapply nth_val_nth_val'_some_eq; eauto.
  }
  rewrite Hmsize in *.

  assert (Hv: v = Vint32 ms \/ v <> Vint32 ms) by tauto. 
  destruct Hv as [Hv | Hv].
  2:{
     hoare_lifts_trms_pre (Aop,absmqattrid).
     eapply abscsq_rule.
     apply noabs_oslinv.
     eapply mqsend_absimp_get_msgsize_abt; eauto.
     can_change_aop_solver.
     eapply absinfer_eq.
     eapply absabort_rule.
  }
  inverts Hv.
  hoare_lifts_trms_pre (Aop,absmqattrid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_get_msgsize; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  (* prepare for exit critical *)
  eapply backward_rule1. 
  intros.
  eapply AMqAttr_select_sn_ex_strong.
  exists v'17. exists (Z.to_nat (Int.unsigned i)). exists v'45. exists v'46.
  sep pauto.

  (*exit critical*)
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier.
  unfold EvtInv.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  unfold AMqEIBs.
  sep pauto.
  pure_auto. pure_auto. pure_auto. pure_auto.
  pure_auto.
  sep cancel AMqAttr.
  sep cancel AMqCap.
  sep pauto.
  pure_auto. pure_auto. pure_auto. pure_auto.
  pure_auto. pure_auto. pure_auto. pure_auto.
  (*L6~ L7 : If(msg_len′ >ₑ y′ ){ RETURN -1; } *)
  lzh_hoare_if.
  pure_auto.
  assert (Hv5: v5 = Vint32 Int.mone \/ v5 <> Vint32 Int.mone) by tauto.
  destruct Hv5 as [Hv5 | Hv5].
  2:{  
     eapply abscsq_rule.
     apply noabs_oslinv.
     eapply mqsend_absimp_if_msgsizelt_yes_abt;eauto.
     pure_auto.
     eapply absinfer_eq.
     eapply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_if_msgsizelt_yes;eauto.
  pure_auto.
  eapply absinfer_eq.
  hoare forward.
  
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_choice2;eauto.
  pure_auto. pure_auto.
  eapply absinfer_eq.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_if_msgsizelt_no;eauto.
  pure_auto. 
  eapply absinfer_eq.
  
  (*L8: x ′ =ᶠ UserAddrCheck (·〈 (long) ∗ 〉 msg_ptr ′·);ₛ *)
  rename x1 into vmsg_ptr.
  assert (Hptr: vmsg_ptr = Vnull \/ (exists p, vmsg_ptr = Vptr p)).
  {
    clear - H3.
    destruct vmsg_ptr.
    unfold isptr in H3. inversion H3. tryfalse. mytac. 
    left. auto.
    right. eexists; eauto.
    unfold isptr in H3. inversion H3. tryfalse. mytac. tryfalse.
    right. eexists; eauto.
  }

  hoare forward.
  pure_auto.
  pure_auto.
  simpl.
  inversion Hptr. left; subst; auto. right. mytac; eexists; eauto.
  pure_auto.
  unfold retpost. introv Hsat.
  inverts Hsat.
  do 2 destruct H19. simpl_sat H19. simpljoin1. intro Hf. inv Hf.
  do 2 destruct H19. simpl_sat H19. simpljoin1. intro Hf. inv Hf.
  pure_auto.
  
  intros. 
  destruct H19.
  destruct H19; try (sep pauto; instantiate (1:=init_lg); sep pauto).
  intros.
  sep pauto. instantiate (1:=init_lg). sep pauto.
  
  hoare unfold.
  eapply backward_rule1.
  intros.
  apply disj_split in H18.
  eauto.
  eapply disj_rule.
  
  hoare unfold.
  inverts H20.
  
  lzh_hoare_if.
  pure_auto.
  (* x = 0 true*)
  assert (Hv5: v5 = Vint32 (Int.mone) \/ v5 <> Vint32 (Int.mone)) by tauto.
  destruct Hv5 as [Hv5 | Hv5].
  2: {
      hoare abscsq.
      apply noabs_oslinv.
      inversion Hptr.  
      subst.
      eapply mqsend_absimp_msg_ptr_null_abt; eauto.
      can_change_aop_solver.
      destruct H19. subst. 
      eapply mqsend_absimp_msg_ptr_abt; eauto.
      inversion H18; tryfalse.
      mytac. inverts H19. auto.
      can_change_aop_solver.
      apply absabort_rule.
  }
  hoare abscsq.
  apply noabs_oslinv.
  eapply mqsend_absimp_msg_ptr_err;eauto.
  inversion H18.
  left. inverts H19;subst;eauto.
  right. mytac. eexists; splits;eauto.
  inverts H19; eauto.
  pure_auto.

  hoare forward.
  (* x = 0 false*)
  tryfalse.
  
  hoare unfold.
  inverts H20.

  lzh_hoare_if.
  pure_auto.
  (* x = 1 true*)
  change (Int.eq ($ 1) ($ 0) ) with false in LHift_true. tryfalse.
  (* x = 1 false*)
  hoare abscsq.
  apply noabs_oslinv.
  eapply mqsend_absimp_msg_ptr_ok; eauto.
  pure_auto.
  
  (*L11: ENTER_CRITICAL;ₛ*)
  clear - E1 E2 E3 Hdiveq Hrgn3 Hrgn4.
  hoare forward prim. 
  hoare unfold.
  unfold EvtInv.
  hoare unfold.
  unfold AMqEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (RH_Q_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hq_nc.
  hoare_assert_pure (length v'34 = ∘ (OS_USER_MAX_EVENTS / 3)).
  { destruct v'14. get_hsat Hsat. sep_rmb_trms_in Hsat AMqAttr.  clear HeqH2. sep destroy Hsat.
    eapply amqattr_len with (s:= x0); eauto. } 
  eapply pure_split_rule'; introv Hl.
  destruct v'14.
  eapply backward_rule1.
  introv Hsat.
  eapply AMqAttr_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned i)).
  sep cancel AMqAttr.
  eauto.
  rewrite Hl.
  unfold nat_of_Z.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.
  
  (*L12:   p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ*)
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  hoare forward.

  eapply assign_rule_lvar with (v2:=nth_val' 5%nat v'43).
  split;intros.
  sep cancel (Alvarmapsto p).
  eauto.
  sep cancel (Alvarmapsto p).
  auto.
  Optimize Proof.
  Optimize Heap.
  
  instantiate (1:=(OS_EVENT∗)).
  2: { apply eq_vptr. do 2 eexists. splits; auto. }
  2: { sep pauto. sep cancel p_local. sep pauto. }
  introv Hsat.
  sep_lifts_trms_in Hsat Astruct.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq.
  lets Hposv_neq: Int.eq_false E3. auto.
  eapply new_array_type_vallist_match_split' in H2; eauto.
  mytac.
  
  subst v'34.
  destruct H11.
  assert (Hlemu: Int.unsigned i <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
  lets H00: mqattr_corr H13 H10 E1 Hlemu.
  destruct H00 as (et & wty & fl & maxm & msize & curm & mqc & Hget & H').
  assert (Hcases: ((exists eid, et = Valid_Addr eid /\ V_QATTRpevent v'43 = Some (Vptr eid) /\ eid <> vhold_addr) \/ et = Null /\ V_QATTRpevent v'43 = Some Vnull ) \/ et = Holder /\ V_QATTRpevent v'43 = Some (Vptr vhold_addr)). 
  { clear -H'. intuition. }
  assert (H01 := H').
  clear H'. 
  destruct Hcases as [ Hok | Habt ].
  2: {
    destruct Habt as (Habt1 & Habt2).
    rewrite Habt1 in Hget.
    hoare_lifts_trms_pre (Aop, absmqattrid).
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mqsend_absimp_get_eid_hold_abt.
    eauto.
    pure_auto.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  assert (Hcases: 
         ((exists eid, et = Valid_Addr eid /\ v0 = Vptr eid) \/ et = Null /\ v0 = Vnull)
      \/ ((exists eid, et = Valid_Addr eid /\ v0 <> Vptr eid) \/ et = Null /\ v0 <> Vnull)).
  {
    inv Hok. destruct H17 as (eid & H'). 
    assert (Hvcs: v0 = Vptr eid \/ v0 <> Vptr eid) by tauto.
    inv Hvcs.
    left. left. exists eid. destructs H'. split; auto.
    right. left. exists eid. destructs H'. split; auto.
    assert (Hvcs: v0 = Vnull \/ v0 <> Vnull) by tauto.
    inv Hvcs.
    left. right. destructs H17. split; auto.
    right. right. destructs H17. split; auto.
  }

  inversion Hcases.
  2:{
     hoare_lifts_trms_pre (Aop, absmqattrid).
     eapply abscsq_rule.
     apply noabs_oslinv.
     eapply mqsend_absimp_get_eid_abt; auto.
     eauto.
     auto.
     pure_auto.
     eapply absinfer_eq. 
     apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, absmqattrid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_get_eid_ok; auto.
  eauto.
  auto.
  pure_auto.
  eapply absinfer_eq. 
  clear Hcases.
  
  (*L13: EXIT_CRITICAL;ₛ  *)
  eapply backward_rule1. 
  intros.
  eapply AMqAttr_select_sn_ex_strong. 
  exists v'14. exists (Z.to_nat (Int.unsigned i)).
  exists v'42. exists v'43.
  sep pauto.

  (*exit critical*)
  hoare forward prim.
  unfold EvtInv.
  unfold AMqEIBs.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqAttr.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel AMqCap.
  sep pauto.
  pure_auto. pure_auto. pure_auto.
  auto. pure_auto. pure_auto. pure_auto. pure_auto.

  assert (H_prm_cases: (exists eid, v0 = Vptr eid /\ nth_val' 5%nat v'43 = Vptr eid) \/ (v0 = Vnull /\ nth_val' 5%nat v'43 = Vnull)).
  {
    inversion Hok as [Heo1 | Heo2]; inversion H17 as [Heo1' | Heo2'].
    destruct Heo1 as (eid & Heoeq1 & Hv_ & Hneq).
    destruct Heo1' as (eid' & Heoeq1' & Hv'_).
    rewrite Heoeq1' in Heoeq1. inverts Heoeq1.
    unfold V_QATTRpevent in Hv_.
    apply nth_val_nth_val'_some_eq in Hv_.
    left. eexists. split; eauto.
    destruct Heo1 as (eid & Heoeq1 & Hv_ & Hneq);
    destruct Heo2' as (Heoeq2' & Hv_');
    tryfalse.
    destruct Heo2 as (Heoeq2 & Hv_);
    destruct Heo1' as (eid & Heoeq1' & Hv_');
    tryfalse.
    unfold V_QATTRpevent in Heo2.
    destruct Heo2. destruct Heo2'.
    right.
    split; auto. 
    apply nth_val_nth_val'_some_eq; auto.
  }
  
  assert (Heq: nth_val' 5%nat v'43 = v0).
  {
    inversion H_prm_cases.
    destruct H18. destruct H18. congruence.
    destruct H18. congruence.
  }
  rewrite Heq. clear Heq. 
  assert (Hvptr: isptr v0).
  {
    inversion H_prm_cases.
    destruct H18. destructs H18.
    rewrite H18. 
    apply ptr_isptr.
    destructs H18.
    rewrite H18.
    apply Vnull_is_ptr.
  }
  clear - E1 E2 E3 H_prm_cases Hvptr Hdiveq Hrgn3 Hrgn4.

  (* L14 : If p = NULL { RETURN -1; } *)
  hoare forward. 
  pure_auto.
  pure_auto.
  hoare unfold.
  assert (Hv0null: v0 = Vnull) by pure_auto.
  subst v0.
  assert (Hv5: v5 = Vint32 (Int.mone) \/ v5 <> Vint32 (Int.mone)) by tauto.
  destruct Hv5 as [Hv5 | Hv5].
  2:{ (* ... <> -1 *)
     eapply abscsq_rule.
     apply noabs_oslinv.
     eapply mqsend_absimp_if_null_yes_abt; auto.
     can_change_aop_solver.
     instantiate (1:=Afalse).
     eapply absinfer_eq.
     apply absabort_rule.
  }
  (* ... = -1 *) 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_if_null_yes; auto.
  can_change_aop_solver.
  eapply absinfer_eq.

  (* the RETURN in case p = NULL *)
  hoare forward.

 (* p <> NULL *)
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  assert (exists eid, v0 = Vptr eid).
  {
    destruct v0. 
    inversion H; tryfalse.
    inversion H; tryfalse.
    inversion H; tryfalse.
    eexists; eauto.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_if_null_no; auto.
  can_change_aop_solver.
  eapply absinfer_eq.

  clear H.
  destruct H0. 
  clear H.
  clear H_prm_cases.

  (* L16 : encrit *) 
  hoare forward prim.
  hoare unfold.
  unfold EvtInv.
  hoare unfold.
  unfold AMqEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (RH_Q_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hq_nc.
  hoare_assert_pure (length v'33 = ∘ (OS_USER_MAX_EVENTS / 3)).
  { destruct v'13. get_hsat Hsat. sep_rmb_trms_in Hsat AMqAttr. clear HeqH2. sep destroy Hsat.
    eapply amqattr_len with (s:= x1); eauto. } 
  eapply pure_split_rule'; introv Hl.
  
  destruct v'13.
  eapply backward_rule1.
  introv Hsat.
  eapply AMqAttr_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned i)).
  sep cancel AMqAttr.
  eauto.
  rewrite Hl.
  unfold nat_of_Z.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.

  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  (*z ′ =ₑ efield (Mq_Attr ′ [mqdes ′]) mq_flags;ₛ*)
  hoare forward.
  eapply assign_rule_lvar with (v2:=nth_val' 1%nat v'42).
  split; intros.
  sep cancel (Alvarmapsto z). eauto.
  sep cancel (Alvarmapsto z). 
  auto.
  Optimize Proof.
  Optimize Heap.
  
  instantiate(1:= (Tint32)).
  2: { apply eq_int. split; right; right; auto. }
  2: { sep pauto. sep pauto. sep cancel p_local. sep pauto. }
  introv Hsat.
  sep_lifts_trms_in Hsat Astruct.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq.
  lets Hposv_neq: Int.eq_false E3. auto.
  eapply new_array_type_vallist_match_split' in H2; eauto.
  mytac.
  
  subst v'33.
  destruct H11.
  assert (Hlemu: Int.unsigned i <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
  lets H00: mqattr_corr H13 H10 E1 Hlemu.  
  destruct H00 as (et & wty & fl & maxm & msize & curm & mqc & Hget & H').
  destruct H' as ( Hcs & Hwaittype & Hflags & Hmaxmsg & Hmsgsize & Hcurmsgs). 
  assert (Hmqflag: nth_val' 1%nat v'42 = Vint32 fl).
  {
    unfolds in Hflags.
    eapply nth_val_nth_val'_some_eq; eauto.
  }
   rewrite Hmqflag in *.

  assert (Hv2: v2 = Vint32 fl \/ v2 <> Vint32 fl) by tauto. 
  destruct Hv2 as [Hv2 | Hv2].
  2:{ 
     hoare_lifts_trms_pre (Aop, absmqattrid).
     eapply abscsq_rule.
     apply noabs_oslinv.
     eapply mqsend_absimp_get_mqflags_abt; eauto.
     can_change_aop_solver.
     eapply absinfer_eq.
     eapply absabort_rule.
  }
  inverts Hv2.
  hoare_lifts_trms_pre (Aop, absmqattrid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_get_mqflags; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  
  (* prepare for exit critical *)
  eapply backward_rule1. 
  intros.
  eapply AMqAttr_select_sn_ex_strong. 
  exists v'13. exists (Z.to_nat (Int.unsigned i)).  exists v'41. exists v'42.
  sep pauto.

  (*L18: exit critical*)
  hoare forward prim.
  sep pauto.
  unfold EvtInv.
  unfold AMqEIBs.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqAttr.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel AMqCap.
  sep cancel CapabilityInv.
  sep pauto.
  pure_auto. pure_auto. pure_auto.
  auto.
  pure_auto. pure_auto. pure_auto. pure_auto.
  
  (*L19 :  If( z′ !=ₑ ′0 &&ₑ  z′ !=ₑ O_NONBLOCK′) *)
  hoare forward.
  destruct (Int.eq fl ($ 0));auto.
  destruct (Int.eq fl ($ 0));auto.
  destruct (Int.eq fl ($ O_NONBLOCK));auto.
  destruct (Int.eq fl ($ O_NONBLOCK));auto.
  pure_auto.
  hoare unfold.
  
  assert (Hv5: v5 = Vint32 Int.mone \/ v5 <> Vint32 Int.mone) by tauto.
  destruct Hv5 as [Hv5 | Hv5].
  2:{  
     eapply abscsq_rule.
     apply noabs_oslinv.
     eapply mqsend_absimp_mqflags_noteq_yes_abt;eauto.
     clear - H3 H18 H10. pure_auto. pure_auto. 
     eapply absinfer_eq.
     eapply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_mqflags_noteq_yes;eauto.
  clear - H3 H18 H10. pure_auto. pure_auto.
  eapply absinfer_eq.
  (* return -1 *)
  hoare forward. 
  
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_choice2;eauto.
  pure_auto. pure_auto.
  eapply absinfer_eq.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_mqflags_noteq_no;eauto. 
  clear - H18.
  change ($ 0) with Int.zero in H18.
  destruct H18;
  pure_auto; simpl in H; inverts H;
  apply eq_sym in HeqH0; apply eq_sym in HeqH1; 
  try apply semacc_int_eq_true in HeqH0;
  try apply semacc_int_eq_true in HeqH1; auto.
  pure_auto.
  eapply absinfer_eq.
  
  clear - E1 E2 E3 v'31 Hvptr x0 Hdiveq Hrgn3 Hrgn4.

  (* ENTER_CRITICAL;ₛ*) 
  hoare forward prim.
  hoare unfold.
  unfold EvtInv.
  hoare unfold.
  unfold AMqEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (RH_Q_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hq_nc. 
  hoare_assert_pure (length v'33 = ∘ (OS_USER_MAX_EVENTS / 3)).
  { destruct v'12. get_hsat Hsat. sep_rmb_trms_in Hsat AMqAttr. clear HeqH2. sep destroy Hsat.
    eapply amqattr_len with (s:= x1); eauto. }
  eapply pure_split_rule'; introv Hl.

  destruct v'12.
  eapply backward_rule1.
  introv Hsat.
  eapply AMqAttr_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned i)).
  sep cancel AMqAttr.
  eauto.
  rewrite Hl.
  unfold nat_of_Z.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.

  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  hoare forward.
  eapply assign_rule_lvar with ( v2:=nth_val' 1%nat v'42).
  split; intros.
  sep cancel (Alvarmapsto z). eauto.
  sep cancel (Alvarmapsto z). auto.
  instantiate(1:= (Tint32)).
  2: { apply eq_int. split; right; right; auto. }
  2: { sep pauto. instantiate (1:=init_lg). sep cancel p_local. sep pauto. }
  introv Hsat.
  sep_lifts_trms_in Hsat Astruct.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq.
  lets Hposv_neq: Int.eq_false E3. auto.
  eapply new_array_type_vallist_match_split' in H2; eauto.
  mytac.
  
  subst v'33.
  destruct H11.
  assert (Hlemu: Int.unsigned i <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
  lets H00: mqattr_corr H13 H10 E1 Hlemu.
  destruct H00 as (et & wty & fl' & maxm & msize & curm & mqc & Hget & H').
  destruct H' as ( Hcs & Hwaittype & Hflags & Hmaxmsg & Hmsgsize & Hcurmsgs). 
  assert (Hmqflag: nth_val' 1%nat v'42 = Vint32 fl').
  {
    unfolds in Hflags.
    eapply nth_val_nth_val'_some_eq; eauto.
  }
   rewrite Hmqflag in *.

  (*执行一步抽象操作*)
  assert (Hv3: v3 = Vint32 fl' \/ v3 <> Vint32 fl') by tauto. 
  destruct Hv3 as [Hv3 | Hv3].
  2:{ 
     hoare_lifts_trms_pre (Aop, absmqattrid).
     eapply abscsq_rule.
     apply noabs_oslinv.
     eapply mqsend_absimp_get_mqflags_abt; eauto.
     can_change_aop_solver.
     eapply absinfer_eq.
     eapply absabort_rule.
  }
  inverts Hv3.
  hoare_lifts_trms_pre (Aop, absmqattrid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_get_mqflags; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  
  (*合并ACNU prepare for exit critical *)
  eapply backward_rule1. 
  intros.
  eapply AMqAttr_select_sn_ex_strong. 
  exists v'12. exists (Z.to_nat (Int.unsigned i)). exists v'41. exists v'42.
  sep pauto.
  
  (*L23: exit critical*)
  hoare forward prim.
  sep pauto.
  unfold EvtInv.
  unfold AMqEIBs.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqAttr.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel AMqCap.
  sep cancel CapabilityInv.
  sep pauto.
  pure_auto. pure_auto. pure_auto.
  auto.
  Optimize Proof.
  Optimize Heap.
  pure_auto. pure_auto. pure_auto. pure_auto.
  
  (*L24: IF( z′ ==ₑ ′0 )*)
  lzh_hoare_if. 
  pure_auto. 
  (* *************************fl' = 0 ************************* *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_mqflags_eqzero_beforepost; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  
  (*L25: ENTER_CRITICAL;ₛ*)
  hoare forward prim.
  hoare unfold.
  unfold EvtInv.
  hoare unfold.
  unfold AMqEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_assert_pure (length v'74 = ∘ (OS_USER_MAX_EVENTS / 3)).
  {   destruct v'54. get_hsat Hsat. sep_rmb_trms_in Hsat AMqAttr. clear HeqH20. sep destroy Hsat.
    eapply amqattr_len with (s:= x1); eauto. }
  eapply pure_split_rule'; introv Hl'.

  destruct v'54.
  eapply backward_rule1.
  introv Hsat.
  eapply AMqAttr_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned i)).
  sep cancel AMqAttr.
  eauto.
  rewrite Hl'.
  unfold nat_of_Z.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.
  
  (*L26: p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ*)
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aop).
  hoare forward.
  eapply assign_rule_lvar with (v2:=nth_val' 5%nat v'83).
  split; intros.
  sep cancel (Alvarmapsto p). eauto.
  sep cancel (Alvarmapsto p). auto.
  
  instantiate (1:=(OS_EVENT∗)).
  2: { apply eq_vptr. do 2 eexists. splits; auto. }
  2: { sep pauto. sep cancel p_local. sep pauto. }
  introv Hsat.
  sep_lifts_trms_in Hsat Astruct.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq.
  lets Hposv_neq: Int.eq_false E3. auto.
  eapply new_array_type_vallist_match_split' in H20; eauto.
  mytac.
  
  subst v'74.
  destruct H29.
  lets H00: mqattr_corr H31 H28 E1 Hlemu.  
  destruct H00 as (et0 & wty0 & fl0 & maxm0 & msize0 & curm0 & mqc0 & Hget0 & H').
  assert (Hcases: ((exists eid, et0 = Valid_Addr eid /\ V_QATTRpevent v'83 = Some (Vptr eid) /\ eid <> vhold_addr) \/ et0 = Null /\ V_QATTRpevent v'83 = Some Vnull) \/ et0 = Holder /\ V_QATTRpevent v'83 = Some (Vptr vhold_addr)). 
  { clear -H'. intuition. }
  assert (H01 := H').
  clear H'. 
  destruct Hcases as [ Hok | Habt ].
  2: {
      destruct Habt as (Habt1 & Habt2).
      rewrite Habt1 in Hget0.
      hoare_lifts_trms_pre (Aop, absmqattrid).
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mqsend_absimp_get_eid_hold_abt.
      eauto.
      pure_auto.
      eapply absinfer_eq.
      apply absabort_rule.
  }
  assert (Hcases: 
         ((exists eid, et0 = Valid_Addr eid /\ v1 = Vptr eid) \/ et0 = Null /\ v1 = Vnull)
      \/ ((exists eid, et0 = Valid_Addr eid /\ v1 <> Vptr eid) \/ et0 = Null /\ v1 <> Vnull)).
  {
    inv Hok. destruct H36 as (eid & H'). 
    assert (Hvcs: v1 = Vptr eid \/ v1 <> Vptr eid) by tauto.
    inv Hvcs.
    left. left. exists eid. destructs H'. split; auto.
    right. left. exists eid. destructs H'. split; auto.
    assert (Hvcs: v1 = Vnull \/ v1 <> Vnull) by tauto.
    inv Hvcs.
    left. right. destructs H36. split; auto.
    right. right. destructs H36. split; auto.
  }

  inversion Hcases.
  2: {
      hoare_lifts_trms_pre (Aop , absmqattrid).
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mqsend_absimp_get_eid_abt; auto.
      eauto.
      auto.
      pure_auto.
      eapply absinfer_eq. 
      apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, absmqattrid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_get_eid_ok; auto.
  eauto.
  auto.
  pure_auto.
  eapply absinfer_eq. 
  clear Hcases.

  assert (H_prm_cases: (exists eid, v1 = Vptr eid /\ nth_val' 5%nat v'83 = Vptr eid) \/ (v1 = Vnull /\ nth_val' 5%nat v'83 = Vnull)).
  {
    inversion Hok as [Heo1 | Heo2]; inversion H36 as [Heo1' | Heo2'].
    destruct Heo1 as (eid & Heoeq1 & Hv_ & Hneq).
    destruct Heo1' as (eid' & Heoeq1' & Hv'_).
    rewrite Heoeq1' in Heoeq1. inverts Heoeq1.
    unfold V_QATTRpevent in Hv_.
    apply nth_val_nth_val'_some_eq in Hv_.
    left. eexists. split; eauto.
    destruct Heo1 as (eid & Heoeq1 & Hv_ & Hneq);
    destruct Heo2' as (Heoeq2' & Hv_');
    tryfalse.
    destruct Heo2 as (Heoeq2 & Hv_);
    destruct Heo1' as (eid & Heoeq1' & Hv_');
    tryfalse.
    unfold V_QATTRpevent in Heo2.
    destruct Heo2. destruct Heo2'.
    right.
    split; auto. 
    apply nth_val_nth_val'_some_eq; auto.
  }
  
  assert (Heq: nth_val' 5%nat v'83 = v1).
  {
    inversion H_prm_cases.
    destruct H37. destruct H37. congruence.
    destruct H37. congruence.
  }
  rewrite Heq. clear Heq. 
  assert (Hv1: (exists x0, v1 = Vptr x0) \/ v1 = Vnull). 
  {
    inversion H36. left. mytac. right. mytac.
  }
  
  (*L27：prepare for exit critical *)
  eapply backward_rule1. 
  intros.
  eapply AMqAttr_select_sn_ex_strong. 
  exists v'54. exists (Z.to_nat (Int.unsigned i)). exists v'82. exists v'83.
  sep pauto.

  (* OSTCBCur ′ → __OSTskQPtr =ₑ p ′;ₛ *)
  hoare_lifts_trms_pre (tcbllsegevaux, AOSTCBList, p_local). 
  eapply backward_rule1.
  introv Hsat.
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre. 
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  hoare_assign_evaux.
  clear -Hv1. destruct Hv1 as [(x0 & Hvl) | Hvl]; rewrite Hvl; auto. 
  clear -Hv1. unfold isevptr. unfold isptr. pure_auto.

  rename v'81 into ptrmp.
  assert (Hevptr: get ptrmp tid = Some (Vnull, Vnull, Vnull)).  
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  rename v'80 into locmp.
  assert (Hloc: get locmp tid = Some (V$ __EvLoc_normal)).
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }

  assert(new_array_type_vallist_match_q_getp:exists v, V_QATTRpevent v'83 = Some v /\ isptr v).
  clear - H20.
  eapply new_array_type_vallist_match_split' in H20; eauto.
  destruct H20 as (_ & _ & Hsp).
  lets Hvl: struct_type_vallist_match_elim_7 Hsp.
  destruct Hvl. do 6 destruct H.
  subst v'83.
  simpl in Hsp. 
  destruct Hsp as (_ & _ & _ & _ & _ &  Hk & _).
  exists x3.
  unfold V_OSMUXINFOPevent. unfold isptr.
  simpl. split; auto.
  destruct x3; tryfalse; pure_auto.

  assert (Hvpevt_eq: nth_val' 5 v'83 = v1).
  { clear -Hok H_prm_cases.
    unfold V_QATTRpevent in *.
    destruct Hok as [( eid & Heo & Hvp & _) | (Heo & Hvp)]; subst et0;
    eapply nth_val_nth_val'_some_eq in Hvp; rewrite Hvp;
    destruct H_prm_cases as [( eid0 & Heo & Hvp1) | (Heo & Hvp1)]; inverts Heo;
    auto;
    rewrite Hvp in Hvp1; tryfalse; auto. 
  }
  assert (Hisptr: isptr (v1)). 
  {
    clear- new_array_type_vallist_match_q_getp Hvpevt_eq.
    simpljoin1. 
    unfold V_QATTRpevent in H.
    do 6 (destruct v'83; simpl in H; tryfalse).  
    inverts H. simpl. auto. 
  }

  rename v'51 into els.
  rename v'75 into semeibs.
  rename v'76 into muxeibs.
  rename v'77 into mqeibs.

  hoare_lifts_trms_pre (Aop, evptrid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_set_evloc_ptr; eauto.
  can_change_aop_solver.
  unfold CurTid. go.
  eapply absinfer_eq.

  remember (v1) as V_pevt.

  (*exit critical*)
  fold_evaux_q (V_pevt).
  clear -Hv1. destruct Hv1 as [(x0 & Hvl) | Hvl]; rewrite Hvl; auto.
  hoare forward prim.
  sep pauto.
  unfold EvtInv.
  unfold AMqEIBs.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqAttr.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel AMqCap.
  eauto.
  eapply evdel_nodup_normal_qptr_preserve; eauto.
  eapply evcre_nodup_normal_qptr_preserve; eauto.
  {
   destruct H_prm_cases as [(eid & Heo & Hvp) | (Heo & Hvp)];
   rewrite Hvp.
   eapply mq_ecb_p_qptr_normal_preserve; eauto.
   unfold is_que.
   destruct H36.
   simpljoin1.
   eapply H34; eauto.
   rewrite H45 in Hvp.
   instantiate (1:= mqc0).
   instantiate (1:= curm0).
   instantiate (1:= msize0).
   instantiate (1:= maxm0).
   instantiate (1:= fl0).
   instantiate (1:= wty0).
   instantiate (1:= i).
   inverts Hvp. auto.
   destruct H36.
   simpljoin1. rewrite H45 in Hvp. tryfalse.
   eapply mq_ecb_p_set_null3_preserve; eauto.
  }
  {
   destruct H_prm_cases as [(eid & Heo & Hvp) | (Heo & Hvp)];
   rewrite Hvp.
   eapply mux_ecb_p_qptr_normal_preserve; eauto.
   unfold is_que.
   destruct H36.
   simpljoin1.
   eapply H34; eauto.
   rewrite H45 in Hvp.
   instantiate (1:= mqc0).
   instantiate (1:= curm0).
   instantiate (1:= msize0).
   instantiate (1:= maxm0).
   instantiate (1:= fl0).
   instantiate (1:= wty0).
   instantiate (1:= i).
   inverts Hvp. auto.
   destruct H36.
   simpljoin1. rewrite H45 in Hvp. tryfalse.
   eapply mux_ecb_p_set_null3_preserve; eauto.
  }
  {
   destruct H_prm_cases as [(eid & Heo & Hvp) | (Heo & Hvp)];
   rewrite Hvp.
   eapply sem_ecb_p_qptr_normal_preserve; eauto.
   unfold is_que.
   destruct H36.
   simpljoin1.
   eapply H34; eauto.
   rewrite H45 in Hvp.
   instantiate (1:= mqc0).
   instantiate (1:= curm0).
   instantiate (1:= msize0).
   instantiate (1:= maxm0).
   instantiate (1:= fl0).
   instantiate (1:= wty0).
   instantiate (1:= i).
   inverts Hvp. auto.
   destruct H36.
   simpljoin1. rewrite H45 in Hvp. tryfalse.
   eapply sem_ecb_p_set_null3_preserve; eauto.
  }
  auto.
  Optimize Proof.
  Optimize Heap.
  pure_auto. pure_auto.  pure_auto. pure_auto.
  pure_auto. pure_auto.


  (* ************** call qtimedpostnew ****************)
  (* rr′ =ᶠ OSQTimedPost(·p′ , 〈Int16u〉(′0) , 〈Void ∗〉msg_ptr′·);ₛ*)
hoare_unfold.
  hoare forward.
  inversion Hv1. destruct H57. 
  do 6 (destruct v'83; tryfalse).
  simpl in H57. subst v7. auto.
  do 6 (destruct v'83; tryfalse).
  simpl in H57. subst v7. auto.


  2:{
     instantiate (2:= nth_val' 5 v'83). 
     instantiate (3:= v4).  
     instantiate (3:=( Vint32 Int.zero :: Vptr x ::nil  ) ).
     change ((nth_val' 5 v'83 :: Vint32 Int.zero :: Vptr x :: nil) ++ v4 :: nil) with  (nth_val' 5 v'83 :: Vint32 Int.zero :: Vptr x :: v4 :: nil).
     simpl spec_code_cons.
     eauto.
  }
  
  {
    
   destruct_s s.
   simpl.
   splits; auto.
   sep_lifts_trms_in H56 (Alvarmapsto msg_ptr, A_dom_lenv).
   sep remember (1::2::nil)%nat in H56.
   (* clear -H52. *)
   simpl in H56.
   simpljoin1.
   unfold eq_dom_env in H66.
   rewrite H73.
   splits;auto.
   change (Int.unsigned Int.zero) with 0 in H74.
   unfold is_int_type.
   eapply load_local; eauto.
   eapply mapstoval_load;eauto.
  }
  pure_auto.
  pure_auto.
  pure_auto.
  unfold retpost. introv Hsat. inverts Hsat.
  do 4 destruct H56.
  sep split in H56.
  destruct H58.
  pure_auto.
  
  {
   inversion Hv1. destruct H56.
   do 6 (destruct v'83; tryfalse).
   simpl in H56. inverts H56. auto.
   do 6 (destruct v'83; tryfalse).
   simpl in H56. inverts H56. auto.
  }
  { sep pauto. sep cancel p_local. sep pauto. }
  { sep pauto. sep cancel p_local. sep pauto. }

  hoare unfold.

  inverts H56.
  do 6 (destruct v'83; simpl in H43; tryfalse).
  unfold V_QATTRpevent in H43. simpl in H43.
  simpl in Hisptr.

  (* ENTER_CRITICAL;ₛ *)
  hoare forward prim.
  unfold EvtInv.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.

  hoare_lifts_trms_pre (tcbllsegevaux, AOSTCBList, p_local). 
  eapply backward_rule1.
  introv Hsat.
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre. 
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  hoare_assign_evaux.

  rename v'123 into ptrmp'.
  assert (Hevptr': get ptrmp' tid = Some  (Vnull, Vnull, v'133)).  
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }

  rename v'117 into semeibs'.
  rename v'118 into muxeibs'.
  rename v'119 into mqeibs'.
  rename v'122 into locmp'.
  rename v'93 into els'.

  (* OSTCBCur ′ → __OSTskQPtr =ₑ NULL;ₛ *) 
  hoare_lifts_trms_pre (Aop, evptrid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_set_evloc_ptr; eauto.
  can_change_aop_solver.
  unfold CurTid. go.
  eapply absinfer_eq.

  (* EXIT_CRITICAL;ₛ *)
  assert(Heq_loc: (set locmp' tid (V$ __EvLoc_normal)) = locmp').
  { eapply get_set_same.  eapply join_get_r; eauto.
     eapply join_sig_get; eauto.
  }
  fold_evaux_q Vnull.
  hoare forward prim.
  sep cancel tcbdllflag.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep pauto. 
  2: { splits; eauto. }
  unfold EvtInv.
  sep pauto.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  unfold tcbllsegevaux.
  sep cancel llsegevaux.
  eauto.
  eapply evdel_nodup_set_null3_preserve; eauto.
  eapply evcre_nodup_set_null3_preserve; eauto. 
  eapply mq_ecb_p_set_null3_preserve; eauto.
  eapply mux_ecb_p_set_null3_preserve; eauto.
  eapply sem_ecb_p_set_null3_preserve; eauto.
  pure_auto. pure_auto.


  instantiate (1:= fun ptrmp => ( EX v v2,
         <|| mqsend_ret (Vint32 v) v5 ||>  **
         Aisr empisr **
         (EX v'80, Aier v'80) **  
         Aie true **
         Ais nil **
         Acs nil **
         p_local OSLInv tid
           (logic_val (V$ 1)
            :: logic_val (V$ os_code_defs.__EvLoc_normal)
               :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
         [| 0 <= Int.unsigned v /\ Int.unsigned v <= Byte.max_unsigned |] **
         LV rr @ char_t |-> Vint32 v **
         LV p @ OS_EVENT ∗ |-> v2 **
         LV z @ long |-> Vint32 fl' **
         LV os_code_defs.x @ char_t |-> (V$ 1) **
         LV y @ long |-> Vint32 ms **
         LV ret @ long |-> v'0 **
         LV msgprio @ long |-> Vint32 i1 **
         LV msg_len @ long |-> Vint32 i0 **
         LV msg_ptr @ (char_t) ∗ |-> Vptr x **
         LV temp_num @ char_t |-> vtemp_dom **
         LV temp_dom @ char_t |-> vtemp_num **
         LV mqdes @ long |-> Vint32 i **
         A_dom_lenv
           ((msgprio, long)
            :: (msg_len, long)
               :: (msg_ptr, (char_t) ∗)
                  :: (mqdes, long)
                     :: (ret, long)
                        :: (os_code_defs.x, char_t)
                           :: (y, long)
                              :: (z, long)
                                 :: (p, OS_EVENT ∗) :: (rr, char_t) :: (temp_dom, char_t) :: (temp_num, char_t) :: nil))).   
  
  sep pauto.
  exists v'80.
  sep cancel Aier.
  sep pauto.
  eauto.

  (*****   ELSE part ************)
  (* *************************fl' <> 0 ************************* *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_choice2. pure_auto.
  2:{ eauto. }
  pure_auto. eauto.
  eapply absinfer_eq.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_mqflags_noteqzero_beforepost; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  
  (*L25: ENTER_CRITICAL;ₛ*)
  hoare forward prim.
  hoare unfold.
  unfold EvtInv.
  hoare unfold.
  unfold AMqEIBs.
  hoare normal pre.
  hoare_ex_intro.
  hoare_assert_pure (length v'74 = ∘ (OS_USER_MAX_EVENTS / 3)).
  {  get_hsat Hsat. sep_rmb_trms_in Hsat AMqAttr. clear HeqH20. sep destroy Hsat.
    destruct v'54. eapply amqattr_len with (s:= x1); eauto. }
  eapply pure_split_rule'; introv Hl'.
  destruct v'54.
  eapply backward_rule1.
  introv Hsat.
  eapply AMqAttr_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned i)).
  sep cancel AMqAttr.
  eauto.
  rewrite Hl'.
  unfold nat_of_Z.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.
  
  (*p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ*)
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  hoare forward.
  eapply assign_rule_lvar with (v2:=nth_val' 5%nat v'83).
  split; intros.
  sep cancel (Alvarmapsto p). eauto.
  sep cancel (Alvarmapsto p). auto.
  
  instantiate (1:=(OS_EVENT∗)).
  2: { apply eq_vptr. do 2 eexists. splits; auto. }
  2: { sep pauto. sep cancel p_local. sep pauto. }
  introv Hsat.
  sep_lifts_trms_in Hsat Astruct.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq.
  lets Hposv_neq: Int.eq_false E3. auto.
  eapply new_array_type_vallist_match_split' in H20; eauto.
  mytac.

  subst v'74.
  destruct H29.
  lets H00: mqattr_corr H31 H28 E1 Hlemu.  
  destruct H00 as (et0 & wty0 & fl0 & maxm0 & msize0 & curm0 & mqc0 & Hget0 & H').
  assert (Hcases: ((exists eid, et0 = Valid_Addr eid /\ V_QATTRpevent v'83 = Some (Vptr eid) /\ eid <> vhold_addr) \/ et0 = Null /\ V_QATTRpevent v'83 = Some Vnull) \/ et0 = Holder /\ V_QATTRpevent v'83 = Some (Vptr vhold_addr)). 
  { clear -H'. intuition. }
  assert (H01 := H').
  clear H'. 
  destruct Hcases as [ Hok | Habt ].
  2: {
      destruct Habt as (Habt1 & Habt2).
      rewrite Habt1 in Hget0.
      hoare_lifts_trms_pre (Aop, absmqattrid).
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mqsend_absimp_get_eid_hold_abt.
      eauto.
      pure_auto.
      eapply absinfer_eq.
      apply absabort_rule.
  }
  assert (Hcases: 
         ((exists eid, et0 = Valid_Addr eid /\ v1 = Vptr eid) \/ et0 = Null /\ v1 = Vnull)
      \/ ((exists eid, et0 = Valid_Addr eid /\ v1 <> Vptr eid) \/ et0 = Null /\ v1 <> Vnull)).
  {
    inv Hok. destruct H36 as (eid & H'). 
    assert (Hvcs: v1 = Vptr eid \/ v1 <> Vptr eid) by tauto.
    inv Hvcs.
    left. left. exists eid. destructs H'. split; auto.
    right. left. exists eid. destructs H'. split; auto.
    assert (Hvcs: v1 = Vnull \/ v1 <> Vnull) by tauto.
    inv Hvcs.
    left. right. destructs H36. split; auto.
    right. right. destructs H36. split; auto.
  }

  inversion Hcases.
  2: {
      hoare_lifts_trms_pre (Aop, absmqattrid).
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mqsend_absimp_get_eid_abt; auto.
      eauto.
      auto.
  Optimize Proof.
  Optimize Heap.
      pure_auto.
      eapply absinfer_eq. 
      apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, absmqattrid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_get_eid_ok; auto.
  eauto.
  auto.
  pure_auto.
  eapply absinfer_eq. 
  clear Hcases.

  assert (H_prm_cases: (exists eid, v1 = Vptr eid /\ nth_val' 5%nat v'83 = Vptr eid) \/ (v1 = Vnull /\ nth_val' 5%nat v'83 = Vnull)).
  {
    inversion Hok as [Heo1 | Heo2]; inversion H36 as [Heo1' | Heo2'].
    destruct Heo1 as (eid & Heoeq1 & Hv_ & Hneq).
    destruct Heo1' as (eid' & Heoeq1' & Hv'_).
    rewrite Heoeq1' in Heoeq1. inverts Heoeq1.
    unfold V_QATTRpevent in Hv_.
    apply nth_val_nth_val'_some_eq in Hv_.
    left. eexists. split; eauto.
    destruct Heo1 as (eid & Heoeq1 & Hv_ & Hneq);
    destruct Heo2' as (Heoeq2' & Hv_');
    tryfalse.
    destruct Heo2 as (Heoeq2 & Hv_);
    destruct Heo1' as (eid & Heoeq1' & Hv_');
    tryfalse.
    unfold V_QATTRpevent in Heo2.
    destruct Heo2. destruct Heo2'.
    right.
    split; auto. 
    apply nth_val_nth_val'_some_eq; auto.
  }
  
  assert (Heq: nth_val' 5%nat v'83 = v1).
  {
    inversion H_prm_cases.
    destruct H37. destruct H37. congruence.
    destruct H37. congruence.
  }
  rewrite Heq. clear Heq. 
  assert (Hv1: (exists x0, v1 = Vptr x0) \/ v1 = Vnull). 
  {
    inversion H36. left. mytac. right. mytac.
  }

  (* prepare for exit critical *)
  eapply backward_rule1. 
  intros.
  eapply AMqAttr_select_sn_ex_strong.
  exists v'54. exists (Z.to_nat (Int.unsigned i)). exists v'82. exists v'83.
  sep pauto.

 (* OSTCBCur ′ → __OSTskQPtr =ₑ p ′;ₛ *)
  hoare_lifts_trms_pre (tcbllsegevaux, AOSTCBList, p_local). 
  eapply backward_rule1.
  introv Hsat.
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre. 
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  hoare_assign_evaux.
  clear -Hv1. destruct Hv1 as [(x0 & Hvl) | Hvl]; rewrite Hvl; auto. 
  clear -Hv1. unfold isevptr. unfold isptr. pure_auto.

  rename v'81 into ptrmp.
  assert (Hevptr: get ptrmp tid = Some (Vnull, Vnull, Vnull)).  
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  rename v'80 into locmp.
  assert (Hloc: get locmp tid = Some (V$ __EvLoc_normal)).
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }

  assert(new_array_type_vallist_match_q_getp:exists v, V_QATTRpevent v'83 = Some v /\ isptr v).
  clear - H20.
  eapply new_array_type_vallist_match_split' in H20; eauto.
  destruct H20 as (_ & _ & Hsp).
  lets Hvl: struct_type_vallist_match_elim_7 Hsp.
  destruct Hvl. do 6 destruct H.
  subst v'83.
  simpl in Hsp. 
  destruct Hsp as (_ & _ & _ & _ & _ &  Hk & _).
  exists x3.
  unfold V_OSMUXINFOPevent. unfold isptr.
  simpl. split; auto.
  destruct x3; tryfalse; pure_auto.

  assert (Hvpevt_eq: nth_val' 5 v'83 = v1).
  { clear -Hok H_prm_cases.
    unfold V_QATTRpevent in *.
    destruct Hok as [( eid & Heo & Hvp & _) | (Heo & Hvp)]; subst et0;
    eapply nth_val_nth_val'_some_eq in Hvp; rewrite Hvp;
    destruct H_prm_cases as [( eid0 & Heo & Hvp1) | (Heo & Hvp1)]; inverts Heo;
    auto;
    rewrite Hvp in Hvp1; tryfalse; auto. 
  }
  assert (Hisptr: isptr (v1)). 
  {
    clear - new_array_type_vallist_match_q_getp Hvpevt_eq.
    simpljoin1.
    unfold V_QATTRpevent in H.
    do 6 (destruct v'83; simpl in H; tryfalse).  
    inverts H. simpl. auto. 
  }

  rename v'51 into els.
  rename v'75 into semeibs.
  rename v'76 into muxeibs.
  rename v'77 into mqeibs.

  hoare_lifts_trms_pre (Aop, evptrid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_set_evloc_ptr; eauto.
  can_change_aop_solver.
  unfold CurTid. go.
  eapply absinfer_eq.

  remember (v1) as V_pevt.

  (*exit critical*)
  fold_evaux_q (V_pevt).
  clear -Hv1. destruct Hv1 as [(x0 & Hvl) | Hvl]; rewrite Hvl; auto.
  hoare forward prim.
  sep pauto.
  unfold EvtInv.
  unfold AMqEIBs.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqAttr.
  sep cancel Aier.
  sep cancel AMqCap.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.
  eapply evdel_nodup_normal_qptr_preserve; eauto.
  eapply evcre_nodup_normal_qptr_preserve; eauto.
  {
   destruct H_prm_cases as [(eid & Heo & Hvp) | (Heo & Hvp)];
   rewrite Hvp.
   eapply mq_ecb_p_qptr_normal_preserve; eauto.
   unfold is_que.
   destruct H36.
   simpljoin1.
   eapply H34; eauto.
   rewrite H45 in Hvp.
   instantiate (1:= mqc0).
   instantiate (1:= curm0).
   instantiate (1:= msize0).
   instantiate (1:= maxm0).
   instantiate (1:= fl0).
   instantiate (1:= wty0).
   instantiate (1:= i).
   inverts Hvp. auto.
   destruct H36.
   simpljoin1. rewrite H45 in Hvp. tryfalse.
   eapply mq_ecb_p_set_null3_preserve; eauto.
  }
  {
   destruct H_prm_cases as [(eid & Heo & Hvp) | (Heo & Hvp)];
   rewrite Hvp.
   eapply mux_ecb_p_qptr_normal_preserve; eauto.
   unfold is_que.
   destruct H36.
   simpljoin1.
   eapply H34; eauto.
   rewrite H45 in Hvp.
   instantiate (1:= mqc0).
   instantiate (1:= curm0).
   instantiate (1:= msize0).
   instantiate (1:= maxm0).
   instantiate (1:= fl0).
   instantiate (1:= wty0).
   instantiate (1:= i).
   inverts Hvp. auto.
   destruct H36.
   simpljoin1. rewrite H45 in Hvp. tryfalse.
   eapply mux_ecb_p_set_null3_preserve; eauto.
  }
  {
   destruct H_prm_cases as [(eid & Heo & Hvp) | (Heo & Hvp)];
   rewrite Hvp.
   eapply sem_ecb_p_qptr_normal_preserve; eauto.
   unfold is_que.
   destruct H36.
   simpljoin1.
   eapply H34; eauto.
   rewrite H45 in Hvp.
   instantiate (1:= mqc0).
   instantiate (1:= curm0).
   instantiate (1:= msize0).
   instantiate (1:= maxm0).
   instantiate (1:= fl0).
   instantiate (1:= wty0).
   instantiate (1:= i).
   inverts Hvp. auto.
   destruct H36.
   simpljoin1. rewrite H45 in Hvp. tryfalse.
   eapply sem_ecb_p_set_null3_preserve; eauto.
  }
  auto. auto. auto.
  unfold isevptr. unfold isptr. unfold isevloc.
  splits; eauto.
  pure_auto. pure_auto.

 (* **************call OSQPost****************)
 (* rr′ =ᶠ OSQPost(·p′ ,〈Void ∗〉msg_ptr′·) *)
  hoare forward.
  { destruct new_array_type_vallist_match_q_getp. simpljoin1.
    unfold V_QATTRpevent in H44. simpl in H44.
    do 6 (destruct v'83; tryfalse).
    simpl in H44. inverts H44.
    destruct H45. inverts H44. auto.
    destruct H44; inverts H44; auto.
  }
  pure_auto. 
  {
   unfold retpost. introv Hsat. inverts Hsat. 
   do 4 destruct H43.
   sep split in H43.
   destruct H45.
   pure_auto. 
  }
  { destruct Hisptr. rewrite H43 in Hvpevt_eq.
    destruct v'83; simpl in Hvpevt_eq; tryfalse. 
    do 5 (destruct v'83; tryfalse). 
    rewrite Hvpevt_eq. auto.
    destruct H43. rewrite H43 in Hvpevt_eq.
    destruct v'83; simpl in Hvpevt_eq; tryfalse. 
    do 5 (destruct v'83; tryfalse). 
    rewrite Hvpevt_eq. auto.
  }
  { sep pauto. sep cancel p_local. sep pauto. }
  { sep pauto. sep cancel p_local. sep pauto. } 
  
  (* ENTER_CRITICAL;ₛ*)
  hoare unfold.
  
  inverts H43.
  do 6 (destruct v'83; simpl in H45; tryfalse).
  unfold V_QATTRpevent in H45. simpl in H41.
  simpl in Hisptr.
  
  hoare forward prim.
  unfold EvtInv.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.

  hoare_lifts_trms_pre (tcbllsegevaux, AOSTCBList, p_local). 
  eapply backward_rule1.
  introv Hsat.
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre. 
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  hoare_assign_evaux.

  rename v'123 into ptrmp'.
  assert (Hevptr': get ptrmp' tid = Some  (Vnull, Vnull, v'133)).  
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }

  rename v'117 into semeibs'.
  rename v'118 into muxeibs'.
  rename v'119 into mqeibs'.
  rename v'122 into locmp'.
  rename v'93 into els'.

  (* OSTCBCur ′ → __OSTskQPtr =ₑ NULL;ₛ *) 
  hoare_lifts_trms_pre (Aop, evptrid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_set_evloc_ptr; eauto.
  can_change_aop_solver.
  unfold CurTid. go.
  eapply absinfer_eq.

  (*  EXIT_CRITICAL;ₛ *)
  assert(Heq_loc: (set locmp' tid (V$ __EvLoc_normal)) = locmp').
  { eapply get_set_same. 
    eapply join_get_r; eauto.
    eapply join_sig_get; eauto.
  }
  fold_evaux_q Vnull.
  hoare forward prim.
  sep cancel tcbdllflag.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep pauto. 
  2: { splits; eauto. }
  unfold EvtInv.
  sep pauto.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  unfold tcbllsegevaux.
  sep cancel llsegevaux.
  eauto.
  eapply evdel_nodup_set_null3_preserve; eauto.
  eapply evcre_nodup_set_null3_preserve; eauto. 
  eapply mq_ecb_p_set_null3_preserve; eauto.
  eapply mux_ecb_p_set_null3_preserve; eauto.
  eapply sem_ecb_p_set_null3_preserve; eauto.
  pure_auto. pure_auto.

  instantiate (1:= fun ptrmp => ( EX v v2,
         <|| mqsend_ret (Vint32 v) v5 ||>  **
         Aisr empisr **
         (EX v'80, Aier v'80) **
         Aie true **
         Ais nil **
         Acs nil **
         p_local OSLInv tid
           (logic_val (V$ 1)
            :: logic_val (V$ os_code_defs.__EvLoc_normal)
               :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
         [| 0 <= Int.unsigned v /\ Int.unsigned v <= Byte.max_unsigned |] **
         LV rr @ char_t |-> Vint32 v **
         LV p @ OS_EVENT ∗ |-> v2 **
         LV z @ long |-> Vint32 fl' **
         LV os_code_defs.x @ char_t |-> (V$ 1) **
         LV y @ long |-> Vint32 ms **
         LV ret @ long |-> v'0 **
         LV msgprio @ long |-> Vint32 i1 **
         LV msg_len @ long |-> Vint32 i0 **
         LV msg_ptr @ (char_t) ∗ |-> Vptr x **
         LV temp_num @ char_t |-> vtemp_dom **
         LV temp_dom @ char_t |-> vtemp_num **
         LV mqdes @ long |-> Vint32 i **
         A_dom_lenv
           ((msgprio, long)
            :: (msg_len, long)
               :: (msg_ptr, (char_t) ∗)
                  :: (mqdes, long)
                     :: (ret, long)
                        :: (os_code_defs.x, char_t)
                           :: (y, long)
                              :: (z, long)
                                 :: (p, OS_EVENT ∗) :: (rr, char_t) :: (temp_dom, char_t) :: (temp_num, char_t) :: nil))).
  sep pauto.
  exists v'80.
  sep cancel Aier.
  sep pauto.
  eauto.

(*********part of IF( z′ ==ₑ ′0 ) ****************)
  hoare unfold.

  hoare_lifts_trms_pre Aop.
  (* ret′ =ₑ 〈Int32〉 rr′ ;ₛ*)
  hoare forward.
  eapply assign_rule_lvar .
  split; intro.
  sep cancel (Alvarmapsto ret). eauto.
  sep cancel (Alvarmapsto ret). eauto.
  intros.
  eapply cast_rv_tint8_tint32.
  sep get rv.
  eapply leb_bytemax_true_intro in H19.
  rewrite H19. auto. simpl. eauto. 
  eapply assign_type_match_true. auto.
  intros. 
  exists (logic_val (V$ 1)
            :: logic_val (V$ os_code_defs.__EvLoc_normal)
               :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil). 
  sep pauto.

  (*L30:  If(ret′ ==ₑ ′OS_Q_FULL){ *)
  hoare forward.
  
  pure_auto.
  hoare unfold.
  
  assert (Hv5: v5 = Vint32 Int.mone \/ v5 <> Vint32 Int.mone) by tauto.
  destruct Hv5 as [Hv5 | Hv5].
  2:{  
     eapply abscsq_rule.
     apply noabs_oslinv.
     eapply mqsend_absimp_ret_eqfull_yes_abt;eauto.
     clear - H17 H20 Hv5. pure_auto. pure_auto. 
     eapply absinfer_eq.
     eapply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_ret_eqfull_yes;eauto.
  clear - H17 H20 Hv5. pure_auto. pure_auto.
  eapply absinfer_eq.
  
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  
  hoare forward.
  pure_auto.
  hoare unfold.
  
  assert (Hv5: v5 <> Vint32 Int.zero \/ v5 = Vint32 Int.zero) by tauto.
  destruct Hv5 as [Hv5 | Hv5].
  { eapply abscsq_rule.
    apply noabs_oslinv. 
    eapply absinfer_choice2. pure_auto.
    2:{ eauto. }
    pure_auto. auto.
    eapply absinfer_eq.
    eapply abscsq_rule.
    apply noabs_oslinv.
      eapply absinfer_choice1. pure_auto.
    2:{ eauto. }
    pure_auto. auto.
    eapply absinfer_eq.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mqsend_absimp_ret_eqnoerr_yes_abt;eauto.
    clear - H17 H20 H21 H22 Hv5. pure_auto.
    clear - H17 H20 H21 H22 Hv5. pure_auto. pure_auto.
    auto.
  Optimize Proof.
  Optimize Heap.
    eapply absinfer_eq.
    eapply absabort_rule.
  }
  { 
   eapply abscsq_rule.
   apply noabs_oslinv. eapply absinfer_choice2. pure_auto.
   2:{ eauto. }
   pure_auto. auto.
   eapply absinfer_eq.
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply absinfer_choice1. pure_auto.
   2:{ eauto. }
   pure_auto. auto.
   eapply absinfer_eq.
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mqsend_absimp_ret_eqnoerr_yes_end;eauto.
   clear - H17 H20 H21 H22. pure_auto.
   clear - H17 H20 H21 H22. pure_auto. pure_auto.
   eapply absinfer_eq.
   hoare forward. 
  }

  hoare unfold.
  assert (Hv5: v5 = Vint32 Int.mone \/ v5 <> Vint32 Int.mone) by tauto.
  destruct Hv5 as [Hv5 | Hv5].
  2:{  
     eapply abscsq_rule.
     apply noabs_oslinv.
     eapply absinfer_choice2. pure_auto.
     2:{ eauto. }
     pure_auto. auto.
     eapply absinfer_eq.   
     eapply abscsq_rule.
     apply noabs_oslinv.  
     eapply absinfer_choice2. pure_auto.
     2:{ eauto. }
     pure_auto. auto.
     eapply absinfer_eq.   
     eapply abscsq_rule.
     apply noabs_oslinv.
     eapply mqsend_absimp_ret_eqnoerr_no_abt;eauto.
     clear - H20.
     destruct H20; destruct (Int.eq v'82 ($ OS_NO_ERR));
     simpl in H; tryfalse; auto.
     clear - H17.
     destruct H17; destruct (Int.eq v'82 ($ OS_Q_FULL));
     simpl in H; tryfalse; auto.
     pure_auto.
     eapply absinfer_eq.
     eapply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_choice2. pure_auto.
  2:{ eauto. }
  
  pure_auto. auto.
  eapply absinfer_eq.
  eapply abscsq_rule.
  apply noabs_oslinv.  
  eapply absinfer_choice2. pure_auto.
  2:{ eauto. }
  
  pure_auto. auto.
  eapply absinfer_eq.   
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_ret_eqnoerr_no_end;eauto.
  clear - H20. pure_auto;simpl in H; tryfalse; auto.
  clear - H17. pure_auto;simpl in H; tryfalse; auto.
  pure_auto.
  eapply absinfer_eq.
  hoare forward. 
  destruct H20.  
  eapply astar_l_afalse_elim.
  instantiate (1:= [|val_inj (if Int.eq v'82 ($ OS_NO_ERR) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) <>
           Vint32 Int.zero /\
           val_inj (if Int.eq v'82 ($ OS_NO_ERR) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) <>
           Vnull /\
           val_inj (if Int.eq v'82 ($ OS_NO_ERR) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) <>
           Vundef|]);auto.
  eapply astar_l_afalse_elim.
  instantiate (1:= [|val_inj (if Int.eq v'82 ($ OS_NO_ERR) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) =
           Vint32 Int.zero \/
           val_inj (if Int.eq v'82 ($ OS_NO_ERR) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) =
           Vnull|]);auto.

(*********part of Else ****************)
  hoare unfold.

  hoare_lifts_trms_pre Aop.
 (*L29 :   ret′ =ₑ 〈Int32〉 rr′ ;ₛ*)
  hoare forward.
  eapply assign_rule_lvar.
  split; intro.
  sep cancel (Alvarmapsto ret). eauto.
  sep cancel (Alvarmapsto ret). eauto.
  intros.
  eapply cast_rv_tint8_tint32.
  sep get rv.
  eapply leb_bytemax_true_intro in H19.
  rewrite H19. auto. simpl. eauto. 
  eapply assign_type_match_true. auto.
  intros. exists (logic_val (V$ 1)
            :: logic_val (V$ os_code_defs.__EvLoc_normal)
               :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil). 
  sep pauto.

  (*L30:  If(ret′ ==ₑ ′OS_Q_FULL){ *)
  hoare forward.

  pure_auto.
  hoare unfold.

  assert (Hv5: v5 = Vint32 Int.mone \/ v5 <> Vint32 Int.mone) by tauto.
  destruct Hv5 as [Hv5 | Hv5].
  2:{
     eapply abscsq_rule.
     apply noabs_oslinv.
     eapply mqsend_absimp_ret_eqfull_yes_abt;eauto.
     clear - H17 H20 Hv5. pure_auto. pure_auto. 
     eapply absinfer_eq.
     eapply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_ret_eqfull_yes;eauto.
  clear - H17 H20 Hv5. pure_auto. pure_auto.
  eapply absinfer_eq.

  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  
  hoare forward.
  pure_auto.
  hoare unfold.
  
  assert (Hv5: v5 <> Vint32 Int.zero \/ v5 = Vint32 Int.zero) by tauto.
  destruct Hv5 as [Hv5 | Hv5].
  { eapply abscsq_rule.
    apply noabs_oslinv. 
    eapply absinfer_choice2. pure_auto.
    2:{ eauto. }
    pure_auto. auto.
    eapply absinfer_eq.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absinfer_choice1. pure_auto.
    2:{ eauto. }
    pure_auto. auto.
    eapply absinfer_eq.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mqsend_absimp_ret_eqnoerr_yes_abt;eauto.
    clear - H20 H21 H22. pure_auto.
    clear - H17 H20 H21 H22 Hv5. pure_auto. pure_auto.
    eapply absinfer_eq.
    eapply absabort_rule.
  }
  { eapply abscsq_rule.
    apply noabs_oslinv. 
    eapply absinfer_choice2. pure_auto.
    2:{ eauto. }
    pure_auto. auto.
    eapply absinfer_eq.   eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absinfer_choice1. pure_auto.
    2:{ eauto. }
    pure_auto. auto.
    eapply absinfer_eq.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mqsend_absimp_ret_eqnoerr_yes_end;eauto.
    clear - H20 H21 H22. pure_auto.
    clear - H17 H20 H21 H22 Hv5. pure_auto. pure_auto.
    eapply absinfer_eq.
    hoare forward. 
  }
  
  hoare unfold.
  assert (Hv5: v5 = Vint32 Int.mone \/ v5 <> Vint32 Int.mone) by tauto.
  destruct Hv5 as [Hv5 | Hv5].
  2:{
     eapply abscsq_rule.
     apply noabs_oslinv.
     eapply absinfer_choice2. pure_auto.
     2:{ eauto. }
     pure_auto. auto.
     eapply absinfer_eq.
     eapply abscsq_rule.
     apply noabs_oslinv.  
     eapply absinfer_choice2. pure_auto.
     2:{ eauto. }
     pure_auto. auto.
     eapply absinfer_eq.  
     eapply abscsq_rule.
     apply noabs_oslinv.
     eapply mqsend_absimp_ret_eqnoerr_no_abt;eauto.
     clear - H20.
     destruct H20; destruct (Int.eq v'82 ($ OS_NO_ERR));
     simpl in H; tryfalse; auto.
     clear - H17.
     destruct H17; destruct (Int.eq v'82 ($ OS_Q_FULL));
     simpl in H; tryfalse; auto.
     pure_auto.
     eapply absinfer_eq.
     eapply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_choice2. pure_auto.
  2:{ eauto. }
  pure_auto. auto.
  eapply absinfer_eq.
  eapply abscsq_rule.
  apply noabs_oslinv.  
  eapply absinfer_choice2. pure_auto.
  2:{ eauto. }
  pure_auto. auto.
  eapply absinfer_eq.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqsend_absimp_ret_eqnoerr_no_end;eauto.
  clear - H20. pure_auto;simpl in H; tryfalse; auto.
  clear - H17. pure_auto;simpl in H; tryfalse; auto.
  pure_auto.
  eapply absinfer_eq.
  hoare forward. 
  destruct H20.  
  eapply astar_l_afalse_elim.
  instantiate (1:= [|val_inj (if Int.eq v'82 ($ OS_NO_ERR) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) <>
           Vint32 Int.zero /\
           val_inj (if Int.eq v'82 ($ OS_NO_ERR) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) <>
           Vnull /\
           val_inj (if Int.eq v'82 ($ OS_NO_ERR) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) <>
           Vundef|]);auto.
  eapply astar_l_afalse_elim.
  instantiate (1:= [|val_inj (if Int.eq v'82 ($ OS_NO_ERR) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) =
           Vint32 Int.zero \/
           val_inj (if Int.eq v'82 ($ OS_NO_ERR) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) =
           Vnull|]);auto.
  Unshelve.
  exact O.
  exact (xH, Int.zero).
  exact O.
  exact O.  exact O.  exact O.  exact O.
Qed.
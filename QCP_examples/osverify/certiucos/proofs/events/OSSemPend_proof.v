
Require Import include_frm.
Require Import abs_infer_step.
Require Import ucos_frmaop.
Require Import seplog_lemmas.
Require Import seplog_tactics.

(* Require Import OSSemPend.
Require Import OSSemPend_spec. *)

Require Import abs_infer_abt.
(* Require Import sem_common_ext. *)
Require Import evauxvar_lemmas.
Require Import evaux_pure.
Require Import gjb_sem_common.

Require Import os_code_defs.
Require Import abs_op.
Require Import os_inv.
Require Import evtinv_lemmas.


Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

(******************************************* sem_pend **********************************)

Lemma absinfer_sem_pend_null_return :
  forall P x k sch, 
    can_change_aop P ->
    k = Vint32 (Int.repr OS_ERR_PEVENT_NULL) ->
    absinfer sch (<|| sem_pend (Vnull :: x :: k :: nil) ||> ** P) 
                               (<|| END Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) ||> **  P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma absinfer_sem_pend_null_return' :
  forall P x k sch s, 
    can_change_aop P ->
    k = Vint32 (Int.repr OS_ERR_PEVENT_NULL) ->
    absinfer sch (<|| spec_code_cons (sem_pend (Vnull :: x :: k :: nil)) s ||> ** P) 
     (<|| s ||> **  P).
Proof.
simpl spec_code_cons.
infer_solver 0%nat.
Qed.

Lemma absinfer_sem_pend_null_return_abt :
  forall P x k sch, 
    can_change_aop P ->
    k <> Vint32 (Int.repr OS_ERR_PEVENT_NULL) ->
    absinfer sch (<|| sem_pend (Vnull :: x :: k :: nil ) ||> ** P) 
                               (<|| ABORT ||> **  P).
Proof.
  intros.
  unfold sem_pend.
  simpl.
  eapply absinfer_trans.
  eapply absinfer_choice1; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
Qed.

Lemma absinfer_sem_pend_null_return_abt' :
  forall P x k sch s, 
    can_change_aop P ->
    k <> Vint32 (Int.repr OS_ERR_PEVENT_NULL) ->
    absinfer sch (<|| spec_code_cons (sem_pend (Vnull :: x :: k :: nil)) s ||> ** P) 
                               (<|| ABORT ||> **  P).
Proof.
intros.
simpl spec_code_cons.
eapply absinfer_trans.
eapply absinfer_choice1; try eauto.
eapply absinfer_trans.
Focus 2.
eapply absinfer_seq_abt; try eauto.
eapply absinfer_seq; try eauto.
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma absinfer_sem_pend_no_active_evt_err:
  forall a P b els tcbls tm curtid sch k s,
    can_change_aop P ->
    EcbMod.get els a = None ->
    k = V$ OS_ERR_EVENT_TYPE -> 
    absinfer sch
      (<|| spec_code_cons (sem_pend (Vptr a ::b:: k :: nil)) s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  introv Hcop Hnone Hk.
  subst.
  simpl spec_code_cons.
  infer_solver 1%nat.
Qed.

Lemma absinfer_sem_pend_no_active_evt_err_abt: 
  forall a P b els tcbls tm curtid sch k s,
    can_change_aop P ->
    EcbMod.get els a = None ->
    k <> V$ OS_ERR_EVENT_TYPE -> 
    absinfer sch
      (<|| spec_code_cons (sem_pend (Vptr a ::b:: k :: nil)) s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> ** 
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  introv Hcop Hnone Hne.
  simpl spec_code_cons.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver.
  2: eauto.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  can_change_aop_solver.
  2: eauto.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate (1:=HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
  can_change_aop_solver.
  instantiate (1:=ABORT).
  eapply absinfer_abt.
  can_change_aop_solver.
  can_change_aop_solver.
  absimp_abt_solver.
  can_change_aop_solver.
  eapply absinfer_seq_abt. 
  can_change_aop_solver.
  can_change_aop_solver.
  intros; auto. 
Qed.

Lemma absinfer_sem_pend_wrong_type_return : 
  forall a b P els tcbls tm curtid sch k, 
    can_change_aop P ->
    Int.unsigned b <= 65535 ->
    (exists d,
       EcbMod.get els a = Some d /\ ~ (exists x wls, d = (abssem x, wls))) ->
    k = Vint32 (Int.repr OS_ERR_EVENT_TYPE) ->
       absinfer sch
      (<|| sem_pend (Vptr a ::Vint32 b:: k :: nil) ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| END Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE))||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  infer_solver 2%nat.
Qed.

Lemma absinfer_sem_pend_wrong_type_return' :
  forall a b P els tcbls tm curtid sch k s, 
    can_change_aop P ->
    Int.unsigned b <= 65535 ->
    (exists d,
       EcbMod.get els a = Some d /\ ~ (exists x wls, d = (abssem x, wls))) ->
    k = Vint32 (Int.repr OS_ERR_EVENT_TYPE) ->
       absinfer sch
      (<|| spec_code_cons (sem_pend (Vptr a ::Vint32 b:: k :: nil)) s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
simpl spec_code_cons.
infer_solver 2%nat.
Qed.

Lemma absinfer_sem_pend_wrong_type_return_abt :
  forall a b P els tcbls tm curtid sch k, 
    can_change_aop P ->
    Int.unsigned b <= 65535 ->
    (exists d,
       EcbMod.get els a = Some d /\ ~ (exists x wls, d = (abssem x, wls))) ->
    k <> Vint32 (Int.repr OS_ERR_EVENT_TYPE) ->
       absinfer sch
      (<|| sem_pend (Vptr a ::Vint32 b:: k :: nil) ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  do 2 destruct H1.
  unfold sem_pend.
  simpl.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 2 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
Qed.

Lemma absinfer_sem_pend_wrong_type_return_abt' :
  forall a b P els tcbls tm curtid sch k s, 
    can_change_aop P ->
    Int.unsigned b <= 65535 ->
    (exists d,
       EcbMod.get els a = Some d /\ ~ (exists x wls, d = (abssem x, wls))) ->
    k <> Vint32 (Int.repr OS_ERR_EVENT_TYPE) ->
       absinfer sch
      (<|| spec_code_cons (sem_pend (Vptr a ::Vint32 b:: k :: nil)) s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  simpl spec_code_cons.
  do 2 destruct H1.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 2 try(eapply absinfer_trans; try (eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try (eapply absinfer_choice1; try eauto).
  eapply absinfer_trans.
  Focus 2.
  eapply absinfer_seq_abt; try eauto.
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
Qed.

Lemma absinfer_sem_pend_from_idle_abt :
  forall a b P els tcbls tm curtid sch k sus, 
    can_change_aop P ->
    Int.unsigned b <= 65535 ->
    (exists st msg, TcbMod.get tcbls curtid = Some (Int.repr OS_IDLE_PRIO, st, msg, sus)) ->
       absinfer sch
      (<|| sem_pend (Vptr a ::Vint32 b:: k :: nil) ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  do 2 destruct H1.
  unfold sem_pend.
  simpl.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 3 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s); 
         instantiate (2 := sem_pend_from_idle_err (|Vptr a :: Vint32 b :: k :: nil|));
         sep pauto).
Qed.

Lemma absinfer_sem_pend_from_idle_abt' :
  forall a b P els tcbls tm curtid sch k s sus, 
    can_change_aop P ->
    Int.unsigned b <= 65535 ->
    (exists st msg, TcbMod.get tcbls curtid = Some (Int.repr OS_IDLE_PRIO, st, msg, sus)) ->
       absinfer sch
      (<|| spec_code_cons (sem_pend (Vptr a ::Vint32 b:: k :: nil)) s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  do 2 destruct H1.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 3 try(eapply absinfer_trans; try (eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try (eapply absinfer_choice1; try eauto).
  eapply absinfer_trans.
  Focus 2.
  eapply absinfer_seq_abt; try eauto.
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := sem_pend_from_idle_err (|Vptr a :: Vint32 b :: k :: nil|));
         sep pauto).
Qed.

Lemma absinfer_sem_pend_not_ready_abt :
  forall P els tcbls tm curtid st msg v x prio sch k sus,
    Int.unsigned v <= 65535 ->
    TcbMod.get tcbls curtid = Some (prio, st, msg, sus) ->
    ~ (st = rdy /\ sus = false) ->
    can_change_aop P ->
    absinfer sch
      (<|| sem_pend (Vptr x :: Vint32 v :: k :: nil) ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  unfold sem_pend.
  simpl.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 4 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s); 
         instantiate (2 := sem_pend_not_ready_err (|Vptr x :: Vint32 v :: k :: nil|));
         sep pauto).
Qed.

Lemma absinfer_sem_pend_not_ready_abt' :
  forall P els tcbls tm curtid st msg a b prio sch k s sus,
    Int.unsigned b <= 65535 ->
    TcbMod.get tcbls curtid = Some (prio, st, msg, sus) ->
    ~ (st = rdy /\ sus = false) ->
    can_change_aop P ->
    absinfer sch
      (<|| spec_code_cons (sem_pend (Vptr a ::Vint32 b:: k :: nil)) s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 4 try(eapply absinfer_trans; try (eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try (eapply absinfer_choice1; try eauto).
  eapply absinfer_trans.
  Focus 2.
  eapply absinfer_seq_abt; try eauto.
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := sem_pend_not_ready_err (|Vptr a :: Vint32 b :: k :: nil|));
         sep pauto).
Qed.

Lemma absinfer_sem_pend_inst_get_return:
  forall P wls sid n tcbls tm curtid v sch k  els , 
    can_change_aop P ->
    Int.unsigned v <= 65535 ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu Int.zero n = true ->
    k = Vint32 (Int.repr OS_NO_ERR) ->
    absinfer sch
      ( <|| sem_pend (Vptr sid :: Vint32 v :: k :: nil) ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| END Some (Vint32 (Int.repr OS_NO_ERR)) ||> **
        HECBList (EcbMod.set els sid (abssem (Int.sub n Int.one), wls)) **
        HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof. 
  infer_solver 5%nat.
Qed.

Lemma absinfer_sem_pend_inst_get_return':
  forall P wls sid n tcbls tm curtid v sch k els s, 
    can_change_aop P ->
    Int.unsigned v <= 65535 ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu Int.zero n = true ->
    k = Vint32 (Int.repr OS_NO_ERR) ->
    absinfer sch
      ( <|| spec_code_cons (sem_pend (Vptr sid ::Vint32 v:: k :: nil)) s ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P) 
      ( <|| s ||> **
        HECBList (EcbMod.set els sid (abssem (Int.sub n Int.one), wls)) **
        HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  infer_solver 5%nat.
Qed.

Lemma absinfer_sem_pend_inst_get_return_abt:
  forall P wls els sid n tcbls tm curtid v sch k,
    can_change_aop P ->
    Int.unsigned v <= 65535 ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu Int.zero n = true ->
    k <> Vint32 (Int.repr OS_NO_ERR) ->
    absinfer sch
      ( <|| sem_pend (Vptr sid :: Vint32 v :: k :: nil) ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| ABORT ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  unfold sem_pend.
  simpl.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 5 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
Qed.

Lemma absinfer_sem_pend_inst_get_return_abt':
  forall P wls els sid n tcbls tm curtid v sch k s,
    can_change_aop P ->
    Int.unsigned v <= 65535 ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu Int.zero n = true ->
    k <> Vint32 (Int.repr OS_NO_ERR) ->
    absinfer sch
      ( <|| spec_code_cons (sem_pend (Vptr sid ::Vint32 v:: k :: nil)) s ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| ABORT ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 5 try(eapply absinfer_trans; try (eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try (eapply absinfer_choice1; try eauto).
  eapply absinfer_trans.
  Focus 2.
  eapply absinfer_seq_abt; try eauto.
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := sem_pend_inst_get_succ (|Vptr sid :: Vint32 v :: k :: nil|));
         sep pauto).
Qed.

(* Lemma absinfer_sem_pend_block_some :
  forall P qid v wl p st m tm curtid tcbls sch k infol minfol qattrl semeibs muxeibs qeibs els vhold
                               ebls pbls evatoms evstructs evarrays
                               tcblh tcbvl fecbh fecbvl,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
    v <> Int.zero /\
    EcbMod.get els qid = Some (abssem Int.zero, wl) ->
    TcbMod.get tcbls curtid = Some (p,st,m) ->
    absinfer sch
      ( <|| sem_pend (Vptr qid :: Vint32 v :: k :: nil) ||>  ** 
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid **
           ACNU infol minfol qattrl semeibs muxeibs qeibs els vhold
                               ebls pbls evatoms evstructs evarrays
                               tcblh tcbvl fecbh fecbvl ** P) 
      (<|| isched;; sem_pend_after_sched (|Vptr qid :: Vint32 v :: k :: nil|)  ;;
           ((* sem_pend_p_not_legal_err (|Vptr qid :: Vint32 v :: k :: nil|) ?? *)
             (* sem_pend_timeout_err_wait (|Vptr qid :: Vint32 v :: k :: nil|) ?? *)
            sem_pend_timeout_err_rdy (|Vptr qid :: Vint32 v :: k :: nil|) ??
            sem_pend_block_get_succ (|Vptr qid :: Vint32 v :: k :: nil|)) ||> **
           HECBList (EcbMod.set els qid (abssem Int.zero ,curtid::wl)) **
           HTCBList (TcbMod.set tcbls curtid (p,wait (os_stat_sem qid) (Some v), m) ) **
           HTime tm ** HCurTCB curtid **
           ACNU infol minfol qattrl semeibs muxeibs qeibs (EcbMod.set els qid (abssem Int.zero ,curtid::wl)) vhold
    pply AEIBAarray_sem_set_wls'_preserve; eauto.
  sep cancel AEIBAarray.
  apply astar_r_aemp_elim; auto. 
  eapply AMqEIBAarray_sem_set_wls'_preserve; eauto.
  sep pauto. 
  eapply RH_SEM_EINFO_ECB_P_set_wls'; eauto.
  eapply mq_ecb_p_sem_set_wls'_preserve; eauto.
  eapply mux_ecb_p_sem_set_wls'_preserve; eauto.
  eapply sem_ecb_p_sem_set_wls'_preserve; eauto. 
  (* eapply ACNU_els_set'; eauto. *)
Qed.                           ebls pbls evatoms evstructs evarrays
                               tcblh tcbvl fecbh fecbvl ** P). 
Proof.
  infer_solver 6%nat.
  unfold ACNU in *.
  sep pauto.
  unfold AEINFO in *.
  sep pauto. 
  eapply AEIBAarray_sem_set_wls'_preserve; eauto.
  sep cancel AEIBAarray.
  apply astar_r_aemp_elim; auto. 
  eapply AMqEIBAarray_sem_set_wls'_preserve; eauto.
  sep pauto. 
  eapply RH_SEM_EINFO_ECB_P_set_wls'; eauto.
  eapply mq_ecb_p_sem_set_wls'_preserve; eauto.
  eapply mux_ecb_p_sem_set_wls'_preserve; eauto.
  eapply sem_ecb_p_sem_set_wls'_preserve; eauto. 
  (* eapply ACNU_els_set'; eauto. *)
Qed. *)

Lemma absinfer_sem_pend_block':
  forall P qid v wl p st m tm curtid tcbls sch k els s sus,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
    EcbMod.get els qid = Some (abssem Int.zero, wl) ->
    TcbMod.get tcbls curtid = Some (p,st,m, sus) ->
    absinfer sch
      ( <|| spec_code_cons (sem_pend (Vptr qid ::Vint32 v:: k :: nil)) s ||>  ** 
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| isched;; sem_pend_after_sched (|Vptr qid :: Vint32 v :: k :: nil|)  ;;
           (
              (sem_pend_timeout_err_rdy (|Vptr qid :: Vint32 v :: k :: nil|) ;; s) ??
              (sem_pend_block_get_succ (|Vptr qid :: Vint32 v :: k :: nil|) ;; s)) ||> **
           HECBList (EcbMod.set els qid (abssem Int.zero ,curtid::wl)) **
           HTCBList (TcbMod.set tcbls curtid (p,wait (os_stat_sem qid) 
              (if Int.eq v Int.zero then None else Some v), m, sus) ) **
           HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  destruct (Int.eq v Int.zero) eqn: eq1.
  eapply sem_lab.semacc_int_eq_true in eq1.
  subst.
  infer_solver 6%nat.
  eapply sem_lab.semacc_int_eq_false in eq1.
  infer_solver 6%nat.
Qed.

(* Lemma absinfer_sem_pend_block_none' :
  forall P qid v wl p st m tm curtid tcbls sch k infol minfol qattrl semeibs muxeibs qeibs els vhold
                               ebls pbls evatoms evstructs evarrays
                               tcblh tcbvl fecbh fecbvl s, 
    Int.unsigned v <= 65535 ->
    v = Int.zero ->
    can_change_aop P ->
    EcbMod.get els qid = Some (abssem Int.zero, wl) ->
    TcbMod.get tcbls curtid = Some (p,st,m) ->
    absinfer sch
      ( <|| spec_code_cons (sem_pend (Vptr qid ::Vint32 v:: k :: nil)) s ||>  ** 
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid **
           ACNU infol minfol qattrl semeibs muxeibs qeibs els vhold
                               ebls pbls evatoms evstructs evarrays
                               tcblh tcbvl fecbh fecbvl ** P) 
      (<|| isched;; sem_pend_after_sched (|Vptr qid :: Vint32 v :: k :: nil|)  ;;
           ((* (sem_pend_p_not_legal_err (|Vptr qid :: Vint32 v :: k :: nil|);; s) ?? *)
              (* (sem_pend_timeout_err_wait (|Vptr qid :: Vint32 v :: k :: nil|) ;; s) ?? *)
              (sem_pend_timeout_err_rdy (|Vptr qid :: Vint32 v :: k :: nil|) ;; s) ??
              (sem_pend_block_get_succ (|Vptr qid :: Vint32 v :: k :: nil|) ;; s)) ||> **
           HECBList (EcbMod.set els qid (abssem Int.zero ,curtid::wl)) **
           HTCBList (TcbMod.set tcbls curtid (p,wait (os_stat_sem qid) None, m) ) **
           HTime tm ** HCurTCB curtid **
           ACNU infol minfol qattrl semeibs muxeibs qeibs (EcbMod.set els qid (abssem Int.zero ,curtid::wl)) vhold
                               ebls pbls evatoms evstructs evarrays
                               tcblh tcbvl fecbh fecbvl ** P).
Proof.
  infer_solver 6%nat.
  unfold ACNU in *.
  sep pauto.
  unfold AEINFO in *.
  sep pauto. 
  eapply AEIBAarray_sem_set_wls'_preserve; eauto.
  sep cancel AEIBAarray.
  apply astar_r_aemp_elim; auto. 
  eapply AMqEIBAarray_sem_set_wls'_preserve; eauto.
  sep pauto. 
  eapply RH_SEM_EINFO_ECB_P_set_wls'; eauto.
  eapply mq_ecb_p_sem_set_wls'_preserve; eauto.
  eapply mux_ecb_p_sem_set_wls'_preserve; eauto.
  eapply sem_ecb_p_sem_set_wls'_preserve; eauto.   
  (* eapply ACNU_els_set'; eauto. *)
Qed. *)

(*---------------------------------------------------------------------*)

Lemma absinfer_sem_pend_p_aftersch :
  forall qid P v els tcbls tm curtid sch k p st m sus,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
     TcbMod.get tcbls curtid = Some (p, st, m, sus) ->
      (st = rdy /\ sus = false
        \/ (st = wait (os_stat_sem qid) (Some Int.zero) /\ sus = false)) ->
    absinfer sch
      (<|| sem_pend_after_sched (|Vptr qid :: Vint32 v :: k :: nil|) ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| END None ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma absinfer_sem_pend_p_aftersch' :
  forall qid P v els tcbls tm curtid sch k p st m s sus,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
     TcbMod.get tcbls curtid = Some (p, st, m, sus) ->
      (st = rdy /\ sus = false
        \/ (st = wait (os_stat_sem qid) (Some Int.zero) /\ sus = false)) ->
    absinfer sch
      (<|| sem_pend_after_sched (|Vptr qid :: Vint32 v :: k :: nil|) ;; s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma absinfer_sem_pend_p_aftersch_abt :
  forall qid P v els tcbls tm curtid sch k p st m sus,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
     TcbMod.get tcbls curtid = Some (p, st, m, sus) ->
      ~(st = rdy /\ sus = false
        \/ (st = wait (os_stat_sem qid) (Some Int.zero) /\ sus = false)) ->
    absinfer sch
      (<|| sem_pend_after_sched (|Vptr qid :: Vint32 v :: k :: nil|) ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s); 
         instantiate (2 := sem_pend_after_sched (|Vptr qid :: Vint32 v :: k :: nil|));
         sep pauto).
Qed.

Lemma absinfer_sem_pend_p_aftersch_abt' :
  forall qid P v els tcbls tm curtid sch k p st m s sus,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
     TcbMod.get tcbls curtid = Some (p, st, m, sus) ->
      ~(st = rdy /\ sus = false
        \/ (st = wait (os_stat_sem qid) (Some Int.zero) /\ sus = false)) ->
    absinfer sch
      (<|| sem_pend_after_sched (|Vptr qid :: Vint32 v :: k :: nil|) ;; s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  eapply absinfer_trans;
    try (eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := sem_pend_after_sched (|Vptr qid :: Vint32 v :: k :: nil|));
         sep pauto).
Qed.

Lemma absinfer_sem_pend_to_timeout_rdy :
  forall P qid tm curtid tcbls v prio m sch k n wls els sus,
    Int.unsigned v <= 65535 ->
    TcbMod.get tcbls curtid = Some (prio, wait (os_stat_sem qid) (Some Int.zero), m, sus) ->
    EcbMod.get els qid = Some (abssem n, wls) ->
    In curtid wls ->
    can_change_aop P ->
     k = Vint32 (Int.repr OS_TIMEOUT) ->
    absinfer sch
      ( <||
            sem_pend_timeout_err_rdy (|Vptr qid :: Vint32 v :: k :: nil|) ??
            sem_pend_block_get_succ (|Vptr qid :: Vint32 v :: k :: nil|) ||>  ** 
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid **
            P) 
      (<|| END Some (Vint32 (Int.repr OS_TIMEOUT)) ||> **
            HECBList (EcbMod.set els qid (abssem n, remove_tid curtid wls)) **
            HTCBList (TcbMod.set tcbls curtid (prio,rdy, m, false) ) ** 
            HTime tm ** HCurTCB curtid **
            P). 
Proof.
  infer_solver 0%nat.
Qed.

Lemma absinfer_sem_pend_to_timeout_rdy' :
  forall P qid tm curtid tcbls v prio m sch k n wls s els sus,
    Int.unsigned v <= 65535 ->
    TcbMod.get tcbls curtid = Some (prio, wait (os_stat_sem qid) (Some Int.zero), m, sus) ->
    EcbMod.get els qid = Some (abssem n, wls) ->
    In curtid wls ->
    can_change_aop P ->
     k = Vint32 (Int.repr OS_TIMEOUT) ->
    absinfer sch
      ( <||
            (sem_pend_timeout_err_rdy (|Vptr qid :: Vint32 v :: k :: nil|) ;; s) ??
            (sem_pend_block_get_succ (|Vptr qid :: Vint32 v :: k :: nil|) ;; s) ||>  ** 
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid **
            P) 
      (<||  s ||> **
            HECBList (EcbMod.set els qid (abssem n, remove_tid curtid wls)) **
            HTCBList (TcbMod.set tcbls curtid (prio,rdy, m, false) ) ** 
            HTime tm ** HCurTCB curtid **
           P). 
Proof.
  infer_solver 0%nat.
Qed.

Lemma absinfer_sem_pend_to_timeout_rdy_abt :
   forall P els qid tm curtid tcbls v prio m sch k n wls sus,
    Int.unsigned v <= 65535 ->
    TcbMod.get tcbls curtid = Some (prio, wait (os_stat_sem qid) (Some Int.zero), m, sus) ->
    EcbMod.get els qid = Some (abssem n, wls) ->
    In curtid wls ->
    can_change_aop P ->
     k <> Vint32 (Int.repr OS_TIMEOUT) ->
    absinfer sch
      ( <||
            sem_pend_timeout_err_rdy (|Vptr qid :: Vint32 v :: k :: nil|) ??
            sem_pend_block_get_succ (|Vptr qid :: Vint32 v :: k :: nil|) ||>  ** 
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P) 
      (<||  ABORT ||> **
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s); 
         instantiate (2 := sem_pend_timeout_err_rdy (|Vptr qid :: Vint32 v :: k :: nil|));
         sep pauto).
Qed.

Lemma absinfer_sem_pend_to_timeout_rdy_abt' :
   forall P els qid tm curtid tcbls v prio m sch k n wls s sus,
    Int.unsigned v <= 65535 ->
    TcbMod.get tcbls curtid = Some (prio, wait (os_stat_sem qid) (Some Int.zero), m, sus) ->
    EcbMod.get els qid = Some (abssem n, wls) ->
    In curtid wls ->
    can_change_aop P ->
     k <> Vint32 (Int.repr OS_TIMEOUT) ->
    absinfer sch
      ( <||
            (sem_pend_timeout_err_rdy (|Vptr qid :: Vint32 v :: k :: nil|) ;; s) ??
            (sem_pend_block_get_succ (|Vptr qid :: Vint32 v :: k :: nil|) ;; s) ||>  ** 
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P) 
      (<||  ABORT ||> **
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_trans; try(eapply absinfer_seq; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := sem_pend_timeout_err_rdy (|Vptr qid :: Vint32 v :: k :: nil|));
         sep pauto).
  eapply absinfer_seq_abt; try eauto.
Qed.

Lemma absinfer_sem_pend_to_succ:
      forall P els qid v tm curtid tcbls sch k p m st sus,
       Int.unsigned v <= 65535 ->
       can_change_aop P ->
      TcbMod.get tcbls curtid = Some (p, st, m, sus) ->
       ~(exists wt, st = wait (os_stat_sem qid) wt) ->
      k = Vint32 (Int.repr OS_NO_ERR) ->
       absinfer sch
         ( <||
            sem_pend_timeout_err_rdy (|Vptr qid :: Vint32 v :: k :: nil|) ??
            sem_pend_block_get_succ (|Vptr qid :: Vint32 v :: k :: nil|) ||> **
               HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
         ( <|| END Some (Vint32 (Int.repr OS_NO_ERR)) ||>  **
                HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma absinfer_sem_pend_to_succ':
      forall P els qid v tm curtid tcbls sch k s p m st sus,
       Int.unsigned v <= 65535 ->
       can_change_aop P ->
       TcbMod.get tcbls curtid = Some (p, st, m, sus) ->
       ~(exists wt, st = wait (os_stat_sem qid) wt) ->
      k = Vint32 (Int.repr OS_NO_ERR) ->
       absinfer sch
         ( <||
              (sem_pend_timeout_err_rdy (|Vptr qid :: Vint32 v :: k :: nil|) ;; s) ??
              (sem_pend_block_get_succ (|Vptr qid :: Vint32 v :: k :: nil|) ;; s) ||> **
               HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
         ( <|| s ||>  **
                HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma absinfer_sem_pend_to_succ_abt:
      forall P els qid v tm curtid tcbls sch k p m st sus,
       Int.unsigned v <= 65535 ->
       can_change_aop P ->
      TcbMod.get tcbls curtid = Some (p, st, m, sus) ->
       ~(exists wt, st = wait (os_stat_sem qid) wt) ->
      k <> Vint32 (Int.repr OS_NO_ERR) ->
       absinfer sch
         ( <||
            sem_pend_timeout_err_rdy (|Vptr qid :: Vint32 v :: k :: nil|) ??
            sem_pend_block_get_succ (|Vptr qid :: Vint32 v :: k :: nil|) ||> **
               HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
         ( <||  ABORT ||>  **
               HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s); 
         instantiate (2 := sem_pend_block_get_succ (|Vptr qid :: Vint32 v :: k :: nil|));
         sep pauto).
Qed.

Lemma absinfer_sem_pend_to_succ_abt':
      forall P els qid v tm curtid tcbls sch k s p m st sus,
       Int.unsigned v <= 65535 ->
       can_change_aop P ->
       TcbMod.get tcbls curtid = Some (p, st, m, sus) ->
       ~(exists wt, st = wait (os_stat_sem qid) wt) ->
      k <> Vint32 (Int.repr OS_NO_ERR) ->
       absinfer sch
         ( <||
              (sem_pend_timeout_err_rdy (|Vptr qid :: Vint32 v :: k :: nil|) ;; s) ??
              (sem_pend_block_get_succ (|Vptr qid :: Vint32 v :: k :: nil|) ;; s) ||> **
               HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
         ( <|| ABORT ||>  **
               HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_seq; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := sem_pend_block_get_succ (|Vptr qid :: Vint32 v :: k :: nil|));
         sep pauto).
  eapply absinfer_seq_abt; try eauto.
Qed.

Require Import gjb_common.
Require Import gjb_sem_common.
Require Import seplog_trm_tacs.
Require Import sem_common.
Require Import sempend_pure.
Require Import sempend_pure_ext.
Require Import Lia.
Require Import OSETWaitPure.
Require Import Mbox_common.
Require Import OSQPostPure.
Require Import OSTimeDlyPure.
Require Import OSTimeTickPure.
(* Require Import OSQPendPure.  *)
Require Import freeevtlist_lemmas.
Require Import semacc_pure.
Require Import sem_corecommu.
Require Import hoare_forward_tac_ext.

Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.
(*---------------------------------------copy--------------------------------------------------*)

(* use this old hoare_if to avoid large modification *)
Ltac lzh_find_ret_stmt stmts :=
  match stmts with
    | sseq ?s ?rs =>
      match s with
        | srete _ => constr:(some 1%nat)
        | _ => lzh_find_ret_stmt rs
      end
    | srete _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac lzh_hoare_if2 :=
  hoare_unfold;
  hoare forward; 
  match goal with
    | |- {|_, _, _, _, _, _|} |- ?ct {{?p ** [|?v <> Vint32 Int.zero /\
                                            ?v <> Vnull /\
                                            ?v <> Vundef|]}} ?stmts {{_}} =>
      (* idtac "if block proof"; *)
      let x := lzh_find_ret_stmt stmts in
        match x with
          | some _ => instantiate (1:=Afalse)
          | none _ => idtac
        end;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse

    | |- {|_, _, _, _, _, _|} |- ?ct {{_}} _ {{_}} => 
      (* idtac "if all"; *)
      hoare forward;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse
      (* first proof if-true condition, then proof if-false condition *)
    | _ => pauto
  end.

Hint Resolve CltEnvMod.beq_refl: brel .
Hint Resolve noabs_oslinv.
Hint Extern 2 (_ <= _) => apply Z.leb_le; trivial.

Lemma low_stat_impl_high_stat_sem_zero_sus'
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid msg sus st,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     prio_not_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
    V_OSTCBDly tcurl = Some (Vint32 wt) ->
    V_OSTCBStat tcurl = Some (Vint32 (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND))) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
    Int.eq wt Int.zero = true ->
    TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
     exists t_opt,
       st = wait (os_stat_sem sid) t_opt /\ (t_opt = (Some wt) \/ t_opt = None).
Proof.
  intros.
  lets Hget: H5.
  eapply low_stat_impl_high_stat_sem_zero_sus in Hget; eauto.
  destruct Hget as (m & t & Hget & Hc).
  rewrite H6 in Hget.
  inverts Hget.
  eauto.
Qed.

Lemma low_stat_impl_high_stat_sem_zero_sus_gen'
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid msg (sus:bool) st,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     (if sus then prio_not_in_tbl prio rtbl else prio_in_tbl prio rtbl) ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
    V_OSTCBDly tcurl = Some (Vint32 wt) ->
    V_OSTCBStat tcurl = Some (Vint32 (if sus then (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)) else ($ OS_STAT_SEM))) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
    Int.eq wt Int.zero = true ->
    TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
     exists t_opt,
       st = wait (os_stat_sem sid) t_opt /\ (t_opt = (Some wt) \/ t_opt = None).
Proof.
  intros.
  destruct sus.
  eapply low_stat_impl_high_stat_sem_zero_sus'; eauto.
  eapply low_stat_impl_high_stat_sem_zero_some' in H4; eauto.
  eapply semacc_int_eq_true in H5.
  subst.
  eauto.
Qed.


Lemma OSSemPend_proof:
  forall vl p r logicl ct, 
    Some p =
    BuildPreI os_internal OSSemPend
              vl logicl OSSemPendPre ct->
    Some r =
    BuildRetI os_internal OSSemPend vl logicl OSSemPendPost ct->
    exists t d1 d2 s,
      os_internal OSSemPend = Some (t, d1, d2, s) /\
      {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  rename v'1 into etype.
  change ((x0 :: Vint32 i :: nil) ++ etype :: nil) with (x0 :: Vint32 i :: etype :: nil).
  subst.

  hoare forward prim.
(*   splits;eauto. intros;splits;eauto. *)
  hoare unfold.
  
  (* L1 - L2 *)
  lzh_hoare_if2.
  subst.
  (* sempend (Vnull :: Vint32 i :: etype :: nil)  *)
  assert (Het: etype = Vint32 (Int.repr OS_ERR_PEVENT_NULL) 
                  \/ etype <> Vint32 (Int.repr OS_ERR_PEVENT_NULL)) by tauto.
  destruct Het. 
  subst.
   (* sempend (Vnull :: Vint32 i :: OS_ERR_PEVENT_NULL :: nil)  *)
  hoare abscsq.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_null_return'; pure_auto.
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel EvtInv.
  sep cancel p_local.
  sep pauto.
  pure_auto.
  pure_auto. 
  hoare forward.
   (* sempend (Vnull :: Vint32 i :: etype :: nil)  *)
  hoare abscsq.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_null_return_abt';
  try can_change_aop_solver; try eauto.
  eapply absabort_rule.

  (* pevent <> NULL *)
  rename x into p.

  hoare unfold.
  unfold EvtInv. 

  rename v'18 into vcspace.
  rename v'19 into v19. 
  rename v'20 into v20. 
  rename v'21 into v21. 

  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst. (* addr of placeholder is now vhold_addr *) 

  rename v'34 into locmp.
  rename v'35 into ptrmp.
  rename v'10 into els.
  rename v'0 into fecbh.
  rename v'18 into fecbvl.
  rename v'29 into semeibs.
  rename v'30 into muxeibs.
  rename v'31 into mqeibs.
  hoare_assert_pure (get ptrmp ct = Some (Vnull, Vptr p, Vnull)
                                             /\ get locmp ct = Some (V$ os_code_defs.__EvLoc_normal)).
  { get_hsat Hsat.
     sep_lifts_trms_in Hsat (evlocid, evptrid, tcbllsegevaux, AOSTCBList,p_local).
    eapply get_aux;eauto.
   }
  hoare_split_pure_all.
  destruct H4 as (Hget_ptr & Hget_loc).

  assert (Hevt: is_evt els p \/ ptr_in_ecblist (Vptr p) fecbh fecbvl).  
  { eapply sem_ecb_nml; eauto. }

  destruct Hevt as [Hevt | Hfree]. 
  Focus 2.
  (* pevent points into list of free ECBs *)
  hoare_assert_pure (exists p, fecbh = Vptr p).
  {
    unfold ptr_in_ecblist in Hfree.
    lets Hptr: ptr_in_ecbsllseg_ptr Hfree.
    eauto.
  }
  hoare_split_pure_all.
  destruct v'0 as (fb & fi).
  subst.
  eapply backward_rule1.
  introv Hsat.
  unfold AOSEventFreeList in Hsat.
  unfold ecbf_sll in Hsat.
  sep normal in Hsat.
  sep_lifts_trms_in Hsat ecbf_sllseg.
  eapply ecbf_sllseg_split3_frm; eauto.
  hoare unfold.
  lzh_hoare_if. 
  2: {
    change (Int.eq ($ OS_EVENT_TYPE_UNUSED) ($ OS_EVENT_TYPE_SEM)) with false in Hif_false. 
    inverts Hif_false.
  }
  unfold AECBList.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Astruct, evsllseg).

  hoare_assert_pure (get els (v'35, Int.zero) = None).
  {
    get_hsat Hsat.
    lets H00: semcre_ecblist_star_not_inh H4 Hsat. 
    auto.
  }
  hoare_split_pure_all.
  rename H11 into Hnone.
  
  casetac etype (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) Heeq Hene.
  2: {
    hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid). 
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absinfer_sem_pend_no_active_evt_err_abt; try pure_auto.
    go. unfold CurTid. go.
    eapply absinfer_eq. 
    apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid). 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_no_active_evt_err; eauto. 
  go. unfold CurTid. go.
  eapply absinfer_eq.

  (* EXIT_CRITICAL *) 
  hoare forward prim. 
  unfold EvtInv.
  
  unfold AECBList.
  sep normal.
  sep pauto.

  sep cancel evsllseg.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel Aier.
  sep cancel p_local.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  unfold AOSEventFreeList.
  sep normal.
  sep cancel OSEventFreeList.
  unfold ecbf_sll.
  sep_lifts_trms ecbf_sllseg. 
  eapply ecbf_sllseg_compose3_frm; eauto. 
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel Aarray. (* new add *)
  sep cancel ecbf_sllseg.
  sep cancel ecbf_sllseg.
  eauto.
  go.
  go. go. go. auto. auto. auto. auto. auto.
  pure_auto.


  (* return OS_ERR_EVENT_TYPE *) 
  hoare forward.

  (* pevent points to an active ECB *) 
  unfold AECBList.
  hoare unfold.
  rename H4 into H_elp.
  assert (Hecb: exists ecb, get els p = Some ecb). 
  {
    unfold is_evt in Hevt.
    destruct Hevt as [Hsem | [Hmux | Hque]].
    unfold is_sem in Hsem.
    simpljoin1; eexists; eauto.
    unfold is_mux in Hmux.
    simpljoin1; eexists; eauto.
    unfold is_que in Hque.
    simpljoin1; eexists; eauto.
  }
  destruct Hecb as (ecb & Hgetecb).
  destruct ecb. 
  lets Hctr: ECBList_P_get_ectr_some Hgetecb H_elp.
  destruct Hctr as (evl & etbl & petbl & Hgetectr). (* add petbl *)
  
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat evsllseg.
  eapply get_ectr_decompose; eauto.
  hoare unfold.

  hoare_assert_pure (length v'13 = length v'29).
  {
    get_hsat Hsat. 
    sep_lifts_trms_in Hsat evsllseg. 
    eapply evsllseg_aux in Hsat. 
    destruct Hsat.
    eauto. 
  }
  eapply pure_split_rule'; introv Heqlen.
  lets H00: ecblist_p_decompose H_elp; eauto. 
  destruct H00 as (els1 & els2 & x' & H''). 
  destruct H'' as (Hecbl1 & Hecbl2 & Hjo).
  hoare_assert_pure (x' = Vptr (v'38, Int.zero)). 
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg. 
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  hoare_split_pure_all; subst.
  
  assert (Hecbl' := Hecbl2).
  do 2 (rewrite ele_lst_cons in Hecbl'). 
  unfold ECBList_P in Hecbl'.
  fold ECBList_P in Hecbl'.
  destruct Hecbl' as (qid & Hqid & Hecbetbl & Hecbpetbl & Hex). (* add Hecbpetbl *)
  inverts Hqid. 
  destruct Hex as (absmq & mqls' & v'' & Helptr & Hjo' & Hrlh & Hecbl20).
  unfold V_OSEventListPtr in Helptr.
  inverts Helptr.

  lzh_hoare_if.
  pure_auto.
  pure_auto.
  
  (* the concrete type is not OS_EVENT_TYPE_SEM *) 
  hoare_assert_pure (~exists n wls, get els (v'38, Int.zero) = Some (abssem n, wls)).
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply semacc_eventtype_neq_sem in Hsat; eauto.
    sep split in Hsat.
    auto.
    go.
  }
  hoare_split_pure_all.

  casetac etype (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) Heeq Hene.
  2: {
    hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid). 
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absinfer_sem_pend_wrong_type_return_abt'; eauto. 
    go. unfold CurTid. go.
    unfold get, EcbMap in Hgetecb.
    unfold get, EcbMap in H4.
    rewrite Hgetecb in H4.
    exists (e, w). simpljoin1. splits; auto.
    introv Hf. apply H4. simpljoin1. do 2 eexists; eauto. 
    eapply absinfer_eq.
    apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid). 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_wrong_type_return'; eauto. 
  go. unfold CurTid. go.
  unfold get, EcbMap in Hgetecb.
  unfold get, EcbMap in H4.
  rewrite Hgetecb in H4.
  exists (e, w). simpljoin1. splits; auto.
  introv Hf. apply H4. simpljoin1. do 2 eexists; eauto.   
  eapply absinfer_eq.

  fold_AEventNode_r. 
  
  eapply backward_rule1.
  introv Hsat.
  
  eapply fold_EvtInv_part1.
  sep cancel AOSQFreeList. 
  sep cancel AOSQFreeBlk.
  sep_lifts_trms_in Hsat (AEventNode ,(evsllseg v'0), (evsllseg v''),OSEventList).

  eapply lzh_evsllseg_compose in Hsat; eauto.
  eapply AECBList_fold in Hsat; eauto. 
  sep cancel AECBList.
  sep pauto.
  eapply backward_rule1.
  introv Hsat.  
  eapply fold_EvtInv_part2;eauto.
  trycancel_EvtInv.
  sep pauto.
  eapply backward_rule1.
  introv Hsat.  
  eapply fold_EvtInv_frm. sep cancel EvtInv_part1. sep cancel EvtInv_part2 . sep pauto.

  (* EXIT_CRITICAL *)
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel EvtInv.
  sep pauto.

  eauto.
  go.

  (* return OS_ERR_EVENT_TYPE *) 
  hoare forward.
  
  (* the concrete type is OS_EVENT_TYPE_SEM *)
  apply semacc_int_eq_true in Hif_false. 
  subst.
  hoare_assert_pure (exists wls, v'31 = DSem i3 /\ absmq = (abssem i3, wls)).  
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply semacc_triangle_sem in Hsat; eauto.
    2: { go. }
    sep split in Hsat.
    auto.
  }
  hoare_split_pure_all.
  destruct H4 as (Hdsem & Habssem). 
  match type of Habssem with
    _ = (?e, ?w) =>
    assert (Hsem: get els (v'38, Int.zero) = Some (e, w)) 
  end.
  {
    eapply join_get_r; eauto.
    eapply join_get_l; eauto.
    rewrite get_a_sig_a; eauto. subst. auto.
  }

  subst.
  
(*******************************  type = sem ********************************)
  lzh_simpl_int_eq. 
  hoare_unfold. 
  
  assert (Fget: exists p st msg sus, TcbMod.get v'11 ct = Some (p, st, msg, sus)). 
  {
    clear -H3.
    unfold RH_CurTCB in H3. 
    auto.
  }
  destruct Fget as (cur_p & cur_st & cur_msg & cur_sus & H4).
  assert (Hcur_p: cur_p = $ OS_IDLE_PRIO \/ cur_p <> $ OS_IDLE_PRIO) by tauto.
  destruct Hcur_p as [Hcur_p | Hcur_p].

(*****************************  Curtid == OS_IDLE_PRIO *********************)
  subst cur_p.
  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid). 

  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_from_idle_abt';
    try can_change_aop_solver; try eauto.
  unfold CurTid. go.   eapply absinfer_eq.
  eapply absabort_rule.
(******************** Curtid == idle finished *********************)
(******************** Curtid <> idle begin: ***********************)

(******************** OSTCBCur is not rdy : a weird situation !*************************)
  assert (Hcur_st: ~(cur_st = rdy /\ cur_sus = false) \/ (cur_st = rdy /\ cur_sus = false)) by tauto.
  destruct Hcur_st as [Hcur_st | Hcur_st].
  
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid). 

  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_not_ready_abt';
    try can_change_aop_solver; try eauto.
  unfold CurTid. go. eapply absinfer_eq.
  eapply absabort_rule.

(********* OSTCBCur is not rdy finished ****************)
  destruct Hcur_st as (Hcur_st & Hcur_sus).
  subst cur_sus.
  subst cur_st.

(****************** cnt > 0, succ return ******************)
  hoare_unfold. 
  lzh_hoare_if2. 

  hoare forward.
  (* pure_auto. *)
  struct_type_match_solver.

(*   eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (evaux_node, llsegevaux v'46). 
  eapply llsegevaux_merge_hd in Hsat; eauto. 
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (llsegevaux v'3, llsegevaux (Vptr ct)). 
  eapply llsegevaux_merge2_frm with (locmp:=set locmp ct (V$ __EvLoc_normal)); eauto.
  rewrite get_set_same; eauto. *)

  assert (Het: etype = Vint32 (Int.repr OS_NO_ERR) 
                  \/ etype <> Vint32 (Int.repr OS_NO_ERR)) by tauto.
  destruct Het. 
  subst.
   (* etype = OS_NO_ERR  *)
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).  
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_inst_get_return'; pure_auto.
  unfold CurTid. go. eapply absinfer_eq.

  (******* fold AECBList  *****)
  transform_pre semacc_new_fundation ltac:(sep cancel AEventData).
  hoare_split_pure_all.
  fold_AEventNode_r.
  compose_evsllseg.
  assert (Hjo_: EcbMod.join (sig (v'38, Int.zero) (abssem i3, v'10)) mqls' els2).
  { join auto. }
  lets Hnewjoin: ecb_get_set_join_join Hsem Hjo_ Hjo. 
  mytac.

  assert (
      ECBList_P v'0 Vnull
                (v'13 ++
                     ((V$ OS_EVENT_TYPE_SEM
                        :: Vint32 i1 :: Vint32 (i3 -ᵢ $ 1) :: x0 :: x1 :: v'' :: Vint32 i0 :: x4 :: nil, etbl,petbl) :: nil) ++
                     v'18)
                (v'29 ++ (DSem (i3-ᵢ$ 1) :: nil) ++ v'30)
                (EcbMod.set els (v'38, Int.zero) (abssem (i3 -ᵢ Int.one), v'10)) 
                v'11).
  {
    eapply semacc_compose_EcbList_P; eauto.
  }
  clear H_elp. 
  fold_AECBList.
  hoare forward prim.
  
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
(*   instantiate(2:= (EcbMod.set els (v'37, Int.zero) (abssem (i3 -ᵢ Int.one), v'4))). *)
  unfold EvtInv.
  sep pauto.
  unfold ASemEIBs in *.
  trycancel_EvtInv.
  sep normal in H36.
  sep destruct H36.
  sep normal.
  sep eexists.
  sep cancel ASeminfo.
  sep cancel ASemCap.
  sep pauto.

  eapply AMuxEIBs_sem_minus_one_preserve; eauto.
  sep cancel AMuxEIBs.
  eapply AMqEIBs_sem_minus_one_preserve; eauto.
  sep cancel AMqEIBs.
  cancel_corecommuinv. 
  
   (* PartitionInv *)
   Require Import sem_partition.
   cancel_partitioninv.
   eauto.
  (* end of PartitionInv *)

  eapply RH_SEM_EINFO_ECB_P_set_minus_one;eauto.
(*   eauto. *)
  eapply mq_ecb_p_sem_minus_one_preserve; eauto.
  eapply mux_ecb_p_sem_minus_one_preserve; eauto. 
  eapply sem_ecb_p_sem_minus_one_preserve; eauto.
(*   splits; eauto. *)
  eapply semacc_RH_TCBList_ECBList_P_hold; eauto.
  pure_auto.
  (* RETURN ′ OS_NO_ERR *) 
  hoare forward.
  simpl. introv Hf. inverts Hf.

   (* etype <> OS_NO_ERR  *)
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).  
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_inst_get_return_abt';
    try can_change_aop_solver; try eauto.
  unfold CurTid. go. eapply absinfer_eq. 
  eapply absabort_rule.

  (* eapply backward_rule1. 
  introv Hsat.
  sep_lifts_trms_in Hsat (evaux_node, llsegevaux v'46).   
  eapply llsegevaux_merge_hd in Hsat; eauto. 
  eapply backward_rule1. 
  introv Hsat.
  sep_lifts_trms_in Hsat (llsegevaux v'3, llsegevaux (Vptr ct)). 
  eapply llsegevaux_merge2_frm; eauto. *)

  (********************** cnt > 0 finished ***************************)
  (* eapply sempend_part1; eauto.  *)
  
  unfold AOSTCBList.
  hoare_split_pure_all.
  destruct H15; subst.
  hoare_assert_pure (get_last_tcb_ptr v'5 v'3 = Some (Vptr ct)). 
  {
    get_hsat Hsat. 
    sep normal in Hsat.  sep destruct Hsat.
    sep_lifts_trms_in Hsat (tcbdllseg v'3).
    eapply tcbdllseg_get_last_tcb_ptr; eauto.
  }
  hoare_split_pure_all. rename H35 into Hlast.
  hoare unfold.

  assert (Fget: exists st sus, TcbMod.get v'35 (v'39, Int.zero) = Some (i7, st, x9, sus)).
  {
    lets Ftmp: TCBListP_head_in_tcb H34; eauto. 
  }
  destruct Fget as (st & sus & Fget).
  lets Fget': TcbMod.join_get_r H32 Fget. 
  rewrite Fget' in H4. inverts H4.
  assert (Hveq: x10 = Vnull /\ i8 = $ OS_STAT_RDY).
  {
    lets Hget_r: get_tcb_stat_rdy H34 Fget. 
    unfold V_OSTCBStat,V_OSTCBEventPtr in Hget_r.
    simpl in Hget_r.
    clear -Hget_r.
    destruct Hget_r; pauto.
  }
  destruct Hveq as (Hvptr & Hvst).
  subst x10. subst i8.

  hoare forward.
  struct_type_match_solver.

  assert (Hor: Int.or ($ OS_STAT_RDY) ($ OS_STAT_SEM) = ($ OS_STAT_SEM)). 
  {
    change ($ OS_STAT_RDY) with (Int.zero).
    rewrite Int.or_commut.
    apply Int.or_zero.
  }
  rewrite Hor.
  hoare forward.
  clear -H1.
  pauto.

  hoare_lifts_trms_pre (Aisr, Ais, A_isr_is_prop,aemp_isr_is).  
  transform_pre a_isr_is_prop_split ltac:(idtac).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  hoare_split_pure_all.
  hoare_unfold.
  hoare forward.

  sep cancel p_local.
  unfold node.
  sep pauto.
  sep cancel Astruct.
  instantiate  (2:=DSem i3).
  unfold AEventNode.
  sep cancel AEventData.
  unfold AOSEvent.
  unfold node.
  sep cancel AOSRdyTblGrp.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Aarray.
  sep cancel AOSPostEventTbl.
  sep cancel Astruct.
  eauto.

  eauto.
  auto.
  eauto.
  eauto.
  unfolds; simpl ; eauto.
  eauto.
  eauto. 
  
  split; auto.
  struct_type_match_solver.
  split; auto.
  struct_type_match_solver.

  split; simpl ; eauto.
  eexists. split. unfolds; simpl ; eauto.
  apply Int.eq_false; eauto.

  eapply tcblist_p_node_rl_sem; eauto.
  pure_auto.

  intros.
  sep auto.
  intros.
  sep auto.

  hoare_ex_intro.
  unfold OS_EventTaskWaitPost.
  unfold OS_EventTaskWaitPost'.
  unfold getasrt.

  hoare_split_pure_all.
  lzh_inverts_logic.
  inverts H35.
  unfold V_OSTCBY,V_OSTCBBitX,V_OSTCBBitY,V_OSEventGrp in H36.
  simpl in H36.
  mytac_H.
  inverts H35.
  inverts H36.
  inverts H37.
  inverts H54.
 
(******************  function call finished **************)
  assert (Hcnt:i3 = $ 0).
  {
    apply semacc_ltu_zero_false.
    auto.
  }
  subst i3.

  assert (Heg: EcbMod.get els (v'38,Int.zero) = Some (abssem Int.zero, v'10)). 
  {
    eapply EcbMod.join_get_r; eauto.
    eapply EcbMod.join_sig_get; eauto.
    clear -Hjo'. unfold TcbJoin in Hjo'. join auto. 
  }

  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).  
  eapply abscsq_rule.
  auto.
  eapply absinfer_sem_pend_block'; eauto. can_change_aop_solver. 
  eapply absinfer_eq.

  unfold AOSTCBPrioTbl.
  hoare_split_pure_all.
  lets cp : H34.
  destruct cp as (td & vv & tcblss & asbs & Hveq & Hnes & Htcj & Htp & Htlis).
  destruct asbs.
  destruct p.
  destruct p.
  destruct Htp as (_ & _ & Hrsl & _).

  funfold Hrsl. 
  assert (0<= Int.unsigned x < 64).
  {
    clear -H58 H66.
    lia.
  }
  assert (prio_neq_cur v'11 (v'39, Int.zero) x).
  {
    eapply R_PrioTbl_P_impl_prio_neq_cur; eauto.
  }
  inverts Hveq.

  (* ** ac: SearchAbout (A_isr_is_prop). *)
  hoare_lifts_trms_pre (Aisr, Ais,Aier).
  transform_pre add_a_isr_is_prop ltac:(idtac).
  transform_pre add_aemp_isr_is_prop ltac:(idtac). sep cancel Aisr. sep cancel Ais. sep cancel Aier. sep pauto.
  simpl update_nth_val.

  assert (Htcblsp0: 
      TCBList_P v'3
                    (v'5++(vv :: v'19 :: Vnull :: cur_msg :: Vint32 i9 :: V$ OS_STAT_RDY :: Vint32 x :: 
                              Vint32 (x&ᵢ$ 7) :: Vint32 (x >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(x&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(x >>ᵢ $ 3)) :: nil)
                        :: v'7) v'41 v'11).
  {
    eapply TCBList_P_Combine; eauto. 
  }

  hoare forward prim.
  sep cancel p_local.
  unfold AOSTCBList.
  unfold tcbdllseg.
  unfold dllseg at 2.
  fold dllseg.
  sep pauto.
  repeat (sep cancel dllseg).
  sep cancel node.
  (* AOSPrioTbl *)
  unfold AOSTCBPrioTbl.
  sep pauto.

  (** tcbdllflag **)
  (* ** ac: Check tcbdllflag_hold. *)
  (* ** ac: Check tcbdllflag_hold_middle. *)
  
  (* AECBList *)
  unfold AECBList.
  sep cancel Aier.

(*   Local Open Scope code_scope. *)
  sep cancel OSPlaceHolder.
  sep cancel vhold_addr.
  unfold EvtInv.
  unfold AECBList.
  sep pauto.
  eapply evsllseg_compose; eauto.
  2: {
    sep cancel AEventNode.
    sep cancel evsllseg.
    sep cancel evsllseg.
    sep cancel APthreadAttr.
  sep cancel CapabilityInv.
    trycancel_EvtInv.

    get_hsat Hsat.
    sep_lifts_trms_in Hsat tcbdllflag.
    sep_lifts_trms tcbdllflag.
    eapply tcbdllflag_hold; [idtac | sep cancel tcbdllflag]. 
    eapply tcbdllflag_hold_middle.
    simpl; auto.
    apply astar_r_aemp_elim.
    
    sep_lifts_trms_in Hsat tcbllsegevaux.
    sep_lifts_trms tcbllsegevaux.
    eapply tcbllsegevaux_tcbvl_tcb_linked_list_same_next_preserve; eauto.
    sep cancel tcbllsegevaux.
    2:eapply tcb_linked_list_same_next_mid; eauto.
    unfold ASemEIBs in *.

    sep normal in Hsat.
    sep destruct Hsat.
    sep normal.
    sep eexists.
    sep cancel ASeminfo.
    sep cancel ASemCap.
  
    sep pauto.
    cancel_corecommuinv.
    cancel_partitioninv.

    sep_lifts_trms_in Hsat (AMuxEIBs,AMqEIBs).
    eapply AMuxEIBs_sem_set_wls'_preserve; eauto.  
    sep cancel AMuxEIBs.
    eapply AMqEIBs_sem_set_wls'_preserve; eauto.
    eapply RH_SEM_EINFO_ECB_P_set_wls';eauto.

  }
  go.

  (** sep assertions end here ~ **)
  eapply mq_ecb_p_sem_set_wls'_preserve; eauto.
  eapply mux_ecb_p_sem_set_wls'_preserve; eauto.
  eapply sem_ecb_p_sem_set_wls'_preserve; eauto.
  
  rewrite list_prop1.
  rewrite list_prop1.

  eapply ecblist_p_compose.

  eapply EcbMod.join_set_r.
  eauto.
  eexists.
  eapply EcbMod.join_get_l.
  unfold TcbJoin in Hjo'. 
  eauto.
  apply EcbMod.get_a_sig_a.
  eapply CltEnvMod.beq_refl.

  (**** ecblist_P ****)
  Focus 2.

  unfold ECBList_P; fold ECBList_P.
  eexists; split.
  eauto.
  splits.
  Focus 3.
  do 3 eexists; splits.
  unfolds; simpl; auto.

  unfold TcbJoin.
  unfold join.
  simpl.
  unfold sig; simpl.
  erewrite <- EcbMod.set_sig.
  eapply EcbMod.join_set_l.
  unfold TcbJoin in Hjo'.
  eauto.
  unfold EcbMod.indom; eexists.
  apply EcbMod.get_a_sig_a.
  auto with brel.
  unfold RLH_ECBData_P.
  splits; auto.
  unfolds; split; intros; auto.
  tryfalse.
  eapply  ECBList_P_high_tcb_block_hold_sem; eauto.

  eapply ejoin_get_none_r. 
  2: eauto. 
  apply EcbMod.get_a_sig_a.
  auto with brel.
  unfold TcbJoin in Hjo'. eauto.
  eapply sempend_pure.R_ECB_ETbl_P_high_tcb_block_hold; eauto.
  (* new add about petbl *)
  eapply R_ECB_PETbl_P_high_tcb_block_hold';eauto.
  clear. unfold V_OSEventType; simpl; pure_auto.
  introv Hf. destruct Hf as (qd & qwt & Hf). inverts Hf.
  (* end of new add *)

  (* ** ac: Check ECBList_P_high_tcb_block_hold_sem. *)
  eapply  ECBList_P_high_tcb_block_hold_sem; eauto.


  eapply ejoin_get_none_l. 
  2:eauto.
  unfold TcbJoin in Hjo'.
  eapply EcbMod.join_get_l; eauto.  
  apply EcbMod.get_a_sig_a.
  auto with brel.
  (** ECBList_P ends here ~ **)

  auto.
  eapply Mbox_common.TcbMod_set_R_PrioTbl_P_hold ; eauto. 
  (* ** ac: Check rtbl_remove_RL_RTbl_PrioTbl_P_hold. *)
  eapply OSTimeDlyPure.rtbl_remove_RL_RTbl_PrioTbl_P_hold; eauto.
  instantiate (1:= (TcbMod.set v'35 (v'39, Int.zero)
     (x, wait (os_stat_sem (v'38, Int.zero)) (if Int.eq i Int.zero then None else Some i), cur_msg, false))).
  destruct (Int.eq i Int.zero) eqn:eq1.

  eapply sempend_pure.TCBList_P_tcb_block_hold_none; eauto.
  eapply TcbMod_join_impl_prio_neq_cur_r; eauto.
  eapply sem_lab.semacc_int_eq_true in eq1. auto.
  
  eapply sempend_pure.TCBList_P_tcb_block_hold; eauto.
  eapply TcbMod_join_impl_prio_neq_cur_r; eauto.
  eapply sem_lab.semacc_int_eq_false in eq1. auto.

  clear Fget'.
  eapply Mbox_common.TCBList_P_tcb_block_hold' with (prio := x); eauto.

  eapply TcbMod_join_impl_prio_neq_cur_r; eauto.
  eapply TcbMod.join_comm; eauto.
  unfold join; simpl.
  eapply TcbMod.join_set_r; eauto.
  unfolds; eexists; eauto.

  unfold V_OSTCBPrev; simpl nth_val; auto.
  unfold V_OSTCBNext; simpl nth_val; auto.

  eapply  RH_CurTCB_high_block_hold_sem; eauto. 

  eapply RH_TCBList_ECBList_P_high_block_hold_sem; eauto.

  pure_auto.
(******************** ex_critical finished ***********************)

(* schedule *) 
  hoare forward.
  unfolds; auto.
  pure_auto.

  introv Hsat. 
  sep destruct Hsat. 
  sep eexists.
  sep cancel p_local.
  sep auto.
  introv Hsat. 
  sep destruct Hsat. 
  sep eexists.
  sep cancel p_local.
  sep auto.

  (* ** ac: Print OS_SchedPost. *)
  unfold OS_SchedPost.
  unfold OS_SchedPost'.
  unfold getasrt.
  hoare_split_pure_all.
  lzh_inverts_logic.
  
  (* enter critical *)
  hoare forward prim.
  hoare normal pre.
  hoare_ex_intro.

  rename v'64 into vcspace1.
  rename v'65 into v65. 
  rename v'66 into v66. 
  rename v'67 into v67. 

  clear Hlast.
  hoare_assert_pure (get_last_tcb_ptr v'44 v'37 = Some (Vptr (v'39, Int.zero))).  
  {
    get_hsat Hsat.
    unfold AOSTCBList in Hsat. 
    sep normal in Hsat. sep destruct Hsat.
    sep split in Hsat. simpljoin1.
    sep_lifts_trms_in Hsat (tcbdllseg v'37).
    eapply tcbdllseg_get_last_tcb_ptr; eauto. 
  }
  hoare_split_pure_all. rename H53 into Hlast.  

  hoare_unfold.
  clear H34 Htcblsp0 Fget Fget'. 
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  hoare_split_pure_all.
  mytac.

(* new add about the absstract stat after sched *)
  assert (Fget: exists st sus, TcbMod.get v'67 (v'39,Int.zero) = Some (i5, st, x10, sus)). 
  {
    eapply TCBListP_head_in_tcb'; try eauto.
  }
  destruct Fget as (st & sus & Fget).
  lets Fget': TcbMod.join_get_r H61 Fget.  
  assert (Hst_cond:
            (st = rdy /\ sus = false \/ st = wait (os_stat_sem (v'38, Int.zero)) (Some Int.zero) /\ sus = false)
            \/ ~(st = rdy /\ sus = false \/ st = wait (os_stat_sem (v'38, Int.zero)) (Some Int.zero) /\ sus = false)) by tauto.  
  destruct Hst_cond.
  Focus 2.
  unfold EvtInv.
  hoare unfold.
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid). 
   
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_p_aftersch_abt'; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule.
  (* (st = rdy \/ (st = wait (os_stat_sem (v'30, Int.zero)) Int.zero)) *)
  
  unfold EvtInv.
  hoare unfold.
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid). 
   
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_p_aftersch'; try eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  assert (Hvst: 
            (i6 = ($ OS_STAT_SEM)
            /\ x11 = Vptr (v'38, Int.zero) /\  i7 = Int.zero /\  prio_in_tbl i5 v'49)
            \/ (i6 = ($ OS_STAT_RDY) /\ x11 = Vnull)). 
  {
    lets Hget_r: get_tcb_stat_rdy_sus H64 Fget.
    destruct sus eqn: eq1; destruct H81 as [(Hc1 & Heq) | (Hc3 & Heq)]; tryfalse;
    lets Hget_s: get_tcb_stat_sem_zero H64 Fget;
    unfold V_OSTCBStat,V_OSTCBEventPtr,V_OSTCBDly in Hget_r,Hget_s;
    simpl in Hget_r,Hget_s.
    right.
    destruct Hget_r; try pauto.
    left.
    eapply Hget_s in Hc3; eauto.
    destruct Hc3 as (Heq1 & Heq2 & Heq3 & Hnin);
    inverts Heq1; inverts Heq2; inverts Heq3; auto.
  }

  lzh_hoare_if2.
  (*OS_TCBCurStat <> OS_STAT_SEM*)
  Focus 2.
  hoare forward.
  destruct Hvst as [(Hvi & Hvptr & Hvdly & Hnp) | (Hvi & Hvptr)];
  substs.
  clear - H83.
  rewrite Int.and_idem in *. unfold OS_STAT_SEM in *.
  destruct H83 ; pure_auto; tryfalse. 

  assert (Hsus: sus = false).
  { clear -H64 Fget.
     funfold H64.
     inverts H.
     eapply TcbMod.join_sig_get in H1.
     rewrite H1 in Fget; inverts Fget.
     funfold H2.
     eapply oscore_common.tcb_stat_imp_sus_false with (stat:= $ OS_STAT_RDY); eauto.
  }
  subst sus.

  assert (Fget_st: ~(exists sid wt, st= wait (os_stat_sem sid) wt)).
  {
    eapply low_stat_impl_high_stat_neq_sem';
    unfold V_OSTCBStat, V_OSTCBPrio,V_OSTCBMsg; try eauto; try (simpl; auto).
  }

  assert (Het: etype = Vint32 (Int.repr OS_NO_ERR)
                  \/ etype <> Vint32 (Int.repr OS_NO_ERR)) by tauto.
  destruct Het.
  subst.
   (* etype = OS_NO_ERR  *)
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid). 
   
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_to_succ'; try eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  fold V_OSTCBPrev.
  fold V_OSTCBNext.
  
  eapply backward_rule1.
  introv Hsat.  
  eapply fold_EvtInv_part1;eauto.
  trycancel_EvtInv1.
  pauto.
  eapply backward_rule1.
  introv Hsat.  
  eapply fold_EvtInv_part2;eauto.
  trycancel_EvtInv2.
  sep pauto.
  
  eapply backward_rule1.
  introv Hsat.  
  eapply fold_EvtInv_frm.
  sep cancel EvtInv_part1. sep cancel EvtInv_part2 . sep pauto.

  hoare forward prim.
  sep cancel Aier.
  sep cancel EvtInv.
  unfold AOSRdyTblGrp. 
  unfold AOSRdyTbl. 
  unfold AOSTCBList.
  unfold tcbdllseg. 
  sep pauto.
  sep cancel AOSRdyGrp.
  sep cancel (dllseg v'37). 
  unfold dllseg.
  fold dllseg.
  unfold node.
  sep pauto.
  sep cancel Astruct. 
  sep cancel dllseg.
  sep cancel p_local.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  exact_s.

  simpl; auto.
  splits; try eauto.
  go.
  split; eauto.
  eauto.
  eauto.
  eauto.
  pure_auto.
  pure_auto.
 
  hoare forward.
  introv Hf. simpl in Hf. inverts Hf. 
  (* etype <> OS_NO_ERR  *) 
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).
   
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_to_succ_abt'; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule.

  (*OS_TCBCurStat = OS_STAT_SEM*)
  destruct Hvst as [(Hvi & Hvptr  & Hvdly & Hnp) | (Hvi & Hvptr)]; 
  substs.
  Focus 2.
  clear - H83.
  change ($ OS_STAT_RDY) with Int.zero in *.
  rewrite Int.and_zero_l in H83.
  destruct H83. tryfalse.

  assert (Hst_eq: st = wait (os_stat_sem (v'38, Int.zero)) (Some Int.zero)).  
  {
    eapply low_stat_impl_high_stat_sem_zero_some'; try eauto.
    eapply Int.eq_true.
  }
  assert (Hsus: sus = false).
  { destruct H81 as [(Heq & _) | (Heq & Heq1)]; subst; inverts Hst_eq.
     auto.
  }
  subst sus.

  unfold AECBList.
  hoare unfold.
  assert (Hprange: 0<= Int.unsigned i5 < 64). 
  {
    lets cp: H64.
    destruct cp as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
    destruct asbs'.
    destruct p0.
    destruct p0.
    destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').

    funfold Hrsl'.
    pure_auto.
  }
  hoare_assert_pure (isptr v'37).
  { get_hsat Hsat.
     sep_lifts_trms_in Hsat (dllseg v'37).
     lets Hisp: oscore_common.dllseg_head_isptr' Hsat. auto.
  }
  eapply pure_split_rule'; introv Hptr.
  destruct Hptr as [Hnull | (tcb_head & Heq)];
  subst v'37. tryfalse.
  assert (Fget_ectr: exists et etbl petbl, get_ectr (Vptr (v'38, Int.zero)) v'55 v'69 = Some (et, etbl, petbl)). 
  {
    eapply tcb_eptr_get_ectr'; try eauto.
  }
  destruct Fget_ectr as (et & etbl & petbl & Fget_ectr).
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (evsllseg v'55).
  lets Hnew: get_ectr_decompose Hsat Fget_ectr.
  clear Hsat.
  exact_s.

  hoare unfold.
  (*start OS_EventTO*)
  hoare_lifts_trms_pre (Aisr, Ais, A_isr_is_prop,aemp_isr_is).  
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  
  hoare forward.

  unfold  node.
  sep pauto.
  sep cancel Astruct.
  sep cancel AEventNode.
  sep cancel p_local.

  exact_s.

  split; auto.
  go.
  simpl; auto.
  eapply TCBList_P_RL_TCBblk_P with (l:= nil).
  rewrite nil_simp.
  eauto.
  pure_auto.


  intros.
  sep auto.
  intros.
  sep auto.

  unfold OS_EventTOPost.
  unfold OS_EventTOPost'.
  unfold getasrt.
  hoare_split_pure_all.
  (*end of OS_EventTO*)
  lzh_inverts_logic.
  mytac.
  inverts H97.
  rename v'96 into vy. rename v'97 into vbitx. rename v'98 into vbity. 
  inverts H96; inverts H104; inverts H105.

  assert (Heg': exists n wls,
             EcbMod.get v'52 (v'38, Int.zero) = Some (abssem n, wls) /\ In (v'39, Int.zero) wls). 
  {
    clear -H54 Fget'. 
    funfold H54.  
    funfold H0.
    eapply H4; try eauto.
  }
  destruct Heg' as (n & wls & Heg' & Hinwl).

  hoare_lifts_trms_pre (Aisr, Ais,Aier). 
  transform_pre add_aemp_isr_is_prop ltac:(idtac). 

  assert (Het: etype = Vint32 (Int.repr OS_TIMEOUT)
                  \/ etype <> Vint32 (Int.repr OS_TIMEOUT)) by tauto.
  destruct Het.
  subst.
   (* etype = OS_TIMEOUT  *)
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid). 
  eapply abscsq_rule.
  apply noabs_oslinv.

  eapply absinfer_sem_pend_to_timeout_rdy'; try eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  fold V_OSTCBPrev.
  fold V_OSTCBNext.
  fold_AEventNode_r.
  unfold node.
  unfold AOSTCBPrioTbl.
  hoare_unfold.
(*   simpl update_nth_val. *)
  
  hoare forward prim.

  unfold AECBList.
  sep pauto. 
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  instantiate (3:=(v'68 :: v'64 :: Vnull :: x10 :: Vint32 Int.zero :: V$ OS_STAT_RDY
                        :: Vint32 i5 :: Vint32 i4 :: Vint32 vy :: Vint32 vbitx :: Vint32 vbity :: nil)).
  unfold EvtInv.
  sep pauto.
  sep_lifts_trms evsllseg.
  sep cancel AOSEventFreeList.
  unfold AECBList.
  sep pauto.
  eapply evsllseg_compose.
  4: {
    sep cancel AEventNode.
    sep cancel (evsllseg v'55).
    sep cancel evsllseg.
    unfold AOSRdyTblGrp.
    unfold AOSRdyTbl.
    unfold AOSTCBList.
    unfold tcbdllseg.
    sep pauto.
    sep cancel AOSRdyGrp.
    sep cancel (dllseg (Vptr tcb_head)).
    unfold dllseg.
    fold dllseg.
    unfold node.
    unfold AOSTCBPrioTbl.
    sep pauto.
    sep cancel dllseg.

    sep cancel Astruct.
    sep cancel AOSQFreeList.
    sep cancel AOSQFreeBlk.

    sep_lifts_trms tcbdllflag.
    eapply tcbdllflag_hold; [idtac | sep cancel tcbdllflag].
    eapply tcbdllflag_hold_middle.
    simpl; auto.
    unfold ASemEIBs in *; sep pauto.
    sep cancel ASeminfo.
    sep cancel ASemCap.

    eapply AMuxEIBs_sem_set_wls'_preserve; eauto.  
    sep cancel AMuxEIBs.
    eapply AMqEIBs_sem_set_wls'_preserve; eauto.
    sep cancel AMqEIBs.

    eapply tcbllsegevaux_tcbvl_tcb_linked_list_same_next_preserve; eauto. 
    sep cancel tcbllsegevaux.
    cancel_corecommuinv. 
    cancel_partitioninv.
    eauto.

    eapply tcb_linked_list_same_next_mid; eauto. 
    eapply TCBList_P_Combine; eauto.
    
    eapply RH_SEM_EINFO_ECB_P_set_wls';eauto.
    auto. 
    auto.   
    auto. (* new add *)
    eapply r_priotbl_p_set_hold; try eauto.
(*     eauto. *)

    unfold V_OSTCBNext; simpl; auto.
    split; auto.
    (* first TCBList_P *) 
    assert (Hyx_eq: vy = i5 >>ᵢ $ 3 /\ vbitx = $ 1<<ᵢ(i5&ᵢ$ 7)).
    {
      lets cp : H64.
      destruct H64 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
      destruct asbs'.
      destruct p0.
      destruct p0.
      destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
      funfold Hrsl'.
      split; auto.
    }
    destruct Hyx_eq as (Hy_eq & Hbx_eq).
    subst vy. subst vbitx.
    asserts_rewrite (
        (v'68 :: v'64 :: Vnull :: x10 :: Vint32 Int.zero :: V$ OS_STAT_RDY
              :: Vint32 i5 :: Vint32 i4 :: Vint32 (i5 >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(i5&ᵢ$ 7)) :: Vint32 vbity :: nil) =
        update_nth_val 5 (
                         update_nth_val 2
                                        (v'68 :: v'64 :: Vptr (v'38, Int.zero) :: x10 :: Vint32 Int.zero ::
                                           Vint32 ($ OS_STAT_SEM)
                                              :: Vint32 i5 :: Vint32 i4 :: Vint32 (i5 >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(i5&ᵢ$ 7)) :: Vint32 vbity :: nil)
                                        Vnull) (V$ OS_STAT_RDY)).  
    { simpl. auto. }
    eapply TCBList_P_hold_for_update_rdy''. eauto. eauto. eauto. eauto.
    eapply Fget . eapply H105.  eauto. eauto. eauto. eauto. eauto.
    (* join ... *)
    destruct H64 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
    inverts Hveq'.
    unfold TcbJoin in Htcj'.
    unfold TcbMod.joinsig.
    unfold join,sig,TcbMap in Htcj'.
    eapply TcbMod.joinsig_set_set; try eauto.
  }
  unfold V_OSEventListPtr.
  eapply nth_upd_neqrev; try pauto.
  eauto. 
  eauto. 

  (* ECBList_P *) 
  assert (Hyx_eq: vy = i5 >>ᵢ $ 3 /\ vbitx = $ 1<<ᵢ(i5&ᵢ$ 7)).
  {
    lets cp : H64.
    destruct H64 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
    destruct asbs'.
    destruct p0.
    destruct p0.
    destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
    funfold Hrsl'.
    split; auto.
  }
  destruct Hyx_eq as (Hy_eq & Hbx_eq).
  subst vy. subst vbitx.
  eapply ECBList_P_hold_for_update_sem_to_rdy; try eauto.
  get_hsat Hsat. 
  sep_lifts_trms_in Hsat evsllseg.  
  eapply evsllseg_list_len_eq; try eauto. 
  
  eapply mq_ecb_p_sem_set_wls'_preserve; eauto.
  eapply mux_ecb_p_sem_set_wls'_preserve; eauto.
  eapply sem_ecb_p_sem_set_wls'_preserve; eauto.       
  
  (* end of ECBList_P *)
  unfold RH_CurTCB.
  rewrite TcbMod.map_get_set.
  eauto.
  (* RH_TCBList_ECBList_P *)
  eapply RH_TCBList_ECBList_P_hold_for_sem_to_rdy; try eauto.
  pure_auto.

  (*RETURN ′ OS_TIMEOUT*)
  hoare forward.

  (* etype <> OS_TIMEOUT  *)
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid). 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_to_timeout_rdy_abt'; try eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule.
  Unshelve. trivial. trivial.

Qed.


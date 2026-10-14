Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import os_ucos_h.

Require Import include_frm. 
Require Import abs_infer_step.
Require Import ucos_frmaop.
Require Import seplog_lemmas.
Require Import seplog_tactics.
Require Import abs_infer_abt.

Require Import seplog_trm_tacs.
Require Import evaux_pure.
Require Import evauxvar_lemmas.
Require Import err_list_common.
Require Import sem_lab.
Require Import OSTimeTickPure.
Require Import OSETWaitPure.
Require Import oscore_common.
Require Import sempend_pure_ext.
Require Import Mbox_common.
Require Import gjb_q_common.
Require Import sem_common.
Require Import gjb_common.
Require Import freeevtlist_lemmas.
Require Import tcblist_setnode_lemmas.
Require Import OS_EventTaskPostRdy_pure.
Require Import OSQPostPure.
Require Import OSQPendPure.
Require Import OSQPendPure_ext.
Require Import OSQDelPure.
Require Import sem_corecommu.
Require Import os_code_defs.

Require Import evtinv_lemmas.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

(*********************** q pend **************************************)

Lemma qpend_absimp_set_errv_abt:
  forall errid verr rv ebls P sch s,
    get ebls errid = None ->
    can_change_aop P ->
    absinfer sch (<|| qpend_set_errv (|Vptr errid :: Vint32 verr :: rv :: nil|) ;; s ||> ** Hebls ebls ** P) 
               (<||ABORT||> ** Hebls ebls ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (Hebls ebls ** P)) by pure_auto.
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
Qed.

Lemma qpend_absimp_set_errv:
  forall errid verr rv ebls P sch s v,
    get ebls errid = Some v ->
    can_change_aop P ->
    absinfer sch (<|| qpend_set_errv (|Vptr errid :: Vint32 verr :: rv :: nil|) ;; s ||> ** Hebls ebls ** P) 
               (<|| s ||> ** Hebls (set ebls errid verr) ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma qpend_absimp_iserr:
  forall P sch s vp rv vt errid,
    can_change_aop P ->
    rv = Vnull -> 
    absinfer sch
             ( <|| spec_code_cons (qpendnew (vp :: vt :: Vptr errid :: rv :: nil)) s ||> ** P)
             (<|| qpend_set_errv (|Vptr errid :: V$ OS_ERR_PEND_ISR :: rv :: nil|) ;; s ||> ** P).
Proof.
intros.
substs.
simpl. 
infer_solver 0%nat.
Qed.

Lemma qpend_absimp_iserr_abt:
  forall P sch s vp rv vt errid,
    can_change_aop P ->
    rv <> Vnull -> 
    absinfer sch
             ( <|| spec_code_cons (qpendnew (vp :: vt :: Vptr errid :: rv :: nil)) s ||> ** P)
             (<|| ABORT ||> ** P).
Proof.
  intros.
  simpl.
  eapply absinfer_trans; try (eapply absinfer_choice1; auto); eauto.
  eapply absinfer_trans; try (eapply absinfer_seq_abt; auto); eauto.
  eapply absinfer_seq; eauto.
   eapply absinfer_abt; auto.
  absimp_abt_solver.
Qed.

Lemma qpend_absimp_null_return_abt:
  forall vt errid rv P sch s,
    rv <> Vnull -> 
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (qpendnew (Vnull :: vt :: Vptr errid :: rv :: nil)) s ||> ** P) 
      (<|| ABORT ||> ** P ). 
Proof.
  intros.
  simpl.
  eapply absinfer_trans; try( eapply absinfer_choice2; eauto).
  eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma qpend_absimp_null_return:
  forall vt errid rv P sch s,
    rv = Vnull -> 
    can_change_aop P -> 
    absinfer sch
      (<||  spec_code_cons (qpendnew (Vnull :: vt :: Vptr errid :: rv :: nil)) s ||> ** P) 
      (<|| qpend_set_errv (|Vptr errid :: V$ OS_ERR_PEVENT_NULL :: rv :: nil|) ;; s ||> ** P ). 
Proof.
intros.
substs.
simpl. 
infer_solver 1%nat.
Qed.

Lemma qpend_absimp_no_q_abt:
  forall vt errid rv P sch s qls qid,
    (~ exists x y pwl wls, get qls qid = Some (absmsgq x y pwl,wls) ) ->
    rv <> Vnull -> 
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (qpendnew (Vptr qid :: vt :: Vptr errid :: rv :: nil)) s ||> ** HECBList qls ** P) 
      (<|| ABORT ||> ** HECBList qls ** P ). 
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList qls ** P)) by pure_auto.
  simpl.
  do 2 (eapply absinfer_trans; try( eapply absinfer_choice2; eauto)).
  eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma qpend_absimp_no_q:
  forall vt errid rv P sch s qls qid,
    (~ exists x y pwl wls, get qls qid = Some (absmsgq x y pwl,wls) ) ->
    rv = Vnull -> 
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (qpendnew (Vptr qid :: vt :: Vptr errid :: rv :: nil)) s ||> ** HECBList qls ** P) 
      (<|| qpend_set_errv (|Vptr errid :: V$ OS_ERR_EVENT_TYPE :: rv :: nil|) ;; s ||> ** HECBList qls ** P ). 
Proof.
  intros.
  substs.
  simpl.
  infer_solver 2%nat.
Qed.

Lemma qpend_absimp_idle_abt:
  forall vt errid rv P sch s tcbls qid ct st msg sus,
    TcbMod.get tcbls ct = Some (Int.repr OS_IDLE_PRIO, st, msg, sus) ->
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (qpendnew (Vptr qid :: vt :: Vptr errid :: rv :: nil)) s ||> ** HTCBList tcbls ** HCurTCB ct ** P) 
      (<|| ABORT ||> ** HTCBList tcbls ** HCurTCB ct ** P ). 
Proof.
  intros.
  assert (Hc: can_change_aop (HTCBList tcbls ** HCurTCB ct ** P)) by pure_auto.
  simpl.
  do 3 (eapply absinfer_trans; try( eapply absinfer_choice2; eauto)).
  eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
  instantiate (3:= s0).
  sep pauto.
  Unshelve.
  exact isched.
Qed.

Lemma qpend_absimp_stat_err_abt:
  forall vt errid rv P sch s tcbls qid ct st msg p sus,
    TcbMod.get tcbls ct = Some (p, st, msg, sus) ->
    ~ (st = rdy /\ sus = false) ->
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (qpendnew (Vptr qid :: vt :: Vptr errid :: rv :: nil)) s ||> ** HTCBList tcbls ** HCurTCB ct ** P) 
      (<|| ABORT ||> ** HTCBList tcbls ** HCurTCB ct ** P ). 
Proof.
  intros.
  assert (Hc: can_change_aop (HTCBList tcbls ** HCurTCB ct ** P)) by pure_auto.
  simpl.
  do 4 (eapply absinfer_trans; try( eapply absinfer_choice2; eauto)).
  eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
  instantiate (3:= s0).
  sep pauto.
  Unshelve.
  exact isched.
Qed.

Lemma qpend_absimp_no_pwl_succ:
  forall vt errid rv P sch s qid ecbls tcbls ct msg' ml n wl ecbls'
             tcblh tcbvl vhold v1 v2 v3,
    get ecbls qid = Some (absmsgq (msg'::ml) n nil ,wl) ->
    ecbls' = set ecbls qid (absmsgq ml n nil ,wl) ->
    rv = msg' -> 
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (qpendnew (Vptr qid :: vt :: Vptr errid :: rv :: nil)) s ||> **
       HECBList ecbls ** HTCBList tcbls ** HCurTCB ct **
       EvtInv_part2 ecbls tcblh tcbvl vhold v1 v2 v3 ** P) 
      (<|| qpend_set_errv (|Vptr errid :: V$ OS_NO_ERR :: rv :: nil|) ;; s ||> **
      HECBList ecbls' ** HTCBList tcbls ** HCurTCB ct ** 
      EvtInv_part2 ecbls' tcblh tcbvl vhold v1 v2 v3 ** P). 
Proof.
  intros.
  substs.
  simpl.
  infer_solver 5%nat.
  unfold EvtInv_part2 in *.
  unfold ASemEIBs in *.
  unfold AMuxEIBs in *.
  unfold AMqEIBs in *.
  sep pauto.
  eapply mq_ecb_p_mq_set_preserve; eauto.
  eapply mux_ecb_p_mq_set_preserve; eauto.
  eapply sem_ecb_p_mq_set_preserve; eauto.
  eapply RH_SEM_EINFO_ECB_P_mq_set_preserve; eauto.  
  eapply RH_MUX_EIB_ECB_P_mq_set_preserve; eauto.
  eapply RH_EIB_ECB_Q_P_mq_set_preserve; eauto.
Qed.

Lemma qpend_absimp_no_pwl_succ_abt:
  forall vt errid rv P sch s qid ecbls tcbls ct msg' ml n wl ecbls' ,
    get ecbls qid = Some (absmsgq (msg'::ml) n nil ,wl) ->
    ecbls' = set ecbls qid (absmsgq ml n nil ,wl) ->
    rv <> msg' -> 
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (qpendnew (Vptr qid :: vt :: Vptr errid :: rv :: nil)) s ||> **
       HECBList ecbls ** HTCBList tcbls ** HCurTCB ct ** P) 
      (<|| ABORT||> **
      HECBList ecbls ** HTCBList tcbls ** HCurTCB ct ** P ). 
Proof.
  intros.
  substs.
  assert (Hc: can_change_aop (HECBList ecbls ** HTCBList tcbls ** HCurTCB ct ** P)) by pure_auto.
  simpl.
  do 5 (eapply absinfer_trans; try( eapply absinfer_choice2; eauto)).
  eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver';
  instantiate (4:= s0);
  sep pauto.
  Unshelve.
  exact isched.
  exact isched.
Qed.

Lemma qpend_absimp_ex_pwl_before_sched:
  forall vt errid rv P sch s qid ecbls tcbls ct pwl msg' ml n wl ecbls' m2 t' p2 st tcbls'
            tcblh tcbvl vhold v1 v2 v3 sus,
    pwl <> nil ->
    get ecbls qid = Some (absmsgq (msg'::ml) n pwl ,wl) ->
    ecbls' = set ecbls qid (absmsgq (ml++(m2::nil)) n (remove_tid t' pwl) ,wl) ->
    GetHWait tcbls pwl t' ->
    get tcbls t' = Some (p2,st,m2, sus) ->
    tcbls' = set tcbls t' (p2,rdy,m2, sus) ->
    rv = msg' -> 
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (qpendnew (Vptr qid :: vt :: Vptr errid :: rv :: nil)) s ||> **
       HECBList ecbls ** HTCBList tcbls ** HCurTCB ct **
       EvtInv_part2 ecbls tcblh tcbvl vhold v1 v2 v3 ** P) 
      (<|| isched;; qpend_set_errv (|Vptr errid :: V$ OS_NO_ERR :: rv :: nil|) ;; s ||> **
      HECBList ecbls' ** HTCBList tcbls' ** HCurTCB ct **
      EvtInv_part2 ecbls' tcblh tcbvl vhold v1 v2 v3 ** P).
Proof.
  intros.
  substs.
  simpl.
  infer_solver 6%nat.
  unfold EvtInv_part2 in *.
  unfold ASemEIBs in *.
  unfold AMuxEIBs in *.
  unfold AMqEIBs in *.
  sep pauto.
  eapply mq_ecb_p_mq_set_preserve; eauto.
  eapply mux_ecb_p_mq_set_preserve; eauto.
  eapply sem_ecb_p_mq_set_preserve; eauto.
  eapply RH_SEM_EINFO_ECB_P_mq_set_preserve; eauto.  
  eapply RH_MUX_EIB_ECB_P_mq_set_preserve; eauto.
  eapply RH_EIB_ECB_Q_P_mq_set_preserve; eauto.
Qed.

Lemma qpend_absimp_ex_pwl_before_sched_abt:
  forall vt errid rv P sch s qid ecbls tcbls ct pwl msg' ml n wl ecbls' m2 t' p2 st tcbls' sus,
    pwl <> nil ->
    get ecbls qid = Some (absmsgq (msg'::ml) n pwl ,wl) ->
    ecbls' = set ecbls qid (absmsgq (ml++(m2::nil)) n (remove_tid t' pwl) ,wl) ->
    GetHWait tcbls pwl t' ->
    get tcbls t' = Some (p2,st,m2, sus) ->
    tcbls' = set tcbls t' (p2,rdy,m2, sus) ->
    rv <> msg' -> 
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (qpendnew (Vptr qid :: vt :: Vptr errid :: rv :: nil)) s ||> **
       HECBList ecbls ** HTCBList tcbls ** HCurTCB ct ** P) 
      (<|| ABORT||> **
      HECBList ecbls ** HTCBList tcbls ** HCurTCB ct ** P ). 
Proof.
  intros.
  substs.
  assert (Hc: can_change_aop (HECBList ecbls ** HTCBList tcbls ** HCurTCB ct ** P)) by pure_auto.
  simpl.
  do 6 (eapply absinfer_trans; try( eapply absinfer_choice2; eauto)).
  eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver'.
  instantiate (3:= s0).
  sep pauto.
  Unshelve.
  exact isched.
Qed.

Lemma qpend_high_step_block:
  forall vt errid rv P sch s qid ecbls tcbls ct pwl n wl ecbls' m prio tcbls' t
             tcblh tcbvl vhold v1 v2 v3 sus,
    Int.unsigned vt <= 65535 ->
    EcbMod.get ecbls qid = Some (absmsgq nil n pwl, wl) ->
    TcbMod.get tcbls ct = Some (prio, rdy, m, sus)->
    ecbls' = set ecbls qid (absmsgq nil n pwl, ct :: wl) ->
    tcbls' = set tcbls ct (prio, wait (os_stat_q qid) ( if (Int.eq vt Int.zero) then None  else Some vt ), m, sus) ->
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (qpendnew (Vptr qid :: Vint32 vt :: Vptr errid :: rv :: nil)) s ||> **
       HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct **
       EvtInv_part2 ecbls tcblh tcbvl vhold v1 v2 v3 ** P) 
      (<|| isched;; qpend_set_stat (|Vptr qid :: nil|);;
               ( (qpend_to (|Vptr qid :: rv :: nil|);; qpend_set_errv (|Vptr errid :: V$ OS_TIMEOUT :: rv :: nil|) ;; s) ??
                  (qpend_block_get (|Vptr qid :: rv :: nil|);; qpend_set_errv (|Vptr errid :: V$ OS_NO_ERR :: rv :: nil|) ;; s) ) ||> **
      HECBList ecbls' ** HTCBList tcbls' ** HTime t ** HCurTCB ct **
      EvtInv_part2 ecbls' tcblh tcbvl vhold v1 v2 v3 ** P).
Proof.
  intros.
  substs.
  simpl.
  destruct (Int.eq vt Int.zero) eqn:eq1.
  (*v2 = Int.zero *)
  eapply semacc_int_eq_true in eq1. subst.
  infer_solver 7%nat.
  unfold EvtInv_part2 in *.
  unfold ASemEIBs in *.
  unfold AMuxEIBs in *.
  unfold AMqEIBs in *.
  sep pauto.
  eapply mq_ecb_p_mq_set_preserve; eauto.
  eapply mux_ecb_p_mq_set_preserve; eauto.
  eapply sem_ecb_p_mq_set_preserve; eauto.
  eapply RH_SEM_EINFO_ECB_P_mq_set_preserve; eauto.  
  eapply RH_MUX_EIB_ECB_P_mq_set_preserve; eauto.
  eapply RH_EIB_ECB_Q_P_mq_set_preserve; eauto.
  (*v2 <> Int.zero *)
  eapply semacc_int_eq_false in eq1. 
  infer_solver 7%nat.
  unfold EvtInv_part2 in *.
  unfold ASemEIBs in *.
  unfold AMuxEIBs in *.
  unfold AMqEIBs in *.
  sep pauto.
  eapply mq_ecb_p_mq_set_preserve; eauto.
  eapply mux_ecb_p_mq_set_preserve; eauto.
  eapply sem_ecb_p_mq_set_preserve; eauto.
  eapply RH_SEM_EINFO_ECB_P_mq_set_preserve; eauto.  
  eapply RH_MUX_EIB_ECB_P_mq_set_preserve; eauto.
  eapply RH_EIB_ECB_Q_P_mq_set_preserve; eauto.
Qed.

Lemma qpend_absimp_qpend_set_stat:
  forall s sch P tcbls ct p st msg qid sus,
    TcbMod.get tcbls ct = Some (p, st, msg, sus) ->
    (st = rdy /\ msg <> Vnull /\ sus = false \/ st = wait (os_stat_q qid) (Some Int.zero) /\ msg = Vnull /\ sus = false) ->
    can_change_aop P ->
     absinfer sch (<|| qpend_set_stat (|Vptr qid :: nil|) ;; s  ||> ** HTCBList tcbls ** HCurTCB ct ** P)
     (<|| s ||> ** HTCBList tcbls ** HCurTCB ct **  P ). 
Proof.
  infer_solver 0%nat.
Qed.

Lemma qpend_absimp_qpend_set_stat_abt:
  forall s sch P tcbls ct p st msg qid sus,
    TcbMod.get tcbls ct = Some (p, st, msg, sus) ->
    ~(st = rdy /\ msg <> Vnull /\ sus = false \/ st = wait (os_stat_q qid)  (Some Int.zero) /\ msg = Vnull /\ sus = false) ->
    can_change_aop P ->
     absinfer sch (<|| qpend_set_stat (|Vptr qid :: nil|) ;; s  ||> ** HTCBList tcbls ** HCurTCB ct ** P)
     (<|| ABORT ||> ** HTCBList tcbls ** HCurTCB ct **  P ). 
Proof.
  intros.
  assert (Hc: can_change_aop (HTCBList tcbls ** HCurTCB ct ** P)) by pure_auto.
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
  instantiate (3:= s0).
  sep pauto.
  Unshelve.
  exact isched.
Qed.

Lemma qpend_absimp_qpend_to:
  forall s1 s2 sch P tcbls ct p qid tcbls' ecbls ecbls' ml n pwl wl rv
             tcblh tcbvl vhold v1 v2 v3 sus,
    get tcbls ct = Some (p, wait (os_stat_q qid)  (Some Int.zero) ,Vnull, sus) ->
    tcbls' = set tcbls ct (p,rdy,Vnull, false) ->
    get ecbls qid = Some (absmsgq ml n pwl , wl) ->
    In ct wl ->
    ecbls' = set ecbls qid  (absmsgq ml n pwl , (remove_tid ct wl)) ->
    rv = Vnull ->
    can_change_aop P ->
     absinfer sch (<|| (qpend_to (|Vptr qid :: rv :: nil|);; s1) ?? s2  ||> 
        ** HECBList ecbls **  HTCBList tcbls ** HCurTCB ct **
        EvtInv_part2 ecbls tcblh tcbvl vhold v1 v2 v3 ** P)
           (<|| s1 ||> **  HECBList ecbls' **  HTCBList tcbls' ** HCurTCB ct **
           EvtInv_part2 ecbls' tcblh tcbvl vhold v1 v2 v3 ** P).
Proof.
  intros.
  substs.
  infer_solver 0%nat.
  unfold EvtInv_part2 in *.
  unfold ASemEIBs in *.
  unfold AMuxEIBs in *.
  unfold AMqEIBs in *.
  sep pauto.
  eapply mq_ecb_p_mq_set_preserve; eauto.
  eapply mux_ecb_p_mq_set_preserve; eauto.
  eapply sem_ecb_p_mq_set_preserve; eauto.
  eapply RH_SEM_EINFO_ECB_P_mq_set_preserve; eauto.  
  eapply RH_MUX_EIB_ECB_P_mq_set_preserve; eauto.
  eapply RH_EIB_ECB_Q_P_mq_set_preserve; eauto.
  Unshelve.
  exact None.
Qed.

Lemma qpend_absimp_qpend_to_abt:
  forall s1 s2 sch P tcbls ct p qid ecbls ml n pwl wl rv sus,
    get tcbls ct = Some (p, wait (os_stat_q qid)  (Some Int.zero) ,Vnull, sus) ->
    get ecbls qid = Some (absmsgq ml n pwl , wl) ->
    In ct wl ->
    rv <> Vnull ->
    can_change_aop P ->
     absinfer sch (<|| (qpend_to (|Vptr qid :: rv :: nil|);; s1) ?? s2  ||> 
        ** HECBList ecbls **  HTCBList tcbls ** HCurTCB ct ** P)
           (<|| ABORT ||> **  HECBList ecbls **  HTCBList tcbls ** HCurTCB ct ** P).
Proof.
   intros.
  assert (Hc: can_change_aop (HECBList ecbls ** HTCBList tcbls ** HCurTCB ct ** P)) by pure_auto.
  eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver;
  instantiate (3:= s);
  sep pauto.
  Unshelve.
  exact None.
  exact isched.
  exact isched.
Qed.

Lemma qpend_absimp_qpend_block_get:
  forall s1 s2 sch P tcbls ct p qid tcbls' rv st m sus,
    get tcbls ct = Some (p, st ,m, sus) ->
    m <> Vnull ->
    tcbls' = set tcbls ct (p,rdy,Vnull, false) ->
    rv = m ->
    can_change_aop P ->
     absinfer sch (<|| s1 ?? (qpend_block_get (|Vptr qid :: rv :: nil|);; s2)  ||> 
        **  HTCBList tcbls ** HCurTCB ct ** P)
           (<|| s2 ||> ** HTCBList tcbls' ** HCurTCB ct ** P).
Proof.
  intros.
  substs.
  infer_solver 1%nat.
  Unshelve.
  exact None.
Qed.

Lemma qpend_absimp_qpend_block_get_abt:
  forall s1 s2 sch P tcbls ct p qid tcbls' rv st m sus,
    get tcbls ct = Some (p, st ,m, sus) ->
    m <> Vnull ->
    tcbls' = set tcbls ct (p,rdy,Vnull, false) ->
    rv <> m ->
    can_change_aop P ->
     absinfer sch (<|| s1 ?? (qpend_block_get (|Vptr qid :: rv :: nil|);; s2)  ||> 
        **  HTCBList tcbls ** HCurTCB ct ** P)
           (<|| ABORT ||> ** HTCBList tcbls ** HCurTCB ct ** P).
Proof.
   intros.
  assert (Hc: can_change_aop (HTCBList tcbls ** HCurTCB ct ** P)) by pure_auto.
  eapply absinfer_trans; try (eapply absinfer_choice2; eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver;
  instantiate (3:= s);
  sep pauto.
  Unshelve.
  exact None.
  exact isched.
Qed.

Lemma OSQPend_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSQPend
                  vl logicl OSQPendPre ct->
      Some r =
      BuildRetI os_internal OSQPend vl logicl OSQPendPost ct->
      exists t d1 d2 s,
        os_internal OSQPend = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  change ((x1 :: Vint32 i :: x :: nil) ++ v'6 :: nil) with (x1 :: Vint32 i :: x :: v'6 :: nil).
  inverts H5.
  inverts H0.
  substs.
  rename v'9 into er.
  rename i into vt.
  rename v'7 into errid.
  rename v'6 into rv.
  rename v'2 into s.
  rename H2 into Hvt_rgn.

  (* OSIntNesting *)
   hoare forward prim.
  unfold AGVars.
  hoare unfold.
  hoare forward.
  pure_auto.
  hoare unfold.
  assert (Hvret: rv =Vnull \/ rv <> Vnull) by tauto. 
   destruct Hvret.
   2: { hoare abscsq.
           apply noabs_oslinv.
           eapply qpend_absimp_iserr_abt; eauto.
           pure_auto.
           eapply absabort_rule.
         } 
  subst.
  hoare abscsq.
  apply noabs_oslinv.
  eapply qpend_absimp_iserr; eauto.
  pure_auto.
  hoare forward prim.
  unfold AGVars.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep cancel Aier.
  sep pauto.
  auto.
  pure_auto.
  instantiate (1:= Afalse).

  clear -Hvt_rgn H3.
  hoare forward prim.
  unfold EvtInv.
  hoare unfold.

  rename v'19 into vcspace.
  rename v'20 into v20. 
  rename v'21 into v21. 
  rename v'22 into v22. 
  rename v'23 into v'19. 
  rename v'24 into v'20. 
  rename v'25 into v'21. 
  rename v'26 into v'22. 
  rename v'27 into v'23. 
  rename v'28 into v'24. 
  rename v'29 into v'25. 
  rename v'30 into v'26. 
  rename v'31 into v'27. 
  rename v'32 into v'28.  
  rename v'33 into v'29. 
  rename v'34 into v'30. 
  rename v'35 into v'31. 
  rename v'36 into v'32. 
  rename v'37 into v'33. 
  rename v'38 into v'34. 
  rename v'39 into v'35. 
  rename v'40 into v'36. 
  rename v'41 into v'37. 

  (* assign err *)
  rename v'35 into ebls.
  hoare_lifts_trms_pre (Aop, eblsid).
  destruct (get ebls errid) eqn: Hgeterr.
  2:{  eapply abscsq_rule.
         apply noabs_oslinv.
         eapply qpend_absimp_set_errv_abt; pauto.
         eapply absinfer_eq.
         apply absabort_rule.
      }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpend_absimp_set_errv; pauto.
  eapply absinfer_eq.
  (* actual assign err *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AErrblkList).
  eapply err_list_split_frm; eauto.
  unfold node.
  hoare unfold.
  inverts H10; inverts H11.
  hoare forward.
  hoare_lifts_trms_pre (Aop, err).
  eapply assign_rule_deref_ptr.
  intros. sep get rv.
  simpl Astruct.
  split.
  introv Hsat. sep cancel (Aptrmapsto). eauto.
  intros; sep auto.
  intros; sep get rv.
  eapply eq_int; auto.
  intros. sep eexists. sep cancel p_local. simpl; auto.
  hoare forward prim.
  sep cancel Aier.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  sep normal.
  sep eexists.
  trycancel_EvtInv.
  sep pauto; eauto.
  unfold AErrblkList.
  sep pauto.
  eapply err_sllseg_merge with (vsem:= (v'44, Int.zero)) (errv:= (Int.repr OS_ERR_PEND_ISR)) 
                                                                   (vl:= ((V$ OS_ERR_PEND_ISR) :: v'40 :: nil)); eauto.
  sep cancel err_sllseg.
  sep cancel err_sllseg.
  unfold node.
  simpl Astruct.
  sep pauto; eauto.
  sep cancel (Aptrmapsto).
  sep cancel Aptrmapsto.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.
  eapply EbMod.my_joinsig_join_set; eauto.
  eapply my_joinsig_set; eauto.
  split; auto. go.
  rewrite EbMod.map_get_set; auto.
  auto.
  pure_auto.
  (* end of err *)
  hoare forward.

  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  hoare forward prim.
  unfold AGVars.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep cancel Aier.
  sep pauto.
  auto.
  pure_auto.
  (* end add *)

   clear -Hvt_rgn H3.
  hoare forward prim.
  (*if (pevent == NUll) *)
  hoare forward; pauto.
  instantiate (1:= Afalse).
  unfold EvtInv.
  rename v'19 into vcspace.
  rename v'20 into v20. 
  rename v'21 into v21. 
  rename v'22 into v22. 

  hoare unfold.
  hoare_lifts_trms_pre Aop.
  destruct H3 as [Hvp_eq | ((vp_b & vp_i) & Hvp_eq)]; subst.
  2: { simpl in H10; tryfalse. }
  assert (Hrv: rv = Vnull \/ rv <> Vnull) by tauto.
  destruct Hrv.
  2: {  eapply abscsq_rule.
          apply noabs_oslinv.
         eapply qpend_absimp_null_return_abt; pauto.
         eapply absinfer_eq.
         apply absabort_rule.
       }
  subst rv.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpend_absimp_null_return; pauto.
  eapply absinfer_eq.
  (* assign err *)
  rename v'35 into ebls.
  hoare_lifts_trms_pre (Aop, eblsid).
  destruct (get ebls errid) eqn: Hgeterr.
  2:{  eapply abscsq_rule.
         apply noabs_oslinv.
         eapply qpend_absimp_set_errv_abt; pauto.
         eapply absinfer_eq.
         apply absabort_rule.
      }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpend_absimp_set_errv; pauto.
  eapply absinfer_eq.
  (* actual assign err *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AErrblkList).
  eapply err_list_split_frm; eauto.
  unfold node.
  hoare unfold.
  inverts H3; inverts H13.
  hoare forward.
  hoare_lifts_trms_pre (Aop, err).
  eapply assign_rule_deref_ptr.
  intros. sep get rv.
  simpl Astruct.
  split.
  introv Hsat. sep cancel (Aptrmapsto). eauto.
  intros; sep auto.
  intros; sep get rv.
  eapply eq_int; auto.
  intros. sep eexists. sep cancel p_local. simpl; auto.
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier.
  unfold EvtInv.
  sep normal.
  sep eexists.
  trycancel_EvtInv.
  sep pauto; eauto.
  unfold AErrblkList.
  sep pauto.
  eapply err_sllseg_merge with (vsem:= (v'43, Int.zero)) (errv:= (Int.repr OS_ERR_PEVENT_NULL)) 
                                                                   (vl:= ((V$ OS_ERR_PEVENT_NULL) :: v'39 :: nil)); eauto.
  sep cancel err_sllseg.
  sep cancel err_sllseg.
  unfold node.
  simpl Astruct.
  sep pauto; eauto.
  sep cancel (Aptrmapsto).
  sep cancel Aptrmapsto.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.
  eapply EbMod.my_joinsig_join_set; eauto.
  eapply my_joinsig_set; eauto.
  split; auto. go.
  rewrite EbMod.map_get_set; auto.
  auto.
  Optimize Proof.
  Optimize Heap.
  pure_auto.
  (* end of err *)
  hoare forward.

  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  destruct H3 as [Hvp_eq | ((vp_b & vp_i) & Hvp_eq)]; subst.
  simpl in H1; destruct H1; tryfalse.

  unfold EvtInv.
  rename v'19 into vcspace.
  rename v'20 into v20. 
  rename v'21 into v21. 
  rename v'22 into v22. 

  hoare unfold.
  rename v'35 into locmp.
  rename v'36 into ptrmp.
  rename v'11 into els.
  rename v'3 into fecbh.
  rename v'19 into fecbvl.
  rename v'30 into semeibs.
  rename v'31 into muxeibs.
  rename v'32 into mqeibs.
  hoare_assert_pure (get ptrmp ct = Some (Vnull, Vnull, Vptr (vp_b, vp_i))
                                             /\ get locmp ct = Some (V$ os_code_defs.__EvLoc_normal)).
  { get_hsat Hsat.
     sep_lifts_trms_in Hsat (evlocid, evptrid, tcbllsegevaux, AOSTCBList,p_local).
    eapply get_aux;eauto.
   }
  hoare_split_pure_all.
  destruct H3 as (Hget_ptr & Hget_loc).

  assert (Hevt: is_evt els (vp_b, vp_i) \/ ptr_in_ecblist (Vptr (vp_b, vp_i)) fecbh fecbvl).  
  { eapply mq_ecb_nml; eauto. }

  destruct Hevt as [Hevt | Hfree]. 
  Focus 2.
  (* pevent points into list of free ECBs *)
  assert (Hfecbh_eq: exists p, fecbh = Vptr p).
  {
    unfold ptr_in_ecblist in Hfree.
    lets Hptr: ptr_in_ecbsllseg_ptr Hfree.
    eauto.
  }
  destruct Hfecbh_eq as ( (fb & fi) & Heq).
  subst fecbh.
  eapply backward_rule1.
  introv Hsat.
  unfold AOSEventFreeList in Hsat.
  unfold ecbf_sll in Hsat.
  sep normal in Hsat.
  sep_lifts_trms_in Hsat ecbf_sllseg.
  eapply ecbf_sllseg_split3_frm; eauto.
  hoare unfold.

  hoare forward.
  go.
  2: { instantiate(1:= Afalse).
          eapply hoare_disj_afalseP_l_pre.
          change (Int.eq ($ OS_EVENT_TYPE_UNUSED) ($ OS_EVENT_TYPE_MUTEX)) with false. 
          hoare unfold.
          simpl in H3; change (Int.notbool Int.zero) with Int.one in H3; 
          destruct H3; tryfalse. }
  unfold AECBList.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Astruct, evsllseg).

  hoare_assert_pure (get els (v'36, Int.zero) = None).
  {
    get_hsat Hsat.
    lets H00: semcre_ecblist_star_not_inh H3 Hsat.
    auto.
  }
  hoare_split_pure_all.
  rename H14 into Hnone.

   assert (Htype_err': ~ (exists n ml pwl wl, get els (v'36, Int.zero) = Some (absmsgq n ml pwl, wl))).
  { rewrite Hnone.
    introv Hf; destruct Hf as (mx & my & mz & md & Hf ); inverts Hf.
  }
  hoare_lifts_trms_pre (Aop, absecblist).
  assert (Hrv: rv = Vnull \/ rv <> Vnull) by tauto.
  destruct Hrv.
  2 :{
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply qpend_absimp_no_q_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        eapply absabort_rule.
  }
  subst rv.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpend_absimp_no_q; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  (* assign err *)
  rename v'34 into ebls.
  hoare_lifts_trms_pre (Aop, eblsid).
  destruct (get ebls errid) eqn: Hgeterr.
  2:{  eapply abscsq_rule.
         apply noabs_oslinv.
         eapply qpend_absimp_set_errv_abt; pauto.
         eapply absinfer_eq.
         apply absabort_rule.
      }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpend_absimp_set_errv; pauto.
  eapply absinfer_eq.
  (* actual assign err *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AErrblkList).
  eapply err_list_split_frm; eauto.
  unfold node.
  hoare unfold.
  inverts H23; inverts H24.
  hoare forward.
  hoare_lifts_trms_pre (Aop, err).
  eapply assign_rule_deref_ptr.
  intros. sep get rv.
  simpl Astruct.
  split.
  introv Hsat. sep cancel (Aptrmapsto). eauto.
  intros; sep auto.
  intros; sep get rv.
  eapply eq_int; auto.
  intros. sep eexists. sep cancel p_local. simpl; auto.
  hoare forward prim.
  unfold EvtInv.
  sep pauto; eauto.
  trycancel_EvtInv.
  sep cancel Aier.
  sep cancel p_local.
  unfold AErrblkList.
  unfold AECBList.
  unfold AOSEventFreeList.
  unfold ecbf_sll.
  sep pauto; eauto.
  sep cancel evsllseg.
  eapply err_sllseg_merge with (vsem:= (v'44, Int.zero)) (errv:= (Int.repr OS_ERR_EVENT_TYPE)) 
                                                                   (vl:= ((V$ OS_ERR_EVENT_TYPE) :: v'40 :: nil)); eauto.
  sep cancel err_sllseg.
  sep cancel err_sllseg.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  unfold node.
  simpl Astruct.
  sep pauto; eauto.
  sep cancel (Aptrmapsto).
  sep cancel Aptrmapsto.
  eapply ecbf_sllseg_compose3_frm; eauto.
  sep cancel Aarray.
  sep cancel Aarray.
  sep cancel ecbf_sllseg.
  sep cancel ecbf_sllseg.
  simpl Astruct.
  sep pauto; eauto.
  unfolds; simpl; auto.
  go.
  eapply EbMod.my_joinsig_join_set; eauto.
  eapply my_joinsig_set; eauto.
  split; auto. go.
  rewrite EbMod.map_get_set; auto.
  auto.
  pure_auto.
  (* end of err *)
  hoare forward.

  (* pevent points to an active ECB *) 
  assert (Hget: exists ecb, get els (vp_b, vp_i) = Some ecb).
  { clear -Hevt.
    unfold is_evt in Hevt.
    destruct Hevt as [Hsem | [Hmux | Hque]].
    unfold is_sem in Hsem.
    simpljoin1; eexists; eauto.
    unfold is_mux in Hmux.
    simpljoin1; eexists; eauto.
    unfold is_que in Hque.
    simpljoin1; eexists; eauto.
  }
  destruct Hget as (d & Hget).
(*   destruct d.  *)
  (* split AECBList *)
  unfold AECBList.
  hoare unfold.
  lets Hget_ectr: ECBList_P_get_ectr_some Hget H3.
  destruct Hget_ectr as (et & etbl & petbl & Hget_ectr).
  eapply backward_rule1.
  intros.
  eapply get_ectr_decompose; eauto.
  sep cancel evsllseg. eauto.
  hoare unfold.
  hoare_assert_pure (length v'14 = length v'30).
  { get_hsat Hsat. sep_lifts_trms_in Hsat (evsllseg v'3).
     eapply evsllseg_list_len_eq in Hsat; auto.
  }
  hoare_split_pure_all.
  lets Hels_split: ecblist_p_decompose_new H11 H25 H26 H3.
  mytac.
  simpl ECBList_P at 1 in H15.
  mytac.
  inverts H15.
  (*if OSEventType !=ₑ ′ OS_EVENT_TYPE_Q*)
  hoare forward.
  go.
  pure_auto.
  pure_auto.
  hoare unfold.
  destruct (Int.eq i1 ($ OS_EVENT_TYPE_Q)) eqn:eq1.
  simpl in H15. change (Int.notbool Int.one) with Int.zero in H15. tryfalse.

  eapply backward_rule1.
  intros.
  eapply eventtype_neq_q_gen; eauto.
  sep cancel AEventData. eauto.
  unfolds; simpl; auto.
  hoare_split_pure_all.
  rename H36 into Htype_err.
  lets Hgete: EcbMod.join_sig_get H37.
  eapply EcbMod.join_get_r in Hgete; eauto.
  unfold get in Hget; unfold EcbMap in Hget.
  rewrite Hget in Hgete; inverts Hgete.
  assert (Htype_err': ~ (exists m n pwl wl, get els (v'39, Int.zero) = Some(absmsgq m n pwl, wl)) ).
  { clear -Htype_err Hget.
     unfold get; unfold EcbMap.
     rewrite Hget.
     introv Hf. simpljoin. inverts H.
     eapply Htype_err; eauto.
  }
  hoare_lifts_trms_pre (Aop, absecblist).
  assert (Hrv: rv = Vnull \/ rv <> Vnull) by tauto.
  destruct Hrv.
  2 :{
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply qpend_absimp_no_q_abt; eauto.
        can_change_aop_solver.
        apply absinfer_eq.
        eapply absabort_rule.
  }
  subst rv.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpend_absimp_no_q; eauto.
  can_change_aop_solver.
  apply absinfer_eq.

  instantiate (1:= Afalse).
  (* assign err *)
  rename v'34 into ebls.
  hoare_lifts_trms_pre (Aop, eblsid).
  destruct (get ebls errid) eqn: Hgeterr.
  2:{  eapply abscsq_rule.
         apply noabs_oslinv.
         eapply qpend_absimp_set_errv_abt; pauto.
         eapply absinfer_eq.
         apply absabort_rule.
      }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpend_absimp_set_errv; pauto.
  eapply absinfer_eq.
  (* actual assign err *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AErrblkList).
  eapply err_list_split_frm; eauto.
  unfold node.
  hoare unfold.
  inverts H42; inverts H43.
  hoare forward.
  hoare_lifts_trms_pre (Aop, err).
  eapply assign_rule_deref_ptr.
  intros. sep get rv.
  simpl Astruct.
  split.
  introv Hsat. sep cancel (Aptrmapsto). eauto.
  intros; sep auto.
  intros; sep get rv.
  eapply eq_int; auto.
  intros. sep eexists. sep cancel p_local. simpl; auto.
  hoare forward prim.
  unfold EvtInv.
  sep pauto; eauto.
  trycancel_EvtInv.
  sep cancel Aier.
  sep cancel p_local.
  unfold AErrblkList.
  unfold AECBList.
  sep pauto; eauto.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eapply err_sllseg_merge with (vsem:= (v'43, Int.zero)) (errv:= (Int.repr OS_ERR_EVENT_TYPE)) 
                                                                   (vl:= ((V$ OS_ERR_EVENT_TYPE) :: v'36 :: nil)); eauto.
  sep cancel err_sllseg.
  sep cancel err_sllseg.
  unfold node.
  simpl Astruct.
  sep pauto; eauto.
  sep cancel (Aptrmapsto).
  sep cancel Aptrmapsto.
  eapply evsllseg_compose;eauto.
  unfolds; simpl; eauto.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  simpl Astruct.
  sep pauto; eauto.
  sep cancel AOSPostEventTbl.
  sep cancel Aarray.
  2: { split; eauto. go. }
  sep pauto; eauto.
  eapply EbMod.my_joinsig_join_set; eauto.
  eapply my_joinsig_set; eauto.
  split; auto. go.
  rewrite EbMod.map_get_set; auto.
  auto.
  Optimize Proof.
  Optimize Heap.
  pure_auto.
  (* end of err *)
  hoare forward.
  (* OSEventType = OS_EVENT_TYPE_Q *)
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  destruct (Int.eq i1 ($ OS_EVENT_TYPE_Q)) eqn:eq1.
  2: { simpl in H15. change (Int.notbool Int.zero) with Int.one in H15.
          destruct H15; tryfalse. }
  eapply semacc_int_eq_true in eq1.
  subst i1.
  destruct v'32;
   simpl AEventData;
(*   [ idtac | simpl AEventData | simpl AEventData | simpl AEventData]; *)
  hoare unfold.
  lets Hgete: EcbMod.join_sig_get H37.
  eapply EcbMod.join_get_r in Hgete; eauto.
  unfold get in Hget; unfold EcbMap in Hget.
  rewrite Hget in Hgete; inverts Hgete.
  destruct x5.
  lets Hcp: H38.
  destruct e; simpl in H38; tryfalse.
  mytac.
  funfold H38.
(*   eapply _mathsolver.repr_unsigned in H57; subst x0. *)
  rename x0 into qentries; rename H57 into qentris.
  funfold H40.
  rewrite Int.repr_unsigned in *.
  rename m into n; rename l into ml; rename l0 into pwl; rename w into wl.

  (* curp not is a idle task *)
  unfold AOSTCBList.
  unfold tcbdllseg.
  simpl dllseg.
  unfold node.
  hoare unfold.
  lets Hget_ct: Mbox_common.TCBListP_head_in_tcb H63.
  destruct Hget_ct as (cst & sus & Hget_ct).
  lets Hget_ct': Hget_ct.
  eapply TcbMod.join_get_r in Hget_ct; eauto.
  rename v'12 into tls.
  rename v'38 into tls1.
  rename v'40 into tls2.
  lets Htcb_rl: TCBList_P_imp_RL H63.
  simpl RL_TCBblk_P_List in Htcb_rl.
   destruct Htcb_rl as (Htcb_rl & _).
   assert (Hct_range: (Int.unsigned i6 < 64)%Z).
  { eapply tcbblk_prio_range; eauto. }

  hoare_lifts_trms_pre (Aop, abstcblsid, curtid).
  assert(Hnidle: i6 <> ($ OS_IDLE_PRIO) \/ i6 = ($ OS_IDLE_PRIO))
 by (clear; tauto).
  destruct Hnidle as [Hnidle | Hnidle].
  2 :{
        subst.
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply qpend_absimp_idle_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        eapply absabort_rule.
  }
(* curp is rdy *)
  assert (Hct_rdy: (cst = rdy /\ sus = false) \/ ~(cst = rdy /\ sus = false)) by (clear; tauto).
  destruct Hct_rdy as [(Hct_rdy & Hsus_eq) | Hf].
  2 :{
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply qpend_absimp_stat_err_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        eapply absabort_rule.
  }
  subst sus.
  subst cst.
  assert (Hveq: x20 = Vnull /\ i7 = $ OS_STAT_RDY).
  {
    lets Hget_r: get_tcb_stat_rdy H63 Hget_ct'.
    unfold V_OSTCBStat,V_OSTCBEventPtr in Hget_r.
    simpl in Hget_r.
    clear -Hget_r.
    destruct Hget_r; pauto.
  }
  destruct Hveq as (Hvptr & Hvst). subst x20. subst i7.
  assert (Hor: Int.or  ($ OS_STAT_RDY) ($ OS_STAT_Q) = ($ OS_STAT_Q)).
  {
    change ($ OS_STAT_RDY) with (Int.zero).
    rewrite Int.or_commut.
    apply Int.or_zero.
  }
  (* pq ′ =ₑ pevent ′ .. OSEventPtr;ₛ*)
  hoare forward.
  go.
  hoare_assert_pure (RH_PrioTbl_P v'2 v'17 vhold_addr).
  { get_hsat Hsat.
     unfold AOSTCBPrioTbl in Hsat.
     sep split in Hsat.
     auto.
   }
  apply pure_split_rule'; introv Hrh_ptbl.
  (* If (pq ′ .. OSQEntries >ₑ ′ 0) *)
  hoare forward.
  go.
  clear; pure_auto.
  instantiate (1:= Afalse).
  hoare unfold.
  destruct (Int.ltu ($ 0) qentries) eqn: eq1;
  simpl in H38; tryfalse.
  (* message ′ =ₑ ∗ pq ′ .. OSQOut;ₛ *)
  lets Hout: OSQOut_elim H44.
  unfold V_qfreeblk,V_OSQOut in Hout.
  simpl nth_val in Hout.
  specialize (Hout (eq_refl _)).
  destruct Hout as (iout & Hout_eq & _).
  inverts Hout_eq.
  simpl in H42.
  inverts H42.
  lets Hiout_mat: wellq_props H46 eq1 Hcp H44.
  change (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero)) with ($ 4) in *.
  destruct Hiout_mat as (Hiout_lt1 & Hiout_sub_eq & Hiout_lt2 & Hiout_lt3 & Hiout_mat).
(*   destruct Hout as (iout & Hout_eq & Hiout_lt1 & Hiout_sub_eq & Hiout_lt2). *)
  hoare forward; try change (Int.unsigned ($ 4)) with 4 in *.
  go.
  auto.
  (* ++ pq ′ .. OSQOut;ₛ *)
  hoare forward.
  go.
  (* −− pq ′ .. OSQEntries;ₛ*)
  hoare forward.
  go.
  (* If (pq ′ .. OSQOut ==ₑ pq ′ .. OSQEnd) *)
  lets Hend: OSQEnd_elim H44.
  unfold V_qfreeblk,V_OSQEnd,V_OSQSize in Hend.
  simpl nth_val in Hend.
  specialize (Hend (eq_refl _) (eq_refl _)).
  inverts Hend.
  lets Hstart: OSQStart_elim H44.
  unfold V_qfreeblk, V_OSQStart, V_OSQSize in Hstart.
  simpl nth_val in Hstart.
  specialize (Hstart (eq_refl _) (eq_refl _)).
  inverts Hstart.
  assert (Hentries_rgn: Int.unsigned (qentries -ᵢ $ 1) <=? Int16.max_unsigned = true).
  apply ge_0_minus_1_in_range; auto.
  hoare_lifts_trms_pre (Aop, pq, Astruct (v'20, Int.zero), OS_MAX_Q_SIZE).
  hoare remember (1:: 2:: 3 :: 4 :: nil)%nat pre.
  eapply seq_rule.
  instantiate (1:= (
  <|| spec_code_cons
          (qpendnew (Vptr (v'39, Int.zero) :: Vint32 vt :: Vptr errid :: rv :: nil))
          s ||>  **
  LV pq @ OS_Q ∗ |-> Vptr (v'20, Int.zero) **
  Astruct (v'20, Int.zero) OS_Q
    (x14
     :: Vptr (v'32, $ 4)
        :: Vptr (v'32, Int.mul n ($ 4) +ᵢ  $ 4)
           :: x8
              ::   ( if  Int.eq iout (Int.mul n ($ 4))
                     then Vptr (v'32, $ 4) 
                     else Vptr (v'32, iout +ᵢ  Int.mul ($ 1) ($ 4)))
                 :: Vint32 n
                    :: Vint32 (qentries -ᵢ $ 1)
                       :: Vptr (v'32, Int.zero) :: nil) **
  Aarray (v'32, $ 4) (Tarray (Void) ∗ ∘ OS_MAX_Q_SIZE) v2 ** H42)).
  hoare forward.
  go.
  go.
  clear; pure_auto.
  hoare forward.
  go.
  get_hsat Hsat.
  rewrite peq_true in Hsat.
  change ( Int.mul ($ 1) ($ 4)) with ($ 4) in Hsat.
  rewrite Int.translate_eq in Hsat.
  destruct (Int.eq iout (Int.mul n ($ 4))) eqn: eq2;
  simpl val_inj in Hsat;
  destruct Hsat as [Hsat | Hsat].
  sep pauto.
  sep split in Hsat.
  destruct H42; tryfalse.
  sep split in Hsat. destruct H75; tryfalse.
  sep pauto.
  lets Hmat_ls: H36.
  unfolds in Hmat_ls.
  unfold V_OSQStart,V_OSQIn,V_OSQOut,V_OSQSize,V_OSQEntries in Hmat_ls.
  simpl in Hmat_ls.
  destruct Hmat_ls as (qstart & qin & qout & qsize & d1 & d2 & qens & Hmat_ls).
  simpljoin.
  inverts H75; inverts H76; inverts H77; inverts H78; inverts H79.
(*   funfold H36. *)
  rename H82 into Hdist_gt; rename H83 into Hptr_ls_ml;
  rename H84 into Hdist_lt; rename H85 into Hdist_eq.
  lets Hmsg: Hcp.
  eapply h_has_same_msg in Hmsg; eauto.
  2: {  simpl. change (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero)) with ($ 4); eauto.    }
  destruct Hmsg as (ml' & qsize' & pwl' & wl' & Heq).
  inverts Heq.
  rename qsize' into qsize; rename pwl' into pwl; rename wl' into wl.
  rename qens into qentries.
  assert (Hwellfemq: 
 WellformedOSQ (x14
            :: Vptr (v'32, $ 4)
               :: Vptr (v'32, Int.mul qsize ($ 4) +ᵢ  $ 4)
                  :: Vptr qin
                     :: (if Int.eq iout (Int.mul qsize ($ 4))
                         then Vptr (v'32, $ 4)
                         else Vptr (v'32, iout +ᵢ  Int.mul ($ 1) ($ 4)))
                        :: Vint32 qsize
                           :: Vint32 (qentries -ᵢ $ 1)
                              :: Vptr (v'32, Int.zero) :: nil)).
  { destruct (Int.eq iout (Int.mul qsize ($ 4))) eqn: eq2.
      eapply get_wellformedosq_end with (ens:= Vint32 qentries);eauto.
      eapply get_wellformedosq_end' with (ens:= Vint32 qentries);eauto.
      change ( Int.mul ($ 1) ($ 4)) with ($ 4).
      clear -eq2. introv Hf.
      remember (Int.mul qsize ($ 4) +ᵢ  $ 4) as iout'.
      inversion Hf.
      subst iout'.
      rewrite <- Int.translate_eq with (d:= $ 4 ) in eq2.
      rewrite H0 in eq2.
      rewrite Int.eq_true in eq2.
      tryfalse.
   }
    assert (Henty_eq: ((qentries -ᵢ $ 1) +ᵢ  $ 1) = qentries).
  {
     clear - qentris eq1 H52.
     unfold Int.sub, Int.add.
     unfold Int.ltu in eq1.
     change (Int.unsigned ($ 1)) with 1.
     change (Int.unsigned ($ 0)) with 0 in eq1.
     assert (1 <= (Int.unsigned qentries)).
     { destruct (zlt 0 (Int.unsigned qentries)) eqn: eq_lt; tryfalse. auto with zarith. }
     int auto.
  Optimize Proof.
  Optimize Heap.
   }
   eapply seq_rule.
   instantiate (1:= ((EX er, Aier er) **
  Aie true **
  Ais nil **
  Acs nil **
  Aisr empisr **
   <|| qpend_set_errv (|Vptr errid :: V$ OS_NO_ERR :: nth_val'
                          (Z.to_nat ((Int.unsigned iout - Int.unsigned ($ 4)) / 4))
                          v2 :: nil|);; s ||>  **
  p_local OSLInv (v'42, Int.zero)
    (logic_val (V$ 1)
     :: logic_val (V$ __EvLoc_normal)
        :: logic_val Vnull
           :: logic_val Vnull :: logic_val (Vptr (v'39, Int.zero)) :: nil) **
  LV os_code_defs.x @ Int16u |-> (if Int.eq i ($ 0) then v'1 else (V$ OS_STAT_POSTQ)) **
  LV pq @ OS_Q ∗ |-> Vptr (v'20, Int.zero) **
  LV message @ (Void) ∗ |-> nth_val'
                          (Z.to_nat ((Int.unsigned iout - Int.unsigned ($ 4)) / 4))
                          v2  **
  LV err @ (char_t) ∗ |-> Vptr errid **
  LV timeout @ Int16u |-> Vint32 vt **
  LV pevent @ OS_EVENT ∗ |-> Vptr (v'39, Int.zero) **
  A_dom_lenv
    ((err, (char_t) ∗)
     :: (timeout, Int16u)
        :: (pevent, OS_EVENT ∗)
           :: (message, (Void) ∗) :: (pq, OS_Q ∗) :: (os_code_defs.x, Int16u) :: nil) **
   [| rv = nth_val'  (Z.to_nat ((Int.unsigned iout - Int.unsigned ($ 4)) / 4)) v2 |])).
  (* IF (pevent ′ .. OSPostEventGrp !=ₑ ′ 0)  *)
  hoare unfold.
  hoare_lifts_trms_pre Aop.
  eapply forward_rule1;
  [ idtac
    | eapply if_rule2';
        [ symbolic execution | idtac | idtac ]].
  eapply disj_intro;
  introv Hsat;
  sep_lifts_trms_in Hsat (val_inj);
  apply sep_pure_split in Hsat;
  destruct Hsat as (Hif & Hsat);
  eauto.
(*   hoare forward. *)
  go.
  clear; pure_auto.
  clear; pure_auto.
  (*  case 1: exist pwl *)
  hoare unfold.
  destruct (Int.eq i ($ 0)) eqn: eq3;
  simpl in H42; try change (Int.notbool Int.one) with Int.zero in H42; tryfalse.
  (* eq3 : Int.eq i ($ 0) = false *)
  (* os_code_defs.x ′ =ₑ ′ OS_STAT_POSTQ;ₛ *)
  hoare forward.
  (* OS_EventTaskPostRdy (-pevent ′, os_code_defs.x ′ -);ₛ *)
  hoare_lifts_trms_pre (Aisr,Ais, aemp_isr_is).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  unfold AOSTCBPrioTbl.
  hoare forward.

  sep cancel p_local.
  sep cancel AOSRdyTblGrp.
  unfold AEventNode.
  unfold AOSEvent.
  unfold AEventData.
  unfold AMsgData.
  unfold AOSQCtr.
  unfold AOSQBlk.
  unfold node.
  unfold AOSEventTbl.
  clear H44. (* old wellformedosq *)
  sep normal.
  sep eexists.
  sep cancel OS_EVENT_TBL_SIZE.
  sep cancel AOSPostEventTbl.
  sep split; eauto.
  sep cancel OS_Q_FREEBLK.
  sep cancel OS_MAX_Q_SIZE.
  sep cancel OS_EVENT.
  sep cancel Astruct.
  unfold tcbdllseg.
  unfold V_OSTCBPrev,V_OSTCBNext.
  eapply dllseg_compose with (h:= v'4) (l2:= (v'41
            :: v'11
               :: Vnull
                  :: x19
                     :: Vint32 i8
                        :: V$ OS_STAT_RDY
                           :: Vint32 i6
                              :: Vint32 i5
                                 :: Vint32 i4 :: Vint32 i3 :: Vint32 i1 :: nil) :: v'8).
  sep cancel (dllseg v'4).
  simpl dllseg at 1.
  unfold node.
  sep pauto.
  sep cancel OS_TCB_flag.
  sep cancel dllseg.
  eauto.
  split; eauto. go.
  unfolds; simpl; eauto.
  unfolds; simpl; eauto.
  unfolds; simpl; eauto.
  unfolds; simpl; eauto.
  split; auto. go.
  unfolds; simpl; eauto.
  split; auto. destruct (Int.eq iout (Int.mul qsize ($ 4))) eqn: eq2; go.
  auto.
  split; auto. go.
  rewrite Henty_eq.
  clear -H44. funfold H44. auto.
  rewrite Henty_eq. change (Int16.max_unsigned) with 65535. auto.
  eauto.
  eauto.
  unfolds; simpl; eauto.
  split. unfolds; simpl; eauto.
  clear -eq3. change ($ 0) with Int.zero in eq3.  eapply semacc_int_eq_false; eauto.
  simpl; eauto.
  simpl; eauto.
  (* TCBList_P *)
   eapply TCBList_P_Combine; eauto.
   get_hsat Hsat.
   sep_lifts_trms_in Hsat (dllseg v'4).
   eapply tcbdllseg_get_last_tcb_ptr; eauto.
  (* end TCBList_P *)
   auto.
   eauto.
   eauto.
   eapply tcbdllseg_combine_ptr_in_tcblist with (s:= s0); eauto.
   unfold tcbdllseg.
   simpl dllseg at 2.
   sep cancel (dllseg v'4).
   unfold V_OSTCBNext,V_OSTCBPrev.
   simpl nth_val.
   unfold node.
   sep normal. sep eexists.
   sep split; eauto.
   sep cancel OS_TCB_flag.
   sep cancel dllseg.
   eauto.
   split; eauto. go.
   pure_auto.

   intros.
    sep auto.
    intros.
    sep auto.

   hoare unfold.
   inverts H114.

   unfold rel_edata_tcbstat_postrdy in H89.
   inverts H87. (* subst v'93. *)
   rename H89 into Hstat_eq.

   assert (Hy_le7: Int.unsigned v'84 <= 7).
   {
      clear - H31 H90.
    lets Hx: osunmapvallist_prop H31; simpljoin.
    rewrite H in H90 ; inverts H90.
    apply Z.leb_le in H0; auto.
    }
    assert (Herow_le255: Int.unsigned v'85 <= 255).
    {
    clear - H91 H103 H104 Hy_le7.
    assert (Z.to_nat (Int.unsigned v'84) < length v'51)%nat.
    rewrite H104; unfold OS_EVENT_TBL_SIZE.
    mauto.
    lets Hx: array_int8u_nth_lt_len H103 H; simpljoin.
    rewrite H91 in H0; invert H0; auto.
    }
    assert(Hx_le7: Int.unsigned v'83 <= 7).
    {
    clear - H92 Herow_le255.
    lets Hx: osunmapvallist_prop Herow_le255; simpljoin.
    rewrite H in H92; inverts H92.
    apply Z.leb_le in H0; auto.
    }
    rename H35 into Hecbptbl.
    assert (Hegrp_nz: v'85 <> $ 0).
    { lets Hrl_egrp: H101.
       eapply rl_tbl_grp_neq_zero in Hrl_egrp; eauto.
       auto with zarith.
     }

    assert(($ Int.unsigned ((v'84<<ᵢ$ 3) +ᵢ  v'83) >>ᵢ $ 3) = v'84) as Heq1.
    { clear - Hy_le7 Hx_le7. mauto. }
    assert(($ Int.unsigned ((v'84<<ᵢ$ 3) +ᵢ  v'83)&ᵢ$ 7) = v'83) as Heq2.
    { clear - Hy_le7 Hx_le7. mauto. }
    assert(Htcbls_tcbjoin: exists n m sus tcbls, 
                     TcbJoin (v'100, Int.zero) 
                     (((v'84<<ᵢ$ 3) +ᵢ  v'83), 
                    wait (os_stat_postq (v'39, Int.zero)) n, m, sus)
                     tcbls v'23).
   { destruct Hecbptbl as (Hlh_ptbl & Hhl_ptbl).
      assert (Hwait: PrioWaitInQ (Int.unsigned ((v'84<<ᵢ$ 3) +ᵢ  v'83)) v'51).
      {  unfolds.
          rewrite Heq1; rewrite Heq2.
          exists v'83 v'84 v'85.
          splits; eauto.
          clear - Hy_le7 Hx_le7.
          mauto.
          apply nth_val'2nth_val; eauto.
          eapply math_8_255_eq; eauto.
      }
     eapply Hlh_ptbl in Hwait; eauto.
     unfold V_OSEventType in Hwait.
     simpl nth_val in Hwait.
     specialize (Hwait (eq_refl _)).
     rewrite Int.repr_unsigned in Hwait.
     destruct Hwait as (tid' & n' & m' & sus' & Hwait).
     unfold TcbJoin.
     exists n' m'.
     destruct H110 as (Hget_t & _ & Hdup).
     eapply Hget_t in H120; eauto.
     3: { apply nth_val'_imp_nth_val_vptr; eauto. }
     2: { clear - Hy_le7 Hx_le7. mauto. }
     destruct H120 as (st0 & m0 & sus0 & Hget_t').
     lets Hx: R_Prio_No_Dup_tid_eq Hdup Hwait Hget_t'.
     destruct Hx as (Hx1 & Hx2 & Hx3); subst st0; subst m0; subst sus0.
     eexists.
     eapply TcbMod.map_join_get_sig; eauto.
    }
   destruct Htcbls_tcbjoin as (wt & msg & sus & tcbls_sub & Htcbjoin).
   assert (Hpend_pre: pwl<>nil /\
                          GetHWait v'23 pwl (v'100,Int.zero) /\
                          TcbMod.get v'23 (v'100,Int.zero) = 
                                     Some (((v'84<<ᵢ$ 3) +ᵢ  v'83), wait (os_stat_postq (v'39, Int.zero)) wt, msg, sus)).
   { eapply pend_expwt_pre with (v'38:= v'84) (v'100:= v'48); eauto.  }
   destruct Hpend_pre as (Hpwl_nnil & Hget_hwait & Hget_wait).
   rewrite Int.repr_unsigned in Heq1,Heq2.
   (* fold EvtInv_part2 *)
   eapply backward_rule1.
   introv Hsat.
   eapply fold_EvtInv_part2; eauto.
   sep pauto.
   trycancel_EvtInv.
   eauto.
   (* change absdata *)
   hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, curtid, EvtInv_part2).
   assert (Hrv: rv = (nth_val'
               (Z.to_nat ((Int.unsigned iout - Int.unsigned ($ 4)) / 4)) v'80) \/
                 rv <> (nth_val'
               (Z.to_nat ((Int.unsigned iout - Int.unsigned ($ 4)) / 4)) v'80) )
   by (clear; tauto).
   destruct Hrv as [Hrv | Habt].
   2: {
         eapply abscsq_rule.
         eapply noabs_oslinv.
         eapply qpend_absimp_ex_pwl_before_sched_abt; eauto.
         can_change_aop_solver.
         eapply absinfer_eq.
         eapply absabort_rule.
    }
    subst rv.
    eapply abscsq_rule.
    eapply noabs_oslinv.
    eapply qpend_absimp_ex_pwl_before_sched; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
    (* EXIT_CRITICAL;ₛ *)
    lets old_tcbnode_p : TCBList_P_tcblist_get_TCBNode_P H112 H80 Hget_wait.
    assert (Hvmsg: v'61 = msg).
    { clear -old_tcbnode_p.
       funfold old_tcbnode_p. auto.
    }
    subst v'61.
     generalize old_tcbnode_p; intro Htmp.
    destruct Htmp as (Hmsg & Hprio & Hh_tcbblk & Hh_tcbstat).
    inverts Hmsg; inverts Hprio.
(*     rewrite Int.and_not_self. *)
    hoare_lifts_trms_pre tcbdllseg.
    eapply set_node_elim_hoare_sus
                  with (st':= rdy) (m':= msg) 
                              (rtbl':= (update_nth_val (Z.to_nat (Int.unsigned v'84)) v'44
                                               (Vint32 (Int.or v'101 v'86)))); eauto.
   eapply TCBNode_P_set_rdy_gen; eauto.
   clear - Hy_le7 Hx_le7.
   mauto.
   rewrite Heq1.
   apply nth_val'2nth_val; auto.
   {
   clear -H77 H99 H117 Hy_le7.
    assert (Z.to_nat (Int.unsigned v'84) < length v'44)%nat.
    rewrite H117.
    eapply z_le_n_lt'; auto.
    lets Hx: array_int8u_nth_lt_len H99 H.
    simpljoin.
    rewrite H77 in H0.
    inverts H0; auto.
    }
    { destruct Hstat_eq; subst v'94.
    assert (Hsus: sus = false) by
    (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: sus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    change (Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_Q)) with ($ OS_STAT_SUSPEND).
    auto.
  Optimize Proof.
  Optimize Heap.
     }
    rewrite Heq2.
    eapply math_mapval_core_prop; auto.
    clear -Hx_le7. mauto.
    (* rtbl_set_one_bit *)
     { destruct sus eqn: eq_sus; auto.
    unfolds.
    rewrite Heq1; rewrite Heq2.
    do 2 eexists.
    splits; eauto.
    clear - Hy_le7 Hx_le7.
    mauto.
    }
    destruct H110 as (_ & _ & Hdup); auto.
    unfolds; simpl; auto.
    hoare_ex_intro.
    hoare_split_pure_all.
    hoare_lifts_trms_pre tcbdllflag.
    eapply backward_rule1.
    introv Hsat.
    eapply tcbdllflag_set_node; eauto.
    unfolds; simpl; auto.
    (* actual exit critical *)
      assert (Heq_sus: Int.eq (v'94&ᵢInt.not ($ OS_STAT_POSTQ)) ($ OS_STAT_RDY) = negb sus).
  { change ($ OS_STAT_RDY) with Int.zero.
    destruct Hstat_eq; subst v'94.
    assert (Hsus: sus = false) by
    (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: sus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    change (Int.or ($ OS_STAT_POSTQ) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_POSTQ)) with ($ OS_STAT_SUSPEND).
    auto.
   }
  rewrite Heq_sus in *. rewrite negb_if in *.

    hoare_lifts_trms_pre (Aisr,Ais,Aier).
    transform_pre add_aemp_isr_is_prop ltac:(sep cancel Aisr; sep cancel Ais; sep cancel Aier).
     hoare forward prim.
     sep cancel p_local.
     sep cancel Aier.
     sep_lifts_trms EvtInv.
     eapply fold_EvtInv_frm'.
     unfold AOSTCBPrioTbl.
     unfold AECBList.
     unfold AOSTCBList.
     sep pauto.
     sep cancel APthreadAttr.
    sep cancel CapabilityInv.
     sep cancel (tcbdllseg v'59).
     sep cancel tcbdllseg.
     sep cancel OSPlaceHolder.
     sep cancel (Aptrmapsto vhold_addr).
     sep cancel tcbdllflag.
     eapply evsllseg_compose; eauto.
     2: { sep cancel AEventNode.
             sep cancel (evsllseg v'3).
             sep cancel evsllseg.
             unfold EvtInv_part2 in *.
             sep pauto.
             cancel_corecommuinv.
             trycancel_EvtInv.
             rewrite <- H35.
             unfold tcbllsegevaux in *.
             eapply llsegevaux_set_node; eauto.
             sep cancel llsegevaux.

             (* PartitionInv *)
             Require Import sem_partition.
             cancel_partitioninv.
             eauto.
             (* end of PartitionInv *)

             unfolds; simpl; auto.
             auto. auto. auto.
          }
      unfolds; simpl; eauto.
      auto.
      eapply R_PrioTbl_P_hold1; eauto.
      auto.
      (* ECBList_P *)
      assert (Heq_case: v'76 = Int.mul v'71 ($ 4) /\ v'69 = Vptr (v'73, $ 4) \/
                                            v'76 <> Int.mul v'71 ($ 4) /\ v'69 = Vptr (v'73, v'76 +ᵢ  ($ 4))).
     { clear -H85.
        destruct H85 as [(Hc & Heq) | (Hc & Heq)];
        [left | right]; split; auto;
        change ( Int.mul ($ 1) ($ 4)) with ($ 4) in *.
        rewrite pair_equal_spec in Hc.
        destruct Hc as (_ & Hc).
        apply semacc_int_eq_true.
        rewrite <- Int.translate_eq with (d:= $ 4).
        rewrite Hc.
        rewrite Int.eq_true; auto.
        introv Hf. apply Hc.
         subst. auto.
     }
     lets Hens_neq: int_ltu_eq_false eq1.
     rewrite Hens_neq in Hdist_eq.
     assert (Hlt_qens: Int.ltu (qentries -ᵢ $ 1) qentries = true).
     {  clear -H40 H57 H52 eq1.
     unfold Int.ltu,Int.sub in *.
     change (Int.unsigned ($ 1)) with 1.
     change (Int.unsigned ($ 0)) with 0 in eq1.
     assert (1 <= (Int.unsigned qentries)).
     { destruct (zlt 0 (Int.unsigned qentries)) eqn: eq_lt; tryfalse. auto with zarith. }
     int auto.
     }
     assert (Hle_qens': Int.ltu (qentries -ᵢ $ 1) v'71 = true).
     { clear -Hwellfemq H44 Hlt_qens.
        rewrite Intlt_true_is_Zlt in *.
        funfold H44. funfold Hwellfemq.
        clear -H12 H19 Hlt_qens.
        eapply Zle_lt_or_eq in H19.
        destruct H19; auto.
        rewrite <- H in *.
        auto with zarith.
      }
     assert (Hptr_msg: isptr msg).
     { clear -H119.
        simpl in H119.
        destruct H119 as (H0 & H1 & H2 & H3 & H4 & H5).
        unfold isptr.
        destruct msg; tryfalse; try eauto.
      }
     assert (Hrgn: Int.unsigned v'86 <= 128).
     {  clear - H94 Hx_le7.
     lets Hx: osmapvallist_prop Hx_le7; simpljoin.
     rewrite H94 in H.  inverts H.
     auto.
      }
     destruct Heq_case as [(Hc & Heq) | (Hc & Heq)]; subst v'69.
     (* v'75 = Int.mul v'70 ($ 4) *)
     subst v'76.
     destruct (Int.eq iout (Int.mul v'71 ($ 4))) eqn: eq2.
     eapply semacc_int_eq_true in eq2; subst iout.
     specialize (Hdist_eq (eq_refl _)).
     destruct Hdist_eq as [ (Hf & _) | (Heq_ens & Hml_eq )].
     tryfalse.
      eapply semacc_int_eq_true in Heq_ens; subst v'71.
     (* Int.eq iout (Int.mul v'70 ($ 4)) = true *)
     eapply ecblist_p_post_exwt_hold1_end' with (pgrep:= v'48); eauto.
     rewrite Henty_eq; eauto.
     lets Hlem: rlh_ecbdata_in_end_part.
     change (Int.mul ($ 1) ($ 4)) with ($ 4) in Hlem.
     eapply Hlem; eauto.
    eapply msgqnode_p_hold_end_part;eauto.
    simpl; auto.
    (* Int.eq iout (Int.mul v'70 ($ 4)) = false *)
     eapply ecblist_p_post_exwt_hold1_end'' with (pgrep:= v'48); eauto.
     rewrite Henty_eq; eauto.
     lets Hlem: rlh_ecbdata_in_end_part.
     change (Int.mul ($ 1) ($ 4)) with ($ 4) in Hlem.
     eapply Hlem; eauto.
     eapply msgqnode_p_hold_no_end_part;eauto.
     simpl; auto.
     (* v'75 <> Int.mul v'70 ($ 4) *)
     assert (Hneq_vptr: Vptr (v'73, Int.mul v'71 ($ 4) +ᵢ  $ 4) <> Vptr (v'73, v'76 +ᵢ  $ 4)).
     { clear -Hc.
     eapply Int_eq_false_Vptr_neq.
     rewrite Int.translate_eq.
     apply Int.eq_false; auto.
     }
     destruct (Int.eq iout (Int.mul v'71 ($ 4))) eqn: eq2.
     eapply semacc_int_eq_true in eq2; subst iout.
     (* Int.eq iout (Int.mul v'70 ($ 4)) = true *)
     eapply ecblist_p_post_exwt_hold1_noend' with (pgrep:= v'48); eauto.
     rewrite Henty_eq; eauto.
     lets Hlem: rlh_ecbdata_in_noend_part.
     change (Int.mul ($ 1) ($ 4)) with ($ 4) in Hlem.
     eapply Hlem; eauto.
    eapply msgqnode_p_hold_end_part;eauto.
    simpl; auto.
    (* Int.eq iout (Int.mul v'70 ($ 4)) = false *)
     eapply ecblist_p_post_exwt_hold1_noend'' with (pgrep:= v'48); eauto.
     rewrite Henty_eq; eauto.
     lets Hlem: rlh_ecbdata_in_noend_part.
     change (Int.mul ($ 1) ($ 4)) with ($ 4) in Hlem.
     eapply Hlem; eauto.
     eapply msgqnode_p_hold_no_end_part;eauto.
     simpl; auto.
     (* end of ECBList_P *)
     (* TCBList_P *)
     eauto.
     eauto.
     eauto.
     (* RH_CurTCB *)
     {
      clear -Hget_ct.
      unfold RH_CurTCB.
      rewrite TcbMod.set_sem.
      destruct (tidspec.beq (v'100, Int.zero) (v'42, Int.zero));
      eauto.
    }
    (* RH_TCBList_ECBList_P *)
    eapply rh_tcblist_ecblist_p_pent_expwt; eauto.
    clear -Hget_hwait. funfold Hget_hwait. auto.

    pure_auto.
    
    (* OS_Sched (­) *)
    eapply forward_rule1.
    2:{
    hoare forward.
    unfold isflag; auto.
    pure_auto.
    intro. sep auto. sep cancel p_local. simpl; auto.
    intro. sep auto. sep cancel p_local. simpl; auto.
    }
   introv Hsat.
(*     get_hsat Hsat. *)
    unfold OS_SchedPost in Hsat.
    unfold OS_SchedPost' in Hsat.
    unfold getasrt in Hsat.
    sep pauto.
    inverts H83.
    sep cancel Aier.
    sep auto.
  Optimize Proof.
  Optimize Heap.
    
    (* not exist pwl, OSPostEventGrp = 0 *)
    (* EXIT_CRITICAL *)
     hoare_split_pure_all.
     destruct (Int.eq i ($0)) eqn: eq3; simpl in H42; 
     try change (Int.notbool Int.zero) with Int.one in H42;
     destruct H42; tryfalse.
    (* fold EvtInv_part2 *)
   eapply backward_rule1.
   introv Hsat.
   eapply fold_EvtInv_part2; eauto.
   sep pauto.
   trycancel_EvtInv.
   eauto.
   (* change absdata *)
   assert (Hpwl_nil: pwl = nil).
   { eapply rlh_ecb_nowait_pwl_prop; eauto.
    }
  subst pwl.
   hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, curtid, EvtInv_part2).
   assert (Hrv: rv = (nth_val'
               (Z.to_nat ((Int.unsigned iout - Int.unsigned ($ 4)) / 4)) v2) \/
                 rv <> (nth_val'
               (Z.to_nat ((Int.unsigned iout - Int.unsigned ($ 4)) / 4)) v2) )
   by (clear; tauto).
   destruct Hrv as [Hrv | Habt].
   2: {
         eapply abscsq_rule.
         eapply noabs_oslinv.
         eapply qpend_absimp_no_pwl_succ_abt; eauto.
         can_change_aop_solver.
         eapply absinfer_eq.
         eapply absabort_rule.
    }
    subst rv.
    eapply abscsq_rule.
    eapply noabs_oslinv.
    eapply qpend_absimp_no_pwl_succ; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
    (* actual exit critical *)
    (* eapply forward_rule1.
    Focus 2. *)
    hoare forward prim.
    sep cancel APthreadAttr.
  sep cancel CapabilityInv.
    sep cancel tcbdllflag.
    sep cancel p_local.
    sep cancel Aier.
    sep_lifts_trms EvtInv.
    eapply fold_EvtInv_frm'.
    sep cancel EvtInv_part2.
    cancel_corecommuinv.
    trycancel_EvtInv.
    unfold AECBList.
    unfold AOSTCBList.
    unfold tcbdllseg.
    sep pauto; eauto.
    sep cancel (dllseg v'4).
    simpl dllseg at 1.
    unfold V_OSTCBPrev,V_OSTCBNext.
    simpl nth_val.
    unfold node.
    sep pauto; eauto.
    sep cancel OS_TCB_flag.
    sep cancel dllseg.
    eapply evsllseg_compose; eauto.
    2: { sep cancel (evsllseg v'3).
           unfold AEventNode.
           unfold AOSEvent.
           unfold node.
           unfold AOSEventTbl.
           sep normal. sep eexists.
           sep cancel AOSPostEventTbl.
           sep cancel OS_EVENT_TBL_SIZE.
           sep pauto; eauto.
           sep cancel OS_EVENT.
           sep cancel evsllseg.
           instantiate (2:= (DMsgQ (Vptr (v'20, Int.zero)) 
            (x14
            :: Vptr (v'32, $ 4)
               :: Vptr (v'32, Int.mul qsize ($ 4) +ᵢ  $ 4)
                  :: Vptr qin
                     :: (if Int.eq iout (Int.mul qsize ($ 4))
                         then Vptr (v'32, $ 4)
                         else Vptr (v'32, iout +ᵢ  Int.mul ($ 1) ($ 4)))
                        :: Vint32 qsize
                           :: Vint32 (qentries -ᵢ $ 1) :: Vptr (v'32, Int.zero) :: nil)
              (x15 :: x16 :: nil) v2)).
           simpl AEventData.
           unfold AMsgData.
           unfold AOSQCtr.
           unfold AOSQBlk.
           unfold node.
           sep pauto; eauto.
           sep cancel OS_Q_FREEBLK.
           sep cancel Aarray.
           sep cancel Astruct.
           eauto.
           cancel_partitioninv.
           eauto.
           unfolds; simpl; eauto.
           split; auto. destruct (Int.eq iout (Int.mul qsize ($ 4))) eqn: eq2; go.
           simpl; auto.
           split; auto. go.
           unfolds; simpl; auto.
           unfolds; simpl; auto.
           split; auto. go.
         }
   unfolds; simpl; auto.
   split; auto. go.
   (* ECBList_P *)
    lets Hnewjoin: ecb_get_set_join_join Hget H37 H32.
    simpljoin1.
   eapply msgqlist_p_compose_pend. eauto. eauto. eauto. eauto.
   destruct (Int.eq iout (Int.mul qsize ($ 4))) eqn: eq2.
   eapply semacc_int_eq_true in eq2; subst iout.
   eapply msgqnode_p_hold_end; eauto.
   simpl; eauto.
   eapply msgqnode_p_hold_no_end; eauto.
   simpl; eauto.
   eauto.
   eauto.
   (* RH_TCBList_ECBList_P *)
   eapply rh_tcbls_mqls_p_getmsg_hold; eauto.

   pure_auto.

   sep cancel Aier.
   sep auto.

  (* begin assign err *)
  clear -Hvt_rgn Hptr_ls_ml.
  hoare forward prim.
  unfold EvtInv.
  hoare unfold.
  rename v'17 into vcspace.
  rename v'18 into v18. 
  rename v'19 into v19. 
  rename v'21 into v21.
  
  rename v'22 into v'17. 
  rename v'23 into v'18. 
  rename v'24 into v'19. 
  rename v'25 into v'21. 
  rename v'26 into v'22. 
  rename v'27 into v'23. 
  rename v'28 into v'24. 
  rename v'29 into v'25. 
  rename v'30 into v'26. 
  rename v'31 into v'27. 
  rename v'32 into v'28. 
  rename v'33 into v'29. 
  rename v'34 into v'30. 
  rename v'35 into v'31. 
  rename v'36 into v'32. 
  rename v'37 into v'33. 
  rename v'38 into v'34. 

  rename v'40 into v'35. 
  rename v'41 into v'36. 
 



  (* assign err *)
  rename v'34 into ebls.
  hoare_lifts_trms_pre (Aop, eblsid).
  destruct (get ebls errid) eqn: Hgeterr.
  2:{  eapply abscsq_rule.
         apply noabs_oslinv.
         eapply qpend_absimp_set_errv_abt; pauto.
         eapply absinfer_eq.
         apply absabort_rule.
      }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpend_absimp_set_errv; pauto.
  eapply absinfer_eq.
  (* actual assign err *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AErrblkList).
  eapply err_list_split_frm; eauto.
  unfold node.
  hoare unfold.
  inverts H9; inverts H10.
  hoare forward.
  hoare_lifts_trms_pre (Aop, err).
  eapply assign_rule_deref_ptr.
  intros. sep get rv.
  simpl Astruct.
  split.
  introv Hsat. sep cancel (Aptrmapsto). eauto.
  intros; sep auto.
  intros; sep get rv.
  eapply eq_int; auto.
  intros. sep eexists. sep cancel p_local. simpl; auto.
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier.
  unfold EvtInv.
  sep pauto; eauto.
  trycancel_EvtInv.
  unfold AErrblkList.
  sep pauto.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eapply err_sllseg_merge with (vsem:= (v'45, Int.zero)) (errv:= (Int.repr OS_NO_ERR)) 
                                                                   (vl:= ((V$ OS_NO_ERR) :: v'40 :: nil)); eauto.
  sep cancel err_sllseg.
  sep cancel err_sllseg.
  unfold node.
  simpl Astruct.
  sep pauto; eauto.
  sep cancel (Aptrmapsto).
  sep cancel Aptrmapsto.
  eauto.
  eapply EbMod.my_joinsig_join_set; eauto.
  eapply my_joinsig_set; eauto.
  split; auto. go.
  rewrite EbMod.map_get_set; auto.
  auto.
  Optimize Proof.
  Optimize Heap.
  pure_auto.
  (* end of err *)
  simpl in Hptr_ls_ml.
  destruct Hptr_ls_ml as (Hptr_msg & _).
  destruct Hptr_msg as [Hmsg_eq | ((msg_b & msg_i) & Hmsg_eq)];
  rewrite Hmsg_eq;
  hoare forward.
  (* OSQEntries = 0 *)
  apply hoare_disj_afalseP_l_pre.
  hoare unfold.
  destruct (Int.ltu ($ 0) qentries) eqn: eq1;
  simpl in H38; destruct H38; tryfalse.
  assert (Hqen_zero: qentries = Int.zero /\ ml = nil).
  { clear -eq1 qentris.
     change ($ 0) with Int.zero in eq1.
     eapply ltu_zero_false_imp_eq_zero in eq1.
     subst.
     change (Int.unsigned Int.zero) with 0 in qentris.
     destruct ml; simpl length in qentris. auto.
     false.
   }
  destruct Hqen_zero. subst qentries; subst ml.
  (* OSTCBCur ′ .. OSTCBStat =ₑ OSTCBCur ′ .. OSTCBStat |ₑ ′ OS_STAT_Q;ₛ *)
  hoare forward.
  go.
  rewrite Hor.
  (* OSTCBCur ′ .. OSTCBDly =ₑ timeout ′;ₛ *)
  hoare forward.
  clear -Hvt_rgn. pure_auto.
  (* OS_EventTaskWait (­ pevent ′­);ₛ *)
  hoare_lifts_trms_pre (Aisr, Ais, A_isr_is_prop,aemp_isr_is).
  transform_pre a_isr_is_prop_split ltac:(idtac).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  (* fold AEventNode *)
  hoare_lifts_trms_pre (Astruct (v'39, Int.zero), OS_EVENT_TBL_SIZE, AOSPostEventTbl, evsllseg v'3, evsllseg x7).
  fold_AEventNode_r.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (OS_Q_FREEBLK, OS_MAX_Q_SIZE, Astruct (v'20, Int.zero)).
  eapply AEventNode_fold.
  sep cancel AOSEvent.
  instantiate(2:= (DMsgQ (Vptr (v'20, Int.zero)) 
           (x14
             :: x13
                :: x3
                   :: x8
                      :: x9
                         :: Vint32 n
                            :: Vint32 Int.zero :: Vptr (v'32, Int.zero) :: nil) (x15 :: x16 :: nil) v2)).
  simpl AEventData.
  unfold AMsgData.
  unfold AOSQCtr.
  unfold AOSQBlk.
  unfold node.
  sep pauto; eauto.
  unfolds; simpl; eauto.
  split; auto. go.
  split; auto. go.
  (* end of fold AEventNode *)
  hoare forward.
  sep cancel p_local.
  sep cancel AOSRdyTblGrp.
  sep cancel AEventNode.
  eapply node_fold; eauto.
  sep cancel OS_TCB_flag.
  eauto.
  go.
  unfold V_OSTCBPrio; simpl nth_val.
  repeat eexists; eauto.
  apply Int.eq_false; auto.
  eapply tcblist_p_node_rl; eauto.
  pure_auto.
  intro. sep auto.
  intro. sep auto.
  hoare unfold.
  inverts H58.
  inverts H76; inverts H77; inverts H78; inverts H83.
  rename v'52 into vy; rename v'53 into vbitx; rename v'54 into vbity.
  rename v'57 into egrp.
  rename v'44 into etbl; rename v'12 into rtbl.
  (* fold EvtInv_part2 *)
   eapply backward_rule1.
   introv Hsat.
   eapply fold_EvtInv_part2; eauto.
   sep pauto.
   trycancel_EvtInv.
   eauto.
  (* change absdata *)
   hoare_lifts_trms_pre (Aop, absecblist, abstcblist, ostm, oscurt, EvtInv_part2).
   eapply abscsq_rule.
   eapply noabs_oslinv.
   eapply qpend_high_step_block; eauto.
   pure_auto.
   eapply absinfer_eq.
  (*vt = Int.zero*)

   (* EXIT_CRITICAL;ₛ *)
   hoare_lifts_trms_pre (Aisr, Ais,Aier).
   transform_pre add_aemp_isr_is_prop ltac:(idtac).
   transform_pre add_a_isr_is_prop ltac:(idtac).
   lets Htcb_rl': Htcb_rl.
   funfold Htcb_rl'.

   hoare forward prim.
   get_hsat Hsat.
   sep cancel p_local.
   sep cancel Aier.
   sep cancel APthreadAttr.
  sep cancel CapabilityInv.
   sep_lifts_trms EvtInv.
   eapply fold_EvtInv_frm'.
   sep_lifts_trms EvtInv_part2.
   eapply evtinv_part2_set_tcbvl_mid_preserve; [idtac | sep cancel EvtInv_part2].
   eapply TCBList_P_Combine; eauto.
   sep_lifts_trms_in Hsat (dllseg v'4).
   eapply tcbdllseg_get_last_tcb_ptr; eauto.
   trycancel_EvtInv.
   cancel_corecommuinv.
   unfold AOSTCBPrioTbl in *.
   unfold AECBList.
   unfold AOSTCBList.
   unfold tcbdllseg.
   sep pauto; eauto.
   sep cancel (dllseg v'4).
   simpl dllseg at 1.
   simpl update_nth_val in Hsat.
   unfold V_OSTCBNext,V_OSTCBPrev.
   simpl nth_val.
   sep pauto.
   sep cancel OS_TCB_flag.
   sep cancel dllseg.
   eapply evsllseg_compose; eauto.
   2: { sep cancel AEventNode.
          sep cancel (evsllseg v'3).
          sep cancel evsllseg.
          sep lift 2%nat.
          eapply tcbdllflag_hold; [idtac | sep cancel tcbdllflag].
          eapply tcbdllflag_hold_middle.
          simpl; auto.
          cancel_partitioninv.
          eauto.
       }
    unfolds; simpl; eauto.
    eapply R_PrioTbl_P_hold1; eauto.
    eapply rtbl_remove_RL_RTbl_PrioTbl_P_hold; eauto.
    rewrite Int.repr_unsigned; auto.
    rewrite Int.repr_unsigned; auto.
    (* ECBList_P *)
    lets Hnewjoin: ecb_get_set_join_join Hget H37 H32.
    destruct Hnewjoin as (eml & Hjos' & Hjo').
    eapply msgqlist_p_compose_pend.
    6: eapply Hjos'.
    6: eapply Hjo'.
    eapply R_ECB_ETbl_P_high_tcb_block_hold ; eauto.
    eapply R_ECB_PETbl_P_high_tcb_block_hold''; eauto.
    introv Hf. destruct Hf as (qd & t & Hf). inverts Hf.
    introv Hf. destruct Hf as (qd & t & Hf). inverts Hf.
    eapply ECBList_P_high_tcb_block_hold; eauto.
    eapply joinsig_join_getnone; eauto.
    eapply ECBList_P_high_tcb_block_hold; eauto.
    eapply joinsig_get_none; eauto.
    { clear -Hcp .
       funfold Hcp.
       unfolds.
       splits; eauto.
       funfold H2.
       unfolds.
       split;intros;tryfalse;auto.
   }

   (* TCBList_P *)
   instantiate (1:= (set tls2 (v'42, Int.zero)
     (x0, wait (os_stat_q (v'39, Int.zero)) (if Int.eq vt Int.zero then None else Some vt), x19, false))).
  Focus.
  destruct (Int.eq vt Int.zero) eqn: Hvt.
    (*vt = Int.zero*)
  { apply semacc_int_eq_true in Hvt. 
   eapply TCBList_P_tcb_block_hold2; eauto.
   eapply TcbMod_join_impl_prio_neq_cur_r; eauto.
   eapply R_PrioTbl_P_impl_prio_neq_cur; eauto.
   }
   {    (*vt <> Int.zero*)
   apply semacc_int_eq_false in Hvt. 
   eapply TCBList_P_tcb_block_hold; eauto.
   eapply TcbMod_join_impl_prio_neq_cur_r; eauto.
   eapply R_PrioTbl_P_impl_prio_neq_cur; eauto.
   }
   Unfocus.
   
   eapply TCBList_P_tcb_block_hold' with (tcs:=tls2); eauto.
   eapply TcbMod_join_impl_prio_neq_cur_l; eauto.
   eapply R_PrioTbl_P_impl_prio_neq_cur; eauto.
   eapply TcbMod.join_set_r; eauto.
   eapply TcbMod.get_indom. eauto.
   (* RH_CurTCB *)
   eapply RH_CurTCB_high_block_hold; eauto.
   eapply RH_TCBList_ECBList_P_high_block_hold; eauto.

   pure_auto.

   (* OS_Sched (­);ₛ *)
   hoare forward.
  unfolds; auto.
  pure_auto.
  intro. sep auto. sep cancel p_local. simpl; auto.
  intro. sep auto. sep cancel p_local. simpl; auto.
  hoare unfold.
  inverts H38.

  (* ENTER_CRITICAL;ₛ *)
  clear -Hvt_rgn.
  hoare forward prim.
  hoare unfold.
  rename v'18 into vcspace.
  rename v'19 into v19. 
  rename v'21 into v21. 
  rename v'22 into v22.
  

  rename v'23 into v'18. 
  rename v'24 into v'19. 
  rename v'25 into v'21. 
  rename v'26 into v'22. 
  rename v'27 into v'23. 

  hoare forward.
  go.
  lets Hget_ct: Mbox_common.TCBListP_head_in_tcb H8.
  destruct Hget_ct as (cst & sus & Hget_ct).
  lets Hget_ct': Hget_ct.
  eapply TcbMod.join_get_r in Hget_ct; eauto.
  rename i3 into prio; rename x6 into msg.
  rename v'10 into tls.
  rename v'21 into tls1.
  rename v'22 into tls2.
  lets Htcb_rl: TCBList_P_imp_RL H8.
  simpl RL_TCBblk_P_List in Htcb_rl.
   destruct Htcb_rl as (Htcb_rl & _).
   assert (Hct_range: (Int.unsigned prio < 64)%Z).
  { eapply tcbblk_prio_range; eauto. }
    rename H13 into Hptr_msg.
  assert (Hcst_case: (cst = rdy /\ msg <> Vnull /\ sus = false \/ cst = wait (os_stat_q (v'39, Int.zero)) (Some Int.zero) /\ msg = Vnull /\ sus = false) \/
                               ~(cst = rdy /\ msg <> Vnull /\ sus = false \/ cst = wait (os_stat_q (v'39, Int.zero)) (Some Int.zero) /\ msg = Vnull /\ sus = false)  ) 
   by tauto.
  hoare_lifts_trms_pre (Aop, abtcblsid, curtid).
  destruct Hcst_case as [ Hcst_case | Habt].
  2: { eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpend_absimp_qpend_set_stat_abt; pauto.
  eapply absinfer_eq.
  apply absabort_rule.
   }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpend_absimp_qpend_set_stat; pauto.
  eapply absinfer_eq.

  (* If (message ′ !=ₑ NULL) *)
  hoare forward.
  apply isptr_zh; auto.
  pauto. pauto.
  instantiate (1:= Afalse).
  hoare unfold.
  destruct Hptr_msg as [Hmsg_eq | ((msg_b & msg_i) & Hmsg_eq)];
  subst msg; simpl in H2; try change (Int.notbool Int.one) with Int.zero in H2; tryfalse.
  destruct Hcst_case as [ (Hcst_eq & _ & Hsus_eq)| (_ & Hf & _)]; [idtac | tryfalse].
  subst cst. subst sus.
  assert (Hveq: x7 = Vnull /\ i4 = $ OS_STAT_RDY).
  {
    lets Hget_r: get_tcb_stat_rdy H8 Hget_ct'.
    unfold V_OSTCBStat,V_OSTCBEventPtr in Hget_r.
    simpl in Hget_r.
    clear -Hget_r.
    destruct Hget_r; pauto.
  }
  destruct Hveq as (Hvptr & Hvst). subst x7. subst i4.
  (* OSTCBCur ′ .. OSTCBMsg =ₑ 〈 (Void) ∗ 〉 NULL;ₛ *)
  hoare forward.
  (* OSTCBCur ′ .. OSTCBStat =ₑ ′ OS_STAT_RDY;ₛ *)
  hoare forward.
  (* OSTCBCur ′ .. OSTCBEventPtr =ₑ 〈 OS_EVENT ∗ 〉 NULL;ₛ *)
  hoare forward.
  (* change absdata *)
  assert (Hrv: rv = Vptr (msg_b, msg_i) \/ rv <> Vptr (msg_b, msg_i)) by tauto.
  hoare_lifts_trms_pre (Aop, abtcblsid, curtid).
  destruct Hrv.
  2:{ eapply abscsq_rule.
        apply noabs_oslinv.
        eapply qpend_absimp_qpend_block_get_abt; pauto.
        eapply absinfer_eq.
        apply absabort_rule.
    }
   subst rv.
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply qpend_absimp_qpend_block_get; pauto.
   eapply absinfer_eq.
  (* EXIT_CRITICAL;ₛ *)
  unfold EvtInv.
  hoare unfold.
  (* hoare_assert_pure (v'13 = vhold_addr).
  { get_hsat Hsat.
     unfold EvtInv in Hsat.
     sep normal in Hsat.
     sep destruct Hsat.
     sep split in Hsat.
     auto.
  }
  hoare_split_pure_all. subst. *)
  hoare forward prim.
  get_hsat Hsat.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep_lifts_trms EvtInv.
  eapply fold_EvtInv_frm'.
  sep_lifts_trms EvtInv_part2.
  eapply evtinv_part2_set_tcbvl_mid_preserve;
  [idtac | eapply fold_EvtInv_part2; eauto; trycancel_EvtInv].
  eapply TCBList_P_Combine; eauto.
  sep_lifts_trms_in Hsat (dllseg v'2).
  eapply tcbdllseg_get_last_tcb_ptr; eauto.
  unfold AOSTCBPrioTbl in *.
  unfold AECBList in *.
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel evsllseg.
  sep cancel (dllseg v'2).
  simpl dllseg at 1.
  unfold node.
  unfold V_OSTCBNext,V_OSTCBPrev.
  simpl nth_val.
  sep pauto; eauto.
  sep cancel OS_TCB_flag.
  sep cancel dllseg.
  eapply tcbdllflag_hold; [idtac | sep cancel tcbdllflag].
  eapply tcbdllflag_hold_middle.
  simpl; auto.
  eauto.
  split; auto. go.
  eapply r_priotbl_p_set_hold; eauto.
  eapply ECBList_P_high_tcb_get_msg_hold; eauto.
  eapply TCBList_P_tcb_msgvnull_hold;eauto.
  eauto.
  eapply TcbMod.join_set_r; eauto.
  eapply TcbMod.get_indom. eauto.
  eapply RH_CurTCB_high_get_msg_hold; eauto.
  eapply RH_TCBList_ECBList_P_high_get_vnull_hold; eauto.
  pure_auto.
  (* end of exit critical *)
  clear -Hvt_rgn.
  hoare forward prim.
  unfold EvtInv.
  hoare unfold.

  rename v'17 into vcspace.
  rename v'18 into v18. 
  rename v'19 into v19. 
  rename v'21 into v21.
  
  rename v'22 into v'17. 
  rename v'23 into v'18. 
  rename v'24 into v'19. 
  rename v'25 into v'21. 
  rename v'26 into v'22. 
  rename v'27 into v'23. 
  rename v'28 into v'24. 
  rename v'29 into v'25. 
  rename v'30 into v'26. 
  rename v'31 into v'27. 
  rename v'32 into v'28. 
  rename v'33 into v'29. 
  rename v'34 into v'30. 
  rename v'35 into v'31. 
  rename v'36 into v'32. 
  rename v'37 into v'33. 
  rename v'38 into v'34. 

  rename v'40 into v'35. 
  rename v'41 into v'36. 
  (* assign err *)
  rename v'34 into ebls.
  hoare_lifts_trms_pre (Aop, eblsid).
  destruct (get ebls errid) eqn: Hgeterr.
  2:{  eapply abscsq_rule.
         apply noabs_oslinv.
         eapply qpend_absimp_set_errv_abt; pauto.
         eapply absinfer_eq.
         apply absabort_rule.
      }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpend_absimp_set_errv; pauto.
  eapply absinfer_eq.
  (* actual assign err *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AErrblkList).
  eapply err_list_split_frm; eauto.
  unfold node.
  hoare unfold.
  inverts H9; inverts H10.
  hoare forward.
  hoare_lifts_trms_pre (Aop, err).
  eapply assign_rule_deref_ptr.
  intros. sep get rv.
  simpl Astruct.
  split.
  introv Hsat. sep cancel (Aptrmapsto). eauto.
  intros; sep auto.
  intros; sep get rv.
  eapply eq_int; auto.
  intros. sep eexists. sep cancel p_local. simpl; auto.
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier.
  unfold EvtInv.
  sep pauto; eauto.
  trycancel_EvtInv.
  unfold AErrblkList.
  sep pauto.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eapply err_sllseg_merge with (vsem:= (v'45, Int.zero)) (errv:= (Int.repr OS_NO_ERR)) 
                                                                   (vl:= ((V$ OS_NO_ERR) :: v'40 :: nil)); eauto.
  sep cancel err_sllseg.
  sep cancel err_sllseg.
  unfold node.
  simpl Astruct.
  sep pauto; eauto.
  sep cancel (Aptrmapsto).
  sep cancel Aptrmapsto.
  eauto.
  eapply EbMod.my_joinsig_join_set; eauto.
  eapply my_joinsig_set; eauto.
  split; auto. go.
  rewrite EbMod.map_get_set; auto.
  auto.
  Optimize Proof.
  Optimize Heap.
  pure_auto.
  (* end of err *)
  hoare forward.

  (* msg = Vnull , part of OS_TIMEOUT*)

  eapply hoare_disj_afalseP_l_pre.

  hoare unfold.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat EvtInv.
  eapply unfold_EvtInv_frm; eauto.
  unfold EvtInv_part1.
  hoare normal pre.
  hoare_ex_intro.
  destruct Hptr_msg as [Hmsg_eq | ((msg_b & msg_i) & Hmsg_eq)] ;
  subst msg; simpl in H2; try change (Int.notbool Int.zero) with Int.one in H2; destruct H2; tryfalse.
  destruct Hcst_case as [ (_ & Hf & _ )| ( Hcst_eq & _ & Hsus_eq )]; [ tryfalse | idtac].
  subst cst. subst sus.
  lets Hveq: get_tcb_stat_q_eq0 H8 Hget_ct'.
  specialize (Hveq (eq_refl _)).
  destruct Hveq as (Hstat_eq & Heptr_eq & Hdly_eq & Hpnin_rtbl). auto.
  inverts Hstat_eq; inverts Heptr_eq; inverts Hdly_eq.
  rename v'7 into rtbl.
  rename v'9 into els.
  lets Hrh_tls_els_q: H.
  destruct Hrh_tls_els_q as (Hrh_tls_els_q & _).
  lets Hget_e: Hget_ct.
  eapply Hrh_tls_els_q in Hget_e; eauto.
  destruct Hget_e as (ml & n & pwl & wl & Hget_e & Hinwl).
  unfold AECBList.
  hoare unfold.
  lets Hget_ectr: ECBList_P_get_ectr_some Hget_e H3.
  destruct Hget_ectr as (et & etbl & petbl & Hget_ectr).
  eapply backward_rule1.
  intros.
  eapply get_ectr_decompose; eauto.
  sep cancel evsllseg. eauto.
  hoare unfold.
  hoare_assert_pure (length v'22 = length v'25).
  { get_hsat Hsat. sep_lifts_trms_in Hsat (evsllseg v'7).
     eapply evsllseg_list_len_eq in Hsat; auto.
  }
  hoare_split_pure_all.
  lets Hels_split: ecblist_p_decompose_new H21 H23 H24 H3.
  simpljoin.
  lets Hels_p_right: H27.
  simpl ECBList_P at 1 in H27.
  simpljoin.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  hoare unfold.
  rename i3 into rgrp.

  (* OS_EventTO (­ pevent ′­);ₛ *)
  hoare_lifts_trms_pre (Aisr, Ais, aemp_isr_is).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  hoare forward.
  sep cancel p_local.
  sep cancel AEventNode.
  unfold node.
  sep pauto.
  sep cancel OS_TCB_flag.
  eauto.
  split; auto. go.
  simpl; auto.
  auto.
  pure_auto.
  intro. sep auto.
  intro. sep auto.
  hoare unfold.
  inverts H27.
  rename v'32 into vy; rename v'33 into vbitx; rename v'34 into vbity.
  inverts H42; inverts H43; inverts H44.

  hoare unfold.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, curtid,EvtInv_part2).
  assert (Hrv: rv = Vnull \/ rv <> Vnull) by tauto.
  destruct Hrv.
  2: {
         eapply abscsq_rule.
         eapply noabs_oslinv.
         eapply qpend_absimp_qpend_to_abt; eauto.
         can_change_aop_solver.
         eapply absinfer_eq.
         apply absabort_rule.
    }
   subst rv.
   eapply abscsq_rule.
   eapply noabs_oslinv.
   eapply qpend_absimp_qpend_to; eauto.
   can_change_aop_solver.
   eapply absinfer_eq.
   (* EXIT_CRITICAL;ₛ *)
   hoare_lifts_trms_pre (Aisr,Ais,Aier).
   transform_pre add_aemp_isr_is_prop ltac:(idtac).
   fold_AEventNode_r.
   hoare_lifts_trms_pre (Aop, EvtInv_part2).
   unfold node. (* AOSRdyGrp. *)
   hoare normal pre.
   hoare_ex_intro.

   hoare_split_pure_all.
   hoare forward prim.
   get_hsat Hsat.
   sep cancel p_local.
   sep cancel Aier.
   sep_lifts_trms EvtInv.
   eapply fold_EvtInv_frm'.
   sep_lifts_trms EvtInv_part2.
   eapply evtinv_part2_set_tcbvl_mid_preserve; [idtac | sep cancel EvtInv_part2].
   eapply TCBList_P_Combine; eauto.
   sep_lifts_trms_in Hsat (dllseg v'2).
   eapply tcbdllseg_get_last_tcb_ptr; eauto.
   trycancel_EvtInv.
   cancel_corecommuinv.
  unfold AOSTCBPrioTbl in *.
  unfold AECBList in *.
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel (dllseg v'2).
  simpl dllseg at 1.
  unfold node.
  unfold V_OSTCBNext,V_OSTCBPrev.
  simpl nth_val.
  sep pauto; eauto.
  sep cancel OS_TCB_flag. 
  sep cancel dllseg.
  eapply evsllseg_compose.
  4: {
  sep cancel AEventNode.
  sep cancel (evsllseg v'7).
  sep cancel evsllseg.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  sep pauto.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep lift 2%nat.
  eapply tcbdllflag_hold; [idtac | sep cancel tcbdllflag].
  eapply tcbdllflag_hold_middle.
  simpl; auto.
  cancel_partitioninv.
  eauto. 
  pure_auto.
  }
  unfold V_OSEventListPtr.
  eapply nth_upd_neqrev; try pauto.
  eauto. 
  eauto. 
  split; auto. go.
  eapply r_priotbl_p_set_hold; eauto.
  eauto.
  (* ECBList_P *)
  assert (Hyx_eq: vy = prio >>ᵢ $ 3 /\ vbitx = $ 1<<ᵢ(prio&ᵢ$ 7)).
  {
    lets cp : H8. 
    destruct H8 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
    destruct asbs'.
    destruct p.
    destruct p.
    destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
    funfold Hrsl'.
    split; auto.
  }
  destruct Hyx_eq as (Hy_eq & Hbx_eq).
  subst vy. subst vbitx.
  eapply ECBList_P_hold_for_update_q_to_rdy'; try eauto.
  (* end of ECBList_P *)
  (* first TCBList_P *) 
    assert (Hyx_eq: vy = prio >>ᵢ $ 3 /\ vbitx = $ 1<<ᵢ(prio&ᵢ$ 7)).
  {
    lets cp : H8. 
    destruct H8 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
    destruct asbs'.
    destruct p.
    destruct p.
    destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
    funfold Hrsl'.
    split; auto.
  }
    destruct Hyx_eq as (Hy_eq & Hbx_eq).
    subst vy. subst vbitx.
    asserts_rewrite (
        (v'23 :: v'18 :: Vnull :: Vnull :: Vint32 Int.zero :: V$ OS_STAT_RDY  :: Vint32 prio
              :: Vint32 i2 :: Vint32 (prio >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(prio&ᵢ$ 7)) :: Vint32 vbity :: nil) =
        update_nth_val 5 (
                         update_nth_val 2
                                        (v'23 :: v'18 :: Vptr (v'39, Int.zero) :: Vnull :: Vint32 Int.zero :: V$ OS_STAT_Q  :: Vint32 prio
                                           :: Vint32 i2 :: Vint32 (prio >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(prio&ᵢ$ 7)) :: Vint32 vbity :: nil)
                                        Vnull) (V$ OS_STAT_RDY)).  
    { simpl. auto. }
    eapply TCBList_P_hold_for_update_rdy with ( prio :=prio) ;eauto.
    split; auto.  apply Int.unsigned_range_2. 
    eauto.
    (*sencond TCBList_P *)
    (* join ... *)
    destruct H8 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
    inverts Hveq'.
    unfold TcbJoin in Htcj'.
    unfold TcbMod.joinsig.
    unfold join,sig,TcbMap in Htcj'.
    eapply TcbMod.joinsig_set_set; try eauto.
    (* RH_CurTCB *)
    unfold RH_CurTCB.
    rewrite TcbMod.map_get_set.
    eauto.
  (* RH_TCBList_ECBList_P *)
  eapply RH_TCBList_ECBList_P_hold_for_q_to_rdy; try eauto.

  pure_auto.

  (* end of exit critical *)
  clear -Hvt_rgn.
  hoare forward prim.
  unfold EvtInv.
  hoare unfold.

  rename v'16 into vcspace.
  rename v'17 into v17. 
  rename v'18 into v18. 
  rename v'19 into v19.
  rename v'21 into v'16.  
  rename v'22 into v'17. 
  rename v'23 into v'18. 
  rename v'24 into v'19. 
  rename v'25 into v'21. 
  rename v'26 into v'22. 
  rename v'27 into v'23. 
  rename v'28 into v'24. 
  rename v'29 into v'25. 
  rename v'30 into v'26. 
  rename v'31 into v'27. 
  rename v'32 into v'28. 
  rename v'33 into v'29. 
  rename v'34 into v'30. 
  rename v'35 into v'31. 
  rename v'36 into v'32. 
  rename v'37 into v'33. 
  rename v'38 into v'34. 

  rename v'40 into v'35. 

  (* assign err *)
  rename v'33 into ebls.
  hoare_lifts_trms_pre (Aop, eblsid).
  destruct (get ebls errid) eqn: Hgeterr.
  2:{  eapply abscsq_rule.
       apply noabs_oslinv.
       eapply qpend_absimp_set_errv_abt; pauto.
       eapply absinfer_eq.
       apply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpend_absimp_set_errv; pauto.
  eapply absinfer_eq.
  (* actual assign err *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AErrblkList).
  eapply err_list_split_frm; eauto.
  unfold node.
  hoare unfold.
  inverts H9; inverts H10.
  hoare forward.
  hoare_lifts_trms_pre (Aop, err).
  eapply assign_rule_deref_ptr.
  intros. sep get rv.
  simpl Astruct.
  split.
  introv Hsat. sep cancel (Aptrmapsto). eauto.
  intros; sep auto.
  intros; sep get rv.
  eapply eq_int; auto.
  intros. sep eexists. sep cancel p_local. simpl; auto.
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier.
  unfold EvtInv.
  sep pauto; eauto.
  trycancel_EvtInv.
  unfold AErrblkList.
  sep pauto.
  eapply err_sllseg_merge with (vsem:= (v'45, Int.zero)) (errv:= (Int.repr OS_TIMEOUT)) 
                                                                   (vl:= ((V$ OS_TIMEOUT) :: v'38 :: nil)); eauto.
  sep cancel err_sllseg.
  sep cancel err_sllseg.
  unfold node.
  simpl Astruct.
  sep pauto; eauto.
  sep cancel (Aptrmapsto).
  sep cancel Aptrmapsto.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.
  eapply EbMod.my_joinsig_join_set; eauto.
  eapply my_joinsig_set; eauto.
  split; auto. go.
  rewrite EbMod.map_get_set; auto.
  auto.
  Optimize Proof.
  Optimize Heap.
  pure_auto.
  (* end of err *)
  hoare forward.
  Unshelve.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  exact (1%positive, Int.zero).
  trivial.
  trivial.
  exact (1%positive, Int.zero).
  Qed.

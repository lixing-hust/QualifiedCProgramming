Require Import os_q.
Require Import abs_op.
Require Import oscore_common. 
Require Import go.

Require Import OSEventTaskRdyPure. 
Require Import OSTimeTickPure.
Require Import OSQPostPure.
Require Import OSQPostPure_ext.
Require Import new_inv.
Require Import tcblist_setnode_lemmas. 
Require Import sem_lab.
Require Import Lia.

Require Import abs_infer_step.
Require Import ucos_frmaop.

Require Import evauxvar_lemmas.
Require Import evaux_pure.
Require Import freeevtlist_lemmas.
Require Import seplog_trm_tacs.
Require Import abs_infer_abt.

Require Import q_common.
Require Import sem_common.
Require Import gjb_q_common.

Require Import evtinv_lemmas.
Require Import hoare_assign_tac_ext.


Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import os_ucos_h.

Require Import sempend_pure.
Require Import sempost_pure.

Require Import gjb_sem_common. 
Require Import gjb_common.
(* Require Import OSIntExitIntPure. *)

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.

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
    lzh_hoare_unfold;
    hoare forward; 
    match goal with
      | |- {|_, _, _, _, _, _|} |- ?ct {{?p ** [|?v <> Vint32 Int.zero /\
                                         ?v <> Vnull /\
                                         ?v <> Vundef|]}} ?stmts {{_}} =>
        (* ** ac: idtac "if block proof"; *)
        let x := lzh_find_ret_stmt stmts in
          match x with
            | some _ => instantiate (1:=Afalse)
            | none _ => idtac
          end;
        hoare_split_pure_all;
        lzh_val_inj_simpl; tryfalse
  
      | |- {|_, _, _, _, _, _|} |- ?ct {{_}} _ {{_}} => 
        (* ** ac: idtac "if all"; *)
        hoare forward;
        hoare_split_pure_all;
        lzh_val_inj_simpl; tryfalse
        (* first proof if-true condition, then proof if-false condition *)
      | _ => pauto
    end.

Lemma absinfer_seq1:
forall (p : asrt) (s1 : absop)  (s2 : spec_code) (s1' : absop) (sc : ossched),
                  can_change_aop p ->
                  sc ⊢  <|| s1 ||>  ** p ⇒  <|| s1' ||>  ** p ->
                  sc ⊢  <|| s1;; s2 ||>  ** p ⇒  <|| s1';; s2 ||>  ** p.
Proof.
  intros.
  eapply absinfer_seq; try eauto.
Qed.

(* 指针为空，但返回值正确 *)
Lemma qpost_ipc_absinfer_null:
  forall qid v_msg v' P sch s,
    qid = Vnull ->
    v' = V$ OS_ERR_PEVENT_NULL ->
    can_change_aop P -> 
    absinfer sch
       ( <|| spec_code_cons (ipcqpost (qid :: v_msg :: v' :: nil)) s ||> ** P) 
       ( <|| s ||> ** P ).
Proof.
  intros.
  simpl.
  subst.
  infer_solver 0%nat.
Qed.

(* 指针为空，但是返回值不对 *)
Lemma qpost_ipc_absinfer_null_abt:
  forall  qid v_msg v' P sch s,
  qid = Vnull ->
   v' <> V$ OS_ERR_PEVENT_NULL ->
   can_change_aop P -> 
   absinfer sch
       ( <|| spec_code_cons (ipcqpost (qid :: v_msg :: v' :: nil)) s ||> ** P)
       ( <|| ABORT ||> ** P ).
Proof.
  intros.
  simpl.
  eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
Qed.

(* 与下面的一致，msg为空的情况 *)
Lemma qpost_ipc_absinfer_msg_null:
  forall qid  v' P sch s,
    v' = V$ OS_ERR_POST_NULL_PTR ->
    can_change_aop P -> 
    absinfer sch
       ( <|| spec_code_cons (ipcqpost (Vptr qid :: Vnull :: v' :: nil)) s ||> ** P) 
       ( <|| s ||> ** P ).

Proof.
  introv  Hv' Hcop.
  eapply absinfer_trans. 
  simpl.
  eapply absinfer_choice2; try eauto.
  eapply absinfer_trans.
  eapply absinfer_choice1; try eauto.
  eapply absinfer_trans.
  
  eapply absinfer_seq1. pure_auto.
  instantiate (1:=END (Some (Vint32 (Int.repr OS_ERR_POST_NULL_PTR)))).
  infer_solver 0%nat. 
  eapply absinfer_seq_end; try pure_auto.
Qed.

Lemma qpost_ipc_absinfer_msg_null':
  forall qid  v' P sch s,
    v' = V$ OS_ERR_POST_NULL_PTR ->
    can_change_aop P -> 
    absinfer sch
       ( <|| spec_code_cons (ipcqpost (Vptr qid :: Vnull :: v' :: nil)) s ||> ** P) 
       ( <|| s ||> ** P ).
Proof.
  introv Hv' Hcop.
  simpl.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  3: eauto. pure_auto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  3: eauto. pure_auto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_seq1. pure_auto.
  instantiate (1:=END (Some (Vint32 (Int.repr OS_ERR_POST_NULL_PTR)))).
  infer_solver 0%nat.
  eapply absinfer_seq_end;try( pure_auto). 
Qed.

(* msg为空，但是返回值不对 *)
Lemma qpost_ipc_absinfer_msg_null_abt:
  forall qid  v' P sch s,
    v' <> V$ OS_ERR_POST_NULL_PTR ->
    can_change_aop P -> 
    absinfer sch
       ( <|| spec_code_cons (ipcqpost (Vptr qid :: Vnull :: v' :: nil)) s ||> ** P) 
       ( <|| ABORT ||> ** P ).

Proof.
  introv  Hv' Hcop.
  eapply absinfer_trans. 
  simpl.
  eapply absinfer_choice2; try eauto.
  eapply absinfer_trans.
  eapply absinfer_choice1; try eauto.
  eapply absinfer_trans.
  
  eapply absinfer_seq1. pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  eapply absinfer_seq_abt; try pure_auto.
Qed.

(* 类型不对，返回值对 *)
Lemma qpost_ipc_absinfer_type_err:
  forall P mqls x v_msg v' sch s, 
    can_change_aop P ->  
    v' = V$ OS_ERR_EVENT_TYPE ->  
    (~ exists a b pwl wl, get mqls x = Some  (absmsgq a b pwl, wl) ) ->
    absinfer sch
      ( <|| spec_code_cons (ipcqpost (Vptr x :: v_msg :: v' :: nil)) s ||>  ** 
            HECBList mqls ** P) 
      (<|| s ||>  ** HECBList mqls ** P).
Proof.
  introv Hcop Hv' Hnoq.
  eapply absinfer_trans. simpl.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.

  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto. 2 :eauto. pauto.
  infer_solver 0%nat. 
  
Qed.

(* 类型不对，返回值也不对 *)
Lemma qpost_ipc_absinfer_type_err_abt:
  forall P mqls x v_msg v' sch s, 
    can_change_aop P ->  
    v' <> V$ OS_ERR_EVENT_TYPE ->  
    ( ~ exists a b pwl wl, get mqls x = Some (absmsgq a b pwl, wl)) ->
    absinfer sch
      ( <|| spec_code_cons (ipcqpost (Vptr x :: v_msg :: v' :: nil)) s ||>  ** 
            HECBList mqls ** P) 
      (<|| ABORT ||>  ** HECBList mqls ** P).
Proof.
  introv Hcop Hv' Hnoq.
  simpl.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.

  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto. 2 :eauto. pauto.
  
  eapply absinfer_trans.
  eapply absinfer_seq1. pure_auto.
  
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver. pauto.
  eapply absinfer_seq_abt; try pure_auto.
Qed.

(* 事件数大于size *)
Lemma qpost_ipc_absinfer_ovf:
  forall P mqls x v_msg v'  a b pwl wl sch s, 
    can_change_aop P ->  
    v' = V$ MSGQ_OVF_ERR ->  
    EcbMod.get mqls x = Some (absmsgq a b pwl, wl) ->
    Z.ge (Z_of_nat (length a)) (Int.unsigned b) ->
    absinfer sch
      ( <|| spec_code_cons (ipcqpost (Vptr x :: v_msg :: v' :: nil)) s ||>  **  
            HECBList mqls ** P) 
      (<|| s ||>  ** HECBList mqls ** P).
Proof.
  introv Hcop Hv' Hq Hlength.
  eapply absinfer_trans. simpl.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto. 2 :eauto. pauto.
  infer_solver 0%nat. 
Qed.


Lemma qpost_ipc_absinfer_ovf_abt:
  forall P mqls x v_msg v'  a b pwl wl sch s, 
    can_change_aop P ->  
    v' <> V$ MSGQ_OVF_ERR ->  
    EcbMod.get mqls x = Some (absmsgq a b pwl, wl) ->
    Z.ge (Z_of_nat (length a)) (Int.unsigned b) ->
    absinfer sch
      ( <|| spec_code_cons ( ipcqpost (Vptr x :: v_msg :: v' :: nil)) s ||>  ** 
            HECBList mqls ** P) 
      (<|| ABORT ||>  ** HECBList mqls ** P).
Proof.
  introv Hcop Hv' Hq Hlength.
  eapply absinfer_trans. simpl.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto. 2 :eauto. pauto.
  
  eapply absinfer_trans.
  eapply absinfer_seq1. pure_auto.
  
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver. pauto.
  eapply absinfer_seq_abt; try pure_auto.
Qed.

(* 不存在等待任务 *)
Lemma qpost_ipc_absinfer_nowt_succ: 
  forall P mqls x v_msg v' a b pwl tcbls t ct sch s tcblh tcbvl vhold v1 v2 v3, 
    can_change_aop P ->  
    v' = V$ OS_NO_ERR ->
    EcbMod.get mqls x = Some (absmsgq a b pwl,nil) ->
    Z.lt (Z_of_nat (length a)) (Int.unsigned b) ->
    absinfer sch
          ( <|| spec_code_cons ( ipcqpost (Vptr x :: v_msg :: v' :: nil)) s ||>  **
            HECBList mqls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** 
            EvtInv_part2 mqls tcblh tcbvl vhold v1 v2 v3 **P) 
          (<||  s ||>  **
            HECBList (EcbMod.set mqls x (absmsgq (a++(v_msg::nil)) b pwl,nil))** HTCBList tcbls ** HTime t ** HCurTCB ct **
            EvtInv_part2 (EcbMod.set mqls x (absmsgq (a++(v_msg::nil)) b pwl,nil) ) tcblh tcbvl vhold v1 v2 v3 ** P).
Proof.
  introv Hcop Hv' Hq Hlength.
  eapply absinfer_trans. simpl.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.

  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto. 2 :eauto. pauto.
  infer_solver 0%nat.
  
    {
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
  } 
Qed.

Lemma qpost_ipc_absinfer_nowt_succ_abt: 
  forall P mqls x v_msg v' a b pwl tcbls t ct sch s, 
    can_change_aop P ->  
    v' <> V$ OS_NO_ERR ->
    EcbMod.get mqls x = Some (absmsgq a b pwl,nil) ->
    Z.lt (Z_of_nat (length a)) (Int.unsigned b) ->
    absinfer sch
          ( <|| spec_code_cons ( ipcqpost (Vptr x :: v_msg :: v' :: nil)) s ||>  **
            HECBList mqls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P) 
          (<||  ABORT ||>  **
            HECBList mqls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  introv Hcop Hv' Hq Hlength.
  eapply absinfer_trans. simpl.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pauto.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto. 2 :eauto. pauto.
  eapply absinfer_trans.
  eapply absinfer_seq1. pure_auto.
  
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver. pauto.
  eapply absinfer_seq_abt; try pure_auto.

Qed.

Lemma qpost_ipc_absinfer_exwt_succ: 
  forall P mqls x v_msg v' vl n pwl wl tls t ct p st m t'  sch s tcblh tcbvl vhold v1 v2 v3 sus, 
    can_change_aop P ->  
    v' = V$ OS_NO_ERR ->
    get mqls x = Some (absmsgq vl n pwl,wl) ->
    ~ wl=nil ->
    GetHWait tls wl t' ->
    get tls t' = Some (p,st,m, sus) ->
    absinfer sch
          ( <|| spec_code_cons ( ipcqpost ( (Vptr x) :: v_msg :: v' :: nil)) s ||>  **
            HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** 
            EvtInv_part2 mqls tcblh tcbvl vhold v1 v2 v3 **P) 
      (<|| END Some (Vint32 (Int.repr OS_NO_ERR)) ;; s ||>  ** 
            HECBList (EcbMod.set mqls x (absmsgq nil n pwl, (remove_tid t' wl) ) ) **
            HTCBList (TcbMod.set tls t' (p,rdy ,v_msg, sus) ) ** HTime t ** HCurTCB ct **
            EvtInv_part2 (EcbMod.set mqls x (absmsgq nil n pwl, (remove_tid t' wl) ) ) tcblh tcbvl vhold v1 v2 v3 **  P).
Proof.
  introv Hcop Hv' Hq Hwl Hhw Htlsget .
  simpl.
  do 5 (
       eapply absinfer_trans; 
       [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ]
   ).

  eapply absinfer_trans.
  2:{ eapply absinfer_seq_end; [idtac | idtac | eauto]; pure_auto. }
  eapply absinfer_seq; pure_auto.
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
Qed.

Lemma qpost_ipc_absinfer_exwt_abt: 
  forall P mqls x v_msg v' vl n pwl wl tls sch s, 
    can_change_aop P ->  
    v' <> V$ OS_NO_ERR ->
    get mqls x = Some (absmsgq vl n pwl,wl) ->
    ~ wl=nil ->
    absinfer sch
          ( <|| spec_code_cons ( ipcqpost ( (Vptr x) :: v_msg :: v' :: nil)) s ||>  **
            HECBList mqls ** HTCBList tls **  P) 
      (<|| ABORT ||>  ** 
            HECBList mqls ** HTCBList tls **  P).
Proof.
  introv Hcop Hv' Hq Hwl.
  simpl.
  do 5 (
       eapply absinfer_trans; 
       [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ]
   ).
  eapply absinfer_trans.
  eapply absinfer_seq1. pure_auto.
  eapply absinfer_choice2; try pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1. pure_auto. 
  eapply absinfer_abt; pure_auto.
  absimp_abt_solver. 
  can_change_aop_solver.
  eapply absinfer_seq_abt; try pure_auto. 
Qed.

Lemma good_frm_p_local:
forall ct lg,
  GoodFrm (p_local OSLInv ct lg).
Proof.
  intros.
  unfold p_local.
  unfold LINV,CurTid.
  unfold OSLInv.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_p_local : good_frm_lemmas.

Lemma add_a_isr_is_prop':
  forall P isr is,
   isr_is_prop isr is -> 
  Aisr isr ** Ais is ** P ==> Aisr isr ** Ais is ** A_isr_is_prop ** P.
Proof.
  intros.
  unfold A_isr_is_prop.
  sep normal.
  sep auto.
Qed.

Ltac hoare_enter_critical2 :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- {|_ , _, ?li , _, _, _|}|-_ {{?P}} (sprim encrit) {{_}} =>
        hoare_lifts_trms_pre (Aop, Aisr, Aier, Aie, Ais, Acs);
        eapply encrit2_rule';
        [ eauto
          | apply GoodI_I
          | good_frm_sovler;
            try (unfold GoodFrm; fold GoodFrm);
            do 3 try (splits; try intros; try tauto);
            try good_frm_sovler
          ]
  end.

Ltac hoare_exit_critical2 :=
  match goal with
    | |- {|_ , _, ?li , _, _, _|}|- _ {{?P}} (sprim excrit) {{_}} =>
          hoare_lifts_trms_pre (Aop, Aisr, Aier, Aie, Ais, Acs);
            eapply excrit2_rule';
            [ eauto
            | apply GoodI_I
            | good_frm_sovler;
            try (unfold GoodFrm; fold GoodFrm);
            do 3 try (splits; try intros; try tauto);
            try good_frm_sovler
            ]
  end.


Open Scope int_scope.
Open Scope code_scope.
Open Scope Z_scope.
Require Import hoare_forward_tac_ext.
Lemma OSIPCQPostProof: 
  forall vl p r logicl ct, 
    Some p =
    BuildPreI os_internal OSIPCQPost vl logicl OSIPCQPostPre ct->
    Some r =
    BuildRetI os_internal OSIPCQPost vl logicl OSIPCQPostPost ct->
    exists t d1 d2 s,
      os_internal OSIPCQPost = Some (t, d1, d2, s) /\
      {|OS_spec , GetHPrio, OSLInv, I, r, Afalse |}|-ct {{p}}s {{Afalse}}.
Proof.
  init_spec.
  rename v'4 into is.
  rename v'5 into isr.
  rename v'6 into ier.
  rename v'7 into vnest.
  rename v'8 into vlock.
  rename H3 into Hvnest.
  hoare_lifts_trms_pre (Aisr, Ais, A_isr_is_prop).
  transform_pre a_isr_is_prop_split ltac:(sep cancel Aisr; sep cancel Ais).
  (* ENTER_CRITICAL *)
  eapply seq_rule.
  hoare_enter_critical2.
  (* If (pevent ′ ==ₑ NULL) *)
  lzh_hoare_if2.
  subst.
  (* EXIT_CRITICAL *)
  eapply seq_rule.
  hoare_exit_critical2.

  (* 处理了一些数据 *)
  (* RETURN ′ OS_ERR_PEVENT_NULL *)
  hoare_lifts_trms_pre logicl.
  eapply backward_rule1.
  introv Hsat.
  (* s |= ?p *)
  eapply disj_star_elim_disj; eauto.
  hoare forward.
  2: { hoare_split_pure_all. tryfalse. }
  hoare_split_pure_all; subst.

  assert (Hor: v'3 <> (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) \/ 
  v'3 = (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) by tauto.
  inversion Hor.

  (* v'3 <> ... *) 
  eapply abscsq_rule.
  (* NoAbs OSLInv *)
  eapply noabs_oslinv.
  (*_ |-Aop... *)
  eapply qpost_ipc_absinfer_null_abt; eauto.
  (* can_change_aop *)
  can_change_aop_solver.
  (* GetHPrio ⊢ ?q ⇒ Afalse *)
  eapply absinfer_eq.
  (* <|| ABORT ||> *)
  eapply absabort_rule.

  (* v'3 = ... *)
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply qpost_ipc_absinfer_null; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq.
  (* return in case pevent = NULL *)
  hoare_lifts_trms_pre (Aisr, Ais).
  transform_pre add_a_isr_is_prop' ltac:(idtac).
  hoare forward.
  eapply adisj_intro; left.
  (* instantiate (1:=(V$ OS_ERR_PEVENT_NULL)). *)
  (* H0 |= [ ]**[]...    有H0 |= Aemp *)
  sep auto.
  splits; eauto.
  unfold OS_ERR_PEVENT_NULL.
  int auto.
  rewrite byte_max_unsigned_val.
  auto with zarith.

  (* 进入msg=v'9=null的判断，好像是先处理退临界区 *)
  (* If (message ′ ==ₑ NULL) *)
  lzh_hoare_if2.
  (* 替换 v'9 = Vnull *)
  subst. 
  eapply seq_rule.
  (* EXIT_CRITICAL *)
  hoare_exit_critical2.

  hoare_lifts_trms_pre logicl.
  eapply backward_rule1.
  introv Hsat.
  eapply disj_star_elim_disj; eauto.
  hoare forward.
  hoare_split_pure_all. tryfalse.
  (* hoare_split_pure_all; subst. *)
  
  assert (Hor: v'3 <> (Vint32 (Int.repr OS_ERR_POST_NULL_PTR)) \/ 
                v'3 = (Vint32 (Int.repr OS_ERR_POST_NULL_PTR))) by tauto.
  inversion Hor.
  (* v'3 <> ... *) 
  hoare_lifts_trms_pre Aop. 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpost_ipc_absinfer_msg_null_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule.

  (* v'3 = ... *)
  hoare_lifts_trms_pre Aop. 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpost_ipc_absinfer_msg_null.
  (* v'3 = V$ OS_ERR_POST_NULL_PTR *)
  pure_auto. 
  can_change_aop_solver.
  eapply absinfer_eq.
  (* return in case msg = NULL *)
  hoare_lifts_trms_pre (Aisr, Ais).
  transform_pre add_a_isr_is_prop' ltac:(idtac).
  hoare_split_pure_all; subst.
  hoare forward.
  (* right有点不一样 *)
  eapply adisj_intro; right.
  sep auto.
  pure_auto.
  (* 替换 *)
  inverts H0.
  (* exists d, EcbMod.get v'4 v'2 = Some d *)
  exists x0.
  eauto.
  (* 结束msg的分支 *)
  splits; eauto.
  unfold OS_ERR_PEVENT_NULL.
  int auto.
  rewrite byte_max_unsigned_val.
  auto with zarith.
  unfold OS_ERR_POST_NULL_PTR.
  auto with zarith.
  unfold OS_ERR_POST_NULL_PTR.
  auto with zarith.

  (* 好像是去掉待证目标中\\//中为空的那个分支 *)
  hoare_lifts_trms_pre logicl.
  eapply backward_rule1.
  introv Hsat.
  eapply disj_star_elim_disj; eauto.
  hoare forward.
  hoare_split_pure_all. tryfalse.
  hoare unfold. (*将一些变量替换为形如v1这种形式*)

  rename v'12 into v12.
  rename v'13 into v13.
  rename v'14 into v14.
  rename v'15 into v'12. 
  rename v'16 into v'13. 
  rename v'17 into v'14. 
  rename v'18 into v'15. 
  rename v'19 into v'16. 
  rename v'20 into v'17. 

  rename v'4 into els.
  hoare_lifts_trms_pre EvtInv.
  eapply backward_rule1.
  introv Hsat.
  eapply unfold_EvtInv_frm in Hsat; eauto.
  unfold EvtInv_part1.
  unfold AECBList.
  hoare unfold.

  (* pevent points to an active ECB *) 
  rename H into H_elp. (* ECBList_P ... *)  
  rename H0 into Hgetecb; rename x1 into ecb.
  destruct ecb as (d & wls).
  lets Hctr: ECBList_P_get_ectr_some Hgetecb H_elp.
  destruct Hctr as (evl & etbl & petbl & Hgetectr).

  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat evsllseg.
  (* s |= ?p 不一样 *)
  eapply get_ectr_decompose; eauto.
  hoare unfold.

  (* 链表里面的长度相等  evsllseg   hoare_assert_pure把他放进|- ct后当作纯断言，可能是与下面的evsllseg有关，才用 *)
  hoare_assert_pure (length v'23 = length v'25). 
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
  rename v'32 into pblk.

  hoare_assert_pure (x' = Vptr (pblk, Int.zero)).
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg. 
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  hoare_split_pure_all; subst. 

  assert (Hecbl' := Hecbl2).
  (* do 2 (rewrite ele_lst_cons in Hecbl').  *)
  unfold ECBList_P in Hecbl'.
  fold ECBList_P in Hecbl'.
  destruct Hecbl' as (qid & Hqid & Hecbetbl & Hex).
  inverts Hqid. 
  destruct Hex as (Hrpetbl & absmq & mqls' & v'' & Helptr & Hjo' & Hrlh & Hecbl20).
  unfold V_OSEventListPtr in Helptr.
  inverts Helptr.

  lzh_hoare_if.
  pure_auto.
  pure_auto.

  hoare_assert_pure ( ~ exists x y pwl wls, get els (pblk, Int.zero) = Some (absmsgq x y pwl, wls)).
  { 
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply eventtype_neq_q in Hsat; eauto.
    sep split in Hsat.
    auto.
  }

  hoare_split_pure_all.
  assert (Hnq: ~ (exists x y pwl wls0, (d, wls) = (absmsgq x y pwl, wls0))).
  {
    unfold get, EcbMap in H.
    rewrite Hgetecb in H.
    clear -H. introv He. simpljoin.
    eapply H; eauto.
  }




  hoare_lifts_trms_pre (Aop, absecblsid).
  rename v'3 into etype. 
  casetac etype (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) Heeq Hene.
  2: {
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply qpost_ipc_absinfer_type_err_abt; eauto.
    go.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpost_ipc_absinfer_type_err; eauto.  
  go.
  eapply absinfer_eq.

  fold_AEventNode_r.
  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_part1.
  trycancel_EvtInv1.
  eapply AECBList_fold; eauto.
  eapply lzh_evsllseg_compose; eauto.
  sep cancel AEventNode.
  sep cancel evsllseg.
  sep cancel evsllseg.
  sep cancel OSEventList.
  eauto.
  unfolds; simpl; eauto.

  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_frm;eauto.
  sep cancel EvtInv_part1.
  sep cancel EvtInv_part2.
  eauto.

  (* EXIT_CRITICAL *)
  eapply seq_rule.
  hoare_exit_critical2.
  (* return OS_ERR_EVENT_TYPE *)
  hoare_lifts_trms_pre (Aisr, Ais).
  transform_pre add_a_isr_is_prop' ltac:(idtac).
  hoare forward.
  eapply adisj_intro; right.
  sep pauto.
  right. eauto.  (*多了一层\/的分支*)
  left. eauto. splits; eauto.
  eauto.
  splits; eauto.
  unfold OS_ERR_PEVENT_NULL.
  int auto.
  rewrite byte_max_unsigned_val.
  auto with zarith.
  unfold OS_ERR_EVENT_TYPE.
  auto with zarith.
  unfold OS_EVENT_TYPE_Q.
  auto with zarith.
  unfold OS_ERR_EVENT_TYPE.
  auto with zarith.

  (* the concrete type is OS_EVENT_TYPE_Q *)
  apply semacc_int_eq_true in Hif_false. 
  subst.
  hoare_assert_pure (exists osq osqblk msgtbl, v'27 = DMsgQ x1 osq osqblk msgtbl ).
  {
    get_hsat Hsat. 
    unfold AEventData in Hsat.
    destruct v'27; sep split in Hsat.
    match goal with H: V_OSEventPtr _ = _ |- _ => unfold V_OSEventPtr in H; simpl in H; inverts H end. 
    do 3 eexists; eauto.
    inverts H. inverts H. inverts H. inverts H.
  }

  hoare_split_pure_all.

  assert (Habsev: get els (pblk, Int.zero) = Some absmq).
  {
    assert (Hpre: join (sig (pblk, Int.zero) absmq) mqls' els2) by join auto. 
    eapply join_sig_get in Hpre; eauto. 
    eapply join_get_r; eauto. 
  }
  assert (absmq = (d, wls)).
  {
    unfold get in Habsev. unfold EcbMap in Habsev. 
    
    rewrite Hgetecb in Habsev.
    inverts Habsev. auto. 
  }
  hoare_assert_pure ( (exists x y pwl wls0, (d, wls) = (absmsgq x y pwl, wls0))).
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply ecbmod_absmsgq. 
    rewrite H in Hrlh. 
    rewrite H0 in Hrlh.
    apply Hrlh.
  }
  (* hoare_assert_pure (exists wls, v'27 = DSem i2 /\ absmq = (abssem i2, wls)).  
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply semacc_triangle_sem in Hsat; eauto.
    2: go. 
    sep split in Hsat.
    auto.
  } *)
  hoare_split_pure_all.
  subst.

  hoare_unfold.
  lzh_hoare_if2.

  (* =================        pq′ =ₑ pevent′→OSEventPtr;ₛ
          If (pq′→OSQEntries ≥ pq′→OSQSize) {   ============================= *)
  (* 先处理后面的，即先跳过这个if分支 *)
  Focus 2.
  (* ===============qpost的证明方法，但是还是少EcbMod.get els (pblk, Int.zero) =
  ========================== *)

  (* pq′ =ₑ pevent′→OSEventPtr;ₛ *)
  hoare forward. 
  struct_type_match_solver. (*pure_auto. *) 
  (* 处理if分支 *)
  unfold AEventData.
  hoare unfold.
  hoare forward;pure_auto.
  instantiate (1 := Afalse).
  pure intro.


  assert (Hnil : v'33 = nil).
  { 
    eapply rlh_ecb_nowait_prop;eauto.  
  }
  subst.

  (*high level step*)
  remember (Int.ltu i3 i1) as Y.
  remember (Int.eq i1 i3 ) as Z.
  assert (Int.ltu Int.zero Int.one || Int.ltu Int.zero Int.one = true).
  simpl.
  go.
  assert (Int.ltu Int.zero Int.one || Int.ltu Int.zero Int.zero = true).
  simpl.
  go.
  assert (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.one = true).
  simpl.
  go.
  assert (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.zero = false).
  simpl.
  go.
  clear H9 H39.

  assert (true = Int.ltu i3 i1 \/ true = Int.eq i1 i3).
  destruct Y;destruct Z;simpl in H0; try rewrite H38 in H0;tryfalse;try rewrite H40 in H0;tryfalse;try rewrite H41 in H0;tryfalse;try rewrite H42 in H0;tryfalse; auto.
  simpl in H0; tryfalse.
  lets Hy:ecbmod_absmsgq Hrlh; simpljoin.
  (* change ((Vptr (v'39, Int.zero) :: x :: nil) ++ v'2 :: nil) with (Vptr (v'39, Int.zero) :: x :: v'2::nil). *)
  assert (Hor: v'3 <> (Vint32 (Int.repr MSGQ_OVF_ERR)) \/ 
                v'3 = (Vint32 (Int.repr MSGQ_OVF_ERR))) by tauto.
  inversion Hor.
  (* v'3 <> ... *)
  hoare_lifts_trms_pre (Aop, absecblsid). 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpost_ipc_absinfer_ovf_abt; eauto.
  can_change_aop_solver. 
  eapply qpost_ovf_prop1; eauto.
  eapply absinfer_eq.
  eapply absabort_rule.
  (* v'3 = ... *)
  hoare_lifts_trms_pre (Aop, absecblsid). 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpost_ipc_absinfer_ovf;eauto.
  can_change_aop_solver.
  eapply qpost_ovf_prop1;eauto.
  eapply absinfer_eq.

 
  (* assert (Heget: EcbMod.get els (pblk, Int.zero) = Some (absmsgq x4 x6 x7, nil)) by auto. *)


  (* EXIT_CRITICAL *)
  eapply seq_rule.
  hoare_exit_critical2.
  (* RETURN ′ OS_SEM_OVF *) 
  hoare_lifts_trms_pre (Aisr, Ais).
  transform_pre add_a_isr_is_prop' ltac:(idtac).
  hoare forward. 
  eapply adisj_intro; right.
  




  sep normal. sep eexists.
  sep pauto; eauto. 
  eapply fold_EvtInv_frm.
  eapply fold_EvtInv_part1.
  sep pauto; eauto.
  trycancel_EvtInv. 
  sep cancel EvtInv_part2.
  sep cancel AOSRdyTblGrp.
  sep cancel AOSTCBPrioTbl.
  sep cancel AOSTCBList.
  unfold AECBList.
  sep normal.
  eexists.
  sep cancel ( OSEventList).  

  eapply evsllseg_compose; eauto.
  (* sep cancel evsllseg.
  sep cancel evsllseg. *)


  (* sep split. *)
 
      instantiate (2:=(V$ OS_EVENT_TYPE_Q
      :: Vint32 i0
         :: Vint32 i2
            :: Vptr (v'34, Int.zero)
               :: x2 :: v'' :: Vint32 i :: x5 :: nil)).
  unfolds; simpl; eauto.
  sep split. 
  instantiate (6:=(DMsgQ (Vptr (v'34, Int.zero))
  (x9
  :: x8
     :: x
        :: x1
           :: x3
              :: Vint32 i3
                 :: Vint32 i1
                    :: Vptr (v'36, Int.zero)
                       :: nil)
                       (x10 :: x11 :: nil) v'20)).
  unfold AEventNode.
  unfold AOSEvent, AEventData.
  unfold AOSEventTbl,  AMsgData.
  unfold AOSQCtr, AOSQBlk; unfold node. 
  sep normal. sep eexists. 
  sep split; eauto.
  2:{ unfolds; simpl; auto. }
  splits;auto;go.
  splits;auto;go.
  splits;auto;go.
  eauto. 
  right. 
  right. 
  left.  eexists. eexists.  eexists. 
  splits; eauto. go.
  (* Z.of_nat (length x4) >= Int.unsigned x6 *)
  eapply qpost_ovf_prop1;eauto.
 (* 以上结束了判断消息数大于size的分支 *)

  (*L21: ∗ pq ′ → OSQIn =ₑ message ′;ₛ*)
  lets Hx: osq_same_blk_st_in' H29. simpljoin.
  simpl in H27; inverts H27.
  lets Hy: wellq_in_props H31 Hrlh H29;eauto.
  simpljoin.

  hoare forward. hoare forward;eauto.
  pure_auto.

  (*L22: pq ′ → OSQIn =ₑ pq ′ → OSQIn +ₑ ′ 1;ₛ*)
    hoare forward. 
    struct_type_match_solver.

  (*L23: pq ′ → OSQEntries =ₑ pq ′ → OSQEntries +ₑ ′ 1;ₛ*)
  hoare forward.
  struct_type_match_solver.

  (*L24: If(pq ′ → OSQIn ==ₑ pq ′ → OSQEnd)*)
  pure intro.
  lets Hx: wellformedosq_ens_add_1 H31 Hrlh H29.
  hoare forward.
  struct_type_match_solver.
  struct_type_match_solver.

  clear - H32.
  destruct x; unfolds in H32;  destruct H32; tryfalse; destruct H; tryfalse.
  simpl; intro; tryfalse.
  destruct a.
  inverts H.
  destruct (peq v'36 b);
  destruct (Int.eq (x4 +ᵢ  Int.mul ($ 1) ($ 4)) i); simpl; intro; tryfalse.
  (*L25: pq ′ → OSQIn =ₑ pq ′ → OSQStart*)
  hoare forward.
  struct_type_match_solver.

  assert (exists a, x = Vptr a).
  clear - H29.
  unfolds in H29; simpl in H29; simpljoin.
  unfolds in H0; simpl in H0; inverts H0.
  eauto. 
  simpljoin. 
  Open Scope code_scope.
  (*combine the 2 cases after if*) 
  eapply backward_rule1 with
  (p:= (EX new_qin,
        [| ((v'36, x4 +ᵢ  Int.mul ($ 1) ($ 4)) = x1 /\ new_qin = x8) \/
         ((v'36, x4 +ᵢ  Int.mul ($ 1) ($ 4)) <> x1 /\ new_qin = (Vptr (v'36, x4 +ᵢ  Int.mul ($ 1) ($ 4)))) |] **
         <||
         spec_code_cons
           (ipcqpost ((Vptr (pblk, Int.zero) :: Vptr x0 :: nil) ++ v'3 :: nil))
           v'1 ||>  **
         LV pq @ OS_Q ∗ |-> Vptr (v'34, Int.zero) **
         Astruct (v'34, Int.zero) OS_Q
           (x9
            :: x8
               :: Vptr x1
                  :: new_qin
                     :: x3
                        :: Vint32 i3
                           :: Vint32 (i1 +ᵢ  $ 1) :: Vptr (v'36, Int.zero) :: nil) **
         Aarray (v'36, Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))
           (Tarray (Void) ∗ ∘ OS_MAX_Q_SIZE)
           (update_nth_val
              (Z.to_nat
                 ((Int.unsigned x4 -
                   Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4)) v'20
              (Vptr x0)) **
         Astruct (v'36, Int.zero) OS_Q_FREEBLK (x10 :: x11 :: nil) **
         Astruct (pblk, Int.zero) OS_EVENT
           (V$ OS_EVENT_TYPE_Q
            :: Vint32 i0
               :: Vint32 i2
                  :: Vptr (v'34, Int.zero) :: x2 :: v'' :: Vint32 i :: x5 :: nil) **
         Aarray v'28 (Tarray char_t ∘ OS_EVENT_TBL_SIZE) etbl **
         AOSPostEventTbl v'30 petbl **
         evsllseg v'21 (Vptr (pblk, Int.zero)) v'23 v'25 **
         evsllseg v'' Vnull v'24 v'26 **
         GV OSEventList @ OS_EVENT ∗ |-> v'21 **
         AOSQFreeList v'18 **
         AOSQFreeBlk v'19 **
         HECBList els **
         EvtInv_part2 els v'5 (v'7 ++ v'8 :: v'9) v'11 v12 v13 v14 **
         AOSUnMapTbl **
         AOSMapTbl **
         AOSRdyTblGrp v'12 v'13 **
         AOSTCBPrioTbl v'14 v'12 v'10 v'15 v'11 **
         AOSTCBList v'5 v'6 v'7 (v'8 :: v'9) v'12 v'17 v'10 **
         HTCBList v'10 **
         HTime v'16 **
         HCurTCB v'17 **
         Aier ier **
         Aisr isr **
         Aie false **
         Ais is **
         Acs (false :: nil) **
         p_local OSLInv ct init_lg **
         GV OSIntNesting @ long |-> Vint32 vnest **
         GV OSLockNesting @ long |-> Vint32 vlock **
         LV x @ Int16u |-> v'0 **
         LV message @ (Void) ∗ |-> Vptr x0 **
         LV pevent @ OS_EVENT ∗ |-> Vptr (pblk, Int.zero) **
         A_dom_lenv
           ((message, (Void) ∗)
            :: (pevent, OS_EVENT ∗) :: (pq, OS_Q ∗) :: (x, Int16u) :: nil)
          )).
  intros.
  destruct H41.

  (*if true*)
  sep auto.
  left.
  split; auto.
  simpljoin.
  clear - H49.
  destruct x1.
  destruct (peq v'36 b) eqn : eq1;
  destruct (Int.eq (x4 +ᵢ  Int.mul ($ 1) ($ 4)) i) eqn : eq2;
  simpl in H49; tryfalse.
  substs.
  pose proof Int.eq_spec (x4 +ᵢ  Int.mul ($ 1) ($ 4)) i.
  rewrite eq2 in H.
  substs; auto.

  (*if false*)
  sep auto.
  right.
  split; auto.
  simpljoin.
  clear - H49.
  destruct x1.
  destruct (peq v'36 b) eqn : eq1;
  destruct (Int.eq (x4 +ᵢ  Int.mul ($ 1) ($ 4)) i) eqn : eq2;
  simpl in H49; destruct H49; tryfalse.
  substs.
  intro.
  inverts H0.
  pose proof Int.eq_spec (x4 +ᵢ  Int.mul ($ 1) ($ 4)) (x4 +ᵢ  Int.mul ($ 1) ($ 4)).
  rewrite eq2 in H0.
  tryfalse.

  intro. inverts H0.
  tryfalse.

  intro. inverts H0.
  tryfalse.

  pure intro.

  (*high level step*)
  lets Hx1: ecbmod_absmsgq Hrlh.
  lets Hx2: EcbMod.join_joinsig_get Hjo  Hjo' .
  simpljoin.

  lets Hx3: rlh_ecb_nowait_prop H10 Hecbetbl Hx2 H4 H; substs.

  eapply backward_rule1.
  introv Hsat.
  eauto.

  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid,EvtInv_part2).
  assert (Hor: v'3 <> (Vint32 (Int.repr OS_NO_ERR)) \/ 
                 v'3 = (Vint32 (Int.repr OS_NO_ERR))) by tauto.
  inversion Hor.
  (* v'3 <> ... *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpost_ipc_absinfer_nowt_succ_abt.
  can_change_aop_solver.
  eauto. eauto.

  assert(Int.ltu i1 i3 = true).
  clear - H39.
  apply val_inj_i1_i2_lt in H39; auto.
  eapply qpost_no_wait_prop'; eauto.
  eapply absinfer_eq.
  eapply absabort_rule.

  (* v'3 = ... *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpost_ipc_absinfer_nowt_succ.
  pure_auto. eauto. eauto.
  assert(Int.ltu i1 i3 = true).
  clear - H39.
  apply val_inj_i1_i2_lt in H39; auto.

  eapply qpost_no_wait_prop'; eauto.
  eapply absinfer_eq.
  
  (* EXIT_CRITICAL *)
  eapply seq_rule.
  hoare_exit_critical2.
  (* RETURN ′ OS_SEM_OVF *) 
  hoare_lifts_trms_pre (Aisr, Ais).
  transform_pre add_a_isr_is_prop' ltac:(idtac).
  hoare forward.
  eapply adisj_intro; right.
  sep normal.  
  do 18 eexists.
  exists (EcbMod.set els (pblk, Int.zero)
  (absmsgq (x ++ Vptr x0 :: nil) x6 x7, nil)) . 
  
  sep pauto; eauto.   
  eapply fold_EvtInv_frm. eauto.
  eapply fold_EvtInv_part1. 
    (* unfold EvtInv_part2 in *. *)
  trycancel_EvtInv.   
  unfold AECBList.
  sep pauto; eauto. 
  eapply evsllseg_compose;eauto.
  instantiate (2:=(V$ OS_EVENT_TYPE_Q
  :: Vint32 i0
     :: Vint32 i2
        :: Vptr (v'34, Int.zero)
           :: x2 :: v'' :: Vint32 i :: x5 :: nil)).
  unfolds; simpl; eauto. 
  sep cancel EvtInv_part2.


  sep cancel AOSRdyTblGrp.
  sep cancel AOSTCBPrioTbl .
  sep cancel evsllseg.
  sep cancel evsllseg. 
  unfold AEventNode.

  unfold AOSEvent.
  unfold AEventData.
  unfold node.
  sep pauto.
  sep cancel OS_EVENT . 
  sep cancel AOSPostEventTbl.
  unfold AOSEventTbl.
  sep pauto.
  instantiate (1:=(DMsgQ (Vptr (v'34, Int.zero))
  (x9
           :: x8
              :: Vptr x1
                 :: v'2
                    :: x3
                       :: Vint32 i3
                          :: Vint32 (i1 +ᵢ  $ 1)
                             :: Vptr (v'36, Int.zero) :: nil)
                       (x10 :: x11 :: nil) (update_nth_val
                       (Z.to_nat
                          ((Int.unsigned x4 -
                            Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
                       v'20 (Vptr x0)))).
  sep pauto.
  unfold AMsgData.
  unfold AOSQCtr.
  sep cancel (Tarray char_t ∘ OS_EVENT_TBL_SIZE).
  unfold node.
  sep pauto.
  sep cancel OS_Q.
  unfold AOSQBlk.
  unfold node.
  sep pauto.
  sep cancel Astruct. sep cancel Aarray.
  instantiate (1:= Vptr (v'36, Int.zero)).
  eauto.
  splits;eauto.
  struct_type_match_solver.
  (* V_qfreeblk *)
  unfolds; simpl; auto.
  (*WellformedOSQ  *)
  {
    destruct H41; simpljoin.
    eapply get_wellformedosq_in_setst; eauto.
    apply val_inj_i1_i2_lt; auto.
    rewrite peq_true.
    rewrite Int.eq_true.
    simpl; intro; tryfalse.
    
    eapply get_wellformedosq_in_setst'; eauto.
    intro. inverts H44; tryfalse.
    apply val_inj_i1_i2_lt; auto.
  }
  (* Vptr (v'34, Int.zero) = Vptr (v'34, Int.zero) /\struct_type_vallist_match OS_Q *)
  split; auto.
  go.
  {
    clear - H28 H41.
    destruct H41; simpljoin; auto.
    unfolds in H28; destruct H28; simpljoin; auto.
  }
  (* array_type_vallist_match  *)
  eauto.

  eauto.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  eauto.
  unfolds; simpl; auto.
  eauto.
  split; auto.
  go.

  (* ECBList_P v'21 Vnull *)
  eapply msgqlist_p_compose'; eauto.
  destruct H1.
  rewrite H1. tryfalse.
  (* clear -H11. simpl in H11. destruct H11;tryfalse. *)
  destruct H1 as (p & H1).
  rewrite H1.
  {  (*destruct the if condition here*)
  destruct H41; simpljoin.
  eapply rlh_ecbdata_in_end;eauto.
  eapply val_inj_i1_i2_lt; auto.

  eapply rlh_ecbdata_in_noend; eauto.
  clear - H41.
  intro; inversion H; apply H41; auto.
  eapply val_inj_i1_i2_lt; auto.
  }
  eapply EcbMod.joinsig_set;eauto.
  eapply EcbMod.joinsig_set_set;eauto.

  right. 
  right. 
  right. 
  left.
  do 3 eexists. splits; eauto. 
  (* Z.of_nat (length x) < Int.unsigned x6 *)
  eapply qpost_no_wait_prop';eauto.
  (* Int.ltu i1 i3 = true *)
  eapply val_inj_i1_i2_lt; auto.
  (* RH_TCBList_ECBList_P  (EcbMod.set els (pblk, Int.zero) *)
  eapply rh_tcbls_mqls_p_setmsg_hold;eauto.


  (******************************* OSEventGrp != 0 ******************************) 
  hoare forward.   
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.
  hoare unfold.
  hoare_assert_pure (v'17 = ct).
  { get_hsat Hsat.
  unfold p_local in Hsat.
  unfold CurTid in Hsat.
  sep normal in Hsat; sep destruct Hsat.
  sep_lifts_skp_in Hsat (OSTCBCur, _N_ 1).
  eapply read_only_merge_vptr in Hsat.
  destruct Hsat; auto.
  }
  hoare_split_pure_all; subst.
  hoare normal pre.
  pure_intro.
  (****************************** L2: event_task_rdy ******************************)
  hoare_lifts_trms_pre (Aisr, Ais).
  transform_pre add_a_isr_is_prop' ltac:(idtac).
  hoare_lifts_trms_pre Aop. 
  hoare forward.
  sep cancel AOSRdyTblGrp.
  sep cancel p_local.
  unfold_msg.
  sep cancel AEventData.
  sep normal.
  sep eexists.
  sep cancel AOSPostEventTbl.
  sep cancel Astruct.
  sep cancel Aarray.
  sep pauto; eauto.
  eapply tcbdllseg_compose.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  eauto.

  splits; eauto. 
  struct_type_match_solver.
  split.
  unfolds; simpl; eauto.
  lzh_simpl_int_eq. auto.
  simpl; eauto.
  simpl; eauto.
  simpl; eauto.
  eapply TCBList_P_Combine.
  eapply tcbdllseg_get_last_tcb_ptr with (s:= s).
  sep cancel tcbdllseg.
  eauto.
  2:eauto.
  2:eauto.
  eauto.

  eauto.
  eauto.
  eauto.

  eapply tcbdllseg_combine_ptr_in_tcblist with (s := s).
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  eauto.

  pure_auto.
  pure_auto.

  intros.
  sep auto.

  intros.
  sep auto.

  (** event task rdy precondition finished **)
  hoare unfold.

  remember (spec_code_cons (ipcqpost ((Vptr (pblk, Int.zero) :: Vptr x0 :: nil) ++ v'3 :: nil)) v'1) as abs_code.
  inverts H63.
  subst v'55.

  (*   rename v'38 into pevent_addr. *)
  rename ct into ctcb.
  rename v'85 into htcb_addr. (** highest tcb in pevent waitlist **)
  rename H36 into Hhtcb.
  rename H57 into Hctcb_in_tcblist. 
  rename v'56 into tcblist_head. 
  rename v'7 into tcblist_seg1.
  rename v'8 into ctcb_node.
  rename v'9 into tcblist_seg2.
  rename H40 into Hrel_et. 

  (* ** ac: Print prio_in_tbl. *)
  rename v'42 into rtbl. 
  (* ** ac: Print TCBList_P. *)

  rename v'38 into tcbls.
  rename v'36 into tcbls1. 
  rename v'37 into tcbls2.

  (** tcbls = tcbls1 ++ tcbls2, tcbls2 = cur_node ++ tcbls2' **)
  remember (tcblist_seg1 ++ ctcb_node :: tcblist_seg2) as tcblist.

  rename v'80 into hprio. 
  assert (Hprio: exists hprio', hprio = Vint32 hprio'). 
  {
    clear - H67. (** struct_type_vallist_match **)
    rename H67 into H. 
    unfold struct_type_vallist_match in H.
    unfold OS_TCB_flag in H.
    unfold struct_type_vallist_match' in H.
    mytac.
    clear - H5.
    (* ** ac: SearchAbout (rule_type_val_match Int8u _). *)
    apply rule_type_val_match_int8u_elim in H5.
    mytac.
  }

  destruct Hprio as (hprio' & Hprio).
  subst hprio.
  rename hprio' into hprio.

  rename v'74 into hnext. 
  rename v'81 into htcbx.
  rename v'82 into htcby.
  rename v'83 into hbitx.
  rename v'84 into hbity. 

  (* ** ac: Check tcblist_get_TCBList_P_get. *)
  (* ** ac: Check sem_post_get_tcb_stat. *)
  (* ** ac: Check rh_tcblist_ecblist_p_post_exwt_aux_sem. *)
  (* ** ac: Check rh_tcblist_ecblist_p_post_exwt_sem. *)
  assert (Hhtcb_get: exists st m sus, get tcbls (htcb_addr, Int.zero) = Some (hprio, st, m, sus)).
  {
    eapply tcblist_get_TCBList_P_get.
    eauto.
    pure_auto.
    eauto.
  }

  destruct Hhtcb_get as (st & msg & sus & Hhtcb_get).
  assert (Hs1: Int.unsigned v'68 <= 7). 
  {
    (* ** ac: Check osunmapvallist_prop. *)
    clear - H41 H17.
    apply osunmapvallist_prop in H17.
    mytac.
    rewrite H in H41.
    inverts H41.
    int auto.
  }

  assert (Hs2: Int.unsigned v'69 <= 255).
  {
    (* ** ac: Check array_int8u_nth_lt_len. *)
    clear - H42 Hs1 H53 H14.
    assert (Z.to_nat (Int.unsigned v'68) < length v'48)%nat. 
    {
      rewrite H14; unfold OS_EVENT_TBL_SIZE.
      unfold nat_of_Z.
      auto with zarith.
    }
    lets Hx: array_int8u_nth_lt_len H53 H.
    mytac.
    rewrite H42 in H0.
    inverts H0.
    auto.
  }

  assert (Hs3: Int.unsigned v'67 <= 7). 
  {
    clear - H43 Hs2.
    lets Hx: osunmapvallist_prop Hs2.
    mytac.
    rewrite H in H43; inverts H43.
    int auto.
  }

  rename v'33 into pwls.
  (* ** ac: Check post_exwt_succ_pre_sem. *)
  generalize Hhtcb_get; intro Hhtcb_join.
  apply map_join_get_sig in Hhtcb_join.
  destruct Hhtcb_join as (tcbls' & Hhtcb_join).
  assert (Hpre: pwls <> nil /\ GetHWait tcbls pwls (htcb_addr, Int.zero) /\
                TcbMod.get tcbls (htcb_addr, Int.zero) = Some (hprio, st, msg, sus) /\
                hprio = ((v'68<<ᵢ$ 3) +ᵢ  v'67)).
  {
    apply map_join_get_sig in Hhtcb_get.
    destruct Hhtcb_get.
    (* ** ac: Check post_exwt_succ_pre_sem. *)
    apply semacc_int_eq_false in H.
    eapply post_exwt_succ_pre'; eauto.

  }

  destruct Hpre as [ ? [? [? ?]]].
  subst hprio.

  assert (Hv'2cs: v'3 <> Vint32 (Int.repr OS_NO_ERR) \/
  v'3 = Vint32 (Int.repr OS_NO_ERR)) by tauto. 
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid,EvtInv_part2).
  inversion Hv'2cs.

  (* v'3 <> ... *) 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpost_ipc_absinfer_exwt_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule.
  (* v'3 = ... *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpost_ipc_absinfer_exwt_succ; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq.

  unfold AEventData.
  unfold_msg.
  hoare_split_pure_all.
  destruct H39.
  inverts H39.
  rename v'9 into pevent_addr.

  unfolds in H47; simpl in H47; inverts H47.
  (* ** ac: Check sem_post_get_tcb_stat. *)
  rename v'48 into etbl.

  rename H62 into Htcblist_p.
  lets Hhtcb_node: TCBList_P_tcblist_get_TCBNode_P Htcblist_p Hhtcb Hhtcb_get.
  generalize Hhtcb_node; intro Htmp.
  unfolds in Htmp.
  mytac.
  inverts H39; inverts H47.

  rename H62 into Hh_tcbblk.
  rename H63 into Hh_tcbstat. 
  unfolds in Hh_tcbblk.
  mytac.
  inverts H76.
  inverts H38. 
  inverts H39.
  inverts H47. 
  inverts H62. 
  inverts H63. 
  inverts H69.

  rename v'68 into p1.
  rename v'67 into p2. 
  remember ((p1<<ᵢ$ 3) +ᵢ  p2) as hprio.

  assert (Hx: x8 = $ OS_STAT_Q \/ x8 = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND)).
  {
    clear - Hrel_et.
    unfolds in Hrel_et.
    auto.
  }

  assert (Hp1: (hprio >>ᵢ $ 3) =  p1).
  {
    subst hprio.
    clear - Hs1 Hs2 Hs3.
    clear Hs2.
    mauto.
  }

  assert (Hp2: hprio &ᵢ ($ 7) = p2).
  {
    subst hprio.
    clear - Hs1 Hs3.
    mauto.
  }

  assert (Hs4: Int.unsigned v'86 <= 255).
  {
    clear - Hs1 H33 H65 H50.
    assert (Z.to_nat (Int.unsigned p1) < length rtbl)%nat.
    {
      rewrite H65. 
      unfold OS_RDY_TBL_SIZE.
      mauto.
    }
    lets Htmp: array_int8u_nth_lt_len H50 H. 
    mytac.
    rewrite H33 in H0. 
    inverts H0.
    auto.
  }

  (* ** ac: Check set_node_elim_hoare. *)
  assert (Htmp: v'70 = $ 1 <<ᵢ p2). 
  {
    eapply math_mapval_core_prop.
    clear - Hs3.
    auto with zarith.
    auto.
  }
  subst v'70.

  assert (Hno_dup: R_Prio_No_Dup tcbls).
  {
    clear - H60.
    unfolds in H60.
    mytac.
  }

  hoare_lifts_trms_pre tcbdllseg.
  eapply set_node_elim_hoare_sus with (tid:=ctcb) (tcbls:=tcbls); eauto.
  {
    eapply TCBNode_P_set_rdy_gen; auto.
    2:eauto.
    rewrite Hp1.
    apply nth_val'2nth_val; eauto.
    2: eauto.
    destruct Hx; subst x8.
    assert (Hsus: sus = false) by
    (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: sus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    change (Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_Q)) with ($ OS_STAT_SUSPEND).
    auto.
  }

  { destruct sus eqn: eq1; auto.
    unfolds.
    rewrite Hp1.
    rewrite Hp2.
    do 2 eexists.
    splits; eauto.
  }
  {
    unfolds.
    unfold V_OSTCBNext , V_OSTCBPrev.
    simpl.
    auto.
  }

  (* ==================处理ELH_ECBData_P相关========================= *)

  (************************* exit critical ***********************************)
  assert (Heq_sus: Int.eq (x8&ᵢInt.not ($ OS_STAT_Q)) ($ OS_STAT_RDY) = negb sus).
  { change ($ OS_STAT_RDY) with Int.zero.
    destruct Hx; subst x8.
    assert (Hsus: sus = false) by
    (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: sus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    change (Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_Q)) with ($ OS_STAT_SUSPEND).
    auto.
   }

  hoare_split_pure_all.
  subst hprio.
  rewrite Hp1 in *.
  rewrite Hp2 in *.

  (* ================================== *)
  unfold AEventNode.
  unfold AOSEvent, AEventData.
  unfold AOSEventTbl, AMsgData.
  unfold AOSQCtr; unfold AOSQBlk.
  unfold node.
  pure intro.
  (* ================================== *)
  (* EXIT_CRITICAL *)
  hoare_lifts_trms_pre (Aisr, Ais, A_isr_is_prop).
  transform_pre a_isr_is_prop_split ltac:(sep cancel Aisr; sep cancel Ais).
  eapply seq_rule.
  hoare_exit_critical2.
  unfold AEventData. pure_auto.
  change ($ 0) with Int.zero in *.
  fold_AEventNode_r.
  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_part1.
  trycancel_EvtInv.
  unfold AECBList.
  sep normal.
  eexists.
  sep cancel OSEventList.
  simpl update_nth_val in H38.
  sep split.
  eapply evsllseg_compose; eauto.
  2:{
    instantiate (8:=  (DMsgQ (Vptr (v'14, Int.zero))
  (x11
  :: x10
      :: x
        :: x1
            :: x3
              :: Vint32 i3
                  :: Vint32 i0 :: Vptr (v'35, Int.zero) :: nil)
  (x12 :: x13 :: nil) v'20)).
   unfold AEventNode.
  unfold AOSEvent, AEventData.
  unfold AOSEventTbl,  AMsgData. 
  unfold AOSQCtr, AOSQBlk; unfold node in *.
  sep normal in Hsat. sep destruct Hsat.
  sep normal. sep eexists.
  sep cancel OS_EVENT_TBL_SIZE.
  sep cancel AOSPostEventTbl.
  sep split;eauto.
  sep cancel OS_EVENT.
  sep cancel evsllseg.
  sep cancel evsllseg.
  sep cancel OS_MAX_Q_SIZE.
  sep cancel OS_Q.
  sep pauto.
  unfolds; simpl; eauto.
  unfolds; simpl; eauto.
  unfolds; simpl; eauto.
  split; auto. go.
  sep split in Hsat. simpljoin.
  split; auto.
  }
  unfolds; simpl; eauto.
  (* ECBList_P *)
  eapply ecblist_p_post_exwt_hold1
  with (v'12:=v'46) (v'39:=p2) (v'38:=p1) (v'13:=etbl); eauto.
  eapply semacc_int_eq_false; eauto.
  clear - Hs3. mauto.

  (* OS_Sched *)
  pure intro.

  hoare forward.

  eapply disj_split.
  left.
  sep cancel p_local.
  sep cancel 1%nat 1%nat.
  sep split.
  exact H73.
  auto.
  left.
  auto. 

  unfolds; eauto.
  pure_auto.
  sep normal.
  intros.
  sep auto.
  intros.
  sep auto.

  hoare unfold.
  inverts H73.

  eapply backward_rule1.
  intros.
  sep lift 9%nat in H73.

  apply disj_split in H73.
  exact H73.
  apply disj_rule.

  hoare unfold.  

  (* RETURN ′ OS_NO_ERR *)
  hoare_lifts_trms_pre Aop. 
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply absinfer_seq_end.
  pure_auto.
  2: eauto.
  pure_auto.
  eapply absinfer_eq.

  assert (Hin_pwls: In (htcb_addr, Int.zero) pwls).
  { clear -H36.
    unfolds in H36.
    simpljoin; auto.
  }

  assert (Hst: exists xl , st = wait (os_stat_q (pevent_addr, Int.zero)) xl).
  {
    eapply rh_tcblist_ecblist_p_post_exwt_aux ;eauto.
  }
  destruct Hst as (t_opt & Hst); subst st.
  assert (Heptr: exists wt, x9 = Vptr (pevent_addr, Int.zero) /\ v'78 = Vint32 wt).
  { 
    clear -Hh_tcbstat.
    destruct Hh_tcbstat as (_ & _ & _ & _ & _ & Hstat).
    destruct Hstat as (_ & _ & Hstat & _ & H ).
     funfold H. simpljoin.
     destruct sus eqn: eq1.
     specialize (H2 _ _ _ _ (eq_refl _)).
     destruct H2 as (Hwt & Hptr & Hst); inverts Hptr; inverts Hst.
     destruct Hwt as [(ts & Heq & Hwt) | (Heq & Hwt)];
     inverts Heq; funfold Hwt; eauto.
     clear -Hstat.
    funfold Hstat.
    specialize (Hstat _ _ _ _ (eq_refl _)).
    simpljoin.
    inverts H0.
    unfold WaitTCBblk,V_OSTCBDly in *.
    simpl nth_val in *.
    destruct H; simpljoin.
    destruct H0; simpljoin.
    inverts H3; eauto.
    inverts H2; eauto.
    inverts H3; eauto.
  }
  destruct Heptr as (wt & Heptr & Hwt); subst.
  hoare_lifts_trms_pre (Aisr, Ais).
  transform_pre add_a_isr_is_prop' ltac:(idtac).
  hoare forward.
  sep cancel p_local.
  eapply adisj_intro; right.
  sep normal. sep eexists.
  sep pauto.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  sep cancel OSPlaceHolder.
  sep cancel Int8u.
  eapply fold_EvtInv_frm.
  sep cancel EvtInv_part1.
  unfold EvtInv_part2 in *.
  sep pauto.
  trycancel_EvtInv.
  unfold tcbllsegevaux.
  eapply llsegevaux_set_node; eauto.
  { unfold same_prev_next. simpl. splits; auto. }
  eauto.
  eauto.
  eauto.
  rewrite Heq_sus. rewrite negb_if.
  repeat right.
  do 10 eexists. splits; eauto. 
  repeat eexists; eauto. 
  assert (Htmp: ctcb = (htcb_addr, Int.zero) \/ ctcb <> (htcb_addr, Int.zero)) by tauto.
  destruct Htmp.
  subst ctcb.
  unfolds. 
  unfold get; simpl.
  rewrite TcbMod.set_a_get_a.
  eauto.
  apply tidspec.eq_beq_true; auto.
  eapply rh_curtcb_set_nct; auto.  

  eapply rh_tcblist_ecblist_p_post_exwt;eauto. 
  eauto.
  eapply r_priotbl_p_set_hold; auto; eauto.
  eauto.
  eauto.
  rewrite Heq_sus. rewrite negb_if.
  eauto.
  rewrite Heq_sus. rewrite negb_if.
  eauto.
  eauto.

  pure intro; tryfalse.
  
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
  trivial.
  trivial.
  trivial.
  trivial.
 Qed.
  
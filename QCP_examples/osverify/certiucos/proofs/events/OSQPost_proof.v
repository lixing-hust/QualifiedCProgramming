Require Import os_q.
Require Import abs_op.

Require Import ucos_include.
(* Require Import absop_rules. *)
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

(* new lemmas about q postnew in absop_rules *)
Require Import abs_infer_step.
Require Import ucos_frmaop.
(* Require Import seplog_lemmas.
Require Import seplog_tactics. *)

Require Import evauxvar_lemmas.
Require Import evaux_pure.
Require Import freeevtlist_lemmas.
Require Import seplog_trm_tacs.
Require Import abs_infer_abt.

Require Import q_common.
Require Import sem_common.
Require Import gjb_q_common.
Require Import sem_corecommu.

Require Import evtinv_lemmas.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Open Scope code_scope.
Open Scope int_scope.
Open Scope Z_scope.

(*  引入下面的定义是为了使用 lzh_hoare_if2 *)
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

(********************** q post*****************************)

Lemma absinfer_seq1:
  forall (p : asrt) (s1 : absop)  (s2 : spec_code) (s1' : absop) (sc : ossched),
                   can_change_aop p ->
                   sc ⊢  <|| s1 ||>  ** p ⇒  <|| s1' ||>  ** p ->
                   sc ⊢  <|| s1;; s2 ||>  ** p ⇒  <|| s1';; s2 ||>  ** p.
Proof.
intros.
eapply absinfer_seq; try eauto.
Qed.

Lemma qpost_absinfer_null:
  forall qid v_msg v' P sch s,
    qid = Vnull ->
    v' = V$ OS_ERR_PEVENT_NULL ->
    can_change_aop P -> 
    absinfer sch
       ( <|| spec_code_cons (qpost (qid :: v_msg :: v' :: nil)) s ||> ** P) 
       ( <|| s ||> ** P ).
Proof.
  introv Hqid Hv' Hcop.
  eapply absinfer_trans. 
  simpl.
  eapply absinfer_choice1;try eauto.

  eapply absinfer_trans.
  eapply absinfer_seq1. pure_auto.
  instantiate (1:=END (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))).
  infer_solver 0%nat. 
  simpljoin.
  repeat tri_exists_and_solver1.
  eapply absinfer_seq_end; try pure_auto.
Qed.

Lemma qpost_absinfer_null_abt:
  forall  qid v_msg v' P sch s,
  qid = Vnull ->
   v' <> V$ OS_ERR_PEVENT_NULL ->
   can_change_aop P -> 
   absinfer sch
       ( <|| spec_code_cons (qpost (qid :: v_msg :: v' :: nil)) s ||> ** P)
       ( <|| ABORT ||> ** P ).
Proof.
  introv Hqid Hv' Hcop.
  eapply absinfer_trans. 
  simpl.
  eapply absinfer_choice1;try eauto.
  eapply absinfer_trans.
  eapply absinfer_seq1. pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  eapply absinfer_seq_abt; try pure_auto.
Qed.

Lemma qpost_absinfer_msg_null:
  forall qid  v' P sch s,
    v' = V$ OS_ERR_POST_NULL_PTR ->
    can_change_aop P -> 
    absinfer sch
       ( <|| spec_code_cons (qpost (Vptr qid :: Vnull :: v' :: nil)) s ||> ** P) 
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

Lemma qpost_absinfer_msg_null':
  forall qid  v' P sch s,
    v' = V$ OS_ERR_POST_NULL_PTR ->
    can_change_aop P -> 
    absinfer sch
       ( <|| spec_code_cons (qpost (Vptr qid :: Vnull :: v' :: nil)) s ||> ** P) 
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

Lemma qpost_absinfer_msg_null_abt:
  forall qid  v' P sch s,
    v' <> V$ OS_ERR_POST_NULL_PTR ->
    can_change_aop P -> 
    absinfer sch
       ( <|| spec_code_cons (qpost (Vptr qid :: Vnull :: v' :: nil)) s ||> ** P) 
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

Lemma qpost_absinfer_type_err:
  forall P mqls x v_msg v' sch s, 
    can_change_aop P ->  
    v' = V$ OS_ERR_EVENT_TYPE ->  
    (~ exists a b pwl wl, get mqls x = Some  (absmsgq a b pwl, wl) ) ->
    absinfer sch
      ( <|| spec_code_cons (qpost (Vptr x :: v_msg :: v' :: nil)) s ||>  ** 
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

Lemma qpost_absinfer_type_err_abt:
  forall P mqls x v_msg v' sch s, 
    can_change_aop P ->  
    v' <> V$ OS_ERR_EVENT_TYPE ->  
    ( ~ exists a b pwl wl, get mqls x = Some (absmsgq a b pwl, wl)) ->
    absinfer sch
      ( <|| spec_code_cons (qpost (Vptr x :: v_msg :: v' :: nil)) s ||>  ** 
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

Lemma qpost_absinfer_ovf:
  forall P mqls x v_msg v'  a b pwl wl sch s, 
    can_change_aop P ->  
    v' = V$ MSGQ_OVF_ERR ->  
    EcbMod.get mqls x = Some (absmsgq a b pwl, wl) ->
    Z.ge (Z_of_nat (length a)) (Int.unsigned b) ->
    absinfer sch
      ( <|| spec_code_cons (qpost (Vptr x :: v_msg :: v' :: nil)) s ||>  **  
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


Lemma qpost_absinfer_ovf_abt:
  forall P mqls x v_msg v'  a b pwl wl sch s, 
    can_change_aop P ->  
    v' <> V$ MSGQ_OVF_ERR ->  
    EcbMod.get mqls x = Some (absmsgq a b pwl, wl) ->
    Z.ge (Z_of_nat (length a)) (Int.unsigned b) ->
    absinfer sch
      ( <|| spec_code_cons ( qpost (Vptr x :: v_msg :: v' :: nil)) s ||>  ** 
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

Lemma qpost_absinfer_nowt_succ: 
  forall P mqls x v_msg v' a b pwl tcbls t ct sch s tcblh tcbvl vhold v1 v2 v3, 
    can_change_aop P ->  
    v' = V$ OS_NO_ERR ->
    EcbMod.get mqls x = Some (absmsgq a b pwl,nil) ->
    Z.lt (Z_of_nat (length a)) (Int.unsigned b) ->
    absinfer sch
          ( <|| spec_code_cons ( qpost (Vptr x :: v_msg :: v' :: nil)) s ||>  **
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

Lemma qpost_absinfer_nowt_succ_abt: 
  forall P mqls x v_msg v' a b pwl tcbls t ct sch s, 
    can_change_aop P ->  
    v' <> V$ OS_NO_ERR ->
    EcbMod.get mqls x = Some (absmsgq a b pwl,nil) ->
    Z.lt (Z_of_nat (length a)) (Int.unsigned b) ->
    absinfer sch
          ( <|| spec_code_cons ( qpost (Vptr x :: v_msg :: v' :: nil)) s ||>  **
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

Lemma qpost_absinfer_exwt_succ: 
  forall P mqls x v_msg v' vl n pwl wl tls t ct p st m t'  sch s tcblh tcbvl vhold v1 v2 v3 sus, 
    can_change_aop P ->  
    v' = V$ OS_NO_ERR ->
    get mqls x = Some (absmsgq vl n pwl,wl) ->
    ~ wl=nil ->
    GetHWait tls wl t' ->
    get tls t' = Some (p,st,m,sus) ->
    absinfer sch
          ( <|| spec_code_cons ( qpost ( (Vptr x) :: v_msg :: v' :: nil)) s ||>  **
            HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** 
            EvtInv_part2 mqls tcblh tcbvl vhold v1 v2 v3 **P) 
      (<|| isched ;; END Some (Vint32 (Int.repr OS_NO_ERR)) ;; s ||>  ** 
            HECBList (EcbMod.set mqls x (absmsgq nil n pwl, (remove_tid t' wl) ) ) **
            HTCBList (TcbMod.set tls t' (p,rdy ,v_msg,sus) ) ** HTime t ** HCurTCB ct **
            EvtInv_part2 (EcbMod.set mqls x (absmsgq nil n pwl, (remove_tid t' wl) ) ) tcblh tcbvl vhold v1 v2 v3 **  P).
Proof.
  introv Hcop Hv' Hq Hwl Hhw Htlsget .
  simpl.
  do 5 (
       eapply absinfer_trans; 
       [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ]
   ).

  eapply absinfer_trans.
  eapply absinfer_seq. pure_auto.
  instantiate (1:=HECBList (EcbMod.set mqls x (absmsgq nil n pwl, (remove_tid t' wl) ) ) **
                     HTCBList (TcbMod.set tls t' (p,rdy ,v_msg,sus) ) ** HTime t ** HCurTCB ct ** EvtInv_part2 (EcbMod.set mqls x (absmsgq nil n pwl, (remove_tid t' wl) ) ) tcblh tcbvl vhold v1 v2 v3 **P ).
  pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto. 
  instantiate (1:=HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct** EvtInv_part2 mqls tcblh tcbvl vhold v1 v2 v3 ** P).
  pure_auto. pure_auto.
  instantiate (1:=END (Some (Vint32 (Int.repr OS_NO_ERR)))).
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
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_eq. 
  eapply absinfer_seq_end; try pure_auto. 
Qed.

Lemma qpost_absinfer_exwt_abt: 
  forall P mqls x v_msg v' vl n pwl wl tls sch s, 
    can_change_aop P ->  
    v' <> V$ OS_NO_ERR ->
    get mqls x = Some (absmsgq vl n pwl,wl) ->
    ~ wl=nil ->
    absinfer sch
          ( <|| spec_code_cons ( qpost ( (Vptr x) :: v_msg :: v' :: nil)) s ||>  **
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

(*-----------OS Q Post-------------------*)

(*Hint Resolve gooda_qpost retpost_osev . *)
(*-------------------------------------------------------------*)
Open Scope int_scope.
Open Scope code_scope.
Open Scope Z_scope.

Lemma OSQPostProof: 
  forall vl p r logicl ct, 
    Some p =
    BuildPreI os_internal OSQPost vl logicl OSQPostPre ct->
    Some r =
    BuildRetI os_internal OSQPost vl logicl OSQPostPost ct->
    exists t d1 d2 s,
      os_internal OSQPost = Some (t, d1, d2, s) /\
      {|OS_spec , GetHPrio, OSLInv, I, r, Afalse |}|-ct {{p}}s {{Afalse}}.
Proof.
  init_spec.  rename H0 into Hnthvl0.
  rename v'2 into vptr; rename v'3 into v'2; rename v'4 into vier.
  (*enter critical -------------------------L1*)
  hoare forward prim. pure_auto.
  hoare unfold.

  (*pevent is Null pointer -------------------------L2 ~ L4*)
  lzh_hoare_if2.
  hoare forward prim.
  sep pauto.
  auto.
  pure_auto.
  
  change ((vptr :: x :: nil) ++ v'2 :: nil) with (vptr :: x :: v'2::nil).
  assert (Hor: v'2 <> (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) \/ 
                 v'2 = (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) by tauto.
  inversion Hor.
  (* v'1 <> ... *) 
  eapply abscsq_rule.
  apply noabs_oslinv.

  eapply qpost_absinfer_null_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq. 
  eapply absabort_rule.
  
  (* v'1 = ... *) 
  eapply abscsq_rule.
  (* eauto. *)
  apply noabs_oslinv.
  eapply qpost_absinfer_null; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq.
  
  (* return in case pevent = NULL *)
  hoare forward.
  instantiate (1:=($ OS_ERR_PEVENT_NULL)).
  unfold OS_ERR_PEVENT_NULL.
  auto with zarith.
  splits; eauto.
  unfold OS_ERR_PEVENT_NULL.
  int auto.
  unfold OS_ERR_PEVENT_NULL.
  change Byte.max_unsigned with 255.
  int auto.
  
  (*msg is Null pointer -------------------------L5 ~ L7*)
  hoare forward.
  apply isptr_zh; auto.
  pauto.
  pure intro.
  assert (x=Vnull) by pauto.
  subst x.
  pure_auto.
  assert (Hor: v'2 <> (Vint32 (Int.repr OS_ERR_POST_NULL_PTR)) \/ 
                 v'2 = (Vint32 (Int.repr OS_ERR_POST_NULL_PTR))) by tauto.
  inversion Hor.
  (* v'2 <> ... *)
  hoare_lifts_trms_pre Aop. 
  eapply abscsq_rule.
  apply noabs_oslinv.
  change ((Vptr x0 :: Vnull :: nil) ++ v'2 :: nil) with (Vptr x0 :: Vnull :: v'2::nil).
  eapply qpost_absinfer_msg_null_abt;eauto.
  can_change_aop_solver.
  instantiate (1:= (Afalse) ).
  eapply absinfer_eq.
  eapply absabort_rule.
  (* exit critical*)
  hoare forward prim.
  sep pauto.
  auto.
  pure_auto.
  
  (* v'2 = ... *)
  eapply abscsq_rule.
  eapply noabs_oslinv.
  change ((Vptr x0 :: Vnull :: nil) ++ v'2 :: nil) with (Vptr x0 :: Vnull :: v'2::nil).
  eapply qpost_absinfer_msg_null'.
  pure_auto.
  can_change_aop_solver.
  eapply absinfer_eq.
  
  hoare forward.
  instantiate (1:=($ OS_ERR_POST_NULL_PTR)).
  unfold OS_ERR_POST_NULL_PTR.
  auto with zarith.
  splits; eauto.
  unfold OS_ERR_POST_NULL_PTR.
  int auto.
  unfold OS_ERR_POST_NULL_PTR.
  change Byte.max_unsigned with 255.
  int auto.

  hoare forward.
  
  (* pevent not in dom legal : Lemma qpost_q_not_in_dom_abt*)
  unfold EvtInv.
  rename v'19 into vcspace.
  rename v'20 into v20. 
  rename v'21 into v21. 
  rename v'22 into v22. 

  hoare unfold.

  rename v'36 into locmp.
  rename v'37 into ptrmp.
  rename v'11 into els.
  rename v'19 into fecbh.
  rename v'20 into fecbvl.
  rename v'31 into semeibs.
  rename v'32 into muxeibs.
  rename v'33 into mqeibs.
  
  hoare_assert_pure (get ptrmp ct = Some (Vnull, Vnull, Vptr x0)
                                             /\ get locmp ct = Some (V$ os_code_defs.__EvLoc_normal)).
  { get_hsat Hsat.
     sep_lifts_trms_in Hsat (evlocid, evptrid, tcbllsegevaux, AOSTCBList,p_local).
    eapply get_aux;eauto.
   }
  hoare_split_pure_all.
  destruct H4 as (Hget_ptr & Hget_loc).

  assert (Hevt: is_evt els x0 \/ ptr_in_ecblist (Vptr x0) fecbh fecbvl).  
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
  
   (*if OSEventType !=ₑ ′ OS_EVENT_TYPE_Q*)
  hoare forward.
  go. 
  2: { instantiate(1:= Afalse).
          eapply hoare_disj_afalseP_l_pre.
          change (Int.eq ($ OS_EVENT_TYPE_UNUSED) ($ OS_EVENT_TYPE_Q)) with false. 
          hoare unfold.
          simpl in H4; change (Int.notbool Int.zero) with Int.one in H4; 
          destruct H4; tryfalse. }
  
  unfold AECBList.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Astruct, evsllseg).

  hoare_assert_pure (get els (v'37, Int.zero) = None).
  {
    get_hsat Hsat. 

    lets H00: semcre_ecblist_star_not_inh H4 Hsat.
    auto.
  }
  hoare_split_pure_all.
  rename H16 into Hnone.

   assert (Htype_err': ~ (exists x y pwl z, get els (v'37, Int.zero) = Some (absmsgq x y pwl, z))).
  { rewrite Hnone.
    introv Hf; destruct Hf as (mx & my & mp & mz & Hf ); inverts Hf.
  }

  assert (Hopv: v'2 = V$ OS_ERR_EVENT_TYPE \/ v'2 <> V$ OS_ERR_EVENT_TYPE) by tauto.
  hoare_lifts_trms_pre (Aop, absecblsid).
  destruct Hopv.
  2 :{
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply qpost_absinfer_type_err_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        eapply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpost_absinfer_type_err; eauto.
  can_change_aop_solver. eapply absinfer_eq.
  hoare forward prim.
  unfold EvtInv.
  unfold AECBList.
  sep pauto.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  unfold AOSEventFreeList.
  sep pauto.
  sep cancel evsllseg.
  unfold ecbf_sll.
  eapply ecbf_sllseg_compose3_frm; eauto. 
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel Aarray.
  sep cancel ecbf_sllseg.
  sep cancel ecbf_sllseg.
  eauto.
  unfolds; simpl; auto.
  go. go. eauto. eauto. eauto. eauto. auto.
  pure_auto.
  hoare forward.
hoare unfold.
  
   (* pevent points to an active ECB *) 
  assert (Hget: exists ecb, get els x0 = Some ecb).
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
  destruct d as [e w].
  
 (* split AECBList *)
  unfold AECBList.
  hoare unfold.
  lets Hget_ectr: ECBList_P_get_ectr_some Hget H4.
  destruct Hget_ectr as (et & etbl & petbl & Hget_ectr).
  eapply backward_rule1.
  intros.
  eapply get_ectr_decompose; eauto.
  sep cancel evsllseg. eauto.
  hoare unfold.
  hoare_assert_pure (length v'19 = length v'31).
  { get_hsat Hsat. sep_lifts_trms_in Hsat (evsllseg v'11).
     eapply evsllseg_list_len_eq in Hsat; auto.
  }
  hoare_split_pure_all.
  lets Hels_split: ecblist_p_decompose H13 H4.
  destruct Hels_split as (els1 & els2 & x0 & H'').
  destruct H'' as (Hecbl1 & Hecbl2 & Hjo).
  
  hoare_assert_pure ( x0 = Vptr (v'40, Int.zero) ).
  {  get_hsat Hsat.
  sep_lifts_trms_in Hsat  (evsllseg v'11).
  eapply ecblistp_evsllseg_tlsame; eauto. }
  hoare_split_pure_all.
  subst.
  simpl ECBList_P at 1 in Hecbl2.
  destruct Hecbl2 as (qid & Hqid & Hecbetbl & Hecbpetbl & Hmt).
  inverts Hqid.
  destruct Hmt as (absev & els' & v'' & H').
  destruct H' as (Helptr & Hjo' & Hrlh & Hecbl2). 
  inverts Helptr.
  
  assert (Habsev: get els (v'40, Int.zero) = Some absev).
  {
    assert (Hpre: join (sig (v'40, Int.zero) absev) els' els2) by join auto. 
    eapply join_sig_get in Hpre; eauto. 
    eapply join_get_r; eauto. 
  }
  assert (absev = (e, w)).
  {
    unfold get in Habsev. destruct EcbMap. 
    unfold Maps.get in Hget.
    rewrite Hget in Habsev.
    inverts Habsev. auto. 
  }
  subst absev.
  
   (*event type not q -------------------------L8 ~ L10*)
  hoare unfold.
  hoare forward; pure_auto.
  instantiate (1:=Afalse).
  pure intro.
  apply notint_neq_zero_eq in H14.
  unfold OS_EVENT_TYPE_Q in H14.
  
  
 (*  lzh_hoare_if2. *)
  eapply backward_rule1.
  intros.
  sep_lifts_trms_in H35 AEventData.
  eapply eventtype_neq_q' in H35; eauto. 
  hoare_split_pure_all.
  
    casetac v'2 (V$ OS_ERR_EVENT_TYPE) Hopveq Hopvne.
    2: {
      hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid). 
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply qpost_absinfer_type_err_abt; eauto.
      go. 
      eapply absinfer_eq.
      apply absabort_rule.
    }
    hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply qpost_absinfer_type_err; eauto.
    go. 
    eapply absinfer_eq.
  
  (*********  exit critical ***********)
  fold_AEventNode_r. 
  compose_evsllseg. 
  fold_AECBList. 
  
  hoare forward prim.
  unfold EvtInv.
  sep pauto.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.

  trycancel_EvtInv.  
  eauto.
  go. go. go. go. go.

  hoare forward.
  instantiate (1:=($ OS_ERR_EVENT_TYPE)).
  unfold OS_ERR_EVENT_TYPE.
  auto with zarith.
  splits; eauto.
  unfold OS_ERR_EVENT_TYPE.
  clear. int auto.
  unfold OS_ERR_EVENT_TYPE.
  clear.
  change Byte.max_unsigned with 255.
  int auto.
  
  (* elim Afalse *)
  hoare forward.
  
  pure intro.
  remember (Int.eq i1 (Int.repr OS_EVENT_TYPE_Q)) as X.
  destruct X;simpl in H14;destruct H14;tryfalse.
  hoare lift 4%nat pre.
  apply hoare_pure_gen with (p:=(exists v1 v2 v3 v4, v'33 = DMsgQ v1 v2 v3 v4)).
  intros.
  unfold AEventData in H17.
  destruct v'33;
  try solve [
    sep split in H17;
  unfolds in H34; simpl in H34;
  inverts H34;
  rewrite Int.eq_false in HeqX; tryfalse].
  eauto.
  pure intro.
  (*finish*)
  
  (* exists task waiting -------L11 ~ L16 ----------- *)
  apply hoare_pure_gen with (p := (exists a, x0=x2 /\ x2 = Vptr (a, Int.zero))).
  clear - H. clear H. clears.
  intros.
  simpljoin.
  unfold AEventData in H.
  sep split in H.
  unfolds in H0; simpl in H0; inverts H0.
  unfold AMsgData in H; unfold AOSQCtr in H; unfold node in H.
  sep normal in H.
  do 2 destruct H; sep split in H.
  destruct H0; substs.
  eauto.
  pure intro.
  
  hoare forward; pure_auto.
  instantiate (1:=Afalse).
  
  pure intro.
  apply notint_neq_zero_eq in H14.
  clear H17 H34.
  hoare forward.
  
  (*call OS_EventTaskRdy*)
  unfold AOSTCBList.
  unfold AOSTCBPrioTbl.
  hoare normal pre.
  pure_intro.
  hoare_lifts_trms_pre (Aisr, Ais, aemp_isr_is).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  hoare_lifts_trms_pre Aop.
  hoare forward.
  
  apply isptr_zh; auto.
  instantiate (3:= (v'6 ++ v'7 :: v'8)).  
  sep_lifts_trms_in H42 ((tcbdllseg v'4), (tcbdllseg(Vptr ct))).
  eapply tcbdllseg_compose in H42.
  (* pre conditions of OS_EventTaskRdy*)
  sep cancel tcbdllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  
(*   unfold AOSPostEventTbl.  *)
  sep normal.
  sep eexists.
  instantiate (16:= etbl).  
  
  sep split; eauto.
  sep cancel  AOSPostEventTbl.
  sep cancel  Astruct.
  sep cancel Aarray.
  sep cancel AEventData.
  sep cancel AOSRdyTblGrp.
  sep cancel p_local.
  eauto.

  split; pure_auto.
  split.
  pure_auto.
  intro; substs.
  clear - H14; rewrite Int.eq_true in H14; tryfalse.
  simpl; eauto.
  simpl; eauto.
  simpl; auto. 
  2: eauto .
  2: eauto .  2: eauto .
  lets Hx: TCBList_P_Combine H35 H36; eauto.

  sep_lifts_trms_in H42 tcbdllseg.
  eapply tcbdllseg_get_last_tcb_ptr; eauto.
  sep_lifts_trms_in H42 ((tcbdllseg v'4), (tcbdllseg(Vptr ct))).
  eapply tcbdllseg_combine_ptr_in_tcblist; eauto.
  
  pure_auto.
  intros.
  sep auto.
  intros.
  sep auto.
  
  unfold isptr in H1.
  destruct H1.
  rewrite H1. auto.
  destruct H1. 
  rewrite H1. auto.
(*finished side conditions*)
  rename H40 into Hrh_priotbl_p; rename H41 into H40.
  hoare normal pre.
  hoare unfold.
  rename H57 into Hxx1; rename H58 into Hxx2; rename H59 into Hxx3; 
  rename H60 into Hxx4; rename H61 into Hxx5; rename H73 into Hxx6; 
  rename H74 into Hxx7. rename H75 into vl_stv_match.
  
(*   rename H57 into H52; rename H58 into H53; rename H59 into H54. 
  rename H60 into H55; rename H61 into H56; rename H62 into H57.  
  rename H63 into H58; rename H64 into H59. rename H68 into H60. *)

  inverts H71.
  
  
  (*after OS_EventTaskRdy*)

  (*prove some properties used by the following reasoning*)
  
  (*1: get the range info of the event table elements*)
  assert ((Int.unsigned v'72 <= 7)%Z) as y_le7. 
  clear - H25 H49.
  lets Hx: osunmapvallist_prop H25; simpljoin.
  rewrite H in H49; inverts H49.
  apply Z.leb_le in H0; auto. 

  assert (Int.unsigned v'73 <= 255)%Z as erow_le255.
  clear - H50 Hxx5 H22 y_le7.
  assert (Z.to_nat (Int.unsigned v'72) < length v'52)%nat.
  rewrite H22; unfold OS_EVENT_TBL_SIZE.
  mauto.
  lets Hx: array_int8u_nth_lt_len Hxx5 H; simpljoin.
  rewrite H50 in H0; invert H0; auto.

  assert(Int.unsigned v'71 <= 7)%Z as x_le7.
  clear - H51 erow_le255.
  lets Hx: osunmapvallist_prop erow_le255; simpljoin.
  rewrite H in H51; inverts H51.
  apply Z.leb_le in H0; auto.
  
(*prepare for EXIT_CRITICAL;ₛ*)
  unfold AEventNode.
  unfold AOSEvent, AEventData.
  unfold AOSEventTbl, AMsgData.
  unfold AOSQCtr; unfold AOSQBlk; unfold node.
  
  (*abs step*)
  lets Hx : ecbmod_absmsgq Hrlh; simpljoin.
  symmetry in HeqX.
  lets Hx: Int.eq_spec i1 (Int.repr OS_EVENT_TYPE_Q).
  rewrite HeqX in Hx; substs.
  
  pure intro. (*x1 is destructed here*)
  pose proof Int.eq_spec v'50 (Int.repr 0). 
  rewrite H14 in H46.
  
  Open Scope int_scope.
  
  assert(exists n m tcbls sus, TcbJoin (v'89, Int.zero) (((v'72<<ᵢInt.repr 3) +ᵢ  v'71), wait (os_stat_q (v'10, Int.zero)) n, m,sus) tcbls v'42) as tcbls_tcbjoin.
  unfolds in Hecbetbl; simpljoin.
  unfolds in H54; simpljoin.
  unfolds in H54.
  unfold V_OSEventType in H54; simpl in H54.
  pose proof H54 (Int.unsigned ((v'72<<ᵢInt.repr 3) +ᵢ  v'71)).
  assert(PrioWaitInQ (Int.unsigned ((v'72<<ᵢInt.repr 3) +ᵢ  v'71)) v'52).
  unfolds.
  assert(($ Int.unsigned ((v'72<<ᵢ$ 3) +ᵢ  v'71) >>ᵢ $ 3) = v'72) as xx1.
  clear - y_le7 x_le7.
  mauto.
  rewrite xx1.
  assert(($ Int.unsigned ((v'72<<ᵢ$ 3) +ᵢ  v'71)&ᵢ$ 7) = v'71) as xx2.
  clear - y_le7 x_le7.
  mauto.
  rewrite xx2.
  exists v'71 v'72 v'73.
  splits; eauto.
  clear - y_le7 x_le7.
  mauto.
  apply nth_val'2nth_val; eauto.
  eapply math_8_255_eq; eauto.
  pose proof rl_tbl_grp_neq_zero.
  lets Hx: rl_tbl_grp_neq_zero Hxx4; eauto.
  clear - y_le7.
  mauto.
  assert (Some (V$ OS_EVENT_TYPE_Q) = Some (V$ OS_EVENT_TYPE_Q)) by auto.
  apply H86 in H88; auto.
  simpljoin. rename  x13 into sus.

  unfolds in H68; simpljoin.
  apply nth_val'2nth_val' in H43.
  lets Hx: H68 H43 H76.
  clear - y_le7 x_le7.
  mauto.
  simpljoin. rename x18 into sus'.

  clear - H90 H88 H91.
  unfold get in H88, H91; simpl in H88, H91.
  rewrite Int.repr_unsigned in H88.
  lets Hx: R_Prio_No_Dup_tid_eq H90 H88 H91.
  simpljoin.
  unfold TcbJoin.
  exists x7 x14 .
  unfold join, sig; simpl.
  exists (TcbMod.minus v'42 (TcbMod.sig (v'89, Int.zero)
        ((v'72<<ᵢ$ 3) +ᵢ  v'71, wait (os_stat_q (v'10, Int.zero)) x7, x14, sus'))).
  eexists.
  eapply TcbMod.map_join_minus. 
  eapply language.TcbMap_obligation_30. auto.
  
(*   unfold TcbMod.join.
  intros.
  destruct (tidspec.beq  (v'88, Int.zero) a) eqn : eq1.
  lets Hx: tidspec.beq_true_eq eq1.
  substs.
  rewrite TcbMod.minus_sem.
  rewrite TcbMod.get_sig_some.
  rewrite H90; auto. 
  lets Hx: tidspec.beq_false_neq eq1.
  rewrite TcbMod.minus_sem.
  rewrite TcbMod.get_sig_none; auto.
  destruct (TcbMod.get v'41 a); auto.
   *)
  simpljoin.
  rename x13 into sus.
  lets Hx: post_exwt_succ_pre H46 H68 H18 Hecbetbl H0.
  lets Hx1: Hx Hjo Hjo' H25 H15 H22; clear Hx.
  lets Hx2: Hx1 H49 y_le7 H50 erow_le255 H51.
  lets Hx3: Hx2 x_le7 H43 H54.
  simpljoin.

  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_part2; eauto.
  trycancel_EvtInv.
  sep pauto.
  
  assert (Hv'2cs: v'2 <> Vint32 (Int.repr OS_NO_ERR) \/
                  v'2 = Vint32 (Int.repr OS_NO_ERR)) by tauto. 
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid,EvtInv_part2).
  inversion Hv'2cs.
  
   (* v'1 <> ... *) 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpost_absinfer_exwt_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule.
  (* v'1 = ... *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpost_absinfer_exwt_succ; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq.
   (*prove TCBList_P hold for the new vltcb and tcbls*)
  clear Hx1 Hx2.

  assert (R_Prio_No_Dup v'42).
  clear - H68.
  unfolds in H68; simpljoin; auto.

  assert (v'83 = $ OS_STAT_Q \/ v'83 = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND)) as Hx.
  {
  clear - H48.
  simpl in H48; substs. auto. }
  
  (*split the new vltcb in hoare pre*)
  hoare_lifts_trms_pre tcbdllseg. 
  lets old_tcbnode_p : TCBList_P_tcblist_get_TCBNode_P H70 H44 H63.
  generalize old_tcbnode_p; intro Htmp.
  unfolds in Htmp.
  mytac.
  inverts H85; inverts H86. 
  rename H87 into Hh_tcbblk.
  rename H88 into Hh_tcbstat. 
  unfolds in Hh_tcbblk.
  mytac.
  inverts H40. inverts H89. inverts H96. inverts H69. 
  inverts H86. inverts H85. inverts H87. inverts H64.
  
  eapply set_node_elim_hoare_sus
  with (st':=rdy) (m':=v'64)
       (rtbl':=update_nth_val (Z.to_nat (Int.unsigned v'72)) v'46
                              (Vint32 (Int.or v'90 v'74))); eauto.
  
  (*TCBNode_P*)
  {
  eapply TCBNode_P_set_rdy_gen; auto. 6:{eauto . }

  assert((((v'72<<ᵢ$ 3) +ᵢ  v'71) >>ᵢ $ 3) = v'72).
  clear - y_le7 x_le7.
  mauto.
  rewrite H64.
  apply nth_val'2nth_val. auto.
  clear - H41 Hxx2 Hxx6 y_le7.
  assert (Z.to_nat (Int.unsigned v'72) < length v'46)%nat.
  rewrite Hxx6.
  eapply z_le_n_lt'; auto.
  lets Hx: array_int8u_nth_lt_len Hxx2 H.
  simpljoin.
  rewrite H41 in H0.
  inverts H0; auto.
  2: {
  clear - y_le7 x_le7.
  mauto. }
  2:{ 
  assert((((v'72<<ᵢ$ 3) +ᵢ  v'71)&ᵢ$ 7) = v'71).
  clear - y_le7 x_le7. 
  mauto.
  rewrite H64.
  eapply math_mapval_core_prop; auto.
  clear - x_le7.
  mauto. }

  destruct Hx; subst x21.
  assert (Hsus: sus = false) by
  (  eapply oscore_common.tcb_stat_imp_sus_false ;
   try solve [unfolds; simpl; eauto]; eauto).
  subst.
  rewrite Int.and_not_self; auto.
  assert (Hsus: sus = true) by
  (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
  subst.
  change (Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_Q)) with ($ OS_STAT_SUSPEND).
  auto.
  }
  destruct sus;auto.
(*rtbl_set_one_bit*)
{  
  unfolds.
  assert((((v'72<<ᵢ$ 3) +ᵢ  v'71) >>ᵢ $ 3) = v'72).
  clear - y_le7 x_le7.
  mauto.
  rewrite H64.
  assert((((v'72<<ᵢ$ 3) +ᵢ  v'71)&ᵢ$ 7) = v'71).
  clear - y_le7 x_le7.
  mauto.
  rewrite H69.
  do 2 eexists.
  splits; eauto.
}  
  unfolds; simpl; auto.
  
  assert (Heq_sus: Int.eq (x21&ᵢInt.not ($ OS_STAT_Q)) ($ OS_STAT_RDY) = negb sus).
  { change ($ OS_STAT_RDY) with Int.zero.
    destruct Hx; subst x21.
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
   
  hoare unfold.
  hoare_lifts_trms_pre (Aisr, Ais, Aier).
  transform_pre add_aemp_isr_is_prop ltac:(sep cancel Aisr; sep cancel Ais; sep cancel aemp_isr_is). 
  (* L14 : EXIT_CRITICAL;ₛ *)
  hoare forward prim. 
(*   
  Ltac hoare_exit_critical2 :=
    match goal with
    | |- {|_ , _, ?li , _, _, _|}|- _ {{?P}} (sprim excrit) {{_}} =>
      match find_aop P with
      | some ?n =>
        hoare lifts (n::nil) pre;
        eapply excrit1_rule'_ISnil_ISRemp'''_lg(* excrit1_rule'_ISnil_ISRemp''' *);
        [ intros; try (unfold OldOSInvWL); (*sep pauto;*)trycancel
        | idtac
        ]
      | _ => fail 1
      end
    end.
  Ltac hoare_forward_prim'2 :=
    let s := fresh in
    let H := fresh in
    match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} (sseq _ _) {{ _ }} =>
      eapply seq_rule; [ hoare_forward_prim'2
                       | try hoare_invchange ]
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
      eapply forward_rule2; [ first [ hoare_enter_critical
                                    | hoare_exit_critical2
                                    | idtac ]
                            | first [ intros s H; exact H
                                    | sep pauto ] ]
    end.
  hoare_forward_prim'2.

  sep normal.
  sep eexists.
  sep cancel AOSMapTbl.
  sep cancel AOSUnMapTbl.
  sep cancel AOSTCBFreeList.
  sep cancel AOSTime.
  sep cancel AGVars.
  sep cancel A_isr_is_prop.
  sep cancel abstcblsid.
  sep cancel ostmid. 
  sep cancel curtid.
  sep cancel Aier.
  sep split; auto.
  sep cancel p_local.

  sep cancel AOSRdyTblGrp.
  sep cancel IntInv.
  sep cancel TmrInv.
  sep cancel CoreCommuInv.
  sep cancel PartitionInv.
  sep cancel CapabilityInv. *)
(*AOSTCBPrioTbl*)
  unfold AOSTCBPrioTbl.
  sep normal.
  sep eexists. inverts H72.
  sep cancel GAarray.
  sep cancel 15%nat 1%nat. 
  sep cancel OSPlaceHolder.
  sep cancel Aier.
  sep split; eauto.
  sep cancel absptlsid.
(*AOSTCBList*)
  unfold AOSTCBList.
  sep normal. do 4 eexists.
  sep cancel OSTCBList.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 2%nat.
  sep cancel OSTCBCur.
  sep split; eauto.

  (*p_local*)
  sep cancel p_local.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  
  eapply fold_EvtInv_frm'.
  trycancel_EvtInv.
  cancel_corecommuinv.

  unfold AECBList.
  sep normal.
  eexists. 
  sep cancel OSEventList.
(*   simpl update_nth_val in H85. *)
  sep split.
  eapply evsllseg_compose; eauto.
  instantiate (2:= (V$ OS_EVENT_TYPE_Q
            :: Vint32 v'51 :: Vint32 i2 :: Vptr (v'24, Int.zero) :: x3 :: v'' :: Vint32 i :: x6 :: nil)).
  unfolds; simpl; eauto.
  instantiate (10:=(DMsgQ (Vptr (v'24, Int.zero))
             (x16
              :: x15
                 :: x9
                    :: x10
                       :: x11
                          :: Vint32 i1
                             :: Vint32 i0 :: Vptr (v'43, Int.zero) :: nil)
             (x1 :: x17 :: nil) x5)).
  unfold AEventNode.
  unfold AOSEvent, AEventData.
  unfold AOSEventTbl,  AMsgData. 
  unfold AOSQCtr, AOSQBlk; unfold node.
  sep normal. sep eexists. 
  instantiate (22:= (update_nth_val (Z.to_nat (Int.unsigned v'72)) v'52
              (Vint32 (v'73&ᵢInt.not v'74)))).
  sep split; eauto.
  do 2 sep cancel 9%nat 7%nat.
  do 6 sep cancel 2%nat 1%nat.
(*   
  unfold tcbllsegevaux in *.

  sep_lift_context_in H85 llsegevaux.
  sep_lift_context llsegevaux.
  eapply llsegevaux_set_node;eauto.
  2:{
    unfold same_prev_next; simpl;auto.
  }
  sep cancel llsegevaux. *)
  (*tcbdllflag*)
  
  sep_lifts_trms_in H88 tcbdllflag.
  eapply tcbdllflag_set_node in H88; eauto.
  2:{ unfolds; simpl; auto. }
  sep cancel tcbdllflag. 
  rewrite <- H64.
  eapply evtinv_part2_set_node; eauto.
  sep cancel EvtInv_part2.
  
  (* PartitionInv *)
  Require Import sem_partition.
  cancel_partitioninv.
  eauto.
  (* end of Partition *)
  
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  splits;auto;go.
  splits;auto;go.
  
  (*ECBList_P*)
  {
  eapply ecblist_p_post_exwt_hold1; eauto.
  clear - H53 x_le7.
  lets Hx: osmapvallist_prop x_le7; simpljoin.
  rewrite H53 in H; inverts H.
  auto. }
  auto.
  (* TCBList_P *)
  rewrite Heq_sus. rewrite negb_if.
  eauto.
  rewrite Heq_sus. rewrite negb_if.
  eauto.
  (*R_PrioTbl_P *)
  {  eapply r_priotbl_p_set_hold; auto; eauto. }
  
  assert(ct = (v'89, Int.zero) \/ ct <> (v'89, Int.zero)).
  tauto.
  destruct H94.
  substs.
  unfolds.
  unfold get; simpl.
  rewrite TcbMod.set_a_get_a.
  eauto.
  apply tidspec.eq_beq_true; auto.
  eapply rh_curtcb_set_nct; auto.
  (*RH_TCBList_ECBList_P*)
  eapply rh_tcblist_ecblist_p_post_exwt; eauto. 
  clear - H58.
  unfolds in H58; simpljoin; auto.

  pure_auto.
  
  (*L15: OS_Sched (­);ₛ*)
  hoare forward.
  unfolds; left; auto.
  pure_auto.
  intros.
  sep auto.
  sep cancel p_local.
  simpl; auto.
  intros.
  sep auto.
  sep cancel 1%nat 1%nat.
  simpl; auto.
  
  hoare unfold.
  inverts H88.
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply absinfer_seq_end.
  pure_auto.
  2: eauto.
  pure_auto.
  eapply absinfer_eq.
  
  (*L16:  RETURN ′ OS_NO_ERR*)
  hoare forward.
  unfold rev; simpl.
  intro. inverts H91.
  
  instantiate (1:=($ OS_NO_ERR)).
  unfold OS_NO_ERR.
  splits; eauto.
  clear. int auto.

  hoare forward.

  (*L17: pq ′ =ₑ pevent ′ → OSEventPtr;ₛ*)
  hoare forward.
  pure_auto.
  pure_auto.

(*L18: If(pq ′ → OSQEntries ≥ pq ′ → OSQSize)*)
  unfold AEventData.
  hoare unfold.
  hoare forward; pure_auto.
  instantiate (1 := Afalse).
  pure intro.

(*high level step*)
  remember (Int.ltu i4 i3) as Y.
  remember (Int.eq i3 i4 ) as Z.
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
  clear H17 H39.

  assert (true = Int.ltu i4 i3 \/ true = Int.eq i3 i4).
  destruct Y;destruct Z;simpl in H14; try rewrite H48 in H14;tryfalse;try rewrite H49 in H14;tryfalse;try rewrite H50 in H14;tryfalse;try rewrite H51 in H14;tryfalse; auto.
  simpl in H14; tryfalse.
  lets Hy:ecbmod_absmsgq Hrlh; simpljoin.
  change ((Vptr (v'40, Int.zero) :: x :: nil) ++ v'2 :: nil) with (Vptr (v'40, Int.zero) :: x :: v'2::nil).
  assert (Hor: v'2 <> (Vint32 (Int.repr MSGQ_OVF_ERR)) \/ 
                 v'2 = (Vint32 (Int.repr MSGQ_OVF_ERR))) by tauto.
  inversion Hor.
  (* v'2 <> ... *)
  hoare_lifts_trms_pre (Aop, absecblsid). 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpost_absinfer_ovf_abt; eauto.
  can_change_aop_solver. 
  eapply qpost_ovf_prop1; eauto.
  eapply absinfer_eq.
  eapply absabort_rule.
  (* v'2 = ... *)
  hoare_lifts_trms_pre (Aop, absecblsid). 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpost_absinfer_ovf;eauto.
  can_change_aop_solver.
  eapply qpost_ovf_prop1;eauto.
  eapply absinfer_eq.
  
  (*L19: EXIT_CRITICAL;ₛ*)
  hoare forward prim.
  unfold EvtInv.
  sep normal. sep pauto.
  trycancel_EvtInv.

  unfold AECBList.
  sep normal.
  eexists.
  sep cancel Aier.
  sep cancel (Agvarmapsto OSEventList).
  sep cancel p_local.
  sep split; eauto.
  eapply evsllseg_compose; eauto. 
  unfolds; simpl; eauto. 
  do 2 sep cancel 8%nat 2%nat.

  unfold AEventNode.
  unfold AOSEvent, AEventData.
  unfold node, AOSEventTbl, AMsgData.
  unfold AOSQCtr; unfold AOSQBlk; unfold node.
  sep normal; sep eexists.
  sep split; eauto.
  do 3 sep cancel 1%nat 1%nat.
  do 3 sep cancel 2%nat 1%nat.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  exact H52.

  split; auto;  go.
  split; auto;  go.
  split; auto;  go.
  split; auto;  go.
  go. go. go. go. pure_auto.
(*L20: RETURN ′ OS_Q_FULL*)
  hoare forward.
  (*elim afalse*)
  hoare forward.
  
  (*L21: ∗ pq ′ → OSQIn =ₑ message ′;ₛ*)
  lets Hx: osq_same_blk_st_in' H38. simpljoin.
  simpl in H36; inverts H36.
  lets Hy: wellq_in_props H40 Hrlh H38;eauto.
  simpljoin.

  hoare forward; eauto.
  pure_auto. 
  apply isptr_zh;auto.

  (*L22: pq ′ → OSQIn =ₑ pq ′ → OSQIn +ₑ ′ 1;ₛ*)
  hoare forward.
  pure_auto.
  go.
  pure_auto.

  (*L23: pq ′ → OSQEntries =ₑ pq ′ → OSQEntries +ₑ ′ 1;ₛ*)
  hoare forward.
  pure_auto.
  go.
  pure_auto.
  
  (*L24: If(pq ′ → OSQIn ==ₑ pq ′ → OSQEnd)*)
  pure intro.
  lets Hx: wellformedosq_ens_add_1 H40 Hrlh H38.
  hoare forward.
  pure_auto.
  go.

  clear - H43.
  destruct x0; unfolds in H43;
  destruct H43; tryfalse; destruct H; tryfalse.
  simpl; intro; tryfalse.
  destruct a.
  inverts H.
  destruct (peq v'33 b);
    destruct (Int.eq (x4 +ᵢ  Int.mul ($ 1) ($ 4)) i); simpl; intro; tryfalse.
  
  (*L25: pq ′ → OSQIn =ₑ pq ′ → OSQStart*)
  hoare forward.
  pure_auto.
  go.
  pure_auto.

  assert (exists a, x0 = Vptr a).
  clear - H38.
  unfolds in H38; simpl in H38; simpljoin.
  unfolds in H0; simpl in H0; inverts H0.
  eauto. 
  simpljoin.

  (*combine the 2 cases after if*) 
  eapply backward_rule1 with
  (p:= (EX new_qin,
        [| ((v'33, x4 +ᵢ  Int.mul ($ 1) ($ 4)) = x2 /\ new_qin = x12) \/
         ((v'33, x4 +ᵢ  Int.mul ($ 1) ($ 4)) <> x2 /\ new_qin = (Vptr (v'33, x4 +ᵢ  Int.mul ($ 1) ($ 4)))) |] **
      <|| spec_code_cons (qpost ((Vptr (v'40, Int.zero) :: x :: nil) ++ v'2 :: nil)) v'1 ||>  **
         LV pq @ OS_Q ∗ |-> Vptr (v'21, Int.zero) **
         Astruct (v'21, Int.zero) OS_Q
           (x13
            :: x12 :: Vptr x2 :: new_qin :: x8 :: Vint32 i4 :: Vint32 (i3 +ᵢ  $ 1) :: Vptr (v'33, Int.zero) :: nil) **
         Aarray (v'33, Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero)) (Tarray (Void) ∗ ∘ OS_MAX_Q_SIZE)
           (update_nth_val (Z.to_nat ((Int.unsigned x4 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
              x5 x) **
         Astruct (v'33, Int.zero) OS_Q_FREEBLK (x1 :: x14 :: nil) **
         Astruct (v'40, Int.zero) OS_EVENT
           (V$ OS_EVENT_TYPE_Q
            :: Vint32 i0 :: Vint32 i2 :: Vptr (v'21, Int.zero) :: x3 :: v'' :: Vint32 i :: x6 :: nil) **
         Aarray v'36 (Tarray char_t ∘ OS_EVENT_TBL_SIZE) etbl **
         AOSPostEventTbl v'38 petbl **
         evsllseg v'11 (Vptr (v'40, Int.zero)) v'19 v'31 **
         evsllseg v'' Vnull v'20 v'32 **
         GV OSEventList @ OS_EVENT ∗ |-> v'11 **
         AOSEventFreeList fecbh fecbvl **
         AOSQFreeList v'22 **
         AOSQFreeBlk v'23 **
         HECBList els **
         Hebls v'35 **
         AErrblkList v'35 **
         Hpbls v'34 **
         APosblkList v'34 **
         HEvAtomHeap v'25 **
         AEvAtomHeap v'25 **
         HEvStructHeap v'26 **
         AEvStructHeap v'26 **
         HEvArrayHeap v'27 **
         AEvArrayHeap v'27 **
         HSEMInfo semeibs **
         ASemEIBs v'28 v20 semeibs els vhold_addr **
         HMuxInfo muxeibs **
         AMuxEIBs v'29 v21 muxeibs els vhold_addr **
         HQAttr mqeibs **
         AMqEIBs v'30 v22 mqeibs els vhold_addr **
         HEvLoc locmp **
         HEvPtr ptrmp **
         APthreadAttr v'18 **
         tcbllsegevaux v'4 (v'6 ++ v'7 :: v'8) locmp ptrmp **
         AOSMapTbl **
         AOSUnMapTbl **
         AOSTCBPrioTbl v'3 v'9 v'12 v'17 vhold_addr **
         AOSTCBList v'4 v'5 v'6 (v'7 :: v'8) v'9 ct v'12 **
         AOSTCBFreeList v'15 v'16 **
         AOSRdyTblGrp v'9 v'10 **
         AOSTime (Vint32 v'13) **
         HTCBList v'12 **
         HTime v'13 **
         HCurTCB ct **
         AGVars **
         A_isr_is_prop **
         IntInv **
         TmrInv **
         CoreCommuInv els **
         PartitionInv els **
         CapabilityInv vcspace **
         tcbdllflag v'4 (v'6 ++ v'7 :: v'8) **
         p_local OSLInv ct
           (logic_val (V$ 1)
            :: logic_val (V$ os_code_defs.__EvLoc_normal)
               :: logic_val Vnull :: logic_val Vnull :: logic_val (Vptr (v'40, Int.zero)) :: nil) **
         Aisr empisr **
         Aie false **
         Ais nil **
         Acs (true :: nil) **
         Aier vier **
         aemp_isr_is **
         LV os_code_defs.x @ Int16u |-> v'0 **
         LV message @ (Void) ∗ |-> x **
         LV pevent @ OS_EVENT ∗ |-> Vptr (v'40, Int.zero) **
         A_dom_lenv
          ((message, (Void) ∗) 
            :: (pevent, OS_EVENT ∗) 
            :: (pq, OS_Q ∗) 
            :: (os_code_defs.x, Int16u) :: nil)
          )).

  intros.
  destruct H50.
  
  (*if true*)
  sep auto.
  left.
  split; auto.
  simpljoin.
  clear - H60.
  destruct x2.
  destruct (peq v'33 b) eqn : eq1;
    destruct (Int.eq (x4 +ᵢ  Int.mul ($ 1) ($ 4)) i) eqn : eq2;
    simpl in H60; tryfalse.
  substs.
  pose proof Int.eq_spec (x4 +ᵢ  Int.mul ($ 1) ($ 4)) i.
  rewrite eq2 in H.
  substs; auto.

  (*if false*)
  sep auto.
  right.
  split; auto.
  simpljoin.
  clear - H60.
  destruct x2.
  destruct (peq v'33 b) eqn : eq1;
    destruct (Int.eq (x4 +ᵢ  Int.mul ($ 1) ($ 4)) i) eqn : eq2;
    simpl in H60; destruct H60; tryfalse.
  substs.
  intro.
  inverts H0.
  pose proof Int.eq_spec (x4 +ᵢ  Int.mul ($ 1) ($ 4)) (x4 +ᵢ  Int.mul ($ 1) ($ 4)).
  rewrite eq2 in H0.
  tryfalse.

  intro. inverts H0.
  tryfalse.

  intro; inverts H0.
  tryfalse.
  
  pure intro.

  (*high level step*)
  lets Hx1: ecbmod_absmsgq Hrlh.
  lets Hx2: EcbMod.join_joinsig_get Hjo  Hjo' .
  simpljoin.
  
  assert(Int.eq i0 ($ 0) = true).
  clear - H34.
  destruct (Int.eq i0 ($ 0)) eqn : eq1; simpl in H34; auto.
  unfold Int.notbool in H34.
  rewrite Int.eq_true in H34.
  destruct H34; tryfalse.
  lets Hx3: rlh_ecb_nowait_prop H18 Hecbetbl Hx2 H0 H51; substs.
  
  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_part2; eauto.
  trycancel_EvtInv.
  sep pauto.
  
  change ((Vptr (v'40, Int.zero) :: x :: nil) ++ v'2 :: nil) with (Vptr (v'40, Int.zero) :: x :: v'2::nil).
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid,EvtInv_part2).
  assert (Hor: v'2 <> (Vint32 (Int.repr OS_NO_ERR)) \/ 
                 v'2 = (Vint32 (Int.repr OS_NO_ERR))) by tauto.
  inversion Hor.
  (* v'2 <> ... *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpost_absinfer_nowt_succ_abt.
  can_change_aop_solver.
  eauto. eauto.
  
  assert(Int.ltu i3 i4 = true).
  clear - H39.
  apply val_inj_i1_i2_lt in H39; auto.
  eapply qpost_no_wait_prop'; eauto.
  eapply absinfer_eq.
  eapply absabort_rule.
  
  (* v'2 = ... *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qpost_absinfer_nowt_succ.
  pure_auto. eauto. eauto.
  assert(Int.ltu i3 i4 = true).
  clear - H39.
  apply val_inj_i1_i2_lt in H39; auto.

  eapply qpost_no_wait_prop'; eauto.
  eapply absinfer_eq.

  (*L26: EXIT_CRITICAL;ₛ*)
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eapply fold_EvtInv_frm'.
  trycancel_EvtInv.
  cancel_corecommuinv.
  sep cancel EvtInv_part2.
  unfold AECBList.
  sep normal.
  eexists.
  sep cancel (OSEventList).
  sep split.
  
  eapply evsllseg_compose with
  (l:= (V$ OS_EVENT_TYPE_Q
            :: Vint32 i0
               :: Vint32 i2 :: Vptr (v'21, Int.zero) :: x3 :: v'' :: Vint32 i :: x6 :: nil)
  ).
  unfolds; simpl; eauto.
  eauto.
  eauto.
  do 2 sep cancel 8%nat 2%nat.

  instantiate (2:=
                 (DMsgQ (Vptr (v'21, Int.zero))
                        (x13
                          :: x12
                             :: Vptr x2
                                :: v'14 :: x8 :: Vint32 i4 
                                      :: Vint32 (i3 +ᵢ  $ 1) :: Vptr (v'33, Int.zero) :: nil)
                        (x1 :: x14 :: nil)
                        (update_nth_val
                          (Z.to_nat ((Int.unsigned x4 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
                          x5 x)
                 )).
  unfold AEventNode;
  unfold AOSEvent, AEventData; unfold AOSEventTbl;
  unfold AMsgData; unfold AOSQBlk, AOSQCtr; unfold node.
  sep normal; sep eexists.
  instantiate (12:= etbl).  
  sep split; eauto.
  sep cancel 4%nat 1%nat.
  sep cancel 3%nat 1%nat.
  do 4 sep cancel 2%nat 1%nat.
  cancel_partitioninv.
  eauto.

  split; auto.
  go.
  unfolds; simpl; eauto.
  {
    destruct H50; simpljoin.
    eapply get_wellformedosq_in_setst; eauto.
    apply val_inj_i1_i2_lt; auto.
    rewrite peq_true.
    rewrite Int.eq_true.
    simpl; intro; tryfalse.
    
    eapply get_wellformedosq_in_setst'; eauto.
    intro. inverts H52; tryfalse.
    apply val_inj_i1_i2_lt; auto.
  }

  split; auto.
  go.
  {
    clear - H41 H50.
    destruct H50; simpljoin; auto.
    unfolds in H41; destruct H41; simpljoin; auto.
  }
  pure_auto.
  lets Hx1: get_wellformedosq_in_setst H38.
  apply val_inj_i1_i2_lt; auto. auto.
  split; auto.
  go.

  eapply msgqlist_p_compose'; eauto.
  destruct H1.
     subst x.
     clear -H11. simpl in H11. destruct H11;tryfalse.
     destruct H1 as (p & H1).
     subst x.
  {  (*destruct the if condition here*)
    destruct H50; simpljoin.
    eapply rlh_ecbdata_in_end;eauto.
    eapply val_inj_i1_i2_lt; auto.

    eapply rlh_ecbdata_in_noend; eauto.
    clear - H1.
    intro; inversion H; apply H1; auto.
    eapply val_inj_i1_i2_lt; auto.
  }
  eapply EcbMod.joinsig_set;eauto.
  eapply EcbMod.joinsig_set_set;eauto.
  eapply rh_tcbls_mqls_p_setmsg_hold;eauto.

  pure_auto.

  (*L27: RETURN ′ OS_NO_ERR*)
  hoare forward.
  unfold rev; simpl.
  intro. tryfalse.
  instantiate (1:=($ OS_NO_ERR)).
  unfold OS_NO_ERR.
  splits; eauto.
  clear. int auto.
  
  Unshelve.
  exact Int.zero. 
  exact v'10.
  exact v'64. exact v'64. 
  exact v'7. 
  exact v'13. 
  exact v'40.
  exact v'2. exact v'15.
  exact v'3.
Qed.
Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import os_ucos_h.

Require Import os_q.
Require Import include_frm. 
Require Import abs_infer_step.
Require Import ucos_frmaop.
Require Import seplog_lemmas.
Require Import seplog_tactics.
Require Import abs_infer_abt.
Require Import gjb_common.
Require Import OSTimeTickPure.
Require Import evt_spec_defs.

Require Import abs_op.
Require Import init_spec.
Require Import inv_prop. (*change*)
Require Import hoare_tactics.
Require Import pure_auto.
Require Import ucos_pauto.
Require Import seplog_tactics.
Require Import seplog_lemmas.
Require Import sep_cancel_ext.
Require Import derived_rules.
Require Import hoare_conseq.
Require Import ucos_forward. (*change*)
Require Import sem_lab.
Require Import Lia.
Require Import q_common.
Require Import hoare_forward_tac_ext.
Require Import seplog_trm_tacs.
Require Import evtinv_lemmas.
Require Import gjb_mutex_common.
Require Import gjb_q_common.
Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

Ltac simpl_sat H := unfold sat in H; fold sat in H; simpl substmo in H; simpl getmem in H; simpl getabst in H; simpl empst in H.

Lemma absinfer_seq1:
  forall (p : asrt) (s1 : absop)  (s2 : spec_code) (s1' : absop) (sc : ossched),
                   can_change_aop p ->
                   sc ⊢  <|| s1 ||>  ** p ⇒  <|| s1' ||>  ** p ->
                   sc ⊢  <|| s1;; s2 ||>  ** p ⇒  <|| s1';; s2 ||>  ** p.
Proof.
intros.
eapply absinfer_seq; try eauto.
Qed.


Lemma qquery_absimp_null_abt:
  forall sid pdata v_ret P sch s,
    sid = Vnull ->
    v_ret <> (V$ OS_ERR_PEVENT_NULL) ->
    can_change_aop P ->
    absinfer sch (<|| spec_code_cons (qquerynew (sid :: pdata ::v_ret :: nil)) s ||> ** P) 
               (<||ABORT||> ** P).
Proof.
  introv Hsid Hv' Hcop.
  simpl.
  eapply absinfer_trans. 
  eapply absinfer_choice1.
  3: eauto. pure_auto. pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1; try pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  eapply absinfer_seq_abt; try pure_auto.
Qed. 



Lemma qquery_absimp_null:
  forall sid v_ret pdata P sch s,
    sid = Vnull ->
    v_ret = (V$ OS_ERR_PEVENT_NULL) ->
    can_change_aop P -> 
    absinfer sch ( <|| spec_code_cons (qquerynew (sid :: pdata ::v_ret :: nil)) s ||> ** P) 
                 ( <|| s ||> ** P ).
Proof.
  introv Hsid Hv' Hcop.
  eapply absinfer_trans. 
  simpl.
  eapply absinfer_choice1.
  3: eauto. 
  pure_auto. pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1. pure_auto.
  instantiate (1:=END (Some (V$ OS_ERR_PEVENT_NULL))).
  infer_solver 0%nat. 
  do 2 eexists.
  splits; eauto.
  subst sid. auto. 
  eapply absinfer_seq_end; try pure_auto.
Qed.

Lemma qquery_absimp_pevent_not_in_dom_abt: 
  forall sid els qid pdata v_ret P sch s,
    sid = Vptr qid ->
    get els qid = None -> 
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (qquerynew (sid :: pdata ::v_ret :: nil)) s ||> ** HECBList els ** P) 
      (<|| ABORT ||> ** HECBList els ** P ).  
Proof.
  introv Hsid Hnone Hcop.
  simpl.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  3: eauto. pure_auto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  3: eauto. pure_auto. pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  pure_auto.
  eapply absinfer_seq_abt; try pure_auto. 
Qed.

Lemma qquery_absimp_no_q:
  forall P qls sid pdata v' sch s,
    can_change_aop P ->
    (~ exists x y pwl wls,get qls sid = Some (absmsgq x y pwl,wls) ) ->
    v' = (V$ OS_ERR_EVENT_TYPE) ->
    absinfer sch
      (<|| spec_code_cons (qquerynew ((Vptr sid) :: pdata :: v' :: nil)) s ||> ** HECBList qls ** P) 
      (<|| s ||> ** HECBList qls ** P). 
Proof.
  introv Hcop Hnsem Hv'.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice1. 
  pure_auto. 2: eauto. pure_auto.
  infer_solver 0%nat. 
Qed.

Lemma qquery_absimp_no_q_abt:
  forall P qls sid pdata v' sch s,
    can_change_aop P ->
    (~ exists x y pwl wls,get qls sid = Some (absmsgq x y pwl,wls) ) ->
    v' <>  (V$ OS_ERR_EVENT_TYPE) ->
    absinfer sch
      (<|| spec_code_cons (qquerynew ((Vptr sid) :: pdata :: v' :: nil)) s ||> ** HECBList qls ** P) 
      (<|| ABORT ||> ** HECBList qls ** P). 
Proof.
  introv Hcop Hnsem Hv'.
  eapply absinfer_trans.
  simpl.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  simpl.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice1. 
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_seq1; try pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  can_change_aop_solver.
  eapply absinfer_seq_abt; try pure_auto. 
Qed.

Lemma qquery_absimp_pdata_validptr_err_abt:
  forall evheap sid pdata v' t l P sch s,
  ( Get_struct evheap pdata = None \/
        (Get_struct evheap pdata = Some (pdata, t, l) /\ t <> OS_Q_DATA) ) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| spec_code_cons (qquerynew ((Vptr sid) ::Vptr pdata :: v' :: nil)) s ||> ** HEvStructHeap evheap ** P) 
      (<|| ABORT ||> ** HEvStructHeap evheap ** P). 
Proof.
  intros.
  eapply absinfer_trans.
  simpl.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  simpl.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
    eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.  
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto.
  instantiate (1:= HEvStructHeap evheap ** P).
  pure_auto.
  pure_auto.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto.  instantiate (1:= HEvStructHeap evheap ** P). pure_auto.
   instantiate (1:= ABORT).
  apply absinfer_abt. pure_auto. pure_auto.
  absimp_abt_solver.
  pure_auto.
  eapply absinfer_seq_abt.
  pure_auto.   pure_auto.
  pure_auto.
Qed. 

Lemma qquery_absimp_succ_if:
  forall P qls sid pdata v' sch s msg mls n pwl wl evheap arrayheap l, 
  forall evheap' evheap'' evheap''' evheap'''' qletbl l2 arrayheap',
    can_change_aop P ->
    get qls sid =Some (absmsgq (msg::mls) n pwl,wl)->
    Get_struct evheap pdata = Some (pdata, OS_Q_DATA, l) ->
    (exists i0, evheap' = Set_struct' evheap pdata OSEventGrp  (Vint32 i0)) ->
    (evheap'' = Set_struct' evheap' pdata OSMsg  (msg)) ->
    (evheap''' = Set_struct' evheap'' pdata OSNMsgs  (V$ (Z.of_nat(length(msg::mls)))) ) ->
    (evheap'''' = Set_struct' evheap''' pdata OSQSize  (Vint32 n))  ->
    id_addrval' (Vptr pdata) code.os_code_defs.OSEventTbl OS_Q_DATA = Some qletbl ->
    Get_array arrayheap qletbl = Some (qletbl, Z.to_nat OS_EVENT_TBL_SIZE , l2) ->
             (exists l2' ,
            arrayheap' = Set_array' arrayheap qletbl l2') ->
    v' = (V$ OS_NO_ERR) ->
    absinfer sch
      (<|| spec_code_cons (qquerynew ((Vptr sid) ::(Vptr pdata ):: v' :: nil)) s ||> ** HECBList qls ** HEvStructHeap evheap ** HEvArrayHeap arrayheap ** P) 
      (<|| s ||> ** HECBList qls ** HEvStructHeap evheap'''' ** HEvArrayHeap arrayheap' ** P). 
Proof.
  intros. (* Hcop Hnsem Hv'. *)
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
(*   eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto. *)
  eapply absinfer_trans.
  eapply absinfer_choice1. 
  pure_auto. 2: eauto. pure_auto.
  destruct H2.
  inverts H2.
  inverts H3.
  inverts H4.
  inverts H5.
  destruct H8.
(*   destruct H5. *)
  inverts H5.
  inverts H8.
  infer_solver 0%nat.
Qed.

Lemma qquery_absimp_succ_if_abt:
  forall P qls sid pdata v' sch s msg mls n pwl wl evheap arrayheap l, 
  forall evheap' evheap'' evheap''' evheap'''' qletbl l2 arrayheap',
    can_change_aop P ->
    get qls sid =Some (absmsgq (msg::mls) n pwl,wl)->
    Get_struct evheap pdata = Some (pdata, OS_Q_DATA, l) ->
    (exists i0, evheap' = Set_struct' evheap pdata OSEventGrp  (Vint32 i0)) ->
    (evheap'' = Set_struct' evheap' pdata OSMsg  (msg)) ->
    (evheap''' = Set_struct' evheap'' pdata OSNMsgs  (V$ (Z.of_nat(length(msg::mls)))) ) ->
    (evheap'''' = Set_struct' evheap''' pdata OSQSize  (Vint32 n))  ->
    id_addrval' (Vptr pdata) code.os_code_defs.OSEventTbl OS_Q_DATA = Some qletbl ->
    Get_array arrayheap qletbl = Some (qletbl, Z.to_nat OS_EVENT_TBL_SIZE , l2) ->
             (exists l2' ,
            arrayheap' = Set_array' arrayheap qletbl l2') ->
    v' <> (V$ OS_NO_ERR) ->
    absinfer sch
      (<|| spec_code_cons (qquerynew ((Vptr sid) ::(Vptr pdata ):: v' :: nil)) s ||> ** HECBList qls ** HEvStructHeap evheap ** HEvArrayHeap arrayheap ** P) 
      (<|| ABORT ||> ** HECBList qls ** HEvStructHeap evheap ** HEvArrayHeap arrayheap ** P). 
Proof.
  intros. (* Hcop Hnsem Hv'. *)
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
(*   eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto. *)
  eapply absinfer_trans.
  eapply absinfer_choice1. 
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_seq1; try pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  sep lift 2%nat in H10.
  eapply H10.
  sep lift 3%nat in H10.
  eapply H10.
  can_change_aop_solver.
  eapply absinfer_seq_abt; try pure_auto.
  Unshelve.
  exact l.
  exact ($ OS_NO_ERR).
Qed.

Lemma qquery_absimp_succ_else:
  forall P qls sid pdata v' sch s mls n pwl wl evheap arrayheap l, 
  forall evheap' evheap'' evheap''' evheap'''' qletbl l2  arrayheap',
    can_change_aop P ->
    get qls sid =Some (absmsgq (mls) n pwl,wl)->
    Get_struct evheap pdata = Some (pdata, OS_Q_DATA, l) ->
    (exists i0, evheap' = Set_struct' evheap pdata OSEventGrp  (Vint32 i0)) ->
    (evheap'' = Set_struct' evheap' pdata OSMsg  (Vnull)) ->
    (evheap''' = Set_struct' evheap'' pdata OSNMsgs  (V$ (Z.of_nat(length(mls)))) ) ->
    (evheap'''' = Set_struct' evheap''' pdata OSQSize  (Vint32 n))  ->
    id_addrval' (Vptr pdata) code.os_code_defs.OSEventTbl OS_Q_DATA = Some qletbl ->
    Get_array arrayheap qletbl = Some (qletbl, Z.to_nat OS_EVENT_TBL_SIZE , l2) ->
             (exists l2', 
            arrayheap' = Set_array' arrayheap qletbl l2') ->
    v' = (V$ OS_NO_ERR) ->
    absinfer sch
      (<|| spec_code_cons (qquerynew ((Vptr sid) ::(Vptr pdata ):: v' :: nil)) s ||> ** HECBList qls ** HEvStructHeap evheap ** HEvArrayHeap arrayheap ** P) 
      (<|| s ||> ** HECBList qls ** HEvStructHeap evheap'''' ** HEvArrayHeap arrayheap' ** P). 
Proof.
  intros. (* Hcop Hnsem Hv'. *)
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
(*   eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto. *)
  eapply absinfer_trans.
  eapply absinfer_choice2. 
  pure_auto. 2: eauto. pure_auto.
  destruct H2.
  inverts H2.
  inverts H3.
  inverts H4.
  inverts H5.
  destruct H8.
(*   destruct H5. *)
  inverts H5.
  inverts H8.
  infer_solver 0%nat.
Qed.

Lemma qquery_absimp_succ_else_abt:
  forall P qls sid pdata v' sch s  mls n pwl wl evheap arrayheap l, 
  forall evheap' evheap'' evheap''' evheap'''' qletbl l2  arrayheap',
    can_change_aop P ->
    get qls sid =Some (absmsgq (mls) n pwl,wl)->
    Get_struct evheap pdata = Some (pdata, OS_Q_DATA, l) ->
    (exists i0, evheap' = Set_struct' evheap pdata OSEventGrp  (Vint32 i0)) ->
    (evheap'' = Set_struct' evheap' pdata OSMsg  (Vnull)) ->
    (evheap''' = Set_struct' evheap'' pdata OSNMsgs  (V$ (Z.of_nat(length(mls)))) ) ->
    (evheap'''' = Set_struct' evheap''' pdata OSQSize  (Vint32 n))  ->
    id_addrval' (Vptr pdata) code.os_code_defs.OSEventTbl OS_Q_DATA = Some qletbl ->
    Get_array arrayheap qletbl = Some (qletbl, Z.to_nat OS_EVENT_TBL_SIZE , l2) ->
             (exists l2' ,
            arrayheap' = Set_array' arrayheap qletbl l2') ->
    v' <> (V$ OS_NO_ERR) ->
    absinfer sch
      (<|| spec_code_cons (qquerynew ((Vptr sid) ::(Vptr pdata ):: v' :: nil)) s ||> ** HECBList qls ** HEvStructHeap evheap ** HEvArrayHeap arrayheap ** P) 
      (<|| ABORT ||> ** HECBList qls ** HEvStructHeap evheap ** HEvArrayHeap arrayheap ** P). 
Proof.
  intros. (* Hcop Hnsem Hv'. *)
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
(*   eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto. *)
  eapply absinfer_trans.
  eapply absinfer_choice2. 
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_seq1; try pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  sep lift 2%nat in H10.
  eapply H10.
  sep lift 3%nat in H10.
  eapply H10.
  can_change_aop_solver.
  eapply absinfer_seq_abt; try pure_auto.
  Unshelve.
  exact l.
  exact ($ OS_NO_ERR).
Qed.

Local Open Scope code_scope.
Local Open Scope int_scope.
  
Lemma OSQquery_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSQQuery vl logicl OSQQueryPre ct->
      Some r =
      BuildRetI os_internal OSQQuery vl logicl OSQQueryPost ct->
      exists t d1 d2 s,
        os_internal OSQQuery = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  hoare forward prim.
  inverts H.
  inverts H0.
  inverts H3.
  inverts H4.
  inverts H.
  rename v'7 into er.
  rename v'5 into opv.
  hoare unfold.
  hoare forward; pauto.
  hoare_split_pure_all.

  assert (Hopv: opv = (V$ OS_ERR_PEVENT_NULL) \/ opv <> (V$ OS_ERR_PEVENT_NULL)) by tauto.
  destruct Hopv. 
  subst.

(*   subst. *)
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  
(*   eapply absinfer_seq1. can_change_aop_solver. *)
  eapply qquery_absimp_null.
  pure_auto.
  auto.
  can_change_aop_solver.
  hoare forward prim.
  sep cancel Aier.
  sep pauto. auto.
  pure_auto; int auto.
  hoare forward.
  splits; pure_auto.

  int_auto.
  mauto.
  split;
  mauto.
  int_auto.
  mauto.
  split;
  mauto.
  
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.

(*   eapply absinfer_seq1. can_change_aop_solver. *)
  eapply qquery_absimp_null_abt.
  pure_auto.
  auto.
  can_change_aop_solver.
  eapply absabort_rule.

  eapply backward_rule1.
  intros.
  destruct H3.
  sep split in H3.
  tryfalse.
  eauto.
  hoare_split_pure_all.
  assert(v'3 <> Vnull).
  { 
    pure_auto.
    rewrite H4 in H3.
    unfold val_eq in H3.
    unfold val_inj in H3.
    destruct H3; tryfalse.
  }
  clear H3.
  rename v'13 into ecbls.
  destruct v'3; destruct H2; tryfalse. destruct H2. tryfalse. destruct H2. tryfalse.
  destruct H2. inverts H2.
  assert (Hcases: get ecbls x = None \/ exists d, get ecbls x = Some d).
  {
    destruct (get ecbls x).
    right. eexists; eauto.
    left; eauto.
  }
  unfold EvtInv.
  rename v'21 into vcspace.
  rename v'22 into v22. 
  rename v'23 into v23. 
  rename v'24 into v24. 

  hoare unfold.
  inversion Hcases as [H_ecbls_qid | H_ecbls_qid].
  hoare_lifts_trms_pre (Aop, absecblsid).
  eapply abscsq_rule.
  pure_auto.
  eapply qquery_absimp_pevent_not_in_dom_abt;
  eauto.
  can_change_aop_solver.
  eapply absinfer_eq. 
  eapply absabort_rule.
  
  destruct H_ecbls_qid as (d & Hget).
  destruct d as [e w].
  unfold AECBList.
  hoare normal pre. 
  hoare unfold.
  lets Hectr: ECBList_P_get_ectr_some H3; eauto.
  destruct Hectr as (et & etbl & petbl & Hgetectr).
  (* destruct et as (et & etbl). *)
  hoare lift 2%nat pre. 
  eapply backward_rule1. 
  intros. 
  eapply get_ectr_decompose; eauto.

  hoare unfold.
  eapply backward_rule1.
  intros.
  match goal with
  | H: _ |= ?P |- _ => instantiate (1:=[| length v'39 = length v'41 |]** P)
  end.  
  sep lift 5%nat in H12.
  assert (H12' := H12).
  eapply evsllseg_aux in H12.
  destruct H12. 
  sep pauto. 
  eapply pure_split_rule'; intro Heqlen.
  assert (H3' := H3). 
  eapply ecblist_p_decompose in H3'; eauto. 
  destruct H3' as (els1 & els2 & x & H'').
  destruct H'' as (Hecbl1 & Hecbl2 & Hjo).

  destruct Hecbl2 as (qid & Hx & Hecbetbl & Hecbpetbl & Hmt).
  change ((v'43 :: nil) ++ v'42) with (v'43 :: v'42) in Hmt.
  simpl in Hmt.
  destruct Hmt as (absev & els' & v'' & H').
  destruct H' as (Helptr & Hjo' & Hrlh & Hecbl2). 
  unfold V_OSEventListPtr in Helptr.
  simpl in Helptr.
  inverts Helptr. 
  eapply backward_rule1. intros.
  assert (H12' := H12).
   match goal with
    H: _ |= ?P |- _ => instantiate (1:=[| x = (Vptr (v'48, Int.zero)) |] ** P)
  end.
  sep lift 5%nat in H12.
  eapply ecblistp_evsllseg_tlsame with (tl:=x) in H12.
  sep pauto. clear H12 H12'. eauto.
  eapply pure_split_rule'; intro Hxeq.
  rewrite Hxeq in Hx. inverts Hx.
  subst x.

  assert (Habsev: get ecbls (v'48, Int.zero) = Some absev).
  {
    assert (Hpre: join (sig (v'48, Int.zero) absev) els' els2) by join auto. 
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

  lzh_hoare_if2.
  transform_pre qacc_eventtype_neq_q ltac:(sep cancel AEventData).
  hoare_split_pure_all.

  hoare_lifts_trms_pre (Aop, absecblsid).
 assert (Hres: opv <> (V$ OS_ERR_EVENT_TYPE)
                \/ opv = (V$ OS_ERR_EVENT_TYPE)) by tauto.
  inversion Hres as [Hres_case | Hres_case]. 
  (* opt <> ... *)
  eapply abscsq_rule.
  pure_auto.
  eapply qquery_absimp_no_q_abt; eauto.
  can_change_aop_solver. 
  unfold not.
  intros.
  do 4 destruct H16.
  unfold get in H16,Habsev.
  unfold EcbMap in H16,Habsev.
  rewrite H16 in Habsev.
  assert ((absmsgq x x0 x3, x4) =  (e, w)).  inverts Habsev. auto.
  rewrite <- H33 in H13.
  unfold not in H13.
  apply H13.
  exists x x0 x3 x4. auto.
  eapply absinfer_eq. 
  eapply absabort_rule.
  (* v'1 = ... *)
  eapply abscsq_rule. 
  pure_auto. 
  eapply qquery_absimp_no_q; eauto.
  can_change_aop_solver. 
  unfold not.
  intros.
  do 4 destruct H16.
  unfold get in H16,Habsev.
  unfold EcbMap in H16,Habsev.
  rewrite H16 in Habsev.
  assert ((absmsgq x x0 x3, x4) =  (e, w)).  inverts Habsev. auto.
  rewrite <- H33 in H13.
  unfold not in H13.
  apply H13.
  exists x x0 x3 x4. auto.
  eapply absinfer_eq. 

  (*********  exit critical ***********)
  fold_AEventNode_r. 
  compose_evsllseg. 
  fold_AECBList. 
  
  hoare forward prim.
  sep cancel Aier.
  unfold EvtInv.
  sep pauto.
  trycancel_EvtInv.
  sep cancel p_local.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  exact_s.
  pauto.
  auto. auto. auto. go.
  hoare forward. 
  splits; pure_auto.

  int_auto.
  mauto.
  split;
  mauto.
  int_auto.
  mauto.
  split;
  mauto.
  split;
  mauto.
  int_auto.  split; mauto. split; mauto.
  int_auto; mauto; split; mauto.
  clear Hcases.
  
  (*os_code_defs.pdata ′ → OSEventGrp =ₑ pevent ′ → OSEventGrp;ₛ*)
  hoare_lifts_trms_pre Aop.
(*   hoare forward. *)
  
  unfold EvtInv.
 (*mq_info ′ → mq_curmsgs =ₑ os_code_defs.pdata ′ → OSNMsgs;ₛ*)
  hoare normal pre.
  hoare unfold.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  
  assert (Hg:  Get_struct v'26 v'6 = None \/ exists t, Get_struct v'26 v'6 = Some t) by (eapply get_struct_or).

  destruct Hg.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply qquery_absimp_pdata_validptr_err_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule. 

  destruct H13 as (ev & Hget').
  destruct ev as (a& l ). destruct a as (a & t).
  assert (Ha: v'6 = a ).
  eapply Get_struct_some_eq; eauto.
  subst a.

  assert (Ht: t = OS_Q_DATA \/ t <> OS_Q_DATA) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply qquery_absimp_pdata_validptr_err_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }
  
  subst t.

  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold_OS_Q_DATA ; eauto. sep pauto.
  hoare_split_pure_all.
  simpljoin. 


  hoare_lifts_trms_pre Aop.
  hoare forward.
  pure_auto.
  pure_auto.
  
  lets Hl': struct_type_vallist_match_elim_5 H13.
  destruct Hl' as (v1' & v2' & v3' & v4' & v5' & Hl).
  subst l.
  simpl. auto with zarith.
  auto.

  destruct v'44.
  hoare forward.
  unfold id_addrval' in H15.
  eapply H15. 
  right. exists ((Pos.to_nat 8)). instantiate (1:= Int8u).
  auto.
  assert (Hget'':= Hget').
  unfold R_Q_Data_P in H2.
  eapply H2 in Hget'.
  destruct Hget'. do 3 destruct H33.
  unfold id_addrval' in H33.
  destruct x.

  hoare forward.
  eapply H33.
  right. exists ((Pos.to_nat 8)). instantiate (1:= Int8u).
  auto.

  eapply backward_rule1.
  intros.
  eapply AEvArrayHeap_unfold.
  sep cancel AEvArrayHeap. sep pauto.
  assert(i4 +ᵢ  Int.mul ($ Z.of_nat (typelen char_t)) ($ 0) = i4).
  {
    change ( Int.mul ($ Z.of_nat (typelen char_t)) ($ 0)) with ($0).
    int_auto.
    split. mauto. simpl. mauto.
    simpl.
    change (Int.unsigned ($ 1) * Int.unsigned ($ 0)) with (Int.unsigned ($0)).
    pure_auto;mauto.
    pure_auto;mauto.
  }
  rewrite H37.
  destruct H35 as (Hi0 & H35).
  destruct H35.
  eauto.

  hoare forward.
  instantiate (1:= 0).
  remember (Int.unsigned (i4 +ᵢ  Int.mul ($ 1) ($ 0))).
  assert(z - z = 0).
  eapply Z.sub_diag.
  rewrite H36.
  eapply Zdiv_0_l.
  remember (Int.unsigned (i4 +ᵢ  Int.mul ($ 1) ($ 0))).
  assert(z - z = 0).
  eapply Z.sub_diag.
  rewrite H36.
  auto.
  simpl.
  change (Int.mul ($ 1) ($ 0)) with ($0).
  assert ((i3 +ᵢ  $ 0) = i3).
  eapply Int.add_zero.
  rewrite H38.
  eapply Z.le_refl.
  
  change (Int.mul ($ 1) ($ 0)) with ($0).
  assert ((i3 +ᵢ  $ 0) = i3).
  eapply Int.add_zero.
  rewrite H38.
  change (i3 +ᵢ  $ 0) with i3.
  assert((Int.unsigned i3 - Int.unsigned i3) = 0).
  eapply Z.sub_diag.
  rewrite H40. auto.

  change (Int.mul ($ 1) ($ 0)) with ($0).
  rewrite Int.add_zero.
  rewrite Z.sub_diag.
  rewrite Zdiv_0_l.
  auto with zarith.
  
  change (Int.mul ($ 1) ($ 0)) with ($0).
  rewrite Int.add_zero.
  rewrite Z.sub_diag.
  rewrite Zdiv_0_l.
  auto with zarith.
  
  rewrite H21.
  simpl.
  auto with zarith.
  
  change (Int.mul ($ 1) ($ 0)) with ($0).
  rewrite Int.add_zero.
  rewrite Z.sub_diag.
  rewrite Zdiv_0_l.
  pure_auto.

  destruct etbl.
  clear -H21.
  simpl in H21. tryfalse.
  destruct v.
  clear -H21 H14.
  destruct H14; tryfalse.
  destruct H14; tryfalse. 
  2:   destruct H14; tryfalse.
  clear - H14.  destruct H14.
  eapply H.
  
  auto with zarith.
  pure_auto.
  sep remember (1::nil)%nat in H37.
  unfold Aarray in H37.
  unfold Aarray' in H37.
  destruct x0.
  simpl in H37.
  simpljoin1;tryfalse.
  mauto.


  hoare forward.
  hoare forward.

  hoare forward;
  change (Int.mul ($ 1) ($ 0)) with ($0);
  change (Int.mul ($ 1) ($ 1)) with ($1);
  try rewrite Int.add_zero;
  try(
    match goal with 
    | |- {| _,_,_,_,_,_|} |- ?ct {{?P}}_{{_}} => idtac
    |_ =>  
    ( unfold id_addrval' in H15;
      simpl in H15;
      inverts H15;
      rewrite Int.add_zero;
      change ($ 1 +ᵢ  $ 1) with ($2);
      change (($ 4 +ᵢ  ($ 2 +ᵢ  $ 2))) with ($8);
      rewrite Int.add_zero_l;
      change ($8 +ᵢ  $ 1) with ($9) 
    )
    end
  ).

  destruct H35;
  do 2 destruct H35;
  destruct H35;
  destruct v'6;
  inverts H37; inverts H35;
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  clear. int_auto. int_auto.
  
  instantiate (1:= 1).
  destruct H35;
  do 2 destruct H35;
  destruct H35;
  destruct v'6;
  inverts H37; inverts H35;
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change ($ 8 +ᵢ  $ 1) with ($9).
  change ((Int.unsigned ($ 9) - Int.unsigned ($ 8)) ) with 1.
  auto.

  destruct H35;
  do 2 destruct H35;
  destruct H35;
  destruct v'6;
  inverts H37; inverts H35;
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change ($ 8 +ᵢ  $ 1) with ($9). clear.
  auto.

  clear.
  int_auto.
  clear. int_auto.
  clear. int_auto.

  rewrite H21.
  clear. int_auto.
  
  pure_auto.
  destruct etbl.
  tryfalse.
  destruct etbl. tryfalse.
  clear -H14 H21.
  destruct v0.

  destruct H14.
  destruct H0.
  unfold rule_type_val_match in H0. tryfalse.
  destruct H14.
  destruct H0.
  unfold rule_type_val_match in H0. tryfalse.
  2:     destruct H14;destruct H0;unfold rule_type_val_match in H0;tryfalse.
  clear - H14.  destruct H14. destruct H0.
  unfold rule_type_val_match in H0.
  eapply H0.

  auto with zarith.
  
  pure_auto.
  sep remember (3::nil)%nat in H37.
  unfold Aarray in H37.
  unfold Aarray' in H37.

  change (Int.zero +ᵢ  ($ 4 +ᵢ  ($ 2 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero))))) with ($ 8) in *.
  change ($ 8 +ᵢ  Int.mul ($ 1) ($ 0)) with ($8) in *.
  destruct ((update_nth_val (Z.to_nat 0) x0
        (nth_val' (Z.to_nat ((Int.unsigned ($ 8) - Int.unsigned ($ 8)) / 1)) etbl))).
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  mauto.
  
  hoare forward.
  hoare forward.
  
  hoare forward;
  change (Int.mul ($ 1) ($ 0)) with ($0);
  change (Int.mul ($ 1) ($ 1)) with ($1);
  try rewrite Int.add_zero;
  try(
    match goal with 
    | |- {| _,_,_,_,_,_|} |- ?ct {{?P}}_{{_}} => idtac
    |_ =>  
    ( unfold id_addrval' in H15;
      simpl in H15;
      inverts H15;
      rewrite Int.add_zero;
      change ($ 1 +ᵢ  $ 1) with ($2);
      change (($ 4 +ᵢ  ($ 2 +ᵢ  $ 2))) with ($8);
      rewrite Int.add_zero_l;
      change (($8 +ᵢ  $ 1)+ᵢ  $ 1) with ($10) 
    )
    end
  ).

  destruct H35;
  do 2 destruct H35;
  destruct H35;
  destruct v'6;
  inverts H37; inverts H35;
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change (($ 8 +ᵢ  $ 1) +ᵢ  $ 1) with ($ 10).
  clear. int_auto.
  
  instantiate (1:= 2).
  destruct H35;
  do 2 destruct H35;
  destruct H35;
  destruct v'6;
  inverts H37; inverts H35;
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change (($ 8 +ᵢ  $ 1) +ᵢ  $ 1) with ($ 10).
  change ((Int.unsigned ($ 10) - Int.unsigned ($ 8)) ) with 2.
  auto.
  
  destruct H35.
  do 2 destruct H35.
  destruct H35.
  destruct v'6.
  inverts H37. inverts H35.
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change (($ 8 +ᵢ  $ 1) +ᵢ  $ 1) with ($ 10).
  clear. auto.
  
  clear. int_auto.
  clear. int_auto.
  clear. int_auto.

  rewrite H21.
  clear. int_auto.
  
  pure_auto.
  destruct etbl.
  tryfalse.
  destruct etbl. tryfalse.
  destruct etbl. tryfalse.
  clear -H14 H21.
  destruct v1.

  destruct H14.
  destruct H0.
  destruct H1.
  unfold rule_type_val_match in H1. tryfalse.
  destruct H14.
  destruct H0.
  destruct H1.
  unfold rule_type_val_match in H1. tryfalse.
  2:     destruct H14;destruct H0;destruct H1; unfold rule_type_val_match in H1;tryfalse.
  clear - H14.  destruct H14. destruct H0. destruct H1.
  unfold rule_type_val_match in H1.
  eapply H1.
  auto with zarith.

  pure_auto.
  sep remember (3::nil)%nat in H37.
  unfold Aarray in H37.
  unfold Aarray' in H37.
  change (Int.zero +ᵢ  ($ 4 +ᵢ  ($ 2 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero))))) with ($ 8) in *.
  change ($ 8 +ᵢ  $ 0) with ($8) in *.
  destruct ((update_nth_val (Z.to_nat 1)
        (update_nth_val 0 x0
           (nth_val' (Z.to_nat ((Int.unsigned ($ 8) - Int.unsigned ($ 8)) / 1)) etbl))
        (nth_val' (Z.to_nat ((Int.unsigned ($ 8 +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1)) etbl))).
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  mauto.
  
  hoare forward.
  hoare forward.
  
  hoare forward;
  change (Int.mul ($ 1) ($ 0)) with ($0);
  change (Int.mul ($ 1) ($ 1)) with ($1);
  try rewrite Int.add_zero;
  try(
    match goal with 
    | |- {| _,_,_,_,_,_|} |- ?ct {{?P}}_{{_}} => idtac
    |_ =>  
    ( unfold id_addrval' in H15;
      simpl in H15;
      inverts H15;
      rewrite Int.add_zero;
      change ($ 1 +ᵢ  $ 1) with ($2);
      change (($ 4 +ᵢ  ($ 2 +ᵢ  $ 2))) with ($8);
      rewrite Int.add_zero_l;
      change ((($8 +ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1) with ($11) 
    )
    end
  ).
  
  destruct H35.
  do 2 destruct H35.
  destruct H35.
  destruct v'6.
  inverts H37. inverts H35.
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change ((($ 8 +ᵢ  $ 1) +ᵢ  $ 1)+ᵢ  $ 1) with ($ 11).
  clear. int_auto.
  
  instantiate (1:= 3).
  destruct H35.
  do 2 destruct H35.
  destruct H35.
  destruct v'6.
  inverts H37. inverts H35.
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change ((($ 8 +ᵢ  $ 1) +ᵢ  $ 1)+ᵢ  $ 1) with ($ 11).
  change ((Int.unsigned ($ 11) - Int.unsigned ($ 8)) ) with 3.
  auto.
  
  destruct H35.
  do 2 destruct H35.
  destruct H35.
  destruct v'6.
  inverts H37. inverts H35.
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change ((($ 8 +ᵢ  $ 1) +ᵢ  $ 1)+ᵢ  $ 1) with ($ 11).
  auto.
  
  clear;int_auto.
  clear. int_auto.
  clear. int_auto.
  rewrite H21.
  clear. int_auto.
  
  pure_auto.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  clear -H14 H21.
  destruct v2;
  try(  destruct H14;
  destruct H0;
  destruct H1;  destruct H2;
  unfold rule_type_val_match in H2; tryfalse).
  eapply H2.

  auto with zarith.

  pure_auto.
  sep remember (3::nil)%nat in H37.
  unfold Aarray in H37.
  unfold Aarray' in H37.
  change (Int.zero +ᵢ  ($ 4 +ᵢ  ($ 2 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero))))) with ($ 8) in *.
  change ($ 8 +ᵢ  $ 0) with ($8) in *.
  destruct ((update_nth_val (Z.to_nat 2)
        (update_nth_val (Pos.to_nat 1)
           (update_nth_val 0 x0
              (nth_val' (Z.to_nat ((Int.unsigned ($ 8) - Int.unsigned ($ 8)) / 1)) etbl))
           (nth_val' (Z.to_nat ((Int.unsigned ($ 8 +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1)) etbl))
        (nth_val' (Z.to_nat ((Int.unsigned (($ 8 +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))
           etbl))).
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  mauto.
  
  hoare forward.
  hoare forward.
  
  hoare forward;
  change (Int.mul ($ 1) ($ 0)) with ($0);
  change (Int.mul ($ 1) ($ 1)) with ($1);
  try rewrite Int.add_zero;
  try(
    match goal with 
    | |- {| _,_,_,_,_,_|} |- ?ct {{?P}}_{{_}} => idtac
    |_ =>  
    ( unfold id_addrval' in H15;
      simpl in H15;
      inverts H15;
      rewrite Int.add_zero;
      change ($ 1 +ᵢ  $ 1) with ($2);
      change (($ 4 +ᵢ  ($ 2 +ᵢ  $ 2))) with ($8);
      rewrite Int.add_zero_l;
      change (((($8 +ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1) with ($12) 
    )
    end
  ).

  unfold id_addrval in H33.
  simpl in H33.
  destruct H35.
  do 2 destruct H35.
  destruct H35.
  destruct v'6.
  inverts H37. inverts H35.
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change (((($ 8 +ᵢ  $ 1) +ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1) with ($ 12).
  clear. int_auto.
  
  instantiate (1:= 4).
  destruct H35.
  do 2 destruct H35.
  destruct H35.
  destruct v'6.
  inverts H37. inverts H35.
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change (((($ 8 +ᵢ  $ 1) +ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1) with ($ 12).
  change ((Int.unsigned ($ 11) - Int.unsigned ($ 8)) ) with 3.
  auto.
  
  destruct H35.
  do 2 destruct H35.
  destruct H35.
  destruct v'6.
  inverts H37. inverts H35.
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change (((($ 8 +ᵢ  $ 1) +ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1) with ($ 12).
  auto.
  
  clear. int_auto.
  clear. int_auto.
  clear. int_auto.
  rewrite H21.
  clear. int_auto.
  
  pure_auto.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  clear -H14 H21.
  destruct v3;
  try(
  destruct H14;
  destruct H0;
  destruct H1;  destruct H2; destruct H3;
  unfold rule_type_val_match in H3; tryfalse
  ).
  eapply H3.

  auto with zarith.

  pure_auto.
  sep remember (3::nil)%nat in H37.
  unfold Aarray in H37.
  unfold Aarray' in H37.
  change (Int.zero +ᵢ  ($ 4 +ᵢ  ($ 2 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero))))) with ($ 8) in *.
  change ($ 8 +ᵢ  $ 0) with ($8) in *.
  destruct ((update_nth_val (Z.to_nat 3)
        (update_nth_val (Pos.to_nat 2)
           (update_nth_val (Pos.to_nat 1)
              (update_nth_val 0 x0
                 (nth_val' (Z.to_nat ((Int.unsigned ($ 8) - Int.unsigned ($ 8)) / 1)) etbl))
              (nth_val' (Z.to_nat ((Int.unsigned ($ 8 +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1)) etbl))
           (nth_val'
              (Z.to_nat ((Int.unsigned (($ 8 +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1)) etbl))
        (nth_val'
           (Z.to_nat ((Int.unsigned ((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))
           etbl))).
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  mauto.
  
  hoare forward.
  hoare forward.
  
  hoare forward;
  change (Int.mul ($ 1) ($ 0)) with ($0);
  change (Int.mul ($ 1) ($ 1)) with ($1);
  try rewrite Int.add_zero;
  try(
    match goal with 
    | |- {| _,_,_,_,_,_|} |- ?ct {{?P}}_{{_}} => idtac
    |_ =>  
    ( unfold id_addrval' in H15;
      simpl in H15;
      inverts H15;
      rewrite Int.add_zero;
      change ($ 1 +ᵢ  $ 1) with ($2);
      change (($ 4 +ᵢ  ($ 2 +ᵢ  $ 2))) with ($8);
      rewrite Int.add_zero_l;
      change ((((($8 +ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1) with ($13) )
    end
  ).

  unfold id_addrval in H33.
  simpl in H33.
  destruct H35.
  do 2 destruct H35.
  destruct H35.
  destruct v'6.
  inverts H37. inverts H35.
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change ((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1) with ($ 13).
  clear. int_auto.
  
  instantiate (1:= 5).
  destruct H35.
  do 2 destruct H35.
  destruct H35.
  destruct v'6.
  inverts H37. inverts H35.
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change ((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1) with ($ 13).
  auto.
  
  destruct H35.
  do 2 destruct H35.
  destruct H35.
  destruct v'6.
  inverts H37. inverts H35.
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change ((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1) with ($ 13).
  auto.
  
  clear. int_auto.
  clear. int_auto.
  clear. int_auto.
  rewrite H21.
  clear. int_auto.

  pure_auto.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  clear -H14 H21.

  destruct v4;
  try(
  destruct H14;
  destruct H0;
  destruct H1;  destruct H2; destruct H3; destruct H4;
  unfold rule_type_val_match in H4; tryfalse
  ).
  eapply H4.
  auto with zarith.

  pure_auto.
  sep remember (3::nil)%nat in H37.
  unfold Aarray in H37.
  unfold Aarray' in H37.
  change (Int.zero +ᵢ  ($ 4 +ᵢ  ($ 2 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero))))) with ($ 8) in *.
  change ($ 8 +ᵢ  $ 0) with ($8) in *.
  destruct ((update_nth_val (Z.to_nat 4)
        (update_nth_val (Pos.to_nat 3)
           (update_nth_val (Pos.to_nat 2)
              (update_nth_val (Pos.to_nat 1)
                 (update_nth_val 0 x0
                    (nth_val'
                       (Z.to_nat
                          ((Int.unsigned ($ 8) -
                            Int.unsigned ($ 8)) / 1)) etbl))
                 (nth_val'
                    (Z.to_nat
                       ((Int.unsigned ($ 8 +ᵢ  $ 1) -
                         Int.unsigned ($ 8)) / 1)) etbl))
              (nth_val'
                 (Z.to_nat
                    ((Int.unsigned (($ 8 +ᵢ  $ 1) +ᵢ  $ 1) -
                      Int.unsigned ($ 8)) / 1)) etbl))
           (nth_val'
              (Z.to_nat
                 ((Int.unsigned ((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) -
                   Int.unsigned ($ 8)) / 1)) etbl))
        (nth_val'
           (Z.to_nat
              ((Int.unsigned
                  (((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) -
                Int.unsigned ($ 8)) / 1)) etbl))).
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  mauto.
  
  hoare forward.
  hoare forward.

  hoare forward;
  change (Int.mul ($ 1) ($ 0)) with ($0);
  change (Int.mul ($ 1) ($ 1)) with ($1);
  try rewrite Int.add_zero;
  try(
    match goal with 
    | |- {| _,_,_,_,_,_|} |- ?ct {{?P}}_{{_}} => idtac
    |_ =>  
    ( unfold id_addrval' in H15;
      simpl in H15;
      inverts H15;
      rewrite Int.add_zero;
      change ($ 1 +ᵢ  $ 1) with ($2);
      change (($ 4 +ᵢ  ($ 2 +ᵢ  $ 2))) with ($8);
      rewrite Int.add_zero_l;
      change (((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1) with ($14) 
    )
    end
  ).

  unfold id_addrval in H33.
  simpl in H33.
  destruct H35.
  do 2 destruct H35.
  destruct H35.
  destruct v'6.
  inverts H37. inverts H35.
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change (((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1) with ($14) .
  clear. int_auto.
  
  instantiate (1:= 6).
  destruct H35.
  do 2 destruct H35.
  destruct H35.
  destruct v'6.
  inverts H37. inverts H35.
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change (((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1) with ($14) .
  change ((Int.unsigned ($ 11) - Int.unsigned ($ 8)) ) with 3.
  auto.
  
  destruct H35.
  do 2 destruct H35.
  destruct H35.
  destruct v'6.
  inverts H37. inverts H35.
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change (((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1) with ($14) .
  auto.
  
  clear. int_auto.
  clear. int_auto.
  clear. int_auto.
  rewrite H21.
  clear. int_auto.

  pure_auto.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  clear -H14 H21.
  destruct v5;
  try(
  destruct H14;
  destruct H0;
  destruct H1;  destruct H2; destruct H3; destruct H4; destruct H5;
  unfold rule_type_val_match in H5; tryfalse
  ).
  eapply H5.

  auto with zarith.

  pure_auto.
  sep remember (3::nil)%nat in H37.
  unfold Aarray in H37.
  unfold Aarray' in H37.
  change (Int.zero +ᵢ  ($ 4 +ᵢ  ($ 2 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero))))) with ($ 8) in *.
  change ($ 8 +ᵢ  $ 0) with ($8) in *.
  destruct ((update_nth_val (Z.to_nat 5)
        (update_nth_val (Pos.to_nat 4)
           (update_nth_val (Pos.to_nat 3)
              (update_nth_val (Pos.to_nat 2)
                 (update_nth_val (Pos.to_nat 1)
                    (update_nth_val 0 x0
                       (nth_val'
                          (Z.to_nat
                             ((Int.unsigned ($ 8) -
                               Int.unsigned ($ 8)) / 1)) etbl))
                    (nth_val'
                       (Z.to_nat
                          ((Int.unsigned ($ 8 +ᵢ  $ 1) -
                            Int.unsigned ($ 8)) / 1)) etbl))
                 (nth_val'
                    (Z.to_nat
                       ((Int.unsigned (($ 8 +ᵢ  $ 1) +ᵢ  $ 1) -
                         Int.unsigned ($ 8)) / 1)) etbl))
              (nth_val'
                 (Z.to_nat
                    ((Int.unsigned
                        ((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) -
                      Int.unsigned ($ 8)) / 1)) etbl))
           (nth_val'
              (Z.to_nat
                 ((Int.unsigned
                     (((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) -
                   Int.unsigned ($ 8)) / 1)) etbl))
        (nth_val'
           (Z.to_nat
              ((Int.unsigned
                  ((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ
                   $ 1) - Int.unsigned ($ 8)) / 1)) etbl))).
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  mauto.
  
  hoare forward.
  hoare forward.

  hoare forward;
  change (Int.mul ($ 1) ($ 0)) with ($0);
  change (Int.mul ($ 1) ($ 1)) with ($1);
  try rewrite Int.add_zero;
  try(
    match goal with 
    | |- {| _,_,_,_,_,_|} |- ?ct {{?P}}_{{_}} => idtac
    |_ =>  
    ( unfold id_addrval' in H15;
      simpl in H15;
      inverts H15;
      rewrite Int.add_zero;
      change ($ 1 +ᵢ  $ 1) with ($2);
      change (($ 4 +ᵢ  ($ 2 +ᵢ  $ 2))) with ($8);
      rewrite Int.add_zero_l;
      change ((((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1) with ($ 15) 
    )
    end
  ).

  unfold id_addrval in H33.
  simpl in H33.
  destruct H35.
  do 2 destruct H35.
  destruct H35.
  destruct v'6.
  inverts H37. inverts H35.
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change ((((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1) with ($ 15) .
  clear. int_auto.
  
  instantiate (1:= 7).
  destruct H35.
  do 2 destruct H35.
  destruct H35.
  destruct v'6.
  inverts H37. inverts H35.
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change ((((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1) with ($ 15) .
  change ((Int.unsigned ($ 11) - Int.unsigned ($ 8)) ) with 3.
  auto.
  
  destruct H35.
  do 2 destruct H35.
  destruct H35.
  destruct v'6.
  inverts H37. inverts H35.
  inverts H33.
  change ($ 0 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  Int.zero)))) with ($ 8).
  change ((((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1)+ᵢ  $ 1) with ($ 15) .
  auto.
  
  clear. int_auto.
  clear. int_auto.
  clear. int_auto.
  rewrite H21.
  clear. int_auto.
  pure_auto.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  destruct etbl; tryfalse.
  clear -H14 H21.
  destruct v6;
  try(
  destruct H14;
  destruct H0;
  destruct H1;  destruct H2; destruct H3; destruct H4; destruct H5; destruct H6;
  unfold rule_type_val_match in H6; tryfalse
  ).
  eapply H6.

  auto with zarith.

  pure_auto.
  sep remember (3::nil)%nat in H37.
  unfold Aarray in H37.
  unfold Aarray' in H37.
  change (Int.zero +ᵢ  ($ 4 +ᵢ  ($ 2 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero))))) with ($ 8) in *.
  change ($ 8 +ᵢ  $ 0) with ($8) in *.
  destruct ((update_nth_val (Z.to_nat 6)
        (update_nth_val (Pos.to_nat 5)
           (update_nth_val (Pos.to_nat 4)
              (update_nth_val (Pos.to_nat 3)
                 (update_nth_val (Pos.to_nat 2)
                    (update_nth_val (Pos.to_nat 1)
                       (update_nth_val 0 x0
                          (nth_val' (Z.to_nat ((Int.unsigned ($ 8) - Int.unsigned ($ 8)) / 1)) etbl))
                       (nth_val' (Z.to_nat ((Int.unsigned ($ 8 +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1)) etbl))
                    (nth_val'  (Z.to_nat ((Int.unsigned (($ 8 +ᵢ  $ 1) +ᵢ  $ 1) -
                            Int.unsigned ($ 8)) / 1)) etbl))
                 (nth_val'  (Z.to_nat  ((Int.unsigned ((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) -
                         Int.unsigned ($ 8)) / 1)) etbl))
              (nth_val' (Z.to_nat  ((Int.unsigned (((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) -
                      Int.unsigned ($ 8)) / 1)) etbl))
           (nth_val' (Z.to_nat ((Int.unsigned
                     ((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) -
                   Int.unsigned ($ 8)) / 1)) etbl))
        (nth_val' (Z.to_nat ((Int.unsigned
                  (((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ
                   $ 1) - Int.unsigned ($ 8)) / 1)) etbl))).
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  destruct l0.
  simpl in H37.
  simpljoin1;tryfalse.
  mauto.
  
  hoare forward.
  hoare forward.

  hoare forward.
  pure_auto.

  eapply semacc_int_eq_true in H12.
  subst i1.
  unfold AEventData.
  destruct v'43.

  2:{
  hoare_split_pure_all.
  unfolds in H38;simpl in H38.
  inverts H38.
  }
  2:{
  hoare_split_pure_all.
  unfolds in H38;simpl in H38.
  inverts H38.
  }

  2:{
  hoare_lifts_trms_pre AOSPostEventTbl.
  apply backward_rule1 with Afalse.
  intros.
  sep split in H12.
  clear - H39.
  unfolds in H39.
  simpl in H39.
  inverts H39.

  apply pfalse_rule.

  }
  (* new add port *)
  2:{
  hoare_split_pure_all.
  unfolds in H38;simpl in H38.
  inverts H38.
  }

  unfold AMsgData.
  unfold AOSQCtr.
  unfold AOSQBlk.
  hoare unfold.
  
  simpl in H12.
  inverts H12.

  assert (exists i', x9 = Vptr (v'45, i')).
  eapply osq_same_blk_st_out';eauto.
  simpljoin1.
  
  hoare forward.
  pure_auto.
  pure intro.  
  hoare_lifts_trms_pre Aop.
  assert(HeqHbo : Int.ltu ($ 0) i7 = true).
  {
    eapply int_eq_false_ltu.
    clear -H12.
    eapply Int.eq_false.
    intro.
    inverts H.
    pure_auto.
  }
  
  lets Hx: wellq_props HeqHbo Hrlh H36 ;eauto.
  simpljoin1.
  hoare forward;auto.
  pure_auto.
  
  hoare_lifts_trms_pre Aop.
  hoare forward.
  
  hoare forward.
  hoare forward.
  pure_auto.
  hoare forward.
  pure_auto.
  
  change (Int.mul ($ 1) ($ 0)) with ($0).
  change (Int.mul ($ 1) ($ 1)) with ($1).
  rewrite Int.add_zero.
  unfold id_addrval' in H15.
  simpl in H15.
  inverts H15.
  rewrite Int.add_zero.
  change (($ 1 +ᵢ  Int.zero)) with ($ 1).
  change ($ 1 +ᵢ  $ 1) with ($2).
  change (($ 4 +ᵢ  ($ 2 +ᵢ  $ 2))) with ($8).
  rewrite Int.add_zero_l.
  change ((Int.zero +ᵢ  $ 8)) with ($8).
  change ((Z.to_nat ((Int.unsigned ($ 8) - Int.unsigned ($ 8)) / 1))) with 0%nat.
  change ((Z.to_nat ((Int.unsigned ($ 8 +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 1%nat.
  change ((Z.to_nat ((Int.unsigned  (($ 8 +ᵢ  $ 1) +ᵢ  $ 1)  - Int.unsigned ($ 8)) / 1))) with 2%nat.
  change ((Z.to_nat ((Int.unsigned ((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 3%nat.
  change ((Z.to_nat ((Int.unsigned (((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 4%nat.
  change ((Z.to_nat ((Int.unsigned ((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 5%nat.
  change ((Z.to_nat ((Int.unsigned (((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1)  - Int.unsigned ($ 8)) / 1))) with 6%nat.
  change ((Z.to_nat ((Int.unsigned ((((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 7%nat.
  change ((Pos.to_nat 1)) with (1%nat).
  change ((Pos.to_nat 2)) with (2%nat).
  change ((Pos.to_nat 3)) with (3%nat).
  change ((Pos.to_nat 4)) with (4%nat).
  change ((Pos.to_nat 5)) with (5%nat).
  change ((Pos.to_nat 6)) with (6%nat).
  change ((Z.to_nat 7)) with (7%nat).
  change ((Pos.to_nat 8)) with (8%nat).

  destruct e.
  clear - Hrlh. unfold RLH_ECBData_P in Hrlh. tryfalse.
  2: clear - Hrlh; unfold RLH_ECBData_P in Hrlh; tryfalse.
  2: clear - Hrlh; unfold RLH_ECBData_P in Hrlh; tryfalse.
  (* new add port *)
  2: clear - Hrlh; unfold RLH_ECBData_P in Hrlh; tryfalse.
  
  hoare_split_pure_all.
  simpljoin1.
  lets Hx: h_has_same_msg Hrlh;eauto.
  eapply int_eq_false_ltu.
  clear -H12.
  eapply Int.eq_false.
  intro.
  inverts H.
  pure_auto.
  simpl;auto.
  simpljoin1.
  
  hoare_lifts_trms_pre (Aop, absecblsid, evstructheapid, evarrayheapid).
  
  assert(opv = V$OS_NO_ERR \/ opv <> V$OS_NO_ERR ) by tauto.
  destruct H41.
  eapply abscsq_rule. 
  pure_auto. 
  eapply qquery_absimp_succ_if;eauto.
  can_change_aop_solver. 
  eapply absinfer_eq. 
  
  2:{
    eapply abscsq_rule. 
    pure_auto. 
    eapply qquery_absimp_succ_if_abt;eauto.
    can_change_aop_solver. 
    eapply absinfer_eq.
    eapply absabort_rule. 
  }
  inverts H41.
  clear H42.
  instantiate (1:= (update_nth_val 7
       (update_nth_val 6
          (update_nth_val 5
             (update_nth_val 4
                (update_nth_val 3
                   (update_nth_val 2
                      (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                         (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                   (nth_val' 3 etbl)) (nth_val' 4 etbl)) (nth_val' 5 etbl))
          (nth_val' 6 etbl)) (nth_val' 7 etbl))).
  instantiate (1:= i0).
  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold_OS_Q_DATA; eauto.
  exists (nth_val' (Z.to_nat ((Int.unsigned x1 - Int.unsigned ($ 4)) / 4)) v2
            :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) v'21 v'24.
  instantiate (2:= (x, $ 0)).
  sep cancel (AEvStructHeap v'21) .
  sep cancel (AEvStructHeap v'24) .
  sep cancel (Astruct (x, $ 0)).
  sep cancel (Alvarmapsto os_code_defs.pdata).
  instantiate (2:= v'21 ++
     (x, $ 0, OS_Q_DATA,
     nth_val' (Z.to_nat ((Int.unsigned x1 - Int.unsigned ($ 4)) / 4)) v2
     :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24).
  sep pauto.
  unfold R_MutexAttr_P; simpl. intros; tryfalse.
  pure_auto.
  assert(HeqHbo:Int.ltu ($ 0) i7 = true).
  {
    eapply int_eq_false_ltu.
    clear -H12.
    eapply Int.eq_false.
    intro.
    eapply H12.
    inverts H.
    pure_auto.
  }
  lets Hx: wellq_props HeqHbo Hrlh H36 ;eauto.
  simpljoin1.
  pure_auto.

  eapply backward_rule1. 
  intros.
  eapply AEvArrayHeap_fold; eauto.
  exists ((update_nth_val 7
        (update_nth_val 6
           (update_nth_val 5
              (update_nth_val 4
                 (update_nth_val 3
                    (update_nth_val 2
                       (update_nth_val 1
                          (update_nth_val 0 x0 (nth_val' 0 etbl))
                          (nth_val' 1 etbl)) 
                       (nth_val' 2 etbl)) (nth_val' 3 etbl))
                 (nth_val' 4 etbl)) (nth_val' 5 etbl))
           (nth_val' 6 etbl)) (nth_val' 7 etbl))) v'26 v'38.
  instantiate (2:=(b0, i4)).
  sep pauto.
  
  destruct etbl. clear - H21; tryfalse.
  destruct etbl. clear - H21; tryfalse.
  destruct etbl. clear - H21; tryfalse.
  destruct etbl. clear - H21; tryfalse.
  destruct etbl. clear - H21; tryfalse.
  destruct etbl. clear - H21; tryfalse.
  destruct etbl. clear - H21; tryfalse.
  destruct etbl. clear - H21; tryfalse.
  destruct etbl. 2 :clear - H21; tryfalse.
  
  destruct x0. clear - H46 . simpl in H46 . tryfalse.
  destruct x0. clear - H46 . simpl in H46 . tryfalse.
  destruct x0. clear - H46 . simpl in H46 . tryfalse.
  destruct x0. clear - H46 . simpl in H46 . tryfalse.
  destruct x0. clear - H46 . simpl in H46 . tryfalse.
  destruct x0. clear - H46 . simpl in H46 . tryfalse.
  destruct x0. clear - H46 . simpl in H46 . tryfalse.
  destruct x0. clear - H46 . simpl in H46 . tryfalse.
  destruct x0. 2:{clear - H46 . simpl in H46 . tryfalse. }
  simpl.
  clear -H14.
  eapply H14.

  eapply backward_rule1.
  intros. 
  eapply node_fold.
  instantiate (4:= b).
  sep pauto. eauto.
  pure_auto.
  eapply backward_rule1.
  intros. 
  eapply AOSEventTbl_fold.
  instantiate (2:= etbl).
  instantiate (2:= (b, $ 8) ).
  sep pauto.
  pure_auto.
  fold_AOSEvent.

  eapply backward_rule1.
  intros. 
  eapply AEventNode_fold.
  sep cancel AOSEvent.
  instantiate(2:=(DMsgQ (Vptr (v'49, Int.zero))
                                (x14 :: x13 :: x7 :: x8 :: Vptr (v'45, x1) :: Vint32 i8:: Vint32 i7
                                   :: Vptr (v'45, Int.zero) :: nil) (x4 :: x6 :: nil) v2)).
  unfold AEventData.
  unfold AMsgData.
  unfold AOSQCtr.
  unfold AOSQBlk.
  sep pauto.
  unfold node.
  sep pauto.
  instantiate (4:= v'49).
  instantiate (3:= v'45).
  instantiate (2:= (v'45, $ 4)).
  sep pauto.
  split;eauto.
  pure_auto.
  split;eauto.
  pure_auto.
  unfold V_qfreeblk.
  unfold nth_val. auto.
  auto.
  compose_evsllseg.
  fold_AECBList.
  hoare forward prim.
  sep cancel tcbdllflag.
    sep cancel APthreadAttr.
  sep cancel CapabilityInv.

  unfold EvtInv.
  sep pauto.
  trycancel_EvtInv.
  
  assert(exists addr, addr = (x, $ 0)).
  {
    exists (x, $ 0). eauto.
  }
  destruct H42.
  sep cancel p_local.
  sep cancel Aier.
  instantiate (1:= LV os_code_defs.pdata @ OS_Q_DATA ∗ |-> Vptr (x, $ 0) **
         LV pq @ OS_Q ∗ |-> Vptr (v'49, Int.zero) **
         LV psrc @ (char_t) ∗
         |-> Vptr
               (b,
               ((((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ
               $ 1) **
         LV pdest @ (char_t) ∗
         |-> Vptr
               (b0,
               (((((((i4 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ
                $ 1) +ᵢ  $ 1) **
         LV pevent @ OS_EVENT ∗ |-> Vptr (b, Int.zero) **
         A_dom_lenv
           ((os_code_defs.pdata, OS_Q_DATA ∗)
            :: (pevent, OS_EVENT ∗)
               :: (pq, OS_Q ∗) :: (psrc, (char_t) ∗) :: (pdest, (char_t) ∗) :: nil)).
  rewrite <- H42 in *.
  assert ((Set_struct'
                  (v'21 ++(x12, OS_Q_DATA,  x15 :: Vint32 i6
                     :: Vint32 i5 :: x18 :: Vint32 i1 :: nil)
                      :: v'24) x12 OSEventGrp (Vint32 i0)) = (v'21 ++
                      (x12, OS_Q_DATA,  x15 :: Vint32 i6
                       :: Vint32 i5 :: x18 :: Vint32 i0 :: nil) :: v'24)).
   {
    clear - Hget'' H34 H42.
    eapply set_struct_update_nth_val'; eauto.
    unfolds; simpl; eauto. 
    simpl; auto. }

  assert((Set_struct'
              (Set_struct'
                 (v'21 ++
                  (x12, OS_Q_DATA,
                  x15
                  :: Vint32 i6
                     :: Vint32 i5 :: x18 :: Vint32 i1 :: nil)
                  :: v'24) x12 OSEventGrp (Vint32 i0)) x12 OSMsg
              (nth_val'
                 (Z.to_nat
                    ((Int.unsigned x1 -
                      Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) /
                     4)) v2)) =
                     (v'21 ++
                  (x12, OS_Q_DATA,
                  (nth_val'
                 (Z.to_nat
                    ((Int.unsigned x1 -
                      Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) /
                     4)) v2) :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i0 :: nil) :: v'24)
                     ).
    {
    rewrite H50.
    clear - Hget'' H34 H42.
    eapply set_struct_update_nth_val'; eauto.
    eapply get_struct_vl; eauto.
  unfolds; simpl; eauto.
  simpl; auto.
  }
  
  assert(
      (Set_struct'
           (Set_struct'
              (Set_struct'
                 (v'21 ++
                  (x12, OS_Q_DATA,
                  x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil) :: v'24) x12
                 OSEventGrp (Vint32 i0)) x12 OSMsg
              (nth_val'
                 (Z.to_nat
                    ((Int.unsigned x1 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) /
                     4)) v2)) x12 OSNMsgs
           (V$ Z.of_nat
                 (length
                    (nth_val'
                       (Z.to_nat
                          ((Int.unsigned x1 -
                            Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4)) v2
                     :: x3)))) =
        (v'21 ++
            (x12, OS_Q_DATA,
            nth_val' (Z.to_nat ((Int.unsigned x1 - Int.unsigned ($ 4)) / 4)) v2
            :: Vint32 i7 :: Vint32 i5 :: x18 :: Vint32 i0 :: nil) :: v'24)
    ).
    {
      rewrite H58.
      clear -Hrlh Hget'' H34 H42.
      unfold RLH_ECBData_P in Hrlh .
      simpljoin1.
      unfold MatchLHMsgLength in H0.
      simpljoin1.
      unfold V_OSQEntries in H0. inverts H0.
      rewrite <- H3.
      assert((V$ Int.unsigned x0) = Vint32 x0).
      clear . int_auto.
      rewrite H0.
      clear - Hget'' H34 .
      assert(H33:exists addr, addr = (x, $ 0)).
      {
       exists (x, $ 0). eauto.
      }
      destruct H33.
      rename H into H33.
      eapply set_struct_update_nth_val'; eauto.
      rewrite <-H33 in *.
      eapply get_struct_vl; eauto.
      unfolds; simpl; eauto.
      simpl; eauto. } 

  assert((Set_struct'
        (Set_struct'
           (Set_struct'
              (Set_struct'
                 (v'21 ++
                  (x12, OS_Q_DATA,
                  x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil) :: v'24) x12
                 OSEventGrp (Vint32 i0)) x12 OSMsg
              (nth_val'
                 (Z.to_nat
                    ((Int.unsigned x1 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) /
                     4)) v2)) x12 OSNMsgs
           (V$ Z.of_nat
                 (length
                    (nth_val'
                       (Z.to_nat
                          ((Int.unsigned x1 -
                            Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4)) v2
                     :: x3)))) x12 OSQSize (Vint32 x9)) =
        (v'21 ++
            (x12, OS_Q_DATA,
            nth_val' (Z.to_nat ((Int.unsigned x1 - Int.unsigned ($ 4)) / 4)) v2
            :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24)
                     ).
   {
       rewrite H59.       
      clear -Hrlh Hget'' H34 H41.
      unfold RLH_ECBData_P in Hrlh .
      simpljoin1.
      unfold MatchLHMsgSize in H1.
      simpljoin1.
      unfold V_OSQSize in H1. inverts H1.
      assert((V$ Int.unsigned x9) = Vint32 x9).
      clear . int_auto.
      rewrite H1.
      clear - Hget'' H34 .
      eapply set_struct_update_nth_val'; eauto.
      eapply get_struct_vl; eauto.  
      unfolds; simpl; auto.
      simpl; auto.
}
  rewrite <- H60 in H41.
  sep cancel AEvStructHeap.
  
  change (Int.mul ($ Z.of_nat (typelen char_t)) ($ 0)) with ($0).
  change (Int.mul ($ Z.of_nat (typelen char_t)) ($ 0)) with ($0) in H41.
  change (Int.mul ($ Z.of_nat (typelen char_t)) ($ 0)) with ($0) in H49.
  change (Int.mul ($ Z.of_nat (typelen char_t)) ($ 0)) with ($0) in H40 .
  assert( forall x, x +ᵢ  $ 0 = x).
  {
    intros. clear. int_auto.
  }

  assert((Set_array' (v'26 ++ (b0, i4, Z.to_nat OS_EVENT_TBL_SIZE, x0) :: v'38) 
        (b0, i4)
        (update_nth_val 7
           (update_nth_val 6
              (update_nth_val 5
                 (update_nth_val 4
                    (update_nth_val 3
                       (update_nth_val 2
                          (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                             (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                       (nth_val' 3 etbl)) (nth_val' 4 etbl)) 
                 (nth_val' 5 etbl)) (nth_val' 6 etbl)) (nth_val' 7 etbl)))
          = (v'26 ++
            (b0, i4, Z.to_nat OS_EVENT_TBL_SIZE,
            update_nth_val 7
              (update_nth_val 6
                 (update_nth_val 5
                    (update_nth_val 4
                       (update_nth_val 3
                          (update_nth_val 2
                             (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                                (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                          (nth_val' 3 etbl)) (nth_val' 4 etbl)) 
                    (nth_val' 5 etbl)) (nth_val' 6 etbl)) (nth_val' 7 etbl)) :: v'38)
           ).
  {
      clear - H40 H49.
      assert(H33:exists addr, addr = (b0, i4)).
      {
       exists (b0, i4). eauto.
      }
      destruct H33.
      rename H into H33.
      rewrite <-H33 in *.
      eapply set_array_update_nth_val; eauto. 
  }
  
  remember ((update_nth_val 0 x0 (nth_val' 0 etbl))).
  remember ((update_nth_val 1 l (nth_val' 1 etbl))).
  remember ((update_nth_val 2 l0 (nth_val' 2 etbl))).
  remember ((update_nth_val 3 l1 (nth_val' 3 etbl))).
  remember ((update_nth_val 4 l2 (nth_val' 4 etbl))).
  remember ((update_nth_val 5 l3 (nth_val' 5 etbl))).
  remember ((update_nth_val 6 l4 (nth_val' 6 etbl))).
  remember ((update_nth_val 7 l5 (nth_val' 7 etbl))).

  Set Nested Proofs Allowed.
  Lemma AAA:
    forall s x y p ,
      x = y ->
      s |= AEvArrayHeap x ** p ->
      s |= AEvArrayHeap y ** p.
   intros.
   rewrite <- H.
   auto.
   Qed.
  
  apply AAA with (x:= v'26 ++ (b0, i4, Z.to_nat OS_EVENT_TBL_SIZE, l6) :: v'38). auto.
  sep cancel AEvArrayHeap.
  sep pauto.
   auto. auto. auto.
  2: auto.
  2: pure_auto.
      
  assert(He:exists addr, addr = (x, $ 0)).
  {
    exists (x, $ 0). eauto.
  }
  destruct He as (addr & He).
  rewrite <- He in *.
  assert (Hs: (Set_struct'
              (v'21 ++
               (addr, OS_Q_DATA,
               x15
               :: Vint32 i6
                  :: Vint32 i5 :: x18 :: Vint32 i1 :: nil)
               :: v'24) addr OSEventGrp 
              (Vint32 i0)) = (v'21 ++
               (addr, OS_Q_DATA,
               x15
               :: Vint32 i6
                  :: Vint32 i5 :: x18 :: Vint32 i0 :: nil)
               :: v'24)).
   {
    clear - Hget'' H34 He.
    eapply set_struct_update_nth_val'; eauto.
    unfolds; simpl; auto.
    simpl; auto. 
   }

  assert(Hs': (Set_struct'
              (Set_struct'
                 (v'21 ++
                  (addr, OS_Q_DATA,
                  x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil) :: v'24) addr
                 OSEventGrp (Vint32 i0)) addr OSMsg
              (nth_val'
                 (Z.to_nat
                    ((Int.unsigned x1 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) /
                     4)) v2)) = 
                     (v'21 ++
                  (addr, OS_Q_DATA,
                  (nth_val'
                 (Z.to_nat
                    ((Int.unsigned x1 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) /
                     4)) v2) :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i0 :: nil) :: v'24)
                     ).
    {
    rewrite Hs.
    clear - Hget'' H34.
    eapply set_struct_update_nth_val'; eauto.
    eapply get_struct_vl; eauto.
    unfolds; simpl; auto.
    simpl; auto. 
    }

  assert(Hss:
      (Set_struct'
           (Set_struct'
              (Set_struct'
                 (v'21 ++
                  (addr, OS_Q_DATA,
                  x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil) :: v'24) addr
                 OSEventGrp (Vint32 i0)) addr OSMsg
              (nth_val'
                 (Z.to_nat
                    ((Int.unsigned x1 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) /
                     4)) v2)) addr OSNMsgs
           (V$ Z.of_nat
                 (length
                    (nth_val'
                       (Z.to_nat
                          ((Int.unsigned x1 -
                            Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4)) v2
                     :: x3)))) =
        (v'21 ++
            (addr, OS_Q_DATA,
            nth_val' (Z.to_nat ((Int.unsigned x1 - Int.unsigned ($ 4)) / 4)) v2
            :: Vint32 i7 :: Vint32 i5 :: x18 :: Vint32 i0 :: nil) :: v'24)
    ).
    {
      rewrite Hs'.
      clear -Hrlh Hget'' H34.
      unfold RLH_ECBData_P in Hrlh .
      simpljoin1.
      unfold MatchLHMsgLength in H0.
      simpljoin1.
      unfold V_OSQEntries in H0. inverts H0.
      rewrite <- H3.
      assert((V$ Int.unsigned x) = Vint32 x).
      clear . int_auto.
      rewrite H0.
      clear - Hget'' H34 .
      assert(H42:exists addr, addr = (x, $ 0)).
      {
       exists (x, $ 0). eauto.
      }
      destruct H42.
      rename H into H42.
      eapply set_struct_update_nth_val'; eauto.
      eapply get_struct_vl; eauto.
      unfolds; simpl; auto.
      simpl; auto.
    }

  assert(Hss': (Set_struct'
        (Set_struct'
           (Set_struct'
              (Set_struct'
                 (v'21 ++
                  (addr, OS_Q_DATA,
                  x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil) :: v'24) addr
                 OSEventGrp (Vint32 i0)) addr OSMsg
              (nth_val'
                 (Z.to_nat
                    ((Int.unsigned x1 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) /
                     4)) v2)) addr OSNMsgs
           (V$ Z.of_nat
                 (length
                    (nth_val'
                       (Z.to_nat
                          ((Int.unsigned x1 -
                            Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4)) v2
                     :: x3)))) addr OSQSize (Vint32 x9)) =
        (v'21 ++
            (addr, OS_Q_DATA,
            nth_val' (Z.to_nat ((Int.unsigned x1 - Int.unsigned ($ 4)) / 4)) v2
            :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24)
                     ).
   {
      rewrite Hss.
      clear -Hrlh Hget'' H34.
      unfold RLH_ECBData_P in Hrlh .
      simpljoin1.
      unfold MatchLHMsgSize in H1.
      simpljoin1.
      unfold V_OSQSize in H1. inverts H1.
      assert((V$ Int.unsigned x9) = Vint32 x9).
      clear . int_auto.
      rewrite H1.
      clear - Hget'' H34 .
      assert(H42:exists addr, addr = (x, $ 0)).
      {
       exists (x, $ 0). eauto.
      }
      destruct H42.
      rename H into H42.
      rename x into x2.
      eapply set_struct_update_nth_val'; eauto.
      eapply get_struct_vl; eauto.
      unfolds; simpl; auto.
      simpl; auto. 
   }

  clear Hs Hs' Hss.
  assert( Hxx:forall x, x +ᵢ  $ 0 = x).
  {
    intros. clear. int_auto.
  }

  assert((Set_array' (v'26 ++ (b0, i4, Z.to_nat OS_EVENT_TBL_SIZE, x0) :: v'38) 
        (b0, i4)
        (update_nth_val 7
           (update_nth_val 6
              (update_nth_val 5
                 (update_nth_val 4
                    (update_nth_val 3
                       (update_nth_val 2
                          (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                             (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                       (nth_val' 3 etbl)) (nth_val' 4 etbl)) 
                 (nth_val' 5 etbl)) (nth_val' 6 etbl)) (nth_val' 7 etbl)))
          = (v'26 ++
            (b0, i4, Z.to_nat OS_EVENT_TBL_SIZE,
            update_nth_val 7
              (update_nth_val 6
                 (update_nth_val 5
                    (update_nth_val 4
                       (update_nth_val 3
                          (update_nth_val 2
                             (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                                (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                          (nth_val' 3 etbl)) (nth_val' 4 etbl)) 
                    (nth_val' 5 etbl)) (nth_val' 6 etbl)) (nth_val' 7 etbl)) :: v'38)
           ).
  {
      clear - H40 H49.
      assert(H33:exists addr, addr = (b0, i4)).
      {
       exists (b0, i4). eauto.
      }
      destruct H33.
      rename H into H33.
      rewrite <-H33 in *.
      eapply set_array_update_nth_val; eauto.
  }

    unfold R_Q_Data_P.
    intros; eauto.
    clear - Hget'' H50 H2 H58 Hss' H42 He Hxx H33 H21 H51 H10 H46 H40 H34 H49 H17.
    
  change (Int.mul ($ 1) ($ 0)) with ($0) in H46.
  change (Int.mul ($ 1) ($ 1)) with ($1) in H46.
  rewrite Int.add_zero in H46.
  change (($ 1 +ᵢ  Int.zero)) with ($ 1) in H46.
  change ($ 1 +ᵢ  $ 1) with ($2) in H46.
  change (($ 4 +ᵢ  ($ 2 +ᵢ  $ 2))) with ($8) in H46.
  rewrite Int.add_zero_l in H46.
  change ((Int.zero +ᵢ  $ 8)) with ($8) in H46.
  change ((Z.to_nat ((Int.unsigned ($ 8) - Int.unsigned ($ 8)) / 1))) with 0%nat in H46.
  change ((Z.to_nat ((Int.unsigned ($ 8 +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 1%nat in H46.
  change ((Z.to_nat ((Int.unsigned  (($ 8 +ᵢ  $ 1) +ᵢ  $ 1)  - Int.unsigned ($ 8)) / 1))) with 2%nat in H46.
  change ((Z.to_nat ((Int.unsigned ((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 3%nat in H46.
  change ((Z.to_nat ((Int.unsigned (((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 4%nat in H46.
  change ((Z.to_nat ((Int.unsigned ((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 5%nat in H46.
  change ((Z.to_nat ((Int.unsigned (((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1)  - Int.unsigned ($ 8)) / 1))) with 6%nat in H46.
  change ((Z.to_nat ((Int.unsigned ((((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 7%nat in H46.
  change ((Pos.to_nat 1)) with (1%nat) in H46.
  change ((Pos.to_nat 2)) with (2%nat) in H46.
  change ((Pos.to_nat 3)) with (3%nat) in H46.
  change ((Pos.to_nat 4)) with (4%nat) in H46.
  change ((Pos.to_nat 5)) with (5%nat) in H46.
  change ((Pos.to_nat 6)) with (6%nat) in H46.
  change ((Z.to_nat 7)) with (7%nat) in H46.
  change ((Pos.to_nat 8)) with (8%nat) in H46.
    
    Lemma BBB : 
    forall x y qid qdata_vl,
        x = y ->
        Get_struct x qid = Some (qid, OS_Q_DATA, qdata_vl) -> 
        Get_struct y qid = Some (qid, OS_Q_DATA, qdata_vl).
      intros.
      inverts H.
      auto.
    Qed.
    lets Hx:BBB Hss' H58. clear H58.
    
    Lemma CCC:
      forall x y qletbl qetbl,
      y = x ->
      Get_array x qletbl = Some (qletbl, Z.to_nat OS_EVENT_TBL_SIZE, qetbl) ->
      Get_array y qletbl = Some (qletbl, Z.to_nat OS_EVENT_TBL_SIZE, qetbl) .
        intros.
        inverts H.
        auto.
     Qed.
        
   destruct qid. inverts He. 
   clear H.
   assert(b <> x \/ b = x) by tauto.
   destruct H.
   {
      assert((b, i) <> (x, $ 0) ). clear - H. mauto.
    (*qid <> x12 *)
  
      assert(Get_struct (v'21 ++
        (x, $ 0, OS_Q_DATA, x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil)
        :: v'24) (b, i) =
      Some ((b, i), OS_Q_DATA, qdata_vl)). 
     {
        clear - H0 Hx.
        induction v'21.
        
        change (nil ++
            (x, $ 0, OS_Q_DATA, x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil) :: v'24) with
          ((x, $ 0, OS_Q_DATA, x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil) :: v'24).
        change (nil ++(
            x, $ 0, OS_Q_DATA,
        nth_val' (Z.to_nat ((Int.unsigned x1 - Int.unsigned ($ 4)) / 4)) v2
        :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24) with
          ((x, $ 0, OS_Q_DATA,
        nth_val' (Z.to_nat ((Int.unsigned x1 - Int.unsigned ($ 4)) / 4)) v2
        :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24) in Hx.
        unfold Get_struct in *.
        destruct (os_inv.beq_addrval (x, $ 0) (b, i)) eqn :H1.
        eapply beq_tid_true_eq in H1. tryfalse.
        fold Get_struct in *. auto.
        destruct a. destruct p.
        assert(a = (b, i) \/ a <> (b, i)) by tauto.
        destruct H.
        inverts H.
        unfold Get_struct in Hx.
        simpl in Hx.
        rewrite beq_pos_true in Hx.
        rewrite Int.eq_true in Hx.
        simpl in Hx.
        simpl.
        rewrite beq_pos_true .  rewrite Int.eq_true. auto.
        
        unfold Get_struct in Hx.
        simpl in Hx.
        unfold Get_struct.
        simpl.
        destruct (os_inv.beq_addrval a (b, i)) eqn : H2.
        eapply beq_tid_true_eq in H2. tryfalse.
        fold Get_struct in *. eapply IHv'21 in Hx. auto.
    }
(*     assert(H1' := H1). *)
    eapply H2 in H1.
    simpljoin1.
    do 3 eexists.
    splits; eauto.
    eapply CCC with (x:= (v'26 ++
      (b0, i4, Z.to_nat OS_EVENT_TBL_SIZE,
      update_nth_val 7
        (update_nth_val 6
           (update_nth_val 5
              (update_nth_val 4
                 (update_nth_val 3
                    (update_nth_val 2
                       (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                          (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                    (nth_val' 3 etbl)) (nth_val' 4 etbl)) (nth_val' 5 etbl))
           (nth_val' 6 etbl)) (nth_val' 7 etbl)) :: v'38)). eapply H42.
    
    assert (x2 <> (b0, i4) ).
    {
      unfold id_addrval' in H1.
      simpl in H1.
      inverts H1.
      unfold id_addrval in H33.
      simpl in H33.
      inverts H33.
      clear - H.
      mauto.
    }
    clear - H3 H4 Hxx.
    induction v'26.
    change ((nil ++
   (b0, i4, Z.to_nat OS_EVENT_TBL_SIZE,
   update_nth_val 7
     (update_nth_val 6
        (update_nth_val 5
           (update_nth_val 4
              (update_nth_val 3
                 (update_nth_val 2
                    (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                       (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                 (nth_val' 3 etbl)) (nth_val' 4 etbl)) (nth_val' 5 etbl))
        (nth_val' 6 etbl)) (nth_val' 7 etbl)) :: v'38)) with
          (((b0, i4, Z.to_nat OS_EVENT_TBL_SIZE,
   update_nth_val 7
     (update_nth_val 6
        (update_nth_val 5
           (update_nth_val 4
              (update_nth_val 3
                 (update_nth_val 2
                    (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                       (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                 (nth_val' 3 etbl)) (nth_val' 4 etbl)) (nth_val' 5 etbl))
        (nth_val' 6 etbl)) (nth_val' 7 etbl)) :: v'38)).
        change (nil ++
        (b0, i4,  Z.to_nat OS_EVENT_TBL_SIZE, x0) :: v'38)  with
          ((b0, i4, Z.to_nat OS_EVENT_TBL_SIZE, x0) :: v'38)  in H4.
        unfold Get_array in *.
        destruct (os_inv.beq_addrval (b0, i4) x2) eqn :H1.
        eapply beq_tid_true_eq in H1. tryfalse.
        auto.
        destruct a. destruct p.
        assert(a = x2 \/ a <> x2) by tauto.
        destruct H.
        inverts H.
        simpl in H4.
        rewrite eq_beq_addrval in H4.
        unfold Get_array. simpl.
        rewrite eq_beq_addrval. auto.
        
        unfold Get_array in H4.
        simpl in H4.
        unfold Get_array.
        simpl. 
        destruct (os_inv.beq_addrval a x2) eqn : H5.
        eapply beq_tid_true_eq in H5. tryfalse.
        fold Get_array in *. eapply IHv'26 in H4. auto.
    }
    
    assert (i <> $0 \/ i = $0) by tauto.
    destruct H0 as [Hi | Hi].
    {
      assert((b, i) <> (x, $ 0) ). clear - Hi. mauto.
    (*qid <> x12 *)
  
      assert(Get_struct (v'21 ++
        (x, $ 0, OS_Q_DATA, x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil)
        :: v'24) (b, i) =
      Some ((b, i), OS_Q_DATA, qdata_vl)). 
     {
        clear - H0 Hx.
        induction v'21.
        change (nil ++
            (x, $ 0, OS_Q_DATA, x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil) :: v'24) with
          ((x, $ 0, OS_Q_DATA, x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil) :: v'24).
        change (nil ++(
            x, $ 0, OS_Q_DATA,
        nth_val' (Z.to_nat ((Int.unsigned x1 - Int.unsigned ($ 4)) / 4)) v2
        :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24) with
          ((x, $ 0, OS_Q_DATA,
        nth_val' (Z.to_nat ((Int.unsigned x1 - Int.unsigned ($ 4)) / 4)) v2
        :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24) in Hx.
        unfold Get_struct in *.
        destruct (os_inv.beq_addrval (x, $ 0) (b, i)) eqn :H1.
        eapply beq_tid_true_eq in H1. tryfalse.
        fold Get_struct in *. auto.
        destruct a. destruct p.
        assert(a = (b, i) \/ a <> (b, i)) by tauto.
        destruct H.
        inverts H.
        unfold Get_struct in Hx.
        simpl in Hx.
        rewrite beq_pos_true in Hx.
        rewrite Int.eq_true in Hx.
        simpl in Hx.
        simpl.
        rewrite beq_pos_true .  rewrite Int.eq_true. auto.
        
        unfold Get_struct in Hx.
        simpl in Hx.
        unfold Get_struct.
        simpl.
        destruct (os_inv.beq_addrval a (b, i)) eqn : H2.
        eapply beq_tid_true_eq in H2. tryfalse.
        fold Get_struct in *. eapply IHv'21 in Hx. auto.
    }
(*     assert(H1' := H1). *)
    eapply H2 in H1.
(*     eapply H6 in Hget''. *)
    simpljoin1.
    do 3 eexists.
    splits; eauto.
    eapply CCC with (x:= (v'26 ++
      (b0, i4, Z.to_nat OS_EVENT_TBL_SIZE,
      update_nth_val 7
        (update_nth_val 6
           (update_nth_val 5
              (update_nth_val 4
                 (update_nth_val 3
                    (update_nth_val 2
                       (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                          (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                    (nth_val' 3 etbl)) (nth_val' 4 etbl)) (nth_val' 5 etbl))
           (nth_val' 6 etbl)) (nth_val' 7 etbl)) :: v'38)). eapply H42.
    tryfalse.
    }

    (* qid = x12 *)
    {
      assert((b, i) = (x, $ 0) ).
      {
        inverts H. inverts Hi. auto.
      }
      inverts H0.

      destruct etbl. clear - H21; tryfalse.
      destruct etbl. clear - H21; tryfalse.
      destruct etbl. clear - H21; tryfalse.
      destruct etbl. clear - H21; tryfalse.
      destruct etbl. clear - H21; tryfalse.
      destruct etbl. clear - H21; tryfalse.
      destruct etbl. clear - H21; tryfalse.
      destruct etbl. clear - H21; tryfalse.
       destruct etbl. 2 :clear - H21; tryfalse.
       
       destruct x0. clear - H46 . simpl in H46 . tryfalse.
       destruct x0. clear - H46 . simpl in H46 . tryfalse.
       destruct x0. clear - H46 . simpl in H46 . tryfalse.
       destruct x0. clear - H46 . simpl in H46 . tryfalse.
       destruct x0. clear - H46 . simpl in H46 . tryfalse.
       destruct x0. clear - H46 . simpl in H46 . tryfalse.
       destruct x0. clear - H46 . simpl in H46 . tryfalse.
       destruct x0. clear - H46 . simpl in H46 . tryfalse.
       destruct x0. 2:{clear - H46 . simpl in H46 . tryfalse. }
       simpl in H46 .
       simpl. simpl in H42.
      do 3 eexists.
      splits. eauto. eauto. 
           
      eapply CCC with (x:= (v'26 ++
      (b0, i4, Pos.to_nat 8, v :: v0 :: v1 :: v3 :: v4 :: v5 :: v6 :: v7 :: nil) :: v'38)). eapply H42.
      
      instantiate(1:= v :: v0 :: v1 :: v3 :: v4 :: v5 :: v6 :: v7 :: nil).
      clear - H40.
      
      induction v'26.
      simpl. 
      rewrite beq_pos_true. rewrite Int.eq_true. simpl. auto.
      destruct a. destruct p.
      change (((a, n, l) :: v'26) ++ (b0, i4, Pos.to_nat 8,
         v :: v0 :: v1 :: v3 :: v4 :: v5 :: v6 :: v7 :: nil) :: v'38) with ((a, n, l) :: (v'26 ++
         (b0, i4, Pos.to_nat 8, v :: v0 :: v1 :: v3 :: v4 :: v5 :: v6 :: v7 :: nil) :: v'38)) in *.
    unfold Get_array in *. fold Get_array in *.
    destruct (os_inv.beq_addrval a (b0, i4)) eqn:eq1.
    inverts H40.
    eapply IHv'26; eauto.
     
     { 
       clear H49 H51 H2 H10 H21 Hget'' H40 H50 H42 H33 Hss' H1 H H46 Hxx.
       induction v'21.
        simpl in Hx. 
        rewrite beq_pos_true in Hx. rewrite Int.eq_true in Hx. simpl in Hx.
        inverts Hx. simpl. auto.
        destruct a. destruct p.
        change (((a, t, l) :: v'21) ++ (x, $ 0, OS_Q_DATA, nth_val'
            (Z.to_nat ((Int.unsigned x1 - Int.unsigned ($ 4)) / 4))
                 v2 :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24) with ((a, t, l) :: (v'21 ++
                     (x, $ 0, OS_Q_DATA, nth_val' (Z.to_nat
                       ((Int.unsigned x1 - Int.unsigned ($ 4)) / 4)) v2
                         :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24)) in Hx.
        unfold Get_struct in *.
        destruct (os_inv.beq_addrval a (x, $ 0)) eqn: eq1.
        inverts H34.
        fold Get_struct in *.
        eapply IHv'21 in H34; eauto.
      }
      auto.
   }

  (* RETURN ′ OS_NO_ERR *)
  hoare forward. splits; eauto.
  clear . eapply Int.unsigned_range_2.
  
   (*else*)
  hoare forward.

  pure_auto.
  hoare forward.
  pure_auto.
  
  change (Int.mul ($ 1) ($ 0)) with ($0).
  change (Int.mul ($ 1) ($ 1)) with ($1).
  rewrite Int.add_zero.
  unfold id_addrval' in H15.
  simpl in H15.
  inverts H15.
  rewrite Int.add_zero.
  change (($ 1 +ᵢ  Int.zero)) with ($ 1).
  change ($ 1 +ᵢ  $ 1) with ($2).
  change (($ 4 +ᵢ  ($ 2 +ᵢ  $ 2))) with ($8).
  rewrite Int.add_zero_l.
  change ((Int.zero +ᵢ  $ 8)) with ($8).
  change ((Z.to_nat ((Int.unsigned ($ 8) - Int.unsigned ($ 8)) / 1))) with 0%nat.
  change ((Z.to_nat ((Int.unsigned ($ 8 +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 1%nat.
  change ((Z.to_nat ((Int.unsigned  (($ 8 +ᵢ  $ 1) +ᵢ  $ 1)  - Int.unsigned ($ 8)) / 1))) with 2%nat.
  change ((Z.to_nat ((Int.unsigned ((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 3%nat.
  change ((Z.to_nat ((Int.unsigned (((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 4%nat.
  change ((Z.to_nat ((Int.unsigned ((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 5%nat.
  change ((Z.to_nat ((Int.unsigned (((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1)  - Int.unsigned ($ 8)) / 1))) with 6%nat.
  change ((Z.to_nat ((Int.unsigned ((((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 7%nat.
  change ((Pos.to_nat 1)) with (1%nat).
  change ((Pos.to_nat 2)) with (2%nat).
  change ((Pos.to_nat 3)) with (3%nat).
  change ((Pos.to_nat 4)) with (4%nat).
  change ((Pos.to_nat 5)) with (5%nat).
  change ((Pos.to_nat 6)) with (6%nat).
  change ((Z.to_nat 7)) with (7%nat).
  change ((Pos.to_nat 8)) with (8%nat).

  destruct e.
  clear - Hrlh. unfold RLH_ECBData_P in Hrlh. tryfalse.
  2: clear - Hrlh; unfold RLH_ECBData_P in Hrlh; tryfalse.
  2: clear - Hrlh; unfold RLH_ECBData_P in Hrlh; tryfalse.
  2: clear - Hrlh; unfold RLH_ECBData_P in Hrlh; tryfalse.
  
  hoare_split_pure_all.
  simpljoin1.
  
  lets Hnomsg: msgqnode_p_nomsg Hrlh;eauto.
  destruct H12.
  2:{ tryfalse. }
  inverts H12. 
  change (Int.zero) with ($0).
  clear. int_auto.

  simpljoin1.
  assert(H100:=H12).
  hoare_lifts_trms_pre (Aop, absecblsid, evstructheapid, evarrayheapid).
  
  assert(opv = V$OS_NO_ERR \/ opv <> V$OS_NO_ERR ) by tauto.
  destruct H37.
  eapply abscsq_rule. 
  pure_auto. 
  eapply qquery_absimp_succ_else;eauto.
  can_change_aop_solver. 
  eapply absinfer_eq. 
  
  2:{
    eapply abscsq_rule. 
    pure_auto. 
    eapply qquery_absimp_succ_else_abt;eauto.
    can_change_aop_solver. 
    eapply absinfer_eq.
    eapply absabort_rule. 
  }
  inverts H37.
  clear H41.
  instantiate (1:= (update_nth_val 7
       (update_nth_val 6
          (update_nth_val 5
             (update_nth_val 4
                (update_nth_val 3
                   (update_nth_val 2
                      (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                         (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                   (nth_val' 3 etbl)) (nth_val' 4 etbl)) (nth_val' 5 etbl))
          (nth_val' 6 etbl)) (nth_val' 7 etbl))).
  instantiate (1:= i0).
  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold_OS_Q_DATA; eauto.
  exists (Vnull :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) v'21 v'24.
  instantiate (2:= (x, $ 0)).
  sep cancel (AEvStructHeap v'21) .
  sep cancel (AEvStructHeap v'24) .
  sep cancel (Astruct (x, $ 0)).
  sep cancel (Alvarmapsto os_code_defs.pdata).
  instantiate (2:= v'21 ++
     (x, $ 0, OS_Q_DATA,
     Vnull
     :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24).
  sep pauto. eauto.
  unfold R_MutexAttr_P. intros; tryfalse.
  pure_auto.

  eapply backward_rule1. 
  intros.
  eapply AEvArrayHeap_fold; eauto.
  exists ((update_nth_val 7
              (update_nth_val 6
                 (update_nth_val 5
                    (update_nth_val 4
                       (update_nth_val 3
                          (update_nth_val 2
                             (update_nth_val 1
                                (update_nth_val 0 x0
                                   (nth_val' 0 etbl))
                                (nth_val' 1 etbl))
                             (nth_val' 2 etbl))
                          (nth_val' 3 etbl))
                       (nth_val' 4 etbl)) 
                    (nth_val' 5 etbl)) 
                 (nth_val' 6 etbl)) (nth_val' 7 etbl))).
  exists v'26. exists v'38.
  instantiate (2:=(b0, i4)).
  sep pauto.
  destruct etbl. clear - H21; tryfalse.
  destruct etbl. clear - H21; tryfalse.
  destruct etbl. clear - H21; tryfalse.
  destruct etbl. clear - H21; tryfalse.
  destruct etbl. clear - H21; tryfalse.
  destruct etbl. clear - H21; tryfalse.
  destruct etbl. clear - H21; tryfalse.
  destruct etbl. clear - H21; tryfalse.
  destruct etbl. 2 :clear - H21; tryfalse.

  destruct x0. clear - H46 . simpl in H46 . tryfalse.
  destruct x0. clear - H46 . simpl in H46 . tryfalse.
  destruct x0. clear - H46 . simpl in H46 . tryfalse.
  destruct x0. clear - H46 . simpl in H46 . tryfalse.
  destruct x0. clear - H46 . simpl in H46 . tryfalse.
  destruct x0. clear - H46 . simpl in H46 . tryfalse.
  destruct x0. clear - H46 . simpl in H46 . tryfalse.
  destruct x0. clear - H46 . simpl in H46 . tryfalse.
  destruct x0. 2:{clear - H46 . simpl in H46 . tryfalse. }
  simpl in H46 .
  simpl. simpl in H58.
  eauto.
  
  eapply backward_rule1.
  intros. 
  eapply node_fold.
  instantiate (4:= b).
  sep pauto. eauto.
  pure_auto.
  eapply backward_rule1.
  intros. 
  eapply AOSEventTbl_fold.
  instantiate (2:= etbl).
  instantiate (2:= (b, $ 8) ).
  sep pauto.
  pure_auto.
  fold_AOSEvent.

  eapply backward_rule1.
  intros. 
  eapply AEventNode_fold.
  sep cancel AOSEvent.
  instantiate(2:=(DMsgQ (Vptr (v'49, Int.zero))
                               (x14 :: x13 :: x7 :: x8 :: Vptr (v'45, x1)
                                 :: Vint32 i8 :: Vint32 i7 :: Vptr (v'45, Int.zero) :: nil) 
                                  (x4 :: x6 :: nil) v2)).
  unfold AEventData.
  unfold AMsgData.
  unfold AOSQCtr.
  unfold AOSQBlk.
  sep pauto.
  unfold node.
  sep pauto.
  instantiate (4:= v'49).
  instantiate (3:= v'45).
  instantiate (2:= (v'45, $ 4)).
  sep pauto.
  split;eauto.
  pure_auto.
  split;eauto.
  pure_auto.
  unfold V_qfreeblk.
  unfold nth_val. auto.
  auto.
  compose_evsllseg.
  fold_AECBList.
  hoare forward prim.
    sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel tcbdllflag.

  unfold EvtInv.
  sep pauto.
  trycancel_EvtInv.
  
  assert(exists addr, addr = (x, $ 0)).
  {
    exists (x, $ 0). eauto.
  }
  destruct H41.
  sep cancel p_local.
  sep cancel Aier.
  instantiate (1:= LV os_code_defs.pdata @ OS_Q_DATA ∗
         |-> Vptr (x, $ 0) **
         LV pq @ OS_Q ∗ |-> Vptr (v'49, Int.zero) **
         LV psrc @ (char_t) ∗
         |-> Vptr
               (b,
               ((((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ
                   $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  
                $ 1) +ᵢ  $ 1) **
         LV pdest @ (char_t) ∗
         |-> Vptr
               (b0,
               (((((((i4 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1)
                  +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  
                $ 1) +ᵢ  $ 1) **
         LV pevent @ OS_EVENT ∗ |-> Vptr (b, Int.zero) **
         A_dom_lenv
           ((os_code_defs.pdata, OS_Q_DATA ∗)
            :: (pevent, OS_EVENT ∗)
               :: (pq, OS_Q ∗)
                  :: (psrc, (char_t) ∗)
                     :: (pdest, (char_t) ∗) :: nil)).
  rename x11 into x12.
  rewrite <- H41 in *.
  assert ((Set_struct'
                 (v'21 ++ (x12, OS_Q_DATA, x15 :: Vint32 i6 :: Vint32 i5
                    :: x18 :: Vint32 i1 :: nil) :: v'24) x12 OSEventGrp (Vint32 i0)) = (v'21 ++
                  (x12, OS_Q_DATA, x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i0 :: nil) :: v'24)).
   {
    clear - Hget'' H34 H41.
    eapply set_struct_update_nth_val'; eauto.
    unfolds; simpl; eauto.
    simpl; auto.
   }

  assert((Set_struct'
              (Set_struct' (v'21 ++(x12, OS_Q_DATA,
                     x15:: Vint32 i6 :: Vint32 i5  :: x18 :: Vint32 i1 :: nil) :: v'24) x12
                       OSEventGrp (Vint32 i0)) x12 OSMsg Vnull) = 
                         (v'21 ++ (x12, OS_Q_DATA,
                           Vnull :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i0 :: nil) :: v'24)).
    {
     rewrite H42.
    clear - Hget'' H34 H41.
    eapply set_struct_update_nth_val'; eauto.
    eapply get_struct_vl; eauto.
    unfolds; simpl; auto.
    simpl; auto.
    }

  change ((length nil)) with (0%nat).
  assert(
      (Set_struct'
           (Set_struct'
              (Set_struct'
                 (v'21 ++
                  (x12, OS_Q_DATA,  x15 :: Vint32 i6  :: Vint32 i5
                        :: x18 :: Vint32 i1 :: nil) :: v'24) x12
                 OSEventGrp (Vint32 i0)) x12 OSMsg Vnull) x12 OSNMsgs (V$ Z.of_nat 0)) =
                  (v'21 ++ (x12, OS_Q_DATA, Vnull :: Vint32 i7 :: Vint32 i5 :: x18 :: Vint32 i0 :: nil) :: v'24)
    ).
    {
      rewrite H50.
      clear -Hrlh Hget'' H34 H41.
      unfold RLH_ECBData_P in Hrlh .
      simpljoin1.
      unfold MatchLHMsgLength in H0.
      simpljoin1.
      unfold V_OSQEntries in H0. inverts H0.
      change ((length nil)) with (0%nat) in H3.
      rewrite <- H3.
      assert((V$ Int.unsigned x0) = Vint32 x0).
      clear . int_auto.
      rewrite H0.
      clear - Hget'' H34 .
      assert(H33:exists addr, addr = (x, $ 0)).
      {
       exists (x, $ 0). eauto.
      }
      destruct H33.
      rename H into H33.
      eapply set_struct_update_nth_val'; eauto.
      eapply get_struct_vl; eauto.
      unfolds; simpl; auto.
      simpl; auto.
     }
  assert((Set_struct'
        (Set_struct'
           (Set_struct'
              (Set_struct'
                 (v'21 ++(x12, OS_Q_DATA, x15 :: Vint32 i6 :: Vint32 i5
                    :: x18 :: Vint32 i1 :: nil) :: v'24) x12 OSEventGrp (Vint32 i0)) x12 OSMsg Vnull) x12 OSNMsgs 
                     (V$ Z.of_nat 0)) x12 OSQSize (Vint32 x3)) =
                       (v'21 ++ (x12, OS_Q_DATA, Vnull :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24)
                     ).
   {
       rewrite H58.
      clear -Hrlh Hget'' H34.
      unfold RLH_ECBData_P in Hrlh .
      simpljoin1.
      unfold MatchLHMsgSize in H1.
      simpljoin1.
      unfold V_OSQSize in H1. inverts H1.
      assert((V$ Int.unsigned x3) = Vint32 x3).
      clear . int_auto.
      rewrite H1.
      clear - Hget'' H34 .
      eapply set_struct_update_nth_val'; eauto.
      eapply get_struct_vl; eauto.
      unfolds; simpl; auto.
      simpl; auto.
    }

  rewrite <- H59 in H37.
  sep cancel AEvStructHeap.
  assert( forall x, x +ᵢ  $ 0 = x).
  {
    intros. clear. int_auto.
  }

  assert((Set_array' (v'26 ++ (b0, i4, Z.to_nat OS_EVENT_TBL_SIZE, x0) :: v'38) 
        (b0, i4)
        (update_nth_val 7
           (update_nth_val 6
              (update_nth_val 5
                 (update_nth_val 4
                    (update_nth_val 3
                       (update_nth_val 2
                          (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                             (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                       (nth_val' 3 etbl)) (nth_val' 4 etbl)) 
                 (nth_val' 5 etbl)) (nth_val' 6 etbl)) (nth_val' 7 etbl)))
          = (v'26 ++
            (b0, i4, Z.to_nat OS_EVENT_TBL_SIZE,
            update_nth_val 7
              (update_nth_val 6
                 (update_nth_val 5
                    (update_nth_val 4
                       (update_nth_val 3
                          (update_nth_val 2
                             (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                                (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                          (nth_val' 3 etbl)) (nth_val' 4 etbl)) 
                    (nth_val' 5 etbl)) (nth_val' 6 etbl)) (nth_val' 7 etbl)) :: v'38)
           ).
  {
      clear - H40 H49.
      assert(H33:exists addr, addr = (b0, i4)).
      {
       exists (b0, i4). eauto.
      }
      destruct H33.
      rename H into H33.
      rewrite <-H33 in *.
      eapply set_array_update_nth_val; eauto.
     }

  remember ((update_nth_val 0 x0 (nth_val' 0 etbl))).
  remember ((update_nth_val 1 l (nth_val' 1 etbl))).
  remember ((update_nth_val 2 l0 (nth_val' 2 etbl))).
  remember ((update_nth_val 3 l1 (nth_val' 3 etbl))).
  remember ((update_nth_val 4 l2 (nth_val' 4 etbl))).
  remember ((update_nth_val 5 l3 (nth_val' 5 etbl))).
  remember ((update_nth_val 6 l4 (nth_val' 6 etbl))).
  remember ((update_nth_val 7 l5 (nth_val' 7 etbl))).
  
  apply AAA with (x:= v'26 ++ (b0, i4, Z.to_nat OS_EVENT_TBL_SIZE, l6) :: v'38). auto.
  sep cancel AEvArrayHeap.
  sep pauto.
  auto. auto. auto.
  2: auto.
  2: pure_auto.

  assert(exists addr, addr = (x, $ 0)).
  {
    exists (x, $ 0). eauto.
  }
  destruct H41.
  rename x11 into x12.
  rewrite <- H41 in *.
  assert ((Set_struct'
                 (v'21 ++ (x12, OS_Q_DATA, x15 :: Vint32 i6
                   :: Vint32 i5 :: x18 :: Vint32 i1 :: nil)  :: v'24) x12 OSEventGrp
                   (Vint32 i0)) = (v'21 ++ (x, $ 0, OS_Q_DATA, x15
                    :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i0 :: nil) :: v'24)).
   {
    clear - Hget'' H34 H41.
    rewrite <- H41.
    eapply set_struct_update_nth_val'; eauto.
    unfolds; simpl; auto.
    simpl; auto.
   }

  assert((Set_struct'
              (Set_struct'
                 (v'21 ++
               (x12, OS_Q_DATA, x15
                 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil)
                  :: v'24) x12 OSEventGrp (Vint32 i0)) x12 OSMsg
                   Vnull) = (v'21 ++ (x12, OS_Q_DATA,
                  Vnull :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i0 :: nil) :: v'24)
                     ).
    {
      rewrite H50.
    clear - Hget'' H34 H41.
    rewrite <- H41.
    eapply set_struct_update_nth_val'; try eapply get_struct_vl; eauto.
    unfolds; simpl; auto.
    simpl ;auto.
   }
  change ((length nil)) with 0%nat.
  assert(
      (Set_struct'
           (Set_struct'
              (Set_struct'
                 (v'21 ++
                  (x12, OS_Q_DATA,
                  x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil) :: v'24) x12
                 OSEventGrp (Vint32 i0)) x12 OSMsg Vnull) x12 OSNMsgs
                  (V$ Z.of_nat 0)) = (v'21 ++
                 (x12, OS_Q_DATA, Vnull :: Vint32 i7 :: Vint32 i5 :: x18 :: Vint32 i0 :: nil) :: v'24)
    ).
    {
      rewrite H58.
      clear -Hrlh Hget'' H34 H41.
      unfold RLH_ECBData_P in Hrlh .
      simpljoin1.
      unfold MatchLHMsgLength in H0.
      simpljoin1.
      unfold V_OSQEntries in H0. inverts H0.
      change ((length nil)) with 0%nat in H3.
      rewrite <- H3.
      assert((V$ Int.unsigned x0) = Vint32 x0).
      clear . int_auto.
      rewrite H0.
      clear - Hget'' H34 .
      assert(H42:exists addr, addr = (x, $ 0)).
      {
       exists (x, $ 0). eauto.
      }
      destruct H42.
      rename H into H42.
      eapply set_struct_update_nth_val'; try eapply get_struct_vl; eauto.
      unfolds; simpl; auto.
      simpl; auto.
    }

  assert((Set_struct'
        (Set_struct'
           (Set_struct'
              (Set_struct'
                 (v'21 ++
                  (x12, OS_Q_DATA,
                  x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil) :: v'24) x12
                 OSEventGrp (Vint32 i0)) x12 OSMsg
              Vnull) x12 OSNMsgs (V$ Z.of_nat
                 0)) x12 OSQSize (Vint32 x3)) =  (v'21 ++
            (x12, OS_Q_DATA, Vnull :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24)
                ).
   {
       rewrite H59.
      clear -Hrlh Hget'' H34 H41.
      unfold RLH_ECBData_P in Hrlh .
      simpljoin1.
      unfold MatchLHMsgSize in H1.
      simpljoin1.
      unfold V_OSQSize in H1. inverts H1.
      assert((V$ Int.unsigned x3) = Vint32 x3).
      clear . int_auto.
      rewrite H1.
      clear - Hget'' H34 .
      assert(H42:exists addr, addr = (x, $ 0)).
      {
       exists (x, $ 0). eauto.
      }
      destruct H42.
      rename H into H42.
      rename x0 into x2.
      eapply set_struct_update_nth_val'; try eapply get_struct_vl; eauto.
      unfolds; simpl; eauto.
      simpl; auto.
     }
  clear H58 H59 .
  assert( Hxx:forall x, x +ᵢ  $ 0 = x).
  {
    intros. clear. int_auto.
  }

  assert((Set_array' (v'26 ++ (b0, i4, Z.to_nat OS_EVENT_TBL_SIZE, x0) :: v'38) 
        (b0, i4)
        (update_nth_val 7
           (update_nth_val 6
              (update_nth_val 5
                 (update_nth_val 4
                    (update_nth_val 3
                       (update_nth_val 2
                          (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                             (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                       (nth_val' 3 etbl)) (nth_val' 4 etbl)) 
                 (nth_val' 5 etbl)) (nth_val' 6 etbl)) (nth_val' 7 etbl)))
          = (v'26 ++
            (b0, i4, Z.to_nat OS_EVENT_TBL_SIZE,
            update_nth_val 7
              (update_nth_val 6
                 (update_nth_val 5
                    (update_nth_val 4
                       (update_nth_val 3
                          (update_nth_val 2
                             (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                                (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                          (nth_val' 3 etbl)) (nth_val' 4 etbl)) 
                    (nth_val' 5 etbl)) (nth_val' 6 etbl)) (nth_val' 7 etbl)) :: v'38)
           ).
  {
      clear - H40 H49.
      assert(H33:exists addr, addr = (b0, i4)).
      {
       exists (b0, i4). eauto.
      }
      destruct H33.
      rename H into H33.
      rewrite <-H33 in *.
      eapply set_array_update_nth_val; eauto.
  }

    unfold R_Q_Data_P.
    intros; eauto.
    clear - Hget'' H2 H60 H58 H59 Hxx H33 H21 H51 H10 H17 H46 H40 H34 H41.
    
  change (Int.mul ($ 1) ($ 0)) with ($0) in H46.
  change (Int.mul ($ 1) ($ 1)) with ($1) in H46.
  rewrite Int.add_zero in H46.
  change (($ 1 +ᵢ  Int.zero)) with ($ 1) in H46.
  change ($ 1 +ᵢ  $ 1) with ($2) in H46.
  change (($ 4 +ᵢ  ($ 2 +ᵢ  $ 2))) with ($8) in H46.
  rewrite Int.add_zero_l in H46.
  change ((Int.zero +ᵢ  $ 8)) with ($8) in H46.
  change ((Z.to_nat ((Int.unsigned ($ 8) - Int.unsigned ($ 8)) / 1))) with 0%nat in H46.
  change ((Z.to_nat ((Int.unsigned ($ 8 +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 1%nat in H46.
  change ((Z.to_nat ((Int.unsigned  (($ 8 +ᵢ  $ 1) +ᵢ  $ 1)  - Int.unsigned ($ 8)) / 1))) with 2%nat in H46.
  change ((Z.to_nat ((Int.unsigned ((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 3%nat in H46.
  change ((Z.to_nat ((Int.unsigned (((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 4%nat in H46.
  change ((Z.to_nat ((Int.unsigned ((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 5%nat in H46.
  change ((Z.to_nat ((Int.unsigned (((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1)  - Int.unsigned ($ 8)) / 1))) with 6%nat in H46.
  change ((Z.to_nat ((Int.unsigned ((((((($ 8 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) - Int.unsigned ($ 8)) / 1))) with 7%nat in H46.
  change ((Pos.to_nat 1)) with (1%nat) in H46.
  change ((Pos.to_nat 2)) with (2%nat) in H46.
  change ((Pos.to_nat 3)) with (3%nat) in H46.
  change ((Pos.to_nat 4)) with (4%nat) in H46.
  change ((Pos.to_nat 5)) with (5%nat) in H46.
  change ((Pos.to_nat 6)) with (6%nat) in H46.
  change ((Z.to_nat 7)) with (7%nat) in H46.
  change ((Pos.to_nat 8)) with (8%nat) in H46.
  
    lets Hx:BBB H60 H59. clear H59.
   destruct qid. inverts H41. 
   clear H.
   assert(b <> x \/ b = x) by tauto.
   destruct H.
   {
      assert((b, i) <> (x, $ 0) ). clear - H. mauto.
    (*qid <> x12 *)
  
      assert(Get_struct (v'21 ++
        (x, $ 0, OS_Q_DATA, x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil)
        :: v'24) (b, i) =
      Some ((b, i), OS_Q_DATA, qdata_vl)). 
     {
        clear - H0 Hx.
        induction v'21.
        change (nil ++
            (x, $ 0, OS_Q_DATA, x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil) :: v'24) with
          ((x, $ 0, OS_Q_DATA, x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil) :: v'24).
        change (nil ++(
            x, $ 0, OS_Q_DATA,
       Vnull
        :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24) with
          ((x, $ 0, OS_Q_DATA,
        Vnull
        :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24) in Hx.
        unfold Get_struct in *.
        destruct (os_inv.beq_addrval (x, $ 0) (b, i)) eqn :H1.
        eapply beq_tid_true_eq in H1. tryfalse.
        fold Get_struct in *. auto.
        destruct a. destruct p.
        assert(a = (b, i) \/ a <> (b, i)) by tauto.
        destruct H.
        inverts H.
        unfold Get_struct in Hx.
        simpl in Hx.
        rewrite beq_pos_true in Hx.
        rewrite Int.eq_true in Hx.
        simpl in Hx.
        simpl.
        rewrite beq_pos_true .  rewrite Int.eq_true. auto.
        
        unfold Get_struct in Hx.
        simpl in Hx.
        unfold Get_struct.
        simpl.
        destruct (os_inv.beq_addrval a (b, i)) eqn : H2.
        eapply beq_tid_true_eq in H2. tryfalse.
        fold Get_struct in *. eapply IHv'21 in Hx. auto.
    }
    eapply H2 in H1.
    simpljoin1.
    do 3 eexists.
    splits; eauto.
    eapply CCC with (x:= (v'26 ++
      (b0, i4, Z.to_nat OS_EVENT_TBL_SIZE,
      update_nth_val 7
        (update_nth_val 6
           (update_nth_val 5
              (update_nth_val 4
                 (update_nth_val 3
                    (update_nth_val 2
                       (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                          (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                    (nth_val' 3 etbl)) (nth_val' 4 etbl)) (nth_val' 5 etbl))
           (nth_val' 6 etbl)) (nth_val' 7 etbl)) :: v'38)). (* rewrite Hxx.  *)eapply H58.
    
    assert (x1 <> (b0, i4) ).
    {
      unfold id_addrval' in H1.
      simpl in H1.
      inverts H1.
      unfold id_addrval in H33.
      simpl in H33.
      inverts H33.
      clear - H.
      mauto.
    }
    clear - H4 H3 Hxx.
    induction v'26.
    change ((nil ++
   (b0, i4, Z.to_nat OS_EVENT_TBL_SIZE,
   update_nth_val 7
     (update_nth_val 6
        (update_nth_val 5
           (update_nth_val 4
              (update_nth_val 3
                 (update_nth_val 2
                    (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                       (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                 (nth_val' 3 etbl)) (nth_val' 4 etbl)) (nth_val' 5 etbl))
        (nth_val' 6 etbl)) (nth_val' 7 etbl)) :: v'38)) with
          (((b0, i4, Z.to_nat OS_EVENT_TBL_SIZE,
   update_nth_val 7
     (update_nth_val 6
        (update_nth_val 5
           (update_nth_val 4
              (update_nth_val 3
                 (update_nth_val 2
                    (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                       (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                 (nth_val' 3 etbl)) (nth_val' 4 etbl)) (nth_val' 5 etbl))
        (nth_val' 6 etbl)) (nth_val' 7 etbl)) :: v'38)).
        change (nil ++
        (b0, i4, Z.to_nat OS_EVENT_TBL_SIZE, x0) :: v'38)  with
          ((b0, i4, Z.to_nat OS_EVENT_TBL_SIZE, x0) :: v'38)  in H4.
        unfold Get_array in *.
        destruct (os_inv.beq_addrval (b0, i4) x1) eqn :H1.
        eapply beq_tid_true_eq in H1. tryfalse.
        auto.
        destruct a. destruct p.
        assert(a = x1 \/ a <> x1) by tauto.
        destruct H.
        inverts H.
        simpl in H4.
        rewrite eq_beq_addrval in H4.
        unfold Get_array. simpl.
        rewrite eq_beq_addrval. auto.
        
        unfold Get_array in H4.
        simpl in H4.
        unfold Get_array.
        simpl. 
        destruct (os_inv.beq_addrval a x1) eqn : H5.
        eapply beq_tid_true_eq in H5. tryfalse.
        fold Get_array in *. eapply IHv'26 in H4. auto.
    }
    
    assert (i <> $0 \/ i = $0) by tauto.
    destruct H0 as [Hi | Hi].
    {
      assert((b, i) <> (x, $ 0) ). clear - Hi. mauto.
    (*qid <> x12 *)
  
      assert(Get_struct (v'21 ++
        (x, $ 0, OS_Q_DATA, x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil)
        :: v'24) (b, i) =
      Some ((b, i), OS_Q_DATA, qdata_vl)). 
     {
        clear - H0 Hx.
        induction v'21.
        change (nil ++
            (x, $ 0, OS_Q_DATA, x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil) :: v'24) with
          ((x, $ 0, OS_Q_DATA, x15 :: Vint32 i6 :: Vint32 i5 :: x18 :: Vint32 i1 :: nil) :: v'24).
        change (nil ++(
            x, $ 0, OS_Q_DATA, Vnull
        :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24) with
          ((x, $ 0, OS_Q_DATA,
        Vnull :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24) in Hx.
        unfold Get_struct in *.
        destruct (os_inv.beq_addrval (x, $ 0) (b, i)) eqn :H1.
        eapply beq_tid_true_eq in H1. tryfalse.
        fold Get_struct in *. auto.
        destruct a. destruct p.
        assert(a = (b, i) \/ a <> (b, i)) by tauto.
        destruct H.
        inverts H.
        unfold Get_struct in Hx.
        simpl in Hx.
        rewrite beq_pos_true in Hx.
        rewrite Int.eq_true in Hx.
        simpl in Hx.
        simpl.
        rewrite beq_pos_true .  rewrite Int.eq_true. auto.
        
        unfold Get_struct in Hx.
        simpl in Hx.
        unfold Get_struct.
        simpl.
        destruct (os_inv.beq_addrval a (b, i)) eqn : H2.
        eapply beq_tid_true_eq in H2. tryfalse.
        fold Get_struct in *. eapply IHv'21 in Hx. auto.
    }
(*     assert(H1' := H1). *)
    eapply H2 in H1.
(*     eapply H6 in Hget''. *)
    simpljoin1.
    do 3 eexists.
    splits; eauto.
    eapply CCC with (x:= (v'26 ++
      (b0, i4, Z.to_nat OS_EVENT_TBL_SIZE,
      update_nth_val 7
        (update_nth_val 6
           (update_nth_val 5
              (update_nth_val 4
                 (update_nth_val 3
                    (update_nth_val 2
                       (update_nth_val 1 (update_nth_val 0 x0 (nth_val' 0 etbl))
                          (nth_val' 1 etbl)) (nth_val' 2 etbl)) 
                    (nth_val' 3 etbl)) (nth_val' 4 etbl)) (nth_val' 5 etbl))
           (nth_val' 6 etbl)) (nth_val' 7 etbl)) :: v'38)).  eapply H58.
    tryfalse.
    }

    (* qid = x12 *)
    {
      assert((b, i) = (x, $ 0) ).
      {
        inverts H. inverts Hi. auto.
      }
      inverts H0.

      destruct etbl. clear - H21; tryfalse.
      destruct etbl. clear - H21; tryfalse.
      destruct etbl. clear - H21; tryfalse.
      destruct etbl. clear - H21; tryfalse.
      destruct etbl. clear - H21; tryfalse.
      destruct etbl. clear - H21; tryfalse.
      destruct etbl. clear - H21; tryfalse.
      destruct etbl. clear - H21; tryfalse.
       destruct etbl. 2 :clear - H21; tryfalse.
       
       destruct x0. clear - H46. simpl in H46. tryfalse.
       destruct x0. clear - H46. simpl in H46. tryfalse.
       destruct x0. clear - H46. simpl in H46. tryfalse.
       destruct x0. clear - H46. simpl in H46. tryfalse.
       destruct x0. clear - H46. simpl in H46. tryfalse.
       destruct x0. clear - H46. simpl in H46. tryfalse.
       destruct x0. clear - H46. simpl in H46. tryfalse.
       destruct x0. clear - H46. simpl in H46. tryfalse.
       destruct x0. 2:{clear - H46. simpl in H46. tryfalse. }
       simpl in H46.
       simpl. simpl in H58.
      do 3 eexists.
      splits. eauto. eauto. 
           
      eapply CCC with (x:= (v'26 ++
      (b0, i4, Pos.to_nat 8, v :: v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: nil) :: v'38)). eapply H58.
      
      instantiate(1:= v :: v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: nil).
      clear - H40.
      
      induction v'26.
      simpl. 
      rewrite beq_pos_true. rewrite Int.eq_true. simpl. auto.
      {
          destruct a. destruct p.
          change (((a, n, l) :: v'26) ++ (b0, i4, Pos.to_nat 8,
             v :: v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: nil) :: v'38) with ((a, n, l) :: (v'26 ++
             (b0, i4, Pos.to_nat 8, v :: v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: nil) :: v'38)) in *.
        unfold Get_array in *. fold Get_array in *.
        destruct (os_inv.beq_addrval a (b0, i4)) eqn:eq1.
        inverts H40.
        eapply IHv'26; eauto.
      }

     { clear H33 H51 H2 H10 H21 Hget'' H40 H46 H60 H58 H1 H.
       induction v'21.
       simpl in Hx. 
       rewrite beq_pos_true in Hx. rewrite Int.eq_true in Hx. simpl in Hx.
       inverts Hx. simpl. auto.
       destruct a. destruct p.
        change (((a, t, l) :: v'21) ++ (x, $ 0, OS_Q_DATA,
        Vnull :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24) with ((a, t, l) :: (v'21 ++
                     (x, $ 0, OS_Q_DATA,
        Vnull :: Vint32 i7 :: Vint32 i8 :: x18 :: Vint32 i0 :: nil) :: v'24)) in Hx.
        unfold Get_struct in *.
        destruct (os_inv.beq_addrval a (x, $ 0)) eqn: eq1.
        inverts H34.
        fold Get_struct in *.
        eapply IHv'21 in H34; eauto.
       }
        auto.
 }
  (* RETURN ′ OS_NO_ERR *)
  hoare forward. splits; eauto.
  clear . eapply Int.unsigned_range_2.
  
  Unshelve.
  exact Tnull.
  exact (Vnull::nil).
  exact ($1).
  exact (Vnull::nil).
  exact ($1).
  exact (Vnull::nil).
Qed.
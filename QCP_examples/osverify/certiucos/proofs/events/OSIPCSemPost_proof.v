Require Import ucos_include.
(* Require Import absop_rules. *)
Require Import symbolic_lemmas.
Require Import os_ucos_h.
(* Require Import oscore_common. *)

Require Import abs_infer_abt.
Require Import sem_common.
Require Import sempend_pure.
Require Import sempost_pure.
Require Import tcblist_setnode_lemmas.
Require Import OSQPostPure.
Require Import evtinv_lemmas.

Require Import OSTimeTickPure. 
Require Import sem_lab.
Require Import evauxvar_lemmas.
Require Import evaux_pure.
Require Import freeevtlist_lemmas.
Require Import gjb_sem_common. 
Require Import gjb_common.
Require Import seplog_tactics.
(* Require Import OSIntExitIntPure. *)
Require Import seplog_trm_tacs.
Require Import hoare_forward_tac_ext.

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.

(* basically the same tac or lemma in OSSemPostProof.v *)
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

Hint Resolve noabs_oslinv.
Hint Extern 2 (_ <= _) => apply Z.leb_le; trivial.

Lemma absimp_sem_post_ipc_null_return:
  forall sid v' P sch s,
    sid = Vnull ->
    v' = (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) ->  
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (sem_post_ipc (sid :: v' :: nil)) s ||> ** P) 
      (<|| s ||> ** P ). 
Proof.
 intros.
 simpl.
 subst.
 infer_solver 0%nat. 
Qed.

Lemma absimp_sem_post_ipc_null_return_abt:
  forall sid v' P sch s,
    sid = Vnull ->
    v' <> (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) -> 
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (sem_post_ipc (sid :: v' :: nil)) s ||> ** P) 
      (<|| ABORT ||> ** P ). 
Proof.
  intros.
  simpl.
  eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
Qed.

Lemma absinfer_sem_post_ipc_no_active_evt_err: 
  forall a P els sch k s,
    can_change_aop P ->
    EcbMod.get els a = None ->
    k = V$ OS_ERR_EVENT_TYPE -> 
    absinfer sch
      (<|| spec_code_cons (sem_post_ipc (Vptr a :: k :: nil)) s ||> ** HECBList els ** P)
      (<|| s ||> ** HECBList els ** P). 
Proof.
  intros.
  subst.
  simpl.
  infer_solver 1%nat.
Qed.

Lemma absinfer_sem_post_ipc_no_active_evt_err_abt: 
  forall a P els sch k s,
    can_change_aop P ->
    EcbMod.get els a = None ->
    k <> V$ OS_ERR_EVENT_TYPE -> 
    absinfer sch
      (<|| spec_code_cons (sem_post_ipc (Vptr a :: k :: nil)) s ||> ** HECBList els ** P)
      (<|| ABORT ||> ** HECBList els ** P). 
Proof.
  intros.
  simpl.
  eapply absinfer_trans; [eapply absinfer_choice2; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [eapply absinfer_choice1; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ | eapply absinfer_seq_abt; [ | | eauto]; pure_auto].
  eapply absinfer_seq; pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  pure_auto.
Qed.

Lemma absimp_sem_post_ipc_wrong_type_return:
  forall P els v' s sid sch,  
    can_change_aop P ->
    (exists d,
      EcbMod.get els sid = Some d /\ ~ (exists n wls, d = (abssem n, wls))) -> 
    v' = Vint32 (Int.repr OS_ERR_EVENT_TYPE) -> 
    absinfer sch
      (<|| spec_code_cons (sem_post_ipc ((Vptr sid) :: v' :: nil)) s ||> ** HECBList els ** P) 
      (<|| s ||> ** HECBList els ** P). 
Proof.
  intros.
  subst.
  simpl.
  infer_solver 2%nat.
Qed.

Lemma absimp_sem_post_ipc_wrong_type_abt:
  forall P els v' s sid sch,
    can_change_aop P ->
    (exists d,
      EcbMod.get els sid = Some d /\ ~ (exists n wls, d = (abssem n, wls))) -> 
    v' <> Vint32 (Int.repr OS_ERR_EVENT_TYPE) -> 
    absinfer sch
      (<|| spec_code_cons (sem_post_ipc ((Vptr sid) :: v' :: nil)) s ||> ** HECBList els ** P) 
      (<|| ABORT ||> ** HECBList els ** P).  
Proof.
  intros.
  simpljoin.
  simpl.
  do 2 ( eapply absinfer_trans; [eapply absinfer_choice2; [ | | eauto]; pure_auto | ]).
  eapply absinfer_trans; [eapply absinfer_choice1; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ | eapply absinfer_seq_abt; [ | | eauto]; pure_auto].
  eapply absinfer_seq; pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  pure_auto.
Qed.

Lemma absimp_sem_post_ipc_put_sem_return: 
  forall P els sid n wls sch v' s tcblh tcbvl vhold v11 v12 v13,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65535) = true ->
    v' = (Vint32 (Int.repr OS_NO_ERR)) -> 
    absinfer sch
      ( <|| spec_code_cons (sem_post_ipc ((Vptr sid) :: v' :: nil)) s ||> ** HECBList els ** EvtInv_part2 els tcblh tcbvl vhold v11 v12 v13 ** P) 
      ( <|| s ||> ** HECBList (EcbMod.set els sid (abssem (Int.add n Int.one), wls)) ** EvtInv_part2 (EcbMod.set els sid (abssem (Int.add n Int.one), wls)) tcblh tcbvl vhold v11 v12 v13 ** P).
Proof.
  intros.
  subst.
  simpl.
  infer_solver 5%nat.
  unfold EvtInv_part2 in *.
  unfold ASemEIBs in *.
  unfold AMuxEIBs in *.
  unfold AMqEIBs in *.
  sep pauto.
  eapply mq_ecb_p_sem_inc_preserve; eauto.
  eapply mux_ecb_p_sem_inc_preserve; eauto.
  eapply sem_ecb_p_sem_inc_preserve; eauto.
  eapply RH_SEM_EINFO_ECB_P_sem_inc; eauto.
  eapply RH_MUX_EIB_ECB_P_sem_inc_preserve; eauto.  
  eapply RH_EIB_ECB_Q_P_sem_inc_preserve; eauto.
Qed.

Lemma absimp_sem_post_ipc_put_sem_abt:  
  forall P els sid n wls sch v' s, 
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65535) = true ->
    v' <> (Vint32 (Int.repr OS_NO_ERR)) -> 
    absinfer sch
      ( <|| spec_code_cons (sem_post_ipc ((Vptr sid) :: v' :: nil)) s ||> ** HECBList els ** P) 
      ( <|| ABORT ||> ** HECBList els ** P).
Proof. 
  intros.
  simpl.
  do 5 ( eapply absinfer_trans; [eapply absinfer_choice2; [ | | eauto]; pure_auto | ]).
  eapply absinfer_trans; [ | eapply absinfer_seq_abt; [ | | eauto]; pure_auto].
  eapply absinfer_seq; pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  pure_auto.
Qed.

Lemma absimp_sem_post_ipc_ovf_err_return:
  forall P els eid n wls sch v'1 s,  
    can_change_aop P ->
    EcbMod.get els eid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65535) = false ->
    v'1 = Vint32 (Int.repr OS_SEM_OVF) ->  
    absinfer sch
      (<|| spec_code_cons (sem_post_ipc (Vptr eid :: v'1 :: nil)) s ||> ** HECBList els ** P) 
      (<|| s ||> ** HECBList els ** P).     
Proof.
  intros.
  simpl.
  subst.
  infer_solver 3%nat.
Qed.

Lemma absimp_sem_post_ipc_ovf_err_abt: 
  forall P els eid n wls sch v'1 s,  
    can_change_aop P ->
    EcbMod.get els eid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65535) = false ->
    v'1 <> Vint32 (Int.repr OS_SEM_OVF) -> 
    absinfer sch
      (<|| spec_code_cons (sem_post_ipc (Vptr eid :: v'1 :: nil)) s ||> ** HECBList els ** P) 
      (<|| ABORT ||> ** HECBList els ** P).   
Proof.
  intros.
  simpl.
  do 3 ( eapply absinfer_trans; [eapply absinfer_choice2; [ | | eauto]; pure_auto | ]).
  eapply absinfer_trans; [eapply absinfer_choice1; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ | eapply absinfer_seq_abt; [ | | eauto]; pure_auto].
  eapply absinfer_seq; pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  pure_auto.
Qed.

Lemma absimp_sem_post_ipc_ex_wt_succ_return:
  forall P els sid tls t' n wls p st m sch v' s t ct sus,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    ~ wls = nil ->
    GetHWait tls wls t' ->
    TcbMod.get tls t' = Some (p, st, m, sus) ->
    v' = V$ OS_NO_ERR -> 
    absinfer sch
             ( <|| spec_code_cons (sem_post_ipc ((Vptr sid) :: v' :: nil)) s ||> ** 
                             HECBList els ** HTCBList tls **
                             HTime t ** HCurTCB ct ** P ) 
             ( <|| END (Some (Vint32 (Int.repr OS_NO_ERR))) ;; s ||> **
                             HECBList (EcbMod.set els sid (abssem n, (remove_tid t' wls))) **
                             HTCBList (TcbMod.set tls t' (p, rdy, Vnull, sus)) **
                             HTime t ** HCurTCB ct ** P ). 
Proof.
  intros.
  simpl.
  subst.
  do 4 ( eapply absinfer_trans; [eapply absinfer_choice2; [ | | eauto]; pure_auto | ]).
  eapply absinfer_trans; [eapply absinfer_choice1; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ | eapply absinfer_seq; [ | | eapply absinfer_eq ]; pure_auto].
  eapply absinfer_trans; [ | eapply absinfer_seq_end; [ | | eauto]; pure_auto ].
  eapply absinfer_seq; pure_auto.
  infer_solver 0%nat.
Qed.

Lemma absimp_sem_post_ipc_ex_wt_succ_abt:
  forall P els sid tls n wls sch v' s,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    ~ wls = nil ->
    v' <> V$ OS_NO_ERR -> 
    absinfer sch
             ( <|| spec_code_cons (sem_post_ipc ((Vptr sid) :: v' :: nil)) s ||> **
                   HECBList els ** HTCBList tls ** P )  
             ( <|| ABORT ||> ** HECBList els ** HTCBList tls ** P ). 
Proof.
  intros.
  simpl.
  do 4 ( eapply absinfer_trans; [eapply absinfer_choice2; [ | | eauto]; pure_auto | ]).
  eapply absinfer_trans; [eapply absinfer_choice1; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ | eapply absinfer_seq_abt; [ | | eauto ]; pure_auto].
  eapply absinfer_seq; pure_auto.
  eapply absinfer_trans; [eapply absinfer_choice2; [ | | eauto]; pure_auto | ].
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  instantiate (3:=sem_post_ex_wt_abt (|Vptr sid :: v' :: nil|)). 
  instantiate (3:=s0).
  sep pauto.
  pure_auto.
Qed.

(* Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope. *)

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

Lemma OSIPCSemPost_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSIPCSemPost
                  vl logicl OSIPCSemPostPre ct->
      Some r =
      BuildRetI os_internal OSIPCSemPost vl logicl OSIPCSemPostPost ct->
      exists t d1 d2 s,
        os_internal OSIPCSemPost = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  rename v'3 into is.
  rename v'4 into isr.
  rename v'5 into ier.
  rename v'6 into vnest.
  rename v'7 into vlock.
  rename H0 into Hvnest.

  hoare_lifts_trms_pre (Aisr, Ais, A_isr_is_prop).
  transform_pre a_isr_is_prop_split ltac:(sep cancel Aisr; sep cancel Ais).
  eapply seq_rule.
  hoare_enter_critical2.

  lzh_hoare_if2.
  subst.
  eapply seq_rule.
  hoare_exit_critical2.

  hoare_lifts_trms_pre logicl.
  eapply backward_rule1.
  introv Hsat.
  eapply disj_star_elim_disj; eauto.
  hoare forward.
  2: { hoare_split_pure_all. tryfalse. }
  hoare_split_pure_all; subst.

  assert (Hor: v'2 <> (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) \/ 
                 v'2 = (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) by tauto.
  inversion Hor.
  (* v'2 <> ... *) 
  eapply abscsq_rule.
  pure_auto.
  (* change ((x :: nil) ++ v'1 :: nil) with (x::v'1::nil). *)
  eapply absimp_sem_post_ipc_null_return_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule.
  (* v'2 = ... *)
  eapply abscsq_rule.
  pure_auto.
  eapply absimp_sem_post_ipc_null_return; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq.
  (* return in case pevent = NULL *)
  hoare_lifts_trms_pre (Aisr, Ais).
  transform_pre add_a_isr_is_prop' ltac:(idtac).
  hoare forward.
  eapply adisj_intro; left.
  sep auto.

  hoare_lifts_trms_pre logicl.
  eapply backward_rule1.
  introv Hsat.
  eapply disj_star_elim_disj; eauto.
  hoare forward.
  hoare_split_pure_all. tryfalse.
  hoare unfold.

  rename v'11 into v11.
  rename v'12 into v12.
  rename v'13 into v13.


  rename v'14 into v'11.
  rename v'15 into v'12.
  rename v'16 into v'13.
  rename v'17 into v'14.
  rename v'18 into v'15.
  rename v'19 into v'16.

  rename v'3 into els.
  hoare_lifts_trms_pre EvtInv.
  eapply backward_rule1.
  introv Hsat.
  eapply unfold_EvtInv_frm in Hsat; eauto.
  unfold EvtInv_part1.
  unfold AECBList.
  hoare unfold.

  (* pevent points to an active ECB *) 
  rename H into H_elp. (* ECBList_P ... *)  
  rename H2 into Hgetecb; rename x0 into ecb.
  destruct ecb as (d & wls).
  lets Hctr: ECBList_P_get_ectr_some Hgetecb H_elp.
  destruct Hctr as (evl & etbl & petbl & Hgetectr).

  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat evsllseg.
  eapply get_ectr_decompose; eauto.
  hoare unfold.

  hoare_assert_pure (length v'22 = length v'24). 
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
  rename v'31 into pblk.
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
  
  (* the concrete type is not OS_EVENT_TYPE_SEM *) 
  hoare_assert_pure (~exists n wls, get els (pblk, Int.zero) = Some (abssem n, wls)).
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply semacc_eventtype_neq_sem in Hsat; eauto.
    sep split in Hsat.
    auto.
    go.
  }
  hoare_split_pure_all.
  assert (Hnsem: ~ (exists n wls0, (d, wls) = (abssem n, wls0))).
  {
    unfold get, EcbMap in H.
    rewrite Hgetecb in H.
    clear -H. introv He. simpljoin.
    eapply H; eauto.
  }

  hoare_lifts_trms_pre (Aop, absecblsid).
  rename v'2 into etype. 
  casetac etype (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) Heeq Hene.
  2: {
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absimp_sem_post_ipc_wrong_type_abt; eauto.
    go.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absimp_sem_post_ipc_wrong_type_return; eauto.  
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
  left. splits; eauto.
  eauto.

  (* the concrete type is OS_EVENT_TYPE_SEM *)
  apply semacc_int_eq_true in Hif_false. 
  subst.
  hoare_assert_pure (exists wls, v'26 = DSem i2 /\ absmq = (abssem i2, wls)).  
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply semacc_triangle_sem in Hsat; eauto.
    2: go. 
    sep split in Hsat.
    auto.
  }
  hoare_split_pure_all.
  destruct H as (Hdsem & Habssem).
  match type of Habssem with
    _ = (?e, ?w) =>
    assert (Hsem: get els (pblk, Int.zero) = Some (e, w)) 
  end.
  {
    eapply join_get_r; eauto.
    eapply join_get_l; eauto.
    rewrite get_a_sig_a; eauto. subst. auto.
  }

  subst.
(*   unfold get,EcbMap in Hsem. *)
(*   rewrite Hgetecb in Hsem; inverts Hsem. *)

  hoare_unfold.
  lzh_hoare_if2.

  Focus 2.
  lzh_hoare_if2.

  lzh_simpl_int_eq.
  unfold AOSTCBPrioTbl.
  hoare_split_pure_all.
  assert (Hnil : v'1 = nil).
  {
    lets Fnil: sempost_grp_wls_nil' H Hecbetbl; eauto.  
  }
  subst.
  hoare forward. 
  struct_type_match_solver.

  hoare_lifts_trms_pre (Aop, absecblsid,EvtInv_part2).
  assert (Hret: v'2 <> Vint32 (Int.repr OS_NO_ERR) \/ v'2 = Vint32 (Int.repr OS_NO_ERR)) 
    by tauto.
  inversion Hret as [Hretcase | Hretcase]. 
  (* v'2 <> ... *)
  eapply abscsq_rule.
  pure_auto.
  eapply absimp_sem_post_ipc_put_sem_abt; eauto. 
  go.
  eapply absinfer_eq. 
  eapply absabort_rule.
  (* v'2 = ... *)
  eapply abscsq_rule.
  pure_auto.
  eapply absimp_sem_post_ipc_put_sem_return; eauto. 
  go.
  eapply absinfer_eq.

  transform_pre sempost_inc_cnt_prop ltac:(sep cancel AEventData).
  hoare_split_pure_all.
  clear Hrlh Hecbetbl.

  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_part1.
  trycancel_EvtInv.
  unfold AECBList.
  sep normal.
  eexists.
  sep cancel OSEventList.
  eapply lzh_evsllseg_compose.
  sep cancel evsllseg.
  sep cancel evsllseg.
  unfold AEventNode.
  sep cancel AEventData.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep normal.
  sep eexists.
  sep cancel AOSPostEventTbl.
  sep cancel OS_EVENT_TBL_SIZE.
  sep cancel Astruct.
  sep split; eauto.

  assert (Heget: EcbMod.get els (pblk, Int.zero) = Some (abssem i2, nil)) by auto.
  assert (Hjsig: EcbMod.joinsig (pblk, Int.zero) (abssem i2, nil) mqls' els2) by auto.
  lets Hnewjoin: ecb_get_set_join_join Heget Hjsig Hjo.
  destruct Hnewjoin as [? [? ?]].
  eapply semacc_compose_EcbList_P; eauto.
  split; [auto | eapply sempost_struct_type_vallist_match_sem; auto].
  unfolds; simpl. auto.
  eauto.
  eauto.

  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_frm.
  sep cancel EvtInv_part1.
  sep cancel EvtInv_part2.
  eauto.
  (* EXIT_CRITICAL *)
  eapply seq_rule.
  hoare_exit_critical2.
   (* RETURN ′ OS_NO_ERR *) 
  hoare_lifts_trms_pre (Aisr, Ais).
  transform_pre add_a_isr_is_prop' ltac:(idtac).
  hoare forward.
  eapply adisj_intro; right.
  sep normal. sep eexists.
  sep cancel EvtInv.
  sep pauto; eauto.
  do 2 right. left.
  eexists.
  splits; eauto.
  eapply sempost_inc_RH_TCBList_ECBList_P_hold; eauto.
  eapply Int.eq_false; eauto.

  (********************** cnt = 65535, overflow! ************************)
  lzh_simpl_int_eq.
  unfold AOSTCBPrioTbl.
  hoare_split_pure_all.
  assert (Hnil : v'1 = nil).
  {
    lets Fnil: sempost_grp_wls_nil' H Hecbetbl; eauto.
  }
  subst.
  hoare_lifts_trms_pre (Aop, absecblsid).
  assert (Hv'1cs: v'2 <> Vint32 (Int.repr OS_SEM_OVF) \/
                  v'2 = Vint32 (Int.repr OS_SEM_OVF)) by tauto. 
  inversion Hv'1cs.
  (* v'2 <> ... *) 
  (* hoare lifts (29::20::nil)%nat pre.  *)
  eapply abscsq_rule.
  pure_auto.
  eapply absimp_sem_post_ipc_ovf_err_abt; eauto.
  go.
  eapply absinfer_eq.
  eapply absabort_rule.
  (* v'2 = ... *)
  eapply abscsq_rule.
  pure_auto.
  eapply absimp_sem_post_ipc_ovf_err_return; eauto.
  go.
  eapply absinfer_eq. 

  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.

  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_frm.
  eapply fold_EvtInv_part1.
  trycancel_EvtInv.
  sep cancel EvtInv_part2.
  eauto.

  (* EXIT_CRITICAL *)
  eapply seq_rule.
  hoare_exit_critical2.
   (* RETURN ′ OS_SEM_OVF *) 
  hoare_lifts_trms_pre (Aisr, Ais).
  transform_pre add_a_isr_is_prop' ltac:(idtac).
  hoare forward.
  eapply adisj_intro; right.
  sep normal. sep eexists.
  sep cancel EvtInv.
  sep pauto; eauto.
  right. left.
  eexists.
  splits; eauto.
  eapply Int.eq_false; eauto.

  (******************************* OSEventGrp != 0 ******************************) 

  hoare forward.
(*   hoare_unfold. *)
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.
  hoare unfold.
  hoare_assert_pure (v'16 = ct).
  { get_hsat Hsat.
     unfold p_local in Hsat.
     unfold CurTid in Hsat.
     sep normal in Hsat; sep destruct Hsat.
     sep_lifts_skp_in Hsat (OSTCBCur, _N_ 1).
     eapply read_only_merge_vptr in Hsat.
     destruct Hsat; auto.
   }
  hoare_split_pure_all; subst.

(*   hoare_split_pure_all. *)
(*   destruct H2. *)

(****************************** L2: event_task_rdy ******************************)
(*   destruct H45.  *)
  hoare_lifts_trms_pre (Aisr, Ais).
  transform_pre add_a_isr_is_prop' ltac:(idtac).
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
  (* ** ac: Locate tcbdllseg_get_last_tcb_ptr. *)
  (* ** ac: Check tcbdllseg_get_last_tcb_ptr. *)
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

  remember (spec_code_cons
                                              (sem_post_ipc ((Vptr (pblk, Int.zero) :: nil) ++ v'2 :: nil)) v'0) as abs_code.
  inverts H62.
  subst v'48.

  (** renameing **)
(*   rename v'38 into pevent_addr. *)
  rename ct into ctcb.
  rename v'78 into htcb_addr. (** highest tcb in pevent waitlist **)
  rename H35 into Hhtcb.
  rename H56 into Hctcb_in_tcblist. 
  rename v'49 into tcblist_head. 
  rename v'6 into tcblist_seg1.
  rename v'7 into ctcb_node.
  rename v'8 into tcblist_seg2.
  rename H39 into Hrel_et. 

  (* ** ac: Print prio_in_tbl. *)
  rename v'35 into rtbl. 
  (* ** ac: Print TCBList_P. *)

  rename v'31 into tcbls.
  rename v'26 into tcbls1. 
  rename v'28 into tcbls2.
  (** tcbls = tcbls1 ++ tcbls2, tcbls2 = cur_node ++ tcbls2' **)
  
  remember (tcblist_seg1 ++ ctcb_node :: tcblist_seg2) as tcblist.
  
  rename v'73 into hprio. 
  assert (Hprio: exists hprio', hprio = Vint32 hprio'). 
  {
    clear - H66. (** struct_type_vallist_match **)
    rename H66 into H. 
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

  rename v'67 into hnext. 
  rename v'74 into htcbx.
  rename v'75 into htcby.
  rename v'76 into hbitx.
  rename v'77 into hbity. 

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

  assert (Hs1: Int.unsigned v'61 <= 7). 
  {
    (* ** ac: Check osunmapvallist_prop. *)
    clear - H40 H16.
    apply osunmapvallist_prop in H16.
    mytac.
    rewrite H in H40.
    inverts H40.
    pure_auto.
  }

  assert (Hs2: Int.unsigned v'62 <= 255).
  {
    (* ** ac: Check array_int8u_nth_lt_len. *)
    clear - H41 Hs1 H52 H13.
    assert (Z.to_nat (Int.unsigned v'61) < length v'41)%nat. 
    {
      rewrite H13; unfold OS_EVENT_TBL_SIZE.
      unfold nat_of_Z.
      auto with zarith.
    }
    lets Hx: array_int8u_nth_lt_len H52 H.
    mytac.
    rewrite H41 in H0.
    inverts H0.
    auto.
  }

  assert (Hs3: Int.unsigned v'60 <= 7). 
  {
    clear - H42 Hs2.
    lets Hx: osunmapvallist_prop Hs2.
    mytac.
    rewrite H in H42; inverts H42.
    pure_auto.
  }

  rename v'1 into pwls.
  (* ** ac: Check post_exwt_succ_pre_sem. *)
  generalize Hhtcb_get; intro Hhtcb_join.
  apply map_join_get_sig in Hhtcb_join.
  destruct Hhtcb_join as (tcbls' & Hhtcb_join).
  assert (Hpre: pwls <> nil /\ GetHWait tcbls pwls (htcb_addr, Int.zero) /\
                TcbMod.get tcbls (htcb_addr, Int.zero) = Some (hprio, st, msg, sus) /\
                hprio = ((v'61<<ᵢ$ 3) +ᵢ  v'60)).
  {
    apply map_join_get_sig in Hhtcb_get.
    destruct Hhtcb_get.
    (* ** ac: Check post_exwt_succ_pre_sem. *)
    apply semacc_int_eq_false in H.
    eapply post_exwt_succ_pre_sem; eauto.
  }

  destruct Hpre as [ ? [? [? ?]]].
  subst hprio.

  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).
  assert (Hv'1cs: v'2 <> Vint32 (Int.repr OS_NO_ERR) \/
                  v'2 = Vint32 (Int.repr OS_NO_ERR)) by tauto.
  inversion Hv'1cs.
  (* v'2 <> ... *)
  eapply abscsq_rule.
  auto.
  eapply absimp_sem_post_ipc_ex_wt_succ_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule.
  (* v'2 = ... *)
  eapply abscsq_rule.
  auto.
  eapply absimp_sem_post_ipc_ex_wt_succ_return; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  (* eauto. *)
  (* eauto. *)
  (* eauto. *)
  (* eauto. *)

  unfold AEventData.
  unfold_msg.
  hoare_split_pure_all.
  destruct H38.
  inverts H38.
  rename v'7 into pevent_addr.

  unfolds in H46; simpl in H46; inverts H46.
  (* ** ac: Check sem_post_get_tcb_stat. *)
  rename v'41 into etbl.

  rename H61 into Htcblist_p.
  lets Hhtcb_node: TCBList_P_tcblist_get_TCBNode_P Htcblist_p Hhtcb Hhtcb_get.
  generalize Hhtcb_node; intro Htmp.
  unfolds in Htmp.
  mytac.
  inverts H38; inverts H46.

  rename H61 into Hh_tcbblk.
  rename H62 into Hh_tcbstat. 
  unfolds in Hh_tcbblk.
  mytac.
  inverts H75.
  inverts H37. inverts H38. inverts H46. inverts H61. inverts H62. inverts H68.
(*   inverts H55. *)

  rename v'61 into p1.
  rename v'60 into p2. 
  remember ((p1<<ᵢ$ 3) +ᵢ  p2) as hprio.
  (* ** ac: Check sem_post_get_tcb_stat. *)

  assert (Hx: x7 = $ OS_STAT_SEM \/ x7 = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)).
  {
    clear - Hrel_et.
    unfolds in Hrel_et.
    auto.
  }
  (* subst x7. *)

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

  assert (Hs4: Int.unsigned v'79 <= 255).
  {
    clear - Hs1 H32 H64 H49.
    assert (Z.to_nat (Int.unsigned p1) < length rtbl)%nat.
    {
      rewrite H64. 
      unfold OS_RDY_TBL_SIZE.
      mauto.
    }
    lets Htmp: array_int8u_nth_lt_len H49 H. 
    mytac.
    rewrite H32 in H0. 
    inverts H0.
    auto.
  }
  (* ** ac: Check set_node_elim_hoare. *)

  assert (Htmp: v'63 = $ 1 <<ᵢ p2). 
  {
    eapply math_mapval_core_prop.
    clear - Hs3.
    auto with zarith.
    auto.
  }
  subst v'63.

  assert (Hno_dup: R_Prio_No_Dup tcbls).
  {
    clear - H59.
    unfolds in H59.
    mytac.
  }
  (** zhang hui's lemma **)
  hoare_lifts_trms_pre tcbdllseg.
  eapply set_node_elim_hoare_sus with (tid:=ctcb) (tcbls:=tcbls); eauto.
  {
    eapply TCBNode_P_set_rdy_gen; auto.
    2:eauto.
    rewrite Hp1.
    apply nth_val'2nth_val; eauto.
    2: eauto.
    destruct Hx; subst x7.
    assert (Hsus: sus = false) by
    (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: sus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    change (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_SEM)) with ($ OS_STAT_SUSPEND).
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

  (************************* exit critical ***********************************)
  hoare_split_pure_all.
  subst hprio.
  rewrite Hp1 in *.
  rewrite Hp2 in *.

  assert (Heq_sus: Int.eq (x7&ᵢInt.not ($ OS_STAT_SEM)) ($ OS_STAT_RDY) = negb sus).
  { change ($ OS_STAT_RDY) with Int.zero.
    destruct Hx; subst x7.
    assert (Hsus: sus = false) by
    (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: sus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    change (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_SEM)) with ($ OS_STAT_SUSPEND).
    auto.
   }

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
  eapply lzh_evsllseg_compose.
  sep cancel evsllseg.
  sep cancel evsllseg.
  sep cancel AEventNode.
  sep split; eauto.
  eapply ecblist_p_post_exwt_hold_sem
    with (v'12:=v'39) (v'39:=p2) (v'38:=p1) (v'13:=etbl); eauto.
  eapply rl_etbl_ptbl_p; auto; eauto.
  eapply semacc_int_eq_false; eauto.
  clear - Hs3. mauto.
  unfolds; simpl; eauto.
  simpl update_nth_val; eauto.
  eauto.

  pure intro.
  (* OS_IPCSched *)
  hoare forward.
  eapply disj_split.
  left.
  sep cancel p_local.
  sep cancel 1%nat 1%nat.
  sep split.

  exact H68.
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
  inverts H68.

  eapply backward_rule1.
  intros.
  sep lift 9%nat in H68.

  apply disj_split in H68.
  exact H68.
  apply disj_rule.

  hoare unfold.


   (* RETURN ′ OS_NO_ERR *)
  hoare_lifts_trms_pre Aop. 
  eapply abscsq_rule.
  pure_auto.
  eapply absinfer_seq_end.
  pure_auto.
  2: eauto.
  pure_auto.
  eapply absinfer_eq.

  assert (Hin_pwls: In (htcb_addr, Int.zero) pwls).
  { clear -H35.
     unfolds in H35.
     simpljoin; auto.
  }
  assert (Hst: exists xl, st = wait (os_stat_sem (pevent_addr, Int.zero)) xl).
  {
    eapply rh_tcblist_ecblist_p_post_exwt_aux_sem ;eauto.
  }
  destruct Hst as (t_opt & Hst); subst st.
  assert (Heptr: exists wt, x8 = Vptr (pevent_addr, Int.zero) /\ v'71 = Vint32 wt).
  { clear -Hh_tcbstat.
     destruct Hh_tcbstat as (_ & _ & _ & _ & _ & Hstat).
     destruct Hstat as (_ & Hstat & H ).
     funfold H. simpljoin.
     destruct sus eqn: eq1.
     specialize (H3 _ _ _ _ (eq_refl _)).
     destruct H3 as (Hwt & Hptr & Hst); inverts Hptr; inverts Hst.
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
  eapply ASemEIBs_sem_set_wls'_preserve; eauto.
  sep cancel ASemEIBs.
  eapply AMuxEIBs_sem_set_wls'_preserve; eauto.
  sep cancel AMuxEIBs.
  eapply AMqEIBs_sem_set_wls'_preserve; eauto. 
  sep cancel AMqEIBs.
  unfold tcbllsegevaux.
  eapply llsegevaux_set_node; eauto.
  { unfold same_prev_next. simpl. splits; auto. }
  eapply mq_ecb_p_sem_set_wls'_preserve; eauto.
  eapply mux_ecb_p_sem_set_wls'_preserve; eauto.
  eapply sem_ecb_p_sem_set_wls'_preserve; eauto.

  rewrite Heq_sus. rewrite negb_if.
  repeat right.
  do 7 eexists. splits; eauto.
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

  eapply rh_tcblist_ecblist_p_post_exwt_sem;eauto.
  (*RH_PrioTbl_P*)
  eauto.
  (* R_PrioTbl_P *)
  eapply r_priotbl_p_set_hold; auto; eauto.
  eauto.
  eauto.
  (* TCBList_P *)
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
Qed.

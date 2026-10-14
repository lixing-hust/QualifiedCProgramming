Require Import ucos_include.
Require Import Lia.


Require Import aux_pureLib.
Require Import abs_op_corecommu_rules.
Require Import corecommu_sep_added.
Require Import corecommu_tactics.
Require Import sem_corecommu.
Require Import partition_rules.
Require Import partition_seprules.
Require Import partition_absrules.
Require Import partition_symrules.
Require Import partition_tactics.
Require Import qportpendproof_aux.
Require Import partinv_lemmas.

Ltac go ::=
  match goal with
    | |- struct_type_vallist_match _ _ => struct_type_match_solver
    | |- GoodFrm _ => clear; (good_frm_sovler || auto)
    | |- can_change_aop _ => clear; can_change_aop_solver' 
    | |- tidspec.beq _ _ = true =>apply CltEnvMod.beq_refl
    | |- tidspec.beq _ _ = false => apply tidspec.neq_beq_false; auto
    | |- EcbMod.get _ _ = Some _       => ecbget_joins_sig_solver
    | |- TcbMod.get _ _ = Some _       => tcbget_joins_sig_solver
    | |- _ /\ _                        => split; go
    | |- _ = _                         => try unfolds; simpl; auto 1
    | |- _                             => eauto 1
  end.



Lemma QPortPendProof :
  forall vl p r tid ,
    Some p = BuildPreA' os_api QPortPend qportpendapi vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api QPortPend qportpendapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api QPortPend = Some (t, d1, d2, s) /\
      {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |-tid {{p }} s {{ Afalse }}.
Proof.
  init_spec.
  destruct v'.
  { hoare name lift Aop pre.
    apply absabort_rule. }
  destruct v' as [ | errv ].
  { hoare name lift Aop pre.
    apply absabort_rule. }
  rename v'6 into ier. rename v'5 into err_v. rename v'4 into res_v. rename v'3 into sem_v. rename v'2 into chan_v. rename v'1 into dkp_v. rename v'0 into kp_v.
  rename x into msg_v. rename x1 into p_v. rename i into tm_v.
  (*resource_get_res ′ =ₑ ′ 0;ₛ  ... semaphore ′ =ₑ ′ DEFAULT_CHANNLE_SEMAPHROE;ₛ *)
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  (* ENTER_CRITICAL;ₛ If (OSIntNesting ′ >ₑ ′ 0) {EXIT_CRITICAL;ₛ *)
  hoare forward prim.
  pure intro.
  hoare name lift AGVars pre.
  unfold AGVars.
  pure intro.
  hoare forward.
  { pauto. }
  { hoare forward prim.
    unfold AGVars.
    sep pauto. auto.
    go.
    hoare remember (1%nat::nil) pre.
    hoare abscsq;[ apply noabs_oslinv | auto ..  ].
    assert (can_change_aop H6) by (subst H6;can_change_aop_solver).
    instantiate (1:= <|| END Some (Vint32 (Int.repr OS_ERR_PEND_ISR)) ||> ** H6).
    clear - H7.
    infer_solver 0%nat.
    subst H6.
    hoare forward. }
  hoare forward.
  pure intro.
  hoare forward prim.
  unfold AGVars.
  sep pauto. auto.
  go.
  clear - H1 H2 H3.
  hoare remember (1%nat::nil) pre.
  hoare abscsq;[ apply noabs_oslinv | auto ..  ].
  apply absinfer_choice2 with (q:= H).
  1,2: subst H; go.
  sep auto.
  subst H.
  (* ENTER_CRITICAL;ₛ If (port_ptr ′ ==ₑ 〈 OS_Port ∗ 〉 NULL) {.. };ₛ  EXIT_CRITICAL;ₛ *)
  partition_enter_trinv.
  destruct H3 as [ | [? ? ]].
  { subst p_v.
    partition_absrulestac port_indomainport_null_abt.
    apply absabort_rule. }
  subst p_v. rename x into p_v.
  hoare forward.
  destruct p_v;pauto.
  { pure intro.
    instantiate (1:= Afalse).
    exfalso.
    destruct p_v.
    simpl in H3. tryfalse. }
  hoare forward.
  pure intro.
  partition_exit_trinv.
  clear -H1 H2.
  (* ENTER_CRITICAL;ₛ If (port_ptr ′ .. coreNum !=ₑ ′ DNUM .. ) { .. };ₛ EXIT_CRITICAL;ₛ *)
  partition_enter_trinv.
  destruct (get dportls p_v) as [port | ] eqn: Hdp.
  2: { partition_absrulestac port_indomainport_none_abt;apply absabort_rule. }
  destruct port as [[[[[[[pcn  pd]  pid]  pdir]  pst ] pintick ] poutick ] pt].
  assert ((pcn = Z.to_nat DNUM) \/ (pcn <> Z.to_nat DNUM)) as [ | ] by tauto.
  2: { partition_absrulestac port_indomainport_none_abt';apply absabort_rule. }
  subst pcn.
  hoare name lift AOSDomainPortPtrList pre.
  destruct H5 as [H5 Hinecb].
  eapply pptr_in_dportls1 in H11 as ?;eauto.
  split_portlist. 
  unfold AOSDomainPortPtrList.
  hoare normal pre.
  hoare name lift dmportp_sll pre.
  eapply backward_rule1.
  eapply dmportp_sllseg_app'_frm;eauto.
  cbn [dmportp_sllseg].
  hoare normal pre.
  pure intro. 
  rename v'19 into p_v. rename v'8 into tcbls.
  eapply Forall_forall with (x := p_v) in Hinecb as ?.
  2: { eapply nth_error_in;eauto. }
  destruct H0 as (p & st & msg  & sus & ?).
  (* If (port_ptr ′ .. coreNum !=ₑ ′ DNUM ||ₑ port_ptr ′ .. OSEventType !=ₑ ′ OS_EVENT_TYPE_PORT
    ||ₑ OSTCBCur ′ .. OSTCBY !=ₑ port_ptr ′ .. domain) *)
  eapply seq_rule.
  eapply ift_rule'';[ symbolic_exe_port | ].
  { (* condition true *)
    instantiate (1:= Afalse).
    pure intro. clear H22 H23.
    rewrite ! Int.eq_true in *.
    assert (Int.eq (p >>ᵢ $ 3) ($ Z.of_nat pd) = false) by pauto.
    clear H18.
    partition_absrulestac port_indomainport_cont. 
    hoare name lift abstcblsid pre.
    hoare name lift curtid pre.
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply port_unmapped;eauto.
    { go.  }
    partition_exit_trinv.
    hoare forward. }
  hoare forward.
  pure intro.
  partition_exit_trinv.
  clear -H1 H2.
  (* ENTER_CRITICAL;ₛ If (port_ptr ′ .. os_code_defs.direction !=ₑ ′ DESTINATION) { .. };ₛ EXIT_CRITICAL;ₛ *)
  partition_enter_trinv.
  destruct (get dportls p_v) as [port | ] eqn: Hdp.
  2: { partition_absrulestac port_indomainport_none_abt. apply absabort_rule. }
  destruct port as [[[[[[[pcn  pd]  pid]  pdir]  pst ] pintick ] poutick ] pt].
  assert ((pcn = Z.to_nat DNUM) \/ (pcn <> Z.to_nat DNUM)) as [ | ] by tauto.
  2: { partition_absrulestac port_indomainport_none_abt';apply absabort_rule. }
  subst pcn.
  hoare name lift AOSDomainPortPtrList pre.
  destruct H5 as [H5 Hinecb].
  eapply pptr_in_dportls1 in H11 as ?;eauto.
  split_portlist.
  unfold AOSDomainPortPtrList.
  hoare normal pre.
  hoare name lift dmportp_sll pre.
  eapply backward_rule1.
  eapply dmportp_sllseg_app'_frm;eauto.
  cbn [dmportp_sllseg].
  hoare normal pre.
  pure intro.
  rename v'19 into p_v. 
  eapply seq_rule.
  eapply ift_rule'';[ symbolic_exe_port | ].
  { instantiate (1:= Afalse).
    pure intro.
    clear  H18 H22.
    destruct pdir.
    2: { exfalso. clear - H14.  rewrite Int.eq_true in *. mauto. }
    clear H14.
    partition_absrulestac port_indomainport_cont.
    partition_absrulestac portpend_err_dire_end.
    partition_exit_trinv. 
    hoare forward. }
  hoare forward.
  pure intro.
  destruct pdir.
  { exfalso. unfold SOURCE, DESTINATION in H14. clear - H14. destruct H14; mauto. }
  assert (OSPortAttrTblDir p_v = (V$ DESTINATION)).
  { eapply RL_PortAttr_dir_DES;eauto.
    rewrite nth_error_app2 by lia.
    rewrite Nat.sub_diag. simpl. auto. }
  partition_exit_trinv.
  clear -H1 H2 H18.  rename H18 into Hdir.
  (* ENTER_CRITICAL;ₛ If (port_ptr ′ .. mode !=ₑ ′ QUEUE){ .. };ₛ EXIT_CRITICAL;ₛ *)
  partition_enter_trinv.
  destruct (get dportls p_v) as [port | ] eqn: Hdp.
  2: { partition_absrulestac port_indomainport_none_abt. apply absabort_rule. }
  destruct port as [[[[[[[pcn  pd]  pid]  pdir]  pst ] pintick ] poutick ] pt].
  assert ((pcn = Z.to_nat DNUM) \/ (pcn <> Z.to_nat DNUM)) as [ | ] by tauto.
  2: { partition_absrulestac port_indomainport_none_abt';apply absabort_rule. }
  subst pcn.
  destruct H5 as [H5 Hinecb].
  eapply pptr_in_dportls1 in H11 as ?;eauto.
  split_portlist.
  unfold AOSDomainPortPtrList.
  hoare normal pre.
  hoare name lift dmportp_sll pre.
  eapply backward_rule1.
  eapply dmportp_sllseg_app'_frm;eauto.
  cbn [dmportp_sllseg].
  hoare normal pre.
  pure intro.
  rename v'19 into p_v. 
  destruct pdir.
  { exfalso. 
    eapply RL_PortAttr_dir_SOURCE in H16;eauto.
    rewrite H16 in Hdir. clear - Hdir. mauto.
    rewrite nth_error_app2 by lia.
    rewrite Nat.sub_diag. simpl. auto.  }
  eapply seq_rule.
  eapply ift_rule'';[ symbolic_exe_port | ].
  { pure intro.
    destruct pt.
    2: { exfalso. clear - H14.  rewrite Int.eq_true in *. mauto. }
    clear H14 H18 H22.
    partition_absrulestac port_indomainport_cont.  
    partition_absrulestac portpend_err_type_end. 
    partition_exit_trinv.
    hoare forward. }
  hoare forward.
  pure intro.
  destruct pt.
  { exfalso. unfold SAMPLE,QUEUE in H14. clear - H14. destruct H14; mauto. }
  assert (OSPortAttrTblMode p_v = (V$ QUEUE)).
  { eapply RL_PortAttr_mode_QUEUE ;eauto.
    rewrite nth_error_app2 by lia.
    rewrite Nat.sub_diag. simpl. auto. }
  partition_exit_trinv.
  clear -H1 H2 Hdir H18.  rename H18 into Hmode.
  (* ENTER_CRITICAL;ₛ If (msg_ptr ′ ==ₑ 〈 OSMsg_t ∗ 〉 NULL) { .. };ₛ EXIT_CRITICAL;ₛ *)
  partition_enter_trinv.
  destruct (get dportls p_v) as [port | ] eqn: Hdp.
  2: { partition_absrulestac port_indomainport_none_abt. apply absabort_rule. }
  destruct port as [[[[[[[pcn  pd]  pid]  pdir]  pst ] pintick ] poutick ] pt].
  assert ((pcn = Z.to_nat DNUM) \/ (pcn <> Z.to_nat DNUM)) as [ | ] by tauto.
  2: { partition_absrulestac port_indomainport_none_abt';apply absabort_rule. }
  subst pcn.
  hoare forward.
  destruct H1 as [ | [[? ?] ?]];subst;auto.
  destruct H1 as [ | [[? ?] ?]];subst;simpl;auto.
  { pure intro.
    assert (msg_v = Vnull) by pauto. subst msg_v.
    partition_absrulestac port_indomainport_cont.
    hoare abscsq;[apply noabs_oslinv | auto .. ].
    eapply absinfer_trans.
    eapply absinfer_choice2; [ | |  intros s Hs; exact Hs].
    1,2: can_change_aop_solver.
    eapply absinfer_trans.
    eapply absinfer_choice2; [ | |  intros s Hs; exact Hs].
    1,2: can_change_aop_solver.
    eapply absinfer_trans.
    eapply absinfer_choice2; [ | |  intros s Hs; exact Hs].
    1,2: can_change_aop_solver.
    eapply err_msgnull_end;eauto.
    can_change_aop_solver.
    partition_exit_trinv.
    hoare forward. }
  hoare forward.
  pure intro.
  assert (exists p, msg_v = Vptr p) as [msg_p ?].
  { destruct H1 as [ | [[? ?] ?]];subst;simpl;auto. destruct H13;tryfalse. eexists. eauto. }
  subst msg_v.
  partition_exit_trinv.
  clear - H1 H2 Hdir Hmode.
  (* msg_ptr ′ .. len =ₑ ′ 0;ₛ  TODO *)
  (* ENTER_CRITICAL;ₛ *)
  partition_enter_trinv.
  rename v'40 into cportlptr. rename v'41 into cportpl. 
  destruct (get dportls p_v) as [port | ] eqn: Hdp.
  2: { partition_absrulestac port_indomainport_none_abt. apply absabort_rule. }
  destruct port as [[[[[[[pcn  pd]  pid]  pdir]  pst ] pintick ] poutick ] pt].
  assert ((pcn = Z.to_nat DNUM) \/ (pcn <> Z.to_nat DNUM)) as [ | ] by tauto.
  2: { partition_absrulestac port_indomainport_none_abt';apply absabort_rule. }
  subst pcn.
  partition_absrulestac port_indomainport_cont.
  destruct H5 as [H5 Hinecb].
  eapply pptr_in_dportls1 in H11 as ?;eauto.
  split_portlist.
  destruct pdir.
  { exfalso. 
    eapply RL_PortAttr_dir_SOURCE in H4;eauto.
    rewrite H4 in Hdir. clear - Hdir. mauto.
    rewrite nth_error_app2 by lia.
    rewrite H18.
    rewrite Nat.sub_diag. simpl. auto. }
  destruct pt as [ ? | sz pq].
  { exfalso. 
    eapply RL_PortAttr_mode_SAMPLE in H4;eauto.
    rewrite H4 in Hmode. clear - Hmode. mauto.
    rewrite nth_error_app2 by lia.
    rewrite H18.
    rewrite Nat.sub_diag. simpl. auto. }
  unfold AOSDomainPortPtrList.
  hoare normal pre.
  hoare name lift dmportp_sll pre.
  eapply backward_rule1.
  eapply dmportp_sllseg_app'_frm;eauto.
  cbn [dmportp_sllseg].
  hoare normal pre.
  pure intro.
  rename v'19 into p_v. 
  (* kport ′ =ₑ OSKernelPortIDTbl ′ [port_ptr ′ .. portID];ₛ *)
  apply R_Kernelport_DomainPort_abs_getsome  with (pptr := p_v)in H9 as ?;auto.
  partition_destruct H14.
  unfold AOSKernelPortIDTbl.
  pure intro.
  unfold OS_K_Port_V_coreNum,  OS_K_Port_V_dmport, OS_K_Port_V_portID in *.
  cbn [nth_val] in *. inverts H24. inverts H25.
  assert (Int.repr DNUM = i1 ). 
  { destruct H17. unfold Domainport_nat_P in H17. partition_destruct H17.
    rewrite H17 in *. inversion H26. subst. auto. }
  subst i1.
  assert (pid < length (kportvl))%nat as Hpidlt.
  { destruct H17.  unfold Domainport_nat_P in *. partition_destruct H17. subst pid. rewrite H29. clear- H40. unfold PORT_NUMS in *.  mauto. }
  eapply seq_rule.
  hoare name lift (Alvarmapsto kport) pre.
  hoare name lift Aop pre.
  eapply assign_rule_lvar;[ 
  intro s; split; intro Hs; exact Hs|
  symbolic_exe_port| apply assign_type_match_true; simpl; auto | li_sepauto li ].
  { rewrite H29 in *. clear- Hpidlt.  unfold PORT_NUMS in *. mauto. }
  { rewrite H29 in *. clear- Hpidlt.  unfold PORT_NUMS in *.  mauto. }
  { eapply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match with (n := pid);eauto. }
  { rewrite H29 in *. clear - Hpidlt H29. unfold PORT_NUMS in *. rewrite Int.unsigned_repr by mauto. rewrite Nat2Z.id. auto. }
  assert (∘ (Int.unsigned i) = pid).
  { destruct H17.  unfold Domainport_nat_P in *. partition_destruct H17.
    rewrite H14 in *. simpljoin1. inverts H38. auto. }
  rewrite H24 in H18.
  erewrite nth_val_nth_val'_some_eq;eauto.
  2: eapply nth_val_nth_error;eauto.
  (* If (kport ′ ==ₑ 〈 OS_K_Port ∗ 〉 NULL) { .. };ₛ *)
  hoare forward.
  destruct p;pauto.
  { instantiate (1:= Afalse). pure intro. exfalso. destruct p. pauto. }
  hoare forward.
  pure intro. clear H25.
  (* channel ′ =ₑ kport ′ .. channel;ₛ *)
  hoare name lift kportNode_P pre.
  eapply backward_rule1.
  { eapply kportNode_P_getsome_frm;eauto. }
  pure intro.
  rename v'21 into kportvl1. rename v'22 into kportvl2. rename v'19 into kp_b.
  rename v'23 into kportl1.  rename v'24 into kportl2.
  remember (Vint32 i :: Vint32 i2 :: Vptr p_v :: x1 :: V$ DNUM :: Vint32 i0 :: x4 :: nil)  as kport.
  eapply seq_rule.
  hoare name lift (Alvarmapsto channel) pre.
  hoare name lift Aop pre.
  eapply assign_rule_lvar;[ 
  intro s; split; intro Hs; exact Hs|
  symbolic_exe_port| apply assign_type_match_true; simpl; auto | li_sepauto li ].
  (* merge kportNode *)
  hoare name lift (kportNode_P kportvl2 kportl2) pre.
  hoare name lift (Astruct' (kp_b, Int.zero) OS_K_Port_Seg_dls) pre.
  hoare name lift (kportNode_P kportvl1 kportl1) pre.
  eapply backward_rule1.
  intros.
  eapply kportNode_P_compose;eauto.
  lia.
  pauto.
  hoare name lift OSKernelPortIDTbl pre.
  hoare remember (1::2::nil)%nat pre.
  eapply backward_rule1.
  instantiate (1:= AOSKernelPortIDTbl (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)  (kportl1 ++
  kport :: kportl2) ** H24).
  unfold AOSKernelPortIDTbl.
  intros.
  sep normal.
  sep pauto.
  subst H24.
  (* If (channel ′ ==ₑ 〈 OS_Channel ∗ 〉 NULL) *)
  rewrite Heqkport at 1.
  cbn [nth_val'].
  eapply RLH_Kernelport_abs_getsome in H7 as ?;eauto.
  2: lia.
  destruct H24 as (kporth & ? & ?).
  hoare forward. 
  { destruct H32 as [ | [[? ?] ?] ];subst x1;auto. }
  { destruct H32 as [ | [[? ?] ?] ];subst x1;auto. }
  { (* condition true *)
    instantiate (1:= Afalse).
    pure intro. clear H40 H41.
    destruct H32 as [ | [[? ?] ?] ];subst x1.
    2: { simpl in H36. tryfalse. }
    destruct kporth as [[[[kpid pdp] pch] kpcn] kpst].
    assert (kpid = ∘ (Int.unsigned i) /\ pdp = Some p_v /\ pch = None /\ kpcn = Z.to_nat DNUM) as (? & ? & ? & ?).
    { destruct H24 as [? [? ?]].
      unfold Kernelport_nat_P, Kernelport_dmport_P,Kernelport_channel_P, OS_K_Port_V_coreNum, OS_K_Port_V_portID,OS_K_Port_V_dmport in *.
      partition_destruct H24.
      destruct pdp, pch;tryfalse.
      cbn in H24, H32, H42.
      inverts H24. inverts H32. inverts H42. subst.
      splits;auto.
      clear. pose proof dnum_range. mauto. }
    subst kpid pdp pch kpcn.
    hoare name lift oskportid pre.
    partition_absrulestac portpend_err_nochannel_end. 
    (* EXIT_CRITICAL;ₛ *)
    partition_exit_trinv.
    { unfold dmportp_sll. sep autocancel.
    exact H32. }
    go.
    hoare forward. }
  hoare forward.
  pure intro.
  destruct H32 as [ | [[? ?] ?] ];subst x1.
  { simpl in H36. destruct H36; tryfalse. }
  clear H39 H36.
  hoare abscsq;[apply noabs_oslinv | | ].
  eapply absinfer_trans.
  eapply absinfer_choice2;[ | | intros s Hs; exact Hs]. 1,2: go.
  eapply absinfer_trans.
  eapply absinfer_choice2;[ | | intros s Hs; exact Hs]. 1,2: go.
  eapply absinfer_trans.
  eapply absinfer_choice2;[ | | intros s Hs; exact Hs]. 1,2: go.
  eapply absinfer_trans.
  eapply absinfer_choice2;[ | | intros s Hs; exact Hs]. 1,2: go.
  eapply absinfer_choice2;[ | | intros s Hs; exact Hs]. 1,2: go.
  destruct kporth as [[[[kpid pdp] pch] kpcn] kpst].
  assert (kpid = ∘ (Int.unsigned i) /\ pdp = Some p_v /\ pch = Some (b, i1) /\ kpcn = Z.to_nat DNUM) as (? & ? & ? & ?).
  { destruct H24 as [? [? ?]].
    unfold Kernelport_nat_P, Kernelport_dmport_P,Kernelport_channel_P, OS_K_Port_V_coreNum, OS_K_Port_V_portID,OS_K_Port_V_dmport in *.
    partition_destruct H24.
    destruct pdp, pch;tryfalse.
    cbn in H24, H32, H36, H40.
    inverts H24. inverts H32. inverts H36. inverts H40. subst.
    splits;auto.
    clear. pose proof dnum_range. mauto. }
  subst kpid pdp pch kpcn.
  (* semaphore ′ =ₑ channel ′ .. semaphore;ₛ *)
  eapply R_KernelPortIDTbl_ChannelIDTbl_abs_getsome with (chanptr := (b, i1)) in H10 as ?;eauto.
  2: lia.
  unfold R_KernelPortIDTbl_ChannelIDTbl_chan_Vptr in H32.
  destruct H32 as (chanid & chanptr & chan & dstportl & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? ).
  unfold OS_K_Port_V_channelID, OS_K_Port_V_channel in *.
  cbn [nth_val ] in *.
  inverts H32. inverts H36.
  unfold AOSChannelIDTbl.
  pure intro.
  hoare name lift ChannelNode pre.
  eapply backward_rule1.
  eapply ChannelNode_getsome_frm; eauto.
  unfold node; hoare normal pre; pure intro.
  rename v'19 into chanvl1. rename v'23 into chanvl2.
  remember (v'28, Int.zero) as chanptr.
  rename v'21 into chanl1. rename v'24 into chanl2.
  rename v'22 into chandstportll1. rename v'25 into chandstportll2. 
  remember (Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: x7 :: x8 :: x9 :: x10 :: nil)  as chan.
  hoare forward.
  { cbn. pauto. }
  (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE){ .. };ₛ *)
  eapply RLH_Channel_app_cons in H8 as ?;eauto.
  destruct H46 as [chanh [? ?]].
  destruct (chanh) as [[[cid cdn] cdstkp] ct].
  hoare name lift resource_get_res pre.
  hoare remember (1:: 2:: nil)%nat pre.
  hoare forward.
  { pauto. }
  { pauto. }
  { pauto. }
  { (* condition true :  semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE *)
    instantiate (1:=Afalse \\// 
      EX csem, [| ct = (OutcoreC csem) |] **
      [| Int.eq i2 ($ DEFAULT_CHANNLE_SEMAPHROE) = false |] ** 
      <|| qportpend_notnil (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|);; Semrelease (Vint32 ($ Z.of_nat csem)) ;; END (Some (Vint32 (Int.repr OS_NO_ERR))) ?? 
      qportpend_nil (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|);; Semrelease (Vint32 ($ Z.of_nat csem));;
      (qportpend_idle_err
      (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|)
      ?? qportpend_not_ready_err
         (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|)
         ?? qportpend_block
            (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|);;
            isched;; ASSERT (port_indomainport (Vptr p_v)) ;; qportpend_after_sched (|Vptr p_v::nil|);;
            ( (spec_code_cons (portpend_accwithoutcheck (Vptr p_v :: Vptr msg_p :: (Vint32 ($ Z.of_nat csem)) ::  errv ::nil)) 
            (qportpend_block_get (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|) ;; END Some (errv)))
             ?? qportpend_block_timeout (|Vptr p_v
                  :: Vint32 tm_v :: Vptr msg_p :: nil|))) ||> **
             LV resource_get_res @ char_t |-> (V$ 1) ** H61 ).
    pure intro.
    assert (Int.eq i2 ($ DEFAULT_CHANNLE_SEMAPHROE) = false) by pauto.
    clear H62 H63 H64.
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_choice1;[ | | intros s Hs; exact Hs]. 1,2: go.
    destruct ct as [ | csem ].
    { exfalso. destruct H46 as [? [? ?]]. unfold Channel_type_P, OS_Channel_V_semaphore in *.
      cbn in H62. simpljoin1. inversion H62. subst i2. tryfalse. }
    assert (i2 = $ (Z.of_nat csem)).
    { destruct H46 as [? [? ?]]. unfold Channel_type_P, OS_Channel_V_semaphore in *.
    cbn in H62. simpljoin1. inversion H62.  auto. }
    subst i2.
    remember (v'28, Int.zero) as chanptr.
    assert (v <> Vint32 ($ Z.of_nat csem) \/ v = Vint32 ($ Z.of_nat csem)) as [ | ] by tauto.
    { hoare name lift oschannelid pre.
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare abscsq;[apply noabs_oslinv | | ].
      eapply corecommu_sem_abt;eauto.
      go. (* can change aop*)
      apply absabort_rule. }
    subst v.
    hoare name lift oschannelid pre.
    hoare name lift oskportid pre.
    partition_absrulestac corecommu_sem_cont.
    (* CSLSEMACC (semaphore ′, resource_get_res ′);ₛ *)
    unfold Semacc_err, Semacc_succ. 
    hoare name lift resource_get_res pre.
    hoare remember (2:: 1:: nil)%nat pre.
    eapply seq_rule.
    { eapply cslsemacc_rule'.
    { subst. can_change_aop_solver'.  }
    { rewrite Z2Nat.id. 1,2: eapply Int.unsigned_range_2. }
    { subst H62. 
      rewrite Z2Nat.id by (apply Int.unsigned_range).
      rewrite Int.repr_unsigned.
      symbolic execution.
      pauto. }
    { intros s Hs. subst. unfold p_local in Hs. unfold CurLINV. sep auto. }
    { intros s Hs. subst. unfold p_local in Hs. unfold CurLINV. sep auto. } }
    hoare forward.
    { (* resource = 0 *)
      subst H62.
      (* If (resource_get_res ′ ==ₑ 〈 char_t 〉 ′ 0) { .. } *)
      hoare forward.
      partition_exit_trinv.
      { unfold dmportp_sll. sep autocancel.
      unfold  AOSChannelIDTbl.
      sep normal. sep pauto. 
      sep lifts (4::3::5::6::nil)%nat in H62.
      eapply ChannelNode_compose in H62;[ | eauto..].
      exact H62.
      1,2: lia.
      go.  }
      go.
      instantiate (1:= Afalse).
      hoare forward.
      left.
      destruct H62.
      sep auto.
      exfalso. sep split in H62.
      clear -H63.
      destruct H63; mauto. }
    { (* resource ≠ 0 *)
      subst H62.
      (* If (resource_get_res ′ ==ₑ 〈 char_t 〉 ′ 0) { .. } *)
      hoare forward.
      { instantiate (1:= Afalse).
      pure intro.
      exfalso.
      clear -H62.
      pauto. }
      destruct H62.
      left;sep auto.
      right.
      unfold portpend_accwithoutcheck, Semacc_err, Semacc_succ.
      cbn [spec_code_cons].
      sep auto. }
  }
  hoare forward.
  -  (* 核间通信*)
    pure intro.
    clear H62 H63 H64.
    hoare forward.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              
    pure intro.
    rename v'19 into csem.
    rename H62 into H61.
    (* merge ChannelNode *)
    hoare name lift (Channel_dstkport_get) pre.
    hoare name lift (ChannelNode chanvl2 chanl2) pre.
    hoare name lift (Astruct (v'28, Int.zero) OS_Channel) pre.
    hoare name lift (ChannelNode chanvl1 chanl1) pre.
    eapply backward_rule1.
    intros.
    eapply ChannelNode_compose;eauto.
    1,2: lia.
    pauto.
    hoare name lift OSChannelIDTbl pre.
    hoare remember (1::2::nil)%nat pre.
    eapply backward_rule1.
    instantiate (1:= AOSChannelIDTbl (chanvl1 ++ Vptr (v'28, Int.zero) :: chanvl2)  (chanl1 ++
    (Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: x7 :: x8 :: x9 :: x10 :: nil) :: chanl2) (chandstportll1 ++ dstportl :: chandstportll2) ** H62).
    unfold AOSChannelIDTbl.
    intros.
    sep normal. sep pauto.
    subst H62.
    (* If (port_ptr ′ .. OSQEntries >ₑ ′ 0) *)
    hoare name lift OS_Port_V_mode pre.
    assert (pq = msgl /\ OS_Port_V_mode dport = Some (Vint32 (ZToInt QUEUE)) /\ 
    OS_Port_V_OSQSize dport = Some (Vint32 ($ (Z.of_nat sz)))) as [? [? ?]].
    { destruct H17 as [_ [_ ?]]. simpl in H17. tauto. }
    subst pq.
    eapply backward_rule1.
    eapply disj_star_elim_disj.
    hoare forward.
    { pure intro. exfalso. rewrite H62 in H63. clear -H63. mauto.  }
    pure intro.
    rename v'22 into qout; rename v'21 into qin; rename v'20 into qstart; rename v'19 into qend; rename v'24 into qentries.
    rewrite H64 in *.
    inversion H68;subst v'23.
    (* If (port_ptr ′ .. OSQEntries >ₑ ′ 0) *)
    eapply seq_rule.
    eapply ift_rule'';[ symbolic_exe_port | ].
    { (* branch QEntries > 0 *)
      instantiate (1:= Afalse).
      pure intro.
      assert (Int.ltu ($ 0) qentries = true) by pauto.
      clear H73 H74 H75.
      assert (∘ (Int.unsigned qentries) > 0)%nat.
      { clear - H68. 
        rewrite <- (Int.repr_unsigned qentries) in H68.
        simpl_intltbool.
        erewrite Int.unsigned_repr in H68 by (apply Int.unsigned_range_2).
        rewrite <- Zabs2Nat.abs_nat_nonneg by lia. lia. }
      hoare abscsq;[apply noabs_oslinv | | ].
      eapply absinfer_choice1;[ | | intros s Hs;exact Hs].
      1,2: go.
      hoare name lift dmportp_sllseg_qport_msg pre.
      eapply backward_rule1.
      eapply dmportp_sllseg_qport_msg_ngt0;eauto.
      pure intro.
      rename x5 into msg. rename x6 into msgl.
      (* msg_ptr ′ .. len =ₑ (port_ptr ′ .. OSQOut) .. len;ₛ *)
      unfold TmrInv, HeapInv'.
      pure intro.
      hoare name lift oscoreheapid pre.
      rename v'19 into cHeapl.
      assert (~ In_heapl_addrval cHeapl msg_p (S (length msg)) \/ In_heapl_addrval cHeapl msg_p (S (length msg))) as [ | ] by tauto.
      { hoare name lift oschannelid pre.
        hoare name lift oskportid pre.
        hoare name lift osdomainportid pre.
        hoare abscsq;[apply noabs_oslinv | | ].
        eapply qportpend_notnil_abt;eauto.
        go.
        apply absabort_rule. }
      hoare name lift AOScoreheapl pre.
      eapply backward_rule1.
      eapply In_heapl_addrval_split;eauto.
      pure intro.
      rename v'19 into cheapl1. rename v'22 into cheapl2.
      rename v'23 into ori_msgn. rename v'24 into ori_msg_vl. rename v'29 into ori_msg_vl2.
      rename v'25 into invalid_msg.
      eapply backward_rule1.
      eapply AOScoreheapl_length_frm with (n:= ori_msgn).
      { apply in_app. right. constructor. reflexivity. }
      pure intro.
      eapply backward_rule1.
      eapply split_coreheapl;eauto.
      pure intro.
      destruct ori_msg_vl as [ | ori_len_v ori_msg_vl ];[simpl in H80;lia | ].
      hoare name lift Aarray pre.
      unfold Aarray. cbn [Aarray'].
      destruct msg_p as [msg_b msg_i].
      hoare normal pre.
      hoare name lift msg_ptr pre.
      assert ((msg_b, msg_i) = get_off_addr (msg_b, msg_i) Int.zero).
      { unfold get_off_addr. cbn [fst snd]. rewrite Int.add_zero. reflexivity. }
      rewrite H82 at 2. clear H82.
      hoare name lift Aop pre.
      eapply seq_rule.
      eapply assign_rule_struct_member;[ | 
      clear;intros s'; split;[ intros Hs;exact Hs  |intros Hs;exact Hs ] | go | go | go 
      | idtac | idtac | symbolic_exe_port | idtac .. ].
      go. 
      { clear - H75. unfold CHANNEL_CACHE_SZIE in *. cbn.
        rewrite Int.unsigned_repr by mauto.
        assert (Z.of_nat (length msg) <=? 255 = true) by lia.
        rewrite H.
        auto. }
      apply eq_int;auto.
      { intros s Hs. subst. sep name lift p_local in Hs.  unfold CurLINV. sep auto. }
      hoare normal pre.
      hoare name lift dmportp_sllseg_qport_msg pre.
      destruct (∘ (Int.unsigned qentries)) as [ | pmsg_l] eqn :?;[ lia | ]. 
      cbn [dmportp_sllseg_qport_msg].
      pure intro.
      clear H83. rename H84 into H83. 
      (* memcpy (­msg_ptr ′ .. data, (port_ptr ′ .. OSQOut) .. data, (port_ptr ′ .. OSQOut) .. len­);ₛ *)
      eapply seq_rule. 
      eapply call_rule';[
      cbn;unfold OS_memcpy_spec;eauto | idtac .. ].
      { (* symbolic *)
        intros. 
        eapply rvl_elim.
        { eapply symbolic_lemmas.addrof_array_elem_rv.
        eapply struct_member_array_rv. symbolic_execution.
        unfold OSMsg_t. eauto.
        1,2,3: cbn;auto.
        sep_get_rv.
        1,2: eauto. }
        eapply rvl_elim;[sep_get_port_rv | ].
        eapply rvl_elim;[ | apply rvl_nil].
        eapply cast_rv_tint8_tint32. 
        sep_get_port_rv. split;[ | lia]. clear. destruct msg;lia. }
      { (* ==> pre*)
        intros;unfold_spec.
        sep normal. sep eexists.
        assert ((length msg) = (Z.to_nat (Int.unsigned ($  Z.of_nat (length msg))))).
        { rewrite Int.unsigned_repr. rewrite Nat2Z.id. auto.
          clear - H75. unfold CHANNEL_CACHE_SZIE in *. mauto. }
        rewrite H85 in H84 at 3.
        unfold Aarray at 1. sep cancel Aarray'.
        rewrite <- H82 in H84.
        apply Aarray_split in H84;auto.
        rewrite H85 in H84 at 1. sep cancel Aarray.
        sep name lift aemp_isr_is in H84. 
        sep name lift Ais in H84. sep name lift Aisr in H84.
        eapply elim_aemp_isr_is_prop in H84.
        sep autocancel. sep pauto.
        { destruct qout. unfold get_off_addr. cbn.
          rewrite ! Int.add_zero. 
          auto. }
        { rewrite H82. clear. unfold CHANNEL_CACHE_SZIE. rewrite Z2Nat.id by lia. mauto.   }
      }
      { (* goodfrm *)
        go. }
      {  sep_unfold_funpost. intros. sep destruct H83. sep auto. }
      {  sep_unfold_funpre. intros. sep destruct H83. sep auto. }
      { simpl;eauto. }
      unfold getasrt; unfold OS_memcopyPost, OS_memcopyPost'.
      hoare normal pre. pure intro.
      inversion H84. inversion H85. clear H85 H84. 
      subst v'23 v'24 v'25 v'29 v'30 v'31 v'34.
      clear v'22.
      rewrite ! Int.add_zero.
      (* merge coreheap *)
      hoare name lift AOScoreheapl pre.
      hoare name lift (Aarray (msg_b, msg_i +ᵢ  $ 1)) pre.
      hoare name lift (get_off_addr (msg_b, msg_i) Int.zero) pre.
      hoare remember (1::2::nil)%nat pre.
      rewrite Int.unsigned_repr.
      2: { clear - H75. unfold CHANNEL_CACHE_SZIE in *. mauto. }
      rewrite Nat2Z.id.
      eapply backward_rule1 with (p:= Aarray (msg_b, msg_i)
      (Tarray char_t (S (length msg))) (V$ (Z.of_nat (length msg))::msg) ** H84 ).
      { unfold Aarray, get_off_addr. 
        cbn [Aarray' snd fst]. intros.
        sep cancel H84.
        cbn [typelen].
        assert (Z.of_nat 1 = 1)%Z by lia.
        rewrite H87.
        rewrite Int.add_zero in H85.
        sep auto. }
      subst H84.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      
      eapply backward_rule1.
      eapply AOScoreheapl_merge;eauto.
      { rewrite <- H80. cbn. rewrite app_length. lia. }
      { rewrite app_length.  rewrite H80. lia. }
      { cbn. 
        assert (Int.unsigned ($ Z.of_nat (length msg)) <= 255).
        { clear - H82. unfold CHANNEL_CACHE_SZIE in *.  
          rewrite <- Zabs2Nat.abs_nat_nonneg in * by lia.
          assert (length msg <= 32)%nat by lia.
          clear - H.
          rewrite Int.unsigned_repr.
          lia.
          mauto. }
        assert (Int.unsigned ($ Z.of_nat (length msg)) <=? 255  = true) by lia.
        rewrite H85.
        split;auto.
        apply array_type_vallist_match_app in H83.
        tauto. }
      (* ++ port_ptr ′ .. OSQOut;ₛ *)
      destruct qout as (qoub & qoubi).
      cbn [fst snd].
      hoare name lift APortStruct pre.
      hoare name lift (Alvarmapsto port_ptr) pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      eapply port_memeber_asgn with (n := 15%nat);[reflexivity | symbolic_exe_port | idtac .. ].
      1,2,3,4,5,6,8: cbn;eauto.
      { eapply eq_vptr;eauto. }
      { intros. sep auto. }
      (* −− port_ptr ′ .. OSQEntries;ₛ *)
      remember ((update_nth_val 15 dport (Vptr (qoub, qoubi +ᵢ  Int.mul ($ 1) ($ 33))))) as dport'.
      assert (OS_Port_V_OSQEntries dport' = Some (Vint32 qentries)).
      { unfold OS_Port_V_OSQEntries in *. subst dport'. 
        eapply nth_upd_neqrev;eauto. }
      assert (struct_type_vallist_match' OS_Port_Seg_dls dport').
      { subst dport'. clear - H20.
        destruct dport; simpl in *; tryfalse.
        do 18 (destruct H20 as [? H20]; split; auto;
            destruct dport; simpl in *; tryfalse).  }
      assert (Int.unsigned (qentries -ᵢ $ 1) <=? 65535 = true) as Hqentries.
      { clear - H68 H71 H72. 
        assert (Int.unsigned (qentries -ᵢ ($ 1)) <= 65535).
        { rewrite Int_unsigned_minus. 
          rewrite Int.unsigned_repr by (clear;mauto).
          lia.   
          simpl_intltbool. 
          rewrite Int.unsigned_repr by (clear;mauto).
          lia. }
        lia. }
      eapply seq_rule.
      eapply port_memeber_asgn with (n := 17%nat);[reflexivity | symbolic_exe_port | idtac .. ].
      1,2,3,4,5,6: cbn;eauto.
      { apply eq_int;auto. }
      { cbn. 
        assert (Int.modu ($ 1) ($ Int16.modulus) = ($ 1)) by (clear;mauto).
        rewrite H87;clear H87.
        rewrite Hqentries. auto. }
      { intros. sep auto. }
      destruct qstart as (qstartb & qstarti).
      unfold Qport_msg_ptrs_P in H70.
      destruct H70 as [H70_ [H70_0 [z1 [z2 H70]]]].
      subst qstarti.
      unfold get_off_addr in H70, H70_0.
      cbn [fst snd] in *.
      destruct H70 as [? [? H70]].
      assert (Z.of_nat (typelen OSMsg_t) = 33).
      { clear. simpl. lia. }
      rewrite H89 in *;clear H89.
      inversion H87. subst qoub qoubi qend qin. clear H87.
      rewrite Int.add_zero_l in *.
      (* If (port_ptr ′ .. OSQOut ==ₑ port_ptr ′ .. OSQEnd) { ... } *)
      subst dport'. 
      assert (Int.modu ($ 1) ($ Int16.modulus) = ($ 1)) by (clear;mauto).
      rewrite H87;clear H87. 
      remember(update_nth_val 17 (update_nth_val 15 dport (Vptr (qstartb, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))))
                  (Vint32 (qentries -ᵢ $ 1)))  as dport'.
      assert (OS_Port_V_OSQOut dport' = Some (Vptr (qstartb, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)))).
      { unfold OS_Port_V_OSQOut in *. subst dport'. 
        eapply nth_upd_neqrev. lia. 
        eapply update_nth;eauto. }
      assert (OS_Port_V_OSQEnd dport' = Some (Vptr (qstartb, Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)))).
      { unfold OS_Port_V_OSQEnd in *. subst dport'. 
        eapply nth_upd_neqrev. lia. 
        eapply nth_upd_neqrev;eauto. }
      assert (struct_type_vallist_match' OS_Port_Seg_dls dport').
      { subst dport'. clear - H20 Hqentries.
        destruct dport; simpl in *; tryfalse.
        do 18 (destruct H20 as [? H20]; split; auto;
            destruct dport; simpl in *; tryfalse).
        cbn. rewrite Hqentries ;auto.  }
      hoare name lift APortStruct pre.
      hoare remember (1::nil)%nat pre.
      eapply seq_rule. 
      instantiate (1:= (EX qout_new, 
        [|Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)) 
        (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)) = true /\ qout_new =  (qstartb, Int.zero) \/ 
        Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)) 
        (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)) = false /\ qout_new = (qstartb, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)) |] ** 
        APortStruct p_v (update_nth_val 17 (update_nth_val 15 dport (Vptr qout_new)) (Vint32 (qentries -ᵢ $ 1))) ** H90)).
      { subst H90.
        eapply forward_rule2.
        eapply ift_rule'';[ symbolic_exe_port | ].
        { (* port_ptr ′ .. OSQOut ==ₑ port_ptr ′ .. OSQEnd *)
        pure intro.
        rewrite peq_true in H90.
        assert (Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
                      (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)) = true) by pauto. 
        clear H90 H91 H92.
        remember (update_nth_val 17 (update_nth_val 15 dport (Vptr (qstartb, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))))
                  (Vint32 (qentries -ᵢ $ 1)))  as dport'.
        assert (OS_Port_V_OSQStart dport' = Some (Vptr (qstartb, Int.zero))).
        { unfold OS_Port_V_OSQStart in *. subst dport'. 
        eapply nth_upd_neqrev. lia. 
        eapply nth_upd_neqrev;eauto. }
        hoare name lift APortStruct pre.
        hoare name lift (Alvarmapsto port_ptr) pre.
        hoare name lift Aop pre.
        eapply port_memeber_asgn with (n := 15%nat);[reflexivity | symbolic_exe_port | idtac .. ].
        1,2,3,4,5,6,8: cbn;eauto.
        { eapply eq_vptr;eauto. }
        sep auto.
        }
        { intros.
          destruct H90. 
          { sep normal in H90. 
            exists (qstartb, Int.zero).
            sep auto.
            2: left; pauto.
            clear - H20 H90.
            destruct dport; simpl in H20; tryfalse.
            do 18 (destruct H20 as [? H20];
                destruct dport; simpl in H20; tryfalse).
            cbn [update_nth_val] in *.
            exact H90. } 
          sep normal in H90.
          exists (qstartb, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)).
          sep auto.
          right.
          destruct (Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
          (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33))).
          { exfalso. rewrite peq_true in H100. destruct H100; tryfalse.  }
          pauto. }
      } 
      subst H90.
      pure intro.
      rename v'22 into qout_new.
      (* abs step : qportpend_notnil *)
      hoare name lift oscoreheapid pre.
      hoare name lift oschannelid pre.
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare abscsq;[apply noabs_oslinv | | ].
      eapply qportpend_notnil_cont;eauto.
      go.
      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE){CSLSEMREL ( semaphore ′)};ₛ *)
      hoare name lift semaphore pre.
      hoare name lift Aop pre.
      assert (i2 = ($ (Z.of_nat csem)) /\ Int.unsigned ($ Z.of_nat csem) <= 255) as [? Hcsem].
      { unfold ChannelNode_P, Channel_type_P in *.
        destruct H46 as [_ [[? _] _] ].
        unfold OS_Channel_V_semaphore in H46.
        cbn in H46. 
        inverts H46. tauto. }
      subst i2.
      hoare forward.
      { pauto. }
      { rewrite H61. pauto. }
      { rewrite H61. pauto. }
      { (* semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE *)
        pure intro.
        clear H94 H95 H96.
        unfold Semrelease.
        eapply cslsemrel_rule.
        go.
        { rewrite Z2Nat.id. apply Int.unsigned_range_2. apply Int.unsigned_range_2. }
        { rewrite Z2Nat.id by (apply Int.unsigned_range_2).  
          rewrite ! Int.repr_unsigned.
          symbolic_execution.
          clear - Hcsem. 
          pauto. }
        unfold CurLINV.  intros.
        sep name lift p_local in H94.
        unfold p_local in H94.
        sep auto. }
      hoare forward.
      2: {  pure intro.
            assert (Int.eq ($ Z.of_nat csem) ($ DEFAULT_CHANNLE_SEMAPHROE) = true).
            { destruct (Int.eq ($ Z.of_nat csem) ($ DEFAULT_CHANNLE_SEMAPHROE)).
             auto.
             destruct H94;tryfalse. }
            exfalso. 
            clear - H46 H95.
            unfold ChannelNode_P, Channel_type_P in *.
            destruct H46 as [_ [[? [? [? _]]] _]].
            congruence. }
      pure intro.
      clear H94 H95 H96.
      (* EXIT_CRITICAL;ₛ *)
      hoare name lift Aier pre; hoare name lift Ais pre; hoare name lift Aisr pre.
      eapply backward_rule1.
      eapply add_aemp_isr_is_prop.
      apply nth_error_split in H16 as [? [? [? ?]]]. subst dpptrl.
      hoare forward prim.
      { unfold get_off_addr in *;cbn [fst snd] in *.
        sep name lift Aisr in H94.
        sep autocancel.
        assert (OS_Port_V_portID (update_nth_val 17 (update_nth_val 15 dport (Vptr qout_new)) (Vint32 (qentries -ᵢ $ 1))) = OS_Port_V_portID dport). {
          unfold OS_Port_V_portID. do 2 (erewrite nth_upd_neqrev; eauto).  }
        assert (OS_Port_V_coreNum (update_nth_val 17 (update_nth_val 15 dport (Vptr qout_new)) (Vint32 (qentries -ᵢ $ 1))) = OS_Port_V_coreNum dport). {  
          unfold OS_Port_V_coreNum. do 2 (erewrite nth_upd_neqrev; eauto). }
        unfold TmrInv, HeapInv'.
        sep normal. sep eexists. sep autocancel.
        sep split;auto.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1, AOSDomainPortPtrList.
        sep normal. sep eexists.
        sep name lift AOSCorePortPtrList in H16.
        eapply AOSCorePortPtrList_update_dportls_frm with (pin := pintick) (tm:= poutick) (msg:= (QueuePort sz msgl)) in H16.
        2: eauto.
        sep autocancel.
        sep split;auto. 
        instantiate (3:= (dportl1 ++ ((update_nth_val 17 (update_nth_val 15 dport (Vptr qout_new)) (Vint32 (qentries -ᵢ $ 1))) :: dportl2))).
        instantiate (2:= (dportmsgll1 ++ msgl:: dportmsgll2)).
        2: eauto.
        3: { eapply R_Kernelport_DomainPort_upd;eauto. } 
        2: { eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1 with (dstportp := p_v) (pin:= pintick) (tm:= poutick) (msg:= QueuePort sz msgl);eauto. }  
        assert (pmsg_l = ∘ ((Int.unsigned (qentries -ᵢ $ 1)))).
        { eapply eq_add_S. rewrite <- Heqn.
          clear - H68 H71 H72.
          pose proof Int.unsigned_range_2 (qentries -ᵢ $ 1).
          assert (S (Z.to_nat (Int.unsigned (qentries -ᵢ $ 1))) = (Z.to_nat (Int.unsigned (qentries -ᵢ $ 1) + 1))) by lia.
          unfold nat_of_Z.
          rewrite H0;clear H0.
          rewrite Int_unsigned_minus.
          rewrite Int.unsigned_repr.
          lia.
          clear;mauto.
          rewrite Int.unsigned_repr by (clear;mauto).
          simpl_intltbool. lia. }
        assert (0 < Int.unsigned ($ Z.of_nat sz)) as Hszgt0.
        { clear - H68 H71.  simpl_intltbool. lia. }
        assert (0 <=  z1 <= Int.max_unsigned) as Hz1range.
        { clear - H70 H72 H93.  unfold Int.max_unsigned, Int.modulus, Int.wordsize; cbn. lia.  }
        assert (0 <=  1 <= Int.max_unsigned) as H1range.
        { unfold Int.max_unsigned, Int.modulus, Int.wordsize; cbn. lia. }
        unfold dmportp_sll.
        eapply dmportp_sllseg_app'_frm;eauto.
        { instantiate (2:= (x5 ++ p_v :: x6)). instantiate (1:= p_v).
          rewrite <- H94. apply nth_error_middle. }
        { eapply RL_PortPtrList_upd;eauto.
          unfold OS_Port_V_nextPort. do 2 (erewrite nth_upd_neqrev; eauto). }
        assert (OS_Port_V_OSQStart (update_nth_val 17 (update_nth_val 15 dport (Vptr qout_new)) (Vint32 (qentries -ᵢ $ 1))) = Some (Vptr (qstartb, Int.zero))).
        { unfold OS_Port_V_OSQStart. do 2 (erewrite nth_upd_neqrev; eauto). }
        cbn [dmportp_sllseg]. 
        sep normal. sep eexists.
        sep name lift (OS_Port_V_mode).
        eapply disj_split.
        right.
        rewrite H97 in H16.
        sep normal. sep eexists.
        sep autocancel.
        assert (qout_new = (dmportp_sllseg_qport_msg_next (qstartb, Int.mul ($ z1) ($ 33)) (qstartb, Int.zero) (qstartb, Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)))) as Hqout_new.
        { unfold dmportp_sllseg_qport_msg_next, msg_distance. cbn [snd].
          assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear;mauto).
          rewrite H99 in *.
          destruct H90 as [[? ?] | [? ?]].
          - rewrite Int_eq_dec in H90. rewrite <- H90.
            rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. 
            rewrite (Int.mul_commut ($ 1)).
            rewrite Int.mul_one.
            assert ((Int.divu ($ 33) ($ 33)) = Int.one)  by (clear;mauto).
            rewrite H101.
            subst qout_new.
            clear.
            unfold Int.one. rewrite (Int.unsigned_repr 1) by mauto.
            assert (1 =? 1 = true) by lia. rewrite H.
            reflexivity. 
          - subst qout_new. clear - H70 H72 H90 H93 Hz1range H1range.
            destruct (Int.unsigned (Int.divu (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33) -ᵢ Int.mul ($ z1) ($ 33)) ($ 33)) =? 1) eqn:?.
            2: { rewrite (Int.mul_commut ($ 1)).  rewrite Int.mul_one. reflexivity. }
            exfalso.
            assert (exists n,  Int.unsigned ($ Z.of_nat sz) = n + z1 /\ 1 <= n <= 65536).
            { exists (Int.unsigned ($ Z.of_nat sz) - (z1)). split;lia. }
            destruct H as [n [H0 H1]].
            rewrite H0 in Heqb.
            assert (z1 <= 65536) by lia. 
            erewrite  <- (Int.unsigned_repr n) in Heqb at 1.
            rewrite  <- (Int.unsigned_repr z1) in Heqb at 1.  
            rewrite  <- Int.add_unsigned in Heqb.
            rewrite Int.mul_add_distr_l in Heqb.
            rewrite Int.add_commut in Heqb.
            rewrite Int.sub_add_l in Heqb. rewrite Int.sub_idem in Heqb.  rewrite Int.add_zero_l in Heqb.
            assert ((Int.divu (Int.mul ($ n) ($ 33)) ($ 33)) = $ n).
            { erewrite Int.Int_mul_divu_r;auto. clear. rewrite Int.unsigned_repr by mauto. lia.
              rewrite Int.unsigned_repr. 
              rewrite Int.unsigned_repr.  
              assert (n * 33 <= 2162688) by lia. 
              assert (2162688 < Int.modulus) by (clear;mauto). lia.
              clear;mauto.
              clear - H1;unfold Int.max_unsigned, Int.modulus, Int.wordsize; cbn; lia.   }
            rewrite H2 in Heqb.
            rewrite Int.unsigned_repr in Heqb. assert (n = 1) by lia.
            subst n.
            rewrite H0 in H90.
            rewrite <- (Int.unsigned_repr 1) in H90 at 2.
            rewrite <- (Int.unsigned_repr z1) in H90 at 2.
            rewrite <- Int.add_unsigned in H90.
            rewrite Int.mul_add_distr_l in H90.
            rewrite (Int.add_commut (Int.mul ($ 1) ($ 33))) in H90. 
            rewrite Int.eq_true in H90. discriminate.
            all : auto.
            all : clear - H1;unfold Int.max_unsigned, Int.modulus, Int.wordsize; cbn; lia. }
        unfold OS_Port_V_OSQStart, OS_Port_V_nextPort, OS_Port_V_OSQSize, OS_Port_V_OSQIn, OS_Port_V_OSQEnd, OS_Port_V_mode.
        sep split;
        match  goal with
        | |- nth_val ?n (update_nth_val 17 (update_nth_val 15 _ _) _) = Some _ => do 2 (erewrite nth_upd_neqrev; eauto)
        | |- _ => auto 
        end.
        rewrite ! Int.add_zero_l in *.
        rewrite <- Hqout_new in *. 
        instantiate (5:= qout_new).
        sep cancel (dmportp_sllseg_qport_msg qout_new (qstartb, Int.mul ($ z2) ($ 33))).
        sep name lift dmportp_sllseg_qport_msg in H16.
        eapply dmportp_sllseg_qport_msg_length in H16.
        apply sep_pure_split in H16 as [? H16].
        instantiate (2:= (invalid_msg ++ (msg :: nil ))).
        instantiate (2:= ($ Z.of_nat sz)).
        assert ( ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned (qentries -ᵢ $ 1)) = ∘ (Int.unsigned ($ Z.of_nat sz) -
        Int.unsigned qentries) + 1)%nat.
        { rewrite Int_unsigned_minus.
          rewrite Z.sub_sub_distr.
          rewrite ( Int.unsigned_repr 1).
          unfold nat_of_Z.
          rewrite Z2Nat.inj_add.
          lia. lia. lia. clear. mauto. 
          clear -H68 H71.
          simpl_intltbool.
          rewrite Int.unsigned_repr by (clear;mauto).
          lia. }
        rewrite H100.
        eapply dmportp_sllseg_qport_msg_app_frm;eauto.
        assert 
        ((dmportp_msg_next_n ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned qentries)
        (qstartb, Int.mul ($ z2) ($ 33)) (qstartb, Int.zero)
        (qstartb, Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33))) = (qstartb, Int.mul ($ z1) ($ 33))).
        { eapply dmportp_sllseg_qport_msg_R_qout_qin in H16. sep split in H16. auto. }
        rewrite ! H101.
        cbn [dmportp_sllseg_qport_msg]. 
        sep normal. exists v'19.
        sep autocancel.
        sep split;auto.
        unfold get_off_addr. cbn [fst snd].
        rewrite <- H82.
        eapply Aarray_merge;eauto.
        { rewrite H82. unfold CHANNEL_CACHE_SZIE. clear. rewrite Z2Nat.id. mauto. lia. }
        rewrite Int.unsigned_repr in H16.
        rewrite Nat2Z.id in H16. 
        sep autocancel.
        exact H16.
        all: auto.
        { clear - H75. unfold CHANNEL_CACHE_SZIE in *. mauto. }
        { clear - H20 Hqentries.
          destruct dport; simpl in *; tryfalse.
          do 18 (destruct H20 as [? H20]; split; auto;
                destruct dport; simpl in *; tryfalse).
          cbn. rewrite Hqentries ;auto. }
        { unfold Qport_msg_ptrs_P, get_off_addr. cbn [fst snd].
          rewrite ! Int.add_zero_l.
          splits;auto.
          assert (Z.of_nat (typelen OSMsg_t) = 33).
          { clear. simpl. lia. }
          destruct H90 as [[? ?] | [? ?]];subst qout_new.
          - exists 0 z2. rewrite ! Int.add_zero_l. rewrite ! H99. rewrite (Int.mul_commut ($ 0)). rewrite Int.mul_zero. splits;auto.
            split;[lia | lia].
          - exists (z1 + 1) z2.  rewrite ! Int.add_zero_l. rewrite ! H99. 
            rewrite <- Int.mul_add_distr_l. rewrite Int.add_unsigned. 
            rewrite Int.unsigned_repr by auto. rewrite Int.unsigned_repr by auto.
            splits;auto.
            clear - H70 H72 H93 H90 Hz1range H1range.
            assert (z1 + 1 <> Int.unsigned ($ Z.of_nat sz)). 
            { unfold not; intros h; rewrite <- h in H90. 
              rewrite <- Int.mul_add_distr_l in H90. rewrite Int.add_unsigned in H90. 
              rewrite Int.unsigned_repr in H90 by auto. rewrite Int.unsigned_repr in H90 by auto. 
              rewrite Int.eq_true in H90. tryfalse. }
            lia. }
          { split.
            + unfold OS_Port_V_OSQEntries in *.  erewrite update_nth;eauto.  erewrite nth_upd_neqrev with (y:= Vint32 qentries);eauto.
            + clear - H71 H68 H1range.
              rewrite Int_unsigned_minus. 
              rewrite ( Int.unsigned_repr 1) by (auto).
              lia.
              simpl_intltbool.
              clear - H68 H1range.
              rewrite ( Int.unsigned_repr 1) by (auto).
              lia. }
          { split;auto.
            unfold OS_Port_V_OSQSize.  do 2 (erewrite nth_upd_neqrev; eauto).  }
          { unfold OS_Port_V_OSQOut in *.
            erewrite nth_upd_neqrev;eauto.
            eapply update_nth with (vi := (Vptr (qstartb, Int.mul ($ z1) ($ 33))));eauto. }
          { eapply RLH_Channel_upd_dportls1;eauto. right. do 4 eexists. eauto. }
          { unfold DomainportNode_P, Domainport_nat_P, Domainport_Portt_P in H17. partition_destruct H17. subst pintick poutick. 
            eapply RLH_Domainportl_upd_Queue;eauto.
            lia.
            unfold DomainportNode_P, Domainport_nat_P, Domainport_Portt_P.
            splits;auto.
            eexists.
            match goal with
            | Hrange : Int.unsigned ?port_id < PORT_NUMS |- _ => exists port_id
            end.
            do 3 eexists. splits; eauto. try (splits; eauto).
            all: unfold OS_Port_V_domain, OS_Port_V_status, OS_Port_V_msgInTick, OS_Port_V_msgOutTick, OS_Port_V_direction, OS_Port_V_OSEventPtrPort, OS_Port_V_mode, OS_Port_V_nextPort,OS_Port_V_OSQSize in *;
              try (do 2 (erewrite nth_upd_neqrev'; eauto)); eauto.
            all: eauto. }
          { unfold RLH_PortPtrINecb. split;auto.  eapply RL_PortPtrList_upd;eauto.
            unfold OS_Port_V_nextPort in *. do 2 (erewrite nth_upd_neqrev;eauto). }
          { eapply RL_PortAttr_upd;eauto. 
            unfold DomainportNode_P, Domainport_nat_P, Domainport_Portt_P in H17. partition_destruct H17.
            all: unfold OS_Port_V_direction, OS_Port_V_mode in *; do 2 (erewrite nth_upd_neqrev';eauto). }
          { eapply join_set_l;eauto. unfold indom. eexists. eauto. }
          { clear - H74. rewrite ! map_app in *. cbn in *.  auto.  }
          }
          auto.
          go.
          (* RETURN 〈 char_t 〉 ′ OS_NO_ERR *)
          hoare forward.
    }
    (* branch QEntries <= 0 *)
    hoare forward.
    pure intro.
    assert (Int.ltu ($ 0) qentries = false).
    { clear - H73. destruct (Int.ltu ($ 0) qentries);auto. destruct H73;tryfalse. }
    clear H73.
    assert (∘ (Int.unsigned qentries) = O). { simpl_intltbool. pose proof Int.unsigned_range_2 qentries. unfold nat_of_Z. lia.  }
    rewrite H73.
    destruct msgl.
    2: { cbn [dmportp_sllseg_qport_msg]. eapply backward_rule1. intros. eapply astar_l_afalse_elim;eauto. apply pfalse_rule.  }
    cbn [dmportp_sllseg_qport_msg].
    pure intro.
    partition_absrulestac qportpend_nil_cont.
    (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE) *)
    assert (i2 = ($ (Z.of_nat csem)) /\ Int.unsigned ($ Z.of_nat csem) <= 255) as [? Hcsem].
    { unfold ChannelNode_P, Channel_type_P in *.
      destruct H46 as [_ [[? _] _]].
      unfold OS_Channel_V_semaphore in H46.
      cbn in H46. 
      inverts H46. tauto. }
    subst i2.
    hoare forward;pauto.
    pure intro.
    clear H74 H75 H76.
    unfold Semrelease.
    eapply cslsemrel_rule.
    go.
    { rewrite Z2Nat.id. apply Int.unsigned_range_2. apply Int.unsigned_range_2. }
    { rewrite Z2Nat.id by (apply Int.unsigned_range_2).  
      rewrite ! Int.repr_unsigned.
      symbolic_execution.
      clear - Hcsem. 
      pauto. }
    unfold CurLINV.  intros.
    sep name lift p_local in H74.
    unfold p_local in H74.
    sep auto. 
    hoare forward.
    2: {  pure intro.
          assert (Int.eq ($ Z.of_nat csem) ($ DEFAULT_CHANNLE_SEMAPHROE) = true).
          { destruct (Int.eq ($ Z.of_nat csem) ($ DEFAULT_CHANNLE_SEMAPHROE)).
            auto.
            destruct H74;tryfalse. }
          exfalso. 
          clear - H46 H75.
          unfold ChannelNode_P, Channel_type_P in *.
          destruct H46 as [_ [[? [? [? _]]]_]].
          congruence. }
    pure intro.
    clear H74 H75 H76.
    hoare name lift A_dom_lenv pre.
    hoare name lift p_local pre.
    hoare name lift aemp_isr_is pre.
    hoare name lift A_isr_is_prop pre.
    hoare name lift Aier pre.
    hoare name lift Aisr pre.
    hoare name lift Acs pre.
    hoare name lift Ais pre.
    hoare name lift Aie pre.
    hoare name lift osdomainportid pre.
    hoare name lift curtid pre.
    hoare name lift abstcblsid pre.
    hoare name lift (Alvarmapsto port_ptr) pre.
    hoare name lift (Alvarmapsto timeout) pre.
    hoare name lift EvtInv pre.
    hoare name lift AOSRdyTblGrp pre.
    hoare name lift AOSTCBPrioTbl pre.
    hoare name lift AOSTCBList pre.
    hoare name lift Aop pre.
    unfold RH_CurTCB in H0. destruct H0 as [curpri [st [m [sus H0]]]].
    assert (exists wt, get ecbls p_v = Some (absport, wt)) as [wt Hportwt].
    { apply nth_error_split in H16 as [? [? [? ?]]]. subst dpptrl.
      apply Forall_app in Hinecb as [? ?].
      inversion H75. auto. }
    assert ((if Int.eq tm_v Int.zero then None else Some tm_v) = Some tm_v /\
    tm_v <> Int.zero \/
    (if Int.eq tm_v Int.zero then None else Some tm_v) = None /\ tm_v = Int.zero) as Htopt.
    { assert (tm_v = Int.zero \/ tm_v <> Int.zero) as [ | ] by tauto.
    right. subst. rewrite Int.eq_true. auto.
    left. rewrite Int.eq_false;auto. }
    eapply seq_rule.
    eapply qportpend_nilblock_part1;eauto.
    { go. }
    { go.  }
    naive pure intro.
    eapply seq_rule.
    (* OSTCBCur ′ .. OSTCBDly =ₑ timeout ′ *)
    assert (tid = (v'24, Int.zero)) by tauto. subst tid.
    eapply qportpend_nilblock_part2;eauto.
    { go. }
    { go. }
    (* OS_EventTaskWait (­ 〈 OS_EVENT ∗ 〉 port_ptr ′­);ₛ *)
    eapply seq_rule.
    assert (tid = (v'24, Int.zero)) by tauto. subst tid.
    eapply qportpend_nilblock_part3;eauto.
    { go. }
    { go. }
    (* EXIT_CRITICAL;ₛ *)
    naive pure intro.
    simpljoin1.
    hoare forward prim.
    sep autocancel.
    sep name lift CoreCommuInv in H74.
    eapply CoreCommuInv_set_notsemq_frm.
    { unfold is_sem, not. intros [? [? ?]].
      clear - H75 Hportwt.
      unfold tid in *.
      rewrite H75 in Hportwt. tryfalse. }
    { unfold is_que, not. intros [? [? [? [? ?]]]].
      clear - H75 Hportwt.
      unfold tid in *.
      rewrite H75 in Hportwt. tryfalse. }
    sep cancel CoreCommuInv.
    sep name lift tcbdllflag in H74.
    sep name lift tcbdllflag.
    eapply tcbdllflag_hold with (l1:= (v'2 ++ v'3 :: v'4));eauto.
    { eapply tcbdllflag_hold_middle. cbn [eq_dllflag].
      clear - H88. eapply struct_type_vallist_match_os_tcb_flag in H88.
      simpljoin1. unfold V_OSTCBflag, V_OSTCBNext; cbn [nth_val update_nth_val].
      split;auto. }
    sep cancel tcbdllflag.
    sep name lift PartitionInv; apply fold_PartitionInv_frm.
    sep cancel PartitionInv_part2.
    unfold PartitionInv_part1.
    sep normal. sep eexists. sep autocancel.
    unfold AOSDomainPortPtrList.
    sep normal. sep eexists.
    sep autocancel.
    sep pauto.
    eapply dmportp_sllseg_compose;eauto.
    sep name lift  (dmportp_sllseg dportlptr (Vptr p_v) dportl1
    dportmsgll1 OS_Port_V_nextPort) in H74.
    sep cancel dmportp_sllseg.
    sep cancel dmportp_sllseg.
    sep cancel APortStruct.
    eapply disj_split.
    right.
    sep normal.
    sep eexists.
    sep autocancel.
    instantiate (2:= v'25). instantiate (2:= qentries). instantiate (2:= ($ Z.of_nat sz)). instantiate (2:= qend).
    instantiate (2:= qin). instantiate (2:= qin). instantiate (2:= (@nil (list val))).
    rewrite H73.
    simpl (dmportp_sllseg_qport_msg qin qin qstart qend O nil).
    sep pauto.
    1,2,3,4,5, 7, 8:eauto.
    4: go.
    { (* RLH_PortPtrINecb *)
      split;auto.
      clear -Hinecb.
      eapply Forall_forall.
      intros.
      eapply Forall_forall in Hinecb;eauto.
      assert (x = p_v \/ x <> p_v) as [ | ] by tauto.
      subst. eexists. erewrite get_set_eq. eauto.
      destruct Hinecb. erewrite get_set_neq; eauto. }
    { (* RH_CurTCB *)
      unfold RH_CurTCB. do 4 eexists. erewrite get_set_eq. eauto. }
    { (* RH_TCBList_ECBList_P *)
      eapply partition_taskeventrules.RH_TCBList_ECBList_P_update_rdy2port;eauto. }
    (* end of critical region 
       sched ... *)
    clear - Hmode Hdir H2 H1 H61 Hcsem. rename v'29 into ier.
    remember ((v'24, Int.zero)) as ct. clear Heqct v'24.
    rename v'28 into cha_b. rename H61 into Hsem.
    (* OS_Sched (­);ₛ *)
    eapply seq_rule.
    eapply call_rule';[
      cbn;unfold OS_Sched_spec;eauto |  intros; 
      do 5 try (apply rvl_elim;[ symbolic_execution | ]);
       first [apply rvl_nil | simpl;auto] |  
       idtac..
      ].
    { (* PRE ==> *)
      intros. unfold_spec. sep normal. sep eexists. sep autocancel. sep pauto.
      unfold isflag. auto. }
    { go. }
    { sep_unfold_funpost.  intros. sep destruct H. sep eexists.  sep autocancel. sep auto. }
    { sep_unfold_funpre.  intros. sep destruct H. sep eexists.  sep autocancel. sep auto. }
    { go. }
    unfold getasrt; unfold OS_SchedPost, OS_SchedPost'.
    naive pure intro. inversion H. clear v' v'0 v'1 ier H H3 H4. rename v'2 into ier.
    eapply qportpend_nilblock_finalcriticalregion;eauto.
  - (* branch : Incore Communication *)
    hoare normal pre.
    naive pure intro.
    subst H61.
    assert (Int.eq i2 ($ DEFAULT_CHANNLE_SEMAPHROE) = true).
    { destruct  (Int.eq i2 ($ DEFAULT_CHANNLE_SEMAPHROE));auto.
      cbn in H62. destruct H62;tryfalse. }
    clear H62. 
    apply Int_eq_dec in H61 as ?. subst i2 chanptr chan.
    (* merge ChannelNode *)
    hoare name lift (Channel_dstkport_get) pre.
    hoare name lift (ChannelNode chanvl2 chanl2) pre.
    hoare name lift (Astruct (v'28, Int.zero) OS_Channel) pre.
    hoare name lift (ChannelNode chanvl1 chanl1) pre.
    eapply backward_rule1.
    intros.
    eapply ChannelNode_compose;eauto.
    1,2: lia.
    pauto. 
    hoare name lift OSChannelIDTbl pre.
    hoare remember (1::2::nil)%nat pre.
    eapply backward_rule1.
    instantiate (1:= AOSChannelIDTbl (chanvl1 ++ Vptr (v'28, Int.zero) :: chanvl2)  (chanl1 ++
    (Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: V$ DEFAULT_CHANNLE_SEMAPHROE :: x7 :: x8 :: x9 :: x10 :: nil) :: chanl2) (chandstportll1 ++ dstportl :: chandstportll2) ** H62).
    unfold AOSChannelIDTbl.
    intros.
    sep normal. sep pauto.
    subst H62.
    (* If (port_ptr ′ .. OSQEntries >ₑ ′ 0) *)
    hoare name lift OS_Port_V_mode pre.
    assert (pq = msgl /\ OS_Port_V_mode dport = Some (Vint32 (ZToInt QUEUE)) /\ 
    OS_Port_V_OSQSize dport = Some (Vint32 ($ (Z.of_nat sz)))) as [? [? ?]].
    { destruct H17 as [_ [_ ?]]. simpl in H17. tauto. }
    subst pq.
    eapply backward_rule1.
    eapply disj_star_elim_disj.
    hoare forward.
    { pure intro. exfalso. rewrite H62 in H63. clear -H63. mauto.  }
    pure intro.
    rename v'22 into qout; rename v'21 into qin; rename v'20 into qstart; rename v'19 into qend; rename v'24 into qentries.
    rewrite H64 in *.
    inversion H68;subst v'23.
    (* If (port_ptr ′ .. OSQEntries >ₑ ′ 0) *)
    eapply seq_rule.
    eapply ift_rule'';[ symbolic_exe_port | ].
    { (* branch QEntries > 0 *)
      instantiate (1:= Afalse).
      pure intro.
      assert (Int.ltu ($ 0) qentries = true) by pauto.
      clear H73 H74 H75.
      assert (∘ (Int.unsigned qentries) > 0)%nat.
      { clear - H68. 
        rewrite <- (Int.repr_unsigned qentries) in H68.
        simpl_intltbool.
        erewrite Int.unsigned_repr in H68 by (apply Int.unsigned_range_2).
        rewrite <- Zabs2Nat.abs_nat_nonneg by lia. lia. }
      hoare abscsq;[apply noabs_oslinv | | ].
      eapply absinfer_choice2;[ | | intros s Hs;exact Hs].
      1,2: go.
      hoare abscsq;[apply noabs_oslinv | | ].
      eapply absinfer_choice1;[ | | intros s Hs;exact Hs].
      1,2: go.
      hoare name lift dmportp_sllseg_qport_msg pre.
      eapply backward_rule1.
      eapply dmportp_sllseg_qport_msg_ngt0;eauto.
      pure intro.
      rename x5 into msg. rename x6 into msgl.
      (* msg_ptr ′ .. len =ₑ (port_ptr ′ .. OSQOut) .. len;ₛ *)
      unfold TmrInv, HeapInv'.
      pure intro.
      hoare name lift oscoreheapid pre.
      rename v'19 into cHeapl.
      assert (~ In_heapl_addrval cHeapl msg_p (S (length msg)) \/ In_heapl_addrval cHeapl msg_p (S (length msg))) as [ | ] by tauto.
      { hoare name lift oschannelid pre.
        hoare name lift oskportid pre.
        hoare name lift osdomainportid pre.
        hoare abscsq;[apply noabs_oslinv | | ].
        eapply qportpend_notnil_abt';eauto.
        go.
        apply absabort_rule. }
      hoare name lift AOScoreheapl pre.
      eapply backward_rule1.
      eapply In_heapl_addrval_split;eauto.
      pure intro.
      rename v'19 into cheapl1. rename v'22 into cheapl2.
      rename v'23 into ori_msgn. rename v'24 into ori_msg_vl. rename v'29 into ori_msg_vl2.
      rename v'25 into invalid_msg.
      eapply backward_rule1.
      eapply AOScoreheapl_length_frm with (n:= ori_msgn).
      { apply in_app. right. constructor. reflexivity. }
      pure intro.
      eapply backward_rule1.
      eapply split_coreheapl;eauto.
      pure intro.
      destruct ori_msg_vl as [ | ori_len_v ori_msg_vl ];[simpl in H80;lia | ].
      hoare name lift Aarray pre.
      unfold Aarray. cbn [Aarray'].
      destruct msg_p as [msg_b msg_i].
      hoare normal pre.
      hoare name lift msg_ptr pre.
      assert ((msg_b, msg_i) = get_off_addr (msg_b, msg_i) Int.zero).
      { unfold get_off_addr. cbn [fst snd]. rewrite Int.add_zero. reflexivity. }
      rewrite H82 at 2. clear H82.
      hoare name lift Aop pre.
      eapply seq_rule.
      eapply assign_rule_struct_member;[ | 
      clear;intros s'; split;[ intros Hs;exact Hs  |intros Hs;exact Hs ] | go | go | go 
      | idtac | idtac | symbolic_exe_port | idtac .. ].
      go. 
      { clear - H75. unfold CHANNEL_CACHE_SZIE in *. cbn.
        rewrite Int.unsigned_repr by mauto.
        assert (Z.of_nat (length msg) <=? 255 = true) by lia.
        rewrite H.
        auto. }
      apply eq_int;auto.
      { intros s Hs. subst. sep name lift p_local in Hs.  unfold CurLINV. sep auto. }
      hoare normal pre.
      hoare name lift dmportp_sllseg_qport_msg pre.
      destruct (∘ (Int.unsigned qentries)) as [ | pmsg_l] eqn :?;[ lia | ]. 
      cbn [dmportp_sllseg_qport_msg].
      pure intro.
      clear H83. rename H84 into H83. 
      (* memcpy (­msg_ptr ′ .. data, (port_ptr ′ .. OSQOut) .. data, (port_ptr ′ .. OSQOut) .. len­);ₛ *)
      eapply seq_rule. 
      eapply call_rule';[
      cbn;unfold OS_memcpy_spec;eauto | idtac .. ].
      { (* symbolic *)
        intros. 
        eapply rvl_elim.
        { eapply symbolic_lemmas.addrof_array_elem_rv.
        eapply struct_member_array_rv. symbolic_execution.
        unfold OSMsg_t. eauto.
        1,2,3: cbn;auto.
        sep_get_rv.
        1,2: eauto. }
        eapply rvl_elim;[sep_get_port_rv | ].
        eapply rvl_elim;[ | apply rvl_nil].
        eapply cast_rv_tint8_tint32. 
        sep_get_port_rv. split;[ | lia]. clear. destruct msg;lia. }
      { (* ==> pre*)
        intros;unfold_spec.
        sep normal. sep eexists.
        assert ((length msg) = (Z.to_nat (Int.unsigned ($  Z.of_nat (length msg))))).
        { rewrite Int.unsigned_repr. rewrite Nat2Z.id. auto.
          clear - H75. unfold CHANNEL_CACHE_SZIE in *. mauto. }
        rewrite H85 in H84 at 3.
        unfold Aarray at 1. sep cancel Aarray'.
        rewrite <- H82 in H84.
        apply Aarray_split in H84;auto.
        rewrite H85 in H84 at 1. sep cancel Aarray.
        sep name lift aemp_isr_is in H84. 
        sep name lift Ais in H84. sep name lift Aisr in H84.
        eapply elim_aemp_isr_is_prop in H84.
        sep autocancel. sep pauto.
        { destruct qout. unfold get_off_addr. cbn.
          rewrite ! Int.add_zero. 
          auto. }
        { rewrite H82. clear. unfold CHANNEL_CACHE_SZIE. rewrite Z2Nat.id by lia. mauto.   }
      }
      { (* goodfrm *)
        go. }
      {  sep_unfold_funpost. intros. sep destruct H83. sep auto. }
      {  sep_unfold_funpre. intros. sep destruct H83. sep auto. }
      { simpl;eauto. }
      unfold getasrt; unfold OS_memcopyPost, OS_memcopyPost'.
      hoare normal pre. pure intro.
      inversion H84. inversion H85. clear H85 H84. 
      subst v'23 v'24 v'25 v'29 v'30 v'31 v'34.
      clear v'22.
      rewrite ! Int.add_zero.
      (* merge coreheap *)
      hoare name lift AOScoreheapl pre.
      hoare name lift (Aarray (msg_b, msg_i +ᵢ  $ 1)) pre.
      hoare name lift (get_off_addr (msg_b, msg_i) Int.zero) pre.
      hoare remember (1::2::nil)%nat pre.
      rewrite Int.unsigned_repr.
      2: { clear - H75. unfold CHANNEL_CACHE_SZIE in *. mauto. }
      rewrite Nat2Z.id.
      eapply backward_rule1 with (p:= Aarray (msg_b, msg_i)
      (Tarray char_t (S (length msg))) (V$ (Z.of_nat (length msg))::msg) ** H84 ).
      { unfold Aarray, get_off_addr. 
        cbn [Aarray' snd fst]. intros.
        sep cancel H84.
        cbn [typelen].
        assert (Z.of_nat 1 = 1)%Z by lia.
        rewrite H87.
        rewrite Int.add_zero in H85.
        sep auto. }
      subst H84.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      
      eapply backward_rule1.
      eapply AOScoreheapl_merge;eauto.
      { rewrite <- H80. cbn. rewrite app_length. lia. }
      { rewrite app_length.  rewrite H80. lia. }
      { cbn. 
        assert (Int.unsigned ($ Z.of_nat (length msg)) <= 255).
        { clear - H82. unfold CHANNEL_CACHE_SZIE in *.  
          rewrite <- Zabs2Nat.abs_nat_nonneg in * by lia.
          assert (length msg <= 32)%nat by lia.
          clear - H.
          rewrite Int.unsigned_repr.
          lia.
          mauto. }
        assert (Int.unsigned ($ Z.of_nat (length msg)) <=? 255  = true) by lia.
        rewrite H85.
        split;auto.
        apply array_type_vallist_match_app in H83.
        tauto. }
      (* ++ port_ptr ′ .. OSQOut;ₛ *)
      destruct qout as (qoub & qoubi).
      cbn [fst snd].
      hoare name lift APortStruct pre.
      hoare name lift (Alvarmapsto port_ptr) pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      eapply port_memeber_asgn with (n := 15%nat);[reflexivity | symbolic_exe_port | idtac .. ].
      1,2,3,4,5,6,8: cbn;eauto.
      { eapply eq_vptr;eauto. }
      { intros. sep auto. }
      (* −− port_ptr ′ .. OSQEntries;ₛ *)
      remember ((update_nth_val 15 dport (Vptr (qoub, qoubi +ᵢ  Int.mul ($ 1) ($ 33))))) as dport'.
      assert (OS_Port_V_OSQEntries dport' = Some (Vint32 qentries)).
      { unfold OS_Port_V_OSQEntries in *. subst dport'. 
        eapply nth_upd_neqrev;eauto. }
      assert (struct_type_vallist_match' OS_Port_Seg_dls dport').
      { subst dport'. clear - H20.
        destruct dport; simpl in *; tryfalse.
        do 18 (destruct H20 as [? H20]; split; auto;
            destruct dport; simpl in *; tryfalse).  }
      assert (Int.unsigned (qentries -ᵢ $ 1) <=? 65535 = true) as Hqentries.
      { clear - H68 H71 H72. 
        assert (Int.unsigned (qentries -ᵢ ($ 1)) <= 65535).
        { rewrite Int_unsigned_minus. 
          rewrite Int.unsigned_repr by (clear;mauto).
          lia.   
          simpl_intltbool. 
          rewrite Int.unsigned_repr by (clear;mauto).
          lia. }
        lia. }
      eapply seq_rule.
      eapply port_memeber_asgn with (n := 17%nat);[reflexivity | symbolic_exe_port | idtac .. ].
      1,2,3,4,5,6: cbn;eauto.
      { apply eq_int;auto. }
      { cbn. 
        assert (Int.modu ($ 1) ($ Int16.modulus) = ($ 1)) by (clear;mauto).
        rewrite H87;clear H87.
        rewrite Hqentries. auto. }
      { intros. sep auto. }
      destruct qstart as (qstartb & qstarti).
      unfold Qport_msg_ptrs_P in H70.
      destruct H70 as [H70_ [H70_0 [z1 [z2 H70]]]].
      subst qstarti.
      unfold get_off_addr in H70, H70_0.
      cbn [fst snd] in *.
      destruct H70 as [? [? H70]].
      assert (Z.of_nat (typelen OSMsg_t) = 33).
      { clear. simpl. lia. }
      rewrite H89 in *;clear H89.
      inversion H87. subst qoub qoubi qend qin. clear H87.
      rewrite Int.add_zero_l in *.
      (* If (port_ptr ′ .. OSQOut ==ₑ port_ptr ′ .. OSQEnd) { ... } *)
      subst dport'. 
      assert (Int.modu ($ 1) ($ Int16.modulus) = ($ 1)) by (clear;mauto).
      rewrite H87;clear H87. 
      remember(update_nth_val 17 (update_nth_val 15 dport (Vptr (qstartb, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))))
                  (Vint32 (qentries -ᵢ $ 1)))  as dport'.
      assert (OS_Port_V_OSQOut dport' = Some (Vptr (qstartb, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)))).
      { unfold OS_Port_V_OSQOut in *. subst dport'. 
        eapply nth_upd_neqrev. lia. 
        eapply update_nth;eauto. }
      assert (OS_Port_V_OSQEnd dport' = Some (Vptr (qstartb, Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)))).
      { unfold OS_Port_V_OSQEnd in *. subst dport'. 
        eapply nth_upd_neqrev. lia. 
        eapply nth_upd_neqrev;eauto. }
      assert (struct_type_vallist_match' OS_Port_Seg_dls dport').
      { subst dport'. clear - H20 Hqentries.
        destruct dport; simpl in *; tryfalse.
        do 18 (destruct H20 as [? H20]; split; auto;
            destruct dport; simpl in *; tryfalse).
        cbn. rewrite Hqentries ;auto.  }
      hoare name lift APortStruct pre.
      hoare remember (1::nil)%nat pre.
      eapply seq_rule. 
      instantiate (1:= (EX qout_new, 
        [|Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)) 
        (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)) = true /\ qout_new =  (qstartb, Int.zero) \/ 
        Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)) 
        (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)) = false /\ qout_new = (qstartb, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)) |] ** 
        APortStruct p_v (update_nth_val 17 (update_nth_val 15 dport (Vptr qout_new)) (Vint32 (qentries -ᵢ $ 1))) ** H90)).
      { subst H90.
        eapply forward_rule2.
        eapply ift_rule'';[ symbolic_exe_port | ].
        { (* port_ptr ′ .. OSQOut ==ₑ port_ptr ′ .. OSQEnd *)
        pure intro.
        rewrite peq_true in H90.
        assert (Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
                      (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)) = true) by pauto. 
        clear H90 H91 H92.
        remember (update_nth_val 17 (update_nth_val 15 dport (Vptr (qstartb, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))))
                  (Vint32 (qentries -ᵢ $ 1)))  as dport'.
        assert (OS_Port_V_OSQStart dport' = Some (Vptr (qstartb, Int.zero))).
        { unfold OS_Port_V_OSQStart in *. subst dport'. 
        eapply nth_upd_neqrev. lia. 
        eapply nth_upd_neqrev;eauto. }
        hoare name lift APortStruct pre.
        hoare name lift (Alvarmapsto port_ptr) pre.
        hoare name lift Aop pre.
        eapply port_memeber_asgn with (n := 15%nat);[reflexivity | symbolic_exe_port | idtac .. ].
        1,2,3,4,5,6,8: cbn;eauto.
        { eapply eq_vptr;eauto. }
        sep auto.
        }
        { intros.
          destruct H90. 
          { sep normal in H90. 
            exists (qstartb, Int.zero).
            sep auto.
            2: left; pauto.
            clear - H20 H90.
            destruct dport; simpl in H20; tryfalse.
            do 18 (destruct H20 as [? H20];
                destruct dport; simpl in H20; tryfalse).
            cbn [update_nth_val] in *.
            exact H90. } 
          sep normal in H90.
          exists (qstartb, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)).
          sep auto.
          right.
          destruct (Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
          (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33))).
          { exfalso. rewrite peq_true in H100. destruct H100; tryfalse.  }
          pauto. }
      } 
      subst H90.
      pure intro.
      rename v'22 into qout_new.
      (* abs step : qportpend_notnil *)
      hoare name lift oscoreheapid pre.
      hoare name lift oschannelid pre.
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare abscsq;[apply noabs_oslinv | | ].
      eapply qportpend_notnil_cont';eauto.
      go.
      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE){CSLSEMREL ( semaphore ′)};ₛ *)
      hoare name lift semaphore pre.
      hoare name lift Aop pre.
      hoare forward.
      { (* semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE *)
        pure intro.
        instantiate (1:= Afalse).
        exfalso. clear - H94. pauto. }
      hoare forward.
      pure intro.
      clear H94.
      (* EXIT_CRITICAL;ₛ *)
      hoare name lift Aier pre; hoare name lift Ais pre; hoare name lift Aisr pre.
      eapply backward_rule1.
      eapply add_aemp_isr_is_prop.
      apply nth_error_split in H16 as [? [? [? ?]]]. subst dpptrl.
      hoare forward prim.
      { unfold get_off_addr in *;cbn [fst snd] in *.
        sep name lift Aisr in H94.
        sep autocancel.
        assert (OS_Port_V_portID (update_nth_val 17 (update_nth_val 15 dport (Vptr qout_new)) (Vint32 (qentries -ᵢ $ 1))) = OS_Port_V_portID dport). {
          unfold OS_Port_V_portID. do 2 (erewrite nth_upd_neqrev; eauto).  }
        assert (OS_Port_V_coreNum (update_nth_val 17 (update_nth_val 15 dport (Vptr qout_new)) (Vint32 (qentries -ᵢ $ 1))) = OS_Port_V_coreNum dport). {  
          unfold OS_Port_V_coreNum. do 2 (erewrite nth_upd_neqrev; eauto). }
        unfold TmrInv, HeapInv'.
        sep normal. sep eexists. sep autocancel.
        sep split;auto.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1, AOSDomainPortPtrList.
        sep normal. sep eexists. 
        sep name lift AOSCorePortPtrList in H16.
        eapply AOSCorePortPtrList_update_dportls_frm with (pin := pintick) (tm:= poutick) (msg:= (QueuePort sz msgl)) in H16.
        2: eauto.
        sep autocancel.
        sep split;auto. 
        instantiate (3:= (dportl1 ++ ((update_nth_val 17 (update_nth_val 15 dport (Vptr qout_new)) (Vint32 (qentries -ᵢ $ 1))) :: dportl2))).
        instantiate (2:= (dportmsgll1 ++ msgl:: dportmsgll2)).
        2: eauto.
        3: { eapply R_Kernelport_DomainPort_upd;eauto. } 
        2: { eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1 with (dstportp := p_v) (pin:= pintick) (tm:= poutick) (msg:= QueuePort sz msgl);eauto. }  
        assert (pmsg_l = ∘ ((Int.unsigned (qentries -ᵢ $ 1)))).
        { eapply eq_add_S. rewrite <- Heqn.
          clear - H68 H71 H72.
          pose proof Int.unsigned_range_2 (qentries -ᵢ $ 1).
          assert (S (Z.to_nat (Int.unsigned (qentries -ᵢ $ 1))) = (Z.to_nat (Int.unsigned (qentries -ᵢ $ 1) + 1))) by lia.
          unfold nat_of_Z.
          rewrite H0;clear H0.
          rewrite Int_unsigned_minus.
          rewrite Int.unsigned_repr.
          lia.
          clear;mauto.
          rewrite Int.unsigned_repr by (clear;mauto).
          simpl_intltbool. lia. }
        assert (0 < Int.unsigned ($ Z.of_nat sz)) as Hszgt0.
        { clear - H68 H71.  simpl_intltbool. lia. }
        assert (0 <=  z1 <= Int.max_unsigned) as Hz1range.
        { clear - H70 H72 H93.  unfold Int.max_unsigned, Int.modulus, Int.wordsize; cbn. lia.  }
        assert (0 <=  1 <= Int.max_unsigned) as H1range.
        { unfold Int.max_unsigned, Int.modulus, Int.wordsize; cbn. lia. }
        unfold dmportp_sll.
        eapply dmportp_sllseg_app'_frm;eauto.
        { instantiate (2:= (x5 ++ p_v :: x6)). instantiate (1:= p_v).
          rewrite <- H94. apply nth_error_middle. }
        { eapply RL_PortPtrList_upd;eauto.
          unfold OS_Port_V_nextPort. do 2 (erewrite nth_upd_neqrev; eauto). }
        assert (OS_Port_V_OSQStart (update_nth_val 17 (update_nth_val 15 dport (Vptr qout_new)) (Vint32 (qentries -ᵢ $ 1))) = Some (Vptr (qstartb, Int.zero))).
        { unfold OS_Port_V_OSQStart. do 2 (erewrite nth_upd_neqrev; eauto). }
        cbn [dmportp_sllseg]. 
        sep normal. sep eexists.
        sep name lift (OS_Port_V_mode).
        eapply disj_split.
        right.
        rewrite H97 in H16.
        sep normal. sep eexists.
        sep autocancel.
        assert (qout_new = (dmportp_sllseg_qport_msg_next (qstartb, Int.mul ($ z1) ($ 33)) (qstartb, Int.zero) (qstartb, Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)))) as Hqout_new.
        { unfold dmportp_sllseg_qport_msg_next, msg_distance. cbn [snd].
          assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear;mauto).
          rewrite H99 in *.
          destruct H90 as [[? ?] | [? ?]].
          - rewrite Int_eq_dec in H90. rewrite <- H90.
            rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. 
            rewrite (Int.mul_commut ($ 1)).
            rewrite Int.mul_one.
            assert ((Int.divu ($ 33) ($ 33)) = Int.one)  by (clear;mauto).
            rewrite H101.
            subst qout_new.
            clear.
            unfold Int.one. rewrite (Int.unsigned_repr 1) by mauto.
            assert (1 =? 1 = true) by lia. rewrite H.
            reflexivity. 
          - subst qout_new. clear - H70 H72 H90 H93 Hz1range H1range.
            destruct (Int.unsigned (Int.divu (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33) -ᵢ Int.mul ($ z1) ($ 33)) ($ 33)) =? 1) eqn:?.
            2: { rewrite (Int.mul_commut ($ 1)).  rewrite Int.mul_one. reflexivity. }
            exfalso.
            assert (exists n,  Int.unsigned ($ Z.of_nat sz) = n + z1 /\ 1 <= n <= 65536).
            { exists (Int.unsigned ($ Z.of_nat sz) - (z1)). split;lia. }
            destruct H as [n [H0 H1]].
            rewrite H0 in Heqb.
            assert (z1 <= 65536) by lia. 
            erewrite  <- (Int.unsigned_repr n) in Heqb at 1.
            rewrite  <- (Int.unsigned_repr z1) in Heqb at 1.  
            rewrite  <- Int.add_unsigned in Heqb.
            rewrite Int.mul_add_distr_l in Heqb.
            rewrite Int.add_commut in Heqb.
            rewrite Int.sub_add_l in Heqb. rewrite Int.sub_idem in Heqb.  rewrite Int.add_zero_l in Heqb.
            assert ((Int.divu (Int.mul ($ n) ($ 33)) ($ 33)) = $ n).
            { erewrite Int.Int_mul_divu_r;auto. clear. rewrite Int.unsigned_repr by mauto. lia.
              rewrite Int.unsigned_repr. 
              rewrite Int.unsigned_repr.  
              assert (n * 33 <= 2162688) by lia. 
              assert (2162688 < Int.modulus) by (clear;mauto). lia.
              clear;mauto.
              clear - H1;unfold Int.max_unsigned, Int.modulus, Int.wordsize; cbn; lia.   }
            rewrite H2 in Heqb.
            rewrite Int.unsigned_repr in Heqb. assert (n = 1) by lia.
            subst n.
            rewrite H0 in H90.
            rewrite <- (Int.unsigned_repr 1) in H90 at 2.
            rewrite <- (Int.unsigned_repr z1) in H90 at 2.
            rewrite <- Int.add_unsigned in H90.
            rewrite Int.mul_add_distr_l in H90.
            rewrite (Int.add_commut (Int.mul ($ 1) ($ 33))) in H90. 
            rewrite Int.eq_true in H90. discriminate.
            all : auto.
            all : clear - H1;unfold Int.max_unsigned, Int.modulus, Int.wordsize; cbn; lia. }
        unfold OS_Port_V_OSQStart, OS_Port_V_nextPort, OS_Port_V_OSQSize, OS_Port_V_OSQIn, OS_Port_V_OSQEnd, OS_Port_V_mode.
        sep split;
        match  goal with
        | |- nth_val ?n (update_nth_val 17 (update_nth_val 15 _ _) _) = Some _ => do 2 (erewrite nth_upd_neqrev'; eauto)
        | |- _ => auto 
        end.
        rewrite ! Int.add_zero_l in *.
        rewrite <- Hqout_new in *. 
        instantiate (5:= qout_new).
        sep cancel (dmportp_sllseg_qport_msg qout_new (qstartb, Int.mul ($ z2) ($ 33))).
        sep name lift dmportp_sllseg_qport_msg in H16.
        eapply dmportp_sllseg_qport_msg_length in H16.
        apply sep_pure_split in H16 as [? H16].
        instantiate (2:= (invalid_msg ++ (msg :: nil ))).
        instantiate (2:= ($ Z.of_nat sz)).
        assert ( ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned (qentries -ᵢ $ 1)) = ∘ (Int.unsigned ($ Z.of_nat sz) -
        Int.unsigned qentries) + 1)%nat.
        { rewrite Int_unsigned_minus.
          rewrite Z.sub_sub_distr.
          rewrite ( Int.unsigned_repr 1).
          unfold nat_of_Z.
          rewrite Z2Nat.inj_add.
          lia. lia. lia. clear. mauto. 
          clear -H68 H71.
          simpl_intltbool.
          rewrite Int.unsigned_repr by (clear;mauto).
          lia. }
        rewrite H100.
        eapply dmportp_sllseg_qport_msg_app_frm;eauto.
        assert 
        ((dmportp_msg_next_n ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned qentries)
        (qstartb, Int.mul ($ z2) ($ 33)) (qstartb, Int.zero)
        (qstartb, Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33))) = (qstartb, Int.mul ($ z1) ($ 33))).
        { eapply dmportp_sllseg_qport_msg_R_qout_qin in H16. sep split in H16. auto. }
        rewrite ! H101.
        cbn [dmportp_sllseg_qport_msg]. 
        sep normal. exists v'19.
        sep autocancel.
        sep split;auto.
        unfold get_off_addr. cbn [fst snd].
        rewrite <- H82.
        eapply Aarray_merge;eauto.
        { rewrite H82. unfold CHANNEL_CACHE_SZIE. clear. rewrite Z2Nat.id. mauto. lia. }
        rewrite Int.unsigned_repr in H16.
        rewrite Nat2Z.id in H16. 
        sep autocancel.
        exact H16.
        all: auto.
        { clear - H75. unfold CHANNEL_CACHE_SZIE in *. mauto. }
        { clear - H20 Hqentries.
          destruct dport; simpl in *; tryfalse.
          do 18 (destruct H20 as [? H20]; split; auto;
                destruct dport; simpl in *; tryfalse).
          cbn. rewrite Hqentries ;auto. }
        { unfold Qport_msg_ptrs_P, get_off_addr. cbn [fst snd].
          rewrite ! Int.add_zero_l.
          splits;auto.
          assert (Z.of_nat (typelen OSMsg_t) = 33).
          { clear. simpl. lia. }
          destruct H90 as [[? ?] | [? ?]];subst qout_new.
          - exists 0 z2. rewrite ! Int.add_zero_l. rewrite ! H99. rewrite (Int.mul_commut ($ 0)). rewrite Int.mul_zero. splits;auto.
          - exists (z1 + 1) z2.  rewrite ! Int.add_zero_l. rewrite ! H99. 
            rewrite <- Int.mul_add_distr_l. rewrite Int.add_unsigned. 
            rewrite Int.unsigned_repr by auto. rewrite Int.unsigned_repr by auto.
            splits;auto.
            clear - H70 H72 H93 H90 Hz1range H1range.
            assert (z1 + 1 <> Int.unsigned ($ Z.of_nat sz)). 
            { unfold not; intros h; rewrite <- h in H90. 
              rewrite <- Int.mul_add_distr_l in H90. rewrite Int.add_unsigned in H90. 
              rewrite Int.unsigned_repr in H90 by auto. rewrite Int.unsigned_repr in H90 by auto. 
              rewrite Int.eq_true in H90. tryfalse. }
            lia. }
          { split.
            + unfold OS_Port_V_OSQEntries in *.  erewrite update_nth;eauto.  erewrite nth_upd_neqrev with (y:= Vint32 qentries);eauto.
            + clear - H71 H68 H1range.
              rewrite Int_unsigned_minus. 
              rewrite ( Int.unsigned_repr 1) by (auto).
              lia.
              simpl_intltbool.
              clear - H68 H1range.
              rewrite ( Int.unsigned_repr 1) by (auto).
              lia. }
          { split;auto.
            unfold OS_Port_V_OSQSize.  do 2 (erewrite nth_upd_neqrev; eauto).  }
          { unfold OS_Port_V_OSQOut in *.
            erewrite nth_upd_neqrev;eauto.
            eapply update_nth with (vi := (Vptr (qstartb, Int.mul ($ z1) ($ 33))));eauto. }
          { eapply RLH_Channel_upd_dportls1;eauto. right. do 4 eexists. eauto. }
          { unfold DomainportNode_P, Domainport_nat_P, Domainport_Portt_P in H17. partition_destruct H17. subst pintick poutick. 
            eapply RLH_Domainportl_upd_Queue;eauto.
            lia.
            unfold DomainportNode_P, Domainport_nat_P, Domainport_Portt_P.
            splits;auto.
            eexists.
            match goal with
            | Hrange : Int.unsigned ?port_id < PORT_NUMS |- _ => exists port_id
            end.
            do 3 eexists. splits; eauto. try (splits; eauto).
            all: unfold OS_Port_V_domain, OS_Port_V_status, OS_Port_V_msgInTick, OS_Port_V_msgOutTick, OS_Port_V_direction, OS_Port_V_OSEventPtrPort, OS_Port_V_mode, OS_Port_V_nextPort,OS_Port_V_OSQSize in *;
              try (do 2 (erewrite nth_upd_neqrev'; eauto)); eauto.
            all: eauto. }
          { unfold RLH_PortPtrINecb. split;auto.  eapply RL_PortPtrList_upd;eauto.
            unfold OS_Port_V_nextPort in *. do 2 (erewrite nth_upd_neqrev;eauto). }
          { eapply RL_PortAttr_upd;eauto. 
            unfold DomainportNode_P, Domainport_nat_P, Domainport_Portt_P in H17. partition_destruct H17.
            all: unfold OS_Port_V_direction, OS_Port_V_mode in *; do 2 (erewrite nth_upd_neqrev';eauto). }
          { eapply join_set_l;eauto. unfold indom. eexists. eauto. }
          { clear - H74. rewrite ! map_app in *. cbn in *.  auto.  }
          }
          auto.
          go.
          (* RETURN 〈 char_t 〉 ′ OS_NO_ERR *)
          hoare forward.
    }
    (* branch QEntries <= 0 *)
    hoare forward.
    pure intro.
    assert (Int.ltu ($ 0) qentries = false).
    { clear - H73. destruct (Int.ltu ($ 0) qentries);auto. destruct H73;tryfalse. }
    clear H73.
    assert (∘ (Int.unsigned qentries) = O). { simpl_intltbool. pose proof Int.unsigned_range_2 qentries. unfold nat_of_Z. lia.  }
    rewrite H73.
    destruct msgl.
    2: { cbn [dmportp_sllseg_qport_msg]. eapply backward_rule1. intros. eapply astar_l_afalse_elim;eauto. apply pfalse_rule.  }
    cbn [dmportp_sllseg_qport_msg].
    pure intro.
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_choice2;[ | | intros s Hs;exact Hs].
    1,2: go.
    partition_absrulestac qportpend_nil_cont.
    (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE) *)
    hoare forward;pauto.
    { pure intro.
      instantiate (1:= Afalse).
      exfalso. clear - H74. pauto. }
    hoare forward.
    pure intro.
    clear H74.
    hoare name lift A_dom_lenv pre.
    hoare name lift p_local pre.
    hoare name lift aemp_isr_is pre.
    hoare name lift A_isr_is_prop pre.
    hoare name lift Aier pre.
    hoare name lift Aisr pre.
    hoare name lift Acs pre.
    hoare name lift Ais pre.
    hoare name lift Aie pre.
    hoare name lift osdomainportid pre.
    hoare name lift curtid pre.
    hoare name lift abstcblsid pre.
    hoare name lift (Alvarmapsto port_ptr) pre.
    hoare name lift (Alvarmapsto timeout) pre.
    hoare name lift EvtInv pre.
    hoare name lift AOSRdyTblGrp pre.
    hoare name lift AOSTCBPrioTbl pre.
    hoare name lift AOSTCBList pre.
    hoare name lift Aop pre.
    unfold RH_CurTCB in H0. destruct H0 as [curpri [st [m [sus H0]]]].
    assert (exists wt, get ecbls p_v = Some (absport, wt)) as [wt Hportwt].
    { apply nth_error_split in H16 as [? [? [? ?]]]. subst dpptrl.
      apply Forall_app in Hinecb as [? ?].
      inversion H75. auto. }
    assert ((if Int.eq tm_v Int.zero then None else Some tm_v) = Some tm_v /\
    tm_v <> Int.zero \/
    (if Int.eq tm_v Int.zero then None else Some tm_v) = None /\ tm_v = Int.zero) as Htopt.
    { assert (tm_v = Int.zero \/ tm_v <> Int.zero) as [ | ] by tauto.
    right. subst. rewrite Int.eq_true. auto.
    left. rewrite Int.eq_false;auto. }
    eapply seq_rule.
    eapply qportpend_nilblock_part1;eauto.
    { go. }
    { go.  }
    naive pure intro.
    eapply seq_rule.
    (* OSTCBCur ′ .. OSTCBDly =ₑ timeout ′ *)
    assert (tid = (v'24, Int.zero)) by tauto. subst tid.
    eapply qportpend_nilblock_part2;eauto.
    { go. }
    { go. }
    (* OS_EventTaskWait (­ 〈 OS_EVENT ∗ 〉 port_ptr ′­);ₛ *)
    eapply seq_rule.
    assert (tid = (v'24, Int.zero)) by tauto. subst tid.
    eapply qportpend_nilblock_part3;eauto.
    { go. }
    { go. }
    (* EXIT_CRITICAL;ₛ *)
    naive pure intro.
    simpljoin1.
    hoare forward prim.
    sep autocancel.
    sep name lift CoreCommuInv in H74.
    eapply CoreCommuInv_set_notsemq_frm.
    { unfold is_sem, not. intros [? [? ?]].
      clear - H75 Hportwt.
      unfold tid in *.
      rewrite H75 in Hportwt. tryfalse. }
    { unfold is_que, not. intros [? [? [? [? ?]]]].
      clear - H75 Hportwt.
      unfold tid in *.
      rewrite H75 in Hportwt. tryfalse. }
    sep cancel CoreCommuInv.
    sep name lift tcbdllflag in H74.
    sep name lift tcbdllflag.
    eapply tcbdllflag_hold with (l1:= (v'2 ++ v'3 :: v'4));eauto.
    { eapply tcbdllflag_hold_middle. cbn [eq_dllflag].
      clear - H88. eapply struct_type_vallist_match_os_tcb_flag in H88.
      simpljoin1. unfold V_OSTCBflag, V_OSTCBNext; cbn [nth_val update_nth_val].
      split;auto. }
    sep cancel tcbdllflag.
    sep name lift PartitionInv; apply fold_PartitionInv_frm.
    sep cancel PartitionInv_part2.
    unfold PartitionInv_part1.
    sep normal. sep eexists. sep autocancel.
    unfold AOSDomainPortPtrList.
    sep normal. sep eexists.
    sep autocancel.
    sep pauto.
    eapply dmportp_sllseg_compose;eauto.
    sep name lift  (dmportp_sllseg dportlptr (Vptr p_v) dportl1
    dportmsgll1 OS_Port_V_nextPort) in H74.
    sep cancel dmportp_sllseg.
    sep cancel dmportp_sllseg.
    sep cancel APortStruct.
    eapply disj_split.
    right.
    sep normal.
    sep eexists.
    sep autocancel.
    instantiate (2:= v'25). instantiate (2:= qentries). instantiate (2:= ($ Z.of_nat sz)). instantiate (2:= qend).
    instantiate (2:= qin). instantiate (2:= qin). instantiate (2:= (@nil (list val))).
    rewrite H73.
    simpl (dmportp_sllseg_qport_msg qin qin qstart qend O nil).
    sep pauto.
    1,2,3,4,5, 7, 8:eauto.
    4: go.
    { (* RLH_PortPtrINecb *)
      split;auto.
      clear -Hinecb.
      eapply Forall_forall.
      intros.
      eapply Forall_forall in Hinecb;eauto.
      assert (x = p_v \/ x <> p_v) as [ | ] by tauto.
      subst. eexists. erewrite get_set_eq. eauto.
      destruct Hinecb. erewrite get_set_neq; eauto. }
    { (* RH_CurTCB *)
      unfold RH_CurTCB. do 4 eexists. erewrite get_set_eq. eauto. }
    { (* RH_TCBList_ECBList_P *)
      eapply partition_taskeventrules.RH_TCBList_ECBList_P_update_rdy2port;eauto. }
    (* end of critical region 
       sched ... *)
    clear - Hmode Hdir H2 H1 H61. rename v'29 into ier.
    remember ((v'24, Int.zero)) as ct. clear Heqct v'24.
    rename v'28 into cha_b. 
    (* OS_Sched (­);ₛ *)
    eapply seq_rule.
    eapply call_rule';[
      cbn;unfold OS_Sched_spec;eauto |  intros; 
      do 5 try (apply rvl_elim;[ symbolic_execution | ]);
       first [apply rvl_nil | simpl;auto] |  
       idtac..
      ].
    { (* PRE ==> *)
      intros. unfold_spec. sep normal. sep eexists. sep autocancel. sep pauto.
      unfold isflag. auto. }
    { go. }
    { sep_unfold_funpost.  intros. sep destruct H. sep eexists.  sep autocancel. sep auto. }
    { sep_unfold_funpre.  intros. sep destruct H. sep eexists.  sep autocancel. sep auto. }
    { go. }
    unfold getasrt; unfold OS_SchedPost, OS_SchedPost'.
    naive pure intro. inversion H. clear v' v'0 v'1 ier H H3 H4. rename v'2 into ier.
    assert (DEFAULT_CHANNLE_SEMAPHROE = Z.of_nat 255).
    {  clear. unfold DEFAULT_CHANNLE_SEMAPHROE. auto. } 
    rewrite H.
    eapply qportpend_nilblock_finalcriticalregion;eauto.
    clear. mauto.
Qed.
  

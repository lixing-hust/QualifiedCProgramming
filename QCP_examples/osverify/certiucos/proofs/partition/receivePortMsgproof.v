Require Import ucos_include.
Require Import Lia.


Require Import aux_pureLib.
Require Import abs_op_corecommu_rules.
Require Import OSTimeTickPure.
Require Import corecommu_sep_added.
Require Import corecommu_tactics.
Require Import partition_rules.
Require Import partition_seprules.
Require Import partition_absrules.
Require Import partition_symrules.
Require Import partition_tactics.
Require Import partition_taskeventrules.
Require Import qportpostproof_aux.
Require Import new_inv.
Require Import hoare_assign.
Require Import partinv_lemmas.


Open Scope code_scope.

Open Scope int_scope.

Lemma direction_P_equiv: forall vl optionp,
    match optionp with
    | Some p =>
        OS_Port_V_OSEventPtrPort vl =
        Some (Vptr p)
    | None =>
        OS_Port_V_OSEventPtrPort vl = Some Vnull
    end <->
    OS_Port_V_OSEventPtrPort vl = Some (option_addrval_to_val optionp).
Proof.
  intros.
  destruct optionp; simpl; tauto.
Qed.

Lemma nth_error_last_firstn: forall (A:Type) (l:list A) (n:nat) p d,
  nth_error l n = Some p ->
  last (firstn (S n) l) d = p.
Proof.
  induction l; destruct n; intros.
  + simpl in H. discriminate.
  + simpl in H. inverts H. 
  + simpl in H. inverts H. simpl. auto.
  + simpl in H. apply IHl with (d:=d) in H as ?.
    simpl. destruct l. rewrite nth_error_nil in H. discriminate.
    auto.
Qed.

Lemma receivePortMsg_tcbls_ecbls_one_step_true: forall n pl p tcbls tcbls' tcbls'' ecbls,
  nth_error pl n = Some p ->
  receivePortMsg_tcbls_ecbls (firstn n pl) ecbls tcbls tcbls' true ->
  receivePortMsg_tcbls_ecbls (p::nil) ecbls tcbls' tcbls'' true ->
  receivePortMsg_tcbls_ecbls (firstn (S n) pl) ecbls tcbls tcbls'' true.
Proof.
  intros.
  assert (n<length pl)%nat.
  apply nth_error_Some. congruence.
  rewrite <- removelast_firstn in H0; auto.
  lets Hx: app_removelast_last addrval (firstn (S n) pl) (1%positive,Int.zero).
  rewrite Hx.
  eapply receivePortMsg_tcbls_ecbls_trans_true.
  eauto.
  erewrite nth_error_last_firstn; eauto.
  destruct pl.
  rewrite nth_error_nil in H. discriminate.
  auto.
Qed.

Lemma receivePortMsg_tcbls_ecbls_one_step_false: forall n pl p tcbls tcbls' tcbls'' ecbls,
  nth_error pl n = Some p ->
  receivePortMsg_tcbls_ecbls (firstn n pl) ecbls tcbls tcbls' true ->
  receivePortMsg_tcbls_ecbls (p::nil) ecbls tcbls' tcbls'' false ->
  receivePortMsg_tcbls_ecbls (firstn (S n) pl) ecbls tcbls tcbls'' false.
Proof.
  intros.
  assert (n<length pl)%nat.
  apply nth_error_Some. congruence.
  rewrite <- removelast_firstn in H0; auto.
  lets Hx: app_removelast_last addrval (firstn (S n) pl) (1%positive,Int.zero).
  rewrite Hx.
  eapply receivePortMsg_tcbls_ecbls_trans_false.
  eauto.
  erewrite nth_error_last_firstn; eauto.
  destruct pl.
  rewrite nth_error_nil in H. discriminate.
  auto.
Qed.


Lemma RH_CorePortPtrList_nth_error_head:
  forall pl head dportls,
  RH_CorePortPtrList head pl dportls ->
  head = option_addrval_to_val (nth_error pl 0).
Proof.
  intros. destruct pl.
  + simpl in *. auto.
  + simpl in *. simpljoin.
Qed.

Lemma RH_CorePortPtrList_nth_error_get:
  forall n pl  head p  dportls,
  RH_CorePortPtrList head pl dportls ->
  nth_error pl n = Some p ->
  exists pcn pd pid pst pin pout pt, 
  get dportls p = Some (pcn, pd, pid, DestinationP (nth_error pl (S n)), pst, pin, pout, pt).
Proof.
  induction n; intros.
  + simpl in H0. destruct pl; try discriminate. inverts H0.
    simpl in H. simpljoin. 
    destruct pl. 
    - do 7 eexists; simpl. simpl in H1. destruct x2; inverts H1. eauto.
    - simpl in H1. simpljoin1. destruct x2; inverts H; auto.
      do 7 eexists. simpl. eauto.
  + destruct pl; try discriminate.
    simpl in H0. simpl in H. simpljoin. destruct pl; simpl.
    rewrite nth_error_nil in H0. discriminate.
    lets Hx:IHn H2 H0. simpl in Hx. assumption.
Qed.

Lemma RH_CorePortPtrList_nth_error_get':
  forall n pl head dportls,
  RH_CorePortPtrList head pl dportls ->
  (n < length pl)%nat ->
  exists p pcn pd pid pst pin pout pt, 
  nth_error pl n = Some p /\ get dportls p = Some (pcn, pd, pid, DestinationP (nth_error pl (S n)), pst, pin, pout, pt).
Proof.
  intros.
  apply nth_error_Some in H0.
  destruct (nth_error pl n) eqn : eq1.
  lets Hx:RH_CorePortPtrList_nth_error_get H eq1. simpljoin.
  do 8 eexists. split; eauto. congruence.
Qed.

Lemma can_change_aop_tcbdllseg1: forall  vl1 head tail headprev tailnext vl2,
  can_change_aop (tcbdllseg1 head headprev tail tailnext vl1 vl2).
Proof.
  induction vl1; simpl; intros; auto.
  splits; auto.
  intros. splits; auto.
  destruct (pair_list_get head vl2); can_change_aop_solver.
Qed.

Lemma RH_CorePortPtrList_isptr' : forall pl p dportls,
  RH_CorePortPtrList p pl dportls ->
  isptr p.
Proof.
  induction pl; intros.
  + unfold RH_CorePortPtrList in H.
    subst. left. auto.
  + simpl RH_CorePortPtrList in H.
    simpljoin1.
    right. eauto.
Qed.

Lemma receivePortMsg_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal receivePortMsg vl logicl receivePortMsgPre ct->
      Some r =
      BuildRetI os_internal receivePortMsg vl logicl receivePortMsgPost ct->
      exists t d1 d2 s,
        os_internal receivePortMsg = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  hoare name lift PartitionInv pre.
  eapply backward_rule1.
  apply unfold_PartitionInv_frm.
  rename v'5 into is.
  rename v'6 into isr.
  rename v'7 into ier.
  rename v'4 into s.
  rename v'9 into ecbls.
  rename v'11 into rtbl.
  rename v'12 into rgrp.
  rename v'10 into ptbl.
  rename v'8 into tcbls.
  rename v'13 into ptls.
  rename v'14 into vhold.
  rename v'15 into p1.
  rename v'16 into p2.
  rename v'17 into tcbl1.
  rename v'18 into tcbcur.
  rename v'19 into tcbl2.
  rename v'3 into prio_hold.
  rename v'2 into y_hold.
  rename v'1 into x_hold.
  rename v'0 into ptcb_hold.
  rename v' into port_ptr_hold.
  unfold PartitionInv_part1.
  naive pure intro.
  rename v' into dportlptr.
  rename v'0 into dportl.
  rename v'1 into dportmsgll.
  rename v'8 into dportls.
  rename v'9 into kportvl.
  rename v'10 into kportl.
  rename v'11 into kportls.
  rename v'14 into chanvl.
  rename v'15 into chanl.
  rename v'16 into chandstkportll.
  rename v'17 into chanls.
  rename v'18 into chanfptr.
  rename v'19 into chanfl.
  rename v'12 into kportfptr.
  rename v'13 into kportfl.
  rename v'4 into otherppl.
  rename v'5 into otherpl.
  rename v'6 into othermsgll.
  rename v'24 into cportpl.
  rename v'23 into cportlptr.
  rename v'2 into dportls1.
  rename v'7 into dportls2.
  rename v'3 into dpptrl.
  rename v'20 into scapl.
  rename v'21 into mcapl.
  rename v'22 into qcapl.
  subst logicl.
  clear H.
  rename H0 into HCORSEM_INECB_P.
  rename H1 into HRH_TCBList_ECBList_P.
  rename H4 into Hjoin_dportls.
  rename H5 into HRL_PortAttr.
  rename H6 into HRLH_PortPtrINecb.
  rename H7 into HRLH_Domainportl.
  rename H8 into HRLH_Kernelport.
  rename H9 into HRLH_Channel.
  rename H10 into HR_KernelPort_DomianPort.
  rename H11 into HR_KernelPortIDTbl_ChannelIDTbl.
  rename H12 into HRLH_OtherPortPtrList.
  rename H13 into Hkportls_nodup.
  unfold RLH_PortPtrINecb in HRLH_PortPtrINecb.
  destruct HRLH_PortPtrINecb as (HRL_PortPtrList & HRLH_PortPtrINecb).
  unfold AOSCorePortPtrList.
  hoare normal pre.
  naive pure intro.
  rename H into HRH_CorePortPtrList.
  hoare forward.
  {
    lets Htmp: RH_CorePortPtrList_isptr' HRH_CorePortPtrList.
    clear - Htmp. pauto.
  }
  hoare name lift AOSRdyGrp AOSTCBPrioTbl AOSTCBList EvtInv pre.
  hoare name lift DynamicRefactorINV AOSMapTbl AOSUnMapTbl AOSRdyTblGrp pre.
  hoare name lift x y prio ptcb AOSDomainPortPtrList pre.
  hoare name lift port_ptr pre.
  hoare remember (1::2::3::4::5::6::7::8::9::10::11::12::13::nil)%nat pre.
  (*High level tcblist and ecblist will not change *)
  apply backward_rule1 with
  (
    EX n x_v y_v prio_v ptcb_v tcbls' rtbl' rgrp' tcbl1' tcbl2' tcbcur',
    LV port_ptr @ OS_Port ∗ |-> option_addrval_to_val (nth_error cportpl n) **
    [| receivePortMsg_tcbls_ecbls (firstn n cportpl) ecbls tcbls tcbls' true |] **
    [| (n <= length cportpl)%nat |] **
    LV x @ char_t |-> x_v **
    LV y @ char_t |-> y_v **
    LV prio @ char_t |-> prio_v **
    LV ptcb @ OS_TCB ∗ |-> ptcb_v **
    AOSDomainPortPtrList dportlptr dportl dportmsgll **
    DynamicRefactorINV ecbls **
    AOSMapTbl **
    AOSUnMapTbl **
    AOSRdyTblGrp rtbl' rgrp' **
    AOSTCBPrioTbl ptbl rtbl' tcbls' ptls vhold **
    AOSTCBList p1 p2 tcbl1' (tcbcur' :: tcbl2') rtbl' ct tcbls' **
    EvtInv ecbls p1 (tcbl1' ++ tcbcur' :: tcbl2') tcbls' vhold scapl mcapl qcapl **
    [| CORESEM_INECB_P ecbls |]**
    [| RH_TCBList_ECBList_P ecbls tcbls' ct |] **
    [| RH_CurTCB ct tcbls' |] **
    [| Forall
    (fun x : addrval =>
     exists wt, get ecbls x = Some (absport, wt)) dpptrl |] **
    H
  ).
  {
    intros state Hs.
    exists O. sep eexists. sep autocancel.
    sep split; auto.
    - lets Htmp: RH_CorePortPtrList_nth_error_head HRH_CorePortPtrList.
      subst cportlptr. sep auto.
    - lia.
    - simpl. constructor.
  }
  (*WHILE Loop*)
  eapply seq_rule.
  {
    apply while_rule with (tp:=Tint32).
    {
      intros. sep destruct H0. symbolic_execution.
      destruct (nth_error cportpl x); auto.
      destruct (nth_error cportpl x); simpl; destruct x; auto.
      destruct a; auto. destruct a; auto.
      destruct (nth_error cportpl x); auto.
      simpl. destruct a; auto.
    }

    naive pure intro.
    rename v' into n.
    rename v'0 into x_v.
    rename v'1 into y_v.
    rename v'2 into prio_v.
    rename v'3 into ptcb_v.
    rename v'4 into tcbls'.
    rename v'5 into rtbl'.
    rename v'6 into rgrp'.
    rename v'7 into tcbl1'.
    rename v'8 into tcbl2'.
    rename v'9 into tcbcur'.
    eapply backward_rule1.
    {
      intros. eapply sep_aconj_r_aistrue_to_astar in H0. apply H0. clear s0 H0.
      intros state Hs.
      symbolic_execution.
      destruct (nth_error cportpl n); auto.
      destruct (nth_error cportpl n); simpl; destruct n; auto.
      destruct a; auto. destruct a; auto.
      destruct (nth_error cportpl n); auto. simpl. destruct a; auto.
    }
    naive pure intro.
    destruct H7 as (Htmp&_&_).
    rename H0 into HreceivePortMsg_tcbls_ecbls'.
    rename H1 into Hn_range.
    rename H3 into HCORESEM_INECB_P'.
    rename H4 into HRH_TCBList_ECBList_P'.
    rename H5 into HRH_CurTCB'.
    rename H6 into Hinecbls'.
    assert (n = length cportpl \/ n<length cportpl)%nat as Htmp' by lia.
    destruct Htmp' as [Htmp' | Htmp'].
    {
      subst n. lets Htmp'': nth_error_None cportpl (length cportpl).
      assert (length cportpl <= length cportpl)%nat as Htmp''' by lia.
      apply Htmp'' in Htmp'''. clear Htmp''.
      rewrite Htmp''' in Htmp.
      simpl in Htmp. unfold Int.notbool in Htmp.
      assert (Int.eq Int.one Int.zero = false) as Htmp'''' by mauto.
      rewrite Htmp'''' in Htmp. congruence.
    }
    clear Hn_range.
    rename Htmp' into Hn_range. clear Htmp.
    lets Hget_port : RH_CorePortPtrList_nth_error_get' HRH_CorePortPtrList Hn_range.
    simpljoin1.
    rename x0 into pcn.
    rename x1 into pd.
    rename x2 into pid.
    rename x3 into pst.
    rename x4 into pin.
    rename x5 into pout.
    rename x6 into pt.
    rename x into portp.
    rename H1 into Hget_portp.
    rewrite H0.
    rename H0 into Hnerr_cportpl.
    simpl option_addrval_to_val.

    (* Split dmportp_sllseg *)
    unfold AOSDomainPortPtrList.
    hoare normal pre.
    lets Htmp: RLH_Domainportl_abs_getsome HRL_PortPtrList HRLH_Domainportl Hget_portp. 
    simpljoin1.
    rename x into pptrn.
    rename x0 into portvl.
    rename x1 into portmsgl.
    rename H into Hnerr_dportl.
    rename H0 into Hnerr_dportmsgll.
    rename H1 into Hnerr_dpptrl.
    rename H3 into HDomainportNode_P. 
    apply nth_error_split in Hnerr_dportl as (dportl1 & dportl2 & Hdportl_split & Hlen_dportl1_n).
    apply nth_error_split in Hnerr_dportmsgll as (dportmsgll1 & dportmsgll2 & Hdportmsgll_split & Hlen_dportmsgll1_n).
    apply nth_error_split in Hnerr_dpptrl as (dpptrl1 & dpptrl2 & Hdpptrl_split & Hlen_dpptrl1_n).
    subst dportl dpptrl dportmsgll.
    unfold dmportp_sll. 
    hoare name lift dmportp_sllseg pre.
    eapply backward_rule1.
    { eapply dmportp_sllseg_app'_frm; eauto. 
      rewrite <- Hlen_dpptrl1_n. apply nth_error_middle.
    }
    assert (exists wt, get ecbls portp = Some (absport, wt)) as [wt Hget_ecbls'_portp].
    {
      apply Forall_app in Hinecbls' as [? ?].
      inverts H0. auto.
    }
    unfold EvtInv at 2.
    naive pure intro.
    rename H into HR_Q_Data_P.
    rename H0 into Hvhold_addr.
    rename H1 into HSEM_ECB_P.
    rename H2 into HRH_CurTCB.
    rename H3 into HMUX_ECB_P.
    rename H4 into HQ_ECB_P.
    rename H5 into Hevcre_nodup.
    rename H6 into Hevdel_nodup.
    rename H7 into Heibref_distinct.
    hoare name lift AECBList pre.
    rename v'1 into ectrl.
    rename v'4 into msgql.
    unfold AECBList.
    naive pure intro.
    rename v'1 into evheadptr.
    rename H into HECBList_P.
    (* split evsllseg*)
    assert (exists et etbl petbl, get_ectr (Vptr portp) evheadptr ectrl = Some (et,etbl, petbl)) as (et & etbl & petbl & Fget_ectr).
    { 
      eapply ECBList_P_get_ectr_some in HECBList_P; try eauto. 
    }
    hoare name lift evsllseg pre.
    eapply backward_rule1.
    { intros ? Hs. eapply get_ectr_decompose in Hs;eauto. }
    naive pure intro.
    rename v'1 into et_next.
    rename v'4 into ectrl1.
    rename v'21 into portmsgq.
    rename v'19 into msgql1.
    rename v'18 into ectrl2.
    rename v'20 into msgql2.
    destruct H as (Hetnext & ? &  ? & Hgetectr1 & Hgetectr2 & Hevheadptr_notnull & Hnexptr ).
    subst ectrl msgql.
    hoare_assert_pure (exists portgrp, V_OSEventGrp et = Some (Vint32 portgrp) /\ struct_type_vallist_match OS_EVENT et ).
    {
      clear - H.
      unfold AEventNode in H.
      unfold AOSEvent in H.
      sep normal in H. sep destruct H. 
      unfold node in H. sep normal in H.  sep destruct H.
      sep split in H. destruct H0. clear - H14 H0.
      struct_type_vallist_match_elim.
      eexists. split. reflexivity. pauto.
    }
    naive pure intro.
    rename v'1 into evgrp.
    destruct H.
    rename H into Het_V_EventGrp.
    rename H0 into Het_type_match.

    (* If (port_ptr ′ .. OSEventGrp !=ₑ ′ 0) *)
    destruct (Int.eq evgrp Int.zero) eqn:Egrp.
    {
      (* OSEventGrp = 0 *)
      eapply seq_rule.
      apply corecommu_rules.ift_zero_rule.
      intros. unfold AEventNode in H.
      unfold AOSEvent in H.
      sep normal in H. sep destruct H. 
      unfold node in H. sep normal in H.  sep destruct H.
      sep split in H. destruct H0. inverts H0.
      eapply symbolic_lemmas.uop_rv.
      eapply symbolic_lemmas.bop_rv.
      sep name lift A_dom_lenv in H.
      eapply symbolic_lemmas.struct_member_rv_typeneq.
      sep autocancel. eauto.
      reflexivity.
      reflexivity.
      reflexivity.
      reflexivity.
      reflexivity.
      auto.
      auto.
      auto.
      reflexivity.
      clear - H14. struct_type_vallist_match_elim. simpl. lia.
      auto.
      instantiate (1:=Vint32 evgrp). 
      struct_type_vallist_match_elim.
      inverts Het_V_EventGrp. 
      reflexivity.
      symbolic_execution.
      simpl. 
      reflexivity.
      pauto.
      reflexivity.
      setoid_rewrite Egrp.
      reflexivity.
      pauto.
      reflexivity.
      unfold DomainportNode_P in HDomainportNode_P.
      destruct HDomainportNode_P as (HDomainportNode_nat_P & HDomainportNode_direction_P & HDomainportNode_Porrt_P).
      unfold Domainport_direction_P in HDomainportNode_direction_P.
      destruct HDomainportNode_direction_P as (HDomainportNode_direction_P & HDomainportNode_direction_P').
      apply direction_P_equiv in HDomainportNode_direction_P'.
      hoare evar lift port_ptr pre.
      hoare abs lift pre.
      eapply forward_rule1.
      2:{
        (* port_ptr ′ =ₑ port_ptr ′ .. OSEventPtrPort *)
        eapply assign_rule_lvar.
        - reflexivity.
        - intros.
          cbn [dmportp_sllseg] in H.
          sep normal in H. sep destruct H.
          sep split in H. invertsr H0.
          sep evar lift port_ptr in H.
          eapply port_OSEventPtrPort_rv; eauto.
        - apply assign_type_match_true. reflexivity.
        - intros. sep auto.  
      }
      intros.
      exists (S n). sep eexists. unfold EvtInv.
      sep normal. sep eexists. sep autocancel.
      sep name lift dmportp_sllseg.
      eapply dmportp_sllseg_app'_frm.
      4: eauto.
      4:{
        sep autocancel.
        unfold AECBList.
        sep normal. sep eexists.
        sep cancel OSEventList.
        eapply evsllseg_compose.
        4:{
          sep autocancel.
          sep split; eauto.
          eapply receivePortMsg_tcbls_ecbls_one_step_true; eauto.
          eapply receivePortMsg_tcbls_ecbls_nochange. eauto.
          constructor.
        }
        1-3: auto.
      }
      3: apply nth_error_middle.
      1,2: congruence.
    }
    {
      (* OSEventGrp != 0 *)
      hoare_assert_pure (length ectrl1 = length msgql1).
      { sep name lift evsllseg in H.
      eapply evsllseg_list_len_eq;eauto. }
      naive pure intro.
      rename H into Hlen_ectrl1_msgql1.
      struct_type_vallist_match_elim.
      inverts Hetnext.
      inverts Het_V_EventGrp.
      rename H into i1_range.
      rename H0 into Hegrp_range.
      rename H1 into Hi2_range.
      rename H2 into Hisptr_x0.
      rename H3 into Hisptr_et_next.
      rename H4 into Hi_range.
      unfold DomainportNode_P in HDomainportNode_P.
      destruct HDomainportNode_P as (HDomainportNode_nat_P & HDomainportNode_direction_P & HDomainportNode_Porrt_P).
      unfold Domainport_nat_P in HDomainportNode_nat_P.
      simpljoin1.
      rename H into Hportvl_V_coreNUM.
      rename x into domain.
      rename H1 into Hportvl_V_domain.
      rename H3 into Hportvl_V_portID.
      rename H5 into Hx2_le_PORT_NUMS.
      rename H6 into Hportvl_V_status.
      rename H8 into Hportvl_V_msgInTick.
      rename H10 into Hportvl_V_msgOutTick.
      assert (
      exists y,
        nth_val' (Z.to_nat (Int.unsigned evgrp)) OSUnMapVallist = Vint32 y /\
        Int.unsigned y < 8 
      ) as Htmp.
      {
        lets Hx1: osunmapvallist_prop Hegrp_range; simpljoin.
        eexists. split; eauto. lia.
      }
      destruct Htmp as (y&unmap_egrp&y_lt8).
      destruct (Int.eq y domain) eqn: Edomain.
      2:{
        (* y!= domain*)
        unfold AOSUnMapTbl at 2.
        unfold AEventNode.
        unfold AOSEvent.
        naive pure intro.
        unfold node.
        naive pure intro. simpljoin.
        inverts H5. rename v'20 into portpb.
        cbn [dmportp_sllseg].
        naive pure intro.
        inverts H5.
        eapply seq_rule.
        apply corecommu_rules.ift_nonzero_rule.
        - intros. exists Int.one. 
          sep normal in H. sep destruct H. 
          sep split. 2:{ clear. mauto. }
          eapply symbolic_lemmas.uop_rv.
          eapply symbolic_lemmas.bop_rv.
          sep name lift A_dom_lenv in H.
          eapply symbolic_lemmas.struct_member_rv_typeneq.
          sep autocancel. eauto.
          reflexivity.
          reflexivity.
          reflexivity.
          reflexivity.
          reflexivity.
          auto.
          auto.
          auto.
          reflexivity.
          simpl. lia.
          auto.
          reflexivity.
          symbolic_execution.
          simpl. setoid_rewrite Egrp. simpl. reflexivity.
          pauto.
          reflexivity.
          reflexivity.
          auto.
          reflexivity.
        - hoare forward.
          rewrite unmap_egrp. rtmatch_solve.
          rewrite unmap_egrp.
          apply corecommu_rules.ift_zero_rule.
          intros.
          eapply symbolic_lemmas.bop_rv.
          instantiate (1:=Vint32 y).
          symbolic_execution.
          rewrite byte_max_unsigned_val.
          clear - y_lt8. 
          assert (Int.unsigned y <=? 255 = true) by lia.
          now rewrite H.
          eapply port_domain_rv; eauto.
          2:{
            sep autocancel. apply H5.
          }
          3,4: auto.
          unfold DomainportNode_P.
          split; eauto.
          unfold Domainport_nat_P.
          do 5 eexists. splits; eauto.
          splits; eauto.
          simpl. unfold Coqlib.nat_of_Z.
          rewrite Z2Nat.id. 2: { clear. pose proof Int.unsigned_range domain. tauto. }
          rewrite Int.repr_unsigned.
          now rewrite Edomain. 
        - hoare evar lift port_ptr pre.
          hoare abs lift pre.
          unfold Domainport_direction_P in HDomainportNode_direction_P.
          destruct HDomainportNode_direction_P as (HDomainportNode_direction_P & HDomainportNode_direction_P').
          apply direction_P_equiv in HDomainportNode_direction_P'.
          eapply forward_rule1.
          2:{
            (* port_ptr ′ =ₑ port_ptr ′ .. OSEventPtrPort *)
            eapply assign_rule_lvar.
            - reflexivity.
            - intros.
              sep evar lift port_ptr in H5.
              eapply port_OSEventPtrPort_rv; eauto.
              sep autocancel. apply H5.
            - apply assign_type_match_true. reflexivity.
            - intros. sep auto.  
          }
          intros.
          exists (S n). sep eexists.
          sep normal. unfold EvtInv. sep normal. sep eexists.  sep autocancel.
          unfold AECBList. sep normal. sep eexists.
          sep cancel OSEventList.
          sep name lift dmportp_sllseg.
          eapply dmportp_sllseg_compose; auto.
          3:{
            unfold AOSUnMapTbl.
            sep autocancel.
            eapply evsllseg_compose.
            4:{
              unfold AEventNode.
              sep normal.
              sep autocancel.
              unfold AOSEvent. unfold node.
              sep normal. sep eexists.
              sep autocancel.
              sep split; eauto.
              eapply receivePortMsg_tcbls_ecbls_one_step_true; eauto.
              eapply receivePortMsg_tcbls_ecbls_nochange. eauto.
              constructor.
            }
            1-3: auto.
          }
          auto. auto.
        }
        {
          (* y = domain*)
          eapply ecblist_p_decompose_new in HECBList_P as ?;eauto.
          destruct H as (ecbls1&ecblsc2&HECBList_P_ecbls1&HECBList_P_ecblsc2&Hjoin_ecbls&Hget_last_ptr).
          simpl app in HECBList_P_ecblsc2.
          cbn [ECBList_P] in HECBList_P_ecblsc2.
          destruct HECBList_P_ecblsc2 as (?&Htmp&HR_ECB_Etbl_P&HR_ECB_PETbl_P&HECBList_P_ecbls2).
          invertsr Htmp.
          simpljoin. invertsr H.
          rename x into porth.
          rename x7 into ecbls2.
          rename H0 into HTcbJoin_ecbls2.
          rename H1 into HRLH_ECBData_P.
          rename H2 into HECBList_P_ecbls2.

          hoare name lift AOSTCBPrioTbl pre.
          unfold AOSTCBPrioTbl at 2.
          naive pure intro.
          simpljoin.
          rename H into Hptbl_type_match.
          rename H3 into Hlen_ptbl.
          rename H0 into HRL_RTbl_PrioTbl_P.
          rename H1 into HR_PrioTbl_P.
          rename H2 into HRH_PrioTbl_P.

          hoare name lift AOSTCBList pre.
          unfold AOSTCBList at 2.
          naive pure intro.
          hoare lifts (2::4::nil)%nat pre.
          hoare_assert_pure (ptr_in_tcblist p2 p1 (tcbl1'++tcbcur'::tcbl2')). 
          {
            eapply OSQPostPure.tcbdllseg_combine_ptr_in_tcblist; eauto.
          }
          naive pure intro.
          rename H3 into Hptr_in_tcblist.
          hoare_assert_pure (OSQPostPure.get_last_tcb_ptr tcbl1' p1 = Some p2 ).
          {
            eapply OSQPostPure.tcbdllseg_get_last_tcb_ptr; eauto.
          }
          naive pure intro.
          rename H3 into Hget_last_tcb_ptr.
          eapply backward_rule1.
          {
            intros.
            eapply tcbdllseg_compose.
            sep cancel 1%nat 1%nat.
            sep cancel 1%nat 1%nat.
            eauto.
          }
          rename v'19 into tcbls1.
          rename v'20 into tcblsc2.
          rename H0 into Hjoin_tcbls.
          rename H1 into HTCBList_P_tcbls1.
          rename H2 into HTCBList_P_tcblsc2.
          destruct H. subst p2.
          lets HTCBListP_tcbls: OSQPostPure.TCBList_P_Combine Hget_last_tcb_ptr Hjoin_tcbls HTCBList_P_tcbls1 HTCBList_P_tcblsc2.
          rename H into Hp1_notnull.

          hoare_assert_pure (length etbl = Z.to_nat OS_EVENT_TBL_SIZE /\ 
          array_type_vallist_match Int8u etbl).
          {
              sep name lift AEventNode in H.
              unfold AEventNode in H.
              unfold AOSEvent in H.
              sep normal in H. sep destruct H.
              sep name lift AOSEventTbl in H.
              unfold AOSEventTbl in H.
              sep normal in H. sep destruct H.
              sep split in H.
              split; auto.
              eapply Aarray_vl_len_eq; eauto.
          }
          naive pure intro.
          destruct H as (Hlen_etbl_EVENT_TBL_SIZE&Hetbl_type_match).
          unfold AEventNode.
          unfold AOSEvent.
          naive pure intro.
          invertsr H0.
          rename H into H_id_addrval_OSEventTbl.
          rename H2 into H_id_addrval_OSPostEventTbl.
          invertsr H3.
          rename H1 into HRL_Tbl_Grp_P_etbl.
          rename H4 into HRL_Tbl_Grp_P_petbl.
          assert (
          exists x erow bitx bity,
            nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 erow /\
            Int.unsigned erow < 256 /\ erow <> $ 0 /\
            nth_val' (Z.to_nat (Int.unsigned erow)) OSUnMapVallist = Vint32 x /\
            Int.unsigned x < 8 /\
            nth_val' (Z.to_nat (Int.unsigned y)) OSMapVallist = Vint32 bity /\
            Int.unsigned bity <= 128 /\
            nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 bitx /\
            Int.unsigned bitx <= 128
          ) as Htmp.
          {
            lets Hx2: array_int8u_nth_lt_len Hetbl_type_match.
            rewrite Hlen_etbl_EVENT_TBL_SIZE in Hx2.
            unfold OS_EVENT_TBL_SIZE in Hx2.
            assert ((Z.to_nat (Int.unsigned y) < 8)%nat) as Htmp by lia.
            lets Hx2': Hx2 Htmp; clear Hx2; simpljoin.
            lets Hx3: osunmapvallist_prop H0; simpljoin.
            apply Zle_bool_imp_le in H2.
            assert (Int.unsigned y <= 7) as Htmp' by lia.
            lets Hx4: osmapvallist_prop Htmp'.
            lets Hx5: osmapvallist_prop H2.
            simp join.
            do 4 eexists; splits; eauto.
            lia. 2: lia.
            eapply rl_tbl_grp_neq_zero with (v'12:= evgrp); eauto.
            int auto. 
            clear - n0 Hegrp_range.
            mauto. 
          }
          destruct Htmp as [x  [erow [bitx [bity Htmp]]]].
          destruct Htmp as
             [nth_val_etbl [erow_lt256 [erow_ne0 [unmap_erow [x_lt8 [map_y
              [bity_le128 [map_x bitx_le128]]]]]]]].
          pose proof lt_8_le_byte_max_unsigned_true y y_lt8 as y_ble_max.
          pose proof lt_8_le_byte_max_unsigned_true x x_lt8 as x_ble_max.
          pose proof lt_256_le_byte_max_unsigned_true erow as erow_ble_max.
          pose proof le_128_le_byte_max_unsigned_true bity bity_le128 as bity_ble_max.
          pose proof le_128_le_byte_max_unsigned_true bitx bitx_le128 as bitx_ble_max.

          unfold node.
          naive pure intro.
          destruct H.
          inverts H.
          rename v'20 into portpb.
          cbn [dmportp_sllseg].
          naive pure intro.
          inverts H.
          rename H1 into Hportvl_V_nextPort.
          rename H2 into Hportvl_type_match.
          rename H3 into Hportvl_V_Qstart.

          hoare_assert_pure (portmsgq = DPort /\ porth = (absport,wt) /\ i1 = ($ OS_EVENT_TYPE_PORT)).
          {
            eapply join_sig_get in HTcbJoin_ecbls2; eauto.
            eapply EcbMod.join_get_get_r in Hjoin_ecbls; eauto.
            unfold get, EcbMap in Hget_ecbls'_portp.
            rewrite Hget_ecbls'_portp in Hjoin_ecbls.
            inverts Hjoin_ecbls.
            unfold RLH_ECBData_P in HRLH_ECBData_P.
            destruct portmsgq; tryfalse.
            splits; auto.
            unfold AEventNode in H.
            unfold AEventData in H.
            sep normal in H. 
            sep name lift V_OSEventType in H.
            sep split in H.
            invertsr H1. auto.
          }
          naive pure intro.
          simpljoin.
          assert(Int.unsigned ((y<<ᵢ$ 3)+ᵢx) < 64) as prio_lt64.
          { clear - y_lt8 x_lt8. mauto. }

          pose proof lt_64_le_byte_max_unsigned_true ((y<<ᵢ$ 3)+ᵢx) prio_lt64 as prio_ble_max.

          assert(exists tid st m sus, get tcbls' tid = Some ((y<<ᵢ$ 3)+ᵢx, st, m, sus) /\ rel_edata_stat (portpb, Int.zero) DPort st) as ex_tid_prio_rel.
          {
            assert(($ (Int.unsigned (y<<ᵢ$ 3) + Int.unsigned x)>>ᵢ$ 3) = y) as y_shl3_shr3.
            clear - x_lt8 y_lt8.
            mauto.
          
            assert(($ (Int.unsigned (y<<ᵢ$ 3) + Int.unsigned x)&ᵢ$ 7) = x) as y_shl3_and7.
            clear - x_lt8 y_lt8.
            mauto.
          
            unfold R_ECB_ETbl_P in HR_ECB_Etbl_P; simp join.
            eapply PrioWaitInQ_RLH_ECB_ETbl_P_tcbls_ex.
            3:{
              unfold rel_edata_etype. reflexivity.
            }
            3:{
              eauto.
            }
            2: reflexivity.
            unfolds.
            clear - prio_lt64 y_lt8 x_lt8 Hetbl_type_match H_id_addrval_OSPostEventTbl nth_val_etbl unmap_erow erow_lt256 erow_ne0 y_shl3_shr3 y_shl3_and7.
            unfold Int.add in prio_lt64.
            rewrite Int.unsigned_repr in prio_lt64.
            do 3 eexists.
            splits; eauto.
            clear - x_lt8 y_lt8.
            mauto.
            apply nth_val'_imp_nth_val_int.
            rewrite y_shl3_shr3.
            eauto.
            rewrite y_shl3_and7.
            eapply math_8_255_eq; auto.
            clear - erow_lt256.
            int auto.
            clear - y_lt8 x_lt8.
            mauto.
          }
          destruct ex_tid_prio_rel as [tid [st [m [sus [Hget_tcbls_tid rel_ed_st]]]]].
          assert (
            nth_val' (Z.to_nat (Int.unsigned ((y<<ᵢ$ 3)+ᵢx))) ptbl = Vptr tid /\ tid <> vhold_addr
            ) as nth_val_ptbl_vhold.
          {clear - HR_PrioTbl_P Hget_tcbls_tid.
          unfolds in HR_PrioTbl_P; destruct HR_PrioTbl_P; destruct H0.
          eapply H0 in Hget_tcbls_tid; simp join; split;  auto.
          
          apply nth_val_nth_val'_some_eq; auto.
          }
          destruct nth_val_ptbl_vhold as [nth_val_ptbl tid_neq_vhold].
          (*key step: prove tid in tcbdllseg*)
          rename v'18 into tail.
          assert (ptr_in_tcblist (Vptr tid) p1 (tcbl1'++tcbcur'::tcbl2')) as Htid_ptr_in_tcblist.
          { eapply tcbls_get_some_TCBList_P_ptr_in_tcblist; eauto. }

          (*get the tcb node pointed by tid*)
          hoare name lift tcbdllseg pre.
          apply tcbdllseg1_init_pre.
          hoare_split_pure_all.
          apply tcbdllseg1_split_pre with (p:=Vptr tid).
          apply ptr_in_tcblist1_init; auto.
          naive pure intro.
          unfold node.
          naive pure intro.
          destruct H2.
          rename v'22 into tidb.
          inverts H2.
          struct_type_vallist_match_elim.
          rename H into Hdistinct_tcbdllseg_nexr_ptr.
          rename H1 into Htcbdllsegl_get_node.
          rename H2 into Hisptr_x17.
          rename H3 into Hisptr_x16.
          rename H4 into Hisptr_x15.
          rename H5 into Hisptr_x14.
          rename H6 into Hi7_range.
          rename H7 into Hi6_range.
          rename H8 into Hi5_range.
          rename H9 into Hi4_range.
          rename H10 into Hi3_range.
          rename H11 into Hi1_range.
          rename H12 into Hi0_range.
          rename H0 into Het_type_match.
          hoare name lift AOSRdyTblGrp pre.
          unfold AOSRdyTblGrp at 2.
          unfold AOSRdyGrp.
          naive pure intro.
          simpl in H.
          destruct rgrp'; try (simpl in H; discriminate H).
          rename i8 into rgrp'.
          rewrite byte_max_unsigned_val in H.
          assert (Int.unsigned rgrp' <= 255) as rgrp'_le255.
          {
            clear - H.
            destruct (Int.unsigned rgrp' <=? 255) eqn:E; try discriminate.
            lia.
          }
          clear H.
          destruct H0 as (HRL_Tbl_Grp_P & Hprio_in_tbl_idle).
          hoare_assert_pure (array_type_vallist_match char_t rtbl' /\ length rtbl' = ∘ OS_RDY_TBL_SIZE).
          { 
            unfold AOSRdyTbl in H.
            seplog_trm_tacs.sep_lifts_trms_in H array_type_vallist_match.
            eapply sep_pure_split in H; destruct H as (Hmat & _).
            auto.
          }
          seplog_trm_tacs.hoare_lifts_trms_pre (array_type_vallist_match).
          eapply pure_split_rule'; introv Hmat.
          destruct Hmat as (Hrtbl_type_match & Hlen_rtbl_rdy_tbl_size).
          assert (exists i, nth_val' (Z.to_nat (Int.unsigned y)) rtbl' = Vint32 i /\
                    Int.unsigned i <= 255) as nth_val_rtbl.
          {
            assert(Hvy: Int.unsigned y <= 7).
            clear - y_lt8.
            lia.
            pose proof z_le_7_imp_n y Hvy.
            lets Hx: array_int8u_nth_lt_len Hrtbl_type_match.
            rewrite Hlen_rtbl_rdy_tbl_size in Hx.
            unfold OS_RDY_TBL_SIZE in Hx.
            eapply Hx; eauto.
          }
          destruct nth_val_rtbl as [rrow [nth_val_rtbl rrow_le_255]].
          assert(y_le7: Int.unsigned y <= 7).
          {
            clear - y_lt8.
            lia.
          }
          assert(xle7: Int.unsigned x <= 7).
          { clear - x_lt8.
            lia.
          }
          assert(Herow: Int.unsigned erow <= 255).
          {
            clear - erow_lt256.
            lia.
          }
          apply sem_lab.semacc_int_eq_false in Egrp as Hevgrp_neq_zero.
          apply get_join in Hget_tcbls_tid as Hjoin_tcbls_tid.
          destruct Hjoin_tcbls_tid as (tcbls_tid&Hjoin_tcbls_tid).
          lets Htmp: port_exwt_succ_pre Hevgrp_neq_zero HR_PrioTbl_P HRL_Tbl_Grp_P_etbl HR_ECB_Etbl_P. 
          {
            pauto. 
          }
          reflexivity. reflexivity. 
          assert (TcbJoin (tidb,Int.zero)  ((y<<ᵢ$ 3) +ᵢ  x, st, m, sus) tcbls_tid tcbls') by tauto.
          clear Hjoin_tcbls_tid.
          rename H into Hjoin_tcbls_tid.
          lets Htmpp: Htmp HRH_TCBList_ECBList_P' Hjoin_ecbls HTcbJoin_ecbls2 Hetbl_type_match Hlen_etbl_EVENT_TBL_SIZE
          unmap_egrp.
          clear Htmp.
          lets Htmp: Htmpp nth_val_etbl unmap_erow nth_val_ptbl Hjoin_tcbls_tid.
          clear Htmpp.
          destruct Htmp as (Hwt_nnil&HGetHwait_tid&_).
          destruct sus.
          {
            assert (receivePortMsg_tcbls_ecbls (firstn (S n) cportpl) ecbls tcbls
            tcbls' false) as Htmp.
            {
              eapply receivePortMsg_tcbls_ecbls_one_step_false; eauto.
              eapply receivePortMsg_tcbls_ecbls_abort; eauto.
              constructor.
            }
            hoare name lift abstcblist absecblist oscoreportpl pre.
            hoare abs lift pre.
            eapply abscsq_rule.
            - apply noabs_oslinv.
            - eapply receivePortMsg_aspec_abt; eauto. can_change_aop_solver'.
              apply can_change_aop_tcbdllseg1.
            - apply absinfer_eq.
            - apply absabort_rule.    
          }
          lets HTCBNode_P: TCBList_P_get_node_TCBNode_P HTCBListP_tcbls Htcbdllsegl_get_node Hget_tcbls_tid.
          lets Hrel_edata_tcbstat: RHL_TCB_Status_Wait_P_rel_edata_stat_rel_edata_tcbstat rel_ed_st.
          {
            unfold TCBNode_P in HTCBNode_P.
            simpljoin.
            unfold R_TCB_Status_P in r0.
            simpljoin.
            apply r5. 
          }
          hoare_assert_pure (i6 = $OS_STAT_PORT).
          {
            unfold TCBNode_P in HTCBNode_P.
            simpljoin.
            lets Htmp: oscore_common.tcb_stat_sus_false_imp_stat_gen H3.
            simpljoin.
            cbn in H4. invertsr H4.

            unfold rel_edata_tcbstat in Hrel_edata_tcbstat.
            clear - Hrel_edata_tcbstat H5.
            destruct Hrel_edata_tcbstat; subst; auto.
            destruct H5; try discriminate.
            repeat (destruct H; try discriminate).
          }
          naive pure intro. subst i6.
          unfold rel_edata_stat in rel_ed_st.
          destruct rel_ed_st as (time & rel_ed_st). subst st.

          eapply seq_rule.
          {
            (* If (port_ptr ′ .. OSEventGrp !=ₑ ′ 0) *) 
            apply corecommu_rules.ift_nonzero_rule.
            {
              intros.
              exists Int.one.
              sep split. 2:{ clear. mauto. }
              eapply symbolic_lemmas.uop_rv.
              eapply symbolic_lemmas.bop_rv.
              sep name lift A_dom_lenv in H.
              eapply symbolic_lemmas.struct_member_rv_typeneq.
              sep autocancel. eauto.
              reflexivity.
              reflexivity.
              reflexivity.
              reflexivity.
              reflexivity.
              auto.
              auto.
              auto.
              reflexivity.
              simpl. lia.
              auto.
              reflexivity.
              symbolic_execution.
              simpl. setoid_rewrite Egrp. simpl. reflexivity.
              pauto.
              reflexivity.
              reflexivity.
              auto.
              reflexivity.
            }
            unfold AOSUnMapTbl at 2.
           

            (* os_code_defs.y ′ =ₑ OSUnMapTbl ′ [port_ptr ′ .. OSEventGrp];ₛ *)
            hoare forward.
            {
              rewrite unmap_egrp. rtmatch_solve. 
            }
            rewrite unmap_egrp.
            apply corecommu_rules.ift_nonzero_rule.
            {
              intros. exists Int.one.
              sep split. 2:{ clear. mauto. }
              eapply symbolic_lemmas.bop_rv.
              instantiate (1:=Vint32 y).
              symbolic_execution.
              rewrite byte_max_unsigned_val.
              clear - y_lt8.
              assert (Int.unsigned y <=? 255 = true) by lia.
              now rewrite H.
              eapply port_domain_rv; eauto.
              2:{
                sep autocancel. apply H.
              }
              3,4: auto.
              unfold DomainportNode_P.
              split; eauto.
              unfold Domainport_nat_P.
              do 5 eexists. splits; eauto.
              splits; eauto.
              simpl. unfold Coqlib.nat_of_Z.
              rewrite Z2Nat.id. 2: { clear. pose proof Int.unsigned_range domain. tauto. }
              rewrite Int.repr_unsigned.
              now rewrite Edomain. 
            }
            

            (* os_code_defs.x ′ =ₑ OSUnMapTbl ′[(port_ptr ′ .. OSEventTbl) [os_code_defs.y ′]];ₛ *)
            unfold AOSEventTbl.
            naive pure intro.
            hoare_split_pure_all.
            clear H.
            hoare forward.
            4: eauto.
            rewrite y_ble_max; auto.
            rewrite Hlen_etbl_EVENT_TBL_SIZE; simpl; auto.
            simpl; rewrite nth_val_etbl; rewrite erow_ble_max; auto.
            auto.
            auto.
            auto.
            simpl; rewrite unmap_erow; rewrite x_ble_max; auto.
            rewrite unmap_erow.


            (* prio ′ =ₑ (os_code_defs.y ′ ≪ ′ 3) +ₑ os_code_defs.x ′;ₛ *)
            hoare forward.
            rewrite y_ble_max; auto.
            rewrite x_ble_max; auto.
            rewrite int_ltu_3_iwordsize.
            simpl val_inj.

            
            (* ptcb ′ =ₑ OSTCBPrioTbl ′ [prio ′];ₛ *)
            hoare forward.
            rewrite prio_ble_max; auto.
            rewrite nth_val_ptbl.
            easy.
            rewrite nth_val_ptbl.
            

            (* ptcb ′ .. OSTCBMsg =ₑ eptrconst OS_PARTITION_MESSAGE_COME_ptr;ₛ *)
            hoare forward.
            {
              hoare abs lift pre.
              eapply assign_rule_struct_aop_typeneq.
              - split; intros.
                + sep autocancel. apply H.
                + sep pauto.
              - reflexivity.
              - reflexivity.
              - reflexivity.
              - reflexivity.
              - reflexivity.
              - reflexivity.
              - intros. auto.
              - intros. auto.
              - intros. auto.
              - intros. instantiate (2:= Tptr Tint32).
                simpl. destruct s0 as [[[[[[]]]]]]. simpl. destruct p.
                splits; eauto.
              - apply assign_type_match_true; auto.
              - simpl. lia.
              - simpl. reflexivity.
              - intros. eexists. sep autocancel. cbv. tauto.
            }
           
            
            
            assert (Int.eq ($ OS_STAT_PORT&ᵢ$ OS_STAT_ILLEGAL)
            ($ OS_STAT_RDY) = true) as Hillegal_rdy_neq by reflexivity.
            assert (Int.eq ($ OS_STAT_PORT&ᵢ$ OS_STAT_SUSPEND)
            ($ OS_STAT_RDY) = true) as Hsus_rdy_neq by reflexivity.

            (* If ( (ptcb ′ .. OSTCBStat &ₑ ′ OS_STAT_ILLEGAL) ==ₑ′ OS_STAT_RDY &&ₑ
                  (ptcb ′.. OSTCBStat &ₑ ′ OS_STAT_SUSPEND) ==ₑ′ OS_STAT_RDY) *)
            apply corecommu_rules.ift_nonzero_rule.
            {
              intros. exists Int.one.
              sep split. 2: { clear. mauto. }
              symbolic_execution.
              {
                clear - Hisptr_x17 Hisptr_x16 Hisptr_x15 Hisptr_x14 Hi7_range Hi6_range Hi5_range Hi4_range Hi3_range Hi1_range Hi0_range.
                pauto.
              }
              {
                clear - Hisptr_x17 Hisptr_x16 Hisptr_x15 Hisptr_x14 Hi7_range Hi6_range Hi5_range Hi4_range Hi3_range Hi1_range Hi0_range.
                pauto. 
              }
            } 
           
            (* OSRdyGrp ′ =ₑ OSRdyGrp ′ |ₑ ptcb ′ .. OSTCBBitY;ₛ*)
            hoare forward.
            {
              rewrite byte_max_unsigned_val.
              clear - rgrp'_le255.
              pauto.
            }
            {
              clear - Hisptr_x17 Hisptr_x16 Hisptr_x15 Hisptr_x14 Hi7_range Hi6_range Hi5_range Hi4_range Hi3_range Hi1_range Hi0_range. 
              pauto.
            }
            
            
            (* OSRdyTbl ′ [ptcb ′ .. OSTCBY] =ₑ OSRdyTbl ′ [ptcb ′ .. OSTCBY] |ₑ ptcb ′ .. OSTCBBitX *)
            hoare name lift AOSRdyTbl pre.
            unfold AOSRdyTbl.
            naive pure intro.
            clear H.
            assert (Hi3_le_8:Int.unsigned i3 < 8).
            {
              clear - HTCBNode_P.
              unfold TCBNode_P in HTCBNode_P.
              unfold RL_TCBblk_P in HTCBNode_P.
              simpljoin. 
              inverts H0.
              inverts H6.
              inverts H1.
              inverts H4.
              clear - H16 H8.
              eapply math_64_le_8; eauto.
            }
            hoare name lift Aop A_dom_lenv pre.
            apply assign_rule_array_g_aop with (tp2:=char_t)(te2:=char_t).
            {
              reflexivity.
            }
            {
              reflexivity.
            }
            {
              intros. symbolic_execution.
              {
                clear - Hisptr_x17 Hisptr_x16 Hisptr_x15 Hisptr_x14 Hi7_range Hi6_range Hi5_range Hi4_range Hi3_range Hi1_range Hi0_range. 
                pauto.
              }
              {
              rewrite Hlen_rtbl_rdy_tbl_size.
              now simpl.
              }
              {
                eapply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match; eauto.
                rewrite Hlen_rtbl_rdy_tbl_size.
                unfold OS_RDY_TBL_SIZE.
                apply Z2Nat.inj_lt.
                clear. pose proof Int.unsigned_range i3. tauto.
                lia. easy.
              }
              {
                clear - Hisptr_x17 Hisptr_x16 Hisptr_x15 Hisptr_x14 Hi7_range Hi6_range Hi5_range Hi4_range Hi3_range Hi1_range Hi0_range. 
                pauto.
              }
              {
                lets Htmp:  nthval'_has_value Hrtbl_type_match Hlen_rtbl_rdy_tbl_size.
                instantiate (1:=(Z.to_nat (Int.unsigned i3))) in Htmp.
                destruct Htmp.
                apply Z2Nat.inj_lt.
                clear. pose proof Int.unsigned_range i3. tauto.
                unfold OS_RDY_TBL_SIZE. lia. easy.
                simpljoin.
                rewrite H0. auto.
              } 
            }
            {
              intros. symbolic_execution.
              clear - Hisptr_x17 Hisptr_x16 Hisptr_x15 Hisptr_x14 Hi7_range Hi6_range Hi5_range Hi4_range Hi3_range Hi1_range Hi0_range. 
              pauto.
            }
            {
              tauto. 
            }
            {
              now simpl. 
            }
            {
              now apply assign_type_match_true.
            }
            {
              rewrite Hlen_rtbl_rdy_tbl_size. now simpl.
            }
            {
              intros. sep auto. 
            }
          }

        hoare name lift Astruct tcbdllseg1 pre.
        apply tcbdllseg1_node_join_pre1; auto.
        {
          clear - Hisptr_x17 Hisptr_x16 Hisptr_x15 Hisptr_x14 Hi7_range Hi6_range Hi5_range Hi4_range Hi3_range Hi1_range Hi0_range. 
          pauto.
        }
        {
          unfolds. simpl. tauto. 
        }

        apply tcbdllseg1_to_tcbdllseg_pre1.
        assert (receivePortMsg_tcbls_ecbls (firstn (S n) cportpl) ecbls tcbls
            tcbls' false) as Htmp.
            {
              eapply receivePortMsg_tcbls_ecbls_one_step_false; eauto.
              eapply receivePortMsg_tcbls_ecbls_abort; eauto.
              constructor.
            }
        hoare name lift abstcblist absecblist oscoreportpl pre.
        hoare abs lift pre.
        eapply abscsq_rule.
        - apply noabs_oslinv.
        - eapply receivePortMsg_aspec_abt; eauto. can_change_aop_solver'.
        - apply absinfer_eq.
        - apply absabort_rule.    
      }
    }
  } 
  naive pure intro.
  eapply backward_rule1.
  intros.
  eapply sep_aconj_r_aisfalse_to_astar.
  2: apply H0.
  intros.
  symbolic_execution.
  destruct (nth_error cportpl v'); auto.
  destruct (nth_error cportpl v'); simpl; auto.
  destruct a ; auto.
  destruct (nth_error cportpl v'); auto.
  simpl. destruct a; auto.

  naive pure intro.
  destruct H7.
  2:{
    destruct (option_addrval_to_val (nth_error cportpl v')); simpl in H7; try discriminate.
    destruct a; discriminate.
  }
  destruct (nth_error cportpl v') eqn:E.
  simpl in H7. destruct a; discriminate.
  clear H7.
  apply nth_error_None in E.
  assert (v'=length cportpl) as Htmp by lia.
  subst v'.
  rewrite firstn_all in H0.
  subst H.

  (*<|| receivePortMsg_aspec (|nil|);; s ||> *)
  unfold EvtInv.
  naive pure intro.
  hoare name lift Aop abstcblist absecblist oscoreportpl pre.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply receivePortMsg_aspec_cont; eauto. can_change_aop_solver'.
  apply absinfer_eq.

  (*RETURN ′ OS_NO_ERR *)
  eapply rete_rule.
  intros. split.
  2: symbolic_execution.
  sep normal. sep eexists.
  sep autocancel.
  sep name lift PartitionInv.
  eapply fold_PartitionInv_frm.
  sep cancel PartitionInv_part2.
  unfold PartitionInv_part1.
  sep normal.
  sep eexists.
  sep autocancel.
  unfold AOSCorePortPtrList.
  sep normal.
  sep autocancel.
  sep split; eauto.
  unfold RLH_PortPtrINecb.
  splits; auto.
Qed.
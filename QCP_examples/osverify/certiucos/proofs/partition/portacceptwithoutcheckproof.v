Require Import ucos_include.
Require Import Lia.

Require Import aux_pureLib.

Require Import abs_op_corecommu_rules.
Require Import corecommu_sep_added.
Require Import corecommu_tactics.
Require Import partition_rules.
Require Import partition_seprules.
Require Import partition_absrules.
Require Import partition_symrules.
Require Import partition_tactics.
Require Import corecommu_rules.
Require Import partinv_lemmas.

Open Scope code_scope.

Open Scope int_scope.

Ltac hoare_ex_intro ::=
  repeat match goal with
    | |- {| _, _, _, _, _, _ |} |- _  {{ EX _, _ }} _ {{ _ }} =>
      apply ex_intro_rule; intros 
  end.

Ltac rename_partitionvars ::=
  match goal with 
  | |- context [AOSDomainPortPtrList ?v ?v1 ?v2] =>
        rename v into dportlptr; rename v1 into dportl; rename v2 into dportmsgll end;
  match goal with 
  | |- context [Hdomainportl ?v] => rename v into dportls  end;
  match goal with 
  | |- context [AOSKernelPortIDTbl ?v ?v'] =>
        rename v into kportvl; rename v' into kportl end;
  match goal with 
  | |- context [Hkernelport ?v] => rename v into kportls end;
  match goal with 
  | |- context [AOSChannelIDTbl ?v ?v0 ?v1] =>
        rename v into chanvl ; rename v0 into chanl; rename v1 into chandstkportll end;
  match goal with 
  | |- context [Hchannell ?v] => rename v into chanls end;
  match goal with 
  | H: context [RL_PortAttr ?v _] |- _ => rename v into dpptrl end;
  match goal with 
  | H: context [RH_TCBList_ECBList_P ?v _ _ ] |- _ => rename v into ecbls end;
  match goal with 
  | H: context [RLH_OtherPortPtrList ?v ?v0 ?v1 ?v2 ] |- _ => 
        rename v into otherppl; rename v0 into otherpl;
        rename v1 into othermsgll; rename v2 into dportls2 end;
  match goal with 
  | H: context [RLH_Domainportl _ _ _ ?v ] |- _ => 
        rename v into dportls1 end.


Lemma OSPortAcceptWithoutCheck_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSPortAcceptWithoutCheck vl logicl OSPortAcceptWithoutCheckPre ct->
      Some r =
      BuildRetI os_internal OSPortAcceptWithoutCheck vl logicl OSPortAcceptWithoutCheckPost ct->
      exists t d1 d2 s,
        os_internal OSPortAcceptWithoutCheck = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  simpl app.

  rename v'2 into s.
  rename v'3 into er.
  rename v'4 into msgptr.
  rename v'5 into pptr.
  rename v'6 into vsem.
  inversion H. subst x0 x. clear H.
  subst logicl.

  unfold port_acc_without_chk.
  cbn [spec_code_cons].
  
  (* ENTER_CRITICAL;ₛ
  If (port_ptr ′ .. os_code_defs.direction !=ₑ ′ DESTINATION)
  {EXIT_CRITICAL;ₛ
  RETURN 〈 char_t 〉 ′ OS_PORT_ERR_DIRECTION_TYPE};ₛ
  EXIT_CRITICAL;ₛ *)
  partition_enter_trinv.
  hoare name lift osdomainportid pre.
  hoare name lift Aop pre.
  destruct (get dportls pptr) eqn: Hpptr.
  2:{
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply port_indomainport_none_abt; eauto.
      can_change_aop_solver'.
    }
    eapply absabort_rule.
  }
  destruct b as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
  assert (p <> Z.to_nat DNUM \/ p = Z.to_nat DNUM) by tauto.
  destruct H13; [ | subst p].
  {
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply port_indomainport_none_abt'; eauto.
      can_change_aop_solver'.
    }
    eapply absabort_rule.
  }

  (* find port_ptr -> direction, mode *)
  assert (get dportls1 pptr = Some (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5)).
  { eapply pptr_in_dportls1; eauto. }

  unfold RLH_PortPtrINecb in H5; destruct H5.
  assert (exists n dport msgl,
    nth_error dportl n = Some dport /\ nth_error dportmsgll n = Some msgl /\
    nth_error dpptrl n = Some pptr /\ DomainportNode_P dport (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5) msgl).
  { eapply RLH_Domainportl_abs_getsome; eauto. }

  simpljoin1.
  rename x into n. rename x0 into dport. rename x1 into msgl.
  apply nth_error_split in H15 as (dportl1 & dportl2 & ? & ?).
  apply nth_error_split in H16 as (dportmsgll1 & dportmsgll2 & ? & ?).
  subst dportl dportmsgll.
  unfold AOSDomainPortPtrList.
  hoare normal pre.
  hoare name lift dmportp_sll pre.
  eapply backward_rule1.
  { eapply dmportp_sllseg_app'_frm; eauto. }
  cbn [dmportp_sllseg].
  hoare normal pre; pure intro.
  rename v'22 into pptr.

  (* If (port_ptr ′ .. os_code_defs.direction !=ₑ ′ DESTINATION) *)
  eapply seq_rule.
  {
    eapply ift_rule''; [symbolic_exe_port|idtac].
    hoare normal pre; pure intro. destruct d.
    2:{ instantiate (1:=Afalse). exfalso. clear - H15. pauto. }
    clear H15 H19 H23.
    hoare name lift osdomainportid pre.
    hoare name lift Aop pre.
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply port_indomainport_cont; eauto.
    can_change_aop_solver'.
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_choice1; eauto.
    1,2: can_change_aop_solver'.
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply portacc_err_dire_end; eauto.
    can_change_aop_solver'.
    partition_exit_trinv.

    (* RETURN 〈 char_t 〉 ′ OS_PORT_ERR_DIRECTION_TYPE *)
    eapply rete_rule.
    eapply inline_tactics.sep_infer_conjI.
    split.
    2: instantiate (1:=(V$ OS_PORT_ERR_DIRECTION_TYPE)).
    {
      intros.
      sep normal; sep eexists; sep autocancel.
      sep pauto.
      simpl; eauto.
    }
    symbolic_execution.
  }

  hoare forward. hoare normal pre; pure intro.
  destruct d.
  {
    exfalso. clear - H15.
    unfold notint, val_inj, SOURCE, DESTINATION in H15;
    rewrite Int.eq_false in H15; destruct H15; pauto; inverts H.
  }
  assert (OSPortAttrTblDir pptr = (V$ DESTINATION)) as Hdir.
  {
    eapply RL_PortAttr_dir_DES ;eauto.
    apply nth_error_middle.
  }
  (* EXIT_CRITICAL *)
  partition_exit_trinv.
  clear - H1 Hdir.

  (* ENTER_CRITICAL;ₛ
  If (msg_ptr ′ ==ₑ 〈 OSMsg_t ∗ 〉 NULL)
  {EXIT_CRITICAL;ₛ
  RETURN 〈 char_t 〉 ′ OS_PORT_MSG_ARG_NULL};ₛ
  EXIT_CRITICAL;ₛ *)
  partition_enter_trinv.
  hoare name lift osdomainportid pre.
  hoare name lift Aop pre.
  destruct (get dportls pptr) eqn: Hpptr.
  2:{
    hoare abscsq; [apply noabs_oslinv | | ].
    eapply port_indomainport_none_abt; eauto.
    can_change_aop_solver'.
    eapply absabort_rule.
  }
  destruct b as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
  assert (p <> Z.to_nat DNUM \/ p = Z.to_nat DNUM) by tauto.
  destruct H12; [ | subst p].
  {
    hoare abscsq; [apply noabs_oslinv | | ].
    eapply port_indomainport_none_abt'; eauto.
    can_change_aop_solver'.
    eapply absabort_rule.
  }
  hoare forward; pauto.
  {
    instantiate (1:=Afalse).
    hoare normal pre; pure intro.
    hoare abscsq; [apply noabs_oslinv | | ].
    eapply port_indomainport_cont; eauto.
    can_change_aop_solver'.
    hoare abscsq; [apply noabs_oslinv | | ].
    eapply absinfer_choice2; [ | | intros ? Hs; apply Hs ].
    1,2: can_change_aop_solver'.
    hoare abscsq; [apply noabs_oslinv | | ].
    eapply absinfer_choice1; [ | | intros ? Hs; apply Hs ].
    1,2: can_change_aop_solver'.
    destruct H1 as [? | [? ?]]; subst.
    {
      hoare abscsq; [apply noabs_oslinv | | ].
      eapply portacc_err_msgnull_end.
      can_change_aop_solver'.
      partition_exit_trinv.
      
      (* RETURN 〈 char_t 〉 ′ OS_PORT_MSG_ARG_NULL *)
      eapply rete_rule.
      eapply inline_tactics.sep_infer_conjI.
      split.
      2: instantiate (1:=(V$ OS_PORT_MSG_ARG_NULL)).
      {
        intros.
        sep normal; sep eexists; sep autocancel.
        sep pauto.
        simpl; eauto.
      }
      symbolic_execution.
    }
    destruct x; contradiction.
  }
  hoare forward. hoare normal pre; pure intro.
  partition_exit_trinv.
  clear - H1 H12 Hdir.
  destruct H1 as [? | [? ?]]; subst.
  { simpl in H12; destruct H12; discriminate. }
  rename x into msgptr; clear H12.

  partition_enter_trinv.
  hoare name lift osdomainportid pre.
  hoare name lift Aop pre.
  destruct (get dportls pptr) eqn: Hpptr.
  2:{
    hoare abscsq; [apply noabs_oslinv | | ].
    eapply port_indomainport_none_abt; eauto.
    can_change_aop_solver'.
    eapply absabort_rule.
  }
  destruct b as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
  assert (p <> Z.to_nat DNUM \/ p = Z.to_nat DNUM) by tauto.
  destruct H11; [ | subst p].
  {
    hoare abscsq; [apply noabs_oslinv | | ].
    eapply port_indomainport_none_abt'; eauto.
    can_change_aop_solver'.
    eapply absabort_rule.
  }
  hoare abscsq; [apply noabs_oslinv | | ].
  eapply port_indomainport_cont; eauto.
  can_change_aop_solver'.
  hoare abscsq; [apply noabs_oslinv | | ].
  eapply absinfer_choice2; [ | | intros ? Hs; apply Hs ].
  1,2: can_change_aop_solver'.
  hoare abscsq; [apply noabs_oslinv | | ].
  eapply absinfer_choice2; [ | | intros ? Hs; apply Hs ].
  1,2: can_change_aop_solver'.
  
  assert (get dportls1 pptr = Some (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5)).
  { eapply pptr_in_dportls1; eauto. }
  unfold RLH_PortPtrINecb in H3; destruct H3.
  assert (exists n dport msgl,
    nth_error dportl n = Some dport /\ nth_error dportmsgll n = Some msgl /\
    nth_error dpptrl n = Some pptr /\ DomainportNode_P dport (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5) msgl).
  { eapply RLH_Domainportl_abs_getsome; eauto. }
  simpljoin1.
  rename x into n. rename x0 into dport. rename x1 into msgl.
  apply nth_error_split in H13 as (dportl1 & dportl2 & ? & ?).
  apply nth_error_split in H14 as (dportmsgll1 & dportmsgll2 & ? & ?).
  subst dportl dportmsgll.
  unfold AOSDomainPortPtrList.
  hoare normal pre.
  hoare name lift dmportp_sll pre.
  eapply backward_rule1.
  eapply dmportp_sllseg_app'_frm; eauto.
  cbn [dmportp_sllseg].
  hoare normal pre; pure intro.
  rename v'22 into pptr.

  (* kport ′ =ₑ OSKernelPortIDTbl ′ [port_ptr ′ .. portID];ₛ *)
  unfold AOSKernelPortIDTbl.
  hoare normal pre; pure intro.
  assert (exists id kportp kport,
          OS_Port_V_portID dport = Some (Vint32 id) /\
          nth_error kportvl (nat_of_Z (Int.unsigned id)) = Some (Vptr kportp) /\ 
          nth_error kportl (nat_of_Z (Int.unsigned id)) = Some kport /\
          struct_type_vallist_match OS_K_Port kport /\
          OS_K_Port_V_portID kport = Some (Vint32 id) /\
          OS_K_Port_V_dmport kport = Some (Vptr pptr) /\
          OS_K_Port_V_coreNum kport = OS_Port_V_coreNum dport).
  { eapply R_Kernelport_DomainPort_abs_getsome; eauto. }
  simpljoin1.
  unfold DomainportNode_P in H16; simpljoin1.
  unfold Domainport_nat_P in H16; simpljoin1.
  rename x1 into kport. rename x0 into kpptr.
  rewrite H34 in H22; inverts H22.

  eapply seq_rule.
  {
    hoare name lift os_code_defs.kport pre.
    hoare name lift Aop pre.
    eapply assign_rule_lvar.
    { intro; split; intros; apply H22. }
    {
      intros.
      eapply symbolic_lemmas.array_member_rv_g.
      { sep autocancel; apply H22. }
      { go. }
      { eauto. }
      {
        eapply port_id_rv; eauto.
        unfold DomainportNode_P; splits; eauto.
        unfold Domainport_nat_P; do 5 eexists;
        repeat (splits; eauto).
        sep autocancel; apply H22.
      }
      { go. }
      { auto. }
      { unfold PORT_NUMS; clear; mauto. }
      {
        rewrite! Coqlib.nat_of_Z_eq.
        { rewrite int_usign_eq by (apply Int.unsigned_range_2); auto. }
        { unfold PORT_NUMS; lia. }
        pose proof Int.unsigned_range_2 x; lia.
      }
      {
        rewrite H21.
        rewrite! Coqlib.nat_of_Z_eq.
        { rewrite int_usign_eq by (apply Int.unsigned_range_2); auto. }
        { unfold PORT_NUMS; lia. }
        pose proof Int.unsigned_range_2 x; lia.
      }
      2: eauto.
      go.
      apply nth_val_nth_error in H23.
      apply nth_val_nth_val'_some_eq in H23.
      assert ((Z.to_nat (Int.unsigned ($ Z.of_nat ∘ (Int.unsigned x)))) = ∘ (Int.unsigned x)).
      {
        clear.
        rewrite Coqlib.nat_of_Z_eq.
        2: pose proof Int.unsigned_range_2 x; lia.
        rewrite int_usign_eq by (apply Int.unsigned_range_2).
        auto.
  Optimize Proof.
  Optimize Heap.
      }
      rewrite H33; rewrite H23; auto.
    }
    { apply eq_vptr; eauto. }
    intros; sep eexists; sep autocancel; sep pauto.
  }
  rewrite Coqlib.nat_of_Z_eq.
  2: pose proof Int.unsigned_range_2 x; lia.
  rewrite int_usign_eq by (apply Int.unsigned_range_2).
  assert (nth_val' (Z.to_nat (Int.unsigned x)) kportvl = Vptr kpptr).
  { apply nth_val_nth_val'_some_eq; apply nth_val_nth_error; auto. }
  rewrite H22; clear H22.

  (* If (kport ′ ==ₑ 〈 OS_K_Port ∗ 〉 NULL) *)
  hoare forward.
  { destruct kpptr; pauto. }
  {
    hoare normal pre; pure intro.
    instantiate (1:=Afalse).
    exfalso; clear - H22; destruct kpptr; pauto.
  }
  hoare forward.
  rename x into portid.
  hoare normal pre; pure intro. clear H22.
  rewrite H16 in H28.
  unfold OS_K_Port_V_coreNum in H28; simpl in H28; inverts H28.
  unfold OS_K_Port_V_portID in H26; simpl in H26; inverts H26.
  unfold OS_K_Port_V_dmport in H27; simpl in H27; inverts H27.
  
  (* If (kport ′ .. channel ==ₑ 〈 OS_Channel ∗ 〉 NULL) *)
  hoare name lift kportNode_P pre.
  eapply backward_rule1.
  { eapply kportNode_P_getsome_frm; eauto. }
  hoare normal pre; pure intro.
  rename v'22 into kportpb. rename v'24 into kportpl1. rename v'25 into kportpl2.
  rename v'26 into kportl1. rename v'27 into kportl2. rename x1 into channel.

  assert (exists kporth, 
    KernelportNode_P (Vint32 portid :: Vint32 i1 ::
      Vptr pptr :: channel :: V$ DNUM :: Vint32 i :: x8 :: nil) kporth /\
    get kportls (kportpb, Int.zero) = Some kporth).
  {
    eapply RLH_Kernelport_abs_getsome; eauto.
    rewrite H28; auto.
  }
  simpljoin1.
  destruct x as [[[[? ?] ?] ?] ?].
  unfold KernelportNode_P in H22; simpljoin1.
  unfold Kernelport_nat_P in H22; simpljoin1.
  unfold OS_K_Port_V_portID in H22; simpl in H22;
    inverts H22; rename x into portid.
  unfold OS_K_Port_V_status in H50; simpl in H50; inverts H50.
  unfold Kernelport_dmport_P in H27; destruct o;
  unfold OS_K_Port_V_dmport in H27; simpl in H27;
    inverts H27; rename a into portp.
  unfold OS_K_Port_V_coreNum in H48; simpl in H48; inverts H48.
  rewrite int_usign_eq in *.
  2,3,4,5,6,7: clear; pose proof dnum_range; mauto.

  eapply seq_rule.
  {
    eapply ift_rule''; [symbolic_exe_port|idtac].
    {
      destruct H38 as [H38 | [? H38]]; subst channel; auto.
      simpl; destruct x; auto.
    }
    hoare normal pre; pure intro.
    destruct H38 as [H38 | [? H38]]; subst channel; simpl in H22.
    2: destruct x; simpl in H22; contradiction.
    clear H22 H27 H47.
    hoare abscsq; [apply noabs_oslinv | | ].
    eapply absinfer_choice1; [ | | intros ? Hs; apply Hs ].
    1,2: can_change_aop_solver'.
    hoare name lift oskportid pre.
    hoare name lift osdomainportid pre.
    hoare name lift Aop pre.
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply portacc_err_nochannel_end; eauto.
      {
        instantiate (1:=∘ (Int.unsigned x1)).
        instantiate (1:=(kportpb, Int.zero)).
        unfold Kernelport_channel_P in H46; destruct o0;
        unfold OS_K_Port_V_channel in H46; simpl in H46; inverts H46.
        auto.
      }
      can_change_aop_solver'.
    }
    instantiate (1:=Afalse).
    partition_exit_trinv.
    {
      unfold dmportp_sll.
      sep autocancel.
      unfold AOSKernelPortIDTbl.
      sep normal; sep eexists; sep autocancel.
      sep split; eauto.
      eapply kportNode_P_compose; eauto.
      rewrite H44; auto.
    }
    { good_frm_sovler. }

    (* RETURN 〈 char_t 〉 ′ OS_ERR_PORT_NO_CHANNEL  *)
    eapply rete_rule.
    eapply inline_tactics.sep_infer_conjI.
    split.
    2: instantiate (1:=(V$ OS_ERR_PORT_NO_CHANNEL)).
    {
      intros.
      sep normal; sep eexists; sep autocancel.
      sep pauto.
      simpl; eauto.
    }
    symbolic_execution.
  }
  hoare forward. hoare normal pre; pure intro.
  destruct H38 as [H38 | [? H38]]; subst channel; simpl in H22.
  { destruct H22; tryfalse. }
  unfold Kernelport_channel_P in H46; destruct o0; 
  unfold OS_K_Port_V_channel in H46; simpl in H46; inverts H46.
  clear H22. rename a into chanptr.

  hoare abscsq; [apply noabs_oslinv | | ].
  eapply absinfer_choice2; [ | | intros ? Hs; apply Hs ].
  1,2: can_change_aop_solver'.

  assert (R_KernelPortIDTbl_ChannelIDTbl_chan_Vptr
    (kportpb, Int.zero) (Vint32 portid :: Vint32 i1 :: Vptr portp :: Vptr chanptr
     :: V$ DNUM :: Vint32 x1 :: x8 :: nil) chanvl chanl chandstkportll kportls dportls1 dportls2).
  {
    eapply R_KernelPortIDTbl_ChannelIDTbl_abs_getsome; eauto.
    { rewrite H44; auto. }
    unfold OS_K_Port_V_channel; simpl; eauto.
  }
  unfold R_KernelPortIDTbl_ChannelIDTbl_chan_Vptr in H22; simpljoin1.
  unfold OS_K_Port_V_channelID in H22; simpl in H22;
    inverts H22; rename x into chanid.
  unfold OS_K_Port_V_channel in H27; simpl in H27;
    inverts H27; rename x0 into chanptr.
  unfold AOSChannelIDTbl.
  hoare normal pre; pure intro.

  hoare name lift ChannelNode pre.
  eapply backward_rule1.
  { eapply ChannelNode_getsome_frm; eauto. }
  unfold node; hoare normal pre; pure intro.
  rename v'31 into chanpb. rename v'22 into chanpl1. rename v'26 into chanpl2.
  rename v'24 into chanl1. rename v'27 into chanl2.
  rename v'25 into chandstkportll1. rename v'28 into chandstkportll2.
  unfold KPort, port_id, addrval, port_coreNum in H26, H49;
  rewrite H26 in H49; inverts H49.
  rename x10 into pptr.
  unfold OS_Channel_V_dstPortsNum in H58; simpl in H58; inverts H58.
  unfold OS_Channel_V_dstPortsHead in H57; simpl in H57; inverts H57.
  
  destruct d.
  {
    assert (OSPortAttrTblDir pptr = (V$ SOURCE)).
    {
      eapply RL_PortAttr_dir_SOURCE; eauto.
      eapply nth_error_middle.
      unfold DomainportNode_P; splits; eauto.
      unfold Domainport_nat_P; do 5 eexists; repeat (splits; eauto).
    }
    rewrite Hdir in H49.
    exfalso; clear - H49; tryfalse.
  }
  unfold Domainport_direction_P in H29.
  destruct H29 as [H29 Hnx].
  unfold OS_Channel_V_channelID in H48; simpl in H48; inverts H48.
  rename x7 into dstkportpl.

  assert (exists chanh,
    ChannelNode_P otherppl (Vint32 chanid :: Vint32 i1
      :: Vint32 v'30 :: Vint32 i :: v'29 :: x15 :: x16 :: x17 :: nil)
      chanh (chanpb, Int.zero) dstkportpl kportls dportls1 dportls2 /\
    get chanls (chanpb, Int.zero) = Some chanh).
  { eapply RLH_Channel_app_cons; eauto. }
  simpljoin1. destruct x as [[[cid cdn] cdstkp] ct'].

  unfold ChannelNode_P in H48; simpljoin1.
  rename H57 into Hnodup_dk.
  unfold Channel_nat_P in H48; simpljoin1.
  unfold OS_Channel_V_channelID in H48; simpl in H48;
    inverts H48; rename x into chanid.
  unfold OS_Channel_V_dstPortsNum in H58; simpl in H58;
    inverts H58; rename x0 into dpnum.
  
  destruct ct'; simpljoin1.
  2:{ (* 核间通信 *)
    unfold Channel_type_P in H52; simpljoin1.
    unfold OS_Channel_V_semaphore in H48; simpl in H48; inverts H48.
    hoare abscsq; [apply noabs_oslinv | | ].
    eapply absinfer_choice1; [ | | intros ? Hs; apply Hs ].
    1,2: can_change_aop_solver'.
    
    (* ASSERT corecommu_ (Vptr pptr) vsem;; *)
    assert (vsem <> (V$ Z.of_nat c) \/ vsem = (V$ Z.of_nat c)) by tauto.
    hoare name lift oschannelid pre.
    hoare name lift oskportid pre.
    hoare name lift osdomainportid pre.
    hoare name lift Aop pre.
    destruct H48.
    {
      hoare abscsq; [apply noabs_oslinv | | ].
      eapply corecommu_sem_abt; eauto.
      can_change_aop_solver'.
      eapply absabort_rule.
    }
    subst vsem.
    hoare abscsq; [apply noabs_oslinv | | ].
    eapply corecommu_sem_cont; eauto.
    can_change_aop_solver'.

    unfold Semacc_err, Semacc_succ.
    cbn [spec_code_cons].
    assert ($ Z.of_nat (Z.to_nat (Int.unsigned ($ Z.of_nat c))) = ($ Z.of_nat c)) as Hsem.
    {
      rewrite Z2Nat.id by apply Int.unsigned_range.
      apply Int.repr_unsigned.
    }

    (* semaphore ′ =ₑ (〈 OS_Channel ∗ 〉 kport ′ .. channel) .. semaphore;ₛ *)
    eapply seq_rule.
    {
      hoare name lift semaphore pre.
      hoare name lift Aop pre.
      eapply assign_rule_lvar.
      { intro; split; intros; apply H48. }
      {
        intros.
        eapply struct_member_off_rv.
        3:{
          instantiate (1:=(chanpb, Int.zero)).
          assert (Vptr (chanpb, Int.zero) = nth_val' 3 (Vint32 portid
          :: Vint32 chanid :: Vptr pptr :: Vptr (chanpb, Int.zero)
             :: V$ DNUM :: Vint32 x1 :: x8 :: nil)) by (simpl; auto).
          rewrite H57; clear H57.
          eapply symbolic_lemmas.cast_rv_tptr.
          eapply kport_channel_rv; eauto.
          sep cancel kport. sep cancel Astruct'. eapply H48.
          auto.
  Optimize Proof.
  Optimize Heap.
        }
        3:{
          unfold Astruct in H48 at 1.
          unfold OS_Channel in H48 at 1.
          unfold Astruct' in H48 at 1.
          sep normal in H48; sep lift 8%nat in H48.
          assert (Z.of_nat (typelen char_t) = 1) by (clear; simpl; lia).
          rewrite H57 in H48.
          assert (((Int.zero +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1 = $ 3) by (clear; mauto).
          rewrite H66 in H48.
          instantiate (5:= ($ 3)).
          unfold get_off_addr, fst, snd.
          rewrite Int.add_zero_l.
          apply H48.
        }
        auto.
        auto.
        instantiate (1:=⌞ channelID @ char_t; srcPortsNum @ char_t ; dstPortsNum @ char_t;
        semaphore @ char_t; dstPortsHead @ OS_K_Port ∗; dstPortsTail @
        OS_K_Port ∗; srcPort @ OS_K_Port ∗; OSEventPtr @ (Void) ∗ ⌟).
        unfold OS_Channel; eauto.
        all: go. pauto.
      }
      eapply eq_int; tauto.
      sep auto.
    }

    (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
    {CSLSEMACC (semaphore ′, resource_get_res ′);ₛ
    If (resource_get_res ′ ==ₑ NULL)
    {EXIT_CRITICAL;ₛ
    RETURN 〈 char_t 〉 ′ OS_CHANNEL_ERR_BEING_USED}};ₛ *)
    hoare forward.
    pauto. pauto. pauto.
    {
      hoare normal pre; pure intro.
      clear H48 H57 H66.
      hoare name lift resource_get_res pre.
      hoare name lift Aop pre.

      (* CSLSEMACC ( semaphore ′, resource_get_res ′) *)
      eapply seq_rule.
      {
        eapply cslsemacc_rule'.
        can_change_aop_solver'.
        { rewrite Z2Nat.id. 1,2: eapply Int.unsigned_range_2. }
        { rewrite Hsem. symbolic execution. pauto. }
        {
          unfold p_local, CurLINV, LINV, OSLInv. intros.
          sep normal in H48; sep destruct H48; sep split in H48.
          sep auto. splits; eauto.
          all: destruct H57 as [? [? [? [? [? ?]]]]]; auto.
        }
        {
          unfold p_local, CurLINV, LINV, OSLInv. intros.
          sep normal in H48; sep destruct H48; sep split in H48.
          sep auto. splits; eauto.
          all: destruct H57 as [? [? [? [? [? ?]]]]]; auto.
        }
      }
      eapply disj_rule'.
      instantiate (1:=Afalse).
      {
        hoare forward. hoare normal pre; pure intro.
        partition_exit_trinv.
        unfold AOSKernelPortIDTbl, AOSChannelIDTbl, dmportp_sll.
        sep pauto; sep autocancel.
        eapply kportNode_P_compose; eauto.
        rewrite H44; auto.
        sep autocancel.
        eapply ChannelNode_compose; eauto.
        rewrite H59; auto.
        rewrite H60; auto.
        unfold OS_Channel_V_dstPortsHead; simpl; eauto.
        unfold OS_Channel_V_dstPortsNum; simpl; eauto.
        pauto.
        sep pauto.
        good_frm_sovler.
        instantiate (1:=Afalse).

        (* RETURN 〈 char_t 〉 ′ OS_CHANNEL_ERR_BEING_USED *)
        eapply rete_rule.
        eapply inline_tactics.sep_infer_conjI.
        split.
        2: instantiate (1:=(V$ OS_CHANNEL_ERR_BEING_USED)).
        {
          intros.
          sep normal; sep eexists; sep autocancel.
          sep pauto.
          simpl; eauto.
        }
        symbolic_execution.
        destruct H48.
        { eapply astar_l_afalse_elim. apply H48. }
        sep split in H48.
        exfalso; clear - H57; mauto.
      }

      eapply ift_rule''.
      intros; symbolic execution.
      hoare normal pre; pure intro.
      instantiate (1:=Afalse).
      exfalso; clear - H48; mauto.
    }
    eapply disj_rule; hoare normal pre; pure intro.
    2: exfalso; rewrite H52 in H48; clear - H48; mauto.
    hoare forward. hoare forward.
    hoare normal pre; pure intro. clear H68 H48 H57 H66.

    hoare lift 16%nat pre.
    eapply backward_rule1.
    intros. eapply disj_split in H48. eapply H48.
    eapply disj_rule; hoare normal pre; pure intro.
    2:{ (* QUEUE *)
      unfold Domainport_Portt_P in H30; destruct p5; simpljoin1.
      (* sample is false *)
      rewrite H75 in H48; inverts H48.
      clear H75.
      rewrite H69 in H74; inverts H74; rename n into sz.
      rename v'22 into qend. rename v'24 into qin.
      rename v'25 into qout. rename v'27 into qentries.
      rename v'23 into qstart.

      destruct qstart as (qstart_b & qstart_i).
      unfold Qport_msg_ptrs_P in H71.
      destruct H71 as [H71_ [H71_0 [z1 [z2 H71]]]].
      subst qstart_i.
      unfold get_off_addr in H71, H71_0.
      cbn [fst snd] in *.
      destruct H71 as [? [? H71]].
      assert (Z.of_nat (typelen OSMsg_t) = 33).
      { clear. simpl. lia. }
      rewrite H75 in *; clear H75.
      subst qout qend qin.
      rewrite ! Int.add_zero_l. rewrite Int.add_zero_l in *.
      destruct msgptr as [msg_b msg_i].
      destruct H71 as [[H71_z1_0 H71_z1_1] [H71_z2_0 H71_z2_1]].

      rename v'28 into invalid_msg.
      destruct msgl.
      2:{
        rename v into msg.

        (* IF (port_ptr ′ .. mode ==ₑ ′ QUEUE) *)
        eapply seq_rule.
        {
          eapply if_rule2'.
          {
            symbolic_exe_port.
            unfold DomainportNode_P. splits; eauto.
            unfold Domainport_nat_P. do 5 eexists; repeat (splits; eauto).
            instantiate (2:=DestinationP next). unfold Domainport_direction_P. auto.
            instantiate (2:=QueuePort sz msgl). unfold Domainport_Portt_P. splits; eauto.
          }
          2:{ (* sample is false *)
            hoare normal pre; pure intro.
            instantiate (1:=Afalse).
            exfalso; clear - H30; mauto.
          }
          hoare normal pre; pure intro.
          clear H30 H74 H71.

          (* If (port_ptr ′ .. OSQEntries >ₑ ′ 0) *)
          eapply ift_rule''; [ symbolic_exe_port | ].
          hoare normal pre; pure intro.
          assert (Int.ltu ($ 0) qentries = true) by pauto.
          clear H30 H74 H71.
          assert (∘ (Int.unsigned qentries) > 0)%nat.
          { clear - H75. 
            rewrite <- (Int.repr_unsigned qentries) in H75.
            simpl_intltbool.
            erewrite Int.unsigned_repr in H75 by (apply Int.unsigned_range_2).
            rewrite <- Zabs2Nat.abs_nat_nonneg by lia. lia. }

          (* choose portacc_queue_notnil (|Vptr pptr :: Vptr msgptr :: nil|) *)
          hoare abscsq; [apply noabs_oslinv | | ].
          eapply absinfer_seq.
          3: eapply absinfer_choice2.
          5: intros ? Hs; apply Hs.
          1,2,3,4: can_change_aop_solver'.
          hoare abscsq; [apply noabs_oslinv | | ].
          eapply absinfer_seq.
          3: eapply absinfer_choice1.
          5: intros ? Hs; apply Hs.
          1,2,3,4: can_change_aop_solver'.
          
          (* find qout memory *)
          hoare lift 2%nat pre.
          eapply backward_rule1.
          eapply dmportp_sllseg_qport_msg_ngt0; eauto.
          pure intro.
          inversion H71. clear H71. subst x x0.

          (* msg_ptr ′ .. len =ₑ (port_ptr ′ .. OSQOut) .. len;ₛ *)
          unfold TmrInv, HeapInv'.
          hoare normal pre; pure intro.
          hoare name lift oscoreheapid pre.
          rename v'22 into cHeapl.
          assert (~ In_heapl_addrval cHeapl (msg_b, msg_i) (S (length msg)) \/ In_heapl_addrval cHeapl (msg_b, msg_i) (S (length msg))) as [ | ] by tauto.
          { hoare name lift oschannelid pre.
            hoare name lift oskportid pre.
            hoare name lift osdomainportid pre.
            hoare abscsq; [apply noabs_oslinv | | ].
            eapply portacc_queue_notnil_abt; eauto.
            can_change_aop_solver'.
            apply absabort_rule. }
          
          hoare name lift AOScoreheapl pre.
          eapply backward_rule1.
          eapply port_split_coreheapl; eauto.
          naive pure intro.

          rename v'22 into cheapl1. rename v'25 into cheapl2.
          rename v'26 into ori_msgn. rename v'27 into ori_msg_vl. rename v'28 into ori_msg_vl2.
          simpljoin1.
          destruct ori_msg_vl as [ | ori_len_v ori_msg_vl ].
          simpl in H83; lia.
          hoare name lift Aarray pre.
          unfold Aarray. cbn [Aarray'].
          hoare normal pre.
          hoare name lift msg_ptr pre.
          assert ((msg_b, msg_i) = get_off_addr (msg_b, msg_i) Int.zero).
          { unfold get_off_addr. cbn [fst snd]. rewrite Int.add_zero. reflexivity. }
          rewrite H79 at 2. clear H79.
          hoare name lift Aop pre.
          eapply seq_rule.
          eapply assign_rule_struct_member;[ | 
          clear;intros s'; split;[ intros Hs;exact Hs  |intros Hs;exact Hs ] | go | go | go 
          | idtac | idtac | symbolic_exe_port | idtac .. ].
          go.
          { clear - H74. unfold CHANNEL_CACHE_SZIE in *. cbn.
            rewrite Int.unsigned_repr by mauto.
            assert (Z.of_nat (length msg) <=? 255 = true) by lia.
            rewrite H. auto. }
          apply eq_int;auto.
          { intros ? Hs. subst. sep name lift p_local in Hs. unfold CurLINV. sep auto. }
          hoare normal pre.
          hoare lift 8%nat pre.
          destruct (∘ (Int.unsigned qentries)) as [ | pmsg_l] eqn :?;[ lia | ]. 
          cbn [dmportp_sllseg_qport_msg].
          hoare normal pre; pure intro.

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
            eapply rvl_elim; [sep_get_port_rv | ].
            eapply rvl_elim; [ | apply rvl_nil].
            eapply cast_rv_tint8_tint32. 
            sep_get_port_rv. split;[ | lia]. clear.
            destruct msg; lia.
          }
          { (* ==> pre*)
            intros; unfold_spec.
            sep normal. sep eexists.
            assert ((length msg) = (Z.to_nat (Int.unsigned ($  Z.of_nat (length msg))))).
            { rewrite Int.unsigned_repr. rewrite Nat2Z.id. auto.
              clear - H74. unfold CHANNEL_CACHE_SZIE in *. mauto. }
            rewrite H86 in H85 at 3.
            unfold Aarray at 1. sep cancel Aarray'.
            rewrite <- H79 in H85.
            apply Aarray_split in H85; auto.
            rewrite H86 in H85 at 1. sep cancel Aarray.
            sep name lift aemp_isr_is in H85. 
            sep name lift Ais in H85. sep name lift Aisr in H85.
            eapply elim_aemp_isr_is_prop in H85.
            sep autocancel. sep pauto.
            { unfold get_off_addr. cbn.
              rewrite ! Int.add_zero. auto. }
            { rewrite H79. clear. unfold CHANNEL_CACHE_SZIE. rewrite Z2Nat.id by lia. mauto. }
          }
          { good_frm_sovler. }
          { sep_unfold_funpost. intros. sep destruct H85. sep auto. }
          { sep_unfold_funpre. intros. sep destruct H85. sep auto. }
          { simpl; eauto. }
          unfold getasrt; unfold OS_memcopyPost, OS_memcopyPost'.
          hoare normal pre. pure intro.
          inversion H85. inversion H86. clear H86 H85. 
          subst v'26 v'27 v'28 v'30 v'31 v'32 v'33.
          clear v'25.

          (* ++ port_ptr ′ .. OSQOut;ₛ *)
          rewrite ! Int.add_zero.
          hoare name lift APortStruct pre.
          hoare name lift (Alvarmapsto port_ptr) pre.
          hoare name lift Aop pre.
          eapply seq_rule.
          eapply port_memeber_asgn with (n := 15%nat);[reflexivity | symbolic_exe_port | idtac .. ].
          1,2,3,4,5,6,8: cbn;eauto.
          { eapply eq_vptr; eauto. }
          { intros. sep auto. }

          (* −− port_ptr ′ .. OSQEntries;ₛ *)
          remember (update_nth_val 15 dport (Vptr (qstart_b, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)))) as dport'.
          assert (OS_Port_V_OSQEntries dport' = Some (Vint32 qentries)).
          { unfold OS_Port_V_OSQEntries in *. subst dport'. 
            eapply nth_upd_neqrev; eauto. }
          assert (struct_type_vallist_match' OS_Port_Seg_dls dport').
          { subst dport'. clear - H19.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; auto;
                  destruct dport; simpl in *; tryfalse). }
          eapply seq_rule.
          eapply port_memeber_asgn with (n := 17%nat);[reflexivity | symbolic_exe_port | idtac .. ].
          1,2,3,4,5,6: cbn;eauto.
          { apply eq_int; auto. }
          { cbn. clear - H72 H75 H73. 
            assert (Int.modu ($ 1) ($ Int16.modulus) = ($ 1)) by (clear;mauto).
            rewrite H;clear H.
            assert (Int.unsigned (qentries -ᵢ ($ 1)) <= 65535).
            { rewrite Int_unsigned_minus. 
              rewrite Int.unsigned_repr by (clear;mauto).
              lia.   
  Optimize Proof.
  Optimize Heap.
              simpl_intltbool. 
              rewrite Int.unsigned_repr by (clear;mauto).
              lia. }
            assert (Int.unsigned (qentries -ᵢ $ 1) <=? 65535 = true) by lia.
            rewrite H0. auto. }
          { intros. sep auto. }

          (* If (port_ptr ′ .. OSQOut ==ₑ port_ptr ′ .. OSQEnd) { ... } *)
          subst dport'. 
          assert (Int.modu ($ 1) ($ Int16.modulus) = ($ 1)) by (clear;mauto).
          rewrite H88; clear H88.
          remember(update_nth_val 17 (update_nth_val 15 dport
              (Vptr (qstart_b,  Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))))
                (Vint32 (qentries -ᵢ $ 1))) as dport'.
          assert (OS_Port_V_OSQOut dport' = Some (Vptr (qstart_b, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)))).
          { unfold OS_Port_V_OSQOut in *. subst dport'. 
            eapply nth_upd_neqrev. lia. 
            eapply update_nth; eauto. }
          assert (OS_Port_V_OSQEnd dport' = Some (Vptr (qstart_b, Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)))).
          { unfold OS_Port_V_OSQEnd in *. subst dport'. 
            eapply nth_upd_neqrev. lia. 
            eapply nth_upd_neqrev; eauto. }
          assert (struct_type_vallist_match' OS_Port_Seg_dls dport').
          { subst dport'. clear - H19 H72 H75 H73.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; auto;
                  destruct dport; simpl in *; tryfalse).
            assert (Int.unsigned (qentries -ᵢ ($ 1)) <= 65535).
            { rewrite Int_unsigned_minus. 
              rewrite Int.unsigned_repr by (clear;mauto).
              lia.   
              simpl_intltbool. 
              rewrite Int.unsigned_repr by (clear;mauto).
              lia. }
            assert (Int.unsigned (qentries -ᵢ $ 1) <=? 65535 = true) by lia.
            rewrite int16_max_unsigned_val, H18. auto. }

          (* abs step : qportpend_notnil *)
          hoare name lift oscoreheapid pre.
          hoare name lift oschannelid pre.
          hoare name lift oskportid pre.
          hoare name lift osdomainportid pre.
          hoare abscsq;[apply noabs_oslinv | | ].
          eapply portacc_queue_notnil_cont; eauto.
          can_change_aop_solver'.
          
          (* merge coreheap *)
          hoare name lift AOScoreheapl pre.
          hoare name lift (Aarray (msg_b, msg_i +ᵢ  $ 1)) pre.
          hoare name lift (get_off_addr (msg_b, msg_i) Int.zero) pre.
          hoare remember (1::2::nil)%nat pre.
          rewrite Int.unsigned_repr.
          2: { clear - H74. unfold CHANNEL_CACHE_SZIE in *. mauto. }
          rewrite Nat2Z.id.
          eapply backward_rule1 with (p:= Aarray (msg_b, msg_i)
          (Tarray char_t (S (length msg))) (V$ (Z.of_nat (length msg))::msg) ** H91 ).
          { unfold Aarray, get_off_addr. 
            cbn [Aarray' snd fst]. intros.
            sep cancel H91.
            cbn [typelen].
            assert (Z.of_nat 1 = 1)%Z by lia.
            rewrite H93.
            rewrite Int.add_zero in H92.
            sep auto. }
          subst H91.

          eapply backward_rule1.
          eapply AOScoreheapl_merge; eauto.
          { rewrite <- H83. lia. }
          { rewrite H83. lia. }
          { cbn. 
            assert (Int.unsigned ($ Z.of_nat (length msg)) <= 255).
            { clear - H74. unfold CHANNEL_CACHE_SZIE in *.  
              (* rewrite <- Zabs2Nat.abs_nat_nonneg in * by lia. *)
              assert (length msg <= 32)%nat by lia.
              clear - H.
              rewrite Int.unsigned_repr.
              lia. mauto. }
            assert (Int.unsigned ($ Z.of_nat (length msg)) <=? 255  = true) by lia.
            rewrite H92.
            split; auto.
            apply array_type_vallist_match_app in H84.
            tauto. }
          
          (* merge HeapInv' *)
          hoare name lift AOScoreheapt pre.
          hoare name lift AOScoreheape pre.
          hoare name lift AOScoreheapl pre.
          hoare name lift oscoreheapid pre.
          hoare remember (1::2::3::4::nil)%nat pre.
          eapply backward_rule1.
          {
            instantiate (1:=HeapInv' ** H91).
            intros. sep cancel H91.
            unfold HeapInv'. sep pauto.
            clear - H71. revert H71.
            induction cheapl1; simpl; intros; auto.
            eapply NoDup_cons_iff in H71; simpljoin1.
            eapply NoDup_cons; eauto.
            intro; destruct H.
            clear - H1.
            induction cheapl1; simpl; intros; auto.
            simpl in H1.
            destruct H1; [left|right]; eauto.
          }
          subst H91.

          (* merge qout Aarray *)
          hoare remember (14::16::nil)%nat pre.
          eapply backward_rule1.
          {
            instantiate (1:=Aarray (get_off_addr (qstart_b, Int.mul ($ z1) ($ 33)) (Int.one)) (Tarray Tint8 (nat_of_Z CHANNEL_CACHE_SZIE)) (msg++v'22) ** H91).
            intros.
            rewrite <- H79.
            eapply Aarray_merge; eauto.
            { rewrite H79. clear. unfold CHANNEL_CACHE_SZIE. mauto. }
            sep autocancel.
            unfold get_off_addr, fst, snd.
            rewrite H87; apply H92.
          }
          subst H91.

          (* merge dmportp_sllseg_qport_msg *)
          hoare remember (1::16::17::nil)%nat pre.
          eapply backward_rule1.
          {
            instantiate (1:=dmportp_sllseg_qport_msg
            (qstart_b, Int.mul ($ z1) ($ 33))
            (qstart_b, Int.mul ($ z2) ($ 33))
            (qstart_b, Int.zero)
            (qstart_b, Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33))
            ∘ (Int.unsigned qentries) (msg :: msgl) ** H91).
            intros.
            rewrite Heqn.
            cbn [dmportp_sllseg_qport_msg].
            sep normal; exists v'22. sep autocancel.
            sep pauto.
          }
          subst H91.

          hoare name lift APortStruct pre.
          hoare remember (1::nil)%nat pre.
          eapply forward_rule2.
          {
            instantiate (1:= ((EX dport_new, 
              [|Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)) 
              (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)) = true /\ dport_new = update_nth_val 15%nat dport' (Vptr (qstart_b, Int.zero)) \/ 
              Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)) 
              (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)) = false /\ dport_new = dport' |] ** 
              APortStruct pptr dport_new) ** H91)).
            subst H91.
            eapply forward_rule2.
            eapply ift_rule'';[ symbolic_exe_port | ].
            { (* port_ptr ′ .. OSQOut ==ₑ port_ptr ′ .. OSQEnd *)
              pure intro.
              rewrite peq_true in H91.
              assert (Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
                        (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)) = true) by pauto. 
              clear H91 H92 H93.
              remember (update_nth_val 17 (update_nth_val 15 dport (Vptr (qstart_b, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))))
                        (Vint32 (qentries -ᵢ $ 1)))  as dport'.
              assert (OS_Port_V_OSQStart dport' = Some (Vptr (qstart_b, Int.zero))).
              { unfold OS_Port_V_OSQStart in *. subst dport'. 
                eapply nth_upd_neqrev. lia. 
                eapply nth_upd_neqrev; eauto. }
              hoare name lift APortStruct pre.
              hoare name lift (Alvarmapsto port_ptr) pre.
              hoare name lift Aop pre.
              eapply port_memeber_asgn with (n := 15%nat);[reflexivity | symbolic_exe_port | idtac .. ].
              1,2,3,4,5,6,8: cbn;eauto.
              { eapply eq_vptr;eauto. }
              sep auto.
            }
            intros.
            destruct H91; sep normal in H91; sep normal.
            { exists  (update_nth_val 15 dport' (Vptr (qstart_b, Int.zero))).
              sep auto. left. pauto. }
            exists dport'. sep auto. right.
            destruct (Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
            (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33))).
            { exfalso. rewrite peq_true in H101. destruct H101; tryfalse.  }
            pauto.
          }

          subst H91 dport'.
          intros ? Hs. apply Hs.
        }

        eapply disj_rule.
        2: pure intro; eapply pfalse_rule.
        hoare normal pre; pure intro.
        clear H30 H71 H74.
        eapply disj_rule; hoare normal pre; pure intro.
        2:{
          destruct (Int.ltu ($ 0) qentries) eqn: ?; simpl in H30.
          destruct H30; inverts H30.
          clear H30.
          apply int_ltu_false_eq0 in Heqb.
          eapply backward_rule1.
          eapply dmportp_sllseg_qport_msg_length.
          pure intro.
          rewrite Heqb in H30; simpl in H30. tryfalse.
        }
        destruct (Int.ltu ($ 0) qentries) eqn: ?; simpl in H71; tryfalse.
        clear H71 H74 H75.
        rename v'22 into dport'.

        (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE) *)
        hoare forward.
        1,2,3: pauto.
        {
          hoare normal pre; pure intro.
          hoare name lift Aop pre.
          eapply cslsemrel_rule.
          { can_change_aop_solver'. }
          { rewrite Z2Nat.id by apply Int.unsigned_range.
            apply Int.unsigned_range_2. }
          { intros. rewrite Hsem.
            symbolic execution. pauto. }
          { unfold p_local, CurLINV, LINV, OSLInv. intros.
            sep normal in H76; sep destruct H76; sep split in H76.
            sep auto. splits; eauto.
            all: destruct H77 as [? [? [? [? [? ?]]]]]; auto. }
        }
        eapply disj_rule; hoare normal pre; pure intro.
        2:{
          exfalso. rewrite H52 in H71. clear - H71.
          unfold notint, val_inj in H71.
          destruct H71; inverts H.
        }
        clear H71 H74 H75.

        (* aemp_isr_is *)
        eapply backward_rule1.
        {
          intros.
          sep name lift Aier in H71.
          sep name lift Ais in H71.
          sep name lift Aisr in H71.
          eapply add_aemp_isr_is_prop in H71.
          eapply H71.
        }

        (* EXIT_CRITICAL;ₛ *)
        apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
        unfold AOSCorePortPtrList.
        hoare normal pre; pure intro.
        rename H74 into Hcptr.
        destruct H30; simpljoin1.
        {
          hoare forward prim.
          {
            sep autocancel.
            unfold TmrInv; sep normal; sep autocancel.
            sep name lift PartitionInv; apply fold_PartitionInv_frm.
            sep cancel PartitionInv_part2.
            unfold PartitionInv_part1; sep normal; sep eexists; sep autocancel.
            sep split.
            {
              unfold AOSCorePortPtrList.
              sep pauto.
              2:{ instantiate (1:=(set dportls1 pptr
                  (Z.to_nat DNUM, ∘ (Int.unsigned x2), ∘ (Int.unsigned portid),
                  DestinationP next, ∘ (Int.unsigned x4), ∘ (Int.unsigned x5),
                  ∘ (Int.unsigned x6), QueuePort sz msgl))).
                  eapply RH_CorePortPtrList_upd_dportls; eauto. }
              
              (* cancel AOSDomainPortPtrList *)
              unfold AOSDomainPortPtrList, dmportp_sll.
              sep normal; sep autocancel.
              instantiate (8:=dportl1 ++ (update_nth_val 15
              (update_nth_val 17
                 (update_nth_val 15 dport
                    (Vptr
                       (qstart_b,
                       Int.mul ($ z1) ($ 33) +ᵢ
                       Int.mul ($ 1) ($ 33))))
                 (Vint32 (qentries -ᵢ $ 1)))
              (Vptr (qstart_b, Int.zero))) :: dportl2).
              instantiate (7:=dportmsgll1 ++ msgl :: dportmsgll2).
              eapply dmportp_sllseg_compose.
              auto.
  Optimize Proof.
  Optimize Heap.
              do 3 (eapply nth_upd_neqrev; eauto).
              { clear - H19 H72 Heqb H73.
                destruct dport; simpl in *; tryfalse.
                do 18 (destruct H19 as [? H19]; split; auto;
                      destruct dport; simpl in *; tryfalse).
                assert (Int.unsigned (qentries -ᵢ ($ 1)) <= 65535).
                { rewrite Int_unsigned_minus. 
                  rewrite Int.unsigned_repr by (clear;mauto).
                  lia.   
                  simpl_intltbool. 
                  rewrite Int.unsigned_repr by (clear;mauto).
                  lia. }
                assert (Int.unsigned (qentries -ᵢ $ 1) <=? 65535 = true) by lia.
                rewrite int16_max_unsigned_val, H18. auto.
              }
              do 3 (eapply nth_upd_neqrev; eauto).
              instantiate (7:=pptr).
              sep autocancel.
              eapply disj_split. right.
              sep normal.
              exists (qstart_b, Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33))
                     (qstart_b, Int.mul ($ z2) ($ 33))
                     (qstart_b, Int.zero) ($ Z.of_nat sz)
                     (qentries -ᵢ $ 1) (invalid_msg ++ (msg::nil)).
              assert (Z.of_nat (typelen OSMsg_t) = 33).
              { clear. simpl. lia. }
              sep split; eauto.
              2:{
                unfold Qport_msg_ptrs_P.
                splits; eauto.
                rewrite H74.
                unfold get_off_addr, fst, snd.
                rewrite Int.add_zero_l. auto.
                rewrite ! H74.
                exists 0 z2. splits; eauto.
                unfold get_off_addr, fst, snd.
                rewrite Int.add_zero_l. auto.
                lia.
              }
              2:{
                split.
                eapply nth_upd_neqrev; eauto.
                eapply update_nth; eauto.
                eapply nth_upd_neqrev; eauto.
                rewrite Int_unsigned_minus.
                rewrite Int.unsigned_repr by (clear;mauto).
                lia.   
                simpl_intltbool. 
                rewrite Int.unsigned_repr by (clear;mauto).
                lia.
              }
              2: split; [do 3 (eapply nth_upd_neqrev; eauto)|auto].
              2:{
                eapply update_nth; eauto.
                eapply nth_upd_neqrev; eauto.
                eapply update_nth; eauto.
              }
              2: do 3 (eapply nth_upd_neqrev; eauto).
              2: do 3 (eapply nth_upd_neqrev; eauto).
              2: do 3 (eapply nth_upd_neqrev; eauto).
              rewrite ! Int_unsigned_minus.
              2:{ simpl_intltbool. 
                  rewrite Int.unsigned_repr by (clear;mauto).
                  lia. }
              assert (∘ (Int.unsigned ($ Z.of_nat sz) -
                      (Int.unsigned qentries - Int.unsigned ($ 1))) = 
                      (∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned qentries) + 1)%nat).
              { rewrite Z.sub_sub_distr.
                rewrite (Int.unsigned_repr 1).
                unfold nat_of_Z.
                rewrite Z2Nat.inj_add.
                lia. lia. lia. clear. mauto. }
              rewrite H75.
              sep lift 2%nat.
              eapply dmportp_sllseg_qport_msg_app_frm.
              { sep lift 4%nat in H30.
                eapply dmportp_sllseg_qport_msg_length in H30.
                sep split in H30; auto. }
              auto.
              { sep lift 4%nat in H30.
                eapply dmportp_sllseg_qport_msg_R_qout_qin in H30.
                sep split in H30. eapply H76. }
              sep lift 4%nat in H30.
              sep cancel dmportp_sllseg_qport_msg.
              rewrite (Int.unsigned_repr 1).
              2: clear; mauto.
              assert (∘ (Int.unsigned qentries) = 
                      S ( ∘ (Int.unsigned qentries - 1) )).
              {
                unfold nat_of_Z.
                rewrite Z2Nat.inj_sub.
                assert (Z.to_nat 1 = 1%nat) by (clear; mauto).
                rewrite H76.
                rewrite minus_Sn_m.
                lia. clear - Heqb.
                simpl_intltbool.
                lia. lia.
              }
              rewrite H76 in H30.
              cbn [dmportp_sllseg_qport_msg] in *.
              sep normal in H30; sep destruct H30.
              sep normal; sep eexists; sep autocancel.
              assert (dmportp_sllseg_qport_msg_next
                      (qstart_b, Int.mul ($ z1) ($ 33)) 
                      (qstart_b, Int.zero)
                      (qstart_b,
                      Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)) =
                      (qstart_b, Int.zero)).
              {
                clear - H15 H71_z1_0 H71_z1_1 H73.
                assert ((qstart_b, Int.zero) =
                dmportp_msg_next_n 1 (qstart_b, Int.mul ($ z1) ($ 33))
                  (qstart_b, Int.zero) (qstart_b, Int.mul ($ (Z.of_nat 1 + z1)) ($ 33))).
                { eapply dmportp_msg_next_n_to_qstart; lia. }
                rewrite H at 2.
                cbn [dmportp_msg_next_n].
                assert (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33) = 
                        Int.mul ($ (Z.of_nat 1 + z1)) ($ 33)).
                2:{ rewrite H0; auto. }
                eapply Int_eq_dec in H15.
                rewrite <- H15.
                assert (Z.of_nat 1 = 1) by (clear; mauto).
                rewrite H0.
                assert (z1 < 65535) by lia.
                clear - H71_z1_0 H1.
                rewrite <- Int.mul_add_distr_l.
                assert (($ z1 +ᵢ  $ 1) = ($ (1 + z1))).
                2: rewrite H; auto.
                rewrite Int.add_unsigned.
                rewrite (Int.unsigned_repr 1).
                rewrite (Int.unsigned_repr z1).
                rewrite Z.add_comm at 1. auto.
                all: rewrite max_unsigned_val.
                all: lia.
              }
              rewrite H77 in H30. sep pauto.

              (* cancel AOSKernelPortIDTbl *)
              unfold AOSKernelPortIDTbl. sep pauto.
              instantiate (5:=kportl1 ++ (Vint32 portid
              :: Vint32 chanid :: Vptr pptr :: Vptr (chanpb, Int.zero)
              :: V$ DNUM :: Vint32 x1 :: x8 :: nil) :: kportl2).
              eapply kportNode_P_compose.
              rewrite H44; auto.
              pauto. eauto.
              sep autocancel.

              (* cancel AOSChannelIDTbl *)
              unfold AOSChannelIDTbl. sep pauto.
              instantiate (2:=chandstkportll1 ++ dstkportpl :: chandstkportll2).
              instantiate (2:=chanl1 ++ (Vint32 chanid :: Vint32 i1 :: Vint32 dpnum
                :: V$ Z.of_nat c :: v'29 :: x15 :: x16 :: x17 :: nil) :: chanl2).
              eapply ChannelNode_compose; eauto.
              rewrite H59; auto.
              rewrite H60; auto.
              unfold OS_Channel_V_dstPortsHead; simpl; eauto.
              unfold OS_Channel_V_dstPortsNum; simpl; eauto.
              pauto. sep autocancel. apply H30.
            }
            auto.
            eauto.
            eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
            eapply R_Kernelport_DomainPort_upd; eauto.
            rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
            eapply RLH_Channel_upd_dportls1; eauto.
            right; do 4 eexists; split; eauto.
            auto.
            eapply RLH_Domainportl_upd_Queue; eauto.
            rewrite H71; auto.
            unfold DomainportNode_P; splits; eauto.
            unfold Domainport_nat_P; do 5 eexists; repeat (splits; eauto).
            unfold Domainport_direction_P; split; eauto.
            unfold Domainport_Portt_P; splits; eauto.
            rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H32; do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H37; do 3 (eapply nth_upd_neqrev; eauto).
            do 3 (eapply nth_upd_neqrev; eauto).
            do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H29; do 3 (eapply nth_upd_neqrev; eauto).
            destruct next; rewrite Hnx; do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H48; do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H69; do 3 (eapply nth_upd_neqrev; eauto).
            split; eauto.
            eapply RL_PortPtrList_upd; eauto.
            rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
            eapply RL_PortAttr_upd; eauto.
            rewrite H29; do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H48; do 3 (eapply nth_upd_neqrev; eauto).
            eapply join_set_set; eauto.
          }
          eauto.
          good_frm_sovler.
          eapply rete_rule.
          eapply inline_tactics.sep_infer_conjI.
          split.
          2: instantiate (1:=(V$ OS_NO_ERR)).
          {
            intros.
            sep normal; sep eexists; sep autocancel.
            sep pauto.
            simpl; eauto.
          }
          symbolic_execution.
        }
        hoare forward prim.
        {
          sep autocancel.
          unfold TmrInv; sep normal; sep autocancel.
          sep name lift PartitionInv; apply fold_PartitionInv_frm.
          sep cancel PartitionInv_part2.
          unfold PartitionInv_part1; sep normal; sep eexists; sep autocancel.
          sep split.
          {
            unfold AOSCorePortPtrList.
            sep pauto.
            2:{ instantiate (1:=(set dportls1 pptr
                (Z.to_nat DNUM, ∘ (Int.unsigned x2), ∘ (Int.unsigned portid),
                DestinationP next, ∘ (Int.unsigned x4), ∘ (Int.unsigned x5),
                ∘ (Int.unsigned x6), QueuePort sz msgl))).
                eapply RH_CorePortPtrList_upd_dportls; eauto. }

            (* cancel AOSDomainPortPtrList *)
            unfold AOSDomainPortPtrList, dmportp_sll.
            sep normal; sep autocancel.
            instantiate (8:=dportl1 ++ (update_nth_val 17
            (update_nth_val 15 dport (Vptr (qstart_b,
                  Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))))
            (Vint32 (qentries -ᵢ $ 1))) :: dportl2).
            instantiate (7:=dportmsgll1 ++ msgl :: dportmsgll2).
            eapply dmportp_sllseg_compose.
            auto.
  Optimize Proof.
  Optimize Heap.
            do 2 (eapply nth_upd_neqrev; eauto).
            { clear - H19 H72 Heqb H73.
              destruct dport; simpl in *; tryfalse.
              do 18 (destruct H19 as [? H19]; split; auto;
                    destruct dport; simpl in *; tryfalse).
              assert (Int.unsigned (qentries -ᵢ ($ 1)) <= 65535).
              { rewrite Int_unsigned_minus. 
                rewrite Int.unsigned_repr by (clear;mauto).
                lia.   
                simpl_intltbool. 
                rewrite Int.unsigned_repr by (clear;mauto).
                lia. }
              assert (Int.unsigned (qentries -ᵢ $ 1) <=? 65535 = true) by lia.
              rewrite int16_max_unsigned_val, H18. auto.
            }
            do 2 (eapply nth_upd_neqrev; eauto).
            instantiate (7:=pptr).
            sep autocancel.
            eapply disj_split. right.
            sep normal.
            exists (qstart_b, Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33))
                    (qstart_b, Int.mul ($ z2) ($ 33))
                    (qstart_b, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
                    ($ Z.of_nat sz) (qentries -ᵢ $ 1) (invalid_msg ++ (msg::nil)).
            assert (Z.of_nat (typelen OSMsg_t) = 33).
            { clear. simpl. lia. }
            sep split; eauto.
            2:{
              unfold Qport_msg_ptrs_P.
              splits; eauto.
              rewrite H74.
              unfold get_off_addr, fst, snd.
              rewrite Int.add_zero_l. auto.
              rewrite ! H74.
              exists (z1 + 1) z2. splits; eauto.
              1,2: unfold get_off_addr, fst, snd.
              1,2: rewrite Int.add_zero_l; auto.
              assert (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33) = Int.mul ($ (z1 + 1)) ($ 33)).
              2: rewrite H75; auto.
              rewrite <- Int.mul_add_distr_l.
              assert (($ z1 +ᵢ  $ 1) = ($ (z1 + 1))).
              2: rewrite H75; auto.
              rewrite Int.add_unsigned.
              rewrite (Int.unsigned_repr 1).
              rewrite (Int.unsigned_repr z1); auto.
              1,2: rewrite max_unsigned_val.
              1,2: lia.
              split. lia.
              assert (z1 + 1 < Int.unsigned ($ Z.of_nat sz) \/ 
                      z1 + 1 = Int.unsigned ($ Z.of_nat sz)) by lia.
              destruct H75; auto.
              exfalso. rewrite <- H75 in H30.
              assert (Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
              (Int.mul ($ (z1 + 1)) ($ 33)) = true).
              2: tryfalse.
              rewrite <- Int.mul_add_distr_l.
              assert (($ z1 +ᵢ  $ 1) = ($ (z1 + 1))).
              2: rewrite H76; apply Int.eq_true.
              rewrite Int.add_unsigned.
              rewrite (Int.unsigned_repr 1).
              rewrite (Int.unsigned_repr z1); auto.
              1,2: rewrite max_unsigned_val.
              1,2: lia.
            }
            2:{
              split.
              eapply update_nth; eauto.
              eapply nth_upd_neqrev; eauto.
              rewrite Int_unsigned_minus.
              rewrite Int.unsigned_repr by (clear;mauto).
              lia.   
              simpl_intltbool. 
              rewrite Int.unsigned_repr by (clear;mauto).
              lia.
            }
            2: split; [do 2 (eapply nth_upd_neqrev; eauto)|auto].
            2:{
              eapply nth_upd_neqrev; eauto.
              eapply update_nth; eauto.
            }
            2: do 2 (eapply nth_upd_neqrev; eauto).
            2: do 2 (eapply nth_upd_neqrev; eauto).
            2: do 2 (eapply nth_upd_neqrev; eauto).
            rewrite ! Int_unsigned_minus.
            2:{ simpl_intltbool. 
                rewrite Int.unsigned_repr by (clear;mauto).
                lia. }
            assert (∘ (Int.unsigned ($ Z.of_nat sz) -
                    (Int.unsigned qentries - Int.unsigned ($ 1))) = 
                    (∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned qentries) + 1)%nat).
            { rewrite Z.sub_sub_distr.
              rewrite (Int.unsigned_repr 1).
              unfold nat_of_Z.
              rewrite Z2Nat.inj_add.
              lia. lia. lia. clear. mauto. }
            rewrite H75.
            sep lift 2%nat.
            eapply dmportp_sllseg_qport_msg_app_frm.
            { sep lift 4%nat in H30.
              eapply dmportp_sllseg_qport_msg_length in H30.
              sep split in H30; auto. }
            auto.
            { sep lift 4%nat in H30.
              eapply dmportp_sllseg_qport_msg_R_qout_qin in H30.
              sep split in H30. eapply H76. }
            sep lift 4%nat in H30.
            sep cancel dmportp_sllseg_qport_msg.
            rewrite (Int.unsigned_repr 1).
            2: clear; mauto.
            assert (∘ (Int.unsigned qentries) = 
                    S ( ∘ (Int.unsigned qentries - 1) )).
            {
              unfold nat_of_Z.
              rewrite Z2Nat.inj_sub.
              assert (Z.to_nat 1 = 1%nat) by (clear; mauto).
              rewrite H76.
              rewrite minus_Sn_m.
              lia. clear - Heqb.
              simpl_intltbool.
              lia. lia.
            }
            rewrite H76 in H30.
            cbn [dmportp_sllseg_qport_msg] in *.
            sep normal in H30; sep destruct H30.
            sep normal; sep eexists; sep autocancel.
            assert (dmportp_sllseg_qport_msg_next
                    (qstart_b, Int.mul ($ z1) ($ 33)) 
                    (qstart_b, Int.zero)
                    (qstart_b,
                    Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)) =
                    (qstart_b, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))).
            {
              clear - H15 H71_z1_0 H71_z1_1 H73.
              unfold dmportp_sllseg_qport_msg_next, msg_distance, snd.
              assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).
              rewrite H; clear H.
              assert (Int.mul ($ 1) ($ 33) = $ 33) by (clear; mauto).
              rewrite H.
              destruct (Int.unsigned (Int.divu
                 (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33) -ᵢ
                  Int.mul ($ z1) ($ 33)) ($ 33)) =? 1) eqn: ?; auto.
              eapply Z.eqb_eq in Heqb.
              exfalso.
              assert (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33) = 
                      Int.mul ($ z1) ($ 33) +ᵢ 
                      Int.mul ($ (Int.unsigned ($ Z.of_nat sz) - z1)) ($ 33)).
              {
                rewrite <- Int.mul_add_distr_l.
                assert ($ z1 +ᵢ  $ (Int.unsigned ($ Z.of_nat sz) - z1) = $ Int.unsigned ($ Z.of_nat sz)).
                2: rewrite H0; auto.
                rewrite Int.add_unsigned.
                rewrite (Int.unsigned_repr (Int.unsigned ($ Z.of_nat sz) - z1)).
                rewrite (Int.unsigned_repr z1). 
                rewrite BinInt.Zplus_minus; auto.
                1,2: rewrite max_unsigned_val; lia.
              }
              rewrite H0, Int.sub_add_l,
                      Int.sub_idem, Int.add_zero_l in Heqb.
              assert ((Int.divu (Int.mul ($ (Int.unsigned ($ Z.of_nat sz) - z1)) ($ 33))
              ($ 33)) = ($ (Int.unsigned ($ Z.of_nat sz) - z1))).
              {
                assert (exists a, a = (Int.unsigned ($ Z.of_nat sz) - z1)) by (eexists; eauto).
                destruct H1. rewrite <- H1.
                assert (x <= 65535) by lia.
                assert (0 < x) by lia.
                clear - H2 H3. mauto.
                rewrite Z_div_mult; mauto.
              }
              rewrite H1 in Heqb; clear H1.
              rewrite (Int.unsigned_repr (Int.unsigned ($ Z.of_nat sz) - z1)) in Heqb.
              2: rewrite max_unsigned_val; lia.
              assert (Int.unsigned ($ Z.of_nat sz) = z1 + 1) by lia.
              rewrite H1 in H15; clear H Heqb H0 H1.
              assert (Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
              (Int.mul ($ (z1 + 1)) ($ 33)) = true).
              2: tryfalse. clear H15.
              rewrite <- Int.mul_add_distr_l.
              assert (($ z1 +ᵢ  $ 1) = ($ (z1 + 1))).
              2: rewrite H; apply Int.eq_true.
              rewrite Int.add_unsigned.
              rewrite (Int.unsigned_repr 1).
              rewrite (Int.unsigned_repr z1); auto.
              1,2: rewrite max_unsigned_val.
              1,2: lia.
            }
            rewrite H77 in H30. sep pauto.

            (* cancel AOSKernelPortIDTbl *)
            unfold AOSKernelPortIDTbl. sep pauto.
            instantiate (5:=kportl1 ++ (Vint32 portid
            :: Vint32 chanid :: Vptr pptr :: Vptr (chanpb, Int.zero)
            :: V$ DNUM :: Vint32 x1 :: x8 :: nil) :: kportl2).
            eapply kportNode_P_compose.
            rewrite H44; auto.
            pauto. eauto.
            sep autocancel.

            (* cancel AOSChannelIDTbl *)
            unfold AOSChannelIDTbl. sep pauto.
            instantiate (2:=chandstkportll1 ++ dstkportpl :: chandstkportll2).
            instantiate (2:=chanl1 ++ (Vint32 chanid :: Vint32 i1 :: Vint32 dpnum
              :: V$ Z.of_nat c :: v'29 :: x15 :: x16 :: x17 :: nil) :: chanl2).
            eapply ChannelNode_compose; eauto.
            rewrite H59; auto.
            rewrite H60; auto.
            unfold OS_Channel_V_dstPortsHead; simpl; eauto.
            unfold OS_Channel_V_dstPortsNum; simpl; eauto.
            pauto. sep autocancel. apply H30.
          }
          auto.
  Optimize Proof.
  Optimize Heap.
          eauto.
          eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
          eapply R_Kernelport_DomainPort_upd; eauto.
          rewrite H34; do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H16; do 2 (eapply nth_upd_neqrev; eauto).
          eapply RLH_Channel_upd_dportls1; eauto.
          right; do 4 eexists; split; eauto.
          auto.
          eapply RLH_Domainportl_upd_Queue; eauto.
          rewrite H71; auto.
          unfold DomainportNode_P; splits; eauto.
          unfold Domainport_nat_P; do 5 eexists; repeat (splits; eauto).
          unfold Domainport_direction_P; split; eauto.
          unfold Domainport_Portt_P; splits; eauto.
          rewrite H16; do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H32; do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H34; do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H37; do 2 (eapply nth_upd_neqrev; eauto).
          do 2 (eapply nth_upd_neqrev; eauto).
          do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H29; do 2 (eapply nth_upd_neqrev; eauto).
          destruct next; rewrite Hnx; do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H48; do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H14; do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H69; do 2 (eapply nth_upd_neqrev; eauto).
          split; eauto.
          eapply RL_PortPtrList_upd; eauto.
          rewrite H14; do 2 (eapply nth_upd_neqrev; eauto).
          eapply RL_PortAttr_upd; eauto.
          rewrite H29; do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H48; do 2 (eapply nth_upd_neqrev; eauto).
          eapply join_set_set; eauto.
        }
        eauto.
        good_frm_sovler.
        eapply rete_rule.
        eapply inline_tactics.sep_infer_conjI.
        split.
        2: instantiate (1:=(V$ OS_NO_ERR)).
        {
          intros.
          sep normal; sep eexists; sep autocancel.
          sep pauto.
          simpl; eauto.
        }
        symbolic_execution.
      }

      eapply backward_rule1.
      eapply dmportp_sllseg_qport_msg_length.
      pure intro. simpl in H30.
      rewrite <- H30.
      assert (Int.unsigned qentries = 0).
      { apply Z2Nat.inj.
        apply Int.unsigned_range. lia.
        unfold nat_of_Z in H30; rewrite <- H30. lia. }
      rewrite H71. rewrite Z.sub_0_r.
      cbn [dmportp_sllseg_qport_msg].
      naive pure intro.
      remember (Int.mul ($ z1) ($ 33)) as A.
      remember (Int.mul ($ z2) ($ 33)) as B.
      inversion H74; subst A B. clear H74.
      (* IF (port_ptr ′ .. mode ==ₑ ′ QUEUE) *)
      eapply seq_rule.
      {
        eapply if_rule2'.
        {
          symbolic_exe_port.
          unfold DomainportNode_P. splits; eauto.
          unfold Domainport_nat_P. do 5 eexists; repeat (splits; eauto).
          instantiate (2:=DestinationP next). unfold Domainport_direction_P. auto.
          instantiate (2:=QueuePort sz nil). unfold Domainport_Portt_P. splits; eauto.
        }
        2:{ (* sample is false *)
          hoare normal pre; pure intro.
          instantiate (1:=Afalse).
          exfalso; clear - H74; mauto.
        }
        hoare normal pre; pure intro.
        clear H74 H75 H77.

        (* If (port_ptr ′ .. OSQEntries >ₑ ′ 0) *)
        eapply ift_rule''; [ symbolic_exe_port | ].
        hoare normal pre; pure intro.
        instantiate (1:=Afalse).
        assert (Int.ltu ($ 0) qentries = true) by pauto.
        clear H74 H75 H77.
        assert (∘ (Int.unsigned qentries) > 0)%nat.
        { clear - H78. 
          rewrite <- (Int.repr_unsigned qentries) in H78.
          simpl_intltbool.
          erewrite Int.unsigned_repr in H78 by (apply Int.unsigned_range_2).
          rewrite <- Zabs2Nat.abs_nat_nonneg by lia. lia. }
        lia.
      }

      eapply disj_rule.
      2: pure intro; eapply pfalse_rule.
      hoare normal pre; pure intro.
      clear H74 H75 H77.
      hoare forward. hoare normal pre; pure intro.
      clear H74.

      (* choose portacc_queue_nil *)
      hoare abscsq; [apply noabs_oslinv | | ].
      eapply absinfer_seq.
      3: eapply absinfer_choice1.
      5: intros ? Hs; apply Hs.
      1,2,3,4: can_change_aop_solver'.
      hoare name lift osdomainportid pre.
      hoare abscsq; [apply noabs_oslinv | | ].
      eapply portacc_queue_nil_cont; eauto.
      can_change_aop_solver'.

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE) *)
      hoare forward.
      1,2,3: pauto.
      {
        hoare normal pre; pure intro.
        hoare name lift Aop pre.
        unfold Semrelease.
        cbn [spec_code_cons].
        eapply cslsemrel_rule.
        { can_change_aop_solver'. }
        { rewrite Z2Nat.id by apply Int.unsigned_range.
          apply Int.unsigned_range_2. }
        { intros. rewrite Hsem.
          symbolic execution. pauto. }
        { unfold p_local, CurLINV, LINV, OSLInv. intros.
          sep normal in H78; sep destruct H78; sep split in H78.
          sep auto. splits; eauto.
          all: destruct H79 as [? [? [? [? [? ?]]]]]; auto. }
      }
      eapply disj_rule; hoare normal pre; pure intro.
      2:{
        exfalso. rewrite H52 in H74. clear - H74.
        unfold notint, val_inj in H74.
        destruct H74; inverts H.
      }
      clear H74 H75 H77.

      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      (* unfold AOSCorePortPtrList.
      hoare normal pre; pure intro.
      rename H75 into Hcptr. *)
      hoare forward prim.
      {
        sep autocancel.
        unfold TmrInv; sep normal; sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1; sep normal; sep eexists; sep autocancel.
        sep split.
        {
          (* unfold AOSCorePortPtrList.
          sep pauto. *)

          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal; sep autocancel.
          instantiate (8:=dportl1 ++ dport :: dportl2).
          instantiate (7:=dportmsgll1 ++ nil :: dportmsgll2).
          eapply dmportp_sllseg_compose; eauto.
          instantiate (7:=pptr).
          sep autocancel.
          eapply disj_split. right.
          sep normal.
          exists (qstart_b, Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33))
                  (qstart_b, Int.mul ($ z2) ($ 33))
                  (qstart_b, Int.mul ($ z2) ($ 33)) ($ Z.of_nat sz)
                  (Int.zero) (invalid_msg).
          assert (Z.of_nat (typelen OSMsg_t) = 33).
          { clear. simpl. lia. }
          sep split; eauto.
          2:{
            unfold Qport_msg_ptrs_P.
            splits; eauto.
            rewrite H15.
            unfold get_off_addr, fst, snd.
            rewrite Int.add_zero_l. auto.
            rewrite ! H15.
            exists z2 z2. splits; eauto;
            unfold get_off_addr, fst, snd;
            rewrite Int.add_zero_l; auto.
          }
          2:{
            split; auto.
            rewrite H70. do 2 f_equal.
            assert ($ Int.unsigned qentries = ($ 0)) by (rewrite H71; auto).
            rewrite Int.repr_unsigned in H77; rewrite H77.
            clear; mauto.
            assert (0 = Int.unsigned Int.zero) by (clear; mauto).
            rewrite <- H77; apply Int.unsigned_range.
          }
          2: rewrite <- H76; auto.
          assert (∘ (Int.unsigned Int.zero) = 0%nat) by (clear; mauto).
          rewrite H77; clear H77.
          assert (Int.unsigned Int.zero = 0) by (clear; mauto).
          rewrite H77, Z.sub_0_r; clear H77.
          cbn [dmportp_sllseg_qport_msg]. sep pauto.

          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl. sep pauto.
          instantiate (5:=kportl1 ++ (Vint32 portid
          :: Vint32 chanid :: Vptr pptr :: Vptr (chanpb, Int.zero)
          :: V$ DNUM :: Vint32 x1 :: x8 :: nil) :: kportl2).
          eapply kportNode_P_compose.
          rewrite H44; auto.
          pauto. eauto.
          sep autocancel.

          (* cancel AOSChannelIDTbl *)
          unfold AOSChannelIDTbl. sep pauto.
          instantiate (2:=chandstkportll1 ++ dstkportpl :: chandstkportll2).
          instantiate (2:=chanl1 ++ (Vint32 chanid :: Vint32 i1 :: Vint32 dpnum
            :: V$ Z.of_nat c :: v'29 :: x15 :: x16 :: x17 :: nil) :: chanl2).
          eapply ChannelNode_compose; eauto.
          rewrite H59; auto.
          rewrite H60; auto.
          unfold OS_Channel_V_dstPortsHead; simpl; eauto.
          unfold OS_Channel_V_dstPortsNum; simpl; eauto.
          pauto. sep autocancel. apply H75.
        }
        all: eauto.
        split; eauto.
      }
      eauto.
      good_frm_sovler.
      eapply rete_rule.
      eapply inline_tactics.sep_infer_conjI.
      split.
      2: instantiate (1:=(V$ OS_NO_ERR)).
      {
        intros.
        sep normal; sep eexists; sep autocancel.
        sep pauto.
        simpl; eauto.
      }
      symbolic_execution.
    }

    {
      unfold Domainport_Portt_P in H30; destruct p5; simpljoin1.
      (* queue is false *)
      2: rewrite H66 in H48; inverts H48.
      rename x into msg.
      destruct msgptr as [msg_b msg_i].

      (* IF (port_ptr ′ .. mode ==ₑ ′ QUEUE) *)
      eapply seq_rule.
      {
        eapply if_rule2'.
        {
          symbolic_exe_port.
          unfold DomainportNode_P. splits; eauto.
          unfold Domainport_nat_P. do 5 eexists; repeat (splits; eauto).
          instantiate (2:=DestinationP next). unfold Domainport_direction_P. auto.
          instantiate (2:=SamplePort (Some msg)). 
          unfold Domainport_Portt_P. eexists; splits; eauto.
        }
        { (* queue is false *)
          hoare normal pre; pure intro.
          instantiate (1:=Afalse).
          exfalso; clear - H30; mauto.
        }
        hoare normal pre; pure intro.
        clear H30.
        rename v'23 into qstart.

        eapply if_rule2'.
        {
          symbolic_exe_port.
          unfold DomainportNode_P. splits; eauto.
          unfold Domainport_nat_P. do 5 eexists; repeat (splits; eauto).
          instantiate (2:=DestinationP next). unfold Domainport_direction_P. auto.
          instantiate (2:=SamplePort (Some msg)). 
          unfold Domainport_Portt_P. eexists; splits; eauto.
        }
        2:{ (* others is false *)
          hoare normal pre; pure intro.
          instantiate (1:=Afalse).
          exfalso; clear - H30; mauto.
        }
        hoare normal pre; pure intro.
        clear H30 H57 H68.

        (* choose portacc_queue_notnil (|Vptr pptr :: Vptr msgptr :: nil|) *)
        hoare abscsq; [apply noabs_oslinv | | ].
        eapply absinfer_seq.
        3: eapply absinfer_choice2.
        5: intros ? Hs; apply Hs.
        1,2,3,4: can_change_aop_solver'.
        hoare abscsq; [apply noabs_oslinv | | ].
        eapply absinfer_seq.
        3: eapply absinfer_choice2.
        5: intros ? Hs; apply Hs.
        1,2,3,4: can_change_aop_solver'.
        
        (* find qstart memory *)
        unfold dmportp_sllseg_sampleport_msg.
        hoare normal pre; pure intro.
        inversion H57; subst v'22; clear H57.
        rename v'23 into msg2.

        (* msg_ptr ′ .. len =ₑ (port_ptr ′ .. OSQStart) .. len;ₛ *)
        unfold TmrInv, HeapInv'.
        hoare normal pre; pure intro.
        hoare name lift oscoreheapid pre.
        rename v'22 into cHeapl.
        assert (~ In_heapl_addrval cHeapl (msg_b, msg_i) (S (length msg)) \/ In_heapl_addrval cHeapl (msg_b, msg_i) (S (length msg))) as [ | ] by tauto.
        { hoare name lift oschannelid pre.
          hoare name lift oskportid pre.
          hoare name lift osdomainportid pre.
          hoare abscsq; [apply noabs_oslinv | | ].
          eapply portacc_sample_abt; eauto.
          can_change_aop_solver'.
          apply absabort_rule. }
        
        hoare name lift AOScoreheapl pre.
        eapply backward_rule1.
        eapply port_split_coreheapl; eauto.
        naive pure intro.

        rename v'22 into cheapl1. rename v'25 into cheapl2.
        rename v'26 into ori_msgn. rename v'27 into ori_msg_vl. rename v'28 into ori_msg_vl2.
        simpljoin1.
        destruct ori_msg_vl as [ | ori_len_v ori_msg_vl ].
        simpl in H77; lia.
        hoare name lift Aarray pre.
        unfold Aarray. cbn [Aarray'].
        hoare normal pre.
        hoare name lift msg_ptr pre.
        assert ((msg_b, msg_i) = get_off_addr (msg_b, msg_i) Int.zero).
        { unfold get_off_addr. cbn [fst snd]. rewrite Int.add_zero. reflexivity. }
        rewrite H73 at 2. clear H73.
        hoare name lift Aop pre.
        eapply seq_rule.
        {
          eapply assign_rule_struct_member.
          8:{
            intros.
            eapply port_OSQStart_len_rv'.
            4:{ sep autocancel.
                sep lift 9%nat in H73.
                apply H73. }
            split; try lia.
            assert ((length msg <= ∘ CHANNEL_CACHE_SZIE)%nat).
            rewrite <- H30. apply Nat.le_add_r.
            unfold nat_of_Z in H76. 
            eapply Z2Nat.inj_le.
            lia. clear; unfold CHANNEL_CACHE_SZIE; mauto.
            rewrite Nat2Z.id; auto.
            auto. auto.
          }
          2: intros s'; split;[ intros Hs;exact Hs  |intros Hs;exact Hs ].
          2: go.
          go. go. go. go.
          assert (Z.of_nat (length msg) <= CHANNEL_CACHE_SZIE).
          eapply Z2Nat.inj_le.
          lia. clear; unfold CHANNEL_CACHE_SZIE; mauto.
          rewrite Nat2Z.id; unfold nat_of_Z in H30;
          rewrite <- H30; apply Nat.le_add_r.
          clear - H73. unfold CHANNEL_CACHE_SZIE in *. cbn.
          unfold language.msg in *.
          rewrite Int.unsigned_repr.
          2: rewrite max_unsigned_val; split; lia.
          assert (Z.of_nat (length msg) <=? 255 = true) by lia.
          rewrite H; auto.
          apply eq_int;auto.
          { intros ? Hs. subst. sep name lift p_local in Hs. unfold CurLINV. sep auto. }
        }
        hoare normal pre; pure intro.

        (* portacc_sample *)
        hoare name lift oscoreheapid pre.
        hoare name lift oschannelid pre.
        hoare name lift oskportid pre.
        hoare name lift osdomainportid pre.
        hoare abscsq; [apply noabs_oslinv | | ].
        eapply portacc_sample_cont; eauto.
        can_change_aop_solver'.
        

        (* memcpy (­msg_ptr ′ .. data, (port_ptr ′ .. OSQStart) .. data, (port_ptr ′ .. OSQStart) .. len­);ₛ *)
        eapply forward_rule2.
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
          eapply rvl_elim.
          eapply symbolic_lemmas.addrof_array_elem_rv.
          eapply port_OSQStart_data_rv.
          eapply H19. eauto.
          sep autocancel; apply H73.
          symbolic_execution. tauto.
          right; eexists; eauto.
          eapply rvl_elim; [ | apply rvl_nil].
          eapply cast_rv_tint8_tint32. 
          eapply port_OSQStart_len_rv'.
          4: sep lift 13%nat in H73.
          4: sep autocancel; apply H73.
          split; try lia.
          assert ((length msg <= ∘ CHANNEL_CACHE_SZIE)%nat).
          rewrite <- H30. apply Nat.le_add_r.
          unfold nat_of_Z in H76. 
          eapply Z2Nat.inj_le.
          lia. clear; unfold CHANNEL_CACHE_SZIE; mauto.
          rewrite Nat2Z.id; auto.
          auto. auto.
        }
        { (* ==> pre*)
          intros; unfold_spec.
          sep normal. sep eexists.
          assert ((length msg) = (Z.to_nat (Int.unsigned ($  Z.of_nat (length msg))))).
          { rewrite Int.unsigned_repr. rewrite Nat2Z.id. auto.
            assert (Z.of_nat (length msg) <= CHANNEL_CACHE_SZIE).
            eapply Z2Nat.inj_le.
            lia. clear; unfold CHANNEL_CACHE_SZIE; mauto.
            rewrite Nat2Z.id; unfold nat_of_Z in H30;
            rewrite <- H30; apply Nat.le_add_r.
            clear - H76. unfold CHANNEL_CACHE_SZIE in *. cbn.
            unfold language.msg in *. lia. }
          rewrite H76 in H73 at 2.
          unfold Aarray at 1. sep cancel Aarray'.
          rewrite <- H30 in H73.
          sep name lift Aarray' in H73.
          apply Aarray_split in H73; auto.
          unfold language.msg in H76.
          rewrite H76 in H73 at 1. sep cancel Aarray.
          sep name lift aemp_isr_is in H73. 
          sep name lift Ais in H73. sep name lift Aisr in H73.
          eapply elim_aemp_isr_is_prop in H73.
          sep autocancel. sep pauto.
          { unfold get_off_addr. cbn.
            rewrite ! Int.add_zero. auto. }
          { rewrite H30. clear. unfold CHANNEL_CACHE_SZIE. rewrite Z2Nat.id by lia. mauto. }
        }
        { good_frm_sovler. }
        { sep_unfold_funpost. intros. sep destruct H73. sep auto. }
        { sep_unfold_funpre. intros. sep destruct H73. sep auto. }
        { simpl; eauto. }
        unfold getasrt; unfold OS_memcopyPost, OS_memcopyPost'.
        intros. sep normal in H73; sep destruct H73.
        assert (logic_lv ori_msg_vl :: logic_lv msg :: logic_ier er
        :: logic_code (spec_code_cons (Semrelease (V$ Z.of_nat c)) s) :: nil =
        logic_lv x9 :: logic_lv x10 :: logic_ier x12 :: logic_code x11 :: nil).
        sep split in H73. auto.
        assert (Vptr (msg_b, (msg_i +ᵢ  ($ 1 +ᵢ  Int.zero)) +ᵢ
        Int.mul ($ Z.of_nat (typelen char_t)) ($ 0)) :: Vptr
        (fst qstart, (snd qstart +ᵢ  Int.one) +ᵢ
        Int.mul ($ Z.of_nat (typelen char_t)) ($ 0))
        :: V$ Z.of_nat (length msg) :: nil =
        Vptr x0 :: Vptr x3 :: Vint32 x7 :: nil).
        sep split in H73. auto.
        inversion H76. inversion H78. clear H76 H78. 
        subst x0 x3 x7 x9 x10 x12 x11. clear x.
        rewrite ! Int.add_zero in *.

        (* merge coreheap *)
        sep name lift AOScoreheapl in H73.
        sep name lift (Aarray (msg_b, msg_i +ᵢ  $ 1)) in H73.
        sep name lift (get_off_addr (msg_b, msg_i) Int.zero) in H73.
        sep remember (1::2::nil)%nat in H73.
        rewrite Int.unsigned_repr in H73.
        2:{ assert (Z.of_nat (length msg) <= CHANNEL_CACHE_SZIE).
            eapply Z2Nat.inj_le.
            lia. clear; unfold CHANNEL_CACHE_SZIE; mauto.
            rewrite Nat2Z.id; unfold nat_of_Z in H30;
            rewrite <- H30; apply Nat.le_add_r.
            clear - H78. unfold CHANNEL_CACHE_SZIE in *. cbn.
            unfold language.msg in *. lia. }
        rewrite Nat2Z.id in H73.
        sep lift 3%nat in H73.
        eapply astar_mono in H73.
        3: instantiate (1:= Aarray (msg_b, msg_i)
        (Tarray char_t (S (length msg))) (V$ (Z.of_nat (length msg))::msg) ).
        2: eauto. sep lift 2%nat in H73.
        2:{ unfold Aarray, get_off_addr. 
            cbn [Aarray' snd fst]. intros.
            cbn [typelen].
            assert (Z.of_nat 1 = 1)%Z by lia.
            rewrite H79.
            rewrite Int.add_zero in H78.
            apply H78. }
        subst H76.

        sep remember (1::2::3::nil)%nat in H73.
        sep lift 4%nat in H73.
        eapply astar_mono in H73.
        2: eauto. sep lift 2%nat in H73.
        2: eapply AOScoreheapl_merge; eauto.
        2:{ rewrite <- H77. lia. }
        2:{ rewrite H77. lia. }
        2:{ cbn. 
            assert (Z.of_nat (length msg) <= CHANNEL_CACHE_SZIE).
            eapply Z2Nat.inj_le.
            lia. clear; unfold CHANNEL_CACHE_SZIE; mauto.
            rewrite Nat2Z.id; unfold nat_of_Z in H30;
            rewrite <- H30; apply Nat.le_add_r.
            split; auto.
            clear - H78. unfold CHANNEL_CACHE_SZIE in *. cbn.
            unfold language.msg in *.
            assert (Int.unsigned ($ Z.of_nat (length msg)) <= 255).
            assert (length msg <= 32)%nat by lia.
            clear - H.
            rewrite Int.unsigned_repr.
            lia. rewrite max_unsigned_val; lia.
            assert (Int.unsigned ($ Z.of_nat (length msg)) <=? 255  = true) by lia.
            rewrite H0; auto.
            apply array_type_vallist_match_app in H69.
            tauto. }
        
        (* merge HeapInv' *)
        subst H76.
        sep normal in H73.
        sep name lift AOScoreheapt in H73.
        sep name lift AOScoreheape in H73.
        sep name lift AOScoreheapl in H73.
        sep name lift oscoreheapid in H73.
        sep remember (1::2::3::4::nil)%nat in H73.
        sep lift 5%nat in H73.
        eapply astar_mono in H73.
        2: eauto. sep lift 2%nat in H73.
        2:{
          instantiate (1:=HeapInv').
          intros. unfold HeapInv'. sep pauto.
          clear - H57. revert H57.
          induction cheapl1; simpl; intros; auto.
          eapply NoDup_cons_iff in H57; simpljoin1.
          eapply NoDup_cons; eauto.
          intro; destruct H.
          clear - H1.
          induction cheapl1; simpl; intros; auto.
          simpl in H1.
          destruct H1; [left|right]; eauto.
        }
        subst H76.
        
        (* merge qstart Aarray *)
        sep remember (9::13::1::nil)%nat in H73.
        sep lift 4%nat in H73.
        eapply astar_mono in H73.
        2: eauto. sep lift 2%nat in H73.
        2:{
          instantiate (1:=Aarray (get_off_addr qstart (Int.one)) (Tarray Tint8 (nat_of_Z CHANNEL_CACHE_SZIE)) (msg++msg2) ** HeapInv').
          intros.
          rewrite <- H30.
          eapply Aarray_merge; eauto.
          { rewrite H30. clear. unfold CHANNEL_CACHE_SZIE. mauto. }
          sep autocancel.
          unfold get_off_addr.
          assert ((length msg) = (Z.to_nat (Int.unsigned ($  Z.of_nat (length msg))))).
          { rewrite Int.unsigned_repr. rewrite Nat2Z.id. auto.
            assert (Z.of_nat (length msg) <= CHANNEL_CACHE_SZIE).
            eapply Z2Nat.inj_le.
            lia. clear; unfold CHANNEL_CACHE_SZIE; mauto.
            rewrite Nat2Z.id; unfold nat_of_Z in H30;
            rewrite <- H30; apply Nat.le_add_r.
            clear - H79. unfold CHANNEL_CACHE_SZIE in *. cbn.
            unfold language.msg in *. lia. }
          unfold language.msg in H79; rewrite H79; apply H78.
        }
        subst H76.
        sep normal in H73.

        (* merge dmportp_sllseg_sampleport_msg *)
        sep remember (1::17::nil)%nat in H73.
        sep lift 3%nat in H73.
        eapply astar_mono in H73.
        2: eauto. sep lift 2%nat in H73.
        2:{
          instantiate (1:=dmportp_sllseg_sampleport_msg qstart (msg::nil)).
          intros.
          unfold dmportp_sllseg_sampleport_msg.
          sep normal; exists msg msg2. sep autocancel.
          sep pauto.
        }
        subst H76.
        sep remember (10::11::2::nil)%nat in H73.
        sep lift 4%nat in H73.
        eapply astar_mono in H73.
        2: eauto. sep lift 2%nat in H73.
        2:{
          instantiate (1:=HeapInv').
          intros. sep pauto.
        }
        subst H76.
        apply H73.
      }
      hoare forward.
      hoare normal pre; pure intro.
      clear H30.
      eapply disj_rule; hoare normal pre; pure intro.
      2: eapply pfalse_rule.
      clear H30 H57 H68.

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE) *)
      hoare forward.
      1,2,3: pauto.
      {
        hoare normal pre; pure intro.
        hoare name lift Aop pre.
        eapply cslsemrel_rule.
        { can_change_aop_solver'. }
        { rewrite Z2Nat.id by apply Int.unsigned_range.
          apply Int.unsigned_range_2. }
        { intros. rewrite Hsem.
          symbolic execution. pauto. }
        { unfold p_local, CurLINV, LINV, OSLInv. intros.
          sep normal in H69; sep destruct H69; sep split in H69.
          sep auto. splits; eauto.
          all: destruct H70 as [? [? [? [? [? ?]]]]]; auto. }
      }
      eapply disj_rule; hoare normal pre; pure intro.
      2:{
        exfalso. rewrite H52 in H30. clear - H30.
        unfold notint, val_inj in H30.
        destruct H30; inverts H.
      }
      clear H30 H57 H68.

      (* aemp_isr_is *)
      eapply backward_rule1.
      {
        intros.
        sep name lift Aier in H30.
        sep name lift Ais in H30.
        sep name lift Aisr in H30.
        eapply add_aemp_isr_is_prop in H30.
        eapply H30.
      }

      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      hoare forward prim.
      {
        sep autocancel.
        unfold TmrInv; sep normal; sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1; sep normal; sep eexists; sep autocancel.
        sep split; eauto.
        2: split; eauto.

        (* cancel AOSDomainPortPtrList *)
        unfold AOSDomainPortPtrList, dmportp_sll.
        sep normal; sep autocancel.
        eapply dmportp_sllseg_compose; eauto.
        instantiate (2:=pptr).
        sep autocancel.
        eapply disj_split. left.
        sep pauto.

        (* cancel AOSKernelPortIDTbl *)
        unfold AOSKernelPortIDTbl. sep pauto.
        eapply kportNode_P_compose; eauto.
        rewrite H44; auto.
        sep autocancel.

        (* cancel AOSChannelIDTbl *)
        unfold AOSChannelIDTbl. sep pauto.
        eapply ChannelNode_compose; eauto.
        rewrite H59; auto.
        rewrite H60; auto.
        unfold OS_Channel_V_dstPortsHead; simpl; eauto.
        unfold OS_Channel_V_dstPortsNum; simpl; eauto.
        pauto. sep autocancel. apply H57.
      }
      eauto.
      good_frm_sovler.
      eapply rete_rule.
      eapply inline_tactics.sep_infer_conjI.
      split.
      2: instantiate (1:=(V$ OS_NO_ERR)).
      {
        intros.
        sep normal; sep eexists; sep autocancel.
        sep pauto.
        simpl; eauto.
      }
      symbolic_execution.
    }
  }

  { (* 核内通信 *)
    unfold Channel_type_P in H52; simpljoin1.
    unfold OS_Channel_V_semaphore in H48; simpl in H48; inverts H48.
    hoare abscsq; [apply noabs_oslinv | | ].
    eapply absinfer_choice2; [ | | intros ? Hs; apply Hs ].
    1,2: can_change_aop_solver'.

    (* semaphore ′ =ₑ (〈 OS_Channel ∗ 〉 kport ′ .. channel) .. semaphore;ₛ *)
    eapply seq_rule.
    {
      hoare name lift semaphore pre.
      hoare name lift Aop pre.
      eapply assign_rule_lvar.
      { intro; split; intros; apply H48. }
      {
        intros.
        eapply struct_member_off_rv.
        3:{
          instantiate (1:=(chanpb, Int.zero)).
          assert (Vptr (chanpb, Int.zero) = nth_val' 3 (Vint32 portid
          :: Vint32 chanid :: Vptr pptr :: Vptr (chanpb, Int.zero)
             :: V$ DNUM :: Vint32 x1 :: x8 :: nil)) by (simpl; auto).
          rewrite H52; clear H52.
          eapply symbolic_lemmas.cast_rv_tptr.
          eapply kport_channel_rv; eauto.
          sep cancel kport. sep cancel Astruct'. eapply H48.
          auto.
  Optimize Proof.
  Optimize Heap.
        }
        3:{
          unfold Astruct in H48 at 1.
          unfold OS_Channel in H48 at 1.
          unfold Astruct' in H48 at 1.
          sep normal in H48. sep lift 5%nat in H48.
          assert (Z.of_nat (typelen char_t) = 1) by (clear; simpl; lia).
          rewrite H52 in H48.
          assert (((Int.zero +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1 = $ 3) by (clear; mauto).
          rewrite H58 in H48.
          instantiate (5:= ($ 3)).
          unfold get_off_addr, fst, snd.
          rewrite Int.add_zero_l.
          apply H48.
        }
        auto.
        auto.
        unfold OS_Channel; eauto.
        all: go.
      }
      eapply eq_int; tauto.
      sep auto.
    }

    (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
    {CSLSEMACC (semaphore ′, resource_get_res ′);ₛ
    If (resource_get_res ′ ==ₑ NULL)
    {EXIT_CRITICAL;ₛ
    RETURN 〈 char_t 〉 ′ OS_CHANNEL_ERR_BEING_USED}};ₛ *)
    hoare forward.
    {
      hoare normal pre; pure intro.
      instantiate (1:=Afalse).
      exfalso; clear - H48; mauto.
    }
    hoare forward. hoare normal pre; pure intro.
    clear H48.

    hoare lift 12%nat pre.
    eapply backward_rule1.
    intros. eapply disj_split in H48. eapply H48.
    eapply disj_rule; hoare normal pre; pure intro.
    2:{ (* QUEUE *)
      unfold Domainport_Portt_P in H30; destruct p5; simpljoin1.
      (* sample is false *)
      rewrite H74 in H48; inverts H48.
      clear H74.
      rewrite H68 in H73; inverts H73; rename n into sz.
      rename v'22 into qend. rename v'24 into qin.
      rename v'25 into qout. rename v'27 into qentries.
      rename v'23 into qstart.

      destruct qstart as (qstart_b & qstart_i).
      unfold Qport_msg_ptrs_P in H70.
      destruct H70 as [H70_ [H70_0 [z1 [z2 H70]]]].
      subst qstart_i.
      unfold get_off_addr in H70, H70_0.
      cbn [fst snd] in *.
      destruct H70 as [? [? H70]].
      assert (Z.of_nat (typelen OSMsg_t) = 33).
      { clear. simpl. lia. }
      rewrite H74 in *; clear H74.
      subst qout qend qin.
      rewrite ! Int.add_zero_l. rewrite Int.add_zero_l in *.
      destruct msgptr as [msg_b msg_i].
      destruct H70 as [[H70_z1_0 H70_z1_1] [H70_z2_0 H70_z2_1]].

      rename v'28 into invalid_msg.
      destruct msgl.
      2:{
        rename v into msg.

        (* IF (port_ptr ′ .. mode ==ₑ ′ QUEUE) *)
        eapply seq_rule.
        {
          eapply if_rule2'.
          {
            symbolic_exe_port.
            unfold DomainportNode_P. splits; eauto.
            unfold Domainport_nat_P. do 5 eexists; repeat (splits; eauto).
            instantiate (2:=DestinationP next). unfold Domainport_direction_P. auto.
            instantiate (2:=QueuePort sz msgl). unfold Domainport_Portt_P. splits; eauto.
          }
          2:{ (* sample is false *)
            hoare normal pre; pure intro.
            instantiate (1:=Afalse).
            exfalso; clear - H30; mauto.
          }
          hoare normal pre; pure intro.
          clear H30 H70 H73.

          (* If (port_ptr ′ .. OSQEntries >ₑ ′ 0) *)
          eapply ift_rule''; [ symbolic_exe_port | ].
          hoare normal pre; pure intro.
          assert (Int.ltu ($ 0) qentries = true) by pauto.
          clear H30 H70 H73.
          assert (∘ (Int.unsigned qentries) > 0)%nat.
          { clear - H74. 
            rewrite <- (Int.repr_unsigned qentries) in H74.
            simpl_intltbool.
            erewrite Int.unsigned_repr in H74 by (apply Int.unsigned_range_2).
            rewrite <- Zabs2Nat.abs_nat_nonneg by lia. lia. }

          (* choose portacc_queue_notnil (|Vptr pptr :: Vptr msgptr :: nil|) *)
          hoare abscsq; [apply noabs_oslinv | | ].
          eapply absinfer_choice2.
          3: intros ? Hs; apply Hs.
          1,2: can_change_aop_solver'.
          hoare abscsq; [apply noabs_oslinv | | ].
          eapply absinfer_choice1.
          3: intros ? Hs; apply Hs.
          1,2: can_change_aop_solver'.
          
          (* find qout memory *)
          hoare lift 2%nat pre.
          eapply backward_rule1.
          eapply dmportp_sllseg_qport_msg_ngt0; eauto.
          pure intro.
          inversion H70. clear H70. subst x x0.

          (* msg_ptr ′ .. len =ₑ (port_ptr ′ .. OSQOut) .. len;ₛ *)
          unfold TmrInv, HeapInv'.
          hoare normal pre; pure intro.
          hoare name lift oscoreheapid pre.
          rename v'22 into cHeapl.
          assert (~ In_heapl_addrval cHeapl (msg_b, msg_i) (S (length msg)) \/ In_heapl_addrval cHeapl (msg_b, msg_i) (S (length msg))) as [ | ] by tauto.
          { hoare name lift oschannelid pre.
            hoare name lift oskportid pre.
            hoare name lift osdomainportid pre.
            hoare abscsq; [apply noabs_oslinv | | ].
            eapply portacc_queue_notnil_abt; eauto.
            can_change_aop_solver'.
            apply absabort_rule. }
          
          hoare name lift AOScoreheapl pre.
          eapply backward_rule1.
          eapply port_split_coreheapl; eauto.
          naive pure intro.

          rename v'22 into cheapl1. rename v'25 into cheapl2.
          rename v'26 into ori_msgn. rename v'27 into ori_msg_vl. rename v'28 into ori_msg_vl2.
          simpljoin1.
          destruct ori_msg_vl as [ | ori_len_v ori_msg_vl ].
          simpl in H82; lia.
          hoare name lift Aarray pre.
          unfold Aarray. cbn [Aarray'].
          hoare normal pre.
          hoare name lift msg_ptr pre.
          assert ((msg_b, msg_i) = get_off_addr (msg_b, msg_i) Int.zero).
          { unfold get_off_addr. cbn [fst snd]. rewrite Int.add_zero. reflexivity. }
          rewrite H78 at 2. clear H78.
          hoare name lift Aop pre.
          eapply seq_rule.
          eapply assign_rule_struct_member;[ | 
          clear;intros s'; split;[ intros Hs;exact Hs  |intros Hs;exact Hs ] | go | go | go 
          | idtac | idtac | symbolic_exe_port | idtac .. ].
          go.
          { clear - H73. unfold CHANNEL_CACHE_SZIE in *. cbn.
            rewrite Int.unsigned_repr by mauto.
            assert (Z.of_nat (length msg) <=? 255 = true) by lia.
            rewrite H. auto. }
          apply eq_int;auto.
          { intros ? Hs. subst. sep name lift p_local in Hs. unfold CurLINV. sep auto. }
          hoare normal pre.
          hoare lift 8%nat pre.
          destruct (∘ (Int.unsigned qentries)) as [ | pmsg_l] eqn :?;[ lia | ]. 
          cbn [dmportp_sllseg_qport_msg].
          hoare normal pre; pure intro.

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
            eapply rvl_elim; [sep_get_port_rv | ].
            eapply rvl_elim; [ | apply rvl_nil].
            eapply cast_rv_tint8_tint32. 
            sep_get_port_rv. split;[ | lia]. clear.
            destruct msg; lia.
          }
          { (* ==> pre*)
            intros; unfold_spec.
            sep normal. sep eexists.
            assert ((length msg) = (Z.to_nat (Int.unsigned ($  Z.of_nat (length msg))))).
            { rewrite Int.unsigned_repr. rewrite Nat2Z.id. auto.
              clear - H73. unfold CHANNEL_CACHE_SZIE in *. mauto. }
            rewrite H85 in H84 at 3.
            unfold Aarray at 1. sep cancel Aarray'.
            rewrite <- H78 in H84.
            apply Aarray_split in H84; auto.
            rewrite H85 in H84 at 1. sep cancel Aarray.
            sep name lift aemp_isr_is in H84. 
            sep name lift Ais in H84. sep name lift Aisr in H84.
            eapply elim_aemp_isr_is_prop in H84.
            sep autocancel. sep pauto.
            { unfold get_off_addr. cbn.
              rewrite ! Int.add_zero. auto. }
            { rewrite H78. clear. unfold CHANNEL_CACHE_SZIE. rewrite Z2Nat.id by lia. mauto. }
          }
          { good_frm_sovler. }
          { sep_unfold_funpost. intros. sep destruct H84. sep auto. }
          { sep_unfold_funpre. intros. sep destruct H84. sep auto. }
          { simpl; eauto. }
          unfold getasrt; unfold OS_memcopyPost, OS_memcopyPost'.
          hoare normal pre. pure intro.
          inversion H84. inversion H85. clear H84 H85. 
          subst v'26 v'27 v'28 v'30 v'31 v'32 v'33.
          clear v'25.

          (* ++ port_ptr ′ .. OSQOut;ₛ *)
          rewrite ! Int.add_zero.
          hoare name lift APortStruct pre.
          hoare name lift (Alvarmapsto port_ptr) pre.
          hoare name lift Aop pre.
          eapply seq_rule.
          eapply port_memeber_asgn with (n := 15%nat);[reflexivity | symbolic_exe_port | idtac .. ].
          1,2,3,4,5,6,8: cbn;eauto.
          { eapply eq_vptr; eauto. }
          { intros. sep auto. }

          (* −− port_ptr ′ .. OSQEntries;ₛ *)
          remember (update_nth_val 15 dport (Vptr (qstart_b, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)))) as dport'.
          assert (OS_Port_V_OSQEntries dport' = Some (Vint32 qentries)).
          { unfold OS_Port_V_OSQEntries in *. subst dport'. 
            eapply nth_upd_neqrev; eauto. }
          assert (struct_type_vallist_match' OS_Port_Seg_dls dport').
          { subst dport'. clear - H19.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; auto;
                  destruct dport; simpl in *; tryfalse). }
          eapply seq_rule.
          eapply port_memeber_asgn with (n := 17%nat);[reflexivity | symbolic_exe_port | idtac .. ].
          1,2,3,4,5,6: cbn;eauto.
          { apply eq_int; auto. }
          { cbn. clear - H71 H74 H72. 
            assert (Int.modu ($ 1) ($ Int16.modulus) = ($ 1)) by (clear;mauto).
            rewrite H;clear H.
            assert (Int.unsigned (qentries -ᵢ ($ 1)) <= 65535).
            { rewrite Int_unsigned_minus. 
              rewrite Int.unsigned_repr by (clear;mauto).
              lia.   
  Optimize Proof.
  Optimize Heap.
              simpl_intltbool. 
              rewrite Int.unsigned_repr by (clear;mauto).
              lia. }
            assert (Int.unsigned (qentries -ᵢ $ 1) <=? 65535 = true) by lia.
            rewrite H0. auto. }
          { intros. sep auto. }

          (* If (port_ptr ′ .. OSQOut ==ₑ port_ptr ′ .. OSQEnd) { ... } *)
          subst dport'. 
          assert (Int.modu ($ 1) ($ Int16.modulus) = ($ 1)) by (clear;mauto).
          rewrite H87; clear H87.
          remember(update_nth_val 17 (update_nth_val 15 dport
              (Vptr (qstart_b,  Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))))
                (Vint32 (qentries -ᵢ $ 1))) as dport'.
          assert (OS_Port_V_OSQOut dport' = Some (Vptr (qstart_b, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)))).
          { unfold OS_Port_V_OSQOut in *. subst dport'. 
            eapply nth_upd_neqrev. lia. 
            eapply update_nth; eauto. }
          assert (OS_Port_V_OSQEnd dport' = Some (Vptr (qstart_b, Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)))).
          { unfold OS_Port_V_OSQEnd in *. subst dport'. 
            eapply nth_upd_neqrev. lia. 
            eapply nth_upd_neqrev; eauto. }
          assert (struct_type_vallist_match' OS_Port_Seg_dls dport').
          { subst dport'. clear - H19 H71 H74 H72.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; auto;
                  destruct dport; simpl in *; tryfalse).
            assert (Int.unsigned (qentries -ᵢ ($ 1)) <= 65535).
            { rewrite Int_unsigned_minus. 
              rewrite Int.unsigned_repr by (clear;mauto).
              lia.   
              simpl_intltbool. 
              rewrite Int.unsigned_repr by (clear;mauto).
              lia. }
            assert (Int.unsigned (qentries -ᵢ $ 1) <=? 65535 = true) by lia.
            rewrite int16_max_unsigned_val, H18. auto. }

          (* abs step : qportpend_notnil *)
          hoare name lift oscoreheapid pre.
          hoare name lift oschannelid pre.
          hoare name lift oskportid pre.
          hoare name lift osdomainportid pre.
          hoare abscsq;[apply noabs_oslinv | | ].
          eapply portacc_queue_notnil_cont; eauto.
          can_change_aop_solver'.
          
          (* merge coreheap *)
          hoare name lift AOScoreheapl pre.
          hoare name lift (Aarray (msg_b, msg_i +ᵢ  $ 1)) pre.
          hoare name lift (get_off_addr (msg_b, msg_i) Int.zero) pre.
          hoare remember (1::2::nil)%nat pre.
          rewrite Int.unsigned_repr.
          2: { clear - H73. unfold CHANNEL_CACHE_SZIE in *. mauto. }
          rewrite Nat2Z.id.
          eapply backward_rule1 with (p:= Aarray (msg_b, msg_i)
          (Tarray char_t (S (length msg))) (V$ (Z.of_nat (length msg))::msg) ** H90 ).
          { unfold Aarray, get_off_addr. 
            cbn [Aarray' snd fst]. intros.
            sep cancel H90.
            cbn [typelen].
            assert (Z.of_nat 1 = 1)%Z by lia.
            rewrite H92.
            rewrite Int.add_zero in H91.
            sep auto. }
          subst H90.

          eapply backward_rule1.
          eapply AOScoreheapl_merge; eauto.
          { rewrite <- H82. lia. }
          { rewrite H82. lia. }
          { cbn. 
            assert (Int.unsigned ($ Z.of_nat (length msg)) <= 255).
            { clear - H73. unfold CHANNEL_CACHE_SZIE in *.  
              (* rewrite <- Zabs2Nat.abs_nat_nonneg in * by lia. *)
              assert (length msg <= 32)%nat by lia.
              clear - H.
              rewrite Int.unsigned_repr.
              lia. mauto. }
            assert (Int.unsigned ($ Z.of_nat (length msg)) <=? 255  = true) by lia.
            rewrite H91.
            split; auto.
            apply array_type_vallist_match_app in H83.
            tauto. }
          
          (* merge HeapInv' *)
          hoare name lift AOScoreheapt pre.
          hoare name lift AOScoreheape pre.
          hoare name lift AOScoreheapl pre.
          hoare name lift oscoreheapid pre.
          hoare remember (1::2::3::4::nil)%nat pre.
          eapply backward_rule1.
          {
            instantiate (1:=HeapInv' ** H90).
            intros. sep cancel H90.
            unfold HeapInv'. sep pauto.
            clear - H70. revert H70.
            induction cheapl1; simpl; intros; auto.
            eapply NoDup_cons_iff in H70; simpljoin1.
            eapply NoDup_cons; eauto.
            intro; destruct H.
            clear - H1.
            induction cheapl1; simpl; intros; auto.
            simpl in H1.
            destruct H1; [left|right]; eauto.
          }
          subst H90.

          (* merge qout Aarray *)
          hoare remember (14::16::nil)%nat pre.
          eapply backward_rule1.
          {
            instantiate (1:=Aarray (get_off_addr (qstart_b, Int.mul ($ z1) ($ 33)) (Int.one)) (Tarray Tint8 (nat_of_Z CHANNEL_CACHE_SZIE)) (msg++v'22) ** H90).
            intros.
            rewrite <- H78.
            eapply Aarray_merge; eauto.
            { rewrite H78. clear. unfold CHANNEL_CACHE_SZIE. mauto. }
            sep autocancel.
            unfold get_off_addr, fst, snd.
            rewrite H86; apply H91.
          }
          subst H90.

          (* merge dmportp_sllseg_qport_msg *)
          hoare remember (1::16::17::nil)%nat pre.
          eapply backward_rule1.
          {
            instantiate (1:=dmportp_sllseg_qport_msg
            (qstart_b, Int.mul ($ z1) ($ 33))
            (qstart_b, Int.mul ($ z2) ($ 33))
            (qstart_b, Int.zero)
            (qstart_b, Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33))
            ∘ (Int.unsigned qentries) (msg :: msgl) ** H90).
            intros.
            rewrite Heqn.
            cbn [dmportp_sllseg_qport_msg].
            sep normal; exists v'22. sep autocancel.
            sep pauto.
          }
          subst H90.

          hoare name lift APortStruct pre.
          hoare remember (1::nil)%nat pre.
          eapply forward_rule2.
          {
            instantiate (1:= ((EX dport_new, 
              [|Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)) 
              (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)) = true /\ dport_new = update_nth_val 15%nat dport' (Vptr (qstart_b, Int.zero)) \/ 
              Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)) 
              (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)) = false /\ dport_new = dport' |] ** 
              APortStruct pptr dport_new) ** H90)).
            subst H90.
            eapply forward_rule2.
            eapply ift_rule'';[ symbolic_exe_port | ].
            { (* port_ptr ′ .. OSQOut ==ₑ port_ptr ′ .. OSQEnd *)
              pure intro.
              rewrite peq_true in H90.
              assert (Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
                        (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)) = true) by pauto. 
              clear H91 H92 H90.
              remember (update_nth_val 17 (update_nth_val 15 dport (Vptr (qstart_b, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))))
                        (Vint32 (qentries -ᵢ $ 1)))  as dport'.
              assert (OS_Port_V_OSQStart dport' = Some (Vptr (qstart_b, Int.zero))).
              { unfold OS_Port_V_OSQStart in *. subst dport'. 
                eapply nth_upd_neqrev. lia. 
                eapply nth_upd_neqrev; eauto. }
              hoare name lift APortStruct pre.
              hoare name lift (Alvarmapsto port_ptr) pre.
              hoare name lift Aop pre.
              eapply port_memeber_asgn with (n := 15%nat);[reflexivity | symbolic_exe_port | idtac .. ].
              1,2,3,4,5,6,8:cbn;eauto.
              { eapply eq_vptr;eauto. }
              sep auto.
            }
            intros.
            destruct H90; sep normal in H90; sep normal.
            { exists  (update_nth_val 15 dport' (Vptr (qstart_b, Int.zero))).
              sep auto. left. pauto. }
            exists dport'. sep auto. right.
            destruct (Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
            (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33))).
            { exfalso. rewrite peq_true in H100. destruct H100; tryfalse.  }
            pauto.
          }

          subst H90 dport'.
          intros ? Hs. apply Hs.
        }

        eapply disj_rule.
        2: pure intro; eapply pfalse_rule.
        hoare normal pre; pure intro.
        clear H30 H70 H73.
        eapply disj_rule; hoare normal pre; pure intro.
        2:{
          destruct (Int.ltu ($ 0) qentries) eqn: ?; simpl in H30.
          destruct H30; inverts H30.
          clear H30.
          apply int_ltu_false_eq0 in Heqb.
          eapply backward_rule1.
          eapply dmportp_sllseg_qport_msg_length.
          pure intro.
          rewrite Heqb in H30; simpl in H30. tryfalse.
        }
        destruct (Int.ltu ($ 0) qentries) eqn: ?; simpl in H70; tryfalse.
        clear H70 H73 H74.
        rename v'22 into dport'.

        (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE) *)
        hoare forward.
        {
          hoare normal pre; pure intro.
          instantiate (1:=Afalse).
          exfalso; clear - H70; mauto.
        }
        hoare forward. hoare normal pre; pure intro.
        clear H70.

        (* aemp_isr_is *)
        eapply backward_rule1.
        {
          intros.
          sep name lift Aier in H70.
          sep name lift Ais in H70.
          sep name lift Aisr in H70.
          eapply add_aemp_isr_is_prop in H70.
          eapply H70.
        }

        (* EXIT_CRITICAL;ₛ *)
        apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
        unfold AOSCorePortPtrList.
        hoare normal pre; pure intro.
        rename H73 into Hcptr.
        destruct H30; simpljoin1.
        {
          hoare forward prim.
          {
            sep autocancel.
            unfold TmrInv; sep normal; sep autocancel.
            sep name lift PartitionInv; apply fold_PartitionInv_frm.
            sep cancel PartitionInv_part2.
            unfold PartitionInv_part1; sep normal; sep eexists; sep autocancel.
            sep split.
            {
              unfold AOSCorePortPtrList.
              sep pauto.
              2:{ instantiate (1:=(set dportls1 pptr
                  (Z.to_nat DNUM, ∘ (Int.unsigned x2), ∘ (Int.unsigned portid),
                  DestinationP next, ∘ (Int.unsigned x4), ∘ (Int.unsigned x5),
                  ∘ (Int.unsigned x6), QueuePort sz msgl))).
                  eapply RH_CorePortPtrList_upd_dportls; eauto. }

              (* cancel AOSDomainPortPtrList *)
              unfold AOSDomainPortPtrList, dmportp_sll.
              sep normal; sep autocancel.
              instantiate (8:=dportl1 ++ (update_nth_val 15
              (update_nth_val 17
                 (update_nth_val 15 dport
                    (Vptr
                       (qstart_b,
                       Int.mul ($ z1) ($ 33) +ᵢ
                       Int.mul ($ 1) ($ 33))))
                 (Vint32 (qentries -ᵢ $ 1)))
              (Vptr (qstart_b, Int.zero))) :: dportl2).
              instantiate (7:=dportmsgll1 ++ msgl :: dportmsgll2).
              eapply dmportp_sllseg_compose.
              auto.
  Optimize Proof.
  Optimize Heap.
              do 3 (eapply nth_upd_neqrev; eauto).
              { clear - H19 H71 Heqb H72.
                destruct dport; simpl in *; tryfalse.
                do 18 (destruct H19 as [? H19]; split; auto;
                      destruct dport; simpl in *; tryfalse).
                assert (Int.unsigned (qentries -ᵢ ($ 1)) <= 65535).
                { rewrite Int_unsigned_minus. 
                  rewrite Int.unsigned_repr by (clear;mauto).
                  lia.   
                  simpl_intltbool. 
                  rewrite Int.unsigned_repr by (clear;mauto).
                  lia. }
                assert (Int.unsigned (qentries -ᵢ $ 1) <=? 65535 = true) by lia.
                rewrite int16_max_unsigned_val, H18. auto. }
              do 3 (eapply nth_upd_neqrev; eauto).
              instantiate (7:=pptr).
              sep autocancel.
              eapply disj_split. right.
              sep normal.
              exists (qstart_b, Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33))
                     (qstart_b, Int.mul ($ z2) ($ 33))
                     (qstart_b, Int.zero) ($ Z.of_nat sz)
                     (qentries -ᵢ $ 1) (invalid_msg ++ (msg::nil)).
              assert (Z.of_nat (typelen OSMsg_t) = 33).
              { clear. simpl. lia. }
              sep split; eauto.
              2:{
                unfold Qport_msg_ptrs_P.
                splits; eauto.
                rewrite H73.
                unfold get_off_addr, fst, snd.
                rewrite Int.add_zero_l. auto.
                rewrite ! H73.
                exists 0 z2. splits; eauto.
                unfold get_off_addr, fst, snd.
                rewrite Int.add_zero_l. auto.
                lia.
              }
              2:{
                split.
                eapply nth_upd_neqrev; eauto.
                eapply update_nth; eauto.
                eapply nth_upd_neqrev; eauto.
                rewrite Int_unsigned_minus.
                rewrite Int.unsigned_repr by (clear;mauto).
                lia.   
                simpl_intltbool. 
                rewrite Int.unsigned_repr by (clear;mauto).
                lia.
              }
              2: split; [do 3 (eapply nth_upd_neqrev; eauto)|auto].
              2:{
                eapply update_nth; eauto.
                eapply nth_upd_neqrev; eauto.
                eapply update_nth; eauto.
              }
              2: do 3 (eapply nth_upd_neqrev; eauto).
              2: do 3 (eapply nth_upd_neqrev; eauto).
              2: do 3 (eapply nth_upd_neqrev; eauto).
              rewrite ! Int_unsigned_minus.
              2:{ simpl_intltbool. 
                  rewrite Int.unsigned_repr by (clear;mauto).
                  lia. }
              assert (∘ (Int.unsigned ($ Z.of_nat sz) -
                      (Int.unsigned qentries - Int.unsigned ($ 1))) = 
                      (∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned qentries) + 1)%nat).
              { rewrite Z.sub_sub_distr.
                rewrite (Int.unsigned_repr 1).
                unfold nat_of_Z.
                rewrite Z2Nat.inj_add.
                lia. lia. lia. clear. mauto. }
              rewrite H74.
              sep lift 2%nat.
              eapply dmportp_sllseg_qport_msg_app_frm.
              { sep lift 4%nat in H30.
                eapply dmportp_sllseg_qport_msg_length in H30.
                sep split in H30; auto. }
              auto.
              { sep lift 4%nat in H30.
                eapply dmportp_sllseg_qport_msg_R_qout_qin in H30.
                sep split in H30. eapply H75. }
              sep lift 4%nat in H30.
              sep cancel dmportp_sllseg_qport_msg.
              rewrite (Int.unsigned_repr 1).
              2: clear; mauto.
              assert (∘ (Int.unsigned qentries) = 
                      S ( ∘ (Int.unsigned qentries - 1) )).
              { unfold nat_of_Z.
                rewrite Z2Nat.inj_sub.
                assert (Z.to_nat 1 = 1%nat) by (clear; mauto).
                rewrite H75.
                rewrite minus_Sn_m.
                lia. clear - Heqb.
                simpl_intltbool.
                lia. lia. }
              rewrite H75 in H30.
              cbn [dmportp_sllseg_qport_msg] in *.
              sep normal in H30; sep destruct H30.
              sep normal; sep eexists; sep autocancel.
              assert (dmportp_sllseg_qport_msg_next
                      (qstart_b, Int.mul ($ z1) ($ 33)) 
                      (qstart_b, Int.zero)
                      (qstart_b,
                      Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)) =
                      (qstart_b, Int.zero)).
              {
                clear - H15 H70_z1_0 H70_z1_1 H72.
                assert ((qstart_b, Int.zero) =
                dmportp_msg_next_n 1 (qstart_b, Int.mul ($ z1) ($ 33))
                  (qstart_b, Int.zero) (qstart_b, Int.mul ($ (Z.of_nat 1 + z1)) ($ 33))).
                { eapply dmportp_msg_next_n_to_qstart; lia. }
                rewrite H at 2.
                cbn [dmportp_msg_next_n].
                assert (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33) = 
                        Int.mul ($ (Z.of_nat 1 + z1)) ($ 33)).
                2:{ rewrite H0; auto. }
                eapply Int_eq_dec in H15.
                rewrite <- H15.
                assert (Z.of_nat 1 = 1) by (clear; mauto).
                rewrite H0.
                assert (z1 < 65535) by lia.
                clear - H70_z1_0 H1.
                rewrite <- Int.mul_add_distr_l.
                assert (($ z1 +ᵢ  $ 1) = ($ (1 + z1))).
                2: rewrite H; auto.
                rewrite Int.add_unsigned.
                rewrite (Int.unsigned_repr 1).
                rewrite (Int.unsigned_repr z1).
                rewrite Z.add_comm at 1. auto.
                all: rewrite max_unsigned_val.
                all: lia.
              }
              rewrite H76 in H30. sep pauto.

              (* cancel AOSKernelPortIDTbl *)
              unfold AOSKernelPortIDTbl. sep pauto.
              instantiate (5:=kportl1 ++ (Vint32 portid
              :: Vint32 chanid :: Vptr pptr :: Vptr (chanpb, Int.zero)
              :: V$ DNUM :: Vint32 x1 :: x8 :: nil) :: kportl2).
              eapply kportNode_P_compose.
              rewrite H44; auto.
              pauto. eauto.
              sep autocancel.

              (* cancel AOSChannelIDTbl *)
              unfold AOSChannelIDTbl. sep pauto.
              instantiate (2:=chandstkportll1 ++ dstkportpl :: chandstkportll2).
              instantiate (2:=chanl1 ++ (Vint32 chanid :: Vint32 i1 :: Vint32 dpnum
                :: V$ DEFAULT_CHANNLE_SEMAPHROE :: v'29 :: x15 :: x16 :: x17 :: nil) :: chanl2).
              eapply ChannelNode_compose; eauto.
              rewrite H59; auto.
              rewrite H60; auto.
              unfold OS_Channel_V_dstPortsHead; simpl; eauto.
              unfold OS_Channel_V_dstPortsNum; simpl; eauto.
              pauto. sep autocancel. apply H30.
            }
            auto.
            eauto.
            eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
            eapply R_Kernelport_DomainPort_upd; eauto.
            rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
            eapply RLH_Channel_upd_dportls1; eauto.
            right; do 4 eexists; split; eauto.
            auto.
            eapply RLH_Domainportl_upd_Queue; eauto.
            rewrite H70; auto.
            unfold DomainportNode_P; splits; eauto.
            unfold Domainport_nat_P; do 5 eexists; repeat (splits; eauto).
            unfold Domainport_direction_P; split; eauto.
            unfold Domainport_Portt_P; splits; eauto.
            rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H32; do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H37; do 3 (eapply nth_upd_neqrev; eauto).
            do 3 (eapply nth_upd_neqrev; eauto).
            do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H29; do 3 (eapply nth_upd_neqrev; eauto).
            destruct next; rewrite Hnx; do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H48; do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H68; do 3 (eapply nth_upd_neqrev; eauto).
            split; eauto.
            eapply RL_PortPtrList_upd; eauto.
            rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
            eapply RL_PortAttr_upd; eauto.
            rewrite H29; do 3 (eapply nth_upd_neqrev; eauto).
            rewrite H48; do 3 (eapply nth_upd_neqrev; eauto).
            eapply join_set_set; eauto.
          }
          eauto.
          good_frm_sovler.
          eapply rete_rule.
          eapply inline_tactics.sep_infer_conjI.
          split.
          2: instantiate (1:=(V$ OS_NO_ERR)).
          {
            intros.
            sep normal; sep eexists; sep autocancel.
            sep pauto.
            simpl; eauto.
          }
          symbolic_execution.
        }
        hoare forward prim.
        {
          sep autocancel.
          unfold TmrInv; sep normal; sep autocancel.
          sep name lift PartitionInv; apply fold_PartitionInv_frm.
          sep cancel PartitionInv_part2.
          unfold PartitionInv_part1; sep normal; sep eexists; sep autocancel.
          sep split.
          {
            unfold AOSCorePortPtrList.
            sep pauto.
            2:{ instantiate (1:=(set dportls1 pptr
                (Z.to_nat DNUM, ∘ (Int.unsigned x2), ∘ (Int.unsigned portid),
                DestinationP next, ∘ (Int.unsigned x4), ∘ (Int.unsigned x5),
                ∘ (Int.unsigned x6), QueuePort sz msgl))).
                eapply RH_CorePortPtrList_upd_dportls; eauto. }
            (* cancel AOSDomainPortPtrList *)
            unfold AOSDomainPortPtrList, dmportp_sll.
            sep normal; sep autocancel.
            instantiate (8:=dportl1 ++ (update_nth_val 17
            (update_nth_val 15 dport (Vptr (qstart_b,
                  Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))))
            (Vint32 (qentries -ᵢ $ 1))) :: dportl2).
            instantiate (7:=dportmsgll1 ++ msgl :: dportmsgll2).
            eapply dmportp_sllseg_compose.
            auto.
  Optimize Proof.
  Optimize Heap.
            do 2 (eapply nth_upd_neqrev; eauto).
            { clear - H19 H71 Heqb H72.
              destruct dport; simpl in *; tryfalse.
              do 18 (destruct H19 as [? H19]; split; auto;
                    destruct dport; simpl in *; tryfalse).
              assert (Int.unsigned (qentries -ᵢ ($ 1)) <= 65535).
              { rewrite Int_unsigned_minus. 
                rewrite Int.unsigned_repr by (clear;mauto).
                lia.   
                simpl_intltbool. 
                rewrite Int.unsigned_repr by (clear;mauto).
                lia. }
              assert (Int.unsigned (qentries -ᵢ $ 1) <=? 65535 = true) by lia.
              rewrite int16_max_unsigned_val, H18. auto.
            }
            do 2 (eapply nth_upd_neqrev; eauto).
            instantiate (7:=pptr).
            sep autocancel.
            eapply disj_split. right.
            sep normal.
            exists (qstart_b, Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33))
                    (qstart_b, Int.mul ($ z2) ($ 33))
                    (qstart_b, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
                    ($ Z.of_nat sz) (qentries -ᵢ $ 1) (invalid_msg ++ (msg::nil)).
            assert (Z.of_nat (typelen OSMsg_t) = 33).
            { clear. simpl. lia. }
            sep split; eauto.
            2:{
              unfold Qport_msg_ptrs_P.
              splits; eauto.
              rewrite H73.
              unfold get_off_addr, fst, snd.
              rewrite Int.add_zero_l. auto.
              rewrite ! H73.
              exists (z1 + 1) z2. splits; eauto.
              1,2: unfold get_off_addr, fst, snd.
              1,2: rewrite Int.add_zero_l; auto.
              assert (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33) = Int.mul ($ (z1 + 1)) ($ 33)).
              2: rewrite H74; auto.
              rewrite <- Int.mul_add_distr_l.
              assert (($ z1 +ᵢ  $ 1) = ($ (z1 + 1))).
              2: rewrite H74; auto.
              rewrite Int.add_unsigned.
              rewrite (Int.unsigned_repr 1).
              rewrite (Int.unsigned_repr z1); auto.
              1,2: rewrite max_unsigned_val.
              1,2: lia.
              split. lia.
              assert (z1 + 1 < Int.unsigned ($ Z.of_nat sz) \/ 
                      z1 + 1 = Int.unsigned ($ Z.of_nat sz)) by lia.
              destruct H74; auto.
              exfalso. rewrite <- H74 in H30.
              assert (Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
              (Int.mul ($ (z1 + 1)) ($ 33)) = true).
              2: tryfalse.
              rewrite <- Int.mul_add_distr_l.
              assert (($ z1 +ᵢ  $ 1) = ($ (z1 + 1))).
              2: rewrite H75; apply Int.eq_true.
              rewrite Int.add_unsigned.
              rewrite (Int.unsigned_repr 1).
              rewrite (Int.unsigned_repr z1); auto.
              1,2: rewrite max_unsigned_val.
              1,2: lia.
            }
            2:{
              split.
              eapply update_nth; eauto.
              eapply nth_upd_neqrev; eauto.
              rewrite Int_unsigned_minus.
              rewrite Int.unsigned_repr by (clear;mauto).
              lia.   
              simpl_intltbool. 
              rewrite Int.unsigned_repr by (clear;mauto).
              lia.
            }
            2: split; [do 2 (eapply nth_upd_neqrev; eauto)|auto].
            2:{
              eapply nth_upd_neqrev; eauto.
              eapply update_nth; eauto.
            }
            2: do 2 (eapply nth_upd_neqrev; eauto).
            2: do 2 (eapply nth_upd_neqrev; eauto).
            2: do 2 (eapply nth_upd_neqrev; eauto).
            rewrite ! Int_unsigned_minus.
            2:{ simpl_intltbool. 
                rewrite Int.unsigned_repr by (clear;mauto).
                lia. }
            assert (∘ (Int.unsigned ($ Z.of_nat sz) -
                    (Int.unsigned qentries - Int.unsigned ($ 1))) = 
                    (∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned qentries) + 1)%nat).
            { rewrite Z.sub_sub_distr.
              rewrite (Int.unsigned_repr 1).
              unfold nat_of_Z.
              rewrite Z2Nat.inj_add.
              lia. lia. lia. clear. mauto. }
            rewrite H74.
            sep lift 2%nat.
            eapply dmportp_sllseg_qport_msg_app_frm.
            { sep lift 4%nat in H30.
              eapply dmportp_sllseg_qport_msg_length in H30.
              sep split in H30; auto. }
            auto.
            { sep lift 4%nat in H30.
              eapply dmportp_sllseg_qport_msg_R_qout_qin in H30.
              sep split in H30. eapply H75. }
            sep lift 4%nat in H30.
            sep cancel dmportp_sllseg_qport_msg.
            rewrite (Int.unsigned_repr 1).
            2: clear; mauto.
            assert (∘ (Int.unsigned qentries) = 
                    S ( ∘ (Int.unsigned qentries - 1) )).
            {
              unfold nat_of_Z.
              rewrite Z2Nat.inj_sub.
              assert (Z.to_nat 1 = 1%nat) by (clear; mauto).
              rewrite H75.
              rewrite minus_Sn_m.
              lia. clear - Heqb.
              simpl_intltbool.
              lia. lia.
            }
            rewrite H75 in H30.
            cbn [dmportp_sllseg_qport_msg] in *.
            sep normal in H30; sep destruct H30.
            sep normal; sep eexists; sep autocancel.
            assert (dmportp_sllseg_qport_msg_next
                    (qstart_b, Int.mul ($ z1) ($ 33)) 
                    (qstart_b, Int.zero)
                    (qstart_b,
                    Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33)) =
                    (qstart_b, Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))).
            {
              clear - H15 H70_z1_0 H70_z1_1 H72.
              unfold dmportp_sllseg_qport_msg_next, msg_distance, snd.
              assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).
              rewrite H; clear H.
              assert (Int.mul ($ 1) ($ 33) = $ 33) by (clear; mauto).
              rewrite H.
              destruct (Int.unsigned (Int.divu
                 (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33) -ᵢ
                  Int.mul ($ z1) ($ 33)) ($ 33)) =? 1) eqn: ?; auto.
              eapply Z.eqb_eq in Heqb.
              exfalso.
              assert (Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33) = 
                      Int.mul ($ z1) ($ 33) +ᵢ 
                      Int.mul ($ (Int.unsigned ($ Z.of_nat sz) - z1)) ($ 33)).
              {
                rewrite <- Int.mul_add_distr_l.
                assert ($ z1 +ᵢ  $ (Int.unsigned ($ Z.of_nat sz) - z1) = $ Int.unsigned ($ Z.of_nat sz)).
                2: rewrite H0; auto.
                rewrite Int.add_unsigned.
                rewrite (Int.unsigned_repr (Int.unsigned ($ Z.of_nat sz) - z1)).
                rewrite (Int.unsigned_repr z1). 
                rewrite BinInt.Zplus_minus; auto.
                1,2: rewrite max_unsigned_val; lia.
              }
              rewrite H0, Int.sub_add_l,
                      Int.sub_idem, Int.add_zero_l in Heqb.
              assert ((Int.divu (Int.mul ($ (Int.unsigned ($ Z.of_nat sz) - z1)) ($ 33))
              ($ 33)) = ($ (Int.unsigned ($ Z.of_nat sz) - z1))).
              {
                assert (exists a, a = (Int.unsigned ($ Z.of_nat sz) - z1)) by (eexists; eauto).
                destruct H1. rewrite <- H1.
                assert (x <= 65535) by lia.
                assert (0 < x) by lia.
                clear - H2 H3. mauto.
                rewrite Z_div_mult; mauto.
              }
              rewrite H1 in Heqb; clear H1.
              rewrite (Int.unsigned_repr (Int.unsigned ($ Z.of_nat sz) - z1)) in Heqb.
              2: rewrite max_unsigned_val; lia.
              assert (Int.unsigned ($ Z.of_nat sz) = z1 + 1) by lia.
              rewrite H1 in H15; clear H Heqb H0 H1.
              assert (Int.eq (Int.mul ($ z1) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
              (Int.mul ($ (z1 + 1)) ($ 33)) = true).
              2: tryfalse. clear H15.
              rewrite <- Int.mul_add_distr_l.
              assert (($ z1 +ᵢ  $ 1) = ($ (z1 + 1))).
              2: rewrite H; apply Int.eq_true.
              rewrite Int.add_unsigned.
              rewrite (Int.unsigned_repr 1).
              rewrite (Int.unsigned_repr z1); auto.
              1,2: rewrite max_unsigned_val.
              1,2: lia.
            }
            rewrite H76 in H30. sep pauto.

            (* cancel AOSKernelPortIDTbl *)
            unfold AOSKernelPortIDTbl. sep pauto.
            instantiate (5:=kportl1 ++ (Vint32 portid
            :: Vint32 chanid :: Vptr pptr :: Vptr (chanpb, Int.zero)
            :: V$ DNUM :: Vint32 x1 :: x8 :: nil) :: kportl2).
            eapply kportNode_P_compose.
            rewrite H44; auto.
            pauto. eauto.
            sep autocancel.

            (* cancel AOSChannelIDTbl *)
            unfold AOSChannelIDTbl. sep pauto.
            instantiate (2:=chandstkportll1 ++ dstkportpl :: chandstkportll2).
            instantiate (2:=chanl1 ++ (Vint32 chanid :: Vint32 i1 :: Vint32 dpnum
              :: V$ DEFAULT_CHANNLE_SEMAPHROE :: v'29 :: x15 :: x16 :: x17 :: nil) :: chanl2).
            eapply ChannelNode_compose; eauto.
            rewrite H59; auto.
            rewrite H60; auto.
            unfold OS_Channel_V_dstPortsHead; simpl; eauto.
            unfold OS_Channel_V_dstPortsNum; simpl; eauto.
            pauto. sep autocancel. apply H30.
          }
          auto.
  Optimize Proof.
  Optimize Heap.
          eauto.
          eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
          eapply R_Kernelport_DomainPort_upd; eauto.
          rewrite H34; do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H16; do 2 (eapply nth_upd_neqrev; eauto).
          eapply RLH_Channel_upd_dportls1; eauto.
          right; do 4 eexists; split; eauto.
          auto.
          eapply RLH_Domainportl_upd_Queue; eauto.
          rewrite H70; auto.
          unfold DomainportNode_P; splits; eauto.
          unfold Domainport_nat_P; do 5 eexists; repeat (splits; eauto).
          unfold Domainport_direction_P; split; eauto.
          unfold Domainport_Portt_P; splits; eauto.
          rewrite H16; do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H32; do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H34; do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H37; do 2 (eapply nth_upd_neqrev; eauto).
          do 2 (eapply nth_upd_neqrev; eauto).
          do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H29; do 2 (eapply nth_upd_neqrev; eauto).
          destruct next; rewrite Hnx; do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H48; do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H14; do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H68; do 2 (eapply nth_upd_neqrev; eauto).
          split; eauto.
          eapply RL_PortPtrList_upd; eauto.
          rewrite H14; do 2 (eapply nth_upd_neqrev; eauto).
          eapply RL_PortAttr_upd; eauto.
          rewrite H29; do 2 (eapply nth_upd_neqrev; eauto).
          rewrite H48; do 2 (eapply nth_upd_neqrev; eauto).
          eapply join_set_set; eauto.
        }
        eauto.
        good_frm_sovler.
        eapply rete_rule.
        eapply inline_tactics.sep_infer_conjI.
        split.
        2: instantiate (1:=(V$ OS_NO_ERR)).
        {
          intros.
          sep normal; sep eexists; sep autocancel.
          sep pauto.
          simpl; eauto.
        }
        symbolic_execution.
      }

      eapply backward_rule1.
      eapply dmportp_sllseg_qport_msg_length.
      pure intro. simpl in H30.
      rewrite <- H30.
      assert (Int.unsigned qentries = 0).
      { apply Z2Nat.inj.
        apply Int.unsigned_range. lia.
        unfold nat_of_Z in H30; rewrite <- H30. lia. }
      rewrite H70. rewrite Z.sub_0_r.
      cbn [dmportp_sllseg_qport_msg].
      naive pure intro.
      remember (Int.mul ($ z1) ($ 33)) as A.
      remember (Int.mul ($ z2) ($ 33)) as B.
      inversion H73; subst A B. clear H73.
      (* IF (port_ptr ′ .. mode ==ₑ ′ QUEUE) *)
      eapply seq_rule.
      {
        eapply if_rule2'.
        {
          symbolic_exe_port.
          unfold DomainportNode_P. splits; eauto.
          unfold Domainport_nat_P. do 5 eexists; repeat (splits; eauto).
          instantiate (2:=DestinationP next). unfold Domainport_direction_P. auto.
          instantiate (2:=QueuePort sz nil). unfold Domainport_Portt_P. splits; eauto.
        }
        2:{ (* sample is false *)
          hoare normal pre; pure intro.
          instantiate (1:=Afalse).
          exfalso; clear - H73; mauto.
        }
        hoare normal pre; pure intro.
        clear H73 H74 H76.

        (* If (port_ptr ′ .. OSQEntries >ₑ ′ 0) *)
        eapply ift_rule''; [ symbolic_exe_port | ].
        hoare normal pre; pure intro.
        instantiate (1:=Afalse).
        assert (Int.ltu ($ 0) qentries = true) by pauto.
        clear H73 H74 H76.
        assert (∘ (Int.unsigned qentries) > 0)%nat.
        { clear - H77. 
          rewrite <- (Int.repr_unsigned qentries) in H77.
          simpl_intltbool.
          erewrite Int.unsigned_repr in H77 by (apply Int.unsigned_range_2).
          rewrite <- Zabs2Nat.abs_nat_nonneg by lia. lia. }
        lia.
      }

      eapply disj_rule.
      2: pure intro; eapply pfalse_rule.
      hoare normal pre; pure intro.
      clear H73 H74 H76.
      hoare forward. hoare normal pre; pure intro.
      clear H73.

      (* choose portacc_queue_nil *)
      hoare abscsq; [apply noabs_oslinv | | ].
      eapply absinfer_choice1.
      3: intros ? Hs; apply Hs.
      1,2: can_change_aop_solver'.
      hoare name lift osdomainportid pre.
      hoare abscsq; [apply noabs_oslinv | | ].
      eapply portacc_queue_nil_cont; eauto.
      can_change_aop_solver'.

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE) *)
      hoare forward.
      {
        hoare normal pre; pure intro.
        instantiate (1:=Afalse).
        exfalso; clear - H73; mauto.
      }
      hoare forward. hoare normal pre; pure intro.
      clear H73.

      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      hoare forward prim.
      {
        sep autocancel.
        unfold TmrInv; sep normal; sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1; sep normal; sep eexists; sep autocancel.
        sep split.
        {
          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal; sep autocancel.
          instantiate (8:=dportl1 ++ dport :: dportl2).
          instantiate (7:=dportmsgll1 ++ nil :: dportmsgll2).
          eapply dmportp_sllseg_compose; eauto.
          instantiate (7:=pptr).
          sep autocancel.
          eapply disj_split. right.
          sep normal.
          exists (qstart_b, Int.mul ($ Int.unsigned ($ Z.of_nat sz)) ($ 33))
                  (qstart_b, Int.mul ($ z2) ($ 33))
                  (qstart_b, Int.mul ($ z2) ($ 33)) ($ Z.of_nat sz)
                  (Int.zero) (invalid_msg).
          assert (Z.of_nat (typelen OSMsg_t) = 33).
          { clear. simpl. lia. }
          sep split; eauto.
          2:{
            unfold Qport_msg_ptrs_P.
            splits; eauto.
            rewrite H15.
            unfold get_off_addr, fst, snd.
            rewrite Int.add_zero_l. auto.
            rewrite ! H15.
            exists z2 z2. splits; eauto;
            unfold get_off_addr, fst, snd;
            rewrite Int.add_zero_l; auto.
          }
          2:{
            split; auto.
            rewrite H69. do 2 f_equal.
            assert ($ Int.unsigned qentries = ($ 0)) by (rewrite H70; auto).
            rewrite Int.repr_unsigned in H76; rewrite H76.
            clear; mauto.
            assert (0 = Int.unsigned Int.zero) by (clear; mauto).
            rewrite <- H76; apply Int.unsigned_range.
          }
          2: rewrite <- H75; auto.
          assert (∘ (Int.unsigned Int.zero) = 0%nat) by (clear; mauto).
          rewrite H76; clear H76.
          assert (Int.unsigned Int.zero = 0) by (clear; mauto).
          rewrite H76, Z.sub_0_r; clear H76.
          cbn [dmportp_sllseg_qport_msg]. sep pauto.

          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl. sep pauto.
          instantiate (5:=kportl1 ++ (Vint32 portid
          :: Vint32 chanid :: Vptr pptr :: Vptr (chanpb, Int.zero)
          :: V$ DNUM :: Vint32 x1 :: x8 :: nil) :: kportl2).
          eapply kportNode_P_compose.
          rewrite H44; auto.
          pauto. eauto.
          sep autocancel.

          (* cancel AOSChannelIDTbl *)
          unfold AOSChannelIDTbl. sep pauto.
          instantiate (2:=chandstkportll1 ++ dstkportpl :: chandstkportll2).
          instantiate (2:=chanl1 ++ (Vint32 chanid :: Vint32 i1 :: Vint32 dpnum
            :: V$ DEFAULT_CHANNLE_SEMAPHROE :: v'29 :: x15 :: x16 :: x17 :: nil) :: chanl2).
          eapply ChannelNode_compose; eauto.
          rewrite H59; auto.
          rewrite H60; auto.
          unfold OS_Channel_V_dstPortsHead; simpl; eauto.
          unfold OS_Channel_V_dstPortsNum; simpl; eauto.
          pauto. sep autocancel. apply H74.
        }
        all: eauto.
        split; eauto.
      }
      eauto.
      good_frm_sovler.
      eapply rete_rule.
      eapply inline_tactics.sep_infer_conjI.
      split.
      2: instantiate (1:=(V$ OS_NO_ERR)).
      {
        intros.
        sep normal; sep eexists; sep autocancel.
        sep pauto.
        simpl; eauto.
      }
      symbolic_execution.
    }

    {
      unfold Domainport_Portt_P in H30; destruct p5; simpljoin1.
      (* queue is false *)
      2:{ rewrite H58 in H48; inverts H48. }
      rename x into msg.
      destruct msgptr as [msg_b msg_i].

      (* IF (port_ptr ′ .. mode ==ₑ ′ QUEUE) *)
      eapply seq_rule.
      {
        eapply if_rule2'.
        {
          symbolic_exe_port.
          unfold DomainportNode_P. splits; eauto.
          unfold Domainport_nat_P. do 5 eexists; repeat (splits; eauto).
          instantiate (2:=DestinationP next). unfold Domainport_direction_P. auto.
          instantiate (2:=SamplePort (Some msg)). 
          unfold Domainport_Portt_P. eexists; splits; eauto.
        }
        { (* queue is false *)
          hoare normal pre; pure intro.
          instantiate (1:=Afalse).
          exfalso; clear - H30; mauto.
        }
        hoare normal pre; pure intro.
        clear H30.
        rename v'23 into qstart.

        eapply if_rule2'.
        {
          symbolic_exe_port.
          unfold DomainportNode_P. splits; eauto.
          unfold Domainport_nat_P. do 5 eexists; repeat (splits; eauto).
          instantiate (2:=DestinationP next). unfold Domainport_direction_P. auto.
          instantiate (2:=SamplePort (Some msg)). 
          unfold Domainport_Portt_P. eexists; splits; eauto.
        }
        2:{ (* others is false *)
          hoare normal pre; pure intro.
          instantiate (1:=Afalse).
          exfalso; clear - H30; mauto.
        }
        hoare normal pre; pure intro.
        clear H30 H52 H66.

        (* choose portacc_sample (|Vptr pptr :: Vptr msgptr :: nil|) *)
        hoare abscsq; [apply noabs_oslinv | | ].
        eapply absinfer_choice2.
        3: intros ? Hs; apply Hs.
        1,2: can_change_aop_solver'.
        hoare abscsq; [apply noabs_oslinv | | ].
        eapply absinfer_choice2.
        3: intros ? Hs; apply Hs.
        1,2: can_change_aop_solver'.
        
        (* find qstart memory *)
        unfold dmportp_sllseg_sampleport_msg.
        hoare normal pre; pure intro.
        inversion H52; subst v'22; clear H52.
        rename v'23 into msg2.

        (* msg_ptr ′ .. len =ₑ (port_ptr ′ .. OSQStart) .. len;ₛ *)
        unfold TmrInv, HeapInv'.
        hoare normal pre; pure intro.
        hoare name lift oscoreheapid pre.
        rename v'22 into cHeapl.
        assert (~ In_heapl_addrval cHeapl (msg_b, msg_i) (S (length msg)) \/ In_heapl_addrval cHeapl (msg_b, msg_i) (S (length msg))) as [ | ] by tauto.
        { hoare name lift oschannelid pre.
          hoare name lift oskportid pre.
          hoare name lift osdomainportid pre.
          hoare abscsq; [apply noabs_oslinv | | ].
          eapply portacc_sample_abt; eauto.
          can_change_aop_solver'.
          apply absabort_rule. }
        
        hoare name lift AOScoreheapl pre.
        eapply backward_rule1.
        eapply port_split_coreheapl; eauto.
        naive pure intro.

        rename v'22 into cheapl1. rename v'25 into cheapl2.
        rename v'26 into ori_msgn. rename v'27 into ori_msg_vl. rename v'28 into ori_msg_vl2.
        simpljoin1.
        destruct ori_msg_vl as [ | ori_len_v ori_msg_vl ].
        simpl in H76; lia.
        hoare name lift Aarray pre.
        unfold Aarray. cbn [Aarray'].
        hoare normal pre.
        hoare name lift msg_ptr pre.
        assert ((msg_b, msg_i) = get_off_addr (msg_b, msg_i) Int.zero).
        { unfold get_off_addr. cbn [fst snd]. rewrite Int.add_zero. reflexivity. }
        rewrite H72 at 2. clear H72.
        hoare name lift Aop pre.
        eapply seq_rule.
        {
          eapply assign_rule_struct_member.
          8:{
            intros.
            eapply port_OSQStart_len_rv'.
            4:{ sep autocancel.
                sep lift 9%nat in H72.
                apply H72. }
            split; try lia.
            assert ((length msg <= ∘ CHANNEL_CACHE_SZIE)%nat).
            rewrite <- H30. apply Nat.le_add_r.
            unfold nat_of_Z in H75. 
            eapply Z2Nat.inj_le.
            lia. clear; unfold CHANNEL_CACHE_SZIE; mauto.
            rewrite Nat2Z.id; auto.
            auto. auto.
          }
          2: intros s'; split;[ intros Hs;exact Hs  |intros Hs;exact Hs ].
          2: go.
          go. go. go. go.
          assert (Z.of_nat (length msg) <= CHANNEL_CACHE_SZIE).
          eapply Z2Nat.inj_le.
          lia. clear; unfold CHANNEL_CACHE_SZIE; mauto.
          rewrite Nat2Z.id; unfold nat_of_Z in H30;
          rewrite <- H30; apply Nat.le_add_r.
          clear - H72. unfold CHANNEL_CACHE_SZIE in *. cbn.
          unfold language.msg in *.
          rewrite Int.unsigned_repr.
          2: rewrite max_unsigned_val; split; lia.
          assert (Z.of_nat (length msg) <=? 255 = true) by lia.
          rewrite H; auto.
          apply eq_int;auto.
          { intros ? Hs. subst. sep name lift p_local in Hs. unfold CurLINV. sep auto. }
        }
        hoare normal pre; pure intro.

        (* portacc_sample *)
        hoare name lift oscoreheapid pre.
        hoare name lift oschannelid pre.
        hoare name lift oskportid pre.
        hoare name lift osdomainportid pre.
        hoare abscsq; [apply noabs_oslinv | | ].
        eapply portacc_sample_cont; eauto.
        can_change_aop_solver'.
        
        (* memcpy (­msg_ptr ′ .. data, (port_ptr ′ .. OSQStart) .. data, (port_ptr ′ .. OSQStart) .. len­);ₛ *)
        eapply forward_rule2.
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
          eapply rvl_elim.
          eapply symbolic_lemmas.addrof_array_elem_rv.
          eapply port_OSQStart_data_rv.
          eapply H19. eauto.
          sep autocancel; apply H72.
          symbolic_execution. tauto.
          right; eexists; eauto.
          eapply rvl_elim; [ | apply rvl_nil].
          eapply cast_rv_tint8_tint32. 
          eapply port_OSQStart_len_rv'.
          4: sep lift 13%nat in H72.
          4: sep autocancel; apply H72.
          split; try lia.
          assert ((length msg <= ∘ CHANNEL_CACHE_SZIE)%nat).
          rewrite <- H30. apply Nat.le_add_r.
          unfold nat_of_Z in H75. 
          eapply Z2Nat.inj_le.
          lia. clear; unfold CHANNEL_CACHE_SZIE; mauto.
          rewrite Nat2Z.id; auto.
          auto. auto.
        }
        { (* ==> pre*)
          intros; unfold_spec.
          sep normal. sep eexists.
          assert ((length msg) = (Z.to_nat (Int.unsigned ($  Z.of_nat (length msg))))).
          { rewrite Int.unsigned_repr. rewrite Nat2Z.id. auto.
            assert (Z.of_nat (length msg) <= CHANNEL_CACHE_SZIE).
            eapply Z2Nat.inj_le.
            lia. clear; unfold CHANNEL_CACHE_SZIE; mauto.
            rewrite Nat2Z.id; unfold nat_of_Z in H30;
            rewrite <- H30; apply Nat.le_add_r.
            clear - H75. unfold CHANNEL_CACHE_SZIE in *. cbn.
            unfold language.msg in *. lia. }
          rewrite H75 in H72 at 2.
          unfold Aarray at 1. sep cancel Aarray'.
          rewrite <- H30 in H72.
          sep name lift Aarray' in H72.
          apply Aarray_split in H72; auto.
          unfold language.msg in H75.
          rewrite H75 in H72 at 1. sep cancel Aarray.
          sep name lift aemp_isr_is in H72. 
          sep name lift Ais in H72. sep name lift Aisr in H72.
          eapply elim_aemp_isr_is_prop in H72.
          sep autocancel. sep pauto.
          { unfold get_off_addr. cbn.
            rewrite ! Int.add_zero. auto. }
          { rewrite H30. clear. unfold CHANNEL_CACHE_SZIE. rewrite Z2Nat.id by lia. mauto. }
        }
        { good_frm_sovler. }
        { sep_unfold_funpost. intros. sep destruct H72. sep auto. }
        { sep_unfold_funpre. intros. sep destruct H72. sep auto. }
        { simpl; eauto. }
        unfold getasrt; unfold OS_memcopyPost, OS_memcopyPost'.
        intros. sep normal in H72; sep destruct H72.
        assert (logic_lv ori_msg_vl :: logic_lv msg :: logic_ier er
        :: logic_code s :: nil =
        logic_lv x9 :: logic_lv x10 :: logic_ier x12 :: logic_code x11 :: nil).
        sep split in H72. auto.
        assert (Vptr (msg_b, (msg_i +ᵢ  ($ 1 +ᵢ  Int.zero)) +ᵢ
        Int.mul ($ Z.of_nat (typelen char_t)) ($ 0)) :: Vptr
        (fst qstart, (snd qstart +ᵢ  Int.one) +ᵢ
        Int.mul ($ Z.of_nat (typelen char_t)) ($ 0))
        :: V$ Z.of_nat (length msg) :: nil =
        Vptr x0 :: Vptr x3 :: Vint32 x7 :: nil).
        sep split in H72. auto.
        inversion H75. inversion H77. clear H75 H77. 
        subst x0 x3 x7 x9 x10 x12 x11. clear x.
        rewrite ! Int.add_zero in *.

        (* merge coreheap *)
        sep name lift AOScoreheapl in H72.
        sep name lift (Aarray (msg_b, msg_i +ᵢ  $ 1)) in H72.
        sep name lift (get_off_addr (msg_b, msg_i) Int.zero) in H72.
        sep remember (1::2::nil)%nat in H72.
        rewrite Int.unsigned_repr in H72.
        2:{ assert (Z.of_nat (length msg) <= CHANNEL_CACHE_SZIE).
            eapply Z2Nat.inj_le.
            lia. clear; unfold CHANNEL_CACHE_SZIE; mauto.
            rewrite Nat2Z.id; unfold nat_of_Z in H30;
            rewrite <- H30; apply Nat.le_add_r.
            clear - H77. unfold CHANNEL_CACHE_SZIE in *. cbn.
            unfold language.msg in *. lia. }
        rewrite Nat2Z.id in H72.
        sep lift 3%nat in H72.
        eapply astar_mono in H72.
        3: instantiate (1:= Aarray (msg_b, msg_i)
        (Tarray char_t (S (length msg))) (V$ (Z.of_nat (length msg))::msg) ).
        2: eauto. sep lift 2%nat in H72.
        2:{ unfold Aarray, get_off_addr. 
            cbn [Aarray' snd fst]. intros.
            cbn [typelen].
            assert (Z.of_nat 1 = 1)%Z by lia.
            rewrite H78.
            rewrite Int.add_zero in H77.
            apply H77. }
        subst H75.

        sep remember (1::2::3::nil)%nat in H72.
        sep lift 4%nat in H72.
        eapply astar_mono in H72.
        2: eauto. sep lift 2%nat in H72.
        2: eapply AOScoreheapl_merge; eauto.
        2:{ rewrite <- H76. lia. }
        2:{ rewrite H76. lia. }
        2:{ cbn. 
            assert (Z.of_nat (length msg) <= CHANNEL_CACHE_SZIE).
            eapply Z2Nat.inj_le.
            lia. clear; unfold CHANNEL_CACHE_SZIE; mauto.
            rewrite Nat2Z.id; unfold nat_of_Z in H30;
            rewrite <- H30; apply Nat.le_add_r.
            split; auto.
            clear - H77. unfold CHANNEL_CACHE_SZIE in *. cbn.
            unfold language.msg in *.
            assert (Int.unsigned ($ Z.of_nat (length msg)) <= 255).
            assert (length msg <= 32)%nat by lia.
            clear - H.
            rewrite Int.unsigned_repr.
            lia. rewrite max_unsigned_val; lia.
            assert (Int.unsigned ($ Z.of_nat (length msg)) <=? 255  = true) by lia.
            rewrite H0; auto.
            apply array_type_vallist_match_app in H68.
            tauto. }
        
        (* merge HeapInv' *)
        subst H75.
        sep normal in H72.
        sep name lift AOScoreheapt in H72.
        sep name lift AOScoreheape in H72.
        sep name lift AOScoreheapl in H72.
        sep name lift oscoreheapid in H72.
        sep remember (1::2::3::4::nil)%nat in H72.
        sep lift 5%nat in H72.
        eapply astar_mono in H72.
        2: eauto. sep lift 2%nat in H72.
        2:{
          instantiate (1:=HeapInv').
          intros. unfold HeapInv'. sep pauto.
          clear - H52. revert H52.
          induction cheapl1; simpl; intros; auto.
          eapply NoDup_cons_iff in H52; simpljoin1.
          eapply NoDup_cons; eauto.
          intro; destruct H.
          clear - H1.
          induction cheapl1; simpl; intros; auto.
          simpl in H1.
          destruct H1; [left|right]; eauto.
        }
        subst H75.
        
        (* merge qstart Aarray *)
        sep remember (9::13::1::nil)%nat in H72.
        sep lift 4%nat in H72.
        eapply astar_mono in H72.
        2: eauto. sep lift 2%nat in H72.
        2:{
          instantiate (1:=Aarray (get_off_addr qstart (Int.one)) (Tarray Tint8 (nat_of_Z CHANNEL_CACHE_SZIE)) (msg++msg2) ** HeapInv').
          intros.
          rewrite <- H30.
          eapply Aarray_merge; eauto.
          { rewrite H30. clear. unfold CHANNEL_CACHE_SZIE. mauto. }
          sep autocancel.
          unfold get_off_addr.
          assert ((length msg) = (Z.to_nat (Int.unsigned ($  Z.of_nat (length msg))))).
          { rewrite Int.unsigned_repr. rewrite Nat2Z.id. auto.
            assert (Z.of_nat (length msg) <= CHANNEL_CACHE_SZIE).
            eapply Z2Nat.inj_le.
            lia. clear; unfold CHANNEL_CACHE_SZIE; mauto.
            rewrite Nat2Z.id; unfold nat_of_Z in H30;
            rewrite <- H30; apply Nat.le_add_r.
            clear - H78. unfold CHANNEL_CACHE_SZIE in *. cbn.
            unfold language.msg in *. lia. }
          unfold language.msg in H78; rewrite H78; apply H77.
        }
        subst H75.
        sep normal in H72.

        (* merge dmportp_sllseg_sampleport_msg *)
        sep remember (1::17::nil)%nat in H72.
        sep lift 3%nat in H72.
        eapply astar_mono in H72.
        2: eauto. sep lift 2%nat in H72.
        2:{
          instantiate (1:=dmportp_sllseg_sampleport_msg qstart (msg::nil)).
          intros.
          unfold dmportp_sllseg_sampleport_msg.
          sep normal; exists msg msg2. sep autocancel.
          sep pauto.
        }
        subst H75.
        sep remember (10::11::2::nil)%nat in H72.
        sep lift 4%nat in H72.
        eapply astar_mono in H72.
        2: eauto. sep lift 2%nat in H72.
        2:{
          instantiate (1:=HeapInv').
          intros. sep pauto.
        }
        subst H75. apply H72.
      }
      hoare forward.
      hoare normal pre; pure intro.
      clear H30.
      eapply disj_rule; hoare normal pre; pure intro.
      2: eapply pfalse_rule.
      clear H30 H52 H66.

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE) *)
      hoare forward.
      {
        hoare normal pre; pure intro.
        instantiate (1:=Afalse).
        exfalso; clear - H30; mauto.
      }
      hoare forward. hoare normal pre; pure intro.
      clear H30.

      (* aemp_isr_is *)
      eapply backward_rule1.
      {
        intros.
        sep name lift Aier in H30.
        sep name lift Ais in H30.
        sep name lift Aisr in H30.
        eapply add_aemp_isr_is_prop in H30.
        eapply H30.
      }

      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      hoare forward prim.
      {
        sep autocancel.
        unfold TmrInv; sep normal; sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1; sep normal; sep eexists; sep autocancel.
        sep split; eauto.
        2: split; eauto.

        (* cancel AOSDomainPortPtrList *)
        unfold AOSDomainPortPtrList, dmportp_sll.
        sep normal; sep autocancel.
        eapply dmportp_sllseg_compose; eauto.
        instantiate (2:=pptr).
        sep autocancel.
        eapply disj_split. left.
        sep pauto.

        (* cancel AOSKernelPortIDTbl *)
        unfold AOSKernelPortIDTbl. sep pauto.
        eapply kportNode_P_compose; eauto.
        rewrite H44; auto.
        sep autocancel.

        (* cancel AOSChannelIDTbl *)
        unfold AOSChannelIDTbl. sep pauto.
        eapply ChannelNode_compose; eauto.
        rewrite H59; auto.
        rewrite H60; auto.
        unfold OS_Channel_V_dstPortsHead; simpl; eauto.
        unfold OS_Channel_V_dstPortsNum; simpl; eauto.
        pauto. sep autocancel. apply H52.
      }
      eauto.
      good_frm_sovler.
      eapply rete_rule.
      eapply inline_tactics.sep_infer_conjI.
      split.
      2: instantiate (1:=(V$ OS_NO_ERR)).
      {
        intros.
        sep normal; sep eexists; sep autocancel.
        sep pauto.
        simpl; eauto.
      }
      symbolic_execution.
    }
  }
Qed.
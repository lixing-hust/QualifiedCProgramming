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
Require Import partinv_lemmas.

Open Scope code_scope.

Open Scope int_scope.

Lemma err_portnull_absinfer:
  forall (P : asrt) (sch : ossched),
    can_change_aop P ->
    sch ⊢  <|| err_portnull (|Vnull :: nil|) ||>  ** P ⇒  <|| END Some (V$ OS_PORT_ERR_NULL) ||>  ** P.
Proof.
  infer_solver 0%nat.
Qed.

Lemma err_unmapped_absinfer:
  forall (P : asrt) (sch : ossched) pptr dpl pcn pd pid pdir pst pin pout pt tcbl tid pri st msg sus,
    get dpl pptr = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) ->
    get tcbl tid = Some (pri, st, msg, sus) ->
    Int.eq (pri >>ᵢ $ 3) ($ Z.of_nat pd) = false ->
    can_change_aop P ->
    sch ⊢ 
      <|| err_unmapped (|Vptr pptr :: nil|) ||> **
      Hdomainportl dpl ** 
      HCurTCB tid ** 
      HTCBList tcbl ** P
    ⇒ 
      <|| END Some (V$ OS_ERR_PARTITION_UNMAPPED) ||> **
      Hdomainportl dpl ** 
      HCurTCB tid ** 
      HTCBList tcbl ** P.
Proof.
  infer_solver 0%nat.
Qed.

Lemma err_msgnull_absinfer:
  forall (P : asrt) (sch : ossched),
    can_change_aop P ->
    sch ⊢ 
      <|| err_msgnull OS_ERR_POST_NULL_PTR (|Vnull :: nil|) ||> ** P
    ⇒ 
      <|| END Some (V$ OS_ERR_POST_NULL_PTR) ||> ** P.
Proof.
  infer_solver 0%nat.
Qed.

Lemma err_porttype_absinfer:
  forall (P : asrt) (sch : ossched) pptr dpl pcn pd pid pdir pst pin pout pt,
    get dpl pptr = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) ->
    (pdir <> SourceP \/ (exists sz ml, pt = QueuePort sz ml)) ->
    can_change_aop P ->
    sch ⊢ 
      <|| err_porttype (|Vptr pptr :: nil|) ||> **
      Hdomainportl dpl ** P
    ⇒ 
      <|| END Some (V$ OS_PORT_ERR_TYPE) ||> **
      Hdomainportl dpl ** P.
Proof.
  infer_solver 0%nat.
Qed.

Lemma err_nochannel_absinfer:
  forall (P : asrt) (sch : ossched) pptr dpl pcn pd pid pdir pst pin pout pt kportl kpaddr kpst,
    get dpl pptr = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) ->
    get kportl kpaddr = Some (pid, Some pptr, None, pcn, kpst) ->
    can_change_aop P ->
    sch ⊢ 
      <|| err_nochannel (|Vptr pptr :: nil|) ||> **
      Hdomainportl dpl ** Hkernelport kportl ** P
    ⇒ 
      <|| END Some (V$ OS_ERR_PORT_NO_CHANNEL) ||> **
      Hdomainportl dpl ** Hkernelport kportl ** P.
Proof.
  infer_solver 0%nat.
Qed.

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


Lemma PortFlushProof :
  forall vl p r tid ,
    Some p = BuildPreA' os_api PortFlush portflushapi vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api PortFlush portflushapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api PortFlush = Some (t, d1, d2, s) /\
      {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |-tid {{p }} s {{ Afalse }}.
Proof.
  init_spec.

  hoare lift 6%nat pre.
  destruct v'.
  { apply absabort_rule. }

  (* resource_get_res ′ =ₑ ′ 0;ₛ
  channel ′ =ₑ 〈 OS_Channel ∗ 〉 NULL;ₛ
  kport ′ =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
  semaphore ′ =ₑ ′ DEFAULT_CHANNLE_SEMAPHROE;ₛ *)
  do 4 hoare forward.
  clear v'0 v'1 v'2 v'3.
  rename v'4 into er.

  (* ENTER_CRITICAL;ₛ
  If (port_ptr ′ ==ₑ 〈 OS_Port ∗ 〉 NULL)
  {EXIT_CRITICAL;ₛ
  RETURN 〈 char_t 〉 ′ OS_PORT_ERR_NULL};ₛ
  EXIT_CRITICAL;ₛ *)
  partition_enter_trinv.
  rename x into portptr.
  destruct H1 as [ | [? ? ]].
  {
    subst portptr.
    hoare name lift Aop pre.
    hoare abscsq; [apply noabs_oslinv | auto .. ].
    apply port_indomainport_null_abt.
    can_change_aop_solver'.
    apply absabort_rule.
  }
  subst portptr; rename x into pptr.
  hoare forward.
  destruct pptr;pauto.
  {
    pure intro.
    instantiate (1:= Afalse).
    exfalso.
    destruct pptr.
    simpl in H1; tryfalse.
  }
  hoare forward.
  pure intro.
  partition_exit_trinv.
  clear.

  (* ENTER_CRITICAL;ₛ
  If (port_ptr ′ .. coreNum !=ₑ ′ DNUM
      ||ₑ port_ptr ′ .. OSEventType !=ₑ ′ OS_EVENT_TYPE_PORT
      ||ₑ OSTCBCur ′ .. OSTCBY !=ₑ port_ptr ′ .. domain)
  {EXIT_CRITICAL;ₛ
  RETURN 〈 char_t 〉 ′ OS_ERR_PARTITION_UNMAPPED};ₛ
  EXIT_CRITICAL;ₛ *)
  partition_enter_trinv.

  (* ASSERT indomainport portptr abort;; *)
  hoare name lift osdomainportid pre.
  hoare name lift Aop pre.
  destruct (get dportls pptr) eqn: Hpptr.
  2:{
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply port_indomainport_none_abt.
      apply Hpptr.
      can_change_aop_solver'.
    }
    eapply absabort_rule.
  }
  destruct b as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].

  assert (p <> Z.to_nat DNUM \/ p = Z.to_nat DNUM) by tauto.
  destruct H11; [ | subst p].
  {
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply port_indomainport_none_abt'; eauto.
      can_change_aop_solver'.
    }
    eapply absabort_rule.
  }

  (* find port_ptr -> coreNum *)
  assert (get dportls1 pptr = Some (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5)).
  { eapply pptr_in_dportls1; eauto. }
  unfold RLH_PortPtrINecb in H3; destruct H3.
  assert (exists n dport msgl,
    nth_error dportl n = Some dport /\ nth_error dportmsgll n = Some msgl /\
    nth_error dpptrl n = Some pptr /\ DomainportNode_P dport (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5) msgl).
  { eapply RLH_Domainportl_abs_getsome; eauto. }
  destruct H13 as [n [dport [msg [? [? [? ?]]]]]].
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
  rename v'19 into pptr.

  (* find port_ptr -> OSEventType *)
  pose proof Forall_forall (fun x : addrval => exists wt, get ecbls x = Some (absport, wt)) dpptrl.
  destruct H13.
  pose proof nth_error_in _ _ H15.
  pose proof H13 H12 pptr H21 as [wt ?].
  clear H13 H17 H21.

  (* find OSTBCur *)
  rename v'8 into tcbls.
  unfold RH_CurTCB in H0.
  destruct H0 as [? [? [? [? ?]]]].
  rename v'2 into tcbl1.
  rename v'3 into tcbcur.
  rename v'4 into tcbl2.
  
  (* If (port_ptr ′ .. coreNum !=ₑ ′ DNUM ||ₑ port_ptr ′ .. OSEventType !=ₑ ′ OS_EVENT_TYPE_PORT
      ||ₑ OSTCBCur ′ .. OSTCBY !=ₑ port_ptr ′ .. domain)
  {EXIT_CRITICAL;ₛ
  RETURN 〈 char_t 〉 ′ OS_ERR_PARTITION_UNMAPPED};ₛ
  EXIT_CRITICAL;ₛ *)
  eapply seq_rule.
  {
    eapply ift_rule''; [symbolic_exe_port|idtac].
    hoare normal pre; pure intro.

    (* eq is false *)
    destruct (Int.eq (x >>ᵢ $ 3) ($ Z.of_nat p0)) eqn: Heq.
    {
      exfalso; clear - H13.
      unfold Int.notbool, bool_or in H13; simpl in H13.
      do 2 rewrite Int.eq_true in H13. simpl in H13.
      pauto.
    }

    hoare name lift osdomainportid pre.
    hoare name lift Aop pre.
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply port_indomainport_cont; eauto.
      can_change_aop_solver'.
    }

    (* err_unmapped (|Vptr pptr :: nil|) *)
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply absinfer_choice1.
      { can_change_aop_solver'. }
      2:{ intros ? Hs; apply Hs. }
      can_change_aop_solver'.
    }
    hoare name lift abstcblsid pre.
    hoare name lift curtid pre.
    hoare name lift osdomainportid pre.
    hoare name lift Aop pre.
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply err_unmapped_absinfer; eauto.
      can_change_aop_solver'.
    }
    partition_exit_trinv.
    hoare forward.
  }
  hoare forward.
  hoare normal pre; pure intro.
  partition_exit_trinv.
  clear.

  (* ENTER_CRITICAL;ₛ *)
  partition_enter_trinv.

  (* ASSERT indomainport portptr abort;; *)
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
  destruct H11; [ | subst p].
  {
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply port_indomainport_none_abt'; eauto.
      can_change_aop_solver'.
    }
    eapply absabort_rule.
  }

  assert (get dportls1 pptr = Some (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5)).
  { eapply pptr_in_dportls1; eauto. }
  unfold RLH_PortPtrINecb in H3; destruct H3.
  assert (exists n dport msgl,
    nth_error dportl n = Some dport /\ nth_error dportmsgll n = Some msgl /\
    nth_error dpptrl n = Some pptr /\ DomainportNode_P dport (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5) msgl).
  { eapply RLH_Domainportl_abs_getsome; eauto. }
  destruct H13 as [n [dport [msg [? [? [? ?]]]]]].
  apply nth_error_split in H13 as (dportl1 & dportl2 & ? & ?).
  apply nth_error_split in H14 as (dportmsgll1 & dportmsgll2 & ? & ?).
  subst dportl dportmsgll.
  unfold AOSDomainPortPtrList.
  hoare normal pre.
  hoare name lift dmportp_sll pre.
  eapply backward_rule1.
  eapply dmportp_sllseg_app'_frm;eauto.
  cbn [dmportp_sllseg].
  hoare normal pre; pure intro.
  rename v'19 into pptr.

  hoare name lift osdomainportid pre.
  hoare name lift Aop pre.
  hoare abscsq; [apply noabs_oslinv | | ].
  {
    eapply port_indomainport_cont; eauto.
    can_change_aop_solver'.
  }
  hoare abscsq; [apply noabs_oslinv | | ].
  {
    eapply absinfer_choice2; [ | | intros ? Hs; apply Hs ].
    all: can_change_aop_solver'.
  }

  (* kport ′ =ₑ OSKernelPortIDTbl ′ [port_ptr ′ .. portID];ₛ *)
  unfold AOSKernelPortIDTbl.
  hoare normal pre; pure intro.
  eapply seq_rule.
  {
    hoare name lift kport pre.
    hoare name lift Aop pre.
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
    eapply assign_rule_lvar.
    { intro s; split; intros; apply H29. }
    {
      intros.
      eapply symbolic_lemmas.array_member_rv_g.
      { sep autocancel; apply H29. }
      { go. }
      { eauto. }
      {
        eapply port_id_rv; eauto.
        sep autocancel; apply H29.
      }
      { go. }
      { auto. }
      { unfold PORT_NUMS; clear; mauto. }
      {
        unfold DomainportNode_P in H16; simpljoin1.
        unfold Domainport_nat_P in H16; simpljoin1.
        clear - H37.
        rewrite! Coqlib.nat_of_Z_eq.
        { rewrite int_usign_eq by (apply Int.unsigned_range_2); auto. }
        { unfold PORT_NUMS; lia. }
        pose proof Int.unsigned_range_2 x3; lia.
      }
      {
        unfold DomainportNode_P in H16; simpljoin1.
        unfold Domainport_nat_P in H16; simpljoin1.
        rewrite H21.
        clear - H37.
        rewrite! Coqlib.nat_of_Z_eq.
        { rewrite int_usign_eq by (apply Int.unsigned_range_2); auto. }
        { unfold PORT_NUMS; lia. }
        pose proof Int.unsigned_range_2 x3; lia.
      }
      2: eauto.
      go.
      unfold DomainportNode_P in H16; simpljoin1.
      unfold Domainport_nat_P in H16; simpljoin1.
      rewrite H35 in H22; inverts H22.
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
      rewrite H22; rewrite H23; auto.
    }
    { apply eq_vptr; eauto. }
    intros; sep eexists; sep autocancel; sep pauto.
  }
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
  rewrite H16 in H28. clear H31.
  rewrite Coqlib.nat_of_Z_eq.
  2: pose proof Int.unsigned_range_2 x; lia.
  rewrite int_usign_eq by (apply Int.unsigned_range_2).
  assert (nth_val' (Z.to_nat (Int.unsigned x)) kportvl = Vptr kpptr).
  { apply nth_val_nth_val'_some_eq; apply nth_val_nth_error; auto. }
  rewrite H22; clear H22.
  rename x into portid.

  (* If (os_code_defs.kport ′ .. channel !=ₑ 〈 OS_Channel ∗ 〉 NULL) *)
  hoare name lift kportNode_P pre.
  eapply backward_rule1.
  { eapply kportNode_P_getsome_frm; eauto. }
  naive pure intro.
  rename v'19 into kportpb. rename v'21 into kportpl1. rename v'22 into kportpl2.
  rename v'23 into kportl1. rename v'24 into kportl2.

  destruct H22, H35.
  subst kpptr kportvl kportl.

  assert (exists kporth, 
    KernelportNode_P kport kporth /\
    get kportls (kportpb, Int.zero) = Some kporth).
  {
    eapply RLH_Kernelport_abs_getsome; eauto.
    rewrite H40; auto.
  }  
  simpljoin1.
  destruct x as [[[[? ?] ?] ?] ?].
  unfold KernelportNode_P in H22; simpljoin1.
  unfold Kernelport_nat_P in H22; simpljoin1.
  rewrite H22 in H26; inverts H26.
  rewrite H44 in H28; inverts H28.
  unfold Kernelport_dmport_P in H33;
  destruct o; rewrite H33 in H27; inverts H27.
  rewrite int_usign_eq in *.
  2,3,4,5: clear; pose proof dnum_range; mauto.
  clear H38.

  hoare name lift Astruct' pre.
  hoare name lift os_code_defs.kport pre.
  pure intro.
  rename x3 into channel.
  unfold OS_K_Port_V_dmport in H33; simpl in H33; inverts H33.
  unfold OS_K_Port_V_portID in H22; simpl in H22; inverts H22.
  unfold OS_K_Port_V_status in H46; simpl in H46; inverts H46.
  unfold OS_K_Port_V_coreNum in H44; simpl in H44; inverts H44.
  
  destruct H28 as [? | [? ?]]; subst channel.
  {
    unfold Kernelport_channel_P in H42.
    destruct o0; unfold OS_K_Port_V_channel in H42;
      simpl in H42; inverts H42.
    
    eapply seq_rule.
    {
      eapply ift_rule''; [symbolic_exe_port|idtac].
      { pauto. }
      hoare normal pre; pure intro.
      instantiate (1:=Afalse).
      exfalso; clear - H22; mauto.
    }
    hoare forward.
    hoare normal pre; pure intro.
    clear H22.

    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply absinfer_choice2; [ | | intros ? Hs; apply Hs ].
      all: can_change_aop_solver'.
    }

    (* port_ptr ′ .. OSQIn =ₑ port_ptr ′ .. OSQStart;ₛ *)
    hoare name lift APortStruct pre.
    hoare name lift port_ptr pre.
    hoare name lift Aop pre.
    eapply seq_rule.
    {
      eapply port_memeber_asgn with (n := 14%nat).
      { pauto. }
      2: pauto.
      2:{
        eapply symbolic_lemmas.nth_val_imp_nth_val'_2.
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 14 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
        lia.
      }
      2: pauto.
      2: pauto.
      2: pauto.
      2: pauto.
      2:{
        instantiate (1:=OSMsg_t ∗).
        eapply eq_vptr; eauto.
      }
      {
        intros.
        eapply port_QStart_rv.
        3: eapply H22.
        2: eauto.
        auto.
      }
      { 
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 12 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
        destruct H19; auto.
      }
      { sep auto. }
    }

    (* port_ptr ′ .. OSQOut =ₑ port_ptr ′ .. OSQStart;ₛ *)
    hoare name lift APortStruct pre.
    hoare name lift port_ptr pre.
    hoare name lift Aop pre.
    eapply seq_rule.
    {
      eapply port_memeber_asgn with (n := 15%nat).
      { pauto. }
      2: pauto.
      2:{
        eapply nth_upd_neqrev; eauto.
        eapply symbolic_lemmas.nth_val_imp_nth_val'_2.
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 15 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
        lia.
      }
      2: pauto.
      2: pauto.
      2: pauto.
      2: pauto.
      2:{
        instantiate (1:=OSMsg_t ∗).
        eapply eq_vptr; eauto.
      }
      {
        intros.
        eapply port_QStart_rv.
        3: eapply H22.
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
        instantiate (1:=v'20); clear - H20.
        eapply nth_upd_neqrev; eauto.
      }
      { 
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 12 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
        destruct H19; auto.
      }
      { sep auto. }
    }

    (* port_ptr ′ .. OSQEntries =ₑ ′ 0;ₛ *)
    hoare name lift APortStruct pre.
    hoare name lift port_ptr pre.
    hoare name lift Aop pre.
    eapply seq_rule.
    {
      eapply port_memeber_asgn with (n := 17%nat).
      { pauto. }
      2: pauto.
      2:{
        eapply nth_upd_neqrev; eauto.
        eapply nth_upd_neqrev; eauto.
        eapply symbolic_lemmas.nth_val_imp_nth_val'_2.
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 17 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
        lia.
  Optimize Proof.
  Optimize Heap.
      }
      2: pauto.
      2: pauto.
      2: pauto.
      2: pauto.
      2:{
        instantiate (1:=Int32u).
        eapply eq_int; auto.
      }
      {
        intros.
        instantiate (1:= (V$ 0)).
        symbolic execution.
      }
      { pauto. }
      { sep auto. }
    }

    hoare lift 9%nat pre.
    eapply backward_rule1.
    { intros. eapply disj_split in H22. apply H22. }
    eapply disj_rule.
    (* sampleport *)
    {
      hoare normal pre; pure intro.
      unfold Domainport_Portt_P in H30; destruct p5; simpljoin1.
      2:{ rewrite H33 in H22; inverts H22. }
      clear H22.

      unfold dmportp_sllseg_sampleport_msg.
      hoare normal pre; pure intro.
      inversion H28; subst x; clear H28.
      rename v'20 into qstart.
      hoare name lift APortStruct pre.
      hoare name lift port_ptr pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      {
        eapply assign_rule_general.
        {
          intros.
          eapply symbolic_lemmas.struct_offset_rv.
          {
            eapply symbolic_lemmas.addrof_deref_rv.
            eapply port_QStart_rv.
            3: sep autocancel; apply H28.
            {
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
            }
            instantiate (1:=qstart); clear - H20.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          all: pauto.
        }
        {
          assert ((fst qstart, snd qstart +ᵢ  Int.zero) = qstart).
          { clear; destruct qstart; simpl; rewrite Int.add_zero; auto. }
          rewrite H28; split; intros.
          { sep autocancel; apply H44. }
          sep pauto.
        }
        {
          intros.
          instantiate (1:=(V$ 0)).
          instantiate (1:=long).
          symbolic_execution.
        }
        { eapply eq_int; tauto. }
        { sep auto. }
      }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
      {CSLSEMREL (semaphore ′)};ₛ *)
      hoare forward.
      {
        hoare normal pre; pure intro.
        instantiate (1:=Afalse).
        exfalso; clear - H28; pauto.
      }
      hoare forward.

      (* portflush_succ (|Vptr pptr :: nil|);; *)
      hoare normal pre; pure intro.
      clear H28.
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare name lift Aop pre.
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply portflush_succ_cont; eauto.
        can_change_aop_solver'.
      }
      
      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      subst dpptrl.
      unfold AOSCorePortPtrList.
      hoare normal pre; pure intro.
      hoare forward prim.
      {
        sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep split.
        {
          sep autocancel.
          (* cancel AOSCorePortPtrList *)
          unfold AOSCorePortPtrList.
          sep pauto.
          2:{ instantiate (1:=(set dportls1 pptr
                (Z.to_nat DNUM, ∘ (Int.unsigned x2),
                ∘ (Int.unsigned portid), d, ∘ (Int.unsigned x4),
                ∘ (Int.unsigned x5), ∘ (Int.unsigned x6),
                SamplePort (Some nil)))).
              eapply RH_CorePortPtrList_upd_dportls; eauto. }

          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl.
          sep normal; sep split.
          2: eapply H17.
          2: split; auto.
          sep autocancel.
          sep name lift kportNode_P.
          eapply kportNode_P_compose.
          4: sep autocancel.
          1,2,3: eauto; pauto.
          rewrite H40; auto.

          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal; sep autocancel.
          instantiate (3:=(dportl1 ++ (update_nth_val 17
          (update_nth_val 15
             (update_nth_val 14 dport (Vptr qstart))
             (Vptr qstart)) (V$ 0)) :: dportl2)).
          instantiate (2:=(dportmsgll1 ++ ((@nil val)::nil) :: dportmsgll2)).
          eapply dmportp_sllseg_compose; eauto.
          { do 3 (eapply nth_upd_neqrev; eauto). }
          {
            clear - H19.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
          }
          { do 3 (eapply nth_upd_neqrev; eauto). }
          sep autocancel.
          eapply disj_split; left.
          sep normal; sep split.
          2: do 3 (eapply nth_upd_neqrev; eauto).
          unfold dmportp_sllseg_sampleport_msg.
          sep normal; sep eexists; sep split.
          2: eauto.
          {
            instantiate (2:=v'19 ++ v'21).
            simpl (length _).
            assert ((fst qstart, snd qstart +ᵢ  Int.zero) = qstart).
            { clear; destruct qstart; simpl; rewrite Int.add_zero; auto. }
            rewrite H46 in H44.
            sep autocancel.
            apply H44.
          }
          simpl; split; auto.
        }
        auto.
        eauto.
        { eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto. }
        {
          eapply R_Kernelport_DomainPort_upd; eauto.
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
        }
        { eapply RLH_Channel_upd_dportls1; eauto. }
        { eauto. }
        {
          eapply RLH_Domainportl_upd_Sample; eauto.
          rewrite H28; auto.
          {
            unfold DomainportNode_P; splits; eauto.
            {
              unfold Domainport_nat_P.
              do 5 eexists; repeat (splits; eauto).
            }
            unfold Domainport_Portt_P.
            eexists; splits; eauto.
          }
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H32; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H37; do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
  Optimize Proof.
  Optimize Heap.
            }
            rewrite H46.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          {
            unfold OS_Port_V_OSEventPtrPort.
            assert (nth_val 10 dport = Some (nth_val' 10 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 10 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H46.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H33; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          unfold RLH_PortPtrINecb; split; eauto.
          eapply RL_PortPtrList_upd; eauto.
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          eapply RL_PortAttr_upd; eauto.
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H46.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H33; do 3 (eapply nth_upd_neqrev; eauto).
        }
        eapply join_set_l; eauto.
        eapply get_indom; eauto.
      }
      eauto.
      good_frm_sovler.
      
      (* RETURN ′ OS_NO_ERR *)
      hoare forward.
    }

    (* queueport *)
    hoare normal pre; pure intro.
    unfold Domainport_Portt_P in H30; destruct p5; simpljoin1.
    { rewrite H51 in H22; inverts H22. }
    clear H22.
    rewrite H44 in H50; inverts H50.
    rename v'20 into qstart.
    rename v'19 into qend.
    rename v'21 into qin.
    rename v'22 into qout.
    rename n into sz.

    unfold Qport_msg_ptrs_P in H47.
    destruct qstart as [qstartb qstarti].
    destruct H47 as [H47_ [H47_0 [z1 [z2 H47]]]].
    subst qstarti.
    unfold get_off_addr in H47, H47_0.
    cbn [fst snd] in *.
    destruct H47 as [? [? H47]].
    assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).
    rewrite H50 in *; clear H50.
    rewrite Int.add_zero_l in *.
    subst qend qout qin.
    rewrite Int.repr_unsigned in *.
    rename v'24 into entries.
    
    assert (z1 + Int.unsigned entries > Int.unsigned ($ Z.of_nat sz) \/
            z1 + Int.unsigned entries <= Int.unsigned ($ Z.of_nat sz)) by tauto.
    destruct H22.
    {
      assert ((qstartb, Int.zero) =
            dmportp_msg_next_n (Z.to_nat ((Int.unsigned ($ Z.of_nat sz)) - z1))
                                (qstartb, Int.mul ($ z1) ($ 33))
                                (qstartb, Int.zero)
                                (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))).
      {
        clear - H47 H49.
        destruct H47. clear z2 H0.
        assert (exists n, n = (Z.to_nat (Int.unsigned ($ Z.of_nat sz) - z1))) by eauto.
        destruct H0; rewrite <- H0.
        assert ((0 < x)%nat) by (subst x; lia).
        assert ((Z.of_nat x <= Int.unsigned ($ Z.of_nat sz))).
        { subst x; rewrite Z2Nat.id; lia. }
        assert (Z.of_nat x <= 65535) by lia.
        assert ($ Z.of_nat sz = $ ((Z.of_nat x) + z1)).
        {
          subst x; rewrite Z2Nat.id by lia.
          assert (Int.unsigned ($ Z.of_nat sz) - z1 + z1 =
                  Int.unsigned ($ Z.of_nat sz)) by lia.
          rewrite H0; rewrite Int.repr_unsigned; auto.
        }
        rewrite H4. rename z1 into y.
        assert (0 <= y) by lia.
        assert (Z.of_nat x + y <= 65535).
        {
          pose proof H49.
          rewrite H4 in H6.
          rewrite int_usign_eq in H6; try lia.
          assert (y < 65535) by lia.
          clear - H3 H7; mauto.
        }
        eapply dmportp_msg_next_n_to_qstart; eauto.
      }

      eapply backward_rule1.
      { eapply dmportp_sllseg_qport_msg_length. }
      naive pure intro.
      pose proof firstn_skipn (Z.to_nat (Int.unsigned ($ Z.of_nat sz) - z1)) msg.
      rewrite <- H52 at 1.
      assert (∘ (Int.unsigned entries) = ((Z.to_nat (Int.unsigned ($ Z.of_nat sz) - z1)) + 
        (∘ (Int.unsigned entries) - (Z.to_nat (Int.unsigned ($ Z.of_nat sz) - z1))))%nat).
      { apply le_plus_minus; unfold nat_of_Z; apply Zle_natle; lia. }
      rewrite H53 at 1.

      hoare remember (1::nil)%nat pre.
      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_app_frm.
        eapply firstn_length_le.
        rewrite H50; unfold nat_of_Z; apply Zle_natle; lia.
        rewrite skipn_length.
        rewrite H50; auto.
        eapply H30.
      }
      subst H54.
      hoare lift 2%nat pre.

      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_ngt0.
        assert ((Z.to_nat (Int.unsigned ($ Z.of_nat sz) - z1)
            < ∘ (Int.unsigned entries))%nat).
        apply Z2Nat.inj_lt.
        lia. apply Int.unsigned_range. lia. lia.
      }

      naive pure intro.
      destruct H54 as [msg0 [msg' [? ?]]].
      rewrite H54.
      remember (∘ (Int.unsigned entries) -
      Z.to_nat (Int.unsigned ($ Z.of_nat sz) - z1))%nat as u.
      destruct u.
      {
        assert (∘ (Int.unsigned entries) = Z.to_nat (Int.unsigned ($ Z.of_nat sz) - z1)) by lia.
        apply Z2Nat.inj in H56.
        lia. apply Int.unsigned_range. lia.
      }
      cbn [dmportp_sllseg_qport_msg].
      naive pure intro.

      (* (port_ptr ′ .. OSQStart) .. len =ₑ ′ 0;ₛ *)
      hoare name lift APortStruct pre.
      hoare name lift port_ptr pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      {
        eapply assign_rule_general.
        {
          intros.
          eapply symbolic_lemmas.struct_offset_rv.
          {
            eapply symbolic_lemmas.addrof_deref_rv.
            eapply port_QStart_rv.
            3: sep autocancel; apply H57.
            {
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
            }
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          all: pauto.
        }
        {
          unfold fst, snd.
          rewrite Int.add_zero.
          split; intros.
          { sep autocancel; apply H57. }
          sep pauto.
        }
        {
          intros.
          instantiate (1:=(V$ 0)).
          instantiate (1:=long).
          symbolic_execution.
        }
        { eapply eq_int; tauto. }
        { sep auto. }
      }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
      {CSLSEMREL (semaphore ′)};ₛ *)
      hoare forward.
      {
        hoare normal pre; pure intro.
        instantiate (1:=Afalse).
        exfalso; clear - H57; pauto.
      }
      hoare forward.

      (* portflush_succ (|Vptr pptr :: nil|);; *)
      hoare normal pre; pure intro.
      clear H57.
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare name lift Aop pre.
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply portflush_succ_cont; eauto.
        can_change_aop_solver'.
      }
      
      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      subst dpptrl.
      unfold AOSCorePortPtrList.
      hoare normal pre; pure intro.
      rename H15 into Hcptr.
      hoare forward prim.
      {
        sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep split.
        {
          sep autocancel.

          unfold AOSCorePortPtrList.
          sep pauto.
          2:{ instantiate (1:=(set dportls1 pptr
                (Z.to_nat DNUM, ∘ (Int.unsigned x2),
                ∘ (Int.unsigned portid), d, ∘ (Int.unsigned x4),
                ∘ (Int.unsigned x5), ∘ (Int.unsigned x6),
                QueuePort sz nil))).
              eapply RH_CorePortPtrList_upd_dportls; eauto. }
          
          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl.
          sep normal; sep split.
          2: eapply H17.
          2: split; auto.
          sep autocancel.
          sep name lift kportNode_P.
          eapply kportNode_P_compose.
          4: sep autocancel.
          1,2,3: eauto; pauto.
          rewrite H40; auto.

          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal; sep autocancel.
          instantiate (3:=(dportl1 ++ (update_nth_val 17
          (update_nth_val 15 (update_nth_val 14 dport
            (Vptr (qstartb, Int.zero))) (Vptr (qstartb, Int.zero))) 
              (V$ 0)) :: dportl2)).
          instantiate (2:=(dportmsgll1 ++ (nil) :: dportmsgll2)).
          eapply dmportp_sllseg_compose; eauto.
          { do 3 (eapply nth_upd_neqrev; eauto). }
          {
            clear - H19.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
          }
          { do 3 (eapply nth_upd_neqrev; eauto). }
          sep autocancel.
          eapply disj_split; right.
          sep normal.
          exists (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))
                 (qstartb, Int.zero) (qstartb, Int.zero)
                 ($ Z.of_nat sz) ($ 0)
                 (nil :: msg' ++ v'25 ++ (firstn (Z.to_nat
                    (Int.unsigned ($ Z.of_nat sz) - z1)) msg)).
          assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).    
          sep split.
          2:{
            unfold Qport_msg_ptrs_P.
            splits; auto.
            {
              rewrite H63, Int.repr_unsigned.
              unfold get_off_addr, fst, snd.
              rewrite Int.add_zero_l; auto.
            }
            exists 0 0.
            splits; auto; try lia.
          }
          2:{
            split.
            eapply update_nth; eauto.
            do 2 (eapply nth_upd_neqrev; eauto).
            assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
            rewrite H64; lia.
          }
          2:{
            split.
            do 3 (eapply nth_upd_neqrev; eauto).
            auto.
  Optimize Proof.
  Optimize Heap.
          }
          2:{
            eapply nth_upd_neqrev; eauto.
            eapply update_nth; eauto.
            eapply nth_upd_neqrev; eauto.
          }
          2:{
            do 2 (eapply nth_upd_neqrev; eauto).
            eapply update_nth; eauto.
          }
          2: do 3 (eapply nth_upd_neqrev; eauto).
          2: do 3 (eapply nth_upd_neqrev; eauto).
          assert (∘ (Int.unsigned ($ 0)) = 0%nat) by (clear; mauto).
          assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
          rewrite H64; rewrite H65.
          unfold dmportp_sllseg_qport_msg at 1.
          sep split; auto.
          rewrite Z.sub_0_r.
          assert (∘ (Int.unsigned ($ Z.of_nat sz)) = ((S u) + 
                  ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries) +
                  Z.to_nat (Int.unsigned ($ Z.of_nat sz) - z1))%nat).
          { rewrite Hequ; unfold nat_of_Z; lia. }
          rewrite H66.
          assert ((S u +
          ∘ (Int.unsigned ($ Z.of_nat sz) -
             Int.unsigned entries) +
          Z.to_nat (Int.unsigned ($ Z.of_nat sz) - z1))%nat = S (u +
          ∘ (Int.unsigned ($ Z.of_nat sz) -
             Int.unsigned entries) +
          Z.to_nat (Int.unsigned ($ Z.of_nat sz) - z1))%nat) by lia.
          rewrite H67.
          cbn [dmportp_sllseg_qport_msg].
          sep normal; exists (msg0 ++ v'19); sep split.
          2: split; auto.
          rewrite app_nil_l.
          unfold fst, snd in H15.
          rewrite Int.add_zero in H15.
          sep autocancel.
          instantiate (1:=LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
                          LV kport @ OS_K_Port ∗ |-> Vptr (kportpb, Int.zero) **
                          LV semaphore @ char_t |-> (V$ DEFAULT_CHANNLE_SEMAPHROE) **
                          LV channel @ OS_Channel ∗ |-> Vnull **
                          LV resource_get_res @ char_t |-> (V$ 0) **
                          A_dom_lenv
                            ((port_ptr, OS_Port ∗)
                              :: (kport, OS_K_Port ∗)
                                :: (channel, OS_Channel ∗)
                                    :: (semaphore, char_t)
                                      :: (resource_get_res, char_t) :: nil)).
          sep autocancel.
          assert ((u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries) +
          Z.to_nat (Int.unsigned ($ Z.of_nat sz) - z1))%nat =
          (u + (∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries) +
          Z.to_nat (Int.unsigned ($ Z.of_nat sz) - z1)))%nat ) by lia.
          rewrite H68; clear H68.
          eapply dmportp_sllseg_qport_msg_app.
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15.
            sep lift 3%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15.
            rewrite app_length; lia.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z2) ($ 33))).
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          sep autocancel.
          eapply dmportp_sllseg_qport_msg_app.
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z1) ($ 33))).
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          sep lift 2%nat in H15; apply H15.
        }
        auto.
        eauto.
        { eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto. }
        {
          eapply R_Kernelport_DomainPort_upd; eauto.
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
        }
        { eapply RLH_Channel_upd_dportls1; eauto.
          right; do 4 eexists; split; eauto. }
        { eauto. }
        {
          eapply RLH_Domainportl_upd_Queue; eauto.
          rewrite H57; auto.
          {
            unfold DomainportNode_P; splits; eauto.
            {
              unfold Domainport_nat_P.
              do 5 eexists; repeat (splits; eauto).
            }
            unfold Domainport_Portt_P; splits; eauto.
          }
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H32; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H37; do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H63.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          {
            unfold OS_Port_V_OSEventPtrPort.
            assert (nth_val 10 dport = Some (nth_val' 10 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 10 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H63.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H51; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H44; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          unfold RLH_PortPtrINecb; split; eauto.
          eapply RL_PortPtrList_upd; eauto.
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          eapply RL_PortAttr_upd; eauto.
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H63.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H51; do 3 (eapply nth_upd_neqrev; eauto).
        }
        eapply join_set_l; eauto.
        eapply get_indom; eauto.
      }
      eauto.
      good_frm_sovler.
      
      (* RETURN ′ OS_NO_ERR *)
      hoare forward.
    }

    assert (exists f, Int.unsigned f = Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries).
    {
      exists (Int.sub ($ Z.of_nat sz) entries).
      eapply Int_unsigned_minus. lia.
    }
    destruct H30 as [f ?]; rewrite <- H30.
    assert (Int.unsigned entries = Int.unsigned ($ Z.of_nat sz) - Int.unsigned f) by lia.
    rewrite H50.

    assert (z2 + Int.unsigned f > Int.unsigned ($ Z.of_nat sz) \/
            z2 + Int.unsigned f <= Int.unsigned ($ Z.of_nat sz)) by tauto.
    destruct H52.
    {
      hoare lift 2%nat pre.
      assert ((qstartb, Int.zero) =
            dmportp_msg_next_n (∘ ((Int.unsigned ($ Z.of_nat sz)) - z2))
                                (qstartb, Int.mul ($ z2) ($ 33))
                                (qstartb, Int.zero)
                                (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))).
      {
        clear - H47 H49.
        destruct H47. clear z1 H. rename H0 into H.
        assert (exists n, n = (∘ (Int.unsigned ($ Z.of_nat sz) - z2))) by eauto.
        destruct H0; rewrite <- H0.
        assert ((0 < x)%nat) by (subst x; unfold nat_of_Z in *; lia).
        assert ((Z.of_nat x <= Int.unsigned ($ Z.of_nat sz))).
        { subst x; rewrite Z2Nat.id; lia. }
        assert (Z.of_nat x <= 65535) by lia.
        assert ($ Z.of_nat sz = $ ((Z.of_nat x) + z2)).
        {
          subst x; rewrite Z2Nat.id by lia.
          assert (Int.unsigned ($ Z.of_nat sz) - z2 + z2 =
                  Int.unsigned ($ Z.of_nat sz)) by lia.
          rewrite H0; rewrite Int.repr_unsigned; auto.
        }
        rewrite H4. rename z2 into y.
        assert (0 <= y) by lia.
        assert (Z.of_nat x + y <= 65535).
        {
          pose proof H49.
          rewrite H4 in H6.
          rewrite int_usign_eq in H6; try lia.
          assert (y < 65535) by lia.
          clear - H3 H7; mauto.
        }
        eapply dmportp_msg_next_n_to_qstart; eauto.
      }
      rename v'25 into msg2.

      eapply backward_rule1.
      { eapply dmportp_sllseg_qport_msg_length. }
      naive pure intro.
      pose proof firstn_skipn ∘ (Int.unsigned ($ Z.of_nat sz) - z2) msg2.
      rewrite <- H55 at 1.
      
      assert (∘ (Int.unsigned f) = 
        (∘ (Int.unsigned ($ Z.of_nat sz) - z2) + 
        (∘ (Int.unsigned f) - ∘ (Int.unsigned ($ Z.of_nat sz) - z2)))%nat).
      { apply le_plus_minus; unfold nat_of_Z; apply Zle_natle; lia. }
      rewrite H56 at 1.

      hoare remember (1::nil)%nat pre.
      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_app_frm.
        eapply firstn_length_le.
        rewrite H54; unfold nat_of_Z; apply Zle_natle; lia.
        rewrite skipn_length.
        rewrite H54; auto.
        eapply H53.
      }
      subst H57.
      hoare lift 2%nat pre.

      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_ngt0.
        assert ((∘ (Int.unsigned ($ Z.of_nat sz) - z2)
            < ∘ (Int.unsigned f))%nat).
        apply Z2Nat.inj_lt.
        lia. apply Int.unsigned_range. lia. lia.
      }

      naive pure intro.
      destruct H57 as [msg0 [msg' [? ?]]].
      rewrite H57.
      remember (∘ (Int.unsigned f) -
      ∘ (Int.unsigned ($ Z.of_nat sz) - z2))%nat as u.
      destruct u.
      {
        assert (∘ (Int.unsigned f) = ∘ (Int.unsigned ($ Z.of_nat sz) - z2)) by lia.
        apply Z2Nat.inj in H59.
        lia. apply Int.unsigned_range. lia.
      }
      cbn [dmportp_sllseg_qport_msg].
      naive pure intro.

      (* (port_ptr ′ .. OSQStart) .. len =ₑ ′ 0;ₛ *)
      hoare name lift APortStruct pre.
      hoare name lift port_ptr pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      {
        eapply assign_rule_general.
        {
          intros.
          eapply symbolic_lemmas.struct_offset_rv.
          {
            eapply symbolic_lemmas.addrof_deref_rv.
            eapply port_QStart_rv.
            3: sep autocancel; apply H60.
            {
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
            }
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          all: pauto.
        }
        {
          unfold fst, snd.
          rewrite Int.add_zero.
          split; intros.
          { sep autocancel; apply H60. }
          sep pauto.
        }
        {
          intros.
          instantiate (1:=(V$ 0)).
          instantiate (1:=long).
          symbolic_execution.
        }
        { eapply eq_int; tauto. }
        { sep auto. }
      }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
      {CSLSEMREL (semaphore ′)};ₛ *)
      hoare forward.
      {
        hoare normal pre; pure intro.
        instantiate (1:=Afalse).
        exfalso; clear - H60; pauto.
      }
      hoare forward.

      (* portflush_succ (|Vptr pptr :: nil|);; *)
      hoare normal pre; pure intro.
      clear H60.
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare name lift Aop pre.
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply portflush_succ_cont; eauto.
        can_change_aop_solver'.
      }
      
      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      subst dpptrl.
      unfold AOSCorePortPtrList.
      hoare normal pre; pure intro.
      rename H15 into Hcptr.
      hoare forward prim.
      {
        sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep split.
        {
          sep autocancel.
          unfold AOSCorePortPtrList.
          sep pauto.
          2:{ instantiate (1:=(set dportls1 pptr
                (Z.to_nat DNUM, ∘ (Int.unsigned x2),
                ∘ (Int.unsigned portid), d, ∘ (Int.unsigned x4),
                ∘ (Int.unsigned x5), ∘ (Int.unsigned x6),
                QueuePort sz nil))).
              eapply RH_CorePortPtrList_upd_dportls; eauto. }

          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl.
          sep normal; sep split.
          2: eapply H17.
          2: split; auto.
          sep autocancel.
          sep name lift kportNode_P.
          eapply kportNode_P_compose.
          4: sep autocancel.
          1,2,3: eauto; pauto.
          rewrite H40; auto.

          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal; sep autocancel.
          instantiate (3:=(dportl1 ++ (update_nth_val 17
          (update_nth_val 15 (update_nth_val 14 dport
            (Vptr (qstartb, Int.zero))) (Vptr (qstartb, Int.zero))) 
              (V$ 0)) :: dportl2)).
          instantiate (2:=(dportmsgll1 ++ (nil) :: dportmsgll2)).
          eapply dmportp_sllseg_compose; eauto.
          { do 3 (eapply nth_upd_neqrev; eauto). }
          {
            clear - H19.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
          }
          { do 3 (eapply nth_upd_neqrev; eauto). }
          sep autocancel.
          eapply disj_split; right.
          sep normal.
          exists (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))
                (qstartb, Int.zero) (qstartb, Int.zero)
                ($ Z.of_nat sz) ($ 0)
                (nil :: msg' ++ msg ++ (firstn (
                  ∘ (Int.unsigned ($ Z.of_nat sz) - z2)) msg2)).
          assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).    
          sep split.
          2:{
            unfold Qport_msg_ptrs_P.
            splits; auto.
            {
              rewrite H66, Int.repr_unsigned.
              unfold get_off_addr, fst, snd.
              rewrite Int.add_zero_l; auto.
            }
            exists 0 0.
            splits; auto; try lia.
          }
          2:{
            split.
            eapply update_nth; eauto.
            do 2 (eapply nth_upd_neqrev; eauto).
            assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
            rewrite H67; lia.
          }
          2:{
            split.
            do 3 (eapply nth_upd_neqrev; eauto).
            auto.
  Optimize Proof.
  Optimize Heap.
          }
          2:{
            eapply nth_upd_neqrev; eauto.
            eapply update_nth; eauto.
            eapply nth_upd_neqrev; eauto.
          }
          2:{
            do 2 (eapply nth_upd_neqrev; eauto).
            eapply update_nth; eauto.
          }
          2: do 3 (eapply nth_upd_neqrev; eauto).
          2: do 3 (eapply nth_upd_neqrev; eauto).
          assert (∘ (Int.unsigned ($ 0)) = 0%nat) by (clear; mauto).
          assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
          rewrite H67; rewrite H68.
          unfold dmportp_sllseg_qport_msg at 1.
          sep split; auto.
          rewrite Z.sub_0_r.
          assert (∘ (Int.unsigned ($ Z.of_nat sz)) = ((S u) + 
                  ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f) +
                  ∘ (Int.unsigned ($ Z.of_nat sz) - z2))%nat).
          { rewrite Hequ; unfold nat_of_Z.
            assert (Int.unsigned f <= Int.unsigned ($ Z.of_nat sz)).
            { rewrite H30; pose proof Int.unsigned_range entries; lia. }
            lia. }
          rewrite H69.
          assert ((S u +
          ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f) +
          ∘ (Int.unsigned ($ Z.of_nat sz) - z2))%nat = S (u +
          ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f) +
          ∘ (Int.unsigned ($ Z.of_nat sz) - z2))%nat) by lia.
          rewrite H70.
          cbn [dmportp_sllseg_qport_msg].
          sep normal; exists (msg0 ++ v'19); sep split.
          2: split; auto.
          rewrite app_nil_l.
          unfold fst, snd in H15.
          rewrite Int.add_zero in H15.
          sep autocancel.
          instantiate (1:=LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
                          LV kport @ OS_K_Port ∗ |-> Vptr (kportpb, Int.zero) **
                          LV semaphore @ char_t |-> (V$ DEFAULT_CHANNLE_SEMAPHROE) **
                          LV channel @ OS_Channel ∗ |-> Vnull **
                          LV resource_get_res @ char_t |-> (V$ 0) **
                          A_dom_lenv
                            ((port_ptr, OS_Port ∗)
                              :: (kport, OS_K_Port ∗)
                                :: (channel, OS_Channel ∗)
                                    :: (semaphore, char_t)
                                      :: (resource_get_res, char_t) :: nil)).
          sep autocancel.
          assert ((u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f) +
          ∘ (Int.unsigned ($ Z.of_nat sz) - z2))%nat =
          (u + (∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f) +
          ∘ (Int.unsigned ($ Z.of_nat sz) - z2)))%nat ) by lia.
          rewrite H71; clear H71.
          eapply dmportp_sllseg_qport_msg_app.
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15.
            sep lift 3%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15.
            rewrite app_length; lia.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z1) ($ 33))).
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          sep autocancel.
          eapply dmportp_sllseg_qport_msg_app.
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z2) ($ 33))).
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          sep lift 2%nat in H15; apply H15.
        }
        auto.
        eauto.
        { eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto. }
        {
          eapply R_Kernelport_DomainPort_upd; eauto.
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
        }
        { eapply RLH_Channel_upd_dportls1; eauto.
          right; do 4 eexists; split; eauto. }
        { eauto. }
        {
          eapply RLH_Domainportl_upd_Queue; eauto.
          rewrite H60; auto.
          {
            unfold DomainportNode_P; splits; eauto.
            {
              unfold Domainport_nat_P.
              do 5 eexists; repeat (splits; eauto).
            }
            unfold Domainport_Portt_P; splits; eauto.
          }
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H32; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H37; do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H66.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          {
            unfold OS_Port_V_OSEventPtrPort.
            assert (nth_val 10 dport = Some (nth_val' 10 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 10 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H66.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H51; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H44; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          unfold RLH_PortPtrINecb; split; eauto.
          eapply RL_PortPtrList_upd; eauto.
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          eapply RL_PortAttr_upd; eauto.
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H66.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H51; do 3 (eapply nth_upd_neqrev; eauto).
        }
        eapply join_set_l; eauto.
        eapply get_indom; eauto.
      }
      eauto.
      good_frm_sovler.
      
      (* RETURN ′ OS_NO_ERR *)
      hoare forward.
    }

    rewrite <- H50. rewrite H30.
    assert ((z1 = 0 /\ Int.unsigned entries > 0) \/
            ((z1 > 0 /\ Int.unsigned entries > 0) \/ Int.unsigned entries = 0)) by lia.
    destruct H53.
    {
      destruct H53; subst z1.
      assert (Int.mul ($ 0) ($ 33) = Int.zero) by (clear; mauto).
      rewrite ! H53. clear H53.

      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_ngt0.
        unfold nat_of_Z. lia.
      }

      naive pure intro.
      destruct H53 as [msg0 [msg' [? ?]]].
      rewrite H53.
      remember (∘ (Int.unsigned entries)) as u.
      destruct u.
      { unfold nat_of_Z in Hequ. lia. }
      cbn [dmportp_sllseg_qport_msg].
      naive pure intro.

      (* (port_ptr ′ .. OSQStart) .. len =ₑ ′ 0;ₛ *)
      hoare name lift APortStruct pre.
      hoare name lift port_ptr pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      {
        eapply assign_rule_general.
        {
          intros.
          eapply symbolic_lemmas.struct_offset_rv.
          {
            eapply symbolic_lemmas.addrof_deref_rv.
            eapply port_QStart_rv.
            3: sep autocancel; apply H57.
            {
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
            }
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          all: pauto.
        }
        {
          unfold fst, snd.
          rewrite Int.add_zero.
          split; intros.
          { sep autocancel; apply H57. }
          sep pauto.
        }
        {
          intros.
          instantiate (1:=(V$ 0)).
          instantiate (1:=long).
          symbolic_execution.
        }
        { eapply eq_int; tauto. }
        { sep auto. }
      }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
      {CSLSEMREL (semaphore ′)};ₛ *)
      hoare forward.
      {
        hoare normal pre; pure intro.
        instantiate (1:=Afalse).
        exfalso; clear - H57; pauto.
      }
      hoare forward.

      (* portflush_succ (|Vptr pptr :: nil|);; *)
      hoare normal pre; pure intro.
      clear H57.
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare name lift Aop pre.
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply portflush_succ_cont; eauto.
        can_change_aop_solver'.
      }
      
      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      subst dpptrl.
      unfold AOSCorePortPtrList.
      hoare normal pre; pure intro.
      rename H15 into Hcptr.
      hoare forward prim.
      {
        sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep split.
        {
          sep autocancel.
          unfold AOSCorePortPtrList.
          sep pauto.
          2:{ instantiate (1:=(set dportls1 pptr
                (Z.to_nat DNUM, ∘ (Int.unsigned x2),
                ∘ (Int.unsigned portid), d, ∘ (Int.unsigned x4),
                ∘ (Int.unsigned x5), ∘ (Int.unsigned x6),
                QueuePort sz nil))).
              eapply RH_CorePortPtrList_upd_dportls; eauto. }

          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl.
          sep normal; sep split.
          2: eapply H17.
          2: split; auto.
          sep autocancel.
          sep name lift kportNode_P.
          eapply kportNode_P_compose.
          4: sep autocancel.
          1,2,3: eauto; pauto.
          rewrite H40; auto.

          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal; sep autocancel.
          instantiate (3:=(dportl1 ++ (update_nth_val 17
          (update_nth_val 15 (update_nth_val 14 dport
            (Vptr (qstartb, Int.zero))) (Vptr (qstartb, Int.zero))) 
              (V$ 0)) :: dportl2)).
          instantiate (2:=(dportmsgll1 ++ (nil) :: dportmsgll2)).
          eapply dmportp_sllseg_compose; eauto.
          { do 3 (eapply nth_upd_neqrev; eauto). }
          {
            clear - H19.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
          }
          { do 3 (eapply nth_upd_neqrev; eauto). }
          sep autocancel.
          eapply disj_split; right.
          sep normal.
          exists (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))
                 (qstartb, Int.zero) (qstartb, Int.zero)
                 ($ Z.of_nat sz) ($ 0) (nil :: msg' ++ v'25).
          assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).    
          sep split.
          2:{
            unfold Qport_msg_ptrs_P.
            splits; auto.
            {
              rewrite H57, Int.repr_unsigned.
              unfold get_off_addr, fst, snd.
              rewrite Int.add_zero_l; auto.
            }
            exists 0 0.
            splits; auto; try lia.
          }
          2:{
            split.
            eapply update_nth; eauto.
            do 2 (eapply nth_upd_neqrev; eauto).
            assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
            rewrite H63; lia.
          }
          2:{
            split.
            do 3 (eapply nth_upd_neqrev; eauto).
            auto.
  Optimize Proof.
  Optimize Heap.
          }
          2:{
            eapply nth_upd_neqrev; eauto.
            eapply update_nth; eauto.
            eapply nth_upd_neqrev; eauto.
          }
          2:{
            do 2 (eapply nth_upd_neqrev; eauto).
            eapply update_nth; eauto.
          }
          2: do 3 (eapply nth_upd_neqrev; eauto).
          2: do 3 (eapply nth_upd_neqrev; eauto).
          assert (∘ (Int.unsigned ($ 0)) = 0%nat) by (clear; mauto).
          assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
          rewrite H63; rewrite H64.
          unfold dmportp_sllseg_qport_msg at 1.
          sep split; auto.
          rewrite Z.sub_0_r.
          assert (∘ (Int.unsigned ($ Z.of_nat sz)) = ((S u) + 
                  ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries))%nat).
          { rewrite Hequ. unfold nat_of_Z. lia. }
          rewrite H65.
          assert ((S u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries))%nat =
                  S (u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries))%nat) by lia.
          rewrite H66.
          cbn [dmportp_sllseg_qport_msg].
          sep normal; exists (msg0 ++ v'19); sep split.
          2: split; auto.
          rewrite app_nil_l.
          unfold fst, snd in H15.
          rewrite Int.add_zero in H15.
          sep autocancel.
          instantiate (1:=LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
                          LV kport @ OS_K_Port ∗ |-> Vptr (kportpb, Int.zero) **
                          LV semaphore @ char_t |-> (V$ DEFAULT_CHANNLE_SEMAPHROE) **
                          LV channel @ OS_Channel ∗ |-> Vnull **
                          LV resource_get_res @ char_t |-> (V$ 0) **
                          A_dom_lenv
                            ((port_ptr, OS_Port ∗)
                              :: (kport, OS_K_Port ∗)
                                :: (channel, OS_Channel ∗)
                                    :: (semaphore, char_t)
                                      :: (resource_get_res, char_t) :: nil)).
          sep autocancel.
          eapply dmportp_sllseg_qport_msg_app.
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z2) ($ 33))).
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          apply H15.
        }
        auto.
        eauto.
        {
          
          eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
        }
        {
          eapply R_Kernelport_DomainPort_upd; eauto.
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
        }
        { eapply RLH_Channel_upd_dportls1; eauto.
          right; do 4 eexists; split; eauto. }
        { eauto. }
        {
          eapply RLH_Domainportl_upd_Queue; eauto.
          rewrite H53; auto.
          {
            unfold DomainportNode_P; splits; eauto.
            {
              unfold Domainport_nat_P.
              do 5 eexists; repeat (splits; eauto).
            }
            unfold Domainport_Portt_P; splits; eauto.
          }
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H32; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H37; do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H57.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          {
            unfold OS_Port_V_OSEventPtrPort.
            assert (nth_val 10 dport = Some (nth_val' 10 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 10 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H57.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H51; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H44; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          unfold RLH_PortPtrINecb; split; eauto.
          eapply RL_PortPtrList_upd; eauto.
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          eapply RL_PortAttr_upd; eauto.
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H57.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H51; do 3 (eapply nth_upd_neqrev; eauto).
        }
        eapply join_set_l; eauto.
        eapply get_indom; eauto.
      }
      eauto.
      good_frm_sovler.
      
      (* RETURN ′ OS_NO_ERR *)
      hoare forward.
    }

    rewrite <- H30. rewrite H50.
    hoare lift 2%nat pre.
    assert ((z2 = 0 /\ Int.unsigned f > 0) \/
            ((z2 > 0 /\ Int.unsigned f > 0) \/ Int.unsigned f = 0)) by lia.
    destruct H54.
    {
      destruct H54; subst z2.
      assert (Int.mul ($ 0) ($ 33) = Int.zero) by (clear; mauto).
      rewrite ! H54. clear H54.

      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_ngt0.
        unfold nat_of_Z. lia.
      }

      naive pure intro.
      destruct H54 as [msg0 [msg' [? ?]]].
      rewrite H54.
      remember (∘ (Int.unsigned f)) as u.
      destruct u.
      { unfold nat_of_Z in Hequ. lia. }
      cbn [dmportp_sllseg_qport_msg].
      naive pure intro.

      (* (port_ptr ′ .. OSQStart) .. len =ₑ ′ 0;ₛ *)
      hoare name lift APortStruct pre.
      hoare name lift port_ptr pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      {
        eapply assign_rule_general.
        {
          intros.
          eapply symbolic_lemmas.struct_offset_rv.
          {
            eapply symbolic_lemmas.addrof_deref_rv.
            eapply port_QStart_rv.
            3: sep autocancel; apply H58.
            {
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
            }
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          all: pauto.
        }
        {
          unfold fst, snd.
          rewrite Int.add_zero.
          split; intros.
          { sep autocancel; apply H58. }
          sep pauto.
        }
        {
          intros.
          instantiate (1:=(V$ 0)).
          instantiate (1:=long).
          symbolic_execution.
        }
        { eapply eq_int; tauto. }
        { sep auto. }
      }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
      {CSLSEMREL (semaphore ′)};ₛ *)
      hoare forward.
      {
        hoare normal pre; pure intro.
        instantiate (1:=Afalse).
        exfalso; clear - H58; pauto.
      }
      hoare forward.

      (* portflush_succ (|Vptr pptr :: nil|);; *)
      hoare normal pre; pure intro.
      clear H58.
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare name lift Aop pre.
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply portflush_succ_cont; eauto.
        can_change_aop_solver'.
      }
      
      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      subst dpptrl.
      unfold AOSCorePortPtrList.
      hoare normal pre; pure intro.
      rename H15 into Hcptr.
      hoare forward prim.
      {
        sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep split.
        {
          sep autocancel.
          unfold AOSCorePortPtrList.
          sep pauto.
          2:{ instantiate (1:=(set dportls1 pptr
              (Z.to_nat DNUM, ∘ (Int.unsigned x2),
              ∘ (Int.unsigned portid), d, ∘ (Int.unsigned x4),
              ∘ (Int.unsigned x5), ∘ (Int.unsigned x6),
              QueuePort sz nil))).
              eapply RH_CorePortPtrList_upd_dportls; eauto. }

          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl.
          sep normal; sep split.
          2: eapply H17.
          2: split; auto.
          sep autocancel.
          sep name lift kportNode_P.
          eapply kportNode_P_compose.
          4: sep autocancel.
          1,2,3: eauto; pauto.
          rewrite H40; auto.

          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal; sep autocancel.
          instantiate (3:=(dportl1 ++ (update_nth_val 17
          (update_nth_val 15 (update_nth_val 14 dport
            (Vptr (qstartb, Int.zero))) (Vptr (qstartb, Int.zero))) 
              (V$ 0)) :: dportl2)).
          instantiate (2:=(dportmsgll1 ++ (nil) :: dportmsgll2)).
          eapply dmportp_sllseg_compose; eauto.
          { do 3 (eapply nth_upd_neqrev; eauto). }
          {
            clear - H19.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
          }
          { do 3 (eapply nth_upd_neqrev; eauto). }
          sep autocancel.
          eapply disj_split; right.
          sep normal.
          exists (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))
                 (qstartb, Int.zero) (qstartb, Int.zero)
                 ($ Z.of_nat sz) ($ 0) (nil :: msg' ++ msg).
          assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).    
          sep split.
          2:{
            unfold Qport_msg_ptrs_P.
            splits; auto.
            {
              rewrite H58, Int.repr_unsigned.
              unfold get_off_addr, fst, snd.
              rewrite Int.add_zero_l; auto.
            }
            exists 0 0.
            splits; auto; try lia.
          }
          2:{
            split.
            eapply update_nth; eauto.
            do 2 (eapply nth_upd_neqrev; eauto).
            assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
            rewrite H64; lia.
          }
          2:{
            split.
            do 3 (eapply nth_upd_neqrev; eauto).
            auto.
  Optimize Proof.
  Optimize Heap.
          }
          2:{
            eapply nth_upd_neqrev; eauto.
            eapply update_nth; eauto.
            eapply nth_upd_neqrev; eauto.
          }
          2:{
            do 2 (eapply nth_upd_neqrev; eauto).
            eapply update_nth; eauto.
          }
          2: do 3 (eapply nth_upd_neqrev; eauto).
          2: do 3 (eapply nth_upd_neqrev; eauto).
          assert (∘ (Int.unsigned ($ 0)) = 0%nat) by (clear; mauto).
          assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
          rewrite H64; rewrite H65.
          unfold dmportp_sllseg_qport_msg at 1.
          sep split; auto.
          rewrite Z.sub_0_r.
          assert (∘ (Int.unsigned ($ Z.of_nat sz)) = ((S u) + 
                  ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f))%nat).
          { rewrite Hequ. unfold nat_of_Z. lia. }
          rewrite H66.
          assert ((S u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f))%nat =
                  S (u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f))%nat) by lia.
          rewrite H67.
          cbn [dmportp_sllseg_qport_msg].
          sep normal; exists (msg0 ++ v'19); sep split.
          2: split; auto.
          rewrite app_nil_l.
          unfold fst, snd in H15.
          rewrite Int.add_zero in H15.
          sep autocancel.
          instantiate (1:=LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
                          LV kport @ OS_K_Port ∗ |-> Vptr (kportpb, Int.zero) **
                          LV semaphore @ char_t |-> (V$ DEFAULT_CHANNLE_SEMAPHROE) **
                          LV channel @ OS_Channel ∗ |-> Vnull **
                          LV resource_get_res @ char_t |-> (V$ 0) **
                          A_dom_lenv
                            ((port_ptr, OS_Port ∗)
                              :: (kport, OS_K_Port ∗)
                                :: (channel, OS_Channel ∗)
                                    :: (semaphore, char_t)
                                      :: (resource_get_res, char_t) :: nil)).
          sep autocancel.
          eapply dmportp_sllseg_qport_msg_app.
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z1) ($ 33))).
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          apply H15.
        }
        auto.
        eauto.
        {
          eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
        }
        {
          eapply R_Kernelport_DomainPort_upd; eauto.
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
        }
        { eapply RLH_Channel_upd_dportls1; eauto.
          right; do 4 eexists; split; eauto. }
        { eauto. }
        {
          eapply RLH_Domainportl_upd_Queue; eauto.
          rewrite H54; auto.
          {
            unfold DomainportNode_P; splits; eauto.
            {
              unfold Domainport_nat_P.
              do 5 eexists; repeat (splits; eauto).
            }
            unfold Domainport_Portt_P; splits; eauto.
          }
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H32; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H37; do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H58.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          {
            unfold OS_Port_V_OSEventPtrPort.
            assert (nth_val 10 dport = Some (nth_val' 10 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 10 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H58.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H51; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H44; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          unfold RLH_PortPtrINecb; split; eauto.
          eapply RL_PortPtrList_upd; eauto.
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          eapply RL_PortAttr_upd; eauto.
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H58.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H51; do 3 (eapply nth_upd_neqrev; eauto).
        }
        eapply join_set_l; eauto.
        eapply get_indom; eauto.
      }
      eauto.
      good_frm_sovler.
      
      (* RETURN ′ OS_NO_ERR *)
      hoare forward.
    }
      
    destruct H53. 2: lia.
    destruct H54. 2: lia.
    rewrite <- H50; rewrite H30.
    hoare lift 2%nat pre.
    eapply backward_rule1.
    {
      eapply dmportp_sllseg_qport_msg_Rle_z1_z2; eauto.
      rewrite Z2Nat.id. all: lia.
    }
    naive pure intro.
    subst z2. rewrite H30 in H52.
    assert (z1 + Z.of_nat ∘ (Int.unsigned entries) +
    (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries) = z1 + Int.unsigned ($ Z.of_nat sz)).
    { rewrite Z2Nat.id. lia. lia. }
    rewrite H55 in H52.
    exfalso; destruct H53; clear - H52 H53; lia.
  }
  unfold Kernelport_channel_P in H42.
  destruct o0; unfold OS_K_Port_V_channel in H42;
    simpl in H42; inverts H42.
  rename a into chan.

  assert (R_KernelPortIDTbl_ChannelIDTbl_chan_Vptr
    (kportpb, Int.zero) (Vint32 portid :: Vint32 i1 :: Vptr pptr :: Vptr chan
    :: V$ DNUM :: Vint32 x1 :: x9 :: nil) chanvl chanl chandstkportll kportls dportls1 dportls2).
  {
    eapply R_KernelPortIDTbl_ChannelIDTbl_abs_getsome; eauto.
    { rewrite H40; auto. }
    unfold OS_K_Port_V_channel; simpl; eauto.
  }
  
  unfold R_KernelPortIDTbl_ChannelIDTbl_chan_Vptr in H22; simpljoin1.
  unfold OS_K_Port_V_channelID in H22; simpl in H22;
    inverts H22; rename x into chanid.
  unfold OS_K_Port_V_channel in H28; simpl in H28;
    inverts H28; rename x0 into chanptr.
  unfold AOSChannelIDTbl.
  hoare normal pre; pure intro.

  hoare name lift ChannelNode pre.
  eapply backward_rule1.
  { eapply ChannelNode_getsome_frm; eauto. }
  unfold node; hoare normal pre; pure intro.
  rename v'28 into chanpb. rename v'19 into chanpl1. rename v'23 into chanpl2.
  rename v'21 into chanl1. rename v'24 into chanl2.
  rename v'22 into chandstkportll1. rename v'25 into chandstkportll2.
  unfold KPort, port_id, addrval, port_coreNum in H31, H47;
  rewrite H31 in H47; inverts H47.
  rename x10 into pptr.
  unfold OS_Channel_V_dstPortsNum in H56; simpl in H56; inverts H56.
  unfold OS_Channel_V_dstPortsHead in H55; simpl in H55; inverts H55.
  unfold OS_Channel_V_channelID in H46; simpl in H46; inverts H46.
  rename x7 into dstkportpl.

  assert (exists chanh,
    ChannelNode_P otherppl (Vint32 chanid :: Vint32 i1
      :: Vint32 v'27 :: Vint32 i :: v'26 :: x15 :: x16 :: x17 :: nil)
      chanh (chanpb, Int.zero) dstkportpl kportls dportls1 dportls2 /\
    get chanls (chanpb, Int.zero) = Some chanh).
  { eapply RLH_Channel_app_cons; eauto. }
  simpljoin1. destruct x as [[[cid cdn] cdstkp] ct].

  unfold ChannelNode_P in H46; simpljoin1.
  rename H55 into Hnodup_dk.
  unfold Channel_nat_P in H46; simpljoin1.
  unfold OS_Channel_V_channelID in H46; simpl in H46;
    inverts H46; rename x into chanid.
  unfold OS_Channel_V_dstPortsNum in H56; simpl in H56;
    inverts H56; rename x0 into dpnum.
  unfold Channel_type_P in H50; simpljoin1.

  destruct ct; simpljoin1.
  2:{
    unfold OS_Channel_V_semaphore in H46; simpl in H46; inverts H46.
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply absinfer_choice1; [ | | intros ? Hs; apply Hs ].
      all: can_change_aop_solver'.
    }
    assert ($ Z.of_nat (Z.to_nat (Int.unsigned ($ Z.of_nat c))) = ($ Z.of_nat c)) as Hsem.
    {
      rewrite Z2Nat.id by apply Int.unsigned_range.
      apply Int.repr_unsigned.
    }

    assert (v <> (V$ Z.of_nat c) \/ v = (V$ Z.of_nat c)) by tauto.
    hoare name lift oschannelid pre.
    hoare name lift oskportid pre.
    hoare name lift osdomainportid pre.
    hoare name lift Aop pre.
    destruct H46.
    {
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply corecommu_sem_abt; eauto.
        all: can_change_aop_solver'.
      }
      eapply absabort_rule.
    }

    subst v.
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply corecommu_sem_cont; eauto.
      all: can_change_aop_solver'.
    }
    unfold Semacc_err, Semacc_succ.

    (* If (kport ′ .. channel !=ₑ 〈 OS_Channel ∗ 〉 NULL)
    {channel ′ =ₑ kport ′ .. channel;ₛ
    semaphore ′ =ₑ channel ′ .. semaphore;ₛ
    If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
    {CSLSEMACC (semaphore ′, resource_get_res ′);ₛ
    If (resource_get_res ′ ==ₑ NULL)
    {EXIT_CRITICAL;ₛ
    RETURN 〈 char_t 〉 ′ OS_CHANNEL_ERR_BEING_USED}}};ₛ *)
    eapply seq_rule.
    {
      eapply ift_rule''; [symbolic_exe_port|idtac].
      { pauto. }
      hoare normal pre; pure intro.
      clear H46 H55 H64.

      (* channel ′ =ₑ kport ′ .. channel;ₛ *)
      eapply seq_rule.
      {
        hoare name lift channel pre.
        hoare name lift Aop pre.
        eapply assign_rule_lvar.
        { intro s; split; intros; apply H46. }
        {
          intros.
          eapply kport_channel_rv; eauto.
          2: sep pauto.
          2: sep cancel Astruct'; eapply H46.
          pauto.
        }
        { apply assign_type_match_true; simpl; auto. }
        sep auto.
  Optimize Proof.
  Optimize Heap.
      }
      unfold nth_val'.

      (* semaphore ′ =ₑ channel ′ .. semaphore;ₛ *)
      hoare forward.
      { pauto. }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE) *)
      hoare forward.
      { pauto. }
      { pauto. }
      { pauto. }
      hoare normal pre; pure intro.
      clear H46 H55 H64.
      
      (* CSLSEMACC (semaphore ′, resource_get_res ′);ₛ *)
      hoare name lift resource_get_res pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      {
        eapply cslsemacc_rule'.
        { can_change_aop_solver'. }
        { rewrite Z2Nat.id. 1,2: eapply Int.unsigned_range_2. }
        { rewrite Hsem. symbolic execution. pauto. }
        {
          unfold p_local, CurLINV, LINV, OSLInv. intros.
          sep normal in H46; sep destruct H46; sep split in H46.
          sep auto. splits; eauto.
          all: destruct H55 as [? [? [? [? [? ?]]]]]; auto.
        }
        {
          unfold p_local, CurLINV, LINV, OSLInv. intros.
          sep normal in H46; sep destruct H46; sep split in H46.
          sep auto. splits; eauto.
          all: destruct H55 as [? [? [? [? [? ?]]]]]; auto.
        }
      }

      eapply disj_rule'.
      instantiate (1:=Afalse).
      {
        hoare forward.
        2:{
          destruct H46.
          {
            instantiate (1:=Afalse) in H46.
            sep pauto.
          }
          sep normal in H46; sep split in H46.
          exfalso; clear - H55.
          assert ((Int.modu ($ 0) ($ Byte.modulus)) = Int.zero) by mauto.
          rewrite H in H55.
          rewrite Int.eq_true in H55; simpl in H55;
            destruct H55; inverts H0.
        }
        hoare normal pre; pure intro.
        clear H46 H55 H64.
        
        (* EXIT_CRITICAL;ₛ *)
        hoare forward prim.
        {
          sep autocancel.
          sep name lift PartitionInv; apply fold_PartitionInv_frm.
          sep cancel PartitionInv_part2.
          unfold PartitionInv_part1.
          sep normal; sep eexists; sep autocancel.
          sep split; eauto.
          2: split; eauto.

          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList;
          sep normal; sep eexists; sep pauto.
          unfold dmportp_sll.
          eapply dmportp_sllseg_compose; eauto.
          sep autocancel.

          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl;
          sep normal; sep eexists; sep pauto.
          eapply kportNode_P_compose; eauto.
          rewrite H40; auto. pauto. sep autocancel.

          (* cancel AOSChannelIDTbl *)
          unfold AOSChannelIDTbl;
          sep normal; sep eexists; sep pauto.
          eapply ChannelNode_compose; eauto.
          rewrite H57; auto.
          rewrite H58; auto.
          unfold OS_Channel_V_dstPortsHead; simpl; eauto.
          unfold OS_Channel_V_dstPortsNum; simpl; eauto.
          pauto. sep autocancel. apply H46.
        }
        auto.
        good_frm_sovler.
        hoare forward.
      }

      hoare forward.
      {
        instantiate (1:=Afalse).
        hoare normal pre; pure intro.
        exfalso; clear - H46. pauto.
      }
    }
    eapply disj_rule; hoare normal pre; pure intro.
    2: exfalso; clear - H46; destruct H46; pauto; inverts H.
    eapply disj_rule; hoare normal pre; pure intro.
    2:{
      exfalso; rewrite H50 in H66; clear - H66.
      unfold notint, val_inj in H66; destruct H66; pauto; inverts H.
    }
    hoare forward. hoare forward.
    hoare normal pre; pure intro.
    clear H46 H55 H64 H66 H67 H68 H69.

    (* port_ptr ′ .. OSQIn =ₑ port_ptr ′ .. OSQStart;ₛ *)
    hoare name lift APortStruct pre.
    hoare name lift port_ptr pre.
    hoare name lift Aop pre.
    eapply seq_rule.
    {
      eapply port_memeber_asgn with (n := 14%nat).
      { pauto. }
      2: pauto.
      2:{
        eapply symbolic_lemmas.nth_val_imp_nth_val'_2.
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 14 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
        lia.
      }
      2: pauto.
      2: pauto.
      2: pauto.
      2: pauto.
      2: instantiate (1:=OSMsg_t ∗); eapply eq_vptr; eauto.
      {
        intros. eapply port_QStart_rv.
        3: eapply H46. 2: eauto. auto.
      }
      { 
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 12 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
        destruct H19; auto.
      }
      { sep auto. }
    }

    (* port_ptr ′ .. OSQOut =ₑ port_ptr ′ .. OSQStart;ₛ *)
    hoare name lift APortStruct pre.
    hoare name lift port_ptr pre.
    hoare name lift Aop pre.
    eapply seq_rule.
    {
      eapply port_memeber_asgn with (n := 15%nat).
      { pauto. }
      2: pauto.
      2:{
        eapply nth_upd_neqrev; eauto.
        eapply symbolic_lemmas.nth_val_imp_nth_val'_2.
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 15 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
        lia.
      }
      2: pauto.
      2: pauto.
      2: pauto.
      2: pauto.
      2: instantiate (1:=OSMsg_t ∗); eapply eq_vptr; eauto.
      {
        intros.
        eapply port_QStart_rv.
        3: eapply H46.
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
        instantiate (1:=v'20); clear - H20.
        eapply nth_upd_neqrev; eauto.
      }
      { 
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 12 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
        destruct H19; auto.
      }
      { sep auto. }
    }

    (* port_ptr ′ .. OSQEntries =ₑ ′ 0;ₛ *)
    hoare name lift APortStruct pre.
    hoare name lift port_ptr pre.
    hoare name lift Aop pre.
    eapply seq_rule.
    {
      eapply port_memeber_asgn with (n := 17%nat).
      { pauto. }
      2: pauto.
      2:{
        eapply nth_upd_neqrev; eauto.
        eapply nth_upd_neqrev; eauto.
        eapply symbolic_lemmas.nth_val_imp_nth_val'_2.
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 17 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
        lia.
  Optimize Proof.
  Optimize Heap.
      }
      2: pauto.
      2: pauto.
      2: pauto.
      2: pauto.
      2: instantiate (1:=Int32u); eapply eq_int; auto.
      { intros; instantiate (1:= (V$ 0)); symbolic execution. }
      { pauto. }
      { sep auto. }
    }

    hoare lift 18%nat pre.
    eapply backward_rule1.
    { intros. eapply disj_split in H46. apply H46. }
    eapply disj_rule.
    (* sampleport *)
    {
      hoare normal pre; pure intro.
      unfold Domainport_Portt_P in H30; destruct p5; simpljoin1.
      2:{ rewrite H64 in H46; inverts H46. }
      clear H46.

      unfold dmportp_sllseg_sampleport_msg.
      hoare normal pre; pure intro.
      inversion H46; subst x; clear H46.
      rename v'20 into qstart.
      hoare name lift APortStruct pre.
      hoare name lift port_ptr pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      {
        eapply assign_rule_general.
        {
          intros.
          eapply symbolic_lemmas.struct_offset_rv.
          {
            eapply symbolic_lemmas.addrof_deref_rv.
            eapply port_QStart_rv.
            3: sep autocancel; apply H46.
            {
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
            }
            instantiate (1:=qstart).
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          all: pauto.
        }
        {
          assert ((fst qstart, snd qstart +ᵢ  Int.zero) = qstart).
          { clear; destruct qstart; simpl; rewrite Int.add_zero; auto. }
          rewrite H46; split; intros.
          { sep autocancel; apply H67. }
          sep pauto.
        }
        {
          intros.
          instantiate (1:=(V$ 0)).
          instantiate (1:=long).
          symbolic_execution.
        }
        { eapply eq_int; tauto. }
        { sep auto. }
      }
      
      (* portflush_succ (|Vptr pptr :: nil|);; *)
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare name lift Aop pre.
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply portflush_succ_cont; eauto.
        can_change_aop_solver'.
      }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
      {CSLSEMREL (semaphore ′)};ₛ *)
      hoare forward.
      { pauto. }
      { pauto. }
      { pauto. }
      {
        hoare normal pre; pure intro.
        clear H46 H67 H68.
        cbn [Semrelease].
        eapply cslsemrel_rule.
        {
          can_change_aop_solver'.
        }
        {
          rewrite Z2Nat.id by apply Int.unsigned_range.
          apply Int.unsigned_range_2.
        }
        { intros; rewrite Hsem; symbolic execution; pauto. }
        {
          unfold p_local, CurLINV, LINV, OSLInv. intros.
          sep normal in H46; sep destruct H46; sep split in H46.
          sep auto. splits; eauto.
          all: destruct H67 as [? [? [? [? [? ?]]]]]; auto.
        }
      }
      eapply disj_rule; hoare normal pre; pure intro.
      2:{
        exfalso; rewrite H50 in H46; clear - H46.
        unfold notint, val_inj in H46; destruct H46; pauto; inverts H.
      }
      
      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      subst dpptrl.
      unfold AOSCorePortPtrList.
      hoare normal pre; pure intro.
      rename H15 into Hcptr.
      hoare forward prim.
      {
        sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep split.
        {
          sep autocancel.
          unfold AOSCorePortPtrList.
          sep pauto.
          2:{ instantiate (1:=(set dportls1 pptr
              (Z.to_nat DNUM, ∘ (Int.unsigned x2),
              ∘ (Int.unsigned portid), d, ∘ (Int.unsigned x4),
              ∘ (Int.unsigned x5), ∘ (Int.unsigned x6),
              SamplePort (Some nil)))).
              eapply RH_CorePortPtrList_upd_dportls; eauto. }

          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl.
          sep normal; sep split.
          2: eapply H17.
          2: split; auto.
          sep autocancel.
          sep name lift kportNode_P.
          eapply kportNode_P_compose.
          4: sep autocancel.
          1,2,3: eauto; pauto.
          rewrite H40; auto.

          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal; sep autocancel.
          instantiate (6:=(dportl1 ++ (update_nth_val 17
          (update_nth_val 15
             (update_nth_val 14 dport (Vptr qstart))
             (Vptr qstart)) (V$ 0)) :: dportl2)).
          instantiate (5:=(dportmsgll1 ++ ((@nil val)::nil) :: dportmsgll2)).
          eapply dmportp_sllseg_compose; eauto.
          { do 3 (eapply nth_upd_neqrev; eauto). }
          {
            clear - H19.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
          }
          { do 3 (eapply nth_upd_neqrev; eauto). }
          sep autocancel.
          eapply disj_split; left.
          sep normal; sep split.
          2: do 3 (eapply nth_upd_neqrev; eauto).
          unfold dmportp_sllseg_sampleport_msg.
          sep normal; sep eexists; sep split.
          2: eauto.
          instantiate (5:=v'19 ++ v'21).
          2: simpl; split; auto.
          simpl (length _).
          assert ((fst qstart, snd qstart +ᵢ  Int.zero) = qstart).
          { clear; destruct qstart; simpl; rewrite Int.add_zero; auto. }
          rewrite H70 in H15.
          sep autocancel.

          (* cancel AOSChannelIDTbl *)
          unfold AOSChannelIDTbl;
          sep normal; sep eexists; sep pauto.
          eapply ChannelNode_compose.
          6: sep autocancel; apply H15.
          rewrite H57; auto.
          rewrite H58; auto.
          unfold OS_Channel_V_dstPortsHead; simpl; eauto.
          unfold OS_Channel_V_dstPortsNum; simpl; eauto.
          pauto.
        }
        auto.
  Optimize Proof.
  Optimize Heap.
        eauto.
        {
          
          eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
        }
        {
          eapply R_Kernelport_DomainPort_upd; eauto.
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
        }
        { eapply RLH_Channel_upd_dportls1; eauto. }
        { eauto. }
        {
          eapply RLH_Domainportl_upd_Sample; eauto.
          rewrite H69; auto.
          {
            unfold DomainportNode_P; splits; eauto.
            {
              unfold Domainport_nat_P.
              do 5 eexists; repeat (splits; eauto).
            }
            unfold Domainport_Portt_P.
            eexists; splits; eauto.
          }
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H32; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H37; do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H70.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          {
            unfold OS_Port_V_OSEventPtrPort.
            assert (nth_val 10 dport = Some (nth_val' 10 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 10 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H70.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H64; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          unfold RLH_PortPtrINecb; split; eauto.
          eapply RL_PortPtrList_upd; eauto.
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          eapply RL_PortAttr_upd; eauto.
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H70.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H64; do 3 (eapply nth_upd_neqrev; eauto).
        }
        eapply join_set_l; eauto.
        eapply get_indom; eauto.
      }
      eauto.
      good_frm_sovler.
      
      (* RETURN ′ OS_NO_ERR *)
      hoare forward.
    }

    (* queueport *)
    hoare normal pre; pure intro.
    unfold Domainport_Portt_P in H30; destruct p5; simpljoin1.
    { rewrite H73 in H46; inverts H46. }
    clear H46.
    rewrite H67 in H72; inverts H72.
    rename v'20 into qstart.
    rename v'19 into qend.
    rename v'21 into qin.
    rename v'22 into qout.
    rename n into sz.

    unfold Qport_msg_ptrs_P in H69.
    destruct qstart as [qstartb qstarti].
    destruct H69 as [H69_ [H69_0 [z1 [z2 H69]]]].
    subst qstarti.
    unfold get_off_addr in H69, H69_0.
    cbn [fst snd] in *.
    destruct H69 as [? [? H69]].
    assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).
    rewrite H72 in *; clear H72.
    rewrite Int.add_zero_l in *.
    subst qend qout qin.
    rewrite Int.repr_unsigned in *.
    rename v'24 into entries.
    
    assert (z1 + Int.unsigned entries > Int.unsigned ($ Z.of_nat sz) \/
            z1 + Int.unsigned entries <= Int.unsigned ($ Z.of_nat sz)) by tauto.
    destruct H30.
    {
      assert ((qstartb, Int.zero) =
            dmportp_msg_next_n (∘ ((Int.unsigned ($ Z.of_nat sz)) - z1))
                                (qstartb, Int.mul ($ z1) ($ 33))
                                (qstartb, Int.zero)
                                (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))).
      {
        clear - H69 H71.
        destruct H69. clear z2 H0.
        assert (exists n, n = (∘ (Int.unsigned ($ Z.of_nat sz) - z1))) by eauto.
        destruct H0; rewrite <- H0.
        assert ((0 < x)%nat) by (subst x; unfold nat_of_Z; lia).
        assert ((Z.of_nat x <= Int.unsigned ($ Z.of_nat sz))).
        { subst x; rewrite Z2Nat.id; lia. }
        assert (Z.of_nat x <= 65535) by lia.
        assert ($ Z.of_nat sz = $ ((Z.of_nat x) + z1)).
        {
          subst x; rewrite Z2Nat.id by lia.
          assert (Int.unsigned ($ Z.of_nat sz) - z1 + z1 =
                  Int.unsigned ($ Z.of_nat sz)) by lia.
          rewrite H0; rewrite Int.repr_unsigned; auto.
        }
        rewrite H4. rename z1 into y.
        assert (0 <= y) by lia.
        assert (Z.of_nat x + y <= 65535).
        {
          pose proof H71.
          rewrite H4 in H6.
          rewrite int_usign_eq in H6; try lia.
          assert (y < 65535) by lia.
          clear - H3 H7; mauto.
        }
        eapply dmportp_msg_next_n_to_qstart; eauto.
      }

      eapply backward_rule1.
      { eapply dmportp_sllseg_qport_msg_length. }
      naive pure intro.
      pose proof firstn_skipn (∘ (Int.unsigned ($ Z.of_nat sz) - z1)) msg.
      rewrite <- H74 at 1.
      assert (∘ (Int.unsigned entries) = ((∘ (Int.unsigned ($ Z.of_nat sz) - z1)) + 
        (∘ (Int.unsigned entries) - (∘ (Int.unsigned ($ Z.of_nat sz) - z1))))%nat).
      { apply le_plus_minus; unfold nat_of_Z; apply Zle_natle; lia. }
      rewrite H75 at 1.

      hoare remember (1::nil)%nat pre.
      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_app_frm.
        eapply firstn_length_le.
        rewrite H72; unfold nat_of_Z; apply Zle_natle; lia.
        rewrite skipn_length; rewrite H72; auto.
        eapply H46.
      }
      subst H76.
      hoare lift 2%nat pre.

      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_ngt0.
        assert ((∘ (Int.unsigned ($ Z.of_nat sz) - z1)
            < ∘ (Int.unsigned entries))%nat).
        apply Z2Nat.inj_lt.
        lia. apply Int.unsigned_range. lia. lia.
      }

      naive pure intro.
      destruct H76 as [msg0 [msg' [? ?]]]; rewrite H76.
      remember (∘ (Int.unsigned entries) -
      ∘ (Int.unsigned ($ Z.of_nat sz) - z1))%nat as u.
      destruct u.
      {
        assert (∘ (Int.unsigned entries) = ∘ (Int.unsigned ($ Z.of_nat sz) - z1)) by lia.
        apply Z2Nat.inj in H78.
        lia. apply Int.unsigned_range. lia.
      }
      cbn [dmportp_sllseg_qport_msg].
      naive pure intro.

      (* (port_ptr ′ .. OSQStart) .. len =ₑ ′ 0;ₛ *)
      hoare name lift APortStruct pre.
      hoare name lift port_ptr pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      {
        eapply assign_rule_general.
        {
          intros.
          eapply symbolic_lemmas.struct_offset_rv.
          {
            eapply symbolic_lemmas.addrof_deref_rv.
            eapply port_QStart_rv.
            3: sep autocancel; apply H79.
            {
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
            }
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          all: pauto.
        }
        {
          unfold fst, snd.
          rewrite Int.add_zero.
          split; intros.
          { sep autocancel; apply H79. }
          sep pauto.
        }
        {
          intros.
          instantiate (1:=(V$ 0)).
          instantiate (1:=long).
          symbolic_execution.
        }
        { eapply eq_int; tauto. }
        { sep auto. }
      }

      (* portflush_succ (|Vptr pptr :: nil|);; *)
      hoare normal pre; pure intro.
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare name lift Aop pre.
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply portflush_succ_cont; eauto.
        can_change_aop_solver'.
      }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
      {CSLSEMREL (semaphore ′)};ₛ *)
      hoare normal pre; pure intro.
      hoare forward.
      { pauto. }
      { pauto. }
      { pauto. }
      {
        hoare normal pre; pure intro.
        clear H84 H85 H86.
        cbn [Semrelease].
        eapply cslsemrel_rule.
        { can_change_aop_solver'. }
        {
          rewrite Z2Nat.id by apply Int.unsigned_range.
          apply Int.unsigned_range_2.
        }
        { intros; rewrite Hsem; symbolic execution; pauto. }
        {
          unfold p_local, CurLINV, LINV, OSLInv. intros.
          sep normal in H84; sep destruct H84; sep split in H84.
          sep auto. splits; eauto.
          all: destruct H85 as [? [? [? [? [? ?]]]]]; auto.
        }
      }
      eapply disj_rule; hoare normal pre; pure intro.
      2:{
        exfalso; rewrite H50 in H84; clear - H84.
        unfold notint, val_inj in H84; destruct H84; pauto; inverts H.
      }
      clear H84 H85 H86.
      
      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      subst dpptrl.
      unfold AOSCorePortPtrList.
      hoare normal pre; pure intro.
      rename H15 into Hcptr.
      hoare forward prim.
      {
        sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep split.
        {
          sep autocancel.
          unfold AOSCorePortPtrList.
          sep pauto.
          2:{ instantiate (1:=(set dportls1 pptr
              (Z.to_nat DNUM, ∘ (Int.unsigned x2),
              ∘ (Int.unsigned portid), d, ∘ (Int.unsigned x4),
              ∘ (Int.unsigned x5), ∘ (Int.unsigned x6),
              QueuePort sz nil))).
              eapply RH_CorePortPtrList_upd_dportls; eauto. }

          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl.
          sep normal; sep split.
          2: eapply H17.
          2: split; auto.
          sep autocancel.
          sep name lift kportNode_P.
          eapply kportNode_P_compose.
          4: sep autocancel.
          1,2,3: eauto; pauto.
          rewrite H40; auto.

          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal; sep autocancel.
          instantiate (6:=(dportl1 ++ (update_nth_val 17
          (update_nth_val 15 (update_nth_val 14 dport
            (Vptr (qstartb, Int.zero))) (Vptr (qstartb, Int.zero))) 
              (V$ 0)) :: dportl2)).
          instantiate (5:=(dportmsgll1 ++ (nil) :: dportmsgll2)).
          eapply dmportp_sllseg_compose; eauto.
          { do 3 (eapply nth_upd_neqrev; eauto). }
          {
            clear - H19.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
          }
          { do 3 (eapply nth_upd_neqrev; eauto). }
          sep autocancel.
          eapply disj_split; right.
          sep normal.
          exists (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))
                 (qstartb, Int.zero) (qstartb, Int.zero)
                 ($ Z.of_nat sz) ($ 0)
                 (nil :: msg' ++ v'25 ++ (firstn (∘
                    (Int.unsigned ($ Z.of_nat sz) - z1)) msg)).
          assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).    
          sep split.
          2:{
            unfold Qport_msg_ptrs_P.
            splits; auto.
            {
              rewrite H85, Int.repr_unsigned.
              unfold get_off_addr, fst, snd.
              rewrite Int.add_zero_l; auto.
            }
            exists 0 0.
            splits; auto; try lia.
          }
          2:{
            split. eapply update_nth; eauto.
            do 2 (eapply nth_upd_neqrev; eauto).
            assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
            rewrite H86; lia.
          }
          2:{ split. do 3 (eapply nth_upd_neqrev; eauto). auto. }
          2:{
            eapply nth_upd_neqrev; eauto.
            eapply update_nth; eauto.
            eapply nth_upd_neqrev; eauto.
          }
          2:{
            do 2 (eapply nth_upd_neqrev; eauto).
            eapply update_nth; eauto.
          }
          2: do 3 (eapply nth_upd_neqrev; eauto).
          2: do 3 (eapply nth_upd_neqrev; eauto).
          assert (∘ (Int.unsigned ($ 0)) = 0%nat) by (clear; mauto).
          assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
          rewrite H86; rewrite H87.
          unfold dmportp_sllseg_qport_msg at 1.
          sep split; auto.
          rewrite Z.sub_0_r.
          assert (∘ (Int.unsigned ($ Z.of_nat sz)) = ((S u) + 
                  ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries) +
                  ∘ (Int.unsigned ($ Z.of_nat sz) - z1))%nat).
          { rewrite Hequ; unfold nat_of_Z; lia. }
          rewrite H88.
          assert ((S u +
          ∘ (Int.unsigned ($ Z.of_nat sz) -
             Int.unsigned entries) +
             ∘ (Int.unsigned ($ Z.of_nat sz) - z1))%nat = S (u +
          ∘ (Int.unsigned ($ Z.of_nat sz) -
             Int.unsigned entries) +
             ∘ (Int.unsigned ($ Z.of_nat sz) - z1))%nat) by lia.
          rewrite H89.
          cbn [dmportp_sllseg_qport_msg].
          sep normal; exists (msg0 ++ v'19); sep split.
          2: split; auto.
          rewrite app_nil_l.
          unfold fst, snd in H15.
          rewrite Int.add_zero in H15.
          sep autocancel.
          assert ((u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries) +
          ∘ (Int.unsigned ($ Z.of_nat sz) - z1))%nat =
          (u + (∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries) +
          ∘ (Int.unsigned ($ Z.of_nat sz) - z1)))%nat ) by lia.
          rewrite H90; clear H90.
          sep lifts (2::3::4::nil)%nat in H15.
          eapply dmportp_sllseg_qport_msg_app_frm.
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15.
            sep lift 3%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15.
            rewrite app_length; lia.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z2) ($ 33))).
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          sep autocancel.
          eapply dmportp_sllseg_qport_msg_app_frm.
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z1) ($ 33))).
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          sep lift 2%nat in H15.
          do 2 sep cancel dmportp_sllseg_qport_msg.

          (* cancel AOSChannelIDTbl *)
          unfold AOSChannelIDTbl;
          sep normal; sep eexists; sep pauto.
          eapply ChannelNode_compose.
          6: sep autocancel; apply H15.
          rewrite H57; auto.
          rewrite H58; auto.
          unfold OS_Channel_V_dstPortsHead; simpl; eauto.
          unfold OS_Channel_V_dstPortsNum; simpl; eauto.
          pauto.
        }
        auto.
  Optimize Proof.
  Optimize Heap.
        eauto.
        {
          
          eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
        }
        {
          eapply R_Kernelport_DomainPort_upd; eauto.
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
        }
        { eapply RLH_Channel_upd_dportls1; eauto.
          right; do 4 eexists; split; eauto. }
        { eauto. }
        {
          eapply RLH_Domainportl_upd_Queue; eauto.
          rewrite H84; auto.
          {
            unfold DomainportNode_P; splits; eauto.
            {
              unfold Domainport_nat_P.
              do 5 eexists; repeat (splits; eauto).
            }
            unfold Domainport_Portt_P; splits; eauto.
          }
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H32; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H37; do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H85.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          {
            unfold OS_Port_V_OSEventPtrPort.
            assert (nth_val 10 dport = Some (nth_val' 10 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 10 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H85.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H73; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H67; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          unfold RLH_PortPtrINecb; split; eauto.
          eapply RL_PortPtrList_upd; eauto.
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          eapply RL_PortAttr_upd; eauto.
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H85.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H73; do 3 (eapply nth_upd_neqrev; eauto).
        }
        eapply join_set_l; eauto.
        eapply get_indom; eauto.
      }
      eauto.
      good_frm_sovler.
      
      (* RETURN ′ OS_NO_ERR *)
      hoare forward.
    }

    assert (exists f, Int.unsigned f = Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries).
    {
      exists (Int.sub ($ Z.of_nat sz) entries).
      eapply Int_unsigned_minus. lia.
    }
    destruct H46 as [f ?]; rewrite <- H46.
    assert (Int.unsigned entries = Int.unsigned ($ Z.of_nat sz) - Int.unsigned f) by lia.
    rewrite H72.

    assert (z2 + Int.unsigned f > Int.unsigned ($ Z.of_nat sz) \/
            z2 + Int.unsigned f <= Int.unsigned ($ Z.of_nat sz)) by tauto.
    destruct H74.
    {
      hoare lift 2%nat pre.
      assert ((qstartb, Int.zero) =
            dmportp_msg_next_n (∘ ((Int.unsigned ($ Z.of_nat sz)) - z2))
                                (qstartb, Int.mul ($ z2) ($ 33))
                                (qstartb, Int.zero)
                                (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))).
      {
        clear - H69 H71.
        destruct H69. clear z1 H. rename H0 into H.
        assert (exists n, n = (∘ (Int.unsigned ($ Z.of_nat sz) - z2))) by eauto.
        destruct H0; rewrite <- H0.
        assert ((0 < x)%nat) by (subst x; unfold nat_of_Z in *; lia).
        assert ((Z.of_nat x <= Int.unsigned ($ Z.of_nat sz))).
        { subst x; rewrite Z2Nat.id; lia. }
        assert (Z.of_nat x <= 65535) by lia.
        assert ($ Z.of_nat sz = $ ((Z.of_nat x) + z2)).
        {
          subst x; rewrite Z2Nat.id by lia.
          assert (Int.unsigned ($ Z.of_nat sz) - z2 + z2 =
                  Int.unsigned ($ Z.of_nat sz)) by lia.
          rewrite H0; rewrite Int.repr_unsigned; auto.
        }
        rewrite H4. rename z2 into y.
        assert (0 <= y) by lia.
        assert (Z.of_nat x + y <= 65535).
        {
          pose proof H71.
          rewrite H4 in H6.
          rewrite int_usign_eq in H6; try lia.
          assert (y < 65535) by lia.
          clear - H3 H7; mauto.
        }
        eapply dmportp_msg_next_n_to_qstart; eauto.
      }
      rename v'25 into msg2.

      eapply backward_rule1.
      { eapply dmportp_sllseg_qport_msg_length. }
      naive pure intro.
      pose proof firstn_skipn ∘ (Int.unsigned ($ Z.of_nat sz) - z2) msg2.
      rewrite <- H77 at 1.
      
      assert (∘ (Int.unsigned f) = 
        (∘ (Int.unsigned ($ Z.of_nat sz) - z2) + 
        (∘ (Int.unsigned f) - ∘ (Int.unsigned ($ Z.of_nat sz) - z2)))%nat).
      { apply le_plus_minus; unfold nat_of_Z; apply Zle_natle; lia. }
      rewrite H78 at 1.

      hoare remember (1::nil)%nat pre.
      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_app_frm.
        eapply firstn_length_le.
        rewrite H76; unfold nat_of_Z; apply Zle_natle; lia.
        rewrite skipn_length.
        rewrite H76; auto. eapply H75.
      }
      subst H79.
      hoare lift 2%nat pre.

      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_ngt0.
        assert ((∘ (Int.unsigned ($ Z.of_nat sz) - z2) < ∘ (Int.unsigned f))%nat).
        apply Z2Nat.inj_lt.
        lia. apply Int.unsigned_range. lia. lia.
      }

      naive pure intro.
      destruct H79 as [msg0 [msg' [? ?]]].
      rewrite H79.
      remember (∘ (Int.unsigned f) - ∘ (Int.unsigned ($ Z.of_nat sz) - z2))%nat as u.
      destruct u.
      {
        assert (∘ (Int.unsigned f) = ∘ (Int.unsigned ($ Z.of_nat sz) - z2)) by lia.
        apply Z2Nat.inj in H81.
        lia. apply Int.unsigned_range. lia.
      }
      cbn [dmportp_sllseg_qport_msg].
      naive pure intro.

      (* (port_ptr ′ .. OSQStart) .. len =ₑ ′ 0;ₛ *)
      hoare name lift APortStruct pre.
      hoare name lift port_ptr pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      {
        eapply assign_rule_general.
        {
          intros.
          eapply symbolic_lemmas.struct_offset_rv.
          {
            eapply symbolic_lemmas.addrof_deref_rv.
            eapply port_QStart_rv.
            3: sep autocancel; apply H82.
            {
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
            }
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          all: pauto.
        }
        {
          unfold fst, snd.
          rewrite Int.add_zero.
          split; intros.
          { sep autocancel; apply H82. }
          sep pauto.
        }
        {
          intros.
          instantiate (1:=(V$ 0)).
          instantiate (1:=long).
          symbolic_execution.
        }
        { eapply eq_int; tauto. }
        { sep auto. }
      }

      (* portflush_succ (|Vptr pptr :: nil|);; *)
      hoare normal pre; pure intro.
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare name lift Aop pre.
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply portflush_succ_cont; eauto.
        can_change_aop_solver'.
      }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
      {CSLSEMREL (semaphore ′)};ₛ *)
      hoare normal pre; pure intro.
      hoare forward.
      { pauto. }
      { pauto. }
      { pauto. }
      {
        hoare normal pre; pure intro.
        clear H87 H88 H89.
        cbn [Semrelease].
        eapply cslsemrel_rule.
        { can_change_aop_solver'. }
        {
          rewrite Z2Nat.id by apply Int.unsigned_range.
          apply Int.unsigned_range_2.
        }
        { intros; rewrite Hsem; symbolic execution; pauto. }
        {
          unfold p_local, CurLINV, LINV, OSLInv. intros.
          sep normal in H87; sep destruct H87; sep split in H87.
          sep auto. splits; eauto.
          all: destruct H88 as [? [? [? [? [? ?]]]]]; auto.
        }
      }
      eapply disj_rule; hoare normal pre; pure intro.
      2:{
        exfalso; rewrite H50 in H87; clear - H87.
        unfold notint, val_inj in H87; destruct H87; pauto; inverts H.
      }
      clear H87 H88 H89.
      
      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      subst dpptrl.
      unfold AOSCorePortPtrList.
      hoare normal pre; pure intro.
      rename H15 into Hcptr.
      hoare forward prim.
      {
        sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep split.
        {
          sep autocancel.
          unfold AOSCorePortPtrList.
          sep pauto.
          2:{ instantiate (1:=(set dportls1 pptr
              (Z.to_nat DNUM, ∘ (Int.unsigned x2),
              ∘ (Int.unsigned portid), d, ∘ (Int.unsigned x4),
              ∘ (Int.unsigned x5), ∘ (Int.unsigned x6),
              QueuePort sz nil))).
              eapply RH_CorePortPtrList_upd_dportls; eauto. }

          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl.
          sep normal; sep split.
          2: eapply H17.
          2: split; auto.
          sep autocancel.
          sep name lift kportNode_P.
          eapply kportNode_P_compose.
          4: sep autocancel.
          1,2,3: eauto; pauto.
          rewrite H40; auto.

          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal; sep autocancel.
          instantiate (6:=(dportl1 ++ (update_nth_val 17
          (update_nth_val 15 (update_nth_val 14 dport
            (Vptr (qstartb, Int.zero))) (Vptr (qstartb, Int.zero))) 
              (V$ 0)) :: dportl2)).
          instantiate (5:=(dportmsgll1 ++ (nil) :: dportmsgll2)).
          eapply dmportp_sllseg_compose; eauto.
          { do 3 (eapply nth_upd_neqrev; eauto). }
          {
            clear - H19.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
          }
          { do 3 (eapply nth_upd_neqrev; eauto). }
          sep autocancel.
          eapply disj_split; right.
          sep normal.
          exists (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))
                 (qstartb, Int.zero) (qstartb, Int.zero)
                 ($ Z.of_nat sz) ($ 0)
                 (nil :: msg' ++ msg ++ (firstn (∘
                    (Int.unsigned ($ Z.of_nat sz) - z2)) msg2)).
          assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).    
          sep split.
          2:{
            unfold Qport_msg_ptrs_P.
            splits; auto.
            {
              rewrite H88, Int.repr_unsigned.
              unfold get_off_addr, fst, snd.
              rewrite Int.add_zero_l; auto.
            }
            exists 0 0.
            splits; auto; try lia.
          }
          2:{
            split. eapply update_nth; eauto.
            do 2 (eapply nth_upd_neqrev; eauto).
            assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
            rewrite H89; lia.
          }
          2:{ split. do 3 (eapply nth_upd_neqrev; eauto). auto. }
          2:{
            eapply nth_upd_neqrev; eauto.
            eapply update_nth; eauto.
            eapply nth_upd_neqrev; eauto.
          }
          2:{
            do 2 (eapply nth_upd_neqrev; eauto).
            eapply update_nth; eauto.
          }
          2: do 3 (eapply nth_upd_neqrev; eauto).
          2: do 3 (eapply nth_upd_neqrev; eauto).
          assert (∘ (Int.unsigned ($ 0)) = 0%nat) by (clear; mauto).
          assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
          rewrite H89; rewrite H90.
          unfold dmportp_sllseg_qport_msg at 1.
          sep split; auto.
          rewrite Z.sub_0_r.
          assert (∘ (Int.unsigned ($ Z.of_nat sz)) = ((S u) + 
                  ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f) +
                  ∘ (Int.unsigned ($ Z.of_nat sz) - z2))%nat).
          { rewrite Hequ; unfold nat_of_Z.
            assert (Int.unsigned f <= Int.unsigned ($ Z.of_nat sz)).
            { rewrite H46; pose proof Int.unsigned_range entries; lia. }
            lia. }
          rewrite H91.
          assert ((S u +
          ∘ (Int.unsigned ($ Z.of_nat sz) -
             Int.unsigned f) +
             ∘ (Int.unsigned ($ Z.of_nat sz) - z2))%nat = S (u +
          ∘ (Int.unsigned ($ Z.of_nat sz) -
             Int.unsigned f) +
             ∘ (Int.unsigned ($ Z.of_nat sz) - z2))%nat) by lia.
          rewrite H92.
          cbn [dmportp_sllseg_qport_msg].
          sep normal; exists (msg0 ++ v'19); sep split.
          2: split; auto.
          rewrite app_nil_l.
          unfold fst, snd in H15.
          rewrite Int.add_zero in H15.
          sep autocancel.
          assert ((u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f) +
          ∘ (Int.unsigned ($ Z.of_nat sz) - z2))%nat =
          (u + (∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f) +
          ∘ (Int.unsigned ($ Z.of_nat sz) - z2)))%nat ) by lia.
          rewrite H93; clear H93.
          sep lifts (2::3::4::nil)%nat in H15.
          eapply dmportp_sllseg_qport_msg_app_frm.
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15.
            sep lift 3%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15.
            rewrite app_length; lia.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z1) ($ 33))).
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          sep autocancel.
          eapply dmportp_sllseg_qport_msg_app_frm.
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z2) ($ 33))).
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          sep lift 2%nat in H15.
          do 2 sep cancel dmportp_sllseg_qport_msg.

          (* cancel AOSChannelIDTbl *)
          unfold AOSChannelIDTbl;
          sep normal; sep eexists; sep pauto.
          eapply ChannelNode_compose.
          6: sep autocancel; apply H15.
          rewrite H57; auto.
          rewrite H58; auto.
          unfold OS_Channel_V_dstPortsHead; simpl; eauto.
          unfold OS_Channel_V_dstPortsNum; simpl; eauto.
          pauto.
        }
        auto.
  Optimize Proof.
  Optimize Heap.
        eauto.
        {
          
          eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
        }
        {
          eapply R_Kernelport_DomainPort_upd; eauto.
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
        }
        { eapply RLH_Channel_upd_dportls1; eauto.
          right; do 4 eexists; split; eauto. }
        { eauto. }
        {
          eapply RLH_Domainportl_upd_Queue; eauto.
          rewrite H87; auto.
          {
            unfold DomainportNode_P; splits; eauto.
            {
              unfold Domainport_nat_P.
              do 5 eexists; repeat (splits; eauto).
            }
            unfold Domainport_Portt_P; splits; eauto.
          }
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H32; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H37; do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H88.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          {
            unfold OS_Port_V_OSEventPtrPort.
            assert (nth_val 10 dport = Some (nth_val' 10 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 10 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H88.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H73; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H67; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          unfold RLH_PortPtrINecb; split; eauto.
          eapply RL_PortPtrList_upd; eauto.
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          eapply RL_PortAttr_upd; eauto.
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H88.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H73; do 3 (eapply nth_upd_neqrev; eauto).
        }
        eapply join_set_l; eauto.
        eapply get_indom; eauto.
      }
      eauto.
      good_frm_sovler.
      
      (* RETURN ′ OS_NO_ERR *)
      hoare forward.
    }

    rewrite <- H72. rewrite H46.
    assert ((z1 = 0 /\ Int.unsigned entries > 0) \/
            ((z1 > 0 /\ Int.unsigned entries > 0) \/ Int.unsigned entries = 0)) by lia.
    destruct H75.
    {
      destruct H75; subst z1.
      assert (Int.mul ($ 0) ($ 33) = Int.zero) by (clear; mauto).
      rewrite ! H75. clear H75.

      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_ngt0.
        unfold nat_of_Z. lia.
      }

      naive pure intro.
      destruct H75 as [msg0 [msg' [? ?]]].
      rewrite H75.
      remember (∘ (Int.unsigned entries)) as u.
      destruct u.
      { unfold nat_of_Z in Hequ. lia. }
      cbn [dmportp_sllseg_qport_msg].
      naive pure intro.

      (* (port_ptr ′ .. OSQStart) .. len =ₑ ′ 0;ₛ *)
      hoare name lift APortStruct pre.
      hoare name lift port_ptr pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      {
        eapply assign_rule_general.
        {
          intros.
          eapply symbolic_lemmas.struct_offset_rv.
          {
            eapply symbolic_lemmas.addrof_deref_rv.
            eapply port_QStart_rv.
            3: sep autocancel; apply H79.
            {
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
            }
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          all: pauto.
        }
        {
          unfold fst, snd.
          rewrite Int.add_zero.
          split; intros.
          { sep autocancel; apply H79. }
          sep pauto.
        }
        {
          intros.
          instantiate (1:=(V$ 0)).
          instantiate (1:=long).
          symbolic_execution.
        }
        { eapply eq_int; tauto. }
        { sep auto. }
      }

      (* portflush_succ (|Vptr pptr :: nil|);; *)
      hoare normal pre; pure intro.
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare name lift Aop pre.
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply portflush_succ_cont; eauto.
        can_change_aop_solver'.
      }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
      {CSLSEMREL (semaphore ′)};ₛ *)
      hoare normal pre; pure intro.
      hoare forward.
      { pauto. }
      { pauto. }
      { pauto. }
      {
        hoare normal pre; pure intro.
        clear H75 H84 H85.
        cbn [Semrelease].
        eapply cslsemrel_rule.
        { can_change_aop_solver'. }
        {
          rewrite Z2Nat.id by apply Int.unsigned_range.
          apply Int.unsigned_range_2.
        }
        { intros; rewrite Hsem; symbolic execution; pauto. }
        {
          unfold p_local, CurLINV, LINV, OSLInv. intros.
          sep normal in H75; sep destruct H75; sep split in H75.
          sep auto. splits; eauto.
          all: destruct H84 as [? [? [? [? [? ?]]]]]; auto.
        }
      }
      eapply disj_rule; hoare normal pre; pure intro.
      2:{
        exfalso; rewrite H50 in H75; clear - H75.
        unfold notint, val_inj in H75; destruct H75; pauto; inverts H.
      }
      clear H75 H84 H85.
      
      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      subst dpptrl.
      unfold AOSCorePortPtrList.
      hoare normal pre; pure intro.
      rename H15 into Hcptr.
      hoare forward prim.
      {
        sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep split.
        {
          sep autocancel.
          unfold AOSCorePortPtrList.
          sep pauto.
          2:{ instantiate (1:=(set dportls1 pptr
              (Z.to_nat DNUM, ∘ (Int.unsigned x2),
              ∘ (Int.unsigned portid), d, ∘ (Int.unsigned x4),
              ∘ (Int.unsigned x5), ∘ (Int.unsigned x6),
              QueuePort sz nil))).
              eapply RH_CorePortPtrList_upd_dportls; eauto. }

          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl.
          sep normal; sep split.
          2: eapply H17.
          2: split; auto.
          sep autocancel.
          sep name lift kportNode_P.
          eapply kportNode_P_compose.
          4: sep autocancel.
          1,2,3: eauto; pauto.
          rewrite H40; auto.

          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal; sep autocancel.
          instantiate (6:=(dportl1 ++ (update_nth_val 17
          (update_nth_val 15 (update_nth_val 14 dport
            (Vptr (qstartb, Int.zero))) (Vptr (qstartb, Int.zero))) 
              (V$ 0)) :: dportl2)).
          instantiate (5:=(dportmsgll1 ++ (nil) :: dportmsgll2)).
          eapply dmportp_sllseg_compose; eauto.
          { do 3 (eapply nth_upd_neqrev; eauto). }
          {
            clear - H19.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
          }
          { do 3 (eapply nth_upd_neqrev; eauto). }
          sep autocancel.
          eapply disj_split; right.
          sep normal.
          exists (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))
                 (qstartb, Int.zero) (qstartb, Int.zero)
                 ($ Z.of_nat sz) ($ 0) (nil :: msg' ++ v'25).
          assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).    
          sep split.
          2:{
            unfold Qport_msg_ptrs_P.
            splits; auto.
            {
              rewrite H84, Int.repr_unsigned.
              unfold get_off_addr, fst, snd.
              rewrite Int.add_zero_l; auto.
            }
            exists 0 0.
            splits; auto; try lia.
          }
          2:{
            split. eapply update_nth; eauto.
            do 2 (eapply nth_upd_neqrev; eauto).
            assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
            rewrite H85; lia.
          }
          2:{ split. do 3 (eapply nth_upd_neqrev; eauto). auto. }
          2:{
            eapply nth_upd_neqrev; eauto.
            eapply update_nth; eauto.
            eapply nth_upd_neqrev; eauto.
          }
          2:{
            do 2 (eapply nth_upd_neqrev; eauto).
            eapply update_nth; eauto.
          }
          2: do 3 (eapply nth_upd_neqrev; eauto).
          2: do 3 (eapply nth_upd_neqrev; eauto).
          assert (∘ (Int.unsigned ($ 0)) = 0%nat) by (clear; mauto).
          assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
          rewrite H85; rewrite H86.
          unfold dmportp_sllseg_qport_msg at 1.
          sep split; auto.
          rewrite Z.sub_0_r.
          assert (∘ (Int.unsigned ($ Z.of_nat sz)) = ((S u) + 
                  ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries))%nat).
          { rewrite Hequ; unfold nat_of_Z; lia. }
          rewrite H87.
          assert ((S u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries))%nat =
                  S (u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries))%nat) by lia.
          rewrite H88.
          cbn [dmportp_sllseg_qport_msg].
          sep normal; exists (msg0 ++ v'19); sep split.
          2: split; auto.
          rewrite app_nil_l.
          unfold fst, snd in H15.
          rewrite Int.add_zero in H15.
          sep autocancel.
          sep lifts (2::3::nil)%nat in H15.
          eapply dmportp_sllseg_qport_msg_app_frm.
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z2) ($ 33))).
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          do 2 sep cancel dmportp_sllseg_qport_msg.

          (* cancel AOSChannelIDTbl *)
          unfold AOSChannelIDTbl;
          sep normal; sep eexists; sep pauto.
          eapply ChannelNode_compose.
          6: sep autocancel; apply H15.
          rewrite H57; auto.
          rewrite H58; auto.
          unfold OS_Channel_V_dstPortsHead; simpl; eauto.
          unfold OS_Channel_V_dstPortsNum; simpl; eauto.
          pauto.
        }
        auto.
  Optimize Proof.
  Optimize Heap.
        eauto.
        {
          
          eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
        }
        {
          eapply R_Kernelport_DomainPort_upd; eauto.
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
        }
        { eapply RLH_Channel_upd_dportls1; eauto.
          right; do 4 eexists; split; eauto. }
        { eauto. }
        {
          eapply RLH_Domainportl_upd_Queue; eauto.
          rewrite H75; auto.
          {
            unfold DomainportNode_P; splits; eauto.
            {
              unfold Domainport_nat_P.
              do 5 eexists; repeat (splits; eauto).
            }
            unfold Domainport_Portt_P; splits; eauto.
          }
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H32; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H37; do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H84.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          {
            unfold OS_Port_V_OSEventPtrPort.
            assert (nth_val 10 dport = Some (nth_val' 10 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 10 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H84.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H73; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H67; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          unfold RLH_PortPtrINecb; split; eauto.
          eapply RL_PortPtrList_upd; eauto.
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          eapply RL_PortAttr_upd; eauto.
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H84.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H73; do 3 (eapply nth_upd_neqrev; eauto).
        }
        eapply join_set_l; eauto.
        eapply get_indom; eauto.
      }
      eauto.
      good_frm_sovler.
      
      (* RETURN ′ OS_NO_ERR *)
      hoare forward.
    }

    rewrite <- H46. rewrite H72.
    hoare lift 2%nat pre.
    assert ((z2 = 0 /\ Int.unsigned f > 0) \/
            ((z2 > 0 /\ Int.unsigned f > 0) \/ Int.unsigned f = 0)) by lia.
    destruct H76.
    {
      destruct H76; subst z2.
      assert (Int.mul ($ 0) ($ 33) = Int.zero) by (clear; mauto).
      rewrite ! H76. clear H76.

      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_ngt0.
        unfold nat_of_Z. lia.
      }

      naive pure intro.
      destruct H76 as [msg0 [msg' [? ?]]].
      rewrite H76.
      remember (∘ (Int.unsigned f)) as u.
      destruct u.
      { unfold nat_of_Z in Hequ. lia. }
      cbn [dmportp_sllseg_qport_msg].
      naive pure intro.

      (* (port_ptr ′ .. OSQStart) .. len =ₑ ′ 0;ₛ *)
      hoare name lift APortStruct pre.
      hoare name lift port_ptr pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      {
        eapply assign_rule_general.
        {
          intros.
          eapply symbolic_lemmas.struct_offset_rv.
          {
            eapply symbolic_lemmas.addrof_deref_rv.
            eapply port_QStart_rv.
            3: sep autocancel; apply H80.
            {
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
            }
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          all: pauto.
        }
        {
          unfold fst, snd.
          rewrite Int.add_zero.
          split; intros.
          { sep autocancel; apply H80. }
          sep pauto.
        }
        {
          intros.
          instantiate (1:=(V$ 0)).
          instantiate (1:=long).
          symbolic_execution.
        }
        { eapply eq_int; tauto. }
        { sep auto. }
      }

      (* portflush_succ (|Vptr pptr :: nil|);; *)
      hoare normal pre; pure intro.
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare name lift Aop pre.
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply portflush_succ_cont; eauto.
        can_change_aop_solver'.
      }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
      {CSLSEMREL (semaphore ′)};ₛ *)
      hoare normal pre; pure intro.
      hoare forward.
      { pauto. }
      { pauto. }
      { pauto. }
      {
        hoare normal pre; pure intro.
        clear H76 H85 H86.
        cbn [Semrelease].
        eapply cslsemrel_rule.
        { can_change_aop_solver'. }
        {
          rewrite Z2Nat.id by apply Int.unsigned_range.
          apply Int.unsigned_range_2.
        }
        { intros; rewrite Hsem; symbolic execution; pauto. }
        {
          unfold p_local, CurLINV, LINV, OSLInv. intros.
          sep normal in H76; sep destruct H76; sep split in H76.
          sep auto. splits; eauto.
          all: destruct H85 as [? [? [? [? [? ?]]]]]; auto.
        }
      }
      eapply disj_rule; hoare normal pre; pure intro.
      2:{
        exfalso; rewrite H50 in H76; clear - H76.
        unfold notint, val_inj in H76; destruct H76; pauto; inverts H.
      }
      clear H76 H85 H86.
      
      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      subst dpptrl.
      unfold AOSCorePortPtrList.
      hoare normal pre; pure intro.
      rename H15 into Hcptr.
      hoare forward prim.
      {
        sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep split.
        {
          sep autocancel.
          unfold AOSCorePortPtrList.
          sep pauto.
          2:{ instantiate (1:=(set dportls1 pptr
              (Z.to_nat DNUM, ∘ (Int.unsigned x2),
              ∘ (Int.unsigned portid), d, ∘ (Int.unsigned x4),
              ∘ (Int.unsigned x5), ∘ (Int.unsigned x6),
              QueuePort sz nil))).
              eapply RH_CorePortPtrList_upd_dportls; eauto. }

          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl.
          sep normal; sep split.
          2: eapply H17.
          2: split; auto.
          sep autocancel.
          sep name lift kportNode_P.
          eapply kportNode_P_compose.
          4: sep autocancel.
          1,2,3: eauto; pauto.
          rewrite H40; auto.

          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal; sep autocancel.
          instantiate (6:=(dportl1 ++ (update_nth_val 17
          (update_nth_val 15 (update_nth_val 14 dport
            (Vptr (qstartb, Int.zero))) (Vptr (qstartb, Int.zero))) 
              (V$ 0)) :: dportl2)).
          instantiate (5:=(dportmsgll1 ++ (nil) :: dportmsgll2)).
          eapply dmportp_sllseg_compose; eauto.
          { do 3 (eapply nth_upd_neqrev; eauto). }
          {
            clear - H19.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
          }
          { do 3 (eapply nth_upd_neqrev; eauto). }
          sep autocancel.
          eapply disj_split; right.
          sep normal.
          exists (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))
                 (qstartb, Int.zero) (qstartb, Int.zero)
                 ($ Z.of_nat sz) ($ 0) (nil :: msg' ++ msg).
          assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).    
          sep split.
          2:{
            unfold Qport_msg_ptrs_P.
            splits; auto.
            {
              rewrite H85, Int.repr_unsigned.
              unfold get_off_addr, fst, snd.
              rewrite Int.add_zero_l; auto.
            }
            exists 0 0.
            splits; auto; try lia.
          }
          2:{
            split. eapply update_nth; eauto.
            do 2 (eapply nth_upd_neqrev; eauto).
            assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
            rewrite H86; lia.
          }
          2:{ split. do 3 (eapply nth_upd_neqrev; eauto). auto. }
          2:{
            eapply nth_upd_neqrev; eauto.
            eapply update_nth; eauto.
            eapply nth_upd_neqrev; eauto.
          }
          2:{
            do 2 (eapply nth_upd_neqrev; eauto).
            eapply update_nth; eauto.
          }
          2: do 3 (eapply nth_upd_neqrev; eauto).
          2: do 3 (eapply nth_upd_neqrev; eauto).
          assert (∘ (Int.unsigned ($ 0)) = 0%nat) by (clear; mauto).
          assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
          rewrite H86; rewrite H87.
          unfold dmportp_sllseg_qport_msg at 1.
          sep split; auto.
          rewrite Z.sub_0_r.
          assert (∘ (Int.unsigned ($ Z.of_nat sz)) = ((S u) + 
                  ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f))%nat).
          { rewrite Hequ; unfold nat_of_Z; lia. }
          rewrite H88.
          assert ((S u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f))%nat =
                  S (u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f))%nat) by lia.
          rewrite H89.
          cbn [dmportp_sllseg_qport_msg].
          sep normal; exists (msg0 ++ v'19); sep split.
          2: split; auto.
          rewrite app_nil_l.
          unfold fst, snd in H15.
          rewrite Int.add_zero in H15.
          sep autocancel.
          sep lifts (2::3::nil)%nat in H15.
          eapply dmportp_sllseg_qport_msg_app_frm.
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z1) ($ 33))).
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          do 2 sep cancel dmportp_sllseg_qport_msg.

          (* cancel AOSChannelIDTbl *)
          unfold AOSChannelIDTbl;
          sep normal; sep eexists; sep pauto.
          eapply ChannelNode_compose.
          6: sep autocancel; apply H15.
          rewrite H57; auto.
          rewrite H58; auto.
          unfold OS_Channel_V_dstPortsHead; simpl; eauto.
          unfold OS_Channel_V_dstPortsNum; simpl; eauto.
          pauto.
        }
        auto.
  Optimize Proof.
  Optimize Heap.
        eauto.
        {
          
          eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
        }
        {
          eapply R_Kernelport_DomainPort_upd; eauto.
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
        }
        { eapply RLH_Channel_upd_dportls1; eauto.
          right; do 4 eexists; split; eauto. }
        { eauto. }
        {
          eapply RLH_Domainportl_upd_Queue; eauto.
          rewrite H76; auto.
          {
            unfold DomainportNode_P; splits; eauto.
            {
              unfold Domainport_nat_P.
              do 5 eexists; repeat (splits; eauto).
            }
            unfold Domainport_Portt_P; splits; eauto.
          }
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H32; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H37; do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H85.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          {
            unfold OS_Port_V_OSEventPtrPort.
            assert (nth_val 10 dport = Some (nth_val' 10 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 10 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H85.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H73; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H67; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          unfold RLH_PortPtrINecb; split; eauto.
          eapply RL_PortPtrList_upd; eauto.
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          eapply RL_PortAttr_upd; eauto.
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H85.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H73; do 3 (eapply nth_upd_neqrev; eauto).
        }
        eapply join_set_l; eauto.
        eapply get_indom; eauto.
      }
      eauto.
      good_frm_sovler.
      
      (* RETURN ′ OS_NO_ERR *)
      hoare forward.
    }
      
    destruct H75. 2: lia.
    destruct H76. 2: lia.
    rewrite <- H72; rewrite H46.
    hoare lift 2%nat pre.
    eapply backward_rule1.
    {
      eapply dmportp_sllseg_qport_msg_Rle_z1_z2; eauto.
      rewrite Z2Nat.id. all: lia.
    }
    naive pure intro.
    subst z2. rewrite H46 in H74.
    assert (z1 + Z.of_nat ∘ (Int.unsigned entries) +
    (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries) = z1 + Int.unsigned ($ Z.of_nat sz)).
    { rewrite Z2Nat.id. lia. lia. }
    rewrite H77 in H74.
    exfalso; destruct H75; clear - H74 H75; lia.
  }
  {
    unfold OS_Channel_V_semaphore in H46; simpl in H46; inverts H46.
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply absinfer_choice2; [ | | intros ? Hs; apply Hs ].
      all: can_change_aop_solver'.
    }

    (* If (kport ′ .. channel !=ₑ 〈 OS_Channel ∗ 〉 NULL)
    {channel ′ =ₑ kport ′ .. channel;ₛ
    semaphore ′ =ₑ channel ′ .. semaphore;ₛ
    If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
    {CSLSEMACC (semaphore ′, resource_get_res ′);ₛ
    If (resource_get_res ′ ==ₑ NULL)
    {EXIT_CRITICAL;ₛ
    RETURN 〈 char_t 〉 ′ OS_CHANNEL_ERR_BEING_USED}}};ₛ *)
    eapply seq_rule.
    {
      eapply ift_rule''; [symbolic_exe_port|idtac].
      { pauto. }
      hoare normal pre; pure intro.
      clear H46 H50 H56.

      (* channel ′ =ₑ kport ′ .. channel;ₛ *)
      eapply seq_rule.
      {
        hoare name lift channel pre.
        hoare name lift Aop pre.
        eapply assign_rule_lvar.
        { intro s; split; intros; apply H46. }
        {
          intros.
          eapply kport_channel_rv; eauto.
          2: sep pauto.
          2: sep cancel Astruct'; eapply H46.
          pauto.
        }
        { apply assign_type_match_true; simpl; auto. }
        sep auto.
      }
      unfold nth_val'.

      (* semaphore ′ =ₑ channel ′ .. semaphore;ₛ *)
      hoare forward.
      { pauto. }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE) *)
      hoare forward.
      hoare normal pre; pure intro.
      instantiate (1:=Afalse).
      exfalso; clear - H46; pauto.
    }
    eapply disj_rule; hoare normal pre; pure intro.
    2: exfalso; clear - H46; destruct H46; pauto; inverts H.
    hoare forward. hoare normal pre; pure intro.
    clear H46 H50 H56 H64.

    (* port_ptr ′ .. OSQIn =ₑ port_ptr ′ .. OSQStart;ₛ *)
    hoare name lift APortStruct pre.
    hoare name lift port_ptr pre.
    hoare name lift Aop pre.
    eapply seq_rule.
    {
      eapply port_memeber_asgn with (n := 14%nat).
      { pauto. }
      2: pauto.
      2:{
        eapply symbolic_lemmas.nth_val_imp_nth_val'_2.
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 14 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
        lia.
  Optimize Proof.
  Optimize Heap.
      }
      2: pauto.
      2: pauto.
      2: pauto.
      2: pauto.
      2: instantiate (1:=OSMsg_t ∗); eapply eq_vptr; eauto.
      {
        intros. eapply port_QStart_rv.
        3: eapply H46. 2: eauto. auto.
      }
      { 
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 12 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
        destruct H19; auto.
      }
      { sep auto. }
    }

    (* port_ptr ′ .. OSQOut =ₑ port_ptr ′ .. OSQStart;ₛ *)
    hoare name lift APortStruct pre.
    hoare name lift port_ptr pre.
    hoare name lift Aop pre.
    eapply seq_rule.
    {
      eapply port_memeber_asgn with (n := 15%nat).
      { pauto. }
      2: pauto.
      2:{
        eapply nth_upd_neqrev; eauto.
        eapply symbolic_lemmas.nth_val_imp_nth_val'_2.
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 15 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
        lia.
      }
      2: pauto.
      2: pauto.
      2: pauto.
      2: pauto.
      2: instantiate (1:=OSMsg_t ∗); eapply eq_vptr; eauto.
      {
        intros.
        eapply port_QStart_rv.
        3: eapply H46.
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
        instantiate (1:=v'20); clear - H20.
        eapply nth_upd_neqrev; eauto.
      }
      { 
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 12 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
        destruct H19; auto.
      }
      { sep auto. }
    }

    (* port_ptr ′ .. OSQEntries =ₑ ′ 0;ₛ *)
    hoare name lift APortStruct pre.
    hoare name lift port_ptr pre.
    hoare name lift Aop pre.
    eapply seq_rule.
    {
      eapply port_memeber_asgn with (n := 17%nat).
      { pauto. }
      2: pauto.
      2:{
        eapply nth_upd_neqrev; eauto.
        eapply nth_upd_neqrev; eauto.
        eapply symbolic_lemmas.nth_val_imp_nth_val'_2.
        clear - H19.
        destruct dport; simpl in *; tryfalse.
        do 17 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
        lia.
      }
      2: pauto.
      2: pauto.
      2: pauto.
      2: pauto.
      2: instantiate (1:=Int32u); eapply eq_int; auto.
      { intros; instantiate (1:= (V$ 0)); symbolic execution. }
      { pauto. }
      { sep auto. }
    }

    hoare lift 15%nat pre.
    eapply backward_rule1.
    { intros. eapply disj_split in H46. apply H46. }
    eapply disj_rule.
    (* sampleport *)
    {
      hoare normal pre; pure intro.
      unfold Domainport_Portt_P in H30; destruct p5; simpljoin1.
      2:{ rewrite H56 in H46; inverts H46. }
      clear H46.

      unfold dmportp_sllseg_sampleport_msg.
      hoare normal pre; pure intro.
      inversion H46; subst x; clear H46.
      rename v'20 into qstart.
      hoare name lift APortStruct pre.
      hoare name lift port_ptr pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      {
        eapply assign_rule_general.
        {
          intros.
          eapply symbolic_lemmas.struct_offset_rv.
          {
            eapply symbolic_lemmas.addrof_deref_rv.
            eapply port_QStart_rv.
            3: sep autocancel; apply H46.
            {
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
            }
            instantiate (1:=qstart).
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          all: pauto.
        }
        {
          assert ((fst qstart, snd qstart +ᵢ  Int.zero) = qstart).
          { clear; destruct qstart; simpl; rewrite Int.add_zero; auto. }
          rewrite H46; split; intros.
          { sep autocancel; apply H66. }
          sep pauto.
        }
        {
          intros.
          instantiate (1:=(V$ 0)).
          instantiate (1:=long).
          symbolic_execution.
        }
        { eapply eq_int; tauto. }
        { sep auto. }
      }
      
      (* portflush_succ (|Vptr pptr :: nil|);; *)
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare name lift Aop pre.
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply portflush_succ_cont; eauto.
        can_change_aop_solver'.
      }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
      {CSLSEMREL (semaphore ′)};ₛ *)
      hoare forward.
      {
        hoare normal pre; pure intro.
        instantiate (1:=Afalse).
        exfalso; clear - H46; pauto.
      }
      hoare forward. hoare normal pre; pure intro.
      clear H46.
      
      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      subst dpptrl.
      unfold AOSCorePortPtrList.
      hoare normal pre; pure intro.
      rename H15 into Hcptr.
      hoare forward prim.
      {
        sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep split.
        {
          sep autocancel.
          unfold AOSCorePortPtrList.
          sep pauto.
          2:{ instantiate (1:=(set dportls1 pptr
              (Z.to_nat DNUM, ∘ (Int.unsigned x2),
              ∘ (Int.unsigned portid), d, ∘ (Int.unsigned x4),
              ∘ (Int.unsigned x5), ∘ (Int.unsigned x6),
              SamplePort (Some nil)))).
              eapply RH_CorePortPtrList_upd_dportls; eauto. }

          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl.
          sep normal; sep split.
          2: eapply H17.
          2: split; auto.
          sep autocancel.
          sep name lift kportNode_P.
          eapply kportNode_P_compose.
          4: sep autocancel.
          1,2,3: eauto; pauto.
          rewrite H40; auto.

          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal; sep autocancel.
          instantiate (6:=(dportl1 ++ (update_nth_val 17
          (update_nth_val 15
             (update_nth_val 14 dport (Vptr qstart))
             (Vptr qstart)) (V$ 0)) :: dportl2)).
          instantiate (5:=(dportmsgll1 ++ ((@nil val)::nil) :: dportmsgll2)).
          eapply dmportp_sllseg_compose; eauto.
          { do 3 (eapply nth_upd_neqrev; eauto). }
          {
            clear - H19.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
          }
          { do 3 (eapply nth_upd_neqrev; eauto). }
          sep autocancel.
          eapply disj_split; left.
          sep normal; sep split.
          2: do 3 (eapply nth_upd_neqrev; eauto).
          unfold dmportp_sllseg_sampleport_msg.
          sep normal; sep eexists; sep split.
          2: eauto.
          instantiate (5:=v'19 ++ v'21).
          2: simpl; split; auto.
          simpl (length _).
          assert ((fst qstart, snd qstart +ᵢ  Int.zero) = qstart).
          { clear; destruct qstart; simpl; rewrite Int.add_zero; auto. }
          rewrite H66 in H15.
          sep autocancel.

          (* cancel AOSChannelIDTbl *)
          unfold AOSChannelIDTbl;
          sep normal; sep eexists; sep pauto.
          eapply ChannelNode_compose.
          6: sep autocancel; apply H15.
          rewrite H57; auto.
          rewrite H58; auto.
          unfold OS_Channel_V_dstPortsHead; simpl; eauto.
          unfold OS_Channel_V_dstPortsNum; simpl; eauto.
          pauto.
        }
        auto.
  Optimize Proof.
  Optimize Heap.
        eauto.
        {
          
          eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
        }
        {
          eapply R_Kernelport_DomainPort_upd; eauto.
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
        }
        { eapply RLH_Channel_upd_dportls1; eauto. }
        { eauto. }
        {
          eapply RLH_Domainportl_upd_Sample; eauto.
          rewrite H46; auto.
          {
            unfold DomainportNode_P; splits; eauto.
            {
              unfold Domainport_nat_P.
              do 5 eexists; repeat (splits; eauto).
            }
            unfold Domainport_Portt_P.
            eexists; splits; eauto.
          }
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H32; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H37; do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H66.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          {
            unfold OS_Port_V_OSEventPtrPort.
            assert (nth_val 10 dport = Some (nth_val' 10 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 10 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H66.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H56; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          unfold RLH_PortPtrINecb; split; eauto.
          eapply RL_PortPtrList_upd; eauto.
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          eapply RL_PortAttr_upd; eauto.
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H66.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H56; do 3 (eapply nth_upd_neqrev; eauto).
        }
        eapply join_set_l; eauto.
        eapply get_indom; eauto.
      }
      eauto.
      good_frm_sovler.
      
      (* RETURN ′ OS_NO_ERR *)
      hoare forward.
    }

    (* queueport *)
    hoare normal pre; pure intro.
    unfold Domainport_Portt_P in H30; destruct p5; simpljoin1.
    { rewrite H72 in H46; inverts H46. }
    clear H46.
    rewrite H66 in H71; inverts H71.
    rename v'20 into qstart.
    rename v'19 into qend.
    rename v'21 into qin.
    rename v'22 into qout.
    rename n into sz.

    unfold Qport_msg_ptrs_P in H68.
    destruct qstart as [qstartb qstarti].
    destruct H68 as [H68_ [H68_0 [z1 [z2 H68]]]].
    subst qstarti.
    unfold get_off_addr in H68, H68_0.
    cbn [fst snd] in *.
    destruct H68 as [? [? H68]].
    assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).
    rewrite H71 in *; clear H71.
    rewrite Int.add_zero_l in *.
    subst qend qout qin.
    rewrite Int.repr_unsigned in *.
    rename v'24 into entries.
    
    assert (z1 + Int.unsigned entries > Int.unsigned ($ Z.of_nat sz) \/
            z1 + Int.unsigned entries <= Int.unsigned ($ Z.of_nat sz)) by tauto.
    destruct H30.
    {
      assert ((qstartb, Int.zero) =
            dmportp_msg_next_n (∘ ((Int.unsigned ($ Z.of_nat sz)) - z1))
                                (qstartb, Int.mul ($ z1) ($ 33))
                                (qstartb, Int.zero)
                                (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))).
      {
        clear - H68 H70.
        destruct H68. clear z2 H0.
        assert (exists n, n = (∘ (Int.unsigned ($ Z.of_nat sz) - z1))) by eauto.
        destruct H0; rewrite <- H0.
        assert ((0 < x)%nat) by (subst x; unfold nat_of_Z; lia).
        assert ((Z.of_nat x <= Int.unsigned ($ Z.of_nat sz))).
        { subst x; rewrite Z2Nat.id; lia. }
        assert (Z.of_nat x <= 65535) by lia.
        assert ($ Z.of_nat sz = $ ((Z.of_nat x) + z1)).
        {
          subst x; rewrite Z2Nat.id by lia.
          assert (Int.unsigned ($ Z.of_nat sz) - z1 + z1 =
                  Int.unsigned ($ Z.of_nat sz)) by lia.
          rewrite H0; rewrite Int.repr_unsigned; auto.
        }
        rewrite H4. rename z1 into y.
        assert (0 <= y) by lia.
        assert (Z.of_nat x + y <= 65535).
        {
          pose proof H70.
          rewrite H4 in H6.
          rewrite int_usign_eq in H6; try lia.
          assert (y < 65535) by lia.
          clear - H3 H7; mauto.
        }
        eapply dmportp_msg_next_n_to_qstart; eauto.
      }

      eapply backward_rule1.
      { eapply dmportp_sllseg_qport_msg_length. }
      naive pure intro.
      pose proof firstn_skipn (∘ (Int.unsigned ($ Z.of_nat sz) - z1)) msg.
      rewrite <- H73 at 1.
      assert (∘ (Int.unsigned entries) = ((∘ (Int.unsigned ($ Z.of_nat sz) - z1)) + 
        (∘ (Int.unsigned entries) - (∘ (Int.unsigned ($ Z.of_nat sz) - z1))))%nat).
      { apply le_plus_minus; unfold nat_of_Z; apply Zle_natle; lia. }
      rewrite H74 at 1.

      hoare remember (1::nil)%nat pre.
      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_app_frm.
        eapply firstn_length_le.
        rewrite H71; unfold nat_of_Z; apply Zle_natle; lia.
        rewrite skipn_length; rewrite H71; auto.
        eapply H46.
      }
      subst H75.
      hoare lift 2%nat pre.

      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_ngt0.
        assert ((∘ (Int.unsigned ($ Z.of_nat sz) - z1)
            < ∘ (Int.unsigned entries))%nat).
        apply Z2Nat.inj_lt.
        lia. apply Int.unsigned_range. lia. lia.
      }

      naive pure intro.
      destruct H75 as [msg0 [msg' [? ?]]]; rewrite H75.
      remember (∘ (Int.unsigned entries) -
      ∘ (Int.unsigned ($ Z.of_nat sz) - z1))%nat as u.
      destruct u.
      {
        assert (∘ (Int.unsigned entries) = ∘ (Int.unsigned ($ Z.of_nat sz) - z1)) by lia.
        apply Z2Nat.inj in H77.
        lia. apply Int.unsigned_range. lia.
      }
      cbn [dmportp_sllseg_qport_msg].
      naive pure intro.

      (* (port_ptr ′ .. OSQStart) .. len =ₑ ′ 0;ₛ *)
      hoare name lift APortStruct pre.
      hoare name lift port_ptr pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      {
        eapply assign_rule_general.
        {
          intros.
          eapply symbolic_lemmas.struct_offset_rv.
          {
            eapply symbolic_lemmas.addrof_deref_rv.
            eapply port_QStart_rv.
            3: sep autocancel; apply H78.
            {
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
            }
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          all: pauto.
        }
        {
          unfold fst, snd.
          rewrite Int.add_zero.
          split; intros.
          { sep autocancel; apply H78. }
          sep pauto.
        }
        {
          intros.
          instantiate (1:=(V$ 0)).
          instantiate (1:=long).
          symbolic_execution.
        }
        { eapply eq_int; tauto. }
        { sep auto. }
      }

      (* portflush_succ (|Vptr pptr :: nil|);; *)
      hoare normal pre; pure intro.
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare name lift Aop pre.
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply portflush_succ_cont; eauto.
        can_change_aop_solver'.
      }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
      {CSLSEMREL (semaphore ′)};ₛ *)
      hoare normal pre; pure intro.
      hoare forward.
      {
        hoare normal pre; pure intro.
        instantiate (1:=Afalse).
        exfalso; clear - H83; pauto.
      }
      hoare forward. hoare normal pre; pure intro.
      clear H83.
      
      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      subst dpptrl.
      unfold AOSCorePortPtrList.
      hoare normal pre; pure intro.
      rename H15 into Hcptr.
      hoare forward prim.
      {
        sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep split.
        {
          sep autocancel.
          unfold AOSCorePortPtrList.
          sep pauto.
          2:{ instantiate (1:=(set dportls1 pptr
              (Z.to_nat DNUM, ∘ (Int.unsigned x2),
              ∘ (Int.unsigned portid), d, ∘ (Int.unsigned x4),
              ∘ (Int.unsigned x5), ∘ (Int.unsigned x6),
              QueuePort sz nil))).
              eapply RH_CorePortPtrList_upd_dportls; eauto. }

          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl.
          sep normal; sep split.
          2: eapply H17.
          2: split; auto.
          sep autocancel.
          sep name lift kportNode_P.
          eapply kportNode_P_compose.
          4: sep autocancel.
          1,2,3: eauto; pauto.
          rewrite H40; auto.

          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal; sep autocancel.
          instantiate (6:=(dportl1 ++ (update_nth_val 17
          (update_nth_val 15 (update_nth_val 14 dport
            (Vptr (qstartb, Int.zero))) (Vptr (qstartb, Int.zero))) 
              (V$ 0)) :: dportl2)).
          instantiate (5:=(dportmsgll1 ++ (nil) :: dportmsgll2)).
          eapply dmportp_sllseg_compose; eauto.
          { do 3 (eapply nth_upd_neqrev; eauto). }
          {
            clear - H19.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
          }
          { do 3 (eapply nth_upd_neqrev; eauto). }
          sep autocancel.
          eapply disj_split; right.
          sep normal.
          exists (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))
                 (qstartb, Int.zero) (qstartb, Int.zero)
                 ($ Z.of_nat sz) ($ 0)
                 (nil :: msg' ++ v'25 ++ (firstn (∘
                    (Int.unsigned ($ Z.of_nat sz) - z1)) msg)).
          assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).    
          sep split.
          2:{
            unfold Qport_msg_ptrs_P.
            splits; auto.
            {
              rewrite H84, Int.repr_unsigned.
              unfold get_off_addr, fst, snd.
              rewrite Int.add_zero_l; auto.
            }
            exists 0 0.
            splits; auto; try lia.
          }
          2:{
            split. eapply update_nth; eauto.
            do 2 (eapply nth_upd_neqrev; eauto).
            assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
            rewrite H85; lia.
          }
          2:{ split. do 3 (eapply nth_upd_neqrev; eauto). auto. }
          2:{
            eapply nth_upd_neqrev; eauto.
            eapply update_nth; eauto.
            eapply nth_upd_neqrev; eauto.
          }
          2:{
            do 2 (eapply nth_upd_neqrev; eauto).
            eapply update_nth; eauto.
          }
          2: do 3 (eapply nth_upd_neqrev; eauto).
          2: do 3 (eapply nth_upd_neqrev; eauto).
          assert (∘ (Int.unsigned ($ 0)) = 0%nat) by (clear; mauto).
          assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
          rewrite H85; rewrite H86.
          unfold dmportp_sllseg_qport_msg at 1.
          sep split; auto.
          rewrite Z.sub_0_r.
          assert (∘ (Int.unsigned ($ Z.of_nat sz)) = ((S u) + 
                  ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries) +
                  ∘ (Int.unsigned ($ Z.of_nat sz) - z1))%nat).
          { rewrite Hequ; unfold nat_of_Z; lia. }
          rewrite H87.
          assert ((S u +
          ∘ (Int.unsigned ($ Z.of_nat sz) -
             Int.unsigned entries) +
             ∘ (Int.unsigned ($ Z.of_nat sz) - z1))%nat = S (u +
          ∘ (Int.unsigned ($ Z.of_nat sz) -
             Int.unsigned entries) +
             ∘ (Int.unsigned ($ Z.of_nat sz) - z1))%nat) by lia.
          rewrite H88.
          cbn [dmportp_sllseg_qport_msg].
          sep normal; exists (msg0 ++ v'19); sep split.
          2: split; auto.
          rewrite app_nil_l.
          unfold fst, snd in H15.
          rewrite Int.add_zero in H15.
          sep autocancel.
          assert ((u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries) +
          ∘ (Int.unsigned ($ Z.of_nat sz) - z1))%nat =
          (u + (∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries) +
          ∘ (Int.unsigned ($ Z.of_nat sz) - z1)))%nat ) by lia.
          rewrite H89; clear H89.
          sep lifts (2::3::4::nil)%nat in H15.
          eapply dmportp_sllseg_qport_msg_app_frm.
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15.
            sep lift 3%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15.
            rewrite app_length; lia.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z2) ($ 33))).
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          sep autocancel.
          eapply dmportp_sllseg_qport_msg_app_frm.
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z1) ($ 33))).
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          sep lift 2%nat in H15.
          do 2 sep cancel dmportp_sllseg_qport_msg.

          (* cancel AOSChannelIDTbl *)
          unfold AOSChannelIDTbl;
          sep normal; sep eexists; sep pauto.
          eapply ChannelNode_compose.
          6: sep autocancel; apply H15.
          rewrite H57; auto.
          rewrite H58; auto.
          unfold OS_Channel_V_dstPortsHead; simpl; eauto.
          unfold OS_Channel_V_dstPortsNum; simpl; eauto.
          pauto.
        }
        auto.
  Optimize Proof.
  Optimize Heap.
        eauto.
        {
          
          eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
        }
        {
          eapply R_Kernelport_DomainPort_upd; eauto.
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
        }
        { eapply RLH_Channel_upd_dportls1; eauto.
          right; do 4 eexists; split; eauto. }
        { eauto. }
        {
          eapply RLH_Domainportl_upd_Queue; eauto.
          rewrite H83; auto.
          {
            unfold DomainportNode_P; splits; eauto.
            {
              unfold Domainport_nat_P.
              do 5 eexists; repeat (splits; eauto).
            }
            unfold Domainport_Portt_P; splits; eauto.
          }
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H32; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H37; do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H84.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          {
            unfold OS_Port_V_OSEventPtrPort.
            assert (nth_val 10 dport = Some (nth_val' 10 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 10 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H84.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H72; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H66; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          unfold RLH_PortPtrINecb; split; eauto.
          eapply RL_PortPtrList_upd; eauto.
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          eapply RL_PortAttr_upd; eauto.
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H84.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H72; do 3 (eapply nth_upd_neqrev; eauto).
        }
        eapply join_set_l; eauto.
        eapply get_indom; eauto.
      }
      eauto.
      good_frm_sovler.
      
      (* RETURN ′ OS_NO_ERR *)
      hoare forward.
    }

    assert (exists f, Int.unsigned f = Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries).
    {
      exists (Int.sub ($ Z.of_nat sz) entries).
      eapply Int_unsigned_minus. lia.
    }
    destruct H46 as [f ?]; rewrite <- H46.
    assert (Int.unsigned entries = Int.unsigned ($ Z.of_nat sz) - Int.unsigned f) by lia.
    rewrite H71.

    assert (z2 + Int.unsigned f > Int.unsigned ($ Z.of_nat sz) \/
            z2 + Int.unsigned f <= Int.unsigned ($ Z.of_nat sz)) by tauto.
    destruct H73.
    {
      hoare lift 2%nat pre.
      assert ((qstartb, Int.zero) =
            dmportp_msg_next_n (∘ ((Int.unsigned ($ Z.of_nat sz)) - z2))
                                (qstartb, Int.mul ($ z2) ($ 33))
                                (qstartb, Int.zero)
                                (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))).
      {
        clear - H68 H70.
        destruct H68. clear z1 H. rename H0 into H.
        assert (exists n, n = (∘ (Int.unsigned ($ Z.of_nat sz) - z2))) by eauto.
        destruct H0; rewrite <- H0.
        assert ((0 < x)%nat) by (subst x; unfold nat_of_Z in *; lia).
        assert ((Z.of_nat x <= Int.unsigned ($ Z.of_nat sz))).
        { subst x; rewrite Z2Nat.id; lia. }
        assert (Z.of_nat x <= 65535) by lia.
        assert ($ Z.of_nat sz = $ ((Z.of_nat x) + z2)).
        {
          subst x; rewrite Z2Nat.id by lia.
          assert (Int.unsigned ($ Z.of_nat sz) - z2 + z2 =
                  Int.unsigned ($ Z.of_nat sz)) by lia.
          rewrite H0; rewrite Int.repr_unsigned; auto.
        }
        rewrite H4. rename z2 into y.
        assert (0 <= y) by lia.
        assert (Z.of_nat x + y <= 65535).
        {
          pose proof H70.
          rewrite H4 in H6.
          rewrite int_usign_eq in H6; try lia.
          assert (y < 65535) by lia.
          clear - H3 H7; mauto.
        }
        eapply dmportp_msg_next_n_to_qstart; eauto.
      }
      rename v'25 into msg2.

      eapply backward_rule1.
      { eapply dmportp_sllseg_qport_msg_length. }
      naive pure intro.
      pose proof firstn_skipn ∘ (Int.unsigned ($ Z.of_nat sz) - z2) msg2.
      rewrite <- H76 at 1.
      
      assert (∘ (Int.unsigned f) = 
        (∘ (Int.unsigned ($ Z.of_nat sz) - z2) + 
        (∘ (Int.unsigned f) - ∘ (Int.unsigned ($ Z.of_nat sz) - z2)))%nat).
      { apply le_plus_minus; unfold nat_of_Z; apply Zle_natle; lia. }
      rewrite H77 at 1.

      hoare remember (1::nil)%nat pre.
      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_app_frm.
        eapply firstn_length_le.
        rewrite H75; unfold nat_of_Z; apply Zle_natle; lia.
        rewrite skipn_length.
        rewrite H75; auto. eapply H74.
      }
      subst H78.
      hoare lift 2%nat pre.

      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_ngt0.
        assert ((∘ (Int.unsigned ($ Z.of_nat sz) - z2) < ∘ (Int.unsigned f))%nat).
        apply Z2Nat.inj_lt.
        lia. apply Int.unsigned_range. lia. lia.
      }

      naive pure intro.
      destruct H78 as [msg0 [msg' [? ?]]].
      rewrite H78.
      remember (∘ (Int.unsigned f) - ∘ (Int.unsigned ($ Z.of_nat sz) - z2))%nat as u.
      destruct u.
      {
        assert (∘ (Int.unsigned f) = ∘ (Int.unsigned ($ Z.of_nat sz) - z2)) by lia.
        apply Z2Nat.inj in H80.
        lia. apply Int.unsigned_range. lia.
      }
      cbn [dmportp_sllseg_qport_msg].
      naive pure intro.

      (* (port_ptr ′ .. OSQStart) .. len =ₑ ′ 0;ₛ *)
      hoare name lift APortStruct pre.
      hoare name lift port_ptr pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      {
        eapply assign_rule_general.
        {
          intros.
          eapply symbolic_lemmas.struct_offset_rv.
          {
            eapply symbolic_lemmas.addrof_deref_rv.
            eapply port_QStart_rv.
            3: sep autocancel; apply H81.
            {
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
            }
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          all: pauto.
        }
        {
          unfold fst, snd.
          rewrite Int.add_zero.
          split; intros.
          { sep autocancel; apply H81. }
          sep pauto.
        }
        {
          intros.
          instantiate (1:=(V$ 0)).
          instantiate (1:=long).
          symbolic_execution.
        }
        { eapply eq_int; tauto. }
        { sep auto. }
      }

      (* portflush_succ (|Vptr pptr :: nil|);; *)
      hoare normal pre; pure intro.
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare name lift Aop pre.
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply portflush_succ_cont; eauto.
        can_change_aop_solver'.
      }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
      {CSLSEMREL (semaphore ′)};ₛ *)
      hoare normal pre; pure intro.
      hoare forward.
      {
        hoare normal pre; pure intro.
        instantiate (1:=Afalse).
        exfalso; clear - H86; pauto.
      }
      hoare forward. hoare normal pre; pure intro.
      clear H86.
      
      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      subst dpptrl.
      unfold AOSCorePortPtrList.
      hoare normal pre; pure intro.
      rename H15 into Hcptr.
      hoare forward prim.
      {
        sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep split.
        {
          sep autocancel.
          unfold AOSCorePortPtrList.
          sep pauto.
          2:{ instantiate (1:=(set dportls1 pptr
              (Z.to_nat DNUM, ∘ (Int.unsigned x2),
              ∘ (Int.unsigned portid), d, ∘ (Int.unsigned x4),
              ∘ (Int.unsigned x5), ∘ (Int.unsigned x6),
              QueuePort sz nil))).
              eapply RH_CorePortPtrList_upd_dportls; eauto. }

          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl.
          sep normal; sep split.
          2: eapply H17.
          2: split; auto.
          sep autocancel.
          sep name lift kportNode_P.
          eapply kportNode_P_compose.
          4: sep autocancel.
          1,2,3: eauto; pauto.
          rewrite H40; auto.

          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal; sep autocancel.
          instantiate (6:=(dportl1 ++ (update_nth_val 17
          (update_nth_val 15 (update_nth_val 14 dport
            (Vptr (qstartb, Int.zero))) (Vptr (qstartb, Int.zero))) 
              (V$ 0)) :: dportl2)).
          instantiate (5:=(dportmsgll1 ++ (nil) :: dportmsgll2)).
          eapply dmportp_sllseg_compose; eauto.
          { do 3 (eapply nth_upd_neqrev; eauto). }
          {
            clear - H19.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
          }
          { do 3 (eapply nth_upd_neqrev; eauto). }
          sep autocancel.
          eapply disj_split; right.
          sep normal.
          exists (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))
                 (qstartb, Int.zero) (qstartb, Int.zero)
                 ($ Z.of_nat sz) ($ 0)
                 (nil :: msg' ++ msg ++ (firstn (∘
                    (Int.unsigned ($ Z.of_nat sz) - z2)) msg2)).
          assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).    
          sep split.
          2:{
            unfold Qport_msg_ptrs_P.
            splits; auto.
            {
              rewrite H87, Int.repr_unsigned.
              unfold get_off_addr, fst, snd.
              rewrite Int.add_zero_l; auto.
            }
            exists 0 0.
            splits; auto; try lia.
          }
          2:{
            split. eapply update_nth; eauto.
            do 2 (eapply nth_upd_neqrev; eauto).
            assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
            rewrite H88; lia.
          }
          2:{ split. do 3 (eapply nth_upd_neqrev; eauto). auto. }
          2:{
            eapply nth_upd_neqrev; eauto.
            eapply update_nth; eauto.
            eapply nth_upd_neqrev; eauto.
          }
          2:{
            do 2 (eapply nth_upd_neqrev; eauto).
            eapply update_nth; eauto.
          }
          2: do 3 (eapply nth_upd_neqrev; eauto).
          2: do 3 (eapply nth_upd_neqrev; eauto).
          assert (∘ (Int.unsigned ($ 0)) = 0%nat) by (clear; mauto).
          assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
          rewrite H88; rewrite H89.
          unfold dmportp_sllseg_qport_msg at 1.
          sep split; auto.
          rewrite Z.sub_0_r.
          assert (∘ (Int.unsigned ($ Z.of_nat sz)) = ((S u) + 
                  ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f) +
                  ∘ (Int.unsigned ($ Z.of_nat sz) - z2))%nat).
          { rewrite Hequ; unfold nat_of_Z.
            assert (Int.unsigned f <= Int.unsigned ($ Z.of_nat sz)).
            { rewrite H46; pose proof Int.unsigned_range entries; lia. }
            lia. }
          rewrite H90.
          assert ((S u +
          ∘ (Int.unsigned ($ Z.of_nat sz) -
             Int.unsigned f) +
             ∘ (Int.unsigned ($ Z.of_nat sz) - z2))%nat = S (u +
          ∘ (Int.unsigned ($ Z.of_nat sz) -
             Int.unsigned f) +
             ∘ (Int.unsigned ($ Z.of_nat sz) - z2))%nat) by lia.
          rewrite H91.
          cbn [dmportp_sllseg_qport_msg].
          sep normal; exists (msg0 ++ v'19); sep split.
          2: split; auto.
          rewrite app_nil_l.
          unfold fst, snd in H15.
          rewrite Int.add_zero in H15.
          sep autocancel.
          assert ((u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f) +
          ∘ (Int.unsigned ($ Z.of_nat sz) - z2))%nat =
          (u + (∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f) +
          ∘ (Int.unsigned ($ Z.of_nat sz) - z2)))%nat ) by lia.
          rewrite H92; clear H92.
          sep lifts (2::3::4::nil)%nat in H15.
          eapply dmportp_sllseg_qport_msg_app_frm.
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15.
            sep lift 3%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15.
            rewrite app_length; lia.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z1) ($ 33))).
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          sep autocancel.
          eapply dmportp_sllseg_qport_msg_app_frm.
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z2) ($ 33))).
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          sep lift 2%nat in H15.
          do 2 sep cancel dmportp_sllseg_qport_msg.

          (* cancel AOSChannelIDTbl *)
          unfold AOSChannelIDTbl;
          sep normal; sep eexists; sep pauto.
          eapply ChannelNode_compose.
          6: sep autocancel; apply H15.
          rewrite H57; auto.
          rewrite H58; auto.
          unfold OS_Channel_V_dstPortsHead; simpl; eauto.
          unfold OS_Channel_V_dstPortsNum; simpl; eauto.
          pauto.
        }
        auto.
  Optimize Proof.
  Optimize Heap.
        eauto.
        {
          
          eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
        }
        {
          eapply R_Kernelport_DomainPort_upd; eauto.
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
        }
        { eapply RLH_Channel_upd_dportls1; eauto.
          right; do 4 eexists; split; eauto. }
        { eauto. }
        {
          eapply RLH_Domainportl_upd_Queue; eauto.
          rewrite H86; auto.
          {
            unfold DomainportNode_P; splits; eauto.
            {
              unfold Domainport_nat_P.
              do 5 eexists; repeat (splits; eauto).
            }
            unfold Domainport_Portt_P; splits; eauto.
          }
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H32; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H37; do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H87.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          {
            unfold OS_Port_V_OSEventPtrPort.
            assert (nth_val 10 dport = Some (nth_val' 10 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 10 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H87.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H72; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H66; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          unfold RLH_PortPtrINecb; split; eauto.
          eapply RL_PortPtrList_upd; eauto.
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          eapply RL_PortAttr_upd; eauto.
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H87.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H72; do 3 (eapply nth_upd_neqrev; eauto).
        }
        eapply join_set_l; eauto.
        eapply get_indom; eauto.
      }
      eauto.
      good_frm_sovler.
      
      (* RETURN ′ OS_NO_ERR *)
      hoare forward.
    }

    rewrite <- H71. rewrite H46.
    assert ((z1 = 0 /\ Int.unsigned entries > 0) \/
            ((z1 > 0 /\ Int.unsigned entries > 0) \/ Int.unsigned entries = 0)) by lia.
    destruct H74.
    {
      destruct H74; subst z1.
      assert (Int.mul ($ 0) ($ 33) = Int.zero) by (clear; mauto).
      rewrite ! H74. clear H74.

      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_ngt0.
        unfold nat_of_Z. lia.
      }

      naive pure intro.
      destruct H74 as [msg0 [msg' [? ?]]].
      rewrite H74.
      remember (∘ (Int.unsigned entries)) as u.
      destruct u.
      { unfold nat_of_Z in Hequ. lia. }
      cbn [dmportp_sllseg_qport_msg].
      naive pure intro.

      (* (port_ptr ′ .. OSQStart) .. len =ₑ ′ 0;ₛ *)
      hoare name lift APortStruct pre.
      hoare name lift port_ptr pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      {
        eapply assign_rule_general.
        {
          intros.
          eapply symbolic_lemmas.struct_offset_rv.
          {
            eapply symbolic_lemmas.addrof_deref_rv.
            eapply port_QStart_rv.
            3: sep autocancel; apply H78.
            {
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
            }
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          all: pauto.
        }
        {
          unfold fst, snd.
          rewrite Int.add_zero.
          split; intros.
          { sep autocancel; apply H78. }
          sep pauto.
        }
        {
          intros.
          instantiate (1:=(V$ 0)).
          instantiate (1:=long).
          symbolic_execution.
        }
        { eapply eq_int; tauto. }
        { sep auto. }
      }

      (* portflush_succ (|Vptr pptr :: nil|);; *)
      hoare normal pre; pure intro.
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare name lift Aop pre.
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply portflush_succ_cont; eauto.
        can_change_aop_solver'.
      }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
      {CSLSEMREL (semaphore ′)};ₛ *)
      hoare normal pre; pure intro.
      hoare forward.
      {
        hoare normal pre; pure intro.
        instantiate (1:=Afalse).
        exfalso; clear - H74; pauto.
      }
      hoare forward. hoare normal pre; pure intro.
      clear H74.
      
      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      subst dpptrl.
      unfold AOSCorePortPtrList.
      hoare normal pre; pure intro.
      rename H15 into Hcptr.
      hoare forward prim.
      {
        sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep split.
        {
          sep autocancel.
          unfold AOSCorePortPtrList.
          sep pauto.
          2:{ instantiate (1:=(set dportls1 pptr
              (Z.to_nat DNUM, ∘ (Int.unsigned x2),
              ∘ (Int.unsigned portid), d, ∘ (Int.unsigned x4),
              ∘ (Int.unsigned x5), ∘ (Int.unsigned x6),
              QueuePort sz nil))).
              eapply RH_CorePortPtrList_upd_dportls; eauto. }

          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl.
          sep normal; sep split.
          2: eapply H17.
          2: split; auto.
          sep autocancel.
          sep name lift kportNode_P.
          eapply kportNode_P_compose.
          4: sep autocancel.
          1,2,3: eauto; pauto.
          rewrite H40; auto.

          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal; sep autocancel.
          instantiate (6:=(dportl1 ++ (update_nth_val 17
          (update_nth_val 15 (update_nth_val 14 dport
            (Vptr (qstartb, Int.zero))) (Vptr (qstartb, Int.zero))) 
              (V$ 0)) :: dportl2)).
          instantiate (5:=(dportmsgll1 ++ (nil) :: dportmsgll2)).
          eapply dmportp_sllseg_compose; eauto.
          { do 3 (eapply nth_upd_neqrev; eauto). }
          {
            clear - H19.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
          }
          { do 3 (eapply nth_upd_neqrev; eauto). }
          sep autocancel.
          eapply disj_split; right.
          sep normal.
          exists (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))
                 (qstartb, Int.zero) (qstartb, Int.zero)
                 ($ Z.of_nat sz) ($ 0) (nil :: msg' ++ v'25).
          assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).    
          sep split.
          2:{
            unfold Qport_msg_ptrs_P.
            splits; auto.
            {
              rewrite H83, Int.repr_unsigned.
              unfold get_off_addr, fst, snd.
              rewrite Int.add_zero_l; auto.
            }
            exists 0 0.
            splits; auto; try lia.
          }
          2:{
            split. eapply update_nth; eauto.
            do 2 (eapply nth_upd_neqrev; eauto).
            assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
            rewrite H84; lia.
          }
          2:{ split. do 3 (eapply nth_upd_neqrev; eauto). auto. }
          2:{
            eapply nth_upd_neqrev; eauto.
            eapply update_nth; eauto.
            eapply nth_upd_neqrev; eauto.
          }
          2:{
            do 2 (eapply nth_upd_neqrev; eauto).
            eapply update_nth; eauto.
          }
          2: do 3 (eapply nth_upd_neqrev; eauto).
          2: do 3 (eapply nth_upd_neqrev; eauto).
          assert (∘ (Int.unsigned ($ 0)) = 0%nat) by (clear; mauto).
          assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
          rewrite H84; rewrite H85.
          unfold dmportp_sllseg_qport_msg at 1.
          sep split; auto.
          rewrite Z.sub_0_r.
          assert (∘ (Int.unsigned ($ Z.of_nat sz)) = ((S u) + 
                  ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries))%nat).
          { rewrite Hequ; unfold nat_of_Z; lia. }
          rewrite H86.
          assert ((S u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries))%nat =
                  S (u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries))%nat) by lia.
          rewrite H87.
          cbn [dmportp_sllseg_qport_msg].
          sep normal; exists (msg0 ++ v'19); sep split.
          2: split; auto.
          rewrite app_nil_l.
          unfold fst, snd in H15.
          rewrite Int.add_zero in H15.
          sep autocancel.
          sep lifts (2::3::nil)%nat in H15.
          eapply dmportp_sllseg_qport_msg_app_frm.
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z2) ($ 33))).
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          do 2 sep cancel dmportp_sllseg_qport_msg.

          (* cancel AOSChannelIDTbl *)
          unfold AOSChannelIDTbl;
          sep normal; sep eexists; sep pauto.
          eapply ChannelNode_compose.
          6: sep autocancel; apply H15.
          rewrite H57; auto.
          rewrite H58; auto.
          unfold OS_Channel_V_dstPortsHead; simpl; eauto.
          unfold OS_Channel_V_dstPortsNum; simpl; eauto.
          pauto.
        }
        auto.
  Optimize Proof.
  Optimize Heap.
        eauto.
        {
          
          eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
        }
        {
          eapply R_Kernelport_DomainPort_upd; eauto.
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
        }
        { eapply RLH_Channel_upd_dportls1; eauto.
          right; do 4 eexists; split; eauto. }
        { eauto. }
        {
          eapply RLH_Domainportl_upd_Queue; eauto.
          rewrite H74; auto.
          {
            unfold DomainportNode_P; splits; eauto.
            {
              unfold Domainport_nat_P.
              do 5 eexists; repeat (splits; eauto).
            }
            unfold Domainport_Portt_P; splits; eauto.
          }
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H32; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H37; do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H83.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          {
            unfold OS_Port_V_OSEventPtrPort.
            assert (nth_val 10 dport = Some (nth_val' 10 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 10 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H83.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H72; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H66; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          unfold RLH_PortPtrINecb; split; eauto.
          eapply RL_PortPtrList_upd; eauto.
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          eapply RL_PortAttr_upd; eauto.
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H83.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H72; do 3 (eapply nth_upd_neqrev; eauto).
        }
        eapply join_set_l; eauto.
        eapply get_indom; eauto.
      }
      eauto.
      good_frm_sovler.
      
      (* RETURN ′ OS_NO_ERR *)
      hoare forward.
    }

    rewrite <- H46. rewrite H71.
    hoare lift 2%nat pre.
    assert ((z2 = 0 /\ Int.unsigned f > 0) \/
            ((z2 > 0 /\ Int.unsigned f > 0) \/ Int.unsigned f = 0)) by lia.
    destruct H75.
    {
      destruct H75; subst z2.
      assert (Int.mul ($ 0) ($ 33) = Int.zero) by (clear; mauto).
      rewrite ! H75. clear H75.

      eapply backward_rule1.
      {
        eapply dmportp_sllseg_qport_msg_ngt0.
        unfold nat_of_Z. lia.
      }

      naive pure intro.
      destruct H75 as [msg0 [msg' [? ?]]].
      rewrite H75.
      remember (∘ (Int.unsigned f)) as u.
      destruct u.
      { unfold nat_of_Z in Hequ. lia. }
      cbn [dmportp_sllseg_qport_msg].
      naive pure intro.

      (* (port_ptr ′ .. OSQStart) .. len =ₑ ′ 0;ₛ *)
      hoare name lift APortStruct pre.
      hoare name lift port_ptr pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      {
        eapply assign_rule_general.
        {
          intros.
          eapply symbolic_lemmas.struct_offset_rv.
          {
            eapply symbolic_lemmas.addrof_deref_rv.
            eapply port_QStart_rv.
            3: sep autocancel; apply H79.
            {
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
            }
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          all: pauto.
        }
        {
          unfold fst, snd.
          rewrite Int.add_zero.
          split; intros.
          { sep autocancel; apply H79. }
          sep pauto.
        }
        {
          intros.
          instantiate (1:=(V$ 0)).
          instantiate (1:=long).
          symbolic_execution.
        }
        { eapply eq_int; tauto. }
        { sep auto. }
      }

      (* portflush_succ (|Vptr pptr :: nil|);; *)
      hoare normal pre; pure intro.
      hoare name lift oskportid pre.
      hoare name lift osdomainportid pre.
      hoare name lift Aop pre.
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply portflush_succ_cont; eauto.
        can_change_aop_solver'.
      }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
      {CSLSEMREL (semaphore ′)};ₛ *)
      hoare normal pre; pure intro.
      hoare forward.
      {
        hoare normal pre; pure intro.
        instantiate (1:=Afalse).
        exfalso; clear - H75; pauto.
      }
      hoare forward. hoare normal pre; pure intro.
      clear H75.
      
      (* EXIT_CRITICAL;ₛ *)
      apply nth_error_split in H15 as (dpptrl1 & dpptrl2 & ? & ?).
      subst dpptrl.
      unfold AOSCorePortPtrList.
      hoare normal pre; pure intro.
      rename H15 into Hcptr.
      hoare forward prim.
      {
        sep autocancel.
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep split.
        {
          sep autocancel.
          unfold AOSCorePortPtrList.
          sep pauto.
          2:{ instantiate (1:=(set dportls1 pptr
              (Z.to_nat DNUM, ∘ (Int.unsigned x2),
              ∘ (Int.unsigned portid), d, ∘ (Int.unsigned x4),
              ∘ (Int.unsigned x5), ∘ (Int.unsigned x6),
              QueuePort sz nil))).
              eapply RH_CorePortPtrList_upd_dportls; eauto. }

          (* cancel AOSKernelPortIDTbl *)
          unfold AOSKernelPortIDTbl.
          sep normal; sep split.
          2: eapply H17.
          2: split; auto.
          sep autocancel.
          sep name lift kportNode_P.
          eapply kportNode_P_compose.
          4: sep autocancel.
          1,2,3: eauto; pauto.
          rewrite H40; auto.

          (* cancel AOSDomainPortPtrList *)
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal; sep autocancel.
          instantiate (6:=(dportl1 ++ (update_nth_val 17
          (update_nth_val 15 (update_nth_val 14 dport
            (Vptr (qstartb, Int.zero))) (Vptr (qstartb, Int.zero))) 
              (V$ 0)) :: dportl2)).
          instantiate (5:=(dportmsgll1 ++ (nil) :: dportmsgll2)).
          eapply dmportp_sllseg_compose; eauto.
          { do 3 (eapply nth_upd_neqrev; eauto). }
          {
            clear - H19.
            destruct dport; simpl in *; tryfalse.
            do 18 (destruct H19 as [? H19]; split; eauto; destruct dport; simpl in *; tryfalse).
          }
          { do 3 (eapply nth_upd_neqrev; eauto). }
          sep autocancel.
          eapply disj_split; right.
          sep normal.
          exists (qstartb, Int.mul ($ Z.of_nat sz) ($ 33))
                 (qstartb, Int.zero) (qstartb, Int.zero)
                 ($ Z.of_nat sz) ($ 0) (nil :: msg' ++ msg).
          assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).    
          sep split.
          2:{
            unfold Qport_msg_ptrs_P.
            splits; auto.
            {
              rewrite H84, Int.repr_unsigned.
              unfold get_off_addr, fst, snd.
              rewrite Int.add_zero_l; auto.
            }
            exists 0 0.
            splits; auto; try lia.
          }
          2:{
            split. eapply update_nth; eauto.
            do 2 (eapply nth_upd_neqrev; eauto).
            assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
            rewrite H85; lia.
          }
          2:{ split. do 3 (eapply nth_upd_neqrev; eauto). auto. }
          2:{
            eapply nth_upd_neqrev; eauto.
            eapply update_nth; eauto.
            eapply nth_upd_neqrev; eauto.
          }
          2:{
            do 2 (eapply nth_upd_neqrev; eauto).
            eapply update_nth; eauto.
          }
          2: do 3 (eapply nth_upd_neqrev; eauto).
          2: do 3 (eapply nth_upd_neqrev; eauto).
          assert (∘ (Int.unsigned ($ 0)) = 0%nat) by (clear; mauto).
          assert (Int.unsigned ($ 0) = 0) by (clear; mauto).
          rewrite H85; rewrite H86.
          unfold dmportp_sllseg_qport_msg at 1.
          sep split; auto.
          rewrite Z.sub_0_r.
          assert (∘ (Int.unsigned ($ Z.of_nat sz)) = ((S u) + 
                  ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f))%nat).
          { rewrite Hequ; unfold nat_of_Z; lia. }
          rewrite H87.
          assert ((S u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f))%nat =
                  S (u + ∘ (Int.unsigned ($ Z.of_nat sz) - Int.unsigned f))%nat) by lia.
          rewrite H88.
          cbn [dmportp_sllseg_qport_msg].
          sep normal; exists (msg0 ++ v'19); sep split.
          2: split; auto.
          rewrite app_nil_l.
          unfold fst, snd in H15.
          rewrite Int.add_zero in H15.
          sep autocancel.
          sep lifts (2::3::nil)%nat in H15.
          eapply dmportp_sllseg_qport_msg_app_frm.
          {
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            sep lift 2%nat in H15.
            eapply dmportp_sllseg_qport_msg_length in H15.
            sep split in H15; auto.
          }
          {
            instantiate (1:=(qstartb, Int.mul ($ z1) ($ 33))).
            eapply dmportp_sllseg_qport_msg_R_qout_qin in H15.
            sep split in H15; auto.
          }
          do 2 sep cancel dmportp_sllseg_qport_msg.

          (* cancel AOSChannelIDTbl *)
          unfold AOSChannelIDTbl;
          sep normal; sep eexists; sep pauto.
          eapply ChannelNode_compose.
          6: sep autocancel; apply H15.
          rewrite H57; auto.
          rewrite H58; auto.
          unfold OS_Channel_V_dstPortsHead; simpl; eauto.
          unfold OS_Channel_V_dstPortsNum; simpl; eauto.
          pauto.
        }
        auto.
  Optimize Proof.
  Optimize Heap.
        eauto.
        {
          
          eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
        }
        {
          eapply R_Kernelport_DomainPort_upd; eauto.
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
        }
        { eapply RLH_Channel_upd_dportls1; eauto.
          right; do 4 eexists; split; eauto. }
        { eauto. }
        {
          eapply RLH_Domainportl_upd_Queue; eauto.
          rewrite H75; auto.
          {
            unfold DomainportNode_P; splits; eauto.
            {
              unfold Domainport_nat_P.
              do 5 eexists; repeat (splits; eauto).
            }
            unfold Domainport_Portt_P; splits; eauto.
          }
          rewrite H16; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H32; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H34; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H37; do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          do 3 (eapply nth_upd_neqrev; eauto).
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H84.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          {
            unfold OS_Port_V_OSEventPtrPort.
            assert (nth_val 10 dport = Some (nth_val' 10 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 10 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H84.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H72; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
          rewrite H66; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          unfold RLH_PortPtrINecb; split; eauto.
          eapply RL_PortPtrList_upd; eauto.
          rewrite H14; do 3 (eapply nth_upd_neqrev; eauto).
        }
        {
          eapply RL_PortAttr_upd; eauto.
          {
            unfold OS_Port_V_direction.
            assert (nth_val 4 dport = Some (nth_val' 4 dport)).
            {
              apply symbolic_lemmas.nth_val_imp_nth_val'_2.
              clear - H19.
              destruct dport; simpl in *; tryfalse.
              do 4 (destruct H19 as [? H19]; destruct dport; simpl in *; tryfalse).
              lia.
            }
            rewrite H84.
            do 3 (eapply nth_upd_neqrev; eauto).
          }
          rewrite H72; do 3 (eapply nth_upd_neqrev; eauto).
        }
        eapply join_set_l; eauto.
        eapply get_indom; eauto.
      }
      eauto.
      good_frm_sovler.
      
      (* RETURN ′ OS_NO_ERR *)
      hoare forward.
    }
      
    destruct H74. 2: lia.
    destruct H75. 2: lia.
    rewrite <- H71; rewrite H46.
    hoare lift 2%nat pre.
    eapply backward_rule1.
    {
      eapply dmportp_sllseg_qport_msg_Rle_z1_z2; eauto.
      rewrite Z2Nat.id. all: lia.
    }
    naive pure intro.
    subst z2. rewrite H46 in H73.
    assert (z1 + Z.of_nat ∘ (Int.unsigned entries) +
    (Int.unsigned ($ Z.of_nat sz) - Int.unsigned entries) = z1 + Int.unsigned ($ Z.of_nat sz)).
    { rewrite Z2Nat.id. lia. lia. }
    rewrite H76 in H73.
    exfalso; destruct H74; clear - H74 H73; lia.
  }
Qed.
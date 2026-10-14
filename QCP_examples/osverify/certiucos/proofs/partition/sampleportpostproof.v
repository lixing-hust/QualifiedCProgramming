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

Ltac hoare_ex_intro ::=
  repeat match goal with
    | |- {| _, _, _, _, _, _ |} |- _  {{ EX _, _ }} _ {{ _ }} =>
      apply ex_intro_rule; intros 
  end.

Ltac rename_partitionvars::=
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


Lemma SamplePortPostProof :
  forall vl p r tid ,
    Some p = BuildPreA' os_api SamplePortPost samplepostapi vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api SamplePortPost samplepostapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api SamplePortPost = Some (t, d1, d2, s) /\
      {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |-tid {{p }} s {{ Afalse }}.
Proof.
  init_spec.

  hoare lift 8%nat pre.
  destruct v'.
  { apply absabort_rule. }
  destruct v'.
  { apply absabort_rule. }
  destruct v'.
  { apply absabort_rule. }
  remember (v1 :: v') as vsdstcl.
  clear v1 v' Heqvsdstcl.
  rename v0 into vsem.

  (* kport ′ =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
  dstKPort ′ =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
  channel ′ =ₑ 〈 OS_Channel ∗ 〉 NULL;ₛ
  semaphore ′ =ₑ ′ DEFAULT_CHANNLE_SEMAPHROE;ₛ
  error ′ =ₑ ′ OS_NO_ERR;ₛ
  resource_get_res ′ =ₑ ′ 0;ₛ *)
  do 6 hoare forward.
  clear v'0 v'1 v'2 v'3 v'4 v'5.
  rename v'6 into er.

  rename x into msgptr.
  rename x0 into portptr.

  (* ENTER_CRITICAL;ₛ
  If (port_ptr ′ ==ₑ 〈 OS_Port ∗ 〉 NULL)
  {EXIT_CRITICAL;ₛ
  RETURN 〈 char_t 〉 ′ OS_PORT_ERR_NULL};ₛ
  EXIT_CRITICAL;ₛ *)
  partition_enter_trinv.
  rename H12 into Hnodup_d_k.
  destruct H2 as [ | [? ? ]].
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
    simpl in H2; tryfalse.
  }
  hoare forward.
  pure intro.
  partition_exit_trinv.
  clear - H1.
  
  (* ENTER_CRITICAL;ₛ
  If (port_ptr ′ .. coreNum !=ₑ ′ DNUM
      ||ₑ port_ptr ′ .. OSEventType !=ₑ ′ OS_EVENT_TYPE_PORT
      ||ₑ OSTCBCur ′ .. OSTCBY !=ₑ port_ptr ′ .. domain)
  {EXIT_CRITICAL;ₛ
  RETURN 〈 char_t 〉 ′ OS_ERR_PARTITION_UNMAPPED};ₛ
  EXIT_CRITICAL;ₛ *)
  partition_enter_trinv.
  rename H11 into Hnodup_d_k.

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
  unfold RLH_PortPtrINecb in H4; destruct H4.
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
  clear - H1.

  (* ENTER_CRITICAL;ₛ
  If (msg_ptr ′ ==ₑ NULL)
  {EXIT_CRITICAL;ₛ
  RETURN 〈 char_t 〉 ′ OS_ERR_POST_NULL_PTR};ₛ
  EXIT_CRITICAL;ₛ *)
  partition_enter_trinv.
  rename H11 into Hnodup_d_k.

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
  hoare forward; pauto.
  {
    hoare normal pre; pure intro.
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
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply absinfer_choice1; [ | | intros ? Hs; apply Hs ].
      all: can_change_aop_solver'.
    }
    destruct H1 as [? | [? ?]]; subst.
    {
      hoare abscsq; [apply noabs_oslinv | | ].
      eapply err_msgnull_absinfer.
      2:{
        instantiate(1:=Afalse).
        partition_exit_trinv.
        hoare forward.
      }
      can_change_aop_solver'.
    }
    destruct x; contradiction.
  }
  hoare forward.
  hoare normal pre; pure intro.
  partition_exit_trinv.
  clear - H1 H11.
  destruct H1 as [? | [? ?]]; subst.
  { simpl in H11; destruct H11; discriminate. }
  rename x into msgptr; clear H11.

  (* ENTER_CRITICAL;ₛ
  If (port_ptr ′ .. os_code_defs.direction !=ₑ ′ SOURCE
      ||ₑ port_ptr ′ .. mode !=ₑ ′ SAMPLE)
  {EXIT_CRITICAL;ₛ
  RETURN 〈 char_t 〉 ′ OS_PORT_ERR_TYPE};ₛ
  EXIT_CRITICAL;ₛ *)
  partition_enter_trinv.
  rename H10 into Hnodup_d_k.

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
  destruct H10; [ | subst p].
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
  unfold RLH_PortPtrINecb in H3; destruct H3.
  assert (exists n dport msgl,
    nth_error dportl n = Some dport /\ nth_error dportmsgll n = Some msgl /\
    nth_error dpptrl n = Some pptr /\ DomainportNode_P dport (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5) msgl).
  { eapply RLH_Domainportl_abs_getsome; eauto. }
  destruct H12 as [n [dport [msg [? [? [? ?]]]]]].
  apply nth_error_split in H12 as (dportl1 & dportl2 & ? & ?).
  apply nth_error_split in H13 as (dportmsgll1 & dportmsgll2 & ? & ?).
  subst dportl dportmsgll.
  unfold AOSDomainPortPtrList.
  hoare normal pre.
  hoare name lift dmportp_sll pre.
  eapply backward_rule1.
  { eapply dmportp_sllseg_app'_frm; eauto. }
  cbn [dmportp_sllseg].
  hoare normal pre; pure intro.
  rename v'19 into pptr.

  (* If (port_ptr ′ .. os_code_defs.direction !=ₑ ′ SOURCE ||ₑ port_ptr ′ .. mode !=ₑ ′ SAMPLE) *)
  eapply seq_rule.
  {
    eapply ift_rule''; [symbolic_exe_port|idtac].
    hoare normal pre; pure intro.
    destruct d; destruct p5.
    { exfalso. clear - H12; destruct H12; unfold SOURCE, SAMPLE; mauto. }
    all: hoare name lift osdomainportid pre.
    all: hoare abscsq;[apply noabs_oslinv | | ].
    1,3,5: eapply port_indomainport_cont; eauto.
    1,2,3: can_change_aop_solver'.
    all: hoare abscsq;[apply noabs_oslinv | | ].
    1,3,5: eapply absinfer_choice2; eauto.
    1,2,3,4,5,6: can_change_aop_solver'.
    all: hoare abscsq;[apply noabs_oslinv | | ].
    1,3,5: eapply absinfer_choice2; eauto.
    1,2,3,4,5,6: can_change_aop_solver'.
    all: hoare abscsq;[apply noabs_oslinv | | ].
    1,3,5: eapply absinfer_choice1; eauto.
    1,2,3,4,5,6: can_change_aop_solver'.
    all: hoare abscsq;[apply noabs_oslinv | | ].
    1,3,5: eapply err_porttype_absinfer; eauto.
    1,2,3: can_change_aop_solver'.
    instantiate (1:=Afalse).
    all: partition_exit_trinv.
    all: hoare forward.
  }
  hoare forward.
  hoare normal pre; pure intro.
  destruct (Int.ltu Int.zero Int.one) eqn: I.
  2:{ apply ltu_zero_false_imp_eq_zero in I; discriminate. }
  destruct d eqn: Hd; destruct p5 eqn: Hm.
  2,3,4: exfalso.
  2,3,4: clear - H12 I.
  2,3,4: unfold DESTINATION, SOURCE, SAMPLE, QUEUE, bool_or in H12.
  2,3,4: assert (Int.eq ($ 1) ($ 0) = false) by (apply Int.eq_false; mauto).
  2,3,4: rewrite H in *; try rewrite Int.eq_true in *; simpl in H12.
  2,3,4: unfold Int.notbool in H12; try rewrite eq_one_zero in *; try rewrite Int.eq_true in *.
  2,3,4: try rewrite Int_ltu_refl in *; try rewrite I in *; simpl in H12.
  2,3,4: destruct H12; discriminate.
  subst d p5; clear H12 I.
  assert (OSPortAttrTblMode pptr = (V$ SAMPLE)).
  {
    eapply RL_PortAttr_mode_SAMPLE ;eauto.
    rewrite nth_error_app2 by lia.
    rewrite Nat.sub_diag; simpl; auto.
  }
  assert (OSPortAttrTblDir pptr = (V$ SOURCE)).
  {
    eapply RL_PortAttr_dir_SOURCE ;eauto.
    rewrite nth_error_app2 by lia.
    rewrite Nat.sub_diag; simpl; auto.
  }
  (* EXIT_CRITICAL *)
  partition_exit_trinv.
  clear - H12 H16.
  rename H12 into Hmode.
  rename H16 into Hdir.

  (* ENTER_CRITICAL;ₛ
  If (port_ptr ′ .. portID ≥ ′ PORT_NUMS)
  {EXIT_CRITICAL;ₛ
  RETURN 〈 char_t 〉 ′ OS_PORT_ID_INVALID};ₛ
  EXIT_CRITICAL;ₛ *)
  partition_enter_trinv.
  rename H10 into Hnodup_d_k.

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
  destruct H10; [ | subst p].
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
  unfold RLH_PortPtrINecb in H3; destruct H3.
  assert (exists n dport msgl,
    nth_error dportl n = Some dport /\ nth_error dportmsgll n = Some msgl /\
    nth_error dpptrl n = Some pptr /\ DomainportNode_P dport (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5) msgl).
  { eapply RLH_Domainportl_abs_getsome; eauto. }
  destruct H12 as [n [dport [msg [? [? [? ?]]]]]].
  apply nth_error_split in H12 as (dportl1 & dportl2 & ? & ?).
  apply nth_error_split in H13 as (dportmsgll1 & dportmsgll2 & ? & ?).
  subst dportl dportmsgll.
  unfold AOSDomainPortPtrList.
  hoare normal pre.
  hoare name lift dmportp_sll pre.
  eapply backward_rule1.
  eapply dmportp_sllseg_app'_frm;eauto.
  cbn [dmportp_sllseg].
  hoare normal pre; pure intro.
  rename v'19 into pptr.

  eapply seq_rule.
  {
    eapply ift_rule''; [symbolic_exe_port|idtac].
    hoare normal pre; pure intro.
    instantiate (1:= Afalse).
    exfalso.
    clear - H12 H15.
    unfold DomainportNode_P in H15; destruct H15 as [? [? ?]].
    unfold Domainport_nat_P in H; simpljoin1.
    clear - H7 H12.
    unfold bool_or, PORT_NUMS in *.
    rewrite Coqlib.nat_of_Z_eq in *; auto.
    2:{ pose proof Int.unsigned_range_2 x0. lia. }
    destruct (Int.ltu ($ 64) ($ Int.unsigned x0)) eqn: Hlt.
    {
      apply Intlt_true_is_Zlt in Hlt.
      rewrite int_usign_eq in Hlt.
      2,3: clear; mauto.
      rewrite int_usign_eq in Hlt.
      2,3: apply Int.unsigned_range_2.
      lia.
  Optimize Proof.
  Optimize Heap.
    }
    destruct (Int.eq ($ Int.unsigned x0) ($ 64)) eqn: Heq.
    {
      apply Int_eq_dec in Heq.
      rewrite Int.repr_unsigned in *; subst x0.
      rewrite int_usign_eq in H7.
      2,3: clear; mauto.
      lia.
    }
    simpl in H12. pauto.
  }
  hoare forward.
  hoare normal pre; pure intro.
  partition_exit_trinv.
  clear - Hdir Hmode.

  (* ENTER_CRITICAL;ₛ *)
  partition_enter_trinv.
  rename H10 into Hnodup_d_k.

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
  destruct H10; [ | subst p].
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
  unfold RLH_PortPtrINecb in H3; destruct H3.
  assert (exists n dport msgl,
    nth_error dportl n = Some dport /\ nth_error dportmsgll n = Some msgl /\
    nth_error dpptrl n = Some pptr /\ DomainportNode_P dport (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5) msgl).
  { eapply RLH_Domainportl_abs_getsome; eauto. }
  destruct H12 as [n [dport [msg [? [? [? ?]]]]]].
  apply nth_error_split in H12 as (dportl1 & dportl2 & ? & ?).
  apply nth_error_split in H13 as (dportmsgll1 & dportmsgll2 & ? & ?).
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
  hoare abscsq; [apply noabs_oslinv | | ].
  {
    eapply absinfer_choice2; [ | | intros ? Hs; apply Hs ].
    all: can_change_aop_solver'.
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
    { intro s; split; intros; apply H28. }
    {
      intros.
      eapply symbolic_lemmas.array_member_rv_g.
      { sep autocancel; apply H28. }
      { go. }
      { eauto. }
      {
        eapply port_id_rv; eauto.
        sep autocancel; apply H28.
      }
      { go. }
      { auto. }
      { unfold PORT_NUMS; clear; mauto. }
      {
        unfold DomainportNode_P in H15; simpljoin1.
        unfold Domainport_nat_P in H15; simpljoin1.
        clear - H36.
        rewrite! Coqlib.nat_of_Z_eq.
        { rewrite int_usign_eq by (apply Int.unsigned_range_2); auto. }
        { unfold PORT_NUMS; lia. }
        pose proof Int.unsigned_range_2 x3; lia.
      }
      {
        unfold DomainportNode_P in H15; simpljoin1.
        unfold Domainport_nat_P in H15; simpljoin1.
        rewrite H20.
        clear - H36.
        rewrite! Coqlib.nat_of_Z_eq.
        { rewrite int_usign_eq by (apply Int.unsigned_range_2); auto. }
        { unfold PORT_NUMS; lia. }
        pose proof Int.unsigned_range_2 x3; lia.
      }
      2: eauto.
      go.
      unfold DomainportNode_P in H15; simpljoin1.
      unfold Domainport_nat_P in H15; simpljoin1.
      rewrite H34 in H21; inverts H21.
      apply nth_val_nth_error in H22.
      apply nth_val_nth_val'_some_eq in H22.
      assert ((Z.to_nat (Int.unsigned ($ Z.of_nat ∘ (Int.unsigned x)))) = ∘ (Int.unsigned x)).
      {
        clear.
        rewrite Coqlib.nat_of_Z_eq.
        2: pose proof Int.unsigned_range_2 x; lia.
        rewrite int_usign_eq by (apply Int.unsigned_range_2).
        auto.
      }
      rewrite H21; rewrite H22; auto.
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
  unfold DomainportNode_P in H15; simpljoin1.
  unfold Domainport_nat_P in H15; simpljoin1.
  rename x1 into kport. rename x0 into kpptr.
  rewrite H33 in H21; inverts H21.
  rewrite H15 in H27. clear H30.
  rewrite Coqlib.nat_of_Z_eq.
  2: pose proof Int.unsigned_range_2 x; lia.
  rewrite int_usign_eq by (apply Int.unsigned_range_2).
  assert (nth_val' (Z.to_nat (Int.unsigned x)) kportvl = Vptr kpptr).
  { apply nth_val_nth_val'_some_eq; apply nth_val_nth_error; auto. }
  rewrite H21; clear H21.

  (* If (kport ′ ==ₑ 〈 OS_K_Port ∗ 〉 NULL) *)
  hoare forward.
  { destruct kpptr; pauto. }
  {
    hoare normal pre; pure intro.
    instantiate (1:=Afalse).
    exfalso; clear - H21; destruct kpptr; pauto.
  }
  hoare forward.
  rename x into portid.
  hoare normal pre; pure intro. clear H21.
  unfold OS_K_Port_V_coreNum in H27; simpl in H27; inverts H27.
  unfold OS_K_Port_V_portID in H25; simpl in H25; inverts H25.
  unfold OS_K_Port_V_dmport in H26; simpl in H26; inverts H26.

  (* If (kport ′ .. channel ==ₑ 〈 OS_Channel ∗ 〉 NULL) *)
  hoare name lift kportNode_P pre.
  eapply backward_rule1.
  { eapply kportNode_P_getsome_frm; eauto. }
  hoare normal pre; pure intro.
  rename v'19 into kportpb. rename v'21 into kportpl1. rename v'22 into kportpl2.
  rename v'23 into kportl1. rename v'24 into kportl2. rename x1 into channel.

  assert (exists kporth, 
    KernelportNode_P (Vint32 portid :: Vint32 i1 ::
      Vptr pptr :: channel :: V$ DNUM :: Vint32 i :: x8 :: nil) kporth /\
    get kportls (kportpb, Int.zero) = Some kporth).
  {
    eapply RLH_Kernelport_abs_getsome; eauto.
    rewrite H42; auto.
  }
  simpljoin1.
  destruct x as [[[[? ?] ?] ?] ?].
  unfold KernelportNode_P in H21; simpljoin1.
  unfold Kernelport_nat_P in H21; simpljoin1.
  unfold OS_K_Port_V_portID in H21; simpl in H21;
    inverts H21; rename x into portid.
  unfold OS_K_Port_V_status in H48; simpl in H48; inverts H48.
  unfold Kernelport_dmport_P in H26; destruct o;
  unfold OS_K_Port_V_dmport in H26; simpl in H26;
    inverts H26; rename a into portp.
  unfold OS_K_Port_V_coreNum in H46; simpl in H46; inverts H46.
  rewrite int_usign_eq in *.
  2,3,4,5,6,7: clear; pose proof dnum_range; mauto.

  eapply seq_rule.
  {
    eapply ift_rule''; [symbolic_exe_port|idtac].
    {
      destruct H34 as [H34 | [? H34]]; subst channel; auto.
      simpl; destruct x; auto.
    }
    hoare normal pre; pure intro.
    destruct H34 as [H34 | [? H34]]; subst channel; simpl in H21.
    2: destruct x; simpl in H21; contradiction.
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply absinfer_choice1; [ | | intros ? Hs; apply Hs ].
      all: can_change_aop_solver'.
    }
    hoare name lift oskportid pre.
    hoare name lift osdomainportid pre.
    hoare name lift Aop pre.
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply err_nochannel_absinfer; eauto.
      {
        instantiate (1:=∘ (Int.unsigned x1)).
        instantiate (1:=(kportpb, Int.zero)).
        unfold Kernelport_channel_P in H44; destruct o0;
        unfold OS_K_Port_V_channel in H44; simpl in H44; inverts H44.
        auto.
  Optimize Proof.
  Optimize Heap.
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
      rewrite H42; auto.
    }
    { good_frm_sovler. }
    hoare forward.
  }
  hoare forward.
  hoare normal pre; pure intro.
  destruct H34 as [H34 | [? H34]]; subst channel; simpl in H21.
  { destruct H21; tryfalse. }
  unfold Kernelport_channel_P in H44; destruct o0; 
  unfold OS_K_Port_V_channel in H44; simpl in H44; inverts H44.
  clear H21. rename a into chanptr.

  (* os_code_defs.channel ′ =ₑ os_code_defs.kport ′ .. os_code_defs.channel;ₛ *)
  eapply seq_rule.
  {
    hoare name lift os_code_defs.channel pre.
    hoare name lift Aop pre.
    eapply assign_rule_lvar.
    { intro s; split; intros; apply H21. }
    {
      intros.
      eapply kport_channel_rv; eauto.
      sep pauto.
    }
    { apply assign_type_match_true; simpl; auto. }
    sep pauto; sep autocancel; sep auto.
  }
  assert (nth_val' 3 (Vint32 portid :: Vint32 i1 :: Vptr portp
        :: Vptr chanptr :: V$ DNUM :: Vint32 x1 :: x8 :: nil) = Vptr chanptr) by auto.
  rewrite H21 in *; clear H21.
  
  (* If ( channel ′ ==ₑ 〈 OS_Channel ∗ 〉 NULL)
  {EXIT_CRITICAL;ₛ RETURN 〈 (char_t) ∗ 〉 ′ OS_ERR_PORT_NO_CHANNEL};ₛ *)
  hoare forward.
  { destruct chanptr; simpl; auto. }
  {
    hoare normal pre; pure intro.
    instantiate (1:=Afalse).
    destruct chanptr; simpl in H21; clear - H21; tryfalse.
  }
  hoare forward; hoare normal pre; pure intro.
  clear H21.

  hoare abscsq;[apply noabs_oslinv | | ].
  {
    eapply absinfer_choice2;[ | | intros s Hs; exact Hs].
    all: can_change_aop_solver'.
  }

  (* semaphore ′ =ₑ channel ′ .. semaphore;ₛ *)
  assert (R_KernelPortIDTbl_ChannelIDTbl_chan_Vptr
    (kportpb, Int.zero) (Vint32 portid :: Vint32 i1 :: Vptr portp :: Vptr chanptr
     :: V$ DNUM :: Vint32 x1 :: x8 :: nil) chanvl chanl chandstkportll kportls dportls1 dportls2).
  {
    eapply R_KernelPortIDTbl_ChannelIDTbl_abs_getsome; eauto.
    { rewrite H42; auto. }
    unfold OS_K_Port_V_channel; simpl; eauto.
  }
  unfold R_KernelPortIDTbl_ChannelIDTbl_chan_Vptr in H21; simpljoin1.
  unfold OS_K_Port_V_channelID in H21; simpl in H21;
    inverts H21; rename x into chanid.
  unfold OS_K_Port_V_channel in H26; simpl in H26;
    inverts H26; rename x0 into chanptr.
  unfold AOSChannelIDTbl.
  hoare normal pre; pure intro.
  
  hoare name lift ChannelNode pre.
  eapply backward_rule1.
  { eapply ChannelNode_getsome_frm; eauto. }
  unfold node; hoare normal pre; pure intro.
  rename v'28 into chanpb. rename v'19 into chanpl1. rename v'23 into chanpl2.
  rename v'21 into chanl1. rename v'24 into chanl2.
  rename v'22 into chandstkportll1. rename v'25 into chandstkportll2.
  unfold KPort, port_id, addrval, port_coreNum in H25, H47;
  rewrite H25 in H47; inverts H47.
  rename x10 into pptr.
  unfold OS_Channel_V_dstPortsNum in H56; simpl in H56; inverts H56.
  unfold OS_Channel_V_dstPortsHead in H55; simpl in H55; inverts H55.

  (* disj *)
  hoare lifts (13::nil)%nat pre.
  hoare remember (1::nil)%nat pre.
  eapply backward_rule1.
  {
    intros.
    eapply disj_split in H50.
    destruct H50.
    { apply H50. }
    sep normal in H50; sep destruct H50; sep split in H50.
    unfold Domainport_Portt_P in H29.
    destruct p5.
    {
      simpljoin1.
      rewrite H55 in H72.
      unfold SAMPLE, QUEUE in H72.
      exfalso; clear - H72; pauto.
    }
    assert (OSPortAttrTblMode pptr = (V$ QUEUE)).
    {
      eapply RL_PortAttr_mode_QUEUE; eauto.
      {
        rewrite nth_error_app2; [idtac|lia].
        rewrite Nat.sub_diag; simpl; eauto.
      }
      unfold DomainportNode_P; split; eauto.
      unfold Domainport_nat_P.
      do 5 eexists; splits; eauto.
      splits; eauto.
    }
    rewrite Hmode in H69.
    exfalso; clear - H69; pauto.
  }
  pure intro.
  unfold Domainport_Portt_P in H29.
  destruct p5; simpljoin1.
  2:{
    rewrite H55 in H50.
    unfold SAMPLE, QUEUE in H50.
    exfalso; clear - H50; pauto.
  }
  clear H50. rename x into srcmsg.
  
  destruct d.
  2:{
    assert (OSPortAttrTblDir pptr = (V$ DESTINATION)).
    {
      eapply RL_PortAttr_dir_DES; eauto.
      {
        rewrite nth_error_app2; [idtac|lia].
        rewrite Nat.sub_diag; simpl; eauto.
      }
      unfold DomainportNode_P; splits; eauto.
      unfold Domainport_nat_P.
      do 5 eexists; splits; eauto.
      splits; eauto.
      unfold Domainport_Portt_P.
      eexists; splits; eauto.
    }
    rewrite Hdir in H29.
    exfalso; clear - H29; tryfalse.
  }
  unfold Domainport_direction_P in H28.
  unfold OS_Channel_V_channelID in H46; simpl in H46; inverts H46.
  rename x7 into dstkportpl.

  unfold samplepost_sendmemcpy.
  assert (exists chanh,
    ChannelNode_P otherppl (Vint32 chanid :: Vint32 i1
      :: Vint32 v'27 :: Vint32 i :: v'26 :: x15 :: x16 :: x17 :: nil)
      chanh (chanpb, Int.zero) dstkportpl kportls dportls1 dportls2 /\
    get chanls (chanpb, Int.zero) = Some chanh).
  { eapply RLH_Channel_app_cons; eauto. }
  simpljoin1. destruct x as [[[cid cdn] cdstkp] ct].
  assert (nodup_dport kportls) by auto.
  clear Hnodup_d_k.

  (* ASSERT samplepost_dstplength_coresem
           (Vptr pptr :: Vptr msgptr :: v :: vsem :: vsdstcl);; *)
  hoare name lift oschannelid pre.
  hoare name lift oskportid pre.
  hoare name lift osdomainportid pre.
  hoare name lift Aop pre.
  assert ((length vsdstcl = length cdstkp)%nat \/ (length vsdstcl <> length cdstkp)%nat) by lia.
  destruct H50.
  2:{
    hoare abscsq;[apply noabs_oslinv | | ].
    {
      eapply samplepost_dstplength_coresem_abt; eauto.
      can_change_aop_solver'.
    }
    eapply absabort_rule.
  }
  assert (
    ~( ( exists csemid,
          vsem = Vint32 (Int.repr (Z.of_nat csemid)) /\
          Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstcl /\
          get chanls (chanpb, Int.zero) = Some (cid, cdn, cdstkp, OutcoreC csemid)) \/ 
        vsem = Vnull /\ 
        Forall (fun (v:val) => v = Vnull) vsdstcl /\  
        get chanls (chanpb, Int.zero) = Some  (cid, cdn, cdstkp, IncoreC) ) \/
        ( ( exists csemid,
        vsem = Vint32 (Int.repr (Z.of_nat csemid)) /\
        Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstcl /\
        get chanls (chanpb, Int.zero) = Some (cid, cdn, cdstkp, OutcoreC csemid)) \/ 
      vsem = Vnull /\ 
      Forall (fun (v:val) => v = Vnull) vsdstcl /\  
      get chanls (chanpb, Int.zero) = Some  (cid, cdn, cdstkp, IncoreC) )
  ) by (clear; tauto).
  destruct H56.
  {
    hoare abscsq;[apply noabs_oslinv | | ].
    {
      eapply samplepost_dstplength_coresem_abt'; eauto.
      can_change_aop_solver'.
    }
    eapply absabort_rule.
  }
  assert (v <> Vint32 (Int.repr (Z.of_nat (length cdstkp))) \/
          v = Vint32 (Int.repr (Z.of_nat (length cdstkp))) ) by (clear; tauto).
  destruct H64.
  {
    hoare abscsq;[apply noabs_oslinv | | ].
    {
      eapply samplepost_dstplength_coresem_abt''; eauto.
      can_change_aop_solver'.
    }
    eapply absabort_rule.
  }
  subst v.
  assert (~( forall n, (n < (length cdstkp))%nat -> 
              exists dstpaddr dstpcn dstpd dstpid dstpst dstpin dstpout dstpm,
              exists dstkpaddr dstkpst nextdst,
              nth_error cdstkp n = Some dstkpaddr /\ 
              get kportls dstkpaddr = Some (dstpid, Some dstpaddr, Some (chanpb, Int.zero), dstpcn, dstkpst) /\ 
              get dportls dstpaddr = Some (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, SamplePort dstpm) /\
              ((Z.of_nat dstpcn) <> DNUM -> nth_error vsdstcl n = Some (Vint32 (Int.repr (Z.of_nat dstpcn)))) ) \/
            ( forall n, (n < (length cdstkp))%nat -> 
              exists dstpaddr dstpcn dstpd dstpid dstpst dstpin dstpout dstpm,
              exists dstkpaddr dstkpst nextdst,
              nth_error cdstkp n = Some dstkpaddr /\ 
              get kportls dstkpaddr = Some (dstpid, Some dstpaddr, Some (chanpb, Int.zero), dstpcn, dstkpst) /\ 
              get dportls dstpaddr = Some (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, SamplePort dstpm) /\
              ((Z.of_nat dstpcn) <> DNUM -> nth_error vsdstcl n = Some (Vint32 (Int.repr (Z.of_nat dstpcn)))) )) by (clear; tauto).
  destruct H64.
  {
    hoare abscsq;[apply noabs_oslinv | | ].
    {
      eapply samplepost_dstplength_coresem_abt'''; eauto.
      can_change_aop_solver'.
    }
    eapply absabort_rule.
  }
  hoare abscsq;[apply noabs_oslinv | | ].
  {
    eapply samplepost_dstplength_coresem_cont; eauto.
    can_change_aop_solver'.
  }

  unfold ChannelNode_P in H29; simpljoin1.
  rename H66 into Hnodup_dk.
  unfold Channel_nat_P in H29; simpljoin1.
  unfold OS_Channel_V_channelID in H29; simpl in H29;
    inverts H29; rename x into chanid.
  unfold OS_Channel_V_dstPortsNum in H67; simpl in H67;
    inverts H67; rename x0 into dpnum.

  (* merge dmportp_sllseg*)
  hoare remember (17::16::15::5::nil)%nat pre.
  eapply backward_rule1.
  {
    intros.
    instantiate (1:=dmportp_sllseg dportlptr Vnull (dportl1 ++ dport :: dportl2)
    (dportmsgll1 ++ (srcmsg :: nil) :: dportmsgll2) OS_Port_V_nextPort ** H29).
    eapply dmportp_sllseg_compose; eauto.
    sep autocancel.
    left; sep split; auto.
  }
  subst H29.

  (* merge kportNode_P*)
  hoare remember (11::12::13::nil)%nat pre.
  eapply backward_rule1.
  {
    intros.
    instantiate (1:=kportNode_P (kportpl1 ++ (Vptr (kportpb, Int.zero)) :: kportpl2)
                    (kportl1 ++ (Vint32 portid :: Vint32 chanid :: Vptr pptr
                         :: Vptr (chanpb, Int.zero) :: V$ DNUM :: Vint32 x1 :: x8 :: nil) :: kportl2) ** H29).
    eapply kportNode_P_compose; eauto.
    rewrite H42; auto.
  }
  subst H29.

  destruct H56; simpljoin1.
  (* 核间通信 *)
  {
    unfold Channel in H46, H66;
    rewrite H46 in H66; inverts H66.
    unfold Channel_type_P in H65; simpljoin1.
    unfold OS_Channel_V_semaphore in H29; simpl in H29; inverts H29.
    rename x into sem.
    unfold samplepost_sendmemcpy_aux.


    assert ($ Z.of_nat (Z.to_nat (Int.unsigned ($ Z.of_nat sem))) = ($ Z.of_nat sem)) as Hsem.
    {
      rewrite Z2Nat.id by apply Int.unsigned_range.
      apply Int.repr_unsigned.
    }
    (* semaphore ′ =ₑ channel ′ .. semaphore;ₛ *)
    hoare forward.
    { pauto. }

    (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
    {CSLSEMACC (semaphore ′, resource_get_res ′);ₛ
    If (resource_get_res ′ ==ₑ 〈 char_t 〉 ′ 0)
    {EXIT_CRITICAL;ₛ
    RETURN 〈 char_t 〉 ′ OS_CHANNEL_ERR_BEING_USED}};ₛ *)
    hoare forward.
    { pauto. }
    { pauto. }
    { pauto. }
    {
      hoare normal pre; pure intro.
      clear H29 H66 H68.
      unfold Semacc_err, Semacc_succ. 
      hoare name lift resource_get_res pre.
      hoare remember (2:: 1:: nil)%nat pre.
      eapply seq_rule.
      {
        eapply cslsemacc_rule'.
        { subst. can_change_aop_solver'. }
        { rewrite Z2Nat.id. 1,2: eapply Int.unsigned_range_2. }
        {
          rewrite Hsem.
          subst H29.
          symbolic execution.
          pauto.
        }
        {
          subst H29.        
          unfold p_local, CurLINV, LINV, OSLInv.
          intros.
          sep normal in H29; sep destruct H29; sep split in H29.
          sep auto.
  Optimize Proof.
  Optimize Heap.
          splits; eauto.
          all: destruct H66 as [? [? [? [? [? ?]]]]]; auto.
        }
        {
          subst H29.
          unfold p_local, CurLINV, LINV, OSLInv.
          intros.
          sep normal in H29; sep destruct H29; sep split in H29.
          sep auto.
          splits; eauto.
          all: destruct H66 as [? [? [? [? [? ?]]]]]; auto.
        }
      }
      eapply disj_rule'.
      instantiate (1:=Afalse).
      {
        hoare forward.
        hoare normal pre; pure intro.
        partition_exit_trinv.
        unfold AOSDomainPortPtrList, AOSKernelPortIDTbl, AOSChannelIDTbl, dmportp_sll.
        sep pauto; sep autocancel.
        eapply ChannelNode_compose; eauto.
        rewrite H57; auto.
        rewrite H58; auto.
        unfold OS_Channel_V_dstPortsHead; simpl; eauto.
        unfold OS_Channel_V_dstPortsNum; simpl; eauto.
        pauto.
        sep pauto.
        good_frm_sovler.
        instantiate (1:=Afalse).
        hoare forward.
        destruct H66.
        { eapply astar_l_afalse_elim. apply H29. }
        sep split in H29.
        exfalso; clear - H66; mauto.
      }
      subst H29.
      eapply ift_rule''.
      intros; symbolic execution.
      hoare normal pre; pure intro.
      instantiate (1:=Afalse).
      exfalso; clear - H29; mauto.
    }
    eapply disj_rule.
    2:{
      hoare normal pre; pure intro.
      exfalso; clear - H65 H29.
      rewrite H65 in H29.
      destruct H29; mauto.
    }
    eapply backward_rule1.
    { intros. eapply disj_split in H29; apply H29. }
    hoare forward.
    eapply backward_rule1.
    { intros. eapply disj_split in H29; apply H29. }
    eapply disj_rule.
    hoare normal pre; pure intro; eapply pfalse_rule.
    hoare normal pre; pure intro.
    clear H29 H66 H68 H70.

    (* dstKPort ′ =ₑ channel ′ .. dstPortsHead;ₛ *)
    hoare forward.
    { pauto. }
    rename v'26 into dstkport.

    destruct H48.
    {
      unfold R_KernelPortIDTbl_ChannelIDTbl_IncoreC in H29; simpljoin1.
      unfold OS_Channel_V_semaphore in H29; simpl in H29.
      remember ($ Z.of_nat sem) as A.
      remember ($ DEFAULT_CHANNLE_SEMAPHROE) as B.
      inverts H29. rewrite H66 in H65.
      exfalso; clear - H65.
      rewrite Int.eq_true in H65; lia.
    }
    unfold R_KernelPortIDTbl_ChannelIDTbl_OutcoreC in H29; simpljoin1.
    clear H48 H29. destruct H66.
    2:{
      exfalso.
      unfold R_KernelPortIDTbl_ChannelIDTbl_dst in H29; simpljoin1.
      clear - H1 H10 H29.
      eapply map_join_get_some with (x:=dportls1) (y:=dportls2) (z:=dportls); eauto.
    }
    unfold R_KernelPortIDTbl_ChannelIDTbl_scr in H29; simpljoin1.
    unfold port_id in H10; rewrite H10 in H29; inverts H29.
    unfold OS_Channel_V_srcPort in H48; simpl in H48; inverts H48.
    
    destruct H67; simpljoin1.
    2:{
      exfalso.
      unfold Channel_srckport_Queue in H48; simpljoin1.
      destruct H48; simpljoin1;
      unfold OS_Channel_V_srcPort in H48; simpl in H48; inverts H48.
      unfold addrval, port_id in H25, H70; rewrite H25 in H70; inverts H70.
      unfold addrval, port_id in H10, H71; rewrite H10 in H71; inverts H71.
    }
    unfold Channel_srckport_Sample in H48; simpljoin1.
    unfold OS_Channel_V_srcPortsNum in H68; simpl in H68; inverts H68.
    destruct H48; simpljoin1.
    { unfold OS_Channel_V_srcPortsNum in H67;
      simpl in H67; inverts H67. }
    unfold OS_Channel_V_srcPort in H48; simpl in H48; inverts H48.
    unfold addrval, port_id in H25, H68; rewrite H25 in H68; inverts H68.
    rename x7 into pptr. clear H67.
    unfold addrval, port_id in H10, H70; rewrite H10 in H70; inverts H70.
    
    unfold nat_of_Z in *.
    assert (dpnum = ($ (Z.of_nat (length dstkportpl)))).
    {
      clear - H53 H69.
      rewrite <- H69.
      rewrite Z2Nat.id by (apply Int.unsigned_range).
      rewrite Int.repr_unsigned.
      reflexivity.
    }
    assert ((Int.unsigned dpnum) = Z.of_nat (length dstkportpl)).
    {
      clear - H69.
      rewrite <- H69.
      rewrite Z2Nat.id by (apply Int.unsigned_range).
      reflexivity.
    }
    rewrite H69 in *.
    rewrite <- H48 at 1; rewrite H67 at 1; rewrite Nat2Z.id at 1.

    (* If (dstKPort ′ !=ₑ 〈 OS_K_Port ∗ 〉 NULL)
    {WHILE (dstKPort ′ !=ₑ 〈 OS_K_Port ∗ 〉 NULL)
    {error ′ =ᶠ OSSampleSendToDomain (·dstKPort ′ .. dmport,
      msg_ptr ′, port_ptr ′ .. msgInTick·);ₛ
    dstKPort ′ =ₑ 〈 OS_K_Port ∗ 〉 dstKPort ′ .. OSEventPtr;ₛ
    If (error ′ !=ₑ ′ OS_NO_ERR){error ′ =ₑ ′ OS_ERR_DSTPORT_FULL}};ₛ *)
    hoare forward.
    clear - H60; destruct H60 as [? | [? ?]]; subst; pauto.
    pauto.
    pauto.
    {
      instantiate (1:=Afalse).
      hoare normal pre; pure intro.
      destruct H60 as [?|[dkpptr ?]]; subst.
      exfalso; clear - H68; mauto.
      clear H68 H70 H71.
      unfold TmrInv, HeapInv'.
      pure intro.
      hoare name lift oscoreheapid pre.
      hoare name lift oschannel pre.
      hoare name lift oskport pre.
      hoare name lift osdomainport pre.
      rename v'19 into cHeapl.
      assert (
        ~ ( exists mlen msg,
          Get_heapl_addrval cHeapl msgptr (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\
          (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z ) \/
        ( exists mlen msg,
              Get_heapl_addrval cHeapl msgptr (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\
              (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z )
      ) as [ | ] by tauto.
      {
        destruct (dstkportpl).
        {
          assert (length (@nil addrval) = 0%nat) by auto.
          rewrite H71.
          cbn [Channel_dstkport_get].
          pure intro; tryfalse.
        }
        assert ((length (a :: l)) = S (length l)) by auto.
        rewrite H71 at 1.
        hoare name lift Aop pre.
        hoare abscsq; [apply noabs_oslinv | auto .. ].
        eapply samplepost_sendmemcpy_aux_Outcore_abt; eauto.
        can_change_aop_solver'.
        apply absabort_rule.
      }
      simpljoin1.
      rename x0 into mlen. rename x3 into msg.
      assert (In_heapl_addrval cHeapl msgptr (Z.to_nat (Int.unsigned mlen + 1))).
      {
        destruct H70 as [? [? [? [? ?]]]].
        unfold In_heapl_addrval.
        exists x0 x3; split; auto.
      }

      (* split AOScoreheapl *)
      hoare name lift AOScoreheapl pre.
      eapply backward_rule1.
      eapply port_split_coreheapl; eauto.
      naive pure intro.
      rename v'19 into cheapl1. rename v'23 into cheapl2.
      rename v'24 into msgn. rename v'25 into msg1. rename v'26 into msg2.
      destruct msg1 as [ | len msg1 ].
      {
        simpl in H74.
        exfalso; clear - H74.
        simpljoin1.
        assert (0%nat = Z.to_nat 0) by auto.
        rewrite H in H2.
        assert (Int.unsigned mlen + 1 > 0).
        { pose proof unsigned_ge0 mlen; lia. }
        eapply Z2Nat.inj in H2; lia.
      }
      simpljoin1. simpl in H77; rewrite <- H77 in *.
      assert (len = Vint32 mlen /\ msg = msg1).
      { eapply nodup_cheapl_get_msg; eauto. }
      simpljoin1; rename msg1 into msg.

      hoare name lift AOSTime pre.
      hoare name lift dstKPort pre.
      hoare name lift Channel_dstkport_get pre.
      hoare name lift osdomainport pre.
      hoare name lift ostmid pre.
      hoare name lift OtherPortPtrList pre.
      rename v'9 into tm.
      rename x5 into pin.
      
      eapply backward_rule1.
      eapply OtherPortPtrList_Forall_struct_type_vallist_match'.
      pure intro.

      assert (
        exists dstportpl dstpptrnl dstportupdl dstportupdhl,
          length dstportpl = length dstkportpl /\
          length dstpptrnl = length dstkportpl /\
          length dstportupdl = length dstkportpl /\
          length dstportupdhl = length dstkportpl /\
          forall n, (n < length dstkportpl)%nat ->
            exists dstkportp dstportp dstpptrn dstpid dstkpst
                dstpd dstpst dstpin dstpout dstpm,
            exists dstpcn dstportupd dstport dstportupdh nextdst,
              nth_error dstkportpl n = Some dstkportp /\
              nth_error dstportpl n = Some dstportp /\
              nth_error dstportupdl n = Some dstportupd /\
              nth_error dstportupdhl n = Some dstportupdh /\
              nth_error dstpptrnl n = Some dstpptrn /\
              nth_error otherppl dstpptrn = Some dstportp /\
              nth_error otherpl dstpptrn = Some dstport /\
              get kportls dstkportp =
                Some (dstpid, Some dstportp, Some (chanpb, Int.zero), dstpcn, dstkpst) /\
              get dportls2 dstportp = 
                Some (dstpcn, dstpd, dstpid,
                  DestinationP nextdst, dstpst, dstpin, dstpout, SamplePort dstpm) /\
              struct_type_vallist_match' OS_Port_Seg_dls dstportupd /\
              OS_Port_V_msgInTick dstportupd = Some (Vint32 pin) /\
              OS_Port_V_msgOutTick dstportupd = Some (Vint32 tm) /\
              (forall (m:nat), (m < 18)%nat -> (m <> 8)%nat -> (m <> 9)%nat -> 
                nth_val m dstportupd = nth_val m dstport) /\
              dstportupdh = (dstpcn, dstpd, dstpid,
                DestinationP nextdst, dstpst, Z.to_nat (Int.unsigned pin),
                Z.to_nat (Int.unsigned tm), SamplePort (Some msg))
      ).
      { eapply dstkportpl_get_and_upd_list_Sample_Outcore; eauto. }
      destruct H76 as [dstportpl [dstpptrnl [dstportupdl [dstportupdhl [? [? [? [? ?]]]]]]]].

      eapply seq_rule.
      {
        hoare name lift osdomainportid pre.
        hoare name lift OtherPortPtrList pre.
        hoare name lift Channel_dstkport_get pre.
        hoare name lift dstKPort pre.
        hoare name lift Aop pre.
        hoare remember (1::2::3::4::5::nil)%nat pre.
        eapply backward_rule1.
        {
          instantiate (1:=
            EX n ndkpv ndkpptr notherpl nothermsgll ndportls2 ndportls,
            ( [| ndkpv = Vnull |] ** [| n = length dstkportpl |] \\//
              [| ndkpv = Vptr ndkpptr |] **
              [| nth_error dstkportpl n = Some ndkpptr |]  ) **
            <||
            spec_code_cons (samplepost_sendmemcpy_aux_Outcore ((length dstkportpl) - n)%nat
              (Vptr pptr
              :: Vptr msgptr
                  :: V$ Z.of_nat (length dstkportpl)
                    :: V$ Z.of_nat sem :: vsdstcl))
            (Semrelease (V$ Z.of_nat sem);; END Some (V$ OS_NO_ERR)) ||>  **
            LV dstKPort @ OS_K_Port ∗ |-> ndkpv **
            Channel_dstkport_get (Vptr dkpptr) Vnull (length dstkportpl) dstkportpl **
            OtherPortPtrList otherppl notherpl nothermsgll **
            Hdomainportl ndportls **
            [| notherpl = set_dportl_n_times otherpl n dstpptrnl dstportupdl |] **
            [| nothermsgll = set_dportmsgll_n_times othermsgll n dstpptrnl (msg :: nil) |] **
            [| ndportls2 = set_dportls_n_times dportls2 n dstportpl dstportupdhl |] **
            [| join dportls1 ndportls2 ndportls |] **
            [| RLH_Channel otherppl
                (chanpl1 ++ Vptr (chanpb, Int.zero) :: chanpl2)
                (chanl1 ++ (Vint32 chanid :: V$ 1 :: V$ Z.of_nat (length dstkportpl)
                 :: V$ Z.of_nat sem :: Vptr dkpptr :: x15 :: Vptr (kportpb, Int.zero) :: x17 :: nil) :: chanl2)
                (chandstkportll1 ++ dstkportpl :: chandstkportll2) chanls
                kportls dportls1 ndportls2 |] **
            [| R_KernelPortIDTbl_ChannelIDTbl
                (kportpl1 ++ Vptr (kportpb, Int.zero) :: kportpl2)
                (kportl1 ++
                (Vint32 portid
                  :: Vint32 chanid
                    :: Vptr pptr
                        :: Vptr (chanpb, Int.zero)
                          :: V$ DNUM :: Vint32 x1 :: x8 :: nil) :: kportl2)
                (chanpl1 ++ Vptr (chanpb, Int.zero) :: chanpl2)
                (chanl1 ++
                (Vint32 chanid
                  :: V$ 1
                    :: V$ Z.of_nat (length dstkportpl)
                        :: V$ Z.of_nat sem
                          :: Vptr dkpptr
                              :: x15
                                :: Vptr (kportpb, Int.zero) :: x17 :: nil)
                :: chanl2)
                (chandstkportll1 ++ dstkportpl :: chandstkportll2) kportls
                dportls1 ndportls2 |] **
            [| RLH_OtherPortPtrList otherppl notherpl nothermsgll ndportls2 |] **
            [| Channel_dstkport_Sample_OutcoreC otherppl 
                (chanpb, Int.zero) dstkportpl kportls ndportls2 |] **
            H82
          ).
          {
            intros.
            exists 0%nat (Vptr dkpptr) dkpptr otherpl othermsgll dportls2; exists dportls.
            sep normal.
            apply disj_split; right.
            destruct dstkportpl; cbn [length ] in *.
            unfold Channel_dstkport_get in H83; sep split in H83; tryfalse.
            cbn [Channel_dstkport_get] in *.
            sep normal in H83; sep destruct H83; sep split in H83. inverts H86.
            sep normal; sep eexists; sep split; eauto.
          }
        }
        subst H82.
        eapply while_rule.
        {
          intros.
          sep destruct H82.
          apply disj_split in H82.
          destruct H82.
          symbolic execution.
          symbolic execution.
          destruct x5; pauto.
          destruct x5; pauto.
        }
        hoare normal pre; hoare_ex_intro.
        rename v'9 into n. rename v'19 into ndkpv.
        rename v'24 into ndportl. rename v'25 into ndportmsgll.
        eapply aconj_aistrue_rule.
        {
          intros.
          sep destruct H82.
          apply disj_split in H82.
          instantiate (1:=val_inj (notint (val_inj (val_eq ndkpv Vnull)))).
          destruct H82; sep normal in H82; sep split in H82.
          symbolic execution.
          symbolic execution.
          destruct v'23; pauto.
          unfold val_eq; destruct v'23; pauto.
        }
        hoare normal pre; pure_intro.
        eapply backward_rule1.
        intros s Hs; eapply disj_split in Hs; apply Hs.
        eapply disj_rule.
        { hoare normal pre; pure intro; exfalso. clear - H90; pauto. }
        hoare normal pre; pure intro.
        rename v'23 into ndstkportp.
        rename v'27 into ndportls.
        clear H90 H91 H92.
        apply nth_error_split in H83 as (dstkportpl1 & dstkportpl2 & ? & ?).
        subst dstkportpl.
        hoare name lift Channel_dstkport_get pre.
        eapply backward_rule1.
        eapply Channel_dstkport_get_app_frm; eauto.
        hoare normal pre; pure intro. rename v'19 into vn.
        assert ((length (dstkportpl1 ++ ndstkportp :: dstkportpl2) - length dstkportpl1)%nat = S (length dstkportpl2)).
        clear; induction dstkportpl1; simpl; try lia.
        rewrite H95.
        assert ((S (length dstkportpl2) - 1)%nat = length dstkportpl2) by (clear; mauto).
        rewrite H96.
        hoare name lift msg_ptr pre.
        assert ((length dstkportpl1 <
        length (dstkportpl1 ++ ndstkportp :: dstkportpl2))%nat).
        clear; induction dstkportpl1; simpl; try lia.
        pose proof H81 _ H97.
        simpljoin1.
        rewrite nth_error_middle in H98; inverts H98; rename x0 into ndstkportp.
        rename x7 into ndstportp.

        (* find ndstkport in kportNode_P *)
        hoare name lift kportNode_P pre.
        pose proof RLH_Kernelport_abs_getsome' _ _ _ _ _ _ _ _ _ H105 H5.
        simpljoin1.
        eapply backward_rule1.
        eapply kportNode_P_getsome_frm; eauto.
        hoare normal pre; pure intro.
        rename v'9 into ndstkportpb.
        rename v'19 into kportpl1'. rename v'23 into kportpl2'.
        rename v'24 into kportl1'. rename v'25 into kportl2'.
        rename x22 into ndstport. rename x9 into ndstpptrn.
        unfold KernelportNode_P in H112.
        simpljoin1.
        unfold Kernelport_dmport_P in H123.
        unfold OS_K_Port_V_dmport in H123; simpl in H123; inverts H123.
        unfold Kernelport_channel_P in H124.
        unfold OS_K_Port_V_channel in H124; simpl in H124; inverts H124.
        unfold Kernelport_nat_P in H112; simpljoin1.
        unfold OS_K_Port_V_portID in H112; simpl in H112;
          inverts H112; rename x0 into ndstportid.
        unfold OS_K_Port_V_status in H126; simpl in H126; inverts H126.
        unfold OS_K_Port_V_coreNum in H124; simpl in H124; inverts H124.
        
        (* find dstport in OtherPortPtrList *)
        hoare name lift OtherPortPtrList pre.
        assert (exists n ndstport ndstmsgll,
          nth_error otherpl n = Some ndstport /\
          nth_error othermsgll n = Some ndstmsgll /\
          nth_error otherppl n = Some ndstportp /\
          OtherPortNode_P ndstport (∘ (Int.unsigned x7), x13, ∘ (Int.unsigned ndstportid),
            DestinationP x24, x14, x16, x18, SamplePort x19) ndstmsgll).
        { eapply RLH_OtherPortPtrList_abs_getsome with (dportls2:=dportls2); auto. }
        simpljoin1.

        assert (x0 = ndstpptrn) by (eapply otherppl_not_same_elements; eauto).
        subst x0. clear H124.
        rewrite H112 in H104; inverts H104.
        hoare name lift OtherPortPtrList pre.
        hoare name lift dmportp_sllseg pre.

        pose proof H64 _ H97; simpljoin1.
        assert (nth_error (dstkportpl1 ++ (ndstkportpb, Int.zero) :: dstkportpl2) (length dstkportpl1) = Some (ndstkportpb, Int.zero)).
        { clear; induction dstkportpl1; simpl; intros; eauto. }
        unfold addrval in H104, H128; rewrite H104 in H128; inverts H128.
        unfold port_coreNum in H105; rewrite H105 in H124; inverts H124.
        rename x0 into ndstportp.
        assert (get dportls ndstportp = Some
          (∘ (Int.unsigned x7), x13, ∘ (Int.unsigned ndstportid),
          DestinationP x24, x14, x16, x18, SamplePort x19)).
        { eapply join_get_get_r; eauto. }
        unfold port_coreNum, port_id in H126, H124;
        rewrite H126 in H124; inverts H124.
        
        assert (exists ndstpin' ndstpout' ndstpm',
        get (set_dportls_n_times dportls2 (length dstkportpl1) dstportpl
        dstportupdhl) ndstportp = Some (∘ (Int.unsigned x7), x13, ∘ (Int.unsigned ndstportid),
          DestinationP x24, x14, ndstpin', ndstpout', SamplePort ndstpm')).
        {
          eapply set_dportls_n_times_upd_same_elements.
          10: eauto.
          9: eauto.
          all: eauto.
          lia.
  Optimize Proof.
  Optimize Heap.
          unfold port_intick, port_outick; rewrite H80; auto.
          rewrite H76; auto.
          rewrite H78; clear - H81; intros.
          specialize (H81 _ H); simpljoin1.
          do 14 eexists; splits; eauto.
        }
        simpljoin1.

        rename x21 into ndstportupd.
        assert (exists ndstport',
        nth_error (set_dportl_n_times otherpl (length dstkportpl1) dstpptrnl
        dstportupdl) ndstpptrn = Some ndstport' /\
        forall m : nat,
          (m < 18)%nat -> m <> 8%nat -> m <> 9%nat ->
          nth_val m ndstportupd = nth_val m ndstport').
        {
          eapply set_dportl_n_times_upd_same_elements.
          7: eauto. all: eauto.
          lia. 
          unfold vallist; rewrite H79; auto.
          rewrite H78; clear - H81; intros.
          specialize (H81 _ H); simpljoin1.
          do 3 eexists; splits; eauto.
        }
        simpljoin1.

        assert ((Int.repr (Z.of_nat (Z.to_nat (Int.unsigned pin))) = pin)%nat) as Hpin.
        {
          rewrite Z2Nat.id by apply Int.unsigned_range.
          apply Int.repr_unsigned.
        }

        assert (∘ (Int.unsigned x7) <> Z.to_nat DNUM) as Hneq.
        {
          unfold OtherPortNode_P in H125; simpljoin1.
          unfold OtherPort_nat_P in H125; simpljoin1.
          unfold nat_of_Z in *.
          apply inline_bittblfunctions.z2n_int_eq in H132.
          subst x22; intro; destruct H133; eapply Z2Nat.inj; eauto.
          apply Int.unsigned_range.
          apply dnum_range.
        }

        eapply seq_rule.
        {
          eapply calle_rule_lvar'.
          { pauto. }
          {
            (* RV *)
            intros. 
            eapply rvl_elim.
            {
              eapply dstKPort_dmport_rv.
              2: sep autocancel; apply H130.
              pauto.
            }
            eapply rvl_elim; [symbolic execution| ].
            eapply rvl_elim;[ | apply rvl_nil].
            instantiate (1:=(Vint32 (Int.repr (Z.of_nat (Z.to_nat (Int.unsigned pin)))))).
            eapply astar_mono in H130.
            2:{
              instantiate (1:=dmportp_sll dportlptr (dportl1 ++ dport :: dportl2)
              (dportmsgll1 ++ (srcmsg :: nil) :: dportmsgll2) OS_Port_V_nextPort ).
              unfold dmportp_sll. sep pauto.
            }
            2:{ intros s0 Hs. apply Hs. }
            eapply dmportp_sllseg_app'_frm in H130; eauto.
            cbn [dmportp_sllseg] in H130.
            sep normal in H130; sep destruct H130; sep split in H130.
            inverts H131; rename x23 into pptr.
            eapply port_msgInTick_rv; eauto.
            2: sep autocancel; apply H130.
            unfold DomainportNode_P.
            splits; simpl.
            {
              do 5 eexists.
              splits; eauto.
              splits; eauto.
            }
            instantiate (1:=SourceP); simpl; eauto.
            instantiate (3:=(SamplePort (Some srcmsg))).
            simpl; eexists; splits; eauto.
          }
          {
            (* ==>pre *)
            unfold getasrt, OSSampleSendToDomainPre, OSSampleSendToDomainPre'.
            intros.
            sep name lift Aisr Ais aemp_isr_is in H130.
            eapply elim_aemp_isr_is_prop in H130.
            sep normal; sep eexists.
            sep autocancel.
            sep split.
            3: auto.
            3: eapply H127.
            20: rewrite H50; instantiate (1:=(dstkportpl1 ++ (ndstkportpb, Int.zero) :: dstkportpl2)); auto.
            20: eauto.
            19: simpl; eauto.
            16,17,18: auto.
            15: eapply H107.
            13: auto.
            13: rewrite Hpin; auto.
            12: eapply H129.
            8: eapply H85.
            6: eapply H87.
            6: eapply H86.
            4: rewrite Hpin; eapply H10.
            4: eauto.
            3: eapply H25.
            4: eapply H105.
            sep name lift Aop in H130.
            eapply disj_split.
            left.
            sep normal; sep eexists.
            sep pauto.
            eapply H128.
            auto.
            eapply H124.
            eapply H46.
            2: rewrite Hpin; eauto.
            2: eauto.
            instantiate (1:=dpptrl).
            eauto.
          }
          { good_frm_sovler. }
          {
            unfold retpost.
            unfold getasrt, OSSampleSendToDomainPost, OSSampleSendToDomainPost'.
            intros.
            sep normal in H130; sep destruct H130; sep split in H130.
            rewrite H143; auto.
          }
          { pauto. }
          {
            unfold getasrt, OSSampleSendToDomainPost, OSSampleSendToDomainPost'.
            sep pauto.
            sep cancel p_local.
            sep pauto.
          }
          {
            unfold getasrt, OSSampleSendToDomainPre, OSSampleSendToDomainPre'.
            sep pauto.
            sep cancel p_local.
            sep pauto.
          }
        }
        unfold getasrt, OSSampleSendToDomainPost, OSSampleSendToDomainPost'.
        hoare normal pre; pure intro.
        inversion H141; clear H141.
        subst v'19 v'23 v'27 v'28 v'30 v'35 v'34 v'36 v'37 v'42 v'43 v'44 v'45 
        v'56 v'57 v'47  v'26 v'24 v'53 v'54 v'55 v'62 v'63 v'64 v'68 v'69 
        v'70 v'71 v'72 v'73 v'65 v'66 v'67.
        simpl in H131; inversion H131; clear H131.
        subst v'46 v'25 v'29. 
        hoare normal pre; pure intro.
        
        (* disj *)
        eapply backward_rule1.
        intros. eapply disj_split in H130; eapply H130.
        eapply disj_rule.
        2:{
          hoare normal pre; pure intro.
          inverts H130.
        }
        naive pure intro.
        subst v'49 v'50 v'51 v'52 v'59 v'58.
        clear v'9 H130.
        unfold port_coreNum, port_id in H142, H124;
        rewrite H142 in H124; inverts H124.
        rewrite H145 in H128; inverts H128.
        
        unfold OS_K_Port_V_OSEventPtr in H84; simpl in H84; inverts H84.
        (* dstKPort ′ =ₑ 〈 OS_K_Port ∗ 〉 dstKPort ′ .. OSEventPtr *)
        eapply seq_rule.
        {
          eapply assign_rule_lvar.
          { split; [ | sep pauto]. sep pauto. }
          {
            intros.
            eapply symbolic_lemmas.cast_rv_tptr with (v:= vn) (t1:= Void).
            2: pauto.
            eapply symbolic_lemmas.struct_member_rv_flag; eauto.
            { sep cancel dstKPort; sep autocancel; apply H84. }
            { pauto. }
            { pauto. }
            { pauto. }
            { pauto. }
          }
          { eapply eq_vptr; eauto. }
          { intros; sep eexists; sep cancel p_local; sep pauto. }
        }

        assert (v'48 = ndstportupd). 
        {
          clear - H132 H133 H134 H135 Hpin H129 H107 H108 H109.
          rewrite Hpin in *; clear Hpin.
          rename v'48 into ndstport.
          destruct ndstport; destruct ndstportupd; simpl in *; tryfalse.
          do 18 (destruct H107 as [? H107]; destruct H132 as [? H132]; destruct ndstport; destruct ndstportupd; simpl in *; tryfalse).
          unfold OS_Port_V_msgInTick in H108; simpl in H108; inverts H108.
          unfold OS_Port_V_msgInTick in H133; simpl in H133; inverts H133.
          unfold OS_Port_V_msgOutTick in H109; simpl in H109; inverts H109.
          unfold OS_Port_V_msgOutTick in H134; simpl in H134; inverts H134.

          assert (v = v0).
          {
            assert ((0 < 18)%nat) by lia; assert ((0 <> 8)%nat) by lia; assert ((0 <> 9)%nat) by lia.
            specialize (H129 _ H35 H36 H37); simpl in H129.
            specialize (H135 _ H35 H36 H37); simpl in H135.
            rewrite <- H129 in H135; inverts H135; auto.
          }
          subst v.
          assert (v1 = v2).
          {
            assert ((1 < 18)%nat) by lia; assert ((1 <> 8)%nat) by lia; assert ((1 <> 9)%nat) by lia.
            specialize (H129 _ H35 H36 H37); simpl in H129.
            specialize (H135 _ H35 H36 H37); simpl in H135.
            rewrite <- H129 in H135; inverts H135; auto.
          }
          subst v1.
          assert (v3 = v4).
          {
            assert ((2 < 18)%nat) by lia; assert ((2 <> 8)%nat) by lia; assert ((2 <> 9)%nat) by lia.
            specialize (H129 _ H35 H36 H37); simpl in H129.
            specialize (H135 _ H35 H36 H37); simpl in H135.
            rewrite <- H129 in H135; inverts H135; auto.
          }
          subst v3.
          assert (v5 = v6).
          {
            assert ((3 < 18)%nat) by lia; assert ((3 <> 8)%nat) by lia; assert ((3 <> 9)%nat) by lia.
            specialize (H129 _ H35 H36 H37); simpl in H129.
            specialize (H135 _ H35 H36 H37); simpl in H135.
            rewrite <- H129 in H135; inverts H135; auto.
          }
          subst v5.
          assert (v7 = v8).
          {
            assert ((4 < 18)%nat) by lia; assert ((4 <> 8)%nat) by lia; assert ((4 <> 9)%nat) by lia.
            specialize (H129 _ H35 H36 H37); simpl in H129.
            specialize (H135 _ H35 H36 H37); simpl in H135.
            rewrite <- H129 in H135; inverts H135; auto. 
          }
          subst v7.
          assert (v9 = v10).
          {
            assert ((5 < 18)%nat) by lia; assert ((5 <> 8)%nat) by lia; assert ((5 <> 9)%nat) by lia.
            specialize (H129 _ H35 H36 H37); simpl in H129.
            specialize (H135 _ H35 H36 H37); simpl in H135.
            rewrite <- H129 in H135; inverts H135; auto.
          }
          subst v9.
          assert (v11 = v12).
          {
            assert ((6 < 18)%nat) by lia; assert ((6 <> 8)%nat) by lia; assert ((6 <> 9)%nat) by lia.
            specialize (H129 _ H35 H36 H37); simpl in H129.
            specialize (H135 _ H35 H36 H37); simpl in H135.
            rewrite <- H129 in H135; inverts H135; auto.
          }
          subst v11.
          assert (v13 = v14).
          {
            assert ((7 < 18)%nat) by lia; assert ((7 <> 8)%nat) by lia; assert ((7 <> 9)%nat) by lia.
            specialize (H129 _ H35 H36 H37); simpl in H129.
            specialize (H135 _ H35 H36 H37); simpl in H135.
            rewrite <- H129 in H135; inverts H135; auto.
          }
          subst v13.
          assert (v19 = v20).
          {
            assert ((10 < 18)%nat) by lia; assert ((10 <> 8)%nat) by lia; assert ((10 <> 9)%nat) by lia.
            specialize (H129 _ H35 H36 H37); simpl in H129.
            specialize (H135 _ H35 H36 H37); simpl in H135.
            rewrite <- H129 in H135; inverts H135; auto.
          }
          subst v19.
          assert (v21 = v22).
          {
            assert ((11 < 18)%nat) by lia; assert ((11 <> 8)%nat) by lia; assert ((11 <> 9)%nat) by lia.
            specialize (H129 _ H35 H36 H37); simpl in H129.
            specialize (H135 _ H35 H36 H37); simpl in H135.
            rewrite <- H129 in H135; inverts H135; auto.
          }
          subst v21.
          assert (v23 = v24).
          {
            assert ((12 < 18)%nat) by lia; assert ((12 <> 8)%nat) by lia; assert ((12 <> 9)%nat) by lia.
            specialize (H129 _ H35 H36 H37); simpl in H129.
            specialize (H135 _ H35 H36 H37); simpl in H135.
            rewrite <- H129 in H135; inverts H135; auto.
          }
          subst v23.
          assert (v25 = v26).
          {
            assert ((13 < 18)%nat) by lia; assert ((13 <> 8)%nat) by lia; assert ((13 <> 9)%nat) by lia.
            specialize (H129 _ H35 H36 H37); simpl in H129.
            specialize (H135 _ H35 H36 H37); simpl in H135.
            rewrite <- H129 in H135; inverts H135; auto.
          }
          subst v25.
          assert (v27 = v28).
          {
            assert ((14 < 18)%nat) by lia; assert ((14 <> 8)%nat) by lia; assert ((14 <> 9)%nat) by lia.
            specialize (H129 _ H35 H36 H37); simpl in H129.
            specialize (H135 _ H35 H36 H37); simpl in H135.
            rewrite <- H129 in H135; inverts H135; auto.
          }
          subst v27.
          assert (v29 = v30).
          {
            assert ((15 < 18)%nat) by lia; assert ((15 <> 8)%nat) by lia; assert ((15 <> 9)%nat) by lia.
            specialize (H129 _ H35 H36 H37); simpl in H129.
            specialize (H135 _ H35 H36 H37); simpl in H135.
            rewrite <- H129 in H135; inverts H135; auto.
          }
          subst v29.
          assert (v31 = v32).
          {
            assert ((16 < 18)%nat) by lia; assert ((16 <> 8)%nat) by lia; assert ((16 <> 9)%nat) by lia.
            specialize (H129 _ H35 H36 H37); simpl in H129.
            specialize (H135 _ H35 H36 H37); simpl in H135.
            rewrite <- H129 in H135; inverts H135; auto.
          }
          subst v31.
          assert (v33 = v34).
          {
            assert ((17 < 18)%nat) by lia; assert ((17 <> 8)%nat) by lia; assert ((17 <> 9)%nat) by lia.
            specialize (H129 _ H35 H36 H37); simpl in H129.
            specialize (H135 _ H35 H36 H37); simpl in H135.
            rewrite <- H129 in H135; inverts H135; auto.
          }
          subst v33.
          auto.
  Optimize Proof.
  Optimize Heap.
        }
        subst v'48; clear H135 H132 H133 H134.

        (* kportNode_P compose *)
        hoare name lift (kportNode_P kportpl1') (Astruct' (ndstkportpb, Int.zero)) (kportNode_P kportpl2') pre. 
        eapply backward_rule1.
        {
          intros.
          eapply kportNode_P_compose in H84.
          { apply H84. }
          { auto. }
          { pauto. }
          { eauto. }
        }

        assert ((ifun_spec.update_nth vallist ndstpptrn
        (set_dportl_n_times otherpl (length dstkportpl1)
           dstpptrnl dstportupdl) ndstportupd) =
           (set_dportl_n_times otherpl (S (length dstkportpl1)) dstpptrnl dstportupdl)).
        { apply set_dportl_S_n_times; auto. }

        assert ((ifun_spec.update_nth (list vallist) ndstpptrn
                (set_dportmsgll_n_times othermsgll 
                  (length dstkportpl1) dstpptrnl 
                  (msg :: nil)) (msg :: nil)) =
                (set_dportmsgll_n_times othermsgll
                (S (length (dstkportpl1))) dstpptrnl (msg :: nil))).
        { apply set_dportmsgll_S_n_times; auto. }

        rewrite Hpin in *.
        assert ((set
                (set_dportls_n_times dportls2 (length dstkportpl1) dstportpl
                  dstportupdhl) ndstportp
                (∘ (Int.unsigned x7), x13, ∘ (Int.unsigned ndstportid),
                DestinationP x24, x14, Z.to_nat (Int.unsigned pin),
                Z.to_nat (Int.unsigned tm), SamplePort (Some msg))) =
                set_dportls_n_times dportls2 (S (length dstkportpl1)) dstportpl
                  dstportupdhl).
        { eapply set_dportls_S_n_times; eauto. }

        (* If (error ′ !=ₑ ′ OS_NO_ERR) {error ′ =ₑ ′ OS_ERR_DSTPORT_FULL} *)
        destruct H94 as [? | [? ?]]; subst vn.
        (* vn = Vnull *)
        {
          destruct dstkportpl2; simpl (length _) in *; cbn [Channel_dstkport_get].
          2:{ hoare normal pre; pure intro. inverts H131. }
          pure intro.
          hoare forward.
          { pure intro. exfalso; clear - H94; pauto. }
          destruct H94.
          { exfalso; sep split in s0. clear - H94; simpljoin1; pauto. }
          instantiate (4:=Vnull).
          instantiate (2:=S (length dstkportpl1)).
          eapply astar_mono.
          {
            instantiate (3:=Aemp); intros; left; sep split; auto.
            clear; induction dstkportpl1; simpl; eauto.
          }
          { eauto. }
          sep lifts (7::5:: 9::nil)%nat in s0.
          eapply add_aemp_isr_is_prop in s0.
          sep pauto.
          assert (length (dstkportpl1 ++ (ndstkportpb, Int.zero) :: nil) = S (length dstkportpl1)).
          { clear; induction dstkportpl1; simpl; eauto. }
          unfold addrval in H130; unfold addrval; rewrite H130.
          rewrite Nat.sub_diag.
          sep autocancel.
          {
            rewrite H114, H115; sep cancel kportNode_P.
            unfold vallist in s0, H84, H124.
            rewrite H84, H124 in s0; sep cancel OtherPortPtrList.
            assert (S (length dstkportpl1) = S ((length dstkportpl1) + 0%nat)).
            { simpl; auto. }
            unfold addrval; unfold addrval in H131; rewrite H131.
            eapply Channel_dstkport_get_compose.
            1,2: auto.
            instantiate (1:=(Vint32 i2 :: Vint32 i1
                  :: x3 :: x5 :: Vint32 i0 :: Vint32 i :: Vnull :: nil)).
            1,2: simpl; pauto.
            cbn [Channel_dstkport_get]; sep pauto.
          }
          { rewrite <- H128; auto. }
          { rewrite <- H84; rewrite <- H124; rewrite <- H128; auto. }
          { rewrite <- H128; auto. }
          { rewrite <- H128; auto. }
          { rewrite <- H128; auto. }
        }
        destruct dstkportpl2; simpl (length _) in *; cbn [Channel_dstkport_get].
        { hoare normal pre; pure intro. inverts H94. }
        pure intro.
        hoare forward.
        { pure intro. exfalso; clear - H131; pauto. }
        destruct H131.
        { exfalso; sep split in s0. clear - H131; simpljoin1; pauto. }
        instantiate (4:=(Vptr a)).
        instantiate (2:=S (length (dstkportpl1))).
        instantiate (2:=a).
        eapply astar_mono.
        {
          instantiate (1:=Aemp); intros; right; sep split; auto.
          clear; induction dstkportpl1; simpl; intros; eauto.
        }
        { eauto. }
        sep lifts (9::7::11::nil)%nat in s0.
        eapply add_aemp_isr_is_prop in s0.
        sep pauto.
        assert ((length (dstkportpl1 ++
         (ndstkportpb, Int.zero) :: a :: dstkportpl2) -
        S (length dstkportpl1))%nat = S (length dstkportpl2)).
        { clear; induction dstkportpl1; simpl; intros; eauto. }
        unfold addrval in H141; unfold addrval; rewrite H141.
        sep autocancel.
        {
          rewrite H114, H115; sep cancel kportNode_P.
          unfold vallist in s0, H84, H124.
          rewrite H84, H124 in s0; sep cancel OtherPortPtrList.
          assert ((length (dstkportpl1 ++ (ndstkportpb, Int.zero) :: a :: dstkportpl2)) = 
                  S ((length dstkportpl1) + S (length dstkportpl2))).
          { clear; induction dstkportpl1; simpl; intros; eauto. }
          unfold addrval; unfold addrval in H143; rewrite H143.
          eapply Channel_dstkport_get_compose.
          1,2: auto.
          instantiate (1:=(Vint32 i2 :: Vint32 i1
                :: x3 :: x5 :: Vint32 i0 :: Vint32 i :: Vptr a :: nil)).
          1,2: simpl; pauto.
          cbn [Channel_dstkport_get]; sep pauto.
          instantiate (1:=(Vint32 i7
          :: Vint32 i6
             :: x23 :: x25 :: Vint32 i4 :: Vint32 i3 :: x29 :: nil)).
          1,2: pauto.
        }
        { rewrite <- H128; auto. }
        { rewrite <- H84; rewrite <- H124; rewrite <- H128; auto. }
        { rewrite <- H128; auto. }
        { rewrite <- H128; auto. }
        { rewrite <- H128; auto. }
      }
      
      (* dstkportp is Vnull *)
      naive pure intro.
      rename v'19 into dstkportv;
      rename v'23 into dstkportp.
      eapply aconj_aisfalse_rule.
      {
        intros.
        sep destruct H82.
        apply disj_split in H82.
        instantiate (1:=val_inj (notint (val_inj (val_eq dstkportv Vnull)))).
        destruct H82; sep normal in H82; sep split in H82.
        symbolic execution.
        symbolic execution.
        destruct dstkportp; pauto.
        unfold val_eq; destruct dstkportp; pauto.
      }
      naive pure intro.
      eapply backward_rule1.
      intros s Hs; eapply disj_split in Hs; apply Hs.
      eapply disj_rule.
      2:{
        naive pure intro; exfalso. 
        subst dstkportv; clear - H92; pauto.
        destruct H92; unfold val_eq, notint, val_inj in *;
        destruct dstkportp; pauto.
        inverts H.
      }

      hoare normal pre; pure intro.
      clear H92.
      rewrite Nat.sub_diag.
      cbn [samplepost_sendmemcpy_aux_Outcore].
      cbn [spec_code_cons].
      hoare abscsq; [apply noabs_oslinv | auto .. ].
      {
        eapply absinfer_seq_end.
        3:{ intros ? Hs; apply Hs. }
        all: can_change_aop_solver'.
      }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
        {CSLSEMREL (semaphore ′)};ₛ *)

      hoare forward.
      { pauto. }
      { pauto. }
      { pauto. }
      {
        naive pure intro.
        cbn [Semrelease].
        (* rewrite H82. *)
        eapply cslsemrel_rule.
        { can_change_aop_solver'. }
        {
          rewrite Z2Nat.id by apply Int.unsigned_range.
          apply Int.unsigned_range_2.
        }
        {
          intros.
          rewrite Hsem.
          symbolic execution.
          pauto.
        }
        {
          unfold p_local, CurLINV, LINV, OSLInv.
          intros.
          sep normal in H83; sep destruct H83; sep split in H83.
          sep auto.
  Optimize Proof.
  Optimize Heap.
          splits; eauto.
          all: destruct H84 as [? [? [? [? [? ?]]]]]; auto.
        }
      }

      eapply disj_rule; naive pure intro.
      2:{
        exfalso; clear - H82 H65; pauto.
        rewrite H65 in H82.
        destruct H82; unfold notint, val_inj in H; pauto.
        inverts H.
      }

      (* EXIT_CRITICAL;ₛ *)
      hoare forward prim.
      {
        sep cancel EvtInv.
        sep cancel CoreCommuInv.
        sep cancel p_local.
        sep cancel Aier.
        sep cancel tcbdllflag.
        
        (* cancel TmrInv *)
        unfold TmrInv, HeapInv'.
        sep normal; sep eexists; sep autocancel.
        eapply AOScoreheapl_merge with (m:= S (length msg)); pauto.
        { simpl; lia. }
        { simpl; lia. }
        sep autocancel.
        sep split; eauto.

        (* cancel PartitionInv *)
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep pauto.
        10: eapply H87.
        9: eapply H2.
        8: unfold RLH_PortPtrINecb; split; eauto.
        7: eapply H4.
        6: eapply H5.
        5: eapply H88.
        4: apply H7.
        3: apply H89.
        2: eapply H90.
        sep autocancel.
        (* cancel AOSDomainPortPtrList *)
        unfold AOSDomainPortPtrList, dmportp_sll.
        sep normal; sep autocancel.
        (* cancel AOSKernelPortIDTbl *)
        unfold AOSKernelPortIDTbl.
        sep normal; sep autocancel.
        sep split; eauto.
        (* cancel AOSChannelIDTbl *)
        unfold AOSChannelIDTbl.
        sep normal; sep pauto.
        eapply ChannelNode_compose; eauto.
        { rewrite H57; eauto. }
        { rewrite H58; eauto. }
        { unfold OS_Channel_V_dstPortsHead; simpl; eauto. }
        { unfold OS_Channel_V_dstPortsNum; simpl; eauto. }
        { pauto. }
        unfold nat_of_Z; rewrite H69.
        sep autocancel.
        eapply H83.
      }
      eauto.
      good_frm_sovler.
      hoare forward.
    }
    hoare forward.
    naive pure intro.

    (* dstkport is null *)
    destruct H60 as [? | [? ?]]; subst dstkport.
    2:{
      exfalso; clear - H68; pauto.
      unfold val_inj, val_eq, notint in H68;
      destruct x0;destruct H68; pauto.
      inverts H.
    }
    destruct dstkportpl.
    2:{
      simpl (length _).
      cbn [Channel_dstkport_get].
      naive pure intro.
      inverts H71.
    }
    simpl (length _).
    cbn [samplepost_sendmemcpy_aux_Outcore].
    cbn [spec_code_cons].
    hoare abscsq; [apply noabs_oslinv | auto .. ].
    {
      eapply absinfer_seq_end.
      3:{ intros ? Hs; apply Hs. }
      all: can_change_aop_solver'.
    }

    hoare forward.
    { pauto. }
    { pauto. }
    { pauto. }
    {
      naive pure intro.
      cbn [Semrelease].
      eapply cslsemrel_rule.
      { can_change_aop_solver'. }
      {
        rewrite Z2Nat.id by apply Int.unsigned_range.
        apply Int.unsigned_range_2.
      }
      {
        intros.
        rewrite Hsem.
        symbolic execution.
        pauto.
      }
      {
        unfold p_local, CurLINV, LINV, OSLInv.
        intros.
        sep normal in H70; sep destruct H70; sep split in H70.
        sep auto.
        splits; eauto.
        all: destruct H71 as [? [? [? [? [? ?]]]]]; auto.
      }
    }

    eapply disj_rule; naive pure intro.
    2:{
      exfalso; clear - H60 H65; pauto.
      rewrite H65 in H60.
      destruct H60; unfold notint, val_inj in H; pauto.
      inverts H.
    }

    (* EXIT_CRITICAL;ₛ *)
    hoare forward prim.
    {
      sep cancel EvtInv.
      sep cancel CoreCommuInv.
      sep cancel p_local.
      sep cancel Aier.
      sep cancel tcbdllflag.
      
      (* cancel TmrInv *)
      unfold TmrInv, HeapInv'.
      sep normal; sep eexists; sep autocancel.

      (* cancel PartitionInv *)
      sep name lift PartitionInv; apply fold_PartitionInv_frm.
      sep cancel PartitionInv_part2.
      unfold PartitionInv_part1.
      sep normal; sep eexists; sep pauto.
      10: eapply H1.
      9: eapply H2.
      8: unfold RLH_PortPtrINecb; split; eauto.
      7: eapply H4.
      6: eapply H5.
      5: eapply H6.
      4: apply H7.
      3: apply H8.
      2: eapply H9.
      sep autocancel.
      (* cancel AOSDomainPortPtrList *)
      unfold AOSDomainPortPtrList, dmportp_sll.
      sep normal; sep autocancel.
      (* cancel AOSKernelPortIDTbl *)
      unfold AOSKernelPortIDTbl.
      sep normal; sep autocancel.
      sep split; eauto.
      (* cancel AOSChannelIDTbl *)
      unfold AOSChannelIDTbl.
      sep normal; sep pauto.
      eapply ChannelNode_compose; eauto.
      { rewrite H57; eauto. }
      { rewrite H58; eauto. }
      { unfold OS_Channel_V_dstPortsHead; simpl; eauto. }
      { unfold OS_Channel_V_dstPortsNum; simpl; eauto. }
      { pauto. }
      unfold nat_of_Z; simpl in H69; rewrite H69.
      sep autocancel.
      eapply H70.
    }
    eauto.
    good_frm_sovler.
    hoare forward.
  }
  {
    unfold Channel in H46, H66; rewrite H46 in H66; inverts H66.
    unfold Channel_type_P in H65; simpljoin1.
    unfold OS_Channel_V_semaphore in H29; simpl in H29; inverts H29.
    unfold samplepost_sendmemcpy_aux.

    (* assert ($ Z.of_nat (Z.to_nat (Int.unsigned ($ Z.of_nat sem))) = ($ Z.of_nat sem)) as Hsem.
    {
      rewrite Z2Nat.id by apply Int.unsigned_range.
      apply Int.repr_unsigned.
    } *)
    (* semaphore ′ =ₑ channel ′ .. semaphore;ₛ *)
    hoare forward.
    { pauto. }

    (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
    {CSLSEMACC (semaphore ′, resource_get_res ′);ₛ
    If (resource_get_res ′ ==ₑ 〈 char_t 〉 ′ 0)
    {EXIT_CRITICAL;ₛ
    RETURN 〈 char_t 〉 ′ OS_CHANNEL_ERR_BEING_USED}};ₛ *)
    hoare forward.
    {
      naive pure intro; simpljoin1.
      instantiate (1:=Afalse).
      exfalso; clear - H29; pauto.
    }
    hoare forward.
    naive pure intro.
    clear H29.

    (* dstKPort ′ =ₑ channel ′ .. dstPortsHead;ₛ *)
    hoare forward.
    { pauto. }
    rename v'26 into dstkport.

    destruct H48.
    2:{
      unfold R_KernelPortIDTbl_ChannelIDTbl_OutcoreC in H29; simpljoin1.
      unfold OS_Channel_V_semaphore in H29; simpl in H29; inverts H29.
      rewrite Int.eq_true in H48; lia.
    }
    unfold R_KernelPortIDTbl_ChannelIDTbl_IncoreC in H29; simpljoin1.
    clear H29. destruct H48.
    2:{
      exfalso.
      unfold R_KernelPortIDTbl_ChannelIDTbl_dst in H29; simpljoin1.
      clear - H10 H29.
      unfold port_id in H29, H10;
      rewrite H10 in H29; inverts H29.
    }
    unfold R_KernelPortIDTbl_ChannelIDTbl_scr in H29; simpljoin1.
    unfold port_id in H10; rewrite H10 in H29; inverts H29.
    unfold OS_Channel_V_srcPort in H48; simpl in H48; inverts H48.
    
    destruct H66; simpljoin1.
    2:{
      exfalso.
      unfold Channel_srckport_Queue in H48; simpljoin1.
      destruct H48; simpljoin1;
      unfold OS_Channel_V_srcPort in H48; simpl in H48; inverts H48.
      unfold addrval, port_id in H25, H68; rewrite H25 in H68; inverts H68.
      unfold addrval, port_id in H10, H70; rewrite H10 in H70; inverts H70.
    }
    unfold Channel_srckport_Sample in H48; simpljoin1.
    unfold OS_Channel_V_srcPortsNum in H67; simpl in H67; inverts H67.
    destruct H48; simpljoin1.
    { unfold OS_Channel_V_srcPortsNum in H66; simpl in H66; inverts H66. }
    unfold OS_Channel_V_srcPort in H48; simpl in H48; inverts H48.
    unfold addrval, port_id in H25, H67; rewrite H25 in H67; inverts H67.
    rename x3 into pptr. clear H66.
    unfold addrval, port_id in H10, H68; rewrite H10 in H68; inverts H68.
    
    unfold nat_of_Z in *.
    assert (dpnum = ($ (Z.of_nat (length dstkportpl)))).
    {
      clear - H53 H69.
      rewrite <- H69.
      rewrite Z2Nat.id by (apply Int.unsigned_range).
      rewrite Int.repr_unsigned.
      reflexivity.
    }
    assert ((Int.unsigned dpnum) = Z.of_nat (length dstkportpl)).
    {
      clear - H69.
      rewrite <- H69.
      rewrite Z2Nat.id by (apply Int.unsigned_range).
      reflexivity.
    }
    rewrite H69 in *.
    rewrite <- H48 at 1; rewrite H66 at 1; rewrite Nat2Z.id at 1.

    (* If (dstKPort ′ !=ₑ 〈 OS_K_Port ∗ 〉 NULL)
    {WHILE (dstKPort ′ !=ₑ 〈 OS_K_Port ∗ 〉 NULL)
    {error ′ =ᶠ OSSampleSendToDomain (·dstKPort ′ .. dmport,
      msg_ptr ′, port_ptr ′ .. msgInTick·);ₛ
    dstKPort ′ =ₑ 〈 OS_K_Port ∗ 〉 dstKPort ′ .. OSEventPtr;ₛ
    If (error ′ !=ₑ ′ OS_NO_ERR){error ′ =ₑ ′ OS_ERR_DSTPORT_FULL}};ₛ *)
    hoare forward.
    clear - H60; destruct H60 as [? | [? ?]]; subst; pauto.
    pauto.
    pauto.
    {
      instantiate (1:=Afalse).
      hoare normal pre; pure intro.
      destruct H60 as [?|[dkpptr ?]]; subst.
      exfalso; clear - H67; mauto.
      clear H68 H70 H67.
      unfold TmrInv, HeapInv'.
      pure intro.
      hoare name lift oscoreheapid pre.
      hoare name lift oschannel pre.
      hoare name lift oskport pre.
      hoare name lift osdomainport pre.
      rename v'19 into cHeapl.
      assert (
        ~ ( exists mlen msg,
          Get_heapl_addrval cHeapl msgptr (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\
          (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z ) \/
        ( exists mlen msg,
              Get_heapl_addrval cHeapl msgptr (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\
              (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z )
      ) as [ | ] by tauto.
      {
        destruct (dstkportpl).
        {
          assert (length (@nil addrval) = 0%nat) by auto.
          rewrite H70.
          cbn [Channel_dstkport_get].
          pure intro; tryfalse.
        }
        assert ((length (a :: l)) = S (length l)) by auto.
        rewrite H70 at 1.
        hoare name lift Aop pre.
        hoare abscsq; [apply noabs_oslinv | auto .. ].
        eapply samplepost_sendmemcpy_aux_Incore_abt; eauto.
        can_change_aop_solver'.
        apply absabort_rule.
      }
      simpljoin1.
      rename x into mlen. rename x0 into msg.
      assert (In_heapl_addrval cHeapl msgptr (Z.to_nat (Int.unsigned mlen + 1))).
      {
        destruct H68 as [? [? [? [? ?]]]].
        unfold In_heapl_addrval.
        exists x x0; split; auto.
      }

      (* split AOScoreheapl *)
      hoare name lift AOScoreheapl pre.
      eapply backward_rule1.
      eapply port_split_coreheapl; eauto.
      naive pure intro.
      rename v'19 into cheapl1. rename v'23 into cheapl2.
      rename v'24 into msgn. rename v'25 into msg1. rename v'26 into msg2.
      destruct msg1 as [ | len msg1 ].
      {
        simpl in H73.
        exfalso; clear - H73.
        simpljoin1.
        assert (0%nat = Z.to_nat 0) by auto.
        rewrite H in H2.
        assert (Int.unsigned mlen + 1 > 0).
        { pose proof unsigned_ge0 mlen; lia. }
        eapply Z2Nat.inj in H2; lia.
      }
      simpljoin1. simpl in H76; rewrite <- H76 in *.
      assert (len = Vint32 mlen /\ msg = msg1).
      { eapply nodup_cheapl_get_msg; eauto. }
      simpljoin1; rename msg1 into msg.

      hoare name lift AOSTime pre.
      hoare name lift dstKPort pre.
      hoare name lift Channel_dstkport_get pre.
      hoare name lift osdomainport pre.
      hoare name lift ostmid pre.
      hoare name lift dmportp_sllseg pre.
      rename v'9 into tm.
      rename x5 into pin.
      
      eapply backward_rule1.
      eapply dmportp_sllseg_Forall_struct_type_vallist_match'.
      pure intro.

      assert (
        exists dstportpl dstpptrnl dstportupdl dstportupdhl,
          length dstportpl = length dstkportpl /\
          length dstpptrnl = length dstkportpl /\
          length dstportupdl = length dstkportpl /\
          length dstportupdhl = length dstkportpl /\
          forall n, (n < length dstkportpl)%nat ->
            exists dstkportp dstportp dstpptrn dstpid dstkpst
                dstpd dstpst dstpin dstpout dstpm,
            exists dstpcn dstportupd dstport dstportupdh nextdst,
              nth_error dstkportpl n = Some dstkportp /\
              nth_error dstportpl n = Some dstportp /\
              nth_error dstportupdl n = Some dstportupd /\
              nth_error dstportupdhl n = Some dstportupdh /\
              nth_error dstpptrnl n = Some dstpptrn /\
              nth_error dpptrl dstpptrn = Some dstportp /\
              nth_error (dportl1 ++ dport :: dportl2) dstpptrn = Some dstport /\
              get kportls dstkportp =
                Some (dstpid, Some dstportp, Some (chanpb, Int.zero), dstpcn, dstkpst) /\
              get dportls1 dstportp = 
                Some (dstpcn, dstpd, dstpid,
                  DestinationP nextdst, dstpst, dstpin, dstpout, SamplePort dstpm) /\
              struct_type_vallist_match' OS_Port_Seg_dls dstportupd /\
              OS_Port_V_msgInTick dstportupd = Some (Vint32 pin) /\
              OS_Port_V_msgOutTick dstportupd = Some (Vint32 tm) /\
              (forall (m:nat), (m < 18)%nat -> (m <> 8)%nat -> (m <> 9)%nat -> 
                nth_val m dstportupd = nth_val m dstport) /\
              dstportupdh = (dstpcn, dstpd, dstpid,
                DestinationP nextdst, dstpst, Z.to_nat (Int.unsigned pin),
                Z.to_nat (Int.unsigned tm), SamplePort (Some msg))
      ).
      { eapply dstkportpl_get_and_upd_list_Sample_Incore; eauto. }
      destruct H75 as [dstportpl [dstpptrnl [dstportupdl [dstportupdhl [? [? [? [? ?]]]]]]]].

      eapply seq_rule.
      {
        hoare name lift AOSCorePortPtrList pre.
        hoare name lift osdomainportid pre.
        hoare name lift dmportp_sllseg pre.
        hoare name lift Channel_dstkport_get pre.
        hoare name lift dstKPort pre.
        hoare name lift Aop pre.
        hoare remember (1::2::3::4::5::6::nil)%nat pre.
        eapply backward_rule1.
        {
          instantiate (1:=
            EX n ndkpv ndkpptr ndportl ndportmsgll ndportls1 ndportls,
            ( [| ndkpv = Vnull |] ** [| n = length dstkportpl |] \\//
              [| ndkpv = Vptr ndkpptr |] **
              [| nth_error dstkportpl n = Some ndkpptr |]  ) **
            <||
            spec_code_cons (samplepost_sendmemcpy_aux_Incore (length dstkportpl - n)%nat
            (Vptr pptr :: Vptr msgptr :: V$ Z.of_nat (length dstkportpl) :: Vnull :: vsdstcl)) (END Some (V$ OS_NO_ERR)) ||>  **
            LV dstKPort @ OS_K_Port ∗ |-> ndkpv **
            Channel_dstkport_get (Vptr dkpptr) Vnull (length dstkportpl) dstkportpl **
            dmportp_sllseg dportlptr Vnull ndportl ndportmsgll OS_Port_V_nextPort **
            Hdomainportl ndportls **
            AOSCorePortPtrList v'40 v'41 ndportls1 **
            [| ndportl = set_dportl_n_times (dportl1 ++ dport :: dportl2) n dstpptrnl dstportupdl |] **
            [| ndportmsgll = set_dportmsgll_n_times (dportmsgll1 ++ (srcmsg :: nil) :: dportmsgll2) n dstpptrnl (msg :: nil) |] **
            [| ndportls1 = set_dportls_n_times dportls1 n dstportpl dstportupdhl |] **
            [| join ndportls1 dportls2 ndportls |] **
            [| RL_PortPtrList dportlptr ndportl dpptrl |] **
            [| RL_PortAttr dpptrl ndportl |] **
            [| RLH_Domainportl dportlptr ndportl ndportmsgll ndportls1 |] **
            [| RLH_Channel otherppl
                (chanpl1 ++ Vptr (chanpb, Int.zero) :: chanpl2)
                (chanl1 ++
                (Vint32 chanid
                  :: V$ 1
                    :: V$ Z.of_nat (length dstkportpl)
                        :: V$ DEFAULT_CHANNLE_SEMAPHROE
                          :: Vptr dkpptr
                              :: x15
                                :: Vptr (kportpb, Int.zero)
                                    :: x17 :: nil) :: chanl2)
                (chandstkportll1 ++ dstkportpl :: chandstkportll2)
                chanls kportls ndportls1 dportls2 |] **
            [| R_KernelPortIDTbl_ChannelIDTbl
                (kportpl1 ++ Vptr (kportpb, Int.zero) :: kportpl2)
                (kportl1 ++
                (Vint32 portid
                  :: Vint32 chanid
                    :: Vptr pptr
                        :: Vptr (chanpb, Int.zero)
                          :: V$ DNUM :: Vint32 x1 :: x8 :: nil)
                :: kportl2)
                (chanpl1 ++ Vptr (chanpb, Int.zero) :: chanpl2)
                (chanl1 ++
                (Vint32 chanid
                  :: V$ 1
                    :: V$ Z.of_nat (length dstkportpl)
                        :: V$ DEFAULT_CHANNLE_SEMAPHROE
                          :: Vptr dkpptr
                              :: x15
                                :: Vptr (kportpb, Int.zero)
                                    :: x17 :: nil) :: chanl2)
                (chandstkportll1 ++ dstkportpl :: chandstkportll2)
                kportls ndportls1 dportls2 |] **
            [| Channel_dstkport_Sample_IncoreC otherppl
                (chanpb, Int.zero) dstkportpl kportls ndportls1 |] **
            [| R_Kernelport_DomainPort
                (kportpl1 ++ Vptr (kportpb, Int.zero) :: kportpl2)
                (kportl1 ++
                (Vint32 portid
                  :: Vint32 chanid
                    :: Vptr pptr
                        :: Vptr (chanpb, Int.zero)
                          :: V$ DNUM :: Vint32 x1 :: x8 :: nil)
                :: kportl2) ndportl dpptrl |] **
            H81
          ).
          {
            intros.
            exists 0%nat (Vptr dkpptr) dkpptr (dportl1 ++ dport :: dportl2)
                  (dportmsgll1 ++ (srcmsg :: nil) :: dportmsgll2) dportls1; exists dportls.
            sep normal.
            apply disj_split; right.
            destruct dstkportpl; cbn [length ] in *.
            unfold Channel_dstkport_get in H82; sep split in H82; tryfalse.
            cbn [Channel_dstkport_get] in *.
            sep normal in H82; sep destruct H82; sep split in H82. inverts H85.
            sep normal; sep eexists; sep split; eauto.
          }
        }
        subst H81.
        eapply while_rule.
        {
          intros.
          sep destruct H81.
          apply disj_split in H81.
          destruct H81.
          symbolic execution.
          symbolic execution.
          destruct x3; pauto.
          destruct x3; pauto.
        }
        hoare normal pre; hoare_ex_intro.
        rename v'9 into n. rename v'19 into ndkpv.
        rename v'24 into ndportl. rename v'25 into ndportmsgll.
        eapply aconj_aistrue_rule.
        {
          intros.
          sep destruct H81.
          apply disj_split in H81.
          instantiate (1:=val_inj (notint (val_inj (val_eq ndkpv Vnull)))).
          destruct H81; sep normal in H81; sep split in H81.
          symbolic execution.
          symbolic execution.
          destruct v'23; pauto.
          unfold val_eq; destruct v'23; pauto.
        }
        hoare normal pre; pure_intro.
        eapply backward_rule1.
        intros s Hs; eapply disj_split in Hs; apply Hs.
        eapply disj_rule.
        { hoare normal pre; pure intro; exfalso. clear - H92; pauto. }
        naive pure intro; subst ndkpv.
        rename v'23 into ndstkportp.
        rename v'27 into ndportls.
        clear H94 H92 H93.
        apply nth_error_split in H82 as (dstkportpl1 & dstkportpl2 & ? & ?).
        subst dstkportpl.
        hoare name lift Channel_dstkport_get pre.
        eapply backward_rule1.
        eapply Channel_dstkport_get_app_frm; eauto.
        hoare normal pre; pure intro. rename v'19 into vn.
        assert ((length (dstkportpl1 ++ ndstkportp :: dstkportpl2) - length dstkportpl1)%nat = S (length dstkportpl2)).
        { clear; induction dstkportpl1; simpl; try lia. }
        assert ((S (length dstkportpl2) - 1)%nat = length dstkportpl2) by (clear; mauto).
        rewrite H97, H98.
        hoare name lift msg_ptr pre.
        assert ((length dstkportpl1 < length (dstkportpl1 ++ ndstkportp :: dstkportpl2))%nat).
        { clear; induction dstkportpl1; simpl; try lia. }
        pose proof H80 _ H99.
        simpljoin1.
        rewrite nth_error_middle in H100; inverts H100; rename x into ndstkportp.
        rename x5 into ndstportp.

        (* find ndstkport in kportNode_P *)
        hoare name lift kportNode_P pre.
        pose proof RLH_Kernelport_abs_getsome' _ _ _ _ _ _ _ _ _ H107 H5.
        simpljoin1.
        eapply backward_rule1.
        eapply kportNode_P_getsome_frm; eauto.
        hoare normal pre; pure intro.
        rename v'9 into ndstkportpb.
        rename v'19 into kportpl1'. rename v'23 into kportpl2'.
        rename v'24 into kportl1'. rename v'25 into kportl2'.
        rename x21 into ndstport. rename x7 into ndstpptrn.
        unfold KernelportNode_P in H114.
        simpljoin1.
        unfold Kernelport_dmport_P in H125.
        unfold OS_K_Port_V_dmport in H125; simpl in H125; inverts H125.
        unfold Kernelport_channel_P in H126.
        unfold OS_K_Port_V_channel in H126; simpl in H126; inverts H126.
        unfold Kernelport_nat_P in H114; simpljoin1.
        unfold OS_K_Port_V_portID in H114; simpl in H114;
          inverts H114; rename x into ndstportid.
        unfold OS_K_Port_V_status in H128; simpl in H128; inverts H128.
        unfold OS_K_Port_V_coreNum in H126; simpl in H126; inverts H126.
        
        (* find dstport in dmportp_sllseg *)
        hoare name lift dmportp_sllseg pre.
        assert (exists n ndstport ndstmsgll,
          nth_error (dportl1 ++ dport :: dportl2) n = Some ndstport /\
          nth_error (dportmsgll1 ++ (srcmsg :: nil) :: dportmsgll2) n = Some ndstmsgll /\
          nth_error dpptrl n = Some ndstportp /\
          DomainportNode_P ndstport (∘ (Int.unsigned x5), x12,
            ∘ (Int.unsigned ndstportid), DestinationP x23, x13,
            x14, x16, SamplePort x18) ndstmsgll).
        { eapply RLH_Domainportl_abs_getsome with (dportls:=dportls1); eauto. }
        simpljoin1.

        assert (x = ndstpptrn) by (eapply dpptrl_not_same_elements; eauto).
        subst x. clear H126.
        rewrite H114 in H106; inverts H106.
        hoare name lift dmportp_sllseg pre.

        pose proof H64 _ H99; simpljoin1.
        assert (nth_error (dstkportpl1 ++ (ndstkportpb, Int.zero) :: dstkportpl2) (length dstkportpl1) = Some (ndstkportpb, Int.zero)).
        { clear; induction dstkportpl1; simpl; intros; eauto. }
        unfold addrval in H106, H130; rewrite H106 in H130; inverts H130.
        unfold port_coreNum in H107; rewrite H107 in H126; inverts H126.
        rename x into ndstportp.
        assert (get dportls ndstportp = Some
            (∘ (Int.unsigned x5), x12,
            ∘ (Int.unsigned ndstportid), DestinationP x23, x13,
            x14, x16, SamplePort x18)).
        { eapply join_get_l; eauto. }
        unfold port_coreNum, port_id in H128, H126;
        rewrite H128 in H126; inverts H126.
        
        assert (exists ndstpin' ndstpout' ndstpm',
        get (set_dportls_n_times dportls1 (length dstkportpl1) dstportpl
        dstportupdhl) ndstportp = Some (∘ (Int.unsigned x5), x12, ∘ (Int.unsigned ndstportid),
          DestinationP x23, x13, ndstpin', ndstpout', SamplePort ndstpm')).
        {
          eapply set_dportls_n_times_upd_same_elements.
          10: eauto.
          9: eauto.
          all: eauto.
          lia.
  Optimize Proof.
  Optimize Heap.
          unfold port_intick, port_outick; rewrite H79; auto.
          rewrite H75; auto.
          rewrite H77; clear - H80; intros.
          specialize (H80 _ H); simpljoin1.
          do 14 eexists; splits; eauto.
        }
        simpljoin1.

        rename x20 into ndstportupd.
        assert (exists ndstport',
        nth_error (set_dportl_n_times (dportl1 ++ dport :: dportl2)
        (length dstkportpl1) dstpptrnl dstportupdl) ndstpptrn = Some ndstport' /\
        forall m : nat,
          (m < 18)%nat -> m <> 8%nat -> m <> 9%nat ->
          nth_val m ndstportupd = nth_val m ndstport').
        {
          eapply set_dportl_n_times_upd_same_elements.
          7: eauto. all: eauto.
          lia. 
          unfold vallist; rewrite H78; auto.
          rewrite H77; clear - H80; intros.
          specialize (H80 _ H); simpljoin1.
          do 3 eexists; splits; eauto.
        }
        simpljoin1.

        assert (get (set_dportls_n_times dportls1 (length dstkportpl1)
        dstportpl dstportupdhl) pptr = Some
          (Z.to_nat DNUM, Z.to_nat (Int.unsigned x2),
          Z.to_nat (Int.unsigned portid), SourceP,
          Z.to_nat (Int.unsigned x4), Z.to_nat (Int.unsigned pin),
          Z.to_nat (Int.unsigned x6), SamplePort (Some srcmsg))).
        {
          eapply set_dportls_n_times_get_pptr_SourceP; eauto.
          rewrite H75; lia.
          unfold port_intick, port_outick; rewrite H79; auto.
          rewrite H75; intros.
          specialize (H80 _ H132); simpljoin1.
          do 18 eexists; splits; eauto.
        }

        assert ((Int.repr (Z.of_nat (Z.to_nat (Int.unsigned pin))) = pin)%nat) as Hpin.
        {
          rewrite Z2Nat.id by apply Int.unsigned_range.
          apply Int.repr_unsigned.
        }

        assert (∘ (Int.unsigned x5) = Z.to_nat DNUM) as Heq.
        {
          unfold DomainportNode_P in H127; simpljoin1.
          unfold Domainport_nat_P in H127; simpljoin1.
          unfold nat_of_Z in *.
          rewrite H135; auto.
        }

        (* find pptr memory *)
        eapply backward_rule1.
        {
          eapply set_dportl_msgll_get_srcptr; eauto; try lia.
          2: unfold vallist; rewrite H78; auto.
          assert ( forall n1 n2 x,
              nth_error dpptrl n1 = Some x ->
              nth_error dpptrl n2 = Some x -> n1 = n2).
          { intros ? ? ?; eapply dpptrl_not_same_elements; eauto. }
          rewrite H77; clear - H80 H3 H4 H133.
          intros; specialize (H80 _ H); simpljoin1.
          do 4 eexists; splits; eauto.
          {
            unfold OS_Port_V_nextPort. specialize (H14 11%nat).
            assert (nth_val 11 x10 = nth_val 11 x11) by (apply H14; lia).
            auto.
          }
          all: unfold OS_Port_V_direction.
          2: assert (nth_val 4 x10 = nth_val 4 x11) by (apply H14; lia).
          2: rewrite H15; clear H15.
          all: assert (exists n dstport msgl,
          nth_error (dportl1 ++ dport :: dportl2) n = Some dstport /\
          nth_error (dportmsgll1 ++ (srcmsg :: nil) :: dportmsgll2) n = Some msgl /\ 
          nth_error dpptrl n = Some x0 /\
          DomainportNode_P dstport (x9, x4, x2, DestinationP x13, x5, x6, x7, SamplePort x8) msgl)
            by (eapply RLH_Domainportl_abs_getsome; eauto).
          all: simpljoin1.
          all: unfold DomainportNode_P in H18; destruct H18 as [? [? ?]].
          all: unfold Domainport_direction_P in H19.
          all: specialize (H133 _ _ _ H7 H17); subst x12.
          all: rewrite H8 in H15; inverts H15.
          all: unfold OS_Port_V_direction in H19; destruct H19.
          all: rewrite H15.
          all: clear; pauto.
        }
        naive pure intro.
        rename v'9 into dportl1'.
        rename v'19 into dportl2'.
        rename v'23 into dportmsgll1'.
        rename v'24 into dportmsgll2'.
        clear H135.

        eapply seq_rule.
        {
          eapply calle_rule_lvar'.
          { pauto. }
          {
            (* RV *)
            intros. 
            eapply rvl_elim.
            {
              eapply dstKPort_dmport_rv.
              2: sep autocancel; apply H135.
              pauto.
            }
            eapply rvl_elim; [symbolic execution| ].
            eapply rvl_elim;[ | apply rvl_nil].
            instantiate (1:=(Vint32 (Int.repr (Z.of_nat (Z.to_nat (Int.unsigned pin)))))).
            eapply astar_mono in H135.
            2:{
              instantiate (1:=dmportp_sll dportlptr (dportl1' ++ dport :: dportl2')
              (dportmsgll1' ++ (srcmsg :: nil) :: dportmsgll2') OS_Port_V_nextPort ).
              unfold dmportp_sll. sep pauto.
            }
            2:{ intros s0 Hs. apply Hs. }
            eapply dmportp_sllseg_app'_frm in H135; eauto.
            2:{
              rewrite <- H133; rewrite <- H134.
              eapply H14.
            }
            2: rewrite H136; auto.
            cbn [dmportp_sllseg] in H135.
            sep normal in H135; sep destruct H135; sep split in H135.
            inverts H138; rename x22 into pptr.
            eapply port_msgInTick_rv; eauto.
            2: sep autocancel; apply H135.
            unfold DomainportNode_P.
            splits; simpl.
            {
              do 5 eexists.
              splits; eauto.
              splits; eauto.
            }
            instantiate (1:=SourceP); simpl; eauto.
            instantiate (3:=(SamplePort (Some srcmsg))).
            simpl; eexists; splits; eauto.
          }
          {
            (* ==>pre *)
            unfold getasrt, OSSampleSendToDomainPre, OSSampleSendToDomainPre'. 
            intros.
            sep name lift Aisr Ais aemp_isr_is in H135.
            eapply elim_aemp_isr_is_prop in H135.
            sep normal; sep eexists.
            sep autocancel.
            sep split.
            3: auto.
            3: eapply H129.
            20: rewrite H50; instantiate (1:=(dstkportpl1 ++ (ndstkportpb, Int.zero) :: dstkportpl2)); auto.
            20: eauto.
            19: simpl; eauto.
            16,17,18: auto.
            15: eapply H109.
            13: auto.
            13: rewrite Hpin; auto.
            12: eapply H131.
            8: eapply H84.
            6: eapply H89.
            6: eapply H88.
            4: rewrite Hpin; eapply H132.
            4: eauto.
            3: eapply H25.
            4: eapply H107.
            sep name lift Aop in H135.
            eapply disj_split.
            right.
            sep normal; sep eexists.
            sep pauto.
            all: try rewrite H136; try rewrite H137.
            eapply H91.
            auto.
            auto.
            auto.
            eapply H130.
            auto.
  Optimize Proof.
  Optimize Heap.
            eapply H126.
            eapply H46.
            2: rewrite Hpin; eauto.
            2: eauto.
            eauto.
          }
          { good_frm_sovler. }
          {
            unfold retpost.
            unfold getasrt, OSSampleSendToDomainPost, OSSampleSendToDomainPost'.
            intros.
            sep normal in H135; sep destruct H135; sep split in H135.
            rewrite H150; auto.
          }
          { pauto. }
          {
            unfold getasrt, OSSampleSendToDomainPost, OSSampleSendToDomainPost'.
            sep pauto.
            sep cancel p_local.
            sep pauto.
          }
          {
            unfold getasrt, OSSampleSendToDomainPre, OSSampleSendToDomainPre'.
            sep pauto.
            sep cancel p_local.
            sep pauto.
          }
        }
        unfold getasrt, OSSampleSendToDomainPost, OSSampleSendToDomainPost'.
        hoare normal pre; pure intro.
        inversion H148; clear H148.
        subst v'19 v'23 v'27 v'28 v'30 v'35 v'34 v'36 v'37 v'42 v'43 v'44 
        v'45 v'56 v'57 v'47 v'26 v'24 v'53 v'54 v'55 v'62 v'63 v'64 
        v'68 v'69 v'70 v'71 v'72 v'73 v'65 v'66 v'67 v'83 v'84.
        simpl in H138; inversion H138; clear H138.
        subst v'46 v'25 v'29. 
        hoare normal pre; pure intro.
        
        (* disj *)
        eapply backward_rule1.
        intros. eapply disj_split in H135; eapply H135.
        eapply disj_rule.
        {
          hoare normal pre; pure intro.
          inverts H135.
        }
        naive pure intro.
        subst v'49 v'50 v'51 v'52 v'58 v'59.
        clear H135.
        unfold port_coreNum, port_id in H149, H126;
        rewrite H149 in H126; inverts H126.
        rewrite H152 in H130; inverts H130.
        
        unfold OS_K_Port_V_OSEventPtr in H83; simpl in H83; inverts H83.
        (* dstKPort ′ =ₑ 〈 OS_K_Port ∗ 〉 dstKPort ′ .. OSEventPtr *)
        eapply seq_rule.
        {
          eapply assign_rule_lvar.
          { split; [ | sep pauto]. sep pauto. }
          {
            intros.
            eapply symbolic_lemmas.cast_rv_tptr with (v:= vn) (t1:= Void).
            2: pauto.
            eapply symbolic_lemmas.struct_member_rv_flag; eauto.
            { sep cancel dstKPort; sep autocancel; apply H83. }
            { pauto. }
            { pauto. }
            { pauto. }
            { pauto. }
          }
          { eapply eq_vptr; eauto. }
          { intros; sep eexists; sep cancel p_local; sep pauto. }
        }

        assert (v'48 = ndstportupd). 
        {
          clear - H139 H140 H141 H142 Hpin H109 H110 H111 H131.
          rewrite Hpin in *; clear Hpin.
          rename v'48 into ndstport.
          destruct ndstport; destruct ndstportupd; simpl in *; tryfalse.
          do 18 (destruct H109 as [? H109]; destruct H139 as [? H139]; destruct ndstport; destruct ndstportupd; simpl in *; tryfalse).
          unfold OS_Port_V_msgInTick in H110; simpl in H110; inverts H110.
          unfold OS_Port_V_msgInTick in H140; simpl in H140; inverts H140.
          unfold OS_Port_V_msgOutTick in H111; simpl in H111; inverts H111.
          unfold OS_Port_V_msgOutTick in H141; simpl in H141; inverts H141.

          assert (v = v0).
          {
            assert ((0 < 18)%nat) by lia; assert ((0 <> 8)%nat) by lia; assert ((0 <> 9)%nat) by lia.
            specialize (H131 _ H35 H36 H37); simpl in H131.
            specialize (H142 _ H35 H36 H37); simpl in H142.
            rewrite <- H131 in H142; inverts H142; auto.
          }
          subst v.
          assert (v1 = v2).
          {
            assert ((1 < 18)%nat) by lia; assert ((1 <> 8)%nat) by lia; assert ((1 <> 9)%nat) by lia.
            specialize (H131 _ H35 H36 H37); simpl in H131.
            specialize (H142 _ H35 H36 H37); simpl in H142.
            rewrite <- H131 in H142; inverts H142; auto.
          }
          subst v1.
          assert (v3 = v4).
          {
            assert ((2 < 18)%nat) by lia; assert ((2 <> 8)%nat) by lia; assert ((2 <> 9)%nat) by lia.
            specialize (H131 _ H35 H36 H37); simpl in H131.
            specialize (H142 _ H35 H36 H37); simpl in H142.
            rewrite <- H131 in H142; inverts H142; auto.
          }
          subst v3.
          assert (v5 = v6).
          {
            assert ((3 < 18)%nat) by lia; assert ((3 <> 8)%nat) by lia; assert ((3 <> 9)%nat) by lia.
            specialize (H131 _ H35 H36 H37); simpl in H131.
            specialize (H142 _ H35 H36 H37); simpl in H142.
            rewrite <- H131 in H142; inverts H142; auto.
          }
          subst v5.
          assert (v7 = v8).
          {
            assert ((4 < 18)%nat) by lia; assert ((4 <> 8)%nat) by lia; assert ((4 <> 9)%nat) by lia.
            specialize (H131 _ H35 H36 H37); simpl in H131.
            specialize (H142 _ H35 H36 H37); simpl in H142.
            rewrite <- H131 in H142; inverts H142; auto. 
          }
          subst v7.
          assert (v9 = v10).
          {
            assert ((5 < 18)%nat) by lia; assert ((5 <> 8)%nat) by lia; assert ((5 <> 9)%nat) by lia.
            specialize (H131 _ H35 H36 H37); simpl in H131.
            specialize (H142 _ H35 H36 H37); simpl in H142.
            rewrite <- H131 in H142; inverts H142; auto.
          }
          subst v9.
          assert (v11 = v12).
          {
            assert ((6 < 18)%nat) by lia; assert ((6 <> 8)%nat) by lia; assert ((6 <> 9)%nat) by lia.
            specialize (H131 _ H35 H36 H37); simpl in H131.
            specialize (H142 _ H35 H36 H37); simpl in H142.
            rewrite <- H131 in H142; inverts H142; auto.
          }
          subst v11.
          assert (v13 = v14).
          {
            assert ((7 < 18)%nat) by lia; assert ((7 <> 8)%nat) by lia; assert ((7 <> 9)%nat) by lia.
            specialize (H131 _ H35 H36 H37); simpl in H131.
            specialize (H142 _ H35 H36 H37); simpl in H142.
            rewrite <- H131 in H142; inverts H142; auto.
          }
          subst v13.
          assert (v19 = v20).
          {
            assert ((10 < 18)%nat) by lia; assert ((10 <> 8)%nat) by lia; assert ((10 <> 9)%nat) by lia.
            specialize (H131 _ H35 H36 H37); simpl in H131.
            specialize (H142 _ H35 H36 H37); simpl in H142.
            rewrite <- H131 in H142; inverts H142; auto.
          }
          subst v19.
          assert (v21 = v22).
          {
            assert ((11 < 18)%nat) by lia; assert ((11 <> 8)%nat) by lia; assert ((11 <> 9)%nat) by lia.
            specialize (H131 _ H35 H36 H37); simpl in H131.
            specialize (H142 _ H35 H36 H37); simpl in H142.
            rewrite <- H131 in H142; inverts H142; auto.
          }
          subst v21.
          assert (v23 = v24).
          {
            assert ((12 < 18)%nat) by lia; assert ((12 <> 8)%nat) by lia; assert ((12 <> 9)%nat) by lia.
            specialize (H131 _ H35 H36 H37); simpl in H131.
            specialize (H142 _ H35 H36 H37); simpl in H142.
            rewrite <- H131 in H142; inverts H142; auto.
          }
          subst v23.
          assert (v25 = v26).
          {
            assert ((13 < 18)%nat) by lia; assert ((13 <> 8)%nat) by lia; assert ((13 <> 9)%nat) by lia.
            specialize (H131 _ H35 H36 H37); simpl in H131.
            specialize (H142 _ H35 H36 H37); simpl in H142.
            rewrite <- H131 in H142; inverts H142; auto.
          }
          subst v25.
          assert (v27 = v28).
          {
            assert ((14 < 18)%nat) by lia; assert ((14 <> 8)%nat) by lia; assert ((14 <> 9)%nat) by lia.
            specialize (H131 _ H35 H36 H37); simpl in H131.
            specialize (H142 _ H35 H36 H37); simpl in H142.
            rewrite <- H131 in H142; inverts H142; auto.
          }
          subst v27.
          assert (v29 = v30).
          {
            assert ((15 < 18)%nat) by lia; assert ((15 <> 8)%nat) by lia; assert ((15 <> 9)%nat) by lia.
            specialize (H131 _ H35 H36 H37); simpl in H131.
            specialize (H142 _ H35 H36 H37); simpl in H142.
            rewrite <- H131 in H142; inverts H142; auto.
          }
          subst v29.
          assert (v31 = v32).
          {
            assert ((16 < 18)%nat) by lia; assert ((16 <> 8)%nat) by lia; assert ((16 <> 9)%nat) by lia.
            specialize (H131 _ H35 H36 H37); simpl in H131.
            specialize (H142 _ H35 H36 H37); simpl in H142.
            rewrite <- H131 in H142; inverts H142; auto.
          }
          subst v31.
          assert (v33 = v34).
          {
            assert ((17 < 18)%nat) by lia; assert ((17 <> 8)%nat) by lia; assert ((17 <> 9)%nat) by lia.
            specialize (H131 _ H35 H36 H37); simpl in H131.
            specialize (H142 _ H35 H36 H37); simpl in H142.
            rewrite <- H131 in H142; inverts H142; auto.
          }
          subst v33.
          auto.
  Optimize Proof.
  Optimize Heap.
        }
        subst v'48; clear H139 H140 H141 H142.

        (* kportNode_P compose *)
        hoare name lift (kportNode_P kportpl1') (Astruct' (ndstkportpb, Int.zero)) (kportNode_P kportpl2') pre. 
        eapply backward_rule1.
        {
          intros.
          eapply kportNode_P_compose in H83.
          { apply H83. }
          { auto. }
          { pauto. }
          { eauto. }
        }

        assert ((ifun_spec.update_nth vallist ndstpptrn
        (set_dportl_n_times (dportl1 ++ dport :: dportl2) (length dstkportpl1)
           dstpptrnl dstportupdl) ndstportupd) =
           (set_dportl_n_times (dportl1 ++ dport :: dportl2) (S (length dstkportpl1)) dstpptrnl dstportupdl)).
        { apply set_dportl_S_n_times; auto. }

        assert ((ifun_spec.update_nth (list vallist) ndstpptrn
                (set_dportmsgll_n_times (dportmsgll1 ++ (srcmsg :: nil) :: dportmsgll2) 
                  (length dstkportpl1) dstpptrnl 
                  (msg :: nil)) (msg :: nil)) =
                (set_dportmsgll_n_times (dportmsgll1 ++ (srcmsg :: nil) :: dportmsgll2)
                (S (length (dstkportpl1))) dstpptrnl (msg :: nil))).
        { apply set_dportmsgll_S_n_times; auto. }

        rewrite Hpin in *.
        assert ((set
                (set_dportls_n_times dportls1 (length dstkportpl1) dstportpl
                  dstportupdhl) ndstportp
                  (∘ (Int.unsigned x5), x12,
                  ∘ (Int.unsigned ndstportid), DestinationP x23, x13,
                  Z.to_nat (Int.unsigned pin),
                  Z.to_nat (Int.unsigned tm), SamplePort (Some msg))) =
                set_dportls_n_times dportls1 (S (length dstkportpl1)) dstportpl
                  dstportupdhl).
        { eapply set_dportls_S_n_times; eauto. }

        (* If (error ′ !=ₑ ′ OS_NO_ERR) {error ′ =ₑ ′ OS_ERR_DSTPORT_FULL} *)
        destruct H96 as [? | [? ?]]; subst vn.
        (* vn = Vnull *)
        {
          destruct dstkportpl2; simpl (length _) in *; cbn [Channel_dstkport_get].
          2:{ hoare normal pre; pure intro. inverts H138. }
          pure intro.
          hoare forward.
          { pure intro. exfalso; clear - H96; pauto. }
          destruct H96.
          { exfalso; sep split in s0. clear - H96; simpljoin1; pauto. }
          instantiate (5:=Vnull).
          instantiate (1:=S (length dstkportpl1)).
          eapply astar_mono.
          {
            instantiate (3:=Aemp); intros; left; sep split; auto.
            clear; induction dstkportpl1; simpl; eauto.
          }
          { eauto. }
          sep lifts (7::5:: 9::nil)%nat in s0.
          eapply add_aemp_isr_is_prop in s0.
          sep pauto.
          assert (length (dstkportpl1 ++ (ndstkportpb, Int.zero) :: nil) = S (length dstkportpl1)).
          { clear; induction dstkportpl1; simpl; eauto. }
          unfold addrval in H135; unfold addrval; rewrite H135.
          rewrite Nat.sub_diag.
          sep autocancel.
          {
            rewrite H116, H117; sep cancel kportNode_P.
            unfold vallist, language.msg in s0, H83, H126.
            rewrite H83, H126 in s0; sep cancel dmportp_sllseg.
            assert (S (length dstkportpl1) = S ((length dstkportpl1) + 0%nat)).
            { simpl; auto. }
            unfold addrval; unfold addrval in H138; rewrite H138.
            (* sep lifts (3::2::nil)%nat in s0. *)
            eapply astar_mono.
            instantiate(1:=PV get_off_addr (ndstkportpb, Int.zero) ($ 12) @ 
            (Void) ∗ |-> Vnull ** Channel_dstkport_get (Vptr dkpptr)
              (Vptr (ndstkportpb, Int.zero)) (length dstkportpl1)
              dstkportpl1).
            intros.
            eapply Channel_dstkport_get_compose.
            1,2: auto.
            instantiate (1:=(Vint32 i2 :: Vint32 i1
                  :: x0 :: x3 :: Vint32 i0 :: Vint32 i :: Vnull :: nil)).
            1,2: simpl; pauto.
            cbn [Channel_dstkport_get]; sep pauto.
            eauto.
            sep pauto.
            rewrite Nat.add_0_r.
            unfold addrval in H130.
            rewrite <- H130.
            sep pauto.
          }
          { rewrite <- H83; auto. }
          { rewrite <- H130; auto. }
          { rewrite <- H130; auto. }
          { rewrite <- H130; auto. }
          { rewrite <- H83. rewrite <- H126. rewrite <- H130; auto. }
          { rewrite <- H83; auto. }
          { rewrite <- H83; auto. }
          { rewrite <- H130; auto. }
        }
        destruct dstkportpl2; simpl (length _) in *; cbn [Channel_dstkport_get].
        { hoare normal pre; pure intro. inverts H96. }
        pure intro.
        hoare forward.
        { pure intro. exfalso; clear - H138; pauto. }
        destruct H138.
        { exfalso; sep split in s0. clear - H138; simpljoin1; pauto. }
        instantiate (5:=(Vptr a)).
        instantiate (3:=S (length (dstkportpl1))).
        instantiate (3:=a).
        eapply astar_mono.
        {
          instantiate (1:=Aemp); intros; right; sep split; auto.
          clear; induction dstkportpl1; simpl; intros; eauto.
        }
        { eauto. }
        sep lifts (9::7::11::nil)%nat in s0.
        eapply add_aemp_isr_is_prop in s0.
        sep pauto.
        assert ((length (dstkportpl1 ++
         (ndstkportpb, Int.zero) :: a :: dstkportpl2) -
        S (length dstkportpl1))%nat = S (length dstkportpl2)).
        { clear; induction dstkportpl1; simpl; intros; eauto. }
        unfold addrval in H148; unfold addrval; rewrite H148.
        sep autocancel.
        {
          rewrite H116, H117; sep cancel kportNode_P.
          unfold vallist, language.msg in s0, H83, H126.
          rewrite H83, H126 in s0; sep cancel dmportp_sllseg.
          assert ((length (dstkportpl1 ++ (ndstkportpb, Int.zero) :: a :: dstkportpl2)) = 
                  S ((length dstkportpl1) + S (length dstkportpl2))).
          { clear; induction dstkportpl1; simpl; intros; eauto. }
          unfold addrval; unfold addrval in H150; rewrite H150.
          eapply astar_mono.
          instantiate(1:=PV get_off_addr a ($ 12) @ (Void) ∗ |-> v'19 **
          Channel_dstkport_get v'19 Vnull (length dstkportpl2)
            dstkportpl2 **
            PV get_off_addr (ndstkportpb, Int.zero) ($ 12) @ 
            (Void) ∗ |-> Vptr a **
            Channel_dstkport_get (Vptr dkpptr)
              (Vptr (ndstkportpb, Int.zero)) (length dstkportpl1)
              dstkportpl1).
          intros.
          eapply Channel_dstkport_get_compose.
          1,2: auto.
          instantiate (1:=(Vint32 i2
            :: Vint32 i1
                :: x0 :: x3 :: Vint32 i0 :: Vint32 i :: Vptr a :: nil)).
          1,2: simpl; pauto.
          cbn [Channel_dstkport_get]; sep pauto.
          instantiate (1:=(Vint32 i7
          :: Vint32 i6
             :: x22 :: x24 :: Vint32 i4 :: Vint32 i3 :: x28 :: nil)).
          1,2: pauto.
          eauto.
          unfold addrval in H130.
          rewrite <- H130.
          sep pauto.
        }
        { rewrite <- H83; auto. }
        { rewrite <- H130; auto. }
        { rewrite <- H130; auto. }
        { rewrite <- H130; auto. }
        { rewrite <- H83. rewrite <- H126. rewrite <- H130; auto. }
        { rewrite <- H83; auto. }
        { rewrite <- H83; auto. }
        { rewrite <- H130; auto. }
      }
      
      (* dstkportp is Vnull *)
      naive pure intro.
      rename v'19 into dstkportv;
      rename v'23 into dstkportp.
      eapply aconj_aisfalse_rule.
      {
        intros.
        sep destruct H81.
        apply disj_split in H81.
        instantiate (1:=val_inj (notint (val_inj (val_eq dstkportv Vnull)))).
        destruct H81; sep normal in H81; sep split in H81.
        symbolic execution.
        symbolic execution.
        destruct dstkportp; pauto.
        unfold val_eq; destruct dstkportp; pauto.
      }
      naive pure intro.
      eapply backward_rule1.
      intros s Hs; eapply disj_split in Hs; apply Hs.
      eapply disj_rule.
      2:{
        naive pure intro; exfalso. 
        subst dstkportv; clear - H94; pauto.
        destruct H94; unfold val_eq, notint, val_inj in *;
        destruct dstkportp; pauto.
        inverts H.
      }

      hoare normal pre; pure intro.
      clear H94.
      rewrite Nat.sub_diag.
      cbn [samplepost_sendmemcpy_aux_Incore].
      cbn [spec_code_cons].
      hoare abscsq; [apply noabs_oslinv | auto .. ].
      {
        eapply absinfer_seq_end.
        3:{ intros ? Hs; apply Hs. }
        all: can_change_aop_solver'.
      }

      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
        {CSLSEMREL (semaphore ′)};ₛ *)

      hoare forward.
      {
        instantiate (1:=Afalse).
        naive pure intro; simpljoin1.
        exfalso; clear - H81; pauto.
      }

      hoare forward.
      naive pure intro.
      clear H81.

      (* EXIT_CRITICAL;ₛ *)
      hoare forward prim.
      {
        sep cancel EvtInv.
        sep cancel CoreCommuInv.
        sep cancel p_local.
        sep cancel Aier.
        sep cancel tcbdllflag.
        
        (* cancel TmrInv *)
        unfold TmrInv, HeapInv'.
        sep normal; sep eexists; sep autocancel.
        eapply AOScoreheapl_merge with (m:= S (length msg)); pauto.
        { simpl; lia. }
        { simpl; lia. }
        sep autocancel.
        sep split; eauto.

        (* cancel PartitionInv *)
        sep name lift PartitionInv; apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep pauto.
        10: eapply H86.
        9: eapply H88.
        8: unfold RLH_PortPtrINecb; split.
        9: apply H11.
        8: eapply H87.
        7: eapply H89.
        6: eapply H5.
        5: eapply H90.
        4: apply H93.
        3: apply H91.
        2: eapply H9.
        sep autocancel.
        (* cancel AOSDomainPortPtrList *)
        unfold AOSDomainPortPtrList, dmportp_sll.
        sep normal; sep autocancel.
        (* cancel AOSKernelPortIDTbl *)
        unfold AOSKernelPortIDTbl.
        sep normal; sep autocancel.
        sep split; eauto.
        (* cancel AOSChannelIDTbl *)
        unfold AOSChannelIDTbl.
        sep normal; sep pauto.
        eapply ChannelNode_compose; eauto.
        { rewrite H57; eauto. }
        { rewrite H58; eauto. }
        { unfold OS_Channel_V_dstPortsHead; simpl; eauto. }
        { unfold OS_Channel_V_dstPortsNum; simpl; eauto. }
        { pauto. }
        unfold nat_of_Z; rewrite H69.
        sep autocancel.
        eapply H81.
      }
      eauto.
      good_frm_sovler.
      hoare forward.
    }
    hoare forward.
    naive pure intro.

    (* dstkport is null *)
    destruct H60 as [? | [? ?]]; subst dstkport.
    2:{
      exfalso; clear - H67; pauto.
      unfold val_inj, val_eq, notint in H67;
      destruct x; destruct H67; pauto.
      inverts H.
    }
    destruct dstkportpl.
    2:{
      simpl (length _).
      cbn [Channel_dstkport_get].
      naive pure intro.
      inverts H70.
    }
    simpl (length _).
    cbn [samplepost_sendmemcpy_aux_Outcore].
    cbn [spec_code_cons].
    hoare abscsq; [apply noabs_oslinv | auto .. ].
    {
      eapply absinfer_seq_end.
      3:{ intros ? Hs; apply Hs. }
      all: can_change_aop_solver'.
    }

    hoare forward.
    {
      instantiate (1:=Afalse).
      naive pure intro; simpljoin1.
      exfalso; clear - H60; pauto.
    }

    hoare forward; naive pure intro.

    (* EXIT_CRITICAL;ₛ *)
    hoare forward prim.
    {
      sep cancel EvtInv.
      sep cancel CoreCommuInv.
      sep cancel p_local.
      sep cancel Aier.
      sep cancel tcbdllflag.
      
      (* cancel TmrInv *)
      unfold TmrInv, HeapInv'.
      sep normal; sep eexists; sep autocancel.

      (* cancel PartitionInv *)
      sep name lift PartitionInv; apply fold_PartitionInv_frm.
      sep cancel PartitionInv_part2.
      unfold PartitionInv_part1.
      sep normal; sep eexists; sep pauto.
      10: eapply H1.
      9: eapply H2.
      8: unfold RLH_PortPtrINecb; split; eauto.
      7: eapply H4.
      6: eapply H5.
      5: eapply H6.
      4: apply H7.
      3: apply H8.
      2: eapply H9.
      sep autocancel.
      (* cancel AOSDomainPortPtrList *)
      unfold AOSDomainPortPtrList, dmportp_sll.
      sep normal; sep autocancel.
      (* cancel AOSKernelPortIDTbl *)
      unfold AOSKernelPortIDTbl.
      sep normal; sep autocancel.
      sep split; eauto.
      (* cancel AOSChannelIDTbl *)
      unfold AOSChannelIDTbl.
      sep normal; sep pauto.
      eapply ChannelNode_compose; eauto.
      { rewrite H57; eauto. }
      { rewrite H58; eauto. }
      { unfold OS_Channel_V_dstPortsHead; simpl; eauto. }
      { unfold OS_Channel_V_dstPortsNum; simpl; eauto. }
      { pauto. }
      unfold nat_of_Z; simpl in H69; rewrite H69.
      sep autocancel.
      eapply H68.
    }
    eauto.
    good_frm_sovler.
    hoare forward.
  }
  Unshelve.
  exact (Atrue).
  exact (msgptr).
  exact (Atrue).
  exact (Atrue).
  exact (msgptr).
  exact (Atrue).
Qed.
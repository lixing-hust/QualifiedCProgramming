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

Open Scope code_scope.

Open Scope int_scope.

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


Lemma PortAcceptProof :
  forall vl p r tid ,
    Some p = BuildPreA' os_api PortAccept portaccapi vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api PortAccept portaccapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api PortAccept = Some (t, d1, d2, s) /\
      {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |-tid {{p }} s {{ Afalse }}.
Proof.
  init_spec.

  hoare name lift Aop pre.
  destruct v'.
  apply absabort_rule.
  rename v into vsem.
  rename v'1 into ier.
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
    eapply absinfer_choice1; eauto.
    1,2: can_change_aop_solver'.
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
    eapply absinfer_choice1; eauto.
    1,2: can_change_aop_solver'.
    hoare abscsq; [apply noabs_oslinv | auto .. ].
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
    eapply absinfer_choice1; eauto.
    1,2: can_change_aop_solver'.
    hoare abscsq; [apply noabs_oslinv | auto .. ].
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
  rename v'20 into pptr.

  (* find port_ptr -> OSEventType *)
  pose proof Forall_forall (fun x : addrval => exists wt, get ecbls x = Some (absport, wt)) dpptrl.
  destruct H13.
  pose proof nth_error_in _ _ H15.
  pose proof H13 H12 pptr H21 as [wt ?].
  clear H13 H17 H21.

  (* find OSTBCur *)
  rename v'9 into tcbls.
  unfold RH_CurTCB in H0.
  destruct H0 as [? [? [? [? ?]]]].
  rename v'3 into tcbl1.
  rename v'4 into tcbcur.
  rename v'5 into tcbl2.
  
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
    eapply absinfer_choice1; eauto.
    1,2: can_change_aop_solver'.
    hoare abscsq; [apply noabs_oslinv | auto .. ].
    {
      eapply port_indomainport_cont; eauto.
      can_change_aop_solver'.
    }

    (* err_unmapped (|Vptr pptr :: nil|) *)
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

  hoare abscsq; [apply noabs_oslinv | | ].
  eapply absinfer_choice2; eauto.
  1,2: can_change_aop_solver'.
  fold (port_acc_without_chk ((Vptr pptr) :: msgptr :: vsem :: nil)).

  (* error ′ =ᶠ OSPortAcceptWithoutCheck (·port_ptr ′, msg_ptr ′·);ₛ *)
  eapply seq_rule.
  {
    eapply calle_rule_lvar'.
    { pauto. }
    {
      intros.
      eapply rvl_elim; [symbolic_execution| ].
      eapply rvl_elim; [symbolic_execution; pauto|eapply rvl_nil].
    }
    {
      unfold getasrt, OSPortAcceptWithoutCheckPre, OSPortAcceptWithoutCheckPre'.
      intros.
      sep normal; sep eexists; sep autocancel.
      sep pauto.
    }
    { go. }
    {
      unfold retpost, getasrt, OSPortAcceptWithoutCheckPost, OSPortAcceptWithoutCheckPost'.
      intros.
      sep normal in H; sep destruct H; sep split in H.
      do 4 (destruct H3; try subst v; auto).
    }
    {
      cbn. unfold isptr in H1.
      destruct H1; simpljoin1; subst; auto.
    }
    {
      unfold getasrt, OSPortAcceptWithoutCheckPost, OSPortAcceptWithoutCheckPost'.
      sep pauto; sep cancel p_local; sep pauto.
    }
    {
      unfold getasrt, OSPortAcceptWithoutCheckPre, OSPortAcceptWithoutCheckPre'.
      sep pauto; sep cancel p_local; sep pauto.
    }
  }

  unfold getasrt, OSPortAcceptWithoutCheckPost, OSPortAcceptWithoutCheckPost'.
  hoare normal pre; pure intro.
  inversion H. subst v'3 v'4. clear H.
  inversion H0. subst v'1 v'2 v'5. clear H0.

  destruct H2.
  {
    inverts H.
    hoare abscsq; [apply noabs_oslinv | | ].
    eapply absinfer_choice1; eauto.
    1,2: can_change_aop_solver'.
    hoare forward.
  }
  hoare abscsq; [apply noabs_oslinv | | ].
  eapply absinfer_choice2; eauto.
  1,2: can_change_aop_solver'.
  destruct H.
  {
    inverts H.
    hoare abscsq; [apply noabs_oslinv | | ].
    eapply absinfer_choice1; eauto.
    1,2: can_change_aop_solver'.
    hoare forward.
  }
  hoare abscsq; [apply noabs_oslinv | | ].
  eapply absinfer_choice2; eauto.
  1,2: can_change_aop_solver'.
  destruct H.
  {
    inverts H.
    hoare abscsq; [apply noabs_oslinv | | ].
    eapply absinfer_choice1; eauto.
    1,2: can_change_aop_solver'.
    hoare forward.
  }
  hoare abscsq; [apply noabs_oslinv | | ].
  eapply absinfer_choice2; eauto.
  1,2: can_change_aop_solver'.
  destruct H.
  {
    inverts H.
    hoare abscsq; [apply noabs_oslinv | | ].
    eapply absinfer_choice1; eauto.
    1,2: can_change_aop_solver'.
    hoare forward.
  }
  hoare abscsq; [apply noabs_oslinv | | ].
  eapply absinfer_choice2; eauto.
  1,2: can_change_aop_solver'.
  inverts H.
  hoare forward.
Qed.
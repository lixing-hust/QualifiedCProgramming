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
Require Import qportpostproof_aux.

Lemma Get_heapl_addrval_split_coreheapl:
  forall coreheapl l m vl1,
  Get_heapl_addrval coreheapl l m vl1 ->
  forall P,
  AOScoreheapl coreheapl ** P
  ==>
  EX l1 l2 n vl2,
  [| coreheapl = l1 ++ (l, n, vl1 ++ vl2) :: l2 |] **
  AOScoreheapl (l1 ++ (get_off_addr l (Int.repr (Z.of_nat m)), (n - m)%nat, vl2) :: l2) **
  Aarray l (Tarray Tint8 m) vl1 **
  [| array_type_vallist_match Tint8 vl1 /\ (n <= (Z.to_nat HEAP_MAX_LENGTH ))%nat /\ 
    (length vl1 + length vl2 = n)%nat /\ (length vl1 = m)%nat |] ** P.
Proof.
  intros.
  destruct H as [n [vl [? ?]]].
  apply in_split in H as [l1 [l2 ?]].
  destruct H1. subst.
  pose proof firstn_skipn m vl; subst.
  exists l1 l2 n (skipn m vl).
  rewrite <- H at 1.
  apply AOScoreheapl_app_frame in H0.
  cbn [AOScoreheapl] in *.
  sep normal in H0. 
  sep name lift Aarray in H0.
  lets Hlen: array_length_intro H0.
  lets Hs: Aarray_split_single m char_t H0; auto.
  sep split in H0. destruct H2.
  pose proof corecommu_rules.HEAP_MAX_LENGTH_range. lia.
  clear H0.
  sep split in Hs.
  destruct H0. rewrite <- H in H0.
  simpl typelen in Hs.
  simpl Z.of_nat in Hs.
  rewrite Int.mul_one in Hs.
  sep auto.
  apply AOScoreheapl_app. 
  cbn [AOScoreheapl].
  sep auto.
  split. 
  eapply array_type_vallist_match_app; eauto.
  lia.
  splits; auto.
  apply array_type_vallist_match_app in H0. tauto.
  rewrite <- app_length. now rewrite H.
  now apply firstn_length_le.
Qed.

Ltac partition_enter':= hoare forward prim; pure intro; hoare name lift PartitionInv pre;
                      eapply backward_rule1;[ apply unfold_PartitionInv_frm | unfold PartitionInv_part1;pure intro;rename_partitionvars].

Ltac partition_exit':= 
  hoare forward prim;   
  match goal with 
    | H: ?s |= ?p |- ?s |= _ => 
      sep name lift PartitionInv; apply fold_PartitionInv_frm;
      match p with 
      | context [ ([|OS_Port_V_mode ?dport = Some (Vint32 (ZToInt SAMPLE))|] **
      dmportp_sllseg_sampleport_msg ?v ?msgl \\// ?q)] => sep name lift ([|OS_Port_V_mode dport = Some (Vint32 (ZToInt SAMPLE))|] **
      dmportp_sllseg_sampleport_msg v msgl \\// q) in H end;
      sep name lift APortStruct in H;
      match p with 
      | context [ dmportp_sllseg ?v Vnull] => sep name lift (dmportp_sllseg v Vnull) in H end;
      match p with 
      | context [ dmportp_sllseg ?v (Vptr ?v')] => sep name lift (dmportp_sllseg v (Vptr v')) in H end;
      eapply dmportp_sllseg_compose in H;eauto;
      sep autocancel;unfold PartitionInv_part1,AOSDomainPortPtrList;
      sep normal;sep eexists;sep pauto
    | |- _ => try (sep name lift PartitionInv; apply fold_PartitionInv_frm; unfold PartitionInv_part1);sep pauto  end;
    match goal with 
    | |-  {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} => idtac 
    | |- RLH_PortPtrINecb _ _ _ _ =>  solve [eauto || unfold RLH_PortPtrINecb;splits;eauto] 
    | |- RH_CurTCB ?tid ?tcbls => solve [eauto || unfold RH_CurTCB;eauto]
    | |- GoodFrm (_ ** _ ) => go  (* 为了排除 GoodFrm ?frm 还没有填的情况 *)
    | |- _ => eauto 
  end.

Lemma QPortPostProof :
  forall vl p r tid ,
    Some p = BuildPreA' os_api QPortPost qportpostapi vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api QPortPost qportpostapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api QPortPost = Some (t, d1, d2, s) /\
      {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |-tid {{p }} s {{ Afalse }}.
Proof.
  init_spec.
  do 3 (destruct v';[hoare abs lift pre; apply absabort_rule | ]).
  rename v0 into vsem.
  rename v into channeldstnum. 
    (* resource_get_res ′ =ₑ ′ 0;ₛ
    semaphore ′ =ₑ ′ DEFAULT_CHANNLE_SEMAPHROE;ₛ
    channel ′ =ₑ 〈 OS_Channel ∗ 〉 NULL;ₛ
    kport ′ =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
    dstKPort ′ =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
    error ′ =ₑ 〈 char_t 〉 ′ OS_NO_ERR;ₛ *)
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
  partition_enter'.
  rename H12 into Hnodup_d_k.

  hoare forward; pauto.
  { 
    instantiate (1:= Afalse).
    naive pure intro.
    destruct portptr; simpl in H12; iauto.
    {
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        apply absinfer_seq. can_change_aop_solver'.
        2:{
          apply absinfer_assert_cont. can_change_aop_solver'.
          2:{
            intros s H100. apply H100.
          }
          can_change_aop_solver'.
          intros. unfold valid_port. auto.
        }
        can_change_aop_solver'.
      }
      partition_absrulestac absinfer_seq_end.
      can_change_aop_solver'. can_change_aop_solver'.
      partition_absrulestac absinfer_choice1.
      can_change_aop_solver'. can_change_aop_solver'.
      partition_absrulestac absinfer_trans.
      apply err_portnull_absinfer. can_change_aop_solver'.
      apply absinfer_eq.
      partition_exit'.
      hoare forward.
    }
    { destruct a. iauto. }
  }
  naive pure intro.
  apply disj_rule.
  {
    naive pure intro.
    apply pfalse_rule.
  }
  naive pure intro.
  destruct portptr; simpl in H12; auto. 
  destruct H12; discriminate.
  destruct H12; discriminate.
  destruct H12; discriminate.
  rename a into portptr. clear H12.
  partition_exit'.
  clear - H1.
  
  partition_enter'.
  rename H11 into Hnodup_d_k.

  (* ASSERT indomainport portptr abort;; *)
  hoare name lift osdomainportid pre.
  hoare abs lift pre.
  destruct (get dportls portptr) eqn: Hpptr.
  2:{
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply valid_port_none_abt.
      apply Hpptr. go.
    }
    apply absabort_rule.
  }
  destruct b as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].

  assert (p <> Z.to_nat DNUM \/ p = Z.to_nat DNUM) by tauto.
  destruct H11; [ | subst p].
  {
    partition_absrulestac valid_port_none_abt'. 
    apply absabort_rule.
  }

  (* find port_ptr -> coreNum *)
  assert (get dportls1 portptr = Some (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5)).
  { eapply pptr_in_dportls1; eauto. }
  unfold RLH_PortPtrINecb in H4; destruct H4.
  assert (exists n dport msgl,
    nth_error dportl n = Some dport /\ nth_error dportmsgll n = Some msgl /\
    nth_error dpptrl n = Some portptr /\ DomainportNode_P dport (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5) msgl).
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
  rename v'20 into portptr.

  (* find port_ptr -> OSEventType *)
  pose proof Forall_forall (fun x : addrval => exists wt, get ecbls x = Some (absport, wt)) dpptrl.
  destruct H13.
  pose proof nth_error_in _ _ H15.
  pose proof H13 H12 portptr H21 as [wt ?].
  clear H13 H17 H21.

  (* find OSTBCur *)
  rename v'9 into tcbls.
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
    instantiate(1:=Afalse).
    destruct (Int.eq (x >>ᵢ $ 3) ($ Z.of_nat p0)) eqn: Heq.
    {
      exfalso; clear - H13.
      unfold Int.notbool, bool_or in H13; simpl in H13.
      do 2 rewrite Int.eq_true in H13. simpl in H13.
      pauto.
    }
    hoare name lift osdomainportid pre.
    hoare abs lift pre.
    partition_absrulestac valid_port_cont.
    can_change_aop_solver'.
    can_change_aop_solver'.
    (* err_unmapped (|Vptr portptr :: nil|) *)
    partition_absrulestac absinfer_choice2.
    1,2: can_change_aop_solver'.
    partition_absrulestac absinfer_choice1.
    1,2: can_change_aop_solver'.
    hoare name lift abstcblsid pre.
    hoare name lift curtid pre.
    hoare name lift osdomainportid pre.
    hoare abs lift pre.
    partition_absrulestac err_unmapped_absinfer.
    1,2: can_change_aop_solver'.
    partition_exit'.
    hoare forward.
  }
  hoare forward.
  hoare normal pre; pure intro.
  partition_exit'.
  clear - H1.

  (* ENTER_CRITICAL;ₛ
  If (msg_ptr ′ ==ₑ NULL)
  {EXIT_CRITICAL;ₛ
  RETURN 〈 char_t 〉 ′ OS_ERR_POST_NULL_PTR};ₛ
  EXIT_CRITICAL;ₛ *)
  partition_enter'.
  rename H11 into Hnodup_d_k.

  (* ASSERT indomainport portptr abort;; *)
  hoare name lift osdomainportid pre.
  hoare abs lift pre.
  destruct (get dportls portptr) eqn: Hpptr.
  2:{
    partition_absrulestac valid_port_none_abt.
    apply absabort_rule.
  }
  destruct b as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
  assert (p <> Z.to_nat DNUM \/ p = Z.to_nat DNUM) by tauto.
  destruct H11; [ | subst p].
  {
    partition_absrulestac valid_port_none_abt'.
    apply absabort_rule.
  }
  hoare forward; pauto.
  {
    hoare normal pre; pure intro.
    partition_absrulestac valid_port_cont.
    partition_absrulestac absinfer_choice2.
    partition_absrulestac absinfer_choice2.
    partition_absrulestac absinfer_choice1.
    destruct H1 as [? | [? ?]]; subst.
    {
      partition_absrulestac err_msgnull_absinfer.
      instantiate(1:=Afalse).
      partition_exit'.
      hoare forward.
    }
    destruct x. simpl in H11. congruence.
  }
  hoare forward.
  hoare normal pre; pure intro.
  partition_exit'.
  clear - H1 H11.
  destruct H1 as [? | [? ?]]; subst.
  { simpl in H11; destruct H11; discriminate. }
  rename x into msgptr; clear H11.

  (* ENTER_CRITICAL;ₛ
  If (port_ptr ′ .. os_code_defs.direction !=ₑ ′ SOURCE
      ||ₑ port_ptr ′ .. mode !=ₑ ′ QUEUE)
  {EXIT_CRITICAL;ₛ
  RETURN 〈 char_t 〉 ′ OS_PORT_ERR_TYPE};ₛ
  EXIT_CRITICAL;ₛ *)
  partition_enter'.
  rename H10 into Hnodup_d_k.

  (* ASSERT indomainport portptr abort;; *)
  hoare name lift osdomainportid pre.
  hoare abs lift pre.
  destruct (get dportls portptr) eqn: Hpptr.
  2:{
    partition_absrulestac valid_port_none_abt.
    apply absabort_rule.
  }
  destruct b as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
  assert (p <> Z.to_nat DNUM \/ p = Z.to_nat DNUM) by tauto.
  destruct H10; [ | subst p].
  {
    partition_absrulestac valid_port_none_abt'.
    apply absabort_rule.
  }

  (* find port_ptr -> direction, mode *)
  assert (get dportls1 portptr = Some (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5)).
  { eapply pptr_in_dportls1; eauto. }
  unfold RLH_PortPtrINecb in H3; destruct H3.
  assert (exists n dport msgl,
    nth_error dportl n = Some dport /\ nth_error dportmsgll n = Some msgl /\
    nth_error dpptrl n = Some portptr /\ DomainportNode_P dport (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5) msgl).
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
  rename v'20 into portptr.

  (* If (port_ptr ′ .. os_code_defs.direction !=ₑ ′ SOURCE ||ₑ port_ptr ′ .. mode !=ₑ ′ QUEUE) *)
  eapply seq_rule.
  {
    eapply ift_rule''; [symbolic_exe_port|idtac].
    hoare normal pre; pure intro.
    destruct d; destruct p5.
    2:{ exfalso. clear - H12; destruct H12; unfold SOURCE, QUEUE;  mauto. }
    all: hoare name lift osdomainportid pre.
    all: hoare abscsq;[apply noabs_oslinv | | ].
    1,3,5: eapply valid_port_cont; eauto.
    1,2,3: can_change_aop_solver'.
    all: hoare abscsq;[apply noabs_oslinv | | ].
    1,3,5: eapply absinfer_choice2; eauto.
    1,2,3,4,5,6: can_change_aop_solver'.
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
    1,3,5: eapply err_porttype_queue_absinfer; eauto.
    1,2,3: can_change_aop_solver'.
    instantiate (1:=Afalse).
    all: partition_exit'.
    all: hoare forward.
  }
  hoare forward.
  hoare normal pre; pure intro.
  assert (Int.eq ($SOURCE) ($SOURCE) = true) as HSS by pauto.
  assert (Int.eq ($QUEUE) ($QUEUE) = true) as HQQ by pauto.
  assert (Int.eq ($SAMPLE) ($QUEUE) = false) as HSQ by pauto.
  assert (Int.eq ($DESTINATION) ($SOURCE) = false) as HDS by pauto.
  assert (Int.ltu (Int.zero) (Int.one)=true) as H01 by mauto.
  destruct d eqn: Hd; destruct p5 eqn: Hm.
  all: try rewrite HSS in *; try rewrite HQQ in *; try rewrite HSQ in *; try rewrite HDS in *.
  all: do 3(unfold Int.notbool in H12; simpl in H12; try rewrite eq_one_zero in H12; try rewrite Int.eq_true in H12;
    try rewrite Int_ltu_refl in H12; try rewrite H01 in H12).
  1,3,4: destruct H12; discriminate.
  subst d p5; clear H12 HSS HQQ HSQ HDS H01.
  assert (OSPortAttrTblMode portptr = (V$ QUEUE)).
  {
    eapply RL_PortAttr_mode_QUEUE ;eauto.
    rewrite nth_error_app2 by lia.
    rewrite Nat.sub_diag; simpl; auto.
  }
  assert (OSPortAttrTblDir portptr = (V$ SOURCE)).
  {
    eapply RL_PortAttr_dir_SOURCE ;eauto.
    rewrite nth_error_app2 by lia.
    rewrite Nat.sub_diag; simpl; auto.
  }
  (* EXIT_CRITICAL *)
  partition_exit'.
  clear - H12 H16.
  rename H12 into Hmode.
  rename H16 into Hdir.

  (* ENTER_CRITICAL;ₛ
  If (port_ptr ′ .. portID ≥ ′ PORT_NUMS)
  {EXIT_CRITICAL;ₛ
  RETURN 〈 char_t 〉 ′ OS_PORT_ID_INVALID};ₛ
  EXIT_CRITICAL;ₛ *)
  partition_enter'.
  rename H10 into Hnodup_d_k.

  (* ASSERT indomainport portptr abort;; *)
  hoare name lift osdomainportid pre.
  hoare abs lift pre.
  destruct (get dportls portptr) eqn: Hpptr.
  2:{ partition_absrulestac valid_port_none_abt. apply absabort_rule.  }
  destruct b as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
  assert (p <> Z.to_nat DNUM \/ p = Z.to_nat DNUM) by tauto.
  destruct H10; [ | subst p].
  {
    partition_absrulestac valid_port_none_abt'. apply absabort_rule.
  }

  (* find port_ptr -> direction, mode *)
  assert (get dportls1 portptr = Some (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5)).
  { eapply pptr_in_dportls1; eauto. }
  unfold RLH_PortPtrINecb in H3; destruct H3.
  assert (exists n dport msgl,
    nth_error dportl n = Some dport /\ nth_error dportmsgll n = Some msgl /\
    nth_error dpptrl n = Some portptr /\ DomainportNode_P dport (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5) msgl).
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
  rename v'20 into portptr.

  eapply seq_rule.
  {
    eapply ift_rule''; [symbolic_exe_port|idtac].
    hoare normal pre; pure intro.
    instantiate (1:= Afalse).
    exfalso.
    clear - H12 H15.
    unfold DomainportNode_P in H15; destruct H15 as [? [? ?]].
    unfold Domainport_nat_P in H; simpljoin1.
    clear - H7 H12. mauto.
  }
  hoare forward.
  hoare normal pre; pure intro.
  partition_exit'.
  clear - Hdir Hmode.

  (* ENTER_CRITICAL;ₛ *)
  partition_enter'.
  rename H10 into Hnodup_d_k.

  (* ASSERT indomainport portptr abort;; *)
  hoare name lift osdomainportid pre.
  hoare abs lift pre.
  destruct (get dportls portptr) eqn: Hpptr.
  2:{ partition_absrulestac valid_port_none_abt. apply absabort_rule.  }
  destruct b as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
  assert (p <> Z.to_nat DNUM \/ p = Z.to_nat DNUM) by tauto.
  destruct H10; [ | subst p].
  {
    partition_absrulestac valid_port_none_abt'. apply absabort_rule.
  }

  (* find port_ptr -> direction, mode *)
  assert (get dportls1 portptr = Some (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5)).
  { eapply pptr_in_dportls1; eauto. }
  unfold RLH_PortPtrINecb in H3; destruct H3.
  assert (exists n dport msgl,
    nth_error dportl n = Some dport /\ nth_error dportmsgll n = Some msgl /\
    nth_error dpptrl n = Some portptr /\ DomainportNode_P dport (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5) msgl).
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
  rename v'20 into portptr.

  hoare name lift osdomainportid pre.
  hoare abs lift pre.
  partition_absrulestac valid_port_cont.
  can_change_aop_solver'.
  partition_absrulestac absinfer_choice2.
  1,2:can_change_aop_solver'.
  partition_absrulestac absinfer_choice2.
  1,2: can_change_aop_solver'.
  partition_absrulestac absinfer_choice2.
  1,2: can_change_aop_solver'.
  partition_absrulestac absinfer_choice2.
  1,2: can_change_aop_solver'.
  partition_absrulestac absinfer_choice2.
  1,2: can_change_aop_solver'.

  (* kport ′ =ₑ OSKernelPortIDTbl ′ [port_ptr ′ .. portID];ₛ *)
  unfold AOSKernelPortIDTbl.
  hoare normal pre; pure intro.
  eapply seq_rule.
  {
    hoare name lift kport pre.
    hoare abs lift pre.
    assert (exists id kportp kport,
            OS_Port_V_portID dport = Some (Vint32 id) /\
            nth_error kportvl (nat_of_Z (Int.unsigned id)) = Some (Vptr kportp) /\ 
            nth_error kportl (nat_of_Z (Int.unsigned id)) = Some kport /\
            struct_type_vallist_match OS_K_Port kport /\
            OS_K_Port_V_portID kport = Some (Vint32 id) /\
            OS_K_Port_V_dmport kport = Some (Vptr portptr) /\
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
      { reflexivity. }
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
        clear - H36. mauto.
      }
      {
        unfold DomainportNode_P in H15; simpljoin1.
        unfold Domainport_nat_P in H15; simpljoin1.
        rewrite H20.
        clear - H36. mauto.
      }
      2: reflexivity.
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
  Optimize Proof.
  Optimize Heap.
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
          OS_K_Port_V_dmport kport = Some (Vptr portptr) /\
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
  rename v'20 into kportpb. rename v'22 into kportpl1. rename v'23 into kportpl2.
  rename v'24 into kportl1. rename v'25 into kportl2. rename x1 into channel.

  assert (exists kporth, 
    KernelportNode_P (Vint32 portid :: Vint32 i1 ::
      Vptr portptr :: channel :: V$ DNUM :: Vint32 i :: x8 :: nil) kporth /\
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
    partition_absrulestac absinfer_choice1.
    1,2: can_change_aop_solver'.
    hoare name lift oskportid pre.
    hoare name lift osdomainportid pre.
    hoare abs lift pre.
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply err_nochannel_absinfer; eauto.
      {
        instantiate (1:=∘ (Int.unsigned x1)).
        instantiate (1:=(kportpb, Int.zero)).
        unfold Kernelport_channel_P in H44; destruct o0;
        unfold OS_K_Port_V_channel in H44; simpl in H44; inverts H44.
        auto.
      }
      can_change_aop_solver'.
    }
    instantiate (1:=Afalse).
    partition_exit'.
    {
      unfold dmportp_sll.
      sep autocancel.
      unfold AOSKernelPortIDTbl.
      sep normal; sep eexists; sep autocancel.
      sep split; eauto.
      eapply kportNode_P_compose; eauto.
      rewrite H42; auto.
    }
    { go. }
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
    hoare abs lift pre.
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

  (* semaphore ′ =ₑ channel ′ .. semaphore;ₛ *)
  assert (R_KernelPortIDTbl_ChannelIDTbl_chan_Vptr
    (kportpb, Int.zero) (Vint32 portid :: Vint32 i1 :: Vptr portp :: Vptr chanptr
     :: V$ DNUM :: Vint32 x1 :: x8 :: nil) chanvl chanl chandstportll kportls dportls1 dportls2).
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
  rename v'29 into chanpb. rename v'20 into chanpl1. rename v'24 into chanpl2.
  rename v'22 into chanl1. rename v'25 into chanl2.
  rename v'23 into chandstkportll1. rename v'26 into chandstkportll2.
  unfold KPort, port_id, addrval, port_coreNum in H25, H47;
  rewrite H25 in H47; inverts H47.
  rename x10 into portptr.
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
    2:{ apply H50. }
    sep normal in H50; sep destruct H50; sep split in H50.
    unfold Domainport_Portt_P in H29.
    destruct p5.
    {
      assert (OSPortAttrTblMode portptr = (V$ SAMPLE)).
      {
        eapply RL_PortAttr_mode_SAMPLE; eauto.
        {
          rewrite nth_error_app2; [idtac|lia].
          rewrite Nat.sub_diag; simpl; eauto.
        }
        unfold DomainportNode_P; split; eauto.
        unfold Domainport_nat_P.
        do 5 eexists; splits; eauto.
        splits; eauto.
      }  
      rewrite Hmode in H56.
      discriminate.
    }
    simpljoin1.
    rewrite H55 in H64.
    unfold SAMPLE, QUEUE in H64.
    exfalso; clear - H64; pauto.
  }
  pure intro.
  rename v'20 into qendptr.
  rename v'22 into qinptr.
  rename v'23 into qoutptr.
  rename v'24 into qsize.
  rename v'25 into qentries.
  rename v'21 into qstartptr.
  unfold Domainport_Portt_P in H29.
  destruct p5; simpljoin1.
  {
    rewrite H70 in H50.
    unfold SAMPLE, QUEUE in H50.
    exfalso; clear - H50; pauto.
  }
  clear H50. 
  rewrite H47 in H65.
  inverts H65. rename n into qsize.
  destruct d.
  2:{
    assert (OSPortAttrTblDir portptr = (V$ DESTINATION)).
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
      splits; eauto.
    }
    rewrite Hdir in H29.
    exfalso; clear - H29; tryfalse.
  }
  unfold Domainport_direction_P in H28.
  unfold OS_Channel_V_channelID in H46; simpl in H46; inverts H46.
  rename x7 into dstkportpl.

  partition_absrulestac absinfer_choice2.
  assert (exists chanh,
    ChannelNode_P otherppl (Vint32 chanid :: Vint32 i1
      :: Vint32 v'28 :: Vint32 i :: v'27 :: x15 :: x16 :: x17 :: nil)
      chanh (chanpb, Int.zero) dstkportpl kportls dportls1 dportls2 /\
    get chanls (chanpb, Int.zero) = Some chanh).
  { eapply RLH_Channel_app_cons; eauto. }
  simpljoin1. destruct x as [[[cid cdn] cdstkp] ct].
  assert (nodup_dport kportls) by auto.
  clear Hnodup_d_k.
  (* ASSERTqportpost_port_kport_channel_map
           (Vptr portptr :: Vptr msgptr :: v :: vsem :: vl:: v');; *)
  hoare name lift oschannelid pre.
  hoare name lift oskportid pre.
  hoare name lift osdomainportid pre.
  hoare abs lift pre.
  assert (
    ~((exists csemid, vsem = Vint32 (Int.repr (Z.of_nat csemid)) /\ 
    get chanls (chanpb, Int.zero) = Some (cid, cdn, cdstkp, OutcoreC csemid)) \/ 
      vsem = Vnull /\  get chanls (chanpb, Int.zero) = Some  (cid, cdn, cdstkp, IncoreC)) \/
      ((exists csemid, vsem = Vint32 (Int.repr (Z.of_nat csemid)) /\ 
                        get chanls (chanpb, Int.zero) = Some (cid, cdn, cdstkp, OutcoreC csemid)) \/ 
        vsem = Vnull /\  get chanls (chanpb, Int.zero) = Some  (cid, cdn, cdstkp, IncoreC))
  ) by (clear; tauto).
  destruct H65.
  {
    partition_absrulestac qportpost_port_kport_channel_map_abt.
    apply absabort_rule.
  }
  
  assert (channeldstnum <> Vint32 (Int.repr (Z.of_nat (length cdstkp))) \/
    channeldstnum = Vint32 (Int.repr (Z.of_nat (length cdstkp))) ) by (clear; tauto).
  destruct H71.
  {
    partition_absrulestac qportpost_port_kport_channel_map_abt'.
    apply absabort_rule. 
  }
  subst channeldstnum.
  partition_absrulestac qportpost_port_kport_channel_map_cont.
  unfold ChannelNode_P in H29; simpljoin1.
  rename H72 into Hdstkportpl_nodup.
  unfold Channel_nat_P in H29; simpljoin1.
  unfold OS_Channel_V_channelID in H29; simpl in H29;
    inverts H29; rename x into chanid.
  unfold OS_Channel_V_dstPortsNum in H73; simpl in H73;
    inverts H73; rename x0 into dpnum.

  (* merge dmportp_sllseg*)
  hoare remember (18::17::16::6::5::nil)%nat pre.
  eapply backward_rule1.
  {
    intros.
    instantiate (1:=dmportp_sllseg dportlptr Vnull (dportl1 ++ dport :: dportl2)
    (dportmsgll1 ++ msg :: dportmsgll2) OS_Port_V_nextPort ** H29).
    eapply dmportp_sllseg_compose; eauto.
    sep autocancel.
    right.
    sep eexists. sep auto.
  }
  subst H29.

  (* merge kportNode_P*)
  hoare remember (11::12::13::nil)%nat pre.
  eapply backward_rule1.
  {
    intros.
    instantiate (1:=kportNode_P (kportpl1 ++ (Vptr (kportpb, Int.zero)) :: kportpl2)
                    (kportl1 ++ (Vint32 portid :: Vint32 chanid :: Vptr portptr
                         :: Vptr (chanpb, Int.zero) :: V$ DNUM :: Vint32 x1 :: x8 :: nil) :: kportl2) ** H29).
    eapply kportNode_P_compose; eauto.
    congruence.
  }
  subst H29.

  destruct H65.
  (* 核间通信 *)
  {
    destruct H29 as [csemid ?]. simpljoin.
    unfold Channel in H46, H65;
    rewrite H46 in H65; inverts H65.
    unfold Channel_type_P in H71; simpljoin1.
    unfold OS_Channel_V_semaphore in H29. simpl in H29. inverts H29.
    remember (v1::v') as vsdstcl.
    clear v1 v' Heqvsdstcl.
    assert ($ Z.of_nat (Z.to_nat (Int.unsigned ($ Z.of_nat csemid))) = ($ Z.of_nat csemid)) as Hsem.
    {
      rewrite Z2Nat.id by apply Int.unsigned_range.
      apply Int.repr_unsigned.
    }
    (* semaphore ′ =ₑ channel ′ .. semaphore;ₛ *)
    hoare forward.
    { qportpostproof_tac. }

    (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
    {CSLSEMACC (semaphore ′, resource_get_res ′);ₛ
    If (resource_get_res ′ ==ₑ 〈 char_t 〉 ′ 0)
    {EXIT_CRITICAL;ₛ
    RETURN 〈 char_t 〉 ′ OS_CHANNEL_ERR_BEING_USED}};ₛ *)
    hoare forward.
    { qportpostproof_tac. }
    { pauto. }
    { pauto. }
    {
      hoare normal pre; pure intro.
      clear H29 H71 H73.
      hoare name lift resource_get_res pre.
      hoare remember (2:: 1:: nil)%nat pre.
      eapply seq_rule.
      {
        eapply cslsemacc_rule'.
        { subst. go. }
        { rewrite Z2Nat.id. 1,2: eapply Int.unsigned_range_2. }
        {
          rewrite Hsem.
          subst H29.
          symbolic execution.
          qportpostproof_tac.
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
          all:  clear- H71; tauto. 
        }
        {
          subst H29.
          unfold p_local, CurLINV, LINV, OSLInv.
          intros.
          sep normal in H29; sep destruct H29; sep split in H29.
          sep auto.
          splits; eauto.
          all: clear-H71; tauto.
        }
      }
      eapply disj_rule'.
      {
        subst H29.
        instantiate (1:=Afalse).
        hoare forward.
        hoare normal pre; pure intro.
        partition_exit'.
        unfold AOSDomainPortPtrList, AOSKernelPortIDTbl, AOSChannelIDTbl, dmportp_sll.
        sep pauto; sep autocancel.
        eapply ChannelNode_compose; eauto.
        congruence.
        congruence.
        unfold OS_Channel_V_dstPortsHead; simpl; eauto.
        unfold OS_Channel_V_dstPortsNum; simpl; eauto.
        qportpostproof_tac.
        sep pauto.
        go.
        instantiate (1:=Afalse).
        hoare forward.
        destruct H29.
        { eapply astar_l_afalse_elim. apply H29. }
        sep split in H29.
        exfalso; clear - H71. destruct H71; mauto.
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
    clear H29 H71 H73 H74.

    (* dstKPort ′ =ₑ channel ′ .. dstPortsHead;ₛ *)
    hoare forward.
    { qportpostproof_tac. }
    rename v'27 into dstkport.

    destruct H48.
    {
      unfold R_KernelPortIDTbl_ChannelIDTbl_IncoreC in H29; simpljoin1.
      unfold OS_Channel_V_semaphore in H29; simpl in H29.
      remember ($ Z.of_nat csemid) as A.
      remember ($ DEFAULT_CHANNLE_SEMAPHROE) as B.
      inverts H29. rewrite H71 in H65.
      exfalso; clear - H65.
      rewrite Int.eq_true in H65; discriminate.
    }
    unfold R_KernelPortIDTbl_ChannelIDTbl_OutcoreC in H29; simpljoin1.
    unfold OS_Channel_V_semaphore in H29; simpl in H29. inverts H29.
    clear H48. destruct H71.
    2:{
      exfalso.
      unfold R_KernelPortIDTbl_ChannelIDTbl_dst in H29; simpljoin1.
      clear - H1 H10 H29.
      eapply map_join_get_some with (x:=dportls1) (y:=dportls2) (z:=dportls); eauto.
    }
    unfold R_KernelPortIDTbl_ChannelIDTbl_scr in H29; simpljoin1.
    unfold port_id in H10; rewrite H10 in H29; inverts H29.
    unfold OS_Channel_V_srcPort in H48; simpl in H48; inverts H48.
    
    destruct H72; simpljoin1.
    {
      exfalso.
      unfold Channel_srckport_Sample in H48; simpljoin1.
      destruct H48; simpljoin1;
      unfold OS_Channel_V_srcPort in H48; simpl in H48; inverts H48.
      unfold addrval, port_id in H25, H74; rewrite H25 in H74; inverts H74.
      unfold addrval, port_id in H10, H76; rewrite H10 in H76; inverts H76.
    }
    unfold Channel_srckport_Queue in H48; simpljoin1.
    unfold OS_Channel_V_srcPortsNum in H73; simpl in H73; inverts H73.
    destruct H48; simpljoin1.
    { unfold OS_Channel_V_srcPortsNum in H72;
      simpl in H72; inverts H72. }
    unfold OS_Channel_V_srcPort in H48; simpl in H48; inverts H48.
    unfold addrval, port_id in H25, H73; rewrite H25 in H73; inverts H73.
    rename x3 into portptr. clear H72.
    unfold addrval, port_id in H10, H74; rewrite H10 in H74; inverts H74.
    
    unfold nat_of_Z in *.
    assert (dpnum = ($ (Z.of_nat (length dstkportpl)))).
    {
      clear - H53 H75.
      rewrite <- H75.
      rewrite Z2Nat.id by (apply Int.unsigned_range).
      rewrite Int.repr_unsigned.
      reflexivity.
    }
    assert ((Int.unsigned dpnum) = Z.of_nat (length dstkportpl)).
    {
      clear - H75.
      rewrite <- H75.
      rewrite Z2Nat.id by (apply Int.unsigned_range).
      reflexivity.
    }
    rewrite H75 in *.
    rewrite <- H48 at 1; try rewrite H72 at 1; try rewrite Nat2Z.id at 1.

    (* If (dstKPort ′ !=ₑ 〈 OS_K_Port ∗ 〉 NULL)
    {WHILE (dstKPort ′ !=ₑ 〈 OS_K_Port ∗ 〉 NULL)
    {error ′ =ᶠ OSQSendToDomain (·dstKPort ′ .. dmport,
      msg_ptr ′, port_ptr ′ .. msgInTick·);ₛ
    dstKPort ′ =ₑ 〈 OS_K_Port ∗ 〉 dstKPort ′ .. OSEventPtr;ₛ
    If (error ′ !=ₑ ′ OS_NO_ERR){error ′ =ₑ ′ OS_ERR_DSTPORT_FULL}};ₛ *)
    hoare forward.
    clear - H60;  pauto.
    pauto.
    pauto.
    { 
      (* qportpost_send_Outcore
      (Z.to_nat (Int.unsigned ($ Z.of_nat (length dstkportpl))))
      (Vptr portptr
        :: Vptr msgptr
          :: V$ Z.of_nat (length dstkportpl)
           :: V$ Z.of_nat csemid :: vdstc :: nil);;
      isched;;
      cslsemrel (Z.to_nat (Int.unsigned ($ Z.of_nat csemid)));;
      (END Some (V$ OS_NO_ERR) ?? END Some (V$ OS_ERR_DSTPORT_FULL))  *)
      
      instantiate (1:=Afalse).
      rename H into HRH_TCB_ECB.
      rename H0 into HRH_curTCB.
      rename H1 into Hjoin_dport.
      rename H3 into HRL_PortPtrList.
      rename H2 into HRL_PortAttr.
      rename H11 into Hdpptrl_ecb.
      rename H4 into HRLH_domainport.
      rename H22 into Hnrr_kportp.
      rename H5 into HRLH_Kernelport.
      rename H6 into HRLH_Channel.
      rename H8 into HR_Kernel_Channel.
      rename H7 into HR_Kernel_Domain.
      rename H9 into HRLHOther.
      rename H14 into Hnrr_portptr.
      rename Hpptr into Hgetportptr. clear H10.
      rename H17 into Hlen_dportmsgll1_dportl1.
      rename H15 into Hdport_V_coreNum.
      rename H31 into Hdport_V_domain.
      rename H33 into Hdport_V_portID.
      rename H35 into Hportid_lt_portnums.
      rename H36 into Hdport_V_status.
      rename H38 into Hdport_V_intick.
      rename H40 into Hdport_V_outtick.
      rename H47 into Hdport_V_qsize.
      rename H70 into Hdport_V_mode.
      rename H28 into Hdport_V_direction.
      rename H13 into Hdport_V_nextport.
      rename H18 into Hdport_type_match.
      rename H19 into Hdport_V_start.
      rename H16 into Hkporttbl_nodup.
      rename H20 into Hlen_kport_portnums.
      rename H12 into Hkportpl_type_match.
      rename H23 into Hnrr_kport.
      rename H24 into Hportid_range.
      rename H30 into Hchanid_range.
      clear H32.
      rename H39 into Hx1_range.
      rename H41 into Hx8_isptr.
      rename H42 into Heq_kportl1_portid.
      rename H27 into Heq_kportpl1_portid.
      rename H43 into Hkport_type_match.
      rename H25 into Hget_kport.
      rename H71 into Hkportp_notin_dstp.
      rename H45 into Hnrr_dstkportpl.
      rename H44 into Hnrr_chan.
      rename H34 into Hnrr_chanp.
      rename H21 into Hchanp_type_match.
      rename H49 into Heq_chanpl_channelnums.
      rename H26 into Hchanp_nodup.
      clear H51 H52 H62. 
      rename H58 into Hlen_chandstkportll1_chanid.
      rename H57 into Hlen_chanl1_chanid.
      rename H54 into Hlen_chanpl1_chanid.
      rename H53 into Hdpnum_range.
      rename H59 into Hcsemid_range.
      rename H60 into Hdstkport_isptr.
      rename H61 into Hx15_isptr.
      rename H63 into Hx17_isptr.
      rename H55 into Hdport_V_End.
      rename H56 into Hdport_V_in.
      rename H64 into Hdport_V_out.
      rename H69 into Hx13_range.
      rename H66 into Hdport_V_entries.
      rename H67 into HQport_msg_ptrs.
      rename H75 into Hlen_dpnum_dstkportpl.
      rename H46 into Hget_chan.
      rename H65 into Hcsemid_neq_default.
      rename H29 into Hchannel_dstk_Queue_Outc.
      rename H50 into Hkportls_nodup.
      rename Hsem into Hcsemid_eq.
      rename H48 into Heq_dpnum_dstkportpl.
      rename H72 into Heq_dpnum_dstkportpl'.

      hoare normal pre; pure intro.
      destruct Hdstkport_isptr as [?|[headptr Hheadptr_isptr]]; subst.
      exfalso; clear - H; mauto.
      clear H H0 H1.
      unfold TmrInv, HeapInv'.
      pure intro.
      hoare name lift osdomainport oskport oschannel oscoreheapid pre.
      rename v' into cheapl.
      rename v'20 into cheape.
      rename v'21 into cheapt.
      partition_absrulestac absinfer_choice2.
      assert (
        ~ ( exists mlen msg,
          Get_heapl_addrval cheapl msgptr (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\
          (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z ) \/
        ( exists mlen msg,
              Get_heapl_addrval cheapl msgptr (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\
              (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z )
      ) as [ | ] by tauto.
      {
        partition_absrulestac qportpost_msg_in_heapl_abt.
        apply absabort_rule.
      }
      simpljoin1.
      rename x into mlen. rename x0 into msg.
      rename H2 into Hget_heapl_msg.
      rename H3 into Hmlen_le_chche_size.
      partition_absrulestac qportpost_msg_in_heapl_cont.
      (* split AOScoreheapl *)
      hoare name lift AOScoreheapl pre.
      eapply backward_rule1.
      {
        eapply Get_heapl_addrval_split_coreheapl; eauto.
      }
      naive pure intro.
      rename v' into cheapl1. rename v'20 into cheapl2.
      rename v'21 into heapmsglen. rename v'22 into irheapmsg. 
      simpljoin1.
      rewrite <- H6. simpl length. rename H3 into Hmsg_type_match.
      rename H4 into Hmsg_heap_max_len.
      rename H6 into HSmlen.
      rename H into Hheapl_nodup.
      rename H0 into Hheape_nodup.
      rename H1 into Hheapt_nodup.
      cbn [Aarray Aarray'].
      destruct msgptr as [msgptrb msgptro].
      partition_absrulestac absinfer_choice2.
      
      (*ASSERT qportpost_dstplength_coresem_Outcore
           (Vptr portptr
            :: Vptr (msgptrb, msgptro)
               :: V$ Z.of_nat (length dstkportpl) :: V$ Z.of_nat csemid :: vsdstcl)*)
      hoare name lift Aop osdomainport oskport oschannel pre. 
               assert (~ ((length vsdstcl = length dstkportpl)%nat /\
      Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstcl /\
      ( forall n, (n < (length dstkportpl))%nat -> 
        exists dstpaddr dstpcn dstpd dstpid dstpst dstpin dstpout dstsz dstpm,
        exists dstkpaddr dstkpst nextdst,
        nth_error dstkportpl n = Some dstkpaddr /\ 
        get kportls dstkpaddr = Some (dstpid, Some dstpaddr, Some (chanpb, Int.zero), dstpcn, dstkpst) /\ 
        get dportls dstpaddr = Some (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz dstpm) /\
        ((Z.of_nat dstpcn) <> DNUM -> nth_error vsdstcl n = Some (Vint32 (Int.repr (Z.of_nat dstpcn)))) )) \/
        ((length vsdstcl = length dstkportpl)%nat /\
      Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstcl /\
      ( forall n, (n < (length dstkportpl))%nat -> 
        exists dstpaddr dstpcn dstpd dstpid dstpst dstpin dstpout dstsz dstpm,
        exists dstkpaddr dstkpst nextdst,
        nth_error dstkportpl n = Some dstkpaddr /\ 
        get kportls dstkpaddr = Some (dstpid, Some dstpaddr, Some (chanpb, Int.zero), dstpcn, dstkpst) /\ 
        get dportls dstpaddr = Some (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz dstpm) /\
        ((Z.of_nat dstpcn) <> DNUM -> nth_error vsdstcl n = Some (Vint32 (Int.repr (Z.of_nat dstpcn)))) ))) by tauto.
      destruct H.
      {
        partition_absrulestac qportpost_dstplength_coresem_Outcore_abt.
        apply absabort_rule.
      }
      partition_absrulestac qportpost_dstplength_coresem_Outcore_cont.

      hoare name lift Aisr Ais aemp_isr_is pre.
      eapply backward_rule1.
      apply elim_aemp_isr_is_prop.
      
      (* WHILE (dstKPort ′ !=ₑ 〈 OS_K_Port ∗ 〉 NULL)
      {error ′ =ᶠ OSQSendToDomain (·dstKPort ′ .. dmport, msg_ptr ′·);ₛ
      dstKPort ′ =ₑ 〈 OS_K_Port ∗ 〉 dstKPort ′ .. OSEventPtr;ₛ
      If (error ′ !=ₑ ′ OS_NO_ERR){error ′ =ₑ ′ OS_ERR_DSTPORT_FULL}};ₛ *)
      hoare normal pre.
      hoare name lift dstKPort pre.
      hoare name lift Channel_dstkport_get pre.
      hoare name lift osdomainport pre.
      hoare name lift OtherPortPtrList pre.
      
      eapply backward_rule1.
      eapply OtherPortPtrList_Forall_struct_type_vallist_match'.
      naive pure intro.
      simpljoin1.
      rename H into Hlen_dstkportpl_vsdstcl.
      rename H1 into Hvsdstcl.
      rename H2 into Hnhypo'.
      rename H0 into Hotherpl_type_match.
     
      assert (
          forall n, (n < length dstkportpl)%nat ->
            exists dstkportp dstportp dstpptrn dstpid dstkpst
                dstpd dstpst dstpin dstpout dstsz, 
                exists dstpm dstpcn dstport nextdst,
              nth_error dstkportpl n = Some dstkportp /\
              nth_error otherppl dstpptrn = Some dstportp /\
              nth_error otherpl dstpptrn = Some dstport /\
              get kportls dstkportp =
                Some (dstpid, Some dstportp, Some (chanpb, Int.zero), dstpcn, dstkpst) /\
              get dportls2 dstportp = 
                Some (dstpcn, dstpd, dstpid,
                  DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz dstpm) /\
                  nth_error vsdstcl n = Some (V$ Z.of_nat dstpcn) /\ 
                  Z.of_nat dstpcn <> DNUM
      ) as Hnhypo.
      { 
        eapply dstkportpl_get_Queue_Outcore; eauto. }
      clear Hnhypo'.
      eapply seq_rule.
      {
        hoare name lift osdomainportid pre.
        hoare name lift OtherPortPtrList pre.
        hoare name lift Channel_dstkport_get pre.
        hoare name lift dstKPort pre.
        hoare evar lift error pre.
        hoare abs lift pre.
        hoare remember (1::2::3::4::5::6::nil)%nat pre.
        eapply backward_rule1.
        {
          instantiate(1:=
          EX n ndkpv notherpl nothermsgll ndportls2 ndportls errv,
          ( [| ndkpv = Vnull |] ** [| n = length dstkportpl |] \\//
            EX ndkpptr, [| ndkpv = Vptr ndkpptr |] **
            [| nth_error dstkportpl n = Some ndkpptr |]  ) **
          LV error @ char_t |-> Vint32 errv  **
          [| errv = Int.repr OS_NO_ERR \/ errv = Int.repr OS_ERR_DSTPORT_FULL |] **
          [| forall m kp dp a1 a2 a3 a4, (n<=m)%nat -> nth_error dstkportpl m = Some kp -> 
            get kportls kp = Some (a1, Some dp, a2, a3, a4) -> get ndportls2 dp = get dportls2 dp|] **
          <||
          spec_code_cons (qportpost_send_Outcore ((length dstkportpl) - n)%nat
            (Vptr portptr
            :: Vptr (msgptrb,msgptro)
                :: V$ Z.of_nat (length dstkportpl)
                  :: V$ Z.of_nat csemid :: vsdstcl))
                  (
                  cslsemrel (Z.to_nat (Int.unsigned ($ Z.of_nat csemid)));; isched;; 
                  (END Some (V$ OS_NO_ERR) ?? END Some (V$ OS_ERR_DSTPORT_FULL))) ||>  **
          LV dstKPort @ OS_K_Port ∗ |-> ndkpv **
          Channel_dstkport_get (Vptr headptr) Vnull (length dstkportpl) dstkportpl **
          OtherPortPtrList otherppl notherpl nothermsgll **
          Hdomainportl ndportls **
          [| join dportls1 ndportls2 ndportls |] **
          [| RLH_Channel otherppl
              (chanpl1 ++ Vptr (chanpb, Int.zero) :: chanpl2)
              (chanl1 ++ (Vint32 chanid :: V$ 1 :: V$ Z.of_nat (length dstkportpl)
               :: V$ Z.of_nat csemid :: Vptr headptr :: x15 :: Vptr (kportpb, Int.zero) :: x17 :: nil) :: chanl2)
              (chandstkportll1 ++ dstkportpl :: chandstkportll2) chanls
              kportls dportls1 ndportls2 |] **
          [| R_KernelPortIDTbl_ChannelIDTbl
              (kportpl1 ++ Vptr (kportpb, Int.zero) :: kportpl2)
              (kportl1 ++
              (Vint32 portid
                :: Vint32 chanid
                  :: Vptr portptr
                      :: Vptr (chanpb, Int.zero)
                        :: V$ DNUM :: Vint32 x1 :: x8 :: nil) :: kportl2)
              (chanpl1 ++ Vptr (chanpb, Int.zero) :: chanpl2)
              (chanl1 ++
              (Vint32 chanid
                :: V$ 1
                  :: V$ Z.of_nat (length dstkportpl)
                      :: V$ Z.of_nat csemid
                        :: Vptr headptr
                            :: x15
                              :: Vptr (kportpb, Int.zero) :: x17 :: nil)
              :: chanl2)
              (chandstkportll1 ++ dstkportpl :: chandstkportll2) kportls
              dportls1 ndportls2 |] **
          [| RLH_OtherPortPtrList otherppl notherpl nothermsgll ndportls2 |] **
          [| Channel_dstkport_Queue_OutcoreC otherppl 
              (chanpb, Int.zero) dstkportpl kportls ndportls2 |] **
          H
          ).
          {
            intros.
            exists 0%nat (Vptr headptr) otherpl othermsgll dportls2; exists dportls (Int.repr OS_NO_ERR).
            sep normal.
            apply disj_split; right.
            destruct dstkportpl; cbn [length ] in *.
            unfold Channel_dstkport_get in H0; sep split in H0; tryfalse.
            cbn [Channel_dstkport_get] in *.
            sep normal in H0; sep destruct H0; sep split in H0. invertsr H3.
            sep normal. exists headptr.
            sep eexists; sep split; eauto.
            rewrite H4. rewrite Heq_dpnum_dstkportpl'.
            repeat f_equal.
            rewrite Nat2Z.id. reflexivity.
          }
        }
        subst H.
        eapply while_rule.
        {
          intros.
          sep destruct H.
          apply disj_split in H.
          destruct H.
          symbolic execution.
          symbolic execution.
          destruct x12; pauto.
          destruct x12; pauto.
        }
        (* Loop Body *)
        naive pure intro.
        rename v' into n. rename v'20 into ndkpv.
        eapply aconj_aistrue_rule.
        {
          intros.
          sep destruct H.
          apply disj_split in H.
          instantiate (1:=val_inj (notint (val_inj (val_eq ndkpv Vnull)))).
          destruct H; sep normal in H; sep split in H.
          symbolic execution.
          symbolic execution.
          destruct x; pauto.
          unfold val_eq; destruct x; pauto.
        }
        naive pure intro.
        eapply backward_rule1.
        intros s Hs; eapply disj_split in Hs; apply Hs.
        eapply disj_rule.
        { naive pure intro. exfalso. subst. clear - H8; pauto. }
        naive pure intro.
        rename v' into dstkportp. subst ndkpv.
        clear H8.
        rename H0 into Hnrr_dstkport.
        rename H1 into Herrv.
        rename H2 into Hdportls2_dportls2'.
        rename v'23 into dportls2'.
        rename v'24 into dportls'.
        rename H3 into Hjoin_dport'.
        rename H4 into HRLH_Channel'.
        rename H5 into HR_Kernel_Channel'.
        rename v'25 into errv.
        apply nth_error_split in Hnrr_dstkport as (dstkportpl1 & dstkportpl2 & ? & ?).
        subst dstkportpl n.
        rename H6 into HRLHOther'.
        rename H7 into HChannel_dstkport_Queue_OutcoreC'.
        
        hoare name lift Channel_dstkport_get pre.
        eapply backward_rule1.
        eapply Channel_dstkport_get_app_frm; eauto.
        naive pure intro. 
        rename v'20 into nextdstkport.
        rename v' into dstkport'.
        rename H into Hdstkport'_type_match.
        rename H0 into Hdstkport'_V_EventPtr.
        assert ((length (dstkportpl1 ++ dstkportp :: dstkportpl2) - length dstkportpl1)%nat = S (length dstkportpl2)).
        clear; induction dstkportpl1; simpl; try lia.
        rewrite H. clear H.
        assert ((S (length dstkportpl2) - 1)%nat = length dstkportpl2) by (clear; mauto).
        rewrite H. clear H.
        hoare name lift msg_ptr pre.
        assert ((length dstkportpl1 <
        length (dstkportpl1 ++ dstkportp :: dstkportpl2))%nat) as Hdstkportpl1_lt_dstkportl.
        clear; induction dstkportpl1; simpl; try lia.
        pose proof Hnhypo _ Hdstkportpl1_lt_dstkportl.
        simpljoin1.
        rewrite nth_error_middle in H. invertsr H. 
        rename x0 into dstportp.
        rename x20 into dstpcn.
        rename x18 into dstsz.
        rename x19 into dstpm.
        rename x3 into othern.
        rename v'21 into otherpl'.
        rename v'22 into othermsgl'.
        rename x21 into dstport.
        rename H0 into Hnrr_dstportp.
        rename H1 into Hnrr_dstport.
        rename H2 into Hget_dstkportp.
        rename H3 into Hget_dstportp.
        rename H4 into Hvsdstcl_dstpcn.
        rename H5 into Hdstpcn_DNUM_neq.
        
        (* find ndstkport in kportNode_P *)
        hoare name lift kportNode_P pre.
        pose proof RLH_Kernelport_abs_getsome' _ _ _ _ _ _ _ _ _ Hget_dstkportp HRLH_Kernelport.
        simpljoin1.
        rename x0 into dstkport.
        rename H into Hnrr_dsrkportp.
        rename H0 into Hnrr_dstkport.
        rename H1 into HKernelportNode_P_dstkport.
        eapply backward_rule1.
        eapply kportNode_P_getsome_frm; eauto.
        naive pure intro.
        rename v' into dstkportpb.
        rename v'20 into kportpl1'. rename v'21 into kportpl2'.
        rename v'22 into kportl1'. rename v'23 into kportl2'.
        simpljoin.
        rename H4 into Hdstkport_type_match.
        rename H0 into Hkportpl_kportpl'.
        rename H1 into Hkportl_kportl'.
        rename H3 into Hlen_kportl1'_kportpl1'.
        unfold KernelportNode_P in HKernelportNode_P_dstkport.
        destruct HKernelportNode_P_dstkport as (HKernelportNode_nat_P_dstkport&
        HKernelportNode_dmport_P_dstkport& HKernelportNode_channel_P_dstkport).
        unfold Kernelport_dmport_P in HKernelportNode_dmport_P_dstkport.
        assert (nth_val' 2 dstkport = Vptr dstportp) as Hnval_dstportp.
        {
          clear - Hdstkport_type_match HKernelportNode_dmport_P_dstkport.
          struct_type_vallist_match_elim.
          inverts HKernelportNode_dmport_P_dstkport.
          reflexivity.
        }
        
        (* error ′ =ᶠ OSQSendToDomain (·dstKPort ′ .. dmport, msg_ptr ′·);ₛ *)

        eapply seq_rule.
        {
          eapply calle_rule_lvar'.
          { reflexivity. }
          {
            (* RV *)
            intros. 
            eapply rvl_elim.
            {
              eapply dstKPort_dmport_rv.
              2:{ sep autocancel. apply H. }
              auto.
  Optimize Proof.
  Optimize Heap.
            }
            eapply rvl_elim; [symbolic execution| ].
            apply rvl_nil.
          }
          {
            (* ==>pre *)
            unfold getasrt, OSQSendToDomainPre, OSQSendToDomainPre'.
            intros.
            apply disj_split.
            left.
            sep normal.
            sep eexists.
            sep cancel Aop.
            sep cancel OtherPortPtrList.
            sep autocancel.
            sep split; eauto.
            4:{
              erewrite Hdportls2_dportls2';[eauto|..]. 
              3:{ apply Hget_dstkportp. }
              2: apply nth_error_middle.
              lia.
            }
            - cbn [Aarray Aarray']. sep normal. sep autocancel. apply H.
            - rewrite <- HSmlen in Hget_heapl_msg. auto.
            - now rewrite Hnval_dstportp.
          }
          { go. }
          {
            unfold retpost. intros.
            unfold getasrt, OSQSendToDomainPost, OSQSendToDomainPost' in H.
            destruct H; sep destruct H; sep split in H.
            - clear - H0. destruct H0; simpljoin; auto.
            - clear - H0. destruct H0; simpljoin; subst; auto.
          }
          { rewrite Hnval_dstportp. pauto.  }
          {
            unfold getasrt, OSQSendToDomainPost, OSQSendToDomainPost'.
            intros. sep destruct H.
            destruct H; sep normal in H; sep destruct H; sep eexists; sep auto.
          }
          {
            unfold getasrt, OSQSendToDomainPre, OSQSendToDomainPre'.
            intros. sep destruct H.
            destruct H; sep normal in H; sep destruct H; sep eexists; sep auto.
          }
        }
        rewrite Hnval_dstportp.
        
        (* Unfold Post*)
        unfold getasrt, OSQSendToDomainPost, OSQSendToDomainPost'.
        naive pure intro.
        
        (* disj *)
        eapply backward_rule1.
        intros. apply disj_split in H; apply H.
        apply disj_rule.
        2:{
          naive pure intro.
          inverts H10.
        }
        naive pure intro.
        invertsr H7.
        invertsr H3.
        subst v'28.
        rename v'48 into dportls2''.
        rename v'49 into dportls''.
        rename v'37 into otherpl''.
        rename v'38 into othermsgll''.
        rename H into Hdportls2''.
        rename H1 into Hchannel_dstk_Queue_Outc''.
        rename H0 into HOther''.
        rename H6 into HR_Kernel_Channel''.
        rename H5 into HRLH_Channel''.
        rename H4 into Hjoin_dport''.
        
        (* dstKPort ′ =ₑ 〈 OS_K_Port ∗ 〉 dstKPort ′ .. OSEventPtr *)
        eapply seq_rule.
        {
          eapply assign_rule_lvar.
          { split; [ | sep pauto]. sep pauto. }
          {
            intros.
            eapply symbolic_lemmas.cast_rv_tptr with (v:= nextdstkport) (t1:= Void).
            2: { clear - Hdstkport'_type_match Hdstkport'_V_EventPtr. 
            struct_type_vallist_match_elim. inverts Hdstkport'_V_EventPtr.
            pauto.
            }
            eapply symbolic_lemmas.struct_member_rv_flag; eauto.
            { sep cancel dstKPort. sep autocancel. apply H. } 
            1-3: reflexivity.
            { clear - Hdstkport'_type_match Hdstkport'_V_EventPtr. 
              struct_type_vallist_match_elim. inverts Hdstkport'_V_EventPtr.
              pauto.
            }
          }
          { now apply assign_type_match_true. }
          { intros; sep eexists; sep cancel p_local; sep pauto. }
        }
        (* If (error ′ !=ₑ ′ OS_NO_ERR)
          {error ′ =ₑ ′ OS_ERR_DSTPORT_FULL} *)
        hoare evar lift error pre.
        hoare remember (1::nil)%nat pre.
        eapply forward_rule1 with
        (EX errv, LV error @ char_t |-> Vint32 errv ** [| errv = $ OS_NO_ERR \/ errv = $ OS_ERR_DSTPORT_FULL |] ** H ).
        2:{
          destruct Hdportls2''; simpljoin.
          - inverts H1. 
            apply corecommu_rules.ift_nonzero_rule.
            2:{ hoare forward. }  
            intros. exists Int.one.
            sep split. symbolic_execution.
            destruct (Int.eq_dec (Int.one) (Int.zero));[discriminate| ].
            now apply Int.eq_false.
          - inverts H1.
            eapply forward_rule1.
            2:{
              apply corecommu_rules.ift_zero_rule.
              symbolic_execution.
            }
            intros.
            sep eexists. sep autocancel.
            sep auto.
        }
        (* To loop invariant *)
        intros.
        sep destruct H0.
        rename x into errv''.
        subst H.
        exists (S (length dstkportpl1)).
        eexists.
        exists otherpl''.
        exists othermsgll''.
        exists dportls2''.
        exists dportls''.
        exists errv''.
        sep autocancel.
        cbn [Aarray Aarray'] in H0.
        sep normal in H0.
        sep autocancel.
        assert (isptr nextdstkport) as Hnextdstkport_isptr.
        {
          clear - Hdstkport'_type_match Hdstkport'_V_EventPtr.
          struct_type_vallist_match_elim.
          inverts Hdstkport'_V_EventPtr.
          pauto.
        }
        destruct Hnextdstkport_isptr as [ | [? ?]].
        - (* nextdstkport is null *)
          subst nextdstkport.
          destruct dstkportpl2.
          2:{
            cbn [length Channel_dstkport_get] in H0.
            sep normal in H0.
            sep destruct H0.
            sep split in H0.
            discriminate.
          }
          apply disj_split. left.
          sep normal.
          sep split; auto.
          4: rewrite app_length; simpl; lia.
          2:{
            sep split in H0.
            rewrite H. repeat f_equal.
            rewrite app_length. simpl. lia.
          }
          {
            rewrite app_length.
            simpl length.
            sep name lift kportNode_P.
            rewrite Hkportpl_kportpl'.
            rewrite Hkportl_kportl'.
            eapply kportNode_P_compose; eauto.
            sep autocancel.
            assert (length dstkportpl1 +1= S (length dstkportpl1)+0)%nat by lia.
            rewrite H. clear H.
            eapply Channel_dstkport_get_compose; auto.
            3: sep autocancel; sep auto.
            apply Hdstkport'_type_match.
            auto.
  Optimize Proof.
  Optimize Heap.
          }
          {
            intros.
            destruct Hdportls2''.
            - simpljoin. eapply Hdportls2_dportls2'.
              3: apply H2.
              2: eauto.
              lia.     
            - simpljoin. rename x into ndstportp.
              rewrite set_a_get_a'.
              eapply Hdportls2_dportls2'.
              3: apply H2.
              2: eauto.
              lia.
              lets Hkportls_nodup': Hkportls_nodup (dstkportpb, Int.zero) kp.
              setoid_rewrite Hget_dstkportp in Hkportls_nodup'.
              setoid_rewrite H2 in Hkportls_nodup'.
              apply Hkportls_nodup'.
              eapply addrval_Nodup_nth_err_neq.
              4: apply H1. auto.
              2:{ apply nth_error_middle. } 
              lia.
          }
          - (* nextdstkport is not null *)
          subst nextdstkport. rename x into nextdstkportp.
          destruct dstkportpl2.
          {
            cbn [length Channel_dstkport_get] in H0.
            sep normal in H0.
            sep destruct H0.
            sep split in H0.
            discriminate.
          }
          apply disj_split. right.
          assert (a=nextdstkportp) as Htmp.
          {
            cbn [length Channel_dstkport_get] in H0. sep split in H0.
            now inverts H.
          }
          subst a. 
          sep normal. sep eexists.
          sep split; auto.
          4: apply nth_error_S_middle.
          2:{
            sep split in H0.
            rewrite H. repeat f_equal.
            rewrite app_length. simpl. lia.
          }
          {
            rewrite app_length.
            simpl length.
            sep name lift kportNode_P.
            rewrite Hkportpl_kportpl'.
            rewrite Hkportl_kportl'.
            eapply kportNode_P_compose; eauto.
            sep autocancel.
            assert (length dstkportpl1 + S (S (length dstkportpl2))= S (length dstkportpl1)+S(length (dstkportpl2)))%nat by lia.
            rewrite H. clear H.
            eapply Channel_dstkport_get_compose; auto.
            simpl length in H0.
            3: sep autocancel; sep auto.
            apply Hdstkport'_type_match.
            auto.
          }
          {
            intros.
            destruct Hdportls2''.
            - simpljoin. eapply Hdportls2_dportls2'.
              3: apply H2.
              2: eauto.
              lia.     
            - simpljoin. rename x into ndstportp.
              rewrite set_a_get_a'.
              eapply Hdportls2_dportls2'.
              3: apply H2.
              2: eauto.
              lia.
              lets Hkportls_nodup': Hkportls_nodup (dstkportpb, Int.zero) kp.
              setoid_rewrite Hget_dstkportp in Hkportls_nodup'.
              setoid_rewrite H2 in Hkportls_nodup'.
              apply Hkportls_nodup'.
              eapply addrval_Nodup_nth_err_neq.
              4: apply H1. auto.
              2:{ apply nth_error_middle. } 
              lia.
          }
        }
      naive pure intro.
      rename v'20 into nextdstkportp.
      rename v'25 into errv.
      rename v' into dstkportpl_n.
      rename v'21 into otherpl_final.
      rename v'22 into othermsgll_final.
      rename v'23 into dportls2_final.
      eapply aconj_aisfalse_rule. 
      {
          
        instantiate(1:=Vint32 (match nextdstkportp with 
          | Vnull => Int.zero  | _ => Int.one end)).
        intros. apply disj_split in H. destruct H.
        - symbolic_execution.
        - sep normal in H. sep destruct H. sep split in H.
          subst.
          symbolic_execution. destruct x; auto.
          destruct x; pauto.
      }
      (* Deal with the end pf loop *)
      naive pure intro.
      eapply backward_rule1.
      intros. apply disj_split in H. exact H.
      apply disj_rule.
      2:{
        naive pure intro.
        subst. destruct H8; discriminate.
      }
      naive pure intro.
      subst nextdstkportp. clear H8. subst dstkportpl_n.
      rename H1 into Herrv.
      clear H2.
      rename v'24 into dportls_final.
      rename H3 into Hjoin_dport_final.
      rename H4 into HRLH_Channel_final.
      rename H5 into HR_Kernel_Channel_final.
      rename H6 into RLH_OtherPortPtrList_final.
      rename H7 into HChannel_dstkport_Queue_OutcoreC_final.
      assert (length dstkportpl - length dstkportpl=0)%nat as Htmp by lia.
      repeat rewrite Htmp. clear Htmp.
      cbn [qportpost_send_Outcore spec_code_cons].

      partition_absrulestac absinfer_seq_end.
      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
        {CSLSEMREL (semaphore ′)};ₛ *)
      eapply seq_rule.
      {
        apply corecommu_rules.ift_nonzero_rule.
        intros. exists Int.one. sep split. symbolic_execution.
        qportpostproof_tac.
        destruct (Int.eq ($ Z.of_nat csemid) ($ DEFAULT_CHANNLE_SEMAPHROE)); auto.
        rewrite Hcsemid_neq_default. reflexivity.
        pauto.
        apply cslsemrel_rule.
        - go.
        - rewrite Z2Nat.id. 2:apply Int.unsigned_range.
          clear - Hcsemid_range. rewrite max_unsigned_val. lia.
        - intros. rewrite Hcsemid_eq.  symbolic_execution.
          qportpostproof_tac.
        - intros. sep name lift p_local in H. 
          unfold p_local in H. sep normal in H.
          unfold CurLINV. eexists. sep autocancel. cbv. tauto.
      }
      hoare name lift Aisr Ais Aier pre.
      eapply backward_rule1.
      apply add_aemp_isr_is_prop.

      (* EXIT_CRITICAL;ₛ *)
      hoare forward prim.
      {
        sep cancel EvtInv.
        sep cancel CoreCommuInv.
        sep cancel p_local.
        sep cancel Aier.
        sep cancel tcbdllflag.
        sep cancel APthreadAttr.
        sep cancel CapabilityInv.
        sep name lift PartitionInv.
        apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        
        (* cancel TmrInv *)
        unfold TmrInv, HeapInv'.
        sep normal; sep eexists; sep autocancel.
        sep split; auto.
        eapply AOScoreheapl_merge with (m:= S (length msg)); pauto.
        { simpl; lia. }
        { simpl; lia. }
        sep autocancel.
        cbn [Aarray Aarray'].
        sep normal. sep autocancel.

        (* cancel PartitionInv *)
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep pauto.
        sep cancel OtherPortPtrList.
        sep cancel AOSChannelFreeList.
        sep cancel AOSKernelPortFreeList.
        sep cancel AOSCorePortPtrList.
        2: eauto.
        9: eauto.
        4: eauto.
        5: eauto.
        6: eauto.
        2: eauto.
        2: auto.
        2: auto.
        2: unfold RLH_PortPtrINecb; tauto.
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
        { congruence. }
        { congruence. }
        { reflexivity. }
        { reflexivity. }
        { pauto. }
        sep autocancel.
        rewrite Int.unsigned_repr.
        2:{
          rewrite <- Heq_dpnum_dstkportpl'.
          apply Int.unsigned_range_2.
        }
        rewrite Nat2Z.id. sep autocancel.
        apply H.
      }
      {
        auto. 
  Optimize Proof.
  Optimize Heap.
      }
      { go. }
      (*OS_Sched (­) *)
      eapply seq_rule.
      {
        eapply call_rule'.
        reflexivity.
        intros. apply rvl_nil.
        intros.
        unfold getasrt, OS_SchedPre, OS_SchedPre'.
        sep normal. sep eexists.
        sep autocancel.
        sep split; eauto.
        unfold isflag. auto.
        go.
        sep_unfold_funpost.
        intros.
        sep destruct H. sep eexists.
        sep autocancel. constructor.
        sep_unfold_funpre. intros.
        sep destruct H. sep eexists.
        sep autocancel. constructor.
        reflexivity.
      }
      unfold getasrt, OS_SchedPost, OS_SchedPost'.
      naive pure intro.
      invertsr H.
      destruct Herrv; subst.
      - (* END Some (V$ OS_NO_ERR) *) 
        partition_absrulestac absinfer_choice1.
        hoare forward.
      - (* END Some (V$ OS_ERR_DSTPORT_FULL)*)
        partition_absrulestac absinfer_choice2.
        hoare forward. 
    }
    (* dstkport is null *)
    apply disj_rule.
    {
      naive pure intro. apply pfalse_rule.
    }
    naive pure intro.
    destruct H60 as [? | [? ?]]; subst dstkport.
    2:{
      exfalso; clear - H73; pauto.
      unfold val_inj, val_eq, notint in H73;
      destruct x;destruct H73; pauto.
      inverts H.
    } clear H73.
    destruct dstkportpl.
    2:{
      simpl (length _).
      cbn [Channel_dstkport_get].
      naive pure intro.
      discriminate.
    }
    simpl (length _).
    eapply backward_rule1.
    {
      intros. sep name lift dmportp_sllseg in H60.
      lets Hss: dmportp_sllseg_app'_frm dportmsgll1 H14 H3.
      reflexivity. 
      assumption.
      apply Hss in H60. clear Hss.
      cbn [dmportp_sllseg] in H60.
      apply H60.
    }
    hoare normal pre. naive pure intro.
    invertsr H60.
    rewrite H13 in H73. invertsr H73.
    clear H74.
    rewrite H19 in H76. invertsr H76.
    simpl in H48. subst dpnum. clear H72.
    hoare name lift Adisj pre.
    eapply backward_rule1.
    apply disj_star_elim_disj.
    apply disj_rule.
    {
      naive pure intro.
      rewrite H70 in H48. discriminate.
    }
    naive pure intro. clear H48.
    rewrite H55 in H60. invertsr H60.
    rewrite H56 in H72. invertsr H72.
    rewrite H64 in H73. invertsr H73.
    simpljoin1.
    rewrite H47 in H72. invertsr H72.
    rewrite H66 in H48. invertsr H48.
    clear H68 H77 H73.
    rename x13 into qsize.
    hoare forward.
    {
      eapply ift_rule''.
      symbolic_exe_port.
      instantiate (1:=Afalse).
      naive pure intro.
      partition_absrulestac absinfer_choice1.
      hoare forward.
      { qportpostproof_tac. }
      { pauto. }
      { pauto. }
      naive pure intro.
      apply cslsemrel_rule.
      { go. }
      {
        rewrite Z2Nat.id by apply Int.unsigned_range.
        apply Int.unsigned_range_2.
      }
      {
        intros. rewrite Hsem. symbolic_execution. qportpostproof_tac.
      }
      {
        unfold p_local, CurLINV, LINV, OSLInv.
        intros.
        sep normal in H72; sep destruct H72; sep split in H72.
        sep auto.
        splits; eauto.
        all: clear - H73; tauto.
      }
      apply disj_rule.
      2:{
        naive pure intro.
        rewrite H65 in H68. clear - H68.
        simpl in H68. destruct H68; pauto. discriminate. 
      }
      {
        naive pure intro.
        clear H48 H68.
        partition_exit'.
        {
          sep autocancel. 
          unfold AOSDomainPortPtrList, dmportp_sll.
          sep normal. sep autocancel.
          unfold AOSKernelPortIDTbl. sep normal. sep autocancel.
          unfold AOSChannelIDTbl. sep normal. sep autocancel.
          sep split; auto.
          sep name lift ChannelNode.
          eapply ChannelNode_compose; pauto.
          congruence. congruence.
          sep autocancel.
          eapply dmportp_sllseg_app'_frm; eauto.
          cbn [dmportp_sllseg].
          sep normal. sep eexists. sep autocancel.
          sep split; eauto.
          apply disj_star_elim_disj'.
          right. sep normal. sep eexists.
          sep split; eauto.
        }
        { go. }
        hoare forward.
      }
    }
    apply disj_rule.
    {
      naive pure intro.
      apply pfalse_rule.
    }
    naive pure intro.
    destruct H48.
    2:{
      exfalso; clear - H48.
      destruct (Int.ltu ($ Z.of_nat qsize) qentries); destruct (Int.eq qentries ($ Z.of_nat qsize)); simpl in H48; mauto.
    }
    clear H52 H53.
    assert (Int.unsigned qentries < Int.unsigned ($ Z.of_nat qsize)).
    {
      clear - H48 H60.
      destruct (Int.ltu ($ Z.of_nat qsize) qentries) eqn:E1; destruct (Int.eq qentries ($ Z.of_nat qsize)) eqn:E2; simpl in H48. 
      1-3: exfalso; mauto.
      apply Inteq_false_is_Zneq in E2. lia.
    }
    clear H48 H60.
    (* (port_ptr ′ → OSQIn) → len =ₑ msg_ptr ′ → len;ₛ *)
    unfold TmrInv. unfold HeapInv'.
    hoare normal pre.
    naive pure intro.
    rename v' into cheapl.
    rename v'20 into cheape.
    rename v'21 into cheapt.
    partition_absrulestac absinfer_choice2. 
    assert (~(exists mlen msg,
    Get_heapl_addrval cheapl msgptr (Z.to_nat (Int.unsigned mlen + 1))
      (Vint32 mlen :: msg) /\ (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z)\/
      (exists mlen msg,
      Get_heapl_addrval cheapl msgptr (Z.to_nat (Int.unsigned mlen + 1))
        (Vint32 mlen :: msg)/\ (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z)) by tauto.
    destruct H68.
    {
      partition_absrulestac qportpost_msg_in_heapl_abt'.
      apply absabort_rule.
    }
    destruct H68 as (mlen&msg&H68&Hmlensize).
    (* ASSERT qportpost_msg_in_heapl
           (Vptr portptr :: Vptr msgptr :: V$ 0 :: V$ Z.of_nat csemid :: vsdstcl)*)
    partition_absrulestac qportpost_msg_in_heapl_cont'.
    partition_absrulestac absinfer_choice1.
    hoare name lift AOScoreheapl pre.
    eapply backward_rule1.
    {
      eapply Get_heapl_addrval_split_coreheapl; eauto.
    }
    naive pure intro.
    rename v' into cheapl1.
    rename v'20 into cheapl2.
    rename v'21 into heapmsglen.
    rename v'22 into irheapmsg.
    simpljoin1.
    rewrite <- H77.
    simpl length.
    cbn [Aarray Aarray'].
    destruct msgptr as [msgptrb msgptro].
    hoare normal pre.
    hoare name lift (dmportp_sllseg_qport_msg qinptr) pre.
    eapply backward_rule1.
    {
      eapply dmportp_sllseg_qport_msg_ngt0.
      clear - H52.
      unfold Coqlib.nat_of_Z. lia.
    }
    naive pure intro.
    destruct H72 as (msghold&msgholdl&?&?). subst v'24.
    simpl in H77.
    assert (Z.to_nat (Int.unsigned mlen + 1) = S (Z.to_nat (Int.unsigned mlen))) by lia.
    rewrite H72 in H77. inverts H77.
    simpl in H74.
    hoare name lift msghold pre.
    eapply backward_rule1.
    {
      apply dmportp_sllseg_qport_msg_split.
      unfold Coqlib.nat_of_Z. lia. 
    }
    naive pure intro.
    destruct H77. destruct H78.
    invertsr H78. rename v'21 into irrmsghold.
    hoare name lift Aop (Aptrmapsto qinptr) pre.
    eapply seq_rule.
    {
      eapply assign_rule_general.
      {
        intros.
        eapply symbolic_lemmas.struct_offset_rv.
        { 
          eapply symbolic_lemmas.addrof_deref_rv.
          sep_get_port_rv.
        }
        all: reflexivity.
      }
      {
        assert ((fst qinptr, Int.add (snd qinptr) (Int.zero)) = qinptr ).
        {
          rewrite Int.add_zero. now destruct qinptr. 
        }
        rewrite H78. clear H78.
        split; intros; eauto.
      }
      { 
        intros. 
        eapply symbolic_lemmas.struct_member_rv_flag.
        sep autocancel.
        2-6: try reflexivity.
        unfold get_off_addr. cbn [fst snd].
        rewrite Int.add_zero.
        sep autocancel. apply H78.
        simpl in H73. tauto. 
      }
      { now apply assign_type_match_true. }
      {
        intros. sep eexists. sep auto.
      }
    }
    clear H72 H81.
    hoare name lift Aisr Ais aemp_isr_is pre.
    eapply backward_rule1.
    apply elim_aemp_isr_is_prop.
    (* memcpy (­&ₐ ((port_ptr ′ → OSQIn) → data) [′ 0], &ₐ (msg_ptr ′ → data) [′ 0],
    〈 long 〉 msg_ptr ′ → len­);ₛ *)
    assert ((fst qinptr, Int.add (snd qinptr) (Int.zero)) = qinptr ).
    {
      rewrite Int.add_zero. now destruct qinptr. 
    }
    rewrite H72. clear H72.
    destruct qinptr as [qinptrb qinptro].
    unfold get_off_addr.  cbn[fst snd].
    hoare name lift (Alvarmapsto port_ptr) APortStruct (Aptrmapsto (qinptrb, qinptro)) pre.
    eapply seq_rule.
    {
      eapply call_rule'; try reflexivity.
      {
        intros.
        eapply rvl_elim.
        {
          eapply symbolic_lemmas.addrof_array_elem_rv.
          {
            eapply port_OSQIn_data_rv'; eauto.
          }
          { symbolic execution. }
          all: pauto.
        }
        eapply rvl_elim.
        {
          eapply symbolic_lemmas.addrof_array_elem_rv.
          {
            eapply struct_member_array_rv. symbolic_execution.
            all: reflexivity.
          }
          { symbolic execution. }
          all: pauto.
        }
        eapply rvl_elim; [ |apply rvl_nil].
        instantiate (1:=(Vint32 mlen)).
        eapply cast_rv_tint8_tint32; auto.
        eapply symbolic_lemmas.struct_member_rv_flag.
        {
          sep autocancel.
          assert ((msgptrb, msgptro) = get_off_addr (msgptrb, msgptro) Int.zero).
          { unfold get_off_addr; cbn [fst snd]; rewrite Int.add_zero; reflexivity. }
          rewrite <- H78. sep autocancel.
          exact H72.
        }
        all: try reflexivity.
        simpl in H73. tauto.
      }
      {
        intros; unfold_spec. cbn [fst snd].
        sep normal. sep eexists.
        sep autocancel; sep split; eauto.
        rewrite ! Int.add_zero.
        sep name lift msghold in H72.
        eapply Aarray_split_single with (m:=(Z.to_nat (Int.unsigned mlen)))in H72.
        2:{
          unfold CHANNEL_CACHE_SZIE. clear. mauto. 
        }
        2:{
          clear - Hmlensize. unfold Coqlib.nat_of_Z. lia.
        }
        2: rewrite app_length; auto.
        sep autocancel.
        sep name lift Aarray' in H72. unfold Aarray.
        rewrite <- H79.
        sep autocancel. apply H72.
      }
      { go.  }
      { sep_unfold_funpost. intros. sep destruct H72. sep auto. }
      { sep_unfold_funpre. intros. sep destruct H72. sep auto. }
      { pauto. }
    }
    unfold getasrt; unfold OS_memcopyPost, OS_memcopyPost'.
    hoare normal pre. pure intro.
    invertsr H78.
    invertsr H72.
    rewrite ! Int.add_zero.
    hoare abs lift pre.
    (* ++ port_ptr ′ → OSQIn;ₛ *)
    eapply seq_rule.
    {
      eapply port_memeber_asgn; try reflexivity.
      - sep auto. split; intros.
        sep autocancel. exact H72.
        sep auto.
  Optimize Proof.
  Optimize Heap.
      - intros. eapply symbolic_lemmas.bop_rv.
        * sep_get_port_rv.
        * symbolic_execution.
        * simpl. reflexivity.
        * auto.
        * reflexivity.
      - instantiate (1:=14%nat).  reflexivity.
      - eauto.
      - auto.
      - auto.
      - auto.
      - now apply assign_type_match_true.
      - reflexivity.
      - intros. sep auto.
    }
    assert (Int.unsigned (qentries +ᵢ  $ 1) <=? Int16.max_unsigned = true) as Hqentriesrange.
    {
      clear - H52 H69.
      pose proof Int_add_one_Sn qentries ltac:(lia).
      rewrite Z.leb_le. rewrite int16_max_unsigned_val. lia.
    }
    eapply seq_rule.
    {
      eapply port_memeber_asgn; try reflexivity.
      - intros. eapply symbolic_lemmas.bop_rv.
        * eapply port_QEntries_rv. 
          3: { sep autocancel. apply H72. }
          { 
            qportpostproof_tac. 
          }
          { port_nth_val_solve. }
        * symbolic_execution.
        * simpl. reflexivity.
        * auto.
        * reflexivity.
      - instantiate (1:=17%nat). reflexivity.
      - port_nth_val_solve.
      - auto.
      - auto.
      - auto.
      - now apply assign_type_match_true.
      - simpl. now rewrite Hqentriesrange.
      - intros. sep auto.
    }
    (* If (port_ptr ′ → OSQIn ==ₑ port_ptr ′ → OSQEnd)
    {port_ptr ′ → OSQIn =ₑ port_ptr ′ → OSQStart};ₛ *)
    hoare name lift APortStruct pre.
    destruct qendptr as [qendptrb qendptro].
    hoare remember (1::nil)%nat pre.
    apply seq_rule with (APortStruct portptr (update_nth_val 17
    (update_nth_val 14 dport
       (Vptr (dmportp_sllseg_qport_msg_next (qinptrb,qinptro) qstartptr (qendptrb,qendptro))))
    (Vint32 (qentries +ᵢ  $ 1)))**H72).
    {
      eapply ift_rule.
      - intros. eexists. subst H72.
        eapply symbolic_lemmas.bop_rv.
        * eapply port_QIn_rv.
          3:{ sep autocancel. eauto. }
          { 
            qportpostproof_tac. 
          }
          port_nth_val_solve. 
        * eapply port_QEnd_rv.
          3:{ sep autocancel. eauto. }
          { 
            qportpostproof_tac.
          }
          port_nth_val_solve.
        * simpl. reflexivity.
        * destruct (peq qinptrb qendptrb); auto.
          destruct (Int.eq (qinptro +ᵢ  Int.mul ($ 1) ($ 33)) qendptro); auto.
        * reflexivity.
      - intros. 
      eapply sep_aconj_r_aisfalse_to_astar in H78.
      2:{ intros. subst H72.
      eapply symbolic_lemmas.bop_rv.
      * eapply port_QIn_rv.
        3:{ sep autocancel. eauto. }
        { 
          qportpostproof_tac. 
        }
        port_nth_val_solve. 
      * eapply port_QEnd_rv.
        3:{ sep autocancel. eauto. }
        { 
          qportpostproof_tac.
        }
        port_nth_val_solve.
      * simpl. reflexivity.
      * destruct (peq qinptrb qendptrb); auto.
        destruct (Int.eq (qinptro +ᵢ  Int.mul ($ 1) ($ 33)) qendptro); auto.
      * reflexivity.
      }
      sep split in H78.
      destruct H83. 
      2:{ destruct (peq qinptrb qendptrb);
      destruct (Int.eq (qinptro +ᵢ  Int.mul ($ 1) ($ 33)) qendptro); auto; simpl in H1; discriminate. }
      sep cancel H72.
      unfold dmportp_sllseg_qport_msg_next.
      simpl typelen. unfold msg_distance.
      unfold Qport_msg_ptrs_P in H67.
      destruct qstartptr. simpljoin1. unfold get_off_addr in *.
      simpl in H84, H86.
      invertsr H84. invertsr H86.
      cbn [fst snd] in *.
      rewrite ! Int.add_zero_l in *.
      rewrite peq_true in H83.
      destruct (Int.eq (Int.mul ($ x0) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
      (Int.mul ($ Int.unsigned ($ Z.of_nat qsize)) ($ 33))) eqn:E'; [discriminate | ].
      simpl typelen. simpl Z.of_nat.
      assert (
      (qinptrb, Int.mul ($ x0) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)) =
      (if
              Int.unsigned
                (Int.divu
                   (Int.mul ($ Int.unsigned ($ Z.of_nat qsize)) ($ 33) -ᵢ
                    Int.mul ($ x0) ($ 33)) ($ 33)) =? 1
             then (qinptrb, Int.zero)
             else (qinptrb, Int.mul ($ x0) ($ 33) +ᵢ  $ 33))).
      {
        clear - H88 H89 H69 E'.
        destruct (Int.unsigned (Int.divu (Int.mul ($ Int.unsigned ($ Z.of_nat qsize)) ($ 33) -ᵢ Int.mul ($ x0) ($ 33)) ($ 33)) =? 1) eqn:?.
        2: { rewrite (Int.mul_commut ($ 1)).  rewrite Int.mul_one. reflexivity. }
        exfalso.
        assert (exists n,  Int.unsigned ($ Z.of_nat qsize) = n + x0 /\ 1 <= n <= 65536).
        { exists (Int.unsigned ($ Z.of_nat qsize)- x0). split;lia. }
        destruct H as [n [H0 H1]].
        rewrite H0 in Heqb.
        assert (x0 <= 65536) by lia. 
        erewrite  <- (Int.unsigned_repr n) in Heqb at 1.
        rewrite  <- (Int.unsigned_repr x0) in Heqb at 1.  
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
          clear - H1;unfold Int.max_unsigned, Int.modulus, Int.wordsize; cbn; lia.
         }
        rewrite H2 in Heqb.
        rewrite Int.unsigned_repr in Heqb. assert (n = 1) by lia.
        subst n.
        rewrite H0 in E'.
        rewrite <- (Int.unsigned_repr 1) in E' at 2.
        rewrite <- (Int.unsigned_repr x0) in E' at 2.
        rewrite <- Int.add_unsigned in E'.
        rewrite Int.mul_add_distr_l in E'.
        rewrite (Int.add_commut (Int.mul ($ 1) ($ 33))) in E'. 
        rewrite Int.eq_true in E'. discriminate.
        all: rewrite max_unsigned_val; lia.
      }
      rewrite H67 in H78. sep autocancel.
    - intros.
      eapply backward_rule1. 
      eapply sep_aconj_r_aistrue_to_astar.
      { intros. subst H72.
      eapply symbolic_lemmas.bop_rv.
      * eapply port_QIn_rv.
        3:{ sep autocancel. eauto. }
        { 
          qportpostproof_tac. 
        }
        port_nth_val_solve. 
      * eapply port_QEnd_rv.
        3:{ sep autocancel. eauto. }
        { 
          qportpostproof_tac.
        }
        port_nth_val_solve.
      * simpl. reflexivity.
      * destruct (peq qinptrb qendptrb); auto.
        destruct (Int.eq (qinptro +ᵢ  Int.mul ($ 1) ($ 33)) qendptro); auto.
      * reflexivity.
      }
      naive pure intro.
      subst H72.
      hoare evar lift port_ptr pre.
      hoare abs lift pre.
      eapply forward_rule1.
      2:{
        eapply port_memeber_asgn; try reflexivity.
        - intros. eapply port_QStart_rv.
          3:{ sep autocancel. eauto. }
          { 
            qportpostproof_tac. 
          }
          port_nth_val_solve.
        - instantiate (1:=14%nat). reflexivity.
        - port_nth_val_solve.
        - auto.
        - auto.
        - auto.
        - now apply assign_type_match_true.
        - reflexivity.
        - intros. sep auto.
      }
      intros. sep autocancel.
      unfold dmportp_sllseg_qport_msg_next.
      simpl typelen. unfold msg_distance.
      unfold Qport_msg_ptrs_P in H67.
      destruct qstartptr. simpljoin1. unfold get_off_addr in *.
      simpl in H85, H87.
      invertsr H85. invertsr H87.
      cbn [fst snd] in *.
      clear H83 H84.
      rewrite ! Int.add_zero_l in *.
      rewrite peq_true in H78.
      destruct (Int.eq (Int.mul ($ x0) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
      (Int.mul ($ Int.unsigned ($ Z.of_nat qsize)) ($ 33))) eqn:E'.
      2:{
        simpl in H78. congruence.
      }
      simpl typelen. simpl Z.of_nat.
      rewrite aux_pureLib.Int_eq_dec in E'.
      rewrite <- E'.
      rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. 
      rewrite (Int.mul_commut ($ 1)).
      rewrite Int.mul_one.
      assert ((Int.divu ($ 33) ($ 33)) = Int.one)  by (clear;mauto).
      rewrite H67. 
      rewrite Int.unsigned_one.
      rewrite Z.eqb_refl.
      rewrite update_nth_val_diff in H72. 2:lia.
      rewrite update_nth_val_same in H72.
      sep auto.
  Optimize Proof.
  Optimize Heap.
    }
    subst H72.
    (* qportpost_store_one
    (|Vptr portptr
    :: Vptr (msgptrb, msgptro) :: V$ 0 :: V$ Z.of_nat csemid :: vdstc :: nil|) *)
    hoare name lift Aop osdomainportid oskportid oschannelid oscoreheapid pre.
    partition_absrulestac qportpost_store_one_OutCore_cont.
    
    eapply seq_rule.
    {
    apply corecommu_rules.ift_nonzero_rule.
    - intros. eexists.  sep split.
      * symbolic_execution. pauto. rewrite H65. auto.
        rewrite H65. unfold notint. simpl. 
        unfold Int.notbool. rewrite Int.eq_true. reflexivity.
      * clear. mauto. 
    - apply cslsemrel_rule.
      * go. 
      * rewrite Z2Nat.id by apply Int.unsigned_range.
        apply Int.unsigned_range_2.
      * intros.  rewrite Z2Nat.id by apply Int.unsigned_range.
        sep evar lift semaphore in H72.
        rewrite Int.repr_unsigned. symbolic_execution.
        clear - H59. 
        rewrite byte_max_unsigned_val. 
        rewrite <- Z.leb_le in H59. pauto.
      * intros. unfold p_local, CurLINV.
        sep name lift p_local in H72. unfold p_local in H72.
        sep eexists. sep auto.
    }
    hoare name lift Aisr Ais Aier pre.
    eapply backward_rule1.
    apply add_aemp_isr_is_prop.
    hoare abs lift pre.
    (* EXIT_CRITICAL;ₛ *)
    hoare forward prim.
    {
      sep autocancel.
      unfold AOSMapTbl.
      sep autocancel.
      unfold AOSUnMapTbl.
      sep autocancel.
      unfold AOSTCBPrioTbl.
      sep normal.
      sep eexists.
      sep autocancel.
      sep split; auto.
      unfold AOSRdyTblGrp. 
      sep normal.
      sep split; eauto.
      unfold AOSRdyTbl. sep normal.
      sep autocancel.
      sep split; auto.
      unfold AOSRdyGrp. sep normal.
      sep autocancel. sep split; auto.
      unfold AOSTime. sep autocancel.
      unfold AGVars. sep normal.
      sep eexists. sep autocancel.
      sep split; auto.
      sep name lift PartitionInv.
      apply fold_PartitionInv_frm.
      sep autocancel.
      sep cancel CapabilityInv.
      (* cancel TmrInv *)
      unfold TmrInv, HeapInv'.
      sep normal; sep eexists; sep autocancel.
      sep split; auto.
      eapply AOScoreheapl_merge.
      instantiate (1:= S (length msg)).
      lia. auto. reflexivity. lia. auto.
      sep autocancel.
      cbn [Aarray Aarray']. 
      sep normal. sep autocancel.
      simpl typelen. simpl Z.of_nat. 
      unfold Aarray at 2 in H72.
      rewrite H81. sep autocancel.
      (* cancel PartitionInv *)
      unfold PartitionInv_part1.
      sep normal; sep eexists; sep pauto.
      sep cancel AOSChannelFreeList.
      sep cancel AOSKernelPortFreeList.
      sep cancel OtherPortPtrList.
      sep name lift AOSCorePortPtrList in H72.
      sep name lift AOSCorePortPtrList.
      unfold AOSCorePortPtrList in H72.
      unfold AOSCorePortPtrList.
      sep normal. sep normal in H72.
      sep cancel OSCorePortPtrList.
      apply sep_pure_split in H72. destruct H72 as (Hnew&H72).
      apply astar_l_apure_intro.
      2:{
        instantiate(1:=(set dportls1 portptr
        (Z.to_nat DNUM, Z.to_nat (Int.unsigned x2), Z.to_nat (Int.unsigned portid), SourceP,
        Z.to_nat (Int.unsigned x4), Z.to_nat (Int.unsigned x5), Z.to_nat (Int.unsigned x6),
        QueuePort qsize (x14 ++ msg :: nil)))).
        eapply RH_CorePortPtrList_upd_dportls; eauto.
      }
      2: eauto.
      5: eauto.
      sep name lift AOSChannelIDTbl.
      unfold AOSChannelIDTbl.
      sep normal. sep autocancel.
      sep split; try tauto.
      eapply ChannelNode_compose.
      instantiate (1:= chanl1). congruence.
      instantiate (1:=chandstkportll1).
      congruence.
      instantiate(2:= (Vint32 chanid
      :: V$ 1
         :: V$ 0
            :: V$ Z.of_nat csemid
               :: Vnull
                  :: x15
                     :: Vptr (kportpb, Int.zero) :: x17 :: nil)).
      reflexivity. 
      reflexivity.
      pauto.
      sep autocancel.
      unfold AOSKernelPortIDTbl. sep normal.
      sep autocancel. sep split; auto.
      5: instantiate (3 := dportlptr).
      5: instantiate (2 := (dportl1++ (update_nth_val 17
      (update_nth_val 14 dport
         (Vptr
            (dmportp_sllseg_qport_msg_next
               (qinptrb, qinptro) qstartptr
               (qendptrb, qendptro))))
      (Vint32 (qentries +ᵢ  $ 1))):: dportl2)).
      8: eapply map_tactics.join_set_set; eauto.
      7: instantiate (1:= dpptrl).
      unfold AOSDomainPortPtrList. sep normal.
      sep autocancel.
      instantiate (2:= (dportmsgll1++ (x14++(msg::nil))::dportmsgll2)).
      rewrite dmportp_sllseg_app'_frm. sep autocancel.
      cbn [dmportp_sllseg]. sep normal. sep eexists.
      sep split.
      2,4: port_nth_val_solve.
      2:{
        qportpostproof_tac.
      }
      sep autocancel.
      apply disj_star_elim_disj'. right.
      sep normal. sep eexists.
      sep split. 3,4: splits.
      3,5,7-10: port_nth_val_solve.
      8: eauto.
      5-7: congruence. 4: auto.
      assert ((Init.Nat.pred
      ∘ (Int.unsigned ($ Z.of_nat qsize) - Int.unsigned qentries))= ∘ (Int.unsigned ($ Z.of_nat qsize) - Int.unsigned (qentries +ᵢ  $ 1))).
      {
          unfold Coqlib.nat_of_Z.
          rewrite <- Z2Nat.inj_pred.
          f_equal.
          rewrite <- Z.sub_1_r. 
          rewrite <- Z.sub_add_distr. f_equal.
          symmetry.
          apply Int_add_one_Sn'.
          clear - H18 H66.
          unfold OS_Port_Seg_dls in H18.
          struct_type_vallist_match'_elim.
          inverts H66. lia.
        }
      rewrite <- H94. clear H94. sep autocancel.
      eapply dmportp_sllseg_qport_msg_append_tail; eauto.
      lia. sep eexists.
      sep autocancel. sep split; auto. apply H72.
      {
        erewrite <- firstn_skipn in H80.
        apply array_type_vallist_match_app.
        simpl in H73. split. tauto.
        apply array_type_vallist_match_app in H80. jauto.
      }
      {
        eapply Qport_msg_ptrs_P_hold; eauto. 
      }
      {
        rewrite Int_add_one_Sn'. lia.
        lia. 
      }
      {
        apply nth_error_split in H14. simpljoin.
        eapply RL_PortPtrList_upd; eauto.
        unfold OS_Port_V_nextPort.
        rewrite nth_val_update_nth_val_diff;[ |lia].
        apply nth_val_update_nth_val_diff. lia.
      }
      {
        eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto. 
      }
      {
        apply nth_error_split in H14. simpljoin.
        eapply R_Kernelport_DomainPort_upd; eauto.
        unfold OS_Port_V_portID.
        rewrite nth_val_update_nth_val_diff;[ |lia].
        apply nth_val_update_nth_val_diff. lia.
        unfold OS_Port_V_coreNum.
        rewrite nth_val_update_nth_val_diff;[ |lia].
        apply nth_val_update_nth_val_diff. lia.
      }
      {
        eapply RLH_Channel_upd_dportls1; eauto.
        right. jauto. 
      }
      {
        apply nth_error_split in H14. simpljoin.
        eapply RLH_Domainportl_upd_Queue'; eauto.
        congruence.
        lets HH: RLH_Domainportl_abs_getsome H3 H4 H10.
        simpljoin.
        assert (x3=length x).
        { assert (nth_error (x++portptr::x0) (length x) = Some portptr).
          apply nth_error_middle.
          eapply dpptrl_not_same_elements; eauto. }
        subst x3.
        setoid_rewrite H95 in H14.
        rewrite nth_error_middle in H14.
        invertsr H14.
        assert (length x = length dportmsgll1) by congruence.
        rewrite H14 in H96.
        rewrite nth_error_middle in H96.
        inverts H96.
        auto.
  Optimize Proof.
  Optimize Heap.
      }
      { 
        unfold RLH_PortPtrINecb.
        splits.
        apply nth_error_split in H14. simpljoin.
        eapply RL_PortPtrList_upd; eauto.
        unfold OS_Port_V_nextPort.
        rewrite nth_val_update_nth_val_diff;[ |lia].
        apply nth_val_update_nth_val_diff. lia.
        rewrite Forall_forall.
        intros. 
        rewrite Forall_forall in H11.
        apply H11 in H95.
        easy.
      }
      {
        apply nth_error_split in H14. simpljoin.
        eapply RL_PortAttr_upd; eauto.
        unfold OS_Port_V_direction.
        rewrite nth_val_update_nth_val_diff;[ |lia].
        apply nth_val_update_nth_val_diff.
        lia.
        unfold OS_Port_V_mode.
        rewrite nth_val_update_nth_val_diff;[ |lia].
        apply nth_val_update_nth_val_diff.
        lia. 
      }
    }
    auto.
    go.
    hoare forward.
  }
  (* 核内通信 *)
  {
    simpljoin.
    unfold Channel in H46, H65;
    rewrite H46 in H65; inverts H65.
    unfold Channel_type_P in H71; simpljoin1.
    unfold OS_Channel_V_semaphore in H29. simpl in H29. inverts H29.
    remember (v1::v') as vsdstcl.
    clear v1 v' Heqvsdstcl.
    hoare name lift Aisr Ais aemp_isr_is pre.
    eapply backward_rule1.
    apply elim_aemp_isr_is_prop.

    (* semaphore ′ =ₑ channel ′ .. semaphore;ₛ *)
    hoare forward.
    { pauto. }

    (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
    {CSLSEMACC (semaphore ′, resource_get_res ′);ₛ
    If (resource_get_res ′ ==ₑ 〈 char_t 〉 ′ 0)
    {EXIT_CRITICAL;ₛ
    RETURN 〈 char_t 〉 ′ OS_CHANNEL_ERR_BEING_USED}};ₛ *)
    eapply seq_rule.
    {
      apply corecommu_rules.ift_zero_rule. symbolic_execution.
    }

    (* dstKPort ′ =ₑ channel ′ .. dstPortsHead;ₛ *)
    hoare forward.
    { pauto. }
    rename v'27 into dstkport.

    destruct H48.
    2:{
      unfold R_KernelPortIDTbl_ChannelIDTbl_OutcoreC in H29; simpljoin1.
      unfold OS_Channel_V_semaphore in H29; simpl in H29.
      inverts H29. 
      exfalso; clear - H48.
      rewrite Int.eq_true in H48. discriminate.
    }
    unfold R_KernelPortIDTbl_ChannelIDTbl_IncoreC in H29; simpljoin1.
    unfold OS_Channel_V_semaphore in H29; simpl in H29. inverts H29.
    destruct H48.
    2:{
      exfalso.
      unfold R_KernelPortIDTbl_ChannelIDTbl_dst in H29; simpljoin1.
      clear - H1 H10 H29.
      setoid_rewrite H10 in H29. inverts H29.
    }
    unfold R_KernelPortIDTbl_ChannelIDTbl_scr in H29; simpljoin1.
    unfold port_id in H10; rewrite H10 in H29; inverts H29.
    unfold OS_Channel_V_srcPort in H48; simpl in H48; inverts H48.
    
    destruct H71; simpljoin1.
    {
      exfalso.
      unfold Channel_srckport_Sample in H48; simpljoin1.
      destruct H48; simpljoin1;
      unfold OS_Channel_V_srcPort in H48; simpl in H48; inverts H48.
      unfold addrval, port_id in H25, H73; rewrite H25 in H73; inverts H73.
      unfold addrval, port_id in H10, H74; rewrite H10 in H74; inverts H74.
    }
    unfold Channel_srckport_Queue in H48; simpljoin1.
    unfold OS_Channel_V_srcPortsNum in H72; simpl in H72; inverts H72.
    destruct H48; simpljoin1.
    { unfold OS_Channel_V_srcPortsNum in H71;
      simpl in H71; inverts H71. }
    unfold OS_Channel_V_srcPort in H48; simpl in H48; inverts H48.
    unfold addrval, port_id in H25, H72; rewrite H25 in H72; inverts H72.
    rename x3 into portptr. clear H71.
    unfold addrval, port_id in H10, H73; rewrite H10 in H73; inverts H73.
    
    unfold nat_of_Z in *.
    assert (dpnum = ($ (Z.of_nat (length dstkportpl)))).
    {
      clear - H53 H75.
      rewrite <- H75.
      rewrite Z2Nat.id by (apply Int.unsigned_range).
      rewrite Int.repr_unsigned.
      reflexivity.
    }
    assert ((Int.unsigned dpnum) = Z.of_nat (length dstkportpl)).
    {
      clear - H75.
      rewrite <- H75.
      rewrite Z2Nat.id by (apply Int.unsigned_range).
      reflexivity.
    }
    rewrite H75 in *.
    rewrite <- H48 at 1; try rewrite H71 at 1; try rewrite Nat2Z.id at 1.

    (* If (dstKPort ′ !=ₑ 〈 OS_K_Port ∗ 〉 NULL)
    {WHILE (dstKPort ′ !=ₑ 〈 OS_K_Port ∗ 〉 NULL)
    {error ′ =ᶠ OSQSendToDomain (·dstKPort ′ .. dmport,
      msg_ptr ′, port_ptr ′ .. msgInTick·);ₛ
    dstKPort ′ =ₑ 〈 OS_K_Port ∗ 〉 dstKPort ′ .. OSEventPtr;ₛ
    If (error ′ !=ₑ ′ OS_NO_ERR){error ′ =ₑ ′ OS_ERR_DSTPORT_FULL}};ₛ *)
    hoare forward.
    clear - H60;  pauto.
    pauto.
    pauto.
    { instantiate (1:=Afalse).
      rename H into HRH_TCB_ECB.
      rename H0 into HRH_curTCB.
      rename H1 into Hjoin_dport.
      rename H3 into HRL_PortPtrList.
      rename H2 into HRL_PortAttr.
      rename H11 into Hdpptrl_ecb.
      rename H4 into HRLH_domainport.
      rename H22 into Hnrr_kportp.
      rename H5 into HRLH_Kernelport.
      rename H6 into HRLH_Channel.
      rename H8 into HR_Kernel_Channel.
      rename H7 into HR_Kernel_Domain.
      rename H9 into HRLHOther.
      rename H14 into Hnrr_portptr.
      rename Hpptr into Hgetportptr. clear H10.
      rename H17 into Hlen_dportmsgll1_dportl1.
      rename H15 into Hdport_V_coreNum.
      rename H31 into Hdport_V_domain.
      rename H33 into Hdport_V_portID.
      rename H35 into Hportid_lt_portnums.
      rename H36 into Hdport_V_status.
      rename H38 into Hdport_V_intick.
      rename H40 into Hdport_V_outtick.
      rename H47 into Hdport_V_qsize.
      rename H70 into Hdport_V_mode.
      rename H28 into Hdport_V_direction.
      rename H13 into Hdport_V_nextport.
      rename H18 into Hdport_type_match.
      rename H19 into Hdport_V_start.
      rename H16 into Hkporttbl_nodup.
      rename H20 into Hlen_kport_portnums.
      rename H12 into Hkportpl_type_match.
      rename H23 into Hnrr_kport.
      rename H24 into Hportid_range.
      rename H30 into Hchanid_range.
      clear H32.
      rename H37 into HDNUM_range.
      rename H39 into Hx1_range.
      rename H41 into Hx8_isptr.
      rename H42 into Heq_kportl1_portid.
      rename H27 into Heq_kportpl1_portid.
      rename H43 into Hkport_type_match.
      rename H25 into Hget_kport.
      rename H65 into Hkportp_notin_dstp.
      rename H45 into Hnrr_dstkportpl.
      rename H44 into Hnrr_chan.
      rename H34 into Hnrr_chanp.
      rename H21 into Hchanp_type_match.
      rename H49 into Heq_chanpl_channelnums.
      rename H26 into Hchanp_nodup.
      clear H51 H52 H62. 
      rename H58 into Hlen_chandstkportll1_chanid.
      rename H57 into Hlen_chanl1_chanid.
      rename H54 into Hlen_chanpl1_chanid.
      rename H53 into Hdpnum_range.
      rename H59 into Hcsemid_range.
      rename H60 into Hdstkport_isptr.
      rename H61 into Hx15_isptr.
      rename H63 into Hx17_isptr.
      rename H55 into Hdport_V_End.
      rename H56 into Hdport_V_in.
      rename H64 into Hdport_V_out.
      rename H69 into Hx13_range.
      rename H66 into Hdport_V_entries.
      rename H67 into HQport_msg_ptrs.
      rename H75 into Hlen_dpnum_dstkportpl.
      rename H46 into Hget_chan.
      rename H29 into Hchannel_dstk_Queue_Inc.
      rename H50 into Hkportls_nodup.
      rename x13 into qsize.
      rename H68 into Hqentries_leqsize.
      rename H48 into Heq_dpnum_dstkportpl.
      rename H71 into Heq_dpnum_dstkportpl'.

      hoare normal pre; pure intro.
      destruct Hdstkport_isptr as [?|[headptr Hheadptr_isptr]]; subst.
      exfalso; clear - H; mauto.
      clear H H0 H1.
      unfold TmrInv, HeapInv'.
      pure intro.
      hoare name lift osdomainport oskport oschannel oscoreheapid pre.
      rename v' into cheapl.
      rename v'20 into cheape.
      rename v'21 into cheapt.
      partition_absrulestac absinfer_choice2.
      assert (
        ~ ( exists mlen msg,
          Get_heapl_addrval cheapl msgptr (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\
          (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z ) \/
        ( exists mlen msg,
              Get_heapl_addrval cheapl msgptr (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\
              (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z )
      ) as [ | ] by tauto.
      {
        partition_absrulestac qportpost_msg_in_heapl_abt.
        apply absabort_rule.
      }
      simpljoin1.
      rename x into mlen. rename x0 into msg.
      rename H2 into Hget_heapl_msg.
      rename H3 into Hmlen_le_chche_size.
      partition_absrulestac qportpost_msg_in_heapl_cont.
      (* split AOScoreheapl *)
      hoare name lift AOScoreheapl pre.
      eapply backward_rule1.
      {
        eapply Get_heapl_addrval_split_coreheapl; eauto.
      }
      naive pure intro.
      rename v' into cheapl1. rename v'20 into cheapl2.
      rename v'21 into heapmsglen. rename v'22 into irheapmsg. 
      simpljoin1.
      rewrite <- H6. simpl length. rename H3 into Hmsg_type_match.
      rename H4 into Hmsg_heap_max_len.
      rename H6 into HSmlen.
      rename H into Hheapl_nodup.
      rename H0 into Hheape_nodup.
      rename H1 into Hheapt_nodup.
      cbn [Aarray Aarray'].
      destruct msgptr as [msgptrb msgptro].
      partition_absrulestac absinfer_choice1.
      
      
      (* WHILE (dstKPort ′ !=ₑ 〈 OS_K_Port ∗ 〉 NULL)
      {error ′ =ᶠ OSQSendToDomain (·dstKPort ′ .. dmport, msg_ptr ′·);ₛ
      dstKPort ′ =ₑ 〈 OS_K_Port ∗ 〉 dstKPort ′ .. OSEventPtr;ₛ
      If (error ′ !=ₑ ′ OS_NO_ERR){error ′ =ₑ ′ OS_ERR_DSTPORT_FULL}};ₛ *)
      hoare normal pre.
      hoare name lift dstKPort pre.
      hoare name lift Channel_dstkport_get pre.
      hoare name lift osdomainport pre.
      hoare name lift dmportp_sllseg pre.

      
      eapply backward_rule1.
      eapply dmportp_sllseg_Forall_struct_type_vallist_match'.
      naive pure intro.
      rename H into Hdportl_type_match.
     
      assert (
          forall n, (n < length dstkportpl)%nat ->
            exists dstkportp dstportp dstpptrn dstpid dstkpst
                dstpd dstpst dstpin dstpout dstsz, 
                exists dstpm  dstport nextdst,
              nth_error dstkportpl n = Some dstkportp /\
              nth_error dpptrl dstpptrn = Some dstportp /\
              nth_error (dportl1 ++ dport :: dportl2) dstpptrn = Some dstport /\
              get kportls dstkportp =
                Some (dstpid, Some dstportp, Some (chanpb, Int.zero), nat_of_Z DNUM, dstkpst) /\
              get dportls1 dstportp = 
                Some (nat_of_Z DNUM, dstpd, dstpid,
                  DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz dstpm)
      ) as Hnhypo.
      { 
        eapply dstkportpl_get_Queue_Incore; eauto. }
      eapply seq_rule.
      {
        hoare name lift osdomainportid pre.
        hoare name lift dmportp_sllseg pre.
        hoare name lift Channel_dstkport_get pre.
        hoare name lift dstKPort pre.
        hoare evar lift error pre.
        hoare abs lift pre.
        hoare name lift AOSMapTbl AOSUnMapTbl AOSTCBPrioTbl AOSTCBList AOSRdyTblGrp pre.
        hoare name lift oscurt abstcblist EvtInv CoreCommuInv tcbdllflag pre.
        rename v'1 into p1.
        rename v'3 into tcbl1.
        rename v'4 into tcbcur.
        rename v'5 into tcbl2.
        rename v'9 into tcbls.
        rename v'11 into vhold.
        rename v'0 into ptbl.
        rename v'6 into rtbl.
        rename v'7 into rgrp.
        rename v'2 into p2.
        hoare name lift AOSCorePortPtrList pre.

        hoare remember (1::2::3::4::5::6::7::8::9::10::11::12::13::14::15::16::17::nil)%nat pre.
        eapply backward_rule1.
        {
          instantiate(1:=
          EX n ndkpv ndportl ndportmsgll ndportls1 ndportls errv  ntcbls necbls nrtbl
          ntcbl1 ntcbcur ntcbl2 nrgrp nptls,
          ( [| ndkpv = Vnull |] ** [| n = length dstkportpl |] \\//
            EX ndkpptr, [| ndkpv = Vptr ndkpptr |] **
            [| nth_error dstkportpl n = Some ndkpptr |]  ) **
          AOSCorePortPtrList v'41 v'42 ndportls1 **
          LV error @ char_t |-> Vint32 errv  **
          [| errv = Int.repr OS_NO_ERR \/ errv = Int.repr OS_ERR_DSTPORT_FULL |] **
          [| forall m kp dp a1 a2 a3 a4, (n<=m)%nat -> nth_error dstkportpl m = Some kp -> 
            get kportls kp = Some (a1, Some dp, a2, a3, a4) -> get ndportls1 dp = get dportls1 dp|] **
          [| get ndportls1 portptr = get dportls1 portptr |] **
          <||
          spec_code_cons (qportpost_send_Incore ((length dstkportpl) - n)%nat
            (Vptr portptr
            :: Vptr (msgptrb,msgptro)
                :: V$ Z.of_nat (length dstkportpl)
                  :: Vnull :: vsdstcl))
                  (isched;; 
                  (END Some (V$ OS_NO_ERR) ?? END Some (V$ OS_ERR_DSTPORT_FULL))) ||>  **
          LV dstKPort @ OS_K_Port ∗ |-> ndkpv **
          Channel_dstkport_get (Vptr headptr) Vnull (length dstkportpl) dstkportpl **
          dmportp_sllseg dportlptr Vnull ndportl ndportmsgll OS_Port_V_nextPort **
          Hdomainportl ndportls **
          [| join ndportls1 dportls2 ndportls |] **
          [| RLH_Channel otherppl
              (chanpl1 ++ Vptr (chanpb, Int.zero) :: chanpl2)
              (chanl1 ++ (Vint32 chanid :: V$ 1 :: V$ Z.of_nat (length dstkportpl)
               :: V$ DEFAULT_CHANNLE_SEMAPHROE :: Vptr headptr :: x15 :: Vptr (kportpb, Int.zero) :: x17 :: nil) :: chanl2)
              (chandstkportll1 ++ dstkportpl :: chandstkportll2) chanls
              kportls ndportls1 dportls2 |] **
          [| R_KernelPortIDTbl_ChannelIDTbl
              (kportpl1 ++ Vptr (kportpb, Int.zero) :: kportpl2)
              (kportl1 ++
              (Vint32 portid
                :: Vint32 chanid
                  :: Vptr portptr
                      :: Vptr (chanpb, Int.zero)
                        :: V$ DNUM :: Vint32 x1 :: x8 :: nil) :: kportl2)
              (chanpl1 ++ Vptr (chanpb, Int.zero) :: chanpl2)
              (chanl1 ++
              (Vint32 chanid
                :: V$ 1
                  :: V$ Z.of_nat (length dstkportpl)
                      :: V$ DEFAULT_CHANNLE_SEMAPHROE
                        :: Vptr headptr
                            :: x15
                              :: Vptr (kportpb, Int.zero) :: x17 :: nil)
              :: chanl2)
              (chandstkportll1 ++ dstkportpl :: chandstkportll2) kportls
              ndportls1 dportls2 |] **
          [| RL_PortAttr dpptrl ndportl |] **
          [| RLH_Domainportl dportlptr ndportl ndportmsgll ndportls1 |] **
          [| Channel_dstkport_Queue_IncoreC otherppl 
              (chanpb, Int.zero) dstkportpl kportls ndportls1 |] **
          [| R_Kernelport_DomainPort (kportpl1 ++ Vptr (kportpb, Int.zero) :: kportpl2)
          (kportl1 ++
           (Vint32 portid
            :: Vint32 chanid
               :: Vptr portptr
                  :: Vptr (chanpb, Int.zero)
                     :: V$ DNUM :: Vint32 x1 :: x8 :: nil)
           :: kportl2) ndportl dpptrl |] **
          [| RLH_PortPtrINecb dportlptr ndportl dpptrl necbls |] **
          AOSMapTbl **
          AOSUnMapTbl **
          AOSTCBPrioTbl ptbl nrtbl ntcbls nptls vhold **
          AOSTCBList p1 p2 ntcbl1 (ntcbcur::ntcbl2) nrtbl tid ntcbls **
          AOSRdyTblGrp nrtbl nrgrp **
          HTCBList ntcbls ** HCurTCB tid **
          EvtInv necbls p1 (ntcbl1++(ntcbcur::ntcbl2)) ntcbls vhold v'17 v'18 v'19**
          [| RH_TCBList_ECBList_P necbls ntcbls tid |] **
          [| RH_CurTCB tid ntcbls |] **
          CoreCommuInv necbls **
          tcbdllflag p1 (ntcbl1++(ntcbcur::ntcbl2)) **
          H
          ).
          {
            intros.
            exists 0%nat (Vptr headptr) (dportl1 ++ dport :: dportl2) (dportmsgll1 ++ x14 :: dportmsgll2) dportls1; exists dportls (Int.repr OS_NO_ERR).
            exists tcbls ecbls rtbl tcbl1 tcbcur. exists tcbl2 rgrp. exists v'14.
            sep normal.
            apply disj_split; right.
            destruct dstkportpl; cbn [length ] in *.
            unfold Channel_dstkport_get in H0; sep split in H0; tryfalse.
            cbn [Channel_dstkport_get] in *.
            sep normal in H0; sep destruct H0; sep split in H0. invertsr H3.
            sep normal. exists headptr.
            sep eexists; sep split; eauto.
            sep autocancel.
            rewrite H4. rewrite Heq_dpnum_dstkportpl'.
            repeat f_equal.
            rewrite Nat2Z.id. reflexivity.
            unfold RLH_PortPtrINecb.
            splits; auto.
          }
        }
        subst H.
        eapply while_rule.
        {
          intros.
          sep destruct H.
          apply disj_split in H.
          destruct H.
          symbolic execution.
          symbolic execution.
          destruct x23; pauto.
          destruct x23; pauto.
        }
        (* Loop Body *)
        naive pure intro.
        rename v' into n. rename v'0 into ndkpv.
        eapply aconj_aistrue_rule.
        {
          intros.
          sep destruct H.
          apply disj_split in H.
          instantiate (1:=val_inj (notint (val_inj (val_eq ndkpv Vnull)))).
          destruct H; sep normal in H; sep split in H.
          symbolic execution.
          symbolic execution.
          destruct x; pauto.
          unfold val_eq; destruct x; pauto.
        }
        naive pure intro.
        eapply backward_rule1.
        intros s Hs; eapply disj_split in Hs; apply Hs.
        eapply disj_rule.
        { naive pure intro. exfalso. subst. clear - H14; pauto. }
        naive pure intro.
        rename v' into dstkportp. subst ndkpv.
        clear H14.
        rename H0 into Hnrr_dstkport.
        rename H1 into Herrv.
        rename H2 into Hdportls1_dportls1'.
        rename v'3 into dportls1'.
        rename v'4 into dportls'.
        rename H3 into Hget_dportls1'_portptr.
        rename H4 into Hjoin_dport'.
        rename H5 into HRLH_Channel'.
        rename H6 into HR_Kernel_Channel'.
        rename v'5 into errv.
        apply nth_error_split in Hnrr_dstkport as (dstkportpl1 & dstkportpl2 & ? & ?).
        subst dstkportpl n.
        rename v'1 into dportl'.
        rename v'7 into tcbls'.
        rename v'6 into ecbls'.
        rename H7 into HRL_PortAttr'.
        rename H8 into HRLH_domainportl'.
        rename H9 into HChannel_dstkport_Queue_IncoreC'.
        rename H10 into HR_Kernel_Domain'.
        rename H11 into HRLH_PortPtrINecb'.
        rename H12 into HRH_TCBList_ECBList_P'.
        rename H13 into HRH_CurTCB'.
        
        hoare name lift Channel_dstkport_get pre.
        eapply backward_rule1.
        eapply Channel_dstkport_get_app_frm; eauto.
        naive pure intro. 
        rename v'0 into nextdstkport.
        rename v' into dstkport'.
        rename H into Hdstkport'_type_match.
        rename H0 into Hdstkport'_V_EventPtr.
        assert ((length (dstkportpl1 ++ dstkportp :: dstkportpl2) - length dstkportpl1)%nat = S (length dstkportpl2)).
        clear; induction dstkportpl1; simpl; try lia.
        rewrite H. clear H.
        assert ((S (length dstkportpl2) - 1)%nat = length dstkportpl2) by (clear; mauto).
        rewrite H. clear H.
        hoare name lift msg_ptr pre.
        assert ((length dstkportpl1 <
        length (dstkportpl1 ++ dstkportp :: dstkportpl2))%nat) as Hdstkportpl1_lt_dstkportl.
        clear; induction dstkportpl1; simpl; try lia.
        pose proof Hnhypo _ Hdstkportpl1_lt_dstkportl.
        simpljoin1.
        rewrite nth_error_middle in H. invertsr H. 
        rename x0 into dstportp.
        rename x16 into dstsz.
        rename x18 into dstpm.
        rename x3 into dstportn.
        rename v'2 into dportmsgll'.
        rename x19 into dstport.
        rename H0 into Hnrr_dstportp.
        rename H1 into Hnrr_dstport.
        rename H2 into Hget_dstkportp.
        rename H3 into Hget_dstportp.
        rename v'11 into tcbl1'.
        rename v'20 into tcbcur'.
        rename v'21 into tcbl2'.
        rename v'22 into rgrp'.
        rename v'9 into rtbl'.
        rename v'14 into ptls.
        rename v'23 into ptls'.
        (* find ndstkport in kportNode_P *)
        hoare name lift kportNode_P pre.
        pose proof RLH_Kernelport_abs_getsome' _ _ _ _ _ _ _ _ _ Hget_dstkportp HRLH_Kernelport.
        simpljoin1.
        rename x0 into dstkport.
        rename H into Hnrr_dsrkportp.
        rename H0 into Hnrr_dstkport.
        rename H1 into HKernelportNode_P_dstkport.
        eapply backward_rule1.
        eapply kportNode_P_getsome_frm; eauto.
        naive pure intro.
        rename v' into dstkportpb.
        rename v'0 into kportpl1'. rename v'1 into kportpl2'.
        rename v'2 into kportl1'. rename v'3 into kportl2'.
        simpljoin.
        rename H4 into Hdstkport_type_match.
        rename H0 into Hkportpl_kportpl'.
        rename H1 into Hkportl_kportl'.
        rename H3 into Hlen_kportl1'_kportpl1'.
        unfold KernelportNode_P in HKernelportNode_P_dstkport.
        destruct HKernelportNode_P_dstkport as (HKernelportNode_nat_P_dstkport&
        HKernelportNode_dmport_P_dstkport& HKernelportNode_channel_P_dstkport).
        unfold Kernelport_dmport_P in HKernelportNode_dmport_P_dstkport.
        assert (nth_val' 2 dstkport = Vptr dstportp) as Hnval_dstportp.
        {
          clear - Hdstkport_type_match HKernelportNode_dmport_P_dstkport.
          struct_type_vallist_match_elim.
          inverts HKernelportNode_dmport_P_dstkport.
          reflexivity.
        }
        
        (* error ′ =ᶠ OSQSendToDomain (·dstKPort ′ .. dmport, msg_ptr ′·);ₛ *)

        eapply seq_rule.
        {
          eapply calle_rule_lvar'.
          { reflexivity. }
          {
            (* RV *)
            intros. 
            eapply rvl_elim.
            {
              eapply dstKPort_dmport_rv.
              2:{ sep autocancel. apply H. }
              auto.
  Optimize Proof.
  Optimize Heap.
            }
            eapply rvl_elim; [symbolic execution| ].
            apply rvl_nil.
          }
          {
            (* ==>pre *)
            unfold getasrt, OSQSendToDomainPre, OSQSendToDomainPre'.
            intros.
            apply disj_split.
            right.
            sep normal.
            sep eexists.
            sep cancel Aop.
            sep cancel dmportp_sllseg.
            sep autocancel.
            sep split; eauto.
            4:{
              erewrite Hdportls1_dportls1';[eauto|..]. 
              3:{ apply Hget_dstkportp. }
              2: apply nth_error_middle.
              lia.
            }
            - cbn [Aarray Aarray']. sep normal. sep autocancel. apply H.
            - rewrite <- HSmlen in Hget_heapl_msg. auto.
            - now rewrite Hnval_dstportp.
          }
          { go. }
          {
            unfold retpost. intros.
            unfold getasrt, OSQSendToDomainPost, OSQSendToDomainPost' in H.
            destruct H; sep destruct H; sep split in H.
            - clear - H0. destruct H0; simpljoin; auto.
            - clear - H0. destruct H0; simpljoin; subst; auto.
          }
          { rewrite Hnval_dstportp. pauto.  }
          {
            unfold getasrt, OSQSendToDomainPost, OSQSendToDomainPost'.
            intros. sep destruct H.
            destruct H; sep normal in H; sep destruct H; sep eexists; sep auto.
          }
          {
            unfold getasrt, OSQSendToDomainPre, OSQSendToDomainPre'.
            intros. sep destruct H.
            destruct H; sep normal in H; sep destruct H; sep eexists; sep auto.
          }
        }
        rewrite Hnval_dstportp.
        
        (* Unfold Post*)
        unfold getasrt, OSQSendToDomainPost, OSQSendToDomainPost'.
        naive pure intro.
        
        (* disj *)
        eapply backward_rule1.
        intros. apply disj_split in H; apply H.
        apply disj_rule.
        {
          naive pure intro.
          inverts H7.
        }
        naive pure intro.
        invertsr H10.
        invertsr H6.
        subst v'7.
        rename v'35 into dportls1''.
        rename v'36 into dportls''.
        rename v'28 into dportl''.
        rename v'29 into dportmsgll''.
        rename v'69 into ecbls''.
        rename v'73 into tcbls''.
        rename v'67 into rtbl''.
        rename v'68 into rgrp''.
        rename v'70 into tcbl1''.
        rename v'71 into tcbcur''.
        rename v'72 into tcbl2''.
        rename v'65 into ptls''.
        rename H into Hdportls1''.
        rename H0 into HRL_PortAttr''.
        rename H1 into HRLH_domainportl''.
        rename H2 into R_Kernelport_DomainPort''.
        rename H3 into Hchannel_dstkport_Queue_IncoreC''.
        rename H5 into HRLH_PortPtrINecb''.
        rename H9 into HR_Kernel_Channel''.
        rename H8 into HRLH_Channel''.
        rename H7 into Hjoin_dport''.
        rename H11 into HRH_TCBList_ECBList_P''.
        rename H12 into HRH_CurTCB''.
        
        (* dstKPort ′ =ₑ 〈 OS_K_Port ∗ 〉 dstKPort ′ .. OSEventPtr *)
        eapply seq_rule.
        {
          eapply assign_rule_lvar.
          { split; [ | sep pauto]. sep pauto. }
          {
            intros.
            eapply symbolic_lemmas.cast_rv_tptr with (v:= nextdstkport) (t1:= Void).
            2: { clear - Hdstkport'_type_match Hdstkport'_V_EventPtr. 
            struct_type_vallist_match_elim. inverts Hdstkport'_V_EventPtr.
            pauto.
            }
            eapply symbolic_lemmas.struct_member_rv_flag; eauto.
            { sep cancel dstKPort. sep autocancel. apply H. } 
            1-3: reflexivity.
            { clear - Hdstkport'_type_match Hdstkport'_V_EventPtr. 
              struct_type_vallist_match_elim. inverts Hdstkport'_V_EventPtr.
              pauto.
            }
          }
          { now apply assign_type_match_true. }
          { intros; sep eexists; sep cancel p_local; sep pauto. }
        }
        (* If (error ′ !=ₑ ′ OS_NO_ERR)
          {error ′ =ₑ ′ OS_ERR_DSTPORT_FULL} *)
        hoare evar lift error pre.
        hoare remember (1::nil)%nat pre.
        eapply forward_rule1 with
        (EX errv, LV error @ char_t |-> Vint32 errv ** [| errv = $ OS_NO_ERR \/ errv = $ OS_ERR_DSTPORT_FULL |] ** H ).
        2:{
          destruct Hdportls1''; simpljoin.
          - inverts H1. 
            apply corecommu_rules.ift_nonzero_rule.
            2:{ hoare forward. }  
            intros. exists Int.one.
            sep split. symbolic_execution.
            destruct (Int.eq_dec (Int.one) (Int.zero));[discriminate| ].
            now apply Int.eq_false.
          - destruct H0.
            * inverts H. inverts H1.
              eapply forward_rule1.
              2:{
                apply corecommu_rules.ift_zero_rule.
                symbolic_execution.
              }
              intros.
              sep eexists. sep autocancel.
              sep auto.
            * inverts H1. 
              eapply forward_rule1.
              2:{
                apply corecommu_rules.ift_zero_rule.
                symbolic_execution.
              }
              intros.
              sep eexists. sep autocancel.
              sep auto.
        }
        (* To loop invariant *)
        intros.
        sep destruct H0.
        rename x into errv''.
        subst H.
        exists (S (length dstkportpl1)).
        eexists.
        exists dportl''.
        exists dportmsgll''.
        exists dportls1''.
        exists dportls''.
        exists errv''.
        exists tcbls''.
        exists ecbls''.
        exists rtbl''.
        exists tcbl1''.
        exists tcbcur''.
        exists tcbl2''.
        exists rgrp''.
        exists ptls''.
        sep autocancel.
        cbn [Aarray Aarray'] in H0.
        sep normal in H0.
        sep autocancel.
        assert (isptr nextdstkport) as Hnextdstkport_isptr.
        {
          clear - Hdstkport'_type_match Hdstkport'_V_EventPtr.
          struct_type_vallist_match_elim.
          inverts Hdstkport'_V_EventPtr.
          pauto.
        }
        destruct Hnextdstkport_isptr as [ | [? ?]].
        - (* nextdstkport is null *)
          subst nextdstkport.
          destruct dstkportpl2.
          2:{
            cbn [length Channel_dstkport_get] in H0.
            sep normal in H0.
            sep destruct H0.
            sep split in H0.
            discriminate.
          }
          apply disj_split. left.
          sep normal.
          sep split; auto.
          5: rewrite app_length; simpl; lia.
          2:{
            sep split in H0.
            rewrite H. repeat f_equal.
            rewrite app_length. simpl. lia.
          }
          {
            rewrite app_length.
            simpl length.
            sep name lift kportNode_P.
            rewrite Hkportpl_kportpl'.
            rewrite Hkportl_kportl'.
            eapply kportNode_P_compose; eauto.
            sep autocancel.
            assert (length dstkportpl1 +1= S (length dstkportpl1)+0)%nat by lia.
            rewrite H. clear H.
            eapply Channel_dstkport_get_compose; auto.
            3: sep autocancel; sep auto.
            apply Hdstkport'_type_match.
            auto.
  Optimize Proof.
  Optimize Heap.
          }
          2:{
            intros.
            destruct Hdportls1''.
            - simpljoin. eapply Hdportls1_dportls1'.
              3: apply H2.
              2: eauto.
              lia.     
            - simpljoin. destruct H3. 
              * invertsr H3. invertsr H4.
                eapply Hdportls1_dportls1'.
                3: apply H2.
                2: eauto.
                lia.
              * simpljoin. 
                rename x into ndstportp.
                rewrite set_a_get_a'.
                eapply Hdportls1_dportls1'.
                3: apply H2.
                2: eauto.
                lia.
                lets Hkportls_nodup': Hkportls_nodup (dstkportpb, Int.zero) kp.
                setoid_rewrite Hget_dstkportp in Hkportls_nodup'.
                setoid_rewrite H2 in Hkportls_nodup'.
                apply Hkportls_nodup'.
                eapply addrval_Nodup_nth_err_neq.
                4: apply H1. auto.
                2:{ apply nth_error_middle. } 
                lia.
          }
          {
            destruct Hdportls1''.
            - simpljoin. auto.  
            - simpljoin. destruct H. 
              * invertsr H. auto. 
              * simpljoin. 
                rename x into ndstportp.
                rewrite set_a_get_a'.
                eauto.
                assert (dstportp = portptr \/ dstportp <> portptr) as Htmp by tauto.
                destruct Htmp; auto. subst dstportp.
                clear - Hgetportptr Hget_dstportp Hjoin_dport.
                eapply join_get_get_l in Hget_dstportp; eauto.
                setoid_rewrite Hgetportptr in Hget_dstportp.
                inverts Hget_dstportp.
          }
          - (* nextdstkport is not null *)
          subst nextdstkport. rename x into nextdstkportp.
          destruct dstkportpl2.
          {
            cbn [length Channel_dstkport_get] in H0.
            sep normal in H0.
            sep destruct H0.
            sep split in H0.
            discriminate.
          }
          apply disj_split. right.
          assert (a=nextdstkportp) as Htmp.
          {
            cbn [length Channel_dstkport_get] in H0. sep split in H0.
            now inverts H.
          }
          subst a. 
          sep normal. sep eexists.
          sep split; auto.
          5: apply nth_error_S_middle.
          2:{
            sep split in H0.
            rewrite H. repeat f_equal.
            rewrite app_length. simpl. lia.
          }
          {
            rewrite app_length.
            simpl length.
            sep name lift kportNode_P.
            rewrite Hkportpl_kportpl'.
            rewrite Hkportl_kportl'.
            eapply kportNode_P_compose; eauto.
            sep autocancel.
            assert (length dstkportpl1 + S (S (length dstkportpl2))= S (length dstkportpl1)+S(length (dstkportpl2)))%nat by lia.
            rewrite H. clear H.
            eapply Channel_dstkport_get_compose; auto.
            simpl length in H0.
            3: sep autocancel; sep auto.
            apply Hdstkport'_type_match.
            auto.
          }
          2:{
            intros.
            destruct Hdportls1''.
            - simpljoin. eapply Hdportls1_dportls1'.
              3: apply H2.
              2: eauto.
              lia.     
            - simpljoin. destruct H3. 
            * invertsr H3. invertsr H4.
              eapply Hdportls1_dportls1'.
              3: apply H2.
              2: eauto.
              lia.
            * simpljoin. 
              rename x into ndstportp.
              rewrite set_a_get_a'.
              eapply Hdportls1_dportls1'.
              3: apply H2.
              2: eauto.
              lia.
              lets Hkportls_nodup': Hkportls_nodup (dstkportpb, Int.zero) kp.
              setoid_rewrite Hget_dstkportp in Hkportls_nodup'.
              setoid_rewrite H2 in Hkportls_nodup'.
              apply Hkportls_nodup'.
              eapply addrval_Nodup_nth_err_neq.
              4: apply H1. auto.
              2:{ apply nth_error_middle. } 
              lia.
          }
          {
            destruct Hdportls1''.
            - simpljoin. auto.  
            - simpljoin. destruct H. 
              * invertsr H. auto. 
              * simpljoin. 
                rename x into ndstportp.
                rewrite set_a_get_a'.
                eauto.
                assert (dstportp = portptr \/ dstportp <> portptr) as Htmp by tauto.
                destruct Htmp; auto. subst dstportp.
                clear - Hgetportptr Hget_dstportp Hjoin_dport.
                eapply join_get_get_l in Hget_dstportp; eauto.
                setoid_rewrite Hgetportptr in Hget_dstportp.
                inverts Hget_dstportp.
          }
        }
      naive pure intro.
      rename v'20 into nextdstkportp.
      rename v'25 into errv.
      rename v' into dstkportpl_n.
      rename v'21 into dportl_final.
      rename v'22 into dportmsgll_final.
      rename v'23 into dportls1_final.
      eapply aconj_aisfalse_rule. 
      {
          
        instantiate(1:=Vint32 (match nextdstkportp with 
          | Vnull => Int.zero  | _ => Int.one end)).
        intros. apply disj_split in H. destruct H.
        - symbolic_execution.
        - sep normal in H. sep destruct H. sep split in H.
          subst.
          symbolic_execution. destruct x; auto.
          destruct x; pauto.
      }
      (* Deal with the end of loop *)
      naive pure intro.
      eapply backward_rule1.
      intros. apply disj_split in H. exact H.
      apply disj_rule.
      2:{
        naive pure intro.
        subst. destruct H14; discriminate.
      }
      naive pure intro.
      subst nextdstkportp. clear H14. subst dstkportpl_n.
      rename H1 into Herrv.
      clear H2.
      rename v'24 into dportls_final.
      rename H3 into Hget_dportls_final_portptr.
      rename H4 into Hjoin_dport_final.
      rename H5 into HRLH_Channel_final.
      rename H6 into HR_Kernel_Channel_final.
      rename H7 into HRL_PortAttr_final.
      rename H8 into HRLH_domainportl_final.
      rename H9 into HChannel_dstkport_Queue_IncoreC_final.
      assert (length dstkportpl - length dstkportpl=0)%nat as Htmp by lia.
      repeat rewrite Htmp. clear Htmp.
      rename H10 into HR_Kernel_Domain_final.
      rename H11 into HRLH_PortPtrINecb_final.
      rename H12 into HRH_TCBList_ECBList_P_final.
      rename H13 into HRH_CurTCB_final.
      cbn [qportpost_send_Incore spec_code_cons].

      partition_absrulestac absinfer_seq_end.
      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
        {CSLSEMREL (semaphore ′)};ₛ *)
      eapply seq_rule.
      {
        apply corecommu_rules.ift_zero_rule.
        intros. symbolic_execution. 
      }
      hoare name lift Aisr Ais Aier pre.
      eapply backward_rule1.
      apply add_aemp_isr_is_prop.

      (* EXIT_CRITICAL;ₛ *)
      hoare forward prim.
      {
        sep cancel EvtInv.
        sep cancel CoreCommuInv.
        sep cancel p_local.
        sep cancel Aier.
        sep cancel tcbdllflag.
        sep cancel APthreadAttr.
        sep cancel CapabilityInv.
        sep name lift PartitionInv.
        apply fold_PartitionInv_frm.
        sep cancel PartitionInv_part2.
        (* cancel TmrInv *)
        unfold TmrInv, HeapInv'.
        sep normal; sep eexists; sep autocancel.
        sep split; auto.
        eapply AOScoreheapl_merge with (m:= S (length msg)); pauto.
        { simpl; lia. }
        { simpl; lia. }
        sep autocancel.
        cbn [Aarray Aarray'].
        sep normal. sep autocancel.

        (* cancel PartitionInv *)
        unfold PartitionInv_part1.
        sep normal; sep eexists; sep pauto.
        sep cancel OtherPortPtrList.
        sep cancel AOSChannelFreeList.
        sep cancel AOSKernelPortFreeList.
        sep cancel AOSCorePortPtrList.
        2: eauto.
        9: eauto.
        4: eauto.
        5: eauto.
        6: eauto.
        2: eauto.
        2: auto.
        2: auto.
        2: auto.
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
        { congruence. }
        { congruence. }
        { reflexivity. }
        { reflexivity. }
        { pauto. }
        sep autocancel.
        rewrite Int.unsigned_repr.
        2:{
          rewrite <- Heq_dpnum_dstkportpl'.
          apply Int.unsigned_range_2.
        }
        rewrite Nat2Z.id. sep autocancel.
        apply H.
      }
      {
        auto. 
  Optimize Proof.
  Optimize Heap.
      }
      { go. }
      (*OS_Sched (­) *)
      eapply seq_rule.
      {
        eapply call_rule'.
        reflexivity.
        intros. apply rvl_nil.
        intros.
        unfold getasrt, OS_SchedPre, OS_SchedPre'.
        sep normal. sep eexists.
        sep autocancel.
        sep split; eauto.
        unfold isflag. auto.
        go.
        sep_unfold_funpost.
        intros.
        sep destruct H. sep eexists.
        sep autocancel. constructor.
        sep_unfold_funpre. intros.
        sep destruct H. sep eexists.
        sep autocancel. constructor.
        reflexivity.
      }
      unfold getasrt, OS_SchedPost, OS_SchedPost'.
      naive pure intro.
      invertsr H.
      destruct Herrv; subst.
      - (* END Some (V$ OS_NO_ERR) *) 
        partition_absrulestac absinfer_choice1.
        hoare forward.
      - (* END Some (V$ OS_ERR_DSTPORT_FULL)*)
        partition_absrulestac absinfer_choice2.
        hoare forward. 
    }
    (* dstkport is null *)
    apply disj_rule.
    {
      naive pure intro. apply pfalse_rule.
    }
    naive pure intro.
    destruct H60 as [? | [? ?]]; subst dstkport.
    2:{
      exfalso; clear - H72; pauto.
      unfold val_inj, val_eq, notint in H72;
      destruct x;destruct H72; pauto.
      inverts H.
    } clear H72.
    destruct dstkportpl.
    2:{
      simpl (length _).
      cbn [Channel_dstkport_get].
      naive pure intro.
      discriminate.
    }
    simpl (length _).
    eapply backward_rule1.
    {
      intros. sep name lift dmportp_sllseg in H60.
      lets Hss: dmportp_sllseg_app'_frm dportmsgll1 H14 H3.
      reflexivity. 
      assumption.
      apply Hss in H60. clear Hss.
      cbn [dmportp_sllseg] in H60.
      apply H60.
    }
    hoare normal pre. naive pure intro.
    invertsr H60.
    rewrite H13 in H72. invertsr H72.
    clear H73.
    rewrite H19 in H74. invertsr H74.
    simpl in H48. subst dpnum. clear H71.
    hoare name lift Adisj pre.
    eapply backward_rule1.
    apply disj_star_elim_disj.
    apply disj_rule.
    {
      naive pure intro.
      rewrite H70 in H48. discriminate.
    }
    naive pure intro. clear H48.
    rewrite H55 in H60. invertsr H60.
    rewrite H56 in H71. invertsr H71.
    rewrite H64 in H72. invertsr H72.
    simpljoin1.
    rewrite H47 in H71. invertsr H71.
    rewrite H66 in H48. invertsr H48.
    clear H68 H72 H76.
    rename x13 into qsize.
    hoare name lift Aisr Ais Aier pre.
    eapply backward_rule1.
    apply add_aemp_isr_is_prop.
    hoare forward.
    {
      eapply ift_rule''.
      symbolic_exe_port.
      instantiate (1:=Afalse).
      naive pure intro.
      partition_absrulestac absinfer_choice1.
      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE){CSLSEMREL (
        semaphore ′)};ₛ *)
      eapply seq_rule.
      apply corecommu_rules.ift_zero_rule.
      symbolic_execution.
      naive pure intro.
      clear H48.
      partition_exit'.
      {
        sep autocancel. 
        unfold AOSDomainPortPtrList, dmportp_sll.
        sep normal. sep autocancel.
        unfold AOSKernelPortIDTbl. sep normal. sep autocancel.
        unfold AOSChannelIDTbl. sep normal. sep autocancel.
        sep split; auto.
        sep name lift ChannelNode.
        eapply ChannelNode_compose; pauto.
        congruence. congruence.
        sep autocancel.
        eapply dmportp_sllseg_app'_frm; eauto.
        cbn [dmportp_sllseg].
        sep normal. sep eexists. sep autocancel.
        sep split; eauto.
        apply disj_star_elim_disj'.
        right. sep normal. sep eexists.
        sep split; eauto.
      }
      {
        go. 
      }
      hoare forward.
    }
    apply disj_rule.
    {
      naive pure intro.
      apply pfalse_rule.
    }
    naive pure intro.
    destruct H48.
    2:{
      exfalso; clear - H48.
      destruct (Int.ltu ($ Z.of_nat qsize) qentries); destruct (Int.eq qentries ($ Z.of_nat qsize)); simpl in H48; mauto.
    }
    clear H52 H53.
    assert (Int.unsigned qentries < Int.unsigned ($ Z.of_nat qsize)).
    {
      clear - H48 H60.
      destruct (Int.ltu ($ Z.of_nat qsize) qentries) eqn:E1; destruct (Int.eq qentries ($ Z.of_nat qsize)) eqn:E2; simpl in H48. 
      1-3: exfalso; mauto.
      apply Inteq_false_is_Zneq in E2. lia.
    }
    clear H48 H60.
    (* (port_ptr ′ → OSQIn) → len =ₑ msg_ptr ′ → len;ₛ *)
    unfold TmrInv. unfold HeapInv'.
    hoare normal pre.
    naive pure intro.
    rename v' into cheapl.
    rename v'20 into cheape.
    rename v'21 into cheapt.

    (* qportpost_store_one
        (|Vptr portptr
          :: Vptr msgptr :: V$ Z.of_nat 0 :: Vnull :: Vnull :: nil|);;
        END Some (V$ OS_NO_ERR) *)
    partition_absrulestac absinfer_choice2. 
    assert (~(exists mlen msg,
    Get_heapl_addrval cheapl msgptr (Z.to_nat (Int.unsigned mlen + 1))
      (Vint32 mlen :: msg) /\ (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z)\/
      (exists mlen msg,
      Get_heapl_addrval cheapl msgptr (Z.to_nat (Int.unsigned mlen + 1))
        (Vint32 mlen :: msg)/\ (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z)) by tauto.
    destruct H68.
    {
      partition_absrulestac qportpost_msg_in_heapl_abt'.
      apply absabort_rule.
    }
    destruct H68 as (mlen&msg&H68&Hmlensize).
    partition_absrulestac qportpost_msg_in_heapl_cont'.
    partition_absrulestac absinfer_choice2.
    hoare name lift AOScoreheapl pre.
    eapply backward_rule1.
    {
      eapply Get_heapl_addrval_split_coreheapl; eauto.
    }
    naive pure intro.
    rename v' into cheapl1.
    rename v'20 into cheapl2.
    rename v'21 into heapmsglen.
    rename v'22 into irheapmsg.
    simpljoin1.
    rewrite <- H76.
    simpl length.
    cbn [Aarray Aarray'].
    destruct msgptr as [msgptrb msgptro].
    hoare normal pre.
    hoare name lift (dmportp_sllseg_qport_msg qinptr) pre.
    eapply backward_rule1.
    {
      eapply dmportp_sllseg_qport_msg_ngt0.
      clear - H52.
      unfold Coqlib.nat_of_Z. lia.
    }
    naive pure intro.
    destruct H71 as (msghold&msgholdl&?&?). subst v'24.
    simpl in H76.
    assert (Z.to_nat (Int.unsigned mlen + 1) = S (Z.to_nat (Int.unsigned mlen))) by lia.
    rewrite H71 in H76. inverts H76.
    simpl in H73.
    hoare name lift msghold pre.
    eapply backward_rule1.
    {
      apply dmportp_sllseg_qport_msg_split.
      unfold Coqlib.nat_of_Z. lia. 
    }
    naive pure intro.
    destruct H76. destruct H77.
    invertsr H77. rename v'21 into irrmsghold.
    hoare name lift Aop (Aptrmapsto qinptr) pre.
    eapply seq_rule.
    {
      eapply assign_rule_general.
      {
        intros.
        eapply symbolic_lemmas.struct_offset_rv.
        { 
          eapply symbolic_lemmas.addrof_deref_rv.
          sep_get_port_rv.
        }
        all: reflexivity.
      }
      {
        assert ((fst qinptr, Int.add (snd qinptr) (Int.zero)) = qinptr ).
        {
          rewrite Int.add_zero. now destruct qinptr. 
        }
        rewrite H77. clear H77.
        split; intros; eauto.
      }
      { 
        intros. 
        eapply symbolic_lemmas.struct_member_rv_flag.
        sep autocancel.
        2-6: try reflexivity.
        unfold get_off_addr. cbn [fst snd].
        rewrite Int.add_zero.
        sep autocancel. apply H77.
        simpl in H72. destruct H72.
        simpl.
        pauto. 
      }
      { now apply assign_type_match_true. }
      {
        intros. sep eexists. sep auto.
      }
    }
    clear H71 H80.
    hoare name lift Aisr Ais aemp_isr_is pre.
    eapply backward_rule1.
    apply elim_aemp_isr_is_prop.
    (* memcpy (­&ₐ ((port_ptr ′ → OSQIn) → data) [′ 0], &ₐ (msg_ptr ′ → data) [′ 0],
    〈 long 〉 msg_ptr ′ → len­);ₛ *)
    assert ((fst qinptr, Int.add (snd qinptr) (Int.zero)) = qinptr ).
    {
      rewrite Int.add_zero. now destruct qinptr. 
    }
    rewrite H71. clear H71.
    destruct qinptr as [qinptrb qinptro].
    unfold get_off_addr.  cbn[fst snd].
    hoare name lift (Alvarmapsto port_ptr) APortStruct (Aptrmapsto (qinptrb, qinptro)) pre.
    eapply seq_rule.
    {
      eapply call_rule'; try reflexivity.
      {
        intros.
        eapply rvl_elim.
        {
          eapply symbolic_lemmas.addrof_array_elem_rv.
          {
            eapply port_OSQIn_data_rv'; eauto.
          }
          { symbolic execution. }
          all: pauto.
        }
        eapply rvl_elim.
        {
          eapply symbolic_lemmas.addrof_array_elem_rv.
          {
            eapply struct_member_array_rv. symbolic_execution.
            all: reflexivity.
          }
          { symbolic execution. }
          all: pauto.
        }
        eapply rvl_elim; [ |apply rvl_nil].
        instantiate (1:=(Vint32 mlen)).
        eapply cast_rv_tint8_tint32; auto.
        eapply symbolic_lemmas.struct_member_rv_flag.
        {
          sep autocancel.
          assert ((msgptrb, msgptro) = get_off_addr (msgptrb, msgptro) Int.zero).
          { unfold get_off_addr; cbn [fst snd]; rewrite Int.add_zero; reflexivity. }
          rewrite <- H77. sep autocancel.
          exact H71.
        }
        all: try reflexivity.
        simpl in H72. tauto.
      }
      {
        intros; unfold_spec. cbn [fst snd].
        sep normal. sep eexists.
        sep autocancel; sep split; eauto.
        rewrite ! Int.add_zero.
        sep name lift msghold in H71.
        eapply Aarray_split_single with (m:=(Z.to_nat (Int.unsigned mlen)))in H71.
        2:{
          unfold CHANNEL_CACHE_SZIE. clear. mauto. 
        }
        2:{
          clear - Hmlensize. unfold Coqlib.nat_of_Z. lia.
        }
        2: rewrite app_length; auto.
        sep autocancel.
        sep name lift Aarray' in H71. unfold Aarray.
        rewrite <- H78.
        sep autocancel. apply H71.
      }
      { go. }
      { sep_unfold_funpost. intros. sep destruct H71. sep auto. }
      { sep_unfold_funpre. intros. sep destruct H71. sep auto. }
      { pauto. }
    }
    unfold getasrt; unfold OS_memcopyPost, OS_memcopyPost'.
    hoare normal pre. pure intro.
    invertsr H77.
    invertsr H71.
    rewrite ! Int.add_zero.
    hoare abs lift pre.
    (* ++ port_ptr ′ → OSQIn;ₛ *)
    eapply seq_rule.
    {
      eapply port_memeber_asgn; try reflexivity.
      - sep auto. split; intros.
        sep autocancel. exact H71.
        sep auto.
  Optimize Proof.
  Optimize Heap.
      - intros. eapply symbolic_lemmas.bop_rv.
        * sep_get_port_rv.
        * symbolic_execution.
        * simpl. reflexivity.
        * auto.
        * reflexivity.
      - instantiate (1:=14%nat).  reflexivity.
      - eauto.
      - auto.
      - auto.
      - auto.
      - now apply assign_type_match_true.
      - reflexivity.
      - intros. sep auto.
    }
    assert (Int.unsigned (qentries +ᵢ  $ 1) <=? Int16.max_unsigned = true) as Hqentriesrange.
    {
      clear - H52 H69.
      pose proof Int_add_one_Sn qentries ltac:(lia).
      rewrite Z.leb_le. rewrite int16_max_unsigned_val. lia.
    }
    eapply seq_rule.
    {
      eapply port_memeber_asgn; try reflexivity.
      - intros. eapply symbolic_lemmas.bop_rv.
        * eapply port_QEntries_rv. 
          3: { sep autocancel. apply H71. }
          {
            qportpostproof_tac. 
          }
          { port_nth_val_solve. }
        * symbolic_execution.
        * simpl. reflexivity.
        * auto.
        * reflexivity.
      - instantiate (1:=17%nat). reflexivity.
      - port_nth_val_solve.
      - auto.
      - auto.
      - auto.
      - now apply assign_type_match_true.
      - simpl. now rewrite Hqentriesrange.
      - intros. sep auto.
    }
    (* If (port_ptr ′ → OSQIn ==ₑ port_ptr ′ → OSQEnd)
    {port_ptr ′ → OSQIn =ₑ port_ptr ′ → OSQStart};ₛ *)
    hoare name lift APortStruct pre.
    destruct qendptr as [qendptrb qendptro].
    hoare remember (1::nil)%nat pre.
    apply seq_rule with (APortStruct portptr (update_nth_val 17
    (update_nth_val 14 dport
       (Vptr (dmportp_sllseg_qport_msg_next (qinptrb,qinptro) qstartptr (qendptrb,qendptro))))
    (Vint32 (qentries +ᵢ  $ 1)))**H71).
    {
      eapply ift_rule.
      - intros. eexists. subst H71.
        eapply symbolic_lemmas.bop_rv.
        * eapply port_QIn_rv.
          3:{ sep autocancel. eauto. }
          { 
            qportpostproof_tac.
          }
          port_nth_val_solve. 
        * eapply port_QEnd_rv.
          3:{ sep autocancel. eauto. }
          {
            qportpostproof_tac. 
          }
          port_nth_val_solve.
        * simpl. reflexivity.
        * destruct (peq qinptrb qendptrb); auto.
          destruct (Int.eq (qinptro +ᵢ  Int.mul ($ 1) ($ 33)) qendptro); auto.
        * reflexivity.
      -  intros. 
      eapply sep_aconj_r_aisfalse_to_astar in H77.
      2:{ intros. subst H71.
      eapply symbolic_lemmas.bop_rv.
      * eapply port_QIn_rv.
        3:{ sep autocancel. eauto. }
        { 
          qportpostproof_tac. 
        }
        port_nth_val_solve. 
      * eapply port_QEnd_rv.
        3:{ sep autocancel. eauto. }
        { 
          qportpostproof_tac.
        }
        port_nth_val_solve.
      * simpl. reflexivity.
      * destruct (peq qinptrb qendptrb); auto.
        destruct (Int.eq (qinptro +ᵢ  Int.mul ($ 1) ($ 33)) qendptro); auto.
      * reflexivity.
      }
      sep split in H77.
      destruct H82. 
      2:{ destruct (peq qinptrb qendptrb);
      destruct (Int.eq (qinptro +ᵢ  Int.mul ($ 1) ($ 33)) qendptro); auto; simpl in H1; discriminate. }
      sep cancel H71.
      unfold dmportp_sllseg_qport_msg_next.
      simpl typelen. unfold msg_distance.
      unfold Qport_msg_ptrs_P in H67.
      destruct qstartptr. simpljoin1. unfold get_off_addr in *.
      simpl in H83, H85.
      invertsr H83. invertsr H85.
      cbn [fst snd] in *.
      rewrite ! Int.add_zero_l in *.
      rewrite peq_true in H82.
      destruct (Int.eq (Int.mul ($ x0) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
      (Int.mul ($ Int.unsigned ($ Z.of_nat qsize)) ($ 33))) eqn:E'; [discriminate | ].
      simpl typelen. simpl Z.of_nat.
      assert (
      (qinptrb, Int.mul ($ x0) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)) =
      (if
              Int.unsigned
                (Int.divu
                   (Int.mul ($ Int.unsigned ($ Z.of_nat qsize)) ($ 33) -ᵢ
                    Int.mul ($ x0) ($ 33)) ($ 33)) =? 1
             then (qinptrb, Int.zero)
             else (qinptrb, Int.mul ($ x0) ($ 33) +ᵢ  $ 33))).
      {
        clear - H87 H88 H69 E'.
        destruct (Int.unsigned (Int.divu (Int.mul ($ Int.unsigned ($ Z.of_nat qsize)) ($ 33) -ᵢ Int.mul ($ x0) ($ 33)) ($ 33)) =? 1) eqn:?.
        2: { rewrite (Int.mul_commut ($ 1)).  rewrite Int.mul_one. reflexivity. }
        exfalso.
        assert (exists n,  Int.unsigned ($ Z.of_nat qsize) = n + x0 /\ 1 <= n <= 65536).
        { exists (Int.unsigned ($ Z.of_nat qsize) - x0). split;lia. }
        destruct H as [n [H0 H1]].
        rewrite H0 in Heqb.
        assert (x0 <= 65536) by lia. 
        erewrite  <- (Int.unsigned_repr n) in Heqb at 1.
        rewrite  <- (Int.unsigned_repr x0) in Heqb at 1.  
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
          clear - H1;unfold Int.max_unsigned, Int.modulus, Int.wordsize; cbn; lia.
         }
        rewrite H2 in Heqb.
        rewrite Int.unsigned_repr in Heqb. assert (n = 1) by lia.
        subst n.
        rewrite H0 in E'.
        rewrite <- (Int.unsigned_repr 1) in E' at 2.
        rewrite <- (Int.unsigned_repr x0) in E' at 2.
        rewrite <- Int.add_unsigned in E'.
        rewrite Int.mul_add_distr_l in E'.
        rewrite (Int.add_commut (Int.mul ($ 1) ($ 33))) in E'. 
        rewrite Int.eq_true in E'. discriminate.
        all: rewrite max_unsigned_val; lia.
      }
      rewrite H67 in H77. sep autocancel.
    - intros.
      eapply backward_rule1. 
      eapply sep_aconj_r_aistrue_to_astar.
      { intros. subst H71.
      eapply symbolic_lemmas.bop_rv.
      * eapply port_QIn_rv.
        3:{ sep autocancel. eauto. }
        { 
          qportpostproof_tac. 
        }
        port_nth_val_solve. 
      * eapply port_QEnd_rv.
        3:{ sep autocancel. eauto. }
        { 
          qportpostproof_tac.
        }
        port_nth_val_solve.
      * simpl. reflexivity.
      * destruct (peq qinptrb qendptrb); auto.
        destruct (Int.eq (qinptro +ᵢ  Int.mul ($ 1) ($ 33)) qendptro); auto.
      * reflexivity.
      }
      naive pure intro.
      subst H71.
      hoare evar lift port_ptr pre.
      hoare abs lift pre.
      eapply forward_rule1.
      2:{
        eapply port_memeber_asgn; try reflexivity.
        - intros. eapply port_QStart_rv.
          3:{ sep autocancel. eauto. }
          { 
            qportpostproof_tac. 
          }
          port_nth_val_solve.
        - instantiate (1:=14%nat). reflexivity.
        - port_nth_val_solve.
        - auto.
        - auto.
        - auto.
        - now apply assign_type_match_true.
        - reflexivity.
        - intros. sep auto.
      }
      intros. sep autocancel.
      unfold dmportp_sllseg_qport_msg_next.
      simpl typelen. unfold msg_distance.
      unfold Qport_msg_ptrs_P in H67.
      destruct qstartptr. simpljoin1. unfold get_off_addr in *.
      simpl in H84, H86.
      invertsr H84. invertsr H86.
      cbn [fst snd] in *.
      clear H82 H83.
      rewrite ! Int.add_zero_l in *.
      rewrite peq_true in H77.
      destruct (Int.eq (Int.mul ($ x0) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
      (Int.mul ($ Int.unsigned ($ Z.of_nat qsize)) ($ 33))) eqn:E'.
      2:{
        simpl in H77. congruence.
      }
      simpl typelen. simpl Z.of_nat.
      rewrite aux_pureLib.Int_eq_dec in E'.
      rewrite <- E'.
      rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. 
      rewrite (Int.mul_commut ($ 1)).
      rewrite Int.mul_one.
      assert ((Int.divu ($ 33) ($ 33)) = Int.one)  by (clear;mauto).
      rewrite H67.
      rewrite Int.unsigned_one.
      rewrite Z.eqb_refl.
      rewrite update_nth_val_diff in H71. 2:lia.
      rewrite update_nth_val_same in H71.
      sep auto.
  Optimize Proof.
  Optimize Heap.
    }
    subst H71.
    (* qportpost_store_one
    (|Vptr portptr
    :: Vptr (msgptrb, msgptro) :: V$ 0 :: Vnull :: Vnull :: nil|) *)
    hoare name lift Aop osdomainportid oskportid oschannelid oscoreheapid pre.
    partition_absrulestac qportpost_store_one_InCore_cont.
    (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE){CSLSEMREL (
    semaphore ′)};ₛ *)
    eapply seq_rule.
    {
      apply corecommu_rules.ift_zero_rule.
      symbolic_execution.
    }
    hoare name lift Aisr Ais Aier pre.
    eapply backward_rule1.
    apply add_aemp_isr_is_prop.

    hoare abs lift pre.
    (* EXIT_CRITICAL;ₛ *)
    hoare forward prim.
    {
      sep autocancel.
      unfold AOSMapTbl.
      sep autocancel.
      unfold AOSUnMapTbl.
      sep autocancel.
      unfold AOSTCBPrioTbl.
      sep normal.
      sep eexists.
      sep autocancel.
      sep split; auto.
      unfold AOSRdyTblGrp. 
      sep normal.
      sep split; eauto.
      unfold AOSRdyTbl. sep normal.
      sep autocancel.
      sep split; auto.
      unfold AOSRdyGrp. sep normal.
      sep autocancel. sep split; auto.
      unfold AOSTime. sep autocancel.
      unfold AGVars. sep normal.
      sep eexists. sep autocancel.
      sep split; auto.
      sep cancel CapabilityInv.
      sep name lift PartitionInv.
      apply fold_PartitionInv_frm.
      sep cancel PartitionInv_part2.
      
      (* cancel TmrInv *)
      unfold TmrInv, HeapInv'.
      sep normal; sep eexists; sep autocancel.
      sep split; auto.
      eapply AOScoreheapl_merge.
      instantiate (1:= S (length msg)).
      lia. auto. reflexivity. lia. auto.
      sep autocancel.
      cbn [Aarray Aarray']. 
      sep normal. sep autocancel.
      simpl typelen. simpl Z.of_nat. 
      unfold Aarray at 2 in H71.
      rewrite H80. sep autocancel.
      (* cancel PartitionInv *)
      unfold PartitionInv_part1.
      sep normal; sep eexists; sep pauto.
      sep cancel AOSChannelFreeList.
      sep cancel AOSKernelPortFreeList.
      sep cancel OtherPortPtrList.
      sep name lift AOSCorePortPtrList in H71.
      sep name lift AOSCorePortPtrList.
      unfold AOSCorePortPtrList in H71.
      unfold AOSCorePortPtrList.
      sep normal in H71. sep normal.
      sep cancel OSCorePortPtrList.
      apply sep_pure_split in H71. destruct H71 as (Htmp&H71).
      apply astar_l_apure_intro.
      2:{
        instantiate (1:=(set dportls1 portptr
        (Z.to_nat DNUM, Z.to_nat (Int.unsigned x2), Z.to_nat (Int.unsigned portid), SourceP,
        Z.to_nat (Int.unsigned x4), Z.to_nat (Int.unsigned x5), Z.to_nat (Int.unsigned x6),
        QueuePort qsize (x14 ++ msg :: nil)))).
        eapply RH_CorePortPtrList_upd_dportls; eauto.
      } 
      2: eauto.
      5: eauto.
      sep name lift AOSChannelIDTbl.
      unfold AOSChannelIDTbl.
      sep normal. sep autocancel.
      sep split; try tauto.
      eapply ChannelNode_compose.
      instantiate (1:= chanl1). congruence.
      instantiate (1:=chandstkportll1).
      congruence.
      instantiate(2:= (Vint32 chanid
      :: V$ 1
         :: V$ 0
            :: V$ DEFAULT_CHANNLE_SEMAPHROE
               :: Vnull
                  :: x15
                     :: Vptr (kportpb, Int.zero) :: x17 :: nil)).
      reflexivity. 
      reflexivity.
      qportpostproof_tac.
      sep autocancel.
      unfold AOSKernelPortIDTbl. sep normal.
      sep autocancel. sep split; auto.
      5: instantiate (3:= dportlptr).
      5: instantiate (2:= (dportl1++ (update_nth_val 17
      (update_nth_val 14 dport
         (Vptr
            (dmportp_sllseg_qport_msg_next
               (qinptrb, qinptro) qstartptr
               (qendptrb, qendptro))))
      (Vint32 (qentries +ᵢ  $ 1))):: dportl2)).
      8: eapply map_tactics.join_set_set; eauto.
      7: instantiate (1:= dpptrl).
      unfold AOSDomainPortPtrList. sep normal.
      sep autocancel.
      instantiate (2:= (dportmsgll1++ (x14++(msg::nil))::dportmsgll2)).
      rewrite dmportp_sllseg_app'_frm. sep autocancel.
      cbn [dmportp_sllseg]. sep normal. sep eexists.
      sep split.
      2,4: port_nth_val_solve.
      2:{
        qportpostproof_tac.
      }
      sep autocancel.
      apply disj_star_elim_disj'. right.
      sep normal. sep eexists.
      sep split. 3,4: splits.
      3,5,7-10: port_nth_val_solve.
      8: eauto.
      5-7: congruence. 4: auto.
      assert ((Init.Nat.pred
      ∘ (Int.unsigned ($ Z.of_nat qsize) - Int.unsigned qentries))= ∘ (Int.unsigned ($ Z.of_nat qsize) - Int.unsigned (qentries +ᵢ  $ 1))).
      {
          unfold Coqlib.nat_of_Z.
          rewrite <- Z2Nat.inj_pred.
          f_equal.
          rewrite <- Z.sub_1_r. 
          rewrite <- Z.sub_add_distr. f_equal.
          symmetry.
          apply Int_add_one_Sn'.
          clear - H18 H66.
          unfold OS_Port_Seg_dls in H18.
          struct_type_vallist_match'_elim.
          inverts H66. lia.
      }
      rewrite <- H93. clear H93. sep autocancel.
      eapply dmportp_sllseg_qport_msg_append_tail; eauto.
      lia. sep eexists.
      sep autocancel. sep split; auto. apply H71.
      {
        apply array_type_vallist_match_app.
        simpl in H72. erewrite <-firstn_skipn in H79.
        splits. tauto. 
        apply array_type_vallist_match_app in H79.
        jauto.   
      }
      {
        eapply Qport_msg_ptrs_P_hold; eauto. 
      }
      {
        rewrite Int_add_one_Sn'. lia.
        lia. 
      }
      {
        apply nth_error_split in H14. simpljoin.
        eapply RL_PortPtrList_upd; eauto.
        unfold OS_Port_V_nextPort.
        rewrite nth_val_update_nth_val_diff;[ |lia].
        apply nth_val_update_nth_val_diff. lia.
      }
      {
        eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto. 
      }
      {
        apply nth_error_split in H14. simpljoin.
        eapply R_Kernelport_DomainPort_upd; eauto.
        unfold OS_Port_V_portID.
        rewrite nth_val_update_nth_val_diff;[ |lia].
        apply nth_val_update_nth_val_diff. lia.
        unfold OS_Port_V_coreNum.
        rewrite nth_val_update_nth_val_diff;[ |lia].
        apply nth_val_update_nth_val_diff. lia.
      }
      {
        eapply RLH_Channel_upd_dportls1; eauto.
        right. jauto. 
      }
      {
        apply nth_error_split in H14. simpljoin.
        eapply RLH_Domainportl_upd_Queue'; eauto.
        congruence.
        lets HH: RLH_Domainportl_abs_getsome H3 H4 H10.
        simpljoin.
        assert (x3=length x).
        { assert (nth_error (x++portptr::x0) (length x) = Some portptr).
          apply nth_error_middle.
          eapply dpptrl_not_same_elements; eauto. }
        subst x3.
        assert (length x = length dportl1) by congruence.
        setoid_rewrite H98 in H14.
        rewrite nth_error_middle in H14.
        invertsr H14.
        assert (length x = length dportmsgll1) by congruence.
        rewrite H14 in H95.
        rewrite nth_error_middle in H95.
        inverts H95.
        auto. 
  Optimize Proof.
  Optimize Heap.
      }
      {
        unfold RLH_PortPtrINecb.
        splits.
        apply nth_error_split in H14. simpljoin.
        eapply RL_PortPtrList_upd; eauto.
        unfold OS_Port_V_nextPort.
        rewrite nth_val_update_nth_val_diff;[ |lia].
        apply nth_val_update_nth_val_diff. lia.
        rewrite Forall_forall.
        intros. 
        rewrite Forall_forall in H11.
        apply H11 in H94.
        easy.
      }
      {
        apply nth_error_split in H14. simpljoin.
        eapply RL_PortAttr_upd; eauto.
        unfold OS_Port_V_direction.
        rewrite nth_val_update_nth_val_diff;[ |lia].
        apply nth_val_update_nth_val_diff.
        lia.
        unfold OS_Port_V_mode.
        rewrite nth_val_update_nth_val_diff;[ |lia].
        apply nth_val_update_nth_val_diff.
        lia. 
      }
    }
    auto.
    go.
    hoare forward.
  }
Qed.
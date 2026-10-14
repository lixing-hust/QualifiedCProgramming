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
Require Import partition_initrules.
Require Import partinv_lemmas.
Require Import portaddtochannelproof_aux.
Require Import portaddtochannelproof_aux2.

Open Scope code_scope.

Open Scope int_scope.

Ltac pure_intro' := hoare_split_pure_all; 
                   isptr_intro; 
                   array_leneq_intro;
                   hoare_split_pure_all; 
                   simpljoin;
                   simpl_field_eq.

Ltac struct_type_vallist_match_elim_H H :=
  match type of H with
    | struct_type_vallist_match ?t _  =>
      try unfold t in H; simpl struct_type_vallist_match in H;
      match type of H with
        | struct_type_vallist_match' ?t' _  => 
          let Hr := fresh in let Hp := fresh in 
          match listlen t' with
            | 0%nat => lets Hr : struct_type_vallist_match_elim_0  H
            | 1%nat => lets Hr : struct_type_vallist_match_elim_1  H
            | 2%nat => lets Hr : struct_type_vallist_match_elim_2  H
            | 3%nat => lets Hr : struct_type_vallist_match_elim_3  H
            | 4%nat => lets Hr : struct_type_vallist_match_elim_4  H
            | 5%nat => lets Hr : struct_type_vallist_match_elim_5  H
            | 6%nat => lets Hr : struct_type_vallist_match_elim_6  H
            | 7%nat => lets Hr : struct_type_vallist_match_elim_7  H
            | 8%nat => lets Hr : struct_type_vallist_match_elim_8  H
            | 9%nat => lets Hr : struct_type_vallist_match_elim_9  H
            | 10%nat => lets Hr : struct_type_vallist_match_elim_10  H
            | 11%nat => lets Hr : struct_type_vallist_match_elim_11  H
            | 12%nat => lets Hr : struct_type_vallist_match_elim_12  H
            | 13%nat => lets Hr : struct_type_vallist_match_elim_13  H
            | 14%nat => lets Hr : struct_type_vallist_match_elim_14  H
            | 15%nat => lets Hr : struct_type_vallist_match_elim_15  H
            | 16%nat => lets Hr : struct_type_vallist_match_elim_16  H
            | 17%nat => lets Hr : struct_type_vallist_match_elim_17  H
            | 18%nat => lets Hr : struct_type_vallist_match_elim_18  H
            | 19%nat => lets Hr : struct_type_vallist_match_elim_19  H
            | 20%nat => lets Hr : struct_type_vallist_match_elim_20  H
            | 21%nat => lets Hr : struct_type_vallist_match_elim_21  H
            | 22%nat => lets Hr : struct_type_vallist_match_elim_22  H
            | 23%nat => lets Hr : struct_type_vallist_match_elim_23  H
            | 24%nat => lets Hr : struct_type_vallist_match_elim_24  H
            | 25%nat => lets Hr : struct_type_vallist_match_elim_25  H
            | 26%nat => lets Hr : struct_type_vallist_match_elim_26  H
            | _ => fail 1
          end;
            [ simp join; lets Hp : struct_array_rm_type_val_match H; 
              simpl remove_array_struct; eauto; clear H; unfold rule_type_val_match_list in Hp; simp join
            | (simpl; auto) .. ]
      end; rule_type_val_match_elim
  end.
                   
Ltac hoare_ex_intro ::=
  repeat match goal with
  | |- {| _, _, _, _, _, _ |} |- _  {{ EX _, _ }} _ {{ _ }} =>
     apply ex_intro_rule; intros 
  end.

Ltac port_combine :=
  match goal with 
    | H: ?s |= ?p |- ?s |= _ => 
      match p with 
      | context [ ([|OS_Port_V_mode ?dport = Some (Vint32 (ZToInt SAMPLE))|] **
      dmportp_sllseg_sampleport_msg ?v ?msgl \\// ?q)] => sep name lift ([|OS_Port_V_mode dport = Some (Vint32 (ZToInt SAMPLE))|] **
      dmportp_sllseg_sampleport_msg v msgl \\// q) in H end;
      sep name lift APortStruct in H;
      match p with 
      | context [ dmportp_sllseg ?v Vnull] => sep name lift (dmportp_sllseg v Vnull) in H end;
      match p with 
      | context [ dmportp_sllseg ?v (Vptr ?v')] => sep name lift (dmportp_sllseg v (Vptr v')) in H end;
      eapply dmportp_sllseg_compose in H;eauto
    end.

Ltac chann_combine chanvl1 chanvl2 :=
  match goal with 
  |H: ?s  |= ?p |- ?s |= _ =>
    match p with 
    | context [Channel_dstkport_get ?v Vnull ?n ?dstportl] => 
      sep name lift (Channel_dstkport_get v Vnull n dstportl) in H end;
    match p with 
    | context [ChannelNode chanvl2 ?chanl2 ?chandstportll2] => 
      sep name lift (ChannelNode chanvl2 chanl2 chandstportll2) in H end;
    match p with 
    | context [Astruct (?b, Int.zero) OS_Channel ?chan] => 
      sep name lift (Astruct (b, Int.zero) OS_Channel chan) in H end;
    match p with 
    | context [ChannelNode chanvl1 ?chanl1 ?chandstportll1] => 
      sep name lift (ChannelNode chanvl1 chanl1 chandstportll1) in H end;
    eapply ChannelNode_compose in H;eauto 
  end.


Ltac kport_combine kportvl1 kportvl2 :=
  match goal with 
  |H: ?s  |= ?p |- ?s |= _ =>
    match p with 
    | context [kportNode_P kportvl2 ?kportl2] => 
      sep name lift (kportNode_P kportvl2 kportl2) in H end;
    match p with 
    | context [Astruct' ?kpptr OS_K_Port_Seg_dls (firstn 6 ?kport)] => 
      sep name lift (Astruct' kpptr OS_K_Port_Seg_dls (firstn 6 kport)) in H end;
    match p with 
    | context [kportNode_P kportvl1 ?kportl1] => 
      sep name lift (kportNode_P kportvl1 kportl1) in H end;
      eapply kportNode_P_compose in H;eauto
  end.

Lemma OSPortAddToChannel_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSPortAddToChannel vl logicl OSPortAddToChannelPre ct->
      Some r =
      BuildRetI os_internal OSPortAddToChannel vl logicl OSPortAddToChannelPost ct->
      exists t d1 d2 s,
        os_internal OSPortAddToChannel = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  intros. 
  match goal with
    | H : Some _ = BuildRetI _ _ _ _ _ _ |-  _ =>
      unfold BuildRetI in H; simpl in H; inverts H
  end.
  init_prespec; 
  unfold_internal_pre;
  hoare normal pre;
  hoare_split_pure_all;
  type_val_match_elim.
  (* init_spec. *)
  inverts H4.

  rename v'6 into aop. rename v'7 into ier.  rename v'8 into chan_v. rename v'9 into p_v. 
  rename v'10 into err_l. rename v'11 into err_v.
  rename v'12 into curdomain. rename v'13 into domainv. rename v'14 into domainvl. rename v'15 into vsem.
  rename v' into sem_v. rename v'0 into res_v. rename v'1 into kp_lv.  
  rename v'2 into chan_lv. rename v'3 into re_v. rename v'4 into flag_v. rename v'5 into srcp_v.
  pure_intro'.
  rename H into Hcurd.  
  rename H0 into Hdomain_type.
  
  (* channel ′ =ₑ 〈 OS_Channel ∗ 〉 NULL;ₛ
  kport ′ =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
  re ′ =ₑ 〈 OS_Port ∗ 〉 NULL;ₛ *)
  hoare forward.
  hoare forward.
  hoare forward.

  (* If (channelID ′ ≥ ′ CHANNEL_NUMS)
  {∗ err ′ =ₑ 〈 char_t 〉 ′ OS_PORT_ID_INVALID;ₛ
  RETURN 〈 OS_Port ∗ 〉 NULL};ₛ *)
  hoare forward.
  { pauto. }
  { pauto. }
  { pauto. }
  { (* If yes *)
    pure_intro'.
    assert (Int.ltu ($ CHANNEL_NUMS) chan_v = true \/  Int.eq chan_v ($ CHANNEL_NUMS) = true) by pauto.
    clear H H0 H3.
    hoare name lift (Aptrmapsto) pre.
    hoare name lift Aop pre.
    eapply seq_rule.
    eapply assign_rule_deref_ptr.
    symbolic_execution.
    intros s. split; intros Hs; exact  Hs.
    symbolic_execution.
    eapply eq_int. auto.
    intros s Hs. sep auto.
    unfold OSPortAddToChannel_aspec.
    cbn [spec_code_cons].
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_choice1;[ | | intros s Hs; exact Hs].
    1,2: can_change_aop_solver'.
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_seq_end;[ | | intros s Hs; exact Hs].
    1,2: can_change_aop_solver'. 
    eapply rete_rule.
    intros s Hs.
    split.
    { unfold OSPortAddToChannelPost'.
      sep normal. sep eexists.
      sep autocancel.
      sep split;[ | cbn;eauto ].       
      destruct Hs.
      left.
      sep split in H.
      sep split;eauto.
      
      right.
      sep normal in H. sep normal.
      sep destruct H.
      sep eexists.
      sep autocancel.

      unfold OSPortAddToChannel_retvalue_case1.
      sep split in H.
      subst.
      sep split;eauto.
      left.
      split;auto.  }
    symbolic_execution. }
  (* If no *)
  hoare forward.
  pure_intro'.
  assert (Int.ltu ($ CHANNEL_NUMS) chan_v = false /\ Int.eq chan_v ($ CHANNEL_NUMS) = false ) as [? Heqfa].
  { destruct (Int.ltu ($ CHANNEL_NUMS) chan_v), (Int.eq chan_v ($ CHANNEL_NUMS));auto.
    simpl in H.
    destruct H;tryfalse.
    1,2: destruct H;tryfalse. }
  clear H.

  eapply backward_rule1.
  intros s Hs.
  sep lift 16%nat in Hs.
  eapply disj_star_elim_disj in Hs.
  exact Hs.
  (* If (port_ptr ′ ==ₑ 〈 OS_Port ∗ 〉 NULL)
  {∗ err ′ =ₑ 〈 char_t 〉 ′ OS_PORT_ERR_NULL;ₛ
  RETURN 〈 OS_Port ∗ 〉 NULL};ₛ *)
  hoare forward.
  { (* p_v = Vnull *)
    hoare normal pre.
    naive pure intro.
    subst.
    hoare forward.
    pure_intro'.

    (* ∗ err ′ =ₑ 〈 char_t 〉 ′ OS_PORT_ERR_NULL;ₛ *)
    hoare forward.
    unfold OSPortAddToChannel_aspec.
    cbn [spec_code_cons].
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_choice1;[ | | intros s Hs; exact Hs].
    1,2: can_change_aop_solver'. 
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_seq_end;[ | | intros s Hs; exact Hs].
    1,2: can_change_aop_solver'.
    eapply rete_rule.
    intros s Hs.
    split.
    { unfold OSPortAddToChannelPost'.
    sep normal.
    sep eexists.
    sep autocancel.
    sep split;[ |cbn;eauto].
    left.
    sep split;eauto. }
    symbolic_execution.

    hoare forward.
    pure_intro'.
    destruct H;tryfalse.
  }
  

  rename H1 into Herrtp.  rename Hdomain_type into H3.
  hoare forward.
  { destruct v'. pauto. } 
  { instantiate (1:= Afalse).
    pure_intro'.
    destruct v'.
    simpl in H17. tryfalse. }
  hoare forward.
  hoare normal pre.
  pure_intro'.
  destruct v' as (p_b & p_i).
  rename v'0 into p1. rename v'1 into p2.  rename v'2 into tcbl1. 
  rename v'3 into tcbcur. rename v'4 into tcbl2. rename v'5 into rtbl. rename v'6 into tcbls.
  rename v'7 into ecbls. rename v'8 into vhold.
  rename v'9 into scapl. rename v'10 into mcapl. rename v'11 into qcapl.
  rename v'12 into dportlptr. rename v'13 into dportl1. rename v'14 into dport.
  rename v'15 into dportl2. rename v'16 into dportmsgll1. rename v'17 into msgl. 
  rename v'18 into dportmsgll2. rename v'19 into dpptrl.
  rename v'20 into otherppl. rename v'21 into otherpl. rename v'22 into othermsgll. 
  rename v'23 into kportvl. 
  rename v'24 into kportl.  rename v'25 into kportfptr. 
  rename v'26 into kportfl. rename v'27 into chanvl. rename v'28 into chanl.
  rename v'29 into chandstkportll.  rename v'30 into chanfptr. rename v'31 into chanfl. 
  rename v'32 into dportls1. rename v'33 into abport.
  rename v'34 into portID. rename v'35 into portattrv. rename v'36 into portattrvl.


  rename H into Hattrporid. rename H1 into Hattrvl_type.
  rename H4 into H. rename H5 into H1. rename H6 into H4. rename H7 into H5. rename H8 into H6.
  rename H9 into H7.  
  
  destruct H as [H Hinecb]. 
  rename H10 into Hvsem. rename H11 into Hchtail.
  rename H12 into Hportch. rename H13 into Hqueuechan. 
  subst. clear H17.
  unfold RH_CurTCB in H15. destruct H15 as (pri & st & msg & sus & H8).
  
  unfold AOSDomainPortPtrList.
  hoare normal pre.
  hoare name lift dmportp_sll pre.
  eapply backward_rule1.
  { eapply dmportp_sllseg_app'_frm; eauto. }
  cbn [dmportp_sllseg].
  hoare normal pre; pure_intro'.
  rename v'1 into pptr. rename v' into p_nextv. 
  (* If (OSRunning ′ &&ₑ (port_ptr ′ .. coreNum !=ₑ ′ DNUM
     ||ₑ port_ptr ′ .. OSEventType !=ₑ ′ OS_EVENT_TYPE_PORT
     ||ₑ OSTCBCur ′ .. OSTCBY !=ₑ port_ptr ′ .. domain))
  {∗ err ′ =ₑ 〈 char_t 〉 ′ OS_ERR_PARTITION_UNMAPPED;ₛ
  RETURN 〈 OS_Port ∗ 〉 NULL};ₛ *)
  destruct abport as (((((((pcn & pd) &  pid) &  pdir) &  pst) & pintick) & poutick) & pt).
  eapply seq_rule.
  {
    eapply ift_rule''; [symbolic_exe_port|idtac].
    { clear - Hinecb H4.
      eapply Forall_forall with (x:= (p_b,p_i)) in Hinecb.
      auto.
      eapply nth_error_In;eauto. }
    instantiate (1:= Afalse).
    hoare normal pre.
    pure intro.
    exfalso.
    clear - H9.
    rewrite ! Int.eq_true in H9.
    destruct (Int.eq (pri >>ᵢ $ 3)
    ($ Z.of_nat pd));mauto.
  }
  hoare forward.
  pure_intro'.
  clear H9.
  (* flag ′ =ᶠ portBindCheck (·port_ptr ′ .. portID, channelID ′·);ₛ *)
  assert ( $ Z.of_nat pid = portID) .
  {  clear - H6 Hattrporid.
     destruct H6 as [? _].
     unfold Domainport_nat_P in *.
     simpljoin1.
     rewrite H3 in Hattrporid.
     inversion Hattrporid.
     subst portID.
     unfold nat_of_Z.
     rewrite Z2Nat.id by (apply Int.unsigned_range_2).
     rewrite Int.repr_unsigned. auto.
  }
  subst portID.
  eapply seq_rule.
  eapply calle_rule_lvar';[
      cbn;unfold portBindCheck_spec;eauto | 
      intros; do 5 try 
      (apply rvl_elim;[ sep_get_port_rv | ]);
      first [apply rvl_nil | simpl;auto]  | 
       |
      idtac |
      idtac |
      simpl;eauto | 
      sep_unfold_funpost |
      sep_unfold_funpre 
      ].
  { (* ==> pre*)
    intros s Hs. unfold_spec. 
    sep normal. sep eexists. sep autocancel.
    sep pauto;try eauto.
    destruct H6. 
    unfold Domainport_nat_P in H6.
    clear - H6.
    simpljoin1.
    clear - H5.
    pose proof Int.unsigned_range_2 x0 as [? _].
    remember (Int.unsigned x0) as z.
    clear Heqz.
    unfold nat_of_Z.
    rewrite Z2Nat.id by auto.
    unfold PORT_NUMS in *.
    assert (0 = z \/ 0 < z) by lia. clear H.
    destruct H0.
    left. subst. clear. mauto.
    right.
    split.  mauto.  apply zlt_true. auto.
    mauto. apply zlt_true. auto.
  }
  good_frm_sovler. split;go. 
  { unfold retpost,portBindCheckPost, getasrt, portBindCheckPost'. 
    intros. sep destruct H9. sep split in H9. subst.
    clear H9. simpljoin1. destruct H13. 
    simpljoin1. auto. 
    simpljoin1.
    destruct H16;simpljoin1. auto.
    destruct H22;simpljoin1; auto. }
  { intros s Hs. eexists. sep auto. }
  { intros s Hs. eexists. sep auto. }
  unfold getasrt; unfold portBindCheckPost, portBindCheckPost'.
  naive pure intro.
  inversion H9. subst v'0 v'1. clear H9.
  inversion H13. subst v'2 v'3 v'4 v'5 v'6 v'7 v'8 . clear H13.
  clear flag_v.
  rename v' into flag_v.
  destruct H14 as (pavl & en & ? ).
  destruct H9 as [ [? ?] | [? ?]].
  { inversion H9;subst flag_v.
    (* If (flag ′ ==ₑ ′ 0){ *)
    hoare forward.
    instantiate (1:= Afalse).
    pure intro.
    hoare forward.
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_choice1;[ | | intros s Hs; exact Hs].
    1,2: can_change_aop_solver'. 
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_seq_end;[ | | intros s Hs; exact Hs].
    1,2: can_change_aop_solver'. 
    (* RETURN 〈 OS_Port ∗ 〉 NULL *)
    unfold OSPortAddToChannelPost', AOSDomainPortPtrList.
    hoare forward.
    { port_combine.
      sep autocancel.
      instantiate (3:= chan_v).
      right.
      sep normal.
      sep eexists.
      sep autocancel.
      instantiate (1:= (p_b, p_i)).
      sep pauto;eauto.
      2:{ unfold RLH_PortPtrINecb. split; auto. }
      { left.
        split;[splits;eauto | ].
        unfold OSPortAddToChannel_retvalue_case1.
        right. right. right. right. right.
        auto.
      }
    }
    reflexivity.
    hoare forward.
    pure intro.
    exfalso.
    clear - H14. destruct H14;tryfalse.  }
  destruct H13 as [parid [dmvl  [? [? ?]]]].
  destruct H15 as [[? ?] | [? ?]].
  { inversion H16;subst flag_v.
    (* If (flag ′ ==ₑ ′ 0) *)
    hoare forward.
    instantiate (1:= Afalse).
    (* ∗ err ′ =ₑ 〈 char_t 〉 ′ CHECK_ERROR;ₛ *)
    hoare forward.
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_choice1;[ | | intros s Hs; exact Hs].
    1,2: can_change_aop_solver'. 
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_seq_end;[ | | intros s Hs; exact Hs].
    1,2: can_change_aop_solver'.
    (* RETURN  〈 OS_Port ∗ 〉 NULL *)
    unfold OSPortAddToChannelPost', AOSDomainPortPtrList.
    hoare forward.
    { port_combine.
      sep autocancel.
      instantiate (3:= chan_v).
      right.
      sep normal.
      sep eexists.
      sep autocancel.
      instantiate (1:= (p_b, p_i)).
      sep pauto;eauto.
      2:{ unfold RLH_PortPtrINecb. split; auto. }
      { left.
        split;[splits;eauto | ].
        unfold OSPortAddToChannel_retvalue_case1.
        right. right. right. right. right.
        auto.
      }
    }
    reflexivity.
    hoare forward.
    pure intro.
    exfalso.
    clear - H17. destruct H17;tryfalse. 
  }
  destruct H16 as [portchanid [? ?]].
  destruct H17 as [[? ?] | [? ?]].
  { inversion H18;subst flag_v.
    (* If (flag ′ ==ₑ ′ 0) *)
    hoare forward.
    instantiate (1:= Afalse).
    (* ∗ err ′ =ₑ 〈 char_t 〉 ′ CHECK_ERROR;ₛ *)
    hoare forward.
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_choice1;[ | | intros s Hs; exact Hs].
    1,2: can_change_aop_solver'. 
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_seq_end;[ | | intros s Hs; exact Hs].
    1,2: can_change_aop_solver'. 
    (* RETURN  〈 OS_Port ∗ 〉 NULL *)
    unfold OSPortAddToChannelPost', AOSDomainPortPtrList.
    hoare forward.
    { port_combine.
      sep autocancel.
      instantiate (3:= chan_v).
      right.
      sep normal.
      sep eexists.
      sep autocancel.
      instantiate (1:= (p_b, p_i)).
      sep pauto;eauto.
      2:{ unfold RLH_PortPtrINecb. split; auto. }
      { left.
        split;[splits;eauto | ].
        unfold OSPortAddToChannel_retvalue_case1.
        right. right. right. right. right.
        auto.
      }
    }
    reflexivity.
    hoare forward.
    pure intro.
    exfalso.
    clear - H19. destruct H19;tryfalse. 
  }
  inversion H18;subst flag_v.
  (* If (flag ′ ==ₑ ′ 0) *)
  hoare forward.
  { instantiate (1:= Afalse).
    pure intro.
    exfalso.
    clear - H19. mauto. }
  hoare forward.
  pure_intro'.
  clear H19.
  (* kport ′ =ₑ OSKernelPortIDTbl ′ [port_ptr ′ .. portID];ₛ *)
  hoare name lift AOSKernelPortIDTbl pre.
  eapply R_Kernelport_DomainPort_init_nth_getsome  with (pptr := (p_b, p_i))in H1 as ?;auto.
  (* port bind to kport or not *)
  destruct H18.
  2: { (* not bind. *)
    destruct H18 as (pidv & Hporid & Hnthkpvl & Hnthkpl).
    assert (pidv = ($ Z.of_nat pid)).
    {  clear -H6 Hporid.  unfold DomainportNode_P in *.
    destruct H6 as [? _].
    unfold Domainport_nat_P in *.
    simpljoin1.
    rewrite Hporid in H3. inversion H3. subst.
    unfold nat_of_Z. rewrite Z2Nat.id.
    rewrite Int.repr_unsigned. auto.
    apply Int.unsigned_range_2.
    }
    subst pidv.
    unfold AOSKernelPortIDTbl.
    hoare normal pre.
    naive pure intro.
    destruct H18.
    hoare name lift (Alvarmapsto kport) pre.
    hoare name lift Aop pre.
    assert (Int.unsigned ($ Z.of_nat pid) <  64).
    { clear -H6.  unfold DomainportNode_P in *.
    destruct H6 as [? _].
    unfold Domainport_nat_P in *.
    simpljoin1.
    unfold nat_of_Z. rewrite Z2Nat.id.
    rewrite Int.repr_unsigned. unfold PORT_NUMS in *. clear - H5. mauto.
    clear. apply Int.unsigned_range_2.
    }
    eapply seq_rule.
    eapply assign_rule_lvar;[ 
    intro s; split; intro Hs; exact Hs|
    symbolic_exe_port | apply assign_type_match_true; simpl; auto | li_sepauto li ].
    lia.
    rewrite H20. unfold PORT_NUMS, nat_of_Z.  lia.
    2: { eapply nth_val_nth_val'_some_eq.
         eapply nth_val_nth_error;eauto. }
    eauto.
    (* channel ′ =ₑ OSChannelIDTbl ′ [channelID ′];ₛ *)
    assert (chan_v = portchanid).
    { apply Int_eq_dec in H17.
      auto.
    }
    subst chan_v.
    assert (Int.unsigned portchanid < 32).
    { clear - H0 Heqfa.
      unfold CHANNEL_NUMS in *.
      simpl_intltbool.
      lia. 
    }
    hoare name lift AOSChannelIDTbl pre.
    unfold AOSChannelIDTbl.
    hoare normal pre.
    naive pure intro.
    destruct H23.
    destruct (nth_error chanvl  (Z.to_nat (Int.unsigned portchanid))) as [chan | ] eqn: Hnthcha.
    2:{ eapply nth_error_None in Hnthcha.
        exfalso.
        rewrite H25 in Hnthcha.
        unfold nat_of_Z, CHANNEL_NUMS in Hnthcha.
        lia.
    }
    eapply nth_error_split in Hnthcha as (chanvl1 & chanvl2 & ? & Hlenchanvl1).
    subst chanvl.
    apply array_type_vallist_match_app in H23 as ?.
    destruct H26 as [_ [? _]]. 
    assert (nth_val' (Z.to_nat (Int.unsigned portchanid)) (chanvl1 ++ chan :: chanvl2) = chan) as Hnthvalchan.
    {  erewrite nth_val_nth_val'_some_eq;eauto. eapply nth_val_nth_error. rewrite <- Hlenchanvl1. apply nth_error_middle. }
    hoare name lift (Alvarmapsto channel) pre.
    hoare name lift Aop pre.
    eapply seq_rule.
    eapply assign_rule_lvar;[ 
    intro s; split; intro Hs; exact Hs|
    symbolic_exe_port | apply assign_type_match_true; simpl; auto | li_sepauto li ].
    auto.
    rewrite H25. unfold CHANNEL_NUMS, nat_of_Z. lia.
    rewrite Hnthvalchan. auto.
   (* If (channel ′ ==ₑ 〈 OS_Channel ∗ 〉 NULL)
    {∗ err ′ =ₑ 〈 char_t 〉 ′ OS_CHANNEL_ERR_NULL;ₛ
        RETURN re ′};ₛ *)
    hoare forward.
    rewrite Hnthvalchan. clear - H26. destruct chan;tryfalse;auto.
    rewrite Hnthvalchan. clear - H26. destruct chan;tryfalse;auto. destruct a. cbn. auto.
    { (* if yes *)
      instantiate (1:= Afalse).
      hoare normal pre.
      pure_intro'.
      rule_type_val_match_elim.
      rewrite Hnthvalchan in *.
      destruct H26 as [ |  [[? ?] ?]];subst.
      2:{ exfalso.
          simpl in H27. tryfalse. }
      (* ∗ err ′ =ₑ 〈 char_t 〉 ′ OS_CHANNEL_ERR_NULL;ₛ *)
      hoare forward.
      hoare abscsq;[apply noabs_oslinv | | ].
      eapply absinfer_choice1;[ | | intros s Hs; exact Hs].
      1,2: can_change_aop_solver'. 
      hoare abscsq;[apply noabs_oslinv | | ].
      eapply absinfer_seq_end;[ | | intros s Hs; exact Hs].
      1,2: can_change_aop_solver'. 
      (* RETURN re ′ *)
      unfold OSPortAddToChannelPost', AOSDomainPortPtrList.
      hoare forward.
      2: cbn;reflexivity.
      sep autocancel.
      right.
      port_combine.
      unfold AOSChannelIDTbl, AOSKernelPortIDTbl.
      sep normal. sep eexists.
      sep autocancel.
      instantiate (1:= (p_b, p_i)).
      sep pauto;eauto.
      2: unfold RLH_PortPtrINecb;auto.
      left.
      split;[splits;auto | ].
      unfold OSPortAddToChannel_retvalue_case1.
      right. left.
      rewrite <- Hlenchanvl1.  rewrite nth_error_middle.
      split;auto. }
    (* if wrong *)
    hoare forward.
    hoare normal pre.
    pure_intro'.
    rule_type_val_match_elim.
    rewrite Hnthvalchan in *.
    destruct H26 as [ |  [(chan_b& chan_i) ?]];subst.
    { exfalso.
      simpl in H27. 
      destruct H27;tryfalse. }
    (* If (kport ′ ==ₑ 〈 OS_K_Port ∗ 〉 NULL)
    {∗ err ′ =ₑ 〈 char_t 〉 ′ OS_PORT_ID_INVALID;ₛ
    RETURN re ′};ₛ *)
    hoare forward.
    instantiate (1:= Afalse).
    2:{ hoare forward.
        pure_intro'.
        exfalso.
        destruct H26;tryfalse. }
    pure_intro'. clear H26 H28 H29.
    (* ∗ err ′ =ₑ 〈 char_t 〉 ′ OS_PORT_ID_INVALID;ₛ
    RETURN re ′ *)
    hoare forward.
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_choice1;[ | | intros s Hs; exact Hs].
    1,2: can_change_aop_solver'. 
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_seq_end;[ | | intros s Hs; exact Hs].
    1,2: can_change_aop_solver'. 
    unfold OSPortAddToChannelPost', AOSDomainPortPtrList.
    hoare forward.
    2: cbn;reflexivity.
    sep autocancel.
    right.
    port_combine.
    unfold AOSChannelIDTbl, AOSKernelPortIDTbl.
    sep normal. sep eexists.
    sep autocancel.
    instantiate (1:= (p_b, p_i)).
    sep pauto;eauto.
    2: unfold RLH_PortPtrINecb;auto.
    left.
    split;[splits;auto | ].
    unfold OSPortAddToChannel_retvalue_case1.
    right. right. left.
    eexists.
    splits;eauto.
  }
  destruct H18 as (pidv & kpptr & kp & Hporid & Hntnkpvl & Hnthkpl & Htykp & Hkpid & Hkpdm & Hkpcn).
  assert (pidv = ($ Z.of_nat pid)).
  {  clear -H6 Hporid.  unfold DomainportNode_P in *.
  destruct H6 as [? _].
  unfold Domainport_nat_P in *.
  simpljoin1.
  rewrite Hporid in H3. inversion H3. subst.
  unfold nat_of_Z. rewrite Z2Nat.id.
  rewrite Int.repr_unsigned. auto.
  apply Int.unsigned_range_2.
  }
  subst pidv.
  unfold AOSKernelPortIDTbl.
  hoare normal pre.
  naive pure intro.
  destruct H18.
  hoare name lift (Alvarmapsto kport) pre.
  hoare name lift Aop pre.
  assert (Int.unsigned ($ Z.of_nat pid) <  64).
  { clear -H6.  unfold DomainportNode_P in *.
  destruct H6 as [? _].
  unfold Domainport_nat_P in *.
  simpljoin1.
  unfold nat_of_Z. rewrite Z2Nat.id.
  rewrite Int.repr_unsigned. unfold PORT_NUMS in *. clear - H5. mauto.
  clear. apply Int.unsigned_range_2.
  }
  eapply seq_rule.
  eapply assign_rule_lvar;[ 
  intro s; split; intro Hs; exact Hs|
  symbolic_exe_port| apply assign_type_match_true; simpl; auto | li_sepauto li ].
  lia. rewrite H20. unfold PORT_NUMS,nat_of_Z. lia.
  2: { eapply nth_val_nth_val'_some_eq.
      eapply nth_val_nth_error;eauto. }
  eauto.
  (* channel ′ =ₑ OSChannelIDTbl ′ [channelID ′];ₛ *)
  assert (chan_v = portchanid).
  { apply Int_eq_dec in H17.
    auto.
  }
  subst chan_v.
  assert (Int.unsigned portchanid < 32).
  { clear - H0 Heqfa.
    unfold CHANNEL_NUMS in *.
    simpl_intltbool.
    lia. 
  }
  hoare name lift AOSChannelIDTbl pre.
  unfold AOSChannelIDTbl.
  hoare normal pre.
  naive pure intro.
  destruct H23.
  destruct (nth_error chanvl  (Z.to_nat (Int.unsigned portchanid))) as [chan | ] eqn: Hnthcha.
  2:{ eapply nth_error_None in Hnthcha.
      exfalso.
      rewrite H25 in Hnthcha.
      unfold nat_of_Z, CHANNEL_NUMS in Hnthcha.
      lia.
  }
  eapply nth_error_split in Hnthcha as (chanvl1 & chanvl2 & ? & Hlenchanvl1).
  subst chanvl.
  apply array_type_vallist_match_app in H23 as ?.
  destruct H26 as [_ [? _]]. 
  assert (nth_val' (Z.to_nat (Int.unsigned portchanid)) (chanvl1 ++ chan :: chanvl2) = chan) as Hnthvalchan.
  {  erewrite nth_val_nth_val'_some_eq;eauto. eapply nth_val_nth_error. rewrite <- Hlenchanvl1. apply nth_error_middle. }
  hoare name lift (Alvarmapsto channel) pre.
  hoare name lift Aop pre.
  eapply seq_rule.
  eapply assign_rule_lvar;[ 
  intro s; split; intro Hs; exact Hs|
  symbolic_exe_port | apply assign_type_match_true; simpl; auto | li_sepauto li ].
  auto.
  rewrite H25. unfold CHANNEL_NUMS, nat_of_Z. lia.
  rewrite Hnthvalchan. auto.
  (* If (channel ′ ==ₑ 〈 OS_Channel ∗ 〉 NULL)
  {∗ err ′ =ₑ 〈 char_t 〉 ′ OS_CHANNEL_ERR_NULL;ₛ
  RETURN re ′};ₛ *)
  hoare forward.
  rewrite Hnthvalchan. clear - H26. destruct chan;tryfalse;auto.
  rewrite Hnthvalchan. clear - H26. destruct chan;tryfalse;auto. destruct a. cbn. auto.
  { (* if yes *)
    instantiate (1:= Afalse).
    hoare normal pre.
    pure_intro'.
    rule_type_val_match_elim.
    rewrite Hnthvalchan in *.
    destruct H26 as [ |  [[? ?] ?]];subst.
    2:{ exfalso.
        simpl in H27. tryfalse. }
    (* ∗ err ′ =ₑ 〈 char_t 〉 ′ OS_CHANNEL_ERR_NULL;ₛ *)
    hoare forward.
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_choice1;[ | | intros s Hs; exact Hs].
    1,2: can_change_aop_solver'. 
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_seq_end;[ | | intros s Hs; exact Hs].
    1,2: can_change_aop_solver'. 
    (* RETURN re ′ *)
    unfold OSPortAddToChannelPost', AOSDomainPortPtrList.
    hoare forward.
    2: reflexivity.
    sep autocancel.
    right.
    port_combine.
    unfold AOSChannelIDTbl, AOSKernelPortIDTbl.
    sep normal. sep eexists.
    sep autocancel.
    instantiate (1:= (p_b, p_i)).
    sep pauto;eauto.
    2: unfold RLH_PortPtrINecb;auto.
    left.
    split;[splits;auto | ].
    unfold OSPortAddToChannel_retvalue_case1.
    right. left.
    rewrite <- Hlenchanvl1.  rewrite nth_error_middle.
    split;auto. }
  (* if no *)
  hoare forward.
  hoare normal pre.
  pure_intro'.
  struct_type_vallist_match_elim_H Htykp.
  rule_type_val_match_elim.
  rewrite Hnthvalchan in *.
  destruct H26 as [ |  [(chan_b& chan_i) ?]];subst.
  { exfalso.
    simpl in H27. 
    destruct H27;tryfalse. }
  (* If (kport ′ ==ₑ 〈 OS_K_Port ∗ 〉 NULL)
  {∗ err ′ =ₑ
    〈 char_t 〉 ′ OS_PORT_ID_INVALID;ₛ
  RETURN re ′};ₛ *)
  hoare forward.
  destruct kpptr;auto.
  { instantiate (1:= Afalse).
    pure_intro'.
    destruct kpptr.
    simpl in H26.
    tryfalse.
  }
  hoare forward.
  pure_intro'.
  clear H26.
  (* semaphore ′ =ₑ channel ′ .. semaphore;ₛ *)
  hoare name lift ChannelNode pre.
  eapply backward_rule1.
  eapply ChannelNode_getsome_frm'; eauto.
  eapply nth_error_middle.
  hoare normal pre.
  pure_intro'.
  assert (firstn (length v' + O) (v' ++ Vptr (chan_b, chan_i) :: v'2) = firstn (length chanvl1 + O) (chanvl1 ++ Vptr (chan_b, chan_i) :: chanvl2)) by (rewrite H36, H39;auto).
  rewrite !firstn_app_2 in H37. simpl in H37. rewrite ! app_nil_r in H37. subst v'.
  apply app_inv_head in H36.
  inversion H36. subst v'2.
  clear H36 H39.
  rename v'0 into chanl1. rename v'3 into chanl2.
  rename v'1 into chandstportll1. rename v'4 into chandstportll2.  
  unfold node; hoare normal pre; pure_intro'.
  remember (v', Int.zero) as chanptr.
  struct_type_vallist_match_elim_H H37.
  remember (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil)   as chan.
  hoare forward.
  { cbn. pauto. }
  (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE) {.. } *)
  hoare name lift resource_get_res pre.
  hoare remember (1:: 2:: nil)%nat pre.
  hoare forward.
  { pauto. }
  { pauto. }
  { pauto. }
  { (* condition true :  semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE *)
    instantiate (1:=Afalse \\// 
    [| Int.eq i3 ($ DEFAULT_CHANNLE_SEMAPHROE) = false |] ** 
    <|| cslsemrel (Z.to_nat (Int.unsigned i3));;
        END None;; aop ||> **
    LV resource_get_res @ char_t |-> (V$ 1) ** H48 ).
    pure_intro'.
    assert (Int.eq i3 ($ DEFAULT_CHANNLE_SEMAPHROE) = false) by pauto.
    clear H49 H50 H51.
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_choice2;[ | | intros s Hs; exact Hs]. 1,2: can_change_aop_solver'.
    remember (v', Int.zero) as chanptr.
    assert (vsem = Vint32 i3).
    { eapply Hvsem;eauto.
      rewrite <- Hlenchanvl1, <- H42. eapply nth_error_middle.
      cbn. auto. 
    }
    subst vsem.
    (* CSLSEMACC (semaphore ′, resource_get_res ′);ₛ *)
    unfold Semacc_err, Semacc_succ. 
    hoare name lift resource_get_res pre.
    hoare remember (2:: 1:: nil)%nat pre.
    eapply seq_rule.
    { eapply cslsemacc_rule'.
    { subst. can_change_aop_solver'.  }
    { rewrite Z2Nat.id. 1,2: eapply Int.unsigned_range_2. }
    { subst H49. 
      rewrite Z2Nat.id by (apply Int.unsigned_range).
      rewrite Int.repr_unsigned.
      symbolic execution.
      pauto. }
    { intros s Hs. subst. unfold p_local in Hs. unfold CurLINV. sep auto. }
    { intros s Hs. subst. unfold p_local in Hs. unfold CurLINV. sep auto. } }
    hoare forward.
    { (* resource = 0 *)
      subst H49.
      (* If (resource_get_res ′ ==ₑ 〈 char_t 〉 ′ 0) { .. } *)
      hoare forward.
      (* ∗ err ′ =ₑ 〈 char_t 〉 ′ OS_CHANNEL_ERR_BEING_USED;ₛ
      RETURN re *)
      pure_intro'.
      instantiate (1:= Afalse).
      hoare abscsq;[apply noabs_oslinv | | ].
      eapply absinfer_seq_end;[ | | intros s Hs; exact Hs].
      1,2: can_change_aop_solver'. 
      hoare forward.
      unfold OSPortAddToChannelPost', AOSDomainPortPtrList.
      hoare forward.
      2: reflexivity.
      sep autocancel.
      port_combine.
      chann_combine chanvl1 chanvl2.
      right.
      unfold AOSChannelIDTbl, AOSKernelPortIDTbl.
      sep normal. sep eexists.
      sep autocancel.
      instantiate (1:= (p_b, p_i)).
      sep pauto;eauto.
      left.
      split;[splits;eauto | ].
      unfold OSPortAddToChannel_retvalue_case1.
      right;right;right;left.
      do 3 eexists.
      splits.
      rewrite <- Hlenchanvl1. eapply nth_error_middle.
      rewrite <- Hlenchanvl1, <- H42. eapply nth_error_middle.
      cbn. eauto. 1,2,3: auto.
      unfold RLH_PortPtrINecb. split;auto.
      cbn. pauto.

      destruct H49.
      left. sep auto.
      exfalso. sep split in H49.
      clear -H50.
      destruct H50; mauto. }
    { (* resource ≠ 0 *)
      subst H49.
      (* If (resource_get_res ′ ==ₑ 〈 char_t 〉 ′ 0) { .. } *)
      hoare forward.
      { instantiate (1:= Afalse).
      pure_intro'.
      exfalso.
      clear -H49.
      pauto. }
      destruct H49.
      left;sep auto.
      right.
      sep normal in H49.
      unfold Semrelease in H49.
      sep eexists.
      sep autocancel.
      sep auto. } }
  hoare forward.
  -  (* 核间通信*)
    pure_intro'.
    hoare forward.
    pure_intro'.
    clear H49 H50 H51.
    (* If (kport ′ .. channel !=ₑ 〈 OS_Channel ∗ 〉 NULL) { .. } *)
    hoare name lift kportNode_P pre.
    eapply backward_rule1.
    { eapply kportNode_P_getsome_frm;eauto. }
    pure_intro'.
    rename v'1 into kportvl1. rename v'2 into kportvl2. rename v'0 into kp_b.
    rename v'3 into kportl1.  rename v'4 into kportl2.
    remember (Vint32 i2 :: Vint32 i1 :: x0 :: x1 :: Vint32 i0 :: Vint32 i :: x4 :: nil)  as kp.
    assert (isptr x1).
    { subst kp; clear - H54.
      simpl in H54. simpljoin1.
      destruct x1;tryfalse.
      unfold isptr. cbn;auto.
      unfold isptr. eauto. }
    eapply seq_rule.
    hoare name lift (Alvarmapsto kport) pre.
    hoare name lift Aop pre.
    eapply ift_rule'';[ symbolic_exe_port | ].
    1,2: subst;pauto;destruct H49 as [ | [[? ?] ?]];subst;cbn;auto.
    { (* if true *)
      instantiate (1:= Afalse).
      pure_intro'. 
      remember (Vint32 i2 :: Vint32 i1 :: x0 :: x1 :: Vint32 i0 :: Vint32 i :: x4 :: nil)  as kp.
      destruct H49 as [ | [[? ?] ?]];subst x1.
      { exfalso. clear - H50. cbn in H50. mauto. }
      (* ∗ err ′ =ₑ 〈 char_t 〉 ′ OS_ERR_PORT_HAVE_BEEN_BINDED;ₛ *)
      hoare forward.
      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE) { .. } *)
      hoare forward;pauto.
      pure_intro'.
      unfold Semrelease.
      eapply cslsemrel_rule.
      { can_change_aop_solver'. }
      rewrite Z2Nat.id. 1,2: apply Int.unsigned_range_2.
      { rewrite Z2Nat.id by (apply Int.unsigned_range_2).  
        rewrite ! Int.repr_unsigned.
        symbolic_execution. 
        clear - H39. 
        pauto. }
      { intros s Hs. subst. unfold p_local in Hs. unfold CurLINV. sep auto. }
      hoare forward.
      { pure_intro'.
        hoare abscsq;[apply noabs_oslinv | | ].
        eapply absinfer_seq_end;[ | | intros s Hs; exact Hs].
        1,2: can_change_aop_solver'. 
        (* RETURN re ′ *)
        unfold OSPortAddToChannelPost', AOSDomainPortPtrList.
        hoare forward.
        2: reflexivity.
        sep autocancel.
        right.
        port_combine. chann_combine chanvl1 chanvl2.  kport_combine kportvl1 kportvl2.
        unfold AOSKernelPortIDTbl, AOSChannelIDTbl.
        sep normal. sep eexists.
        sep autocancel.
        instantiate (1:= (p_b, p_i)).
        sep pauto;eauto.
        left.
        split;[splits;eauto | ].
        unfold OSPortAddToChannel_retvalue_case1.
        do 4 right. left.
        do 4 eexists.
        splits;eauto.
        cbn;auto.
        unfold RLH_PortPtrINecb;split;auto.
        lia.
        pauto.
      }
      pure_intro'.
      exfalso.
      rewrite H48 in H49.
      clear - H49.
      destruct H49;mauto.
    }
    (* if false *)
    hoare forward.
    pure_intro'.
    remember (Vint32 i2 :: Vint32 i1 :: x0 :: x1 :: Vint32 i0 :: Vint32 i :: x4 :: nil)  as kp.
    destruct H49 as [ | [[? ?] ?]];subst x1.
    2: { exfalso. clear - H50. cbn in H50. mauto. }
    clear H27 H50.
    cbn in H41. inversion H41;subst v'6.
    cbn in H40. inversion H40;subst v'5. clear H40 H41.
    (* IF (port_ptr ′.. os_code_defs.direction ==ₑ ′ SOURCE) { .. } *)
    hoare name lift (Astruct (v', Int.zero) OS_Channel) pre.
    hoare name lift (Astruct') pre.
    hoare name lift Aop pre.
    hoare remember (1:: 2:: 3:: nil)%nat pre.
    eapply seq_rule.
    hoare name lift (Alvarmapsto port_ptr) pre.
    hoare name lift Aop pre.
    eapply if_rule2';[ subst;symbolic_exe_port | | ].
    + (* SOURCE PORT *)
    instantiate (1:= ( <|| END None ;; aop ||>  ** 
    [| pdir = SourceP |] **
    Astruct' (kp_b, Int.zero) OS_K_Port_Seg_dls (Vint32 i2 :: Vint32 portchanid
       :: x0 :: Vptr (v', Int.zero) :: Vint32 i0 :: Vint32 i :: nil) **
    Astruct (v', Int.zero) OS_Channel
    (Vint32 i6 :: V$ 1 :: Vint32 i4 :: Vint32 i3
             :: x3 :: x5 :: Vptr (kp_b, Int.zero) :: x7 :: nil) **
    H27)).
    naive pure intro.
    destruct pdir.
    2:{ exfalso. clear - H40. simpljoin1. unfold DESTINATION, SOURCE in *. mauto. }
    clear H40.
    eapply OSPortAddToChannel_outcore_SourcePort;eauto.
    + (* DESTINATION PORT *)
    pure_intro'.
    destruct pdir.
    { exfalso. clear - H40. unfold DESTINATION, SOURCE in *. mauto. }
    assert (Int.unsigned i4 <= 254).
    { eapply Hqueuechan;eauto.
      rewrite <- Hlenchanvl1, <- H42. apply nth_error_middle.
      rewrite <- Hlenchanvl1, <- H43;apply nth_error_middle.
      clear - H6.
      unfold DomainportNode_P, Domainport_direction_P in H6.
      simpljoin1. auto.
      cbn. auto. }
    eapply backward_rule2.
    eapply portaddtochannelproof_outcore_destionation;try eassumption.
    reflexivity.
    intros s Hs.
    sep autocancel.
    + hoare forward.
      * naive pure intro.
        clear H41. subst pdir.
        eapply OSPortAddToChannel_SourcePort_ret;eauto.
      * naive pure intro.
        destruct pdir.
        { clear - H55.
          unfold SOURCE in *.
          exfalso.
          destruct H55;
          tryfalse.
        }
       rename v'0 into head.
       rename v'1 into srcpv.
       rename v'2 into dportl.
       rename v'3 into dportmsgll.
       eapply OSPortAddToChannel_DestinationPort_ret;try eassumption.
       subst.
       cbn.
       auto.
  -  (* 核内通信*)
    pure_intro'.
    assert (Int.eq i3 ($ DEFAULT_CHANNLE_SEMAPHROE) = true).
    { destruct (Int.eq i3 ($ DEFAULT_CHANNLE_SEMAPHROE));auto.
      destruct H49;tryfalse. 
    }
    clear H49. 
    hoare abscsq;[apply noabs_oslinv | | ].
    eapply absinfer_choice1;[ | | intros s Hs; exact Hs].
    1,2: can_change_aop_solver'.
    (* If (kport ′ .. channel !=ₑ 〈 OS_Channel ∗ 〉 NULL) { .. } *)
    hoare name lift kportNode_P pre.
    eapply backward_rule1.
    { eapply kportNode_P_getsome_frm;eauto. }
    pure_intro'.
    rename v'1 into kportvl1. rename v'2 into kportvl2. rename v'0 into kp_b.
    rename v'3 into kportl1.  rename v'4 into kportl2.
    remember (Vint32 i2 :: Vint32 i1 :: x0 :: x1 :: Vint32 i0 :: Vint32 i :: x4 :: nil)  as kp.
    assert (isptr x1).
    { subst kp; clear - H54.
      simpl in H54. simpljoin1.
      destruct x1;tryfalse.
      unfold isptr. cbn;auto.
      unfold isptr. eauto. }
    eapply seq_rule.
    hoare name lift (Alvarmapsto kport) pre.
    hoare name lift Aop pre.
    eapply ift_rule'';[ symbolic_exe_port | ].
    1,2: subst;pauto;destruct H49 as [ | [[? ?] ?]];subst;cbn;auto.
    { (* if true *)
      instantiate (1:= Afalse).
      pure_intro'. 
      remember (Vint32 i2 :: Vint32 i1 :: x0 :: x1 :: Vint32 i0 :: Vint32 i :: x4 :: nil)  as kp.
      destruct H49 as [ | [[? ?] ?]];subst x1.
      { exfalso. clear - H50. cbn in H50. mauto. }
      (* ∗ err ′ =ₑ 〈 char_t 〉 ′ OS_ERR_PORT_HAVE_BEEN_BINDED;ₛ *)
      hoare forward.
      (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE) { .. } *)
      hoare forward;pauto.
      pure_intro'.
      { instantiate (1:= Afalse).
      rewrite H48 in H49.
      exfalso.
      clear - H49.
      mauto. }
      hoare forward.
      pure_intro'.
      hoare abscsq;[apply noabs_oslinv | | ].
      eapply absinfer_seq_end;[ | | intros s Hs; exact Hs].
      1,2: can_change_aop_solver'.
      (* RETURN re ′ *)
      unfold OSPortAddToChannelPost', AOSDomainPortPtrList.
      hoare forward.
      2: reflexivity.
      sep autocancel.
      right.
      port_combine. chann_combine chanvl1 chanvl2.  kport_combine kportvl1 kportvl2.
      unfold AOSKernelPortIDTbl, AOSChannelIDTbl.
      sep normal. sep eexists.
      sep autocancel.
      instantiate (1:= (p_b, p_i)).
      sep pauto;eauto.
      left.
      split;[splits;eauto | ].
      unfold OSPortAddToChannel_retvalue_case1.
      do 4 right. left.
      do 4 eexists.
      splits;eauto.
      cbn;auto.
      unfold RLH_PortPtrINecb;split;auto.
      lia.
      pauto.
    }
    (* if false *)
    hoare forward.
    pure_intro'.
    remember (Vint32 i2 :: Vint32 i1 :: x0 :: x1 :: Vint32 i0 :: Vint32 i :: x4 :: nil)  as kp.
    destruct H49 as [ | [[? ?] ?]];subst x1.
    2: { exfalso. clear - H50. cbn in H50. mauto. }
    clear H27 H50.
    cbn in H41. inversion H41;subst v'6.
    cbn in H40. inversion H40;subst v'5. clear H40 H41.
    (* IF (port_ptr ′.. os_code_defs.direction ==ₑ ′ SOURCE) { .. } *)
    hoare name lift (Astruct (v', Int.zero) OS_Channel) pre.
    hoare name lift (Astruct') pre.
    hoare name lift Aop pre.
    hoare remember (1:: 2:: 3:: nil)%nat pre.
    eapply seq_rule.
    hoare name lift (Alvarmapsto port_ptr) pre.
    hoare name lift Aop pre.
    eapply if_rule2';[ subst;symbolic_exe_port | | ].
    + (* SOURCE PORT *)
    instantiate (1:= ( <|| END None ;; aop ||>  ** 
    [| pdir = SourceP |] **
    Astruct' (kp_b, Int.zero) OS_K_Port_Seg_dls (Vint32 i2 :: Vint32 portchanid
       :: x0 :: Vptr (v', Int.zero) :: Vint32 i0 :: Vint32 i :: nil) **
    Astruct (v', Int.zero) OS_Channel
    (Vint32 i6 :: V$ 1 :: Vint32 i4 :: Vint32 i3
             :: x3 :: x5 :: Vptr (kp_b, Int.zero) :: x7 :: nil) **
    H27)).
    naive pure intro.
    destruct pdir.
    2:{ exfalso. clear - H40. simpljoin1. unfold DESTINATION, SOURCE in *. mauto. }
    clear H40.
    eapply OSPortAddToChannel_incore_SourcePort with (H30 := H27);eauto.
    + (* DESTINATION PORT *)
    pure_intro'.
    destruct pdir.
    { exfalso. clear - H40. unfold DESTINATION, SOURCE in *. mauto. }
    assert (Int.unsigned i4 <= 254).
    { eapply Hqueuechan;eauto.
      rewrite <- Hlenchanvl1, <- H42. apply nth_error_middle.
      rewrite <- Hlenchanvl1, <- H43;apply nth_error_middle.
      clear - H6.
      unfold DomainportNode_P, Domainport_direction_P in H6.
      simpljoin1. auto.
      cbn. auto. }
    eapply backward_rule2.
    eapply portaddtochannelproof_incore_destionation;try eassumption.
    reflexivity.
    intros s Hs.
    sep autocancel.
    + hoare forward.
      * naive pure intro.
        clear H41. subst pdir.
        eapply OSPortAddToChannel_SourcePort_ret;eauto.
      * naive pure intro.
        destruct pdir.
        { clear - H55.
          unfold SOURCE in *.
          exfalso.
          destruct H55;
          tryfalse.
        }
       rename v'0 into head.
       rename v'1 into srcpv.
       rename v'2 into dportl.
       rename v'3 into dportmsgll.
       eapply OSPortAddToChannel_DestinationPort_ret;try eassumption.
       subst.
       cbn.
       auto.
Qed.     

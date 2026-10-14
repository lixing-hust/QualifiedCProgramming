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
Require Import partition_initrules.
Require Import corecommu_rules.

Open Scope code_scope.

Open Scope int_scope.

Ltac hoare_ex_intro ::=
  repeat match goal with
    | |- {| _, _, _, _, _, _ |} |- _  {{ EX _, _ }} _ {{ _ }} =>
      apply ex_intro_rule; intros 
  end.

Lemma update_nth_vallist_middle : forall l1 x l2 y,
  update_nth_vallist (length l1) (l1++x::l2) y = l1++y::l2.
Proof.
  induction l1.
  - intros. simpl. auto.
  - intros.
    simpl.
    rewrite IHl1.
    auto.
Qed.

Lemma QPortCreate_proof:
  forall vl p r logicl ct, 
    Some p =
    BuildPreI os_internal QPortCreate vl logicl QPortCreatePre ct->
    Some r =
    BuildRetI os_internal QPortCreate vl logicl QPortCreatePost ct->
    exists t d1 d2 s,
      os_internal QPortCreate = Some (t, d1, d2, s) /\
      {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  simpljoin1.

  invertsr H.

  rename v' into flag.
  rename v'0 into portptr.
  rename v'1 into aop.
  rename v'2 into vsem.
  rename v'3 into er.
  rename v'4 into dmportp.
  rename i into size.
  rename i0 into portid.
  rename v'6 into msgp.
  rename v'7 into errptr.
  rename v'8 into errv.
  rename v'9 into nest.
  rename v'10 into cportp.
  rename v'11 into dportp.
  rename v'12 into portattrv.
  rename v'13 into portattrvl.
  rename v'14 into chan_v.
  rename v'15 into dmport.
  rename v'16 into dmevetype.
  rename v'17 into curdomain.
  rename v'18 into domainv.
  rename v'19 into domainvl.
  rename v'20 into p1.
  rename v'21 into p2.
  rename v'22 into tcbl1.
  rename v'23 into tcbcur.
  rename v'24 into tcbl2.
  rename v'25 into rtbl.
  rename v'26 into tcbls.
  rename v'27 into ecbls.
  rename v'28 into vhold.
  rename v'29 into scapl.
  rename v'30 into mcapl.
  rename v'31 into qcapl.
  rename v'32 into dportl.
  rename v'33 into dpptrl.
  rename v'34 into dportmsgll.
  rename v'35 into kportvl.
  rename v'36 into kportl.
  rename v'37 into chanvl.
  rename v'38 into chanl.
  rename v'39 into chandstkportll.
  rename v'40 into kportfptr.
  rename v'41 into kportfl.
  rename v'42 into chanfptr.
  rename v'43 into chanfl.
  rename v'44 into otherppl.
  rename v'45 into otherpl.
  rename v'46 into othermsgll.
  rename v'47 into buff.
  rename v'50 into dportls.
  rename v'51 into domn.
  rename v'52 into dir_.
  rename v'53 into absdir.
  rename v'54 into status.
  rename v'55 into intick.
  rename v'56 into outick.

  
  rename H1 into Herrisp.
  rename H2 into Hsize.
  rename H3 into Hmsgisp.
  rename H5 into Hdmisp.
  rename H0 into Hltp.
  rename H6 into Hcisp.
  rename H31 into Hdisp.
  rename H7 into Hpatty.
  rename H8 into Hpat_3.
  rename H9 into Hpat_4.
  rename H10 into Hpat_5.
  rename H11 into Hdmty.
  rename H12 into Hcurdm.
  rename H13 into Hdmtar.
  rename H14 into Htcb.
  rename H15 into Hppi.
  rename H16 into Hkdi.
  rename H17 into Hsem.
  rename H18 into Hcdt.
  rename H19 into Hcs.
  rename H20 into Hchann.
  rename H21 into Habs.
  rename H22 into Hsndmsg.
  rename H23 into Hsizege.
  rename H24 into Hnd_kpf.
  rename H25 into Hpat_2.
  rename H26 into Hdm_sta.
  rename H27 into Hdm_in.
  rename H28 into Hdm_out.
  rename H30 into Hdir_eq.
  rename x0 into wt.
  rename H4 into Hecb_get.
  rename H32 into Hdp_notin.

  assert ((length dmport = 18%nat)%nat).
  { clear - Hdmty.
    destruct dmport; simpl in Hdmty; tryfalse.
    do 18 (destruct Hdmty as [? Hdmty];
    destruct dmport; simpl in Hdmty; tryfalse).
    simpl. auto. }
  rename H into Hdmlen.

  (* port ′ .. portID =ₑ portId ′;ₛ *)
  eapply seq_rule.
  { eapply port_memeber_asgn' with (n := 3%nat).
    { split.
      { intros Hs. sep autocancel. apply Hs. }
        sep pauto. }
    { symbolic_execution. }
    { go. }
    { rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
      { go. } { lia. } }
    { go. } { go. } { go. } { go. }
    { eapply eq_int; tauto. }
    { go. }
    { sep auto. } }
  
  (* port_ptr ′ =ₑ &ₐ OSPortAttrTbl ′ [portId ′];ₛ *)
  unfold Alvarmapsto at 9.
  naive pure intro.
  rename v' into port_b.
  destruct portattrv as [pattrt_b pattrt_i].
  hoare name lift Aop pre.
  eapply seq_rule.
  { eapply assign_rule_general.
    { intros ? Hs.
      eapply symbolic_lemmas.addrof_lvar_rv.
      sep autocancel. apply Hs. }
    { split.
      { intros Hs. sep autocancel. apply Hs. }
      { sep pauto. } }
    { intros ? Hs.
      eapply symbolic_lemmas.addrof_array_elem_rv.
      2: symbolic_execution.
      2: tauto.
      { symbolic_execution. }
      { eauto. } }
    { eapply eq_vptr; eauto. }
    { sep auto. } }
  
  assert (($ Z.of_nat (typelen OSport_attr_t)) = ($ 12)).
  { clear. simpl. auto. }
  rewrite H. clear H.
  assert ((pattrt_b, pattrt_i +ᵢ  Int.mul ($ 12) portid) =
          get_off_addr (pattrt_b, pattrt_i) (Int.mul ($ 12) portid)).
  { unfold get_off_addr, fst, snd. auto. }
  rewrite H. clear H.
  assert (exists (portattrv:addrval), portattrv = (pattrt_b, pattrt_i)) by eauto.
  destruct H as [portattrv H]. rewrite <- H in *.
  clear H pattrt_b pattrt_i.
  hoare remember (2::3::nil)%nat pre.
  eapply backward_rule1.
  { instantiate (1:=LV port_ptr @ OSport_attr_t ∗ |-> Vptr (get_off_addr portattrv (Int.mul ($ 12) portid)) ** H).
    intros ? Hs. sep autocancel.
    unfold Alvarmapsto. exists port_b. sep pauto. }
  subst H. hoare name lift Aop pre.

  apply struct_type_vallist_match_OSport_attr_t in Hpatty.
  destruct Hpatty as [enable [pid [dm [dir [mode [cid [Heq [Henable [Hpid [Hdm Hcid]]]]]]]]]].
  subst portattrvl.
  simpl in Hpat_2, Hpat_3, Hpat_4, Hpat_5.
  invertsr Hpat_4. invertsr Hpat_5.
  invertsr Hpat_2. invertsr Hpat_3.
  (* port ′ .. mode =ₑ port_ptr ′ .. mode;ₛ *)
  eapply seq_rule.
  { eapply port_memeber_asgn' with (n := 5%nat).
    { split.
      { intros Hs. sep autocancel. apply Hs. }
        sep pauto. }
    { symbolic_execution. pauto. }
    { go. }
    { rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
      { go. }
      { rewrite update_nth_val_len_eq. lia. } }
    { go. } { go. } { go. } { go. }
    { eapply eq_int; tauto. }
    { go. }
    { sep auto. } }

  (* port ′ .. os_code_defs.direction =ₑ port_ptr ′ .. os_code_defs.direction;ₛ *)
  eapply seq_rule.
  { eapply port_memeber_asgn' with (n := 4%nat).
    { split.
      { intros Hs. sep autocancel. apply Hs. }
        sep pauto. }
    { symbolic_execution. pauto. }
    { go. }
    { rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
      { go. }
      { repeat rewrite update_nth_val_len_eq. lia. } }
    { go. } { go. } { go. } { go. }
    { eapply eq_int; tauto. }
    { go. }
    { sep auto. } }

  (* port ′ .. domain =ₑ port_ptr ′ .. domain;ₛ *)
  eapply seq_rule.
  { eapply port_memeber_asgn' with (n := 0%nat).
    { split.
      { intros Hs. sep autocancel. apply Hs. }
        sep pauto. }
    { symbolic_execution. pauto. }
    { go. }
    { rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
      { go. }
      { repeat rewrite update_nth_val_len_eq. lia. } }
    { go. } { go. } { go. } { go. }
    { eapply eq_int; tauto. }
    { go. }
    { sep auto. } }
  
  (* port ′ .. OSEventType =ₑ 〈 char_t 〉 ′ OS_EVENT_TYPE_UNUSED;ₛ *)
  eapply seq_rule.
  { eapply assign_rule_general.
    { intros ? Hs.
      eapply symbolic_lemmas.struct_offset_rv.
      { eapply symbolic_lemmas.addrof_deref_rv.
        symbolic_execution. }
      { unfold OS_Port; eauto. }
      { go. } { go. } }
    { unfold get_off_addr.
      assert (Int.zero = ($ 0)) by (clear; mauto).
      rewrite H; clear H. split.
      { intros Hs. sep autocancel. apply Hs. }
      { sep pauto. } }
    { symbolic_execution. }
    { eapply eq_int; tauto. }
    { sep auto. } }
  assert ((Int.modu ($ OS_EVENT_TYPE_UNUSED) ($ Byte.modulus)) = ($ OS_EVENT_TYPE_UNUSED)).
  { clear. unfold OS_EVENT_TYPE_UNUSED. mauto. }
  rewrite H. clear H.
  assert ((fst dmportp, snd dmportp +ᵢ  Int.zero) = 
          get_off_addr dmportp ($ 0)).
  { destruct dmportp; unfold get_off_addr; simpl.
    assert (Int.zero = $ 0) by (clear; mauto).
    rewrite <- H. auto. }
  rewrite H; clear H.

  (* port ′ .. OSQStart =ₑ start ′;ₛ *)
  eapply seq_rule.
  { eapply port_memeber_asgn' with (n := 12%nat).
    { split.
      { intros Hs. sep autocancel. apply Hs. }
        sep pauto. }
    { symbolic_execution. }
    { go. }
    { rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
      { go. }
      { repeat rewrite update_nth_val_len_eq. lia. } }
    { go. } { go. } { go. } { go. }
    { eapply eq_vptr; eauto. }
    { go. }
    { sep auto. } }
  
  (* port ′ .. OSQEnd =ₑ &ₐ start ′ [os_code_defs.size ′];ₛ *)
  destruct msgp as [msgb msgi].
  eapply seq_rule.
  { eapply port_memeber_asgn' with (n := 13%nat).
    { split.
      { intros Hs. sep autocancel. apply Hs. }
        sep pauto. }
    { intros * Hs.
      eapply symbolic_lemmas.addrof_array_elem_rv.
      { symbolic_execution. }
      { symbolic_execution.
        clear - Hsize.
        rewrite int16_max_unsigned_val.
        destruct (Int.unsigned size <=? 65535) eqn: Heq; auto.
        apply Z.leb_gt in Heq. lia. }
      { auto. }
      { auto. } }
    { go. }
    { rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
      { go. }
      { repeat rewrite update_nth_val_len_eq. lia. } }
    { go. } { go. } { go. } { go. }
    { eapply eq_vptr; eauto. }
    { go. }
    { sep auto. } }
  assert (($ Z.of_nat (typelen OSMsg_t)) = ($33)).
  { cbn. clear. mauto. }
  rename H into Hmsglen. rewrite Hmsglen in *.
  unfold fst at 3. unfold snd at 3.
  assert ( (msgb, msgi +ᵢ  Int.mul ($ 33) size) = 
           get_off_addr (msgb, msgi) (Int.mul ($ 33) size) ).
  { clear. unfold get_off_addr, fst, snd. auto. }
  rewrite H in *. clear H.
  assert ( exists (msgp: addrval), msgp = (msgb, msgi) ) by eauto.
  destruct H as [msgp H]. rewrite <- H in *. clear H msgb msgi.

  (* port ′ .. OSQIn =ₑ start ′;ₛ *)
  eapply seq_rule.
  { eapply port_memeber_asgn' with (n := 14%nat).
    { split.
      { intros Hs. sep autocancel. apply Hs. }
        sep pauto. }
    { symbolic_execution. }
    { go. }
    { rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
      { go. }
      { repeat rewrite update_nth_val_len_eq. lia. } }
    { go. } { go. } { go. } { go. }
    { eapply eq_vptr; eauto. }
    { go. }
    { sep auto. } }
  
  (* port ′ .. OSQOut =ₑ start ′;ₛ *)
  eapply seq_rule.
  { eapply port_memeber_asgn' with (n := 15%nat).
    { split.
      { intros Hs. sep autocancel. apply Hs. }
        sep pauto. }
    { symbolic_execution. }
    { go. }
    { rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
      { go. }
      { repeat rewrite update_nth_val_len_eq. lia. } }
    { go. } { go. } { go. } { go. }
    { eapply eq_vptr; eauto. }
    { go. }
    { sep auto. } }
  
  (* port ′ .. OSQSize =ₑ os_code_defs.size ′;ₛ *)
  eapply seq_rule.
  { eapply port_memeber_asgn' with (n := 16%nat).
    { split.
      { intros Hs. sep autocancel. apply Hs. }
        sep pauto. }
    { symbolic_execution.
      clear - Hsize.
      rewrite int16_max_unsigned_val.
      destruct (Int.unsigned size <=? 65535) eqn: Heq; auto.
      apply Z.leb_gt in Heq. lia. }
    { go. }
    { rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
      { go. }
      { repeat rewrite update_nth_val_len_eq. lia. } }
    { go. } { go. } { go. } { go. }
    { eapply eq_int; split; eauto. }
    { go. clear - Hsize.
      rewrite int16_max_unsigned_val.
      destruct (Int.unsigned size <=? 65535) eqn: Heq; auto.
      apply Z.leb_gt in Heq. lia. }
    { sep auto. } }

  (* port ′ .. OSQEntries =ₑ ′ 0;ₛ *)
  eapply seq_rule.
  { eapply port_memeber_asgn' with (n := 17%nat).
    { split.
      { intros Hs. sep autocancel. apply Hs. }
        sep pauto. }
    { symbolic_execution. }
    { go. }
    { rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
      { go. }
      { repeat rewrite update_nth_val_len_eq. lia. } }
    { go. } { go. } { go. } { go. }
    { eapply eq_int; split; eauto. }
    { go. }
    { sep auto. } }

  (* port ′ .. coreNum =ₑ ′ DNUM;ₛ *)
  eapply seq_rule.
  { eapply port_memeber_asgn' with (n := 2%nat).
    { split.
      { intros Hs. sep autocancel. apply Hs. }
        sep pauto. }
    { symbolic_execution. }
    { go. }
    { rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
      { go. }
      { repeat rewrite update_nth_val_len_eq. lia. } }
    { go. } { go. } { go. } { go. }
    { eapply eq_int; eauto. }
    { go. pose proof dnum_range as Hdum.
      rewrite byte_max_unsigned_val.
      destruct (Int.unsigned ($ DNUM) <=? 255) eqn: Heq.
      { auto. }
      exfalso. clear - Heq Hdum.
      apply Z.leb_gt in Heq.
      assert (Int.unsigned ($ DNUM) = DNUM); [ |lia].
      eapply int_usign_eq. lia.
      rewrite max_unsigned_val; lia. }
    { sep auto. } }

  (* flag ′ =ᶠ portCreateCheck (·portId ′·);ₛ *)
  unfold Alvarmapsto at 10.
  naive pure intro. rename v' into flag_b.
  eapply seq_rule.
  { eapply calle_rule'.
    { go. unfold portCreateCheck_spec. pauto. }
    { intros ? Hs.
      unfold getasrt, portCreateCheckPre, portCreateCheckPre'.
      sep normal. sep eexists. sep autocancel. sep split.
      { apply Hs. }
      { eauto. }
      instantiate (1:=portid); eauto. }
    { good_frm_sovler. }
    { unfold retpost. intros * Hs.
      unfold getasrt, portCreateCheckPost, portCreateCheckPost' in Hs.
      sep destruct Hs; sep split in Hs.
      destruct H0; subst; auto. }
    { intros ? Hs.
      eapply rvl_elim; [ |apply rvl_nil].
      symbolic_execution. f_equal.
      apply inline_bittblfunctions.mutexpost_intlemma1.
      clear - Hltp.
      unfold PORT_NUMS in Hltp.
      apply Intlt_true_is_Zlt in Hltp.
      assert (Int.unsigned ($ 64) = 64) by (clear; mauto).
      lia. }
    { intros ? Hs.
      eapply symbolic_lemmas.lvar_to_lv.
      sep autocancel. apply Hs. }
    { unfold tl_vl_match, type_val_match.
      destruct (Int.unsigned portid <=? Byte.max_unsigned) eqn: Heq.
      { auto. }
      exfalso. clear - Heq Hltp.
      unfold PORT_NUMS in Hltp.
      apply Intlt_true_is_Zlt in Hltp.
      rewrite byte_max_unsigned_val in *.
      apply Z.leb_gt in Heq.
      assert (Int.unsigned ($ 64) = 64) by (clear; mauto).
      lia. }
    { intros * Hs.
      unfold getasrt, portCreateCheckPost, portCreateCheckPost' in Hs.
      sep destruct Hs. sep auto. }
    { intros * Hs.
      unfold getasrt, portCreateCheckPre, portCreateCheckPre' in Hs.
      sep destruct Hs. sep auto. } }
  unfold getasrt, portCreateCheckPost, portCreateCheckPost'.
  naive pure intro.
  invertsr H; invertsr H1.
  hoare remember (9::10::nil)%nat pre.
  eapply backward_rule1.
  { instantiate (1:=LV os_code_defs.flag @ long |-> v' ** H).
    intros ? Hs. sep autocancel.
    unfold Alvarmapsto. exists flag_b. sep pauto. }
  subst H. hoare name lift Aop pre.
  clear flag_b. rename v' into flag_new.

  (* If (flag ′ ==ₑ ′ 0){∗ err ′ =ₑ 〈 char_t 〉 ′ CHECK_ERROR;ₛ RETURN};ₛ *)
  hoare name lift Aop errptr pre.
  destruct H0.
  2:{ inverts H.
      partition_absrulestac absinfer_choice1.
      partition_absrulestac absinfer_seq_end.
      eapply seq_rule.
      { eapply corecommu_rules.ift_nonzero_rule.
        intros.
        exists (Int.one).
        sep split.
        symbolic_execution.
        reflexivity.
        instantiate (1:=Afalse).
        eapply seq_rule.
        { eapply assign_rule_general.
          symbolic_execution. reflexivity.
          symbolic_execution.
          now apply assign_type_match_true.
          intros. sep auto. }
        (* RETURN *)
        partition_absrulestac absinfer_choice1.
        partition_absrulestac absinfer_seq_end.
        assert ((Int.modu ($ CHECK_ERROR) ($ Byte.modulus)) = ($ CHECK_ERROR)).
        { clear. unfold CHECK_ERROR. mauto. }
        rewrite H in *. clear H.
        eapply ret_rule.
        intros * Hs.
        sep normal. sep eexists.
        sep autocancel. sep split.
        { left. sep autocancel. sep split.
          { sep cancel dmportp_sllseg_qport_msg. }
          { auto. } }
        { auto. } { eauto. } { simpl. auto. } }
      apply pfalse_rule. }
  inverts H.
  eapply seq_rule.
  { apply corecommu_rules.ift_zero_rule.
    intros. symbolic_execution. }

  (* OSKernelPortCreate (­port ′, portId ′, err ′­);ₛ *)
  unfold AOSDomainPortPtrList, AOSKernelPortIDTbl.
  naive pure intro. destruct H.
  rename H into Hkpar. rename H1 into Hkplen.
  rename H0 into Hndkp.
  hoare name lift kportNode_P pre.
  eapply backward_rule1.
  { eapply kportNode_P_len_eq_frm. }
  naive pure intro. rename H into Hkpllen.
  eapply seq_rule.
  { eapply call_rule'.
    { cbn; unfold OSKernelPortCreate_spec; eauto. }
    { intros * Hs.
      eapply rvl_elim; [symbolic_execution| ].
      eapply rvl_elim; [symbolic_execution| ].
      eapply rvl_elim; [symbolic_execution|eapply rvl_nil]. }
    { intros * Hs.
      unfold getasrt, OSKernelPortCreatePre, OSKernelPortCreatePre'.
      sep normal; sep eexists. sep autocancel. sep pauto.
      2:{ destruct Hppi. apply r. }
      clear - Hdmty Hltp Hdm Hmsgisp Hsize.
      destruct dmport; simpl in *; tryfalse.
      repeat (destruct Hdmty as [? Hdmty]; split; auto;
      destruct dmport; simpl in *; tryfalse).
      clear. pose proof dnum_range as Hdum.
      rewrite byte_max_unsigned_val.
      destruct (Int.unsigned ($ DNUM) <=? 255) eqn: Heq.
      { auto. }
      exfalso. apply Z.leb_gt in Heq.
      assert (Int.unsigned ($ DNUM) = DNUM); [ |lia].
      eapply int_usign_eq. lia.
      rewrite max_unsigned_val; lia.
      clear - Hsize.
      rewrite int16_max_unsigned_val.
      destruct (Int.unsigned size <=? 65535) eqn: Heq; auto.
      apply Z.leb_gt in Heq. lia. }
    { good_frm_sovler. }
    { unfold getasrt, OSKernelPortCreatePost, OSKernelPortCreatePost'.
      intros * Hs. sep auto. }
    { unfold getasrt, OSKernelPortCreatePre, OSKernelPortCreatePre'.
      intros * Hs. sep auto. }
    { pauto. } }
  unfold getasrt, OSKernelPortCreatePost, OSKernelPortCreatePost'.
  hoare normal pre. naive pure intro.
  invertsr H. invertsr H0.
  rename v' into vret. rename v'3 into verr.
  
  eapply backward_rule1.
  { intros * Hs.
    sep lift 12%nat in Hs.
    eapply disj_split in Hs.
    apply Hs. }
  eapply disj_rule.
  { naive pure intro. invertsr H0.
    clear H1. rename H into Herr.

    (* If (∗ err ′ ==ₑ 〈 char_t 〉 ′ OS_NO_ERR)
      {OSPortAddToChannel (­port_ptr ′ .. channelID, port ′, err ′­)};ₛ *)
    eapply seq_rule.
    { eapply ift_rule'.
      { symbolic_execution.
        { clear - Herr. cbn in *.
          destruct Herr as [? | [? | [? | [? ?]]]];
          rewrite H; clear; pauto. }
        { clear - Herr.
          destruct Herr as [? | [? | [? | [? ?]]]];
          rewrite H; clear; pauto. } }
      { instantiate (1:=Afalse).
        naive pure intro. exfalso.
        destruct H. clear - H Herr.
        destruct Herr as [? | [? | [? | [? ?]]]];
        rewrite H0 in H; pauto. } }
      hoare forward. naive pure intro. clear H.
      (* RETURN *)
      assert (exists i, verr = Vint32 i).
      { clear - Herr; destruct Herr as [? | [? | [? | [? ?]]]]; eauto. }
      destruct H as [verri Herri]. subst verr.
      partition_absrulestac absinfer_choice1.
      partition_absrulestac absinfer_seq_end.
      eapply ret_rule'. intros * Hs.
      sep normal. sep eexists.
      sep name lift errptr in Hs.
      sep autocancel. sep split.
      { left. sep autocancel. sep split.
        { sep cancel dmportp_sllseg_qport_msg. }
        { auto. } { split; auto. } { eauto. } }
      { auto. } { auto. } { simpl; auto. } }
  
  naive pure intro.
  eapply backward_rule1.
  { intros * Hs.
    sep lift 3%nat in Hs.
    eapply disj_split in Hs.
    apply Hs. }
  eapply disj_rule.
  { naive pure intro.
    subst kportfptr verr vret.
    rename H into Hkp_n.
    (* If (∗ err ′ ==ₑ 〈 char_t 〉 ′ OS_NO_ERR)
    {OSPortAddToChannel (­port_ptr ′ .. channelID, port ′, err ′­)};ₛ *)
    eapply seq_rule.
    { eapply ift_rule'.
      { symbolic_execution. }
      { instantiate (1:=Afalse).
        pure intro. exfalso. pauto. } }
      hoare forward. hoare normal pre; pure intro. clear H.
      hoare lift 6%nat pre.
      eapply backward_rule1.
      { intros * Hs. eapply disj_split in Hs. apply Hs. }
      eapply disj_rule.
      { (* RETURN *)
        partition_absrulestac absinfer_choice1.
        partition_absrulestac absinfer_seq_end.
        remember (update_nth_val 11 (update_nth_val 2
                 (update_nth_val 17 (update_nth_val 16
                 (update_nth_val 15 (update_nth_val 14
                 (update_nth_val 13 (update_nth_val 12
                 (update_nth_val 0 (update_nth_val 4
                 (update_nth_val 5 (update_nth_val 3 dmport 
                 (Vint32 portid)) (V$ QUEUE)) (V$ dir_)) 
                 (Vint32 dm)) (Vptr msgp))
                 (Vptr (get_off_addr msgp (Int.mul ($ 33) size))))
                 (Vptr msgp)) (Vptr msgp)) (Vint32 size)) 
                 (V$ 0)) (V$ DNUM)) dportp) as dmport'.
        eapply ret_rule'. intros * Hs.
        sep normal. sep eexists.
        sep name lift errptr in Hs.
        sep autocancel. sep split.
        { right. left. sep autocancel.
          eapply disj_split. left. sep split.
          { sep autocancel.
            instantiate (1:=nil :: dportmsgll).
            instantiate (1:=dmport' :: dportl).
            unfold dmportp_sll in *.
            cbn [dmportp_sllseg].
            sep normal. sep eexists.
            sep autocancel. sep split.
            { right. sep normal. sep eexists.
              sep split.
              { instantiate (1:=buff).
                instantiate (1:=Int.zero).
                instantiate (1:=size).
                instantiate (1:=(get_off_addr msgp (Int.mul ($ 33) size))).
                instantiate (1:=msgp).
                instantiate (1:=msgp).
                instantiate (1:=msgp).
                unfold nat_of_Z in *.
                rewrite Int.unsigned_zero.
                rewrite Z.sub_0_r, Z2Nat.inj_0.
                sep autocancel.
                cbn [dmportp_sllseg_qport_msg].
                sep pauto. }
              { unfold Qport_msg_ptrs_P.
                destruct msgp as [msgb msgi].
                split;[ |split;[ |exists 0 0;split;[ |split;[ |split]]]].
                { simpl snd in Hsndmsg. auto. }
                { rewrite Hmsglen.
                  rewrite Int.repr_unsigned.
                  rewrite Int.mul_commut.
                  reflexivity. }
                { rewrite Hmsglen, Int.mul_commut.
                  rewrite repr_zero, Int.mul_zero.
                  rewrite <- repr_zero.
                  rewrite get_off_addr_0. auto. }
                { rewrite Hmsglen, Int.mul_commut.
                  rewrite repr_zero, Int.mul_zero.
                  rewrite <- repr_zero.
                  rewrite get_off_addr_0. auto. }
                { split; lia. }
                { split; lia. } }
              { split.
                2:{ rewrite Int.unsigned_zero.
                    apply Int.unsigned_range. }
                unfold OS_Port_V_OSQEntries. subst dmport'.
                do 2 (rewrite nth_upd_neqrev'; auto).
                eapply update_nth.
                do 9 (rewrite nth_upd_neqrev'; auto).
                eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
              { split. 2: lia.
                unfold OS_Port_V_OSQSize. subst dmport'.
                do 3 (rewrite nth_upd_neqrev'; auto).
                eapply update_nth.
                do 8 (rewrite nth_upd_neqrev'; auto).
                eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
              { unfold OS_Port_V_OSQOut. subst dmport'.
                do 4 (rewrite nth_upd_neqrev'; auto).
                eapply update_nth.
                do 7 (rewrite nth_upd_neqrev'; auto).
                eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
              { unfold OS_Port_V_OSQIn. subst dmport'.
                do 5 (rewrite nth_upd_neqrev'; auto).
                eapply update_nth.
                do 6 (rewrite nth_upd_neqrev'; auto).
                eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
              { unfold OS_Port_V_OSQEnd. subst dmport'.
                do 6 (rewrite nth_upd_neqrev'; auto).
                eapply update_nth.
                do 5 (rewrite nth_upd_neqrev'; auto).
                eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
              { unfold OS_Port_V_mode. subst dmport'.
                do 10 (rewrite nth_upd_neqrev'; auto). unfold ZToInt.
                eapply update_nth.
                do 1 (rewrite nth_upd_neqrev'; auto).
                eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. } }
            { unfold OS_Port_V_OSQStart. subst dmport'.
              do 7 (rewrite nth_upd_neqrev'; auto).
              eapply update_nth.
              do 4 (rewrite nth_upd_neqrev'; auto).
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
            { subst dmport'. clear - Hdmty Hltp Hdm Hdisp Hsize.
              destruct dmport; tryfalse.
              repeat (simpl in *; destruct Hdmty as [? Hdmty];
              split; eauto; destruct dmport; tryfalse).
              { pose proof dnum_range as Hdum.
                rewrite byte_max_unsigned_val.
                destruct (Int.unsigned ($ DNUM) <=? 255) eqn: Heq.
                { auto. }
                exfalso. clear - Heq Hdum.
                apply Z.leb_gt in Heq.
                assert (Int.unsigned ($ DNUM) = DNUM); [ |lia].
                eapply int_usign_eq. lia.
                rewrite max_unsigned_val; lia. }
              { destruct Hdisp as [? |[? ?]]; subst; auto. }
              { clear - Hsize.
                rewrite int16_max_unsigned_val.
                destruct (Int.unsigned size <=? 65535) eqn: Heq; auto.
                apply Z.leb_gt in Heq. lia. } }
            { subst dmport'. unfold OS_Port_V_nextPort.
              eapply update_nth.
              do 11 (rewrite nth_upd_neqrev'; auto).
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
            { auto. } }
          { auto. } { split; auto. } { eauto. } { eauto. }
          { unfold RLH_PortPtrINecb. split.
            { cbn. split; auto.
              eexists; split.
              2:{ destruct Hppi. apply r. }
              subst. unfold OS_Port_V_nextPort.
              eapply update_nth.
              do 11 (rewrite nth_upd_neqrev'; eauto).
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
            apply Forall_cons.
            { eauto. } { destruct Hppi; auto. } }
          { subst dmport'. eauto. } }
        { auto. } { eauto. } { simpl; auto. } }
      { (* RETURN *)
        partition_absrulestac absinfer_choice1.
        partition_absrulestac absinfer_seq_end.
        remember (update_nth_val 11 (update_nth_val 10
                 (update_nth_val 2 (update_nth_val 17
                 (update_nth_val 16 (update_nth_val 15
                 (update_nth_val 14 (update_nth_val 13
                 (update_nth_val 12 (update_nth_val 0
                 (update_nth_val 4 (update_nth_val 5
                 (update_nth_val 3 dmport (Vint32 portid))
                 (V$ QUEUE)) (V$ dir_)) (Vint32 dm)) (Vptr msgp))
                 (Vptr (get_off_addr msgp (Int.mul ($ 33) size))))
                 (Vptr msgp)) (Vptr msgp)) (Vint32 size)) (V$ 0)) 
                 (V$ DNUM)) cportp) dportp) as dmport'.
        eapply ret_rule'. intros * Hs.
        sep normal. sep eexists.
        sep name lift errptr in Hs.
        sep autocancel. sep split.
        { right. left. sep autocancel.
          eapply disj_split. right. sep split.
          { sep autocancel.
            instantiate (1:=nil :: dportmsgll).
            instantiate (1:=dmport' :: dportl).
            unfold dmportp_sll in *.
            cbn [dmportp_sllseg].
            sep normal. sep eexists.
            sep autocancel. sep split.
            { right. sep normal. sep eexists.
              sep split.
              { instantiate (1:=buff).
                instantiate (1:=Int.zero).
                instantiate (1:=size).
                instantiate (1:=(get_off_addr msgp (Int.mul ($ 33) size))).
                instantiate (1:=msgp).
                instantiate (1:=msgp).
                instantiate (1:=msgp).
                unfold nat_of_Z in *.
                rewrite Int.unsigned_zero.
                rewrite Z.sub_0_r, Z2Nat.inj_0.
                sep autocancel.
                cbn [dmportp_sllseg_qport_msg].
                sep pauto. }
              { unfold Qport_msg_ptrs_P.
                destruct msgp as [msgb msgi].
                split;[ |split;[ |exists 0 0;split;[ |split;[ |split]]]].
                { simpl snd in Hsndmsg. auto. }
                { rewrite Hmsglen.
                  rewrite Int.repr_unsigned.
                  rewrite Int.mul_commut.
                  reflexivity. }
                { rewrite Hmsglen, Int.mul_commut.
                  rewrite repr_zero, Int.mul_zero.
                  rewrite <- repr_zero.
                  rewrite get_off_addr_0. auto. }
                { rewrite Hmsglen, Int.mul_commut.
                  rewrite repr_zero, Int.mul_zero.
                  rewrite <- repr_zero.
                  rewrite get_off_addr_0. auto. }
                { split; lia. }
                { split; lia. } }
              { split.
                2:{ rewrite Int.unsigned_zero.
                    apply Int.unsigned_range. }
                unfold OS_Port_V_OSQEntries. subst dmport'.
                do 3 (rewrite nth_upd_neqrev'; auto).
                eapply update_nth.
                do 9 (rewrite nth_upd_neqrev'; auto).
                eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
              { split. 2: lia.
                unfold OS_Port_V_OSQSize. subst dmport'.
                do 4 (rewrite nth_upd_neqrev'; auto).
                eapply update_nth.
                do 8 (rewrite nth_upd_neqrev'; auto).
                eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
              { unfold OS_Port_V_OSQOut. subst dmport'.
                do 5 (rewrite nth_upd_neqrev'; auto).
                eapply update_nth.
                do 7 (rewrite nth_upd_neqrev'; auto).
                eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
              { unfold OS_Port_V_OSQIn. subst dmport'.
                do 6 (rewrite nth_upd_neqrev'; auto).
                eapply update_nth.
                do 6 (rewrite nth_upd_neqrev'; auto).
                eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
              { unfold OS_Port_V_OSQEnd. subst dmport'.
                do 7 (rewrite nth_upd_neqrev'; auto).
                eapply update_nth.
                do 5 (rewrite nth_upd_neqrev'; auto).
                eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
              { unfold OS_Port_V_mode. subst dmport'.
                do 11 (rewrite nth_upd_neqrev'; auto). unfold ZToInt.
                eapply update_nth.
                do 1 (rewrite nth_upd_neqrev'; auto).
                eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. } }
            { unfold OS_Port_V_OSQStart. subst dmport'.
              do 8 (rewrite nth_upd_neqrev'; auto).
              eapply update_nth.
              do 4 (rewrite nth_upd_neqrev'; auto).
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
            { subst dmport'. clear - Hdmty Hltp Hdm Hdisp Hcisp Hsize.
              destruct dmport; tryfalse.
              repeat (simpl in *; destruct Hdmty as [? Hdmty];
              split; eauto; destruct dmport; tryfalse).
              { pose proof dnum_range as Hdum.
                rewrite byte_max_unsigned_val.
                destruct (Int.unsigned ($ DNUM) <=? 255) eqn: Heq.
                { auto. }
                exfalso. clear - Heq Hdum.
                apply Z.leb_gt in Heq.
                assert (Int.unsigned ($ DNUM) = DNUM); [ |lia].
                eapply int_usign_eq. lia.
                rewrite max_unsigned_val; lia. }
              { destruct Hcisp as [? |[? ?]]; subst; auto. }
              { destruct Hdisp as [? |[? ?]]; subst; auto. }
              { clear - Hsize.
                rewrite int16_max_unsigned_val.
                destruct (Int.unsigned size <=? 65535) eqn: Heq; auto.
                apply Z.leb_gt in Heq. lia. } }
            { subst dmport'. unfold OS_Port_V_nextPort.
              eapply update_nth.
              do 12 (rewrite nth_upd_neqrev'; auto).
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
            { auto. } }
          { auto. } { split; auto. } { eauto. } { eauto. }
          { unfold RLH_PortPtrINecb. split.
            { cbn. split; auto.
              eexists; split.
              2:{ destruct Hppi. apply r. }
              subst. unfold OS_Port_V_nextPort.
              eapply update_nth.
              do 12 (rewrite nth_upd_neqrev'; eauto).
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
            apply Forall_cons.
            { eauto. } { destruct Hppi; auto. } }
          { subst dmport'. eauto. } }
        { auto. } { eauto. } { simpl; auto. } } }
  
  naive pure intro.
  subst v'0 vret verr kportfptr.
  rename v'2 into kportp. rename v'1 into kport.
  rename v' into kportfptr. rename dir_ into dir.
   
  rename H1 into Hkp_pid.
  rename H2 into Hkp_dm. rename H3 into Hkp_cid.
  rename H4 into Hkp_evp. rename H5 into Hkp_cnum.
  rename H6 into Hkp_chan. rename H into Hkp_n.

  (* If (∗ err ′ ==ₑ 〈 char_t 〉 ′ OS_NO_ERR)
    {OSPortAddToChannel (­port_ptr ′ .. channelID, port ′, err ′­)};ₛ *)
  hoare name lift Aop pre.
  assert (END None;; aop
  ?? Semacc_err vsem;; END None;; aop
     ?? Semacc_succ vsem;; Semrelease vsem;; END None;; aop = 
    spec_code_cons (OSPortAddToChannel_aspec vsem) aop) by (simpl; auto).
  rewrite H. clear H.

  (* div kportvl kportl *)
  assert (exists kportv kportvl1 kportvl2,
    kportvl = kportvl1 ++ kportv :: kportvl2 /\
    length kportvl1 = Z.to_nat (Int.unsigned portid)).
  { clear - Hltp Hkplen.
    unfold PORT_NUMS, nat_of_Z in *.
    destruct (nth_error kportvl (Z.to_nat (Int.unsigned portid))) eqn: I.
    { exists v. eapply nth_error_split. eauto. }
    exfalso. eapply nth_error_None in I.
    rewrite Hkplen in I.
    eapply Intlt_true_is_Zlt in Hltp.
    eapply Z2Nat.inj_le in I.
    2: lia. 2: eapply Int.unsigned_range.
    assert (Int.unsigned ($ 64) = 64) by (clear; mauto). lia. }
  destruct H as [kportv [kportvl1 [kportvl2 [Hkvl Hkvllen]]]].
  subst kportvl.
  rewrite Hkplen in Hkpllen.
  assert (exists kport kportl1 kportl2,
    kportl = kportl1 ++ kport :: kportl2 /\
    length kportl1 = Z.to_nat (Int.unsigned portid)).
  { clear - Hltp Hkpllen.
    unfold PORT_NUMS, nat_of_Z in *.
    destruct (nth_error kportl (Z.to_nat (Int.unsigned portid))) eqn: I.
    { exists v. eapply nth_error_split. eauto. }
    exfalso. eapply nth_error_None in I.
    rewrite <- Hkpllen in I.
    eapply Intlt_true_is_Zlt in Hltp.
    eapply Z2Nat.inj_le in I.
    2: lia. 2: eapply Int.unsigned_range.
    assert (Int.unsigned ($ 64) = 64) by (clear; mauto). lia. }
  destruct H as [kport_ [kportl1 [kportl2 [Hkl Hkllen]]]].
  subst kportl.
  assert ((update_nth_val (Z.to_nat (Int.unsigned portid))
  (kportvl1 ++ kportv :: kportvl2) (Vptr kportp)) = kportvl1 ++ (Vptr kportp) :: kportvl2).
  { rewrite <- Hkvllen. apply update_nth_val_midlle. }
  rewrite H. clear H.
  assert (update_nth_vallist (Z.to_nat (Int.unsigned portid))
  (kportl1 ++ kport_ :: kportl2) kport = (kportl1 ++ kport :: kportl2)).
  { rewrite <- Hkllen. apply update_nth_vallist_middle. }
  rewrite H. clear H.
  rewrite <- Hkvllen in Hkp_n.
  rewrite nth_error_middle in Hkp_n.
  invertsr Hkp_n.

  hoare name lift kportNode_P pre.
  hoare remember (1::nil)%nat pre.
  eapply backward_rule1.
  { eapply kportNode_P_getsome_frm.
    instantiate (1:=kportp).
    instantiate (1:=(Z.to_nat (Int.unsigned portid))).
    2: instantiate (1:=kport).
    { rewrite <- Hkvllen. apply nth_error_middle. }
    { rewrite <- Hkllen. apply nth_error_middle. } }
  naive pure intro.
  assert (v'0 = kportvl1 /\ v'1 = kportvl2).
  { destruct H3. clear - H3 H1 Hkvllen.
    rewrite <- H3 in Hkvllen. clear H3.
    revert kportp kportvl2 v'0 v'1 H1 Hkvllen.
    induction kportvl1; intros; destruct v'0.
    { simpl in *. split; auto. invertsr H1. auto. }
    { simpl in *. lia. }
    { simpl in *. lia. }
    { simpl in *. invertsr H1.
      assert (v'0 = kportvl1 /\ v'1 = kportvl2).
      { eapply IHkportvl1. eauto. lia. }
      simpljoin1. auto. } }
  assert (v'2 = kportl1 /\ v'3 = kportl2).
  { destruct H3. clear - H5 H2 Hkllen.
    rename H5 into H3. rename H2 into H1.
    rename v'2 into v'0. rename v'3 into v'1.
    rename kportl1 into kportvl1. rename kportl2 into kportvl2.
    rewrite <- H3 in Hkllen. clear H3.
    revert kport kportvl2 v'0 v'1 H1 Hkllen.
    induction kportvl1; intros; destruct v'0.
    { simpl in *. split; auto. invertsr H1. auto. }
    { simpl in *. lia. }
    { simpl in *. lia. }
    { simpl in *. invertsr H1.
      assert (v'0 = kportvl1 /\ v'1 = kportvl2).
      { eapply IHkportvl1. eauto. lia. }
      simpljoin1. auto. } }
  simpljoin1. clear H3 H8.
  rename H9 into Hkpty. rename v' into kportb.
  assert (exists i0 i1 v0 v1 i2 i3 v2,
          kport = (Vint32 i0) :: (Vint32 i1) :: v0 ::
                  v1 :: (Vint32 i2) :: (Vint32 i3) :: v2 :: nil /\
          Int.unsigned i0 <= 255 /\ Int.unsigned i1 <= 255 /\
          isptr v0 /\ isptr v1 /\ Int.unsigned i2 <= 255 /\
          Int.unsigned i3 <= 255 /\ isptr v2 ).
  { clear - Hkpty. struct_type_vallist_match_elim. jauto. }
  clear Hkpty.
  destruct H as [kpid [kcid [kdm [kchan [kcnum [kst [kevt [Heq [Hkpid [Hkcid [Hkdm [Hkchan [Hkcnum [Hkst Hkevt]]]]]]]]]]]]]].
  subst kport. simpl firstn.
  remember (update_nth_val 2 (update_nth_val 17
  (update_nth_val 16 (update_nth_val 15 (update_nth_val 14
  (update_nth_val 13 (update_nth_val 12 (update_nth_val 0
  (update_nth_val 4 (update_nth_val 5 (update_nth_val 3
  dmport (Vint32 kpid)) (V$ QUEUE)) (V$ dir)) (Vint32 dm))
  (Vptr msgp)) (Vptr (get_off_addr msgp (Int.mul ($ 33) size))))
  (Vptr msgp)) (Vptr msgp)) (Vint32 size)) (V$ 0)) (V$ DNUM)) as dmport'.
  assert (OS_Port_V_coreNum dmport' = Some (V$ DNUM)).
  { unfold OS_Port_V_coreNum. subst dmport'.
    eapply update_nth.
    repeat (erewrite nth_upd_neqrev'; [ |lia]).
    eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
  rename H into Hdm'_cnum.
  invertsr Hkp_chan. invertsr Hkp_pid. invertsr Hkp_dm.
  invertsr Hkp_evp. invertsr Hkp_cid.
  rewrite <- Heqdmport' in *.
  rewrite Hdm'_cnum in Hkp_cnum. invertsr Hkp_cnum.
  
  eapply seq_rule.
  { eapply corecommu_rules.ift_nonzero_rule.
    intros * Hs.
    exists (Int.one).
    sep split.
    symbolic_execution.
    reflexivity.

    eapply backward_rule1.
    { intros * Hs. sep lift 10%nat in Hs.
      apply disj_split in Hs. apply Hs. }
    eapply disj_rule'.
    { naive pure intro. rename H into Hdest.

      (* merge dmport_sll *)
      hoare name lift dmportp_sll APortStruct dmportp_sllseg_qport_msg Aop pre.
      hoare remember (1::2::3::nil)%nat pre.
      eapply backward_rule1.
      { instantiate (1:=dmportp_sll (Vptr dmportp)
                                    ((update_nth_val 11 dmport' dportp) :: dportl)
                                    (nil :: dportmsgll)
                                    OS_Port_V_nextPort ** H).
        intros ? Hs. unfold dmportp_sll. cbn [dmportp_sllseg].
        sep normal. sep eexists. sep autocancel. sep split.
        { eapply disj_split. right. sep normal.
          unfold dmportp_sll in Hs. 
          sep eexists. sep cancel dmportp_sllseg.
          sep split.
          { instantiate (1:=buff).
            instantiate (1:=Int.zero).
            instantiate (1:=size).
            instantiate (1:=(get_off_addr msgp (Int.mul ($ 33) size))).
            instantiate (1:=msgp).
            instantiate (1:=msgp).
            instantiate (1:=msgp).
            unfold nat_of_Z in *.
            rewrite Int.unsigned_zero.
            rewrite Z.sub_0_r, Z2Nat.inj_0.
            sep autocancel.
            cbn [dmportp_sllseg_qport_msg].
            sep pauto. }
          { unfold Qport_msg_ptrs_P.
            destruct msgp as [msgb msgi].
            split;[ |split;[ |exists 0 0;split;[ |split;[ |split]]]].
            { simpl snd in Hsndmsg. auto. }
            { rewrite Hmsglen.
              rewrite Int.repr_unsigned.
              rewrite Int.mul_commut.
              reflexivity. }
            { rewrite Hmsglen, Int.mul_commut.
              rewrite repr_zero, Int.mul_zero.
              rewrite <- repr_zero.
              rewrite get_off_addr_0. auto. }
            { rewrite Hmsglen, Int.mul_commut.
              rewrite repr_zero, Int.mul_zero.
              rewrite <- repr_zero.
              rewrite get_off_addr_0. auto. }
            { split; lia. }
            { split; lia. } }
          { split.
            2:{ rewrite Int.unsigned_zero.
                apply Int.unsigned_range. }
            unfold OS_Port_V_OSQEntries. subst dmport'.
            do 2 (rewrite nth_upd_neqrev'; auto).
            eapply update_nth.
            do 9 (rewrite nth_upd_neqrev'; auto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
          { split. 2: lia.
            unfold OS_Port_V_OSQSize. subst dmport'.
            do 3 (rewrite nth_upd_neqrev'; auto).
            eapply update_nth.
            do 8 (rewrite nth_upd_neqrev'; auto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
          { unfold OS_Port_V_OSQOut. subst dmport'.
            do 4 (rewrite nth_upd_neqrev'; auto).
            eapply update_nth.
            do 7 (rewrite nth_upd_neqrev'; auto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
          { unfold OS_Port_V_OSQIn. subst dmport'.
            do 5 (rewrite nth_upd_neqrev'; auto).
            eapply update_nth.
            do 6 (rewrite nth_upd_neqrev'; auto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
          { unfold OS_Port_V_OSQEnd. subst dmport'.
            do 6 (rewrite nth_upd_neqrev'; auto).
            eapply update_nth.
            do 5 (rewrite nth_upd_neqrev'; auto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
          { unfold OS_Port_V_mode. subst dmport'.
            do 10 (rewrite nth_upd_neqrev'; auto). unfold ZToInt.
            eapply update_nth.
            do 1 (rewrite nth_upd_neqrev'; auto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. } }
        { subst dmport'. unfold OS_Port_V_OSQStart.
          do 7 (rewrite nth_upd_neqrev'; auto).
          eapply update_nth.
          do 4 (rewrite nth_upd_neqrev'; auto).
          eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
        { subst dmport'. clear - Hdmty Hltp Hdm Hdisp Hsize.
          destruct dmport; tryfalse.
          repeat (simpl in *; destruct Hdmty as [? Hdmty];
          split; eauto; destruct dmport; tryfalse).
          { pose proof dnum_range as Hdum.
            rewrite byte_max_unsigned_val.
            destruct (Int.unsigned ($ DNUM) <=? 255) eqn: Heq.
            { auto. }
            exfalso. clear - Heq Hdum.
            apply Z.leb_gt in Heq.
            assert (Int.unsigned ($ DNUM) = DNUM); [ |lia].
            eapply int_usign_eq. lia.
            rewrite max_unsigned_val; lia. }
          { destruct Hdisp as [? |[? ?]]; subst; auto. }
          { clear - Hsize.
            rewrite int16_max_unsigned_val.
            destruct (Int.unsigned size <=? 65535) eqn: Heq; auto.
            apply Z.leb_gt in Heq. lia. } }
        { subst dmport'. unfold OS_Port_V_nextPort.
          eapply update_nth.
          do 11 (rewrite nth_upd_neqrev'; auto).
          eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
        auto. }
      subst H.

      (* merge kport_V_OSEventPtr *)
      hoare name lift kport_V_OSEventPtr get_off_addr pre.
      hoare remember (1::2::nil)%nat pre.
      eapply backward_rule1.
      { intros * Hs.
        sep name lift H in Hs.
        eapply astar_mono in Hs. 2: eauto.
        2: eapply kport_V_OSEventPtr_upd.
        2: lia. 
        2:{ instantiate (1:=(Vint32 kpid :: V$ DEFAULT_CHANELID
            :: Vptr dmportp :: Vnull :: V$ DNUM :: Vint32 kst :: Vnull :: nil)).
            eauto. }
        instantiate (1:=dmportp) in Hs.
        instantiate (1:=update_nth_val 11 dmport' dportp) in Hs.
        sep lifts (2::3::nil)%nat in Hs.
        apply Hs. }
      subst H.

      (* OSPortAddToChannel (­port_ptr ′ .. channelID, port ′, err ′­) *)
      eapply call_rule'.
      { cbn. unfold OSPortAddToChannel_spec. eauto. }
      { intros * Hs.
        eapply rvl_elim.
        { eapply cast_rv_tint8_tint32.
          symbolic_execution. pauto. }
        eapply rvl_elim; [symbolic_execution| ].
        eapply rvl_elim; [symbolic_execution|apply rvl_nil]. }
      { (* ==> pre *)
        intros * Hs.
        unfold getasrt, OSPortAddToChannelPre, OSPortAddToChannelPre'.
        sep normal. exists aop er cid (Vptr dmportp) errptr.
        exists ($ OS_NO_ERR) curdomain domainv domainvl vsem.
        unfold get_off_addr; cbn [fst snd].
        sep autocancel.
        sep split. 2,3,4: eauto.
        eapply disj_split. right.
        sep normal. sep eexists. sep split.
        2: eauto. 2: eauto.
        { sep autocancel.
          unfold AOSDomainPortPtrList, AOSKernelPortIDTbl.
          sep normal. sep autocancel. sep split.
          2: eapply NoDup_kportvl_upd; eauto.
          2:{ split.
              { apply array_type_vallist_match_app.
                apply array_type_vallist_match_app in Hkpar.
                destruct Hkpar as [Hkpar_1 [Hkpvty Hkpar_2]].
                split; auto. cbn. split; auto. }
              { rewrite <- Hkplen. clear.
                induction kportvl1; simpl; eauto. } }
          instantiate (2:=(dmportp :: dpptrl)).
          instantiate (2:=dportl).
          instantiate (2:=update_nth_val 11 dmport' dportp).
          instantiate (2:=nil).
          instantiate (2:=(kportl1 ++ (Vint32 kpid
                          :: V$ DEFAULT_CHANELID :: Vptr dmportp
                          :: Vnull :: V$ DNUM :: Vint32 kst :: Vnull :: nil)
                          :: kportl2)).
          instantiate (2:=dportmsgll).
          instantiate (2:=nil).
          instantiate (2:=nil).
          simpl (nil ++ _). sep autocancel.
          eapply kportNode_P_compose.
          { lia. } { pauto. } { eauto. }
          sep autocancel. apply Hs. }
        { eauto. }
        { simpl (nil ++ _).
          intros.
          rename H into Hchvl. rename H0 into Hchl.
          rename H1 into Hchdl. rename H2 into Hds.
          unfold OS_Port_V_direction in Hds.
          rewrite nth_upd_neqrev' in Hds. 2: lia.
          exfalso. destruct Hdest. auto. }
        { simpl (nil ++ _).
          unfold channel_V_srcdstkport_aux. split.
          { apply channel_V_srcdstkport_upd_dport.
            eapply channel_V_srcdstkport_upd_kport_null.
            { lia. }
            { instantiate (1:=kport_).
              destruct Hcs. auto. } }
          eapply NoDup_kportf_eq.
          eapply NoDup_kportvl_upd; eauto. }
        { auto. }
        { auto. }
        { eapply Habs. }
        { unfold DomainportNode_P.
          split; [ |split].
          { unfold Domainport_nat_P.
            do 5 eexists. splits; eauto.
            { unfold OS_Port_V_coreNum. subst.
              rewrite nth_upd_neqrev'; eauto. }
            { unfold OS_Port_V_domain. subst.
              do 8 (rewrite nth_upd_neqrev'; eauto).
              eapply update_nth.
              do 3 (rewrite nth_upd_neqrev'; eauto).
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
            { unfold OS_Port_V_portID. subst.
              do 11 (rewrite nth_upd_neqrev'; eauto).
              eapply update_nth.
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
            { clear - Hltp.
              apply Intlt_true_is_Zlt in Hltp.
              unfold PORT_NUMS in *.
              assert (Int.unsigned ($ 64) = 64) by (clear; mauto).
              lia. }
            splits; eauto.
            { unfold OS_Port_V_status. subst.
              do 12 (rewrite nth_upd_neqrev'; eauto). }
            { unfold OS_Port_V_msgInTick. subst.
              do 12 (rewrite nth_upd_neqrev'; eauto). }
            { unfold OS_Port_V_msgOutTick. subst.
              do 12 (rewrite nth_upd_neqrev'; eauto). } }
          { unfold Domainport_direction_P.
            destruct Hdir_eq.
            { destruct H. subst.
              unfold OS_Port_V_direction.
              do 9 (rewrite nth_upd_neqrev'; eauto).
              eapply update_nth.
              do 2 (rewrite nth_upd_neqrev'; eauto).
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
            { exfalso. destruct Hdest.
              destruct H; subst.
              unfold OS_Port_V_direction.
              do 8 (rewrite nth_upd_neqrev'; eauto).
              eapply update_nth.
              do 2 (rewrite nth_upd_neqrev'; eauto).
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. } }
          { unfold Domainport_Portt_P.
            splits; eauto.
            { rewrite Z2Nat.id. 2: apply Int.unsigned_range.
              rewrite Int.repr_unsigned.
              unfold OS_Port_V_OSQSize. subst.
              do 3 (rewrite nth_upd_neqrev'; eauto).
              eapply update_nth.
              do 8 (rewrite nth_upd_neqrev'; eauto).
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
            { unfold OS_Port_V_mode. subst.
              do 10 (rewrite nth_upd_neqrev'; eauto).
              eapply update_nth.
              do 1 (rewrite nth_upd_neqrev'; eauto).
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. } } }
        { auto. }
        { auto. }
        { simpl (nil ++ _).
          cbn [R_Kernelport_DomainPort_init]. split.
          { left. do 3 eexists. splits.
            { unfold OS_Port_V_portID. subst.
              instantiate (1:=kpid).
              do 11 (rewrite nth_upd_neqrev'; eauto).
              eapply update_nth.
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
            { unfold nat_of_Z.
              rewrite <- Hkvllen.
              eapply nth_error_middle. }
            { unfold nat_of_Z.
              rewrite <- Hkllen.
              eapply nth_error_middle. }
            { pauto. } { auto. } { auto. }
            { cbn. unfold OS_Port_V_coreNum. subst.
              rewrite nth_upd_neqrev'; eauto. } }
          eapply R_Kernelport_DomainPort_init_inj.
          eapply R_Kernelport_DomainPort_init_nonull_upd_kport_null; eauto.
          { lia. } { pauto. } }
        { simpl (nil ++ _).
          unfold RLH_PortPtrINecb. split.
          { cbn. split; auto.
            eexists; split.
            2:{ destruct Hppi. apply r. }
            subst. unfold OS_Port_V_nextPort.
            eapply update_nth.
            do 11 (rewrite nth_upd_neqrev'; eauto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
          apply Forall_cons.
          { eauto. } { destruct Hppi; auto. } }
        { pauto. }
        { unfold OS_Port_V_portID. subst dmport'.
          do 11 (rewrite nth_upd_neqrev'; eauto).
          eapply update_nth.
          eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. } }
      { good_frm_sovler. }
      { unfold getasrt, OSPortAddToChannelPost, OSPortAddToChannelPost'.
        sep auto. }
      { unfold getasrt, OSPortAddToChannelPre, OSPortAddToChannelPre'.
        sep auto. }
      { pauto. } }

    { naive pure intro. rename H into Hdest.

      (* merge dmport_sll *)
      hoare name lift dmportp_sll APortStruct dmportp_sllseg_qport_msg Aop pre.
      hoare remember (1::2::3::nil)%nat pre.
      eapply backward_rule1.
      { instantiate (1:=dmportp_sll (Vptr dmportp)
                                    ((update_nth_val 11
                                        (update_nth_val 10 dmport' cportp) dportp) :: dportl)
                                    (nil :: dportmsgll)
                                    OS_Port_V_nextPort ** H).
        intros ? Hs. unfold dmportp_sll. cbn [dmportp_sllseg].
        sep normal. sep eexists. sep autocancel. sep split.
        { eapply disj_split. right. sep normal.
          unfold dmportp_sll in Hs. 
          sep eexists. sep cancel dmportp_sllseg.
          sep split.
          { instantiate (1:=buff).
            instantiate (1:=Int.zero).
            instantiate (1:=size).
            instantiate (1:=(get_off_addr msgp (Int.mul ($ 33) size))).
            instantiate (1:=msgp).
            instantiate (1:=msgp).
            instantiate (1:=msgp).
            unfold nat_of_Z in *.
            rewrite Int.unsigned_zero.
            rewrite Z.sub_0_r, Z2Nat.inj_0.
            sep autocancel.
            cbn [dmportp_sllseg_qport_msg].
            sep pauto. }
          { unfold Qport_msg_ptrs_P.
            destruct msgp as [msgb msgi].
            split;[ |split;[ |exists 0 0;split;[ |split;[ |split]]]].
            { simpl in Hsndmsg. auto. }
            { rewrite Hmsglen.
              rewrite Int.repr_unsigned.
              rewrite Int.mul_commut.
              reflexivity. }
            { rewrite Hmsglen, Int.mul_commut.
              rewrite repr_zero, Int.mul_zero.
              rewrite <- repr_zero.
              rewrite get_off_addr_0. auto. }
            { rewrite Hmsglen, Int.mul_commut.
              rewrite repr_zero, Int.mul_zero.
              rewrite <- repr_zero.
              rewrite get_off_addr_0. auto. }
            { split; lia. }
            { split; lia. } }
          { split.
            2:{ rewrite Int.unsigned_zero.
                apply Int.unsigned_range. }
            unfold OS_Port_V_OSQEntries. subst dmport'.
            do 3 (rewrite nth_upd_neqrev'; auto).
            eapply update_nth.
            do 9 (rewrite nth_upd_neqrev'; auto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
          { split. 2: lia.
            unfold OS_Port_V_OSQSize. subst dmport'.
            do 4 (rewrite nth_upd_neqrev'; auto).
            eapply update_nth.
            do 8 (rewrite nth_upd_neqrev'; auto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
          { unfold OS_Port_V_OSQOut. subst dmport'.
            do 5 (rewrite nth_upd_neqrev'; auto).
            eapply update_nth.
            do 7 (rewrite nth_upd_neqrev'; auto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
          { unfold OS_Port_V_OSQIn. subst dmport'.
            do 6 (rewrite nth_upd_neqrev'; auto).
            eapply update_nth.
            do 6 (rewrite nth_upd_neqrev'; auto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
          { unfold OS_Port_V_OSQEnd. subst dmport'.
            do 7 (rewrite nth_upd_neqrev'; auto).
            eapply update_nth.
            do 5 (rewrite nth_upd_neqrev'; auto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
          { unfold OS_Port_V_mode. subst dmport'.
            do 11 (rewrite nth_upd_neqrev'; auto). unfold ZToInt.
            eapply update_nth.
            do 1 (rewrite nth_upd_neqrev'; auto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. } }
        { subst dmport'. unfold OS_Port_V_OSQStart.
          do 8 (rewrite nth_upd_neqrev'; auto).
          eapply update_nth.
          do 4 (rewrite nth_upd_neqrev'; auto).
          eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
        { subst dmport'. clear - Hdmty Hltp Hdm Hdisp Hcisp Hsize.
          destruct dmport; tryfalse.
          repeat (simpl in *; destruct Hdmty as [? Hdmty];
          split; eauto; destruct dmport; tryfalse).
          { pose proof dnum_range as Hdum.
            rewrite byte_max_unsigned_val.
            destruct (Int.unsigned ($ DNUM) <=? 255) eqn: Heq.
            { auto. }
            exfalso. clear - Heq Hdum.
            apply Z.leb_gt in Heq.
            assert (Int.unsigned ($ DNUM) = DNUM); [ |lia].
            eapply int_usign_eq. lia.
            rewrite max_unsigned_val; lia. }
          { destruct Hcisp as [? |[? ?]]; subst; auto. }
          { destruct Hdisp as [? |[? ?]]; subst; auto. }
          { clear - Hsize.
            rewrite int16_max_unsigned_val.
            destruct (Int.unsigned size <=? 65535) eqn: Heq; auto.
            apply Z.leb_gt in Heq. lia. } }
        { subst dmport'. unfold OS_Port_V_nextPort.
          eapply update_nth.
          do 12 (rewrite nth_upd_neqrev'; auto).
          eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
        auto. }
      subst H.

      (* merge kport_V_OSEventPtr *)
      hoare name lift kport_V_OSEventPtr get_off_addr pre.
      hoare remember (1::2::nil)%nat pre.
      eapply backward_rule1.
      { intros * Hs.
        sep name lift H in Hs.
        eapply astar_mono in Hs. 2: eauto.
        2: eapply kport_V_OSEventPtr_upd.
        2: lia. 
        2:{ instantiate (1:=(Vint32 kpid :: V$ DEFAULT_CHANELID
            :: Vptr dmportp :: Vnull :: V$ DNUM :: Vint32 kst :: Vnull :: nil)).
            eauto. }
        instantiate (1:=dmportp) in Hs.
        instantiate (1:=update_nth_val 11
                        (update_nth_val 10 dmport' cportp) dportp) in Hs.
        sep lifts (2::3::nil)%nat in Hs.
        apply Hs. }
      subst H.

      (* OSPortAddToChannel (­port_ptr ′ .. channelID, port ′, err ′­) *)
      eapply call_rule'.
      { cbn. unfold OSPortAddToChannel_spec. eauto. }
      { intros * Hs.
        eapply rvl_elim.
        { eapply cast_rv_tint8_tint32.
          symbolic_execution. pauto. }
        eapply rvl_elim; [symbolic_execution| ].
        eapply rvl_elim; [symbolic_execution|apply rvl_nil]. }
      { (* ==> pre *)
        intros * Hs.
        unfold getasrt, OSPortAddToChannelPre, OSPortAddToChannelPre'.
        sep normal. exists aop er cid (Vptr dmportp) errptr.
        exists ($ OS_NO_ERR) curdomain domainv domainvl vsem.
        unfold get_off_addr; cbn [fst snd].
        sep autocancel.
        sep split. 2,3,4: eauto.
        eapply disj_split. right.
        sep normal. sep eexists. sep split.
        2: eauto. 2: eauto.
        { sep autocancel.
          unfold AOSDomainPortPtrList, AOSKernelPortIDTbl.
          sep normal. sep autocancel. sep split.
          2: eapply NoDup_kportvl_upd; eauto.
          2:{ split.
              { apply array_type_vallist_match_app.
                apply array_type_vallist_match_app in Hkpar.
                destruct Hkpar as [Hkpar_1 [Hkpvty Hkpar_2]].
                split; auto. cbn. split; auto. }
              { rewrite <- Hkplen. clear.
                induction kportvl1; simpl; eauto. } }
          instantiate (2:=(dmportp :: dpptrl)).
          instantiate (2:=dportl).
          instantiate (2:=update_nth_val 11
          (update_nth_val 10 dmport' cportp) dportp).
          instantiate (2:=nil).
          instantiate (2:=(kportl1 ++ (Vint32 kpid
                          :: V$ DEFAULT_CHANELID :: Vptr dmportp
                          :: Vnull :: V$ DNUM :: Vint32 kst :: Vnull :: nil)
                          :: kportl2)).
          instantiate (2:=dportmsgll).
          instantiate (2:=nil).
          instantiate (2:=nil).
          simpl (nil ++ _). sep autocancel.
          eapply kportNode_P_compose.
          { lia. } { pauto. } { eauto. }
          sep autocancel. apply Hs. }
        { eauto. }
        { simpl (nil ++ _).
          intros.
          rename H into Hchvl. rename H0 into Hchl.
          rename H1 into Hchdl. rename H2 into Hds.
          unfold OS_Port_V_direction in Hds.
          rewrite nth_upd_neqrev' in Hds. 2: lia.
          split.
          { specialize (Hchann _ _ _ Hchvl Hchl Hchdl).
            destruct Hchann as [Hchann_0 Hchann_1]. auto. }
          { intros. split.
            { unfold OS_Port_V_OSQEntries; subst.
              do 3 (rewrite nth_upd_neqrev'; eauto).
              eapply update_nth.
              do 9 (rewrite nth_upd_neqrev'; eauto).
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
            eapply channel_V_src_P'_upd_dport.
            { subst dmport'; unfold OS_Port_V_mode.
              do 11 (rewrite nth_upd_neqrev'; eauto).
              eapply update_nth.
              do 1 (rewrite nth_upd_neqrev'; eauto).
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
            eapply channel_V_src_P'_upd_kport_null; eauto.
            { lia. }
            specialize (Hchann _ _ _ Hchvl Hchl Hchdl).
            destruct Hchann as [Hchann_0 Hchann_1]. eauto. } }
        { simpl (nil ++ _).
          unfold channel_V_srcdstkport_aux. split.
          { eapply channel_V_srcdstkport_upd_dport.
            eapply channel_V_srcdstkport_upd_kport_null.
            { lia. }
            { instantiate (1:=kport_).
              destruct Hcs. auto. } }
          eapply NoDup_kportf_eq.
          eapply NoDup_kportvl_upd; eauto. }
        { auto. }
        { auto. }
        { eapply Habs. }
        { unfold DomainportNode_P.
          split; [ |split].
          { unfold Domainport_nat_P.
            do 5 eexists. splits; eauto.
            { unfold OS_Port_V_coreNum. subst.
              do 2 (rewrite nth_upd_neqrev'; eauto). }
            { unfold OS_Port_V_domain. subst.
              do 9 (rewrite nth_upd_neqrev'; eauto).
              eapply update_nth.
              do 3 (rewrite nth_upd_neqrev'; eauto).
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
            { unfold OS_Port_V_portID. subst.
              do 12 (rewrite nth_upd_neqrev'; eauto).
              eapply update_nth.
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
            { clear - Hltp.
              apply Intlt_true_is_Zlt in Hltp.
              unfold PORT_NUMS in *.
              assert (Int.unsigned ($ 64) = 64) by (clear; mauto).
              lia. }
            splits; eauto.
            { unfold OS_Port_V_status. subst.
              do 13 (rewrite nth_upd_neqrev'; eauto). }
            { unfold OS_Port_V_msgInTick. subst.
              do 13 (rewrite nth_upd_neqrev'; eauto). }
            { unfold OS_Port_V_msgOutTick. subst.
              do 13 (rewrite nth_upd_neqrev'; eauto). } }
          { unfold Domainport_direction_P.
            destruct Hdir_eq.
            { destruct H. subst.
              unfold OS_Port_V_direction in Hdest.
              do 8 (rewrite nth_upd_neqrev' in Hdest; eauto).
              eapply nth_upd_eq in Hdest.
              invertsr Hdest. }
            { destruct H; subst.
              unfold OS_Port_V_direction, OS_Port_V_OSEventPtrPort.
              destruct H0 as [[? ?]|[? [? ?]]]; subst; split.
              { do 10 (rewrite nth_upd_neqrev'; eauto). }
              { rewrite nth_upd_neqrev'; eauto.
                eapply update_nth.
                do 11 (rewrite nth_upd_neqrev'; eauto).
                eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
              { do 10 (rewrite nth_upd_neqrev'; eauto). }
              { rewrite nth_upd_neqrev'; eauto.
                eapply update_nth.
                do 11 (rewrite nth_upd_neqrev'; eauto).
                eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. } } }
          { unfold Domainport_Portt_P.
            splits; eauto.
            { rewrite Z2Nat.id. 2: apply Int.unsigned_range.
              rewrite Int.repr_unsigned.
              unfold OS_Port_V_OSQSize. subst.
              do 4 (rewrite nth_upd_neqrev'; eauto).
              eapply update_nth.
              do 8 (rewrite nth_upd_neqrev'; eauto).
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
            { unfold OS_Port_V_mode. subst.
              do 11 (rewrite nth_upd_neqrev'; eauto).
              eapply update_nth.
              do 1 (rewrite nth_upd_neqrev'; eauto).
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. } } }
        { auto. }
        { auto. }
        { simpl (nil ++ _).
          cbn [R_Kernelport_DomainPort_init]. split.
          { left. do 3 eexists. splits.
            { unfold OS_Port_V_portID. subst.
              instantiate (1:=kpid).
              do 12 (rewrite nth_upd_neqrev'; eauto).
              eapply update_nth.
              eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
            { unfold nat_of_Z.
              rewrite <- Hkvllen.
              eapply nth_error_middle. }
            { unfold nat_of_Z.
              rewrite <- Hkllen.
              eapply nth_error_middle. }
            { pauto. } { auto. } { auto. }
            { cbn. unfold OS_Port_V_coreNum. subst.
              do 2 (rewrite nth_upd_neqrev'; eauto). } }
          eapply R_Kernelport_DomainPort_init_inj.
          eapply R_Kernelport_DomainPort_init_nonull_upd_kport_null.
          { lia. } { pauto. } { eauto. } }
        { simpl (nil ++ _).
          unfold RLH_PortPtrINecb. split.
          { cbn. split; auto.
            eexists; split.
            2:{ destruct Hppi. apply r. }
            subst. unfold OS_Port_V_nextPort.
            eapply update_nth.
            do 12 (rewrite nth_upd_neqrev'; eauto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
          apply Forall_cons.
          { eauto. } { destruct Hppi; auto. } }
        { pauto. }
        { unfold OS_Port_V_portID. subst dmport'.
          do 12 (rewrite nth_upd_neqrev'; eauto).
          eapply update_nth.
          eapply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. } }
      { good_frm_sovler. }
      { unfold getasrt, OSPortAddToChannelPost, OSPortAddToChannelPost'.
        sep auto. }
      { unfold getasrt, OSPortAddToChannelPre, OSPortAddToChannelPre'.
        sep auto. }
      { pauto. } } }
  
  eapply disj_rule.
  { unfold getasrt, OSPortAddToChannelPost, OSPortAddToChannelPost'.
    naive pure intro.
    eapply backward_rule1.
    { intros * Hs.
      sep lift 13%nat in Hs.
      eapply disj_split in Hs.
      apply Hs. }
    eapply disj_rule.
    { naive pure intro.
      invertsr H. invertsr H0. }
    naive pure intro.
    invertsr H3. invertsr H5. invertsr H6. clear H3.
    
    remember (update_nth_val 11 dmport' dportp) as dmport''.
    simpl (nil ++ _) in *.

    (* RETURN *)
    eapply ret_rule. intros * Hs.
    sep normal. sep eexists. sep autocancel.
    sep lift 2%nat. eapply disj_split.
    right. sep normal. eapply disj_split.
    right. sep normal. eapply disj_split.
    left. sep normal. sep autocancel. sep split.
    { unfold AOSDomainPortPtrList, AOSKernelPortIDTbl in Hs.
      sep normal in Hs. sep split in Hs.
      sep autocancel. }
    { eauto. }
    { eauto. }
    { simpl; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eapply NoDup_kportvl_upd; eauto. }
    { split.
      { apply array_type_vallist_match_app.
        apply array_type_vallist_match_app in Hkpar.
        destruct Hkpar as [Hkpar_1 [Hkpvty Hkpar_2]].
        split; auto. cbn. split; auto. }
      { rewrite <- Hkplen. clear.
        induction kportvl1; simpl; eauto. } }
    { eauto. }
    { instantiate (1:=dm).
      instantiate (1:=$ dir).
      instantiate (1:=$ QUEUE).
      subst dmport'' dmport'. eauto. } }
  { unfold getasrt, OSPortAddToChannelPost, OSPortAddToChannelPost'.
    naive pure intro.
    eapply backward_rule1.
    { intros * Hs.
      sep lift 13%nat in Hs.
      eapply disj_split in Hs.
      apply Hs. }
    eapply disj_rule.
    { naive pure intro.
      invertsr H. invertsr H0. }
    naive pure intro.
    invertsr H3. invertsr H5. invertsr H6. clear H3.
    
    remember (update_nth_val 11
    (update_nth_val 10 dmport' cportp) dportp) as dmport''.
    simpl (nil ++ _) in *.

    (* RETURN *)
    eapply ret_rule.
    intros * Hs.
    sep normal. sep eexists. sep autocancel.
    sep lift 2%nat. eapply disj_split.
    right. sep normal. eapply disj_split.
    right. sep normal. eapply disj_split.
    right. sep normal. sep autocancel. sep split.
    { unfold AOSDomainPortPtrList, AOSKernelPortIDTbl in Hs.
      sep normal in Hs. sep split in Hs.
      sep autocancel. }
    { eauto. }
    { eauto. }
    { simpl. eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eapply NoDup_kportvl_upd; eauto. }
    { split.
      { apply array_type_vallist_match_app.
        apply array_type_vallist_match_app in Hkpar.
        destruct Hkpar as [Hkpar_1 [Hkpvty Hkpar_2]].
        split; auto. cbn. split; auto. }
      { rewrite <- Hkplen. clear.
        induction kportvl1; simpl; eauto. } }
    { eauto. }
    { instantiate (1:=dm).
      instantiate (1:=$ dir).
      instantiate (1:=$ QUEUE).
      subst dmport'' dmport'. eauto. } }
  Unshelve.
  all: try exact nil.
  all: try exact None.
  all: try exact Vnull.
Qed.
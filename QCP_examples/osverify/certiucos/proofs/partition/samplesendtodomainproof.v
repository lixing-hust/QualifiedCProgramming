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

Open Scope code_scope.

Open Scope int_scope.

Ltac hoare_ex_intro ::=
  repeat match goal with
    | |- {| _, _, _, _, _, _ |} |- _  {{ EX _, _ }} _ {{ _ }} =>
      apply ex_intro_rule; intros 
  end.

Lemma OSSampleSendToDomain_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSSampleSendToDomain vl logicl OSSampleSendToDomainPre ct->
      Some r =
      BuildRetI os_internal OSSampleSendToDomain vl logicl OSSampleSendToDomainPost ct->
      exists t d1 d2 s,
        os_internal OSSampleSendToDomain = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  simpl app.
  rename v' into s.
  rename v'0 into er.
  rename v'1 into pptr.
  rename v'2 into msgptr.
  rename v'3 into tm.
  rename v'4 into ori_msg_vl.
  rename v'5 into mlen.
  rename v'6 into pin.
  rename v'7 into cHeapl.
  rename v'8 into dstkportpl.
  rename v'9 into dstkportpl1.
  rename v'10 into dstkportp.
  rename v'11 into dstkportpl2.
  rename v'12 into headptr.
  rename v'13 into dportl.
  rename v'14 into dportmsgll.
  rename v'15 into dpptrl.
  rename v'16 into dportls.
  rename v'17 into dstportp.
  rename v'18 into ndstpptrn.
  rename v'19 into ndstportupd.
  rename v'20 into dportl'.
  rename v'21 into dportmsgll'.
  rename v'22 into otherpl'.
  rename v'23 into othermsgll'.
  rename v'24 into otherppl.
  rename v'25 into otherpl.
  rename v'26 into othermsgll.
  rename v'27 into dportls1.
  rename v'28 into dportls2.
  rename v'29 into dportls1'.
  rename v'30 into dportls2'.
  rename v'31 into dportls'.
  rename v'32 into ndstportupdh.
  rename v'33 into ndstport.
  rename v'34 into kportls.
  rename v'35 into chanls.
  rename v'36 into vsem.
  rename v'37 into vsdstcl.
  rename v'38 into cHeape.
  rename v'39 into cHeapt.
  rename v'40 into pcn.
  rename v'41 into pd.
  rename v'42 into pid.
  rename v'43 into pst.
  rename v'44 into dstpin.
  rename v'45 into dstpout.
  rename v'46 into pm.
  rename v'47 into ppcn.
  rename v'48 into ppd.
  rename v'49 into ppid.
  rename v'50 into ppst.
  rename v'51 into pout.
  rename v'52 into srcmsg.
  rename v'53 into chanpl.
  rename v'54 into chanl.
  rename v'55 into chandstkportll.
  rename v'56 into kportpl.
  rename v'57 into kportl.
  rename v'58 into kportp.
  rename v'59 into chanp.
  rename v'60 into kpst.
  rename v'61 into cid.
  rename v'62 into cdn.
  rename v'63 into dstkpst.
  rename v'64 into next.
  rename v'65 into cphd.
  rename v'66 into cpl.
  rename H22 into Hnodup.
  inverts H4.
  subst logicl.

  (* divide to prove *)
  eapply backward_rule1.
  { intros. eapply disj_split in H1; apply H1. }
  eapply disj_rule.
  {
    hoare normal pre; pure intro.
    assert (exists n dstport dstmsgl,
      nth_error otherpl n = Some dstport /\
      nth_error othermsgll n = Some dstmsgl /\
      nth_error otherppl n = Some dstportp /\
      OtherPortNode_P dstport (pcn, pd, pid, DestinationP next, pst,
        dstpin, dstpout, SamplePort pm) dstmsgl).
    { eapply RLH_OtherPortPtrList_abs_getsome; eauto. }
    simpljoin1.
    assert (x = ndstpptrn).
    { eapply otherppl_not_same_elements; eauto. }
    subst x; clear H12.
    rewrite H in H32; inverts H32.
    apply nth_error_split in H as (otherpl1 & otherpl2 & ? & ?).
    apply nth_error_split in H1 as (othermsgll1 & othermsgll2 & ? & ?).
    apply nth_error_split in H31 as (otherppl1 & otherppl2 & ? & ?).
    subst otherppl otherpl othermsgll. rename x1 into ndstmsgl.

    hoare name lift OtherPortPtrList pre.
    eapply backward_rule1.
    { eapply OtherPortPtrList_app'_frm; eauto. }
    cbn [OtherPortPtrList].
    hoare normal pre; pure intro.
  
    (* dmportp_sllseg_sampleport_msg *)
    hoare lift 2%nat pre.
    eapply backward_rule1.
    {
      eapply astar_mono.
      {
        intros.
        destruct H25.
        { apply H25. }
        sep destruct H25; sep split in H25.
        unfold OtherPortNode_P in H14; simpljoin1.
        unfold OtherPort_Portt_P in H39; simpljoin1.
        rewrite H41 in H26.
        exfalso; clear - H26; pauto.
      }
      eauto.
    }
    hoare normal pre; pure intro.
    rename v'0 into qstart.
    
    assert ((update_nth_val 9 (update_nth_val 8 ndstport (Vint32 pin))
      (Vint32 tm)) = ndstportupd).
    {
      clear - H H8 H9 H10 H11.
      destruct ndstport; destruct ndstportupd; simpl in *; tryfalse.
      do 18 (destruct H8 as [? H8]; destruct H as [? H]; destruct ndstport; destruct ndstportupd; simpl in *; tryfalse).
      unfold OS_Port_V_msgInTick in H9; simpl in H9; inverts H9.
      unfold OS_Port_V_msgOutTick in H10; simpl in H10; inverts H10.
      assert (v = v0).
      {
        assert ((0 < 18)%nat) by lia; assert ((0 <> 8)%nat) by lia; assert ((0 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v.
      assert (v1 = v2).
      {
        assert ((1 < 18)%nat) by lia; assert ((1 <> 8)%nat) by lia; assert ((1 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v1.
      assert (v3 = v4).
      {
        assert ((2 < 18)%nat) by lia; assert ((2 <> 8)%nat) by lia; assert ((2 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v3.
      assert (v5 = v6).
      {
        assert ((3 < 18)%nat) by lia; assert ((3 <> 8)%nat) by lia; assert ((3 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v5.
      assert (v7 = v8).
      {
        assert ((4 < 18)%nat) by lia; assert ((4 <> 8)%nat) by lia; assert ((4 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v7.
      assert (v9 = v10).
      {
        assert ((5 < 18)%nat) by lia; assert ((5 <> 8)%nat) by lia; assert ((5 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v9.
      assert (v11 = v12).
      {
        assert ((6 < 18)%nat) by lia; assert ((6 <> 8)%nat) by lia; assert ((6 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v11.
      assert (v13 = v14).
      {
        assert ((7 < 18)%nat) by lia; assert ((7 <> 8)%nat) by lia; assert ((7 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v13.
      assert (v19 = v20).
      {
        assert ((10 < 18)%nat) by lia; assert ((10 <> 8)%nat) by lia; assert ((10 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v19.
      assert (v21 = v22).
      {
        assert ((11 < 18)%nat) by lia; assert ((11 <> 8)%nat) by lia; assert ((11 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v21.
      assert (v23 = v24).
      {
        assert ((12 < 18)%nat) by lia; assert ((12 <> 8)%nat) by lia; assert ((12 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v23.
      assert (v25 = v26).
      {
        assert ((13 < 18)%nat) by lia; assert ((13 <> 8)%nat) by lia; assert ((13 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v25.
      assert (v27 = v28).
      {
        assert ((14 < 18)%nat) by lia; assert ((14 <> 8)%nat) by lia; assert ((14 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v27.
      assert (v29 = v30).
      {
        assert ((15 < 18)%nat) by lia; assert ((15 <> 8)%nat) by lia; assert ((15 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v29.
      assert (v31 = v32).
      {
        assert ((16 < 18)%nat) by lia; assert ((16 <> 8)%nat) by lia; assert ((16 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v31.
      assert (v33 = v34).
      {
        assert ((17 < 18)%nat) by lia; assert ((17 <> 8)%nat) by lia; assert ((17 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v33.
      auto.
    }
    subst ndstportupd.

    (* port_ptr ′ .. msgInTick =ₑ inTime ′;ₛ *)
    assert (exists itk, OS_Port_V_msgInTick ndstport = Some (Vint32 itk)).
    {
      clear - H; unfold OS_Port_V_msgInTick.
      destruct ndstport; simpl in *; tryfalse.
      do 8 (destruct H as [? H]; destruct ndstport; simpl in *; tryfalse).
      destruct H as [? H].
      destruct v7; tryfalse. eauto.
    }
    destruct H26 as [itk ?].

    assert (exists otk, OS_Port_V_msgOutTick ndstport = Some (Vint32 otk)).
    {
      clear - H; unfold OS_Port_V_msgOutTick.
      destruct ndstport; simpl in *; tryfalse.
      do 9 (destruct H as [? H]; destruct ndstport; simpl in *; tryfalse).
      destruct H as [? H].
      destruct v8; tryfalse. eauto.
    }
    destruct H27 as [otk ?].
    
    hoare name lift APortStruct pre.
    hoare name lift port_ptr pre.
    hoare name lift Aop pre.
    eapply seq_rule.
    {
      eapply port_memeber_asgn with (n := 8%nat); try pauto.
      { symbolic execution. }
      { eapply eq_int; tauto. }
      { pauto. }
      { sep auto. }
    }

    (* port_ptr ′ .. msgOutTick =ₑ OSTime ′;ₛ *)
    unfold AOSTime.
    hoare name lift APortStruct pre.
    hoare name lift port_ptr pre.
    hoare name lift Aop pre.
    eapply seq_rule.
    {
      eapply port_memeber_asgn with (n := 9%nat); try pauto.
      { symbolic execution. }
      { eapply nth_upd_neqrev; eauto. }
      { eapply eq_int; tauto. }
      { pauto. }
      { sep auto. }
    }

    (* (port_ptr ′ .. OSQStart) .. len =ₑ msg_ptr ′ .. len;ₛ *)
    unfold dmportp_sllseg_sampleport_msg.
    hoare normal pre; pure intro.
    hoare lifts (3::2::4::5::22::nil)%nat pre.
    unfold Aarray at 2. cbn [Aarray'].
    destruct msgptr as [msg_b msg_i].
    hoare normal pre.
    eapply seq_rule.
    {
      eapply assign_rule_general.
      {
        intros.
        eapply symbolic_lemmas.struct_offset_rv.
        {
          eapply symbolic_lemmas.addrof_deref_rv.
          eapply port_QStart_rv.
          3: sep autocancel; apply H29.
          { pauto. }
          {
            unfold OS_Port_V_OSQStart.
            eapply nth_upd_neqrev; eauto.
            eapply nth_upd_neqrev; eauto.
          }
        }
        all: pauto.
      }
      {
        assert ((fst qstart, snd qstart +ᵢ  Int.zero) = qstart).
        { clear; destruct qstart; simpl; rewrite Int.add_zero; auto. }
        rewrite H29; split; eauto.
      }
      {
        intros.
        eapply symbolic_lemmas.struct_member_rv_flag.
        {
          sep autocancel.
          assert ((msg_b, msg_i) = get_off_addr (msg_b, msg_i) Int.zero).
          { unfold get_off_addr; cbn [fst snd]; rewrite Int.add_zero; reflexivity. }
          rewrite H35 in H29.
          sep cancel get_off_addr.
          apply H29.
        }
        all: pauto.
        destruct H18; auto.
      }
      { eapply eq_int; tauto. }
      { sep auto. }
    }

    (* memcpy (­(port_ptr ′ .. OSQStart) .. data, msg_ptr ′ .. data, msg_ptr ′ .. len­);ₛ *)
    eapply seq_rule.
    {
      eapply call_rule'.
      { cbn; unfold OS_memcpy_spec; eauto. }
      {
        intros.
        eapply rvl_elim.
        {
          eapply symbolic_lemmas.addrof_array_elem_rv.
          {
            eapply port_OSQStart_data_rv.
            3: sep autocancel; apply H29.
            { pauto. }
            unfold OS_Port_V_OSQStart.
            eapply nth_upd_neqrev; eauto.
            eapply nth_upd_neqrev; eauto.
          }
          { symbolic execution. }
          all: pauto.
        }
        eapply rvl_elim.
        {
          eapply symbolic_lemmas.addrof_array_elem_rv.
          {
            eapply struct_member_array_rv. symbolic_execution.
            unfold OSMsg_t. eauto.
            1,2,3: cbn;auto.
          }
          { symbolic execution. }
          { auto. }
          { pauto. }
        }
        eapply rvl_elim; [ |apply rvl_nil].
        instantiate (1:=(Vint32 mlen)).
        destruct H18.
        eapply cast_rv_tint8_tint32; auto.
        eapply symbolic_lemmas.struct_member_rv_flag.
        {
          sep autocancel.
          assert ((msg_b, msg_i) = get_off_addr (msg_b, msg_i) Int.zero).
          { unfold get_off_addr; cbn [fst snd]; rewrite Int.add_zero; reflexivity. }
          rewrite H36 in H29.
          sep lift 5%nat in H29.
          apply H29.
        }
        all: pauto.
      }
      {
        intros; unfold_spec.
        sep normal. sep eexists.
        sep autocancel; sep split; eauto.
        rewrite ! Int.add_zero. 
        assert (length ori_msg_vl = Z.to_nat (Int.unsigned mlen)) by lia.
        rewrite H35 in H29.
        unfold Aarray at 2. sep cancel Aarray'.
        sep lift 5%nat in H29.
        pose proof firstn_skipn (Z.to_nat (Int.unsigned mlen)) (v'0 ++ v'1).
        assert ((length (firstn (Z.to_nat (Int.unsigned mlen)) (v'0 ++ v'1)) = (Z.to_nat (Int.unsigned mlen)))%nat).
        {
          apply firstn_length_le.
          rewrite H31; unfold nat_of_Z; apply Zle_natle; auto.
        }
        assert ((length (skipn (Z.to_nat (Int.unsigned mlen)) (v'0 ++ v'1)) = (Z.to_nat (CHANNEL_CACHE_SZIE - Int.unsigned mlen)))%nat).
        {
          rewrite skipn_length.
          rewrite H31; unfold nat_of_Z; lia.
        }
        assert ((Z.to_nat (Int.unsigned mlen) + Z.to_nat (CHANNEL_CACHE_SZIE - Int.unsigned mlen) = Z.to_nat CHANNEL_CACHE_SZIE)%nat) by lia.
        unfold nat_of_Z in H29. rewrite <- H39 in H29.
        rewrite <- H36 in H29. rewrite <- H37 in H29 at 1. rewrite <- H38 in H29.
        eapply Aarray_split in H29; auto.
        {
          rewrite H37 in H29. rewrite H38 in H29.
          sep cancel Aarray; apply H29.
        }
        rewrite H37, H38, H39.
        clear. unfold CHANNEL_CACHE_SZIE.
        rewrite Z2Nat.id by lia. mauto.
      }
      { good_frm_sovler. }
      { sep_unfold_funpost. intros. sep destruct H29. sep auto. }
      { sep_unfold_funpre. intros. sep destruct H29. sep auto. }
      { pauto. }
    }
    unfold getasrt; unfold OS_memcopyPost, OS_memcopyPost'.
    hoare normal pre. pure intro.
    inversion H35. subst v'7 v'8 v'9 v'6. clear H35.
    inversion H29. subst v'4 v'3 v'5. clear H29.

    fold (samplepost_generateipc (S (length dstkportpl2)) (Vptr pptr :: Vptr (msg_b, msg_i)
       :: V$ Z.of_nat (length (dstkportpl1 ++ dstkportp :: dstkportpl2)) :: V$ Z.of_nat v' :: vsdstcl)).
    rename v' into csemid.
    
    (*go abscode: samplepost_sendmemcpy_one *)
    hoare remember (1::22::23::24::25::20::nil)%nat pre.
    hoare abscsq; [apply noabs_oslinv | auto .. ].
    {
      eapply samplepost_sendmemcpy_one_cont; eauto.
      2:{ eapply join_get_l; eauto. }
      3:{ eapply join_get_r; eauto. }
      2:{ rewrite <- H7; eauto. }
      subst H29; can_change_aop_solver'.
    }

    subst H29.
    eapply seq_rule.
    {
      eapply ift_rule''.
      {
        intros.
        sep_get_port_rv.
        {
          eapply port_coreNum_rv'.
          2: sep autocancel; apply H29.
          { pauto. }
        }
        all: pauto.
        {
          assert (nth_val' 2 (update_nth_val 9 (update_nth_val 8 ndstport (Vint32 pin)) (Vint32 tm)) = nth_val' 2 ndstport).
          {
            rewrite nth_val_nth_val'_some_eq at 1; eauto.
            do 2 (eapply nth_upd_neqrev; eauto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2.
            clear - H.
            destruct ndstport; simpl in *; tryfalse.
            do 2 (destruct H as [? H]; destruct ndstport; simpl in *; tryfalse).
            lia.
          }
          rewrite H35.
          unfold OtherPortNode_P in H14; simpljoin1.
          unfold OtherPort_nat_P in H14; simpljoin1.
          unfold OS_Port_V_coreNum in H14;
          apply nth_val_nth_val'_some_eq in H14; rewrite H14.
          pauto.
        } 
        {
          assert (nth_val' 2 (update_nth_val 9 (update_nth_val 8 ndstport (Vint32 pin)) (Vint32 tm)) = nth_val' 2 ndstport).
          {
            rewrite nth_val_nth_val'_some_eq at 1; eauto.
            do 2 (eapply nth_upd_neqrev; eauto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2.
            clear - H.
            destruct ndstport; simpl in *; tryfalse.
            do 2 (destruct H as [? H]; destruct ndstport; simpl in *; tryfalse).
            lia.
          }
          rewrite H35.
          unfold OtherPortNode_P in H14; simpljoin1.
          unfold OtherPort_nat_P in H14; simpljoin1.
          unfold OS_Port_V_coreNum in H14;
          apply nth_val_nth_val'_some_eq in H14; rewrite H14.
          pauto.
        } 
      }
      hoare normal pre; pure intro.
      clear H29 H35 H38.
      unfold samplepost_generateipc.
      rewrite <- H0.
      assert ((length dstkportpl1 + S (length dstkportpl2))%nat = length (dstkportpl1 ++ dstkportp :: dstkportpl2)).
      { clear; induction dstkportpl1; simpl; try lia. }
      pose proof Nat.add_sub_eq_r _ _ _ H29.
      rewrite H35, H21.
      2: lia.
      eapply generateipc_rule.
      2:{
        rewrite Z2Nat.id by apply Int.unsigned_range.
        apply Int.unsigned_range_2.
      }
      2:{
        intros; split.
        {
          unfold OtherPortNode_P in H14; simpljoin1.
          unfold OtherPort_nat_P in H14; simpljoin1.
          unfold nat_of_Z.
          rewrite ! Z2Nat.id by apply Int.unsigned_range.
          rewrite ! Int.repr_unsigned.
          unfold OS_Port_V_coreNum in H14.
          apply nth_val_nth_val'_some_eq in H14.
          rewrite <- H14.
          assert (nth_val' 2 (update_nth_val 9 (update_nth_val 8 ndstport (Vint32 pin)) (Vint32 tm)) = nth_val' 2 ndstport).
          {
            rewrite nth_val_nth_val'_some_eq at 1; eauto.
            do 2 (eapply nth_upd_neqrev; eauto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2.
            clear - H.
            destruct ndstport; simpl in *; tryfalse.
            do 2 (destruct H as [? H]; destruct ndstport; simpl in *; tryfalse).
            lia.
          }
          rewrite <- H41.
          eapply port_coreNum_rv'.
          { pauto. }
          sep autocancel; apply H38.
        }
        symbolic_execution.
      }
      2:{
        unfold p_local, CurLINV, LINV, OSLInv.
        intros.
        sep normal in H38; sep destruct H38; sep split in H38.
        sep auto.
        splits; eauto.
        all: destruct H39 as [? [? [? [? [? ?]]]]]; auto.
      }
      can_change_aop_solver'.
    }

    eapply disj_rule.
    2:{
      hoare normal pre; pure intro. exfalso.
      assert (nth_val' 2 (update_nth_val 9 (update_nth_val 8 ndstport (Vint32 pin)) (Vint32 tm)) = nth_val' 2 ndstport).
      {
        rewrite nth_val_nth_val'_some_eq at 1; eauto.
        do 2 (eapply nth_upd_neqrev; eauto).
        eapply symbolic_lemmas.nth_val_imp_nth_val'_2.
        clear - H.
        destruct ndstport; simpl in *; tryfalse.
        do 2 (destruct H as [? H]; destruct ndstport; simpl in *; tryfalse).
        lia.
      }
      rewrite H35 in H29.
      unfold OtherPortNode_P in H14; simpljoin1.
      unfold OtherPort_nat_P in H14; simpljoin1.
      unfold OS_Port_V_coreNum in H14.
      apply nth_val_nth_val'_some_eq in H14.
      rewrite H14 in H29.
      destruct (Int.eq ($ DNUM) x) eqn: I.
      {
        apply Int_eq_dec in I; subst x; clear - H41.
        rewrite Int.unsigned_repr in H41.
        pauto.
        pose proof dnum_range. mauto.
      }
      unfold notint, val_inj, Int.notbool in H29.
      destruct H29; pauto. inverts H29.
    }
    hoare normal pre; pure intro.
    clear H29 H35 H38.
    
    (* merge OtherPortPtrList *)
    hoare remember (13::16::17::19::21::22::nil)%nat pre.
    eapply backward_rule1.
    {
      intros.
      instantiate (1:=
        OtherPortPtrList (otherppl1 ++ dstportp :: otherppl2)
        (otherpl1 ++ (update_nth_val 9 (update_nth_val 8 ndstport (Vint32 pin)) (Vint32 tm)) :: otherpl2)
        (othermsgll1 ++ (ori_msg_vl :: nil) :: othermsgll2) ** H29 ).
      eapply OtherPortPtrList_compose; eauto.
      { rewrite H24; auto. }
      {
        instantiate (1:=qstart).
        clear - H1.
        unfold OS_Port_V_OSQStart in *.
        do 2 (apply nth_upd_neqrev; eauto).
      }
      sep lift 4%nat.
      eapply disj_split; left.
      sep normal; sep eexists; sep autocancel.
      sep pauto.
      2:{
        clear - H25.
        unfold OS_Port_V_mode in *.
        do 2 (apply nth_upd_neqrev; eauto).
      }
      unfold dmportp_sllseg_sampleport_msg.
      sep normal; sep eexists; sep autocancel.
      instantiate (1:=ori_msg_vl).
      instantiate (1:=(skipn (Z.to_nat (Int.unsigned mlen)) (v'0 ++ v'1))).
      assert ((fst qstart, snd qstart +ᵢ  Int.zero) = qstart).
      { clear; destruct qstart; simpl; rewrite Int.add_zero; auto. }
      rewrite H29 in H35.
      sep pauto.
      2:{
        f_equal; rewrite H36.
        rewrite Z2Nat.id by (apply Int.unsigned_range).
        rewrite Int.repr_unsigned; auto.
      }
      2:{
        split.
        { rewrite H36, H37; unfold nat_of_Z; lia. }
        apply array_type_vallist_match_app; split.
        { destruct H18; auto. }
        pose proof firstn_skipn (Z.to_nat (Int.unsigned mlen)) (v'0 ++ v'1).
        rewrite <- H38 in H32.
        apply array_type_vallist_match_app in H32.
        destruct H32; auto.
      }
      assert ((Z.to_nat (Int.unsigned mlen) + Z.to_nat (CHANNEL_CACHE_SZIE - Int.unsigned mlen) = Z.to_nat CHANNEL_CACHE_SZIE)%nat) by lia.
      unfold nat_of_Z; rewrite <- H38.
      eapply astar_r_aemp_elim.
      eapply Aarray_merge; eauto.
      {
        rewrite H38.
        clear. unfold CHANNEL_CACHE_SZIE.
        rewrite Z2Nat.id by lia. mauto.
      }
      sep pauto.
      rewrite ! Int.add_zero in H35.
      unfold get_off_addr; sep auto.
    }
    subst H29.

    (* RETURN ′ OS_NO_ERR *)
    eapply rete_rule.
    eapply inline_tactics.sep_infer_conjI.
    split.
    {
      intros.
      sep normal; sep eexists; sep autocancel.
      eapply disj_split; left.
      sep normal; sep eexists; sep autocancel.
      sep pauto.
      5: simpl; eauto.
      {
        rewrite ! Int.add_zero in H29.
        unfold Aarray in *; cbn [Aarray'].
        rewrite H36. sep auto.
      }
      { eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls2; eauto. }
      { eapply RLH_Channel_upd_dportls2_Sample; eauto. }
      {
        clear - H30 H15.
        eapply join_comm.
        eapply join_comm in H15.
        eapply join_set_set in H30; eauto.
      }
      { eapply Channel_dstkport_Sample_OutcoreC_upd_dportls2_Sample; eauto. }
      {
        eapply RLH_OtherPortPtrList_upd_Sample; eauto.
        all: eapply H11; lia.
      }
      {
        rewrite <- H12; clear.
        induction otherpl1; simpl; eauto.
      }
      { eauto. }
      {
        rewrite <- H24; clear.
        revert ori_msg_vl othermsgll2 v'0; induction othermsgll1;
        simpl; intros; auto.
        specialize (IHothermsgll1 ori_msg_vl othermsgll2 v'0).
        rewrite IHothermsgll1; auto.
      }
      {
        rewrite <- H12; clear.
        revert tm pin ndstport otherpl2; induction otherpl1;
        simpl; intros; auto.
        specialize (IHotherpl1 tm pin ndstport otherpl2).
        rewrite IHotherpl1; auto.
      }
    }
    intros.
    symbolic_execution.
  }
  {
    hoare normal pre; pure intro.
    assert (exists n dstport dstmsgl,
      nth_error dportl n = Some dstport /\
      nth_error dportmsgll n = Some dstmsgl /\
      nth_error dpptrl n = Some dstportp /\
      DomainportNode_P dstport (Z.to_nat DNUM, pd, pid, DestinationP next, pst, dstpin,
      dstpout, SamplePort pm) dstmsgl).
    { eapply RLH_Domainportl_abs_getsome; eauto. }
    simpljoin1.
    assert (x = ndstpptrn).
    { eapply dpptrl_not_same_elements; eauto. }
    subst x; clear H12.
    rewrite H in H32; inverts H32.
    apply nth_error_split in H as (dportl1 & dportl2 & ? & ?).
    apply nth_error_split in H1 as (dportmsgll1 & dportmsgll2 & ? & ?).
    apply nth_error_split in H31 as (dpptrl1 & dpptrl2 & ? & ?).
    subst dportl dportmsgll dpptrl. rename x1 into ndstmsgl.

    hoare name lift dmportp_sllseg pre.
    eapply backward_rule1.
    { eapply dmportp_sllseg_app'_frm; eauto.
      rewrite <- H25; instantiate (1:=dstportp).
      apply nth_error_middle. }
    cbn [dmportp_sllseg].
    hoare normal pre; pure intro.
    rename v'0 into dstportp.
  
    (* dmportp_sllseg_sampleport_msg *)
    hoare lift 2%nat pre.
    eapply backward_rule1.
    {
      eapply astar_mono.
      {
        intros.
        destruct H.
        { apply H. }
        sep destruct H; sep split in H.
        unfold DomainportNode_P in H14; simpljoin1.
        unfold Domainport_Portt_P in H42; simpljoin1.
        rewrite H44 in H25.
        exfalso; clear - H25; pauto.
      }
      eauto.
    }
    hoare normal pre; pure intro.
    rename v'1 into qstart.
    
    assert ((update_nth_val 9 (update_nth_val 8 ndstport (Vint32 pin))
      (Vint32 tm)) = ndstportupd).
    {
      clear - H24 H8 H9 H10 H11.
      destruct ndstport; destruct ndstportupd; simpl in *; tryfalse.
      do 18 (destruct H8 as [? H8]; destruct H24 as [? H24]; destruct ndstport; destruct ndstportupd; simpl in *; tryfalse).
      unfold OS_Port_V_msgInTick in H9; simpl in H9; inverts H9.
      unfold OS_Port_V_msgOutTick in H10; simpl in H10; inverts H10.
      assert (v = v0).
      {
        assert ((0 < 18)%nat) by lia; assert ((0 <> 8)%nat) by lia; assert ((0 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v.
      assert (v1 = v2).
      {
        assert ((1 < 18)%nat) by lia; assert ((1 <> 8)%nat) by lia; assert ((1 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v1.
      assert (v3 = v4).
      {
        assert ((2 < 18)%nat) by lia; assert ((2 <> 8)%nat) by lia; assert ((2 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v3.
      assert (v5 = v6).
      {
        assert ((3 < 18)%nat) by lia; assert ((3 <> 8)%nat) by lia; assert ((3 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v5.
      assert (v7 = v8).
      {
        assert ((4 < 18)%nat) by lia; assert ((4 <> 8)%nat) by lia; assert ((4 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v7.
      assert (v9 = v10).
      {
        assert ((5 < 18)%nat) by lia; assert ((5 <> 8)%nat) by lia; assert ((5 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v9.
      assert (v11 = v12).
      {
        assert ((6 < 18)%nat) by lia; assert ((6 <> 8)%nat) by lia; assert ((6 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v11.
      assert (v13 = v14).
      {
        assert ((7 < 18)%nat) by lia; assert ((7 <> 8)%nat) by lia; assert ((7 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v13.
      assert (v19 = v20).
      {
        assert ((10 < 18)%nat) by lia; assert ((10 <> 8)%nat) by lia; assert ((10 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v19.
      assert (v21 = v22).
      {
        assert ((11 < 18)%nat) by lia; assert ((11 <> 8)%nat) by lia; assert ((11 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v21.
      assert (v23 = v24).
      {
        assert ((12 < 18)%nat) by lia; assert ((12 <> 8)%nat) by lia; assert ((12 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v23.
      assert (v25 = v26).
      {
        assert ((13 < 18)%nat) by lia; assert ((13 <> 8)%nat) by lia; assert ((13 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v25.
      assert (v27 = v28).
      {
        assert ((14 < 18)%nat) by lia; assert ((14 <> 8)%nat) by lia; assert ((14 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v27.
      assert (v29 = v30).
      {
        assert ((15 < 18)%nat) by lia; assert ((15 <> 8)%nat) by lia; assert ((15 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v29.
      assert (v31 = v32).
      {
        assert ((16 < 18)%nat) by lia; assert ((16 <> 8)%nat) by lia; assert ((16 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v31.
      assert (v33 = v34).
      {
        assert ((17 < 18)%nat) by lia; assert ((17 <> 8)%nat) by lia; assert ((17 <> 9)%nat) by lia.
        specialize (H11 _ H9 H10 H40); simpl in H11; inverts H11; auto.
      }
      subst v33.
      auto.
    }
    subst ndstportupd.

    (* port_ptr ′ .. msgInTick =ₑ inTime ′;ₛ *)
    assert (exists itk, OS_Port_V_msgInTick ndstport = Some (Vint32 itk)).
    {
      clear - H24; unfold OS_Port_V_msgInTick.
      destruct ndstport; simpl in *; tryfalse.
      do 8 (destruct H24 as [? H24]; destruct ndstport; simpl in *; tryfalse).
      destruct H24 as [? H24].
      destruct v7; tryfalse. eauto.
    }
    destruct H25 as [itk ?].

    assert (exists otk, OS_Port_V_msgOutTick ndstport = Some (Vint32 otk)).
    {
      clear - H24; unfold OS_Port_V_msgOutTick.
      destruct ndstport; simpl in *; tryfalse.
      do 9 (destruct H24 as [? H24]; destruct ndstport; simpl in *; tryfalse).
      destruct H24 as [? H24].
      destruct v8; tryfalse. eauto.
    }
    destruct H27 as [otk ?].
    
    hoare name lift APortStruct pre.
    hoare name lift port_ptr pre.
    hoare name lift Aop pre.
    eapply seq_rule.
    {
      eapply port_memeber_asgn with (n := 8%nat); try pauto.
      { symbolic execution. }
      { eapply eq_int; tauto. }
      { pauto. }
      { sep auto. }
    }

    (* port_ptr ′ .. msgOutTick =ₑ OSTime ′;ₛ *)
    unfold AOSTime.
    hoare name lift APortStruct pre.
    hoare name lift port_ptr pre.
    hoare name lift Aop pre.
    eapply seq_rule.
    {
      eapply port_memeber_asgn with (n := 9%nat); try pauto.
      { symbolic execution. }
      { eapply nth_upd_neqrev; eauto. }
      { eapply eq_int; tauto. }
      { pauto. }
      { sep auto. }
    }

    (* (port_ptr ′ .. OSQStart) .. len =ₑ msg_ptr ′ .. len;ₛ *)
    unfold dmportp_sllseg_sampleport_msg.
    hoare normal pre; pure intro.
    hoare lifts (3::2::4::5::22::nil)%nat pre.
    unfold Aarray at 2. cbn [Aarray'].
    destruct msgptr as [msg_b msg_i].
    hoare normal pre.
    eapply seq_rule.
    {
      eapply assign_rule_general.
      {
        intros.
        eapply symbolic_lemmas.struct_offset_rv.
        {
          eapply symbolic_lemmas.addrof_deref_rv.
          eapply port_QStart_rv.
          3: sep autocancel; apply H29.
          { pauto. }
          {
            unfold OS_Port_V_OSQStart.
            eapply nth_upd_neqrev; eauto.
            eapply nth_upd_neqrev; eauto.
          }
        }
        all: pauto.
      }
      {
        assert ((fst qstart, snd qstart +ᵢ  Int.zero) = qstart).
        { clear; destruct qstart; simpl; rewrite Int.add_zero; auto. }
        rewrite H29; split; eauto.
      }
      {
        intros.
        eapply symbolic_lemmas.struct_member_rv_flag.
        {
          sep autocancel.
          assert ((msg_b, msg_i) = get_off_addr (msg_b, msg_i) Int.zero).
          { unfold get_off_addr; cbn [fst snd]; rewrite Int.add_zero; reflexivity. }
          rewrite H38 in H29.
          sep cancel get_off_addr.
          apply H29.
        }
        all: pauto.
        destruct H18; auto.
      }
      { eapply eq_int; tauto. }
      { sep auto. }
    }

    (* memcpy (­(port_ptr ′ .. OSQStart) .. data, msg_ptr ′ .. data, msg_ptr ′ .. len­);ₛ *)
    eapply seq_rule.
    {
      eapply call_rule'.
      { cbn; unfold OS_memcpy_spec; eauto. }
      {
        intros.
        eapply rvl_elim.
        {
          eapply symbolic_lemmas.addrof_array_elem_rv.
          {
            eapply port_OSQStart_data_rv.
            3: sep autocancel; apply H29.
            { pauto. }
            unfold OS_Port_V_OSQStart.
            eapply nth_upd_neqrev; eauto.
            eapply nth_upd_neqrev; eauto.
          }
          { symbolic execution. }
          all: pauto.
        }
        eapply rvl_elim.
        {
          eapply symbolic_lemmas.addrof_array_elem_rv.
          {
            eapply struct_member_array_rv. symbolic_execution.
            unfold OSMsg_t. eauto.
            1,2,3: cbn;auto.
          }
          { symbolic execution. }
          { auto. }
          { pauto. }
        }
        eapply rvl_elim; [ |apply rvl_nil].
        instantiate (1:=(Vint32 mlen)).
        destruct H18.
        eapply cast_rv_tint8_tint32; auto.
        eapply symbolic_lemmas.struct_member_rv_flag.
        {
          sep autocancel.
          assert ((msg_b, msg_i) = get_off_addr (msg_b, msg_i) Int.zero).
          { unfold get_off_addr; cbn [fst snd]; rewrite Int.add_zero; reflexivity. }
          rewrite H39 in H29.
          sep lift 5%nat in H29.
          apply H29.
        }
        all: pauto.
      }
      {
        intros; unfold_spec.
        sep normal. sep eexists.
        sep autocancel; sep split; eauto.
        rewrite ! Int.add_zero. 
        assert (length ori_msg_vl = Z.to_nat (Int.unsigned mlen)) by lia.
        rewrite H38 in H29.
        unfold Aarray at 2. sep cancel Aarray'.
        sep lift 5%nat in H29.
        pose proof firstn_skipn (Z.to_nat (Int.unsigned mlen)) (v'0 ++ v'1).
        assert ((length (firstn (Z.to_nat (Int.unsigned mlen)) (v'0 ++ v'1)) = (Z.to_nat (Int.unsigned mlen)))%nat).
        {
          apply firstn_length_le.
          rewrite H31; unfold nat_of_Z; apply Zle_natle; auto.
        }
        assert ((length (skipn (Z.to_nat (Int.unsigned mlen)) (v'0 ++ v'1)) = (Z.to_nat (CHANNEL_CACHE_SZIE - Int.unsigned mlen)))%nat).
        {
          rewrite skipn_length.
          rewrite H31; unfold nat_of_Z; lia.
        }
        assert ((Z.to_nat (Int.unsigned mlen) + Z.to_nat (CHANNEL_CACHE_SZIE - Int.unsigned mlen) = Z.to_nat CHANNEL_CACHE_SZIE)%nat) by lia.
        unfold nat_of_Z in H29. rewrite <- H42 in H29.
        rewrite <- H39 in H29. rewrite <- H40 in H29 at 1. rewrite <- H41 in H29.
        eapply Aarray_split in H29; auto.
        {
          rewrite H40 in H29. rewrite H41 in H29.
          sep cancel Aarray; apply H29.
        }
        rewrite H40, H41, H42.
        clear. unfold CHANNEL_CACHE_SZIE.
        rewrite Z2Nat.id by lia. mauto.
      }
      { good_frm_sovler. }
      { sep_unfold_funpost. intros. sep destruct H29. sep auto. }
      { sep_unfold_funpre. intros. sep destruct H29. sep auto. }
      { pauto. }
    }
    unfold getasrt; unfold OS_memcopyPost, OS_memcopyPost'.
    hoare normal pre. pure intro.
    inversion H38. subst v'7 v'8 v'9 v'6. clear H38.
    inversion H29. subst v'4 v'3 v'5. clear H29.

    (*go abscode: samplepost_sendmemcpy_one *)
    hoare remember (1::22::23::24::25::20::nil)%nat pre.
    hoare abscsq; [apply noabs_oslinv | auto .. ].
    {
      eapply samplepost_sendmemcpy_one_cont; eauto.
      2:{ eapply join_get_l; eauto. }
      3:{ eapply join_get_l; eauto. }
      2:{ rewrite <- H7; eauto. }
      subst H29; can_change_aop_solver'.
    }

    subst H29.
    eapply seq_rule.
    {
      eapply ift_rule''.
      {
        intros.
        sep_get_port_rv.
        {
          eapply port_coreNum_rv'.
          2: sep autocancel; apply H29.
          { pauto. }
        }
        all: pauto.
        {
          assert (nth_val' 2 (update_nth_val 9 (update_nth_val 8 ndstport (Vint32 pin)) (Vint32 tm)) = nth_val' 2 ndstport).
          {
            rewrite nth_val_nth_val'_some_eq at 1; eauto.
            do 2 (eapply nth_upd_neqrev; eauto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2.
            clear - H24.
            destruct ndstport; simpl in *; tryfalse.
            do 2 (destruct H24 as [? H24]; destruct ndstport; simpl in *; tryfalse).
            lia.
          }
          rewrite H38.
          unfold DomainportNode_P in H14; simpljoin1.
          unfold Domainport_nat_P in H14; simpljoin1.
          unfold OS_Port_V_coreNum in H14;
          apply nth_val_nth_val'_some_eq in H14; rewrite H14.
          pauto.
        } 
        {
          assert (nth_val' 2 (update_nth_val 9 (update_nth_val 8 ndstport (Vint32 pin)) (Vint32 tm)) = nth_val' 2 ndstport).
          {
            rewrite nth_val_nth_val'_some_eq at 1; eauto.
            do 2 (eapply nth_upd_neqrev; eauto).
            eapply symbolic_lemmas.nth_val_imp_nth_val'_2.
            clear - H24.
            destruct ndstport; simpl in *; tryfalse.
            do 2 (destruct H24 as [? H24]; destruct ndstport; simpl in *; tryfalse).
            lia.
          }
          rewrite H38.
          unfold DomainportNode_P in H14; simpljoin1.
          unfold Domainport_nat_P in H14; simpljoin1.
          unfold OS_Port_V_coreNum in H14;
          apply nth_val_nth_val'_some_eq in H14; rewrite H14.
          pauto.
        } 
      }
      hoare normal pre; pure intro.
      instantiate (1:=Afalse).
      exfalso.
      assert (nth_val' 2 (update_nth_val 9 (update_nth_val 8 ndstport (Vint32 pin)) (Vint32 tm)) = nth_val' 2 ndstport).
      {
        rewrite nth_val_nth_val'_some_eq at 1; eauto.
        do 2 (eapply nth_upd_neqrev; eauto).
        eapply symbolic_lemmas.nth_val_imp_nth_val'_2.
        clear - H24.
        destruct ndstport; simpl in *; tryfalse.
        do 2 (destruct H24 as [? H24]; destruct ndstport; simpl in *; tryfalse).
        lia.
      }
      rewrite H42 in H29.
      unfold DomainportNode_P in H14; simpljoin1.
      unfold Domainport_nat_P in H14; simpljoin1.
      unfold OS_Port_V_coreNum in H14;
      apply nth_val_nth_val'_some_eq in H14; rewrite H14 in H29.
      clear - H29; unfold val_inj, notint in H29;
      rewrite Int.eq_true in H29; pauto.
    }

    hoare forward.
    hoare normal pre; pure intro.
    clear H29.
    
    (* merge dmportp_sllseg *)
    hoare remember (13::16::17::19::21::22::nil)%nat pre.
    eapply backward_rule1.
    {
      intros.
      instantiate (1:=
        dmportp_sllseg headptr Vnull (dportl1 ++ (update_nth_val 9
              (update_nth_val 8 ndstport (Vint32 pin)) 
              (Vint32 tm)) :: dportl2)
        (dportmsgll1 ++ (ori_msg_vl :: nil) :: dportmsgll2) OS_Port_V_nextPort ** H29 ).
      eapply dmportp_sllseg_compose; eauto.
      { rewrite H12; auto. }
      {
        instantiate (1:=v').
        clear - H1.
        unfold OS_Port_V_nextPort in *.
        do 2 (apply nth_upd_neqrev; eauto).
      }
      {
        instantiate (1:=qstart).
        clear - H26.
        unfold OS_Port_V_OSQStart in *.
        do 2 (apply nth_upd_neqrev; eauto).
      }
      sep lift 4%nat.
      eapply disj_split; left.
      sep normal; sep eexists; sep autocancel.
      sep pauto.
      2:{
        clear - H.
        unfold OS_Port_V_mode in *.
        do 2 (apply nth_upd_neqrev; eauto).
      }
      unfold dmportp_sllseg_sampleport_msg.
      sep normal; sep eexists; sep autocancel.
      instantiate (1:=ori_msg_vl).
      instantiate (1:=(skipn (Z.to_nat (Int.unsigned mlen)) (v'0 ++ v'1))).
      assert ((fst qstart, snd qstart +ᵢ  Int.zero) = qstart).
      { clear; destruct qstart; simpl; rewrite Int.add_zero; auto. }
      rewrite H29 in H38.
      sep pauto.
      2:{
        f_equal. rewrite H39.
        rewrite Z2Nat.id by (apply Int.unsigned_range).
        rewrite Int.repr_unsigned; auto.
      }
      2:{
        split.
        { rewrite H39, H40; unfold nat_of_Z; lia. }
        apply array_type_vallist_match_app; split.
        { destruct H18; auto. }
        pose proof firstn_skipn (Z.to_nat (Int.unsigned mlen)) (v'0 ++ v'1).
        rewrite <- H41 in H32.
        apply array_type_vallist_match_app in H32.
        destruct H32; auto.
      }
      assert ((Z.to_nat (Int.unsigned mlen) + Z.to_nat (CHANNEL_CACHE_SZIE - Int.unsigned mlen) = Z.to_nat CHANNEL_CACHE_SZIE)%nat) by lia.
      unfold nat_of_Z; rewrite <- H41.
      eapply astar_r_aemp_elim.
      eapply Aarray_merge; eauto.
      {
        rewrite H41.
        clear. unfold CHANNEL_CACHE_SZIE.
        rewrite Z2Nat.id by lia. mauto.
      }
      sep pauto.
      rewrite ! Int.add_zero in H38.
      unfold get_off_addr; sep auto.
    }
    subst H29.

    (* RETURN ′ OS_NO_ERR *)
    unfold AOSCorePortPtrList at 2.
    hoare normal pre; pure intro.
    rename H29 into Hcptr.
    eapply rete_rule.
    eapply inline_tactics.sep_infer_conjI.
    split.
    {
      intros.
      sep normal; sep eexists; sep autocancel.
      eapply disj_split; right.
      sep normal; sep eexists; sep autocancel.
      sep pauto.
      {
        unfold AOSCorePortPtrList.
        sep pauto.
        2:{ eapply RH_CorePortPtrList_upd_dportls; eauto. }
        rewrite ! Int.add_zero in H29.
        unfold Aarray in *; cbn [Aarray'].
        rewrite H39. sep auto.
      }
      { eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto. }
      { eapply RLH_Channel_upd_dportls1; eauto. }
      {
        clear - H30 H15.
        eapply join_set_set in H30; eauto.
      }
      { eapply Channel_dstkport_Sample_IncoreC_upd_dportls1; eauto. }
      { eapply R_Kernelport_DomainPort_upd; eauto. all: eapply H11; lia. }
      { eapply RLH_Domainportl_upd_Sample; eauto. all: eapply H11; lia. }
      { eapply RL_PortAttr_upd; eauto. all: eapply H11; lia. }
      { eapply RL_PortPtrList_upd; eauto. all: eapply H11; lia. }
      {
        rewrite <- H12; clear.
        induction dportl1; simpl; eauto.
      }
      { eauto. }
      {
        rewrite <- H23; clear.
        revert ori_msg_vl dportmsgll2 v'0; induction dportmsgll1;
        simpl; intros; auto.
        specialize (IHdportmsgll1 ori_msg_vl dportmsgll2 v'0).
        rewrite IHdportmsgll1; auto.
      }
      {
        rewrite <- H12; clear.
        revert tm pin ndstport dportl2; induction dportl1;
        simpl; intros; auto.
        specialize (IHdportl1 tm pin ndstport dportl2).
        rewrite IHdportl1; auto.
      }
    }
    intros.
    symbolic_execution.
  }
Qed.
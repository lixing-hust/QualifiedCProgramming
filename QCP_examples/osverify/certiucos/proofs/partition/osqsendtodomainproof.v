Require Import ucos_include.
Require Import Lia.

Require Import aux_pureLib.

Require Import abs_op_corecommu_rules.
Require Import corecommu_sep_added.
Require Import corecommu_tactics.
Require Import OSTimeTickPure.
Require Import partition_rules.
Require Import partition_seprules.
Require Import partition_absrules.
Require Import partition_symrules.
Require Import partition_tactics.
Require Import partition_taskeventrules.
Require Import corecommu_rules.
Require Import qportpostproof_aux.
Require Import gjb_common.
Require Import sem_corecommu.
Require Import new_inv.

Open Scope code_scope.

Open Scope int_scope.

Lemma OSQSendToDomain_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSQSendToDomain vl logicl OSQSendToDomainPre ct->
      Some r =
      BuildRetI os_internal OSQSendToDomain vl logicl OSQSendToDomainPost ct->
      exists t d1 d2 s,
        os_internal OSQSendToDomain = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  rename x into msg_ptr_hold.
  rename x0 into port_ptr_hold.
  rename H1 into Hmsg_ptr_hold_isptr.
  rename H2 into Hport_ptr_hold_isptr.
  eapply backward_rule1.
  intros. sep name lift Aop in H. apply disj_split in H. apply H.
  (* divide to prove *)
  apply disj_rule.
  - (*核间通讯*)
    naive pure intro.
    rename v' into s.
    rename v'0 into er.
    rename v'1 into portptr.
    rename v'2 into msgptr.
    rename v'3 into msg.
    rename v'4 into mlen.
    rename v'5 into cheapl.
    rename v'6 into dstkportpl.
    rename v'7 into dstkportpl1.
    rename v'8 into dstkportp.
    rename v'9 into dstkportpl2.
    rename v'10 into dportl.
    rename v'11 into dstportp.
    inverts H8.
    clear Hmsg_ptr_hold_isptr Hport_ptr_hold_isptr.
    rename v'12 into ndstpptrn.
    rename v'13 into otherppl.
    rename v'14 into otherpl.
    rename v'15 into othermsgll.
    rename v'16 into dportls1.
    rename v'17 into dportls2.
    rename v'18 into kportls.
    rename v'19 into chanls.
    rename v'20 into vsdstcl.
    rename v'21 into cheape.
    rename v'22 into cheapt.
    rename v'23 into pcn.
    rename v'24 into pd.
    rename v'25 into pid.
    rename v'26 into pst.
    rename v'27 into dstpin.
    rename v'28 into dstpout.
    rename v'29 into dstsz.
    rename v'30 into dstpm.
    rename v'31 into ppcn.
    rename v'32 into ppid.
    rename v'33 into chanpl.
    rename v'34 into chanl.
    rename v'35 into chandstkportll.
    rename v'36 into kportpl.
    rename v'37 into kportl.
    rename v'38 into kportp.
    rename v'39 into chanptr.
    rename v'40 into kpst.
    rename v'41 into cid.
    rename v'42 into cdn.
    rename v'43 into dstkpst.
    rename v'44 into csemid.
    rename v'45 into nextdst.
    rename H6 into Hdstkportpl_split.
    rename H7 into Hlen_dstkportpl_vsdstcl.
    subst logicl.
    rename H9 into Hgetheapmsg.
    rename H10 into Hmlensize.
    rename H11 into HSmlen.
    rename H12 into Hget_dstkportp.
    rename H13 into Hdportljoin.
    rename H14 into HRLHChannel.
    rename H15 into HRLH_Kernel_Channel.
    rename H16 into Hmsg_type_match.
    rename H17 into Hget_kportp.
    rename H18 into Hvsdstcl_pcn.
    rename H19 into Hkportls_nodup.
    rename H into Hvsdstcl.
    rename H0 into Hget_chanptr.
    rename H1 into Hpcn_DNUM_neq.
    rename H2 into Hget_dstportp.
    rename H3 into Hnerr_otherppl.
    rename H4 into HRLH_Other.
    rename H5 into HChannel_dstkport_Queue_OutcoreC.
    
    assert (exists n dstport dstmsgl,
      nth_error otherpl n = Some dstport /\
      nth_error othermsgll n = Some dstmsgl /\
      nth_error otherppl n = Some dstportp /\
      OtherPortNode_P dstport (pcn, pd, pid, DestinationP nextdst, pst,
        dstpin, dstpout, QueuePort dstsz dstpm) dstmsgl).
    { eapply RLH_OtherPortPtrList_abs_getsome; eauto. }
    simpljoin1.
    rename H into Hnerr_otherpl.
    rename H0 into Hnerr_othermsgll.
    rename H1 into Hnerr_otherppl'.
    rename H2 into HOtherPortNode.
    assert (x = ndstpptrn).
    { eapply otherppl_not_same_elements; eauto. }
    subst x. clear Hnerr_otherppl'.
    rename x0 into dstport.
    rename x1 into dstportmsgl.
    apply nth_error_split in Hnerr_otherpl as (otherpl1 & otherpl2 & Hotherpl_split & Hlen_otherpl_n).
    apply nth_error_split in Hnerr_othermsgll as (othermsgll1 & othermsgll2 & Hothermsgll_split & Hlen_othermsgl_n).
    apply nth_error_split in Hnerr_otherppl as (otherppl1 & otherppl2 & Hotherppl_split & Hlen_otherppl_n).
    subst otherppl otherpl othermsgll. 

    hoare name lift OtherPortPtrList pre.
    eapply backward_rule1.
    { eapply OtherPortPtrList_app'_frm; eauto. }
    cbn [OtherPortPtrList].
    naive pure intro.
    rename H into Hdstport_type_match.
    rename H0 into Hdstport_V_Start.
    (* dmportp_sllseg_qport_msg *)
    hoare lift 2%nat pre.
    eapply backward_rule1.
    {
      eapply astar_mono.
      {
        intros.
        destruct H.
        2:{ apply H. }
        sep destruct H; sep split in H.
        unfold OtherPortNode_P in HOtherPortNode; simpljoin1.
        unfold OtherPort_Portt_P in H3; simpljoin1.
        setoid_rewrite H5 in H0. discriminate.
      }
      eauto.
    }
    naive pure intro.
    rename v' into qstart.
    rename H into Hdstport_V_mode.
    rename H0 into Hdstport_V_End.
    rename H1 into Hdstport_V_In.
    rename H2 into Hdstport_V_Out.
    simpljoin.
    rename H1 into Hdstport_V_Size.
    rename H2 into Hsize_range.
    rename H into Hdstport_V_Entries.
    rename H0 into Hentries_le_size.
    rename H5 into HQport_msg_ptrs.
    

    (* If (′ DNUM ==ₑ port_ptr ′ .. coreNum);ₛ *)
    eapply seq_rule.
    {
      apply ift_zero_rule.
      intros.
      unfold OtherPortNode_P in HOtherPortNode.
      destruct HOtherPortNode as (HOtherPortNode&_&_).
      unfold OtherPort_nat_P in HOtherPortNode.
      simpljoin.
      eapply symbolic_lemmas.bop_rv.
      - symbolic_execution.
      - eapply port_coreNum_rv''; eauto.
        sep autocancel; apply H.
      - simpl. clear - Hpcn_DNUM_neq. rewrite Int.eq_false. reflexivity.
        pose proof Int.eq_dec ($ DNUM) x. destruct H; auto.
        subst. rewrite Int.unsigned_repr in Hpcn_DNUM_neq. unfold Coqlib.nat_of_Z in Hpcn_DNUM_neq.
        rewrite Z2Nat.id in Hpcn_DNUM_neq. lia.
        pose proof dnum_range. lia.
        pose proof dnum_range. rewrite max_unsigned_val. lia.
      - auto.
      - reflexivity.
    }
    hoare forward.
    eapply ift_rule'' with (q:=Afalse).
    * symbolic_exe_port.
    * (*GENERATEIPC (port_ptr ′ .. coreNum, ′ GET_PORT_MESSAGE);ₛ
      RETURN 〈 char_t 〉 ′ OS_Q_FULL *)
      cbn [qportpost_send_Outcore]. simpl spec_code_cons.
      partition_absrulestac absinfer_choice1.
      rewrite <- Hlen_dstkportpl_vsdstcl.
      rewrite app_length. cbn [length].
      assert (length dstkportpl1 + S (length dstkportpl2) -
      S (length dstkportpl2)=length dstkportpl1)%nat as Htmp by lia.
      rewrite Htmp. clear Htmp.
      rewrite Hvsdstcl_pcn ; [ | lia].
      unfold OtherPortNode_P in HOtherPortNode.
      unfold OtherPort_nat_P in HOtherPortNode.
      assert (OS_Port_V_coreNum dstport = Some (V$ (Z.of_nat pcn))) as Hdstport_V_coreNum.
      {
        unfold OS_Port_Seg_dls in HOtherPortNode.
        destruct HOtherPortNode as (HOtherPortNode&_&_).
        simpljoin.
        rewrite H. repeat f_equal.
        rewrite Z2Nat.id.
        now rewrite Int.repr_unsigned.
        pose proof Int.unsigned_range x. lia.
      }
      eapply seq_rule.
      + apply generateipc_rule.
        ++ go. 
        ++ rewrite Z2Nat.id.
          pose proof Int.unsigned_range_2 ($ Z.of_nat pcn). tauto.
          pose proof Int.unsigned_range_2 ($ Z.of_nat pcn). tauto.
        ++ intros. split. 
          -- eapply port_coreNum_rv''; eauto.
              ** rewrite Hdstport_V_coreNum. f_equal.
                unfold OS_Port_Seg_dls in Hdstport_type_match.
                clear - Hdstport_type_match Hdstport_V_coreNum.
                struct_type_vallist_match'_elim.
                unfold OS_Port_V_coreNum in Hdstport_V_coreNum.
                simpl in Hdstport_V_coreNum. inverts Hdstport_V_coreNum.
                f_equal. rewrite Z2Nat.id.
                now rewrite Int.repr_unsigned.
                pose proof Int.unsigned_range ($ Z.of_nat pcn). lia.
              ** sep autocancel. apply H.
          -- symbolic_execution.
        ++ intros. unfold CurLINV. unfold p_local in H. sep auto.
      + eapply rete_rule. intros. split.
        2: symbolic_execution.
        sep normal.
        sep eexists. sep autocancel. left.
        sep normal. sep eexists.
        sep name lift OtherPortPtrList.
        eapply OtherPortPtrList_compose; eauto.
        2:{ 
          sep autocancel. 
          apply disj_star_elim_disj'. right.
          sep normal. sep eexists. sep autocancel.
          sep split; eauto. 
          - sep auto.
          - rewrite app_length. simpl length. sep auto.
          - simpl. eauto.
        }
        congruence.
      * rename v'0 into qend.
        rename v'1 into qin.
        rename v'2 into qout.
        rename v'3 into qsize.
        rename v'4 into qentries.
        apply disj_rule.
        naive pure intro. apply pfalse_rule.
        naive pure intro.
        destruct H.
        2:{
        exfalso; clear - H.
        destruct (Int.ltu qsize qentries); destruct (Int.eq qentries qsize); simpl in H; mauto.
        }
        assert (Int.unsigned qentries < Int.unsigned qsize) as Hentries_lt_size.
        {
        clear - H Hentries_le_size.
        destruct (Int.ltu qsize qentries) eqn:E1; destruct (Int.eq qentries qsize) eqn:E2; simpl in H.
        1-3:mauto.
        apply Inteq_false_is_Zneq in E2. lia.
        }
        clear H Hentries_le_size.
        (* (port_ptr ′ .. OSQIn) .. len =ₑ msg_ptr ′ .. len;ₛ *)
        destruct msgptr as [msgptrb msgptro].
        hoare normal pre.
        hoare name lift (dmportp_sllseg_qport_msg qin) pre.
        eapply backward_rule1.
        {
          eapply dmportp_sllseg_qport_msg_ngt0.
          clear - Hentries_lt_size.
          unfold Coqlib.nat_of_Z. lia.
        }
        naive pure intro.
        destruct H as (msghold&msgholdl&?&Hmsg_le_channel_size). subst v'5.
        assert (Z.to_nat (Int.unsigned mlen + 1) = S (Z.to_nat (Int.unsigned mlen))) as HSmlen' by lia.
        rewrite HSmlen' in HSmlen. inverts HSmlen.
        hoare name lift msghold pre.
        eapply backward_rule1.
        {
          apply dmportp_sllseg_qport_msg_split.
          unfold Coqlib.nat_of_Z. lia. 
        }
        naive pure intro.
        destruct H. destruct H1.
        invertsr H1. rename v'1 into irrmsghold.
        rename H2 into Hmsghold_type_match.
        rename H into Hmsghold_channel_size.
        rename H3 into Hmsghold_le_channel_size.
        cbn [Aarray Aarray'].
        hoare name lift Aop (Aptrmapsto qin) pre.
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
            assert ((fst qin, Int.add (snd qin) (Int.zero)) = qin ).
            {
              rewrite Int.add_zero. now destruct qin. 
            }
            rewrite H. clear H.
            split; intros; eauto.
          }
          { 
            intros. 
            eapply symbolic_lemmas.struct_member_rv_flag.
            sep autocancel.
            2-6: try reflexivity.
            unfold get_off_addr. cbn [fst snd].
            rewrite Int.add_zero.
            sep autocancel. apply H.
            simpl. clear - Hmsg_type_match.
            simpl in Hmsg_type_match. tauto.
          }
          { now apply assign_type_match_true. }
          {
            intros. sep eexists. sep auto.
          }
        }
        clear Hmsg_le_channel_size.
        rename H0 into Hlenmsg_mlen.
        (* memcpy (­&ₐ ((port_ptr ′ .. OSQIn) .. data) [′ 0], &ₐ (msg_ptr ′ .. data) [′ 0],
        〈 long 〉 msg_ptr ′ .. len­);ₛ *)
        assert ((fst qin, Int.add (snd qin) (Int.zero)) = qin).
        {
          rewrite Int.add_zero. now destruct qin. 
        }
        rewrite H. clear H.
        destruct qin as [qinb qino].
        unfold get_off_addr.  cbn[fst snd].
        hoare name lift (Alvarmapsto port_ptr) APortStruct (Aptrmapsto (qinb, qino)) pre.
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
              rewrite <- H0. sep autocancel.
              exact H.
            }
            all: try reflexivity.
            simpl in Hmsg_type_match. tauto.
          }
          {
            intros; unfold_spec. cbn [fst snd].
            sep normal. sep eexists.
            sep autocancel; sep split; eauto.
            rewrite ! Int.add_zero.
            sep name lift msghold in H.
            eapply Aarray_split_single with (m:=(Z.to_nat (Int.unsigned mlen)))in H.
            2:{
              unfold CHANNEL_CACHE_SZIE. clear. mauto. 
            }
            2:{
              clear - Hmlensize. unfold Coqlib.nat_of_Z. lia.
            }
            2: rewrite app_length; auto.
            sep autocancel.
            sep name lift Aarray' in H. unfold Aarray.
            rewrite <- Hlenmsg_mlen.
            sep autocancel. apply H.
          }
          { go. }
          { sep_unfold_funpost. intros. sep destruct H. sep auto. }
          { sep_unfold_funpre. intros. sep destruct H. sep auto. }
          { pauto. }
        }
        unfold getasrt; unfold OS_memcopyPost, OS_memcopyPost'.
        hoare normal pre. pure intro.
        invertsr H.
        invertsr H0. clear H1.
        rename H2 into Hlen_irrmsghold.
        rewrite ! Int.add_zero.
        hoare abs lift pre.
        (* ++ port_ptr ′ .. OSQIn;ₛ *)
        eapply seq_rule.
        {
          eapply port_memeber_asgn; try reflexivity.
          - sep auto. split; intros.
            sep autocancel. exact H.
            sep auto.
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
        assert (Int.unsigned (qentries +ᵢ  $ 1) <=? Int16.max_unsigned = true) as Hqentries_range.
        {
          clear - Hentries_lt_size Hsize_range.
          pose proof Int_add_one_Sn qentries ltac:(lia).
          rewrite Z.leb_le. rewrite int16_max_unsigned_val. lia.
        }
        eapply seq_rule.
        {
          eapply port_memeber_asgn; try reflexivity.
          - intros. eapply symbolic_lemmas.bop_rv.
            * eapply port_QEntries_rv. 
              3: { sep autocancel. apply H. }
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
          - simpl. now rewrite Hqentries_range.
          - intros. sep auto.
        }
        (* If (port_ptr ′ .. OSQIn ==ₑ port_ptr ′ .. OSQEnd)
        {port_ptr ′ .. OSQIn =ₑ port_ptr ′ .. OSQStart};ₛ *)
        hoare name lift APortStruct pre.
        destruct qend as [qendb qendo].
        hoare remember (1::nil)%nat pre.
        apply seq_rule with (APortStruct dstportp (update_nth_val 17
        (update_nth_val 14 dstport
          (Vptr (dmportp_sllseg_qport_msg_next (qinb,qino) qstart (qendb,qendo))))
        (Vint32 (qentries +ᵢ  $ 1)))**H).
        {
          eapply ift_rule.
          - intros. eexists. subst H.
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
            * destruct (peq qinb qendb); auto.
              destruct (Int.eq (qino +ᵢ  Int.mul ($ 1) ($ 33)) qendo); auto.
            * reflexivity.
          - intros. 
            eapply sep_aconj_r_aisfalse_to_astar in H0.
            2:{ intros. subst H.
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
            * destruct (peq qinb qendb); auto.
              destruct (Int.eq (qino +ᵢ  Int.mul ($ 1) ($ 33)) qendo); auto.
            * reflexivity.
            }
            sep split in H0.
            destruct H1. 
            2:{ destruct (peq qinb qendb);
            destruct (Int.eq (qino +ᵢ  Int.mul ($ 1) ($ 33)) qendo); auto; simpl in H1; discriminate. }
            sep cancel H.
            unfold dmportp_sllseg_qport_msg_next.
            simpl typelen. unfold msg_distance.
            unfold Qport_msg_ptrs_P in HQport_msg_ptrs.
            destruct qstart. simpljoin1. unfold get_off_addr in *.
            simpl in H3, H5.
            invertsr H3. invertsr H5.
            cbn [fst snd] in *.
            rewrite ! Int.add_zero_l in *.
            rewrite peq_true in H1.
            destruct (Int.eq (Int.mul ($ x0) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
            (Int.mul ($ Int.unsigned qsize) ($ 33))) eqn:E'; [discriminate | ].
            simpl typelen. simpl Z.of_nat.
            assert (
            (qinb, Int.mul ($ x0) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)) =
            (if
                    Int.unsigned
                      (Int.divu
                         (Int.mul ($ Int.unsigned qsize) ($ 33) -ᵢ
                          Int.mul ($ x0) ($ 33)) ($ 33)) =? 1
                   then (qinb, Int.zero)
                   else (qinb, Int.mul ($ x0) ($ 33) +ᵢ  $ 33))).
            {
              clear - H7 H8 Hsize_range E'.
              destruct (Int.unsigned (Int.divu (Int.mul ($ Int.unsigned qsize) ($ 33) -ᵢ Int.mul ($ x0) ($ 33)) ($ 33)) =? 1) eqn:?.
              2: { rewrite (Int.mul_commut ($ 1)).  rewrite Int.mul_one. reflexivity. }
              exfalso.
              assert (exists n,  Int.unsigned qsize = n + x0 /\ 1 <= n <= 65536).
              { exists (Int.unsigned qsize- x0). split;lia. }
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
            rewrite H in H0. sep autocancel.
          - intros.
            eapply backward_rule1. 
            eapply sep_aconj_r_aistrue_to_astar.
            { intros. subst H.
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
            * destruct (peq qinb qendb); auto.
              destruct (Int.eq (qino +ᵢ  Int.mul ($ 1) ($ 33)) qendo); auto.
            * reflexivity.
            }
            naive pure intro.
            subst H.
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
            unfold Qport_msg_ptrs_P in HQport_msg_ptrs.
            destruct qstart. simpljoin1. unfold get_off_addr in *.
            simpl in H4, H6.
            invertsr H4. invertsr H6.
            cbn [fst snd] in *.
            clear H1 H2.
            rewrite ! Int.add_zero_l in *.
            rewrite peq_true in H0.
            destruct (Int.eq (Int.mul ($ x0) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
            (Int.mul ($ Int.unsigned qsize) ($ 33))) eqn:E'.
            2:{
              simpl in H0. congruence.
            }
            simpl typelen. simpl Z.of_nat.
            rewrite aux_pureLib.Int_eq_dec in E'.
            rewrite <- E'.
            rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. 
            rewrite (Int.mul_commut ($ 1)).
            rewrite Int.mul_one.
            assert ((Int.divu ($ 33) ($ 33)) = Int.one)  by (clear;mauto).
            rewrite H1.
            rewrite Int.unsigned_one.
            rewrite Z.eqb_refl.
            rewrite update_nth_val_diff in H. 2:lia.
            rewrite update_nth_val_same in H.
            sep auto.
      }
        subst H.
        (*  qportpost_send_one_Outcore (S (length dstkportpl2))
          (|Vptr portptr
            :: Vptr (msgptrb, msgptro)
            :: V$ Z.of_nat (length (dstkportpl1 ++ dstkportp :: dstkportpl2))
              :: V$ Z.of_nat csemid :: vsdstcl|) *)
        
        partition_absrulestac absinfer_choice2.
        
        hoare name lift Aop osdomainportid oskportid oschannelid oscoreheapid pre.
        hoare abscsq;[apply noabs_oslinv| | ].
        {
          eapply qportpost_send_one_OutCore_cont.
          - go. 
          - apply Hget_kportp.
          - apply Hget_chanptr.
          - rewrite HSmlen'. rewrite <- Hlenmsg_mlen. eauto.
          - auto.
          - assert (length (dstkportpl1 ++ dstkportp :: dstkportpl2) - S (length dstkportpl2) = length dstkportpl1)%nat as Htmp.
            rewrite app_length. simpl length. lia.
            rewrite Htmp. apply nth_error_middle.
          - eauto.
          - eapply join_get_get_r; eauto.
          - assert (length (dstkportpl1 ++ dstkportp :: dstkportpl2) - S (length dstkportpl2) = length dstkportpl1)%nat as Htmp.
            rewrite app_length. simpl length. lia.
            rewrite Htmp. auto. 
        }

        (*GENERATEIPC (port_ptr ′ .. coreNum, ′ GET_PORT_MESSAGE);ₛ*)
        rewrite <- Hlen_dstkportpl_vsdstcl.
        rewrite app_length. cbn [length].
        assert (length dstkportpl1 + S (length dstkportpl2) -
        S (length dstkportpl2)=length dstkportpl1)%nat as Htmp by lia.
        rewrite Htmp. clear Htmp.
        rewrite Hvsdstcl_pcn; [ | lia].
        unfold OtherPortNode_P in HOtherPortNode.
        unfold OtherPort_nat_P in HOtherPortNode.
        assert (OS_Port_V_coreNum dstport = Some (V$ (Z.of_nat pcn))) as Hdstport_V_coreNum.
        {
          unfold OS_Port_Seg_dls in HOtherPortNode.
          destruct HOtherPortNode as (HOtherPortNode&_&_).
          simpljoin.
          rewrite H. repeat f_equal.
          rewrite Z2Nat.id.
          now rewrite Int.repr_unsigned.
          pose proof Int.unsigned_range x. lia.
        }
        eapply seq_rule.
        + apply generateipc_rule.
          ++ go.
          ++ rewrite Z2Nat.id.
            pose proof Int.unsigned_range_2 ($ Z.of_nat pcn). tauto.
            pose proof Int.unsigned_range_2 ($ Z.of_nat pcn). tauto.
          ++ intros. split. 
            -- eapply port_coreNum_rv''.
                **  instantiate (1:= update_nth_val 17
                  (update_nth_val 14 dstport
                    (Vptr
                        (dmportp_sllseg_qport_msg_next
                          (qinb, qino) qstart
                          (qendb, qendo))))(Vint32 (qentries +ᵢ  $ 1))).
                  port_nth_val_solve. 
                  rewrite Z2Nat.id.
                  rewrite Int.repr_unsigned. auto.
                  pose proof Int.unsigned_range ($ Z.of_nat pcn). lia.
                ** qportpostproof_tac. 
                ** sep autocancel. apply H.
          -- symbolic_execution.
          ++ intros. unfold CurLINV. unfold p_local in H. sep auto.
        + eapply rete_rule. intros. split.
          2: symbolic_execution.
          sep normal.
          sep eexists.
          sep cancel port_ptr.
          sep cancel msg_ptr.
          sep cancel A_dom_lenv.
          left.
          sep normal. sep eexists.
          do 4 (sep cancel Aabsdata).
          sep cancel Aie.
          sep cancel Ais.
          sep cancel Aisr.
          sep cancel Aier.
          sep cancel A_isr_is_prop.
          sep cancel Acs.
          sep cancel p_local.
          sep split; auto.
          6: reflexivity.

          sep normal.
          sep autocancel.
          simpl typelen. simpl Z.of_nat.
          unfold Aarray at 2 in H. rewrite Hlenmsg_mlen.
          sep name lift OtherPortPtrList.
          eapply OtherPortPtrList_compose.
          5:{ 
            sep cancel Aarray'. 
            sep cancel OtherPortPtrList.
            sep cancel OtherPortPtrList.
            sep cancel APortStruct.
            right.
            sep normal. sep eexists.
            sep name lift dmportp_sllseg_qport_msg.
            sep split.
            5-8: port_nth_val_solve.
            3,4: split;[ port_nth_val_solve | auto ].
            eapply dmportp_sllseg_qport_msg_append_tail.
            4:{
              sep eexists. sep autocancel.
              assert (∘(Int.unsigned qsize - Int.unsigned (qentries +ᵢ  $ 1))=
              Init.Nat.pred ∘ (Int.unsigned qsize - Int.unsigned qentries))%nat as Htmp.
              {
                unfold Coqlib.nat_of_Z.
                rewrite <- Z2Nat.inj_pred.
                f_equal.
                rewrite <- Z.sub_1_r. 
                rewrite <- Z.sub_add_distr. f_equal.
                apply Int_add_one_Sn'.
                clear - Hdstport_type_match Hdstport_V_Entries.
                unfold OS_Port_Seg_dls in Hdstport_type_match.
                struct_type_vallist_match'_elim.
                inverts Hdstport_V_Entries. lia.
              }
              rewrite Htmp. clear Htmp.
              sep autocancel. sep auto.
              cbn in Hmsg_type_match.
              destruct Hmsg_type_match as (Hmsg_type_match'&Hmsg_type_match).
              apply array_type_vallist_match_app. split. auto.
              rewrite <- firstn_skipn with (n:= Z.to_nat (Int.unsigned mlen)) in Hmsghold_type_match.
              apply array_type_vallist_match_app in Hmsghold_type_match.
              tauto.
            }
            - auto.
            - clear - Hqentries_range Hdstport_type_match Hdstport_V_Entries.
              unfold OS_Port_Seg_dls in Hdstport_type_match.
              struct_type_vallist_match'_elim.
              inverts Hdstport_V_Entries.
              rewrite Z.leb_le in Hqentries_range.
              rewrite Int_add_one_Sn' in Hqentries_range.
              rewrite int16_max_unsigned_val in Hqentries_range. lia.
              lia.
            - auto.
            - clear - HQport_msg_ptrs Hsize_range.
              apply Qport_msg_ptrs_P_hold; auto.
            - rewrite Int_add_one_Sn'. lia.
              clear - Hdstport_type_match Hdstport_V_Entries.
              unfold OS_Port_Seg_dls in Hdstport_type_match.
              struct_type_vallist_match'_elim.
              inverts Hdstport_V_Entries. lia.    
        }
        8: {eapply join_set_r; auto. eauto. unfold indom. eexists. eauto. }
        10:{ right. eexists. splits; eauto. }
        ** auto.
        ** congruence.
        ** qportpostproof_tac.
        ** port_nth_val_solve.
        ** rewrite app_length. simpl length. sep auto.
        ** eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls2; eauto.
        ** eapply RLH_Channel_upd_dportls2_Queue; eauto.
        ** eapply Channel_dstkport_Queue_OutcoreC_upd_dportls2_Queue; eauto.
        ** eapply RLH_OtherPortPtrList_upd_Queue; eauto.
  - (*核内通讯*)
    naive pure intro.
    rename v' into s.
    rename v'0 into er.
    rename v'1 into portptr.
    rename v'2 into msgptr.
    rename v'3 into msg.
    rename v'4 into mlen.
    rename v'5 into cheapl.
    rename v'6 into dstkportpl.
    rename v'7 into dstkportpl1.
    rename v'8 into dstkportp.
    rename v'9 into dstkportpl2.
    rename v'10 into headptr.
    rename v'11 into dportl.
    rename v'12 into dportmsgll.
    invertsr H9.
    clear Hmsg_ptr_hold_isptr Hport_ptr_hold_isptr.
    rename v'13 into dpptrl.
    rename v'14 into dportls.
    rename v'15 into dstportp.
    rename v'16 into ndstpptrn.
    rename v'17 into otherppl.
    rename v'18 into dportls1.
    rename v'19 into dportls2.
    rename v'20 into kportls.
    rename v'21 into chanls.
    rename v'22 into vsdstcl.
    rename v'23 into cheape.
    rename v'24 into cheapt.
    subst v'25.
    rename v'26 into pd.
    rename v'27 into pid.
    rename v'28 into pst.
    rename v'29 into dstpin.
    rename v'30 into dstpout.
    rename v'31 into dstsz.
    rename v'32 into dstpm.
    rename v'33 into ppcn.
    rename v'34 into ppid.
    rename v'35 into chanpl.
    rename v'36 into chanl.
    rename v'37 into chandstkportll.
    rename v'38 into kportpl.
    rename v'39 into kportl.
    rename v'40 into kportp.
    rename v'41 into chanptr.
    rename v'42 into kpst.
    rename v'43 into cid.
    rename v'44 into cdn.
    rename v'45 into dstkpst.
    rename v'46 into rtbl.
    rename v'47 into rgrp.
    rename v'48 into ecbls.
    rename v'49 into p1.
    rename v'50 into p2.
    rename v'51 into tcbl1.
    rename v'52 into tcbcur.
    rename v'53 into tcbl2.
    rename v'54 into tcbls.
    rename v'55 into vhold.
    rename v'56 into scapl.
    rename v'57 into mcapl.
    rename v'58 into qcapl.
    rename v'59 into ptls.
    rename v'60 into ptbl.
    rename v'61 into nextdst.
    rename v'62 into cportlptr.
    rename v'63 into cportpl.
    rename H into Hget_chanptr.
    rename H1 into Hget_dstportp.
    rename H2 into Hnerr_dpptrl.
    rename H3 into HRL_PortAttr.
    rename H4 into HRLH_Domainportl.
    rename H5 into HR_KernelPort_DomianPort.
    rename H6 into HChannel_dstkport_Queue_IncoreC.
    rename H7 into Hdstkportpl_split.
    unfold RLH_PortPtrINecb in H8.
    destruct H8 as (HRL_PortPtrList&Hinecb).
    subst logicl.
    rename H10 into Hgetheapmsg.
    rename H11 into H_mlen_le_CHANNEL_size.
    rename H12 into HSmlen.
    rename H13 into Hget_dstkportp.
    rename H14 into Hdportljoin.
    rename H15 into HRLH_Channel.
    rename H16 into HRLH_Kernel_Channel.
    rename H17 into Hmsg_type_match.
    rename H18 into Hget_kportp.
    rename H19 into Hkportls_nodup.
    rename H21 into HRH_TCBList_ECBList.
    rename H22 into HRH_CurTCB.
    
    assert (exists n dstport dstmsgl,
      nth_error dportl n = Some dstport /\
      nth_error dportmsgll n = Some dstmsgl /\
      nth_error dpptrl n = Some dstportp /\
      DomainportNode_P dstport (Z.to_nat DNUM, pd, pid, DestinationP nextdst, pst,
        dstpin, dstpout, QueuePort dstsz dstpm) dstmsgl).
    { eapply RLH_Domainportl_abs_getsome; eauto. }
    simpljoin1.
    assert (x=ndstpptrn).
    { eapply dpptrl_not_same_elements; eauto. }
    subst x. clear H1.
    rename x0 into dstport.
    rename x1 into dstportmsgl.
    rename H into Hnerr_dportl.
    rename H0 into Hnerr_dportmsgll.
    rename H2 into HDomainportNode.
    
    apply nth_error_split in Hnerr_dportl as (dportl1 & dportl2 & Hdportl_split & Hlen_dportl1_n).
    apply nth_error_split in Hnerr_dportmsgll as (dportmsgll1 & dportmsgll2 & Hdportmsgll_split & Hlen_dportmsgll1_n).
    apply nth_error_split in Hnerr_dpptrl as (dpptrl1 & dpptrl2 & Hdpptrl_split & Hlen_dpptrl1_n).
    subst dportl dpptrl dportmsgll. 

    hoare name lift dmportp_sllseg pre.
    eapply backward_rule1.
    { eapply dmportp_sllseg_app'_frm; eauto. 
      rewrite <- Hlen_dpptrl1_n. apply nth_error_middle.
    }
    cbn [dmportp_sllseg].
    naive pure intro.
    invertsr H.
    rename v' into nextport.
    rename v'1 into qstart.
    rename H1 into Hdstport_type_match.
    rename H0 into Hdstport_V_nextPort.
    rename H2 into Hdstport_V_Start.
    (* dmportp_sllseg_qport_msg *)
    hoare lift 2%nat pre.
    eapply backward_rule1.
    {
      eapply astar_mono.
      {
        intros.
        destruct H.
        2:{ apply H. }
        sep destruct H; sep split in H.
        unfold DomainportNode_P in HDomainportNode; simpljoin1.
        unfold Domainport_Portt_P in H3; simpljoin1.
        setoid_rewrite H5 in H0. discriminate.
      }
      eauto.
    }
    naive pure intro.
    rename v' into qend.
    rename v'0 into qin.
    rename v'1 into qout.
    rename v'2 into qsize.
    rename v'3 into qentries.
    rename H into Hdstport_V_mode.
    rename H0 into Hdstport_V_End.
    rename H1 into Hdstport_V_In.
    rename H2 into Hdstport_V_Out.
    simpljoin.
    rename H1 into Hdstport_V_Size.
    rename H2 into Hsize_range.
    rename H into Hdstport_V_Entries.
    rename H0 into Hentries_le_size.
    rename H5 into HQport_msg_ptrs.

    (* If (′ DNUM ==ₑ port_ptr ′ .. coreNum);ₛ *)
    eapply seq_rule.
    2:{ instantiate (1:=Afalse). apply pfalse_rule. }
    apply ift_nonzero_rule.
    intros.
    unfold DomainportNode_P in HDomainportNode.
    destruct HDomainportNode as (HDomainportNode&_&_).
    unfold Domainport_nat_P in HDomainportNode.
    simpljoin.
    exists (Int.one).
    sep split. 2: pauto.
    eapply symbolic_lemmas.bop_rv.
    symbolic_execution.
    eapply port_coreNum_rv''; eauto.
    sep autocancel; apply H.
    cbn. rewrite Int.eq_true. reflexivity.
    auto.
    reflexivity.
    unfold RH_CurTCB in HRH_CurTCB.
    destruct HRH_CurTCB as (curpri&st&curmsg&sus&HRH_CurTCB).
    assert (exists wt, get ecbls dstportp = Some (absport, wt)) as [wt Hget_ecbls_dstportp].
    {
      apply Forall_app in Hinecb as [? ?].
      inverts H0. auto.
    }

    unfold EvtInv at 2.
    naive pure intro.
    rename H0 into Hvhold_addr.
    rename H1 into HSEM_ECB_P.
    rename H2 into HMUX_ECB_P.
    rename H3 into HQ_ECB_P.
    rename H4 into Hevcre_nodup.
    rename H5 into Hevdel_nodup.
    rename H6 into Heibref_distinct.
    hoare name lift AECBList pre.
    rename v'1 into ectrl.
    rename v'5 into msgql.
    unfold AECBList.
    naive pure intro.
    rename v'1 into evheadptr.
    rename H0 into HECBList_P.
    
    assert (exists et etbl petbl, get_ectr (Vptr dstportp) evheadptr ectrl = Some (et,etbl, petbl)) as (et & etbl & petbl & Fget_ectr).
  { eapply ECBList_P_get_ectr_some in HECBList_P; try eauto. }
  hoare name lift evsllseg pre.
  eapply backward_rule1.
  { intros ? Hs. eapply get_ectr_decompose in Hs;eauto. }
  naive pure intro.
  rename v'1 into et_next.
  rename v'5 into ectrl1.
  rename v'22 into portmsgq.
  rename v'20 into msgql1.
  rename v'19 into ectrl2.
  rename v'21 into msgql2.
  destruct H0 as (Hetnext & ? &  ? & Hgetectr1 & Hgetectr2 & Hevheadptr_notnull & Hnexptr ). 
  subst ectrl msgql.
  hoare_assert_pure (exists portgrp, V_OSEventGrp et = Some (Vint32 portgrp) /\ struct_type_vallist_match OS_EVENT et ).
  {
    clear - H0.
    unfold AEventNode in H0.
    unfold AOSEvent in H0.
    sep normal in H0. sep destruct H0. 
    unfold node in H0. sep normal in H0.  sep destruct H0.
    sep split in H0. destruct H. clear - H14 H0.
    struct_type_vallist_match_elim.
    eexists. split. reflexivity. pauto.
  }
  naive pure intro.
  rename v'1 into evgrp.
  destruct H0.
  rename H0 into Het_V_EventGrp.
  rename H1 into Het_type_match.
  eapply seq_rule.
  (* If (port_ptr ′ .. OSEventGrp !=ₑ ′ 0)
  {OS_PortTaskRdy (­port_ptr ′, msg_ptr ′, ′ OS_STAT_PORT­);ₛ *)
  {
    eapply ift_rule'.
    {
      intros. unfold AEventNode in H0.
      unfold AOSEvent in H0.
      sep normal in H0. sep destruct H0. 
      unfold node in H0. sep normal in H0.  sep destruct H0.
      sep split in H0. destruct H1. inverts H1.
      eapply symbolic_lemmas.uop_rv.
      eapply symbolic_lemmas.bop_rv.
      sep name lift A_dom_lenv in H0.
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
      clear - H15. struct_type_vallist_match_elim. simpl. lia.
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
      reflexivity.
      pauto.
      reflexivity.      
    }
    instantiate (1:=Afalse).
    naive pure intro.
    simpljoin.
    clear H1 H2.
    destruct ( Int.eq evgrp ($ 0)) eqn: E.
    simpl in H0. unfold Int.notbool in H0.
    rewrite Int.eq_false in H0. congruence.
    pauto.
    clear H0. rename H into HR_Q_Data_P.
    rename E into Hevgrp_neq_zero.
    apply sem_lab.semacc_int_eq_false in Hevgrp_neq_zero.
    hoare_assert_pure (length ectrl1 = length msgql1).
    { sep name lift evsllseg in H.
    eapply evsllseg_list_len_eq;eauto. }
    naive pure intro.
    rename H into Hlen_ectrl1_msgql1. 
    eapply ecblist_p_decompose_new in HECBList_P as ?;eauto.
    destruct H as (ecbls1&ecblsc2&HECBList_P_ecbls1&HECBList_P_ecblsc2&Hjoin_ecbls&Hget_last_ptr).
    simpl app in HECBList_P_ecblsc2.
    cbn [ECBList_P] in HECBList_P_ecblsc2.
    destruct HECBList_P_ecblsc2 as (?&Htmp&HR_ECB_Etbl_P&HR_ECB_PETbl_P&HECBList_P_ecbls2).
    invertsr Htmp.
    simpljoin.
    setoid_rewrite Hetnext in H. invertsr H.
    rename x into dstporth.
    rename x0 into ecbls2.
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
    hoare_assert_pure (ptr_in_tcblist p2 p1 (tcbl1++tcbcur::tcbl2)). 
    {
      eapply OSQPostPure.tcbdllseg_combine_ptr_in_tcblist; eauto. 
    }
    naive pure intro.
    rename H3 into Hptr_in_tcblist.
    hoare_assert_pure (OSQPostPure.get_last_tcb_ptr tcbl1 p1 = Some p2 ).
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
    rename v'20 into tcbls1.
    rename v'21 into tcblsc2.
    rename H0 into Hjoin_tcbls.
    rename H1 into HTCBList_P_tcbls1.
    rename H2 into HTCBList_P_tcblsc2.
    destruct H. subst p2.
    lets HTCBListP_tcbls: OSQPostPure.TCBList_P_Combine Hget_last_tcb_ptr Hjoin_tcbls HTCBList_P_tcbls1 HTCBList_P_tcblsc2.

    rename H into Hp1_notnull.
    hoare_assert_pure (portmsgq = DPort /\ dstporth = (absport,wt) /\  V_OSEventType et = Some (V$ OS_EVENT_TYPE_PORT)).
    {
      sep name lift AEventNode in H.
      eapply join_sig_get in HTcbJoin_ecbls2; eauto.
      eapply EcbMod.join_get_get_r in Hjoin_ecbls; eauto.
      unfold get, EcbMap in Hget_ecbls_dstportp.
      rewrite Hget_ecbls_dstportp in Hjoin_ecbls.
      inverts Hjoin_ecbls.
      unfold RLH_ECBData_P in HRLH_ECBData_P.
      destruct portmsgq; tryfalse.
      splits; auto.
      unfold AEventNode in H.
      unfold AEventData in H.
      sep normal in H. sep split in H.
      auto.
    }
    naive pure intro.
    simpljoin.
    rename H1 into Het_V_EventType.
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

    (* OS_PortTaskRdy (­port_ptr ′, msg_ptr ′,
     ′ OS_STAT_PORT­);ₛ *)
    eapply seq_rule.
    {
      eapply call_rule'.
      - reflexivity.
      - intros.
        eapply rvl_elim.
        symbolic_execution.
        eapply rvl_elim.
        symbolic_execution.
        eapply rvl_elim.
      
        eapply cast_rv_tint32_tint16.
        symbolic_execution.
        simpl.
        assert ((Int.modu ($ OS_STAT_PORT) ($ Int16.modulus))= $ OS_STAT_PORT) by reflexivity.
        rewrite H0. reflexivity.
        apply rvl_nil.
      - intros. unfold getasrt. unfold OS_PortTaskRdyPre.
        unfold OS_PortTaskRdyPre'.
        sep normal. sep eexists.
        sep cancel AEventNode.
        sep cancel tcbdllseg.
        sep autocancel.
        sep split.
        2-24: auto.
        sep name lift dmportp_sllseg_qport_msg in H.
        sep cancel 1%nat 1%nat.
        sep cancel dmportp_sllseg_qport_msg.
        apply H.
        all: eauto.
      - go.
      - sep_unfold_funpost. intros. sep destruct H. sep auto.
      - sep_unfold_funpre. intros. sep destruct H. sep auto.
      - reflexivity.
    }

    (* Deal with funpost*)
    unfold getasrt; unfold OS_PortTaskRdyPost, OS_PortTaskRdyPost'.
    naive pure intro.
    do 8 (hoare lifts (16::nil)%nat pre;
    apply pure_split_rule'; intros).
    hoare lifts (17::nil)%nat pre;
    apply pure_split_rule'; intros.
    invertsr H20.
    invertsr H27.
    clear H28 H25 H26 H22 H24. 
    rename H23 into HRL_RTbl_PrioTbl_P'.
    rename H21 into Hptr_in_tcblist'.
    rename H18 into HRL_Tbl_Grp_P'.
    clear H19.
    destruct H15.
    rename H18 into Hide_prio_in_tbl.
    rename H15 into HRL_Tbl_Grp_P.
    rename H17 into Hrgrp_type_match.
    destruct H16.
    rename H16 into Hlen_rtbl_edy_tbl_size.
    rename H15 into Hrtbl_type_match.
    clear v'20 H14. (*return val*)
    rename v'33 into etbl'.
    rename v'37 into et'. subst v'62. subst v'63.
    rename v'24 into tcbl'.
    rename v'27 into rtbl'.
    rename v'58 into y.
    rename v'59 into i1.
    rename v'57 into x.
    rename v'61 into bity.
    rename v'60 into bitx.
    rename v'69 into stat.
    rename v'64 into next.
    rename v'65 into prev.
    rename v'70 into prio.
    rename v'71 into tcbx.
    rename v'72 into tcby.
    rename v'73 into tcbbitx.
    rename v'74 into tcbbity.
    rename v'75 into t.
    rename v'76 into i1'.
    rename H0 into Heq_rtbl'.
    rename H3 into Heq_tcbl'.
    rename H12 into Heq_et'.
    rename H13 into Heq_etbl'.
    destruct H1.
    rename H into Hnval_rtbl_i1'.
    rename H0 into Hnval_ptbl_t.
    rename H1 into Ht_vhold_addr_neq.
    destruct H2.
    rename H into Htcblist_get_t.
    rename H0 into Ht_OSTCB_flag_type_match.
    rename H6 into Hrel_edata_tcbstat.
    rename H7 into Hnval_OSUnMapVallist_y.
    rename H8 into Hnval_etbl_i1.
    rename H9 into Hnval_OSUnMapVallist_x.
    rename H10 into Hnval_OSMapVallist_bity.
    rename H11 into Hnval_OSMapVallist_bitx.

    (* wt <> nil*)
    lets Hget_tcbls_t: tcblist_get_TCBList_P_get_tcbls Htcblist_get_t HTCBListP_tcbls.
    destruct Hget_tcbls_t as (prio_t& st_t& m_t& sus_t&Hget_tcbls_t).
    apply get_join in Hget_tcbls_t as Hjoin_tcbls_t.
    destruct Hjoin_tcbls_t as (tcbls_t&Hjoin_tcbls_t).
    assert (TcbJoin (t,Int.zero)  (prio_t, st_t, m_t, sus_t) tcbls_t tcbls) by tauto.
    clear Hjoin_tcbls_t.
    rename H into Hjoin_tcbls_t.
    lets Htmp: port_exwt_succ_pre Hevgrp_neq_zero HR_PrioTbl_P HRL_Tbl_Grp_P' Het_type_match
    Het_V_EventType Het_V_EventGrp. 
    lets Htmpp: Htmp HR_ECB_Etbl_P HRH_TCBList_ECBList Hjoin_ecbls HTcbJoin_ecbls2
    Hetbl_type_match Hlen_etbl_EVENT_TBL_SIZE.
    clear Htmp.
    lets Htmp: Htmpp Hnval_OSUnMapVallist_y Hnval_etbl_i1 Hnval_OSUnMapVallist_x Hnval_ptbl_t Hjoin_tcbls_t.
    clear Htmpp.
    destruct Htmp as (Hwt_nnil&HGetHwait_t&_&Hprio_t_xy).
    
    assert (Int.unsigned y <= 7) as y_le7.
    clear - Het_type_match Hnval_OSUnMapVallist_y Het_V_EventGrp.
    struct_type_vallist_match_elim.
    inverts Het_V_EventGrp.
    lets Hx: osunmapvallist_prop H0; simpljoin.
    rewrite Hnval_OSUnMapVallist_y in H5; inverts H5.
    apply Z.leb_le in H6; auto.


    assert (Int.unsigned i1 <= 255) as i1_le255.
    clear - Hetbl_type_match Hnval_etbl_i1 Hlen_etbl_EVENT_TBL_SIZE  y_le7.
    assert (Z.to_nat (Int.unsigned y) < length etbl)%nat.
    rewrite Hlen_etbl_EVENT_TBL_SIZE; unfold OS_EVENT_TBL_SIZE.
    lia.
    lets Hx: array_int8u_nth_lt_len Hetbl_type_match H; simpljoin.
    rewrite Hnval_etbl_i1 in H0; invert H0; auto.
  
    assert(Int.unsigned x <= 7) as x_le7.
    clear - Hnval_OSUnMapVallist_x i1_le255.
    lets Hx: osunmapvallist_prop i1_le255; simpljoin.
    rewrite Hnval_OSUnMapVallist_x in H; inverts H.
    apply Z.leb_le in H0; auto.
    assert(($ Int.unsigned ((y<<ᵢ$ 3) +ᵢ  x) >>ᵢ $ 3) = y) as xx1.
    clear - y_le7 x_le7.
    mauto.
    rewrite Int.repr_unsigned in xx1.
    assert(($ Int.unsigned ((y<<ᵢ$ 3) +ᵢ  x)&ᵢ$ 7) = x) as xx2.
    clear - y_le7 x_le7.
    mauto.
    rewrite Int.repr_unsigned in xx2.

    assert (Int.unsigned i1' <= 255) as i1'_le255.
    clear - Hrtbl_type_match Hnval_rtbl_i1' Hlen_rtbl_edy_tbl_size  y_le7.
    assert (Z.to_nat (Int.unsigned y) < length rtbl)%nat.
    rewrite Hlen_rtbl_edy_tbl_size; unfold OS_RDY_TBL_SIZE.
    unfold Coqlib.nat_of_Z.
    lia.
    lets Hx: array_int8u_nth_lt_len Hrtbl_type_match H; simpljoin.
    rewrite Hnval_rtbl_i1' in H0; invert H0; auto.

    lets HTCBNode: tcblist_get_TCBNode_P Hget_tcbls_t Htcblist_get_t HTCBListP_tcbls.

    lets Htmp: rh_tcblist_ecblist_p_post_exwt_aux_port HRH_TCBList_ECBList Hjoin_ecbls
    HTcbJoin_ecbls2 Hget_tcbls_t.
    eapply GetHWait_in_wt; eauto.
    destruct Htmp as (t_time&Htmp).
    subst st_t.
    
    hoare name lift Adisj pre.
  
    eapply backward_rule1.
    {
      intros. apply disj_split in H.
      eauto.
    }
    
    apply disj_rule.
    - hoare normal pre.
      hoare abs lift pre.
      eapply abscsq_rule.
      apply noabs_oslinv.
      apply absinfer_choice1'. go.
      apply absinfer_eq.
      
      destruct sus_t.
      {
        hoare name lift abstcblist absecblist osdomainport oskport oschannel pre.
        hoare abs lift pre.
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply qportpost_send_one_InCore_porttskrdy_abt. go.
        8: eauto.
        8: apply absinfer_eq.
        5-8: eauto.
        4: eauto.
        1,2: eauto.
        rewrite app_length. simpl length.
        assert (length dstkportpl1 + S (length dstkportpl2) - S (length dstkportpl2) = length dstkportpl1)%nat by lia.
        rewrite H. apply nth_error_middle.
        apply absabort_rule.
      }

      hoare name lift abstcblist absecblist osdomainport oskport oschannel pre.
      hoare abs lift pre.
      
      (* qportpost_send_one_Incore_porttskrdy (S (length dstkportpl2))
      (|Vptr portptr
        :: Vptr msgptr
           :: V$ Z.of_nat (length (dstkportpl1 ++ dstkportp :: dstkportpl2))
              :: Vnull :: vsdstcl|) *)
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply qportpost_send_one_InCore_porttskrdy_cont. go.
      3: {
        rewrite app_length. simpl length. 
        assert (length dstkportpl1 + S (length dstkportpl2) - S (length dstkportpl2) = length dstkportpl1)%nat by lia.
        rewrite H. apply nth_error_middle.
      }
      4: eauto.
      4-6: eauto.
      4: apply absinfer_eq.
      1-3: eauto.
      hoare_assert_pure (stat = $OS_STAT_PORT).
      {
        unfold TCBNode_P in HTCBNode.
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
      naive pure intro. subst stat.
      rewrite statport_and_not_statport_eq_rdy in Heq_rtbl'.

      eapply backward_rule1.
      {
        intros. sep name lift tcbdllseg in H.
        rewrite  Heq_tcbl' in H.
        eapply set_node_elim with (tid:=ct)(tcbls:=tcbls)(prio:=prio_t)
        (st:=wait (os_stat_port dstportp) t_time)(m:=m_t)(sus:=false)(rtbl:=rtbl)(rtbl':=rtbl')(st':=rdy)
        (m':=Vptr OS_PARTITION_MESSAGE_COME_ptr)(sus':=false) in H.
        eauto. 
        2: eauto.
        2: auto.
        2: apply Hget_tcbls_t.
        5: { cbv. auto. }
        4:{
          unfold R_PrioTbl_P in HR_PrioTbl_P.
          clear - HR_PrioTbl_P. tauto.
        }
        {
          rewrite ptr_in_tcbdllseg_ptr_in_tcbdllseg1.
          eapply ptr_in_tcbdllseg1_set_node.
          rewrite <- tcblist_get_tcbdllseg1_get_node.
          apply Htcblist_get_t.
          cbv. auto.
          rewrite <- ptr_in_tcbdllseg_ptr_in_tcbdllseg1.
          apply Hptr_in_tcblist.
        }
        {
          pose proof statport_and_not_statport_eq_rdy.
          apply Int_eq_dec in H0.
          rewrite H0.
          rewrite Heq_rtbl'.
          subst prio_t.
          eapply TCBNode_P_set_rdy; eauto.
          2:{
            rewrite xx1. clear - Hnval_rtbl_i1'. 
            apply OSQPostPure.nth_val'2nth_val. auto.
          }
          {
            clear - x_le7 y_le7.
            mauto. 
          }
          {
             rewrite xx2.
             eapply math_mapval_core_prop; eauto.
             lia.
          }
        }
        {
          (*rtbl_set_one_bit*)
          rewrite Heq_rtbl'.
          unfolds. subst prio_t.
          do 2 eexists. splits; eauto.
          clear - x_le7 y_le7. mauto.
          rewrite xx1. eauto.
          rewrite xx2. eauto.
          rewrite xx1. reflexivity.
        }
      }
      naive pure intro.
      rename v'20 into tcbl1'.
      rename v'21 into tcbl2'.
      rename v'22 into tcbcur'.
      rename H into Htcbl'_split_t.
      rename v'24 into tcbls1'.
      rename v'25 into tcblsc2'.
      rename H0 into Htcbls'_split_t.
      rename H1 into HTCBList_P_tcbls1'.
      rename H2 into HTCBList_P_tcblsc2'.
  
      (*  RETURN ′ OS_NO_ERR *)
      
      eapply rete_rule'.
      intros. symbolic_execution.
      intros. sep normal. sep eexists. 
      sep name lift Adisj.
      apply disj_split.
      right.
      sep normal.
      sep eexists.
      sep cancel Aop.
      sep cancel osdomainport.
      sep cancel oskport.
      sep cancel oschannel.
      sep cancel oscoreheap.
      sep cancel p_local.
      sep cancel A_dom_lenv.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Aisr.
      sep cancel Aier.
      sep cancel A_isr_is_prop.
      sep cancel Acs.
      sep cancel port_ptr.
      sep cancel msg_ptr.
      sep cancel AOSRdyTblGrp.
      sep cancel curtid.
      sep cancel AOSMapTbl.
      sep cancel AOSUnMapTbl.
      unfold AOSTCBPrioTbl.
      sep normal.
      sep eexists.
      sep cancel OSTCBPrioTbl.
      sep cancel OSPlaceHolder.
      sep cancel absptlsid.

      (*  AOSTCBList *)
      sep name lift AOSTCBList.
      unfold AOSTCBList. sep normal.
      sep eexists.
      sep cancel OSTCBList.
      sep cancel OSTCBCur.
      sep cancel 1%nat 1%nat.
      sep cancel 1%nat 1%nat.
      sep cancel abstcblist.
      sep name lift TCBList_P.
      apply astar_l_apure_intro.
      2: apply HTCBList_P_tcbls1'.
      sep name lift TCBList_P.
      apply astar_l_apure_intro.
      2: apply HTCBList_P_tcblsc2'.
      apply astar_l_apure_intro.
      2: jauto.
      apply astar_l_apure_intro.
      2: auto.
      
      (* EvtInv *)
      sep name lift EvtInv.
      unfold EvtInv.
      unfold AECBList.
      sep normal. sep eexists.
      sep cancel OSEventList.
      eapply evsllseg_compose with (l:=et'); eauto.
      rewrite Heq_et'.
      unfold V_OSEventListPtr.
      apply nth_upd_neqrev. lia. 
      apply Hetnext.
      sep cancel AEventNode.
      sep cancel (evsllseg evheadptr).
      sep cancel (evsllseg et_next).
      sep cancel absecblist.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
      sep cancel AErrblkList.
      sep cancel APosblkList.
      sep cancel AEvStructHeap.
      sep cancel AEvArrayHeap.
      sep cancel AEvAtomHeap.
      sep name lift ASemEIBs.
      eapply ASemEIBs_port_set_ecbls_preserve; eauto.
      sep cancel ASemEIBs.
      sep name lift AMuxEIBs.
      eapply AMuxEIBs_port_set_ecbls_preserve; eauto.
      sep cancel AMuxEIBs.
      sep name lift AMqEIBs.
      eapply AMqEIBs_port_set_ecbls_preserve; eauto.
      sep cancel AMqEIBs.
      sep cancel eblsid.
      sep cancel pblsid.
      sep cancel evatomheapid.
      sep cancel evstructheapid.
      sep cancel evarrayheapid.
      sep cancel seminfoid.
      sep cancel absmutinfoid.
      sep cancel absmqattrid.
      sep name lift SEM_ECB_P.
      apply astar_l_apure_intro.
      2:eapply sem_ecb_p_mutex_set_preserve; eauto.
      sep name lift MUX_ECB_P.
      apply astar_l_apure_intro.
      2:eapply mux_ecb_p_port_set_preserve; eauto.
      sep name lift Q_ECB_P.
      apply astar_l_apure_intro.
      2:eapply mq_ecb_p_sem_set_ecbls_port_preserve; eauto.
      sep name lift R_Q_Data_P.
      apply astar_l_apure_intro;auto.
      sep name lift vhold_addr;
      apply astar_l_apure_intro;auto.
      sep name lift evcre_nodup;
      apply astar_l_apure_intro;auto.
      sep name lift evdel_nodup;
      apply astar_l_apure_intro;auto.
      sep name lift eibref_distinct;
      apply astar_l_apure_intro;auto.
      sep cancel vhold_addr.
      sep cancel evlocid.
      sep cancel evptrid.
      sep name lift RH_TCBList_ECBList_P.
      apply astar_l_apure_intro.
      2:{
        eapply rh_tcblist_ecblist_p_post_exwt_port; eauto.
        eapply GetHWait_in_wt; eauto.
      }
      sep name lift RH_PrioTbl_P.
      apply astar_l_apure_intro.
      2: eauto.
      sep name lift array_type_vallist_match.
      apply astar_l_apure_intro.
      2: eauto.
      sep name lift RL_RTbl_PrioTbl_P.
      apply astar_l_apure_intro.
      2: eauto.
      sep name lift R_PrioTbl_P.
      apply astar_l_apure_intro.
      2:{
          eapply OSQPostPure.r_priotbl_p_set_hold; eauto.
      }
      sep name lift RH_CurTCB.
      apply astar_l_apure_intro.
      2: {
        unfold RH_CurTCB.
        assert(ct = (t, Int.zero) \/ ct <> (t, Int.zero)) by tauto.
        destruct H0; auto. subst.
        do 4 eexists.
        rewrite TcbMod.set_a_get_a.
        eauto.
        apply tidspec.eq_beq_true; auto.
        eapply OSQPostPure.rh_curtcb_set_nct; auto.
        unfold RH_CurTCB.
        do 4 eexists. eauto.
      }
      apply astar_l_apure_intro.
      2:{
        rewrite Heq_etbl'.
        eapply ecblist_p_post_exwt_hold_port; eauto.
        lets Htmp: osmapvallist_prop x_le7.
        destruct Htmp as (?&?&?).
        rewrite Hnval_OSMapVallist_bitx in H0; inverts H0.
        auto.
      }
      sep name lift tcbllsegevaux.
      sep name lift tcbllsegevaux in H.
      eapply tcbllsegevaux_tcbvl_tcb_linked_list_same_next_preserve;eauto.
      sep cancel tcbllsegevaux.
      2:{
        rewrite <- Htcbl'_split_t.
        eapply tcb_linked_list_same_next_set_node; eauto.
        unfold same_prev_next. simpl. auto.
      }
      sep name lift tcbdllflag.
      sep name lift tcbdllflag in H.
      eapply tcbdllflag_hold with (l1:=tcbl1++tcbcur::tcbl2); eauto.
      rewrite <- Htcbl'_split_t.
      eapply set_node_eq_dllflag; eauto.
      sep cancel tcbdllflag.
      
      sep name lift CoreCommuInv.
      eapply CoreCommuInv_set_notsemq_frm.
      introv. intros.
      unfold is_sem in H0.
      simpljoin1.
      setoid_rewrite Hget_ecbls_dstportp in H0. inverts H0.
      introv. intros.
      unfold is_que in H0.
      simpljoin1.
      setoid_rewrite Hget_ecbls_dstportp in H0. inverts H0.
      sep cancel CoreCommuInv.
      sep cancel Aarray.
      sep cancel AOSCorePortPtrList.
      sep name lift dmportp_sllseg.
      eapply dmportp_sllseg_compose; eauto.
      2:{
        sep cancel (dmportp_sllseg nextport).
        sep cancel dmportp_sllseg.
        sep cancel APortStruct.
        apply disj_split.
        right.
        sep normal. sep eexists.
        sep name lift dmportp_sllseg_qport_msg.
        sep cancel 1%nat 1%nat.
        sep name lift dmportp_sllseg_qport_msg.
        sep cancel 1%nat 1%nat. 
        sep split; auto. reflexivity.
        unfold RLH_PortPtrINecb.
        split; auto.
        rewrite Forall_forall.
        intros.
        rewrite Forall_forall in Hinecb.
        apply Hinecb in H0.
        simpljoin1.
        destruct (addrval_eq_dec x0 dstportp).
        subst. eexists.
        apply EcbMod.set_a_get_a.
        apply TcbMod.beq_refl.
        eexists.
        rewrite EcbMod.set_a_get_a'; eauto.
        apply tidspec.neq_beq_false.
        congruence.
      }
      congruence.
    - naive pure intro.
      rename v'20 into irheapmsg'.
      rename H into HSqentries.
      hoare abs lift pre.
      eapply abscsq_rule.
      apply noabs_oslinv.
      apply absinfer_choice2'. go.
      apply absinfer_eq.
      eapply abscsq_rule.
      apply noabs_oslinv.
      apply absinfer_choice1'. go.
      apply absinfer_eq.
      
      destruct sus_t.
      {
        hoare name lift abstcblist absecblist osdomainport oskport oschannel pre.
        hoare abs lift pre.
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply qportpost_send_one_InCore_porttskrdy_abt. go.
        8: eauto.
        8: apply absinfer_eq.
        5-8: eauto.
        4: eauto.
        1,2: eauto.
        rewrite app_length. simpl length.
        assert (length dstkportpl1 + S (length dstkportpl2) - S (length dstkportpl2) = length dstkportpl1)%nat by lia.
        rewrite H. apply nth_error_middle.
        apply absabort_rule.
      }

      hoare name lift abstcblist absecblist osdomainport oskport oschannel pre.
      hoare abs lift pre.
      
      (* qportpost_send_one_Incore_porttskrdy (S (length dstkportpl2))
      (|Vptr portptr
        :: Vptr msgptr
          :: V$ Z.of_nat (length (dstkportpl1 ++ dstkportp :: dstkportpl2))
              :: Vnull :: vsdstcl|) *)
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply qportpost_send_one_InCore_porttskrdy_cont. go.
      3: {
        rewrite app_length. simpl length. 
        assert (length dstkportpl1 + S (length dstkportpl2) - S (length dstkportpl2) = length dstkportpl1)%nat by lia.
        rewrite H. apply nth_error_middle.
      }
      4: eauto.
      4-6: eauto.
      4: apply absinfer_eq.
      1-3: eauto.
      hoare_assert_pure (stat = $OS_STAT_PORT).
      {
        unfold TCBNode_P in HTCBNode.
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
      naive pure intro. subst stat.
      rewrite statport_and_not_statport_eq_rdy in Heq_rtbl'.

      eapply backward_rule1.
      {
        intros. sep name lift tcbdllseg in H.
        rewrite  Heq_tcbl' in H.
        eapply set_node_elim with (tid:=ct)(tcbls:=tcbls)(prio:=prio_t)
        (st:=wait (os_stat_port dstportp) t_time)(m:=m_t)(sus:=false)(rtbl:=rtbl)(rtbl':=rtbl')(st':=rdy)
        (m':=Vptr OS_PARTITION_MESSAGE_COME_ptr)(sus':=false) in H.
        eauto. 
        2: eauto.
        2: auto.
        2: apply Hget_tcbls_t.
        5: { cbv. auto. }
        4:{
          unfold R_PrioTbl_P in HR_PrioTbl_P.
          clear - HR_PrioTbl_P. tauto.
        }
        {
          rewrite ptr_in_tcbdllseg_ptr_in_tcbdllseg1.
          eapply ptr_in_tcbdllseg1_set_node.
          rewrite <- tcblist_get_tcbdllseg1_get_node.
          apply Htcblist_get_t.
          cbv. auto.
          rewrite <- ptr_in_tcbdllseg_ptr_in_tcbdllseg1.
          apply Hptr_in_tcblist.
        }
        {
          pose proof statport_and_not_statport_eq_rdy.
          apply Int_eq_dec in H0.
          rewrite H0.
          rewrite Heq_rtbl'.
          subst prio_t.
          eapply TCBNode_P_set_rdy; eauto.
          2:{
            rewrite xx1. clear - Hnval_rtbl_i1'. 
            apply OSQPostPure.nth_val'2nth_val. auto.
          }
          {
            clear - x_le7 y_le7.
            mauto. 
          }
          {
            rewrite xx2.
            eapply math_mapval_core_prop; eauto.
            lia.
          }
        }
        {
          (*rtbl_set_one_bit*)
          rewrite Heq_rtbl'.
          unfolds. subst prio_t.
          do 2 eexists. splits; eauto.
          clear - x_le7 y_le7. mauto.
          rewrite xx1. eauto.
          rewrite xx2. eauto.
          rewrite xx1. reflexivity.
        }
      }
      naive pure intro.
      rename v'20 into tcbl1'.
      rename v'21 into tcbl2'.
      rename v'22 into tcbcur'.
      rename H into Htcbl'_split_t.
      rename v'24 into tcbls1'.
      rename v'25 into tcblsc2'.
      rename H0 into Htcbls'_split_t.
      rename H1 into HTCBList_P_tcbls1'.
      rename H2 into HTCBList_P_tcblsc2'.

      hoare name lift osdomainport oskport oschannel oscoreheap pre.
      hoare abs lift pre. 
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply qportpost_send_one_InCore_cont. go.
      1,2: eauto.
      3:{
        rewrite app_length.
        simpl length.
        assert (length dstkportpl1 + S (length dstkportpl2) - S (length dstkportpl2) = length dstkportpl1)%nat by lia.
        rewrite H. apply nth_error_middle.
      }
      3: eauto.
      4: apply absinfer_eq.
      3:{
        eapply join_get_l; eauto.
      }
      rewrite <- HSmlen.
      eauto.
      auto.
      (*  RETURN ′ OS_NO_ERR *)
      
      eapply rete_rule'.
      intros. symbolic_execution.
      intros. sep normal. sep eexists. 
      sep name lift Adisj.
      apply disj_split.
      right.
      sep normal.
      sep eexists.
      sep cancel Aop.
      sep cancel osdomainport.
      sep cancel oskport.
      sep cancel oschannel.
      sep cancel oscoreheap.
      sep cancel p_local.
      sep cancel A_dom_lenv.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Aisr.
      sep cancel Aier.
      sep cancel A_isr_is_prop.
      sep cancel Acs.
      sep cancel port_ptr.
      sep cancel msg_ptr.
      sep cancel AOSRdyTblGrp.
      sep cancel curtid.
      sep cancel AOSMapTbl.
      sep cancel AOSUnMapTbl.
      unfold AOSTCBPrioTbl.
      sep normal.
      sep eexists.
      sep cancel OSTCBPrioTbl.
      sep cancel OSPlaceHolder.
      sep cancel absptlsid.

      (*  AOSTCBList *)
      sep name lift AOSTCBList.
      unfold AOSTCBList. sep normal.
      sep eexists.
      sep cancel OSTCBList.
      sep cancel OSTCBCur.
      sep cancel 1%nat 1%nat.
      sep cancel 1%nat 1%nat.
      sep cancel abstcblist.
      sep name lift TCBList_P.
      apply astar_l_apure_intro.
      2: apply HTCBList_P_tcbls1'.
      sep name lift TCBList_P.
      apply astar_l_apure_intro.
      2: apply HTCBList_P_tcblsc2'.
      apply astar_l_apure_intro.
      2: jauto.
      apply astar_l_apure_intro.
      2: auto.
      
      (* EvtInv *)
      sep name lift EvtInv.
      unfold EvtInv.
      unfold AECBList.
      sep normal. sep eexists.
      sep cancel OSEventList.
      eapply evsllseg_compose with (l:=et'); eauto.
      rewrite Heq_et'.
      unfold V_OSEventListPtr.
      apply nth_upd_neqrev. lia. 
      apply Hetnext.
      sep cancel AEventNode.
      sep cancel (evsllseg evheadptr).
      sep cancel (evsllseg et_next).
      sep cancel absecblist.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
      sep cancel AErrblkList.
      sep cancel APosblkList.
      sep cancel AEvStructHeap.
      sep cancel AEvArrayHeap.
      sep cancel AEvAtomHeap.
      sep name lift ASemEIBs.
      eapply ASemEIBs_port_set_ecbls_preserve; eauto.
      sep cancel ASemEIBs.
      sep name lift AMuxEIBs.
      eapply AMuxEIBs_port_set_ecbls_preserve; eauto.
      sep cancel AMuxEIBs.
      sep name lift AMqEIBs.
      eapply AMqEIBs_port_set_ecbls_preserve; eauto.
      sep cancel AMqEIBs.
      sep cancel eblsid.
      sep cancel pblsid.
      sep cancel evatomheapid.
      sep cancel evstructheapid.
      sep cancel evarrayheapid.
      sep cancel seminfoid.
      sep cancel absmutinfoid.
      sep cancel absmqattrid.
      sep name lift SEM_ECB_P.
      apply astar_l_apure_intro.
      2:eapply sem_ecb_p_mutex_set_preserve; eauto.
      sep name lift MUX_ECB_P.
      apply astar_l_apure_intro.
      2:eapply mux_ecb_p_port_set_preserve; eauto.
      sep name lift Q_ECB_P.
      apply astar_l_apure_intro.
      2:eapply mq_ecb_p_sem_set_ecbls_port_preserve; eauto.
      sep name lift R_Q_Data_P.
      apply astar_l_apure_intro;auto.
      sep name lift vhold_addr;
      apply astar_l_apure_intro;auto.
      sep name lift evcre_nodup;
      apply astar_l_apure_intro;auto.
      sep name lift evdel_nodup;
      apply astar_l_apure_intro;auto.
      sep name lift eibref_distinct;
      apply astar_l_apure_intro;auto.
      sep cancel vhold_addr.
      sep cancel evlocid.
      sep cancel evptrid.
      sep name lift RH_TCBList_ECBList_P.
      apply astar_l_apure_intro.
      2:{
        eapply rh_tcblist_ecblist_p_post_exwt_port; eauto.
        eapply GetHWait_in_wt; eauto.
      }
      sep name lift RH_PrioTbl_P.
      apply astar_l_apure_intro.
      2: eauto.
      sep name lift array_type_vallist_match.
      apply astar_l_apure_intro.
      2: eauto.
      sep name lift RL_RTbl_PrioTbl_P.
      apply astar_l_apure_intro.
      2: eauto.
      sep name lift R_PrioTbl_P.
      apply astar_l_apure_intro.
      2:{
          eapply OSQPostPure.r_priotbl_p_set_hold; eauto.
      }
      sep name lift RH_CurTCB.
      apply astar_l_apure_intro.
      2: {
        unfold RH_CurTCB.
        assert(ct = (t, Int.zero) \/ ct <> (t, Int.zero)) by tauto.
        destruct H0; auto. subst.
        do 4 eexists.
        rewrite TcbMod.set_a_get_a.
        eauto.
        apply tidspec.eq_beq_true; auto.
        eapply OSQPostPure.rh_curtcb_set_nct; auto.
        unfold RH_CurTCB.
        do 4 eexists. eauto.
      }
      apply astar_l_apure_intro.
      2:{
        rewrite Heq_etbl'.
        eapply ecblist_p_post_exwt_hold_port; eauto.
        lets Htmp: osmapvallist_prop x_le7.
        destruct Htmp as (?&?&?).
        rewrite Hnval_OSMapVallist_bitx in H0; inverts H0.
        auto.
      }
      sep name lift tcbllsegevaux.
      sep name lift tcbllsegevaux in H.
      eapply tcbllsegevaux_tcbvl_tcb_linked_list_same_next_preserve;eauto.
      sep cancel tcbllsegevaux.
      2:{
        rewrite <- Htcbl'_split_t.
        eapply tcb_linked_list_same_next_set_node; eauto.
        unfold same_prev_next. simpl. auto.
      }
      sep name lift tcbdllflag.
      sep name lift tcbdllflag in H.
      eapply tcbdllflag_hold with (l1:=tcbl1++tcbcur::tcbl2); eauto.
      rewrite <- Htcbl'_split_t.
      eapply set_node_eq_dllflag; eauto.
      sep cancel tcbdllflag.
      
      sep name lift CoreCommuInv.
      eapply CoreCommuInv_set_notsemq_frm.
      introv. intros.
      unfold is_sem in H0.
      simpljoin1.
      setoid_rewrite Hget_ecbls_dstportp in H0. inverts H0.
      introv. intros.
      unfold is_que in H0.
      simpljoin1.
      setoid_rewrite Hget_ecbls_dstportp in H0. inverts H0.
      sep cancel CoreCommuInv.

      sep cancel Aarray.
      sep name lift AOSCorePortPtrList in H.
      sep name lift AOSCorePortPtrList.
      unfold AOSCorePortPtrList in H.
      unfold AOSCorePortPtrList.
      sep normal in H.
      sep normal.
      sep cancel OSCorePortPtrList.
      sep split in H.
      rename H0 into HRH_CorePortPtrList.
      apply astar_l_apure_intro.
      2:{
        instantiate(1:=(set dportls1 dstportp
        (Z.to_nat DNUM, pd, pid, DestinationP nextdst, pst, dstpin, dstpout,
        QueuePort dstsz (dstpm ++ msg :: nil)))).
        eapply RH_CorePortPtrList_upd_dportls; eauto.
      }
      sep name lift dmportp_sllseg.

      eapply dmportp_sllseg_compose.
      5:{
        sep cancel APortStruct.
        sep cancel 4%nat 1%nat.
        sep cancel 3%nat 1%nat.
        sep name lift Aop.
        apply disj_split. right.
        sep normal. sep eexists.
        assert (∘(Int.unsigned qsize - Int.unsigned (qentries +ᵢ  $ 1))=
        Init.Nat.pred ∘ (Int.unsigned qsize - Int.unsigned qentries))%nat as Htmp.
        {
          unfold Coqlib.nat_of_Z.
          rewrite <- Z2Nat.inj_pred.
          f_equal.
          rewrite <- Z.sub_1_r. 
          rewrite <- Z.sub_add_distr. f_equal.
          apply Int_add_one_Sn'.
          clear - Hdstport_type_match Hdstport_V_Entries.
          unfold OS_Port_Seg_dls in Hdstport_type_match.
          struct_type_vallist_match'_elim.
          inverts Hdstport_V_Entries. lia.
        }
        rewrite <- Htmp in H. clear Htmp.
        sep cancel 1%nat 9%nat.
        sep name lift dmportp_sllseg_qport_msg.
        sep cancel 1%nat 1%nat.
        sep split. auto.
        reflexivity.
        4: reflexivity.
        5: auto.
        3: { eapply join_set_set; eauto. }
        8:{
          right. splits; auto.
          right. eauto.
        }
        11-14: port_nth_val_solve.
        10: splits; auto.
        10: port_nth_val_solve.
        9: splits; auto. 
        9: port_nth_val_solve.
        3:{
          unfold RLH_PortPtrINecb.
          split; auto.
          - eapply RL_PortPtrList_upd; eauto.
            unfold OS_Port_V_nextPort.
            rewrite nth_val_update_nth_val_diff;[ |lia].
            apply nth_val_update_nth_val_diff. lia.
          - rewrite Forall_forall.
            intros.
            rewrite Forall_forall in Hinecb.
            apply Hinecb in H0.
            simpljoin1.
            destruct (addrval_eq_dec x0 dstportp).
            subst. eexists.
            apply EcbMod.set_a_get_a.
            apply TcbMod.beq_refl.
            eexists.
            rewrite EcbMod.set_a_get_a'; eauto.
            apply tidspec.neq_beq_false.
            congruence.
        }
        7: apply Qport_msg_ptrs_P_hold; auto.
        eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
        5: {
          eapply RL_PortAttr_upd; eauto.
          unfold OS_Port_V_direction.
          rewrite nth_val_update_nth_val_diff;[ |lia].
          apply nth_val_update_nth_val_diff. lia.
          unfold OS_Port_V_mode.
          rewrite nth_val_update_nth_val_diff;[ |lia].
          apply nth_val_update_nth_val_diff. lia.
        }
        {
          eapply RLH_Channel_upd_dportls1; eauto.
          right. do 4 eexists. eauto.
        }
        {
          eapply Channel_dstkport_Queue_IncoreC_upd_dportls1; eauto.
          right. do 4 eexists. eauto. 
        }
        {
          eapply R_Kernelport_DomainPort_upd; eauto.
          unfold OS_Port_V_portID.
          rewrite nth_val_update_nth_val_diff;[ |lia].
          apply nth_val_update_nth_val_diff. lia.
          unfold OS_Port_V_coreNum.
          rewrite nth_val_update_nth_val_diff;[ |lia].
          apply nth_val_update_nth_val_diff. lia.
        }
        {
          eapply RLH_Domainportl_upd_Queue'; eauto. 
        }
      }
      congruence.
      port_nth_val_solve.
      2: port_nth_val_solve.
      clear - Hdstport_type_match HSqentries Hsize_range.
      unfold OS_Port_Seg_dls in Hdstport_type_match.
      struct_type_vallist_match'_elim.
      simpl. splits; auto. pauto. pauto.
      splits; auto. 1-5: pauto.
      splits; auto. pauto. pauto.
      rewrite int16_max_unsigned_val.
      assert (Int.unsigned (qentries +ᵢ  $ 1) <= 65535) by lia.
      pauto.
    }
  {
    apply disj_rule.
    apply pfalse_rule.
    (*IF (port_ptr ′ .. OSQSize >ₑ port_ptr ′ .. OSQEntries)
    {(port_ptr ′ .. OSQIn) .. len =ₑ msg_ptr ′ .. len;ₛ
    memcpy (­&ₐ ((port_ptr ′ .. OSQIn) .. data) [′ 0], &ₐ (msg_ptr ′ .. data) [′ 0],
    〈 long 〉 msg_ptr ′ .. len­);ₛ
    ++ port_ptr ′ .. OSQIn;ₛ
    ++ port_ptr ′ .. OSQEntries;ₛ
    If (port_ptr ′ .. OSQIn ==ₑ port_ptr ′ .. OSQEnd)
    {port_ptr ′ .. OSQIn =ₑ port_ptr ′ .. OSQStart}}ELSE {RETURN 
    〈 char_t 〉 ′ OS_Q_FULL};ₛ
    RETURN ′ OS_NO_ERR *)
    naive pure intro.
    clear H0.
    assert (Int.unsigned qentries = Int.unsigned qsize \/ Int.unsigned qentries < Int.unsigned qsize) by lia.
    destruct H0 as [ H0| qentries_lt_qsize ].
    - simpl qportpost_send_Incore at 2.
      cbn [spec_code_cons].
      hoare abs lift pre.
      eapply abscsq_rule.
      apply noabs_oslinv.
      apply absinfer_choice2'. go.
      apply absinfer_eq.
      eapply abscsq_rule.
      apply noabs_oslinv.
      apply absinfer_choice2'. go.
      apply absinfer_eq.
      eapply abscsq_rule.
      apply noabs_oslinv.
      apply absinfer_choice2'. go.
      apply absinfer_eq.
      apply seq_rule with Afalse.
      2: apply pfalse_rule.
      {
        apply if_zero_rule.
        symbolic_exe_port.
        apply unsigned_inj in H0.
        subst qentries.
        rewrite Int_ltu_refl; auto.
        eapply rete_rule'.
        intros. symbolic_execution.
        (* {RETURN 〈 char_t 〉 ′ OS_Q_FULL} *)
        intros. sep normal. sep eexists.
        sep autocancel.
        right.
        sep normal. sep eexists.
        sep name lift dmportp_sllseg.
        eapply dmportp_sllseg_compose; eauto.
        2:{
          sep cancel APortStruct.
          sep cancel (dmportp_sllseg nextport).
          sep cancel dmportp_sllseg.
          apply disj_split. right.
          sep normal. sep eexists.
          sep cancel dmportp_sllseg_qport_msg.
          sep cancel dmportp_sllseg_qport_msg.
          sep autocancel.
          unfold EvtInv.
          sep normal. sep eexists.
          sep autocancel.
          unfold AECBList.
          sep normal. sep eexists.
          sep name lift evsllseg.
          eapply evsllseg_compose; eauto.
          sep autocancel.
          sep auto.
          all: auto.
          unfold RH_CurTCB. do 4 eexists. eauto.
          reflexivity.
          unfold RLH_PortPtrINecb.
          split; auto.
      }
      congruence.
    }
  - hoare name lift (dmportp_sllseg_qport_msg qin) pre.
    eapply backward_rule1.
    {
      eapply dmportp_sllseg_qport_msg_ngt0.
      clear - qentries_lt_qsize.
      unfold Coqlib.nat_of_Z. lia.
    }
    rename H into HR_Q_Data_P. naive pure intro. 
    destruct H as (msghold&msgholdl&?&Hmsg_le_channel_size). subst v'4.
    assert (Z.to_nat (Int.unsigned mlen + 1) = S (Z.to_nat (Int.unsigned mlen))) as HSmlen' by lia.
    rewrite HSmlen' in HSmlen. inverts HSmlen.
    hoare name lift msghold pre.
    eapply backward_rule1.
    {
      apply dmportp_sllseg_qport_msg_split.
      unfold Coqlib.nat_of_Z. lia. 
    }
    naive pure intro.
    destruct H. destruct H1.
    invertsr H1. rename v'5 into irrmsghold.
    rename H2 into Hmsghold_type_match.
    rename H into Hmsghold_channel_size.
    rename H3 into Hmsghold_le_channel_size.
    destruct qin as [qinb qino].
    hoare name lift APortStruct (dmportp_sllseg_qport_msg  (dmportp_sllseg_qport_msg_next (qinb, qino) qstart qend)) (dmportp_sllseg_qport_msg qout) pre.
    hoare remember (1::2::3::4::5::nil) pre.
    apply seq_rule with (APortStruct dstportp (update_nth_val 17
    (update_nth_val 14 dstport
      (Vptr (dmportp_sllseg_qport_msg_next (qinb,qino) qstart qend)))
    (Vint32 (qentries +ᵢ  $ 1)))**
    Aarray (qinb, qino +ᵢ  Int.one) (Tarray char_t (Z.to_nat (Int.unsigned mlen))) msg **
    Aarray
    (get_off_addr (qinb, qino +ᵢ  Int.one)
       (Int.mul ($ Z.of_nat (Z.to_nat (Int.unsigned mlen))) ($ Z.of_nat (typelen char_t))))
    (Tarray char_t (∘ CHANNEL_CACHE_SZIE - Z.to_nat (Int.unsigned mlen)))
    (skipn (Z.to_nat (Int.unsigned mlen)) (msghold ++ irrmsghold)) **
    PV (qinb, qino) @ char_t |-> Vint32 mlen **
    dmportp_sllseg_qport_msg qout (qinb, qino) qstart qend ∘ (Int.unsigned qentries)
    dstportmsgl **
    dmportp_sllseg_qport_msg (dmportp_sllseg_qport_msg_next (qinb, qino) qstart qend) qout
    qstart qend (Init.Nat.pred ∘ (Int.unsigned qsize - Int.unsigned qentries)) msgholdl **
    H).
    {
      subst H.
      apply if_one_rule.
      symbolic_exe_port.
      clear - qentries_lt_qsize.
      apply Intlt_true_is_Zlt in qentries_lt_qsize.
      now rewrite qentries_lt_qsize.
      clear Hentries_le_size.
      (* (port_ptr ′ .. OSQIn) .. len =ₑ msg_ptr ′ .. len;ₛ *)
      destruct msgptr as [msgptrb msgptro].
      hoare normal pre.
     
      cbn [Aarray Aarray'].
      hoare name lift Aop (Aptrmapsto (qinb,qino)) pre.
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
          assert ((qinb, Int.add (qino) (Int.zero)) = (qinb,qino) ).
          {
            rewrite Int.add_zero. auto. 
          }
          cbn [fst snd].
          rewrite H. clear H.
          split; intros; eauto.
        }
        { 
          intros. 
          eapply symbolic_lemmas.struct_member_rv_flag.
          sep autocancel.
          2-6: try reflexivity.
          unfold get_off_addr. cbn [fst snd].
          rewrite Int.add_zero.
          sep autocancel. apply H.
          simpl. clear - Hmsg_type_match.
          simpl in Hmsg_type_match. tauto.
        }
        { now apply assign_type_match_true. }
        {
          intros. sep eexists. sep auto.
        }
      }
      clear Hmsg_le_channel_size.
      rename H0 into Hlenmsg_mlen.
      (* memcpy (­&ₐ ((port_ptr ′ .. OSQIn) .. data) [′ 0], &ₐ (msg_ptr ′ .. data) [′ 0],
      〈 long 〉 msg_ptr ′ .. len­);ₛ *)
      assert ((qinb, Int.add (qino) (Int.zero)) = (qinb,qino)).
      {
        rewrite Int.add_zero. auto. 
      }
      cbn [fst snd].
      rewrite H. clear H.
      unfold get_off_addr.  cbn[fst snd].
      hoare name lift (Alvarmapsto port_ptr) APortStruct (Aptrmapsto (qinb, qino)) pre.
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
            rewrite <- H0. sep autocancel.
            exact H.
          }
          all: try reflexivity.
          simpl in Hmsg_type_match. tauto.
        }
        {
          intros; unfold_spec. cbn [fst snd].
          sep normal. sep eexists.
          sep autocancel; sep split; eauto.
          rewrite ! Int.add_zero.
          sep name lift msghold in H.
          eapply Aarray_split_single with (m:=(Z.to_nat (Int.unsigned mlen)))in H.
          2:{
            unfold CHANNEL_CACHE_SZIE. clear. mauto. 
          }
          2:{
            clear - H_mlen_le_CHANNEL_size. unfold Coqlib.nat_of_Z. lia.
          }
          2: rewrite app_length; auto.
          sep autocancel.
          sep name lift Aarray' in H. unfold Aarray.
          rewrite <- Hlenmsg_mlen.
          sep autocancel. apply H.
        }
        { go. unfold AEventNode. go. unfold AEventData. destruct portmsgq; go. }
        { sep_unfold_funpost. intros. sep destruct H. sep auto. }
        { sep_unfold_funpre. intros. sep destruct H. sep auto. }
        { pauto. }
      }
      unfold getasrt; unfold OS_memcopyPost, OS_memcopyPost'.
      hoare normal pre. pure intro.
      invertsr H.
      invertsr H0. clear H1.
      rename H3 into Hlen_irrmsghold.
      clear H8. 
      rename H2 into Hisptr_et_next.
      rename H4 into Hi1_range.
      rename H5 into Hevgrp_range.
      rename H6 into Hi2_range.
      rename H7 into Hisptr_x0.
      rename H9 into Hi_range.
      rewrite ! Int.add_zero.
      hoare abs lift pre.
      (* ++ port_ptr ′ .. OSQIn;ₛ *)
      eapply seq_rule.
      {
        eapply port_memeber_asgn; try reflexivity.
        - sep auto. split; intros.
          sep autocancel. exact H.
          sep auto.
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
      assert (Int.unsigned (qentries +ᵢ  $ 1) <=? Int16.max_unsigned = true) as Hqentries_range.
      {
        clear - qentries_lt_qsize Hsize_range.
        pose proof Int_add_one_Sn qentries ltac:(lia).
        rewrite Z.leb_le. rewrite int16_max_unsigned_val. lia.
      }
      eapply seq_rule.
      {
        eapply port_memeber_asgn; try reflexivity.
        - intros. eapply symbolic_lemmas.bop_rv.
          * eapply port_QEntries_rv. 
            3: { sep autocancel. apply H. }
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
        - simpl. now rewrite Hqentries_range.
        - intros. sep auto.
      }
      (* If (port_ptr ′ .. OSQIn ==ₑ port_ptr ′ .. OSQEnd)
      {port_ptr ′ .. OSQIn =ₑ port_ptr ′ .. OSQStart};ₛ *)
      hoare name lift APortStruct pre.
      destruct qend as [qendb qendo].
      eapply ift_rule.
      - intros. eexists. 
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
        * destruct (peq qinb qendb); auto.
          destruct (Int.eq (qino +ᵢ  Int.mul ($ 1) ($ 33)) qendo); auto.
        * reflexivity.
      - intros. sep eexists. 
        eapply sep_aconj_r_aisfalse_to_astar in H.
        2:{ intros.
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
        * destruct (peq qinb qendb); auto.
          destruct (Int.eq (qino +ᵢ  Int.mul ($ 1) ($ 33)) qendo); auto.
        * reflexivity.
        }
        sep autocancel.
        sep normal in H.
        sep destruct H.
        unfold AOSMapTbl.
        unfold AOSUnMapTbl.
        unfold AOSTCBPrioTbl.
        unfold AOSRdyTblGrp.
        unfold AOSRdyTbl. unfold AOSRdyGrp.
        sep normal. sep eexists. sep autocancel.
        sep split in H.
        destruct H0. 
        2:{ destruct (peq qinb qendb);
        destruct (Int.eq (qino +ᵢ  Int.mul ($ 1) ($ 33)) qendo); auto; simpl in H0; discriminate. }
        unfold dmportp_sllseg_qport_msg_next.
        simpl typelen. unfold msg_distance.
        unfold Qport_msg_ptrs_P in HQport_msg_ptrs.
        destruct qstart. simpljoin1. unfold get_off_addr in *.
        simpl in H2, H4.
        invertsr H2. invertsr H4.
        cbn [fst snd] in *.
        rewrite ! Int.add_zero_l in *.
        rewrite peq_true in H0.
        destruct (Int.eq (Int.mul ($ x3) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
        (Int.mul ($ Int.unsigned qsize) ($ 33))) eqn:E'; [discriminate | ].
        simpl typelen. simpl Z.of_nat.
        assert (
        (qinb, Int.mul ($ x3) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)) =
        (if
                Int.unsigned
                  (Int.divu
                      (Int.mul ($ Int.unsigned qsize) ($ 33) -ᵢ
                      Int.mul ($ x3) ($ 33)) ($ 33)) =? 1
                then (qinb, Int.zero)
                else (qinb, Int.mul ($ x3) ($ 33) +ᵢ  $ 33))).
        {
          clear - H6 H7 Hsize_range E'.
          destruct (Int.unsigned (Int.divu (Int.mul ($ Int.unsigned qsize) ($ 33) -ᵢ Int.mul ($ x3) ($ 33)) ($ 33)) =? 1) eqn:?.
          2: { rewrite (Int.mul_commut ($ 1)).  rewrite Int.mul_one. reflexivity. }
          exfalso.
          assert (exists n,  Int.unsigned qsize = n + x3 /\ 1 <= n <= 65536).
          { exists (Int.unsigned qsize- x3). split;lia. }
          destruct H as [n [H0 H1]].
          rewrite H0 in Heqb.
          assert (x3 <= 65536) by lia. 
          erewrite  <- (Int.unsigned_repr n) in Heqb at 1.
          rewrite  <- (Int.unsigned_repr x3) in Heqb at 1.  
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
          rewrite <- (Int.unsigned_repr x3) in E' at 2.
          rewrite <- Int.add_unsigned in E'.
          rewrite Int.mul_add_distr_l in E'.
          rewrite (Int.add_commut (Int.mul ($ 1) ($ 33))) in E'. 
          rewrite Int.eq_true in E'. discriminate.
          all: rewrite max_unsigned_val; lia.
        }
        rewrite H1 in H. sep autocancel.
        unfold Aarray in H. sep autocancel.
        rewrite Hlenmsg_mlen. sep autocancel.
      - intros.
        eapply backward_rule1. 
        eapply sep_aconj_r_aistrue_to_astar.
        { intros. 
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
        * destruct (peq qinb qendb); auto.
          destruct (Int.eq (qino +ᵢ  Int.mul ($ 1) ($ 33)) qendo); auto.
        * reflexivity.
        }
        naive pure intro.
        hoare name lift APortStruct pre.
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
        unfold Qport_msg_ptrs_P in HQport_msg_ptrs.
        destruct qstart. simpljoin1. unfold get_off_addr in *.
        simpl in H14, H16.
        invertsr H14. invertsr H16.
        cbn [fst snd] in *.
        clear H8 H9.
        rewrite ! Int.add_zero_l in *.
        rewrite peq_true in H6.
        destruct (Int.eq (Int.mul ($ x2) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
        (Int.mul ($ Int.unsigned qsize) ($ 33))) eqn:E'.
        2:{
          simpl in H6. congruence.
        }
        simpl typelen. simpl Z.of_nat.
        rewrite aux_pureLib.Int_eq_dec in E'.
        rewrite <- E'.
        rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. 
        rewrite (Int.mul_commut ($ 1)).
        rewrite Int.mul_one.
        assert ((Int.divu ($ 33) ($ 33)) = Int.one)  by (clear;mauto).
        rewrite H8.
        rewrite Int.unsigned_one.
        rewrite Z.eqb_refl.
        rewrite update_nth_val_diff in H7. 2:lia.
        rewrite update_nth_val_same in H7.
        sep auto.
        unfold Aarray in H7.
        sep autocancel.
        rewrite Hlenmsg_mlen. sep autocancel.
    }
    assert (∘(Int.unsigned qsize - Int.unsigned (qentries +ᵢ  $ 1))=
              Init.Nat.pred ∘ (Int.unsigned qsize - Int.unsigned qentries))%nat as Htmp.
              {
                unfold Coqlib.nat_of_Z.
                rewrite <- Z2Nat.inj_pred.
                f_equal.
                rewrite <- Z.sub_1_r. 
                rewrite <- Z.sub_add_distr. f_equal.
                apply Int_add_one_Sn'.
                clear - Hdstport_type_match Hdstport_V_Entries.
                unfold OS_Port_Seg_dls in Hdstport_type_match.
                struct_type_vallist_match'_elim.
                inverts Hdstport_V_Entries. lia.
              }
      rewrite <- Htmp. clear Htmp.
      subst H.
      (* abs step: qportpost_send_one_Incore*)
      hoare name lift osdomainport oskport oschannel oscoreheap pre.
      hoare abs lift pre.
      cbn [qportpost_send_Incore].
      cbn [spec_code_cons].
      eapply abscsq_rule.
      apply noabs_oslinv.
      apply absinfer_choice2'. go.
      apply absinfer_eq.
      eapply abscsq_rule.
      apply noabs_oslinv.
      apply absinfer_choice2'. go.
      apply absinfer_eq.
      eapply abscsq_rule.
      apply noabs_oslinv.
      apply absinfer_choice1'. go.
      apply absinfer_eq.
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply qportpost_send_one_InCore_cont.
      go.
      2: eauto.
      4: {
        rewrite app_length. simpl length.
        assert (length dstkportpl1 + S (length dstkportpl2) -
        S (length dstkportpl2) = length dstkportpl1)%nat as Htmp by lia.
        rewrite Htmp. apply nth_error_middle.
      }
      4: eauto.
      eauto.
      4: apply absinfer_eq.
      {
        rewrite HSmlen'. rewrite <- H0. eauto. 
      }
      auto.
      {
        eapply join_get_l; eauto.
      }

      eapply rete_rule'.
      intros. symbolic_execution.
      (* RETURN ′ OS_NO_ERR *)
      intros. sep normal. sep eexists.
      sep autocancel.
      right.
      sep normal. sep eexists.
      sep cancel Aop.
      sep name lift AOSCorePortPtrList in H.
      sep name lift AOSCorePortPtrList.
      unfold AOSCorePortPtrList in H.
      unfold AOSCorePortPtrList.
      sep normal in H.
      sep normal.
      sep cancel OSCorePortPtrList.
      apply sep_pure_split in H.
      destruct H as (HRH_CorePortPtrList&H).
      apply astar_l_apure_intro.
      2:{
        instantiate(1:=(set dportls1 dstportp
        (Z.to_nat DNUM, pd, pid, DestinationP nextdst, pst, dstpin, dstpout,
        QueuePort dstsz (dstpm ++ msg :: nil)))).
        eapply RH_CorePortPtrList_upd_dportls; eauto.
      }
      sep name lift dmportp_sllseg.
      eapply dmportp_sllseg_compose.
      5:{
        sep cancel APortStruct.
        sep name lift dmportp_sllseg in H.
        sep cancel 1%nat 2%nat.
        sep cancel dmportp_sllseg.
        apply disj_split.
        right.
        sep normal. sep eexists.
        sep name lift dmportp_sllseg_qport_msg.
        eapply dmportp_sllseg_qport_msg_append_tail.
        4:{
          sep eexists.
          sep cancel Aarray.
          sep cancel Aarray.
          sep cancel dmportp_sllseg_qport_msg.
          sep autocancel.
          unfold EvtInv.
          sep normal. sep eexists.
          sep autocancel.
          unfold AECBList.
          sep normal. sep eexists.
          sep name lift evsllseg.
          eapply evsllseg_compose; eauto.
          sep cancel AEventNode.
          sep cancel evsllseg.
          sep cancel evsllseg.
          sep autocancel.
          sep split.
          auto.
          unfold RH_CurTCB. do 4 eexists. eauto.
          auto.
          reflexivity.
          3:{
            eapply join_set_set; eauto.
          }
          all: auto.
          eapply R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1; eauto.
          eapply RLH_Channel_upd_dportls1; eauto.
          right. do 4 eexists. eauto.
          reflexivity.
          unfold RLH_PortPtrINecb.
          split; auto.
          eapply RL_PortPtrList_upd; eauto.
          unfold OS_Port_V_nextPort.
          rewrite nth_val_update_nth_val_diff;[ |lia].
          apply nth_val_update_nth_val_diff. lia.
          eapply Channel_dstkport_Queue_IncoreC_upd_dportls1; eauto.
          right. do 4 eexists. eauto.
          eapply R_Kernelport_DomainPort_upd; eauto.
          unfold OS_Port_V_portID.
          rewrite nth_val_update_nth_val_diff;[ |lia].
          apply nth_val_update_nth_val_diff. lia.
          unfold OS_Port_V_coreNum.
          rewrite nth_val_update_nth_val_diff;[ |lia].
          apply nth_val_update_nth_val_diff. lia.
          eapply RLH_Domainportl_upd_Queue'; eauto.
          eapply RL_PortAttr_upd; eauto.
          unfold OS_Port_V_direction.
          rewrite nth_val_update_nth_val_diff;[ |lia].
          apply nth_val_update_nth_val_diff. lia.
          unfold OS_Port_V_mode.
          rewrite nth_val_update_nth_val_diff;[ |lia].
          apply nth_val_update_nth_val_diff. lia.
          right. splits; auto. right.
          eauto.
          eapply Qport_msg_ptrs_P_hold; eauto.
          splits; auto.
          port_nth_val_solve.
          rewrite Int_add_one_Sn'. lia.
          lia.
          splits; auto.
          port_nth_val_solve.
          port_nth_val_solve.
          port_nth_val_solve.
          port_nth_val_solve.
          port_nth_val_solve.
          apply array_type_vallist_match_app. splits; auto.
          simpl in Hmsg_type_match. tauto.
          erewrite <- firstn_skipn in Hmsghold_type_match.
          apply array_type_vallist_match_app in Hmsghold_type_match.
          jauto.
        }
        auto.
        lia.
        auto.
      }
      congruence.
      port_nth_val_solve.
      2: port_nth_val_solve.
      clear - Hdstport_type_match qentries_lt_qsize Hsize_range.
      unfold OS_Port_Seg_dls in Hdstport_type_match.
      struct_type_vallist_match'_elim.
      simpl. splits; auto. pauto. pauto.
      splits; auto. 1-5: pauto.
      splits; auto. pauto. pauto.
      rewrite int16_max_unsigned_val.
      assert (Int.unsigned (qentries +ᵢ  $ 1) <= 65535).
      {
        pose proof Int_add_one_Sn qentries ltac:(lia). lia.
      }
      pauto.
    }
Qed.
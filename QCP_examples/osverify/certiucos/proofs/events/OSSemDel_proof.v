Require Import include_frm.
Require Import os_code_defs.
Require Import os_ucos_h.
Require Import code_notations.
Require Import abs_op.
Require Import ifun_spec.
Require Import sem_common.
Require Import semdel_pure.

Require Import seplog_trm_tacs. 

Lemma OSSemDel_proof:
  forall vl p r logicl ct, 
    Some p =
    BuildPreI os_internal OSSemDel vl logicl OSSemDelPre ct->
    Some r =
    BuildRetI os_internal OSSemDel vl logicl OSSemDelPost ct->
    exists t d1 d2 s,
      os_internal OSSemDel = Some (t, d1, d2, s) /\
      {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  rename v'22 into er.
  inverts H0.
  rename v'2 into pevent_blk.
  subst logicl.
  (* new add *)
  rename v'18 into pegrp.
  rename v'19 into petbl_addr.
  rename v'20 into lpetbl.
  rename v'21 into petbl.
  rename H11 into Hpegrp_range.
  rename H12 into Hid_petbl.
  rename H13 into Hrl_petbl.
  rename H14 into Hmat_petbl.
  rename H15 into Hlen_petbl.
  (* end of new add *)

  hoare_unfold.
  lzh_hoare_if.
  destruct (Int.ltu ($ 0) v'17); auto.
  change (Int.ltu ($ 0) v'17) with false.
  tryfalse.
  clear Hif_false.

  lzh_hoare_if.
  destructs LHift_true.
  false.

  hoare_assert_pure (isptr v'3). 
  {
    sep_lifts_trms_in H0 (evsllseg v'3).
    apply evsllseg_isptr in H0; auto.
  }
  hoare_split_pure_all.
  lzh_hoare_if.
  change (Int.eq ($ OS_EVENT_TYPE_SEM) ($ OS_EVENT_TYPE_SEM)) with true in LHift_true.
  tryfalse.
  
  hoare_unfold.
  lzh_hoare_if.
  change (Int.eq ($ 0) ($ 0)) with true in LHif_true. tryfalse.

  hoare forward. 
  
  change (Int.eq ($ 0) ($ 0)) with true in Hif_true. tryfalse.
  
  lzh_hoare_if;
  pure_auto;
  lzh_val_inj_simpl;
  lzh_simpl_int_eq; tryfalse.

  2: {
    instantiate (1:=Afalse) in H12.
    instantiate (1:=Afalse) in H12.
    destruct H12.
    sep split in H12. auto.
    sep split in H12. auto.
  }
  clear Hif_false1 LHif_true.
  clear Hif_false0.

  eapply seq_rule.
  eapply call_rule with (vl:=Vptr (pevent_blk, Int.zero)::nil).
  2: { unfold OS_spec. simpl. unfold OS_EventRemove_spec. eauto. }
  2: {
    introv Hsat.
    simpl getasrt.
    unfold OS_EventRemovePre'.
    sep normal.
    exists v'13. exists ((DSem v'6)::v'14).
    exists v'11. exists (((V$ OS_EVENT_TYPE_SEM :: V$ 0 :: Vint32 v'6 :: v'7 :: v'8 :: v'3 :: Vint32 pegrp :: petbl_addr :: nil),v'4,petbl)::v'12).
    eexists. eexists. eexists. eexists.
    trycancel.
    sep cancel Aop.
    sep cancel Aier.
    sep pauto.
    eapply evsllseg_merge; eauto.
    sep_lifts_trms_in Hsat (evsllseg v'10).
    eapply evsllseg_list_len_eq; eauto.
    simpl. apply eq_S.
    sep_lifts_trms_in Hsat (evsllseg v'3).
    eapply evsllseg_list_len_eq; eauto.
    sep cancel (evsllseg v'10).
    unfold evsllseg.
    fold evsllseg.
    sep normal. exists v'3.
    sep split; eauto.
    unfold AEventNode.
    unfold AOSEvent.
(*     sep pauto. *)
    unfold AOSEventTbl.
    unfold AOSPostEventTbl.
    unfold node.
    sep pauto; eauto.
    sep cancel Astruct.
    sep cancel Aarray.
    sep cancel Aarray.
    (* unfold node.
    sep pauto.
    sep cancel Astruct. *)
    unfold AEventData.
    sep split.
    eauto.
    clear -H8. int auto.
    unfold V_OSEventCnt. simpl. auto.
    unfold V_OSEventType. simpl. auto.
    split; auto.
    struct_type_match_solver.
    (* eauto.
    unfold V_OSEventGrp. simpl. auto.
    auto. *)
    sep_lifts_trms_in Hsat (evsllseg v'10).
    destruct v'11.
    unfold evsllseg at 1 in Hsat. sep split in Hsat. 
    split. introv Hnil. simpljoin1. eauto.
    introv Hf. false.
    sep destroy Hsat. 
    eapply evsllseg_get_last_eq in H12. 
    split. introv Hf. tryfalse. introv HH. rewrite H12. auto.
    auto.
    sep_lifts_trms_in Hsat (evsllseg v'10).
    eapply evsllseg_list_len_eq; eauto.
    simpl. auto.
  }
  go.
  intros.
  apply rvl_elim.
  sep get rv.
  apply rvl_nil.
  go.
  unfold getasrt.
  unfold OS_EventRemovePre. unfold OS_EventRemovePre'.
  introv Hsat.
  sep destruct Hsat.
  unfold CurLINV. 
  exists init_lg.
  unfold p_local in Hsat.
  sep cancel CurTid.
  sep cancel LINV.
  sep auto.

  introv Hsat.
  sep destruct Hsat.
  unfold getasrt in Hsat.
  unfold OS_EventRemovePost in Hsat.
  unfold OS_EventRemovePost' in Hsat.
  sep destruct Hsat.
  unfold CurLINV.
  exists init_lg.
  unfold p_local in Hsat. sep cancel CurTid. sep cancel LINV.
  sep auto.

  hoare_ex_intro.
  unfold getasrt.
  unfold OS_EventRemovePost.
  unfold OS_EventRemovePost'.
  hoare normal pre.
  hoare_ex_intro.
  hoare_unfold.
  inverts H11.

  (*pevent ′ → OSEventType =ₑ ′ OS_EVENT_TYPE_UNUSED;ₛ*)
  hoare forward. 
  hoare unfold.
  hoare_assert_pure (isptr v'9). (* ecbf_sllseg v'9 ... *)
  seg_isptr.  
  hoare forward.
  pure_auto.
  (* OSEventFreeList ′ =ₑ pevent ′;ₛ *)
  hoare forward.
  
  (* return NULL *)
  unfold AOSPostEventTbl.
  hoare unfold.
  eapply rete_rule; auto.
  split.
  sep normal.
  sep eexists.
  sep cancel Aie.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel Ais.
  sep cancel A_isr_is_prop.
  sep cancel Aop.
  sep cancel Aier.
  sep cancel OSEventFreeList.
  sep cancel Astruct.
  sep cancel A_dom_lenv.
  sep cancel (Alvarmapsto tasks_waiting).
  sep cancel (Alvarmapsto pevent).
  sep cancel p_local.
  sep split.
  9: { eauto. }
  sep cancel evsllseg.
  unfold os_inv.id_addrval', id_addrval' in *.
  assert (v'34 = v'5) by congruence.
  subst.
  sep cancel Aarray.
  assert (v'36 = lpetbl) by congruence.
  subst.
  sep cancel Aarray.
  sep cancel ecbf_sllseg.
  sep cancel (Agvarmapsto OSEventList).
  unfold AEventData in H15.
  sep normal in H15.
  sep split in H15.
  sep pauto. 

  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  eauto.
  sep get rv.

  Unshelve.
  exact Afalse.
Qed.

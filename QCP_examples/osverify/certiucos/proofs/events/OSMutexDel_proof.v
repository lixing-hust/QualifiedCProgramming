Require Import include_frm.
Require Import Lists.ListSet.
Require Import os_code_defs.
Require Import os_ucos_h.
Require Import abs_op.
Require Import os_core.
Require Import code_notations.
Require Import inv_prop.
Require Import ifun_spec.
Require Import List.
Require Import sem_common.
Require Import err_list_common.
Require Import OSMutex_common.
Require Import mutex_pend_pure.
Require Import seplog_trm_tacs.
Require Export os_inv. 

Local Open Scope list_scope.
Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

Lemma mutexdel_int:
  forall x,
    Int.unsigned x <= 65535 ->
    (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus)) = (x >>ᵢ $ 8).
Proof.
  intros.
  eapply mund_int_a1 in H.
  remember (x >>ᵢ $ 8).
  clear Heqi.
  unfold Int.modu.
  rewrite mund_int_byte_modulus.
  repeat ur_rewriter.
  apply mund_int_mod. auto.
Qed.

Lemma OSMutexDel_proof:
  forall vl p r logicl ct, 
    Some p =
    BuildPreI os_internal OSMutexDel vl logicl OSMutexDelPre ct->
    Some r =
    BuildRetI os_internal OSMutexDel vl logicl OSMutexDelPost ct->
    exists t d1 d2 s,
      os_internal OSMutexDel = Some (t, d1, d2, s) /\
      {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec. 
  
  inverts H0.
  rename v'3 into pevent_blk.
  subst logicl.
  rename v'23 into pegrp.  (* new add *)
  rename v'24 into petbl_addr.  (* new add *)
  rename v'25 into lpetbl.
  rename v'26 into petbl.
  rename H15 into Hpegrp_range. (* new add *)
  rename H16 into Hid_petbl.
  rename H17 into Hrl_petbl.
  rename H18 into Hmat_petbl.
  rename H19 into Hlen_petbl.

  hoare_unfold.
  lzh_hoare_if.
  destruct (Int.ltu ($ 0) v'22); auto.
  change (Int.ltu ($ 0) v'22) with false.
  tryfalse.

  hoare_assert_pure (isptr v'4). 
  {
    sep_lifts_trms_in H15 (evsllseg v'4).
    apply evsllseg_isptr in H15; auto.
  }
  hoare_split_pure_all.
  lzh_hoare_if.
  destruct LHift_true; tryfalse.
  hoare_unfold.
  lzh_hoare_if.
  change (Int.eq ($ OS_EVENT_TYPE_MUTEX)
               ($ OS_EVENT_TYPE_MUTEX)) with true; tryfalse.

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
    instantiate (1:=Afalse) in H17.
    instantiate (1:=Afalse) in H17.
    destruct H17.
    sep split in H17. auto.
    sep split in H17. auto.
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
    exists v'14. eexists ((DMutex  (Vint32 v'7) v'8) :: v'15). 
    exists v'12.
    exists (((V$ OS_EVENT_TYPE_MUTEX :: V$ 0:: Vint32 v'7 :: v'8 :: v'9 :: v'4 :: Vint32 pegrp :: petbl_addr :: nil),v'5, petbl)::v'13).
    do 4 eexists. (* eexists. eexists. *)
    sep cancel Aop.
    sep cancel Aie.
    sep cancel Ais.
    sep cancel Acs.
    sep cancel Aisr.
    sep cancel Aier.
    sep pauto.    
    eapply evsllseg_merge; eauto.
    sep_lifts_trms_in Hsat (evsllseg v'11).
    eapply evsllseg_list_len_eq; eauto.
    simpl. apply eq_S.
    sep_lifts_trms_in Hsat (evsllseg v'4).
    eapply evsllseg_list_len_eq; eauto.
    sep cancel (evsllseg v'11).
    unfold evsllseg.
    fold evsllseg.
    sep normal. exists v'4.
    sep split; eauto.
    unfold AEventNode.
    unfold AOSEvent.
    unfold AOSEventTbl.
    unfold AOSPostEventTbl.
    unfold node.
    sep pauto; eauto.
    sep cancel Astruct.
    sep cancel Aarray.
    sep cancel Aarray.
    unfold AEventData.
    sep split.
    eauto.
(*     unfold AOSEventTbl. *)
(*     sep pauto.
    sep cancel Aarray.
    unfold node.
    sep pauto.
    sep cancel Astruct.
    unfold AEventData.
    sep split.
    eauto. *)
    unfold V_OSEventPtr;simpl;auto.
    unfold V_OSEventCnt; simpl; auto.
    unfold V_OSEventType; simpl; auto.
    split; auto.
    struct_type_match_solver.
    (* eauto.
    unfold V_OSEventGrp. simpl. auto.
    auto. *)
    sep_lifts_trms_in Hsat (evsllseg v'11).
    destruct v'12.
    unfold evsllseg at 1 in Hsat. sep split in Hsat. 
    split. introv Hnil. simpljoin1. eauto.
    introv Hf. false. 
    splits; intros; tryfalse. 
    sep destroy Hsat. 
    eapply evsllseg_get_last_eq in H18; auto.
    sep_lifts_trms_in Hsat (evsllseg v'11).
    eapply evsllseg_list_len_eq; eauto.
    simpl. auto.
  }
  pure_auto.
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
  inverts H16. 
  inverts H28.
  unfold abs_op.id_addrval' in H8.
  unfold id_addrval' in H24.
  rewrite H8 in H24; inverts H24.
  unfold abs_op.id_addrval' in Hid_petbl.
  unfold id_addrval' in H27.
  rewrite Hid_petbl in H27; inverts H27.

(******pip ′ =ₑ 〈 char_t 〉 (pevent ′ → OSEventCnt ≫ ′ 8);ₛ*****)
  hoare forward.
  go.
  apply intlemma0.

(*********OSTCBPrioTbl ′ [pip ′] =ₑ NULL;ₛ*********)
  unfolds in H3.
  destruct v'18;destruct e; try solve [clear -H3; tryfalse].
  simpljoin.
  unfolds in H3.
  tryfalse.
  simpljoin.
  unfolds in H16.
  simpljoin.
  inverts H3.

  hoare forward.
  change (Byte.max_unsigned) with 255.
  simpl.
  clear -H31.
  assert(Int.unsigned (Int.modu (x >>ᵢ $ 8) ($ Byte.modulus)) <= 255).
  eapply postintlemma2'.
  pure_auto.
  eapply del_intlemma2; eauto.
  rewrite H4.
  eapply del_intlemma2; eauto.

  (*pevent ′ → OSEventType =ₑ ′ OS_EVENT_TYPE_UNUSED;ₛ*)
  hoare forward. 
  hoare unfold.
  hoare_assert_pure (isptr v'10). (* ecbf_sllseg v'9 ... *)
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
  sep cancel Aier.
  sep cancel A_isr_is_prop.
  sep cancel Aop.
  sep cancel OSEventFreeList.
  sep cancel Astruct.
  sep cancel A_dom_lenv.
  sep cancel (Alvarmapsto tasks_waiting).
  sep cancel (Alvarmapsto pevent).
  sep cancel p_local.
  sep split.
  9: { eauto. }
  sep cancel evsllseg. 
  sep cancel Aarray.
  sep cancel Aarray.
  sep pauto.
  sep cancel ecbf_sllseg.
  unfold AEventData in H38.
  sep normal in H38.
  sep split in H38.
  sep pauto. 
  eapply mutexdel_int in H12.
  rewrite H12.
  eauto.

  auto.
  auto.
  instantiate (1:= x2).
  auto.
  auto.
  eapply H21.
  eapply H33.
  eauto.
  splits; eauto.
  eapply array_type_vallist_match_hold; eauto.
  rewrite H4.
  clear -H27.
  int auto.
  simpl.
  rewrite update_nth_val_len_eq; eauto.
  eauto.
  substs.
  auto.
(*   rewrite H24 in H8. *)
(*   inverts H8. *)
(*   auto. *)
  sep get rv.

  Unshelve.
  exact Afalse.
Qed.

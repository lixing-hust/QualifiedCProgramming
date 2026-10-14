
Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import ifun_spec.
Require Import abs_op.

(* absimp lemmas *)
Require Import abs_infer_step.
Require Import abs_infer_abt. 
Require Import ucos_frmaop.

Require Import hoare_tactics.
Require Import pure_auto.
Require Import ucos_pauto.
Require Import sep_auto.
Require Import seplog_tactics.
Require Import seplog_lemmas.
Require Import sep_cancel_ext.
Require Import derived_rules.
Require Import hoare_conseq.
Require Import ucos_forward.
Require Import math_auto.

Require Import sem_lab.
Require Import symbolic_lemmas.
Require Import Aarray_new_common.

Require Import sem_common.
Require Import gjb_common.
Require Import gjb_sem_common.
Require Import partition_common.
Require Import part_pos_rgn_spec.
Require Import part_pos_rgn_proof.
Require Import partinv_lemmas.

Require Import OSTimeTickPure.
Require Import OSMutex_common.
Require Import gjb_mutex_common.
Require Import sem_corecommu.

Require Import pos_list_common.
Require Import ev_aux_code.
Require Import evauxvar_lemmas.
Require Import evaux_pure.
Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Local Open Scope code_scope.


Lemma mutex_destroy_absimp_muxerr:
  forall sch vmux s0 P,
    (vmux = Vnull \/
       exists v'4, vmux = Vptr v'4 /\
                     (cmpaddr Cle v'4 userAddrStart = true \/
                        cmpaddr Clt userAddrEnd v'4 = true)) -> 
    can_change_aop P ->
    absinfer sch
      (<|| (mutex_destroy_muxerr (| vmux::nil|) ?? s0) ||>  ** P) 
      (<|| END (Some (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutex_destroy_absimp_mux_nopblk_abt:
  forall sch vmux a pbls P,
    vmux = Vptr a /\
    (cmpaddr Clt userAddrStart a = true /\ cmpaddr Cle a userAddrEnd = true) ->
    get pbls a = None ->
    can_change_aop P ->
    absinfer sch
      (<|| mutex_destroy (vmux :: nil) ||>  ** Hpbls pbls ** P)  
      (<|| ABORT ||> ** Hpbls pbls ** P).
Proof.
  introv Hrgn Hnone Hcop.
  assert (Hc: can_change_aop (Hpbls pbls ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try eapply absinfer_choice2; eauto.
  eapply absinfer_trans; try eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  simpljoin1.
  absimp_abt_solver.
  Unshelve.
  exact None.
Qed.

Lemma mutex_destroy_absimp_pos_err:
  forall sch vmux a pbls pos P,
    vmux = Vptr a /\
    (cmpaddr Clt userAddrStart a = true /\ cmpaddr Cle a userAddrEnd = true) ->
    get pbls a = Some pos ->
    (Int.ltu pos Int.zero = true \/ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) pos = true \/ Int.eq pos (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) ->
    can_change_aop P ->
    absinfer sch
      (<|| mutex_destroy (vmux :: nil) ||>  ** Hpbls pbls ** P)  
      (<|| END (Some (Vint32 (Int.repr EINVAL))) ||> ** Hpbls pbls ** P).
Proof.
  intros.
  simpljoin1.
  infer_solver 2%nat.
Qed.

Lemma mutex_destroy_absimp_pevent_null_err:
  forall sch a pbls pos muxeibs ow tp rcnt prot prioc wq cnsa P mc,
    (cmpaddr Clt userAddrStart a = true /\ cmpaddr Cle a userAddrEnd = true) ->
    get pbls a = Some pos ->
    (pos = Int.zero \/ Int.ltu Int.zero pos = true) ->
    Int.ltu pos ($ (OS_USER_MAX_EVENTS / 3)) = true -> 
    get muxeibs pos = Some (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    can_change_aop P ->
    absinfer sch
      (<|| mutex_destroy (Vptr a :: nil) ||>  ** Hpbls pbls ** HMuxInfo muxeibs ** P)  
      (<|| END (Some (Vint32 (Int.repr EINVAL)))  ||> ** Hpbls pbls ** HMuxInfo muxeibs ** P).
Proof.
  intros. simpljoin1.
  infer_solver 4%nat.
Qed.

Lemma mutex_destroy_absimp_pevent_holder_abt:
  forall sch a pbls pos muxeibs ow tp rcnt prot prioc wq cnsa P mc,
    (cmpaddr Clt userAddrStart a = true /\ cmpaddr Cle a userAddrEnd = true) ->
    get pbls a = Some pos ->
    (pos = Int.zero \/ Int.ltu Int.zero pos = true) ->
    Int.ltu pos ($ (OS_USER_MAX_EVENTS / 3)) = true -> 
    get muxeibs pos = Some (Holder, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    can_change_aop P ->
    absinfer sch
      (<|| mutex_destroy (Vptr a :: nil) ||>  ** Hpbls pbls ** HMuxInfo muxeibs ** P)  
      (<|| ABORT  ||> ** Hpbls pbls ** HMuxInfo muxeibs ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (Hpbls pbls ** HMuxInfo muxeibs ** P)) by can_change_aop_solver.
  do 3 (eapply absinfer_trans; try eapply absinfer_choice2; eauto).
  eapply absinfer_trans; try eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  simpljoin1.
  absimp_abt_solver;
  instantiate (3:= s);
  instantiate (2:= mutex_destroy_not_placeholder_assm (|Vptr a :: nil|));
  sep pauto.
  Unshelve.
  exact None.
Qed.

Lemma mutex_destroy_absimp_waiting_tasks_err:
  forall sch a pbls pos muxeibs ow tp rcnt prot prioc wq cnsa P eid els pip o wls mc,
    (cmpaddr Clt userAddrStart a = true /\ cmpaddr Cle a userAddrEnd = true) ->
    get pbls a = Some pos ->
    (pos = Int.zero \/ Int.ltu Int.zero pos = true) ->
    Int.ltu pos ($ (OS_USER_MAX_EVENTS / 3)) = true -> 
    get muxeibs pos = Some (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    get els eid = Some (absmutexsem pip o, wls) ->
    wls <> nil ->
    can_change_aop P ->
    absinfer sch
      (<|| mutex_destroy (Vptr a :: nil) ||>  ** Hpbls pbls ** HMuxInfo muxeibs ** HECBList els ** P)  
      (<|| END (Some (Vint32 (Int.repr EBUSY)))  ||> ** Hpbls pbls ** HMuxInfo muxeibs ** HECBList els **P).
Proof.
  intros. simpljoin1.
  infer_solver 6%nat.
Qed.

Lemma mutex_destroy_absimp_iserr:
  forall sch P vmux,
    can_change_aop P ->
    absinfer sch
      (<|| mutex_destroy (vmux :: nil) ||>  ** P)  
      (<|| END (Some (Vint32 (Int.repr EBUSY)))  ||> ** P).
Proof.
  infer_solver 7%nat.
Qed.

Lemma mutex_destroy_absimp_pip_err:
  forall sch a pbls pos muxeibs ow tp rcnt prot prioc wq cnsa P eid els pip o ptls mc,
    (cmpaddr Clt userAddrStart a = true /\ cmpaddr Cle a userAddrEnd = true) ->
    get pbls a = Some pos ->
    (pos = Int.zero \/ Int.ltu Int.zero pos = true) ->
    Int.ltu pos ($ (OS_USER_MAX_EVENTS / 3)) = true -> 
    get muxeibs pos = Some (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    get els eid = Some (absmutexsem pip o, nil) ->
    ~(get ptls pip = Some Holder) ->
    can_change_aop P ->
    absinfer sch
      (<|| mutex_destroy (Vptr a :: nil) ||> 
         ** Hpbls pbls ** HMuxInfo muxeibs ** HECBList els ** HPriotls ptls ** P)  
      (<|| ABORT  ||> 
       ** Hpbls pbls ** HMuxInfo muxeibs ** HECBList els ** HPriotls ptls ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (Hpbls pbls ** HMuxInfo muxeibs ** HECBList els ** HPriotls ptls ** P)) by can_change_aop_solver.
  do 8 (eapply absinfer_trans; try eapply absinfer_choice2; eauto).
  eapply absinfer_trans; try eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  simpljoin1.
  absimp_abt_solver;
  instantiate (3:= s);
  instantiate (2:= mutex_destroy_pip_err (|Vptr a :: nil|));
  sep pauto.
Qed.

Lemma mutex_destroy_absimp_succ:
  forall sch a pbls pos muxeibs ow tp rcnt prot prioc wq cnsa P eid els pip o els' muxeibs' ptls ptls' mc,
    (cmpaddr Clt userAddrStart a = true /\ cmpaddr Cle a userAddrEnd = true) ->
    get pbls a = Some pos ->
    (pos = Int.zero \/ Int.ltu Int.zero pos = true) ->
    Int.ltu pos ($ (OS_USER_MAX_EVENTS / 3)) = true -> 
    get muxeibs pos = Some (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    get els eid = Some (absmutexsem pip o, nil) ->
    get ptls pip = Some Holder ->
    ptls' = set ptls pip Null ->
    join els' (sig eid (absmutexsem pip o, nil)) els ->
    muxeibs' = set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    can_change_aop P ->
    absinfer sch
      (<|| mutex_destroy (Vptr a :: nil) ||>  ** Hpbls pbls ** HMuxInfo muxeibs ** HECBList els ** HPriotls ptls ** P)  
      (<|| END (Some (Vint32 Int.zero))  ||> ** Hpbls pbls ** HMuxInfo muxeibs' ** HECBList els' ** HPriotls ptls' ** P).
Proof.
  intros. simpljoin1.
  infer_solver 9%nat.
  eapply tidsame_trans; [idtac | eapply tidsame_set;eauto].
  eapply tidsame_trans; repeat try eapply tidsame_set; eauto.
Qed.

Lemma evt_not_in_core:
forall eid els,
~ is_sem els eid ->
~ is_que els eid ->
is_que els dynrefcmsgQ_addr ->
CORESEM_INECB_P els ->
notIncoreSemQ eid.
Proof.
intros.
eapply nsem_not_in_core_sem in H; eauto.
simpljoin.
unfolds.
splits; auto.
introv Hf.
inverts Hf.
tryfalse.
Qed.

Lemma PthreadMutexDestroyProof: 
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api pthread_mutex_destroy
              (mutex_destroy,(Tint32,Tptr pthread_mutex_t::nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api pthread_mutex_destroy
              (mutex_destroy,(Tint32,Tptr pthread_mutex_t ::nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api pthread_mutex_destroy = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}.
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  destruct v'; try apply absabort_rule.
  rename x into vmux.
  rename H1 into Hptr.
  
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  assert (Heqf: Int.eq ($ OS_USER_MAX_EVENTS) ($ Int.min_signed) = false).
  eapply int_min_neq_maxevents.
  lets Hrgn': usr_max_evts_rgn'.
  destruct Hrgn' as (Hrgn5 & Hrgn6).
  assert (Hsieq : (Int.signed ($ OS_USER_MAX_EVENTS) / Int.signed ($ 3)) = (OS_USER_MAX_EVENTS / 3)).
  clear -Hrgn5 Hrgn6.
  int auto.
  assert (Hdiveq: (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3) = $ (OS_USER_MAX_EVENTS / 3))).
  { unfold Int.divs in *.
     rewrite zdiv_equiv in *.
     rewrite Hsieq in *.
     auto.
     clear -Hrgn5 Hrgn6. int auto.
     clear. int auto.
  }
  assert (Hchg: Int.eq ($ 3) Int.zero ||
                Int.eq ($ OS_USER_MAX_EVENTS) ($ Int.min_signed) && 
                Int.eq ($ 3) Int.mone = false).
  { rewrite Heqf.
     change (Int.eq ($ 3) Int.zero || false && Int.eq ($ 3) Int.mone) with false.
     auto.
  }

  hoare forward prim.
  hoare_lifts_trms_pre (Aisr, Ais, aemp_isr_is).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  hoare unfold.
  hoare forward.
  pure_auto.
  pure_auto.
  sep cancel p_local. 
  eauto.
  simpl.
  destruct Hptr as [Hptr | (muxv & Hptr)]; subst vmux; eauto.
  unfold aemp_isr_is.
  pure_auto. 
  unfold retpost. introv Hsat.
  inverts Hsat.
  sep destruct H1. sep split in H1. subst. introv Hf. inv Hf.
  sep destruct H1. sep split in H1. subst. introv Hf. inv Hf.
  pure_auto.

  introv Hsat.
  sep pauto. destruct Hsat; sep auto.
  introv Hsat.
  sep pauto. sep cancel p_local. simpl; auto.

  (* end of call to UserAddrCheck *)
  
  hoare unfold. 
  eapply backward_rule1.
  intros. get_hsat Hsat.
  apply disj_split in Hsat. 
  eauto.
  eapply disj_rule.

  (*----------------------------------------- illegal range for mux ---------------------------------------*) 

  hoare unfold.
  inverts H3.

  hoare abscsq.
  eapply noabs_oslinv.
  eapply mutex_destroy_absimp_muxerr; eauto.
  destruct H1 as [Heq | (a & Heq & Hrange)]; inverts Heq; eauto.
  pure_auto.

  lzh_hoare_if.
  (* pos = -1 *) 
  hoare forward.
  change (Int.eq ($ 0) ($ 0)) with true in LHif_false. tryfalse.
  2: { instantiate (1:=Afalse). eapply pfalse_rule. }

  (* If ( pos < 0 || pos >= OS_USER_MAX_EVENTS/3 ) *)
  lzh_hoare_if;
  try (rewrite Hchg);
  simpl;
  pure_auto.
  simpljoin1.
  hoare_lifts_trms_pre (Aisr, Ais,Aier).
   transform_pre add_aemp_isr_is_prop ltac:(idtac).
  hoare forward prim.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel CoreCommuInv.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel PartitionInv.
  sep cancel CapabilityInv.
  eauto.
  auto.
  pure_auto.
  hoare forward.

  change (Int.ltu ($ -1) ($ 0)) with false in Hif_false.
  simpl in Hif_false.
  rewrite Hchg in Hif_false. 
  simpl in Hif_false.
  rewrite Hdiveq in Hif_false.
  change ($ -1) with (Int.mone) in Hif_false.
  assert (Het: Int.ltu ($ OS_USER_MAX_EVENTS / 3) Int.mone = true).
  { clear -Hrgn3 Hrgn4. int auto. }
  rewrite Het in Hif_false.
  simpl in Hif_false.
  assert (Hmf: Int.eq Int.mone ($ OS_USER_MAX_EVENTS / 3) = false).
  { clear -Hrgn3 Hrgn4. int auto. }
  rewrite Hmf in Hif_false.
  simpl in Hif_false.
  change (Int.ltu Int.zero Int.one) with true in Hif_false.
  change (Int.ltu Int.zero Int.zero) with false in Hif_false.
  simpl in Hif_false.
  change (Int.ltu Int.zero Int.one) with true in Hif_false.
  simpl in Hif_false.
  inverts Hif_false; tryfalse.

  (* ------------------------------------------- legal range for mux ----------------------------------- *)
  hoare unfold.
  inverts H3.
  rename x into muxadr.
  rename H4 into Hrgn1.
  rename H5 into Hrgn2.

  unfold EvtInv.
  hoare normal pre.
  hoare_ex_intro.
  rename v'39 into pbls.
  hoare_lifts_trms_pre ( R_Q_Data_P).
  eapply pure_split_rule'; introv Hrqdata.
  hoare unfold.
  assert (Hor: get pbls muxadr = None \/ (exists posv, get pbls muxadr = Some posv)).
  {
    destruct (get pbls muxadr).
    right. eexists. eauto. 
    left. auto.
  }
  destruct Hor as [Hnone | (posv & Hsome)].
  (* get pbls muxadr = None *)
  hoare_lifts_trms_pre (Aop, pblsid). 
  eapply abscsq_rule. 
  apply noabs_oslinv. 
  eapply mutex_destroy_absimp_mux_nopblk_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.

  eapply backward_rule1. 
  introv Hsat.
  sep_lifts_trms_in Hsat APosblkList.
  eapply pos_list_split_frm; eauto.
  unfold node.
  hoare unfold.
  inverts H8. inverts H9.

  lzh_hoare_if.
  {
    change (Int.eq ($ 1) ($ 0)) with false in LHif_true.
    tryfalse. 
  }
  2: { change (Int.eq ($ 1) ($ 0)) with false in Hif_true. tryfalse. }
  hoare_lifts_trms_pre (Aop, Alvarmapsto os_code_defs.pos, Alvarmapsto mutex).
   eapply assign_rule_lvar with (v2:= Vint32 posv).
   split; introv Hsat. eauto. sep auto.
   simpl Astruct. introv Hsat. sep get rv.
   eapply eq_int; auto.
   intros. eexists. sep cancel p_local. simpl; auto.
   match goal with H: get pbls (?v, _) = _ |- _ => rename v into mux_b end.

   (* If ( pos < 0 || pos >= OS_USER_MAX_EVENTS/3 ) *)
  lzh_hoare_if.
  simpl; pure_auto.
  rewrite Hchg; simpl; pure_auto.
  rewrite Hchg; simpl; pure_auto.
  rewrite Hchg; simpl; pure_auto.
  rewrite Hchg; simpl; pure_auto.
  rewrite Hchg; simpl; pure_auto.
  rewrite Hchg; simpl; pure_auto.
  simpl in LHift_true.
  rewrite Hchg in LHift_true; simpl in LHift_true.
  destruct LHift_true as (Ha & Hb & Hc). clear Hb Hc.
  assert (Hif_true:  Int.ltu posv Int.zero = true \/
  Int.ltu (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) posv = true \/ Int.eq posv (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) = true).
  { clear -Ha.
     destruct (Int.ltu posv ($ 0)) eqn: E1; 
     destruct (Int.ltu (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) posv) eqn: E2;
     destruct (Int.eq posv (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))) eqn: E3;
     auto.
   }
  clear Ha.
  rewrite Hdiveq in Hif_true.

  hoare_lifts_trms_pre (Aop, pblsid, A_dom_lenv). 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutex_destroy_absimp_pos_err; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  hoare_lifts_trms_pre (Aisr, Ais,Aier).
  transform_pre add_aemp_isr_is_prop ltac:(idtac).
  hoare forward prim.
  sep cancel tcbdllflag. sep cancel p_local.
  sep cancel CapabilityInv.
  unfold EvtInv.
  sep cancel Aier.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  unfold APosblkList.
  sep pauto.
  eapply pos_sllseg_merge; eauto.
  unfold node.
  sep pauto; eauto.
  sep cancel pos_sllseg. sep cancel Astruct. sep cancel pos_sllseg.
  sep cancel APthreadAttr.
  eauto.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  split; auto. go.
  auto.
  pure_auto.
  (* return ′ EINVAL *) 
  hoare forward.

  simpl in Hif_false0.
  rewrite Hchg in Hif_false0; simpl in Hif_false0.
  assert (Hposrgn:  Int.ltu posv Int.zero = false /\
  Int.ltu (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) posv = false /\ Int.eq posv (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) = false).
  { clear -Hif_false0.
     destruct (Int.ltu posv ($ 0)) eqn: E1; 
     destruct (Int.ltu (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) posv) eqn: E2;
     destruct (Int.eq posv (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))) eqn: E3;
     repeat (try simpl in Hif_false0;
     try change (Int.ltu Int.zero Int.one) with true in *);
     destruct Hif_false0; tryfalse;
     auto.
   }
   rewrite Hdiveq in Hposrgn.
   clear Hif_false0.
   assert (Hposrgn': ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\  Int.ltu posv ($ (OS_USER_MAX_EVENTS / 3)) = true)).
   { clear -Hposrgn Hrgn3 Hrgn4.
      mytac.
      int auto.
      left. mauto.
   }
(*   clear Hposrgn. rename Hposrgn' into Hposrgn. *)
  destruct Hposrgn' as (Hpos_range1 & Hpos_range2).
  lets Hpos_range2': Hpos_range2.
  rewrite Intlt_true_is_Zlt in Hpos_range2'.
   (* compose pos list *)
  eapply backward_rule1. introv Hsat.
  eapply pos_sllseg_merge; eauto.
  unfold node.
  sep pauto; eauto.
  sep cancel pos_sllseg. sep cancel Astruct. sep cancel pos_sllseg.
  eauto.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  split; auto. go.
  hoare_lifts_trms_pre (pos_sllseg, GJB_pos_list).
  eapply backward_rule1.
  introv Hsat.
  match type of Hsat with
    _ |= _ ** _ ** ?P => instantiate (1:=APosblkList pbls ** P)
  end.
  unfold APosblkList. sep auto.
  (* split (Pthread_Mutex ′ [os_code_defs.pos ′]) *)
  unfold AMuxEIBs.
  hoare_lifts_trms_pre APthreadMutex.
  hoare normal pre.
  eapply ex_intro_rule; intro lmux.
  destruct lmux as (lmux_b & lmux_i).
   match goal with
    | |- {| _ , _, _, _, _, _ |} |- _ {{ APthreadMutex _ ?vl ** _ }} _ {{ _ }} =>
       hoare_assert_pure (length vl = (∘ (OS_USER_MAX_EVENTS / 3)))
    end.
 {   get_hsat Hsat. sep_lifts_trms_in Hsat APthreadMutex.  eapply apthreadmutex_len_frm; eauto.  }
 eapply pure_split_rule'; introv Hl.

  hoare_lifts_trms_pre (MuxCapArray_P, (OS_USER_MAX_EVENTS / 3)).
  eapply pure_split_rule'; introv Hmcap.
  eapply pure_split_rule'; introv Hlen_mcap.
  hoare unfold.
  eapply backward_rule1.
  introv Hsat.
   sep_lift_context_in Hsat APthreadMutex.
  eapply APthreadMutex_unfold_any_idx_frm with (idx:=∘(Int.unsigned posv)); eauto.
  clear -Hl Hpos_range2' Hrgn3 Hrgn4 Hdiveq.
  rewrite Hl.
  unfold nat_of_Z.
  clear -Hpos_range2' Hrgn3 Hrgn4.
  int auto.
  hoare unfold.
  (* unfold the vallist of  efield (Pthread_Mutex ′ [pos ′]) *)
  match goal with H: new_array_type_vallist_match pthread_mutex_info_t (_ ++ ?vl :: _) |- _ =>
  rename vl into muxvl;
  lets Hsplit: H end.  (* new_array_type_vallist_match ... *)
  eapply new_array_type_vallist_match_split1 in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_10 Hsp.
  repeat try (destruct Hvl as (? & Hvl)). subst muxvl.

  assert (Hpos_range3: Int.unsigned posv <= Int.max_signed).
  { clear -Hpos_range1 Hpos_range2 Hrgn3 Hrgn4.
    int auto.
  }
  match goal with H: EIBMAarray_P _ (?vl1 ++ _) _ _, H': length ?vl1 = _ |- _ =>
  lets H00: muxb_corr H H' end.
  match type of H00 with _ -> _ -> ?R => assert (R); [apply H00 | ] end.
  auto.
  clear -Hpos_range1 Hpos_range2 Hrgn3 Hrgn4.
  int auto.
  clear H00.
  destruct H17 as (eid_t & ow & tp & rcnt & prot & prioc & wq & cnsa & mc &(Hget & Heidor & Hvow)).
  destruct Hvow as (Hvow & Hvtp & Hvrcnt & Hvprioc & Hvprot & Hvwq & Hvcnsa).
  inverts Hvtp. inverts Hvrcnt. inverts Hvprioc. inverts Hvprot. inverts Hvwq. inverts Hvcnsa.

  assert (Hptr_p: isptr x3).
  { clear -Heidor.
     unfold isptr. unfold V_OSMUXINFOPevent in *.
     simpl in *.
     destruct Heidor as [(_ & Heq) | [(_ & Heq) | (eid & _ & Heq & _)]];
     inverts Heq; eauto.
  }
  unfold V_OSMUXINFOPevent in Heidor; simpl in Heidor.

  (* p ′ =ₑ efield (Pthread_Mutex ′ [os_code_defs.pos ′]) pevent;ₛ *)
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply assign_rule_lvar.
  split; introv Hsat. sep cancel (Alvarmapsto p). eauto.
  sep auto.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  eapply eq_vptr; eauto.
  intros. eexists. sep cancel p_local. simpl; eauto.
  simpl nth_val'.
  (* If (p ′ ==ₑ NULL)  *)
  lzh_hoare_if.
(*   hoare forward. *)
  clear -Hptr_p; pure_auto.
  clear -Hptr_p; pure_auto.
  subst x3.
  destruct Heidor as [(Heq & _) | [(_ & Heq) | (eid & _ & Heq & _)]];
  inverts Heq.
  hoare_lifts_trms_pre (Aop, pblsid, absmutinfoid). 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutex_destroy_absimp_pevent_null_err; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  hoare_lifts_trms_pre (Aisr, Ais,Aier).
  transform_pre add_aemp_isr_is_prop ltac:(idtac).
  hoare forward prim.
  sep cancel tcbdllflag. sep cancel p_local.
  sep cancel CapabilityInv.
  unfold EvtInv.
  unfold AMuxEIBs.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMqEIBs.
  sep cancel APthreadAttr.
  eapply APthreadMutex_select_sn_ex_strong.
  eexists. exists (∘ (Int.unsigned posv)). eexists.
  exists (Vint32 tp :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: x0 :: Vint32 rcnt :: x2 :: Vnull :: x4 :: nil). 
  sep pauto.
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel Aier.
  eauto.
  auto.
  auto.
  pure_auto.
  (* RETURN ′ EINVAL *)
  hoare forward.

  (* p is not holder *)
  assert (Hp: x = vhold_addr \/ x <> vhold_addr) by tauto.
  destruct Hp as [Hhold | Hp_eq].
  subst x.
  destruct Heidor as [(_ & Heq) | [(Heq & _) | (eid & _ & Heq & Hf)]];
  inverts Heq; tryfalse.
  hoare_lifts_trms_pre (Aop, pblsid, absmutinfoid). 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutex_destroy_absimp_pevent_holder_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.

  (* p is a valid ptr *)
  destruct Heidor as [(_ & Heq) | [(_ & Heq) | (eid & Hed & Heq & _)]];
  inverts Heq; tryfalse.
  subst eid_t.
  match goal with H: RH_ECBlk_EIBlk_Mux_P _ _ |- _ =>
  rename H into Hreibecb end.
  lets Hecb: Hreibecb Hget.
  specialize (Hecb (eq_refl _)).
  destruct Hecb as (pip & o & wls & Hgetecb).
  (* split ecb list *)
   unfold AECBList.
   hoare unfold.
   lets Help': H8.
  rename H8 into H_elp. (* ECBList_P ... *)
  lets Hctr: ECBList_P_get_ectr_some Hgetecb H_elp. 
  destruct Hctr as (evl & etbl & petbl & Hgetectr).
  
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat evsllseg.
  eapply get_ectr_decompose; eauto.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  hoare unfold.
  match goal with H: ECBList_P _ _ (?vl1 ++ _) (?vl2 ++ _) _ _ |- _ =>
  hoare_assert_pure (length vl1 = length vl2) end.
  {
    get_hsat Hsat. 
    sep_lifts_trms_in Hsat evsllseg.
    eapply evsllseg_aux in Hsat.
    destruct Hsat.
    eauto.
  }
  eapply pure_split_rule'; introv Heqlen.
  eapply ecblist_p_decompose in H_elp; eauto. 
  destruct H_elp as (x' & els1 & els2 & H'').
  destruct H'' as (Hecbl1 & Hecbl2 & Hjo & Hglast).

  match goal with H: get_ectr (Vptr (?b, _)) _ _ = None |- _ => rename  b into eid_b end.
  hoare_assert_pure (x' = Vptr (eid_b, Int.zero)).
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg.
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  hoare_split_pure_all; subst.

  hoare_assert_pure (i1 = (Int.repr OS_EVENT_TYPE_MUTEX)).
     { destruct (Int.eq i1 (Int.repr OS_EVENT_TYPE_MUTEX)) eqn: eq_tp.
        eapply inteqeq in eq_tp; subst; auto.
        simpl in Hecbl2.
        mytac.
        inverts H23.
        get_hsat Hsat.
        sep_lifts_trms_in Hsat (AEventData).
        eapply eventtype_neq_mutex in Hsat; eauto.
        sep split in Hsat.
        false.
        apply H8; eauto.
     }
    hoare_split_pure_all; subst.

(* If (′ OS_USER_MAX_EVENTS ÷ ′ 3 ÷ Core_partition_num ′
    × Domain2Index ′ [ksCurDomain ′] >ₑ os_code_defs.pos ′
    ||ₑ os_code_defs.pos ′
        ≥ ′ OS_USER_MAX_EVENTS ÷ ′ 3 ÷ Core_partition_num ′
          × (Domain2Index ′ [ksCurDomain ′] +ₑ ′ 1))
{EXIT_CRITICAL;ₛ
RETURN ′ (-1)};ₛ *)
  match goal with
  | |- {| _, _, _, _, _, _ |} |- _  {{ ?P }} _ {{ _ }} =>
  eapply seq_rule with (p':= P)
  end.
  unfold PartitionInv.
  unfold Adomain2index.
  unfold Adomain2index'.
  unfold AKsCurDomain.
  unfold ACorepartnum.
  unfold ACorepartnum'.
  hoare unfold.
  match goal with
  H: R_Cpartnum_Dom2idx_P ?v _ , H1: RHL_Dom2idx_P _ ?abs,
  H2: 0 <= Int.unsigned ?vdom < DOMAIN_SIZE \/ ?vdom = Int.mone |- _ =>
  rename v into cpn; rename abs into domls; rename vdom into vcurd end.

  hoare_lifts_trms_pre (Aop, kscurdom).
  assert(Hvcurd : vcurd = Int.mone \/ vcurd <> Int.mone) by tauto.
  destruct Hvcurd as [Habt | Hvcurd].
  eapply abscsq_rule.
  apply noabs_oslinv.
  do 5 try (eapply absinfer_trans; [ eapply absinfer_choice2; eauto; try can_change_aop_solver | idtac]).
  eapply absinfer_choice1; eauto; try can_change_aop_solver.
  eapply absinfer_eq.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_kscurdom_ext_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.
  match goal with H: _ \/ vcurd = Int.mone |- _ => destruct H as [Hcd_rgn | Hf]; try subst; tryfalse end.
  destruct Hcd_rgn as (Hcd_pos & Hcd_lt).
  hoare_lifts_trms_pre (Aop, Domain2Index, ksCurDomain).
  match goal with
  | H: length ?vl = ?len
    |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** _ Domain2Index _ ?vl ** GV ksCurDomain @ _ |-> Vint32 ?idx ** _ }} _ {{ _ }} =>
     rename H into Hlen; assert (Hle_len: (Z.to_nat (Int.unsigned idx) < len)%nat)
  end.
  solve_part_int_rgn.
  lets Hnth: Hle_len.
  eapply pure_lib.nthval'_has_value in Hnth; eauto.
  destruct Hnth as (rv_dom & Hnth & Hmat).
  hoare_lifts_trms_pre (Aop, kscurdom, domindexlist).
  match goal with
  H: RLH_Dom2idx_P _ _ |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** _ ** HDomain2index ?absdomls ** _ }} _ {{ _ }} =>
  rename H into Hlh_dom
  end.
  assert (Hget_dom:get domls  vcurd = Some rv_dom).
  eapply Hlh_dom; eauto.
  eapply inline_bittblfunctions.nth_val'2nth_val; eauto.

  assert (Heqf': Int.eq ($ OS_USER_MAX_EVENTS / 3) ($ Int.min_signed) = false).
  { clear. lets Hrgn: usr_max_evts_rgn.
    destruct Hrgn as (Hrgn3 & Hrgn4).
    unfold nat_of_Z in *.
    unfold Int.eq.
    rewrite Int.unsigned_repr.
    2:{ split; solve_usr_max_evts_rgn. }
    destruct (zeq (OS_USER_MAX_EVENTS / 3) (Int.unsigned ($ Int.min_signed))); auto.
    change (Int.unsigned ($ Int.min_signed)) with 2147483648  in *.
    rewrite e in Hrgn4.
    false. auto with zarith.
  }
  assert (Hif_cpn: Int.eq cpn Int.zero || Int.eq ($ OS_USER_MAX_EVENTS / 3) ($ Int.min_signed) &&
                                Int.eq cpn Int.mone = false).
  { rewrite Heqf'.
     destruct (Int.eq cpn Int.zero) eqn: eq1; try tauto.
     eapply sem_lab.semacc_int_eq_true in eq1; subst.
     change (Int.unsigned Int.zero) with 0 in *.
     false; auto with zarith.
  }
  eapply forward_rule1.
  2:{
  eapply ift_rule''.
  introv Hsat.
  sep get rv; 
  (* hoare forward;  *)try rewrite Hchg; try rewrite Hdiveq; try rewrite Hnth; simpl val_inj.
  pure_auto.
  rewrite Hif_cpn; simpl val_inj; pure_auto.
  solve_part_int_rgn.
  auto.
  rewrite Hif_cpn; simpl val_inj; pure_auto.
  rewrite Hif_cpn; simpl val_inj; pure_auto.
  pure_auto.
  rewrite Hif_cpn; simpl val_inj; pure_auto.
  solve_part_int_rgn.
  auto.
  pure_auto.
  rewrite Hif_cpn; simpl val_inj; pure_auto.
  rewrite Hif_cpn; simpl val_inj; pure_auto.
  pure_auto.
  rewrite Hif_cpn; simpl val_inj; pure_auto.
  solve_part_int_rgn.
  auto.
  pure_auto.
  rewrite Hif_cpn; simpl val_inj; pure_auto.
  rewrite Hif_cpn; simpl val_inj; pure_auto.
  rewrite Hif_cpn; simpl val_inj; pure_auto.
  rewrite Hif_cpn; simpl val_inj; pure_auto.
  try rewrite Hchg; try rewrite Hdiveq; try rewrite Hnth; simpl val_inj.
  rewrite Hif_cpn; simpl val_inj.
  hoare_lifts_trms_pre val_inj.
  eapply pure_split_rule'; introv Hval_inj.
  assert (Hif_part_pos: Int.ltu posv (Int.mul (Int.divs (Int.repr (OS_USER_MAX_EVENTS / 3)) cpn) rv_dom) = true \/
        Int.ltu posv (Int.mul (Int.divs (Int.repr (OS_USER_MAX_EVENTS / 3)) cpn) (Int.add rv_dom Int.one)) = false).
  { clear - Hval_inj.
     destruct Hval_inj as (Hval_inj & _).
     destruct (Int.ltu posv (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn) rv_dom)) eqn: eq1; auto.
     right.
     rewrite Intlt_false_is_Zge.
    destruct (Int.ltu (Int.mul  (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn)  (rv_dom +ᵢ  $ 1)) posv) eqn: eq2;
    destruct (Int.eq posv  (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn) (rv_dom +ᵢ  $ 1))) eqn: eq3;
    simpl val_inj in Hval_inj; 
    repeat (try change (Int.ltu Int.zero Int.zero) with false in *; 
                      try change (Int.ltu Int.zero Int.one) with true in *; simpl in *);
    tryfalse;
    try (eapply sem_lab.semacc_int_eq_true in eq3; subst);
    try eapply sem_lab.semacc_int_eq_false in eq3;
    try rewrite Intlt_false_is_Zge in eq2; 
    try rewrite Intlt_true_is_Zlt in eq2;
    auto with zarith.
    eapply Z.le_ge.
    eapply Z.lt_le_incl; eauto.
  }
  clear Hval_inj.
  hoare_lifts_trms_pre (Aop, kscurdom).
  eapply abscsq_rule.
  apply noabs_oslinv.
  do 5 try (eapply absinfer_trans; [ eapply absinfer_choice2; eauto; try can_change_aop_solver | idtac]).
  eapply absinfer_choice1; eauto; try can_change_aop_solver.
  eapply absinfer_eq.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_kscurdom_ext; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  hoare_lifts_trms_pre (Aop,pblist, kscurdom, domindexlist, cpartnum).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_partition_pos_out_of_rgn_err; eauto.
  can_change_aop_solver.
  rewrite Hdiveq; auto.
  eapply absinfer_eq.
  instantiate (1:= Afalse).
  hoare_lifts_trms_pre (Aisr, Ais, Aier).
  transform_pre add_aemp_isr_is_prop ltac:(idtac).
  hoare forward prim.
  sep cancel CoreCommuInv.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel APthreadAttr.
  sep cancel Aier.
  unfold EvtInv.
  unfold AMuxEIBs.
  unfold AECBList.
  unfold AGVars.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMqEIBs.
  sep_lifts_trms evsllseg.
  eapply evsllseg_compose; eauto.
  unfolds; simpl; eauto.
  sep cancel evsllseg.
  sep cancel evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto; eauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel AOSPostEventTbl.
  eapply APthreadMutex_select_sn_ex_strong.
  sep pauto; eauto.
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel Astruct.
  sep cancel CapabilityInv.
  unfold PartitionInv.
  unfold Adomain2index.
  unfold Adomain2index'.
  unfold AKsCurDomain.
  unfold ACorepartnum.
  unfold ACorepartnum'.
  sep pauto; eauto.
  split; auto. go.
  auto.
  pure_auto.
  (* RETURN ′(-1) *)
  hoare forward.
  }
  introv Hsat.
(*   get_hsat Hsat. *)
  destruct Hsat as [Hsat | Hsat].
  eapply astar_l_afalse_elim in Hsat; simpl in Hsat; tryfalse.
  sep_lifts_trms_in Hsat val_inj.
  eapply sep_pure_split in Hsat; destruct Hsat as (Hval_inj & Hsat).
  clear Hval_inj.
  sep cancel Aop.
  sep cancel Aier.
  sep cancel p_local.
  trycancel.
  sep auto; eauto.

  (* If ((efield (Pthread_Mutex ′ [os_code_defs.pos ′]) pevent) → OSEventGrp
    !=ₑ ′ 0 ||ₑ OSIntNesting ′ >ₑ ′ 0) *)
   unfold AGVars.
   hoare unfold.
   rename H8 into Hgv_rgn1; rename H23 into Hgv_rgn2.
   rename v'67 into vnest.
   eapply seq_rule.
   eapply lzh_if_then_rule.
   introv Hsat.
   eapply bop_rv; eauto.
   { (* Rv (efield (Pthread_Mutex ′ [os_code_defs.pos ′]) pevent) → OSEventGrp *)
      eapply uop_rv; eauto.
      eapply bop_rv; eauto.
      sep_get_rv_array_struct'.
      rewrite Hdiveq; eauto.
      rewrite Hdiveq; eauto.
      simpl; eauto.
      sep get rv.
      simpl; pure_auto.
      simpl; pure_auto.
      simpl; pure_auto.
      simpl; pure_auto.
    }
   sep get rv.
   pure_auto.
   simpl; pure_auto.
   simpl; pure_auto.
   (* process if conditon *)
   hoare unfold.
   simpl in H8.
   instantiate (1:= Afalse).
   change ($ 0) with Int.zero in H8.
   assert (Hif_true: Int.eq i0 Int.zero = false \/ Int.ltu Int.zero vnest = true). (* change i -> i0 *)
   { clear -H8.
      destruct (Int.eq i0 Int.zero) eqn: eq1; (* change i -> i0 *)
      destruct (Int.ltu Int.zero vnest) eqn: eq2;
      simpl in *; auto.
   }
   clear H8 H23 H28.
   hoare_lifts_trms_pre (Aop, pblsid, absmutinfoid, absecblsid). 
   destruct Hif_true as [Hgrp_nzero | Hiserr].
   2: {
          eapply abscsq_rule.
          apply noabs_oslinv.
          eapply mutex_destroy_absimp_iserr; eauto.
          can_change_aop_solver.
          eapply absinfer_eq.
          hoare_lifts_trms_pre (Aisr, Ais,Aier).
          transform_pre add_aemp_isr_is_prop ltac:(idtac).
          hoare forward prim.
          sep cancel tcbdllflag.
          sep cancel p_local.
          unfold EvtInv.
          unfold AMuxEIBs.
          unfold AECBList.
          unfold AGVars.
          sep pauto; eauto.
          trycancel.
           sep cancel ASemEIBs.
           sep cancel AMqEIBs.
           sep_lifts_trms evsllseg.
           eapply evsllseg_compose; eauto.
           unfolds; simpl; eauto.
           sep cancel evsllseg.
           sep cancel evsllseg.
           unfold AEventNode.
           unfold AOSEvent.
           unfold node.
           unfold AOSEventTbl.
           sep pauto; eauto.
           sep cancel Astruct.
           sep cancel Aarray.
           sep cancel AOSPostEventTbl.
           eapply APthreadMutex_select_sn_ex_strong.
           sep pauto; eauto.
           sep cancel Aarray_new.
           sep cancel Aarray_new.
           sep cancel Astruct.
           sep cancel APthreadAttr.
           sep cancel CapabilityInv.
           eauto.
           split; auto. go.
           auto.
           pure_auto.
          (* RETURN ′ EBUSY *)
          hoare forward.
         }
     assert (Hwls_nnil: wls <> nil).
     {  assert (Hgetecb': exists z zz t' tl, EcbMod.get v'11 (eid_b, Int.zero) = Some (absmutexsem z zz, t' :: tl)).
         { simpl in Hecbl2.
            mytac.
            inverts H8.
            eapply ecb_wt_ex_prop_mutex; eauto.
          }
          destruct Hgetecb' as (pip' & o' & t' & tl & Hgetecb').
          clear -Hgetecb Hgetecb'.
          unfold get in *. unfold EcbMap in *.
          rewrite Hgetecb in Hgetecb'; inverts Hgetecb'.
          pure_auto.
      }
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutex_destroy_absimp_waiting_tasks_err; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
    hoare_lifts_trms_pre (Aisr, Ais,Aier).
    transform_pre add_aemp_isr_is_prop ltac:(idtac).
    hoare forward prim.
    sep cancel tcbdllflag.
    sep cancel p_local.
    unfold EvtInv.
    unfold AMuxEIBs.
    unfold AECBList.
    unfold AGVars.
    sep pauto; eauto.
    trycancel.
    sep cancel ASemEIBs.
    sep cancel AMqEIBs.
    sep_lifts_trms evsllseg.
    eapply evsllseg_compose; eauto.
    unfolds; simpl; eauto.
     sep cancel evsllseg.
     sep cancel evsllseg.
     unfold AEventNode.
     unfold AOSEvent.
     unfold node.
     unfold AOSEventTbl.
     sep pauto; eauto.
     sep cancel Astruct.
     sep cancel Aarray.
     sep cancel AOSPostEventTbl.
     eapply APthreadMutex_select_sn_ex_strong.
     sep pauto; eauto.
     sep cancel Aarray_new.
     sep cancel Aarray_new.
     sep cancel Astruct.
     sep cancel APthreadAttr.
     sep cancel CapabilityInv.
     eauto.
     split; auto. go.
     auto.
     pure_auto.
     (* RETURN ′ EBUSY *)
     hoare forward.
     hoare forward.
     hoare unfold.
     apply pfalse_rule.
     hoare unfold.
     assert (Hif_cond: Int.eq i0 Int.zero = true /\ Int.ltu Int.zero vnest = false).
   { clear -H8.
      change ($ 0) with Int.zero in H8.
      simpl in H8.
      destruct (Int.eq i0 Int.zero) eqn: eq1;
      destruct (Int.ltu Int.zero vnest) eqn: eq2;
      simpl in *; auto;
      try change (Int.notbool Int.one) with Int.zero in *;
      try change (Int.ltu Int.zero Int.one) with true in *;
      try change (Int.ltu Int.zero Int.zero) with false in *;
      simpl in *; destruct H8; tryfalse.
   }
   clear H8.
   destruct Hif_cond as (Hgrp_zero & Hnest).
   eapply inteqeq in Hgrp_zero; subst i0.
   hoare_assert_pure (R_PrioTbl_P v' v'12 vhold_addr).
   { get_hsat Hsat.
      unfold AOSTCBPrioTbl in Hsat.
      sep split in Hsat.
      auto.
    }
   hoare_split_pure_all.
   rename H8 into Hrptbl.
   assert (Hwls_nil: wls = nil).
   { simpl in Hecbl2.
      mytac.
      inverts H8.
      lets Hgetecb': H42.
      eapply EcbMod.join_sig_get in Hgetecb'.
      eapply EcbMod.join_get_r in Hgetecb'; eauto.
      unfold get in Hgetecb; unfold EcbMap in Hgetecb.
      rewrite Hgetecb in Hgetecb'; inverts Hgetecb'.
      eapply post_exwt_succ_pre_mutex'; eauto.
    }
   subst wls.
   (* p ′ =ₑ efield (Pthread_Mutex ′ [os_code_defs.pos ′]) pevent;ₛ  *)
   hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply assign_rule_lvar.
  split; introv Hsat. sep cancel (Alvarmapsto p). eauto.
  sep auto.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  eapply eq_vptr; eauto.
  intros. eexists. sep cancel p_local. simpl; eauto.
  simpl nth_val'.
  (* efield (Pthread_Mutex ′ [os_code_defs.pos ′]) pevent =ₑ 
〈 OS_EVENT ∗ 〉 NULL;ₛ*)
  eapply seq_rule.
  hoare_assign_array_struct.
  match goal with H: MUX_ECB_P ?loc ?ptr ?ecb ?fecbh ?fecbvl ?sem ?mux ?mq |- _ =>
  rename loc into locmp; rename ptr into ptrmp; rename ecb into ecbls;
  rename sem into semeibs; rename mux into muxeibs; rename mq into mqeibs
  end.
  assert (Heibref: eib_ref semeibs muxeibs mqeibs (eid_b, Int.zero)).  
  {
    unfold eib_ref. right. left.
    unfold muxeib_ref. repeat eexists; eauto.
  }
  assert (Hncre1: ~exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre1 (eid_b, Int.zero)).  
  {
    eapply eib_ref_no_tsk_cre1; eauto. 
  }
  assert (Hncre2: ~exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre2 (eid_b, Int.zero)).  
  {
    eapply eib_ref_no_tsk_cre2; eauto. 
  }
  assert (Hndel: ~exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbdel (eid_b, Int.zero)).
  {
    eapply eib_ref_no_tsk_del; eauto. 
  }
  match goal with H: ECBList_P _ _ (_ ++ ((_ :: _ :: ?vcnt :: ?vp :: _, _ , _) :: _) ++ _) (_ ++ (?data :: _) ++ _) _ _ |- _ =>
  rename data into vdata; 
  hoare_assert_pure (vdata = DMutex vcnt vp) end.
  {
    get_hsat Hsat. 
    unfold AEventData in Hsat.
    destruct vdata;
    unfold V_OSEventType in Hsat; simpl nth_val in *;
    sep split in Hsat; tryfalse.
    inverts H23. inverts H28.
    auto.
  }
  hoare_split_pure_all.
  subst vdata.
  (* OSMutexDel (­ p ′­);ₛ *)
  unfold AOSTCBPrioTbl.
  hoare unfold.
  lets Hecbl2': Hecbl2.
  simpl in Hecbl2'.
  mytac.
  inverts H43.
  inverts H46.
  lets Hgetecb': H47.
  eapply EcbMod.join_sig_get in Hgetecb'.
  eapply EcbMod.join_get_r in Hgetecb'; eauto.
  unfold get in Hgetecb; unfold EcbMap in Hgetecb.
  rewrite Hgetecb in Hgetecb'; inverts Hgetecb'.
  rename H40 into Hr_etbl.
  rename H45 into Hr_prtbl.
  destruct H48 as (Hmat_mux & Hrh_ecb).
  rename H49 into Hecbl2_right.
  (* new add *)
  unfold AOSPostEventTbl.
  hoare unfold.
  inverts H26.
  match goal with
   H: os_inv.id_addrval' _ OSEventTbl OS_EVENT = Some ?v1, 
   H': os_inv.id_addrval' _ OSPostEventTbl OS_EVENT = Some ?v2 |- _ =>
  rename v2 into lpetbl; rename v1 into letbl end.
  (* end of new add *)
  hoare forward.
  sep cancel Aarray.
  sep cancel evsllseg.
  sep cancel evsllseg.
  sep cancel AOSEventFreeList.
  sep cancel (Astruct (eid_b, Int.zero)).
  sep cancel Aarray.
  eauto.
  auto.
  auto.
  auto.
  auto.
  change (Byte.max_unsigned) with 255; auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  eauto.
  eauto.
(*   auto. *)
  eauto.
  instantiate(1:= (absmutexsem pip o, nil)).
  simpl; eauto.
  unfold AEventData. pure_auto.
  introv Hsat.
  exists init_lg. sep destruct Hsat. sep cancel p_local. sep auto.
  introv Hsat.
  exists init_lg. sep destruct Hsat. sep cancel p_local. sep auto.

  hoare unfold.
  inverts H26. (* logic_code ... :: ... = logic_code ... :: ... *)
  match goal with H: _ = _ -> Vptr (?v, Int.zero) = _ /\ _ /\ _ |- _ =>
  rename v into eid_b end.

  assert (Hupd: (Vint32 tp :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: x0 :: Vint32 rcnt :: x2 :: Vnull :: x4 :: nil) =
                update_nth_val 8 (Vint32 tp :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: x0 :: Vint32 rcnt :: x2 :: Vptr (eid_b, Int.zero) :: x4 :: nil) Vnull).
  {
    simpl. auto.
  }
  match goal with  | |- {| _ , _, _, _, _, _ |} |- ?t {{ _ }} _ {{ _ }} => rename t into ct end.
  hoare_assert_pure (get ptrmp ct = Some (Vnull, Vnull, Vnull)).
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat (tcbllsegevaux,AOSTCBList, p_local).
    eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
    sep normal in Hsat.
    sep destruct Hsat.
    sep split in Hsat.
    subst.
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  hoare_split_pure_all.
  rename H26 into Hgetauxp.

  assert (Hnsref: ~semeib_ref semeibs (eid_b, Int.zero)).
  { 
    eapply eibref_distinct_muxref_nsemref; eauto.
    unfold muxeib_ref. repeat eexists; eauto.
  }
  assert (Hnqref: ~mqeib_ref mqeibs (eid_b, Int.zero)).
  {
    eapply eibref_distinct_muxref_nmqref; eauto.
    unfold muxeib_ref. repeat eexists; eauto.    
  }
(*   lets Hpip_eq: mutexdel_int H30. *)
(*   rewrite Hpip_eq. *)
  lets Hcp: Hmat_mux.
  funfold Hcp.
  inverts H26.
  rename x into cnt.
  lets Hcp: Hrh_ecb.
  funfold Hcp.
  rename H61 into Hpip_range.

  match goal with
  H: RH_PrioTbl_P ?ptbl0 ?ptls0 _,
  H': R_PrioTbl_P ?ptbl0 ?tls0 _,
  H'': RL_RTbl_PrioTbl_P ?rtbl0 ?ptbl0 _ |- _ =>
  rename ptbl0 into ptbl; rename rtbl0 into rtbl; rename tls0 into tls; rename ptls0 into ptls end.

  assert (Hjo_new: join (sig (eid_b, Int.zero) (absmutexsem (cnt >>ᵢ $ 8) o, nil)) 
                                                 (merge els1 x6) ecbls).
  { eapply join_join_merge'_ecb; eauto.
     eapply EcbMod.map_join_comm; eauto.
  }
  lets Hjo_new': EcbMod.map_join_comm Hjo_new.
  hoare_lifts_trms_pre (Aop, pblsid, absmutinfoid, absecblsid,absptlsid).
  assert (Hpip_case: get ptls (cnt >>ᵢ $ 8) = Some Holder \/ ~(get ptls (cnt >>ᵢ $ 8) = Some Holder)) by tauto.
  destruct Hpip_case as [Hget_ptls | Hf ].
  2: {  eapply abscsq_rule.
            apply noabs_oslinv.
            eapply mutex_destroy_absimp_pip_err; eauto.
            pure_auto.
            eapply absinfer_eq.
            apply absabort_rule.
        }

   assert (Hpip_available: prio_available (cnt >>ᵢ $ 8) tls).
   { eapply RH_PrioTbl_P_prio_available; eauto. }
  assert (Hpip_range': 0 <= Int.unsigned (cnt >>ᵢ $ 8)  < 64).
  { clear -Hpip_range; int auto. }

  hoare_assert_pure (notIncoreSemQ (eid_b, Int.zero)).
  { get_hsat Hsat.
     sep_lifts_trms_in Hsat CoreCommuInv.
     sep remember (1 :: nil)%nat in Hsat.
     clear HeqH61.
     unfold CoreCommuInv in Hsat; unfold DynamicRefactorINV in Hsat.
     sep normal in Hsat; sep destruct Hsat.
     sep split in Hsat.
     eapply evt_not_in_core; eauto.
     unfold is_sem. introv Hf. destruct Hf as (n_ & wls_ & Hf).
     unfold get in Hf; simpl in Hf.
     rewrite Hgetecb in Hf; tryfalse.
     unfold is_que. introv Hf. destruct Hf as (n1_ & n2_ & n3_ & wls_ & Hf).
     unfold get in Hf; simpl in Hf.
     rewrite Hgetecb in Hf; tryfalse.
   }
  eapply pure_split_rule'; introv Hmux_nc.

  match goal with 
    H: ECBList_P _ (Vptr (eid_b, Int.zero)) ?l _ _ _ |- _ => 
    assert (Hnilor: l = nil \/ l <> nil) by tauto
  end.
  destruct Hnilor as [Hnil | Hnnil].

  (* the event list before pevent is nil *)
  subst.
  simpl in Hecbl1.
  simpljoin1. subst.
  assert (els2 = ecbls).
  { clear -Hjo. join auto. }
  subst ecbls.

  eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutex_destroy_absimp_succ; eauto.
   pure_auto.
   eapply absinfer_eq.

  specialize (H50 (eq_refl _)). simpljoin1.
  assert (Hmerge_eq: forall els2, merge EcbMod.emp els2 = els2).
  { join auto. }
  erewrite Hmerge_eq in *.

  hoare_lifts_trms_pre (Aisr, Ais,Aier).
  transform_pre add_aemp_isr_is_prop ltac:(idtac).
  hoare forward prim.
  sep cancel p_local.
  sep cancel tcbdllflag.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv. 
  unfold EvtInv.
  unfold AOSIntNesting  in *.
  unfold AGVars.
  unfold AOSEventFreeList.
  unfold AECBList.
  sep pauto; eauto.
  get_hsat Hsat.
  rewrite nil_simp in Hsat.
  sep cancel evsllseg.
  unfold ecbf_sll.
  sep_lifts_trms_in Hsat (OS_EVENT_TYPE_UNUSED, ecbf_sllseg).
  match goal with H: _ |= Astruct _ OS_EVENT ?vl ** ecbf_sllseg _ _ ?vl' OS_EVENT _ ** _ |- _ =>
  instantiate (12:= vl :: vl') end.
  unfold_ecbfsll.
  sep pauto.
  sep cancel Astruct.
  sep cancel ecbf_sllseg.
  sep cancel Aarray.
  sep cancel Aarray.
  2: { eauto. }
  2: { auto. }
  2: { unfolds; simpl; auto. }
  2: { split. auto. go. }
  (* 2: { rewrite nil_simp; auto.  } *)
  6: { eapply ecb_del_prop_RHhold; eauto.
          introv Hf; destruct Hf as (qd & wt & pqwl & Hf & _); inverts Hf. }

  trycancel.
  unfold AMuxEIBs.
  sep normal. sep eexists. sep split; eauto.
  sep cancel AMuxCap.
  sep_lifts_trms APthreadMutex.
  eapply APthreadMutex_select_sn_ex_strong ; eauto.
  sep eexists.
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel Astruct.
  sep pauto; eauto.
  2: {
    rewrite <- Hl.
    rewrite app_length. rewrite app_length.
    eapply f_equal2_plus; eauto.
  }
  2: {
    apply new_array_type_vallist_match_compose_struct; eauto.
  }
  sep_lifts_trms_in Hsat ASemEIBs.
  eapply asemeib_delmux_preserve in Hsat; eauto.
  sep cancel ASemEIBs.
  sep_lifts_trms_in Hsat AMqEIBs. 
  eapply mqeib_delmux_preserve in Hsat; eauto.
  sep cancel AMqEIBs.
  cancel_corecommuinv.
  unfold AOSTCBPrioTbl.
  sep pauto.
  (* PartitionInv *)
  Require Import sem_partition.
  cancel_partitioninv.
  eauto.
  (* end of PartitionInv *)

  eapply RH_PrioTbl_P_update_null; eauto.
  eapply R_Prio_Tbl_P_hold_for_del_gen; eauto.
  clear -H41. funfold H41; eauto.
  eapply RL_RTbl_PrioTbl_P_hold_for_del_gen; eauto.
  clear -H41. funfold H41; eauto.
  eapply mux_einfo_ecb_delmux_preserve; eauto.
  (* MuxCapArray_P *)
  eapply MuxCapArray_P_hold; eauto.
  {
    rewrite Hupd.
    eapply EIBMAarray_P_hold_for_update_to_null'; eauto.
    apply Int.unsigned_range_2.
  }
  eapply eibref_distinct_muxdel_preserve; eauto.
  eapply mq_ecb_p_muxdel_preserve; eauto.
  eapply mux_ecb_p_muxdel_preserve; eauto.
  eapply sem_ecb_p_muxdel_preserve; eauto. 
  unfold AEventData.
  pure_auto.
  hoare forward.
  get_hsat Hsat.
  unfold AEventData in Hsat.
  sep auto.

  (* the event list before pevent is not nil *)
  specialize (H49 Hnnil).
  simpljoin1.

  eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutex_destroy_absimp_succ; eauto.
   pure_auto.
   eapply absinfer_eq.

   hoare_lifts_trms_pre (Aisr, Ais,Aier).
   transform_pre add_aemp_isr_is_prop ltac:(idtac).
   hoare forward prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel p_local.
  sep cancel tcbdllflag.
  unfold EvtInv.
  unfold AOSIntNesting  in *.
  unfold AGVars.
  unfold AOSEventFreeList.
  unfold AECBList.
  sep pauto; eauto.
  get_hsat Hsat.
  sep cancel evsllseg.
  unfold ecbf_sll.
  sep_lifts_trms_in Hsat (OS_EVENT_TYPE_UNUSED, ecbf_sllseg).
  match goal with H: _ |= Astruct _ OS_EVENT ?vl ** ecbf_sllseg _ _ ?vl' OS_EVENT _ ** _ |- _ =>
  instantiate (13:= vl :: vl') end.
  unfold_ecbfsll.
  sep pauto.
  sep cancel Astruct.
  sep cancel ecbf_sllseg.
  sep cancel Aarray.
  sep cancel Aarray.
  2: { eauto. }
  2: { auto. }
  2: { unfolds; simpl; auto. }
  2: { split. auto. go. }
  6: {  eapply ecb_list_join_join; eauto.
           eapply EcbMod.map_join_comm; eauto.
           eapply join_join_merge_1_ecb; eauto.
           eapply EcbMod.map_join_comm; eauto.   }
  6: { eapply ecb_del_prop_RHhold; eauto.
          introv Hf; destruct Hf as (qd & wt & pqwl & Hf & _); inverts Hf. }

  sep cancel Aier.
  trycancel.
  unfold AMuxEIBs.
  sep normal. sep eexists. sep split; eauto.
  sep cancel AMuxCap.
  sep_lifts_trms APthreadMutex.
  eapply APthreadMutex_select_sn_ex_strong ; eauto.
  sep eexists.
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel Astruct.
  sep pauto; eauto.
  2: {
    rewrite <- Hl.
    rewrite app_length. rewrite app_length.
    eapply f_equal2_plus; eauto.
  }
  2: {
    apply new_array_type_vallist_match_compose_struct; eauto.
  }
  sep_lifts_trms_in Hsat ASemEIBs.
  eapply asemeib_delmux_preserve in Hsat; eauto.
  sep cancel ASemEIBs.
  sep_lifts_trms_in Hsat AMqEIBs. 
  eapply mqeib_delmux_preserve in Hsat; eauto.
  sep cancel AMqEIBs.
  cancel_corecommuinv.
  unfold AOSTCBPrioTbl.
  sep pauto.
  cancel_partitioninv.
  eauto.

  eapply RH_PrioTbl_P_update_null; eauto.
  eapply R_Prio_Tbl_P_hold_for_del_gen; eauto.
  clear -H41. funfold H41; eauto.
  eapply RL_RTbl_PrioTbl_P_hold_for_del_gen; eauto.
  clear -H41. funfold H41; eauto.
  eapply mux_einfo_ecb_delmux_preserve; eauto.
  eapply MuxCapArray_P_hold; eauto.
  {
    rewrite Hupd.
    eapply EIBMAarray_P_hold_for_update_to_null'; eauto.
    apply Int.unsigned_range_2.
  }
  eapply eibref_distinct_muxdel_preserve; eauto.
  eapply mq_ecb_p_muxdel_preserve; eauto.
  eapply mux_ecb_p_muxdel_preserve; eauto.
  eapply sem_ecb_p_muxdel_preserve; eauto.
  unfold AEventData.
  pure_auto.
  hoare forward.
  get_hsat Hsat.
  unfold AEventData in Hsat.
  sep auto.

  Unshelve.
  exact Afalse.
  exact 0%nat.
  exact 0%nat.
  exact 0%nat.
  exact Vnull. 
  exact Vnull. 
  exact Vnull. 
  exact Vnull. 
  exact Vnull. 
  exact Vnull. 
  exact Vnull. 
  exact Vnull. 
  exact Vnull. 
  exact Vnull. 
  exact Vnull. 
  exact Vnull. 

Qed.


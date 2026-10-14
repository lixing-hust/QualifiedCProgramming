
Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import os_sem_cap.
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

Require Import ev_aux_code.
Require Import pos_list_common.
Require Import seplog_trm_tacs. 
Require Import evauxvar_lemmas.
Require Import evaux_pure.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Lemma semdestroy_absimp_semerr:
  forall sch vsem s0 P,
    (vsem = Vnull \/
       exists v'4, vsem = Vptr v'4 /\
                     (cmpaddr Cle v'4 userAddrStart = true \/
                        cmpaddr Clt userAddrEnd v'4 = true)) -> 
    can_change_aop P ->
    absinfer sch
      (<|| (semdestroy_semerr (| vsem::nil|) ?? s0) ||>  ** P) 
      (<|| END (Some (Vint32 Int.mone)) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma semdestroy_absimp_sem_nopblk_abt:
  forall sch vsem a pbls P,
    vsem = Vptr a /\
    (cmpaddr Clt userAddrStart a = true /\ cmpaddr Cle a userAddrEnd = true) ->
    get pbls a = None ->
    can_change_aop P ->
    absinfer sch
      (<|| semdestroy (vsem :: nil) ||>  ** Hpbls pbls ** P)  
      (<|| ABORT ||> ** Hpbls pbls ** P).
Proof.
  introv Hrgn Hnone Hcop.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver. instantiate (1:=Hpbls pbls ** P). can_change_aop_solver.
  intros; auto.
  eapply absinfer_trans. 
  eapply absinfer_choice1.
  can_change_aop_solver.  instantiate (1:=Hpbls pbls ** P). can_change_aop_solver.
  intros; auto.
  eapply absinfer_abt;
    can_change_aop_solver.
  simpljoin1.
  absimp_abt_solver.
  can_change_aop_solver.
  Unshelve.
  exact None.
Qed.

Lemma semdestroy_absimp_pos_err:
  forall sch vsem a pbls pos P,
    vsem = Vptr a /\
    (cmpaddr Clt userAddrStart a = true /\ cmpaddr Cle a userAddrEnd = true) ->
    get pbls a = Some pos ->
    (Int.ltu pos Int.zero = true \/ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) pos = true \/ Int.eq pos (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) ->
    can_change_aop P ->
    absinfer sch
      (<|| semdestroy (vsem :: nil) ||>  ** Hpbls pbls ** P)  
      (<|| END (Some (Vint32 Int.mone)) ||> ** Hpbls pbls ** P).
Proof.
  intros.
  simpljoin1.
  infer_solver 2%nat.
Qed.

Lemma semdestroy_absimp_pevent_null_err:
  forall sch a pbls pos semeibs tp P sc,
    (cmpaddr Clt userAddrStart a = true /\ cmpaddr Cle a userAddrEnd = true) ->
    get pbls a = Some pos ->
    (pos = Int.zero \/ Int.ltu Int.zero pos = true) ->
    Int.ltu pos ($ (OS_USER_MAX_EVENTS / 3)) = true -> 
    get semeibs pos = Some (infonull, tp, sc) -> 
    can_change_aop P ->
    absinfer sch
      (<|| semdestroy (Vptr a :: nil) ||>  ** Hpbls pbls ** HSEMInfo semeibs ** P)  
      (<|| END (Some (Vint32 Int.mone)) ||> ** Hpbls pbls ** HSEMInfo semeibs ** P).
Proof.
  intros. simpljoin1.
  infer_solver 4%nat.
Qed.

Lemma semdestroy_absimp_pevent_holder_abt:
  forall sch a pbls pos semeibs tp P sc,
    (cmpaddr Clt userAddrStart a = true /\ cmpaddr Cle a userAddrEnd = true) ->
    get pbls a = Some pos ->
    (pos = Int.zero \/ Int.ltu Int.zero pos = true) ->
    Int.ltu pos ($ (OS_USER_MAX_EVENTS / 3)) = true -> 
    get semeibs pos = Some (infohold, tp, sc) ->  
    can_change_aop P ->
    absinfer sch
             (<|| semdestroy (Vptr a :: nil) ||>  ** Hpbls pbls ** HSEMInfo semeibs ** P)  
             (<|| ABORT ||> ** Hpbls pbls ** HSEMInfo semeibs ** P).
Proof.
   intros.
  assert (Hc: can_change_aop (Hpbls pbls ** HSEMInfo semeibs ** P)) by can_change_aop_solver.
  do 3 (eapply absinfer_trans; try eapply absinfer_choice2; eauto).
  eapply absinfer_trans; try eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  simpljoin1.
  absimp_abt_solver;
  instantiate (3:= s);
  instantiate (2:= semdestroy_not_placeholder_assm (|Vptr a :: nil|));
  sep pauto.
  Unshelve.
  exact None.
Qed.

Lemma semdestroy_absimp_waiting_tasks_err:
  forall sch a pbls pos semeibs tp sc els n eid wls P,
    can_change_aop P ->
    (cmpaddr Clt userAddrStart a = true /\ cmpaddr Cle a userAddrEnd = true) ->
    get pbls a = Some pos ->
    (pos = Int.zero \/ Int.ltu Int.zero pos = true) ->
    Int.ltu pos ($ (OS_USER_MAX_EVENTS / 3)) = true -> 
    get semeibs pos = Some (infotid eid, tp, sc) ->  
    get els eid = Some (abssem n, wls) ->  
    wls <> nil -> 
    absinfer sch
             (<|| semdestroy (Vptr a :: nil) ||>  ** Hpbls pbls ** HSEMInfo semeibs ** HECBList els ** P)  
             (<|| END (Some (Vint32 (Int.mone))) ||> ** Hpbls pbls ** HSEMInfo semeibs ** HECBList els ** P). 
Proof.
  intros.
  simpljoin1.
  infer_solver 6%nat.
Qed.

Lemma semdestroy_absimp_iserr:
  forall sch P vsem,
    can_change_aop P ->
    absinfer sch
      (<|| semdestroy (vsem :: nil) ||>  ** P)  
      (<|| END (Some (Vint32 (Int.mone)))  ||> ** P).
Proof.
  infer_solver 7%nat.
Qed.

Lemma semdestroy_absimp_succ: 
  forall sch a pbls pos semeibs tp sc els els' n eid P,
    can_change_aop P ->
    (cmpaddr Clt userAddrStart a = true /\ cmpaddr Cle a userAddrEnd = true) ->
    get pbls a = Some pos ->
    (pos = Int.zero \/ Int.ltu Int.zero pos = true) ->
    Int.ltu pos ($ (OS_USER_MAX_EVENTS / 3)) = true -> 
    get semeibs pos = Some (infotid eid, tp, sc) ->  
    get els eid = Some (abssem n, nil) ->
    join els' (sig eid (abssem n, nil)) els ->
    absinfer sch
             (<|| semdestroy (Vptr a :: nil) ||>  ** Hpbls pbls ** HSEMInfo semeibs ** HECBList els ** P)  
             (<|| END (Some (Vint32 (Int.zero))) ||> **
                  Hpbls pbls ** HSEMInfo (set semeibs pos (infonull, tp, sc)) ** HECBList els' ** P). 
Proof.
  intros.
  simpljoin1.
  infer_solver 8%nat.
Qed.

Require Import OSTimeTickPure.
Require Import semdel_pure. 

Local Open Scope code_scope.

(* copy form OSMutex_common.v *)
Goal forall x y, Int.eq x y = true  -> x=y.
intros.
int auto.
apply unsigned_inj.
auto.
Save inteqeq.
(* end of copy *)

Lemma OSSemDestroyProof: 
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api sem_destroy
              (semdestroy,(Tint32,Tint32::nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api sem_destroy
              (semdestroy,(Tint32,Tint32::nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api sem_destroy = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}.
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  destruct v'; try apply absabort_rule.
  rename x into vsem.
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

  (* encrit *)
  hoare forward prim. 
  hoare_lifts_trms_pre (Aisr, Ais, aemp_isr_is).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  hoare unfold.
  rename v'20 into vcspace.
  rename v'21 into v21. 
  rename v'22 into v22. 
  rename v'23 into v23. 
  
  (*x ′ =ᶠ UserAddrCheckCrit (·〈 (long) ∗ 〉 sem ′·);ₛ*)
  hoare forward.
  pure_auto.
  pure_auto.
  sep cancel p_local. 
  eauto.
  simpl.
  eauto.
  destruct Hptr as [Hptr | (semv & Hptr)]; subst vsem; eauto.
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

  (*----------------------------------------- illegal range for sem ---------------------------------------*)
  hoare unfold.
  inverts H3.

  hoare abscsq.
  eapply noabs_oslinv.
  eapply semdestroy_absimp_semerr; eauto.
  destruct H1 as [Heq | (a & Heq & Hrange)]; inverts Heq; eauto.
  pure_auto.

  (* hoare_ex_intro. *) 
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
  hoare_lifts_trms_pre (Aisr, Ais, Aier).
  transform_pre add_aemp_isr_is_prop ltac:(idtac).
  (* EXIT_CRITICAL;ₛ *)
  hoare forward prim.
  sep cancel CoreCommuInv.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  sep cancel Aier.
  eauto.
  auto.
  pure_auto.
  (* RETURN ′ (-1) *)
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

  (* ------------------------------------------- legal range for sem -------------------------------------------------------- *) 
  hoare_split_pure_all.
  inverts H2. 
  inverts H3.
  destruct H1 as (semadr & (Hsemeq & Hsemrgn1 & Hsemrgn2)).

  unfold EvtInv.
  hoare normal pre.
  hoare_ex_intro.
  rename v'36 into pbls.
  hoare_lifts_trms_pre ( R_Q_Data_P).
  eapply pure_split_rule'; introv Hrqdata.
  hoare_split_pure_all. subst.
  assert (Hor: get pbls semadr = None \/ (exists posv, get pbls semadr = Some posv)).
  {
    destruct (get pbls semadr).
    right. eexists. eauto. 
    left. auto.
  }
  destruct Hor as [Hnone | (posv & Hsome)].
  (* get pbls smadr = None *)
  hoare_lifts_trms_pre (Aop, pblsid). 
  eapply abscsq_rule. 
  apply noabs_oslinv. 
  eapply semdestroy_absimp_sem_nopblk_abt; eauto.
  simpljoin1. splits; eauto. inverts Hsemeq; auto.
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule. 
  inverts Hsemeq. 

  eapply backward_rule1. 
  introv Hsat.
  sep_lifts_trms_in Hsat APosblkList.
  eapply pos_list_split_frm; eauto.
  unfold node.
  hoare unfold.
  inverts H8. inverts H9.
(*   hoare_lifts_trms_pre (Aop, Alvarmapsto x). *)
  lzh_hoare_if.
  {
    change (Int.eq ($ 1) ($ 0)) with false in LHif_true.
    tryfalse. 
  }
  2: { change (Int.eq ($ 1) ($ 0)) with false in Hif_true. tryfalse. }
  hoare_lifts_trms_pre (Aop, Alvarmapsto os_code_defs.pos, Alvarmapsto sem).
   eapply assign_rule_lvar with (v2:= Vint32 posv).
   split; introv Hsat. eauto. sep auto.
   simpl Astruct. introv Hsat. sep get rv.
   eapply eq_int; auto.
   intros. eexists. sep cancel p_local. simpl; auto.
   rename v'46 into sem_b.

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
  eapply semdestroy_absimp_pos_err; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  
  hoare_lifts_trms_pre (Aisr, Ais,Aier).
  transform_pre add_aemp_isr_is_prop ltac:(idtac).
  (* EXIT_CRITICAL;ₛ *)
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel APthreadAttr.
  unfold EvtInv.
  sep cancel Aier.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel CapabilityInv.
  unfold APosblkList.
  sep pauto.
  eapply pos_sllseg_merge; eauto.
  unfold node.
  sep pauto; eauto.
  sep cancel pos_sllseg. sep cancel Astruct. sep cancel pos_sllseg.
  eauto.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  split; auto. go.
  pure_auto.
  pure_auto.
  (* return ′ -1 *)
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
  assert (Hposrgn': ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\ Int.ltu posv ($ (OS_USER_MAX_EVENTS / 3)) = true)).
  { clear -Hposrgn Hrgn3 Hrgn4.
    mytac.
    int auto.
    left. mauto.
  }
  (* clear Hposrgn. rename Hposrgn' into Hposrgn. *)
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
  (* split (Sem_info ′ [os_code_defs.pos ′]) *)
  unfold ASemEIBs.
  hoare unfold.
  destruct v'41.
  rename H8 into HH8.
  rename H9 into HH9.
  rename H12 into H8.
  rename H14 into H9.
  rename H15 into H12.
  rename H16 into H14.
  rename H17 into H15.
  eapply backward_rule1.
  introv Hsat.
   sep_lift_context_in Hsat ASeminfo.
  eapply ASeminfo_unfold_any_idx_frm with (idx:=∘(Int.unsigned posv)); eauto.
  lets Hl: aseminfo_len_frm Hsat.
  clear -Hl Hpos_range2' Hrgn3 Hrgn4 Hdiveq.
  rewrite Hl.
  unfold nat_of_Z.
  clear -Hpos_range2' Hrgn3 Hrgn4.
  int auto.
  hoare unfold.
  (* unfold the vallist of  efield (Sem_info ′ [pos ′]) *) 
  lets Hmt3: new_array_type_vallist_match_split H16.
  specialize (Hmt3 (eq_refl _)).
  destruct Hmt3 as (Hmt1 & Hmt2 & Hmtm).
  lets Hvl: struct_type_vallist_match_sem_info_t_vl Hmtm.
  clear Hptr.
  lets Hptr: struct_type_vallist_match_sem_info_t_ptr Hmtm.
  simpljoin1.
  simpl in Hptr.

  assert (Hpos_range3: Int.unsigned posv <= Int.max_signed).
  { clear -Hpos_range1 Hpos_range2 Hrgn3 Hrgn4.
     int auto.
  }

  lets Hcorr: semb_corr H1 H19.
(*   instantiate (1:=∘ (Int.unsigned posv)) in Hcorr. *)
  match type of Hcorr with
    _ -> _ -> ?Q => assert (Hcorr': Q); [apply Hcorr; eauto | ]
  end.
  clear -Hpos_range1 Hpos_range2 Hrgn3 Hrgn4.
  int auto.
  clear Hcorr.
  destruct Hcorr' as (eid_opt & tp & sc & Hgeteib & Htp & Hcases).
  inverts Htp.
  unfold V_OSSINFOPevent in Hcases; simpl nth_val in Hcases.

  assert (Heidcases: eid_opt = infonull \/ eid_opt = infohold \/ (exists eid, eid_opt = infotid eid)).
  {
    destruct eid_opt; auto.
    right. right.
    eexists; eauto.
  }
  destruct Heidcases as [Hnull | [Hhold | Hvptr]].
  subst eid_opt.
  assert (x6 = Vnull).
  {
    destruct Hcases. simpljoin1. tryfalse.
    destruct H18. simpljoin1. tryfalse.
    simpljoin1. inverts H22.
    auto.
  }
  subst x6.

  eapply seq_rule.
  eapply lzh_if_then_rule.
  introv Hsat.
  sep_lifts_trms_in Hsat Astruct.
  eapply bop_rv; eauto.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  sep get rv.
  go.
  go.

  hoare_lifts_trms_pre (Aop, pblsid, seminfoid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semdestroy_absimp_pevent_null_err; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aisr, Ais,Aier).
  transform_pre add_aemp_isr_is_prop ltac:(idtac).
  (* EXIT_CRITICAL *)
  hoare forward prim.
  sep cancel APthreadAttr.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier.
  unfold EvtInv. sep normal.
  do 19 eexists.
  unfold ASemEIBs.
  get_hsat Hsat. 
  sep_lifts_trms_in Hsat (Sem_info, _N_ 4, Astruct, _N_ 6).
  sep cancel AOSEventFreeList.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AECBList. 
  eapply ASeminfo_select_sn_strong in Hsat.
  sep pauto.
  sep cancel ASeminfo.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel ASemCap.
  sep cancel CapabilityInv.
  eauto.
  auto.
  auto.
  auto.
  auto.
  pure_auto.
  pure_auto.
  auto.
  go.
  (* RETURN -1 *)
  hoare forward.

  (* code after if (Sem_info[pos].pevent != NULL) {...} is reached -- impossible when ...=NULL *)
  simpl bop_eval.
  simpl val_inj.
  hoare forward; hoare unfold.
  apply pfalse_rule.
  destruct H18; tryfalse.

  (* Sem_info[pos].pevent is placeholder *) 
  subst.
  hoare_lifts_trms_pre (Aop, pblsid, seminfoid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semdestroy_absimp_pevent_holder_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.

  (* Sem_info[pos].pevent is a valid pointer *) 
  destruct Hvptr as (eid & Heo).
  subst eid_opt.
  destruct Hcases as [Hptr' | [Hhold | Hnull]].
  2: { simpljoin1. tryfalse. }
  2: { simpljoin1. tryfalse. } 
  simpljoin1.
  inverts H18.  (* infotid eid = infotid x1 *) 
  inverts H22.

  rename x into ecbptr.
  rename H8 into Hreibecb.
  lets Hecb: Hreibecb Hgeteib.
  destruct Hecb as (n & wls & Hgetecb).

  unfold AECBList.
  hoare normal pre.
  hoare unfold.
  rename H8 into H_elp. (* ECBList_P ... *)
  lets H_elp': H_elp.
  lets Hctr: ECBList_P_get_ectr_some Hgetecb H_elp. 
  destruct Hctr as (evl & etbl & petbl & Hgetectr).
  
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat evsllseg.
  eapply get_ectr_decompose; eauto.
  hoare unfold.
  hoare_assert_pure (length v'48 = length v'50).
  {
    get_hsat Hsat. 
    sep_lifts_trms_in Hsat evsllseg.
    eapply evsllseg_aux in Hsat.
    destruct Hsat.
    eauto.
  }
  eapply pure_split_rule'; introv Heqlen.
  eapply ecblist_p_decompose in H_elp; eauto. 
  destruct H_elp as (els1 & els2 & x' & H'').
  destruct H'' as (Hecbl1 & Hecbl2 & Hjo).  

  hoare_assert_pure (x' = Vptr (v'57, Int.zero)).
  { get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg.
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  hoare_split_pure_all; subst.
  rename v'57 into eid_b. 

  hoare_assert_pure (i2 = (Int.repr OS_EVENT_TYPE_SEM)). (* change i1 -> i2 *)
  { destruct (Int.eq i2 (Int.repr OS_EVENT_TYPE_SEM)) eqn: eq_tp.  (* change i1 -> i2 *)
    eapply inteqeq in eq_tp; subst; auto.
    simpl in Hecbl2.
    simpljoin.
    inverts H22.
    lets Hgete': H45.
    eapply EcbMod.join_sig_get in Hgete'.
    eapply EcbMod.join_get_r in Hgete'; eauto.
    unfold get in Hgetecb; unfold EcbMap in Hgetecb.
    rewrite Hgetecb in Hgete'; inverts Hgete'.
    get_hsat Hsat.
    sep_lifts_trms_in Hsat (AEventData).
    eapply sem_eventtype_neq_sem in Hsat; eauto.
    sep split in Hsat.
    false.
    apply H8; eauto.
    unfolds; simpl; auto.
  }
  hoare_split_pure_all; subst.

  eapply seq_rule.
  eapply lzh_if_then_rule.
  introv Hsat.
  sep lift 10%nat in Hsat. 
  eapply bop_rv; eauto.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  sep get rv.
  go.
  go.

  hoare_split_pure_all.
  simpl in H8. 
  destruct H8 as (Hf & _ & _).
  false.

  instantiate (1:=Afalse). 
  eapply backward_rule1.
  introv Hsat.
  destruct Hsat.
  2: { eauto. }
  sep split in H8.
  clear -H8.
  tryfalse. 
  hoare_split_pure_all.
  rename H8 into Hinjor.
  clear Hinjor.

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
  unfold ASemEIBs.
  unfold AECBList.
  unfold AGVars.
  sep pauto; eauto.
  trycancel.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep_lift_context evsllseg.
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
  eapply ASeminfo_select_sn_ex_strong.
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
  (* If ((efield (Sem_info ′ [os_code_defs.pos ′]) pevent) → OSEventGrp
    !=ₑ ′ 0 ||ₑ OSIntNesting ′ >ₑ ′ 0) *)
  unfold AGVars.
  unfold AOSIntNesting.
  hoare normal pre. hoare_ex_intro.
  rename v'64 into vnest.
  eapply seq_rule.
  eapply lzh_if_then_rule.
  introv Hsat.
  eapply bop_rv; eauto.
  { (* Rv (efield (Sem_info ′ [os_code_defs.pos ′]) pevent) → OSEventGrp *)
   eapply uop_rv; eauto.
   eapply bop_rv; eauto.
   sep_get_rv_array_struct'.
   rewrite Hdiveq; eauto.
   rewrite Hdiveq; eauto.
   simpl; auto.
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
  assert (Hif_true: Int.eq i1 Int.zero = false \/ Int.ltu Int.zero vnest = true). (* change i0 -> i1 *)
  { clear -H8.
    destruct (Int.eq i1 Int.zero) eqn: eq1; (* change i0 -> i1 *)
    destruct (Int.ltu Int.zero vnest) eqn: eq2;
    simpl in *; auto.
  }
  clear H8 H43 H44.
  hoare_lifts_trms_pre (Aop, pblsid, seminfoid, absecblsid). 
  destruct Hif_true as [Hgrp_nzero | Hiserr].
  2: { eapply abscsq_rule.
       apply noabs_oslinv.
       eapply semdestroy_absimp_iserr; eauto.
       can_change_aop_solver.
       eapply absinfer_eq.
       hoare_lifts_trms_pre (Aisr, Ais,Aier).
       transform_pre add_aemp_isr_is_prop ltac:(idtac).
       hoare forward prim.
       sep cancel tcbdllflag.
       sep cancel p_local.
       unfold EvtInv.
       unfold ASemEIBs.
       unfold AECBList.
       unfold AGVars.
       sep pauto; eauto.
       trycancel.
       sep cancel AMuxEIBs.
       sep cancel AMqEIBs.
       sep_lift_context evsllseg.
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
       sep cancel AOSPostEventTbl. (* new add *)
       eapply ASeminfo_select_sn_ex_strong.
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
       (* RETURN ′ -1 *)
       hoare forward.
  }
  assert (Hwls_nnil: wls <> nil).
  { assert (Hgetecb': exists cnt' t' tl, EcbMod.get v'12 (eid_b, Int.zero) = Some (abssem cnt', t' :: tl)).
    { simpl in Hecbl2.
      mytac.
      inverts H8.
      eapply sem_ecb_wt_ex_prop; eauto.
    }
    destruct Hgetecb' as (cnt' & t' & tl & Hgetecb').
    clear -Hgetecb Hgetecb'.
    unfold get in *. unfold EcbMap in *.
    rewrite Hgetecb in Hgetecb'; inverts Hgetecb'.
    pure_auto.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semdestroy_absimp_waiting_tasks_err; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  hoare_lifts_trms_pre (Aisr, Ais,Aier).
  transform_pre add_aemp_isr_is_prop ltac:(idtac).
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  unfold ASemEIBs.
  unfold AECBList.
  unfold AGVars.
  sep pauto; eauto.
  trycancel.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep_lift_context evsllseg.
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
  eapply ASeminfo_select_sn_ex_strong.
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
  (* RETURN ′ -1 *)
  hoare forward.
  hoare forward.
  hoare unfold.
  apply pfalse_rule.
  hoare unfold.
  assert (Hif_cond: Int.eq i1 Int.zero = true /\ Int.ltu Int.zero vnest = false).
  { clear -H8.
    change ($ 0) with Int.zero in H8.
    simpl in H8.
    destruct (Int.eq i1 Int.zero) eqn: eq1;
    destruct (Int.ltu Int.zero vnest) eqn: eq2;
    simpl in *; auto;
    try change (Int.notbool Int.one) with Int.zero in *;
    try change (Int.ltu Int.zero Int.one) with true in *;
    try change (Int.ltu Int.zero Int.zero) with false in *;
    simpl in *; destruct H8; tryfalse.
  }
  clear H8.
  destruct Hif_cond as (Hgrp_zero & Hnest).
  eapply inteqeq in Hgrp_zero; subst i1.
  hoare_assert_pure (v'52 = DSem i3).
  { get_hsat Hsat. 
    unfold AEventData in Hsat.
    destruct v'52;
    sep split in Hsat.
    inverts H43.
    inverts H43.
    auto.
    inverts H8.
    inverts H8.
    inverts H8.
  }
  hoare_split_pure_all.
  subst v'52. 

  (* del_pevent = Sem_info[pos].pevent; *)
  hoare_lifts_trms_pre Aop. 
  eapply seq_rule.
  eapply assign_rule_lvar.
  split; introv Hsat. sep cancel (Alvarmapsto p). eauto.
  sep auto.
  introv Hsat.
  sep lift 22%nat in Hsat.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  apply eq_vptr.
  do 2 eexists. split; eauto.
  introv Hsat.
  exists init_lg. sep cancel p_local. simpl;auto.
  simpl nth_val'.

  (* Sem_info[pos].pevent = NULL *)
  hoare forward.

  rename v'33 into semeibs.
  rename v'34 into muxeibs.
  rename v'35 into mqeibs. 
  rename v'38 into locmp.
  rename v'39 into ptrmp.
  assert (Heibref: eib_ref semeibs muxeibs mqeibs (eid_b, Int.zero)).  
  { unfold eib_ref. left.
    unfold semeib_ref. do 2 eexists; eauto.
  }
  assert (Hncre1: ~exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre1 (eid_b, Int.zero)).  
  { eapply eib_ref_no_tsk_cre1; eauto. }
  assert (Hncre2: ~exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre2 (eid_b, Int.zero)).  
  { eapply eib_ref_no_tsk_cre2; eauto. }
  assert (Hndel: ~exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbdel (eid_b, Int.zero)).
  { eapply eib_ref_no_tsk_del; eauto. }

  (* OSSemDel (­ p ′­);ₛ *)
  unfold AOSPostEventTbl.
  hoare unfold.
  inverts H29.
  hoare forward.
  sep cancel Aarray.
  sep cancel evsllseg.
  sep cancel evsllseg.
  sep cancel AOSEventFreeList.
  sep cancel Aarray.
  sep cancel (Astruct (eid_b, Int.zero)).
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
  unfold AEventData. pure_auto.
  introv Hsat.
  exists init_lg. sep destruct Hsat. sep cancel p_local. sep auto.
  introv Hsat.
  exists init_lg. sep destruct Hsat. sep cancel p_local. sep auto.

  hoare unfold.
  inverts H29. (* logic_code ... :: ... = logic_code ... :: ... *)
  rename v'35 into pevent_blk.

  assert (Hupd: Vint32 tp :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: Vnull :: x7 :: nil =
                update_nth_val 7 (Vint32 tp :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: Vptr (pevent_blk, Int.zero) :: x7 :: nil) Vnull).
  { simpl. auto. }

  hoare_assert_pure (get ptrmp v'76 = Some (Vnull, Vnull, Vnull)).
  { get_hsat Hsat.
    sep_lifts_trms_in Hsat (tcbllsegevaux, AOSTCBList, p_local).
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
  rename H29 into Hgetauxp.

  assert (Hnmref: ~muxeib_ref muxeibs (pevent_blk, Int.zero)).
  { eapply eibref_distinct_semref_nmuxref; eauto.
    unfold semeib_ref. do 2 eexists; eauto.
  }
  assert (Hnqref: ~mqeib_ref mqeibs (pevent_blk, Int.zero)).
  { eapply eibref_distinct_semref_nmqref; eauto.
    unfold semeib_ref. do 2 eexists; eauto.    
  }

  match goal with 
    H: ECBList_P _ (Vptr (pevent_blk, Int.zero)) ?l _ _ _ |- _ => 
    assert (Hnilor: l = nil \/ l <> nil) by tauto
  end.
  destruct Hnilor as [Hnil | Hnnil].

  (* the event list before pevent is nil *)
  subst.
  simpl in Hecbl1.
  simpljoin1. subst.
  assert (els2 = v'12).
  { clear -Hjo. join auto. }
  subst v'12.
  
  rename v'74 into i1.
  assert (EcbMod.get els2 (pevent_blk, Int.zero) = Some (abssem i1, nil) /\
          (exists vv,
              EcbMod.join vv (EcbMod.sig (pevent_blk, Int.zero) (abssem i1, nil)) els2 /\
              ECBList_P v'52 Vnull v'71 v'73 vv v'13)).
  { eapply semdel_ecblist_ecbmod_get with (v'53 := v'39); eauto. }
  simpljoin1.

  hoare_lifts_trms_pre (Aop, pblsid, seminfoid, absecblsid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semdestroy_absimp_succ with (pos:=posv); eauto.
  go.
  eapply absinfer_eq.

  specialize (H46 (eq_refl _)). simpljoin1.
  
  hoare_lifts_trms_pre (Aisr, Ais,Aier).
  transform_pre add_aemp_isr_is_prop ltac:(idtac).
  (* EXIT_CRITICAL;ₛ *)
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
  instantiate (10:=((V$ OS_EVENT_TYPE_UNUSED :: V$ 0 :: Vint32 i1 :: v'56 :: v'64 :: v'66 :: Vint32 v'77 :: v'78 ::  nil) :: v'75)).
  unfold_ecbfsll.
  sep pauto.
  sep cancel Astruct.
  sep cancel ecbf_sllseg.
  sep cancel Aarray.
  sep cancel Aarray.
  2: { eauto. }
  2: { unfolds; simpl; auto. }
  2: { auto. }
  2: { split. auto. go. } 
  6: { eapply semdel_ecb_del_prop_RHhold; eauto.
          introv Hf; destruct Hf as (qd & wt & pqwl & Hf & _); inverts Hf.  }
          
  2: { eapply eibref_distinct_semdel_preserve; eauto. }
  4: { eapply sem_ecb_p_semdel_preserve; eauto. }
  3: { eapply mux_ecb_p_semdel_preserve; eauto. }
  2: { eapply mq_ecb_p_semdel_preserve; eauto.  }

  trycancel.
  
  (* CoreCommuInv  *)
  Require Import sem_corecommu.
  cancel_corecommuinv.
  2: { lets Hq_nc': H9 Hgeteib. eauto. }
  (* end of CoreCommuInv *)
  
  (* PartitionInv *)
  Require Import sem_partition.
  cancel_partitioninv.
  eauto.
  (* end of PartitionInv *)

  unfold ASemEIBs.
  sep normal. 
  eexists.
  sep cancel ASemCap.
  sep split; eauto.
  instantiate (6:=v'41 ++ (Vint32 tp :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: Vnull :: x7 :: nil) :: v'46).
  eapply ASeminfo_select_sn_strong ; eauto.
  sep cancel (Agvarmapsto Sem_info).
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel Astruct.
  2: { apply new_array_type_vallist_match_compose_struct; eauto. }
  2: { rewrite <- H17.
       rewrite app_length. rewrite app_length.
       eapply f_equal2_plus; eauto.
     }
  sep_lifts_trms_in Hsat AMuxEIBs.
  eapply amuxeibs_delsem_preserve in Hsat; eauto.
  sep cancel AMuxEIBs.
  sep_lifts_trms_in Hsat AMqEIBs. 
  eapply mqeibaarray_delsem_preserve in Hsat; eauto.
  5: { go. unfold AEventData. go. }
  
  eapply RH_SEM_NOT_IN_CORE_P_hold_neid; eauto.
  introv Hf; simpljoin; tryfalse.
  eapply sem_einfo_ecb_delsem_preserve; eauto.
  (* SemCapArray_P *)
  eapply SemCapArray_P_hold; eauto.

  rewrite Hupd.
  asserts_rewrite (posv = Int.add posv Int.zero).
  { rewrite Int.add_zero. auto. }
  eapply EIBArray_P_hold_for_update_to_null; eauto.
  { rewrite H19.
    rewrite unsigned_to_z_eq; eauto.
    rewrite Z2Nat.id; eauto.
    clear. int auto.
    clear. int auto.
  }
  rewrite H19.
  rewrite unsigned_to_z_eq; eauto.
  rewrite Z2Nat.id; eauto.
  clear. int auto.
  clear. int auto.
  clear. int auto.

  unfold AEventData.
  hoare_split_pure_all.
  hoare forward.
  
  (* the event list before pevent is not nil *)
  specialize (H45 Hnnil).
  simpljoin1.
  rename v'74 into i1.
  lets Hcp: H_elp'.
  eapply semdel_ecblist_ecbmod_get' in Hcp; eauto.
  simpljoin1.
  
  assert (Hjo_new: join (sig (pevent_blk, Int.zero) (abssem i1, nil)) (merge x x6) v'12).
  { eapply join_join_merge'_ecb; eauto.
    eapply EcbMod.map_join_comm; eauto.
    eapply EcbMod.map_join_comm; eauto.
  }
  lets Hjo_new': EcbMod.map_join_comm Hjo_new.

  hoare_lifts_trms_pre (Aop, pblsid, seminfoid, absecblsid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semdestroy_absimp_succ with (pos:=posv); eauto.
  go.
  eapply absinfer_eq.

  hoare_lifts_trms_pre (Aisr, Ais,Aier).
  transform_pre add_aemp_isr_is_prop ltac:(idtac).
  hoare forward prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel p_local.
  sep cancel tcbdllflag.
  sep cancel Aier.
  unfold EvtInv.
  unfold AOSIntNesting  in *.
  unfold AGVars.
  unfold AOSEventFreeList.
  unfold AECBList.
  sep pauto; eauto.
  get_hsat Hsat.
  sep cancel evsllseg.
  unfold ecbf_sll.
  instantiate (10:=((V$ OS_EVENT_TYPE_UNUSED :: V$ 0 :: Vint32 i1 :: v'56 :: v'64 :: v'66 :: Vint32 v'77 :: v'78 ::  nil) :: v'75)).
  unfold_ecbfsll.
  sep pauto.
  sep cancel Astruct.
  sep cancel ecbf_sllseg.
  sep cancel Aarray.
  sep cancel Aarray.
  2: { eauto. }
  2: { unfolds; simpl; auto. }
  2: { auto. }
  2: { split. auto. go. }
  6: { eapply semdel_ecb_list_join_join ; eauto.
       apply EcbMod.join_comm.
       eapply EcbMod.join_merge_disj; eauto.
       eapply EcbMod.disj_comm.
       eapply EcbMod.join_join_disj_l; eauto.
       eapply EcbMod.join_comm; eauto.
     }
  6: { eapply semdel_ecb_del_prop_RHhold; eauto.
       introv Hf; destruct Hf as (qd & wt & pqwl & Hf & _); inverts Hf.  }
  2: { eapply eibref_distinct_semdel_preserve; eauto. }
  4: { eapply sem_ecb_p_semdel_preserve; eauto. }
  3: { eapply mux_ecb_p_semdel_preserve; eauto. }
  2: { eapply mq_ecb_p_semdel_preserve; eauto.  }
  trycancel.

   (* CoreCommuInv  *)
  Require Import sem_corecommu.
  cancel_corecommuinv.
  2: { lets Hq_nc': H9 Hgeteib. eauto. }
  (* end of CoreCommuInv *)
  
  (* PartitionInv *)
   cancel_partitioninv.
   eauto.
   (* end of PartitionInv *)

  unfold ASemEIBs.
  sep normal.
  eexists.
  sep cancel ASemCap. 
  sep split; eauto.
  instantiate (6:=v'41 ++ (Vint32 tp :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: Vnull :: x7 :: nil) :: v'46).
  eapply ASeminfo_select_sn_strong ; eauto.
  sep cancel (Agvarmapsto Sem_info).
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel Astruct.
  2: { apply new_array_type_vallist_match_compose_struct; eauto. }
  2: { rewrite <- H17.
       rewrite app_length. rewrite app_length.
       eapply f_equal2_plus; eauto.
     }
  sep_lifts_trms_in Hsat AMuxEIBs.
  eapply amuxeibs_delsem_preserve in Hsat; eauto.
  sep cancel AMuxEIBs.
  sep_lifts_trms_in Hsat AMqEIBs. 
  eapply mqeibaarray_delsem_preserve in Hsat; eauto.
  5: { go. unfold AEventData. go. }
  eapply RH_SEM_NOT_IN_CORE_P_hold_neid; eauto.
  introv Hf; simpljoin; tryfalse.
  eapply sem_einfo_ecb_delsem_preserve; eauto.
  eapply SemCapArray_P_hold; eauto.
  rewrite Hupd.
  asserts_rewrite (posv = Int.add posv Int.zero).
  { rewrite Int.add_zero. auto. }
  eapply EIBArray_P_hold_for_update_to_null; eauto.
  { rewrite H19.
    rewrite unsigned_to_z_eq; eauto.
    rewrite Z2Nat.id; eauto.
    clear. int auto.
    clear. int auto.
  }
  rewrite H19.
  rewrite unsigned_to_z_eq; eauto.
  rewrite Z2Nat.id; eauto.
  clear. int auto.
  clear. int auto.
  clear. int auto.

  unfold AEventData.
  hoare_split_pure_all.
  hoare forward.

  Unshelve.
  trivial.
  exact Afalse.
  exact 0%nat.
  exact 0%nat.
  exact 0%nat. 
  exact 0%nat.
  exact Vnull. exact Vnull. exact Vnull. exact Vnull.
  exact Vnull. exact Vnull. exact Vnull. exact Vnull.
  exact Vnull. exact Vnull. exact Vnull. exact Vnull.
Qed.


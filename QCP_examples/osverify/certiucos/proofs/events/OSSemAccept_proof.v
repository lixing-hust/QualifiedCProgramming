Require Import include_frm.
Require Import abs_infer_step.
Require Import ucos_frmaop.
Require Import seplog_lemmas.
Require Import seplog_tactics.
Require Import os_sem.
Require Import ifun_spec.

Require Import abs_infer_abt.
Require Import sem_common.
Require Import evauxvar_lemmas.
Require Import evaux_pure.
Require Import gjb_sem_common.
Require Import seplog_trm_tacs.
Require Import evtinv_lemmas.

Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

(*********************** sem acc **************************************)

Lemma semacc_absimp_null:
  forall v' P sch,
    v' = Vint32 Int.zero ->
    can_change_aop P -> 
    absinfer sch ( <|| semacc (Vnull :: v' :: nil) ||> ** P)  ( <|| END (Some (Vint32 Int.zero)) ||> ** P ).
Proof.
infer_solver 0%nat.
Qed.

Lemma semacc_absimp_null':
  forall sid v' P sch s,
    sid = Vnull ->
    v' = Vint32 Int.zero ->
    can_change_aop P -> 
    absinfer sch ( <|| semacc (sid :: v' :: nil) ;; s ||> ** P)  ( <|| s ||> ** P ).
Proof.
intros.
substs.
eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
2 : { eapply absinfer_seq_end; eauto. }
infer_solver 0%nat.
Qed.

Lemma semacc_absimp_null_abt:
  forall sid v' P sch,
    sid = Vnull ->
    v' <> Vint32 Int.zero ->
    can_change_aop P -> 
    absinfer sch ( <|| semacc (sid :: v' :: nil) ||> ** P) ( <|| ABORT ||> ** P ).
Proof.
intros. substs.
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma semacc_absimp_null_abt':
  forall sid v' P sch s,
    sid = Vnull ->
    v' <> Vint32 Int.zero ->
    can_change_aop P -> 
    absinfer sch ( <|| semacc (sid :: v' :: nil) ;; s ||> ** P)  ( <|| ABORT ||> ** P ).
Proof.
intros. substs.
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma semacc_absimp_no_sem:
  forall P els tcbls tm curtid sid v' sch,
    can_change_aop P ->
    (~ exists n wls, EcbMod.get els sid = Some (abssem n, wls)) ->
    v' = Vint32 Int.zero ->
    absinfer sch 
      ( <|| semacc (Vptr sid :: v' :: nil) ||> ** 
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid  ** P)
      ( <|| END (Some (Vint32 Int.zero)) ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid  ** P).
Proof.
infer_solver 1%nat.
Qed.

Lemma semacc_absimp_no_sem':
  forall P els tcbls tm curtid sid v' sch s,
    can_change_aop P ->
    (~ exists n wls, EcbMod.get els sid = Some (abssem n, wls)) ->
    v' = Vint32 Int.zero ->
    absinfer sch 
      ( <|| semacc (Vptr sid :: v' :: nil) ;; s ||> ** 
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| s ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
intros.
assert (can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
2 : { eapply absinfer_seq_end; eauto. }
infer_solver 1%nat.
Qed.

Lemma semacc_absimp_no_sem_abt:
  forall P els tcbls tm curtid sid v' sch,
    can_change_aop P ->
    (~ exists n wls, EcbMod.get els sid = Some (abssem n, wls)) ->
    v' <> Vint32 Int.zero ->
    absinfer sch 
      ( <|| semacc (Vptr sid :: v' :: nil) ||> ** 
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| ABORT ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
intros.
assert (can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_choice2; eauto).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma semacc_absimp_no_sem_abt':
  forall P els tcbls tm curtid sid v' sch s,
    can_change_aop P ->
    (~ exists n wls, EcbMod.get els sid = Some (abssem n, wls)) ->
    v' <> Vint32 Int.zero ->
    absinfer sch 
      ( <|| semacc (Vptr sid :: v' :: nil) ;; s ||> ** 
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| ABORT ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
intros.
assert (can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
eapply absinfer_trans; try (eapply absinfer_choice2; eauto).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.
  
Lemma semacc_absimp_no_source:
  forall P els tcbls tm curtid sid v' wls sch,
    can_change_aop P ->
    get els sid = Some (abssem Int.zero, wls) ->
    v' = Vint32 Int.zero ->
    absinfer sch
      ( <|| semacc (Vptr sid :: v' :: nil) ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| END (Some (Vint32 Int.zero)) ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
infer_solver 2%nat.
Qed.

Lemma semacc_absimp_no_source':
  forall P els tcbls tm curtid sid v' wls sch s,
    can_change_aop P ->
    get els sid = Some (abssem Int.zero, wls) ->
    v' = Vint32 Int.zero ->
    absinfer sch
      ( <|| semacc (Vptr sid :: v' :: nil) ;; s ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| s ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
intros.
assert (can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
2 : { eapply absinfer_seq_end; eauto. }
infer_solver 2%nat.
Qed.

Lemma semacc_absimp_no_source_abt:
  forall P els tcbls tm curtid sid v' wls sch,
    can_change_aop P ->
    get els sid = Some (abssem Int.zero, wls) ->
    v' <> Vint32 Int.zero ->
    absinfer sch
      ( <|| semacc (Vptr sid :: v' :: nil) ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| ABORT ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
intros.
assert (can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
can_change_aop_solver.
do 2 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma semacc_absimp_no_source_abt':
  forall P els tcbls tm curtid sid v' wls sch s,
    can_change_aop P ->
    get els sid = Some (abssem Int.zero, wls) ->
    v' <> Vint32 Int.zero ->
    absinfer sch
      ( <|| semacc (Vptr sid :: v' :: nil) ;; s ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| ABORT ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
intros.
assert (can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
do 2 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

(* Require Import join_lib. *)

Lemma semacc_absimp_succ:
  forall P wls sid n tcbls tm curtid v' sch els vhold tcblh tcbvl v19 v20 v21, 
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu Int.zero n = true ->
    v' = Vint32 n ->
    absinfer sch
             ( <|| semacc (Vptr sid :: v' :: nil) ||> **
                   HECBList els **
                   HTCBList tcbls ** HTime tm ** HCurTCB curtid **
                   EvtInv_part2 els tcblh tcbvl vhold v19 v20 v21**
                   P)
             ( <|| END (Some (Vint32 n)) ||> **
                   HECBList (set els sid (abssem (Int.sub n Int.one), wls)) **
                   HTCBList tcbls ** HTime tm ** HCurTCB curtid ** 
                   EvtInv_part2 (set els sid (abssem (Int.sub n Int.one), wls)) tcblh tcbvl vhold v19 v20 v21 **
                   P).
Proof.
infer_solver 3%nat.
unfold EvtInv_part2 in *.
unfold ASemEIBs in *.
unfold AMuxEIBs in *.
unfold AMqEIBs in *.

sep pauto.
eapply mq_ecb_p_sem_minus_one_preserve; eauto.
eapply mux_ecb_p_sem_minus_one_preserve; eauto.
eapply sem_ecb_p_sem_minus_one_preserve; eauto.
eapply RH_SEM_EINFO_ECB_P_set_minus_one; eauto.
eapply RH_MUX_EIB_ECB_P_sem_minus_one_preserve; eauto.
eapply RH_EIB_ECB_Q_P_sem_minus_one_preserve; eauto.
Qed.

Lemma semacc_absimp_succ':
  forall P wls sid n tcbls tm curtid v' sch s els vhold
                               tcblh tcbvl v19 v20 v21,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu Int.zero n = true ->
    v' = Vint32 n ->
    absinfer sch
      ( <|| semacc (Vptr sid :: v' :: nil) ;; s ||> **
        HECBList els **
        HTCBList tcbls ** HTime tm ** HCurTCB curtid **
        EvtInv_part2 els tcblh tcbvl vhold v19 v20 v21 **
        P)
      ( <|| s ||> **
        HECBList (set els sid (abssem (Int.sub n Int.one), wls)) **
        HTCBList tcbls ** HTime tm ** HCurTCB curtid **
        EvtInv_part2 (set els sid (abssem (Int.sub n Int.one), wls)) tcblh tcbvl vhold v19 v20 v21 **
        P). 
Proof.
intros. subst.
eapply absinfer_trans.
2 : { eapply absinfer_seq_end; [idtac | idtac | eauto]; can_change_aop_solver. }
eapply absinfer_seq; try can_change_aop_solver.
infer_solver 3%nat.
unfold EvtInv_part2 in *.
unfold ASemEIBs in *.
unfold AMuxEIBs in *.
unfold AMqEIBs in *.
sep pauto.
eapply mq_ecb_p_sem_minus_one_preserve; eauto.
eapply mux_ecb_p_sem_minus_one_preserve; eauto.
eapply sem_ecb_p_sem_minus_one_preserve; eauto.
eapply RH_SEM_EINFO_ECB_P_set_minus_one; eauto.
eapply RH_MUX_EIB_ECB_P_sem_minus_one_preserve; eauto.
eapply RH_EIB_ECB_Q_P_sem_minus_one_preserve; eauto.
Qed.

Lemma semacc_absimp_succ_abt:
  forall P wls els sid n tcbls tm curtid v' sch,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu Int.zero n = true ->
    v' <> Vint32 n ->
    absinfer sch
      ( <|| semacc (Vptr sid :: v' :: nil) ||> ** HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| ABORT ||> ** HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P). 
Proof.
intros.
assert (can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
can_change_aop_solver.
do 3 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma semacc_absimp_succ_abt':
  forall P wls els sid n tcbls tm curtid v' sch s,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu Int.zero n = true ->
    v' <> Vint32 n ->
    absinfer sch
      ( <|| semacc (Vptr sid :: v' :: nil) ;; s ||> ** HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| ABORT ||> ** HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
intros.
assert (can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
do 3 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

(* new in OSSemAcceptProof.v *)

Require Import os_code_defs.
Require Import ucos_include.
Require Import Lia.
Require Import OSTimeTickPure.
(* Require Import sem_common. *)
(* Require Import seplog_trm_tacs. *)
Require Import gjb_common.
(* Require Import gjb_sem_common. *)
Require Import freeevtlist_lemmas.
Require Import semacc_pure.
Require Import sem_corecommu.
Require Import hoare_forward_tac_ext.

Lemma can_change_aop_aemp_isr_is:
can_change_aop aemp_isr_is.
Proof.
unfold aemp_isr_is.
pure_auto.
Qed.

Hint Resolve can_change_aop_aemp_isr_is: can_change_aop.

Local Open Scope code_scope.

Lemma OSSemAccept_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSSemAccept
                  vl logicl OSSemAcceptPre ct->
      Some r =
      BuildRetI os_internal OSSemAccept vl logicl OSSemAcceptPost ct->
      exists t d1 d2 s,
        os_internal OSSemAccept = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  rename v'2 into opv.
  change ((x :: nil) ++ opv :: nil) with (x :: opv :: nil).
  (* ENTER_CRITICAL *)
  hoare forward prim. 
 (* L1 - L2 *)
  destruct H1.
  subst.
  (* semacc (Vnull :: Vint32 opv :: nil)  *)
  assert (Hopv: opv = Vint32 Int.zero \/ opv <> Vint32 Int.zero) by tauto.
  destruct Hopv. 
  subst.
  (* semacc (Vnull :: Vint32 Int.zero :: nil) *)
  hoare unfold.
  lzh_hoare_if; pure_auto.
(*   subst. *)
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
(*   eapply absinfer_seq1. can_change_aop_solver. *)
  eapply semacc_absimp_null'; eauto.
  can_change_aop_solver.
  (* EXIT_CRITICAL *)
  hoare forward prim.
  sep cancel EvtInv. (* new add *)
  eauto. (* new add *)
  auto. (* new add *)
  go.
  (* return 0 *)
  hoare forward. 
  pure_auto; int auto.

  destruct Hif_false; tryfalse.
(*   tryfalse. *)

  (* Vint32 opv <> Vint32 Int.zero *)
  hoare abscsq.
  auto.
  eapply semacc_absimp_null_abt'; eauto.
(*   auto. *)
(*   auto. *)
  can_change_aop_solver.
  eapply absabort_rule.

  destruct H1; subst.
  simpl in H0. inverts H0. 
  destruct x0. 
  (* <|| semacc (Vptr (b, i) :: Vint32 opv :: nil) ||> *)
  lzh_hoare_if; pure_auto. 
  hoare unfold.
  tryfalse.

  hoare unfold.
  unfold EvtInv.

  rename v'18 into vcspace.
  rename v'19 into v19. 
  rename v'20 into v20. 
  rename v'21 into v21. 

  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst. (* addr of placeholder is now vhold_addr *)

  hoare_lifts_trms_pre (tcbllsegevaux,AOSTCBList,p_local).
  eapply backward_rule1. 
  introv Hsat. 
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  rename v'35 into locmp.
  rename v'36 into ptrmp.
  rename v'10 into els.
  rename v'18 into fecbh.
  rename v'19 into fecbvl.
  rename v'30 into semeibs.
  rename v'31 into muxeibs.
  rename v'32 into mqeibs.
  assert (Hevptr: get ptrmp ct = Some (Vnull, Vptr (b, i), Vnull)).
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  assert (Hevloc: get locmp ct = Some (V$ __EvLoc_normal)). 
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  assert (Hevt: is_evt els (b, i) \/ ptr_in_ecblist (Vptr (b, i)) fecbh fecbvl).  
  { eapply sem_ecb_nml; eauto. }

  destruct Hevt as [Hevt | Hfree]. 
  Focus 2.
  (* pevent points into list of free ECBs *)
  hoare_assert_pure (exists p, fecbh = Vptr p).
  {
    unfold ptr_in_ecblist in Hfree.
    lets Hptr: ptr_in_ecbsllseg_ptr Hfree.
    eauto.
  }
  hoare_split_pure_all.
  subst. 
  eapply backward_rule1.
  introv Hsat.
  unfold AOSEventFreeList in Hsat.
  unfold ecbf_sll in Hsat.
  sep normal in Hsat.
  sep_lifts_trms_in Hsat ecbf_sllseg.
  eapply ecbf_sllseg_split3_frm; eauto.
  hoare unfold.

  lzh_hoare_if. 
  2: {
    change (Int.eq ($ OS_EVENT_TYPE_UNUSED) ($ OS_EVENT_TYPE_SEM)) with false in Hif_false0. 
    inverts Hif_false0.
  }
  unfold AECBList.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Astruct, evsllseg).

  hoare_assert_pure (get els (v'43, Int.zero) = None).
  {
    get_hsat Hsat. 
    lets H00: semcre_ecblist_star_not_inh H2 Hsat.
    auto.
  }
  hoare_split_pure_all.
  rename H14 into Hnone.
  
  casetac opv (Vint32 Int.zero) Hopveq Hopvne.
  2: {
    hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid). 
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply semacc_absimp_no_sem_abt'; eauto.
    go. (* unfold CurTid. go. *)
    introv Hex. destruct Hex as (n & wls & Hsem).
    unfold get, EcbMap in Hnone.
    rewrite Hnone in Hsem. tryfalse.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semacc_absimp_no_sem'; eauto.
  go. (* unfold CurTid. go. *)
  introv Hex.
  destruct Hex as (n & wls & Hsem).
  unfold get, EcbMap in Hnone.
  rewrite Hnone in Hsem. tryfalse.
  eapply absinfer_eq.

  (* EXIT_CRITICAL *) 
  hoare forward prim.
  sep cancel Aier. 
 sep cancel CapabilityInv.
  sep cancel p_local.
  sep cancel tcbdllflag.
  sep cancel APthreadAttr.
  unfold EvtInv.
  unfold AECBList.
  sep pauto; eauto.
  sep cancel evsllseg.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  unfold AOSEventFreeList.
  unfold ecbf_sll.
  sep cancel OSEventFreeList.
  eapply ecbf_sllseg_compose3_frm; eauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel Aarray.
  sep cancel ecbf_sllseg.
  sep cancel ecbf_sllseg.
  unfold tcbllsegevaux.
  eapply llsegevaux_merge2_frm; eauto.
  sep cancel llsegevaux.
  eapply llsegevaux_merge_hd; eauto.
  unfolds; simpl; auto.
  go.
  auto.
  pure_auto.

  (* return 0 *) 
  hoare forward.
  splits; eauto.
  rewrite Int.unsigned_zero.
  auto with zarith.

  (* pevent points to an active ECB *) 

  unfold AECBList.
  hoare unfold.
  rename H2 into H_elp.
  assert (Hecb: exists ecb, get els (b, i) = Some ecb).
  {
    unfold is_evt in Hevt.
    destruct Hevt as [Hsem | [Hmux | Hque]].
    unfold is_sem in Hsem.
    simpljoin1; eexists; eauto.
    unfold is_mux in Hmux.
    simpljoin1; eexists; eauto.
    unfold is_que in Hque.
    simpljoin1; eexists; eauto.
  }
  destruct Hecb as (ecb & Hgetecb).
  destruct ecb. 
  lets Hctr: ECBList_P_get_ectr_some Hgetecb H_elp.
  destruct Hctr as (evl & etbl & petbl & Hgetectr).
  
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat evsllseg.
  eapply get_ectr_decompose; eauto.
  hoare unfold.

  hoare_assert_pure (length v'18 = length v'30).
  {
    get_hsat Hsat. 
    sep_lifts_trms_in Hsat evsllseg. 
    eapply evsllseg_aux in Hsat. 
    destruct Hsat.
    eauto. 
  }
  eapply pure_split_rule'; introv Heqlen.
  lets H00: ecblist_p_decompose H_elp; eauto. 
  destruct H00 as (els1 & els2 & x' & H''). 
  destruct H'' as (Hecbl1 & Hecbl2 & Hjo).      
  hoare_assert_pure (x' = Vptr (v'45, Int.zero)). 
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg. 
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  hoare_split_pure_all; subst. 
  
  assert (Hecbl' := Hecbl2).
  do 2 (rewrite ele_lst_cons in Hecbl').
  unfold ECBList_P in Hecbl'.
  fold ECBList_P in Hecbl'.
  destruct Hecbl' as (qid & Hqid & Hecbetbl & Hecbpetbl & Hex).
  inverts Hqid. 
  destruct Hex as (absmq & mqls' & v'' & Helptr & Hjo' & Hrlh & Hecbl20).
  unfold V_OSEventListPtr in Helptr.
  inverts Helptr.

  lzh_hoare_if.
  pure_auto.
  pure_auto.

  (* the concrete type is not OS_EVENT_TYPE_SEM *) 
  hoare_assert_pure (~exists n wls, get els (v'45, Int.zero) = Some (abssem n, wls)).
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply semacc_eventtype_neq_sem in Hsat; eauto.
    sep split in Hsat.
    auto.
    go.
  }
  hoare_split_pure_all.

  casetac opv (Vint32 Int.zero) Hopveq Hopvne.
  2: {
    hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid). 
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply semacc_absimp_no_sem_abt'; eauto.
    go. (* unfold CurTid. go. *)
    eapply absinfer_eq.
    apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid). 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semacc_absimp_no_sem'; eauto.
  go. (* unfold CurTid. go. *)
  eapply absinfer_eq.

  fold_AEventNode_r.
  (* EXIT_CRITICAL *)
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier. 
  sep cancel CapabilityInv.
  sep cancel APthreadAttr.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat (AEventNode,evsllseg v'4, evsllseg v'', OSEventList).
  eapply lzh_evsllseg_compose in Hsat; eauto.
  eapply AECBList_fold in Hsat; eauto. 
  unfold EvtInv.
  sep pauto; eauto.
  trycancel.
   sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  unfold tcbllsegevaux.
  eapply llsegevaux_merge2_frm; eauto.
  sep cancel llsegevaux.
  eapply llsegevaux_merge_hd; eauto.
  auto.
  go.

  (* return 0 *)
  hoare forward.
  splits; eauto. 
  rewrite Int.unsigned_zero.
  auto with zarith.
  rewrite Int.unsigned_zero.
  clear. mauto. 

  (* the concrete type is OS_EVENT_TYPE_SEM *)
  apply semacc_int_eq_true in Hif_false0.
  subst.
  hoare_assert_pure (exists wls, v'32 = DSem i3 /\ absmq = (abssem i3, wls)). 
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply semacc_triangle_sem in Hsat; eauto.
    2: { go. }
    sep split in Hsat.
    auto.
  }
  hoare_split_pure_all.
  destruct H2 as (Hdsem & Habssem).
  match type of Habssem with
    _ = (?e, ?w) =>
    assert (Hsem: get els (v'45, Int.zero) = Some (e, w))
  end.
  {
    eapply join_get_r; eauto.
    eapply join_get_l; eauto.
    rewrite get_a_sig_a; eauto. subst. auto.
  }

  (* cnt ′ =ₑ pevent ′ → OSEventCnt;ₛ *)
  hoare unfold.
  lzh_simpl_int_eq; subst.
  clear Hif_false.
  hoare forward.
  (* pure_auto. *)
  struct_type_match_solver.
  lzh_hoare_if.
  pure_auto.
  pure_auto.
  hoare forward.
  (* pure_auto. *)
  struct_type_match_solver.

(***************************** cnt = 0 ****************************)
  Focus 2.
  apply semacc_ltu_zero_false in Hif_false.
  subst.
  casetac opv (Vint32 Int.zero) Hopveq Hopvne.
  subst.
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).
  eapply abscsq_rule.
  auto.
  eapply semacc_absimp_no_source'; pauto.
  go. (* unfold CurTid. go.  *)
  eapply absinfer_eq.
  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.

  (* EXIT_CRITICAL *)
  hoare forward prim.
  sep cancel APthreadAttr.
  unfold EvtInv.
  sep pauto; eauto.
  sep cancel p_local.
  sep cancel Aier. 
 sep cancel CapabilityInv.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  unfold tcbllsegevaux.
  eapply llsegevaux_merge2_frm; eauto.
  sep cancel llsegevaux.
  eapply llsegevaux_merge_hd; eauto.
  sep cancel evaux_node.
  sep cancel llsegevaux.
  eauto.
  auto.
  go.
  (* return cnt *)
  hoare forward. 
  do 2 (split; try eauto).
  rewrite Int.unsigned_zero.
  rewrite <- Int16.unsigned_zero at 2.
  eapply Int16.unsigned_range_2.

  (* Vint32 opv <> Vint32 Int.zero *)
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).
  eapply abscsq_rule.
  auto. 
  eapply semacc_absimp_no_source_abt'; pauto.
  go. (* unfold CurTid. go.  *)
  eapply absinfer_eq.
  eapply absabort_rule. 

  (**************************** cnt = 0 finished ***************************)
  (******************************** cnt > 0 *******************************)
  casetac opv (Vint32 i3) Hopveq Hopvne.
  subst.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (evaux_node, llsegevaux v'42). 
  eapply llsegevaux_merge_hd in Hsat; eauto. 
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (llsegevaux v'2, llsegevaux (Vptr ct)).
  eapply llsegevaux_merge2_frm with (locmp:=set locmp ct (V$ __EvLoc_normal)); eauto.
  rewrite get_set_same; eauto.
  eapply backward_rule1.
  introv Hsat.
  eapply get_set_same in Hevloc.
(*   unfold set in Hevloc,Hsat. unfold EvAuxLocMap in Hevloc, Hsat. *)
  rewrite Hevloc in Hsat.
  eapply fold_EvtInv_part2; eauto.
  unfold tcbllsegevaux.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel llsegevaux.
  sep pauto.
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid, EvtInv_part2).
  eapply abscsq_rule.
  auto. 
  eapply semacc_absimp_succ'; pauto.  
  go. (* unfold CurTid. go.  *)
  eapply absinfer_eq.

  transform_pre semacc_new_fundation ltac:(sep cancel AEventData).
  clear Hrlh Hecbetbl. 
  hoare_split_pure_all.
  fold_AEventNode_r.
  compose_evsllseg.
  unfold TcbJoin in Hjo'.
  assert (Hjo_: EcbMod.joinsig (v'45, Int.zero) (abssem i3, v'10) mqls' els2).
  { clear -Hjo'. join auto. }
  lets Hnewjoin: ecb_get_set_join_join Hsem Hjo_ Hjo. 
  destruct Hnewjoin as (ml1n & F1 & F2).
  assert (
      ECBList_P v'4 Vnull
               (v'18 ++
                      ((V$ OS_EVENT_TYPE_SEM
                          :: Vint32 i1 :: Vint32 (i3-ᵢ$ 1) :: x0 :: x1 :: v'' :: Vint32 i0 :: x4 :: nil, etbl,petbl) :: nil)%list ++ v'19)
                (v'30 ++ (DSem (i3-ᵢ$ 1) :: nil) ++ v'31) 
                (EcbMod.set els (v'45, Int.zero) (abssem (i3-ᵢ$ 1), v'10)) v'11). 
  eapply semacc_compose_EcbList_P; eauto.

  fold_AECBList.
  hoare forward prim.
  sep cancel APthreadAttr.
  eapply fold_EvtInv_frm'.
  trycancel.
  sep cancel Aier. 
 sep cancel CapabilityInv.
  sep cancel p_local.
  sep cancel tcbdllflag.
  sep cancel EvtInv_part2.
  cancel_corecommuinv.
  
   (* PartitionInv *)
   Require Import sem_partition.
   cancel_partitioninv.
   eauto.
  (* end of PartitionInv *)

  eapply semacc_RH_TCBList_ECBList_P_hold; eauto.
  pauto.
  eapply rete_rule. 
  introv Hsat.
  split.
  sep normal. 
  do 4 eexists. exists i3. exists (Vptr (v'45, Int.zero)). eexists.
  sep_cancel_iers.
  sep cancel p_local.
  sep cancel cnt.
  sep cancel pevent.
  sep cancel A_dom_lenv.
  sep split; eauto.
  simpl. introv Hf. tryfalse.
  splits; eauto.
  clear -Hif_true.
  rewrite Intlt_true_is_Zlt in Hif_true.
  int auto.
  sep get rv.
  pure_auto.

  (* Vint32 opv <> Vint32 i2 *)
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).
  eapply abscsq_rule.
  auto. 
  eapply semacc_absimp_succ_abt'; pauto.
  go. (* unfold CurTid. go.  *)
  eapply absinfer_eq.
  eapply absabort_rule.

Qed.


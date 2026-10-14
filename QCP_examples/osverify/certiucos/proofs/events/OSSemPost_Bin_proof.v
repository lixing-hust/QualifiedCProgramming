Require Import os_sem.
Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import os_ucos_h.

Require Import sem_common.
Require Import sem_corecommu.
Require Import sempend_pure.
Require Import sempost_pure.
(* Require Import sempost_pure_ext.  *)
Require Import tcblist_setnode_lemmas.
Import OSQPostPure.
Require Import gjb_common.

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.

(* basically the same tac or lemma in OSSemPostProof.v *)

(* use this old hoare_if to avoid large modification *)
Ltac lzh_find_ret_stmt stmts :=
  match stmts with
    | sseq ?s ?rs =>
      match s with
        | srete _ => constr:(some 1%nat)
        | _ => lzh_find_ret_stmt rs
      end
    | srete _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac lzh_hoare_if2 :=
  lzh_hoare_unfold;
  hoare forward; 
  match goal with
    | |- {|_, _, _, _, _, _|} |- ?ct {{?p ** [|?v <> Vint32 Int.zero /\
                                       ?v <> Vnull /\
                                       ?v <> Vundef|]}} ?stmts {{_}} =>
      (* ** ac: idtac "if block proof"; *)
      let x := lzh_find_ret_stmt stmts in
        match x with
          | some _ => instantiate (1:=Afalse)
          | none _ => idtac
        end;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse

    | |- {|_, _, _, _, _, _|} |- ?ct {{_}} _ {{_}} => 
      (* ** ac: idtac "if all"; *)
      hoare forward;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse
      (* first proof if-true condition, then proof if-false condition *)
    | _ => pauto
  end.

Hint Resolve noabs_oslinv.
Hint Extern 2 (_ <= _) => apply Z.leb_le; trivial.

Require Import abs_infer_abt.

Lemma absinfer_seq1:
  forall (p : asrt) (s1 : absop)  (s2 : spec_code) (s1' : absop) (sc : ossched),
    can_change_aop p ->
    sc ⊢  <|| s1 ||>  ** p ⇒  <|| s1' ||>  ** p ->
    sc ⊢  <|| s1;; s2 ||>  ** p ⇒  <|| s1';; s2 ||>  ** p.
Proof.
  intros.
  eapply absinfer_seq; try eauto.
Qed.

Lemma absimp_sem_post_null_return:
  forall sid v' P sch s,
    sid = Vnull ->
    v' = (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) ->  
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (sem_post_bin (sid :: v' :: nil)) s ||> ** P) 
      (<|| s ||> ** P ). 
Proof.
  introv Hsid Hv' Hcop.
  eapply absinfer_trans. 
  simpl.
  eapply absinfer_choice1.
  3: eauto. 
  pure_auto. pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1. pure_auto.
  instantiate (1:=END (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))).
  infer_solver 0%nat. 
  eexists.
  splits; eauto.
  subst sid. auto. 
  eapply absinfer_seq_end; try pure_auto.
Qed.

Lemma absimp_sem_post_null_return_abt:
  forall sid v' P sch s,
    sid = Vnull ->
    v' <> (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) -> 
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (sem_post_bin (sid :: v' :: nil)) s ||> ** P) 
      (<|| ABORT ||> ** P ). 
Proof.
  introv Hsid Hv' Hcop.
  simpl.
  eapply absinfer_trans. 
  eapply absinfer_choice1.
  3: eauto. pure_auto. pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1; try pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  eapply absinfer_seq_abt; try pure_auto.
Qed.

Lemma absinfer_sem_post_no_active_evt_err: 
  forall a P els sch k s,
    can_change_aop P ->
    EcbMod.get els a = None ->
    k = V$ OS_ERR_EVENT_TYPE -> 
    absinfer sch
      (<|| spec_code_cons (sem_post_bin (Vptr a :: k :: nil)) s ||> ** HECBList els ** P)
      (<|| s ||> ** HECBList els ** P). 
Proof.
  introv Hcop Hnone Hk.
  subst.
  simpl spec_code_cons.
  infer_solver 1%nat.
Qed.

Lemma absinfer_sem_post_no_active_evt_err_abt: 
  forall a P els sch k s,
    can_change_aop P ->
    EcbMod.get els a = None ->
    k <> V$ OS_ERR_EVENT_TYPE -> 
    absinfer sch
      (<|| spec_code_cons (sem_post_bin (Vptr a :: k :: nil)) s ||> ** HECBList els ** P)
      (<|| ABORT ||> ** HECBList els ** P). 
Proof.
  introv Hcop Hnone Hne.
  simpl spec_code_cons.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver.
  2: eauto.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  can_change_aop_solver.
  2: eauto.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate (1:=HECBList els ** P).
  can_change_aop_solver.
  instantiate (1:=ABORT).
  eapply absinfer_abt.
  can_change_aop_solver.
  can_change_aop_solver.
  absimp_abt_solver.
  can_change_aop_solver.
  eapply absinfer_seq_abt. 
  can_change_aop_solver.
  can_change_aop_solver.
  intros; auto. 
Qed. 

Lemma absimp_sem_post_wrong_type_return:
  forall P els v' s sid sch,  
    can_change_aop P ->
    (exists d,
      EcbMod.get els sid = Some d /\ ~ (exists n wls, d = (abssem n, wls))) -> 
    v' = Vint32 (Int.repr OS_ERR_EVENT_TYPE) -> 
    absinfer sch
      (<|| spec_code_cons (sem_post_bin ((Vptr sid) :: v' :: nil)) s ||> ** HECBList els ** P) 
      (<|| s ||> ** HECBList els ** P). 
Proof.
  introv Hcop Hnsem Hv'.
  eapply absinfer_trans.
  simpl.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2. 
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto. 2: eauto. pure_auto.
  infer_solver 0%nat. 
Qed. 

Lemma absimp_sem_post_wrong_type_abt:
  forall P els v' s sid sch,  
    can_change_aop P ->
    (exists d,
      EcbMod.get els sid = Some d /\ ~ (exists n wls, d = (abssem n, wls))) -> 
    v' <> Vint32 (Int.repr OS_ERR_EVENT_TYPE) -> 
    absinfer sch
      (<|| spec_code_cons (sem_post_bin ((Vptr sid) :: v' :: nil)) s ||> ** HECBList els ** P) 
      (<|| ABORT ||> ** HECBList els ** P).  
Proof.
  introv Hcop Hnsem Hv'.
  destruct Hnsem. destruct H.
  simpl.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2. 
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto. 2: eauto. pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1; try pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  can_change_aop_solver.
  eapply absinfer_seq_abt; try pure_auto. 
Qed.   

Lemma absimp_sem_post_put_sem_return: 
  forall P els sid n wls sch v' s, 
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65535) = true ->
    v' = (Vint32 (Int.repr OS_NO_ERR)) -> 
    absinfer sch
      ( <|| spec_code_cons (sem_post_bin ((Vptr sid) :: v' :: nil)) s ||> ** HECBList els ** P) 
      ( <|| s ||> ** HECBList (EcbMod.set els sid (abssem (Int.add n Int.one), wls)) ** P).          
Proof.
  introv Hcop Habsem Hrgn Hv'.
  simpl.
  do 5 (
       eapply absinfer_trans;
       [eapply absinfer_choice2; [  | instantiate (1:=HECBList els ** P) | ]; pure_auto | ]).  
  infer_solver 0%nat.
Qed.

Lemma absimp_sem_post_put_sem_abt:  
  forall P els sid n wls sch v' s, 
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65535) = true ->
    v' <> (Vint32 (Int.repr OS_NO_ERR)) -> 
    absinfer sch
      ( <|| spec_code_cons (sem_post_bin ((Vptr sid) :: v' :: nil)) s ||> ** HECBList els ** P) 
      ( <|| ABORT ||> ** HECBList els ** P).   
Proof. 
  introv Hcop Habsem Hrgn Hv'.
  simpl.
  repeat
    (try eapply absinfer_trans;
     [eapply absinfer_choice2; [ | instantiate (1:=HECBList els ** P) | ]; pure_auto | ]).
  eapply absinfer_trans.
  eapply absinfer_seq1; try pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  can_change_aop_solver.
  eapply absinfer_seq_abt; try pure_auto. 
Qed.

Lemma absimp_sem_post_ovf_err_return:
  forall P els eid n wls sch v'1 s,  
    can_change_aop P ->
    EcbMod.get els eid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 1) = false ->
    v'1 = Vint32 (Int.repr OS_SEM_OVF) ->  
    absinfer sch
      (<|| spec_code_cons (sem_post_bin (Vptr eid :: v'1 :: nil)) s ||> ** HECBList els ** P) 
      (<|| s ||> ** HECBList els ** P).     
Proof.
  introv Hcop Hget Hltu Hv'1.
  simpl.
  infer_solver 3%nat.   
Qed. 

Lemma absimp_sem_post_ovf_err_abt: 
  forall P els eid n wls sch v'1 s,  
    can_change_aop P ->
    EcbMod.get els eid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 1) = false ->
    v'1 <> Vint32 (Int.repr OS_SEM_OVF) -> 
    absinfer sch
      (<|| spec_code_cons (sem_post_bin (Vptr eid :: v'1 :: nil)) s ||> ** HECBList els ** P) 
      (<|| ABORT ||> ** HECBList els ** P).   
Proof.
  introv Hcop Hget Hltu Hneq.
  simpl.
  do 3 (
       eapply absinfer_trans;
       [ eapply absinfer_choice2; [ | | eauto ]; pure_auto | ]
     ).
  eapply absinfer_trans. 
  eapply absinfer_choice1.
  3: eauto. pure_auto. pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  can_change_aop_solver.
  eapply absinfer_seq_abt; try pure_auto.
Qed.

Lemma absimp_sem_post_ex_wt_succ_return:
  forall P els sid tls t' n wls p st m sch v' s t ct sus,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    ~ wls = nil ->
    GetHWait tls wls t' ->
    TcbMod.get tls t' = Some (p, st, m, sus) ->
    v' = V$ OS_NO_ERR -> 
    absinfer sch
             ( <|| spec_code_cons (sem_post_bin ((Vptr sid) :: v' :: nil)) s ||> ** 
                             HECBList els ** HTCBList tls **
                             HTime t ** HCurTCB ct ** P ) 
             ( <|| isched;; END (Some (Vint32 (Int.repr OS_NO_ERR))) ;; s ||> **
                             HECBList (EcbMod.set els sid (abssem n, (remove_tid t' wls))) **
                             HTCBList (TcbMod.set tls t' (p, rdy, Vnull, sus)) **
                             HTime t ** HCurTCB ct ** P ). 
Proof.
  introv Hcop Hget Heq Hhw Htlsget Hv'.
  simpl.
  do 4 (
       eapply absinfer_trans; 
       [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ]
     ).
  eapply absinfer_trans. 
  eapply absinfer_choice1. 3: eauto. pure_auto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto. 
  instantiate (1:=HECBList (EcbMod.set els sid (abssem n, (remove_tid t' wls))) **
                           HTCBList (TcbMod.set tls t' (p, rdy, Vnull, sus)) ** HTime t ** HCurTCB ct ** P ).
  pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto. 
  instantiate (1:=HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
  pure_auto. pure_auto.
  instantiate (1:=END (Some (Vint32 (Int.repr OS_NO_ERR)))).
  infer_solver 0%nat. 

  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_eq. 
  eapply absinfer_seq_end; try pure_auto. 
Qed.

Lemma absimp_sem_post_ex_wt_succ_abt:
  forall P els sid tls n wls sch v' s,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    ~ wls = nil ->
    v' <> V$ OS_NO_ERR -> 
    absinfer sch
             ( <|| spec_code_cons (sem_post_bin ((Vptr sid) :: v' :: nil)) s ||> **
                   HECBList els ** HTCBList tls ** P )  
             ( <|| ABORT ||> ** HECBList els ** HTCBList tls ** P ). 
Proof.
  introv Hcop Hget Hneq Hv'.
  simpl.
  do 4 (
       eapply absinfer_trans; 
       [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ]
     ).
  eapply absinfer_trans. 
  eapply absinfer_choice1.
  3: eauto. pure_auto. pure_auto.
  eapply absinfer_trans. 
  eapply absinfer_seq1. pure_auto.
  eapply absinfer_choice2; try pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1. pure_auto. 
  eapply absinfer_abt; pure_auto.
  absimp_abt_solver.
  instantiate (1:=HECBList els ** P).
  instantiate (2:=sem_post_ex_wt_succ (|Vptr sid :: v' :: nil|)). 
  instantiate (2:=s0).
  sep pauto.
  can_change_aop_solver.
  eapply absinfer_seq_abt; try pure_auto. 
Qed. 

Require Import OSTimeTickPure. 
Require Import sem_lab.

Require Import seplog_trm_tacs.
Require Import evauxvar_lemmas.
Require Import evaux_pure.

Require Import freeevtlist_lemmas. 

Require Import gjb_sem_common.
Require Import hoare_forward_tac_ext.
Require Import evtinv_lemmas.
Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.
Lemma OSSemPostBin_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSSemPostBin
                  vl logicl OSSemPostBinPre ct->
      Some r =
      BuildRetI os_internal OSSemPostBin vl logicl OSSemPostBinPost ct->
      exists t d1 d2 s,
        os_internal OSSemPostBin = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.

  hoare forward prim.
  hoare unfold.
  
  lzh_hoare_if2.
  hoare forward prim.
  sep pauto. auto.
  pure_auto.
  hoare_lifts_trms_pre Aop.
  assert (Hor: v'2 <> (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) \/ 
                 v'2 = (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) by tauto. 
  inversion Hor.
  (* v'2 <> ... *)  
  eapply abscsq_rule.
  pure_auto.
  (* change ((x :: nil) ++ v'1 :: nil) with (x::v'1::nil). *)
  eapply absimp_sem_post_null_return_abt; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq. 
  eapply absabort_rule.
  (* v'2 = ... *)  
  eapply abscsq_rule.
  pure_auto.
  (* change ((x :: nil) ++ v'1 :: nil) with (x::v'1::nil). *) 
  eapply absimp_sem_post_null_return; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq.
  (* return in case pevent = NULL *)
  hoare forward.

  rename v'12 into els.

  hoare unfold.
  unfold EvtInv.
  rename v'20 into vcspace.
  rename v'21 into v21. 
  rename v'22 into v22. 
  rename v'23 into v23.   
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
  rename v'36 into ptrmp.  
  assert (Hevptr: get ptrmp ct = Some (Vnull, Vptr x, Vnull)). 
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  rename v'35 into locmp.
  assert (Hevloc: get locmp ct = Some (V$ os_code_defs.__EvLoc_normal)). 
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  rename v'1 into fecbh.
  rename v'12 into fecbvl. 
  rename v'30 into semeibs.
  rename v'31 into muxeibs.
  rename v'32 into mqeibs.
  
  assert (Hevt: is_evt els x \/ ptr_in_ecblist (Vptr x) fecbh fecbvl).  
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
  Set Printing Depth 99.
  lzh_hoare_if. 
  2: {
    change (Int.eq ($ OS_EVENT_TYPE_UNUSED) ($ OS_EVENT_TYPE_SEM)) with false in Hif_false. 
    inverts Hif_false.
  }
  unfold AECBList.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Astruct, evsllseg).

  hoare_assert_pure (get els (v'44, Int.zero) = None).
  {
    get_hsat Hsat. 
    lets H00: semcre_ecblist_star_not_inh H0 Hsat. 
    auto.
  }
  hoare_split_pure_all.
  rename H15 into Hnone. 
  rename v'2 into etype. 
  casetac etype (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) Heeq Hene.
  2: {
    hoare_lifts_trms_pre (Aop, absecblsid).  
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absinfer_sem_post_no_active_evt_err_abt; try pure_auto.
    go. unfold CurTid. go.
    eapply absinfer_eq. 
    apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, absecblsid).  
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_post_no_active_evt_err; eauto. 
  go. unfold CurTid. go.
  eapply absinfer_eq.

  (* EXIT_CRITICAL *) 
  hoare forward prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv. 
  sep cancel Aier.
  unfold EvtInv.
  unfold AECBList.
  sep normal.
  sep eexists.
  sep cancel OSEventList.
  sep cancel evsllseg.
  sep split; eauto.
  sep cancel tcbdllflag.
  sep cancel p_local.
  trycancel_EvtInv.
  sep pauto. 

(*   instantiate (2:=v'3++(V$ OS_EVENT_TYPE_UNUSED :: Vint32 i0 :: Vint32 i2 :: x1 :: x2 :: v'31 :: Vint32 i :: x5 :: nil) :: v'16). 
  instantiate (2:=Vptr v'1).  *)
  unfold AOSEventFreeList.
  sep normal.
  sep cancel OSEventFreeList.
  unfold ecbf_sll.
  sep_lifts_trms ecbf_sllseg. 
  eapply ecbf_sllseg_compose3_frm; eauto. 
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel ecbf_sllseg.
  sep cancel ecbf_sllseg.

  2: { go. }
  2: { go. }
  2: eauto.
  sep cancel Aarray.
  unfold tcbllsegevaux.
  eapply llsegevaux_merge2_frm; eauto.
  sep cancel llsegevaux.
  eapply llsegevaux_merge_hd; eauto.
  go.

  (* return OS_ERR_EVENT_TYPE *) 
  hoare forward. 

  (* pevent points to an active ECB *) 
  Set Printing Depth 99.
  unfold AECBList.
  hoare unfold.
  rename H0 into H_elp. (* ECBList_P ... *)  
  assert (Hecb: exists ecb, get els x = Some ecb). 
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

  hoare_assert_pure (length v'12 = length v'31). 
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
  hoare_assert_pure (x' = Vptr (v'46, Int.zero)).  
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg. 
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  hoare_split_pure_all; subst. 
  
  assert (Hecbl' := Hecbl2).
  (* do 2 (rewrite ele_lst_cons in Hecbl').  *)
  unfold ECBList_P in Hecbl'.
  fold ECBList_P in Hecbl'.
  destruct Hecbl' as (qid & Hqid & Hecbetbl & Hex).
  inverts Hqid. 
  destruct Hex as (Hpetbl & absmq & mqls' & v'' & Helptr & Hjo' & Hrlh & Hecbl20).
  unfold V_OSEventListPtr in Helptr.
  inverts Helptr.
  
  lzh_hoare_if.
  pure_auto.
  pure_auto.
  
  (* the concrete type is not OS_EVENT_TYPE_SEM *) 
  hoare_assert_pure (~exists n wls, get els (v'46, Int.zero) = Some (abssem n, wls)).
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply semacc_eventtype_neq_sem in Hsat; eauto.
    sep split in Hsat.
    auto.
    go.
  }
  hoare_split_pure_all.

  rename v'2 into etype. 
  casetac etype (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) Heeq Hene.
  2: {
    hoare_lifts_trms_pre (Aop, absecblsid).  
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absimp_sem_post_wrong_type_abt; eauto. 
    go. unfold CurTid. go.
    unfold get, EcbMap in Hgetecb.
    unfold get, EcbMap in H0.
    rewrite Hgetecb in H0. 
    exists (e, w). simpljoin1. splits; auto.
    introv Hf. apply H0. simpljoin1. do 2 eexists; eauto. 
    eapply absinfer_eq.
    apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, absecblsid).  
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absimp_sem_post_wrong_type_return; eauto.  
  go. unfold CurTid. go.
  unfold get, EcbMap in Hgetecb.
  unfold get, EcbMap in H0.
  rewrite Hgetecb in H0.
  exists (e, w). simpljoin1. splits; auto.
  introv Hf. apply H0. simpljoin1. do 2 eexists; eauto.   
  eapply absinfer_eq.

  fold_AEventNode_r. 
  (* EXIT_CRITICAL *)
  hoare forward prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel tcbdllflag. 
  sep cancel p_local.
  sep cancel Aier.
  unfold EvtInv.
  sep pauto.
  trycancel_EvtInv. 
  get_hsat Hsat.
  eapply lzh_evsllseg_compose in Hsat; eauto.
  eapply AECBList_fold in Hsat; eauto. 
  sep cancel AECBList.
  unfold tcbllsegevaux.
  eapply llsegevaux_merge2_frm; eauto.
  sep cancel llsegevaux.
  eapply llsegevaux_merge_hd; eauto.
  go.
  auto. auto. auto.
  go.
  (* return OS_ERR_EVENT_TYPE *) 
  hoare forward.
  
  (* the concrete type is OS_EVENT_TYPE_SEM *)
  apply semacc_int_eq_true in Hif_false. 
  subst.
  hoare_assert_pure (exists wls, v'35 = DSem i2 /\ absmq = (abssem i2, wls)).  
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply semacc_triangle_sem in Hsat; eauto.
    2: go. 
    sep split in Hsat.
    auto.
  }
  hoare_split_pure_all.
  destruct H0 as (Hdsem & Habssem). 
  match type of Habssem with
    _ = (?e, ?w) =>
    assert (Hsem: get els (v'46, Int.zero) = Some (e, w)) 
  end.
  {
    eapply join_get_r; eauto.
    eapply join_get_l; eauto.
    rewrite get_a_sig_a; eauto. subst. auto.
  }

  subst.

  repeat match goal with H: get_ectr _ _ _ = _ |- _ => clear H end.  
  (* lzh_simpl_int_eq.  *) 
  hoare_unfold.
  lzh_hoare_if2.

  Focus 2. 
  lzh_hoare_if2. 
  
  lzh_simpl_int_eq. 
  unfold AOSTCBPrioTbl. 
  hoare_split_pure_all. 
  assert (Hnil : v'6 = nil). 
  {
    lets Fnil: sempost_grp_wls_nil' H0 Hecbetbl; eauto.  
  }
  subst v'6. 
  hoare forward. 
  struct_type_match_solver.  
  
  assert (Hret: v'2 <> Vint32 (Int.repr OS_NO_ERR) \/ v'2 = Vint32 (Int.repr OS_NO_ERR)) 
    by tauto.
  inversion Hret as [Hretcase | Hretcase]. 
  (* v'2 <> ... *)
  hoare_lifts_trms_pre (Aop, absecblsid).   
  eapply abscsq_rule.
  pure_auto. 

  eapply absimp_sem_post_put_sem_abt; eauto. 
  go.   clear -H16. int auto. 
  eapply absinfer_eq. 
  eapply absabort_rule.

  hoare_lifts_trms_pre (Aop, absecblsid). 
  eapply abscsq_rule.
  pure_auto. 
  eapply absimp_sem_post_put_sem_return; eauto. 
  go. 
  clear -H16. int auto.
  eapply absinfer_eq. 

  eapply backward_rule1.
  intros; eapply sempost_inc_cnt_prop; eauto.
  sep cancel AEventData;try exact_s; sep pauto.
  clear -H16. int auto.

  hoare_split_pure_all. 
  clear Hrlh Hecbetbl. 

  hoare forward prim.
  unfold EvtInv.
  unfold AECBList.
  sep pauto.
  eapply lzh_evsllseg_compose.
  sep cancel evsllseg.
  sep cancel evsllseg.
  unfold AEventNode.
  sep cancel AEventData.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel Aier.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  instantiate(19:= etbl).
  sep pauto; eauto.
  sep cancel Astruct.
  sep cancel Aarray.
  unfold AOSTCBPrioTbl.
  sep pauto.
  trycancel_EvtInv.
  sep cancel p_local.
  (* 2: { splits; eauto. }
  unfold ACNU.
  sep pauto. *)
  sep_lifts_trms (tcbllsegevaux).
  unfold tcbllsegevaux.
  sep_lifts_trms llsegevaux.
  eapply llsegevaux_merge2_frm; eauto.
  sep cancel llsegevaux.
  eapply llsegevaux_merge_hd; eauto.
  sep cancel evaux_node.
  sep cancel llsegevaux.
  unfold ASemEIBs in *.
  sep pauto. sep cancel ASeminfo. 
  sep cancel ASemCap. 
  2: { eapply RH_SEM_EINFO_ECB_P_sem_inc; eauto. }
  eapply AMuxEIBs_sem_inc_preserve; eauto. 
  sep cancel AMuxEIBs.
  eapply AMqEIBs_sem_inc_preserve; eauto.
  cancel_corecommuinv. 
  sep cancel AMqEIBs.
  
  (* PartitionInv *)
  Require Import sem_partition.
  cancel_partitioninv.
  eauto.
  (* end of PartitionInv *)

  auto.
  auto. 
  auto. (* EIBArray_P ... *)
  splits; auto.
  assert(Int.unsigned (i2 +ᵢ  $ 1) <= 65535).
  { clear -H16 H28.  eapply sempost_vallist_match_assert1; eauto.
    assert(Int.ltu i2 ($ 65535) = true).
    int auto. auto. }
  go.
  unfolds; simpl; auto.
  eauto.
  eauto.
  eapply mq_ecb_p_sem_inc_preserve; eauto. 
  eapply mux_ecb_p_sem_inc_preserve; auto.
  eapply sem_ecb_p_sem_inc_preserve; auto. 

  assert (Heget: EcbMod.get els (v'46, Int.zero) = Some (abssem i2, nil)) by auto.
  assert (Hjsig: EcbMod.joinsig (v'46, Int.zero) (abssem i2, nil) mqls' els2) by auto.  
  lets Hnewjoin: ecb_get_set_join_join Heget Hjsig Hjo. 
  destruct Hnewjoin as [? [? ?]]. 
  eapply semacc_compose_EcbList_P; eauto.

  eapply sempost_inc_RH_TCBList_ECBList_P_hold; eauto.
  clear -H16. (* Int.ltu _ ($ 1) = true *)
  int auto. 
  pauto. (* GoodFrm *) 
  (* RETURN ′ OS_NO_ERR *)
  hoare forward.

  introv Hf. simpl in Hf. inverts Hf. 
  
  (********************** cnt = 1, overflow! ************************)
  lzh_simpl_int_eq.
  unfold AOSTCBPrioTbl.
  hoare_split_pure_all.
  assert (Hnil : v'6 = nil). 
  {
    lets Fnil: sempost_grp_wls_nil' H0 Hecbetbl; eauto.
  }
  subst v'6. 

  assert (Hv'1cs:
            v'2 <> Vint32 (Int.repr OS_SEM_OVF) \/
            v'2 = Vint32 (Int.repr OS_SEM_OVF)) by tauto. 
  inversion Hv'1cs.
  (* v'2 <> ... *) 
  hoare_lifts_trms_pre (Aop, absecblsid).   
  (* hoare lifts (29::20::nil)%nat pre.  *)
  eapply abscsq_rule.
  pure_auto.
  eapply absimp_sem_post_ovf_err_abt; eauto.
  go. unfold CurTid. go. 
  eapply absinfer_eq. 
  eapply absabort_rule.
  (* v'2 = ... *)
  hoare_lifts_trms_pre (Aop, absecblsid). 
  (* hoare lifts (29::20::nil)%nat pre.  *)
  eapply abscsq_rule.
  pure_auto.
  eapply absimp_sem_post_ovf_err_return; eauto.
  go. unfold CurTid. go. 
  eapply absinfer_eq. 

  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.

  hoare forward prim.
  unfold AOSTCBPrioTbl.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep pauto.
  unfold EvtInv.
  sep pauto.
  trycancel_EvtInv.
  unfold tcbllsegevaux.
  sep_lifts_trms llsegevaux.
  eapply llsegevaux_merge2_frm; eauto.
  sep cancel llsegevaux.
  eapply llsegevaux_merge_hd; eauto.
  sep cancel evaux_node.
  sep cancel llsegevaux.
  sep pauto.
  auto. auto. auto.
  auto. auto. auto. auto.
  go. 

  (* return OS_SEM_OVF *) 
  hoare forward.

  (******************************* OSEventGrp != 0 ******************************) 
  inverts Hsem.  
  hoare forward.

  hoare_unfold. 
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.
  hoare_split_pure_all.
  destruct H16. 
  
(****************************** L2: event_task_rdy ******************************)
  hoare_lifts_trms_pre (Aisr, Ais, aemp_isr_is).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  destruct H37.  
  hoare forward.

  unfold_msg.
  sep cancel AEventData.
  sep cancel p_local.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel AOSPostEventTbl.
  sep cancel AOSRdyTblGrp.
  eapply tcbdllseg_compose.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.

  eauto.
  unfold V_OSEventGrp; simpl. auto.
  pauto.
  pauto.  eauto.  eauto. 
  unfolds; simpl; eauto.
  eauto. eauto.
  splits; eauto. 
  struct_type_match_solver.
  splits.
  unfold V_OSEventGrp; simpl; eauto.
  lzh_simpl_int_eq. auto.
  simpl; eauto.
  simpl; eauto.
  pure_auto.

  (* ** ac: SearchAbout TCBList_P. *)
  (* ** ac: Locate tcbdllseg_get_last_tcb_ptr. *)
  (* ** ac: Check tcbdllseg_get_last_tcb_ptr. *)
  eapply TCBList_P_Combine.
  eapply tcbdllseg_get_last_tcb_ptr.
  instantiate (5:=s).
  sep cancel (tcbdllseg v'5).
  sep pauto.
  2:eauto.
  2:eauto.
  eauto.
  
  eauto.
  eauto.
  eauto.

  eapply tcbdllseg_combine_ptr_in_tcblist.
  instantiate (7:=s).
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  eauto.

  pure_auto.
  pure_auto.

  intros.
  sep auto.

  intros.
  sep auto.

  (** event task rdy precondition finished **)
  Set Printing Depth 500.
  hoare unfold.

  remember (spec_code_cons
                                              (sem_post_bin ((Vptr (v'46, Int.zero) :: nil) ++ v'2 :: nil)) v'0) as abs_code.
  inverts H73.
  subst v'67.

  (** renameing **)
  rename v'46 into pevent_addr.
  rename ct into ctcb.
  rename v'97 into htcb_addr. (** highest tcb in pevent waitlist **)
  rename H46 into Hhtcb. 
  rename H67 into Hctcb_in_tcblist.  
  rename v'68 into tcblist_head. 
  rename v'7 into tcblist_seg1.
  rename v'8 into ctcb_node.
  rename v'9 into tcblist_seg2.
  rename H50 into Hrel_et. 

  (* ** ac: Print prio_in_tbl. *)
  rename v'54 into rtbl. 
  (* ** ac: Print TCBList_P. *)

  rename v'50 into tcbls. 
  rename v'35 into tcbls1. 
  rename v'43 into tcbls2.
  (** tcbls = tcbls1 ++ tcbls2, tcbls2 = cur_node ++ tcbls2' **)
  
  remember (tcblist_seg1 ++ ctcb_node :: tcblist_seg2) as tcblist.
  
  rename v'92 into hprio. 
  assert (exists hprio', hprio = Vint32 hprio'). 
  {
    clear - H77. (** struct_type_vallist_match **)
    rename H77 into H. 
    unfold struct_type_vallist_match in H.
    unfold OS_TCB_flag in H.
    unfold struct_type_vallist_match' in H.
    mytac.
    clear - H5.
    (* ** ac: SearchAbout (rule_type_val_match Int8u _). *)
    apply rule_type_val_match_int8u_elim in H5.
    mytac.
  }
    
  destruct H41.  
  subst hprio.
  rename x into hprio.
  
  rename v'86 into hnext. 
  rename v'93 into htcbx.
  rename v'94 into htcby.
  rename v'95 into hbitx.
  rename v'96 into hbity. 

  (* ** ac: Check tcblist_get_TCBList_P_get. *)
  (* ** ac: Check sem_post_get_tcb_stat. *)
  (* ** ac: Check rh_tcblist_ecblist_p_post_exwt_aux_sem. *)
  (* ** ac: Check rh_tcblist_ecblist_p_post_exwt_sem. *)
  assert (Hhtcb_get: exists st m sus, get tcbls (htcb_addr, Int.zero) = Some (hprio, st, m, sus)).
  {
    eapply tcblist_get_TCBList_P_get.
    eauto.
    pure_auto.
    eauto.
  }

  destruct Hhtcb_get as (st & msg & sus & Hhtcb_get).

  assert (Hs1: Int.unsigned v'80 <= 7). 
  {
    (* ** ac: Check osunmapvallist_prop. *)
    clear - H51 H27. 
    apply osunmapvallist_prop in H27.
    mytac.
    rewrite H in H51.
    inverts H51. 
    pure_auto.
  }
  
  assert (Hs2: Int.unsigned v'81 <= 255).
  {
    (* ** ac: Check array_int8u_nth_lt_len. *)
    clear - H52 Hs1 H63 H24. 
    assert (Z.to_nat (Int.unsigned v'80) < length v'60)%nat. 
    {
      rewrite H24; unfold OS_EVENT_TBL_SIZE.
      mauto.
    }
    lets Hx: array_int8u_nth_lt_len H63 H. 
    mytac.
    rewrite H52 in H0. 
    inverts H0.
    auto.
  }

  assert (Hs3: Int.unsigned v'79 <= 7). 
  {
    clear - H53 Hs2.  
    lets Hx: osunmapvallist_prop Hs2.
    mytac.
    rewrite H in H53; inverts H53.  
    pure_auto.
  }

  rename v'6 into pwls.
  (* ** ac: Check post_exwt_succ_pre_sem. *)
  generalize Hhtcb_get; intro Hhtcb_join.
  apply map_join_get_sig in Hhtcb_join.
  destruct Hhtcb_join as (tcbls' & Hhtcb_join).
  assert (Hpre: pwls <> nil /\ GetHWait tcbls pwls (htcb_addr, Int.zero) /\
                TcbMod.get tcbls (htcb_addr, Int.zero) = Some (hprio, st, msg, sus) /\
                hprio = ((v'80<<ᵢ$ 3) +ᵢ  v'79)). 
  {
    apply map_join_get_sig in Hhtcb_get.
    destruct Hhtcb_get.
    (* ** ac: Check post_exwt_succ_pre_sem. *)
    apply semacc_int_eq_false in H0. 
    eapply post_exwt_succ_pre_sem; eauto.
  }

  destruct Hpre as [ ? [? [? ?]]].
  subst hprio.
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).
  assert (Hv'1cs: v'2 <> Vint32 (Int.repr OS_NO_ERR) \/
                  v'2 = Vint32 (Int.repr OS_NO_ERR)) by tauto. 
  inversion Hv'1cs.
  (* v'2 <> ... *)
  eapply abscsq_rule.
  auto.
  eapply absimp_sem_post_ex_wt_succ_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule.
  (* v'2 = ... *) 
  eapply abscsq_rule.
  auto.
  eapply absimp_sem_post_ex_wt_succ_return; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  unfold AEventData. 
  unfold_msg.
  hoare_split_pure_all.
  destruct H48. 
  inverts H48.  
  rename v'5 into pevent_addr.

  unfolds in H56; simpl in H56; inverts H56.  
  (* ** ac: Check sem_post_get_tcb_stat. *)
  rename v'60 into etbl. 

  rename H72 into Htcblist_p. 
  lets Hhtcb_node: TCBList_P_tcblist_get_TCBNode_P Htcblist_p Hhtcb Hhtcb_get.
  generalize Hhtcb_node; intro Htmp.
  unfolds in Htmp.
  mytac.
  inverts H48; inverts H56.  

  rename H67 into Hh_tcbblk.
  rename H72 into Hh_tcbstat.  
  unfolds in Hh_tcbblk.
  mytac.
  inverts H47. 
  inverts H67. inverts H85; inverts H73; inverts H56; inverts H48; inverts H72.

  rename v'80 into p1.
  rename v'79 into p2. 
  remember ((p1<<ᵢ$ 3) +ᵢ  p2) as hprio.
  
  (* ** ac: Check sem_post_get_tcb_stat. *)

  assert (Hx:  x7 = $ OS_STAT_SEM \/ x7 = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)).
  {
    clear - Hrel_et.
    unfolds in Hrel_et.
    auto.
  }
(*   subst v'90. *)

  assert (Hp1: (hprio >>ᵢ $ 3) =  p1).
  {
    subst hprio.
    clear - Hs1 Hs2 Hs3.
    clear Hs2.
    mauto.
  }

  assert (Hp2: hprio &ᵢ ($ 7) = p2).
  {
    subst hprio.
    clear - Hs1 Hs3.
    mauto.
  }

  assert (Hs4: Int.unsigned v'98 <= 255). 
  {
    clear - Hs1 H43 H75 H60. 
    assert (Z.to_nat (Int.unsigned p1) < length rtbl)%nat.
    {
      rewrite H75. 
      unfold OS_RDY_TBL_SIZE.
      mauto.
    }
    lets Htmp: array_int8u_nth_lt_len H60 H. 
    mytac.
    rewrite H43 in H0. 
    inverts H0.
    auto.
  }
  
  (* ** ac: Check set_node_elim_hoare. *)
  
  assert (Htmp: v'82 = $ 1 <<ᵢ p2). 
  {
    eapply math_mapval_core_prop.
    clear - Hs3.
    mauto.
    auto.
  }
  subst v'82.
  
  assert (Hno_dup: R_Prio_No_Dup tcbls).
  {
    clear - H39.
    unfolds in H39. 
    mytac.
  }
  (** zhang hui's lemma **)
  hoare_lifts_trms_pre tcbdllseg. 
  (* hoare lift 19%nat pre. *)
  eapply set_node_elim_hoare_sus with (tid:=ctcb) (tcbls:=tcbls); eauto.
  {
    eapply TCBNode_P_set_rdy_gen; auto.
    2:eauto.
    rewrite Hp1.
    apply nth_val'2nth_val; eauto.
    2: eauto.
    destruct Hx; substs.
    assert (Hsus: sus = false) by
    (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: sus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    change (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_SEM)) with ($ OS_STAT_SUSPEND).
    auto.
  }
  { destruct sus eqn: eq1; auto.
    unfolds.
    rewrite Hp1.
    rewrite Hp2.
    do 2 eexists.
    splits; eauto.
  }
  {
    unfolds.
    unfold V_OSTCBNext , V_OSTCBPrev.
    simpl.
    auto.
  }

  (************************* exit critical ***********************************)
  assert (Heq_sus: Int.eq (x7&ᵢInt.not ($ OS_STAT_SEM)) ($ OS_STAT_RDY) = negb sus).
  { change ($ OS_STAT_RDY) with Int.zero.
    destruct Hx; subst x7.
    assert (Hsus: sus = false) by
    (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: sus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    change (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_SEM)) with ($ OS_STAT_SUSPEND).
    auto.
   }

  hoare_split_pure_all.
  subst hprio.
  rewrite Hp1 in *.
  rewrite Hp2 in *.
  hoare_lifts_trms_pre (Aisr, Ais, Aier).
  transform_pre add_aemp_isr_is_prop ltac:(sep cancel Aisr; sep cancel Ais;(*  sep cancel Aier; *) sep cancel aemp_isr_is). 
  Ltac hoare_exit_critical2 :=
    match goal with
    | |- {|_ , _, ?li , _, _, _|}|- _ {{?P}} (sprim excrit) {{_}} =>
      match find_aop P with
      | some ?n =>
        hoare lifts (n::nil) pre;
        eapply excrit1_rule'_ISnil_ISRemp'''_lg(* excrit1_rule'_ISnil_ISRemp''' *);
        [ intros; try (unfold OldOSInvWL); (*sep pauto;*)trycancel
        | idtac
        ]
      | _ => fail 1
      end
    end.
  Ltac hoare_forward_prim'2 :=
    let s := fresh in
    let H := fresh in
    match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} (sseq _ _) {{ _ }} =>
      eapply seq_rule; [ hoare_forward_prim'2
                       | try hoare_invchange ]
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
      eapply forward_rule2; [ first [ hoare_enter_critical
                                    | hoare_exit_critical2
                                    | idtac ]
                            | first [ intros s H; exact H
                                    | sep pauto ] ]
    end.
  hoare_forward_prim'2. 
  (*hoare forward prim.*)
  unfold EvtInv.
  sep normal.
  sep eexists.
  trycancel_EvtInv.
  sep cancel Aier.
  sep cancel p_local.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep pauto.
  
  (** AECBList **)
  unfold AECBList.
  sep normal.
  sep eexists.
  sep cancel OSEventList. 
  eapply lzh_evsllseg_compose.
  sep cancel evsllseg.
  sep cancel evsllseg.
  unfold AEventNode.
  unfold_msg.
  sep normal.
  sep eexists.
  sep split; auto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel AOSPostEventTbl.
  instantiate (29 := DSem i2). 
  unfold AEventData.
  sep split; auto.

  (** AOSTCBPrioTbl **)
  unfold AOSTCBPrioTbl.
  sep normal.
  sep eexists.
  sep split; auto.
  sep cancel vhold_addr. (* PV vhold_addr .. *)
  sep cancel GAarray.
  sep cancel OSPlaceHolder.

  (** AOSTCBList **)
  unfold AOSTCBList.
  sep normal.
  sep eexists.
  sep split; auto.
  sep cancel OSTCBList. 
  sep cancel tcbdllseg.
  sep cancel OSTCBCur. 
  sep cancel tcbdllseg.
  
  (** tcbdllflag **) 
  get_hsat Hsat.
  sep_lifts_trms_in Hsat tcbdllflag.
  unfold AEventData in Hsat. 
  eapply tcbdllflag_set_node in Hsat; eauto.
  sep cancel tcbdllflag. 
  2: { unfold same_prev_next. simpl. splits; auto. }

  sep_lifts_trms_in Hsat (evaux_node, llsegevaux v'42).
  eapply llsegevaux_merge_hd in Hsat; eauto. 
  sep_lifts_trms_in Hsat (llsegevaux tcblist_head, llsegevaux (Vptr ctcb)). 
  eapply llsegevaux_merge2_frm in Hsat; eauto. 
  unfold tcbllsegevaux.
  sep_lifts_trms llsegevaux.
  eapply llsegevaux_set_node; eauto.
  2: { unfold same_prev_next. simpl. splits; auto. } 
  sep cancel llsegevaux.
  eapply ASemEIBs_sem_set_wls'_preserve; eauto.
  sep cancel ASemEIBs. 
  eapply AMuxEIBs_sem_set_wls'_preserve; eauto.
  sep cancel AMuxEIBs. 
  eapply AMqEIBs_sem_set_wls'_preserve; eauto. 
  sep cancel AMqEIBs. 
  sep cancel AOSTCBFreeList.
  sep cancel AOSRdyTblGrp.
  sep cancel absptlsid.
  cancel_corecommuinv. 
  cancel_partitioninv.
  eauto.

  (** TCBList_P **)
  rewrite Heq_sus. rewrite negb_if.
  eauto.
  rewrite Heq_sus. rewrite negb_if.
  eauto.
  eauto.
  split; auto.
  eauto. eauto. 
  (** R_PrioTbl_P **)
  eapply r_priotbl_p_set_hold; auto; eauto.
  eauto.
  split; auto.

  clear - H28. 
  int auto.

  (** ecblist_p **)
  eapply ecblist_p_post_exwt_hold_sem
    with (v'12:=v'58) (v'39:=p2) (v'69:=v'81) (v'38:=p1) (v'13:=etbl) (v'36:=v'53); eauto.
  eapply rl_etbl_ptbl_p; auto; eauto.
  lzh_simpl_int_eq; auto.
  
  clear - Hs3.
  mauto.

  (* RL_Tbl_Grp_P *)
  eauto.
  go. eauto.
  go.
  go. eauto. eauto.
  split; auto.
  go.
  simpl. eauto. eauto.

  assert (Htmp: ctcb = (htcb_addr, Int.zero) \/ ctcb <> (htcb_addr, Int.zero)) by tauto.
  destruct Htmp.
  subst ctcb.
  unfolds.
  unfold get; simpl.
  rewrite TcbMod.set_a_get_a.
  eauto.
  apply tidspec.eq_beq_true; auto.
  eapply rh_curtcb_set_nct; auto.
  

  assert (Hst: exists xl, st = wait (os_stat_sem (v'7, Int.zero)) xl).
  {
    eapply rh_tcblist_ecblist_p_post_exwt_aux_sem ;eauto.
    clear -H44. 
    unfolds in H44; mytac; auto.  
  }
  destruct Hst as (t_opt & Hst). 
  subst st.

  eapply rh_tcblist_ecblist_p_post_exwt_sem;eauto.
  (* ** ac: Check rh_tcblist_ecblist_p_post_exwt_sem. *)
  clear -H44.
  unfolds in H44; mytac; auto. 

   eapply mq_ecb_p_sem_set_wls'_preserve; eauto. 
  eapply mux_ecb_p_sem_set_wls'_preserve; eauto.
  eapply sem_ecb_p_sem_set_wls'_preserve; eauto.
  (* unfold AEventData. *)
  pure_auto.

  (* crit. region exited *)

  hoare_split_pure_all.

  Ltac hoare_call2 :=
    match goal with
    | |- {| _, _, ?li, _, _, _ |} |- ?ct {{ ?P }} scall _ ?el {{ _ }} =>
      match find_aop P with
      | some ?n =>
        hoare lifts (n::nil)%nat pre;
        eapply call_rule';
        [intuition eauto |
         intros;
         do 5 try (apply rvl_elim;[ symbolic_execution | ]);
         first [apply rvl_nil | simpl;auto] |
         intros;unfold_spec(*;sep pauto*) |
         idtac |
         sep_unfold_funpost |
         sep_unfold_funpre |
         simpl;eauto
        ]
      | none _ => idtac
      end
    end.
  eapply seq_rule; eapply forward_rule2.
  1: hoare_call2.
  5: try sep_unfold_funpost; sep pauto.
  6: sep pauto.
  (*hoare forward.*)

  sep normal.
  sep eexists.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel Aop. 
  sep cancel Aier.
  sep cancel p_local. 
  sep split; auto.
  exact_s.
  unfolds; left; auto.
  go.  
  intros.
  get_hsat Hsat. sep destruct Hsat.
  eexists.
  sep cancel p_local.
  sep auto.

  intros.
  get_hsat Hsat. sep destruct Hsat. 
  eexists.
  sep cancel p_local. 
  sep auto.

  hoare unfold.
  inverts H81.

  hoare_lifts_trms_pre Aop. 
  eapply abscsq_rule.
  pure_auto.
  eapply absinfer_seq_end.
  pure_auto.
  2: eauto.
  pure_auto.
  eapply absinfer_eq.

  eapply forward_rule2.
  1: eapply rete_rule'; [symbolic execution | intros].
  2: try sep_unfold_funpost; sep pauto.
  (*hoare forward.*)
  
  sep cancel A_dom_lenv.
  sep normal.
  exists (Vptr (v'7, Int.zero)).
  eexists.
  exists v'0. 
  sep eexists.
  sep cancel Aop. 
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel Aier.
  sep cancel p_local. 
  sep cancel x.
  sep cancel pevent.
  sep pauto.

  introv Hp. simpl in Hp. inverts Hp. 

  Unshelve.
  auto.
  auto.
  auto. auto.
  auto. auto.
Qed.


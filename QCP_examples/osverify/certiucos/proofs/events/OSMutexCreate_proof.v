
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import os_mutex.
Require Import abs_op.
Require Import ifun_spec.

Require Import abs_infer_step.
Require Import ucos_frmaop.
Require Import seplog_lemmas.
Require Import seplog_tactics.

Require Import abs_step.
Require Import abs_infer_abt.

Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(*********************** mutex cre **************************************)

Lemma mutexcre_absimp_err_none_abt:
  forall P sch s verr ebls s1,
    can_change_aop P ->
    ((exists errid, verr = Vptr errid /\ get ebls errid = None) \/
       verr = Vnull) ->
    absinfer sch
             ( <|| (mutexcre_err_none (| verr :: nil|) ?? s1) ;; s ||> ** Hebls ebls ** P)
             (<|| ABORT ||> ** Hebls ebls ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (Hebls ebls ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
   eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexcre_absimp_seterr:
  forall P sch s s1 ebls ebls' ed errid erv ,
    can_change_aop P ->
    get ebls errid = Some ed ->
    ebls' = set ebls errid erv ->
    absinfer sch
             ( <|| (s1 ?? mutexcre_seterr (| Vptr errid :: (Vint32 erv)  :: nil|)) ;; s ||> ** Hebls ebls ** P)
             (<|| s ||> ** Hebls ebls' ** P).
Proof.
  intros.
  assert (Hc: forall ebls, can_change_aop (Hebls ebls ** P)) by (intros; can_change_aop_solver).
  eapply absinfer_trans; try (eapply absinfer_seq_end; auto); eauto.
  eapply absinfer_seq; eauto.
  infer_solver 1%nat.
Qed.


Lemma mutexcre_absimp_iserr:
  forall P prio verr sch s rv,
    can_change_aop P ->
    rv = Vnull ->
    absinfer sch
             ( <|| mutexcre (Vint32 prio :: verr :: rv :: nil) ;; s ||> ** P)
             (<|| (mutexcre_err_none (| verr :: nil|) 
                        ?? mutexcre_seterr (| verr :: (Vint32 (Int.repr OS_ERR_CREATE_ISR))  :: nil|)) ;; s ||> ** P).
Proof.
  intros.
  eapply absinfer_seq; eauto.
  infer_solver 0%nat.
Qed.

Lemma mutexcre_absimp_iserr_abt:
  forall P prio verr sch s rv,
    can_change_aop P ->
    rv <> Vnull ->
    absinfer sch
             ( <|| mutexcre (Vint32 prio :: verr :: rv :: nil) ;; s ||> ** P)
             (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans; try (eapply absinfer_seq_abt; auto); eauto.
  eapply absinfer_seq; eauto.
  eapply absinfer_trans; try (eapply absinfer_choice1; auto); eauto.
  eapply absinfer_trans; try (eapply absinfer_seq_abt; auto); eauto.
  eapply absinfer_seq; eauto.
   eapply absinfer_abt; auto.
  absimp_abt_solver.
Qed.

Lemma mutexcre_absimp_prio_err:
  forall P prio sch s rv verr,
    can_change_aop P ->
    Int.ltu prio (Int.repr OS_LOWEST_PRIO) = false ->
    rv = Vnull ->
    absinfer sch
             ( <|| mutexcre (Vint32 prio :: verr :: rv :: nil) ;; s ||> ** P)
             (<|| (mutexcre_err_none (| verr :: nil|) 
                        ?? mutexcre_seterr (| verr :: (Vint32 (Int.repr OS_PRIO_INVALID))  :: nil|)) ;; s ||> ** P).
Proof.
  intros.
  eapply absinfer_seq; eauto.
  infer_solver 1%nat.
Qed.

Lemma mutexcre_absimp_prio_err_abt:
  forall P prio sch s rv verr,
    can_change_aop P ->
    Int.ltu prio (Int.repr OS_LOWEST_PRIO) = false ->
    rv <> Vnull ->
    absinfer sch
             ( <|| mutexcre (Vint32 prio :: verr :: rv :: nil) ;; s ||> ** P)
             (<|| ABORT ||> ** P).
Proof.
  intros.
   eapply absinfer_trans; try (eapply absinfer_seq_abt; auto); eauto.
  eapply absinfer_seq; eauto.
  eapply absinfer_trans; try (eapply absinfer_choice2; auto); eauto.
  eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; auto); eauto.
  eapply absinfer_seq; eauto.
   eapply absinfer_abt; auto.
  absimp_abt_solver.
Qed.

Lemma mutexcre_absimp_prio_not_available:
  forall P prio sch s rv ptls d verr,
    can_change_aop P ->
    Int.ltu prio (Int.repr OS_LOWEST_PRIO) = true ->
    get ptls prio = Some d ->
    d <> Null ->
    rv = Vnull ->
    absinfer sch
             ( <|| mutexcre (Vint32 prio :: verr :: rv :: nil) ;; s ||> ** HPriotls ptls ** P)
             (<|| (mutexcre_err_none (| verr :: nil|) 
                        ?? mutexcre_seterr (| verr :: (Vint32 (Int.repr OS_PRIO_EXIST))  :: nil|)) ;; s ||> ** HPriotls ptls ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HPriotls ptls ** P)) by can_change_aop_solver.
  eapply absinfer_seq; eauto.
  infer_solver 2%nat.
Qed.

Lemma mutexcre_absimp_prio_not_available_abt:
  forall P prio sch s rv ptls d verr,
    can_change_aop P ->
    Int.ltu prio (Int.repr OS_LOWEST_PRIO) = true ->
    get ptls prio = Some d ->
    d <> Null ->
    rv <> Vnull ->
    absinfer sch
             ( <|| mutexcre (Vint32 prio :: verr :: rv :: nil) ;; s ||> ** HPriotls ptls ** P)
             (<|| ABORT ||> ** HPriotls ptls ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HPriotls ptls ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  do 2 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
  eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexcre_absimp_no_free:
  forall P prio sch s rv ptls verr,
    can_change_aop P ->
    Int.ltu prio (Int.repr OS_LOWEST_PRIO) = true ->
    get ptls prio = Some Null ->
    rv = Vnull ->
    absinfer sch
             ( <|| mutexcre (Vint32 prio :: verr :: rv :: nil) ;; s ||> ** HPriotls ptls ** P)
             (<|| (mutexcre_err_none (| verr :: nil|) 
                        ?? mutexcre_seterr (| verr :: (Vint32 (Int.repr OS_ERR_PEVENT_NULL))  :: nil|)) ;; s ||> ** HPriotls ptls ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HPriotls ptls ** P)) by can_change_aop_solver.
  eapply absinfer_seq; eauto.
  infer_solver 3%nat.
Qed.

Lemma mutexcre_absimp_no_free_abt:
  forall P prio sch s rv ptls verr,
    can_change_aop P ->
    Int.ltu prio (Int.repr OS_LOWEST_PRIO) = true ->
    get ptls prio = Some Null ->
    rv <> Vnull ->
    absinfer sch
             ( <|| mutexcre (Vint32 prio :: verr :: rv :: nil) ;; s ||> ** HPriotls ptls ** P)
             (<|| ABORT ||> ** HPriotls ptls ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HPriotls ptls ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  do 3 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
  eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexcre_absimp_ecb_avail:
  forall P sch s prio rv els  sid locmp locmp' ptrmp ptrmp' ct muxp semp qp ptls ptls' verr, 
    can_change_aop P ->
    Int.ltu prio (Int.repr OS_LOWEST_PRIO) = true ->
    get ptls prio = Some Null ->
    ptls' = set ptls prio Holder ->
    rv = Vptr sid ->
    get els sid = None ->
    locmp' = set locmp ct (Vint32 ($__EvLoc_ecbcre1)) ->
    get ptrmp ct = Some (muxp, semp, qp) ->
    ptrmp' = set ptrmp ct (Vptr sid, semp, qp) ->
    absinfer sch
             (<|| mutexcre(Vint32 prio ::verr ::  rv :: nil) ;; s ||> 
                ** HPriotls ptls ** HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P) 
             (<|| (mutexcre_prio_vhold (| Vint32 prio :: nil |) ;;
                       mutexcre_prio_unused (| Vint32 prio :: nil |) ;;
                        mutexcre_ecb_activate (|Vint32 prio :: Vptr sid :: nil|) ;;
                        (mutexcre_err_none (| verr :: nil|) 
                        ?? mutexcre_seterr (| verr :: (Vint32 (Int.repr OS_NO_ERR))  :: nil|)) ) ;; s ||> 
                ** HPriotls ptls' ** HECBList els ** HEvLoc locmp' ** HEvPtr ptrmp' ** HCurTCB ct ** P).  
Proof. 
  intros.
  assert (Hc: forall ptls els locmp ptrmp, 
                  can_change_aop (HPriotls ptls ** HECBList els ** 
                                                       HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P))
  by (intros; can_change_aop_solver).
  substs.
  eapply absinfer_seq; auto; eauto.
  do 4 (eapply absinfer_trans; try (eapply absinfer_choice2; auto); eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_end; auto); eauto.
  eapply absinfer_seq; eauto.
  infer_solver 0%nat.
  eapply tidsame_trans; [idtac | eapply tidsame_set;eauto].
  2: { introv Hf; inverts Hf. }
  eapply tidsame_trans; repeat try eapply tidsame_set; eauto;
  try (introv Hf; inverts Hf).
Qed.

Lemma mutexcre_absimp_ecb_avail_abt:
  forall P sch s prio rv els  sid locmp ptrmp ct muxp semp qp ptls verr, 
    can_change_aop P ->
    Int.ltu prio (Int.repr OS_LOWEST_PRIO) = true ->
    get ptls prio = Some Null ->
    rv <> Vptr sid ->
    get els sid = None ->
    get ptrmp ct = Some (muxp, semp, qp) ->
    absinfer sch
             (<|| mutexcre(Vint32 prio :: verr :: rv :: nil) ;; s ||> 
                ** HPriotls ptls ** HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P) 
             (<|| ABORT ||> 
                ** HPriotls ptls ** HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P).  
Proof.
  intros.
  assert (Hc:
                  can_change_aop (HPriotls ptls ** HECBList els ** 
                                                       HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P))
  by (can_change_aop_solver).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  do 4 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver;
  try instantiate (3:= s0);
  try instantiate (4:= s0);
  try instantiate (2:= mutexcre_ecb_available (|Vint32 prio :: Vptr sid :: nil|));
  try instantiate (3:= mutexcre_ecb_available (|Vint32 prio :: Vptr sid :: nil|));
  sep pauto.
Qed.

Lemma mutexcre_absimp_ecb_avail_abt2:
  forall P sch s prio rv els  sid locmp ptrmp ct muxp semp qp ptls verr, 
    can_change_aop P ->
    Int.ltu prio (Int.repr OS_LOWEST_PRIO) = true ->
    get ptls prio = Some Null ->
    (exists t', tsk_normal_ev locmp ptrmp t' sid) -> 
    get els sid = None ->
    get ptrmp ct = Some (muxp, semp, qp) ->
    absinfer sch
             (<|| mutexcre(Vint32 prio :: verr :: rv :: nil) ;; s ||> 
                ** HPriotls ptls ** HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P) 
             (<|| ABORT ||> 
                ** HPriotls ptls ** HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P).  
Proof.
  intros.
  assert (Hc:
                  can_change_aop (HPriotls ptls ** HECBList els ** 
                                                       HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P))
  by (can_change_aop_solver).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  do 4 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver;
  try instantiate (3:= s0);
  try instantiate (4:= s0);
  try instantiate (2:= mutexcre_ecb_available (|Vint32 prio :: Vptr sid :: nil|));
  try instantiate (3:= mutexcre_ecb_available (|Vint32 prio :: Vptr sid :: nil|));
  sep pauto.
Qed.

Lemma mutexcre_absimp_prio_vhold:
  forall P prio sch s ptls sid s1,
    can_change_aop P ->
    get ptls prio = Some Holder ->
    absinfer sch
             ( <|| (mutexcre_prio_vhold (| Vint32 prio :: nil |) ;; mutexcre_prio_unused (| Vint32 prio :: nil |) ;;
                        mutexcre_ecb_activate (|Vint32 prio :: Vptr sid :: nil|) ;; s1) ;; s ||> ** HPriotls ptls ** P)
             (<|| (mutexcre_prio_unused (| Vint32 prio :: nil |) ;; mutexcre_ecb_activate (|Vint32 prio :: Vptr sid :: nil|) ;; s1) ;; s ||> ** HPriotls ptls ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HPriotls ptls ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_seq; eauto).
  2:{ eapply absinfer_eq. }
  eapply absinfer_trans; try (eapply absinfer_seq_end; eauto).
  eapply absinfer_seq; eauto.
  infer_solver 0%nat.
Qed.

Lemma mutexcre_absimp_prio_vhold_abt:
  forall P prio sch s ptls sid d s1,
    can_change_aop P ->
    get ptls prio = Some d ->
    d <> Holder ->
    absinfer sch
             ( <|| (mutexcre_prio_vhold (| Vint32 prio :: nil |) ;; mutexcre_prio_unused (| Vint32 prio :: nil |) ;;
                        mutexcre_ecb_activate (|Vint32 prio :: Vptr sid :: nil|) ;; s1) ;; s ||> ** HPriotls ptls ** P)
             (<|| ABORT ||> ** HPriotls ptls ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HPriotls ptls ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexcre_absimp_prio_unused:
  forall P prio sch s els sid s1,
    can_change_aop P ->
    ~(exists eid ow wl, get els eid = Some (absmutexsem prio ow, wl)) ->
    absinfer sch
             ( <|| (mutexcre_prio_unused (| Vint32 prio :: nil |) ;;
                        mutexcre_ecb_activate (|Vint32 prio :: Vptr sid :: nil|) ;; s1) ;; s ||> ** HECBList els ** P)
             (<|| (mutexcre_ecb_activate (|Vint32 prio :: Vptr sid :: nil|) ;; s1) ;; s ||> ** HECBList els ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_seq; eauto).
  2:{ eapply absinfer_eq. }
  eapply absinfer_trans; try (eapply absinfer_seq_end; eauto).
  eapply absinfer_seq; eauto.
  infer_solver 0%nat.
Qed.

Lemma mutexcre_absimp_prio_unused_abt:
  forall P prio sch s els sid s1,
    can_change_aop P ->
    (exists eid ow wl, get els eid = Some (absmutexsem prio ow, wl)) ->
    absinfer sch
             ( <|| (mutexcre_prio_unused (| Vint32 prio :: nil |) ;;
                        mutexcre_ecb_activate (|Vint32 prio :: Vptr sid :: nil|) ;; s1) ;; s ||> ** HECBList els ** P)
             (<|| ABORT ||> ** HECBList els ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els **  P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexcre_absimp_ecb_activate: 
  forall sch prio sid s locmp locmp' ct P els els' s1,       
    can_change_aop P ->
    Int.ltu prio ($ OS_LOWEST_PRIO) = true -> 
    get els sid = None -> 
    els' = (set els sid (absmutexsem prio None, nil)) -> 
    locmp' = set locmp ct (Vint32 ($__EvLoc_ecbcre2)) ->
    absinfer sch
             (<|| (mutexcre_ecb_activate (|Vint32 prio :: Vptr sid :: nil|) ;; s1) ;; s ||> ** HECBList els **  HEvLoc locmp ** HCurTCB ct ** P)
             (<|| s1 ;; s ||> ** HECBList els' ** HEvLoc locmp' ** HCurTCB ct ** P).  
Proof.
  intros.
  assert (Hc: forall els locmp, can_change_aop (HECBList els **  HEvLoc locmp ** HCurTCB ct ** P)) by (intros; can_change_aop_solver).
  substs.
  eapply absinfer_seq; auto; eauto.
  eapply absinfer_trans; try (eapply absinfer_seq_end; auto); eauto.
  infer_solver 0%nat.
Qed.

(* new in OSMutexCreateProof.v *)

Require Import ucos_include.
Require Import os_ucos_h.
Require Import symbolic_lemmas.
Require Import OSMutex_common.
Require Import Lia.
Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.

Require Import evauxvar_lemmas.
Require Import evaux_pure.

Require Import freeevtlist_lemmas. 
Require Import gjb_common.
Require Import sem_common.
Require Import sem_corecommu.
Require Import err_list_common.
Require Import evtinv_lemmas.

Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.

Lemma OSMutexCreate_proof:
  forall vl p r logicl ct, 
    Some p =
    BuildPreI os_internal OSMutexCreate vl logicl OSMutexCreatePre ct->
    Some r =
    BuildRetI os_internal OSMutexCreate vl logicl OSMutexCreatePost ct->
    exists t d1 d2 s,
      os_internal OSMutexCreate = Some (t, d1, d2, s) /\
      {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  rename H1 into Hverr_ptr.
  rename H2 into Hrange.
  rename v'1 into vsid.
  rename v'2 into ier.
  change ((Vint32 i :: x :: nil) ++ (vsid :: nil)) with (Vint32 i :: x :: vsid :: nil).
  subst logicl.

  (* OSIntNesting *)
   hoare forward prim.
   (* splits; pauto. *)
  unfold AGVars.
  hoare unfold.
  hoare forward.
  pure_auto.
  hoare unfold.
  assert (Hvret: vsid =Vnull \/ vsid <> Vnull) by tauto. 
   destruct Hvret.
   2: { hoare abscsq.
           apply noabs_oslinv.
           eapply mutexcre_absimp_iserr_abt; eauto.
           pure_auto.
           eapply absabort_rule.
         } 
  subst.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexcre_absimp_iserr; eauto.
  pure_auto.
  hoare forward prim.
  unfold AGVars.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep pauto.
  auto.
  pure_auto.
  instantiate (1:= Afalse).
  (* assign err *)
  hoare forward prim.
  (* splits; pauto. *)
  unfold EvtInv.
  rename v'17 into vcspace.
  rename v'18 into v18. 
  rename v'19 into v19. 
  rename v'20 into v20.
  
  rename v'21 into v'17. 
  rename v'22 into v'18. 
  rename v'23 into v'19. 
  rename v'24 into v'20. 
  rename v'25 into v'21. 
  rename v'26 into v'22. 
  rename v'27 into v'23. 
  rename v'28 into v'24. 
  rename v'29 into v'25. 
  rename v'30 into v'26. 
  rename v'31 into v'27. 
  rename v'32 into v'28. 
  

  hoare normal pre; hoare_ex_intro. (* new add *)
  hoare_lifts_trms_pre (R_Q_Data_P). (* new add *)
  eapply pure_split_rule'; introv Hrqdata. (* new add *)
  hoare unfold.
  rename v'45 into vcspace1.
  rename v'46 into v46. 
  rename v'47 into v47. 
  rename v'48 into v48. 

  rename v'49 into v'45. 
  rename v'50 into v'46. 
  rename v'51 into v'47. 
  rename v'52 into v'48. 
  rename v'53 into v'49. 
  rename v'54 into v'50. 
  rename v'55 into v'51. 
  rename v'56 into v'52. 
  rename v'57 into v'53. 
  rename v'58 into v'54. 
  rename v'59 into v'55. 
  rename v'60 into v'56.  
  rename v'61 into v'57. 
  rename v'62 into v'58. 
  rename v'63 into v'59. 
  rename v'64 into v'60. 
  rename v'65 into v'61. 
  rename v'66 into v'62. 
  rename v'67 into v'63. 


  hoare_lifts_trms_pre (Aop, eblist).
  destruct Hverr_ptr as [Hverr_eq | (errid & Hverr_eq)];
  rewrite Hverr_eq.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexcre_absimp_err_none_abt; eauto.
  pure_auto.
  eapply absinfer_eq. 
  eapply absabort_rule.
  rename v'61 into ebls.
  destruct (EbMod.get ebls errid) eqn: eq1.
  2: { eapply abscsq_rule.
          apply noabs_oslinv.
          eapply mutexcre_absimp_err_none_abt; eauto.
          pure_auto.
          eapply absinfer_eq. 
          eapply absabort_rule.
        }
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutexcre_absimp_seterr; eauto.
    pure_auto.
    eapply absinfer_eq. 
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AErrblkList).
  eapply err_list_split_frm; eauto.
  unfold node.
  hoare unfold.
  inverts H15; inverts H16.
  hoare forward.
  hoare_lifts_trms_pre (Aop, err).
  eapply assign_rule_deref_ptr.
  intros. sep get rv.
  simpl Astruct.
  split.
  introv Hsat. sep cancel (Aptrmapsto). eauto.
  intros; sep auto.
  intros; sep get rv.
  eapply eq_int; auto.
  intros. sep eexists. sep cancel p_local. simpl; auto.
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  sep pauto; eauto.
  trycancel_EvtInv.
  sep cancel Aier.
  unfold AErrblkList.
  sep pauto.
  eapply err_sllseg_merge with (vsem:= (v'70, Int.zero)) (errv:= (Int.repr OS_ERR_CREATE_ISR)) (vl:= ((V$ OS_ERR_CREATE_ISR) :: v'66 :: nil)); eauto.
  sep cancel err_sllseg.
  sep cancel err_sllseg.
  unfold node.
  simpl Astruct.
  sep pauto; eauto.
  sep cancel (Aptrmapsto).
  sep cancel Aptrmapsto.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.
  eapply EbMod.my_joinsig_join_set; eauto.
  eapply my_joinsig_set; eauto.
  split; auto. go.
  rewrite EbMod.map_get_set; auto.
  auto.
  pure_auto.
  (* end of err *)
  hoare forward.
  unfold isptr; eauto.
  (*  end of retrun Vnull *)
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  hoare forward prim.
  unfold AGVars.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep pauto.
  auto.
  pure_auto.
  clear -Hverr_ptr Hrange.
  (* end add *)

  hoare forward;  pauto.
  hoare unfold.
  assert (Hprio_range: Int.ltu i ($ OS_LOWEST_PRIO) = false).
  { clear -H.
      destruct (Int.ltu ($ OS_LOWEST_PRIO) i) eqn: eq1;
      try lets Heq: ltu_eq_false eq1;
      destruct (Int.eq i ($ OS_LOWEST_PRIO)) eqn: eq2;
      simpl in H;
      try change (Int.ltu Int.zero Int.one) with true in H;
      try change (Int.ltu Int.zero Int.zero) with false in H;
      simpl in H; tryfalse;
      unfold OS_LOWEST_PRIO in *;
      int auto.
   }
   clear -Hprio_range.
   instantiate (1:= Afalse).
   assert (Hvret: vsid =Vnull \/ vsid <> Vnull) by tauto. 
   destruct Hvret.
   2: { hoare abscsq.
           apply noabs_oslinv.
           eapply mutexcre_absimp_prio_err_abt; eauto.
           pure_auto.
           eapply absabort_rule.
         } 
    subst.
    hoare abscsq.
    apply noabs_oslinv.
    eapply mutexcre_absimp_prio_err; eauto.
    pure_auto.
    (* assign err *)
  hoare forward prim.
  (* splits; pauto. *)
  unfold EvtInv.

   hoare normal pre; hoare_ex_intro. (* new add *)
   rename v'17 into vcspace.
   rename v'18 into v18. 
   rename v'19 into v19. 
   rename v'20 into v20.
   
   rename v'21 into v'17. 
   rename v'22 into v'18. 
   rename v'23 into v'19. 
   rename v'24 into v'20. 
   rename v'25 into v'21. 
   rename v'26 into v'22. 
   rename v'27 into v'23. 
   rename v'28 into v'24. 
   rename v'29 into v'25. 
   rename v'30 into v'26. 
   rename v'31 into v'27. 
   rename v'32 into v'28. 
   rename v'33 into v'29. 
   rename v'34 into v'30. 
   rename v'35 into v'31. 
   rename v'36 into v'32. 
   rename v'37 into v'33. 
   rename v'38 into v'34. 
   rename v'39 into v'35. 
 
  hoare_lifts_trms_pre ( R_Q_Data_P ). (* new add *)
  eapply pure_split_rule'; introv Hrqdata. (* new add *)
  hoare unfold.

  hoare_lifts_trms_pre (Aop, eblist).
  destruct Hverr_ptr as [Hverr_eq | (errid & Hverr_eq)];
  rewrite Hverr_eq.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexcre_absimp_err_none_abt; eauto.
  pure_auto.
  eapply absinfer_eq. 
  eapply absabort_rule.
  rename v'33 into ebls.
  destruct (EbMod.get ebls errid) eqn: eq1.
  2: { eapply abscsq_rule.
          apply noabs_oslinv.
          eapply mutexcre_absimp_err_none_abt; eauto.
          pure_auto.
          eapply absinfer_eq. 
          eapply absabort_rule.
        }
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutexcre_absimp_seterr; eauto.
    pure_auto.
    eapply absinfer_eq. 
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AErrblkList).
  eapply err_list_split_frm; eauto.
  unfold node.
  hoare unfold.
  inverts H8; inverts H9.
  hoare forward.
  hoare_lifts_trms_pre (Aop, err).
  eapply assign_rule_deref_ptr.
  intros. sep get rv.
  simpl Astruct.
  split.
  introv Hsat. sep cancel (Aptrmapsto). eauto.
  intros; sep auto.
  intros; sep get rv.
  eapply eq_int; auto.
  intros. sep eexists. sep cancel p_local. simpl; auto.
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  sep pauto; eauto.
  trycancel_EvtInv.
  sep cancel Aier.
  unfold AErrblkList.
  sep pauto.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eapply err_sllseg_merge with (vsem:= (v'42, Int.zero)) (errv:= (Int.repr OS_PRIO_INVALID)) 
                                                                   (vl:= ((V$ OS_PRIO_INVALID) :: v'38 :: nil)); eauto.
  sep cancel err_sllseg.
  sep cancel err_sllseg.
  unfold node.
  simpl Astruct.
  sep pauto; eauto.
  sep cancel (Aptrmapsto).
  sep cancel Aptrmapsto.
  eauto.
  eapply EbMod.my_joinsig_join_set; eauto.
  eapply my_joinsig_set; eauto.
  split; auto. go.
  rewrite EbMod.map_get_set; auto.
  auto.
  pure_auto.
  (* end of err *)
    hoare forward.
    unfold isptr; splits; eauto.
    eapply hoare_disj_afalseP_l_pre.

    hoare unfold.
    assert (Hprio_range: Int.ltu i ($ OS_LOWEST_PRIO) = true).
  { clear -H.
      destruct (Int.ltu ($ OS_LOWEST_PRIO) i) eqn: eq1;
      try lets Heq: ltu_eq_false eq1;
      destruct (Int.eq i ($ OS_LOWEST_PRIO)) eqn: eq2;
      simpl in H;
      try change (Int.ltu Int.zero Int.one) with true in H;
      try change (Int.ltu Int.zero Int.zero) with false in H;
      simpl in H; destruct H; tryfalse;
      unfold OS_LOWEST_PRIO in *;
      int auto.
   }
   clear -Hverr_ptr Hrange Hprio_range.
   assert (Hprio_range': Int.unsigned i < 64).
   { clear -Hprio_range. unfold OS_LOWEST_PRIO in *; int auto. }
   hoare forward prim.
   (* splits; pauto. *)
   unfold AOSTCBPrioTbl.
   hoare unfold.
   rename H5 into Hptbl_len.
   rename H2 into Hrh_ptls.
   assert (Hget_ptls: exists d, get v'15 i = Some d).
   { destruct (get v'15 i) eqn: eq1.
      eauto. eapply Hrh_ptls in eq1.
      clear -eq1 Hprio_range'.
      false. eapply eq1. int auto.
    }
   destruct Hget_ptls as (d & Hget_ptls).
   assert (Hrt_mat: rule_type_val_match OS_TCB ∗ (nth_val' (Z.to_nat (Int.unsigned i)) v'1) = true).
   { eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
      rewrite Hptbl_len; auto with zarith.
    }
   assert (Hisptr: isptr (nth_val' (Z.to_nat (Int.unsigned i)) v'1)).
   { simpl in Hrt_mat. unfold isptr.
     destruct (nth_val' (Z.to_nat (Int.unsigned i)) v'1) eqn: eq1; tryfalse;
     eauto.
   }
   (* If (OSTCBPrioTbl ′ [prio ′] !=ₑ NULL) *)
   hoare forward.
   pure_auto.
   auto.
   pure_auto.
   pure_auto.
   hoare unfold.
   destruct Hisptr as [Hptr_eq | ((tid_b & tid_i) & Hptr_eq)];
   rewrite Hptr_eq in H2; simpl in H2; try change (Int.notbool Int.one) with Int.zero in H2;
    simpl in H2; tryfalse.
   assert (Hd_neq: d <> Null).
   { destruct d; auto.
      eapply Hrh_ptls in Hget_ptls; eauto.
      destruct Hget_ptls as (_ & Hf).
      eapply nth_val_nth_val'_some_eq in Hf.
      unfold nat_of_Z in Hf; rewrite Hptr_eq in Hf; inverts Hf.
    }
   instantiate (1:= Afalse).
   hoare_lifts_trms_pre (Aop, absptls).
   assert (Hvret: vsid =Vnull \/ vsid <> Vnull) by tauto. 
   destruct Hvret.
   2: { eapply abscsq_rule.
           apply noabs_oslinv.
           eapply mutexcre_absimp_prio_not_available_abt; eauto.
           pure_auto.
           eapply absinfer_eq. 
           eapply absabort_rule.
         } 
    subst.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutexcre_absimp_prio_not_available; eauto.
    pure_auto.
    eapply absinfer_eq. 
    hoare forward prim.
    unfold AOSTCBPrioTbl.
    sep pauto; eauto.
    eauto.
    pure_auto.
    (* assign err *)
  clear -Hverr_ptr Hrange.
  hoare forward prim.
  (* splits; pauto. *)
  unfold EvtInv.
  hoare normal pre; hoare_ex_intro. (* new add *)

  rename v'17 into vcspace.
  rename v'18 into v18. 
  rename v'19 into v19. 
  rename v'20 into v20.
  
  rename v'21 into v'17. 
  rename v'22 into v'18. 
  rename v'23 into v'19. 
  rename v'24 into v'20. 
  rename v'25 into v'21. 
  rename v'26 into v'22. 
  rename v'27 into v'23. 
  rename v'28 into v'24. 
  rename v'29 into v'25. 
  rename v'30 into v'26. 
  rename v'31 into v'27. 
  rename v'32 into v'28. 
  rename v'33 into v'29. 
  rename v'34 into v'30. 
  rename v'35 into v'31. 
  rename v'36 into v'32. 
  rename v'37 into v'33. 
  rename v'38 into v'34. 
  rename v'39 into v'35. 

  hoare_lifts_trms_pre ( R_Q_Data_P ). (* new add *)
  eapply pure_split_rule'; introv Hrqdata. (* new add *)
  hoare unfold.
  hoare_lifts_trms_pre (Aop, eblist).
  destruct Hverr_ptr as [Hverr_eq | (errid & Hverr_eq)];
  rewrite Hverr_eq.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexcre_absimp_err_none_abt; eauto.
  pure_auto.
  eapply absinfer_eq. 
  eapply absabort_rule.
  rename v'33 into ebls.
  destruct (EbMod.get ebls errid) eqn: eq1.
  2: { eapply abscsq_rule.
          apply noabs_oslinv.
          eapply mutexcre_absimp_err_none_abt; eauto.
          pure_auto.
          eapply absinfer_eq. 
          eapply absabort_rule.
        }
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutexcre_absimp_seterr; eauto.
    pure_auto.
    eapply absinfer_eq. 
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AErrblkList).
  eapply err_list_split_frm; eauto.
  unfold node.
  hoare unfold.
  inverts H8; inverts H9.
  hoare forward.
  hoare_lifts_trms_pre (Aop, err).
  eapply assign_rule_deref_ptr.
  intros. sep get rv.
  simpl Astruct.
  split.
  introv Hsat. sep cancel (Aptrmapsto). eauto.
  intros; sep auto.
  intros; sep get rv.
  eapply eq_int; auto.
  intros. sep eexists. sep cancel p_local. simpl; auto.
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  sep pauto; eauto.
  trycancel_EvtInv.
  sep cancel Aier.
  unfold AErrblkList.
  sep pauto.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eapply err_sllseg_merge with (vsem:= (v'42, Int.zero)) (errv:= (Int.repr OS_PRIO_EXIST)) 
                                                                   (vl:= ((V$ OS_PRIO_EXIST) :: v'38 :: nil)); eauto.
  sep cancel err_sllseg.
  sep cancel err_sllseg.
  unfold node.
  simpl Astruct.
  sep pauto; eauto.
  sep cancel (Aptrmapsto).
  sep cancel Aptrmapsto.
  eauto.
  eapply EbMod.my_joinsig_join_set; eauto.
  eapply my_joinsig_set; eauto.
  split; auto. go.
  rewrite EbMod.map_get_set; auto.
  auto.
  pure_auto.
  (* end of err *)
    hoare forward.
    unfold isptr; splits; eauto.
    eapply hoare_disj_afalseP_l_pre.

    hoare_split_pure_all.
    destruct Hisptr as [Hptr_eq | ((tid_b & tid_i) & Hptr_eq)];
   rewrite Hptr_eq in H2; simpl in H2; try change (Int.notbool Int.zero) with Int.one in H2;
    simpl in H2; destruct H2; tryfalse.
    assert (Hd_eq: d = Null).
    { eapply nth_val'_imply_nth_val in Hptr_eq; eauto.
       eapply Hrh_ptls in Hptr_eq; eauto.
       rewrite Hget_ptls in Hptr_eq; inverts Hptr_eq; auto.
       clear -Hprio_range'; int auto.
       rewrite Hptbl_len; auto with zarith. }
   subst d.
   (* OSTCBPrioTbl ′ [prio ′] =ₑ 〈 OS_TCB ∗ 〉 PlaceHolder;ₛ *)
    unfold PlaceHolder.
    hoare unfold.
    hoare forward.
    eapply forward_rule2.
    match goal with
  | |- {|_ ,_, _, _, _, _|}|- _ {{?P}}?x ′ [_] =ₑ _ {{_}} =>
   match find_dom_lenv P with
     | (none _, _) => fail
     | (some ?m, Some ?ls) =>
       let ret1 := constr:(var_notin_dom x ls) in
       let ret2 := eval compute in ret1 in
                                    match ret2 with
                                      | true =>
                                        match find_aop P with
                                          | none _ => assert (3=12)
                                          | some ?n =>
                                            match find_gvararray P x with
                                              | none _ => assert (1=11)
                                              | some ?o => 
                                                hoare lifts (n :: m :: o :: nil) pre;
                                                  eapply assign_rule_array_g_aop;
                                                  idtac
                                            end
                                        end
                                      | false => assert (2=2)
                                    end
   end
  end.
  intro s.
  split; introv Hsat; exact Hsat.
  simpl; auto.

  2:symbolic execution.
  introv Hsat.
  eapply cast_rv_tptr.
  eapply addrof_gvar_rv.
  apply  astar_l_anotinlenv_intro.
  sep cancel OSPlaceHolder.
  eauto.
  apply astar_l_adomlenv_elim in Hsat.
  destruct Hsat as (Hlenv & _).
  clear -Hlenv.
   unfolds in Hlenv.
   unfold EnvMod.indom.
   pure_auto.
   destruct H as ((l & t) & H).
   assert (Hf: ~ListSet.set_In (OSPlaceHolder, t)
                            ((err, (Int8u) ∗)
           :: (prio, Int8u) :: (pevent, OS_EVENT ∗) :: nil)).
   simpl; pure_auto; tryfalse.
  rewrite Hlenv in Hf.
  pure_auto.
  simpl; auto.
  pure_auto.
  auto.
  auto with zarith.
  apply eq_vptr. eauto.
  rewrite Hptbl_len; auto with zarith.
  intros. sep eexists. sep cancel p_local. simpl; auto.
  eauto.
  (* pevent ′ =ₑ OSEventFreeList ′;ₛ *)
  hoare_lifts_trms_pre EvtInv.
  unfold EvtInv.

  rename v'17 into vcspace.
  rename v'18 into v18. 
  rename v'19 into v19. 
  rename v'20 into v20.
  
  rename v'21 into v'17. 


  hoare normal pre.
  hoare_ex_intro.
  hoare_lifts_trms_pre (AOSQFreeList, AOSQFreeBlk, AECBList, absecblist).
  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_part1; eauto.
  hoare_lifts_trms_pre ( R_Q_Data_P ).
  eapply pure_split_rule'; introv Hrqdata.
  hoare unfold.
  hoare forward.
  destruct H11 as [Hfels_eq | ((fecb_b & fecb_i) & Hfels_eq)];
  rewrite Hfels_eq; auto.
  destruct H11 as [Hfels_eq | ((fecb_b & fecb_i) & Hfels_eq)];
  subst.
  (* OSEventFreeList = Null *)
   hoare forward.
   hoare unfold.
   instantiate (1:= Afalse).
   hoare forward.
   pure_auto.
   rewrite update_nth_val_len_eq; rewrite Hptbl_len; auto with arith.
   hoare_lifts_trms_pre (Aop, absptls).
   assert (Hvret: vsid =Vnull \/ vsid <> Vnull) by tauto. 
   destruct Hvret.
   2: { eapply abscsq_rule.
           apply noabs_oslinv.
           eapply mutexcre_absimp_no_free_abt; eauto.
           pure_auto.
           eapply absinfer_eq. 
           eapply absabort_rule.
         } 
    subst.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutexcre_absimp_no_free; eauto.
    pure_auto.
    eapply absinfer_eq.
    lets Hup_eq: Hptr_eq.
    eapply update_nth_val_eq_same_doble in Hup_eq.
    erewrite Hup_eq.
    hoare forward prim.
    unfold AOSTCBPrioTbl.
    sep pauto; eauto.
    sep cancel p_local.
    sep cancel Aptrmapsto.
    sep cancel OSPlaceHolder.
    sep cancel Aier.
    sep cancel APthreadAttr.
  sep cancel CapabilityInv.
    eapply fold_EvtInv_frm.
    sep cancel EvtInv_part1.
    eapply fold_EvtInv_part2; eauto.
    unfold AOSEventFreeList.
    unfold ecbf_sll.
    sep cancel ecbf_sllseg.
    trycancel_EvtInv.
    sep pauto.
    auto.
    pure_auto.
     (* assign err *)
  clear -Hverr_ptr Hrange.
  hoare forward prim.
  (* splits; pauto. *)
  unfold EvtInv.
  hoare normal pre; hoare_ex_intro.

  rename v'16 into vcspace.
  rename v'17 into v17. 
  rename v'18 into v18. 
  rename v'19 into v19.

  rename v'20 into v'16.   
  rename v'21 into v'17. 
  rename v'22 into v'18. 
  rename v'23 into v'19. 
  rename v'24 into v'20. 
  rename v'25 into v'21. 
  rename v'26 into v'22. 
  rename v'27 into v'23. 
  rename v'28 into v'24. 
  rename v'29 into v'25. 
  rename v'30 into v'26. 
  rename v'31 into v'27. 
  rename v'32 into v'28. 
  rename v'33 into v'29. 
  rename v'34 into v'30. 
  rename v'35 into v'31. 
  rename v'36 into v'32. 
  rename v'37 into v'33. 
  rename v'38 into v'34. 


  hoare_lifts_trms_pre ( R_Q_Data_P ).
  eapply pure_split_rule'; introv Hrqdata.
  hoare unfold.
  hoare_lifts_trms_pre (Aop, eblist).
  destruct Hverr_ptr as [Hverr_eq | (errid & Hverr_eq)];
  rewrite Hverr_eq.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexcre_absimp_err_none_abt; eauto.
  pure_auto.
  eapply absinfer_eq. 
  eapply absabort_rule.
  rename v'32 into ebls. (* change v'22 -> v'21 *)
  destruct (EbMod.get ebls errid) eqn: eq1.
  2: { eapply abscsq_rule.
          apply noabs_oslinv.
          eapply mutexcre_absimp_err_none_abt; eauto.
          pure_auto.
          eapply absinfer_eq. 
          eapply absabort_rule.
        }
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutexcre_absimp_seterr; eauto.
    pure_auto.
    eapply absinfer_eq. 
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AErrblkList).
  eapply err_list_split_frm; eauto.
  unfold node.
  hoare unfold.
  inverts H8; inverts H9.
  hoare forward.
  hoare_lifts_trms_pre (Aop, err).
  eapply assign_rule_deref_ptr.
  intros. sep get rv.
  simpl Astruct.
  split.
  introv Hsat. sep cancel (Aptrmapsto). eauto.
  intros; sep auto.
  intros; sep get rv.
  eapply eq_int; auto.
  intros. sep eexists. sep cancel p_local. simpl; auto.
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier.
  unfold EvtInv.
  sep pauto; eauto.
  trycancel_EvtInv.
  unfold AErrblkList.
  sep pauto.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eapply err_sllseg_merge with (vsem:= (v'41, Int.zero)) (errv:= (Int.repr OS_ERR_PEVENT_NULL)) 
                                                                   (vl:= ((V$ OS_ERR_PEVENT_NULL) :: v'37 :: nil)); eauto.
  sep cancel err_sllseg.
  sep cancel err_sllseg.
  unfold node.
  simpl Astruct.
  sep pauto; eauto.
  sep cancel (Aptrmapsto).
  sep cancel Aptrmapsto.
  eauto.
  eapply EbMod.my_joinsig_join_set; eauto.
  eapply my_joinsig_set; eauto.
  split; auto. go.
  rewrite EbMod.map_get_set; auto.
  auto.
  pure_auto.
  (* end of err *)
    hoare forward.
    unfold isptr; splits; eauto.
    eapply hoare_disj_afalseP_l_pre.
    hoare unfold.
    destruct H2; tryfalse.
    (* OSEventFreeList <> Null *)
    hoare forward.
    hoare unfold.
    tryfalse.
(*     instantiate (1:= Afalse). *)
    eapply hoare_disj_afalseP_l_pre.
    hoare unfold.
    clear H2.
    (* OSEventFreeList ′ =ₑ 〈 OS_EVENT ∗ 〉 OSEventFreeList ′ → OSEventListPtr; *)
    destruct v'19.
    simpl ecbf_sllseg.
    hoare unfold.
    tryfalse.
    hoare unfold.
    hoare forward.
    go.
    destruct H17 as [Hfels_eq | ((fecb_b & fecb_i) & Hfels_eq)];
    rewrite Hfels_eq; auto.
  
(***************************** OSEventFreeList <> Null **************************)
  rename v'40 into pevent_block.
  rename v'18 into pevent_event_tbl.
  rename v'38 into pevent_event_ptbl.
(*   rename H14 into Hrl_petbl. *)
  rename v'9 into els.
  hoare_assert_pure (EcbMod.get els (pevent_block, Int.zero) = None). 
  {
    get_hsat Hsat.
    unfold EvtInv_part1 in Hsat.
    unfold AECBList in Hsat.
    sep normal in Hsat.
    sep destruct Hsat.
    sep split in Hsat.
    sep_lifts_trms_in Hsat (Astruct, evsllseg).
    eapply semcre_ecblist_star_not_inh; eauto.
  }
  hoare_split_pure_all.
  rename H2 into Hnone.  (* EcbMod.get v'14 (pevent_block, Int.zero) = None *)

  hoare_lifts_trms_pre (tcbllsegevaux, AOSTCBList, p_local). 
  eapply backward_rule1. 
  introv Hsat. 
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  hoare_assign_evaux.
  hoare_assign_evaux.
  unfold isevloc; auto.

  unfold EvtInv_part1. hoare normal pre. hoare_ex_intro.
  rename v'35 into locmp.
  rename v'36 into ptrmp.
  assert (Hnull: get ptrmp ct = Some (Vnull, Vnull, Vnull)). (* v'34 -> v'36 *)
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }

  assert (Hvsid: vsid = Vptr (pevent_block, Int.zero) \/ vsid <> Vptr (pevent_block, Int.zero)) by tauto. 
  destruct Hvsid.
  2: {
    hoare_lifts_trms_pre (Aop, absptls, absecblsid, evlocid, evptrid, curtid). 
    eapply abscsq_rule. 
    apply noabs_oslinv.
    eapply mutexcre_absimp_ecb_avail_abt; eauto.
    pure_auto.
    simpl. intros. splits; auto.
    eapply absinfer_eq.
    apply absabort_rule.
  }

  assert (Hncre1: ~(exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 (pevent_block, Int.zero))). (* v'32,34 -> v'34,36 *)
  {
    match goal with
      H: MUX_ECB_P _ _ _ _ (?v :: ?vl) _ _ _ |- _ => remember v as hv; remember vl as tvl
    end.
    assert (Hptrin: ptr_in_ecblist (Vptr (pevent_block, Int.zero)) (Vptr (pevent_block, Int.zero)) (hv :: tvl)).
    {
      unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg. simpl.
      asserts_rewrite (beq_pos pevent_block pevent_block = true).
      {
        rewrite beq_pos_Pos_eqb_eq. 
        apply Pos.eqb_refl.
      }
      change (Int.eq Int.zero Int.zero) with true.
      simpl. auto.
    }
     eapply ptr_in_freelist_notcre1; eauto. 
  }
  assert (Hv: pevent_event_tbl = (pevent_block, Int.zero +ᵢ  ($ 4 +ᵢ  ($ 2 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero)))))) by
      (simpl in H13; inverts H13; auto).
  rewrite Hv.
  assert (Hv': pevent_event_ptbl = (pevent_block, Int.zero +ᵢ  ($ 1 +ᵢ  ($ 4 +ᵢ ($ 8 +ᵢ ($ 4 +ᵢ  ($ 2 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero)))))))))  by
      (simpl in H14; inverts H14; auto).
  rewrite Hv'.
  subst vsid.

  assert (Hnormal:
            (~(exists t, tsk_normal_ev locmp ptrmp t (pevent_block, Int.zero))) \/
            (exists t, tsk_normal_ev locmp ptrmp t (pevent_block, Int.zero))) by tauto. (* v'32,34 -> v'34,36 *)
  destruct Hnormal as [Hnml | Hnnml].
  2: {
    hoare_lifts_trms_pre (Aop, absptls, absecblsid, evlocid, evptrid, curtid).
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutexcre_absimp_ecb_avail_abt2; eauto.
    can_change_aop_solver.
    simpl. intros. splits; auto.
    eapply absinfer_eq.
    apply absabort_rule.
  }

(*   hoare normal pre. hoare_ex_intro.   *)
  hoare_lifts_trms_pre (Aop, absptls, absecblsid, evlocid, evptrid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply mutexcre_absimp_ecb_avail; pure_auto.
  simpl. intros. splits; auto.
  eapply absinfer_eq.

  (* prepare for EXIT_CRITICAL;ₛ *)
  fold_evaux_mux_loc (V$ __EvLoc_ecbcre1) (Vptr (pevent_block, Int.zero)).

  assert (Hncre2: ~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 (pevent_block, Int.zero)).
  {
    eapply not_in_els_notcre2; eauto. 
  }

  hoare_assert_pure (isptr v'12).
  {
    get_hsat Hsat. 
    sep_lifts_trms_in Hsat ecbf_sllseg.
    lets H00: isptr_ecbf_sllseg_frm Hsat.
    auto.
  }
  hoare_split_pure_all.
  hoare_assert_pure (~ptr_in_ecblist (Vptr (pevent_block, Int.zero)) v'12 v'19).
  {
    match goal with H: isptr _ |- _ => rename H into Hisptr end.
    unfold isptr in Hisptr.
    destruct Hisptr as [Heq | (p & Heq)];
    subst v'12. unfolds. introv Hf. unfold ptr_in_ecblist in Hf. destruct v'19; tryfalse.
    get_hsat Hsat.
    sep_lifts_trms_in Hsat (Astruct, ecbf_sllseg). 
    apply hd_not_in_evt_freelist in Hsat; auto.
  }
  hoare_split_pure_all.
  match goal with
    H: MUX_ECB_P _ _ _ _ (?v :: ?vl) _ _ _ |- _ => remember v as hv; remember vl as tvl
  end.
  assert (Hin: ptr_in_ecblist (Vptr (pevent_block, Int.zero)) (Vptr (pevent_block, Int.zero)) (hv :: tvl)).
  {
    unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg. simpl.
    asserts_rewrite (beq_pos pevent_block pevent_block = true).
    {
      rewrite beq_pos_Pos_eqb_eq. 
      apply Pos.eqb_refl.
    }
    change (Int.eq Int.zero Int.zero) with true.
    simpl. auto.
  }
  assert (Hptr: V_OSEventListPtr hv = Some v'12).
  { subst hv; unfolds; simpl; auto. }
  unfold ASemEIBs.
  unfold AMuxEIBs.
  unfold AMqEIBs.
  hoare_split_pure_all.
  eapply backward_rule1. 
  introv Hsat.
  eapply fold_EvtInv_frm'.
  trycancel_EvtInv.
  eapply fold_EvtInv_part2; try sep cancel evloc; try sep cancel evptr; eauto.
  eapply semecb_preserve_cre1_mux; eauto.
  eapply muxecb_preserve_cre1_mux; eauto.
  eapply qecb_preserve_cre1_mux; eauto.
  eapply not_in_els_notdel; eauto.
  eapply evcre_nodup_cre1_preserve_mux; eauto.
  eapply evdel_nodup_cre1_preserve_mux; eauto.
  unfold ASemEIBs.
  unfold AMuxEIBs.
  unfold AMqEIBs.
  unfold AOSEventFreeList.
  unfold ecbf_sll.
  sep cancel ecbf_sllseg.
  unfold tcbllsegevaux.
  trycancel_EvtInv.
  sep pauto; eauto.

  (* EXIT_CRITICAL;ₛ *)
  assert (Hprio_range'': 0<= Int.unsigned i < 64).
  clear -Hprio_range'; split; int auto.
  hoare forward prim.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  unfold p_local. unfold LINV. unfold OSLInv.
  unfold AOSTCBPrioTbl.
  sep normal.
  sep eexists.
  sep cancel Aier.
  sep cancel OSTCBPrioTbl.
  sep cancel OSPlaceHolder.
  sep cancel vhold_addr.
  sep cancel absptls.
  sep split; eauto.
  sep cancel CurTid.
  sep cancel flag_off.
  try_cancel_evaux_asst.
  sep cancel CoreCommuInv.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  eauto.
  eapply RH_PrioTbl_P_update_vhold; eauto.
  eapply R_PrioTbl_P_update_vhold; eauto.
  clear -Hprio_range; unfold OS_LOWEST_PRIO in *; int auto.
  eapply RL_RTbl_PrioTbl_P_update_vhold; eauto.
  clear -Hprio_range; unfold OS_LOWEST_PRIO in *; int auto.
  split.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hptbl_len; auto with zarith.
  rewrite update_nth_val_len_eq; auto.
  splits; eauto.
  unfold isevloc. auto.
  auto.
  pure_auto.
  (* end of EXIT_CRITICAL;ₛ *)
  substs.
  rename H20 into Hi1; rename H23 into Heptr.
  clear -Hverr_ptr Hrange Hprio_range Hprio_range' Hprio_range'' Hi1 Heptr.
  (* assign *)
  hoare forward.
  hoare forward.
  pure_auto.
  hoare forward.
  change (Int.ltu ($ 8) Int.iwordsize) with true.
  simpl val_inj.
  hoare forward.
  sep cancel Aop.
  trycancel.
  sep cancel Aier.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel Aarray.
  sep cancel p_local.
  eauto.
  change (Int.unsigned ($ OS_EVENT_TYPE_MUTEX)) with 4.
  splits; auto with zarith.
  clear -Hprio_range'.
  unfold OS_MUTEX_AVAILABLE. mauto.
  unfold isptr; auto.
  pure_auto.

  intros. sep auto.
  intros. sep auto.

  unfold OS_EventWaitListInitPost.
  unfold OS_EventWaitListInitPost'.
  unfold getasrt.

  pure intro.
  inverts H5.
  hoare forward prim.
  (* splits; pauto. *)
  unfold EvtInv.
  hoare normal pre.
  hoare_ex_intro.

  rename v'21 into vcspace.
  rename v'22 into v22. 
  rename v'23 into v23. 
  rename v'24 into v24.

  rename v'25 into v'21. 
  rename v'26 into v'22. 
  rename v'27 into v'23. 
  rename v'28 into v'24. 
  rename v'29 into v'25. 
  rename v'30 into v'26. 
  rename v'31 into v'27. 
  rename v'32 into v'28.  
  rename v'33 into v'29. 
  rename v'34 into v'30. 
  rename v'35 into v'31. 
  rename v'36 into v'32. 
  rename v'37 into v'33. 
  rename v'38 into v'34. 
  rename v'39 into v'35. 
  rename v'40 into v'36. 
  rename v'41 into v'37. 
  rename v'42 into v'38.  
  rename v'43 into v'39. 
  rename v'44 into v'40. 
  rename v'45 into v'41. 
 
  hoare_split_pure_all.
  hoare unfold.
  hoare forward.
  pure_auto.
  rename v'1 into vp.
  rename v'13 into els.
  hoare_assert_pure (EcbMod.get els (vp, Int.zero) = None).
  {
    eapply semcre_ecblist_star_not_inh; eauto.
    instantiate (3:= s0).
    sep pauto.
  }
  hoare_split_pure_all.

  hoare unfold.
  hoare forward.
  fold_AEventNode_r.

  hoare_lifts_trms_pre (tcbllsegevaux, AOSTCBList, p_local). 
  eapply backward_rule1. 
  introv Hsat. 
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  hoare_assign_evaux.
  unfold isevloc; auto.
  rename v'40 into locmp.
  rename v'41 into ptrmp.

  assert (Hptr: get ptrmp ct = Some (Vptr (vp, Int.zero), Vnull, Vnull)).
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  assert (Hloc: get locmp ct = Some (V$ __EvLoc_ecbcre1)).
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  assert (Hncre1': ~exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 (vp, Int.zero)).
  {
    eapply cre_nodup_no_cre1_mux; eauto.
  }
  assert (Hncre2': ~exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 (vp, Int.zero)).
  {
    eapply cre_nodup_no_cre2_mux; eauto.
  }
  assert (Hndel: ~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel (vp, Int.zero)).
  {
    eapply not_in_els_notdel; eauto.
  }

  (* execute absop *)
  unfold AOSTCBPrioTbl.
  hoare normal pre.
  hoare_ex_intro.
   hoare_lifts_trms_pre RH_PrioTbl_P.
   eapply pure_split_rule'; introv Hrh_ptbl.
   destruct (get v'19 i) eqn: eq1.
   2:{ eapply Hrh_ptbl in eq1. clear -Hprio_range' eq1.
          false; eapply eq1; split; int auto.  }
   hoare_lifts_trms_pre (Aop, absptls).
   assert (Hpdata: e = Holder \/ e <> Holder) by tauto.
   destruct Hpdata.
   2: { eapply abscsq_rule.
           apply noabs_oslinv.
           eapply mutexcre_absimp_prio_vhold_abt; eauto.
           pure_auto.
           simpl. intros; split; auto.
           eapply absinfer_eq. 
           apply absabort_rule.
         }
     subst e.
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mutexcre_absimp_prio_vhold; eauto.
      pure_auto.
      simpl. intros; split; auto.
      eapply absinfer_eq. 

     hoare_lifts_trms_pre (Aop, absecblist).
   assert (Hpcase: ~(exists eid ow wl, get els eid = Some (absmutexsem i ow, wl)) \/
                                      (exists eid ow wl, get els eid = Some (absmutexsem i ow, wl))) by tauto.
   destruct Hpcase.
   2: { eapply abscsq_rule.
           apply noabs_oslinv.
           eapply mutexcre_absimp_prio_unused_abt; eauto.
           pure_auto.
           simpl. intros; split; auto.
           eapply absinfer_eq. 
           apply absabort_rule.
         }
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mutexcre_absimp_prio_unused; eauto.
      pure_auto.
      simpl. intros; split; auto.
      eapply absinfer_eq.

  hoare_lifts_trms_pre (Aop, absecblsid, evlocid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexcre_absimp_ecb_activate; auto.
  can_change_aop_solver.
  simpl. intros; split; auto.
  pure_auto.
  eapply absinfer_eq.

  (* prepare to exit from critical section *)
  fold_evaux_loc (V$ __EvLoc_ecbcre2).
    unfold ASemEIBs.
  unfold AMuxEIBs.
  unfold AMqEIBs.
  hoare_split_pure_all.
  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_frm'.
  unfold AECBList.
  trycancel_EvtInv.
  sep normal.
  sep eexists.
  sep cancel OSEventList.
  instantiate (9:= (DMutex (Vint32 (Int.or (i<<ᵢ$ 8) ($ OS_MUTEX_AVAILABLE))) Vnull) :: v'26).
  instantiate (9:= ((V$ OS_EVENT_TYPE_MUTEX
             :: Vint32 Int.zero
                :: Vint32 (Int.or (i<<ᵢ$ 8) ($ OS_MUTEX_AVAILABLE))
                   :: Vnull :: v'5 :: v'42 :: Vint32 Int.zero :: v'9 :: nil), INIT_EVENT_TBL, INIT_EVENT_PTBL) :: v'23).
  simpl evsllseg at 1.
  unfold AEventNode.
  unfold AOSEvent.
  unfold AEventData.
  unfold AOSEventTbl.
  unfold AOSPostEventTbl.
  sep normal.
  sep eexists.
  sep cancel node.
  sep cancel Aarray.
  sep cancel Aarray.
  sep cancel evsllseg.
  sep split; eauto.
  eapply fold_EvtInv_part2; try sep cancel evloc; try sep cancel evptr; eauto.
  eapply sem_ecb_cre2_preserve_mux; eauto.
  eapply mux_ecb_cre2_preserve_mux; eauto.
  eapply q_ecb_cre2_preserve_mux; eauto.
  introv Hex. apply Hndel.
  destruct Hex as (t & Hneq & tle).
  exists t. auto.
  eapply evcre_nodup_cre2_preserve_mux; eauto.
  eapply evdel_nodup_cre2_preserve; eauto.
  unfold ASemEIBs.
  unfold AMuxEIBs.
  unfold AMqEIBs.
  unfold tcbllsegevaux.
  trycancel_EvtInv.
  sep pauto; eauto.
  eapply RH_SEM_EINFO_ECB_P_semcre_preserve; eauto.  
  eapply RH_ECBlk_EIBlk_Mux_P_semcre_preserve; eauto.  
  eapply RH_EIBlk_ECBlk_Q_P_preserve; eauto.


  eapply ECBList_Mutex_Create_prop; eauto.
  clear -Hprio_range; unfold OS_LOWEST_PRIO in *; int auto.
  apply semcre_RL_Tbl_init_prop.
  unfolds; simpl; auto.
  unfold array_type_vallist_match.
  splits; pauto.
  apply semcre_RL_Tbl_init_prop.
  unfolds; simpl; auto.
  unfold array_type_vallist_match.
  splits; pauto.

  eapply Hrh_ptbl in eq1.
  destruct eq1 as (Hprio_range'' & Hnth).
  hoare forward prim.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep cancel Aier.
  unfold AOSTCBPrioTbl.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep cancel CurTid.
  sep normal. sep eexists.
  sep split; eauto.
  try_cancel_evaux_asst.
  sep cancel flag_off.
  sep cancel vhold_addr.
  sep cancel OSTCBPrioTbl.
  sep cancel OSPlaceHolder.
  sep cancel absptls.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  cancel_corecommuinv. 
  
  (* PartitionInv *)
  Require Import sem_partition.
  cancel_partitioninv.
  eauto.
  (* end of PartitionInv *)

  splits; eauto. unfold isevloc. auto. 
  eapply Mutex_Create_TCB_prop; eauto.
  eapply priotbl_null_no_tcb'; eauto.
  
  pure_auto.

   (* assign err *)
   clear -Hverr_ptr Hrange.
  hoare forward prim.
  (* splits; pauto. *)
  unfold EvtInv.
  hoare unfold.

  rename v'17 into vcspace.
  rename v'18 into v18. 
  rename v'19 into v19. 
  rename v'20 into v20.
  
  rename v'21 into v'17. 
  rename v'22 into v'18. 
  rename v'23 into v'19. 
  rename v'24 into v'20. 
  rename v'25 into v'21. 
  rename v'26 into v'22. 
  rename v'27 into v'23. 
  rename v'28 into v'24. 
  rename v'29 into v'25. 
  rename v'30 into v'26. 
  rename v'31 into v'27. 
  rename v'32 into v'28. 
  rename v'33 into v'29. 
  rename v'34 into v'30. 
  rename v'35 into v'31. 
  rename v'36 into v'32. 
  rename v'37 into v'33. 
  rename v'38 into v'34. 
  rename v'39 into v'35. 
  
  hoare_lifts_trms_pre (Aop, eblist).
  destruct Hverr_ptr as [Hverr_eq | (errid & Hverr_eq)];
  rewrite Hverr_eq.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexcre_absimp_err_none_abt; eauto.
  pure_auto.
  eapply absinfer_eq. 
  eapply absabort_rule.
  rename v'33 into ebls.
  destruct (EbMod.get ebls errid) eqn: eq1.
  2: { eapply abscsq_rule.
          apply noabs_oslinv.
          eapply mutexcre_absimp_err_none_abt; eauto.
          pure_auto.
          eapply absinfer_eq. 
          eapply absabort_rule.
        }
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutexcre_absimp_seterr; eauto.
    pure_auto.
    eapply absinfer_eq. 
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AErrblkList).
  eapply err_list_split_frm; eauto.
  unfold node.
  hoare unfold.
  inverts H9; inverts H10.
  hoare forward.
  hoare_lifts_trms_pre (Aop, err).
  eapply assign_rule_deref_ptr.
  intros. sep get rv.
  simpl Astruct.
  split.
  introv Hsat. sep cancel (Aptrmapsto). eauto.
  intros; sep auto.
  intros; sep get rv.
  eapply eq_int; auto.
  intros. sep eexists. sep cancel p_local. simpl; auto.
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  sep pauto; eauto.
  trycancel_EvtInv.
  sep cancel Aier.
  unfold AErrblkList.
  sep pauto.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eapply err_sllseg_merge with (vsem:= (v'42, Int.zero)) (errv:= (Int.repr OS_NO_ERR)) 
                                                                   (vl:= ((V$ OS_NO_ERR) :: v'38 :: nil)); eauto.
  sep cancel err_sllseg.
  sep cancel err_sllseg.
  unfold node.
  simpl Astruct.
  sep pauto; eauto.
  sep cancel (Aptrmapsto).
  sep cancel Aptrmapsto.
  eauto.
  eapply EbMod.my_joinsig_join_set; eauto.
  eapply my_joinsig_set; eauto.
  split; auto. go.
  rewrite EbMod.map_get_set; auto.
  auto.
  pure_auto.
  (* end of err *)

  (* return *) 
  hoare forward.
  pure_auto.
  unfold isptr; pure_auto.
Qed.

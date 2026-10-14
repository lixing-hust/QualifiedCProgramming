Require Import ucos_include.
Require Import os_ucos_h.
Require Import sep_lemmas_ext.
Require Import linv_solver.
Require Import inline_definitions.
Require Import inline_bittblfunctions.
Require Import inline_tactics.
Require Import symbolic_lemmas.
Require Import new_inv.
Require Import task_pure.

Require Import seplog_lemmas.
Require Import seplog_tactics.
Require Import sep_cancel_ext.
Require Import sep_combine_lemmas.
Require Import sep_combine.

Require Import protect.
Require Import OSQPostPure.
Require Import Lia.

Require Import abs_infer_abt. 


(* Require Import ifun_taskcreate. *)
Require Import List.
Require Import ifun_spec.
Require Import os_program.
Require Import os_task.
Require Import seplog_trm_tacs.

Require Import assertion.
Require Import hoare_assign.
Require Import hoare_if.
Require Import hoare_ret.
Require Import hoare_call.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.
Require Import ifun_taskdel_spec.

Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.

Lemma fold_init_lg :
  init_lg = (logic_val  (Vint32 (Int.repr 1%Z)) ::
  logic_val (Vint32 (Int.repr __EvLoc_normal)) ::
  logic_val Vnull ::
  logic_val Vnull ::
  logic_val Vnull ::
  nil).
Proof.
  unfold init_lg.
  auto. 
Qed.


Lemma aemp_isr_elim:
forall s P,
  s |= aemp_isr_is ** P -> s |= P.
Proof.
  introv Hsat.
  simpl in Hsat.
  simpljoin.
  destruct_s s. 
  simpl in *.
  assert (m=x0) by join auto.
  assert (o=x3) by join auto.
  subst.
  auto.
Qed.



Lemma absimp_taskdel_rdy_succ:
forall P v3 sch t tls mqls ct ,
  can_change_aop P ->
  (* Int.lt ($ 63) v3 = false ->
   * (* OSAbstMod.get O abtcblsid = Some (abstcblist tls) -> *)
   * ~ (exists t' st msg, TcbMod.get tls t' = Some (v3, st, msg)) ->
   * (exists t', TcbMod.join tls (TcbMod.sig t' (v3, rdy, Vnull)) tls' )-> *)
  absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||> **
                     HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
           ( <|| sdel ((Vint32 v3):: nil);;isched ;; END (Some (Vint32 (Int.repr NO_ERR))) ||> **  HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
intros.
unfold taskdelcode.
infer_branch 5%nat.
unfold sdel.
eapply absinfer_eq.
Qed.

Lemma absimp_taskdel_cler_waitls_bit:
  forall P v3 sch tls els ct els' st wait_t msg sus eid ehb wl tid t,
    can_change_aop P ->
    TcbMod.get tls tid = Some (v3, wait st wait_t, msg, sus) ->
    isWait4Ecb st eid ->
    EcbMod.get els eid = Some (ehb, wl) ->
    els' = set els eid (ehb, (remove_tid tid wl)) ->
    (* Int.lt ($ 63) v3 = false ->
     * (* OSAbstMod.get O abtcblsid = Some (abstcblist tls) -> *)
     * ~ (exists t' st msg, TcbMod.get tls t' = Some (v3, st, msg)) ->
     * (exists t', TcbMod.join tls (TcbMod.sig t' (v3, rdy, Vnull)) tls' )-> *)
    absinfer sch 
             ( <|| taskdel_clear_waitls_bit (|((Vint32 v3) :: nil)|) ;; spec_del (Vint32 v3)  ;;isched ;; END (Some (Vint32 (Int.repr NO_ERR))) ||> **  HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| spec_del (Vint32 v3);;  isched ;; END (Some (Vint32 (Int.repr NO_ERR))) ||> **  HECBList els' ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
.
Proof.
  intros.
  infer_part1 0%nat.
  infer_part2.
Qed.


Lemma derive_delself_rule':
  forall pa P  prio st msg sus tls' tls t e tp  aop r ri sd Spec I isr ier ie is cs,
    GoodLInvAsrt pa ->
    GoodFrm P ->
    joinsig t (prio, st, msg, sus) tls' tls  ->
    P ==>  Rv e @ tp == Vptr t //\\  CurLINV pa t ->
    InfRules Spec sd pa I r ri 
             (
               <|| spec_del  (Vint32 prio);; aop ||>  **
                   Aabsdata abstcblsid (abstcblist tls) **
                   Aabsdata curtid (oscurt t) **
                   Aisr isr ** Aier ier ** Aie ie ** Ais is ** Acs cs ** P
             ) 
             (sprim (stkfree e))
             (
               <|| aop ||>  **
                   Aabsdata abstcblsid (abstcblist tls') ** 
                   Aabsdata curtid (oscurt t) **
                   Aisr isr ** Aier ier ** Aie ie ** Ais is ** Acs cs 
                   ** P
             ) t.
Proof.
  intros.
  eapply backward_rule1.
  instantiate (1:= (
                    <|| spec_del (Vint32 prio);; aop ||> ** P**
                        HTCBList tls ** HCurTCB t ** Aisr isr ** Aier ier ** Aie ie ** Ais is ** Acs cs 
                        
                  )).
  intro.
  intros.
  sep pauto.
  eapply forward_rule2.
  eapply delself_rule; eauto.
  intro.
  intro.
  sep pauto.
Qed.

Lemma derive_delself_rule:
  forall pa P  prio st msg sus tls' tls t e tp  aop r ri sd Spec I isr ier ie is cs,
    GoodLInvAsrt pa ->
    GoodFrm P ->
    joinsig t (prio, st, msg, sus) tls' tls  ->
    P ==>  Rv e @ tp == Vptr t //\\  CurLINV pa t ->
    InfRules Spec sd pa I r ri 
             (
               <|| spec_del  (Vint32 prio);; aop ||>  **
                   Aabsdata abstcblsid (abstcblist tls) **
                   Aabsdata curtid (oscurt t) **
                   OS[isr, ier, ie, is, cs] ** P
             ) 
             (sprim (stkfree e))
             (
               <|| aop ||>  **
                   Aabsdata abstcblsid (abstcblist tls') ** 
                   Aabsdata curtid (oscurt t) **
                   OS[isr, ier, ie, is, cs]  
                   ** P
             ) t.
Proof.
  intros.
  eapply backward_rule1.
  instantiate (1:= (
                    <|| spec_del (Vint32 prio);; aop ||> ** P**
                        HTCBList tls ** HCurTCB t ** OS [isr, ier, ie, is, cs] 
                        
                  )).
  intro.
  intros.
  sep pauto.
  eapply forward_rule2.
  eapply delself_rule; eauto.
  intro.
  intro.
  sep pauto.
Qed.

Local Ltac sifs := 
  match goal with
    | |- context[if ?e then _ else _] => destruct e; sifs
    | |- _ <> _ => try solve [simpl; intro; tryfalse]
    | _ => idtac
  end.


Set Nested Proofs Allowed.

Lemma OSTaskDelete_proof:
  forall vl p r logicl ct, 
    Some p =
    BuildPreI new_os_internal OSTaskDel
                vl logicl OSTaskDeletePre ct->
    Some r =
    BuildRetI new_os_internal OSTaskDel vl logicl OSTaskDeletePost ct->
    exists t d1 d2 s,
      new_os_internal OSTaskDel = Some (t, d1, d2, s) /\
      {|new_OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  hoare unfold.

  rename v'5 into vier.

  (* If (prio ′ ==ₑ ′ OS_IDLE_PRIO)*)
  hoare forward.
  math simpls.

  destruct ( Int.eq i ($ OS_IDLE_PRIO)); simpl; intro; tryfalse.

  hoare unfold.
 
  assert(Int.eq ($ OS_IDLE_PRIO) i = true).
  change OS_IDLE_PRIO with 63 in *.
  int auto.

  rename v'4 into opv.
  change ((Vint32 i :: nil) ++ opv :: nil) with (Vint32 i  :: opv :: nil).
  assert (Hopv: opv = Vint32 (Int.repr OS_TASK_DEL_IDLE) \/ opv <>Vint32 (Int.repr OS_TASK_DEL_IDLE)) by tauto.
  destruct Hopv. 
  subst.

 (* opv = Vint32 (Int.repr OS_TASK_DEL_IDLE) *)
  
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskdel_prio_is_idle'.
  auto.
  go.
 auto.
 
  hoare forward.
  pure_auto.
  change OS_TASK_DEL_IDLE with 61.
  int auto.
  change OS_IDLE_PRIO with 63; lia.
  change OS_IDLE_PRIO with 63; lia.
  change OS_TASK_DEL_IDLE with 61.
  int auto.
  change OS_IDLE_PRIO with 63; lia.
  change OS_IDLE_PRIO with 63; lia.


 (* opv <> Vint32 (Int.repr OS_TASK_DEL_IDLE) *) 
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskdel_prio_is_idle_abt'.
  auto.
  can_change_aop_solver.
  auto.
  eapply absabort_rule.

  (* (prio ′ ≥ ′ OS_LOWEST_PRIO) *)
  hoare forward.
  hoare forward.
  math simpls.
  sifs.
  math simpls.
  sifs.
  sifs.
  hoare unfold.

  assert(Int.ltu ($ OS_LOWEST_PRIO) i = true).
  change OS_LOWEST_PRIO with 63 in *.
  change OS_IDLE_PRIO with 63 in *.
  change OS_PRIO_SELF with 255 in *.
  int auto.
  destruct H.
  inversion H.
  inversion H.

  rename v'4 into opv.
  change ((Vint32 i :: nil) ++ opv :: nil) with (Vint32 i  :: opv :: nil).
  assert (Hopv: opv = Vint32 (Int.repr OS_PRIO_INVALID) \/ opv <>Vint32 (Int.repr OS_PRIO_INVALID)) by tauto.
  destruct Hopv. 
  subst.

   (* opv = Vint32 (Int.repr OS_PRIO_INVALID) *)
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskdel_prio_invalid'.
  auto.
  go.
  auto.

  hoare forward.
  pure_auto; int auto; change OS_LOWEST_PRIO with 63; change OS_IDLE_PRIO with 63; change OS_PRIO_INVALID  with 42; lia.

   (* opv <> Vint32 (Int.repr OS_PRIO_INVALID) *) 

   hoare abscsq.
   apply noabs_oslinv.
   eapply absimp_taskdel_prio_invalid_abt'.
   auto.
   can_change_aop_solver.
   auto.
   eapply absabort_rule.

  hoare forward.
  hoare unfold.

  (* ENTER_CRITICAL;ₛ*)
  eapply seq_rule.
  hoare_enter_critical.

  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (OSInv, p_local).
  apply inv_change in Hsat.
  rewrite <- fold_init_lg in Hsat.
  unfold OldOSInvWL in Hsat.
  exact Hsat.
  unfold EvtInv.

  (* Do not expand init_lg *)
  (* hoare forward prim. *)
  hoare unfold.

  rename v'15 into vv15.
  rename v'17 into vv17.
  rename v'18 into vv18.
  rename v'19 into vptb.
  rename v'20 into vpthattr.
  rename v'21 into vcspace.
  rename v'22 into vv22. 
  rename v'23 into vv23. 
  rename v'24 into vv24.
  rename v'27 into vv27.
  
  rename v'14 into v'19.
  rename v'13 into v'18.
  rename v'12 into v'17.
  rename v'11 into v'16.
  rename v'10 into v'15.
  rename v'9 into v'14.
  rename v'8 into v'13.
  rename v'7 into v'12.
  rename v'6 into v'11.
  rename v'5 into v'10.
  rename v'44 into v'27.


  rename H2 into HH2.
  rename H4 into HH4. 
  rename H5 into HH5.
  rename H6 into HH6.
  rename H7 into HH7.
  rename H8 into HH8.
  rename H9 into HH9. 
  rename H15 into HH15.

  rename H10 into H2.
  rename H11 into H3.
  rename H12 into H4.
  rename H13 into H5.
  rename H14 into H6.
  rename H16 into H7.  

 
  unfold AOSTCBList.  
  hoare normal pre.
  hoare_split_pure_all.

  rename v'28 into vv28.
  rename v'29 into vv29.
  rename v'30 into vv30.
  rename v'31 into vv31.

  rename v'5 into v'28.
  rename v'6 into v'29.
  rename v'7 into v'30.
  rename v'8 into v'31.

  rename v'25 into v'5.
  rename v'26 into vv26.
  rename vv28 into v'6.
  rename vv29 into v'7.
  rename vv27 into v'9.
  rename vv30 into v'8.
  rename vv17 into v'22.
  rename vv18 into v'23.


  unfold1 tcbdllseg.
  unfold1 dllseg.
  unfold node.
  hoare normal pre.
  hoare_split_pure_all.

  rename v'32 into vv32.
  rename v'33 into vv33.
  rename v'20 into v'32.
  rename v'21 into v'33.  
  simpljoin.

  inverts H12.

(* ** ac:   Check OSTCBflag_des. *)
                               
  lets bb: OSTCBflag_des H16.
  simpljoin.

  hoare unfold.
  assert (Int.unsigned i < 64).
  clear -H0.
  change OS_LOWEST_PRIO with 63 in *.
  int auto.
  destruct H0;
  tryfalse.
  assert (Int.unsigned i <> 63).
  clear -H.
  change OS_IDLE_PRIO with 63 in *.
  destruct H; int auto.
  clear H H0.
  rename H13 into H.
  rename H14 into H0.

  unfold  OS_LOWEST_PRIO in *.
  assert (   rule_type_val_match OS_TCB ∗ (nth_val' (Z.to_nat (Int.unsigned i)) v'10) = true).
  eapply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match.
  rewrite H7.
  clear -H.
  mauto.
  auto.
  

(* ptcb ′ =ₑ OSTCBPrioTbl ′ [prio ′];ₛ *)
  hoare forward.
  math simpls.
  assumption.
  
  assert (exists t sus, TcbMod.get v'19 ((v'33, Int.zero)) = Some (x5, t, x2, sus)).
  {
  unfold1 TCBList_P in H11.
  simpljoin.
  unfolds in H18.
  destruct x11; destruct p; destruct p.
  simpljoin.
  inverts H20.
  unfolds in H22; simpl in H22.
  inverts H18.
  inverts H11.
  unfold join,sig,get in *; simpl in *.
  unfold join,sig,get in *; simpl in *.
  do 2 eexists.
  go.
  }


  destruct H14 as (hello & vsus & kitty).
  protect kitty.

  clear H3.
  assert (H3: RH_CurTCB (v'33, Int.zero) v'19).
  {
   unfold RH_CurTCB.
   exists x5 hello x2 vsus.
   auto.   
  }

 
  (* If (ptcb ′ ==ₑ NULL){EXIT_CRITICAL;ₛ
RETURN ′ OS_TASK_DEL_ERR};ₛ *)
  hoare forward.
    (* ptcb ′ ==ₑ NULL *)
  destruct ( nth_val' (Z.to_nat (Int.unsigned i)) v'10 ); tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  unfold val_eq in H17.
  destruct a; tryfalse.
  
  hoare unfold.

  assert(~
  (exists tid st msg sus,
   TcbMod.get v'19 tid = Some (i, st, msg, sus))).
  {
    intro.
    apply H14.
    destruct H13.
    Focus 2.
    simpljoin.
    rename x11 into vsus1.
    rename x12 into x11.
    rewrite H13.
    simpl.
    destruct x11.
    reflexivity.
    false.
    simpljoin.
    rename x11 into vsus1.
    unfolds in H6.
    simpljoin.
    lets bb: H20 H19.
    simpljoin.
    unfold nat_of_Z in H22.
    apply nv'2nv in H13.
    rewrite H13 in H22.
    inverts H22.
    intro; tryfalse.
  }

  rename v'4 into opv.
  change ((Vint32 i :: nil) ++ opv :: nil) with (Vint32 i  :: opv :: nil).
  assert (Hopv: opv = Vint32 (Int.repr OS_TASK_DEL_ERR) \/ opv <>Vint32 (Int.repr OS_TASK_DEL_ERR)) by tauto.
  destruct Hopv. 
  subst.
(* opv = Vint32 (Int.repr OS_TASK_DEL_ERR) *)  

  hoare lifts (1::13::41::42::43::nil)%nat pre.
  instantiate(1:= Afalse).

  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absimp_taskdel_prio_no_such_tcb'; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.


(* EXIT_CRITICAL;ₛ RETURN ′ OS_TASK_DEL_ERR*)
  hoare forward prim.
  sep cancel APthreadAttr. 
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep cancel p_local.
  sep cancel Aier.  
  unfold EvtInv.

  sep normal.
  do 19 eexists.


  sep cancel AOSEventFreeList.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AECBList.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel AEvArrayHeap.

  sep cancel AErrblkList .
  sep cancel tcbllsegevaux.
  unfold AOSTCBFreeList.
  instantiate(1:=LV x @ OS_TCB ∗ |-> v'2 **
  LV self @ char_t |-> v'1 **
  LV pevent @ OS_EVENT ∗ |-> v' **
  LV prio @ char_t |-> Vint32 i ** LV ptcb @ OS_TCB ∗ |-> nth_val' (Z.to_nat (Int.unsigned i)) v'10 **
  A_dom_lenv
    ((prio, char_t)
     :: (pevent, OS_EVENT ∗)
        :: (ptcb, OS_TCB ∗)
           :: (self, char_t) :: (x, OS_TCB ∗) :: nil)).
  sep auto.

  eauto.
  go.
  go.
  go.
  go.

  hoare forward.

  pure_auto; int auto;  change OS_TASK_DEL_ERR  with 60; lia.


  (* opv <> Vint32 (Int.repr OS_TASK_DEL_ERR) *) 

  hoare lifts (1::13::41::42::43::nil)%nat pre.

  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absimp_taskdel_prio_no_such_tcb_abt'; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule.

  (*  If (ptcb ′ ==ₑ os_task.PlaceHolder)*)
  hoare forward.
  hoare_split_pure_all.

  unfold os_task.PlaceHolder.
  hoare unfold.
  assert (exists p, (nth_val' (Z.to_nat (Int.unsigned i)) v'10) = Vptr p).
  clear -H13 H14.
  destruct H14.
  unfolds in H13.
  
  destruct (nth_val' (Z.to_nat (Int.unsigned i)) v'10); tryfalse.
  destruct H13; tryfalse.
  assumption.
  destruct (nth_val' (Z.to_nat (Int.unsigned i)) v'10); tryfalse.
  destruct a; simpl in H.
  tryfalse.
  clear H13 H14.
  simpljoin.
  rewrite H13.

  eapply seq_rule.
  {
    eapply ift_rule''.
    intro.
    intros.
    eapply symbolic_lemmas.bop_rv.
    sep_get_rv.
    eapply symbolic_lemmas.addrof_gvar_rv.
    gen_notin_lenv H14 OSPlaceHolder.
    eapply symbolic_lemmas.dom_lenv_imp_notin_lenv.
    eauto.
    sep cancel A_dom_lenv.
    sep cancel Agvarenv'.
    eauto.
    eauto.
    simpl.
    destruct x; destruct vhold_addr.
    destruct ( Int.eq i0 i1 ); destruct (peq b b0); simpl; intro; tryfalse.
    simpl.
    eauto.
    hoare unfold.
    instantiate (1:=Afalse).

  assert(~
  (exists tid st msg sus,
   TcbMod.get v'19 tid = Some (i, st, msg, sus))).
   {
    intro.
    apply H14.
    assert ( x <> vhold_addr \/ x = vhold_addr).
    tauto.
    destruct H20.
    simpl.
    destruct x; destruct vhold_addr.
    remember (peq b b0).
    destruct s.
    subst.
(* ** ac:       SearchAbout (Int.eq ). *)
    rewrite Int.eq_false.
    reflexivity.
    intro; tryfalse.
    reflexivity.
    subst x.
    simpl.
    false.
    simpljoin.
    unfolds in H6.
    simpljoin.
    lets bb: H20 H19.
    simpljoin.
    unfold nat_of_Z in H22.
    apply nv'2nv in H13.
    rewrite H13 in H22.
    inverts H22.
    apply H23; reflexivity.
    intro; tryfalse.
  }

  rename v'4 into opv.
  change ((Vint32 i :: nil) ++ opv :: nil) with (Vint32 i  :: opv :: nil).
  assert (Hopv: opv = Vint32 (Int.repr OS_TASK_DEL_ERR) \/ opv <>Vint32 (Int.repr OS_TASK_DEL_ERR)) by tauto.
  destruct Hopv. 
  subst.

  
(* opv = Vint32 (Int.repr OS_TASK_DEL_ERR) *) 


   hoare lifts (1::13::41::42::43::nil)%nat pre. 
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absimp_taskdel_prio_no_such_tcb'; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.


    hoare forward.
    hoare unfold.

    instantiate(1:=(<|| v'3 ||>  **
    Aisr empisr **
    Aie true **
    Ais nil **
    Acs nil **
    p_local OSLInv (v'33, Int.zero) init_lg **
    LV ptcb @ OS_TCB ∗ |-> Vptr x **
    LV os_code_defs.x @ OS_TCB ∗ |-> v'2 **
    LV self @ char_t |-> v'1 **
    LV pevent @ OS_EVENT ∗ |-> v' **
    LV prio @ char_t |-> Vint32 i **
    A_dom_lenv
      ((prio, char_t)
       :: (pevent, OS_EVENT ∗)
          :: (ptcb, OS_TCB ∗)
             :: (self, char_t)
                :: (os_code_defs.x, OS_TCB ∗) :: nil))).

    hoare forward prim.
    unfold EvtInv.
    sep normal.
    do 19 eexists.
    sep cancel APthreadAttr. 
    sep cancel CoreCommuInv.
    sep cancel CapabilityInv.
    sep cancel p_local.
    sep cancel Aier.
    sep cancel AOSEventFreeList.
    sep cancel AOSQFreeList.
    sep cancel AOSQFreeBlk.
    sep cancel AECBList.
    sep cancel ASemEIBs.
    sep cancel AMuxEIBs.
    sep cancel AMqEIBs.
    sep cancel AEvArrayHeap.
  
    sep cancel AErrblkList .
    sep cancel tcbllsegevaux.

    unfold AOSTCBPrioTbl.
    unfold AOSTCBList.

    sep pauto.

    sep cancel 4%nat 1%nat.
    
    unfold tcbdllseg.
    unfold1 dllseg.
    unfold node.
    sep pauto.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat .
    eauto.
    go.
    go.
    go.
    go.
    go.
    go.
    sep auto.

    hoare forward.

    pure_auto; int auto;  change OS_TASK_DEL_ERR  with 60; lia.

    (* opv <> Vint32 (Int.repr OS_TASK_DEL_ERR) *) 

    hoare lifts (1::13::41::42::43::nil)%nat pre.
  
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absimp_taskdel_prio_no_such_tcb_abt'; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
    eapply absabort_rule.

  }

  (* self ′ =ᶠ OS_IsSomeMutexOwner (·ptcb ′·);ₛ *)

  hoare forward.  
  hoare unfold.


  (*
  eapply seq_rule.
  eapply calle_rule_lvar'.
  intuition eauto.
  intros.
  apply rvl_elim.
  symbolic_execution.
  apply rvl_nil.
  intros.
  unfold_spec.

  *)

  (**********************)
  (* last is H15 *)


  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (aemp_isr_is).
  eapply aemp_isr_elim in Hsat. 
  exact Hsat.

  hoare forward.

  sep cancel AECBList.
  sep cancel tcbdllflag.
  sep cancel AOSRdyTblGrp.
  unfold AOSTCBList.
  unfold AOSTCBPrioTbl.

  sep pauto.
  sep cancel 5%nat 1%nat.
  unfold tcbdllseg.
  unfold1 dllseg.
  sep pauto.
  unfold node.
  sep pauto.
  sep cancel dllseg.
  sep cancel Astruct.
  sep cancel 2%nat 1%nat.
  eauto.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.

Lemma retpost_issomemutexowner: 
retpost OS_IsSomeMutexOwnerPost.
Proof.
  unfolds.
  intros.
  unfold getasrt in H.
  unfold  OS_IsSomeMutexOwnerPost in H.
  unfold  OS_IsSomeMutexOwnerPost' in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  destruct H4.
  simpljoin.
  intro; tryfalse.
  simpljoin.
  intro; tryfalse.
Qed.

exact retpost_issomemutexowner. (* retpost*)
  intro;intros.
  linv_solver.
  linv_solver.
  unfold OS_IsSomeMutexOwnerPost.
  unfold getasrt.
  unfold OS_IsSomeMutexOwnerPost'.
  hoare unfold.
  apply eq_sym in H20.
  inverts H20.
  destruct H21.
  Focus 2.
  (* is some mutex owner *)
  simpljoin.
  inverts H18.
  hoare forward.
  change (Int.eq ($ 1) ($ 1)) with true.
  (* simpl; intro; tryfalse. *)
  hoare unfold.
  instantiate (1:=Afalse).

  rename v'50 into v'45.


  assert(exists x y z w tt mm sus,
  TcbMod.get v'19 v'45 = Some (i, tt, mm, sus) /\ EcbMod.get v'18 x = Some (absmutexsem y (Some (v'45, z)), w)).
  {
    unfolds in H20.
    assert (v'45 <> vhold_addr) as some_pure.
    clear -H14.
    intro.
    subst.
    simpl in H14.
    destruct vhold_addr; simpl in H14.
    rewrite peq_true in H14.
    rewrite Int.eq_true in H14.
    simpl in H14.
    destruct H14; tryfalse.
    unfolds in H6.
    simpljoin.
    unfold nat_of_Z in H6.
    assert (0 <= Int.unsigned i < 64).
    clear -H.
    int auto.
    apply nv'2nv in H13.
    lets bb: H6 H25 H13 some_pure.
    simpljoin.
    repeat tri_exists_and_solver1.
    intro; tryfalse.
  } 
  

  rename v'4 into opv.
  change ((Vint32 i :: nil) ++ opv :: nil) with (Vint32 i  :: opv :: nil).
  assert (Hopv: opv = Vint32 (Int.repr OS_TASK_DEL_SOME_MUTEX_OWNER) \/ opv <>Vint32 (Int.repr OS_TASK_DEL_SOME_MUTEX_OWNER)) by tauto.
  destruct Hopv. 
  subst.

  
(* opv = Vint32 (Int.repr OS_TASK_DEL_SOME_MUTEX_OWNER) *)   

   hoare lifts (15::11::12::45::13::nil)%nat pre. 
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply absimp_taskdel_some_mutex_owner'; eauto.
   can_change_aop_solver.
   eapply absinfer_eq.

hoare_lifts_trms_pre (Aisr, Ais, Aier).
eapply backward_rule1.
introv Hsat.
eapply add_aemp_isr_is_prop in Hsat.
exact Hsat.

hoare forward prim.

unfold EvtInv.
sep normal.
sep eexists.
sep cancel APthreadAttr. 
sep cancel CoreCommuInv.
sep cancel CapabilityInv.
sep cancel p_local.
sep cancel Aier.
sep cancel AOSEventFreeList.
sep cancel AOSQFreeList.
sep cancel AOSQFreeBlk.
sep cancel AECBList.
sep cancel ASemEIBs.
sep cancel AMuxEIBs.
sep cancel AMqEIBs.
sep cancel AEvArrayHeap.

sep cancel AErrblkList .
sep cancel tcbllsegevaux.
sep pauto.
go.
go.

hoare forward.

pure_auto; int auto; change OS_TASK_DEL_SOME_MUTEX_OWNER  with 62; lia.

(* opv <> Vint32 (Int.repr OS_TASK_DEL_SOME_MUTEX_OWNER) *) 

hoare lifts (15::11::12::45::13::nil)%nat pre. 
  
eapply abscsq_rule.
apply noabs_oslinv.
eapply absimp_taskdel_some_mutex_owner_abt'; eauto.
can_change_aop_solver.
eapply absinfer_eq.
eapply absabort_rule.

(* If (ptcb ′ .. OSTCBNext ==ₑ NULL)*)
hoare forward.
hoare unfold.
false.
clear -H18.
int auto.
destruct H18; tryfalse.
simpljoin.
inverts H18.
rename v'50 into v'45.
rename H20 into some_pure_hyp.

(* If (self ′ ==ₑ ′ 1){EXIT_CRITICAL;ₛ
RETURN ′ OS_TASK_DEL_SOME_MUTEX_OWNER};ₛ *)
hoare forward.

change (Int.eq ($ 0) ($ 1)) with false.
hoare unfold.
false.
clear -H18.
int auto.
instantiate (1:=Afalse).
hoare forward.
hoare unfold.
clear H18.

Lemma valinjbopevallemma:
forall x v'19, val_inj (bop_eval (Vptr x) (Vptr v'19) OS_TCB ∗ (Int8u) ∗ oeq) =
    Vint32 Int.zero \/
    val_inj (bop_eval (Vptr x) (Vptr v'19) OS_TCB ∗ (Int8u) ∗ oeq) =
    Vnull -> x <> v'19.
Proof.
intros.
destruct H.
simpl in H.
destruct x; destruct v'19.
intro.
inverts H0.
rewrite peq_true in H.
rewrite Int.eq_true in H.
inverts H.
simpl in H.
destruct x; destruct v'19.
destruct (peq b b0); destruct (Int.eq i i0); tryfalse.
Qed.

apply valinjbopevallemma in H14.
unfold AOSTCBList.
hoare unfold.

rename v'35 into vv35.
rename v'21 into v'35.
rename v'34 into vv34.
rename v'20 into v'34.

(* rename v'21 into vhold. *)
rename v'33 into cur_tcb_blk.
rename v'19 into tcbmap.
rename v'10 into priotbl.
rename v'45 into todelptr.
assert (exists st m sus, TcbMod.get tcbmap todelptr = Some (i, st, m, sus)). 
unfolds in H6.
simpljoin.
apply H6.
splits.
clear; int auto.
omega.
unfold nat_of_Z.
eapply nv'2nv.
assumption.
intro; tryfalse.
assumption.
simpljoin.
rename v'15 into l2.
rename v'13 into l1.
remember  (v'32
       :: v'28
          :: x1
             :: x2 :: x3 :: x4 :: Vint32 x5 :: x6 :: x7 :: x8 :: x9 :: nil) as tcbcur.
protect Heqtcbcur.


eapply backward_rule1.
intro.
intros.
Set Printing Depth 999.
(* ** ac:   Show. *)

instantiate (1 := (
   [|ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'11 (l1++ tcbcur::l2)|] **
   tcbdllseg v'11 Vnull v'14 Vnull (l1++tcbcur::l2) **
   [|TCBList_P v'11 (l1++tcbcur::l2) v'16 tcbmap|] **   
   GV OSTCBList @ OS_TCB ∗ |-> v'11 **
   (* tcbdllseg v'11 Vnull v'12 (Vptr (cur_tcb_blk, Int.zero)) l1 ** *)
   GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
   (* tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'12 v'14 Vnull (tcbcur :: l2) ** *)
   Aisr empisr **
   Aie false **
   Ais nil **
   Acs (true :: nil) **
   Aier v'54 **
   AECBList v'9 v'8 v'18 tcbmap **
   tcbdllflag v'11 (l1 ++ tcbcur :: l2) **
   AOSRdyTblGrp v'16 v'17 **
   AOSTCBPrioTbl priotbl v'16 tcbmap v'53 vhold_addr **
   HECBList v'18 **
   HTCBList tcbmap **
   HCurTCB (cur_tcb_blk, Int.zero) **
   A_isr_is_prop **
    <||
   ASSERT (fun _ : osabst => 2%nat = 2%nat);;
   (taskdel_err_prio_invalid (|Vint32 i :: v'4 :: nil|);; v'3
    ?? taskdel_err_no_such_tcb (|Vint32 i :: v'4 :: nil|);; v'3
       ?? taskdel_err_prio_is_idle (|Vint32 i :: v'4 :: nil|);; v'3
          ?? taskdel_err_is_some_mutex_owner (|Vint32 i :: v'4 :: nil|);; v'3
             ?? taskdel_err_has_no_next (|Vint32 i :: v'4 :: nil|);; v'3
                ?? spec_del (Vint32 i);; isched;; taskdel_succ (|v'4 :: nil|);; v'3
                   ?? taskdel_clear_waitls_bit (|Vint32 i :: v'4 :: nil|);;
                      spec_del (Vint32 i);; isched;; taskdel_succ (|v'4 :: nil|);; v'3) ||>  **
   p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
   LV self @ char_t |-> (V$ 0) **
   LV ptcb @ OS_TCB ∗ |-> Vptr todelptr **
   AOSEventFreeList v'5 vv26 **
   AOSQFreeList v'6 **
   AOSQFreeBlk v'7 **
   Hebls v'41 ** AErrblkList v'41 ** Hpbls v'40 ** APosblkList v'40 ** HEvAtomHeap vv31 ** AEvAtomHeap vv31 **
   HEvStructHeap vv32 **
   AEvStructHeap vv32 **
   HEvArrayHeap vv33 **
   AEvArrayHeap vv33 **
   HSEMInfo v'37 **
   ASemEIBs vv34 vv22 v'37 v'18 vhold_addr **
   HMuxInfo v'38 **
   AMuxEIBs vv35 vv23 v'38 v'18 vhold_addr **
   HQAttr v'39 **
   AMqEIBs v'36 vv24 v'39 v'18 vhold_addr **
   HEvLoc v'42 **
   HEvPtr v'43 **
   tcbllsegevaux v'11 (l1 ++ tcbcur :: l2) v'42 v'43 **
   AOSMapTbl **
   AOSUnMapTbl **
   AOSTCBFreeList v'22 v'23 **
   AOSTime (Vint32 vv15) **
   HTime vv15 **
   AGVars **
   APthreadAttr vpthattr **
   IntInv **
   TmrInv **
   CoreCommuInv v'18 **
   PartitionInv **
   CapabilityInv vcspace **
   LV os_code_defs.x @ OS_TCB ∗ |-> v'2 **
   LV pevent @ OS_EVENT ∗ |-> v' **
   LV prio @ char_t |-> Vint32 i **
   A_dom_lenv
     ((prio, char_t)
      :: (pevent, OS_EVENT ∗) :: (ptcb, OS_TCB ∗) :: (self, char_t) :: (os_code_defs.x, OS_TCB ∗) :: nil)   
)).
eapply tcbdllseg_combine.
sep cancel tcbllsegevaux.
sep_cancel_iers.
sep pauto.
go.
go.
go.

hoare_split_pure_all.
rename x10 into xxsus.

assert (ptr_in_tcbdllseg (Vptr todelptr) v'11 (l1++tcbcur ::l2)).
Lemma tcbget_ptr_in_tcblist:
   forall tcblst head rtbl tcbmap x xx,
    TCBList_P head tcblst rtbl tcbmap ->
    get tcbmap x = Some xx ->
    ptr_in_tcbdllseg (Vptr x) head tcblst.
Proof.
  induction tcblst.
  intros.
  simpl in H.
  subst tcbmap.
(* ** ac:     SearchAbout (get empenv _ = _). *)
  rewrite map_emp_get in H0.
  inverts H0.
  intros.
  unfold1 ptr_in_tcbdllseg.
  remember (beq_val (Vptr x) head).
  destruct b.
  auto.
  unfold1 TCBList_P in H.
  simpljoin.
  rewrite H1.
  eapply IHtcblst.
  exact H4.
  assert ( x <> x0).
  intro.
  subst x0.
(* ** ac:     SearchAbout beq_val. *)
  rewrite beq_val_true in Heqb.
  tryfalse.
  unfold join,get,sig in *; simpl in *.
  eapply TcbMod.join_get_or in H2.
  destruct H2; eauto.
  rewrite TcbMod.get_a_sig_a' in H2.
  inverts H2.
  go.
  eauto.
Qed.

eapply tcbget_ptr_in_tcblist.
eauto.
eauto.
eapply backward_rule1.
intro.
intros.
eapply tcbdllseg_split' in H27.
eauto.
exact H26.
eauto.
clear Heqtcbcur.
remember (l1  ++ tcbcur :: l2) as tcblst.
protect Heqtcblst.
hoare unfold.
rename v'20 into v'21.
clear dependent v'30.
clear dependent v'31.
(*v*)
destruct v'13.
simpl.
unfold tcbdllseg.
simpl.
hoare unfold.
inverts H9.

unfold tcbdllseg.
unfold1 dllseg.
unfold node.
hoare_split_pure_all.
rename v'20 into v'30.
rename v'24 into v'31.
simpljoin.
inverts H9.
rename v'31 into todelblock.
hoare unfold.

(* If (ptcb ′ → OSTCBNext ==ₑ NULL) {EXIT_CRITICAL;ₛ
RETURN ′ OS_TASK_DEL_HAS_NO_NEXT};ₛ *)
hoare forward.
(* intro; tryfalse. *)
go.
clear -H9.
destruct H9; subst; simpl; intro; tryfalse.
simpljoin; subst; tryfalse.
simpl in H0.
destruct x; tryfalse.
hoare unfold.

rename v'4 into opv.
change ((Vint32 i :: nil) ++ opv :: nil) with (Vint32 i  :: opv :: nil).
assert (Hopv: opv = Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT) \/ opv <>Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT)) by tauto.
destruct Hopv. 
subst.


(* opv = Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT) *)      

   hoare lifts (19::15::16::49::17::nil)%nat pre. 
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply absimp_taskdel_prio_HAS_NO_NEXT'; eauto.
   can_change_aop_solver.
   eapply absinfer_eq.
  
  rename vv15 into v'20.
  remember
  (v'30
  :: v'15
     :: x22
        :: x21
           :: Vint32 i13
              :: Vint32 i12
                 :: Vint32 i11
                    :: Vint32 i10
                       :: Vint32 i9
                          :: Vint32 i8
                             :: Vint32 i7 :: nil) 
   as todelblk.
   rename v'13 into l2'.
   rename v'10 into l1'.

   eapply backward_rule1.
   intro.
   intros.
   Set Printing Depth 999.
   instantiate (1:= (
      [|ptr_in_tcbdllseg (Vptr (todelblock, Int.zero)) v'11 (l1'++ todelblk::l2')|] **
      tcbdllseg v'11 Vnull v'14 Vnull (l1'++todelblk::l2') **
      [|TCBList_P v'11 (l1'++todelblk::l2') v'16 tcbmap|] **
      <|| v'3 ||>  **
      HECBList v'18 **
      HTCBList tcbmap **
      HTime v'20 **
      HCurTCB (cur_tcb_blk, Int.zero) **
      (* Astruct (todelblock, Int.zero) OS_TCB_flag todelblk **
      dllseg v'30 (Vptr (todelblock, Int.zero)) v'14 Vnull l2' OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
        (fun vl : vallist => nth_val 0 vl) **
      dllseg v'11 Vnull v'15 (Vptr (todelblock, Int.zero)) l1' OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
        (fun vl : vallist => nth_val 0 vl) ** *)
      GV OSTCBList @ OS_TCB ∗ |-> v'11 **
      GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
      Aisr empisr **
      Aie false **
      Ais nil **
      Acs (true :: nil) **
      Aier v'54 **
      AECBList v'9 v'8 v'18 tcbmap **
      tcbdllflag v'11 (l1' ++ todelblk :: l2') **
      AOSRdyTblGrp v'16 v'17 **
      AOSTCBPrioTbl priotbl v'16 tcbmap v'53 vhold_addr **
      A_isr_is_prop **
      p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
      LV self @ char_t |-> (V$ 0) **
      LV ptcb @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
      AOSEventFreeList v'5 vv26 **
      AOSQFreeList v'6 ** AOSQFreeBlk v'7 ** Hebls v'41 ** AErrblkList v'41 ** Hpbls v'40 ** APosblkList v'40 **
      HEvAtomHeap vv31 **
         AEvAtomHeap vv31 **
         HEvStructHeap vv32 **
         AEvStructHeap vv32 **
         HEvArrayHeap vv33 **
         AEvArrayHeap vv33 **
         HSEMInfo v'37 **
         ASemEIBs vv34 vv22 v'37 v'18 vhold_addr **
         HMuxInfo v'38 **
         AMuxEIBs vv35 vv23 v'38 v'18 vhold_addr **
         HQAttr v'39 **
         AMqEIBs v'36 vv24 v'39 v'18 vhold_addr **
         HEvLoc v'42 **
         HEvPtr v'43 **
         tcbllsegevaux v'11 (l1' ++ todelblk :: l2') v'42 v'43 **
         AOSMapTbl **
         AOSUnMapTbl **
         AOSTCBFreeList v'22 v'23 **
         AOSTime (Vint32 v'20) **
         AGVars **
         APthreadAttr vpthattr **
         IntInv **
         TmrInv **
         CoreCommuInv v'18 **
         PartitionInv **
         CapabilityInv vcspace **
         LV os_code_defs.x @ OS_TCB ∗ |-> v'2 **
         LV pevent @ OS_EVENT ∗ |-> v' **
         LV prio @ char_t |-> Vint32 i **
         A_dom_lenv
           ((prio, char_t)
            :: (pevent, OS_EVENT ∗) :: (ptcb, OS_TCB ∗) :: (self, char_t) :: (os_code_defs.x, OS_TCB ∗) :: nil)
   )).

   eapply tcbdllseg_combine.
   sep pauto.
   sep cancel tcbdllflag.
   sep cancel Aop.
   unfold tcbdllseg.
   unfold1 dllseg.
   unfold node.
   sep pauto.
   go.
   go.
   go.
   go.

   hoare_split_pure_all.

   instantiate (1:=Afalse).
  (* EXIT_CRITICAL;ₛ
RETURN ′ OS_TASK_DEL_HAS_NO_NEXT*)

  eapply backward_rule1.
  intros.
  eapply tcbdllseg_split' in H55.
  eauto.
  exact H24.
  eauto.
  hoare unfold.
  rename v'24 into v'31.
  rename v'25 into v'33.

  destruct v'10.
  unfold tcbdllseg; unfold dllseg.
  hoare_split_pure_all.
  inverts H59.
  rewrite H55.

  hoare_lifts_trms_pre (Aisr, Ais, Aier).
  eapply backward_rule1.
  introv Hsat.
  eapply add_aemp_isr_is_prop in Hsat.
  exact Hsat.

  hoare forward prim.

  unfold EvtInv.
  sep normal.
  sep eexists.
  sep cancel APthreadAttr. 
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel AOSEventFreeList.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AECBList.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel AEvArrayHeap.

  sep cancel AErrblkList .
  sep cancel tcbllsegevaux.

  unfold AOSTCBList.
  sep pauto.

  go.
  go.
  go.
  go.
  go.

  (* RETURN ′ OS_TASK_DEL_HAS_NO_NEXT*)
  hoare forward.

  pure_auto; int auto; change OS_TASK_DEL_HAS_NO_NEXT with 64; lia.

  (* opv <> Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT ) *) 

  hoare lifts (19::15::16::49::17::nil)%nat pre. 
  
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absimp_taskdel_prio_HAS_NO_NEXT_abt'; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule.

  unprotect Heqtcblst.

  (* (OSRdyTbl ′ [ptcb ′ → OSTCBY] &= ∼ ptcb ′ → OSTCBBitX;ₛ*)



  hoare forward.

  hoare_split_pure_all.
  assert (exists n, v'30 = Vptr n).
  clear -H9 H10.
  destruct H10; simpljoin; destruct H9; simpljoin; subst; simpl in *; tryfalse.
  eauto.
  eauto.
  clear H9 H10.

  simpljoin.
  rename v'10 into l1'.
  rename v'13 into l2'.

  lets backup: H30.
  unfold1 TCBList_P in H30.
  simpljoin.
  inverts H9.
  inverts H10.
  unfolds in H30.
  destruct x14; destruct p; destruct p.
  simpljoin.
  inverts H9; inverts H10.
  assert ( (p, t, m, s) = (i, x, x0, xxsus)).
  clear -H11 H23 H28.
  assert (get tcbmap (todelblock, Int.zero) =Some  (p, t, m, s)).
  unfold get,sig, join in *; simpl in *.
  unfold get,sig, join in *; simpl in *.
  go.
  unfold get,sig, join in *; simpl in *.
  unfold get,sig, join in *; simpl in *.
  rewrite H in H23.
  inverts H23.
  reflexivity.
  inverts H9.
  unfolds in H30.
  simpljoin.
  inverts H9; inverts H56; inverts H63; inverts H30.
  inverts H54; inverts H10; inverts H55.


  change ((OSRdyTbl ′ [ptcb ′ → OSTCBY] &= ∼ ptcb ′ → OSTCBBitX;ₛ
                                                                  If(OSRdyTbl ′ [ptcb ′ → OSTCBY] ==ₑ ′ 0)
                                                                  {OSRdyGrp ′ &= ∼ ptcb ′ → OSTCBBitY}  )) with (      inline_call inline_bittbl_clearbit ((OSRdyGrp ′):: (OSRdyTbl ′)::(ptcb ′ → OSTCBBitX)::(ptcb ′ → OSTCBBitY)::(ptcb ′ → OSTCBY)::nil)
                                                                                                                ).
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold GAarray.
  unfold AOSRdyGrp.
  unfold Agvarmapsto at 3.
  hoare unfold.




  Ltac inline_forward :=
    match goal with
      | |- {| _ , _ , _, _, _, _|} |- _ {{ _ }} inline_call ?inline_record _ {{ _ }} => eapply backward_rule2; [eapply (inl_proof inline_record)  | intro;intros;inline_pre_unfolder inline_record |idtac..]
    end.
  eapply seq_rule.

  inline_forward.
  2: {
   sep normal.
   sep eexists.

   sep cancel 2%nat 4%nat. 
   sep cancel 3%nat 4%nat. 
   sep cancel Aop.
   instantiate (2:=x11).

   sep pauto.
   go; math simpls.
   clear -H; mauto.
   intro.
   intros.
   lrv_solver.
   go.
   go.
   go. 
   }


  intro.
  intros.
  linv_solver.

(* pevent ′ =ₑ ptcb ′ .. OSTCBEventPtr;ₛ *)  
  inline_post_unfolder inline_bittbl_clearbit.

  hoare unfold.

  rename v'52 into v'48.
  rename v'43 into vv43.
  rename v'47 into v'43.  
  rename v'51 into v'47.
  rename v'42 into vv42.


  rename v'46 into v'42.
  rename v'41 into vv41.
  rename v'45 into v'41.
  rename v'40 into vv40.
  rename v'44 into v'40.
  rename v'39 into vv39.
  rename v'33 into v'39.
  rename v'38 into vv38.
  rename v'31 into v'38.
  rename v'37 into vv37.
  rename v'30 into v'37.
  rename v'36 into vv36.
  rename v'26 into v'36.
  rename v'25 into v'33.
  rename v'24 into v'31.
  rename v'20 into v'30.

  rename v'50 into v'46.
  rename v'49 into v'45.

  inverts H58.
  eapply backward_rule1.
  intro.
  intros.
  sep lift 2%nat in H58.
  sep lift 5%nat in H58.
  eapply GrefArray in H58.
  sep lift 3%nat in H58.
  sep lift 4%nat in H58.
  apply GrefPV in H58.
  eauto.
  hoare unfold.
  hoare forward.
  go.

  (* If (pevent ′ !=ₑ NULL)
{(pevent ′ .. OSEventTbl) [ptcb ′ .. OSTCBY] &=
 ∼ ptcb ′ .. OSTCBBitX;ₛ *)

 destruct H62.
 rename vv15 into v'20.

 {

 hoare lifts (1::18::19::51::20::nil)%nat pre. 
 eapply abscsq_rule.
 apply noabs_oslinv.
 eapply absimp_taskdel_rdy_succ'; eauto.
 can_change_aop_solver.
 eapply absinfer_eq.



   (* not in wait list *)
   rewrite H58 in H64.
   assert (Hxx: x23 = Vnull). {
      clear -H64.
      auto.
   }
   subst x21.
   rewrite (Hxx). 
   clear Hxx.

   (* If (pevent ′ !=ₑ NULL)
{(pevent ′ → OSEventTbl) [ptcb ′ → OSTCBY] &=
 ∼ ptcb ′ → OSTCBBitX;ₛ*)
   hoare forward.

   hoare_split_pure_all.
   false.
   clear -H58.
   int auto.
   instantiate (1:=Afalse).
   hoare forward.
   hoare unfold.
   clear H58.
   hoare forward.
   hoare forward.



   
(*
   protect Heqtcblst.
   eapply task_delete_ready with 
   (x23 := x23) (x20 := x20) (x19 := x19) (x18 := x18) (x17 := x17) ( i6 := i6) ( i5 := i5 ) ( i4 := i4) ( i3 := i3) ( i2 := i2) (i1 := i1 ) ( i0 := i0) ( l2 := l2)  (l1' := l1' ) (v'3 := v'5) (v'4 := v'6) (v'5 := v'7) (v'6 := v'8) (v'7 := v'9) (v'9 := v'11) (v'16 := v'18) (v'18 := v'20) (v'20 := v'22) (v'21 := v'23) (v'25 := v'34) (v'26 := v'35) (v'27 := v'32) (v'12 := v'14) (v'13 := v'15) (v'17 := v'19) (v'19 := v'21) (v'29 := v'31) (v'30 := v'33) (v'32 := v'37) (v'33 := v'38) (v'34 := v'39) (v'35 := v'40) (v'36 := v'41) (v'40 := v'45) (v'41 := v'46) (v'43 := v'48) (v'73 := v'3) (v'74 := v'4) (v'64 := v'24) (v'65 := v'25) (v'66 := v'26); 
    eauto.

*)


intros.

  rename v'12 into vv12.
  rename v'13 into vv13.
  rename v'27 into vv27.
  rename v'29 into vv29.
  rename v'36 into vvv36.

  rename v'3 into v'73.
  rename v'4 into v'74.

  rename v'5 into v'3.
  rename v'6 into v'4.
  rename v'7 into v'5.
  rename v'8 into v'6.
  rename v'9 into v'7.
  rename v'11 into v'9.
  rename v'19 into v'17.
  rename v'21 into v'19.
  rename v'18 into v'16.
  rename v'20 into v'18.
  rename v'22 into v'20.
  rename v'23 into v'21.

  (* rename v'24 into v'64. 
  rename v'25 into v'65.
  rename v'26 into v'66.*)

  rename v'34 into v'25.
  rename v'35 into v'26.

  rename v'14 into v'12.
  rename v'15 into v'13.

  rename v'31 into v'29.
  rename v'33 into v'30.

  rename v'32 into v'27.
  rename v'37 into v'32.
  rename v'38 into v'33.
  rename v'39 into v'34.
  rename v'40 into v'35.

  rename v'41 into v'36.
  rename v'45 into v'40.
  rename v'46 into v'41.
  rename v'48 into v'43.




  hoare unfold.

  rename H72 into HH72.
  rename H73 into H72.
  hoare forward.
  math simpls.

  (* ... *)
  Set Printing Depth 999.
  hoare forward.



    destruct l2'.

    (*l2' = nil*)
    unfold1 dllseg.
    hoare unfold.


    inverts H73.


  (*l2' = v:: l2'*)
    unfold1 dllseg.
    unfold node.
    hoare unfold.


  
    
  destruct l1'.

    (*l1' = nil*)  
  hoare_assert_pure (v'13 = Vnull). 
  unfold1 dllseg in H73.
  sep normal in H73.
  sep destruct H73.
  sep split in H73.
  rewrite H75; reflexivity.

  rename v'11 into v'15.
  rename v'10 into v'14.


  
  (* v'13 is null, deleting first tcb node *)
  {
    hoare_split_pure_all.
    subst v'13.
    hoare forward.
    go.

    Focus 2.
    hoare_split_pure_all; false.
    clear -H73; simpljoin.
    destruct H73; tryfalse.

    hoare unfold.
    hoare forward.
  
    go.
    hoare forward.
    hoare forward.

    hoare forward.

    Focus 2.
    hoare_split_pure_all.
    false.
    clear -H73; destruct H73; tryfalse.

    hoare unfold.

    hoare  remember (1::2::3::4::5::6::7::8::9::10::11::12::13::14::15::16::17::18::19::20::21::22::23::24::25::26::27::28::29::30::nil)%nat pre.

    rename H89 into HH89.
    unfold AOSTCBFreeList in HeqH89.
    hoare unfold.

    hoare forward.

    eapply isptr_is_definitely_ptr.
    eapply sll_head_isptr.
    instantiate (5:=s).
    sep cancel sll.
    go.


    hoare forward.



    clear H73 H74 H75.
    assert (todelblock = cur_tcb_blk \/ todelblock <> cur_tcb_blk) by tauto. 
    destruct H73.

   (* todelblock = cur_tcb_blk *) 

    {

      subst todelblock.

      rewrite H23 in kitty.

      

      Set Printing Depth 999.
      eapply backward_rule1.
      instantiate (1:= (
         <|| spec_code_cons (sdel (Vint32 v'43 :: v'74 :: nil)) v'73 ||>  **
         HTCBList tcbmap **
                  HCurTCB (cur_tcb_blk, Int.zero) **
                  OS [ empisr, v'54, false, nil, (true::nil)] **
  A_dom_lenv
    ((prio, char_t) :: (pevent, OS_EVENT ∗) :: (ptcb, OS_TCB ∗) :: (self, char_t) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
  GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
  LV ptcb @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
  Astruct (cur_tcb_blk, Int.zero) OS_TCB_flag
    (v'20
     :: Vnull
        :: Vnull
           :: x0
              :: V$ 0
                 :: V$ OS_STAT_RDY
                    :: Vint32 v'43
                       :: Vint32 (v'43&ᵢ$ 7)
                          :: Vint32 (v'43 >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil) **
  GV OSTCBList @ OS_TCB ∗ |-> Vptr (v'15, Int.zero) **
  LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (v'15, Int.zero) **
  Astruct (v'15, Int.zero) OS_TCB_flag
    (v'14
     :: Vnull
        :: x25 :: x24 :: Vint32 i12 :: Vint32 i11 :: Vint32 i10 :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil) **
  dllseg v'14 (Vptr (v'15, Int.zero)) v'12 Vnull l2' OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
    (fun vl : vallist => nth_val 0 vl) **
  GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) (update_nth_val (Z.to_nat (Int.unsigned v'43)) priotbl Vnull) **
  PV vhold_addr @ char_t |-> v'8 **
  HECBList v'16 **
  (* HTCBList tcbmap ** *)
  HTime v'18 **
  (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
  LV pevent @ OS_EVENT ∗ |-> Vnull **
  GV OSRdyGrp @ char_t |-> Vint32 v'40 **
  GAarray OSRdyTbl (Tarray char_t ∘ OS_RDY_TBL_SIZE)
    (update_nth_val (Z.to_nat (Int.unsigned (v'43 >>ᵢ $ 3))) v'30
       (val_inj (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'43&ᵢ$ 7))))))) **
  dllseg v'9 Vnull Vnull (Vptr (cur_tcb_blk, Int.zero)) nil OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
    (fun vl : vallist => nth_val 0 vl) **
  GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
  (* Aisr empisr **
  Aie false **
  Ais nil **
  Acs (true :: nil) **
  Aier v'54 ** *)
  AECBList v'7 v'6 v'16 tcbmap **
  tcbdllflag v'9
  (nil ++
   (Vptr (v'15, Int.zero)
    :: Vnull
       :: Vnull
          :: x0
             :: Vint32 i13
                :: V$ OS_STAT_RDY
                   :: Vint32 v'43
                      :: Vint32 (v'43&ᵢ$ 7)
                         :: Vint32 (v'43 >>ᵢ $ 3)
                            :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                               :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
     :: (v'14
         :: Vptr (cur_tcb_blk, Int.zero)
            :: x25
               :: x24 :: Vint32 i12 :: Vint32 i11 :: Vint32 i10 :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil)
        :: l2') ** 
        G& OSPlaceHolder @ char_t == vhold_addr ** HPriotls v'53 ** A_isr_is_prop **
        p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
         LV self @ char_t |-> (V$ 0) **
         AOSEventFreeList v'3 vv26 **
         AOSQFreeList v'4 **
         AOSQFreeBlk v'5 **
         Hebls vv41 **
         AErrblkList vv41 **
         Hpbls vv40 **
         APosblkList vv40 **
         HEvAtomHeap vv31 **
         AEvAtomHeap vv31 **
         HEvStructHeap vv32 **
         AEvStructHeap vv32 **
         HEvArrayHeap vv33 **
         AEvArrayHeap vv33 **
         HSEMInfo vv37 **
         ASemEIBs vv34 vv22 vv37 v'16 vhold_addr **
         HMuxInfo vv38 **
         AMuxEIBs vv35 vv23 vv38 v'16 vhold_addr **
         HQAttr vv39 **
         AMqEIBs vv36 vv24 vv39 v'16 vhold_addr **
         HEvLoc vv42 **
         HEvPtr vv43 **
         tcbllsegevaux v'9
         (nil ++
         (Vptr (v'15, Int.zero)
          :: Vnull
             :: Vnull
                :: x0
                   :: Vint32 i13
                      :: V$ OS_STAT_RDY
                         :: Vint32 v'43
                            :: Vint32 (v'43&ᵢ$ 7)
                               :: Vint32 (v'43 >>ᵢ $ 3)
                                  :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                     :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
            :: (v'14
                :: Vptr (cur_tcb_blk, Int.zero)
                   :: x25
                      :: x24
                         :: Vint32 i12
                            :: Vint32 i11 :: Vint32 i10 :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil) :: l2')
           vv42 vv43 **
         AOSMapTbl **
         AOSUnMapTbl **
         sll v'20 v'21 OS_TCB_flag (fun vl : vallist => nth_val 0 vl) **
         sllfreeflag v'20 v'21 **
         AOSTime (Vint32 v'18) **
         AGVars **
         APthreadAttr vpthattr **
         IntInv **
         TmrInv ** CoreCommuInv v'16 ** PartitionInv ** CapabilityInv vcspace ** LV prio @ char_t |-> Vint32 v'43 
   )).
      clear.
      intro; intros.
      (* sep_lifts_trms (Aisr, Ais).
      eapply elim_a_isr_is_prop. *)
      sep_cancel_iers.
      sep cancel tcbdllflag.
      sep cancel tcbllsegevaux.

      sep pauto.



      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (cur_tcb_blk, Int.zero) (v'43, x, x0, xxsus) mmm tcbmap).
      apply tcb_get_join.
      unfold get, sig, join in *; simpl in *.
      unfold get, sig, join in *; simpl in *.
      go.

      destruct H73 as (tcbmap_left & tcbmapleft_join_hyp).

      eapply backward_rule1.
      introv Hsat.

      sep_lifts_trms_in Hsat (Aisr, Ais, A_isr_is_prop).      
      eapply elim_a_isr_is_prop in Hsat.
      sep lifts (3::4::5::1::6::7::2::8::nil)%nat in Hsat.     
      exact Hsat. 

      eapply seq_rule.
      eapply  derive_delself_rule'.

        
      apply goodlinv.
      go.
      unfold AEventData.

      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.

      exact tcbmapleft_join_hyp.

      intro; intros.
      split.
      sep_get_rv.
      unfold p_local in H73.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.



      rewrite app_nil_l.
      
      hoare  remember (1::2::3::4::5::6::7::8::9::10::11::12::13::14::15::16::17::18::19::20::21::22::23::24::25::26::27::28::29::30::nil)%nat pre.

      unfold1 tcbdllflag.
      unfold1 dllsegflag.   

      unfold1 tcbllsegevaux in HeqH73.
      unfold1 llsegevaux in HeqH73.
      hoare unfold.
      
      rename v'22 into v'38.
      rename v'10 into v'13.

      hoare lift 4%nat pre.
      unfold p_local at 2.
      unfold OSLInv at 3.
      unfold LINV.
      unfold1 dllseg.
      hoare unfold.

      rename v'10 into vv10.
      rename v'11 into vv11.
      rename v'14 into vv14.
      rename v'22 into v22.
      rename v'31 into v31.
      rename v'37 into v37.
      rename v'39 into v39.
      rename v'42 into v42.
      rename v'44 into vv44.
      rename v'45 into vv45.
      rename v'48 into vv48.
      rename v'49 into vv49.
      rename v'50 into vv50.
      rename v'51 into vv51.
      rename v'52 into vv52.
      rename v'55 into vv55.
      rename v'47 into v'38.

      rename H94 into H73.
      rename H89 into HH89.
      rename H97 into H89.
      rename H98 into H90.

      rename H75 into HH75.
      rename H93 into HH93.
      rename H92 into HH92.
      rename H99 into HH99.
      rename H100 into HH100.
      rename H101 into HH101.
      rename H102 into HH102.


      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)


      sep combine ( get_off_addr (cur_tcb_blk, Int.zero) (flag_off)) in H74.
      eauto.

      hoare_lifts_trms_pre Aop.
      eapply seq_rule.
      eapply assign_rule'.
      Focus 2.

      intro; intros.
      split.
      eapply field_asrt_impl.
      Focus 3.
      sep cancel 20%nat 1%nat.
      eauto.
      reflexivity.
      reflexivity.
      sep get rv.
      eapply eq_int; auto.

      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.

      sep cancel 4%nat 2%nat.
      sep cancel 4%nat 2%nat.
      sep cancel 4%nat 2%nat.
      sep cancel 4%nat 2%nat.  

      sep cancel 67%nat 1%nat.
      simpl; auto.

      splits; eauto.
      unfolds; auto.
            
      eapply backward_rule1.

      intro; intros.



      sep_lifts_trms_in H74 (Aisr, Ais, Aier).
      eapply add_aemp_isr_is_prop in H74.
           
      sep_lifts_trms_in H74 (Aisr, Ais).
      eapply add_a_isr_is_prop in H74.
      
      sep_lifts_trms_in H74 Aop.
      eauto.

      eapply seq_rule.
      eapply excrit1_rule'_ISnil_ISRemp''.

      intro.
      intros.

      sep_cancel_iers.
      sep cancel aemp_isr_is.
      unfold p_local, OSLInv.
      unfold LINV.
      sep pauto.
      sep cancel 2%nat 1%nat.

      sep cancel 6%nat 1%nat. 
      sep cancel 6%nat 1%nat. 
      sep cancel 6%nat 1%nat. 
      sep cancel 6%nat 1%nat. 

      sep cancel CurTid.
      unfold OSInv.
      unfold EvtInv.
      sep normal.
      sep eexists.
      sep pauto.

      sep cancel APthreadAttr.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.

      sep cancel ASemEIBs.
      sep cancel AMuxEIBs.
      sep cancel AMqEIBs.
      sep cancel CapabilityInv.

      instantiate (21 := v'7).
      instantiate (20 := v'6).      
      unfold AECBList.
      unfold AECBList in H74.
      sep pauto.
      unfold AOSTCBPrioTbl.
      sep pauto.

      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      sep_lifts_trms AOSTCBList'.
      unfold AOSTCBList'.
      eapply intro_or_r.
      sep pauto.
      unfold tcblist.


      instantiate (5 := nil).
      instantiate (3 := l2'). 

      instantiate ( 4 := (v'38
      :: Vnull
      :: x25
      :: x24
      :: Vint32 i12
      :: Vint32 i11
      :: Vint32 i10
      :: Vint32 i9
      :: Vint32 i8
      :: Vint32 i7 :: Vint32 i :: nil)).

     
(* ** ac:       Print  TCB_Not_In . *)
      unfold TCB_Not_In.
      sep pauto.

      eapply tcbdllseg_compose.
      unfold tcbdllseg.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 12%nat 1%nat.
      sep cancel 12%nat 1%nat.
      unfold1 tcbdllflag.
      unfold1 tcbllsegevaux.
      rewrite app_nil_l.
      unfold1 dllsegflag.
      unfold1 llsegevaux .

      sep pauto.
      sep cancel dllsegflag.
      sep cancel llsegevaux.
      sep cancel 2%nat 1%nat.
      (* freelist *)
      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_r. 
      unfold TCBFree_Eq.
      sep pauto.
      sep cancel sll.
      sep cancel sllfreeflag.
      unfold evaux_node in H74.
      sep pauto.
      go.
      eapply isptr_is_definitely_ptr.
      eapply sll_head_isptr.
      instantiate (5:=s).
      sep cancel sll.
      go.
      unfolds.
      {
        do 6 eexists.
        splits.
        go.
        go.
        go.
        go.
        go.
        go.
        go.
        splits.
        go.
        go.
        go.
        go.
        left; auto.
        repeat tri_exists_and_solver1.
        go.

       assert( $ OS_STAT_RDY = $ OS_STAT_RDY \/ $ OS_STAT_RDY = $ OS_STAT_SUSPEND).
       {
         auto.
       }
       lets bb: H64 H92.
       subst.
       reflexivity.
      }
      eexists; go.
      {
        unfolds in H6.
        simpljoin.
        clear -tcbmapleft_join_hyp H93.
        unfolds.
        unfolds in tcbmapleft_join_hyp.
        intro.
        simpljoin.

        unfolds in H93.
        assert (x1 <> (cur_tcb_blk, Int.zero)).
        intro.
        subst.
(* ** ac:         SearchAbout join. *)
(* ** ac:         SearchAbout TcbMod.join. *)
        eapply TcbMod.map_join_get_some .
        
        auto.
        eauto.
        2: exact H.
        instantiate (1:=(v'43, x, x0, xxsus)).
        unfold get in *; simpl in *.
        unfold sig in *; simpl in *.
        eapply TcbMod.get_a_sig_a.
        go.
        unfold join, sig, get in *; simpl in *.
        assert (TcbMod.get tcbmap x1 =Some (v'43, x2, x3, x4) ).
        go.
        assert (TcbMod.get tcbmap (cur_tcb_blk, Int.zero) =Some (v'43, x, x0, xxsus) ).
        go.
        lets bb: H93 H0 H1 H2.
        apply bb.
        reflexivity.

      }
      
      go.
      go.
      eauto.
      join auto.
      intro; tryfalse.
      go.
      go.
      {
        split.
        rewrite ptr_in_tcblist_app.
        2: simpl; auto.
        intro.
        destruct H92.
        simpl in H92.
        exact H92.
        simpl (val_inj (get_last_tcb_ptr nil (Vptr (v'15, Int.zero)))) in H92.
        gen H92.
        eapply distinct_is_unique_second.
        3: eapply  TCBLP_imply_dictinct_list .
        2:instantiate ( 1 := (Vptr (v'15, Int.zero)
      :: Vnull
         :: x23
            :: x0
               :: Vint32 i13
                  :: V$ OS_STAT_RDY
                     :: Vint32 v'43
                        :: Vint32 (v'43&ᵢ$ 7)
                           :: Vint32 (v'43 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                              :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)).
        2: go.
        2:instantiate (3 :=  nil).
        simpl; auto.
        rewrite app_nil_l.

         exact backup.
         simpl.
         auto.
         eauto.
      }
       (* from tcblist_p, get they are all different? *)
      {
        rewrite app_nil_l.
        rewrite app_nil_l in H25.
(* ** ac:         Print  R_PrioTbl_P . *)
        

        eapply tcblist_p_hold_for_del_a_tcb_at_head.
        lia.
        2:go.
        2:go.
        3: exact H25.
        2: exact tcbmapleft_join_hyp.
        unfolds in H6.
        simpljoin; assumption.
      }
      split.
      assumption.
      eapply (H68 _ H55).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.

        
(* OSTimeDlyPure.update_rtbl_tcblist_hold: *)

        
        
      {
        eapply  r_priotbl_p_hold_for_del_a_tcb.
        lia.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .

      }
       (* r_priotbl_p hold for deleting a tcb *)
      
{
  eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
  lia.
  rewrite Int.repr_unsigned.
  reflexivity.

  rewrite Int.repr_unsigned.
  reflexivity.

  2: assumption.
  unfold nat_of_Z.
  apply nv'2nv.
  
  assumption.
  intro; tryfalse.
  
      }

       (* rl_rtbl_ptbl_p hold for deleting a tcb *)

      split.
      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.
(* ** ac:       Check  ECBLP_hold4del_a_tcb. *)
(* ** ac:       Print ECBList_P. *)
(* ** ac:       Print isWait4Ecb. *)
      Lemma ECBLP_hold4del_a_tcb_rdy:
        forall lowl head tail highl ecbmap tcbmap v'43 x x0 tcbmap_left tcb_block,
          ECBList_P head tail lowl highl ecbmap tcbmap ->
          TcbMod.joinsig (tcb_block, Int.zero) (v'43, x, x0) tcbmap_left tcbmap ->
          (forall ecbid, ~ exists bb cc, x = wait bb cc /\ isWait4Ecb bb ecbid ) ->
          ECBList_P head tail lowl highl ecbmap tcbmap_left .
      Proof.
        induction lowl.
        simpl.
        intros.
        auto.
        intros.
        unfold1 ECBList_P in *.
        simpljoin.
        destruct highl; tryfalse.
        destruct a.
        simpljoin.
        repeat tri_exists_and_solver1.
        rewrite R_ECB_ETbl_P_is_poi.
        rewrite R_ECB_ETbl_P_is_poi in H2.
        unfold poi_RLEHT in *.
        simpljoin.
        splits; auto.

        unfold poi_RHT_LE in *.
        intros.
        assert (get tcbmap tid0 = Some (prio, wait hwb n, m)).
        unfold get in *; simpl in *.
        go.
        eapply H2; eauto.
        
        unfold poi_RLE_HT in *.
        intros.

        lets bb: H6 H8.
        simpljoin.

        eapply join_get_or in H9.
        2: auto.
        2: exact H0.
        destruct H9.
        Focus 2.
        repeat tri_exists_and_solver1.
        false.
        apply (H1 x1).
        assert ( x5 = (tcb_block, Int.zero) \/ x5 <> (tcb_block, Int.zero)).
        tauto.
        destruct H12; subst;
        unfold get in *; simpl in *.
        rewrite TcbMod.get_a_sig_a in H9.
        inverts H9.
        repeat tri_exists_and_solver1.
        go.


        rewrite TcbMod.get_a_sig_a' in H9.
        inverts H9.
        go.
      Qed.

      assert (forall ecbid, ~ exists bb cc, x = wait bb cc /\ isWait4Ecb bb ecbid ). 
      intros.
      intro.
      simpljoin.
      Lemma lowready_not_wait4ecb:
        forall v'15 x0 i13  v'30 v'43 x11 x12 ecbid, 
        R_TCB_Status_P
          (Vptr (v'15, Int.zero)
           :: Vnull
              :: Vnull
                 :: x0
                    :: Vint32 i13
                       :: V$ OS_STAT_RDY
                          :: Vint32 v'43
                             :: Vint32 (v'43&ᵢ$ 7)
                                :: Vint32 (v'43 >>ᵢ $ 3)
                                   :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                      :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
          v'30 (v'43, wait x11 x12, x0) ->
        ~ isWait4Ecb x11 ecbid .
      Proof.
        intros.
        unfolds in H.
        simpljoin.
        clear -H2.
        unfolds in H2.
        simpljoin.
        unfold isWait4Ecb.
        intro.
        destruct H4; subst.
        {
        clear -H0.
        unfolds in H0.
        lets bb: H0 (eq_refl  (v'43, wait (os_stat_sem ecbid) x12, x0) ).
        simpljoin;  tryfalse.
        }
       destruct H4; subst.
        {
        clear -H1.
        unfolds in H1.
        lets bb: H1 (eq_refl  (v'43, wait (os_stat_q ecbid) x12, x0) ).
        simpljoin;  tryfalse.
        }
       
        destruct H4; subst.
        {
        clear -H2.
        unfolds in H2.
        lets bb: H2 (eq_refl  (v'43, wait (os_stat_mbox ecbid) x12, x0) ).
        simpljoin;  tryfalse.
        }
       
        {
        clear -H3.
        unfolds in H3.
        lets bb: H3 (eq_refl  (v'43, wait (os_stat_mutexsem ecbid) x12, x0) ).
        simpljoin;  tryfalse.
        }
      Qed.
      gen H93.
      eapply lowready_not_wait4ecb.
      lets bb: H64 (eq_refl ($ OS_STAT_RDY)).
      subst x23.
      exact H53.

      eapply ECBLP_hold4del_a_tcb_rdy; eauto.
      
          
(* ** ac:       Check poi_RHTEP_hold_for_del_a_tcb. *)
      assert (forall ecbid, ~ exists bb cc, x = wait bb cc /\ isWait4Ecb bb ecbid ). 
      intros.
      intro.
      simpljoin.
      gen H92.
      eapply lowready_not_wait4ecb.
      lets bb: H64 (eq_refl ($ OS_STAT_RDY)).
      subst x23.
      exact H53.

      rewrite <- poi_is_rtep.
      rewrite <- poi_is_rtep in H2.
      Lemma poi_RH_T_E_P_hold_for_tcbdel_rdy:
        forall todel v'43 x x0 tcbmap_left tcbmap v'16,
          ~ is_some_mutex_owner todel v'16  ->
          TcbMod.joinsig todel (v'43, x, x0) tcbmap_left tcbmap ->
          (forall ecbid, ~ exists bb cc, x = wait bb cc /\ isWait4Ecb bb ecbid ) ->
          poi_RH_T_E_P v'16 tcbmap ->
          poi_RH_T_E_P v'16 tcbmap_left.
      Proof.
        intros.
        unfold poi_RH_T_E_P in *; simpljoin.
        splits; auto.
        unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
        intros.
        lets bb: H2 H5.
        simpljoin.
        eapply join_get_or in H6.
        2:auto.
        2: eauto.
        destruct H6; eauto.
        assert (todel = tid \/ todel <> tid).
        tauto.
        unfold get in *; simpl in *.
        destruct H7; subst.
        rewrite TcbMod.get_a_sig_a in H6.
        inverts H6.
        false.
        apply H.
        unfolds.
        eauto.
        go.

        rewrite TcbMod.get_a_sig_a' in H6.
        inverts H6.
        go.

        unfold poi_R_TE in *.
        intros.
        assert (get tcbmap tid = Some (p, wait waitstat t, msg)).
        unfold get in *; simpl in *.
        go.
        lets bb: H3 H5 H7.
        auto.

        unfold poi_R_ET in *.
        intros.
        lets bb: H4 H5.
        simpljoin.
        
        eapply join_get_or in H6; eauto.
        destruct H6; eauto.
        assert (todel = tid \/ todel <> tid).
        tauto.
        unfold get in *; simpl in *.
        destruct H8; subst.
        rewrite TcbMod.get_a_sig_a in H6.
        inverts H6.
(* ** ac:         SearchAbout hle2wait. *)
        
        false.
        apply (H1 eid).
        repeat tri_exists_and_solver1.
(* ** ac:         SearchAbout hle2wait. *)
        Lemma isw4e_hle2w_same':
          forall (a : edata) (b : ecbid),
             isWait4Ecb (hle2wait a b) b .
        Proof.
          intros.
          unfold isWait4Ecb; unfold hle2wait.
          destruct a; auto.
        Qed.

        apply isw4e_hle2w_same'.
        go.

        rewrite TcbMod.get_a_sig_a' in H6.
        inverts H6.
        go.
        
      Qed.

      eapply poi_RH_T_E_P_hold_for_tcbdel_rdy; eauto.

      splits; go.
      unfolds; auto.
      go.
      hoare forward.


      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.

      hoare unfold.

      inverts H74.
      assert (Hopv: v'74 = Vint32 (Int.repr OS_NO_ERR) \/ v'74 <>Vint32 (Int.repr OS_NO_ERR)) by tauto.
      destruct Hopv.
    
      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskdel_succ.
      go.
      go.


      hoare forward.
      splits.
      eauto.
      eauto.
      
      change OS_NO_ERR with 0.
      rewrite Int.unsigned_repr. lia.
      rewrite max_unsigned_val. lia.

      change OS_NO_ERR with 0.
      rewrite Int.unsigned_repr.
      change Byte.max_unsigned with 255. lia.
      rewrite max_unsigned_val. lia.

      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskdel_succ_abt.
      can_change_aop_solver.
      auto.
    
      eapply absabort_rule.
    
    }

    (* delete some tcb other than current, at head *)
    {
      eapply backward_rule1.
      Set Printing Depth 999.
      intro; intros.
      Set Printing Depth 999.
(* ** ac:       Show. *)
      instantiate ( 1 := (
        <|| spec_code_cons (sdel (Vint32 v'43 :: v'74 :: nil)) v'73 ||>  **
                              HTCBList tcbmap **
                              HCurTCB (cur_tcb_blk, Int.zero) **
                              OS [ empisr, false, nil, (true::nil)] **
 (* <|| sdel (Vint32 v'43 :: nil);; isched;; END Some (V$ NO_ERR) ||>  ** *)
           A_dom_lenv
             ((prio, Int8u)
              :: (pevent, OS_EVENT ∗)
                 :: (ptcb, OS_TCB ∗)
                    :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
           GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
           LV ptcb @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
           Astruct (todelblock, Int.zero) OS_TCB_flag
             (v'20
              :: Vnull
                 :: Vnull
                    :: x0
                       :: V$ 0
                          :: V$ OS_STAT_RDY
                             :: Vint32 v'43
                                :: Vint32 (v'43&ᵢ$ 7)
                                   :: Vint32 (v'43 >>ᵢ $ 3)
                                      :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                         :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3))
                                            :: nil) **
           GV OSTCBList @ OS_TCB ∗ |-> Vptr (v'15, Int.zero) **
           LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (v'15, Int.zero) **
           Astruct (v'15, Int.zero) OS_TCB_flag
             (v'14
              :: Vnull
                 :: x25
                    :: x24
                       :: Vint32 i12
                          :: Vint32 i11
                             :: Vint32 i10
                                :: Vint32 i9
                                   :: Vint32 i8
                                      :: Vint32 i7 :: Vint32 i :: nil) **
           dllseg v'14 (Vptr (v'15, Int.zero)) v'12 Vnull l2' OS_TCB_flag
             (fun vl : vallist => nth_val 1 vl)
             (fun vl : vallist => nth_val 0 vl) **
           GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
             (update_nth_val (Z.to_nat (Int.unsigned v'43)) priotbl Vnull) **
           PV vhold @ Int8u |-> v'8 **
           HECBList v'16 **
           (* HTCBList tcbmap ** *)
           HTime v'18 **
           (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
           LV pevent @ OS_EVENT ∗ |-> Vnull **
           GV OSRdyGrp @ Int8u |-> Vint32 v'40 **
           GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
             (update_nth_val (Z.to_nat (Int.unsigned (v'43 >>ᵢ $ 3))) v'30
                (val_inj
                   (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'43&ᵢ$ 7))))))) **
           dllseg v'9 Vnull Vnull (Vptr (todelblock, Int.zero)) nil
             OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
             (fun vl : vallist => nth_val 0 vl) **
           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
           (* Aie false ** *)
           (* Ais nil ** *)
           (* Acs (true :: nil) ** *)
           (* Aisr empisr ** *)
           AECBList v'7 v'6 v'16 tcbmap **
           tcbdllflag v'9
             (nil ++
              (Vptr (v'15, Int.zero)
               :: Vnull
                  :: Vnull
                     :: x0
                        :: Vint32 i13
                           :: V$ OS_STAT_RDY
                              :: Vint32 v'43
                                 :: Vint32 (v'43&ᵢ$ 7)
                                    :: Vint32 (v'43 >>ᵢ $ 3)
                                       :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                          :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3))
                                             :: nil)
              :: (v'14
                  :: Vptr (todelblock, Int.zero)
                     :: x25
                        :: x24
                           :: Vint32 i12
                              :: Vint32 i11
                                 :: Vint32 i10
                                    :: Vint32 i9
                                       :: Vint32 i8
                                          :: Vint32 i7 :: Vint32 i :: nil)
                 :: l2') **
           G& OSPlaceHolder @ Int8u == vhold **
           (* A_isr_is_prop ** *)
           p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
           LV self @ Int8u |-> (V$ 0) **
           AOSEventFreeList v'3 **
           AOSQFreeList v'4 **
           AOSQFreeBlk v'5 **
           AOSMapTbl **
           AOSUnMapTbl **
           AOSIntNesting **
           sll v'20 v'21 OS_TCB_flag (fun vl : vallist => nth_val 0 vl) **
           sllfreeflag v'20 v'21 **
           AOSTime (Vint32 v'18) **
           AGVars ** APthreadAttr v'64 v'65 v'66 ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'43)).
      sep lifts (4:: 6::nil)%nat. 
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.
      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (todelblock, Int.zero) (v'43, x, x0) mmm tcbmap).
      apply tcb_get_join.
      unfold get, sig, join in H11; simpl in H11.
      unfold get, sig, join in H11, H20; simpl in H11, H20.
      go.

      destruct H74 as (tcbmap_left & tcbmapleft_join_hyp).
      rename H73 into not_cur_hyp.


      eapply seq_rule.
      eapply  derive_delother_rule.
      apply goodlinv.
       (* goodlinv *)
      go.
      (* unfold AEventData. *)
      (* destruct x22; go. *)
      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.
      exact tcbmapleft_join_hyp.
      clear -H3.
      unfolds in H3.
      unfolds.
      simpljoin; eauto.

      clear -not_cur_hyp.
      intro H; inverts H; apply not_cur_hyp; reflexivity.

      
      intro; intros.
      split.
      sep_get_rv.
      unfold p_local in H73.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.

      rewrite app_nil_l.
      unfold1 tcbdllflag.
      unfold1 dllsegflag.
      hoare unfold.
      rename v'23 into v'39.
      rename v'10 into v'13.
      hoare lift 4%nat pre.
      unfold OSLInv at 3.
      unfold LINV.
      unfold1 dllseg.
      hoare unfold.
      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)
      sep combine ( get_off_addr (todelblock, Int.zero) ($ 24)  ) in H73.
      eauto.

      (* hoare lift 2%nat pre. *)
      hoare lift 4%nat pre.
      eapply seq_rule.
      eapply assign_rule'.
      Focus 2.

      intro; intros.
      split.
      eapply field_asrt_impl.
      Focus 3.
      sep cancel 12%nat 1%nat.
      eauto.
      reflexivity.
      reflexivity.
      sep get rv.
      eapply eq_int; auto.

      linv_solver.


      eapply backward_rule1.
      

      intro; intros.
      sep lifts (7::9::nil)%nat in H73.
      eapply add_a_isr_is_prop in H73.
      eauto.
      
      hoare lift 4%nat pre.
      eapply seq_rule.


      eapply excrit1_rule'_ISnil_ISRemp''.

      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel p_local.
      eapply poi_OSINV_imply_OSInv.

      unfold poi_OSINV.

      sep pauto.
      sep cancel APthreadAttr.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
      instantiate (14 := v'7).
      instantiate (13 := v'6).

      unfold AECBList.

      unfold AECBList in H73.
      sep pauto.


      unfold AOSTCBPrioTbl.
      sep pauto.
      idtac.
      idtac.
      sep cancel 12%nat 1%nat.
      sep cancel 16%nat 1%nat.
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold poi_AOSTCBList.
      
      sep pauto.
      instantiate (4 := (
                          (v'39
                             :: Vnull
                             :: x25
                             :: x24
                             :: Vint32 i12
                             :: Vint32 i11
                             :: Vint32 i10
                             :: Vint32 i9
                             :: Vint32 i8
                             :: Vint32 i7 :: Vint32 i :: nil)
                            :: l2')).

      unfold tcbdllseg.
      unfold tcbdllflag.
      unfold1 dllsegflag.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 2%nat 1%nat.
      sep cancel dllsegflag.
      sep cancel dllseg.
      sep cancel 7%nat 1%nat.


      (* freelist *)
      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_l. 
      unfold TCBFree_Not_Eq.
      sep pauto.
      instantiate (2 := (
                           (v'20
                              :: Vnull
                              :: Vnull
                              :: x0
                              :: V$ 0
                              :: V$ OS_STAT_RDY
                              :: Vint32 v'43
                              :: Vint32 (v'43&ᵢ$ 7)
                              :: Vint32 (v'43 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                              :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3))
                              :: nil) ::v'21
                                      
                         )).
      unfold sll.
      unfold sllfreeflag.
      unfold1 sllseg.
      unfold1 sllsegfreeflag.
      unfold node.
      unfold sll in H73.
      unfold sllfreeflag in H73.
      sep pauto.
      sep cancel sllseg.
      sep cancel sllsegfreeflag.
      
      sep cancel 1%nat 1%nat.
      sep cancel Astruct.
      eauto.
      go.
      go.
      apply isptr_is_definitely_ptr.
      eapply sllseg_head_isptr.
      instantiate (5:=s).
      sep cancel sllseg.
      eauto.

      go.
      intro; tryfalse.
      go.
      go.
      go.
      intro; tryfalse.
      {

        rewrite app_nil_l in H25.
        eapply tcblist_p_hold_for_del_a_tcb_at_head.
        lia.
        2:go.
        2:go.
        3: exact H25.
        2: exact tcbmapleft_join_hyp.
        unfolds in H6.
        simpljoin; assumption.
      }
       (* tcblist_p hold for deleting a tcb *)
      {

        clear -H24 not_cur_hyp .

        eapply ptr_in_tcbdllseg_change_head.
        Focus 2.
                eapply ptr_in_tcbdllseg_not_head.
        rewrite app_nil_l in H24.
        2: eauto.
        simpl; auto.
        intro; tryfalse.
        unfold V_OSTCBNext.
        reflexivity.
      }

      
       (* from tcblist_p, get they are all different? *)
      split.
      assumption.
      eapply (H68 _ H55).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.

      {
        eapply r_priotbl_p_hold_for_del_a_tcb.
        
        lia.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .
      }
       (* r_priotbl_p hold for deleting a tcb *)
      {
        eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
        lia.
        rewrite Int.repr_unsigned.
        reflexivity.

        rewrite Int.repr_unsigned.
        reflexivity.

        2: assumption.
        unfold nat_of_Z.
        apply nv'2nv.
        
        assumption.
        intro; tryfalse.
      }
       (* rl_rtbl_ptbl_p hold for deleting a tcb *)

      split.

      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.

      {
      assert (forall ecbid, ~ exists bb cc, x = wait bb cc /\ isWait4Ecb bb ecbid ). 
      intros.
      intro.
      simpljoin.
      
      gen H91.
      eapply lowready_not_wait4ecb.
      lets bb: H64 (eq_refl ($ OS_STAT_RDY)).
      subst x23.
      exact H53.

      eapply ECBLP_hold4del_a_tcb_rdy; eauto.
      }
       (* from H101 : RL_Tbl_Grp_P
           (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
              (val_inj
                 (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
           (Vint32 v'53), ECBList_P holds for deleting a tcb *)
      {
        rewrite <- poi_is_rtep.
        rewrite <- poi_is_rtep in H2.

        eapply poi_RH_T_E_P_hold_for_tcbdel_rdy; eauto.
      intros.
      intro.
      simpljoin.
      
      gen H90.
      eapply lowready_not_wait4ecb.
      lets bb: H64 (eq_refl ($ OS_STAT_RDY)).
      subst x23.
      exact H53.
      }
       (* change to poi,
from some_pure_hyp : forall (eid : tidspec.A) (pr : int32) 
                    (tid0 : tid) (opr : int32) (wls : waitset),
                  EcbMod.get ecbmap eid =
                  Some (absmutexsem pr (Some (tid0, opr)), wls) ->
                  tid0 <> (cur_tcb_blk, Int.zero)
get rh_te_p hold for deleting a tcb
              *)
      go.
      hoare forward.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.

      hoare unfold.

      inverts H73.
      assert (Hopv: v'74 = Vint32 (Int.repr OS_NO_ERR) \/ v'74 <>Vint32 (Int.repr OS_NO_ERR)) by tauto.
      destruct Hopv.
    
      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskdel_succ.
      go.
      go.


      hoare forward.
      splits.
      eauto.
      eauto.
      
      change OS_NO_ERR with 0.
      rewrite Int.unsigned_repr. lia.
      rewrite max_unsigned_val. lia.

      change OS_NO_ERR with 0.
      rewrite Int.unsigned_repr.
      change Byte.max_unsigned with 255. lia.
      rewrite max_unsigned_val. lia.

      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskdel_succ_abt.
      can_change_aop_solver.
      auto.
    
      eapply absabort_rule.
      
    }
    (* delete some tcb in the middle of the tcblist *)
  }
  rename v'11 into v'15.
  rename v'10 into v'14.
  {
    destruct H42.
    hoare_assert_pure False.
    (* hw **)
    subst v'13.

    eapply dllseg_tail_not_null.
    instantiate (10:=s0).
    sep pauto.
    sep cancel 16%nat 1%nat.
    eauto.
    hoare unfold.
    inverts H73.

    destruct H42 as (prev_tcb_ptr & eqprev); subst v'13.
    (* rename x11 into prev_tcb_ptr. *)

    eapply backward_rule1.
    intro; intros.
    sep lift 16%nat in H42.
    rewrite dllseg_split_node_tail in H42.
    
    eauto.
    unfold node.
    hoare unfold.
    rename v'22 into v'38.
    rename v'10 into v'13.
    rename v'28 into vv28.
    rename v'11 into v'28.


    rename v'38 into prev_tcb_block.
    rename v'15 into next_tcb_block.

    hoare forward.
    go.
    hoare unfold.
    instantiate (1:= Afalse).
    false.

    hoare unfold.
    clear H42.
    hoare forward.
    go.
    hoare forward.
    go.
    
    hoare forward.
    go.
    
    hoare forward.

    go.

    hoare forward.
    hoare unfold.
    unfold   AOSTCBFreeList.
    hoare normal pre.
    hoare forward.
    eapply isptr_match_eq_true.
    eapply sll_head_isptr.
    instantiate (5 := s).
    sep cancel sll.
    eauto.

    hoare forward.
    assert (todelblock = cur_tcb_blk \/ todelblock <> cur_tcb_blk) by tauto. 
    destruct H74.
    (* delete current *)
    {
      subst todelblock.
      (* unfold get in H16; simpl in H16. *)
      rewrite H23 in kitty.

      eapply backward_rule1.
      instantiate (1:=
                     (
                      <|| spec_code_cons (sdel (Vint32 v'43 :: v'74 :: nil)) v'73 ||>  **
                           HTCBList tcbmap **
                           HCurTCB (cur_tcb_blk, Int.zero) **
                           OS [ empisr, false, nil, (true::nil)] **

   (* <|| sdel (Vint32 v'43 :: nil);; isched;; END Some (V$ NO_ERR) ||>  ** *)
   A_dom_lenv
     ((prio, Int8u)
      :: (pevent, OS_EVENT ∗)
         :: (ptcb, OS_TCB ∗)
            :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
   GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
   LV ptcb @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
   Astruct (cur_tcb_blk, Int.zero) OS_TCB_flag
     (v'20
      :: Vptr (prev_tcb_block, Int.zero)
         :: Vnull
            :: x0
               :: V$ 0
                  :: V$ OS_STAT_RDY
                     :: Vint32 v'43
                        :: Vint32 (v'43&ᵢ$ 7)
                           :: Vint32 (v'43 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil) **
   LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (next_tcb_block, Int.zero) **
   Astruct (next_tcb_block, Int.zero) OS_TCB_flag
     (v'14
      :: Vptr (prev_tcb_block, Int.zero)
         :: x25
            :: x24
               :: Vint32 i12
                  :: Vint32 i11
                     :: Vint32 i10
                        :: Vint32 i9
                           :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil) **
   Astruct (prev_tcb_block, Int.zero) OS_TCB_flag
     (Vptr (next_tcb_block, Int.zero)
      :: v'13
         :: x26
            :: x22
               :: Vint32 i20
                  :: Vint32 i19
                     :: Vint32 i18
                        :: Vint32 i17
                           :: Vint32 i16 :: Vint32 i15 :: Vint32 i14 :: nil) **
   dllseg v'9 Vnull v'13 (Vptr (prev_tcb_block, Int.zero)) v'28 OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   dllseg v'14 (Vptr (next_tcb_block, Int.zero)) v'12 Vnull l2' OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
     (update_nth_val (Z.to_nat (Int.unsigned v'43)) priotbl Vnull) **
   PV vhold @ Int8u |-> v'8 **
   HECBList v'16 **
   (* HTCBList tcbmap ** *)
   HTime v'18 **
   (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
   LV pevent @ OS_EVENT ∗ |-> Vnull **
   GV OSRdyGrp @ Int8u |-> Vint32 v'40 **
   GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned (v'43 >>ᵢ $ 3))) v'30
        (val_inj (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'43&ᵢ$ 7))))))) **
   GV OSTCBList @ OS_TCB ∗ |-> v'9 **
   GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
   (* Aie false ** *)
   (* Ais nil ** *)
   (* Acs (true :: nil) ** *)
   (* Aisr empisr ** *)
   AECBList v'7 v'6 v'16 tcbmap **
   tcbdllflag v'9
     ((v :: l1') ++
      (Vptr (next_tcb_block, Int.zero)
       :: Vptr (prev_tcb_block, Int.zero)
          :: Vnull
             :: x0
                :: Vint32 i13
                   :: V$ OS_STAT_RDY
                      :: Vint32 v'43
                         :: Vint32 (v'43&ᵢ$ 7)
                            :: Vint32 (v'43 >>ᵢ $ 3)
                               :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                  :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
      :: (v'14
          :: Vptr (cur_tcb_blk, Int.zero)
             :: x25
                :: x24
                   :: Vint32 i12
                      :: Vint32 i11
                         :: Vint32 i10
                            :: Vint32 i9
                               :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil)
         :: l2') **
   G& OSPlaceHolder @ Int8u == vhold **
   (* A_isr_is_prop ** *)
   p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
   LV self @ Int8u |-> (V$ 0) **
   AOSEventFreeList v'3 **
   AOSQFreeList v'4 **
   AOSQFreeBlk v'5 **
   AOSMapTbl **
   AOSUnMapTbl **
   AOSIntNesting **
   sll v'20 v'21 OS_TCB_flag V_OSTCBNext **
   sllfreeflag v'20 v'21 **
   AOSTime (Vint32 v'18) **
   AGVars ** APthreadAttr v'64 v'65 v'66 ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'43 )).

      clear.
      intro; intros.
      sep lifts (4:: 6::nil)%nat. 
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.

      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (cur_tcb_blk, Int.zero) (v'43, x,  x0) mmm tcbmap).
      apply tcb_get_join.
      unfold get, sig, join in *; simpl in *.
      unfold get, sig, join in *; simpl in *.
      go.

      destruct H74 as (tcbmap_left & tcbmapleft_join_hyp).


      eapply seq_rule.
      eapply derive_delself_rule.
      apply goodlinv.

       (* goodlinv *)
      go.
      (* unfold AEventData. *)
      (* destruct x22; go. *)
      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.
      exact tcbmapleft_join_hyp.
      intro; intros.
      split.
      sep_get_rv.
      unfold p_local in H74.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.
      hoare lift 27%nat pre.
      eapply backward_rule1.
      eapply dllsegflag_split.
      hoare_split_pure_all.
      unfold dllsegflag at 2.
      fold dllsegflag .
      hoare_split_pure_all.
      inverts H75.
      inverts H101.
      inverts H100.
      inverts H74.
      inverts H75.
      rewrite H73.

      rename v'11 into v'37.
      rename v'23 into v'42.


      hoare_assert_pure ( (fun vl : vallist => nth_val 0 vl) (Vptr (cur_tcb_blk, Int.zero)
                                                                   :: v'13
                                                                   :: x26
                                                                   :: x22
                                                                   :: Vint32 i20
                                                                   :: Vint32 i19
                                                                   :: Vint32 i18
                                                                   :: Vint32 i17
                                                                   :: Vint32 i16
                                                                   :: Vint32 i15 :: Vint32 i14 :: nil) = Some (Vptr v'37) ).
      eapply dllsegflag_last_next_is_endstnl.
      instantiate (4 := s0).
      sep cancel 4%nat 1%nat.
      eauto.

      hoare_split_pure_all.
      inverts H74.

      
      
      (* rewrite app_nil_l. *)
      (* hoare unfold. *)
      (* hoare lift 4%nat pre. *)
      unfold p_local at 2.
      unfold OSLInv at 3.
      unfold LINV.
      hoare_split_pure_all.
      (* unfold1 dllseg. *)
      (* hoare unfold. *)
      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)
      sep combine ( get_off_addr (cur_tcb_blk, Int.zero) ($ 24)  ) in H100.
      eauto.

      hoare lift 5%nat pre.
      eapply seq_rule.
      eapply assign_rule'.
      Focus 2.

      intro; intros.
      split.
      eapply field_asrt_impl.
      Focus 3.
      sep cancel 13%nat 1%nat.
      eauto.
      reflexivity.
      reflexivity.
      sep get rv.
      eapply eq_int; auto.

      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.
      sep cancel 44%nat 1%nat.
      simpl; auto.
      splits; eauto.
      unfolds; auto.
      

      eapply backward_rule1.
      intro; intros.
      sep lifts (8::10::nil)%nat in H100.
      eapply add_a_isr_is_prop in H100.
      eauto.
      hoare lift 4%nat pre.
      eapply seq_rule.

      eapply excrit1_rule'_ISnil_ISRemp''.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      unfold p_local, OSLInv.
      unfold LINV.
      sep pauto.
      sep cancel 2%nat 1%nat.
      sep cancel CurTid.
      unfold OSInv.
      sep pauto.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
      instantiate (20 := v'7).
      instantiate (19 := v'6).
      unfold AECBList.

      unfold AECBList in H100.
      sep pauto.

      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel 20%nat 2%nat.
      sep cancel 14%nat 1%nat.
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold AOSTCBList'.
      eapply intro_or_r.
      sep pauto.
      unfold tcblist.

      instantiate ( 8 :=(v'28 ++
                               (Vptr (next_tcb_block, Int.zero)
                                     :: v'13
                                     :: x26
                                     :: x22
                                     :: Vint32 i20
                                     :: Vint32 i19
                                     :: Vint32 i18
                                     :: Vint32 i17
                                     :: Vint32 i16
                                     :: Vint32 i15 :: Vint32 i14 :: nil)
                               :: nil)  ).

      instantiate ( 6 := l2').

      instantiate ( 7 :=
                      (v'42
                         :: Vptr (prev_tcb_block, Int.zero)
                         :: x25
                         :: x24
                         :: Vint32 i12
                         :: Vint32 i11
                         :: Vint32 i10
                         :: Vint32 i9
                         :: Vint32 i8
                         :: Vint32 i7 :: Vint32 i :: nil)).


      unfold TCB_Not_In.
      sep pauto.
      eapply tcbdllseg_compose.
      unfold tcbdllseg.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel APthreadAttr.
      sep cancel 10%nat 1%nat.
      sep cancel 12%nat 1%nat.

      eapply dllseg_is_poi.
      eapply split_poillseg.
      sep eexists.
      rewrite <- dllseg_is_poi.
      sep lift 2%nat.
      rewrite <- dllseg_is_poi.
      instantiate (3 := (Vptr (prev_tcb_block, Int.zero))).
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 10%nat 1%nat.
      sep cancel dllseg.



      unfold tcbdllflag.
      sep lift 4%nat in H100.
      rewrite dllsegflag_is_poi in H100.
      apply split_poillseg in H100.

      apply dllsegflag_is_poi.
      sep pauto.
      apply split_poillseg.
      sep eexists.
      apply split_poillseg.
      sep eexists.
      sep cancel 1%nat 1%nat.
      unfold1 @poi_llseg in *.
      sep normal.
      sep normal in H100.
      sep destruct H100.
      sep eexists.
      instantiate ( 3 := Vptr (next_tcb_block, Int.zero)).
      sep pauto.
      sep lift 2%nat.
      rewrite <- dllsegflag_is_poi.
      sep cancel dllsegflag.
      (* instantiate (x1 := x14). *)
      sep cancel 1%nat 2%nat.
      sep cancel 2%nat 1%nat.

      (* freelist *)
      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_r. 
      unfold TCBFree_Eq.
      sep pauto.
      sep cancel sll.
      sep cancel sllfreeflag.
      eauto.
      go.
      eapply isptr_is_definitely_ptr.
      eapply sll_head_isptr.
      instantiate (5:=s).
      sep cancel sll.
      go.
      unfolds.
      {
        do 6 eexists.
        splits.
        go.
        go.
        go.
        go.
        go.
        go.
        go.
        splits.
        go.
        go.
        go.
        go.
        left; auto.
        repeat tri_exists_and_solver1.
        go.
        rewrite (H64 (eq_refl ($ OS_STAT_RDY))).
        reflexivity.
      }
      eexists; go.
           {
        unfolds in H6.
        simpljoin.
        clear -tcbmapleft_join_hyp H104.
        unfolds.
        unfolds in tcbmapleft_join_hyp.
        intro.
        simpljoin.

        unfolds in H104.
        assert (x1 <> (cur_tcb_blk, Int.zero)).
        intro.
        subst.
(* ** ac:         SearchAbout join. *)
(* ** ac:         SearchAbout TcbMod.join. *)
        eapply TcbMod.map_join_get_some .
        
        auto.
        eauto.
        2: exact H.
        instantiate (1:=(v'43, x, x0)).
        unfold get in *; simpl in *.
        unfold sig in *; simpl in *.
        eapply TcbMod.get_a_sig_a.
        go.
        unfold join, sig, get in *; simpl in *.
        assert (TcbMod.get tcbmap x1 =Some (v'43, x2, x3) ).
        go.
        assert (TcbMod.get tcbmap (cur_tcb_blk, Int.zero) =Some (v'43, x, x0) ).
        go.
        lets bb: H104 H0 H1 H2.
        apply bb.
        reflexivity.

      }
  
      go.
      2: go.
      go.
      (* intro; tryfalse. *)
      go.
      go.
      (* intro; tryfalse. *)
      go.
      go.
      go.
      {
        splits.
assert( list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None)
   (v'28 ++
    (Vptr (cur_tcb_blk, Int.zero)
     :: v'13
        :: x26
           :: x22
              :: Vint32 i20
                 :: Vint32 i19
                    :: Vint32 i18
                       :: Vint32 i17
                          :: Vint32 i16 :: Vint32 i15 :: Vint32 i14 :: nil)
    :: nil) )as hell.

change ((fun x => list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None) x)
         (v'28 ++
      (Vptr (cur_tcb_blk, Int.zero)
       :: v'13
          :: x26
             :: x22
                :: Vint32 i20
                   :: Vint32 i19
                      :: Vint32 i18
                         :: Vint32 i17
                            :: Vint32 i16 :: Vint32 i15 :: Vint32 i14 :: nil)
      :: nil)).
 
 rewrite <- H73.

     
 eapply TCBLP_imply_nextnotnull_list.
 exact H29.
 
 rewrite H73.
 
         rewrite get_last_tcb_ptr_appsig.
         reflexivity.

        (* here *)
        rewrite ptr_in_tcblist_app.
        (* 2: simpl; auto. *)
        intro.
        destruct H102.
        eapply ptr_in_tcblist_last_ir in H102.
        gen H102.
        eapply distinct_is_unique_first.
instantiate ( 1 :=(Vptr (cur_tcb_blk, Int.zero)
             :: v'13
                :: x26
                   :: x22
                      :: Vint32 i20
                         :: Vint32 i19
                            :: Vint32 i18
                               :: Vint32 i17
                                  :: Vint32 i16
                                  :: Vint32 i15 :: Vint32 i14 :: nil)).

exact hell.

         eapply  TCBLP_imply_dictinct_list .
         rewrite <- H73.
         exact H25.

         rewrite get_last_tcb_ptr_appsig.
         reflexivity.

           
       
        (* simpl in H131. *)
        (* exact H131. *)
         rewrite get_last_tcb_ptr_appsig in H102.
         simpl (val_inj (Some (Vptr (next_tcb_block, Int.zero)))) in H102. 

        eapply ptr_in_tcblist_change_first in H102.
        gen H102.

        eapply distinct_is_unique_second.
        3: eapply  TCBLP_imply_dictinct_list .
        3: exact H25.
        2: go.
        rewrite H73.
        exact hell.
        rewrite H73.
        rewrite get_last_tcb_ptr_appsig.
        reflexivity.
        rewrite list_all_P_app.
        rewrite list_all_P_app in hell.
        simpljoin.
        splits; auto.
        simpl.
        split; auto.
         (* unfold V_OSTCBNext; simpl; intro; tryfalse. *)
        eauto.
      }
       (* from tcblist_p, get they are all different? *)
      {


         eapply TCBList_merge_prop.
         instantiate (2 := v'17).
         instantiate (1 := x13).

         eapply some_join_lemma0; eauto.
         exact H11.
         exact tcbmapleft_join_hyp.
         rewrite app_last.
         simpl.
         go.
         Focus 2.

         eapply  tcblist_p_hold_for_del_a_tcb_at_head .
         lia.

        2:go.
        2:go.
        2: exact H11.
        2: exact backup.
        unfolds in H6.
        simpljoin.
        clear -H103 H28.
        eapply R_Prio_No_Dup_hold_for_subset.
        apply TcbMod.join_comm; eauto.
        eauto.

        
        eapply OSTimeDlyPure.update_rtbl_tcblist_hold.

        lia.
        unfold nat_of_Z; eapply nv'2nv.
        exact H60.
        intro; tryfalse.
        intros.

        unfolds in H6.
        simpljoin.
        clear -H28 H11 H104 H102.
        eapply H104.
        instantiate (2 := tid).
        instantiate (1 := (cur_tcb_blk, Int.zero)).
        intro; subst tid.
        eapply TcbMod.map_join_get_some.
        auto.
        exact H28.
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        go.
        
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        go.
        
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        unfold get; simpl.
        go.
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        unfold get; simpl.
        go.


        eapply TCBList_P_hold_for_last_change.
        rewrite H73 in H29.
        exact H29.
        
        
      }
       (* tcblist_p hold for deleting a tcb *)
      split.
      assumption.
      eapply (H68 _ H55).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.
       
      {
        eapply  r_priotbl_p_hold_for_del_a_tcb.
        lia.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .

      }

       (* r_priotbl_p hold for deleting a tcb *)
      
{
  eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
  lia.
  rewrite Int.repr_unsigned.
  reflexivity.

  rewrite Int.repr_unsigned.
  reflexivity.

  2: assumption.
  unfold nat_of_Z.
  apply nv'2nv.
  
  assumption.
  intro; tryfalse.
  
      }

       (* rl_rtbl_ptbl_p hold for deleting a tcb *)

      split.
      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.


      {
      assert (forall ecbid, ~ exists bb cc, x = wait bb cc /\ isWait4Ecb bb ecbid ). 
      intros.
      intro.
      simpljoin.
      
      gen H103.
      eapply lowready_not_wait4ecb.
      lets bb: H64 (eq_refl ($ OS_STAT_RDY)).
      subst x23.
      exact H53.

      eapply ECBLP_hold4del_a_tcb_rdy; eauto.
      }

      {
        rewrite <- poi_is_rtep.
        rewrite <- poi_is_rtep in H2.

        eapply poi_RH_T_E_P_hold_for_tcbdel_rdy; eauto.
      intros.
      intro.
      simpljoin.
      
      gen H102.
      eapply lowready_not_wait4ecb.
      lets bb: H64 (eq_refl ($ OS_STAT_RDY)).
      subst x23.
      exact H53.
      }

      splits; go.
      unfolds; auto.
      go.
      hoare forward.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.

      hoare unfold.

      inverts H100.
      assert (Hopv: v'74 = Vint32 (Int.repr OS_NO_ERR) \/ v'74 <>Vint32 (Int.repr OS_NO_ERR)) by tauto.
      destruct Hopv.
    
      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskdel_succ.
      go.
      go.


      hoare forward.
      splits.
      eauto.
      eauto.
      
      change OS_NO_ERR with 0.
      rewrite Int.unsigned_repr. lia.
      rewrite max_unsigned_val. lia.

      change OS_NO_ERR with 0.
      rewrite Int.unsigned_repr.
      change Byte.max_unsigned with 255. lia.
      rewrite max_unsigned_val. lia.

      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskdel_succ_abt.
      can_change_aop_solver.
      auto.
    
      eapply absabort_rule.

    }

    (* delete not current *)
    {


      eapply backward_rule1.
      Set Printing Depth 999.
(* ** ac:       Show. *)
      instantiate (1:=
                     (
                      <|| spec_code_cons (sdel (Vint32 v'43 :: v'74 :: nil)) v'73 ||>  **
                           HTCBList tcbmap **
                           HCurTCB (cur_tcb_blk, Int.zero) **
                           OS [ empisr, false, nil, (true::nil)] **
   (* <|| spec_del (Vint32 v'53);; isched;; END Some (V$ NO_ERR) ||>  ** *)
   (* <|| sdel (Vint32 v'43 :: nil);; isched;; END Some (V$ NO_ERR) ||>  ** *)
   A_dom_lenv
     ((prio, Int8u)
      :: (pevent, OS_EVENT ∗)
         :: (ptcb, OS_TCB ∗)
            :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
   GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
   LV ptcb @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
   Astruct (todelblock, Int.zero) OS_TCB_flag
     (v'20
      :: Vptr (prev_tcb_block, Int.zero)
         :: Vnull
            :: x0
               :: V$ 0
                  :: V$ OS_STAT_RDY
                     :: Vint32 v'43
                        :: Vint32 (v'43&ᵢ$ 7)
                           :: Vint32 (v'43 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil) **
   LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (next_tcb_block, Int.zero) **
   Astruct (next_tcb_block, Int.zero) OS_TCB_flag
     (v'14
      :: Vptr (prev_tcb_block, Int.zero)
         :: x25
            :: x24
               :: Vint32 i12
                  :: Vint32 i11
                     :: Vint32 i10
                        :: Vint32 i9
                           :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil) **
   Astruct (prev_tcb_block, Int.zero) OS_TCB_flag
     (Vptr (next_tcb_block, Int.zero)
      :: v'13
         :: x26
            :: x22
               :: Vint32 i20
                  :: Vint32 i19
                     :: Vint32 i18
                        :: Vint32 i17
                           :: Vint32 i16 :: Vint32 i15 :: Vint32 i14 :: nil) **
   dllseg v'9 Vnull v'13 (Vptr (prev_tcb_block, Int.zero)) v'28 OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   dllseg v'14 (Vptr (next_tcb_block, Int.zero)) v'12 Vnull l2' OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
     (update_nth_val (Z.to_nat (Int.unsigned v'43)) priotbl Vnull) **
   PV vhold @ Int8u |-> v'8 **
   HECBList v'16 **
   (* HTCBList tcbmap ** *)
   HTime v'18 **
   (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
   LV pevent @ OS_EVENT ∗ |-> Vnull **
   GV OSRdyGrp @ Int8u |-> Vint32 v'40 **
   GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned (v'43 >>ᵢ $ 3))) v'30
        (val_inj (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'43&ᵢ$ 7))))))) **
   GV OSTCBList @ OS_TCB ∗ |-> v'9 **
   GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
   (* Aie false ** *)
   (* Ais nil ** *)
   (* Acs (true :: nil) ** *)
   (* Aisr empisr ** *)
   AECBList v'7 v'6 v'16 tcbmap **
   tcbdllflag v'9
     ((v :: l1') ++
      (Vptr (next_tcb_block, Int.zero)
       :: Vptr (prev_tcb_block, Int.zero)
          :: Vnull
             :: x0
                :: Vint32 i13
                   :: V$ OS_STAT_RDY
                      :: Vint32 v'43
                         :: Vint32 (v'43&ᵢ$ 7)
                            :: Vint32 (v'43 >>ᵢ $ 3)
                               :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                  :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
      :: (v'14
          :: Vptr (todelblock, Int.zero)
             :: x25
                :: x24
                   :: Vint32 i12
                      :: Vint32 i11
                         :: Vint32 i10
                            :: Vint32 i9
                               :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil)
         :: l2') **
   G& OSPlaceHolder @ Int8u == vhold **
   (* A_isr_is_prop ** *)
   p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
   LV self @ Int8u |-> (V$ 0) **
   AOSEventFreeList v'3 **
   AOSQFreeList v'4 **
   AOSQFreeBlk v'5 **
   AOSMapTbl **
   AOSUnMapTbl **
   AOSIntNesting **
   sll v'20 v'21 OS_TCB_flag V_OSTCBNext **
   sllfreeflag v'20 v'21 **
   AOSTime (Vint32 v'18) **
   AGVars ** APthreadAttr v'64 v'65 v'66 ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'43)).
      clear.
      intro; intros.
      sep lifts (4:: 6::nil)%nat. 
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.

      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (todelblock, Int.zero) (v'43, x , x0) mmm tcbmap).
      apply tcb_get_join.
      unfold get, sig, join in *; simpl in *.
      unfold get, sig, join in *; simpl in *.
      go.

      destruct H75 as (tcbmap_left & tcbmapleft_join_hyp).


      eapply seq_rule.
      eapply derive_delother_rule.
      apply goodlinv.

       (* goodlinv *)
      go.
      (* unfold AEventData. *)
      (* destruct x22; go. *)
      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.
      exact tcbmapleft_join_hyp.
      clear -H3; unfolds in H3.
      unfolds.
      simpljoin.
      eauto.
      intro; tryfalse.
      intro; intros.
      split.
      sep_get_rv.
      unfold p_local in H75.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.
      hoare lift 28%nat pre.
      eapply backward_rule1.
      eapply dllsegflag_split.
      hoare_split_pure_all.
      unfold dllsegflag at 2.
      fold dllsegflag .
      hoare_split_pure_all.

      rename v'15 into vv15.

      rename v'10 into v'15.
      rename v'11 into v'37.
      rename v'15 into v'38.
      rename v'22 into v'39.
      rename v'23 into v'42.
      rename v'24 into v'44.

      inverts H102.
      inverts H100.
      
      rename v'38 into v'15.
      rename vv15 into v'38.
      
      subst v'15.
      inverts H103.
      rewrite H73.



      hoare_assert_pure ( (fun vl : vallist => nth_val 0 vl) (Vptr (todelblock, Int.zero)
                                                                   :: v'13
                                                                   :: x26
                                                                   :: x22
                                                                   :: Vint32 i20
                                                                   :: Vint32 i19
                                                                   :: Vint32 i18
                                                                   :: Vint32 i17
                                                                   :: Vint32 i16
                                                                   :: Vint32 i15 :: Vint32 i14 :: nil) = Some (Vptr v'38) ).
      eapply dllsegflag_last_next_is_endstnl.
      instantiate (4 := s0).
      sep cancel 5%nat 1%nat.
      eauto.

      hoare_split_pure_all.
      inverts H75.

      
      
      (* rewrite app_nil_l. *)
      (* hoare unfold. *)
      (* hoare lift 4%nat pre. *)
      unfold p_local at 2.
      unfold OSLInv at 3.
      unfold LINV.
      hoare_split_pure_all.
      (* unfold1 dllseg. *)
      (* hoare unfold. *)
      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)
      sep combine ( get_off_addr (todelblock, Int.zero) ($ 24)  ) in H101.
      eauto.

      hoare lift 5%nat pre.
      eapply seq_rule.
      eapply assign_rule'.
      Focus 2.

      intro; intros.
      split.
      eapply field_asrt_impl.
      Focus 3.
      sep cancel 13%nat 1%nat.
      eauto.
      reflexivity.
      reflexivity.
      sep get rv.
      eapply eq_int; auto.

      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.
      sep lift 30%nat in H101.
      unfold OSLInv in H101.
      sep normal in H101.
      sep destruct H101.
      sep split in H101.
      unfold init_lg in H75; destruct H75.
      inverts H75.
      sep cancel 1%nat 1%nat.
      eauto.

      simpl; auto.
      splits; eauto.
      unfolds; auto.
      

      eapply backward_rule1.
      intro; intros.
      sep lifts (8::10::nil)%nat in H101.
      eapply add_a_isr_is_prop in H101.
      eauto.
      hoare lift 4%nat pre.
      eapply seq_rule.

      eapply excrit1_rule'_ISnil_ISRemp''.
      rename v'10 into v'14.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      unfold p_local.
      sep pauto.
      unfold LINV.
      sep pauto.
      sep cancel OSLInv.
      eapply poi_OSINV_imply_OSInv.
      unfold poi_OSINV.
      sep pauto.
      sep cancel APthreadAttr.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
      unfold AECBList in H101.
      unfold AECBList.
      instantiate (14 := v'7).
      instantiate (13 := v'6).

      sep pauto.

      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel 20%nat 2%nat.
      sep cancel 14%nat 1%nat.
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold poi_AOSTCBList.
      
      sep pauto.
      instantiate (4 := (
(v'28 ++
               (Vptr (next_tcb_block, Int.zero)
                :: v'13
                   :: x26
                      :: x22
                         :: Vint32 i20
                            :: Vint32 i19
                               :: Vint32 i18
                                  :: Vint32 i17
                                     :: Vint32 i16
                                        :: Vint32 i15 :: Vint32 i14 :: nil)
               :: nil)  ++
                         (v'44
               :: Vptr (prev_tcb_block, Int.zero)
                  :: x25
                     :: x24
                        :: Vint32 i12
                           :: Vint32 i11
                              :: Vint32 i10
                                 :: Vint32 i9
                                    :: Vint32 i8
                                       :: Vint32 i7 :: Vint32 i :: nil) 
                          
                            :: l2')).
      unfold tcbdllseg.
      unfold tcbdllflag.
      unfold1 dllsegflag.
      unfold1 dllseg.
      unfold node.
      sep pauto.

      

      eapply dllseg_is_poi.
      eapply split_poillseg.
      sep eexists.
      eapply split_poillseg.
      sep eexists.
      rewrite <- dllseg_is_poi.
      sep lift 2%nat.
      rewrite <- dllseg_is_poi.
      sep lift 3%nat.
      rewrite <- dllseg_is_poi.
      unfold1 dllseg.
      unfold node.
      sep normal.
      sep eexists.
      instantiate (22 := prev_tcb_block).
      instantiate (4 := Vptr (prev_tcb_block, Int.zero)).
      instantiate (4 := v'13).
      instantiate (15 := Vptr (next_tcb_block, Int.zero)).
      instantiate (4 := Vptr (next_tcb_block, Int.zero)).
      instantiate (6 := Vptr (prev_tcb_block, Int.zero)).
      instantiate (7 := next_tcb_block).

      sep pauto.
      sep cancel 11%nat 1%nat.
      sep cancel 10%nat 1%nat.
      (* sep cancel 11%nat 1%nat. *)
      (* sep cancel dllseg. *)

      sep lift 4%nat in H101.
      rewrite dllsegflag_is_poi in H101.
      apply split_poillseg in H101.
      sep destruct H101.
      apply dllsegflag_is_poi.
      apply split_poillseg.
      sep eexists.
      apply split_poillseg.
      sep eexists.
      sep pauto.
      sep cancel 1%nat 1%nat.
      unfold1 @poi_llseg in *.
      sep normal in H101; sep destruct H101.
      sep normal; sep eexists.
      instantiate (5 := Vptr (next_tcb_block, Int.zero)).
      sep pauto.
      2: go.
      sep lift 2%nat.
      rewrite <- dllsegflag_is_poi.
      sep cancel dllsegflag.
      (* instantiate (x1 := x14). *)
      sep cancel 1%nat 2%nat.
      sep cancel 2%nat 1%nat.

      (* freelist *)
      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_l. 
      unfold TCBFree_Not_Eq.
      sep pauto.
      instantiate ( 2 := (
(v'20
               :: Vptr (prev_tcb_block, Int.zero)
                  :: Vnull
                     :: x0
                        :: V$ 0
                           :: V$ OS_STAT_RDY
                              :: Vint32 v'43
                                 :: Vint32 (v'43&ᵢ$ 7)
                                    :: Vint32 (v'43 >>ᵢ $ 3)
                                       :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                          :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3))
                                             :: nil) :: v'21
                            
                          )).
      unfold1 sll.
      unfold1 sllfreeflag.
      unfold1 sllseg.
      unfold1 sllsegfreeflag.
      
      sep pauto.
      unfold node.
      unfold sll, sllfreeflag in H101.
      sep pauto.
      sep cancel sllsegfreeflag.
      sep cancel sllseg.
      sep cancel Astruct.
      eauto.
      go.
      eapply isptr_is_definitely_ptr.
      eapply sll_head_isptr.
      instantiate (5:=s).
      unfold sll.
      sep cancel sllseg.
      go.
      go.
      
      go.
      intro; tryfalse.
      (* intro; tryfalse. *)
      go.
      go.
      go.
      intro; tryfalse.

      {


         eapply TCBList_merge_prop.
         instantiate (2 := v'17).
         instantiate (1 := x13).

         eapply some_join_lemma0; eauto.
         exact H11.
         exact tcbmapleft_join_hyp.
                  

         rewrite app_last.
         simpl.
         go.
         Focus 2.

         eapply  tcblist_p_hold_for_del_a_tcb_at_head .
         lia.

        2:go.
        2:go.
        2: exact H11.
        2: exact backup.
        unfolds in H6.
        simpljoin.
        clear -H104 H28.
        eapply R_Prio_No_Dup_hold_for_subset.
        apply TcbMod.join_comm; eauto.
        eauto.

        
        eapply OSTimeDlyPure.update_rtbl_tcblist_hold.

        lia.
        unfold nat_of_Z; eapply nv'2nv.
        exact H60.
        intro; tryfalse.
        intros.

        unfolds in H6.
        simpljoin.
        clear -H28 H11 H105 H103.
        eapply H105.
        instantiate (2 := tid).
        instantiate (1 := (todelblock, Int.zero)).
        intro; subst tid.
        eapply TcbMod.map_join_get_some.
        auto.
        exact H28.
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        go.
        
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        go.
        
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        unfold get; simpl.
        go.
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        unfold get; simpl.
        go.
        eapply TCBList_P_hold_for_last_change.
        rewrite H73 in H29.
        exact H29.
        
      }
       (* tcblist_p hold for deleting a tcb *)

      {
        assert (list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None) (v'28 ++
         (Vptr (todelblock, Int.zero)
          :: v'13
             :: x26
                :: x22
                   :: Vint32 i20
                      :: Vint32 i19
                         :: Vint32 i18
                            :: Vint32 i17
                               :: Vint32 i16
                                  :: Vint32 i15 :: Vint32 i14 :: nil) :: nil
                                                                         )).

 eapply TCBLP_imply_nextnotnull_list.
 rewrite H73 in H29.
 exact H29.
 rewrite  get_last_tcb_ptr_appsig.
 eauto.


 
        eapply  ptr_in_tcblist_app in H24.
        destruct H24.
        apply  ptr_in_tcblist_app.

        2: left; eapply ptr_in_tcblist_last_ir.
        apply  list_all_P_app.
        apply  list_all_P_app in H103.
        simpljoin.
        splits; auto.
        simpl; go.
        (* unfold V_OSTCBNext; simpl; intro; tryfalse. *)
        rewrite H73 in H24; exact H24.

        
        apply  ptr_in_tcblist_app.

        apply  list_all_P_app.
        apply  list_all_P_app in H103.
        simpljoin.
        splits; auto.
        simpl; go.
        (* unfold V_OSTCBNext; simpl; intro; tryfalse. *)

        right.
        
        rewrite          get_last_tcb_ptr_appsig.
        rewrite H73 in H24.
        rewrite          get_last_tcb_ptr_appsig in H24.
        eapply  ptr_in_tcbdllseg_change_head.
        Focus 2.
        eapply ptr_in_tcbdllseg_not_head. 
        2: exact H24.
        reflexivity.
        simpl; intro; tryfalse.
        reflexivity.
        rewrite H73.
        exact H103.
        
      }
       (* from tcblist_p, get they are all different? *)
      split.
      assumption.
      eapply (H68 _ H55).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.
        
      {
        eapply  r_priotbl_p_hold_for_del_a_tcb.
        lia.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .

      }

       (* r_priotbl_p hold for deleting a tcb *)
      
{
  eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
  lia.
  rewrite Int.repr_unsigned.
  reflexivity.

  rewrite Int.repr_unsigned.
  reflexivity.

  2: assumption.
  unfold nat_of_Z.
  apply nv'2nv.
  
  assumption.
  intro; tryfalse.
  
      }

       (* rl_rtbl_ptbl_p hold for deleting a tcb *)

      split.
      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.



      {
      assert (forall ecbid, ~ exists bb cc, x = wait bb cc /\ isWait4Ecb bb ecbid ). 
      intros.
      intro.
      simpljoin.
      
      gen H104.
      eapply lowready_not_wait4ecb.
      lets bb: H64 (eq_refl ($ OS_STAT_RDY)).
      subst x23.
      exact H53.

      eapply ECBLP_hold4del_a_tcb_rdy; eauto.
      }
       (* from H101 : RL_Tbl_Grp_P
           (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
              (val_inj
                 (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
           (Vint32 v'53), ECBList_P holds for deleting a tcb *)
      {
        rewrite <- poi_is_rtep.
        rewrite <- poi_is_rtep in H2.

        eapply poi_RH_T_E_P_hold_for_tcbdel_rdy; eauto.
      intros.
      intro.
      simpljoin.
      
      gen H103.
      eapply lowready_not_wait4ecb.
      lets bb: H64 (eq_refl ($ OS_STAT_RDY)).
      subst x23.
      exact H53.
      }
      go.

Ltac sep_semiauto_nosplit2 :=
    intros;
    match goal with
      | H:?s |= _
        |- ?s |= _ =>
        try (solve [ exact H | apply atrue_intro ]); sep normal in H; sep
                                                                        destruct H;  (try progress ssplit_apure_in H); subst;
        repeat match goal with
                 | H0 : exists _ , _ |- _ => destruct H0
                 | H0 : _ /\ _ |- _ => destruct H0
               end;
        (let Hp := type of H in
         let H' := fresh in
         assert Hp as H' by exact H; clear H; rename H' into H); sep normal;
        sep eexists; ssplit_apure(*;
        match goal with
          | |- _ |= _ => idtac 1;scancel
          | _ => idtac 2;sep_pure
        end*)
      | _ => idtac
    end.
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
                 intros;unfold_spec;sep_semiauto_nosplit2 |
                 idtac |
                 sep_unfold_funpost |
                 sep_unfold_funpre |
                 simpl;eauto
                ] 
        | none _ => idtac
      end
  end.
  hoare normal pre; hoare_ex_intro; eapply seq_rule.
  eapply forward_rule2.
  1: hoare_call2.
  7: try sep_unfold_funpost; sep pauto.

      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.

      hoare unfold.

      inverts H101.
      assert (Hopv: v'74 = Vint32 (Int.repr OS_NO_ERR) \/ v'74 <>Vint32 (Int.repr OS_NO_ERR)) by tauto.
      destruct Hopv.
    
      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskdel_succ.
      go.
      go.


      hoare forward.
      splits.
      eauto.
      eauto.
      
      change OS_NO_ERR with 0.
      rewrite Int.unsigned_repr. lia.
      rewrite max_unsigned_val. lia.

      change OS_NO_ERR with 0.
      rewrite Int.unsigned_repr.
      change Byte.max_unsigned with 255. lia.
      rewrite max_unsigned_val. lia.

      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskdel_succ_abt.
      can_change_aop_solver.
      auto.
    
      eapply absabort_rule.

    }
  }

  Unshelve.
  exact (Afalse).
  exact cur_tcb_blk.
  exact cur_tcb_blk.    
  exact cur_tcb_blk.
  exact cur_tcb_blk.    

(* end of eapply task_delete_ready*)
 }


 {
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskdel_succ'.
  go.
  

      lets bb: TcbIsWait H53 H58.
      simpljoin.
      rename v'18 into ecbmap.
  
     
      lets bbackup: H2.
        
      rewrite <- poi_is_rtep in H2.
      unfolds in H2.
      simpljoin.
      unfolds in H61.
      lets cc: H61 H72 H23.
      simpljoin.
        
  

      unfold AECBList.
      hoare normal pre.
      hoare unfold.
      lets cc: hl_get_ecb_can_split_ecblist H73 H75.
      simpljoin.
  
      hoare lift 2%nat pre.
      eapply backward_rule1.
      eapply evsllseg_split.
  (* ** ac:     SearchAbout (length _ = length _). *)
      eapply ecblistp_length_eq_1; eauto.
      hoare normal pre.
      hoare_split_pure_all.
      hoare_assert_pure (v'8 = Vptr x12).
      symmetry.
      eapply ecblistp_evsllseg_tlsame; eauto.
  
  
      hoare unfold.
      unfold1 evsllseg.
      destruct x16.
      hoare unfold.
      unfold AEventNode.
      unfold AOSEvent.
      unfold node.
      unfold AOSEventTbl.
      hoare unfold.
  
      hoare forward.
      (* intro; tryfalse. *)
      (* intro; tryfalse. *)
      change (
          (pevent ′ → OSEventTbl) [ptcb ′ → OSTCBY] &= ∼ ptcb ′ → OSTCBBitX;ₛ
                                                                              If((pevent ′ → OSEventTbl) [ptcb ′ → OSTCBY] ==ₑ ′ 0)
                                                                              {pevent ′ → OSEventGrp &= ∼ ptcb ′ → OSTCBBitY}
        ) with (
        inline_call inline_bittbl_clearbit ((pevent′→OSEventGrp):: (pevent′→OSEventTbl)::(ptcb ′ → OSTCBBitX)::(ptcb ′ → OSTCBBitY)::(ptcb ′ → OSTCBY)::nil)
      ).
  
      hoare_split_pure_all.
      inline_forward.
      Focus 2.
      sep pauto.
      sep cancel Aop.
      sep cancel 2%nat 2%nat.
  
      8: exact H87.
      unfold Astruct in H83 at 1.
      unfold OS_EVENT in H83 at 1.
      unfold Astruct' in H83.

      sep normal in H83.
      sep cancel 2%nat 1%nat.
      eauto.
      instantiate (1:= v'48).
      clear -H; omega.
      unfolds.
      math simpls.
      assumption.
      assumption.
      clear -H; mauto.
      intro; intros.
      lrv_solver.
  
  
      Theorem struct_member_array_rv'':
        forall s x t l (* vl *) tid decl id t' n P ad perm,
          s |=  LV x @ (Tptr t) |=> Vptr l @ perm  (* ** Astruct l t vl  *)** P->
          t = Tstruct tid decl ->
          good_decllist decl = true ->
          ftype id decl = Some (Tarray t' n) ->
          id_addrval l id t = Some ad ->
          s |= Rv (efield (ederef (evar x)) id) @ (Tarray t' n) == Vptr ad.
      Proof.
  
        Import DeprecatedTactic.
        intros.
        destruct s as [[[[[[]]]]]].
        simpl in *;mytac.
        rewrite H12.
        rewrite H2.
        unfold load;unfold loadm.
        rewrite Int.unsigned_zero in H13.
        lets Hf: mapstoval_loadbytes H13.
        simpl;auto.
        destruct Hf.
        destruct H.
        lets Hf: loadbytes_local H4 H.
        assert ( loadbytes m (x13, 0%Z) (typelen (Tptr (Tstruct tid decl))) = Some x2);auto.
        rewrite H5.
        rewrite H0.
        destruct l.
        unfold getoff.
        unfold evaltype.
        rewrite H12.
        unfold id_addrval in H3.
        remember (field_offset id decl ) as X.
        destruct X;tryfalse.
        rewrite Int.repr_unsigned.
        simpl.
        rewrite Int.repr_unsigned.
        inverts H3;auto.
        rewrite H12.
        auto.
        intro; tryfalse.
      Qed.
  
      eapply struct_member_array_rv''.
      sep cancel 13%nat 1%nat.
      eauto.
      unfold OS_EVENT.
      auto.
      unfolds; simpl.
      reflexivity.
  
      unfolds; simpl.
      reflexivity.
  
      assumption.
  
      Theorem struct_member_lv:
        forall s x t (* vl *) tid decl id t' a b off,
          s |= Rv (evar x) @ (Tptr t) == Vptr (a, b)  (* Astruct l t vl ** *) ->
          t = Tstruct tid decl ->
          good_decllist decl = true ->
          ftype id decl = Some t' ->
          field_offset id decl = Some off ->
          s |= Lv (efield (ederef (evar x)) id) @ t' == (a, b +ᵢ off).
      Proof.
        intros.
        destruct s as [[[[[[]]]]]].
        simpl in *.
  
        unfold getoff.
        simpl.
        simpljoin.
        destruct (get e0 x).
        destruct p.
        rewrite H.
        destruct l.
        inverts H4.
        splits; auto.
        rewrite H3.
        rewrite Int.repr_unsigned.
        auto.
  
        destruct (get e x).
        destruct p.
        rewrite H.
        inverts H4.
        rewrite H3.
        splits; auto.
  
        rewrite Int.repr_unsigned.
        auto.
        inverts H4.
        
      Qed.
  (* ** ac:     Show. *)
  
      eapply struct_member_lv.
      symbolic_execution.
      unfold OS_EVENT; auto.
      unfolds; reflexivity.
      reflexivity.
      reflexivity.
      (* intro; tryfalse. *)
      go.
      (* intro; tryfalse. *)
      go.
      (* intro; tryfalse. *)
      go.
  
      linv_solver.
  
  
      hoare forward.
  
      Focus 2.
      hoare unfold.
      false.
      clear -H78.
      destruct H78; int auto.    
      
      inline_post_unfolder inline_bittbl_clearbit.
      hoare unfold.
      inverts H78.
      hoare forward.
      hoare forward.
      hoare unfold.
      hoare forward.
      math simpls.
      (* clear -H; mauto. *)
      clear H101 H102 H103.
  
      destruct l2'.
      unfold1 dllseg.
      hoare unfold.
      inverts H101.
      unfold1 dllseg.
      unfold node.
      hoare unfold.



(*      eapply task_deletewaiting with 
  (x20 := x20) (x19 := x19) (x18 := x18) (x17 := x17) ( i6 := i6) ( i5 := i5 ) ( i4 := i4) ( i3 := i3) ( i2 := i2) (i1 := i1 ) ( i0 := i0) ( l2 := l2) (v'3 := v'5) (v'4 := v'6) (v'5 := v'7) (v'6 := v'8) (v'7 := v'9) (v'9 := v'11) (v'12 := v'14) (v'13 := v'15) (v'14 := v'16) (v'15 := v'17) (v'16 := v'18) (v'17 := v'19) (v'18 := v'20) (v'19 := v'21) (v'20 := v'22) (v'21 := v'23) (v'25 := v'34) (v'26 := v'35) (v'27 := v'32) (v'28 := v'30) (v'29 := v'31) (v'30 := v'33) (v'32 := v'37) (v'33 := v'38) (v'34 := v'39) (v'35 := v'40) (v'36 := v'41) (v'37 := v'42) (v'38 := v'43) (v'39 := v'44) (v'40 := v'45) (v'41 := v'46) (v'42 := v'47) (v'44 := v'49) (v'45 := v'50) (v'46 := v'51) (v'50 := v'55) (v'51 := v'56) (v'53 := v'58) (v'73 := v'3) (v'74 := v'4) (v'64 := v'24) (v'65 := v'25) (v'66 := v'26); eauto.   *)
  intros.
  rename v'12 into vv12.
  rename v'13 into vv13.
  rename v'27 into vv27.
  rename v'28 into vv28.  
  rename v'29 into vv29.
  rename v'36 into vv36.

  rename v'3 into v'73.
  rename v'4 into v'74.
  rename v'24 into v'64.
  rename v'25 into v'65.
  rename v'26 into v'66.
  rename v'5 into v'3.
  rename v'6 into v'4.
  rename v'7 into v'5.
  rename v'8 into v'6.
  rename v'9 into v'7.
  rename v'10 into v'8.
  rename v'11 into v'9.
  rename v'14 into v'12.  
  rename v'15 into v'13. 
  rename v'16 into v'14. 
  rename v'17 into v'15.
  rename v'18 into v'16.  
  rename v'19 into v'17.
  rename v'20 into v'18.  
  rename v'21 into v'19.
  rename v'22 into v'20.
  rename v'23 into v'21.

  rename v'30 into v'28.
  rename v'31 into v'29.
  rename v'32 into v'27.  
  rename v'33 into v'30.
  rename v'34 into v'25.
  rename v'35 into v'26.
  rename v'37 into v'32.
  rename v'38 into v'33.
  rename v'39 into v'34.
  rename v'40 into v'35.
  rename v'41 into v'36.
  rename v'42 into v'37.
  rename v'43 into v'38.
  rename v'44 into v'39.
  rename v'45 into v'40.
  rename v'46 into v'41.
  rename v'47 into v'42.
  rename v'49 into v'44.
  rename v'50 into v'45.
  rename v'51 into v'46.
  rename v'55 into v'50.
  rename v'56 into v'51.
  rename v'58 into v'53.


  Set Printing Depth 999.
  hoare forward.

  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskdel_cler_waitls_bit'.
  go.
  exact H23.
  go.
  go.
  go.
  
  destruct l1'.
  hoare_assert_pure (v'13 = Vnull). 
  unfold1 dllseg in H101.
  sep normal in H101.
  sep destruct H101.
  sep split in H101.
  rewrite H103; reflexivity.
  
  (* v'13 is null, deleting first tcb node *)
  {
    hoare_split_pure_all.
    subst v'13.

    hoare forward.
    (* intro; tryfalse. *)
    go.
    (* intro; tryfalse. *)

    Focus 2.
    hoare_split_pure_all; false.
    clear -H101; simpljoin.
    destruct H101; tryfalse.

    hoare unfold.
    hoare forward.
    (* intro; tryfalse. *)
    go.
    hoare forward.
    hoare forward.

    hoare forward.

    Focus 2.
    hoare_split_pure_all.
    false.
    clear -H101; destruct H101; tryfalse.


    hoare unfold.
    unfold AOSTCBFreeList.
    hoare unfold.
    hoare forward.

    eapply isptr_is_definitely_ptr.
    eapply sll_head_isptr.
    instantiate (5:=s).
    sep cancel sll.
    go.

    hoare forward.

    clear H101 H102 H103.
    assert (todelblock = cur_tcb_blk \/ todelblock <> cur_tcb_blk) by tauto. 
    destruct H101.
    (* delete current *)
    {
      subst todelblock.
      (* unfold get in H16; simpl in H16. *)
      rewrite H23 in kitty.
      Set Printing Depth 999.
      eapply backward_rule1.
      instantiate (1:=
                     (
                       <|| spec_del (Vint32 v'53);; isched;; taskdel_succ (|v'74 :: nil|);; v'73 ||>  **
                           HTCBList tcbmap **
                           HCurTCB (cur_tcb_blk, Int.zero) **
                           OS [ empisr, false, nil, (true::nil)] **
  (* <|| spec_del (Vint32 v'53);; isched;; END Some (V$ NO_ERR) ||>  ** *)
   A_dom_lenv
     ((prio, Int8u)
      :: (pevent, OS_EVENT ∗)
         :: (ptcb, OS_TCB ∗)
            :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
   GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
   LV ptcb @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
   Astruct (cur_tcb_blk, Int.zero) OS_TCB_flag
     (v'20
      :: Vnull
         :: Vnull
            :: x0
               :: V$ 0
                  :: V$ OS_STAT_RDY
                     :: Vint32 v'53
                        :: Vint32 (v'53&ᵢ$ 7)
                           :: Vint32 (v'53 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) :: nil) **
   GV OSTCBList @ OS_TCB ∗ |-> Vptr (v'16, Int.zero) **
   LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (v'16, Int.zero) **
   Astruct (v'16, Int.zero) OS_TCB_flag
     (v'14
      :: Vnull
         :: x35
            :: x34
               :: Vint32 i15
                  :: Vint32 i14
                     :: Vint32 i12
                        :: Vint32 i11
                           :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil) **
   dllseg v'14 (Vptr (v'16, Int.zero)) v'12 Vnull l2' OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
     (update_nth_val (Z.to_nat (Int.unsigned v'53)) priotbl Vnull) **
   PV vhold @ Int8u |-> v'7 **
   Aarray v'38 (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
        (val_inj (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
   PV (v'15, Int.zero +ᵢ  $ 1) @ Int8u |-> Vint32 v'50 **
   PV (v'15, Int.zero) @ Int8u |-> Vint32 i7 **
   PV (v'15,
      (Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
      $ Z.of_nat (typelen Int8u)) @ Int16u |-> Vint32 i8 **
   PV (v'15,
      ((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
       $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) @
   (Void) ∗ |-> x29 **
   PV (v'15,
      ((((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
         $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) +ᵢ
       $ Z.of_nat (typelen (Void) ∗)) +ᵢ
      $ Z.of_nat (typelen (Tarray Int8u ∘ OS_EVENT_TBL_SIZE))) @
   STRUCT os_event ⋆ |-> v'6 **
   AEventData
     (Vint32 i7 :: Vint32 v'28 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil) x22 **
   evsllseg v'6 Vnull x15 x24 **
   evsllseg v'8 (Vptr (v'15, Int.zero)) x11 x23 **
   GV OSEventList @ OS_EVENT ∗ |-> v'8 **
   HECBList
   (EcbMod.set ecbmap (v'15, Int.zero)
        (x, remove_tid (cur_tcb_blk, Int.zero) x14))
   (* ecbmap *)
   **
   (* HTCBList tcbmap ** *)
   HTime v'18 **
   (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
   LV pevent @ OS_EVENT ∗ |-> Vptr (v'15, Int.zero) **
   GV OSRdyGrp @ Int8u |-> Vint32 v'40 **
   GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
        (val_inj (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
   dllseg v'9 Vnull Vnull (Vptr (cur_tcb_blk, Int.zero)) nil OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
   (* Aie false ** *)
   (* Ais nil ** *)
   (* Acs (true :: nil) ** *)
   (* Aisr empisr ** *)
   tcbdllflag v'9
     (nil ++
      (Vptr (v'16, Int.zero)
       :: Vnull
          :: Vptr (v'15, Int.zero)
             :: x0
                :: Vint32 i13
                   :: Vint32 x21
                      :: Vint32 v'53
                         :: Vint32 (v'53&ᵢ$ 7)
                            :: Vint32 (v'53 >>ᵢ $ 3)
                               :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                  :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) :: nil)
      :: (v'14
          :: Vptr (cur_tcb_blk, Int.zero)
             :: x35
                :: x34
                   :: Vint32 i15
                      :: Vint32 i14
                         :: Vint32 i12
                            :: Vint32 i11
                               :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
         :: l2') **
   G& OSPlaceHolder @ Int8u == vhold **
   (* A_isr_is_prop ** *)
   p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
   LV self @ Int8u |-> (V$ 0) **
   AOSEventFreeList v'3 **
   AOSQFreeList v'4 **
   AOSQFreeBlk v'5 **
   AOSMapTbl **
   AOSUnMapTbl **
   AOSIntNesting **
   sll v'20 v'21 OS_TCB_flag (fun vl : vallist => nth_val 0 vl) **
   sllfreeflag v'20 v'21 **
   AOSTime (Vint32 v'18) **
   AGVars ** APthreadAttr v'64 v'65 v'66 ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'53 
                           (* Aisr empisr **
                            * Aie false **
                            * Ais nil **
                            * Acs (true :: nil) ** *)
                  )).
      clear.
      intro; intros.
      sep lifts (4:: 6::nil)%nat. 
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.
      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (cur_tcb_blk, Int.zero) (v'53, wait (hle2wait x (v'15, Int.zero)) i13 , x0) mmm tcbmap).
      apply tcb_get_join.
      unfold get, sig, join in *; simpl in *.
      unfold get, sig, join in *; simpl in *.
      go.

      destruct H101 as (tcbmap_left & tcbmapleft_join_hyp).


      eapply seq_rule.
      eapply  derive_delself_rule.

        
      apply goodlinv.
       (* goodlinv *)
      go.
      unfold AEventData.
      destruct x22; go.
      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.

      exact tcbmapleft_join_hyp.
      intro; intros.
      split.
      sep_get_rv.
      unfold p_local in H101.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.

      rewrite app_nil_l.
      unfold1 tcbdllflag.
      unfold1 dllsegflag.
      hoare unfold.
      hoare lift 4%nat pre.
      unfold p_local at 2.
      unfold OSLInv at 3.
      unfold LINV.
      unfold1 dllseg.
      hoare unfold.
      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)
      sep combine ( get_off_addr (cur_tcb_blk, Int.zero) ($ 24)  ) in H102.
      eauto.

      hoare lift 2%nat pre.
      eapply seq_rule.
      eapply assign_rule'.
      Focus 2.

      intro; intros.
      split.
      eapply field_asrt_impl.
      Focus 3.
      sep cancel 12%nat 1%nat.
      eauto.
      reflexivity.
      reflexivity.
      sep get rv.
      eapply eq_int; auto.

      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.
      sep cancel 50%nat 1%nat.
      simpl; auto.
      splits; eauto.
      unfolds; auto.
      

      eapply backward_rule1.
      intro; intros.
      sep lifts (7::9::nil)%nat in H102.
      eapply add_a_isr_is_prop in H102.
      eauto.
      hoare lift 4%nat pre.
      eapply seq_rule.

      eapply excrit1_rule'_ISnil_ISRemp''.
      rename v'22 into v'48.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      unfold p_local, OSLInv.
      unfold LINV.
      sep pauto.
      sep cancel 2%nat 1%nat.
      sep cancel CurTid.
      unfold OSInv.
      sep pauto.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
      sep cancel APthreadAttr.
      unfold AECBList.

      instantiate (17 := (x11 ++ (Vint32 i7 :: Vint32 v'50 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil,
                                 (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
                                                 (val_inj
                                                    (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
                                ) :: x15)).
      instantiate (16 :=(x23 ++ x22 :: x24) ).
      sep pauto.
      eapply evsllseg_merge.
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H80).
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H81).

      unfold1 evsllseg .
      sep pauto.
      unfold AEventNode.
      sep cancel evsllseg.
      sep cancel evsllseg.
      unfold AOSEvent.
      unfold node.
      unfold AOSEventTbl.
      sep pauto.
      sep cancel Aarray.
      sep lift 2%nat.
      eapply AED_changegrp.
      sep cancel AEventData.
      unfold Astruct.
      unfold OS_EVENT.
      unfold Astruct'.
      sep normal.
      sep cancel 14%nat 2%nat.
      repeat sep cancel 14%nat 1%nat.
      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel 12%nat 1%nat.
      sep cancel 16%nat 1%nat.
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold AOSTCBList'.
      eapply intro_or_r.
      sep pauto.
      unfold tcblist.
      instantiate ( 5 := nil).
      instantiate ( 3 := l2').

      instantiate ( 4 := (v'48
                             :: Vnull
                             :: x35
                             :: x34
                             :: Vint32 i15
                             :: Vint32 i14
                             :: Vint32 i12
                             :: Vint32 i11
                             :: Vint32 i10
                             :: Vint32 i9 :: Vint32 i :: nil)).
     
      
(* ** ac:       Print  TCB_Not_In . *)
      unfold TCB_Not_In.
      sep pauto.
      (* unfold tcbdllseg. *)
      (* SearchAbout dllseg. *)
      eapply tcbdllseg_compose.
      unfold tcbdllseg.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 9%nat 1%nat.
      sep cancel 9%nat 1%nat.
      unfold1 tcbdllflag.
      unfold tcbdllflag in H102.
      rewrite app_nil_l.
      unfold1 dllsegflag.
      unfold1 dllsegflag in H102.
      sep normal in H102.
      sep pauto.
      (* inverts H126. *)
      sep cancel dllsegflag.
      sep cancel 2%nat 1%nat.
      (* freelist *)
      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_r. 
      unfold TCBFree_Eq.
      sep pauto.
      sep cancel sll.
      sep cancel sllfreeflag.
      eauto.
      go.
      eapply isptr_is_definitely_ptr.
      eapply sll_head_isptr.
      instantiate (5:=s).
      sep cancel sll.
      go.
      unfolds.
      {
        do 6 eexists.
        splits.
        go.
        go.
        go.
        go.
        go.
        go.
        go.
        splits.
        go.
        go.
        go.
        go.
        left; auto.
      repeat tri_exists_and_solver1.
      go.
      }
      eexists; go.
           {
        unfolds in H6.
        simpljoin.
        clear -tcbmapleft_join_hyp H122.
        unfolds.
        unfolds in tcbmapleft_join_hyp.
        intro.
        simpljoin.

        unfolds in H122.
        assert (x1 <> (cur_tcb_blk, Int.zero)).
        intro.
        subst.
(* ** ac:         SearchAbout join. *)
(* ** ac:         SearchAbout TcbMod.join. *)
        eapply TcbMod.map_join_get_some .
        
        auto.
        eauto.
        2: exact H.
        (* instantiate (1:=(v'43, x, x0)). *)
        unfold get in *; simpl in *.
        unfold sig in *; simpl in *.
        eapply TcbMod.get_a_sig_a.
        go.
        unfold join, sig, get in *; simpl in *.
        assert (TcbMod.get tcbmap x1 =Some (v'53, x2, x3) ).
        go.
        assert (TcbMod.get tcbmap (cur_tcb_blk, Int.zero) =Some(v'53, wait (hle2wait x (v'15, Int.zero)) i13,
                             x0)  ).
        go.
        lets bb: H122 H0 H1 H2.
        apply bb.
        reflexivity.

      }
 
      go.
      go.
      intro;tryfalse.
      go.
      go.
      {
        split.
        rewrite ptr_in_tcblist_app.
        2: simpl; auto.
        intro.
        destruct H121.
        simpl in H121.
        exact H121.
        simpl (val_inj (get_last_tcb_ptr nil (Vptr (v'16, Int.zero)))) in H121.
        gen H121.
        eapply distinct_is_unique_second.
        3: eapply  TCBLP_imply_dictinct_list .
        2:instantiate ( 1 := (Vptr (v'16, Int.zero)
      :: Vnull
         :: Vptr (v'15, Int.zero)
            :: x0
               :: Vint32 i13
                  :: Vint32 x21
                     :: Vint32 v'53
                        :: Vint32 (v'53&ᵢ$ 7)
                           :: Vint32 (v'53 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                              :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) :: nil)).
        2: go.
        instantiate (1 :=  nil).
        simpl; auto.
(* ** ac:         SearchAbout (nil ++ _). *)
        rewrite app_nil_l.

         exact backup.
         simpl.
         auto.
         eauto.
      }
       (* from tcblist_p, get they are all different? *)
      {
        rewrite app_nil_l.
        rewrite app_nil_l in H25.
(* ** ac:         Print  R_PrioTbl_P . *)
        

        eapply tcblist_p_hold_for_del_a_tcb_at_head.
        lia.
        2:go.
        2:go.
        3: exact H25.
        2: exact tcbmapleft_join_hyp.
        unfolds in H105.
        simpljoin; assumption.
      }
      split.
      assumption.
      eapply (H68 _ H55).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.

        
(* OSTimeDlyPure.update_rtbl_tcblist_hold: *)
             
      {
        eapply  r_priotbl_p_hold_for_del_a_tcb.
        lia.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .

      }
       (* r_priotbl_p hold for deleting a tcb *)
      
{
  eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
  lia.
  rewrite Int.repr_unsigned.
  reflexivity.

  rewrite Int.repr_unsigned.
  reflexivity.

  2: assumption.
  unfold nat_of_Z.
  apply nv'2nv.
  
  assumption.
  intro; tryfalse.
  
      }

       (* rl_rtbl_ptbl_p hold for deleting a tcb *)

      split.
      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.
      go.
      go.
      go.
      go.
      clear -H96 H121.
      unfolds in H96.
      change Byte.max_unsigned with 255%Z in * .
      math simpl in H96.
      lia.
      go.

      {
        eapply ECBLP_hold4del_a_tcb; eauto.
        3:exact tcbmapleft_join_hyp.
        clear -H6; unfolds in H6; tauto.
        clear -H6; unfolds in H6; tauto.
      }

        
      eapply poi_is_rtep.

       

      {
        eapply poi_RHTEP_hold_for_del_a_tcb.
        assumption.
        go.
        eapply tcbmapleft_join_hyp.
        go.
        clear -H2 H61 H62; unfolds; splits; auto.
      }
        
      
       (* change to poi, *)
(* from some_pure_hyp : forall (eid : tidspec.A) (pr : int32) 
 *                     (tid0 : tid) (opr : int32) (wls : waitset),
 *                   EcbMod.get ecbmap eid =
 *                   Some (absmutexsem pr (Some (tid0, opr)), wls) ->
 *                   tid0 <> (cur_tcb_blk, Int.zero)
 * get rh_te_p hold for deleting a tcb *)
      splits; go.
      unfolds; auto.
      go.
      hoare forward.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.

      hoare unfold.

      inverts H102.
      assert (Hopv: v'74 = Vint32 (Int.repr OS_NO_ERR) \/ v'74 <>Vint32 (Int.repr OS_NO_ERR)) by tauto.
      destruct Hopv.
    
      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskdel_succ.
      go.
      go.


      hoare forward.
      splits.
      eauto.
      eauto.
      
      change OS_NO_ERR with 0.
      rewrite Int.unsigned_repr. lia.
      rewrite max_unsigned_val. lia.

      change OS_NO_ERR with 0.
      rewrite Int.unsigned_repr.
      change Byte.max_unsigned with 255. lia.
      rewrite max_unsigned_val. lia.

      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskdel_succ_abt.
      can_change_aop_solver.
      auto.
    
      eapply absabort_rule.

    }

    (* delete some tcb other than current, at head *)
    {
      eapply backward_rule1.
      Set Printing Depth 999.
      intro; intros.
      Set Printing Depth 999.
(* ** ac:       Show. *)
      instantiate ( 1 := (
        <|| spec_del (Vint32 v'53);; isched;; taskdel_succ (|v'74 :: nil|);; v'73 ||>  **
                              HTCBList tcbmap **
                              HCurTCB (cur_tcb_blk, Int.zero) **
                              OS [ empisr, false, nil, (true::nil)] **

                           (* <|| spec_del (Vint32 v'53);; isched;; END Some (V$ NO_ERR) ||>  ** *)
            A_dom_lenv
              ((prio, Int8u)
               :: (pevent, OS_EVENT ∗)
                  :: (ptcb, OS_TCB ∗)
                     :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
            GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
            LV ptcb @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
            Astruct (todelblock, Int.zero) OS_TCB_flag
              (v'20
               :: Vnull
                  :: Vnull
                     :: x0
                        :: V$ 0
                           :: V$ OS_STAT_RDY
                              :: Vint32 v'53
                                 :: Vint32 (v'53&ᵢ$ 7)
                                    :: Vint32 (v'53 >>ᵢ $ 3)
                                       :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                          :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3))
                                             :: nil) **
            GV OSTCBList @ OS_TCB ∗ |-> Vptr (v'16, Int.zero) **
            LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (v'16, Int.zero) **
            Astruct (v'16, Int.zero) OS_TCB_flag
              (v'14
               :: Vnull
                  :: x35
                     :: x34
                        :: Vint32 i15
                           :: Vint32 i14
                              :: Vint32 i12
                                 :: Vint32 i11
                                    :: Vint32 i10
                                       :: Vint32 i9 :: Vint32 i :: nil) **
            dllseg v'14 (Vptr (v'16, Int.zero)) v'12 Vnull l2' OS_TCB_flag
              (fun vl : vallist => nth_val 1 vl)
              (fun vl : vallist => nth_val 0 vl) **
            GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
              (update_nth_val (Z.to_nat (Int.unsigned v'53)) priotbl Vnull) **
            PV vhold @ Int8u |-> v'7 **
            Aarray v'38 (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
              (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
                 (val_inj
                    (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
            PV (v'15, Int.zero +ᵢ  $ 1) @ Int8u |-> Vint32 v'50 **
            PV (v'15, Int.zero) @ Int8u |-> Vint32 i7 **
            PV (v'15,
               (Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
               $ Z.of_nat (typelen Int8u)) @ Int16u |-> 
            Vint32 i8 **
            PV (v'15,
               ((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
                $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) @
            (Void) ∗ |-> x29 **
            PV (v'15,
               ((((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
                  $ Z.of_nat (typelen Int8u)) +ᵢ  
                 $ Z.of_nat (typelen Int16u)) +ᵢ
                $ Z.of_nat (typelen (Void) ∗)) +ᵢ
               $ Z.of_nat (typelen (Tarray Int8u ∘ OS_EVENT_TBL_SIZE))) @
            STRUCT os_event ⋆ |-> v'6 **
            AEventData
              (Vint32 i7
               :: Vint32 v'28 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil) x22 **
            evsllseg v'6 Vnull x15 x24 **
            evsllseg v'8 (Vptr (v'15, Int.zero)) x11 x23 **
            GV OSEventList @ OS_EVENT ∗ |-> v'8 **
            HECBList (EcbMod.set ecbmap (v'15, Int.zero)
      (x, remove_tid (todelblock, Int.zero) x14))

            **
            (* HTCBList tcbmap ** *)
            HTime v'18 **
            (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
            LV pevent @ OS_EVENT ∗ |-> Vptr (v'15, Int.zero) **
            GV OSRdyGrp @ Int8u |-> Vint32 v'40 **
            GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
              (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
                 (val_inj
                    (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
            dllseg v'9 Vnull Vnull (Vptr (todelblock, Int.zero)) nil
              OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
              (fun vl : vallist => nth_val 0 vl) **
            GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
            (* Aie false ** *)
            (* Ais nil ** *)
            (* Acs (true :: nil) ** *)
            (* Aisr empisr ** *)
            tcbdllflag v'9
              (nil ++
               (Vptr (v'16, Int.zero)
                :: Vnull
                   :: Vptr (v'15, Int.zero)
                      :: x0
                         :: Vint32 i13
                            :: Vint32 x21
                               :: Vint32 v'53
                                  :: Vint32 (v'53&ᵢ$ 7)
                                     :: Vint32 (v'53 >>ᵢ $ 3)
                                        :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                           :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3))
                                              :: nil)
               :: (v'14
                   :: Vptr (todelblock, Int.zero)
                      :: x35
                         :: x34
                            :: Vint32 i15
                               :: Vint32 i14
                                  :: Vint32 i12
                                     :: Vint32 i11
                                        :: Vint32 i10
                                           :: Vint32 i9 :: Vint32 i :: nil)
                  :: l2') **
            G& OSPlaceHolder @ Int8u == vhold **
            (* A_isr_is_prop ** *)
            p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
            LV self @ Int8u |-> (V$ 0) **
            AOSEventFreeList v'3 **
            AOSQFreeList v'4 **
            AOSQFreeBlk v'5 **
            AOSMapTbl **
            AOSUnMapTbl **
            AOSIntNesting **
            sll v'20 v'21 OS_TCB_flag (fun vl : vallist => nth_val 0 vl) **
            sllfreeflag v'20 v'21 **
            AOSTime (Vint32 v'18) **
            AGVars ** APthreadAttr v'64 v'65 v'66 ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'53
                        )).
   
      sep lifts (4:: 6::nil)%nat. 
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.
      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (todelblock, Int.zero) (v'53, wait (hle2wait x (v'15, Int.zero)) i13 , x0) mmm tcbmap).
      apply tcb_get_join.
      unfold get, sig, join in H11; simpl in H11.
      unfold get, sig, join in H11, H20; simpl in H11, H20.
      go.

      destruct H102 as (tcbmap_left & tcbmapleft_join_hyp).
      rename H101 into not_cur_hyp.


      eapply seq_rule.
      eapply  derive_delother_rule.
      apply goodlinv.
       (* goodlinv *)
      go.
      unfold AEventData.
      destruct x22; go.
      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.
      exact tcbmapleft_join_hyp.
      clear -H3.
      unfolds in H3.
      unfolds.
      simpljoin; eauto.

      clear -not_cur_hyp.
      intro H; inverts H; apply not_cur_hyp; reflexivity.

      
      intro; intros.
      split.
      sep_get_rv.
      unfold p_local in H101.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.

      rewrite app_nil_l.
      unfold1 tcbdllflag.
      unfold1 dllsegflag.
      hoare unfold.
      hoare lift 4%nat pre.
      unfold OSLInv at 3.
      unfold LINV.
      unfold1 dllseg.
      hoare unfold.
      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)
      sep combine ( get_off_addr (todelblock, Int.zero) ($ 24)  ) in H101.
      eauto.

      (* hoare lift 2%nat pre. *)
      hoare lift 4%nat pre.
      eapply seq_rule.
      eapply assign_rule'.
      Focus 2.

      intro; intros.
      split.
      eapply field_asrt_impl.
      Focus 3.
      sep cancel 12%nat 1%nat.
      eauto.
      reflexivity.
      reflexivity.
      sep get rv.
      eapply eq_int; auto.

      linv_solver.

      rename v'23 into v'49.

      eapply backward_rule1.
      intro; intros.
      sep lifts (7::9::nil)%nat in H101.
      eapply add_a_isr_is_prop in H101.
      eauto.
      hoare lift 4%nat pre.
      eapply seq_rule.

      eapply excrit1_rule'_ISnil_ISRemp''.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel p_local.
      eapply poi_OSINV_imply_OSInv.

      unfold poi_OSINV.

      sep pauto.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
      sep cancel APthreadAttr.
      unfold AECBList.
      instantiate (14 := (x11 ++ (Vint32 i7 :: Vint32 v'50 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil,
                                 (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
                                                 (val_inj
                                                    (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
                                ) :: x15)).
      instantiate (13 :=(x23 ++ x22 :: x24) ).

      sep pauto.
      eapply evsllseg_merge.

      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H80).
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H81).
      unfold1 evsllseg .
      sep pauto.
(* ** ac:       Print AEventNode. *)
      unfold AEventNode.
      sep cancel evsllseg.
      sep cancel evsllseg.
      unfold AOSEvent.
      unfold node.
      unfold AOSEventTbl.
      sep pauto.
      sep cancel Aarray.

      sep lift 2%nat.
      eapply AED_changegrp.
      sep cancel AEventData.
      unfold Astruct.
      unfold OS_EVENT.
      unfold Astruct'.
      sep normal.
      sep cancel 14%nat 2%nat.
      repeat sep cancel 14%nat 1%nat.
      unfold AOSTCBPrioTbl.
      sep pauto.
      idtac.
      idtac.
      sep cancel 12%nat 1%nat.
      sep cancel 16%nat 1%nat.
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold poi_AOSTCBList.
      
      sep pauto.
      instantiate (4 := (
                          (v'49
                             :: Vnull
                             :: x35
                             :: x34
                             :: Vint32 i15
                             :: Vint32 i14
                             :: Vint32 i12
                             :: Vint32 i11
                             :: Vint32 i10
                             :: Vint32 i9 :: Vint32 i :: nil)
                            :: l2')).

      unfold tcbdllseg.
      unfold tcbdllflag.
      unfold1 dllsegflag.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 2%nat 1%nat.
      sep cancel dllsegflag.
      sep cancel dllseg.
      sep cancel 7%nat 1%nat.

      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_l. 
      unfold TCBFree_Not_Eq.
      sep pauto.
      instantiate (2 := (
                           (v'20
                              :: Vnull
                              :: Vnull
                              :: x0
                              :: V$ 0
                              :: V$ OS_STAT_RDY
                              :: Vint32 v'53
                              :: Vint32 (v'53&ᵢ$ 7)
                              :: Vint32 (v'53 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                              :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3))
                              :: nil) ::v'21
                                      
                         )).
      unfold sll.
      unfold sllfreeflag.
      unfold1 sllseg.
      unfold1 sllsegfreeflag.
      unfold node.
      unfold sll in H101.
      unfold sllfreeflag in H101.
      sep pauto.
      sep cancel sllseg.
      sep cancel sllsegfreeflag.
      
      sep cancel 1%nat 1%nat.
      sep cancel Astruct.
      eauto.
      go.
      go.
      apply isptr_is_definitely_ptr.
      eapply sllseg_head_isptr.
      instantiate (5:=s).
      sep cancel sllseg.
      eauto.

      go.
      intro; tryfalse.
      go.
      go.
      go.
      intro; tryfalse.
      {

        rewrite app_nil_l in H25.
        eapply tcblist_p_hold_for_del_a_tcb_at_head.
        lia.
        2:go.
        2:go.
        3: exact H25.
        2: exact tcbmapleft_join_hyp.
        unfolds in H105.
        simpljoin; assumption.
      }
       (* tcblist_p hold for deleting a tcb *)
      {

        clear -H24 not_cur_hyp .

        eapply ptr_in_tcbdllseg_change_head.
        Focus 2.
                eapply ptr_in_tcbdllseg_not_head.
        rewrite app_nil_l in H24.
        2: eauto.
        simpl; auto.
        intro; tryfalse.
        unfold V_OSTCBNext.
        reflexivity.
      }

      
       (* from tcblist_p, get they are all different? *)
      split.
      assumption.
      eapply (H68 _ H55).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.

      {
        eapply r_priotbl_p_hold_for_del_a_tcb.
        
        lia.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .
      }
       (* r_priotbl_p hold for deleting a tcb *)
      {
        eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
        lia.
        rewrite Int.repr_unsigned.
        reflexivity.

        rewrite Int.repr_unsigned.
        reflexivity.

        2: assumption.
        unfold nat_of_Z.
        apply nv'2nv.
        
        assumption.
        intro; tryfalse.
      }
       (* rl_rtbl_ptbl_p hold for deleting a tcb *)

      split.

      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.
      go.
      go.
      go.
      go.
      go.
      clear -H96 H103.
      unfolds in H96.
      change Byte.max_unsigned with 255%Z in * .
      math simpl in H96.
      lia.
      go.
      {

        eapply ECBLP_hold4del_a_tcb; eauto.
        3:exact tcbmapleft_join_hyp.
        clear -H6; unfolds in H6; tauto.
        clear -H6; unfolds in H6; tauto.
        
      }
       (* from H101 : RL_Tbl_Grp_P
           (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
              (val_inj
                 (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
           (Vint32 v'53), ECBList_P holds for deleting a tcb *)
      {

      eapply poi_is_rtep.
        
        eapply poi_RHTEP_hold_for_del_a_tcb.
        assumption.
        go.
        eapply tcbmapleft_join_hyp.
        go.
        clear -H2 H61 H62; unfolds; splits; auto.
      }
       (* change to poi,
from some_pure_hyp : forall (eid : tidspec.A) (pr : int32) 
                    (tid0 : tid) (opr : int32) (wls : waitset),
                  EcbMod.get ecbmap eid =
                  Some (absmutexsem pr (Some (tid0, opr)), wls) ->
                  tid0 <> (cur_tcb_blk, Int.zero)
get rh_te_p hold for deleting a tcb
              *)
      go.
      hoare forward.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.

      hoare unfold.

      inverts H101.
      assert (Hopv: v'74 = Vint32 (Int.repr OS_NO_ERR) \/ v'74 <>Vint32 (Int.repr OS_NO_ERR)) by tauto.
      destruct Hopv.
    
      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskdel_succ.
      go.
      go.


      hoare forward.
      splits.
      eauto.
      eauto.
      
      change OS_NO_ERR with 0.
      rewrite Int.unsigned_repr. lia.
      rewrite max_unsigned_val. lia.

      change OS_NO_ERR with 0.
      rewrite Int.unsigned_repr.
      change Byte.max_unsigned with 255. lia.
      rewrite max_unsigned_val. lia.

      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskdel_succ_abt.
      can_change_aop_solver.
      auto.
    
      eapply absabort_rule.


    }
    (* delete some tcb in the middle of the tcblist *)
  }
  {
    destruct H42.
    hoare_assert_pure False.
    (* hw **)
    subst v'13.


    eapply dllseg_tail_not_null.
    instantiate (10:=s0).
    sep pauto.
    sep cancel 26%nat 1%nat.
    eauto.
    hoare unfold.
    inverts H101.

    destruct H42 as (prev_tcb_ptr & eqprev); subst v'13.
    (* rename x11 into prev_tcb_ptr. *)

    eapply backward_rule1.
    intro; intros.
    sep lift 26%nat in H42.
    rewrite dllseg_split_node_tail in H42.
    
    eauto.
    unfold node.
    hoare unfold.
    rename v'10 into v'13.
    rename v'22 into v'48.
    rename v'11 into v'43.
    rename v'48 into prev_tcb_block.
    rename v'16 into next_tcb_block.

    hoare forward.
    (* intro; tryfalse. *)
    go.
    (* intro; tryfalse. *)
    hoare unfold.
    instantiate (1:= Afalse).
    false.

    hoare unfold.
    clear H42.
    hoare forward.
    (* intro; tryfalse. *)
    go.
    hoare forward.
    (* intro; tryfalse. *)
    go.
    
    hoare forward.
    (* intro; tryfalse. *)
    go.
    
    hoare forward.
    (* intro; tryfalse. *)
    go.

    hoare forward.
    hoare unfold.
    unfold   AOSTCBFreeList.
    hoare normal pre.
    hoare forward.
    eapply isptr_match_eq_true.
    eapply sll_head_isptr.
    instantiate (5 := s).
    sep cancel sll.
    eauto.

    hoare forward.
    assert (todelblock = cur_tcb_blk \/ todelblock <> cur_tcb_blk) by tauto. 
    destruct H102.
    (* delete current *)
    {
      subst todelblock.
      (* unfold get in H16; simpl in H16. *)
      rewrite H23 in kitty.

      eapply backward_rule1.
      instantiate (1:=
                     (
                       <|| spec_del (Vint32 v'53);; isched;; taskdel_succ (|v'74 :: nil|);; v'73 ||>  **
                           HTCBList tcbmap **
                           HCurTCB (cur_tcb_blk, Int.zero) **
                           OS [ empisr, false, nil, (true::nil)] **

  (* <|| spec_del (Vint32 v'53);; isched;; END Some (V$ NO_ERR) ||>  ** *)
   A_dom_lenv
     ((prio, Int8u)
      :: (pevent, OS_EVENT ∗)
         :: (ptcb, OS_TCB ∗)
            :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
   GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
   LV ptcb @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
   Astruct (cur_tcb_blk, Int.zero) OS_TCB_flag
     (v'20
      :: Vptr (prev_tcb_block, Int.zero)
         :: Vnull
            :: x0
               :: V$ 0
                  :: V$ OS_STAT_RDY
                     :: Vint32 v'53
                        :: Vint32 (v'53&ᵢ$ 7)
                           :: Vint32 (v'53 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) :: nil) **
   LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (next_tcb_block, Int.zero) **
   Astruct (next_tcb_block, Int.zero) OS_TCB_flag
     (v'14
      :: Vptr (prev_tcb_block, Int.zero)
         :: x35
            :: x34
               :: Vint32 i15
                  :: Vint32 i14
                     :: Vint32 i12
                        :: Vint32 i11
                           :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil) **
   Astruct (prev_tcb_block, Int.zero) OS_TCB_flag
     (Vptr (next_tcb_block, Int.zero)
      :: v'13
         :: x36
            :: x33
               :: Vint32 i22
                  :: Vint32 i21
                     :: Vint32 i20
                        :: Vint32 i19
                           :: Vint32 i18 :: Vint32 i17 :: Vint32 i16 :: nil) **
   dllseg v'9 Vnull v'13 (Vptr (prev_tcb_block, Int.zero)) v'43 OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   dllseg v'14 (Vptr (next_tcb_block, Int.zero)) v'12 Vnull l2' OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
     (update_nth_val (Z.to_nat (Int.unsigned v'53)) priotbl Vnull) **
   PV vhold @ Int8u |-> v'7 **
   Aarray v'38 (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
        (val_inj (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
   PV (v'15, Int.zero +ᵢ  $ 1) @ Int8u |-> Vint32 v'50 **
   PV (v'15, Int.zero) @ Int8u |-> Vint32 i7 **
   PV (v'15,
      (Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
      $ Z.of_nat (typelen Int8u)) @ Int16u |-> Vint32 i8 **
   PV (v'15,
      ((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
       $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) @
   (Void) ∗ |-> x29 **
   PV (v'15,
      ((((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
         $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) +ᵢ
       $ Z.of_nat (typelen (Void) ∗)) +ᵢ
      $ Z.of_nat (typelen (Tarray Int8u ∘ OS_EVENT_TBL_SIZE))) @
   STRUCT os_event ⋆ |-> v'6 **
   AEventData
     (Vint32 i7 :: Vint32 v'28 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil) x22 **
   evsllseg v'6 Vnull x15 x24 **
   evsllseg v'8 (Vptr (v'15, Int.zero)) x11 x23 **
   GV OSEventList @ OS_EVENT ∗ |-> v'8 **
   (* HECBList ecbmap ** *)

   HECBList
   (EcbMod.set ecbmap (v'15, Int.zero)
        (x, remove_tid (cur_tcb_blk, Int.zero) x14)) **
   (* HTCBList tcbmap ** *)
   HTime v'18 **
   (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
   LV pevent @ OS_EVENT ∗ |-> Vptr (v'15, Int.zero) **
   GV OSRdyGrp @ Int8u |-> Vint32 v'40 **
   GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
        (val_inj (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
   GV OSTCBList @ OS_TCB ∗ |-> v'9 **
   GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
   (* Aie false ** *)
   (* Ais nil ** *)
   (* Acs (true :: nil) ** *)
   (* Aisr empisr ** *)
   tcbdllflag v'9
     ((v :: l1') ++
      (Vptr (next_tcb_block, Int.zero)
       :: Vptr (prev_tcb_block, Int.zero)
          :: Vptr (v'15, Int.zero)
             :: x0
                :: Vint32 i13
                   :: Vint32 x21
                      :: Vint32 v'53
                         :: Vint32 (v'53&ᵢ$ 7)
                            :: Vint32 (v'53 >>ᵢ $ 3)
                               :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                  :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) :: nil)
      :: (v'14
          :: Vptr (cur_tcb_blk, Int.zero)
             :: x35
                :: x34
                   :: Vint32 i15
                      :: Vint32 i14
                         :: Vint32 i12
                            :: Vint32 i11
                               :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
         :: l2') **
   G& OSPlaceHolder @ Int8u == vhold **
   (* A_isr_is_prop ** *)
   p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
   LV self @ Int8u |-> (V$ 0) **
   AOSEventFreeList v'3 **
   AOSQFreeList v'4 **
   AOSQFreeBlk v'5 **
   AOSMapTbl **
   AOSUnMapTbl **
   AOSIntNesting **
   sll v'20 v'21 OS_TCB_flag V_OSTCBNext **
   sllfreeflag v'20 v'21 **
   AOSTime (Vint32 v'18) **
   AGVars ** APthreadAttr v'64 v'65 v'66 ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'53)).
     
    
      clear.
      intro; intros.
      sep lifts (4:: 6::nil)%nat. 
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.

      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (cur_tcb_blk, Int.zero) (v'53, wait (hle2wait x (v'15, Int.zero)) i13 , x0) mmm tcbmap).
      apply tcb_get_join.
      unfold get, sig, join in *; simpl in *.
      unfold get, sig, join in *; simpl in *.
      go.

      destruct H102 as (tcbmap_left & tcbmapleft_join_hyp).


      eapply seq_rule.
      eapply derive_delself_rule.
      apply goodlinv.

       (* goodlinv *)
      go.
      unfold AEventData.
      destruct x22; go.
      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.
      exact tcbmapleft_join_hyp.
      intro; intros.
      split.
      sep_get_rv.
      unfold p_local in H102.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.
(* ** ac:       Check dllsegflag_split. *)
      hoare lift 36%nat pre.
      eapply backward_rule1.
      eapply dllsegflag_split.
      hoare_split_pure_all.
      unfold dllsegflag at 2.
      fold dllsegflag .
      hoare_split_pure_all.
      inverts H130.
      inverts H103.
      inverts H131.
      inverts H103.
      rewrite H101.

      rename v'11 into v'47.



      hoare_assert_pure ( (fun vl : vallist => nth_val 0 vl) (Vptr (cur_tcb_blk, Int.zero)
                                                                   :: v'13
                                                                   :: x36
                                                                   :: x33
                                                                   :: Vint32 i22
                                                                   :: Vint32 i21
                                                                   :: Vint32 i20
                                                                   :: Vint32 i19
                                                                   :: Vint32 i18
                                                                   :: Vint32 i17 :: Vint32 i16 :: nil) = Some (Vptr v'47) ).
      eapply dllsegflag_last_next_is_endstnl.
      instantiate (4 := s0).
      sep cancel 4%nat 1%nat.
      eauto.

      hoare_split_pure_all.
      inverts H102.

      
      
      (* rewrite app_nil_l. *)
      (* hoare unfold. *)
      (* hoare lift 4%nat pre. *)
      unfold p_local at 2.
      unfold OSLInv at 3.
      unfold LINV.
      hoare_split_pure_all.
      (* unfold1 dllseg. *)
      (* hoare unfold. *)
      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)
      sep combine ( get_off_addr (cur_tcb_blk, Int.zero) ($ 24)  ) in H130.
      eauto.

      hoare lift 5%nat pre.
      eapply seq_rule.
      eapply assign_rule'.
      Focus 2.

      intro; intros.
      split.
      eapply field_asrt_impl.
      Focus 3.
      sep cancel 13%nat 1%nat.
      eauto.
      reflexivity.
      reflexivity.
      sep get rv.
      eapply eq_int; auto.

      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.
      sep cancel 53%nat 1%nat.
      simpl; auto.
      splits; eauto.
      unfolds; auto.
      

      eapply backward_rule1.
      intro; intros.
      sep lifts (8::10::nil)%nat in H130.
      eapply add_a_isr_is_prop in H130.
      eauto.
      hoare lift 4%nat pre.
      eapply seq_rule.

      eapply excrit1_rule'_ISnil_ISRemp''.
      rename v'23 into v'52.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      unfold p_local, OSLInv.
      unfold LINV.
      sep pauto.
      sep cancel 2%nat 1%nat.
      sep cancel CurTid.
      unfold OSInv.
      sep pauto.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
      sep cancel APthreadAttr.
      unfold AECBList.
instantiate (17 := (x11 ++ (Vint32 i7 :: Vint32 v'50 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil,
                                 (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
                                                 (val_inj
                                                    (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
                                ) :: x15)).
      instantiate (16 :=(x23 ++ x22 :: x24) ).

      sep pauto.
      eapply evsllseg_merge.
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H80).
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H81).


      unfold1 evsllseg .
      sep pauto.
      unfold AEventNode.
      sep cancel evsllseg.
      sep cancel evsllseg.
      unfold AOSEvent.
      unfold node.
      unfold AOSEventTbl.
      sep pauto.
      sep cancel Aarray.

      sep lift 2%nat.
      eapply AED_changegrp.
      sep cancel AEventData.
      unfold Astruct.
      unfold OS_EVENT.
      unfold Astruct'.
      sep normal.
      sep cancel 16%nat 2%nat.
      repeat sep cancel 16%nat 1%nat.
      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel 20%nat 2%nat.
      sep cancel 14%nat 1%nat.
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold AOSTCBList'.
      eapply intro_or_r.
      sep pauto.
      unfold tcblist.

      instantiate ( 5 :=(v'43 ++
                               (Vptr (next_tcb_block, Int.zero)
                                     :: v'13
                                     :: x36
                                     :: x33
                                     :: Vint32 i22
                                     :: Vint32 i21
                                     :: Vint32 i20
                                     :: Vint32 i19
                                     :: Vint32 i18
                                     :: Vint32 i17 :: Vint32 i16 :: nil)
                               :: nil)  ).

      instantiate ( 3 := l2').
      instantiate ( 4 :=
                      (v'52
                         :: Vptr (prev_tcb_block, Int.zero)
                         :: x35
                         :: x34
                         :: Vint32 i15
                         :: Vint32 i14
                         :: Vint32 i12
                         :: Vint32 i11
                         :: Vint32 i10
                         :: Vint32 i9 :: Vint32 i :: nil)).


      unfold TCB_Not_In.
      sep pauto.
      eapply tcbdllseg_compose.
      unfold tcbdllseg.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 10%nat 1%nat.
      sep cancel 12%nat 1%nat.

      eapply dllseg_is_poi.
      eapply split_poillseg.
      sep eexists.
      rewrite <- dllseg_is_poi.
      sep lift 2%nat.
      rewrite <- dllseg_is_poi.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 10%nat 1%nat.
      sep cancel dllseg.


      unfold tcbdllflag.
      sep lift 4%nat in H130.
      rewrite dllsegflag_is_poi in H130.
      apply split_poillseg in H130.

      apply dllsegflag_is_poi.
      sep pauto.
      apply split_poillseg.
      sep eexists.
      apply split_poillseg.
      sep eexists.
      sep cancel 1%nat 1%nat.
      unfold1 @poi_llseg in *.

(* Here sep_pure fails *)
(*
Ltac sep_semiauto_nosplit2 :=
    intros;
    match goal with
      | H:?s |= _
        |- ?s |= _ =>
        try (solve [ exact H | apply atrue_intro ]); sep normal in H; sep
                                                                        destruct H;  (try progress ssplit_apure_in H); subst;
        repeat match goal with
                 | H0 : exists _ , _ |- _ => destruct H0
                 | H0 : _ /\ _ |- _ => destruct H0
               end;
        (let Hp := type of H in
         let H' := fresh in
         assert Hp as H' by exact H; clear H; rename H' into H); sep normal;
        sep eexists; ssplit_apure(*;
        match goal with
          | |- _ |= _ => idtac 1;scancel
          | _ => idtac 2;sep_pure
        end*)
      | _ => idtac
    end.
*)    
  sep_semiauto_nosplit2.
  1: scancel.
  2: sep normal in H130;
        sep destruct H130;
        sep split in H130;
        subst.

      sep lift 2%nat.
      rewrite <- dllsegflag_is_poi.
      sep cancel dllsegflag.
      instantiate (3 := x16).
      sep cancel 1%nat 2%nat.
      sep cancel 2%nat 1%nat.

      (* freelist *)
      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_r. 
      unfold TCBFree_Eq.
      sep pauto.
      sep cancel sll.
      sep cancel sllfreeflag.
      eauto.
      go.
      eapply isptr_is_definitely_ptr.
      eapply sll_head_isptr.
      instantiate (5:=s).
      sep cancel sll.
      go.
      unfolds.
      {
        do 6 eexists.
        splits.
        go.
        go.
        go.
        go.
        go.
        go.
        go.
        splits.
        go.
        go.
        go.
        go.
        left; auto.
        repeat tri_exists_and_solver1.
        go.
      }
      eexists; go.
{
        unfolds in H6.
        simpljoin.
        clear -tcbmapleft_join_hyp H134.
        unfolds.
        unfolds in tcbmapleft_join_hyp.
        intro.
        simpljoin.

        unfolds in H134.
        assert (x1 <> (cur_tcb_blk, Int.zero)).
        intro.
        subst.
(* ** ac:         SearchAbout join. *)
(* ** ac:         SearchAbout TcbMod.join. *)
        eapply TcbMod.map_join_get_some .
        
        auto.
        eauto.
        2: exact H.
        (* instantiate (1:=(v'43, x, x0)). *)
        unfold get in *; simpl in *.
        unfold sig in *; simpl in *.
        eapply TcbMod.get_a_sig_a.
        go.
        unfold join, sig, get in *; simpl in *.
        assert (TcbMod.get tcbmap x1 =Some (v'53, x2, x3) ).
        go.
        assert (TcbMod.get tcbmap (cur_tcb_blk, Int.zero) =Some(v'53, wait (hle2wait x (v'15, Int.zero)) i13,
                             x0)  ).
        go.
        lets bb: H134 H0 H1 H2.
        apply bb.
        reflexivity.

      }      
      go.
      2: go.
      go.
      go.
      intro; tryfalse.
      go.
      go.
      intro; tryfalse.
      go.
      go.
      go.
      {
        splits.
assert( list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None)
   (v'43 ++
    (Vptr (cur_tcb_blk, Int.zero)
     :: v'13
        :: x36
           :: x33
              :: Vint32 i22
                 :: Vint32 i21
                    :: Vint32 i20
                       :: Vint32 i19
                          :: Vint32 i18 :: Vint32 i17 :: Vint32 i16 :: nil)
    :: nil) )as hell.

change ((fun x => list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None) x)
         (v'43 ++
      (Vptr (cur_tcb_blk, Int.zero)
       :: v'13
          :: x36
             :: x33
                :: Vint32 i22
                   :: Vint32 i21
                      :: Vint32 i20
                         :: Vint32 i19
                            :: Vint32 i18 :: Vint32 i17 :: Vint32 i16 :: nil)
      :: nil)).
 
 rewrite <- H101.

     
(* ** ac:  Show. *)
 eapply TCBLP_imply_nextnotnull_list.
 exact H29.
 
 rewrite H101.
 
         rewrite get_last_tcb_ptr_appsig.
         reflexivity.

        (* here *)
        rewrite ptr_in_tcblist_app.
        (* 2: simpl; auto. *)
        intro.
        destruct H131.
        eapply ptr_in_tcblist_last_ir in H131.
        gen H131.
        eapply distinct_is_unique_first.
instantiate ( 1 :=(Vptr (cur_tcb_blk, Int.zero)
             :: v'13
                :: x36
                   :: x33
                      :: Vint32 i22
                         :: Vint32 i21
                            :: Vint32 i20
                               :: Vint32 i19
                                  :: Vint32 i18
                                  :: Vint32 i17 :: Vint32 i16 :: nil)).

exact hell.
(* ** ac: SearchAbout get_last_tcb_ptr. *)

         eapply  TCBLP_imply_dictinct_list .
         rewrite <- H101.
         exact H25.

         rewrite get_last_tcb_ptr_appsig.
         reflexivity.

           
       
        (* simpl in H131. *)
        (* exact H131. *)
         rewrite get_last_tcb_ptr_appsig in H131.
         simpl (val_inj (Some (Vptr (next_tcb_block, Int.zero)))) in H131. 
(* ** ac:          SearchAbout ptr_in_tcblist. *)

(* ** ac:         Show. *)
        eapply ptr_in_tcblist_change_first in H131.
        gen H131.

        eapply distinct_is_unique_second.
        3: eapply  TCBLP_imply_dictinct_list .
        3: exact H25.
        2: go.
        rewrite H101.
        exact hell.
        rewrite H101.
        rewrite get_last_tcb_ptr_appsig.
        reflexivity.
        rewrite list_all_P_app.
        rewrite list_all_P_app in hell.
        simpljoin.
        splits; auto.
        simpl.
        split; auto.
         (* unfold V_OSTCBNext; simpl; intro; tryfalse. *)
        eauto.
      }
       (* from tcblist_p, get they are all different? *)
      {

(* ** ac:         SearchAbout TCBList_P. *)

         eapply TCBList_merge_prop.
         instantiate (2 := v'17).
         instantiate (1 := x13).

(* ** ac:          SearchAbout TcbMod.join. *)
         eapply some_join_lemma0; eauto.
         exact H11.
         exact tcbmapleft_join_hyp.
                  

(* ** ac:          SearchAbout last. *)
(* ** ac:          Print get_last_tcb_ptr. *)
(* ** ac:          SearchAbout last. *)
         rewrite app_last.
         simpl.
         go.
         Focus 2.



         eapply  tcblist_p_hold_for_del_a_tcb_at_head .
         lia.

        2:go.
        2:go.
        2: exact H11.
        2: exact backup.
        unfolds in H6.
        simpljoin.
        clear -H133 H28.
        eapply R_Prio_No_Dup_hold_for_subset.
        apply TcbMod.join_comm; eauto.
        eauto.

        
        eapply OSTimeDlyPure.update_rtbl_tcblist_hold.

        lia.
        unfold nat_of_Z; eapply nv'2nv.
        exact H60.
        intro; tryfalse.
        intros.

        unfolds in H6.
        simpljoin.
        clear -H28 H11 H131 H134.
(* ** ac:         Print R_Prio_No_Dup. *)
        eapply H134.
        instantiate (2 := tid).
        instantiate (1 := (cur_tcb_blk, Int.zero)).
        intro; subst tid.
(* ** ac:         SearchAbout TcbMod.join. *)
        eapply TcbMod.map_join_get_some.
        auto.
        exact H28.
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        go.
        
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        go.
        
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        unfold get; simpl.
        go.
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        unfold get; simpl.
        go.

(* ** ac:         SearchAbout TCBList_P. *)

        eapply TCBList_P_hold_for_last_change.
        rewrite H101 in H29.
        exact H29.
        
        

      }
       (* tcblist_p hold for deleting a tcb *)
      split.
      assumption.
      eapply (H68 _ H55).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.
       
      {
        eapply  r_priotbl_p_hold_for_del_a_tcb.
        lia.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .

      }

       (* r_priotbl_p hold for deleting a tcb *)
      
{
  eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
  lia.
  rewrite Int.repr_unsigned.
  reflexivity.

  rewrite Int.repr_unsigned.
  reflexivity.

  2: assumption.
  unfold nat_of_Z.
  apply nv'2nv.
  
  assumption.
  intro; tryfalse.
  
      }

       (* rl_rtbl_ptbl_p hold for deleting a tcb *)

      split.
      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.
      go.
      go.
      go.
      go.
      clear -H96 H131.
      unfolds in H96.
      change Byte.max_unsigned with 255%Z in * .
      math simpl in H96.
      lia.
      go.

      {
        eapply ECBLP_hold4del_a_tcb; eauto.
        3:exact tcbmapleft_join_hyp.
        clear -H6; unfolds in H6; tauto.
        clear -H6; unfolds in H6; tauto.
      }

       (* from H101 : RL_Tbl_Grp_P
           (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
              (val_inj
                 (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
           (Vint32 v'53), ECBList_P holds for deleting a tcb *)

       

      {
      eapply poi_is_rtep.
        eapply poi_RHTEP_hold_for_del_a_tcb.
        assumption.
        go.
        eapply tcbmapleft_join_hyp.
        go.
        clear -H2 H61 H62; unfolds; splits; auto.
      }

       (* change to poi,
from some_pure_hyp : forall (eid : tidspec.A) (pr : int32) 
                    (tid0 : tid) (opr : int32) (wls : waitset),
                  EcbMod.get ecbmap eid =
                  Some (absmutexsem pr (Some (tid0, opr)), wls) ->
                  tid0 <> (cur_tcb_blk, Int.zero)
get rh_te_p hold for deleting a tcb
              *)
      splits; go.
      unfolds; auto.
      go.
      hoare forward.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.

      hoare unfold.

      inverts H130.
      assert (Hopv: v'74 = Vint32 (Int.repr OS_NO_ERR) \/ v'74 <>Vint32 (Int.repr OS_NO_ERR)) by tauto.
      destruct Hopv.
    
      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskdel_succ.
      go.
      go.


      hoare forward.
      splits.
      eauto.
      eauto.
      
      change OS_NO_ERR with 0.
      rewrite Int.unsigned_repr. lia.
      rewrite max_unsigned_val. lia.

      change OS_NO_ERR with 0.
      rewrite Int.unsigned_repr.
      change Byte.max_unsigned with 255. lia.
      rewrite max_unsigned_val. lia.

      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskdel_succ_abt.
      can_change_aop_solver.
      auto.
    
      eapply absabort_rule.

    }

    (* delete not current *)
    {

      eapply backward_rule1.
      Set Printing Depth 999.
(* ** ac:       Show. *)
      instantiate (1:=
                     (
                       <|| spec_del (Vint32 v'53);; isched;; taskdel_succ (|v'74 :: nil|);; v'73 ||>  **
                           HTCBList tcbmap **
                           HCurTCB (cur_tcb_blk, Int.zero) **
                           OS [ empisr, false, nil, (true::nil)] **
   (* <|| spec_del (Vint32 v'53);; isched;; END Some (V$ NO_ERR) ||>  ** *)
   A_dom_lenv
     ((prio, Int8u)
      :: (pevent, OS_EVENT ∗)
         :: (ptcb, OS_TCB ∗)
            :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
   GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
   LV ptcb @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
   Astruct (todelblock, Int.zero) OS_TCB_flag
     (v'20
      :: Vptr (prev_tcb_block, Int.zero)
         :: Vnull
            :: x0
               :: V$ 0
                  :: V$ OS_STAT_RDY
                     :: Vint32 v'53
                        :: Vint32 (v'53&ᵢ$ 7)
                           :: Vint32 (v'53 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) :: nil) **
   LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (next_tcb_block, Int.zero) **
   Astruct (next_tcb_block, Int.zero) OS_TCB_flag
     (v'14
      :: Vptr (prev_tcb_block, Int.zero)
         :: x35
            :: x34
               :: Vint32 i15
                  :: Vint32 i14
                     :: Vint32 i12
                        :: Vint32 i11
                           :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil) **
   Astruct (prev_tcb_block, Int.zero) OS_TCB_flag
     (Vptr (next_tcb_block, Int.zero)
      :: v'13
         :: x36
            :: x33
               :: Vint32 i22
                  :: Vint32 i21
                     :: Vint32 i20
                        :: Vint32 i19
                           :: Vint32 i18 :: Vint32 i17 :: Vint32 i16 :: nil) **
   dllseg v'9 Vnull v'13 (Vptr (prev_tcb_block, Int.zero)) v'43 OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   dllseg v'14 (Vptr (next_tcb_block, Int.zero)) v'12 Vnull l2' OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
     (update_nth_val (Z.to_nat (Int.unsigned v'53)) priotbl Vnull) **
   PV vhold @ Int8u |-> v'7 **
   Aarray v'38 (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
        (val_inj (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
   PV (v'15, Int.zero +ᵢ  $ 1) @ Int8u |-> Vint32 v'50 **
   PV (v'15, Int.zero) @ Int8u |-> Vint32 i7 **
   PV (v'15,
      (Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
      $ Z.of_nat (typelen Int8u)) @ Int16u |-> Vint32 i8 **
   PV (v'15,
      ((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
       $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) @
   (Void) ∗ |-> x29 **
   PV (v'15,
      ((((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
         $ Z.of_nat (typelen Int8u)) +ᵢ  $ Z.of_nat (typelen Int16u)) +ᵢ
       $ Z.of_nat (typelen (Void) ∗)) +ᵢ
      $ Z.of_nat (typelen (Tarray Int8u ∘ OS_EVENT_TBL_SIZE))) @
   STRUCT os_event ⋆ |-> v'6 **
   AEventData
     (Vint32 i7 :: Vint32 v'28 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil) x22 **
   evsllseg v'6 Vnull x15 x24 **
   evsllseg v'8 (Vptr (v'15, Int.zero)) x11 x23 **
   GV OSEventList @ OS_EVENT ∗ |-> v'8 **
   (* HECBList ecbmap ** *)
   HECBList
   (EcbMod.set ecbmap (v'15, Int.zero)
        (x, remove_tid (todelblock, Int.zero) x14)) **
   (* HTCBList tcbmap ** *)
   HTime v'18 **
   (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
   LV pevent @ OS_EVENT ∗ |-> Vptr (v'15, Int.zero) **
   GV OSRdyGrp @ Int8u |-> Vint32 v'40 **
   GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'30
        (val_inj (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7))))))) **
   GV OSTCBList @ OS_TCB ∗ |-> v'9 **
   GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
   (* Aie false ** *)
   (* Ais nil ** *)
   (* Acs (true :: nil) ** *)
   (* Aisr empisr ** *)
   tcbdllflag v'9
     ((v :: l1') ++
      (Vptr (next_tcb_block, Int.zero)
       :: Vptr (prev_tcb_block, Int.zero)
          :: Vptr (v'15, Int.zero)
             :: x0
                :: Vint32 i13
                   :: Vint32 x21
                      :: Vint32 v'53
                         :: Vint32 (v'53&ᵢ$ 7)
                            :: Vint32 (v'53 >>ᵢ $ 3)
                               :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                  :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3)) :: nil)
      :: (v'14
          :: Vptr (todelblock, Int.zero)
             :: x35
                :: x34
                   :: Vint32 i15
                      :: Vint32 i14
                         :: Vint32 i12
                            :: Vint32 i11
                               :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
         :: l2') **
   G& OSPlaceHolder @ Int8u == vhold **
   (* A_isr_is_prop ** *)
   p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
   LV self @ Int8u |-> (V$ 0) **
   AOSEventFreeList v'3 **
   AOSQFreeList v'4 **
   AOSQFreeBlk v'5 **
   AOSMapTbl **
   AOSUnMapTbl **
   AOSIntNesting **
   sll v'20 v'21 OS_TCB_flag V_OSTCBNext **
   sllfreeflag v'20 v'21 **
   AOSTime (Vint32 v'18) **
   AGVars ** APthreadAttr v'64 v'65 v'66 ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'53 )).

      clear.
      intro; intros.
      sep lifts (4:: 6::nil)%nat. 
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.

      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (todelblock, Int.zero) (v'53, wait (hle2wait x (v'15, Int.zero)) i13 , x0) mmm tcbmap).
      apply tcb_get_join.
      unfold get, sig, join in *; simpl in *.
      unfold get, sig, join in *; simpl in *.
      go.

      destruct H103 as (tcbmap_left & tcbmapleft_join_hyp).


      eapply seq_rule.
      eapply derive_delother_rule.
      apply goodlinv.

       (* goodlinv *)
      go.
      unfold AEventData.
      destruct x22; go.
      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.
      exact tcbmapleft_join_hyp.
      clear -H3; unfolds in H3.
      unfolds.
      simpljoin.
      eauto.
      intro; tryfalse.
      intro; intros.
      split.
      sep_get_rv.
      unfold p_local in H103.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.
      hoare lift 37%nat pre.
      eapply backward_rule1.
      eapply dllsegflag_split.
      hoare_split_pure_all.
      unfold dllsegflag at 2.
      fold dllsegflag .
      hoare_split_pure_all.
      inverts H130.
      inverts H103.
      inverts H131.
      inverts H132.
      rewrite H101.

      rename v'11 into v'47.
      rename v'16 into v'48.


      hoare_assert_pure ( (fun vl : vallist => nth_val 0 vl) (Vptr (todelblock, Int.zero)
                                                                   :: v'13
                                                                   :: x36
                                                                   :: x33
                                                                   :: Vint32 i22
                                                                   :: Vint32 i21
                                                                   :: Vint32 i20
                                                                   :: Vint32 i19
                                                                   :: Vint32 i18
                                                                   :: Vint32 i17 :: Vint32 i16 :: nil) = Some (Vptr v'48) ).
      eapply dllsegflag_last_next_is_endstnl.
      instantiate (4 := s0).
      sep cancel 5%nat 1%nat.
      eauto.

      hoare_split_pure_all.
      inverts H131.

      
      
      (* rewrite app_nil_l. *)
      (* hoare unfold. *)
      (* hoare lift 4%nat pre. *)
      unfold p_local at 2.
      unfold OSLInv at 3.
      unfold LINV.
      hoare_split_pure_all.
      (* unfold1 dllseg. *)
      (* hoare unfold. *)
      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)
      sep combine ( get_off_addr (todelblock, Int.zero) ($ 24)  ) in H133.
      eauto.

      hoare lift 5%nat pre.
      eapply seq_rule.
      eapply assign_rule'.
      Focus 2.

      intro; intros.
      split.
      eapply field_asrt_impl.
      Focus 3.
      sep cancel 13%nat 1%nat.
      eauto.
      reflexivity.
      reflexivity.
      sep get rv.
      eapply eq_int; auto.

      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.
      sep lift 39%nat in H133.
      unfold OSLInv in H133.
      sep normal in H133.
      sep destruct H133.
      sep split in H133.
      unfold init_lg in H131; destruct H131.
      inverts H131.
      sep cancel 1%nat 1%nat.
      eauto.

      simpl; auto.
      splits; eauto.
      unfolds; auto.
      
      rename v'24 into v'54.
      eapply backward_rule1.
      intro; intros.
      sep lifts (8::10::nil)%nat in H133.
      eapply add_a_isr_is_prop in H133.
      eauto.
      hoare lift 4%nat pre.
      eapply seq_rule.

      eapply excrit1_rule'_ISnil_ISRemp''.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      unfold p_local.
      sep pauto.
      unfold LINV.
      sep pauto.
      sep cancel OSLInv.
      eapply poi_OSINV_imply_OSInv.
      unfold poi_OSINV.
      sep pauto.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
      sep cancel APthreadAttr.
      unfold AECBList.
instantiate (14 := (x11 ++ (Vint32 i7 :: Vint32 v'50 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil,
                                 (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
                                                 (val_inj
                                                    (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
                                ) :: x15)).
      instantiate (13 :=(x23 ++ x22 :: x24) ).


      sep pauto.
      eapply evsllseg_merge.
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H80).
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H81).


      unfold1 evsllseg .
      sep pauto.
      unfold AEventNode.
      sep cancel evsllseg.
      sep cancel evsllseg.
      unfold AOSEvent.
      unfold node.
      unfold AOSEventTbl.
      sep pauto.
      sep cancel Aarray.

      sep lift 2%nat.
      eapply AED_changegrp.
      sep cancel AEventData.
      unfold Astruct.
      unfold OS_EVENT.
      unfold Astruct'.
      sep normal.
      sep cancel 16%nat 2%nat.
      repeat sep cancel 16%nat 1%nat.
      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel 20%nat 2%nat.
      sep cancel 14%nat 1%nat.
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold poi_AOSTCBList.
      
      sep pauto.

      instantiate (4 := (
(v'43 ++
               (Vptr (next_tcb_block, Int.zero)
                :: v'13
                   :: x36
                      :: x33
                         :: Vint32 i22
                            :: Vint32 i21
                               :: Vint32 i20
                                  :: Vint32 i19
                                     :: Vint32 i18
                                        :: Vint32 i17 :: Vint32 i16 :: nil)
               :: nil)  ++
                         (v'54
               :: Vptr (prev_tcb_block, Int.zero)
                  :: x35
                     :: x34
                        :: Vint32 i15
                           :: Vint32 i14
                              :: Vint32 i12
                                 :: Vint32 i11
                                    :: Vint32 i10
                                       :: Vint32 i9 :: Vint32 i :: nil) 
                          
                            :: l2')).
unfold tcbdllseg.
      unfold tcbdllflag.
      unfold1 dllsegflag.
      unfold1 dllseg.
      unfold node.
      sep pauto.


      eapply dllseg_is_poi.
      eapply split_poillseg.
      sep eexists.
      eapply split_poillseg.
      sep eexists.
      rewrite <- dllseg_is_poi.
      sep lift 2%nat.
      rewrite <- dllseg_is_poi.
      sep lift 3%nat.
      rewrite <- dllseg_is_poi.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 11%nat 1%nat.
      sep cancel 10%nat 1%nat.
      sep cancel 11%nat 1%nat.
      sep cancel dllseg.

      sep lift 4%nat in H133.
      rewrite dllsegflag_is_poi in H133.
      apply split_poillseg in H133.
      sep destruct H133.
      apply dllsegflag_is_poi.
      apply split_poillseg.
      sep eexists.
      apply split_poillseg.
      sep eexists.
      sep pauto.
      sep cancel 1%nat 1%nat.
      unfold1 @poi_llseg in *.

  sep_semiauto_nosplit2.
  1: scancel.
  2: sep normal in H133;
        sep destruct H133;
        sep split in H133;
        subst.

      sep lift 2%nat.
      rewrite <- dllsegflag_is_poi.
      sep cancel dllsegflag.
      instantiate (4 := x16).
      sep cancel 1%nat 2%nat.
      sep cancel 2%nat 1%nat.

      (* freelist *)
      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_l. 
      unfold TCBFree_Not_Eq.
      sep pauto.
      instantiate ( 2 := (
(v'20
               :: Vptr (prev_tcb_block, Int.zero)
                  :: Vnull
                     :: x0
                        :: V$ 0
                           :: V$ OS_STAT_RDY
                              :: Vint32 v'53
                                 :: Vint32 (v'53&ᵢ$ 7)
                                    :: Vint32 (v'53 >>ᵢ $ 3)
                                       :: Vint32 ($ 1<<ᵢ(v'53&ᵢ$ 7))
                                          :: Vint32 ($ 1<<ᵢ(v'53 >>ᵢ $ 3))
                                             :: nil) :: v'21
                            
                          )).
      unfold1 sll.
      unfold1 sllfreeflag.
      unfold1 sllseg.
      unfold1 sllsegfreeflag.
      
      sep pauto.
      unfold node.
      unfold sll, sllfreeflag in H133.
      sep pauto.
      sep cancel sllsegfreeflag.
      sep cancel sllseg.
      sep cancel Astruct.
      eauto.
      go.
      eapply isptr_is_definitely_ptr.
      eapply sll_head_isptr.
      instantiate (5:=s).
      unfold sll.
      sep cancel sllseg.
      go.
      go.
      
      go.
      intro; tryfalse.
      2:go.
      go.
      go.
      intro; tryfalse.
      intro; tryfalse.
      go.
      go.
      go.
      go.
      go.
      go.
      intro; tryfalse.
      {


         eapply TCBList_merge_prop.
         instantiate (2 := v'17).
         instantiate (1 := x13).

         eapply some_join_lemma0; eauto.
         exact H11.
         exact tcbmapleft_join_hyp.
                  

         rewrite app_last.
         simpl.
         go.
         Focus 2.

         eapply  tcblist_p_hold_for_del_a_tcb_at_head .
         lia.

        2:go.
        2:go.
        2: exact H11.
        2: exact backup.
        unfolds in H6.
        simpljoin.
        clear -H135 H28.
        eapply R_Prio_No_Dup_hold_for_subset.
        apply TcbMod.join_comm; eauto.
        eauto.

        
        eapply OSTimeDlyPure.update_rtbl_tcblist_hold.

        lia.
        unfold nat_of_Z; eapply nv'2nv.
        exact H60.
        intro; tryfalse.
        intros.

        unfolds in H6.
        simpljoin.
        clear -H28 H11 H136 H134.
        eapply H136.
        instantiate (2 := tid).
        instantiate (1 := (todelblock, Int.zero)).
        intro; subst tid.
        eapply TcbMod.map_join_get_some.
        auto.
        exact H28.
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        go.
        
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        go.
        
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        unfold get; simpl.
        go.
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        unfold get; simpl.
        go.
        eapply TCBList_P_hold_for_last_change.
        rewrite H101 in H29.
        exact H29.
        

      }
       (* tcblist_p hold for deleting a tcb *)

      {
(* ** ac:         SearchAbout ptr_in_tcbdllseg. *)
(* ** ac:         Search ptr_in_tcbdllseg. *)
(* ** ac:         SearchAbout ptr_in_tcbdllseg. *)
        assert (list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None) (v'43 ++
         (Vptr (todelblock, Int.zero)
          :: v'13
             :: x36
                :: x33
                   :: Vint32 i22
                      :: Vint32 i21
                         :: Vint32 i20
                            :: Vint32 i19
                               :: Vint32 i18
                                  :: Vint32 i17 :: Vint32 i16 :: nil) :: nil
                                                                         )).

 eapply TCBLP_imply_nextnotnull_list.
 rewrite H101 in H29.
 exact H29.
 rewrite  get_last_tcb_ptr_appsig.
 eauto.


 
        eapply  ptr_in_tcblist_app in H24.
        destruct H24.
        apply  ptr_in_tcblist_app.

        2: left; eapply ptr_in_tcblist_last_ir.
        apply  list_all_P_app.
        apply  list_all_P_app in H134.
        simpljoin.
        splits; auto.
        simpl; go.
        (* unfold V_OSTCBNext; simpl; intro; tryfalse. *)
        rewrite H101 in H24; exact H24.

        
        apply  ptr_in_tcblist_app.

        apply  list_all_P_app.
        apply  list_all_P_app in H134.
        simpljoin.
        splits; auto.
        simpl; go.
        (* unfold V_OSTCBNext; simpl; intro; tryfalse. *)

        right.
        
        rewrite          get_last_tcb_ptr_appsig.
        rewrite H101 in H24.
        rewrite          get_last_tcb_ptr_appsig in H24.
        eapply  ptr_in_tcbdllseg_change_head.
        Focus 2.
        eapply ptr_in_tcbdllseg_not_head. 
        2: exact H24.
        reflexivity.
        simpl; intro; tryfalse.
        reflexivity.
        rewrite H101.
        exact H134.
        
      }
       (* from tcblist_p, get they are all different? *)
      split.
      assumption.
      eapply (H68 _ H55).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.
        
      {
        eapply  r_priotbl_p_hold_for_del_a_tcb.
        lia.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .

      }

       (* r_priotbl_p hold for deleting a tcb *)
      
{
  eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
  lia.
  rewrite Int.repr_unsigned.
  reflexivity.

  rewrite Int.repr_unsigned.
  reflexivity.

  2: assumption.
  unfold nat_of_Z.
  apply nv'2nv.
  
  assumption.
  intro; tryfalse.
  
      }

       (* rl_rtbl_ptbl_p hold for deleting a tcb *)

      split.
      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.
      go.
      go.
      go.
      go.
      clear -H96 H134.
      unfolds in H96.
      change Byte.max_unsigned with 255%Z in * .
      math simpl in H96.
      lia.
      go.
      {
        eapply ECBLP_hold4del_a_tcb; eauto.
        3:exact tcbmapleft_join_hyp.
        clear -H6; unfolds in H6; tauto.
        clear -H6; unfolds in H6; tauto.
      }

       (* from H101 : RL_Tbl_Grp_P
           (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
              (val_inj
                 (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
           (Vint32 v'53), ECBList_P holds for deleting a tcb *)

        

       

      {
      eapply poi_is_rtep.
        eapply poi_RHTEP_hold_for_del_a_tcb.
        assumption.
        go.
        eapply tcbmapleft_join_hyp.
        go.
        clear -H2 H61 H62; unfolds; splits; auto.
      }

       (* change to poi,
from some_pure_hyp : forall (eid : tidspec.A) (pr : int32) 
                    (tid0 : tid) (opr : int32) (wls : waitset),
                  EcbMod.get ecbmap eid =
                  Some (absmutexsem pr (Some (tid0, opr)), wls) ->
                  tid0 <> (cur_tcb_blk, Int.zero)
get rh_te_p hold for deleting a tcb
              *)
      go.

(*     
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
*) 
      eapply seq_rule.
      1: hoare_call2.
      sep_semiauto_nosplit2.
         sep pauto.
      2: try sep_unfold_funpost; sep pauto.
      5: sep pauto.
      (*hoare forward.*)

      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.

      hoare unfold.

      inverts H133.
      assert (Hopv: v'74 = Vint32 (Int.repr OS_NO_ERR) \/ v'74 <>Vint32 (Int.repr OS_NO_ERR)) by tauto.
      destruct Hopv.
    
      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskdel_succ.
      go.
      go.


      hoare forward.
      splits.
      eauto.
      eauto.
      
      change OS_NO_ERR with 0.
      rewrite Int.unsigned_repr. lia.
      rewrite max_unsigned_val. lia.

      change OS_NO_ERR with 0.
      rewrite Int.unsigned_repr.
      change Byte.max_unsigned with 255. lia.
      rewrite max_unsigned_val. lia.

      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskdel_succ_abt.
      can_change_aop_solver.
      auto.
    
      eapply absabort_rule.

    }


    Unshelve.
    exact (Afalse).

    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).

    exact (V$0).
    exact (V$0).    exact (V$0).    exact (V$0).    exact (V$0).    exact (V$0).
 
    exact (V$0).    exact (V$0).    exact (V$0).    exact (V$0).    exact (V$0).    exact (V$0).
  
    exact (V$0).    exact (V$0).   

  } 
(* end of eapply task_deletewaiting*)
 }
    
Qed.

   

      
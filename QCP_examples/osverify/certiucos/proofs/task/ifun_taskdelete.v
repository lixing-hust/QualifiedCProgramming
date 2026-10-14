Require Import ucos_include1.
Require Import os_code_defs1.
Require Import os_ucos_h1.
Require Import code_notations1.
Require Import sep_lemmas_ext1.
Require Import linv_solver1.
Require Import taskcreate_pure.
Require Import protect1.
Require Import Lia.

Require Import infer_absabt_step1. 

Require Import inline_definitions1.
Require Import inline_bittblfunctions1.
Require Import inline_tactics1.
Require Import symbolic_lemmas1.
Require Import new_inv1.
Require Import protect1.
Require Import Lia.

Require Import ifun_taskcreate.
Require Import List.
Require Import ifun_spec1.
Require Import os_program1.
Require Import os_task1.

Require Import task_pure.
Require Import ifun_taskdel_spec.

Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.

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

  hoare forward prim.
  hoare unfold.
  unfold AOSTCBList.
  hoare normal pre.
  hoare_split_pure_all.
  unfold1 tcbdllseg.
  unfold1 dllseg.
  unfold node.
  hoare normal pre.
  hoare_split_pure_all.
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
  eapply symbolic_lemmas1.array_type_vallist_match_imp_rule_type_val_match.
  rewrite H7.
  clear -H.
  mauto.
  auto.

(* ptcb ′ =ₑ OSTCBPrioTbl ′ [prio ′];ₛ *)
  hoare forward.
  math simpls.
  assumption.
  
  assert (exists t , TcbMod.get v'19 ((v'33, Int.zero)) = Some (x5, t, x2)).
  unfold1 TCBList_P in H11.
  simpljoin.
  unfolds in H18.
  destruct x11; destruct p.
  simpljoin.
  inverts H20.
  unfolds in H22; simpl in H22.
  inverts H18.
  inverts H11.
  unfold join,sig,get in *; simpl in *.
  unfold join,sig,get in *; simpl in *.
  eexists.
  go.
  destruct H14 as (hello & kitty).
  protect kitty.
 
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
  (exists tid st msg,
   TcbMod.get v'19 tid = Some (i, st, msg))).
  {
    intro.
    apply H14.
    destruct H13.
    Focus 2.
    simpljoin.
    rewrite H13.
    simpl.
    destruct x11.
    reflexivity.
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
    intro; tryfalse.
  }

  rename v'4 into opv.
  change ((Vint32 i :: nil) ++ opv :: nil) with (Vint32 i  :: opv :: nil).
  assert (Hopv: opv = Vint32 (Int.repr OS_TASK_DEL_ERR) \/ opv <>Vint32 (Int.repr OS_TASK_DEL_ERR)) by tauto.
  destruct Hopv. 
  subst.
(* opv = Vint32 (Int.repr OS_TASK_DEL_ERR) *)  
  hoare abscsq.

  apply noabs_oslinv.
  eapply absimp_taskdel_prio_no_such_tcb'.
  auto.
  go.
  auto.

(* EXIT_CRITICAL;ₛ RETURN ′ OS_TASK_DEL_ERR*)
  hoare forward prim.
  sep cancel APthreadAttr. 
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.
  sep pauto.
  sep cancel tcbdllflag.
  sep cancel 4%nat 1%nat.
  
  unfold tcbdllseg.
  unfold1 dllseg.
  sep pauto.
  unfold node.
  sep pauto.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat .
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  eauto.
  go.
  go.
  go.
  go.
  go.
  go.
  go.

  hoare forward.

  pure_auto; int auto;  change OS_TASK_DEL_ERR  with 60; lia.

  (* opv <> Vint32 (Int.repr OS_TASK_DEL_ERR) *) 

  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskdel_prio_no_such_tcb_abt'.
  auto.
  can_change_aop_solver.
  auto.
  eapply absabort_rule.

  (*  If (ptcb ′ ==ₑ os_task1.PlaceHolder)*)
  hoare forward.
  hoare_split_pure_all.

  unfold os_task1.PlaceHolder.
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
    eapply symbolic_lemmas1.bop_rv.
    sep_get_rv.
    eapply symbolic_lemmas1.addrof_gvar_rv.
    gen_notin_lenv H14 OSPlaceHolder.
    eapply symbolic_lemmas1.dom_lenv_imp_notin_lenv.
    eauto.
    sep cancel A_dom_lenv.
    sep cancel Agvarenv'.
    eauto.
    eauto.
    simpl.
    destruct x; destruct v'21.
    destruct ( Int.eq i0 i1 ); destruct (peq b b0); simpl; intro; tryfalse.
    simpl.
    eauto.
    hoare unfold.
    instantiate (1:=Afalse).

  assert(~
  (exists tid st msg,
   TcbMod.get v'19 tid = Some (i, st, msg))).
   {
    intro.
    apply H14.
    assert ( x <> v'21 \/ x = v'21).
    tauto.
    destruct H20.
    simpl.
    destruct x; destruct v'21.
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
    hoare abscsq.
    apply noabs_oslinv.
    eapply absimp_taskdel_prio_no_such_tcb'.
    auto.
    go.
    auto.

    hoare forward.
    hoare unfold.

    hoare forward prim.
    sep cancel 10%nat 3%nat. 
    unfold AOSTCBPrioTbl.
    unfold AOSTCBList.
    sep pauto.
    sep cancel tcbdllflag.
    sep cancel 4%nat 1%nat.
    
    unfold tcbdllseg.
    unfold1 dllseg.
    unfold node.
    sep pauto.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat .
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    eauto.
    go.
    go.
    go.
    go.
    go.
    go.
    go.
    hoare forward.

    pure_auto; int auto;  change OS_TASK_DEL_ERR  with 60; lia.

    (* opv <> Vint32 (Int.repr OS_TASK_DEL_ERR) *) 
  
    hoare abscsq.
    apply noabs_oslinv.
    eapply absimp_taskdel_prio_no_such_tcb_abt'.
    auto.
    can_change_aop_solver.
    auto.
    eapply absabort_rule.
  }

  (* self ′ =ᶠ OS_IsSomeMutexOwner (·ptcb ′·);ₛ *)

  hoare forward.
  hoare unfold.
  (**********************)
  (* last is H15 *)
  hoare forward.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  
  sep cancel Aop.
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

  assert(exists x y z w tt mm,
  TcbMod.get v'19 v'45 = Some (i, tt, mm) /\ EcbMod.get v'18 x = Some (absmutexsem y (Some (v'45, z)), w)).
  {
    unfolds in H20.
    assert (v'45 <> v'21) as some_pure.
    clear -H14.
    intro.
    subst.
    simpl in H14.
    destruct v'21; simpl in H14.
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

  hoare abscsq.
  apply noabs_oslinv.
  
(*
Lemma absimp_taskdel_some_mutex_owner:
  forall P v3 sch mqls tls t ct tid ,
    can_change_aop P ->
    (exists x y z w tt mm , TcbMod.get tls tid = Some (v3, tt, mm) /\ EcbMod.get mqls x = Some (absmutexsem y (Some (tid, z)), w)) ->
    absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| END (Some (Vint32 (Int.repr  OS_TASK_DEL_SOME_MUTEX_OWNER))) ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) .
Proof.
  intros.
  simpljoin.
  infer_solver 3%nat.
Qed.
*)  



eapply absimp_taskdel_some_mutex_owner'.
auto.
go.

instantiate (1 := (v'45)).
auto.

hoare forward prim.
sep cancel APthreadAttr.
eauto.
go.
hoare forward.

pure_auto; int auto; change OS_TASK_DEL_SOME_MUTEX_OWNER  with 62; lia.

(* opv <> Vint32 (Int.repr OS_TASK_DEL_SOME_MUTEX_OWNER) *) 

hoare abscsq.
apply noabs_oslinv.
eapply absimp_taskdel_some_mutex_owner_abt'.
auto.
can_change_aop_solver.

instantiate (1 := (v'45)).
auto.

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
rename v'21 into vhold.
rename v'33 into cur_tcb_blk.
rename v'19 into tcbmap.
rename v'10 into priotbl.
rename v'45 into todelptr.
assert (exists st m, TcbMod.get tcbmap todelptr = Some (i, st, m)). 
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
            (*<|| taskdelcode (Vint32 i :: nil) ||>  ** *)
                    (* GV OSTCBList @ OS_TCB ∗ |-> v'9 ** *)
           (* tcbdllseg v'9 Vnull v'10 (Vptr (cur_tcb_blk, Int.zero)) l1 ** *)
           (* GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) ** *)
           (* tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'10 v'12 Vnull
            *   (tcbcur :: l2) ** *)
  GV OSTCBList @ OS_TCB ∗ |-> v'11 **
  (* tcbdllseg v'11 Vnull v'12 (Vptr (cur_tcb_blk, Int.zero)) l1 ** *)
  GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
  (* tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'12 v'14 Vnull (tcbcur :: l2) ** *)
  Aie false **
  Ais nil **
  Acs (true :: nil) **
  Aisr empisr **
  AECBList v'9 v'8 v'18 tcbmap **
  tcbdllflag v'11 (l1 ++ tcbcur :: l2) **
  AOSRdyTblGrp v'16 v'17 **
  AOSTCBPrioTbl priotbl v'16 tcbmap vhold **
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
               ?? spec_del (Vint32 i);;
                  isched;; taskdel_succ (|v'4 :: nil|);; v'3
                  ?? taskdel_clear_waitls_bit (|Vint32 i :: v'4 :: nil|);;
                     spec_del (Vint32 i);;
                     isched;; taskdel_succ (|v'4 :: nil|);; v'3) ||>  **
  p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
  LV self @ char_t |-> (V$ 0) **
  LV ptcb @ OS_TCB ∗ |-> Vptr todelptr **
  AOSEventFreeList v'5 **
  AOSQFreeList v'6 **
  AOSQFreeBlk v'7 **
  AOSMapTbl **
  AOSUnMapTbl **
  AOSIntNesting **
  AOSTCBFreeList v'22 v'23 **
  AOSTime (Vint32 v'20) **
  HTime v'20 **
  AGVars **
  APthreadAttr v'24 v'25 v'26 **
  atoy_inv' **
  LV os_code_defs1.x @ OS_TCB ∗ |-> v'2 **
  LV pevent @ OS_EVENT ∗ |-> v' **
  LV prio @ char_t |-> Vint32 i **
  A_dom_lenv
    ((prio, char_t)
     :: (pevent, OS_EVENT ∗)
        :: (ptcb, OS_TCB ∗)
           :: (self, char_t) :: (os_code_defs1.x, OS_TCB ∗) :: nil)
)).
eapply tcbdllseg_combine.
sep pauto.
go.
go.
go.

hoare_split_pure_all.

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


(* 
Lemma absimp_taskdel_prio_HAS_NO_NEXT:
  forall P v3 sch mqls tls t ct,
    can_change_aop P ->
    absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| END (Some (Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT))) ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) .
Proof.
  infer_solver 4%nat.
Qed.
*)


(* opv = Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT) *)      
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskdel_prio_HAS_NO_NEXT'.
  auto.
  go.



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
    (* Astruct (todelblock, Int.zero) OS_TCB_flag todelblk ** *)
    (* dllseg v'30 (Vptr (todelblock, Int.zero)) v'14 Vnull l2' OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl)
      (fun vl : vallist => nth_val 0 vl) ** *)
    (* dllseg v'11 Vnull v'15 (Vptr (todelblock, Int.zero)) l1' OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl)
      (fun vl : vallist => nth_val 0 vl) ** *)
    GV OSTCBList @ OS_TCB ∗ |-> v'11 **
    GV OSTCBCur @ OS_TCB ∗
    |-r-> Vptr (cur_tcb_blk, Int.zero) **
    Aie false **
    Ais nil **
    Acs (true :: nil) **
    Aisr empisr **
    AECBList v'9 v'8 v'18 tcbmap **
    tcbdllflag v'11 (l1' ++ todelblk :: l2') **
    AOSRdyTblGrp v'16 v'17 **
    AOSTCBPrioTbl priotbl v'16 tcbmap vhold **
    A_isr_is_prop **
    p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
    LV self @ char_t |-> (V$ 0) **
    LV ptcb @ OS_TCB ∗
    |-> Vptr (todelblock, Int.zero) **
    AOSEventFreeList v'5 **
    AOSQFreeList v'6 **
    AOSQFreeBlk v'7 **
    AOSMapTbl **
    AOSUnMapTbl **
    AOSIntNesting **
    AOSTCBFreeList v'22 v'23 **
    AOSTime (Vint32 v'20) **
    AGVars **
    APthreadAttr v'24 v'25 v'26 **
    atoy_inv' **
    LV os_code_defs1.x @ OS_TCB ∗ |-> v'2 **
    LV pevent @ OS_EVENT ∗ |-> v' **
    LV prio @ char_t |-> Vint32 i **
    A_dom_lenv
      ((prio, char_t)
       :: (pevent, OS_EVENT ∗)
          :: (ptcb, OS_TCB ∗)
             :: (self, char_t)
                :: (os_code_defs1.x, OS_TCB ∗) :: nil)
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
  destruct v'10.
  unfold tcbdllseg; unfold dllseg.
  hoare_split_pure_all.
  inverts H59.
  rewrite H55.

  hoare forward prim.

  sep cancel APthreadAttr.
  sep cancel tcbdllflag.
  unfold AOSTCBList.
  sep pauto.
  go.
  go.
  go.
  go.

  (* RETURN ′ OS_TASK_DEL_HAS_NO_NEXT*)
  hoare forward.

  pure_auto; int auto; change OS_TASK_DEL_HAS_NO_NEXT with 64; lia.

  (* opv <> Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT ) *) 

  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskdel_prio_HAS_NO_NEXT_abt'.
  auto.
  go.
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
  destruct x14; destruct p.
  simpljoin.
  inverts H9; inverts H10.
  assert ( (p, t, m) = (i, x, x0)).
  clear -H11 H23 H28.
  assert (get tcbmap (todelblock, Int.zero) =Some  (p, t, m)).
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
  Focus 2.
  sep pauto.
  sep cancel Aop.
  sep cancel 4%nat 2%nat.
  sep cancel 2%nat 1%nat.
  eauto.

  instantiate (1 := x11).
  omega.
  go.
  math simpls.
  go.
  go.
  clear -H.
  mauto.

  2:go.

  intro.
  intros.

  lrv_solver.
  go.
  go.
  go.

  intro.
  intros.
  linv_solver.

(* pevent ′ =ₑ ptcb ′ .. OSTCBEventPtr;ₛ *)  
  inline_post_unfolder inline_bittbl_clearbit.
  hoare unfold.
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

 {
hoare abscsq.
apply noabs_oslinv.
eapply absimp_taskdel_rdy_succ'.
go.


   (* not in wait list *)
   subst x21.
   rewrite (H64 (eq_refl  ($ OS_STAT_RDY))). 

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
   Require Import taskdelete_ready.
   protect Heqtcblst.

   eapply task_delete_ready with 
   (x23 := x23) (x20 := x20) (x19 := x19) (x18 := x18) (x17 := x17) ( i6 := i6) ( i5 := i5 ) ( i4 := i4) ( i3 := i3) ( i2 := i2) (i1 := i1 ) ( i0 := i0) ( l2 := l2)  (l1' := l1' ) (v'3 := v'5) (v'4 := v'6) (v'5 := v'7) (v'6 := v'8) (v'7 := v'9) (v'9 := v'11) (v'16 := v'18) (v'18 := v'20) (v'20 := v'22) (v'21 := v'23) (v'25 := v'34) (v'26 := v'35) (v'27 := v'32) (v'12 := v'14) (v'13 := v'15) (v'17 := v'19) (v'19 := v'21) (v'29 := v'31) (v'30 := v'33) (v'32 := v'37) (v'33 := v'38) (v'34 := v'39) (v'35 := v'40) (v'36 := v'41) (v'40 := v'45) (v'41 := v'46) (v'43 := v'48) (v'73 := v'3) (v'74 := v'4) (v'64 := v'24) (v'65 := v'25) (v'66 := v'26); 
    eauto.
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
      Require Import taskdelete_waiting.
      eapply task_deletewaiting with 
  (x20 := x20) (x19 := x19) (x18 := x18) (x17 := x17) ( i6 := i6) ( i5 := i5 ) ( i4 := i4) ( i3 := i3) ( i2 := i2) (i1 := i1 ) ( i0 := i0) ( l2 := l2) (v'3 := v'5) (v'4 := v'6) (v'5 := v'7) (v'6 := v'8) (v'7 := v'9) (v'9 := v'11) (v'12 := v'14) (v'13 := v'15) (v'14 := v'16) (v'15 := v'17) (v'16 := v'18) (v'17 := v'19) (v'18 := v'20) (v'19 := v'21) (v'20 := v'22) (v'21 := v'23) (v'25 := v'34) (v'26 := v'35) (v'27 := v'32) (v'28 := v'30) (v'29 := v'31) (v'30 := v'33) (v'32 := v'37) (v'33 := v'38) (v'34 := v'39) (v'35 := v'40) (v'36 := v'41) (v'37 := v'42) (v'38 := v'43) (v'39 := v'44) (v'40 := v'45) (v'41 := v'46) (v'42 := v'47) (v'44 := v'49) (v'45 := v'50) (v'46 := v'51) (v'50 := v'55) (v'51 := v'56) (v'53 := v'58) (v'73 := v'3) (v'74 := v'4) (v'64 := v'24) (v'65 := v'25) (v'66 := v'26); eauto.
  
    }
    
Qed.

   

      
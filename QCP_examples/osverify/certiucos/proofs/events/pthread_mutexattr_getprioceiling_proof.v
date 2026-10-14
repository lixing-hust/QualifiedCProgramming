Require Import os_code_defs.
Require Import List.
Require Import os_mutex_cap.
Require Import abs_op.
Require Import ifun_spec.
Require Import os_ucos_h.
Require Import os_program.
Require Import inv_prop.

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
Require Import abs_infer_step.
Require Import abs_infer_abt.
Require Import hoare_forward.
Require Import pure.

Require Import evt_spec_defs.
Require Import OSTimeTickPure.
Require Import gjb_common.
Require Import gjb_mutex_common.
Require Import evheap_pure.

Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

(* mutexattr_gettype_mtperr *)
Lemma mutexattrgetprioceiling_absimp_mtpok_abt_null:
  forall attr sch s V_ret P,
    can_change_aop P ->
    cmpaddr Clt userAddrStart attr = true ->
    cmpaddr Cle attr userAddrEnd = true ->
    V_ret <> Vint32 (Int.repr EINVAL) -> 
    absinfer sch
      (<|| (mutexattr_getprioceiling_mtperr (|(Vptr attr) :: Vnull :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed. 

Lemma mutexattrgetprioceiling_absimp_mtperr_abt:
  forall s sch attr v'4 V_ret P,
    cmpaddr Clt userAddrStart attr = true ->
    cmpaddr Cle attr userAddrEnd = true ->
    (cmpaddr Cle v'4 userAddrStart = true \/ cmpaddr Clt userAddrEnd v'4 = true) ->  
    V_ret <> Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_getprioceiling_mtperr (|(Vptr attr) :: (Vptr v'4) :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexattrgetprioceiling_absimp_mtpok_abt_null':
  forall sch s attr V_ret P,
    can_change_aop P ->
    cmpaddr Clt userAddrStart attr = true ->
    cmpaddr Cle attr userAddrEnd = true ->
    V_ret = Vint32 (Int.repr EINVAL) -> 
    absinfer sch
      (<||(mutexattr_getprioceiling_mtperr (|(Vptr attr) :: Vnull :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| END (Some  (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexattrgetprioceiling_absimp_mtperr_end:
  forall s sch attr v'4 V_ret P,
    cmpaddr Clt userAddrStart attr = true ->
    cmpaddr Cle attr userAddrEnd = true ->
    (cmpaddr Cle v'4 userAddrStart = true \/ cmpaddr Clt userAddrEnd v'4 = true) ->  
    V_ret = Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_getprioceiling_mtperr (|(Vptr attr) :: (Vptr v'4) :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| END (Some  (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexattrgetprioceiling_absimp_attrok_abt_null:
  forall sch s V_ret P,
    can_change_aop P ->
    V_ret <> Vint32 (Int.repr EINVAL) -> 
    absinfer sch
      (<||
          (mutexattr_getprioceiling_attrerr (|Vnull :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexattrgetprioceiling_absimp_attrerr_abt:
  forall s sch v'4 V_ret P,
    (cmpaddr Cle v'4 userAddrStart = true \/ cmpaddr Clt userAddrEnd v'4 = true) ->  
    V_ret <> Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_getprioceiling_attrerr (|(Vptr v'4) :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexattrgetprioceiling_absimp_attrok_abt_null':
  forall sch s V_ret P,
    can_change_aop P ->
    V_ret = Vint32 (Int.repr EINVAL) -> 
    absinfer sch
      (<||(mutexattr_getprioceiling_attrerr (|Vnull :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| END (Some  (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed. 

Lemma mutexattrgetprioceiling_absimp_attrerr_end:
  forall s sch v'4 V_ret P,
    (cmpaddr Cle v'4 userAddrStart = true \/ cmpaddr Clt userAddrEnd v'4 = true) ->  
    V_ret = Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_getprioceiling_attrerr (|(Vptr v'4) :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| END (Some  (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexattrgetprioceiling_absimp_getstrt_none_abt:
  forall attr pc evheap s t l P sch,
   cmpaddr Clt userAddrStart attr = true ->
   cmpaddr Cle attr userAddrEnd = true ->
   cmpaddr Clt userAddrStart pc = true ->
   cmpaddr Cle pc userAddrEnd = true ->
   (Get_struct evheap attr = None \/
   (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t))->
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_getprioceiling_getstruct_none_abt (|(Vptr attr) :: (Vptr pc) :: nil|) ?? s ||> ** 
              HEvStructHeap evheap ** P)
      (<|| ABORT ||> ** 
          HEvStructHeap evheap ** P). 
Proof.
  intros.
  assert (can_change_aop (HEvStructHeap evheap ** P)).
  pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  clear H1 H2.
  absimp_abt_solver.
Qed.

Lemma mutexattrgetprioceiling_absimp_gethp_none_abt:
  forall pc evhp s t l P sch,
   (Get_heap evhp pc = None \/
   (Get_heap evhp pc = Some (pc, t, l) /\ t <> Tint32))->
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_getprioceiling_gethpnone_abt (| (Vptr pc) :: nil|) ?? s ||> ** 
              HEvAtomHeap evhp ** P)
      (<|| ABORT ||> ** 
          HEvAtomHeap evhp ** P). 
Proof.
  intros.
  assert (can_change_aop (HEvAtomHeap evhp ** P)).
  pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.


Lemma mutexattrgetprioceiling_init_zero_eq_end:
  forall s sch init V_ret P,
    init = Vint32 Int.zero ->
    V_ret = Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_getprioceiling_init_zero_eq (|init :: V_ret :: nil|)) ?? s ||>  ** P)
      (<|| END (Some  (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexattrgetprioceiling_init_zero_eq_abt:
  forall s sch init V_ret P,
    init = Vint32 Int.zero ->
    V_ret <> Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_getprioceiling_init_zero_eq (|init :: V_ret :: nil|)) ?? s ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexattr_getprioceiling_absimp_getinit_ok: 
  forall attr pc evheap e V_init s1 sch P, 
   cmpaddr Clt userAddrStart attr = true ->
   cmpaddr Cle attr userAddrEnd = true ->
   cmpaddr Clt userAddrStart pc = true ->
   cmpaddr Cle pc userAddrEnd = true ->
   Some e = Get_structe evheap attr is_initialized ->
   V_init = e ->
   can_change_aop P -> 
   absinfer sch 
   (<|| mutexattr_getprioceiling_getinit(|(Vptr attr) :: (Vptr pc) :: V_init :: nil|) ;; s1 ||>  **  HEvStructHeap evheap ** P)
   (<||  s1  ||>  **  HEvStructHeap evheap ** P). 
Proof.
  infer_solver 0%nat. 
Qed.

Lemma mutexattr_getprioceiling_absimp_getinit_abt: 
  forall attr pc evheap e V_init s1 sch P, 
   cmpaddr Clt userAddrStart attr = true ->
   cmpaddr Cle attr userAddrEnd = true ->
   cmpaddr Clt userAddrStart pc = true ->
   cmpaddr Cle pc userAddrEnd = true ->
   Some e = Get_structe evheap attr is_initialized ->
   V_init <> e ->
   can_change_aop P -> 
   absinfer sch 
   (<|| mutexattr_getprioceiling_getinit(|(Vptr attr) :: (Vptr pc) :: V_init :: nil|) ;; s1 ||>  **  HEvStructHeap evheap ** P)
   (<||  ABORT ||>  **  HEvStructHeap evheap ** P). 
Proof.
  intros.   
  assert(can_change_aop(HEvStructHeap evheap ** P)).
  can_change_aop_solver.
  eapply absinfer_trans.
  2:{ eapply absinfer_seq_abt; eauto. }
  eapply absinfer_seq; try eauto.
  apply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexattrgetprioceiling_absimp_tp_set_priocl_end:
  forall attr priocl mattrheap V_ret pc evhp evhp'  P sch,
   Some priocl = Get_structe mattrheap attr prio_ceiling ->
   evhp' = Set_sval evhp pc priocl ->
   V_ret = Vint32 (Int.repr 0) ->
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_getprioceiling_tp_set_priocl (|(Vptr attr) :: (Vptr pc) :: V_ret :: nil|) ||> ** 
              HEvStructHeap mattrheap ** HEvAtomHeap evhp ** P)
      (<|| END (Some  (Vint32 (Int.repr 0))) ||> ** 
          HEvStructHeap mattrheap ** HEvAtomHeap evhp' ** P). 
Proof.
  infer_solver 0%nat. 
Qed.

Lemma mutexattrgetprioceiling_absimp_tp_set_priocl_abt:
  forall attr priocl mattrheap V_ret pc evhp evhp'  P sch,
   Some priocl = Get_structe mattrheap attr prio_ceiling ->
   evhp' = Set_sval evhp pc priocl ->
   V_ret <> Vint32 (Int.repr 0) ->
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_getprioceiling_tp_set_priocl (|(Vptr attr) :: (Vptr pc) :: V_ret :: nil|) ||> ** 
              HEvStructHeap mattrheap ** HEvAtomHeap evhp ** P)
      (<|| ABORT ||> ** 
          HEvStructHeap mattrheap ** HEvAtomHeap evhp ** P). 
Proof.
  intros.
  assert (can_change_aop (HEvStructHeap mattrheap ** HEvAtomHeap evhp ** P)).
  pure_auto.
  apply absinfer_abt; eauto.
  absimp_abt_solver.
  instantiate (4:= s).
  sep pauto.
  Unshelve.
  exact nil.
  exact (1%positive,Int.zero).
  exact (END None).
Qed.

Lemma mutexattrgetprioceiling_absimp_ok: 
  forall s1 s2 sch P, 
         can_change_aop P ->
         absinfer sch
           (<|| s1 ?? s2 ||> ** P)
           (<|| s1 ||>  ** P). 
Proof.
  intros.
  eapply absinfer_choice1; eauto.
Qed.

Lemma mutexattrgetprioceiling_absimp_ok2: 
  forall s1 s2 sch P, 
         can_change_aop P ->
         absinfer sch
           (<|| s1 ?? s2 ||> ** P)
           (<|| s2 ||>  ** P). 
Proof.
  intros.
  eapply absinfer_choice2; eauto.
Qed.

Local Open Scope code_scope.

Lemma OSMutexAttrGetprioceilingProof:  
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api pthread_mutexattr_getprioceiling
              (mutexattrgetprioceiling,(Tint32,Tptr pthread_mutexattr_t::nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api pthread_mutexattr_getprioceiling
              (mutexattrgetprioceiling,(Tint32,Tptr pthread_mutexattr_t::nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api pthread_mutexattr_getprioceiling = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}}s {{Afalse}}.
Proof.
   init_spec.
   hoare_lifts_trms_pre Aop.
   do 3 try destruct v'; try apply absabort_rule.
   rename v'5 into er.

(***********ad ′ =ₑ 〈 (long) ∗ 〉 attr ′;ₛ**********)
  hoare forward.
  pure_auto. pure_auto.
  rename x0 into V_attr.
  rename H2 into Hptr.
(*********os_code_defs.x ′ =ᶠ UserAddrCheck (·ad ′·);ₛ************)
  hoare forward.
  pure_auto.
  simpl. destruct Hptr; simpljoin; eauto.
  pure_auto.
  unfold retpost. introv Hsat.
  inverts Hsat.
  sep destruct H. simpl_sat H. simpljoin1. intro Hf. inv Hf.
  sep destruct H. simpl_sat H. simpljoin1. intro Hf. inv Hf.
  pure_auto.
  intros.
  destruct H.
  destruct H; try (sep pauto; sep cancel p_local; sep pauto).
  intros.
  sep pauto. sep cancel p_local. sep pauto.
(****)

  hoare unfold.
  eapply backward_rule1.
  intros.
  apply disj_split in H.
  eauto.
  eapply disj_rule.

  hoare unfold.
  inverts H2.
  assert (Hv: v0 = Vint32 (Int.repr EINVAL) \/ v0 <> Vint32 (Int.repr EINVAL)) by tauto.
  destruct Hv.  
  2: {
    hoare abscsq.
    apply noabs_oslinv.
    destruct Hptr; simpljoin.
    eapply mutexattrgetprioceiling_absimp_attrok_abt_null; eauto.
    can_change_aop_solver.
    destruct H; simpljoin; tryfalse.
    inverts H.
    eapply mutexattrgetprioceiling_absimp_attrerr_abt; eauto.
    can_change_aop_solver.
    apply absabort_rule.
  }
  hoare abscsq.
  apply noabs_oslinv.
  destruct Hptr; simpljoin.
  eapply mutexattrgetprioceiling_absimp_attrok_abt_null'; eauto.
  can_change_aop_solver.
  destruct H; simpljoin; tryfalse.
  inverts H.
  eapply mutexattrgetprioceiling_absimp_attrerr_end; eauto.
  can_change_aop_solver.

(***********If (x ′ ==ₑ ′ 0)**********)
  hoare forward; try rewrite Int.eq_true; simpl val_inj.
  hoare forward.
  hoare forward.
  hoare unfold.
  destruct H2; tryfalse.
  (* x <> 0 *)
  hoare unfold.
  inverts H2.
  hoare forward; change (Int.eq ($ 1) ($ 0)) with false; simpl val_inj.
  hoare unfold. tryfalse.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.

(***********pc ′ =ₑ 〈 (long) ∗ 〉 prioceiling ′;ₛ***************)
  hoare forward.
  pure_auto. pure_auto.
  rename x into V_priocl.
  rename H1 into Hptr'.
(*********y ′ =ᶠ UserAddrCheck (·pc ′·);ₛ************)
  hoare forward.
  pure_auto.
  simpl. destruct Hptr'; simpljoin; eauto.
  pure_auto.
  unfold retpost. introv Hsat.
  inverts Hsat.
  sep destruct H0. simpl_sat H0. simpljoin1. intro Hf. inv Hf.
  sep destruct H0. simpl_sat H0. simpljoin1. intro Hf. inv Hf.
  pure_auto.
  intros.
  destruct H0.
  destruct H0; try (sep pauto; sep cancel p_local; sep pauto).
  intros.
  sep pauto. sep cancel p_local. sep pauto.
(****)

  hoare unfold.
  eapply backward_rule1.
  intros.
  apply disj_split in H0.
  eauto.
  eapply disj_rule.

  hoare unfold.
  inverts H2.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexattrgetprioceiling_absimp_ok2.
  pure_auto.

  assert (Hv: v0 = Vint32 (Int.repr EINVAL) \/ v0 <> Vint32 (Int.repr EINVAL)) by tauto.
  destruct Hv.
  2: {
    hoare abscsq.
    apply noabs_oslinv.
    destruct Hptr'; simpljoin.
    eapply mutexattrgetprioceiling_absimp_mtpok_abt_null; eauto.
    can_change_aop_solver.
    destruct H0; simpljoin; tryfalse.
    inverts H0.
    eapply mutexattrgetprioceiling_absimp_mtperr_abt; eauto.
    can_change_aop_solver.
    apply absabort_rule.
  }
  hoare abscsq.
  apply noabs_oslinv.
  destruct Hptr'; simpljoin.
  eapply mutexattrgetprioceiling_absimp_mtpok_abt_null'; eauto.
  can_change_aop_solver.
  destruct H0; simpljoin; tryfalse.
  inverts H0.
  eapply mutexattrgetprioceiling_absimp_mtperr_end; eauto.
  can_change_aop_solver.

(***********If (y ′ ==ₑ ′ 0)**********)
  hoare forward; try rewrite Int.eq_true; simpl val_inj.
  hoare forward.
  hoare forward.
  hoare unfold.
  destruct H2; tryfalse.
  (* y <> 0 *)
  hoare unfold.
  inverts H2.
  hoare forward; change (Int.eq ($ 1) ($ 0)) with false; simpl val_inj.
  hoare unfold. tryfalse.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.

  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexattrgetprioceiling_absimp_ok2.
  pure_auto.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexattrgetprioceiling_absimp_ok2.
  pure_auto.

  hoare forward prim.
  hoare unfold.
  rename v'21 into vpthattr.
  rename v'22 into vcspace.
  rename v'23 into v23. 
  rename v'24 into v24. 
  rename v'25 into v25. 


  unfold EvtInv.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  rename v'28 into evstructs.
  destruct (Get_struct evstructs x0) eqn: eq1.
  2:{
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrgetprioceiling_absimp_getstrt_none_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.
  }
  rename eq1 into Hget.
  destruct p as ((a & t) & l).
  lets Heq: Get_struct_some_eq Hget. subst a.

  assert (Ht: t = pthread_mutexattr_t \/ t <> pthread_mutexattr_t) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrgetprioceiling_absimp_getstrt_none_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrgetprioceiling_absimp_ok2; eauto.
  pure_auto.
  eapply absinfer_eq.

(*******enter critical********)
  subst.
   hoare_lifts_trms_pre (AEvStructHeap, attr).
   eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold; eauto.
  hoare unfold.

(*******init ′ =ₑ attr ′ → is_initialized;ₛ********)
  hoare forward.
  go.
  assert (Hgete: Get_structe
  (v'17 ++
   (x0, pthread_mutexattr_t,
   Vint32 i5
   :: Vint32 i4
      :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil) :: v'28)
  x0 is_initialized = Some (Vint32 i5)).
  { eapply Get_structe_eq with (id := is_initialized) in H17; eauto.
     2:{ unfolds; simpl; eauto. }
     simpl nth_val in *. auto.
  }

  hoare_lifts_trms_pre (Aop, evstructheapid).
  assert (Hv: v = Vint32 i5 \/ v<> Vint32 i5) by tauto.
  destruct Hv.
  2:{
    eapply abscsq_rule.
    eapply noabs_oslinv.
    eapply mutexattr_getprioceiling_absimp_getinit_abt; eauto.
    pure_auto.
    eapply absinfer_eq.
    eapply absabort_rule. }

    eapply abscsq_rule.
    eapply noabs_oslinv.
    eapply mutexattr_getprioceiling_absimp_getinit_ok; eauto.
    pure_auto.
    eapply absinfer_eq. 

  subst.
  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold.
  exists (Vint32 i5
           :: Vint32 i4
              :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil).
  exists v'17 v'28.
  sep pauto.
  go.

  (*EXIT_CRITICAL*)
  hoare forward prim.
  unfold EvtInv.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.   
  eauto.
  auto.
  pure_auto.

(****If (init ′ ==ₑ ′ 0)******)
  hoare forward; change ($ 0) with Int.zero.
  pure_auto.
  hoare unfold.
  destruct (Int.eq i5 Int.zero) eqn: eq1; simpl val_inj in *; tryfalse.
  eapply OSMutex_common.inteqeq in eq1; subst.

  assert (Hv0: v0 = Vint32 (Int.repr EINVAL) \/ v0 <> Vint32 (Int.repr EINVAL)) by tauto.
  destruct Hv0.
  2:{
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply mutexattrgetprioceiling_init_zero_eq_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }

  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply mutexattrgetprioceiling_init_zero_eq_end; eauto.
  pure_auto.
  eapply absinfer_eq.
  hoare forward.

  hoare forward. 
  hoare unfold.
  clear -H3 H4 H5 H6.

  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrgetprioceiling_absimp_ok2; eauto.
  pure_auto.
  eapply absinfer_eq.

  hoare forward prim.
  hoare unfold.
  rename v'15 into vpthattr.
  rename v'16 into vcspace.
  rename v'17 into v17. 
  rename v'18 into v18. 
  rename v'19 into v19. 


  unfold EvtInv.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  rename v'22 into evstructs.
  destruct (Get_struct evstructs x0) eqn: eq1.
  2:{
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrgetprioceiling_absimp_getstrt_none_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.
  }
  rename eq1 into Hget.
  destruct p as ((a & t) & l).
  lets Heq: Get_struct_some_eq Hget. subst a.

  assert (Ht: t = pthread_mutexattr_t \/ t <> pthread_mutexattr_t) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrgetprioceiling_absimp_getstrt_none_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }
  subst.

  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrgetprioceiling_absimp_ok2; eauto.
  pure_auto.
  eapply absinfer_eq.
  hoare_lifts_trms_pre (Aop, evatomheapid).
  rename v'21 into evatoms.
  destruct (Get_heap evatoms x) eqn: eq2.
  2:{
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrgetprioceiling_absimp_gethp_none_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.
  }
  rename eq2 into Hgete.
  destruct p as ((a' & t') & l').
  lets Heq: Get_heap_some_eq Hgete. subst a'.

  assert (Ht': t' = Tint32 \/ t' <> Tint32) by tauto.
  destruct Ht' as [Hteq | Htneq].
  2:{
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrgetprioceiling_absimp_gethp_none_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }
  subst.

  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrgetprioceiling_absimp_ok2; eauto.
  pure_auto.
  eapply absinfer_eq.


(*******enter critical********)
   hoare_lifts_trms_pre (AEvAtomHeap, prioceiling).
   eapply backward_rule1.
  intros.
  eapply AEvAtomHeap_unfold with (ident := prioceiling); eauto.
  hoare unfold.

  hoare_lifts_trms_pre (AEvStructHeap, attr).
   eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold; eauto.
  hoare unfold.

  (* ∗ prioceiling ′ =ₑ attr ′ → prio_ceiling;ₛ *)
  hoare forward.
  go.
  assert (Hgete': Get_structe
  (v'22 ++
   (x0, pthread_mutexattr_t,
   Vint32 i7
   :: Vint32 i6
      :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
   :: v'34) x0 prio_ceiling = Some (Vint32 i4)).
  { eapply Get_structe_eq with (id := prio_ceiling) in H16; eauto.
     2:{ unfolds; simpl; eauto. }
     simpl nth_val in *. auto.
  }

  hoare_lifts_trms_pre (Aop, evstructheapid, evatomheapid).
  assert (Hv: v0 = Vint32 Int.zero \/ v0 <> Vint32 Int.zero ) by tauto.
  destruct Hv as [ Ht | Hf].
  2:{
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply mutexattrgetprioceiling_absimp_tp_set_priocl_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply mutexattrgetprioceiling_absimp_tp_set_priocl_end; eauto.
  pure_auto.
  eapply absinfer_eq.

  subst.
  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold.
  exists (Vint32 i7
   :: Vint32 i6
      :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil).
  exists v'22 v'34.
  sep pauto.
  go.

  assert (Heq: (Set_sval (v'11 ++ (x, long, Vint32 i) :: v'21) x (Vint32 i4)) = 
       (v'11 ++ (x, long, Vint32 i4) :: v'21)  ).
  { eapply Set_sval_eq; eauto. }
  rewrite Heq.

  eapply backward_rule1. 
  intros.
  eapply AEvAtomHeap_fold with (x:= x) (ident:= prioceiling).
  exists ( Vint32 i4) v'11 v'21.
  sep pauto.

  (*EXIT_CRITICAL*)
  hoare forward prim.
  unfold EvtInv.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr. 
  sep cancel CapabilityInv.  
  eauto.
  auto.
  pure_auto.

(***********RETURN ′ 0***********)
  hoare forward.
  Unshelve.
  exact Tnull.
  exact nil.
  exact Tnull.
  exact nil.
  exact Tnull. exact Vundef.
Qed.

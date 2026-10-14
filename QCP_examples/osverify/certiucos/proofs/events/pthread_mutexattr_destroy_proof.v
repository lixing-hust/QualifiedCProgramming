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

Open Scope list_scope.
Open Scope int_scope.
Open Scope code_scope.
Open Scope Z_scope.

Lemma mutexattrdestroy_absimp_attrok_abt_null:
  forall sch s V_ret P,
    can_change_aop P ->
    V_ret <> Vint32 (Int.repr EINVAL) -> 
    absinfer sch
      (<||
          (mutexattr_destroy_attrerr (|Vnull :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexattrdestroy_absimp_attrerr_abt:
  forall s sch v'4 V_ret P,
    (cmpaddr Cle v'4 userAddrStart = true \/ cmpaddr Clt userAddrEnd v'4 = true) ->  
    V_ret <> Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_destroy_attrerr (|(Vptr v'4) :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexattrdestroy_absimp_attrok_abt_null':
  forall sch s V_ret P,
    can_change_aop P ->
    V_ret = Vint32 (Int.repr EINVAL) -> 
    absinfer sch
      (<||(mutexattr_destroy_attrerr (|Vnull :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| END (Some  (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexattrdestroy_absimp_attrerr_end:
  forall s sch v'4 V_ret P,
    (cmpaddr Cle v'4 userAddrStart = true \/ cmpaddr Clt userAddrEnd v'4 = true) ->  
    V_ret = Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_destroy_attrerr (|(Vptr v'4) :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| END (Some  (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexattrdestroy_absimp_abt1:
  forall attr evheap s t l P sch,
   (Get_struct evheap attr = None \/
   (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t))->
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_destroy_validptr_err (|(Vptr attr) :: nil|) ?? s ||> ** 
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
  absimp_abt_solver.
Qed.

Lemma mutexattrdestroy_absimp_initialize_end:
  forall attr V_ret evheap vl P sch,
   cmpaddr Clt userAddrStart attr = true ->
   cmpaddr Cle attr userAddrEnd = true ->
   Get_struct evheap attr = Some (attr, pthread_mutexattr_t, vl) ->
   V_ret = Vint32 (Int.repr 0) -> 
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_destroy_clearinit (|(Vptr attr) :: V_ret :: nil|) ||> ** 
              HEvStructHeap evheap ** P)
      (<|| END (Some  (Vint32 (Int.repr 0))) ||> ** 
          HEvStructHeap (Set_struct' evheap attr is_initialized (Vint32 Int.zero)) ** P). 
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexattrdestroy_absimp_initialize_abt1:
  forall attr V_ret evheap t vl P sch,
   cmpaddr Clt userAddrStart attr = true ->
   cmpaddr Cle attr userAddrEnd = true ->
   Get_struct evheap attr = Some (attr, t, vl) ->
   t = pthread_mutexattr_t ->
   V_ret <> Vint32 (Int.repr 0) -> 
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_destroy_clearinit (|(Vptr attr) :: V_ret :: nil|) ||> ** 
              HEvStructHeap evheap ** P)
      (<|| ABORT ||> ** 
          HEvStructHeap evheap ** P). 
Proof.
  intros.
  assert (can_change_aop (HEvStructHeap evheap ** P)).
  pure_auto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexinit_absimp_ok: 
  forall s1 s2 sch P, 
         can_change_aop P ->
         absinfer sch
           (<|| s1 ?? s2 ||> ** P)
           (<|| s1 ||>  ** P). 
Proof.
  intros.
  eapply absinfer_choice1; eauto.
Qed.

Lemma mutexinit_absimp_ok2: 
  forall s1 s2 sch P, 
         can_change_aop P ->
         absinfer sch
           (<|| s1 ?? s2 ||> ** P)
           (<|| s2 ||>  ** P). 
Proof.
  intros.
  eapply absinfer_choice2; eauto.
Qed.

Lemma OSMutexAttrDestroyProof:  
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api pthread_mutexattr_destroy
              (mutexattrdestroy,(Tint32,Tptr pthread_mutexattr_t::nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api pthread_mutexattr_destroy
              (mutexattrdestroy,(Tint32,Tptr pthread_mutexattr_t::nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api pthread_mutexattr_destroy = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  do 2 try destruct v'; try apply absabort_rule.
  rename v'2 into er.
  hoare forward.
  pure_auto. pure_auto.
  rename x into V_attr.
  rename H1 into Hptr.

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

  hoare unfold.
  eapply backward_rule1.
  intros.
  apply disj_split in H.
  eauto.
  eapply disj_rule.

  hoare unfold.
  inverts H1.
  assert (Hv: v = Vint32 (Int.repr EINVAL) \/ v <> Vint32 (Int.repr EINVAL)) by tauto.
  destruct Hv.
  2: {
    hoare abscsq.
    apply noabs_oslinv.
    destruct Hptr; simpljoin.
    eapply mutexattrdestroy_absimp_attrok_abt_null; eauto.
    can_change_aop_solver.
    destruct H; simpljoin; tryfalse.
    inverts H.
    eapply mutexattrdestroy_absimp_attrerr_abt; eauto.
    can_change_aop_solver.
    apply absabort_rule.
  }
  hoare abscsq.
  apply noabs_oslinv.
  destruct Hptr; simpljoin.
  eapply mutexattrdestroy_absimp_attrok_abt_null'; eauto.
  can_change_aop_solver.
  destruct H; simpljoin; tryfalse.
  inverts H.
  eapply mutexattrdestroy_absimp_attrerr_end; eauto.
  can_change_aop_solver.

  hoare forward; try rewrite Int.eq_true; simpl val_inj.
  hoare forward.
  hoare forward.
  hoare unfold.
  destruct H1; tryfalse.
  (* x <> 0 *)
  hoare unfold.
  inverts H1.
  hoare forward; change (Int.eq ($ 1) ($ 0)) with false; simpl val_inj.
  hoare unfold. tryfalse.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.

  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexinit_absimp_ok2.
  pure_auto.

  hoare forward prim.
  hoare unfold.
  rename v'17 into vpthattr.
  rename v'18 into vcspace.
  rename v'19 into v19. 
  rename v'20 into v20. 
  rename v'21 into v21. 


  unfold EvtInv.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  rename v'24 into evstructs.
  destruct (Get_struct evstructs x) eqn: eq1.
  2:{
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrdestroy_absimp_abt1; eauto.
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
  eapply mutexattrdestroy_absimp_abt1; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }

  hoare_lifts_trms_pre (Aop, evstructheapid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexinit_absimp_ok2. pure_auto. 
  eapply absinfer_eq.
(*******enter critical********)
  subst.
   hoare_lifts_trms_pre (AEvStructHeap, attr).
   eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold; eauto.
  hoare unfold.

 (*******attr -> is_initialized = 0*********)
  hoare forward.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  assert (Hr: v = Vint32 Int.zero \/ v <> Vint32 Int.zero) by tauto.
  destruct Hr.
  2:{
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutexattrdestroy_absimp_initialize_abt1; eauto.
    pure_auto.
    eapply absinfer_eq.
    eapply absabort_rule. }
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutexattrdestroy_absimp_initialize_end ; eauto.
    pure_auto.
    eapply absinfer_eq.

  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold.
  exists (V$ 0
            :: Vint32 i4
               :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil).
  exists v'13 v'24.
  sep pauto.
  struct_type_match_solver.
  subst.

  assert (Heq: Set_struct'
       (v'13 ++
        (x, pthread_mutexattr_t,
        Vint32 i5
        :: Vint32 i4
           :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
        :: v'24) x is_initialized (Vint32 Int.zero) = 
       (v'13 ++
     (x, pthread_mutexattr_t,
     Vint32 Int.zero
     :: Vint32 i4
        :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
     :: v'24)  ).
  { eapply set_struct_update_nth_val'; eauto.
     unfolds; simpl; eauto.
     simpl; auto.
  }
  rewrite Heq.

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
  change ( Vint32 Int.zero
   :: Vint32 i4
      :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil) with
    (update_nth_val 0 ( Vint32 i5
   :: Vint32 i4
      :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil) (Vint32 Int.zero)).
  eapply R_Q_Data_P_muxattr; eauto.
  auto.
  pure_auto.
  hoare forward.
  Unshelve.
  exact Tnull.
  trivial.
Qed.

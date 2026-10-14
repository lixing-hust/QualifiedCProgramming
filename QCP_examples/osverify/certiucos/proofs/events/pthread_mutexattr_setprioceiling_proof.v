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
Require Import symbolic_lemmas.

Require Import evt_spec_defs.
Require Import OSTimeTickPure.
Require Import gjb_common.
Require Import gjb_mutex_common.
Require Import evheap_pure.

Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Open Scope list_scope.
Open Scope Z_scope.
Open Scope code_scope.
Open Scope int_scope.

Lemma mutexattrsetprioceiling_absimp_attrok_abt_null:
  forall sch s V_ret P,
    can_change_aop P ->
    V_ret <> Vint32 (Int.repr EINVAL) -> 
    absinfer sch
      (<||(mutexattr_setprioceiling_attrerr (|Vnull :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexattrsetprioceiling_absimp_attrerr_abt:
  forall s sch v'4 V_ret P,
    (cmpaddr Cle v'4 userAddrStart = true \/ cmpaddr Clt userAddrEnd v'4 = true) ->  
    V_ret <> Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_setprioceiling_attrerr (|(Vptr v'4) :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexattrsetprioceiling_absimp_attrok_abt_null':
  forall sch s V_ret P,
    can_change_aop P ->
    V_ret = Vint32 (Int.repr EINVAL) -> 
    absinfer sch
      (<||(mutexattr_setprioceiling_attrerr (|Vnull :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| END (Some  (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexattrsetprioceiling_absimp_attrerr_end:
  forall s sch v'4 V_ret P,
    (cmpaddr Cle v'4 userAddrStart = true \/ cmpaddr Clt userAddrEnd v'4 = true) ->  
    V_ret = Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_setprioceiling_attrerr (|(Vptr v'4) :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| END (Some  (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexattrsetprioceiling_absimp_getstrt_none_abt:
  forall attr evheap s t l P sch,
   cmpaddr Clt userAddrStart attr = true ->
   cmpaddr Cle attr userAddrEnd = true ->
   (Get_struct evheap attr = None \/
   (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t))->
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_setprioceiling_getstruct_none_abt (|(Vptr attr) :: nil|) ?? s ||> ** 
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

Lemma mutexattrsetprioceiling_absimp_getstrt_none_pc_abt:
  forall attr pc evheap s t l P sch,
   cmpaddr Clt userAddrStart attr = true ->
   cmpaddr Cle attr userAddrEnd = true ->
    Int.ltu pc Int.zero = false ->
    Int.ltu ($ OS_MAX_TASKS) pc = false ->
   (Get_struct evheap attr = None \/
   (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t))->
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_setprioceiling_getstruct_none_pc_abt (|(Vptr attr) :: (Vint32 pc) :: nil|) ?? s ||> ** 
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

Lemma mutexattrsetprioceiling_init_zero_eq_end:
  forall s sch init V_ret P,
    init = Vint32 Int.zero ->
    V_ret = Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_setprioceiling_init_zero_eq (|init :: V_ret :: nil|)) ?? s ||>  ** P)
      (<|| END (Some  (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexattrsetprioceiling_init_zero_eq_abt:
  forall s sch init V_ret P,
    init = Vint32 Int.zero ->
    V_ret <> Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_setprioceiling_init_zero_eq (|init :: V_ret :: nil|)) ?? s ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexattr_setprioceiling_absimp_getinit_ok: 
  forall attr evheap e V_init s1 sch P, 
   cmpaddr Clt userAddrStart attr = true ->
   cmpaddr Cle attr userAddrEnd = true ->
   Some e = Get_structe evheap attr is_initialized ->
   V_init = e ->
   can_change_aop P -> 
   absinfer sch 
   (<|| mutexattr_setprioceiling_getinit(|(Vptr attr) :: V_init :: nil|) ;; s1 ||>  **  HEvStructHeap evheap ** P)
   (<||  s1  ||>  **  HEvStructHeap evheap ** P). 
Proof.
  infer_solver 0%nat. 
Qed.

Lemma mutexattr_setprioceiling_absimp_getinit_abt: 
  forall attr evheap e V_init s1 sch P, 
   cmpaddr Clt userAddrStart attr = true ->
   cmpaddr Cle attr userAddrEnd = true ->
   Some e = Get_structe evheap attr is_initialized ->
   V_init <> e ->
   can_change_aop P -> 
   absinfer sch 
   (<|| mutexattr_setprioceiling_getinit(|(Vptr attr) :: V_init :: nil|) ;; s1 ||>  **  HEvStructHeap evheap ** P)
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

Lemma mutexattrsetprioceiling_priocl_end:
  forall s sch priocl V_ret P,
    (Int.ltu priocl Int.zero = true \/
    Int.ltu (Int.repr OS_MAX_TASKS) priocl = true ) ->
    V_ret = Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_setprioceiling_priocl_err (|(Vint32 priocl) :: V_ret :: nil|)) ?? s ||>  ** P)
      (<|| END (Some  (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexattrsetprioceiling_priocl_abt:
  forall s sch priocl V_ret P,
    (Int.ltu priocl Int.zero = true \/
    Int.ltu (Int.repr OS_MAX_TASKS) priocl = true ) ->
    V_ret <> Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_setprioceiling_priocl_err (|(Vint32 priocl) :: V_ret :: nil|)) ?? s ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexattrsetprioceiling_absimp_getstruct_none_abt:
  forall attr evheap pc s t l P sch,
   cmpaddr Clt userAddrStart attr = true ->
   cmpaddr Cle attr userAddrEnd = true ->
   Int.ltu pc Int.zero = false ->
   Int.ltu ($ OS_MAX_TASKS) pc = false ->
   (Get_struct evheap attr = None \/
   (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t))->
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_setprioceiling_getstruct_none_pc_abt (|(Vptr attr) :: (Vint32 pc) :: nil|) ?? s ||> **
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

Lemma mutexattrsetprioceiling_extcb_priocl_end:
  forall s sch ptls priocl tid V_ret P,
   Int.ltu priocl Int.zero = false ->
   Int.ltu (Int.repr OS_MAX_TASKS) priocl = false ->
     (get ptls priocl = Some (Valid_Addr tid) \/
     get ptls priocl = Some Holder) ->
    V_ret = Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_setprioceiling_extcb_priocl_err (|(Vint32 priocl) :: V_ret :: nil|)) ?? s ||> ** HPriotls ptls ** P)
      (<|| END (Some  (Vint32 (Int.repr EINVAL))) ||> ** HPriotls ptls ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexattrsetprioceiling_extcb_priocl_abt:
  forall s sch ptls priocl tid V_ret P,
   Int.ltu priocl Int.zero = false ->
   Int.ltu (Int.repr OS_MAX_TASKS) priocl = false ->
    (get ptls priocl = Some (Valid_Addr tid) \/
     get ptls priocl = Some Holder) ->
    V_ret <> Vint32 (Int.repr EINVAL) -> 
    can_change_aop P ->
    absinfer sch
      (<|| (mutexattr_setprioceiling_extcb_priocl_err (|(Vint32 priocl) :: V_ret :: nil|)) ?? s ||> ** HPriotls ptls ** P)
      (<|| ABORT ||> ** HPriotls ptls ** P).
Proof.
  intros.
  assert (can_change_aop (HPriotls ptls ** P)).
  pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexattrsetprioceiling_none_setpriocl_end:
  forall sch attr ptls priocl evheap l evheap' V_ret P,
   Int.ltu priocl Int.zero = false ->
   Int.ltu (Int.repr OS_MAX_TASKS) priocl = false ->
     get ptls priocl = Some Null ->
    Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) ->
    V_ret = Vint32 (Int.repr 0) -> 
    evheap' = Set_struct' evheap attr prio_ceiling (Vint32 priocl) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_setprioceiling_none_setpriocl (|(Vptr attr) :: (Vint32 priocl) :: V_ret :: nil|)) ||> 
        ** HPriotls ptls ** HEvStructHeap evheap ** P)
      (<|| END (Some  (Vint32 (Int.repr 0))) ||> ** HPriotls ptls ** HEvStructHeap evheap' ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexattrsetprioceiling_none_setpriocl_abt:
  forall sch attr ptls priocl evheap l V_ret P,
   Int.ltu priocl Int.zero = false ->
   Int.ltu (Int.repr OS_MAX_TASKS) priocl = false ->
     get ptls priocl = Some Null ->
    Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) ->
    V_ret <> Vint32 (Int.repr 0) ->
    can_change_aop P ->
    absinfer sch
      (<|| (mutexattr_setprioceiling_none_setpriocl (|(Vptr attr) :: (Vint32 priocl) :: V_ret :: nil|)) ||> ** 
      HPriotls ptls ** HEvStructHeap evheap ** P)
      (<|| ABORT ||> ** HPriotls ptls ** HEvStructHeap evheap ** P).
Proof.
  intros.
  assert (can_change_aop (HPriotls ptls ** HEvStructHeap evheap ** P)).
  pure_auto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
  instantiate (3:= s).
  sep pauto.
  Unshelve.
  exact nil.
  exact (END None).
Qed.


Lemma mutexattrsetprioceiling_absimp_ok: 
  forall s1 s2 sch P, 
         can_change_aop P ->
         absinfer sch
           (<|| s1 ?? s2 ||> ** P)
           (<|| s1 ||>  ** P). 
Proof.
  intros.
  eapply absinfer_choice1; eauto.
Qed.

Lemma mutexattrsetprioceiling_absimp_ok2: 
  forall s1 s2 sch P, 
         can_change_aop P ->
         absinfer sch
           (<|| s1 ?? s2 ||> ** P)
           (<|| s2 ||>  ** P). 
Proof.
  intros.
  eapply absinfer_choice2; eauto.
Qed.

Lemma R_MutexAttr_P_hold:
forall vl v ,
(0 <= Int.unsigned v < 64)%Z ->
R_MutexAttr_P pthread_mutexattr_t vl->
R_MutexAttr_P pthread_mutexattr_t
  (update_nth_val 2 vl (Vint32 v)).
Proof. 
  unfold R_MutexAttr_P in *.
  intros.
  destruct H0; auto.
  eexists v.
  splits; eauto.
  unfold V_muxattr_prioceiling. 
  destruct H0.
  eapply pure_lib.update_nth; eauto.
  destruct H; eauto. 
  destruct H; eauto. 
Qed.


Lemma OSMutexAttrSetprioceilingProof:  
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api pthread_mutexattr_setprioceiling
              (mutexattrsetprioceiling,(Tint32,Tptr pthread_mutexattr_t::nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api pthread_mutexattr_setprioceiling
              (mutexattrsetprioceiling,(Tint32,Tptr pthread_mutexattr_t::nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api pthread_mutexattr_setprioceiling = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}}s {{Afalse}}.
Proof.
   init_spec.
   hoare_lifts_trms_pre Aop.
   do 3 try destruct v'; try apply absabort_rule.
   rename v'3 into er.

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
  inverts H1.
  assert (Hv: v0 = Vint32 (Int.repr EINVAL) \/ v0 <> Vint32 (Int.repr EINVAL)) by tauto.
  destruct Hv.  
  2: {
    hoare abscsq.
    apply noabs_oslinv.
    destruct Hptr; simpljoin.
    eapply mutexattrsetprioceiling_absimp_attrok_abt_null; eauto.
    can_change_aop_solver.
    destruct H; simpljoin; tryfalse.
    inverts H.
    eapply mutexattrsetprioceiling_absimp_attrerr_abt; eauto.
    can_change_aop_solver.
    apply absabort_rule.
  }
  hoare abscsq.
  apply noabs_oslinv.
  destruct Hptr; simpljoin.
  eapply mutexattrsetprioceiling_absimp_attrok_abt_null'; eauto.
  can_change_aop_solver.
  destruct H; simpljoin; tryfalse.
  inverts H.
  eapply mutexattrsetprioceiling_absimp_attrerr_end; eauto.
  can_change_aop_solver.

(***********If (x ′ ==ₑ ′ 0)**********)
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
  (* ENTER_CRITICAL;ₛ
       init ′ =ₑ attr ′ → is_initialized;ₛ
       EXIT_CRITICAL;ₛ *)
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexattrsetprioceiling_absimp_ok2.
  pure_auto.

  hoare forward prim.
  hoare unfold.
  rename v'18 into vpthattr.
  rename v'19 into vcspace.
  rename v'20 into v20. 
  rename v'21 into v21. 
  rename v'22 into v22. 

  unfold EvtInv.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  rename v'25 into evstructs.
  destruct (Get_struct evstructs x) eqn: eq1.
  2:{
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrsetprioceiling_absimp_getstrt_none_abt; eauto.
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
  eapply mutexattrsetprioceiling_absimp_getstrt_none_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrsetprioceiling_absimp_ok2; eauto.
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
  (v'14 ++
   (x, pthread_mutexattr_t,
   Vint32 i6
   :: Vint32 i5
      :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) :: v'25)
  x is_initialized = Some (Vint32 i6)).
  { eapply Get_structe_eq with (id := is_initialized) in H14; eauto.
     2:{ unfolds; simpl; eauto. }
     simpl nth_val in *. auto.
  }

  hoare_lifts_trms_pre (Aop, evstructheapid).
  assert (Hv: v = Vint32 i6 \/ v<> Vint32 i6) by tauto.
  destruct Hv.
  2:{
    eapply abscsq_rule.
    eapply noabs_oslinv.
    eapply mutexattr_setprioceiling_absimp_getinit_abt; eauto.
    pure_auto.
    eapply absinfer_eq.
    eapply absabort_rule. }

    eapply abscsq_rule.
    eapply noabs_oslinv.
    eapply mutexattr_setprioceiling_absimp_getinit_ok; eauto.
    pure_auto.
    eapply absinfer_eq. 

  subst.
  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold.
  exists (Vint32 i6
           :: Vint32 i5
              :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil).
  exists v'14 v'25.
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
  destruct (Int.eq i6 Int.zero) eqn: eq1; simpl val_inj in *; tryfalse.
  eapply OSMutex_common.inteqeq in eq1; subst.

  assert (Hv0: v0 = Vint32 (Int.repr EINVAL) \/ v0 <> Vint32 (Int.repr EINVAL)) by tauto.
  destruct Hv0.
  2:{
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply mutexattrsetprioceiling_init_zero_eq_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }

  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply mutexattrsetprioceiling_init_zero_eq_end; eauto.
  pure_auto.
  eapply absinfer_eq.
  hoare forward.

  hoare forward. 
  hoare unfold.

  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrsetprioceiling_absimp_ok2; eauto.
  pure_auto.
  eapply absinfer_eq.
  clear -H2 H3.
  (* If (CFalse >ₑ prioceiling ′ ||ₑ prioceiling ′ >ₑ ′ OS_MAX_TASKS){RETURN ′ EINVAL};ₛ *)
  hoare forward.
  pure_auto.
  pure_auto.
  pure_auto.
  hoare unfold.
  assert (Hpc:  Int.ltu i Int.zero = true \/ Int.ltu ($ OS_MAX_TASKS) i = true).
  {
     destruct (Int.ltu i Int.zero) eqn: eq1;
     destruct (Int.ltu ($ OS_MAX_TASKS) i) eqn: eq2;
     simpl in *; tryfalse; auto.
   }

  assert (Hv0: v0 = Vint32 (Int.repr EINVAL) \/ v0 <> Vint32 (Int.repr EINVAL)) by tauto.
  destruct Hv0.
  2:{
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply mutexattrsetprioceiling_priocl_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply mutexattrsetprioceiling_priocl_end; eauto.
  pure_auto.
  eapply absinfer_eq.
  hoare forward.
  hoare forward.
  hoare unfold.
  assert (Hpc: Int.ltu i Int.zero = false /\ Int.ltu ($ OS_MAX_TASKS) i = false).
  {
     destruct (Int.ltu i Int.zero) eqn: eq1;
     destruct (Int.ltu ($ OS_MAX_TASKS) i) eqn: eq2;
     simpl val_inj in *;
     try change (Int.ltu Int.zero Int.one) with true in *;
     try change (Int.ltu Int.zero Int.zero) with false in *;
     simpl val_inj in *;
     destruct H;
     tryfalse; auto.
   }
  clear H. destruct Hpc as (Hr1 & Hr2).
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrsetprioceiling_absimp_ok2; eauto.
  pure_auto.
  eapply absinfer_eq.
  (* ENTER_CRITICAL;ₛ *)
  hoare forward prim.
  hoare unfold.
  rename v'15 into vpthattr.
  rename v'16 into vcspace.
  rename v'17 into v17. 
  rename v'18 into v18. 
  rename v'19 into v19. 

  rename v'20 into v'15. 
  unfold EvtInv.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  rename v'23 into evstructs.
  destruct (Get_struct evstructs x) eqn: eq1.
  2:{
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrsetprioceiling_absimp_getstrt_none_pc_abt; eauto.
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
  eapply mutexattrsetprioceiling_absimp_getstrt_none_pc_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }
  subst.

  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrsetprioceiling_absimp_ok2; eauto.
  pure_auto.
  eapply absinfer_eq.
(*******enter critical********)
  (* If (OSTCBPrioTbl ′ [prioceiling ′] !=ₑ NULL) *)
  assert (Hpc: (Z.to_nat (Int.unsigned i) < 64)%nat).
  { change (OS_MAX_TASKS) with 30 in *.
    int auto. }
  assert (Hmat: rule_type_val_match OS_TCB ∗ (nth_val' (Z.to_nat (Int.unsigned i)) v') = true).
  { eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
     rewrite H7; auto with zarith.
   }
  lets Hptr : rule_type_val_match_ptr_elim Hmat.
  hoare forward.
  rewrite Hmat; auto.
  pure_auto.
  pure_auto.
  hoare unfold.
  destruct Hptr as [Hvq | ((vp_b & vp_i) & Hvq)]; rewrite Hvq in *;
  simpl val_inj in *;
  try change (Int.notbool Int.one) with Int.zero in *;
  simpl in H9; tryfalse.
  assert (Hgetp: get v'14 i = Some (Valid_Addr (vp_b, vp_i)) \/ 
                           get v'14 i = Some Holder).
  { assert (Hc: (vp_b, vp_i) = vhold_addr \/ (vp_b, vp_i) <> vhold_addr) by tauto.
     destruct Hc as [Heq | Hneq]; [right | left]; try rewrite Heq in *;
     eapply H6; eauto; try solve [ unfold OS_MAX_TASKS in *; int auto] ;auto with zarith;
     unfold nat_of_Z;
     eapply nth_val'_imply_nth_val; eauto;
     rewrite H7;
     auto with zarith.
   }
  hoare_lifts_trms_pre (Aop, absptlsid).
  assert (Hv0: v0 = Vint32 (Int.repr EINVAL) \/ v0 <> Vint32 (Int.repr EINVAL)) by tauto.
  destruct Hv0.
  2:{
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply mutexattrsetprioceiling_extcb_priocl_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }
  subst.
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply mutexattrsetprioceiling_extcb_priocl_end; eauto.
  pure_auto.
  eapply absinfer_eq.
  hoare forward prim.
  sep cancel CoreCommuInv.
  sep cancel p_local.
  sep cancel Aier.  
  sep cancel APthreadAttr.
  sep cancel CapabilityInv. 
  unfold EvtInv.
  unfold AOSTCBPrioTbl.
  sep pauto; eauto.
  auto.
  pure_auto.
  hoare forward.
  hoare forward.
  (* attr ′ → prio_ceiling =ₑ prioceiling ′;ₛ *)
  hoare unfold.
  destruct Hptr as [Hvq | ((vp_b & vp_i) & Hvq)]; rewrite Hvq in *;
  simpl val_inj in *;
  try change (Int.notbool Int.zero) with Int.one in *;
  simpl in H9; destruct H9; tryfalse.
  assert (Hgetp: get v'14 i = Some Null).
  { eapply H6; eauto. unfold OS_MAX_TASKS in *. int auto.
     unfold nat_of_Z.
     eapply nth_val'_imply_nth_val; eauto.
     rewrite H7.
     auto with zarith.
   }
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrsetprioceiling_absimp_ok2; eauto.
  pure_auto.
  eapply absinfer_eq.
  hoare_lifts_trms_pre (Aop, absptlsid, evstructheapid).
  assert (Hv0: v0 = Vint32 (Int.repr 0) \/ v0 <> Vint32 (Int.repr 0)) by tauto.
  destruct Hv0.
  2:{
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply mutexattrsetprioceiling_none_setpriocl_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }
  subst.
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply mutexattrsetprioceiling_none_setpriocl_end; eauto.
  pure_auto.
  eapply absinfer_eq.
  (* attr ′ → prio_ceiling =ₑ prioceiling ′;ₛ *)
   hoare_lifts_trms_pre (AEvStructHeap, attr).
   eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold; eauto.
  hoare unfold.

  hoare forward.
  assert (Hrgn: 0 <= Int.unsigned i < 64).
  { clear -Hpc.
    int auto.
   }
  destruct Hrgn as (Hrgn1 & Hrgn2).
  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_fold.
  exists (update_nth_val 2 (Vint32 i7
              :: Vint32 i5
                 :: Vint32 i4
                    :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) (Vint32 i)).
  exists v'11 v'23.
  sep split; eauto.
  sep pauto.
  eapply R_MutexAttr_P_hold; eauto.
  struct_type_match_solver.
  subst.
  simpl update_nth_val.

  assert (Heq: Set_struct'
       (v'11 ++
        (x, pthread_mutexattr_t,
        Vint32 i7
     :: Vint32 i5
        :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
        :: v'23) x prio_ceiling (Vint32 i) = 
       (v'11 ++
     (x, pthread_mutexattr_t,
     Vint32 i7
     :: Vint32 i5
        :: Vint32 i :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
     :: v'23)  ).
  { eapply set_struct_update_nth_val'; eauto.
     unfolds; simpl; eauto.
     simpl; auto.
  }
  rewrite Heq.

  hoare forward prim.
  unfold EvtInv.
  unfold AOSTCBPrioTbl.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel p_local.
  sep cancel Aier.  
  sep cancel APthreadAttr.
  sep cancel CapabilityInv. 
  sep cancel vhold_addr.
  sep cancel OSPlaceHolder.
  eauto.
  change ( Vint32 i7
     :: Vint32 i5
        :: Vint32 i :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) with
    (update_nth_val 2 (Vint32 i7
     :: Vint32 i5
        :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) (Vint32 i)).
  eapply R_Q_Data_P_muxattr; eauto.
  auto.
  pure_auto.
  hoare forward.
  Unshelve.
  exact Tnull.
  exact nil.
  exact Tnull.
  exact nil.
Qed.



Require Import include_frm. 
Require Import NPeano.
Require Import os_code_defs. 
Require Import code_notations. 
Require Import os_ucos_h. 
Require Import os_mutex.
Require Import gjb_common.
Require Import gjb_mutex_common.
Require Import OSMutexPendPure1.
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
Require Import evauxvar_lemmas.

Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Open Scope list_scope.
Open Scope Z_scope.
Open Scope code_scope.
Open Scope int_scope.

Lemma mutexattrinit_absimp_attrok_abt_null:
  forall sch s V_ret P,
    can_change_aop P ->
    V_ret <> Vint32 (Int.repr EINVAL) -> 
    absinfer sch
      (<|| (mutexattr_init_attrerr (|Vnull :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed. 

Lemma mutexattrinit_absimp_attrerr_abt:
  forall s sch v'4 V_ret P,
    (cmpaddr Cle v'4 userAddrStart = true \/ cmpaddr Clt userAddrEnd v'4 = true) ->  
    V_ret <> Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_init_attrerr (|(Vptr v'4) :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexattrinit_absimp_attrok_abt_null':
  forall sch s V_ret P,
    can_change_aop P ->
    V_ret = Vint32 (Int.repr EINVAL) -> 
    absinfer sch
      (<||
          (mutexattr_init_attrerr (|Vnull :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| END (Some  (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed. 

Lemma mutexattrinit_absimp_attrerr_end:
  forall s sch v'4 V_ret P,
    (cmpaddr Cle v'4 userAddrStart = true \/ cmpaddr Clt userAddrEnd v'4 = true) ->  
    V_ret = Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_init_attrerr (|(Vptr v'4) :: V_ret :: nil|) ?? s) ||>  ** P)
      (<|| END (Some  (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
 infer_solver 0%nat.
Qed.

Lemma mutexattrinit_absimp_init_end:
  forall attr evheap vl s P sch,
   cmpaddr Clt userAddrStart attr = true ->
   cmpaddr Cle attr userAddrEnd = true ->
   Get_struct evheap attr = Some (attr, pthread_mutexattr_t, vl) ->
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_init_set1_init (|(Vptr attr) :: nil|) ;; s ||> ** 
              HEvStructHeap evheap ** P)
      (<|| s ||> ** 
          HEvStructHeap (Set_struct' evheap attr is_initialized (Vint32 Int.one)) ** P). 
Proof.
  infer_solver 0%nat. 
  Unshelve.
  exact Tnull.
Qed.

Lemma mutexattrinit_absimp_init_abt:
  forall attr evheap l t s P sch,
   cmpaddr Clt userAddrStart attr = true ->
   cmpaddr Cle attr userAddrEnd = true ->
  (Get_struct evheap attr = None \/
  (Get_struct evheap attr = Some (attr, t, l)/\  t <> pthread_mutexattr_t))->
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_init_set1_init (|(Vptr attr) :: nil|) ;; s ||> ** 
              HEvStructHeap evheap ** P)
      (<|| ABORT ||> ** 
          HEvStructHeap evheap ** P). 
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

Lemma mutexattrinit_absimp_proc_abt:
  forall attr evheap t l s P sch,
  (Get_struct evheap attr = None \/
  (Get_struct evheap attr = Some (attr, t, l)/\  t <> pthread_mutexattr_t))->
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_init_set1_proc (|(Vptr attr) :: nil|) ;; s ||> ** 
              HEvStructHeap evheap ** P)
      (<|| ABORT ||> ** 
          HEvStructHeap evheap ** P). 
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

Lemma mutexattrinit_absimp_proc_end:
  forall attr evheap vl s P sch,
   Get_struct evheap attr = Some (attr, pthread_mutexattr_t, vl) ->
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_init_set1_proc (|(Vptr attr) :: nil|) ;; s ||> ** 
              HEvStructHeap evheap ** P)
      (<|| s ||> ** 
          HEvStructHeap (Set_struct' evheap attr process_shared (Vint32 Int.one)) ** P). 
Proof.
  infer_solver 0%nat.
  Unshelve.
  exact Tnull. 
Qed.

Lemma mutexattrinit_absimp_priocl_abt:
  forall attr evheap l t ct tls pr st m sus s P sch,
   get tls ct = Some (pr,st,m, sus) ->
  (Get_struct evheap attr = None \/
  (Get_struct evheap attr = Some (attr, t, l)/\  t <> pthread_mutexattr_t))->
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_init_set1_priocl (|(Vptr attr) :: nil|) ;; s ||> ** 
              HEvStructHeap evheap ** HCurTCB ct ** HTCBList tls ** P)
      (<|| ABORT ||> ** 
          HEvStructHeap evheap **
          HCurTCB ct ** 
          HTCBList tls ** P). 
Proof.
  intros.   
  assert(can_change_aop(HEvStructHeap evheap** HCurTCB ct ** HTCBList tls ** P)).
  can_change_aop_solver. 
  eapply absinfer_trans.
 2:{ eapply absinfer_seq_abt; eauto. }
  eapply absinfer_seq; try eauto.
  apply absinfer_abt; eauto.
  absimp_abt_solver.
  instantiate (3:= s0).
  sep pauto.
  Unshelve.
  exact (END None).
Qed.

Lemma mutexattrinit_absimp_priocl_end:
  forall attr evheap vl ct tls pr st m sus s P sch,
   get tls ct = Some (pr,st,m, sus) ->
   Get_struct evheap attr = Some (attr, pthread_mutexattr_t, vl) ->
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_init_set1_priocl (|(Vptr attr) :: nil|) ;; s ||> ** 
              HEvStructHeap evheap ** HCurTCB ct ** HTCBList tls ** P)
      (<|| s ||> ** 
          HEvStructHeap (Set_struct' evheap attr prio_ceiling (Vint32 pr)) **
          HCurTCB ct ** 
          HTCBList tls ** P). 
Proof.
  infer_solver 0%nat. 
  Unshelve.
  exact Tnull.
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

Lemma mutexattrinit_absimp_abt1:
  forall attr evheap s t l P sch,
   (Get_struct evheap attr = None \/
   (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t))->
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_init_abt (|(Vptr attr) :: nil|) ?? s ||> ** 
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

(* Open Scope int_scope. *)
Lemma mutexattrinit_absimp_seq1:
  forall v'100 n x s P sch,
   can_change_aop P ->
   absinfer sch
      (<|| (mutexattr_extcb (|V$ Z.of_nat v'100 :: nil|);;
          mutexattr_for (Vptr x) n (v'100 + 1)
          ?? mutexattr_none (|V$ Z.of_nat v'100 :: nil|);;
               mutexattr_init_afterfor_set2_priocl
                 (|Vptr x :: V$ Z.of_nat v'100 :: nil|)) ;; s ||> ** P)
      (<|| (mutexattr_none (|V$ Z.of_nat v'100 :: nil|);;
               mutexattr_init_afterfor_set2_priocl
                 (|Vptr x :: V$ Z.of_nat v'100 :: nil|)) ;; s ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  2:{ eapply absinfer_seq; eauto.  eapply absinfer_eq. }
  eapply absinfer_seq; eauto.
  eapply absinfer_choice2; eauto.
Qed.

Lemma mutexattrinit_absimp_seq2:
  forall v'100 n x s P sch,
   can_change_aop P ->
   absinfer sch
      (<|| (mutexattr_extcb (|V$ Z.of_nat v'100 :: nil|);;
          mutexattr_for (Vptr x) n (v'100 + 1)
          ?? mutexattr_none (|V$ Z.of_nat v'100 :: nil|);;
               mutexattr_init_afterfor_set2_priocl
                 (|Vptr x :: V$ Z.of_nat v'100 :: nil|)) ;; s ||> ** P)
      (<|| (mutexattr_extcb (|V$ Z.of_nat v'100 :: nil|);;
          mutexattr_for (Vptr x) n (v'100 + 1)) ;; s ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
   2:{ eapply absinfer_seq; eauto.  eapply absinfer_eq. }
  eapply absinfer_seq; eauto.
  eapply absinfer_choice1; eauto.
Qed.

Lemma mutexattrinit_absimp_extcb_end:
  forall ptls v'100 tid s1 s2 P sch,
   (get ptls ($ Z.of_nat v'100) = Some (Valid_Addr tid) \/
   get ptls ($ Z.of_nat v'100) = Some Holder)  ->
   can_change_aop P ->
   absinfer sch
      (<||(mutexattr_extcb (|V$ Z.of_nat v'100 :: nil|);; s1) ;; s2 ||> ** HPriotls ptls ** P)
      (<|| s1 ;; s2 ||> ** HPriotls ptls ** P).
Proof.
  intros.
  assert(can_change_aop(HPriotls ptls ** P)).
  pure_auto.
  eapply absinfer_trans.
  2:{ eapply absinfer_seq; eauto. eapply absinfer_eq. }
  eapply absinfer_seq; eauto.
  infer_solver 0%nat.
  Unshelve.
  exact (Some Vnull).
Qed.

Lemma mutexattrinit_absimp_getptls_none_end:
  forall ptls i s s1 P sch,
   get ptls ($ Z.of_nat i) = Some Null  ->
   can_change_aop P ->
   absinfer sch
      (<|| (mutexattr_none (|V$ Z.of_nat i :: nil|);; s);; s1 ||> ** 
              HPriotls ptls ** P)
      (<|| s ;; s1 ||> ** 
          HPriotls ptls ** P).
Proof.
  intros.
  assert(can_change_aop(HPriotls ptls ** P)).
  pure_auto.
  eapply absinfer_trans.
  2:{ eapply absinfer_seq; eauto. eapply absinfer_eq. }
  eapply absinfer_seq; eauto.
  infer_solver 0%nat.
  Unshelve.
  exact (Some Vnull).
Qed.

Lemma mutexattrinit_absimp_for_setpriocl_end:
  forall attr evheap evheap' s i l P sch,
   Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l)->
   can_change_aop P ->
   evheap' = Set_struct' evheap attr prio_ceiling (Vint32 i) ->
   absinfer sch
      (<|| mutexattr_init_afterfor_set2_priocl (|(Vptr attr) :: (Vint32 i) :: nil|) ;; s ||> ** 
              HEvStructHeap evheap ** P)
      (<|| s ||> ** 
          HEvStructHeap evheap' ** P). 
Proof.
  intros.
  substs.
  infer_solver 0%nat.
  Unshelve.
  exact Tnull.
Qed.

Lemma mutexattrinit_absimp_for_setpriocl_abt:
  forall attr evheap s t i l P sch,
   (Get_struct evheap attr = None \/
   (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t))->
   can_change_aop P ->
   absinfer sch
      (<|| mutexattr_init_afterfor_set2_priocl (|(Vptr attr) :: (Vint32 i) :: nil|) ;; s ||> ** 
              HEvStructHeap evheap ** P)
      (<|| ABORT ||> ** 
          HEvStructHeap evheap ** P). 
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

Lemma mutexattrinit_setprot_end:
  forall attr s evheap l evheap' sch P,
    Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) ->
    evheap' = Set_struct' evheap attr protocol (V$ PTHREAD_PRIO_INHERIT) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_init_afterfor_set_protocol (|(Vptr attr) :: nil|)) ;; s ||>  ** HEvStructHeap evheap ** P)
      (<|| s ||> ** HEvStructHeap evheap' ** P).
Proof.
  intros.  substs.  infer_solver 0%nat.
  Unshelve.
  exact Tnull.
Qed.

Lemma mutexattrinit_setprot_abt:
  forall s sch evheap attr t l P,
  (Get_struct evheap attr = None \/
  (Get_struct evheap attr = Some (attr, t, l)/\  t <> pthread_mutexattr_t))->
    can_change_aop P ->
    absinfer sch
      (<|| (mutexattr_init_afterfor_set_protocol (|(Vptr attr) :: nil|)) ;; s ||> ** HEvStructHeap evheap ** P)
      (<|| ABORT ||> ** HEvStructHeap evheap ** P).
Proof.
  intros.
  assert (can_change_aop (HEvStructHeap evheap ** P)).
  pure_auto.
  eapply absinfer_trans.
  2:{ eapply absinfer_seq_abt; eauto. }
  eapply absinfer_seq; try eauto.
  apply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexattrinit_setrecurv_end:
  forall attr s evheap l evheap' sch P,
    Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) ->
    evheap' = Set_struct' evheap attr recursive (V$ PTHREAD_MUTEX_ERRORCHECK) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_init_afterfor_set_recursive (|(Vptr attr) :: nil|)) ;; s ||>  ** HEvStructHeap evheap ** P)
      (<|| s ||> ** HEvStructHeap evheap' ** P).
Proof.
  intros.  substs.  infer_solver 0%nat.
  Unshelve.
  exact Tnull.
Qed.

Lemma mutexattrinit_setrecurv_abt:
  forall s sch evheap attr t l P,
  (Get_struct evheap attr = None \/
  (Get_struct evheap attr = Some (attr, t, l)/\  t <> pthread_mutexattr_t))->
    can_change_aop P ->
    absinfer sch
      (<|| (mutexattr_init_afterfor_set_recursive (|(Vptr attr) :: nil|)) ;; s ||> ** HEvStructHeap evheap ** P)
      (<|| ABORT ||> ** HEvStructHeap evheap ** P).
Proof.
  intros.
  assert (can_change_aop (HEvStructHeap evheap ** P)).
  pure_auto.
  eapply absinfer_trans.
  2:{ eapply absinfer_seq_abt; eauto. }
  eapply absinfer_seq; try eauto.
  apply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexattrinit_setcancelsafe_end:
  forall attr s evheap l evheap' sch P,
    Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) ->
    evheap' = Set_struct' evheap attr cancel_safe (V$ PTHREAD_CANCEL_UNSAFE) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutexattr_init_afterfor_set_cancel_safe (|(Vptr attr) :: nil|)) ;; s ||>  ** HEvStructHeap evheap ** P)
      (<|| s ||> ** HEvStructHeap evheap' ** P).
Proof.
  intros.  substs.  infer_solver 0%nat.
  Unshelve.
  exact Tnull.
Qed.

Lemma mutexattrinit_setcancelsafe_abt:
  forall s sch evheap attr t l P,
  (Get_struct evheap attr = None \/
  (Get_struct evheap attr = Some (attr, t, l)/\  t <> pthread_mutexattr_t))->
    can_change_aop P ->
    absinfer sch
      (<|| (mutexattr_init_afterfor_set_cancel_safe (|(Vptr attr) :: nil|)) ;; s ||> ** HEvStructHeap evheap ** P)
      (<|| ABORT ||> ** HEvStructHeap evheap ** P).
Proof.
  intros.
  assert (can_change_aop (HEvStructHeap evheap ** P)).
  pure_auto.
  eapply absinfer_trans.
  2:{ eapply absinfer_seq_abt; eauto. }
  eapply absinfer_seq; try eauto.
  apply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexattrinit_setwaittype_end:
  forall attr evheap l evheap' s sch P,
    Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) ->
    evheap' = Set_struct' evheap attr waitq_type (Vint32 Int.zero) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mutexattr_init_afterfor_set_waitq_type (|(Vptr attr) :: nil|) ;; s ||>  ** HEvStructHeap evheap ** P)
      (<|| s ||> ** HEvStructHeap evheap' ** P).
Proof.
  intros.  substs.  infer_solver 0%nat.
  Unshelve.
  exact None.
  exact Tnull.
Qed.

Lemma mutexattrinit_setwaittype_abt:
  forall sch evheap attr t l s P,
  (Get_struct evheap attr = None \/
  (Get_struct evheap attr = Some (attr, t, l)/\  t <> pthread_mutexattr_t))->
    can_change_aop P ->
    absinfer sch
      (<|| (mutexattr_init_afterfor_set_waitq_type (|(Vptr attr) :: nil|)) ;; s||> ** HEvStructHeap evheap ** P)
      (<|| ABORT ||> ** HEvStructHeap evheap ** P).
Proof.
  intros.
  assert(can_change_aop(HEvStructHeap evheap ** P)).
  can_change_aop_solver. 
  eapply absinfer_trans.
  2:{ eapply absinfer_seq_abt; eauto. }
  eapply absinfer_seq; try eauto.
  apply absinfer_abt; eauto.
  absimp_abt_solver.
  Unshelve.
  exact None.
Qed.

Lemma mutexattrinit_rv_abt:
  forall sch rv P,
    rv <> Vint32 (Int.repr 0)->
    can_change_aop P ->
    absinfer sch
      (<|| (mutexattrinit_rv (|rv :: nil|))||> ** P)
      (<|| ABORT ||> ** P).
Proof.
  intros.
  apply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutexattrinit_rv_end:
  forall sch rv P,
    rv = Vint32 (Int.repr 0)->
    can_change_aop P ->
    absinfer sch
      (<|| (mutexattrinit_rv (|rv :: nil|))||> ** P)
      (<|| END (Some (Vint32 (Int.repr 0))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexattrinit_skip_end:
  forall sch s P,
    can_change_aop P ->
    absinfer sch
      (<||mutexattr_for_skip (|nil|);;s||> ** P)
      (<|| s ||> ** P).
Proof.
  infer_solver 0%nat.
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

Lemma OSMutexAttrInitProof:  
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api pthread_mutexattr_init
              (mutexattrinit,(Tint32,Tptr pthread_mutexattr_t::nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api pthread_mutexattr_init
              (mutexattrinit,(Tint32,Tptr pthread_mutexattr_t::nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api pthread_mutexattr_init = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
   do 3 try destruct v'; try apply absabort_rule.
   rename v'5 into er.

  (***********ad ′ =ₑ 〈 (long) ∗ 〉 attr ′;ₛ**********)
  hoare forward.
  pure_auto. pure_auto.
  rename x into V_attr.
  rename H1 into Hptr.
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
  assert (Hv: v = Vint32 (Int.repr EINVAL) \/ v <> Vint32 (Int.repr EINVAL)) by tauto.
  destruct Hv.  
  2: {
    hoare abscsq.
    apply noabs_oslinv.
    destruct Hptr; simpljoin.
    eapply mutexattrinit_absimp_attrok_abt_null; eauto.
    can_change_aop_solver.
    destruct H; simpljoin; tryfalse.
    inverts H.
    eapply mutexattrinit_absimp_attrerr_abt; eauto.
    can_change_aop_solver.
    apply absabort_rule.
  }
  hoare abscsq.
  apply noabs_oslinv.
  destruct Hptr; simpljoin.
  eapply mutexattrinit_absimp_attrok_abt_null'; eauto.
  can_change_aop_solver.
  destruct H; simpljoin; tryfalse.
  inverts H.
  eapply mutexattrinit_absimp_attrerr_end; eauto.
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

  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexinit_absimp_ok2.
  pure_auto.

  hoare forward prim.
  hoare unfold.
  rename v'20 into vpthattr.
  rename v'21 into vcspace.
  rename v'22 into v22. 
  rename v'23 into v23. 
  rename v'24 into v24. 

  unfold EvtInv.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  rename v'27 into evstructs.
  destruct (Get_struct evstructs x) eqn: eq1.
  2:{
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrinit_absimp_init_abt; eauto.
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
  eapply mutexattrinit_absimp_init_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }

(*******enter critical********)
  subst.
   hoare_lifts_trms_pre (AEvStructHeap, attr).
   eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold; eauto.
  hoare unfold.

 (*******attr -> is_initialized = 1*********)
  hoare forward.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexattrinit_absimp_init_end; eauto.
  pure_auto. 
  eapply absinfer_eq.

  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold.
  exists (V$ 1
            :: Vint32 i4
               :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil).
  exists v'16 v'27.
  sep pauto.
  struct_type_match_solver.
  subst.

  assert (Heq: Set_struct'
       (v'16 ++
        (x, pthread_mutexattr_t,
        Vint32 i5
        :: Vint32 i4
           :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
        :: v'27) x is_initialized (Vint32 Int.one) = 
       (v'16 ++
     (x, pthread_mutexattr_t,
     Vint32 Int.one
     :: Vint32 i4
        :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
     :: v'27)  ).
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
  change ( Vint32 Int.one
   :: Vint32 i4
      :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil) with
    (update_nth_val 0 ( Vint32 i5
   :: Vint32 i4
      :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil) (Vint32 Int.one)).
  eapply R_Q_Data_P_muxattr; eauto.
  auto.
  pure_auto.

  (* ENTER_CRITICAL;ₛ
      attr ′ → process_shared =ₑ ′ 1;ₛ
      EXIT_CRITICAL;ₛ *)
  clear -H2 H3.
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
  eapply mutexattrinit_absimp_proc_abt; eauto.
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
  eapply mutexattrinit_absimp_proc_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }

(*******enter critical********)
  subst.
   hoare_lifts_trms_pre (AEvStructHeap, attr).
   eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold; eauto.
  hoare unfold.

 (*******attr ′ → process_shared =ₑ ′ 1;ₛ*********)
  hoare forward.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexattrinit_absimp_proc_end; eauto.
  pure_auto. 
  eapply absinfer_eq.

  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold.
  exists (Vint32 i5
            :: V$ 1
               :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil).
  exists v'14 v'25.
  sep pauto.
  struct_type_match_solver.
  subst.

  assert (Heq: Set_struct'
       (v'14 ++
        (x, pthread_mutexattr_t,
        Vint32 i5
        :: Vint32 i4
           :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
        :: v'25) x process_shared (Vint32 Int.one) = 
       (v'14 ++
     (x, pthread_mutexattr_t,
     Vint32 i5
     :: Vint32 Int.one
        :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
     :: v'25)  ).
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
  change ( Vint32 i5
   :: Vint32 Int.one
      :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil) with
    (update_nth_val 1 ( Vint32 i5
   :: Vint32 i4
      :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil) (Vint32 Int.one)).
  eapply R_Q_Data_P_muxattr; eauto.
  auto.
  pure_auto.

(* ENTER_CRITICAL;ₛ
      OSPrioCur ′ =ₑ OSTCBCur ′ → OSTCBPrio;ₛ
      attr ′ → prio_ceiling =ₑ OSPrioCur ′;ₛ
      EXIT_CRITICAL;ₛ *)
  clear -H2 H3.
  hoare forward prim.
  hoare unfold.

  rename v'18 into vpthattr.
  rename v'19 into vcspace.
  rename v'20 into v20. 
  rename v'21 into v21. 
  rename v'22 into v22. 


  rename v'23 into v'18. 
  rename v'24 into v'19. 
  rename v'25 into v'20. 
  rename v'26 into v'21. 
  rename v'27 into v'22. 
  rename v'28 into v'23.


  unfold EvtInv.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  lets Hget_t: sempend_pure.TCBListP_head_in_tcb H10.
  destruct Hget_t as (st & sus & Hget_t).
  lets Hget_t': Hget_t.
  eapply TcbMod.join_get_r in Hget_t'; eauto.
  hoare_lifts_trms_pre (Aop, evstructheapid, curtid, abstcblsid).
  rename v'29 into evstructs.
  destruct (Get_struct evstructs x) eqn: eq1.
  2:{
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrinit_absimp_priocl_abt; eauto.
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
  eapply mutexattrinit_absimp_priocl_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }
  subst.
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrinit_absimp_priocl_end; eauto.
  pure_auto.
  eapply absinfer_eq.

(*******actual enter critical********)
   hoare_lifts_trms_pre (AEvStructHeap, attr).
   eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold; eauto.
  hoare unfold.
  (* OSPrioCur ′ =ₑ OSTCBCur ′ → OSTCBPrio;ₛ  *)
  unfold AGVars.
  hoare unfold.
  hoare forward.
  go.
 (*******attr ′ → prio_ceiling =ₑ OSPrioCur ′;ₛ*********)
  hoare forward.
  pure_auto.

  assert (Hrgn: 0 <= Int.unsigned i3 < 64).
  { clear -H10.
  funfold H10. inverts H.
  destruct x2 as [[[]]].
  funfold H2.
  eapply ucos_common.tcbblk_prio_range; eauto.
   }
  destruct Hrgn as (Hrgn1 & Hrgn2).
  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold.
  exists (update_nth_val 2 (Vint32 i12
     :: Vint32 i11
        :: Vint32 i10 :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: nil) (Vint32 i3)).
  exists v'14 v'29.
  sep split; eauto.
  sep pauto.
  eapply R_MutexAttr_P_hold; eauto.
  struct_type_match_solver.
  subst.
  simpl update_nth_val.

  assert (Heq: Set_struct'
       (v'14 ++
        (x, pthread_mutexattr_t,
        Vint32 i12
        :: Vint32 i11
           :: Vint32 i10 :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: nil)
        :: v'29) x prio_ceiling (Vint32 i3) = 
       (v'14 ++
     (x, pthread_mutexattr_t,
     Vint32 i12
        :: Vint32 i11
           :: Vint32 i3 :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: nil)
     :: v'29)  ).
  { eapply set_struct_update_nth_val'; eauto.
     unfolds; simpl; eauto.
     simpl; auto.
  }
  rewrite Heq.

  hoare forward prim.
  unfold EvtInv.
  unfold AGVars.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.   
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto; eauto.
  simpl dllseg at 2.
  unfold node.
  sep pauto; eauto.
  sep cancel Astruct.
  sep cancel dllseg.
  sep cancel dllseg.
  eauto.
  unfolds; simpl ;eauto.
  unfolds; simpl ;eauto.
  split; auto. go.
  auto with zarith.
  change ( Vint32 i12
   :: Vint32 i11
      :: Vint32 i3 :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: nil) with
    (update_nth_val 2 ( Vint32 i12
   :: Vint32 i11
      :: Vint32 i10 :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: nil) (Vint32 i3)).
  eapply R_Q_Data_P_muxattr; eauto.
  auto.
  pure_auto.
  (* flag ′ =ₑ ′ 1;ₛ *)
  clear -H2 H3.
  rename v'23 into ct_b.
  hoare forward.
  (* i = 0 *)
  hoare forward.

  (* WHILE (′ OS_LOWEST_PRIO +ₑ ′ 1 >ₑ i ′ &&ₑ flag ′) *)
  hoare_lifts_trms_pre (Aop, os_code_defs.i, flag, Alvarmapsto ptb).
  hoare remember (1::2::3::4::nil)%nat pre.
  eapply backward_rule1 with (p := 
      (EX i v',
      LV os_code_defs.i @ long |-> (V$ (Z.of_nat i)) **
      LV flag @ long |-> Vint32 v' **
      LV ptb @ OS_TCB ∗ |-> Vnull **
      <||                mutexattr_init_afterfor_set_protocol(|(Vptr x) :: nil|) ;;
                           mutexattr_init_afterfor_set_recursive(|(Vptr x) :: nil|);;
                           mutexattr_init_afterfor_set_cancel_safe(|(Vptr x) :: nil|);;
                           mutexattr_init_afterfor_set_waitq_type(|(Vptr x) :: nil|);;
                           mutexattrinit_rv (|v :: nil|)||> **
      [|Z.of_nat (i) < OS_LOWEST_PRIO + 1 |] **  (* find available prio, out of the loop *)
      [| v' = ($ 0) |] ** H)\\//
        (EX i v' v'2,
      LV os_code_defs.i @ long |-> (V$ (Z.of_nat i)) **
      LV flag @ long |-> Vint32 v' **
      LV ptb @ OS_TCB ∗ |-> v'2 **
      <||    (* mutexattr_for_skip (|nil|);; *)
                           mutexattr_init_afterfor_set_protocol(|(Vptr x) :: nil|) ;;
                           mutexattr_init_afterfor_set_recursive(|(Vptr x) :: nil|);;
                           mutexattr_init_afterfor_set_cancel_safe(|(Vptr x) :: nil|);;
                           mutexattr_init_afterfor_set_waitq_type(|(Vptr x) :: nil|);;
                           mutexattrinit_rv (|v :: nil|)||> **
      [| Z.of_nat (i) = OS_LOWEST_PRIO + 1|] ** (* no available prio, out of the loop *)
      [|v' = ($ 1)|] ** H) \\//
    ( EX i v' v'2, LV os_code_defs.i @ long |-> (V$ (Z.of_nat i)) **
      LV flag @ long |-> Vint32 v' **
      LV ptb @ OS_TCB ∗ |-> v'2 **
       <||mutexattr_for (Vptr x) (64-i) i ;;
                          mutexattr_init_afterfor_set_protocol(|(Vptr x) :: nil|) ;;
                           mutexattr_init_afterfor_set_recursive(|(Vptr x) :: nil|);;
                           mutexattr_init_afterfor_set_cancel_safe(|(Vptr x) :: nil|);;
                           mutexattr_init_afterfor_set_waitq_type(|(Vptr x) :: nil|);;
                           mutexattrinit_rv (|v :: nil|)||> **
      [|Z.of_nat (i) < OS_LOWEST_PRIO + 1 |] ** (* still in the loop *)
      [|v' = ($ 1)|] ** H)
     ).
  intros.
  right. right.
  exists 0%nat.
  sep pauto.
  unfold OS_LOWEST_PRIO; auto with zarith.

  eapply seq_rule.
  eapply while_rule.
  introv Hsat.
  destruct Hsat as [Hsat | [Hsat | Hsat]];
  sep pauto; try sep get rv; try solve [pure_auto].

(*****  Aistrue  (′ OS_LOWEST_PRIO +ₑ ′ 1 >ₑ os_code_defs.i ′ &&ₑ flag ′)*****)
  eapply backward_rule1 with (p := 
    ( EX i v' v'2 , LV os_code_defs.i @ long |-> (V$ (Z.of_nat i)) **
      LV flag @ long |-> Vint32 v' **
      LV ptb @ OS_TCB ∗ |-> v'2 **
       <||mutexattr_for (Vptr x) (64-i) i ;; 
                          mutexattr_init_afterfor_set_protocol(|(Vptr x) :: nil|) ;;
                           mutexattr_init_afterfor_set_recursive(|(Vptr x) :: nil|);;
                           mutexattr_init_afterfor_set_cancel_safe(|(Vptr x) :: nil|);;
                           mutexattr_init_afterfor_set_waitq_type(|(Vptr x) :: nil|);;
                           mutexattrinit_rv (|v :: nil|)||> **
      [|Z.of_nat (i) < OS_LOWEST_PRIO + 1 |] **
      [|v' = ($ 1)|] **  H )).
  introv Hsat.
  destruct Hsat as ([Hsat | [Hsat | Hsat]] & Histrue);
  sep destruct Hsat;
  lets Hcp: aconj_intro Hsat Histrue;
  eapply sep_aconj_r_aistrue_to_astar in Hcp; eauto;
  try solve [intros; sep get rv; try solve [pure_auto]];
  clear -Hcp; [ | | sep pauto ];
  false;
  sep split in Hcp;
  simpljoin; clear Hcp;
  try change ($ 0) with Int.zero in *;
  try change ($ 1) with Int.one in *;
  destruct (Int.ltu ($ Z.of_nat x0) ($ OS_LOWEST_PRIO +ᵢ  Int.one)) eqn: eq1;
  simpl in *;
  try change (Int.ltu Int.zero Int.one) with true in *;
  try change (Int.ltu Int.zero Int.zero) with false in *;
  simpl in *; tryfalse.
  rewrite H0 in eq1; change ($ OS_LOWEST_PRIO +ᵢ  Int.one) with ($ 64) in eq1.
  rewrite sem_common.sempend_ltu_ass1 in eq1; tryfalse.

  subst.
  hoare forward prim.
  hoare unfold.
  rename v'21 into vpthattr.
  rename v'22 into vcspace.
  rename v'23 into v23. 
  rename v'24 into v24. 
  rename v'25 into v25. 

  rename v'26 into v'21. 
  change (OS_LOWEST_PRIO + 1) with 64 in *.
  assert (Heq: Int.unsigned ($ Z.of_nat v') = Z.of_nat v').
  { int auto. }
  assert (Hmat: rule_type_val_match OS_TCB ∗ (nth_val' (Z.to_nat (Z.of_nat v')) v'5) = true).
  { eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite H9; auto with zarith.
   }
  lets Hptr : rule_type_val_match_ptr_elim Hmat.
  (* ptb ′ =ₑ OSTCBPrioTbl ′ [i ′];ₛ  *)
  hoare forward.
  rewrite Heq. auto.
  destruct Hptr as [Hvp | ((vp_b & vp_i) & Hvp)]; rewrite Hvp in *.
  (*case1: Vnull, out of loop *)
  assert (Hget: get v'20 ($ Z.of_nat v') = Some Null).
  { eapply H8; eauto. auto with zarith.
     unfold nat_of_Z.
     rewrite Heq.
     eapply nth_val'_imply_nth_val; eauto.
     rewrite H9.
     auto with zarith.
   }
  destruct (64 - v')%nat eqn: eq_suc.
  false.
  auto with zarith.
  simpl mutexattr_for.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexattrinit_absimp_seq1.
  pure_auto.
  eapply absinfer_eq.
  hoare_lifts_trms_pre (Aop, absptlsid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexattrinit_absimp_getptls_none_end; eauto.
  pure_auto.
  eapply absinfer_eq.

  (* EXIT_CRITICAL *)
  hoare forward prim.
  sep cancel EvtInv.
  sep cancel CoreCommuInv.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv. 
  sep cancel p_local.
  unfold AOSTCBPrioTbl.
  sep pauto; eauto.
  auto.
  pure_auto.
  rewrite Heq.
  (* IF (ptb ′ ==ₑ NULL) *)
  hoare forward.
  rewrite Hvp; pure_auto.
  rewrite Hvp; pure_auto.
  (* process post condition *)
  Focus 3.
  get_hsat Hsat.
 eapply adisj_intro.
 destruct Hsat as [Hsat | Hsat]; [left | right].
 sep split in Hsat.
 exact Hsat.
 sep split in Hsat.
 exact Hsat.
 (* back to if case *)
  hoare_split_pure_all.
  (* ENTER_CRITICAL;ₛ
      attr ′ → prio_ceiling =ₑ i ′;ₛ
      EXIT_CRITICAL;ₛ *)
  hoare forward prim.
  hoare unfold.

  rename v'36 into vpthattr1.
  rename v'37 into vcspace1.
  rename v'38 into v38. 
  rename v'39 into v39. 
  rename v'40 into v40. 


  unfold EvtInv.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  rename v'43 into evstructs.
  destruct (Get_struct evstructs x) eqn: eq1.
  2:{
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrinit_absimp_for_setpriocl_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.
  }
  rename eq1 into Hget'.
  destruct p as ((a & t) & l).
  lets Heq': Get_struct_some_eq Hget'. subst a.

  assert (Ht: t = pthread_mutexattr_t \/ t <> pthread_mutexattr_t) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrinit_absimp_for_setpriocl_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }

(*******enter critical********)
  subst.
   hoare_lifts_trms_pre (AEvStructHeap, attr).
   eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold; eauto.
  hoare unfold.

 (*******attr ′ → prio_ceiling =ₑ i ′;ₛ*********)
  hoare forward.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexattrinit_absimp_for_setpriocl_end; eauto.
  pure_auto. 
  eapply absinfer_eq.

  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold.
  exists (update_nth_val 2(Vint32 i5
            :: Vint32 i4
               :: Vint32 i3
                  :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil) (V$ Z.of_nat v')).
  exists v'32 v'43.
  sep split; eauto.
  sep pauto.
  eapply R_MutexAttr_P_hold; eauto.
  clear -H1; int auto.
  struct_type_match_solver.
  subst.
  simpl update_nth_val.

  assert (Heq': Set_struct'
       (v'32 ++
        (x, pthread_mutexattr_t,
        Vint32 i5
        :: Vint32 i4
           :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
        :: v'43) x prio_ceiling (V$ Z.of_nat v') = 
       (v'32 ++
     (x, pthread_mutexattr_t,
     Vint32 i5
     :: Vint32 i4
        :: V$ Z.of_nat v':: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
     :: v'43)  ).
  { eapply set_struct_update_nth_val'; eauto.
     unfolds; simpl; eauto.
     simpl; auto.
  }
  rewrite Heq'.

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
  change ( Vint32 i5
   :: Vint32 i4
      :: V$ Z.of_nat v' :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil) with
    (update_nth_val 2 ( Vint32 i5
   :: Vint32 i4
      :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil) (V$ Z.of_nat v')).
  eapply R_Q_Data_P_muxattr; eauto.
  auto.
  pure_auto.
  (* flag ′ =ₑ ′ 0 *)
  eapply forward_rule1.
  2:{ hoare forward. }
  introv Hsat.
  sep eexists.
  sep cancel Aop.
  sep pauto.
  (* false if *)
  eapply backward_rule1 with (p:= Afalse).
  introv Hsat.
  rewrite Hvp in Hsat.
  simpl val_inj in Hsat.
  clear -Hsat. sep split in Hsat.
  destruct H; tryfalse.
  apply pfalse_rule.
  (* case2: Vptr (vp_b, vp_i) *)
   assert (Hget: get v'20 ($ Z.of_nat v') = Some (Valid_Addr (vp_b, vp_i)) \/ 
                           get v'20 ($ Z.of_nat v') = Some Holder).
  { assert (Hc: (vp_b, vp_i) = v'17 \/ (vp_b, vp_i) <> v'17) by tauto.
     destruct Hc; [right | left]; subst;
     eapply H8; eauto; auto with zarith;
     unfold nat_of_Z;
     rewrite Heq;
     eapply nth_val'_imply_nth_val; eauto;
     rewrite H9;
     auto with zarith.
   }

   destruct (64 - v')%nat eqn: eq_suc.
  false.
  auto with zarith.
  unfold mutexattr_for.
  fold mutexattr_for.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexattrinit_absimp_seq2.
  pure_auto.
  eapply absinfer_eq.
  hoare_lifts_trms_pre (Aop, absptlsid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexattrinit_absimp_extcb_end; eauto.
  pure_auto.
  eapply absinfer_eq.
  (* EXIT_CRITICAL *)
  hoare forward prim.
  sep cancel EvtInv.
  sep cancel CoreCommuInv.
  sep cancel Aier.
  sep cancel p_local.
  unfold AOSTCBPrioTbl.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv. 
  sep pauto; eauto.
  auto.
  pure_auto.
  rewrite Heq.
  (* IF (ptb ′ ==ₑ NULL) *)
  hoare forward.
  rewrite Hvp; pure_auto.
  rewrite Hvp; pure_auto.
  (* process post condition *)
  Focus 3.
  get_hsat Hsat.
 eapply adisj_intro.
 destruct Hsat as [Hsat | Hsat]; [left | right].
 sep split in Hsat.
 exact Hsat.
 sep split in Hsat.
 exact Hsat.
 (* back to if case *)
  (* false if Vnull *)
  eapply backward_rule1 with (p:= Afalse).
  introv Hsat.
  rewrite Hvp in Hsat.
  simpl val_inj in Hsat.
  clear -Hsat. sep split in Hsat.
  simpljoin; tryfalse.
  apply pfalse_rule.
  (* ++ i ′ *)
  assert (Heqi: ($ Z.of_nat v' +ᵢ  $ 1) = ($ Z.of_nat (v' + 1)) ).
  { clear -H1. int auto. }
  assert (Heqn: n = (64 - (v' + 1))%nat).
  { clear -eq_suc. auto with zarith. }
   subst n.
  assert (Hc: Z.of_nat (v' + 1) = 64 \/ Z.of_nat (v' + 1) < 64).
  { clear -H1. int auto. }
  hoare_split_pure_all.
   destruct Hc as [Hout | Hin_loop].
  (* case2.1 : Z.of_nat (v' + 1) = 64, out of loop *)
  assert (Hz: ((64 - (v' + 1)) = 0)%nat ).
  { clear -Hout. auto with zarith. }
  rewrite Hz in *.
  unfold mutexattr_for in *.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply  mutexattrinit_skip_end; eauto.
  pure_auto.
  apply absinfer_eq.
  hoare forward.
  left.
  rewrite Heqi in *.
  sep pauto.
  (* case 2.2:  Z.of_nat (v' + 1) < 64, still in the loop *)
  hoare forward.
  rewrite Heqi in *.
  right.
  sep pauto.
 (*Aisfalse(′ OS_LOWEST_PRIO +ₑ ′ 1 >ₑ os_code_defs.i ′ &&ₑ flag ′)*)
eapply backward_rule1 with (p := 
(    (EX i v' v'2,
      LV os_code_defs.i @ long |-> (V$ (Z.of_nat i)) **
      LV flag @ long |-> Vint32 v' **
      LV ptb @ OS_TCB ∗ |-> v'2 **
      <||                mutexattr_init_afterfor_set_protocol(|(Vptr x) :: nil|) ;;
                           mutexattr_init_afterfor_set_recursive(|(Vptr x) :: nil|);;
                           mutexattr_init_afterfor_set_cancel_safe(|(Vptr x) :: nil|);;
                           mutexattr_init_afterfor_set_waitq_type(|(Vptr x) :: nil|);;
                           mutexattrinit_rv (|v :: nil|)||> **
      [| (Z.of_nat (i) < OS_LOWEST_PRIO + 1 /\ v' = ($ 0)) (* find available prio, out of the loop *)
          \/ (Z.of_nat (i) = OS_LOWEST_PRIO + 1 /\ v' = ($ 1)) |] (* no available prio, out of the loop *)
      ** H))).
  introv Hsat.
  destruct Hsat as ([Hsat | [Hsat | Hsat]] & Hisfalse);
  sep destruct Hsat;
  lets Hcp: aconj_intro Hsat Hisfalse;
  eapply sep_aconj_r_aisfalse_to_astar in Hcp; eauto;
  try solve [intros; sep get rv; try solve [pure_auto]];
  clear -Hcp; [ idtac | idtac | false].
  sep pauto.
  sep pauto.
  sep split in Hcp.
  simpljoin; clear Hcp H3;
  change ($ 1) with Int.one in *;
  destruct (Int.ltu ($ Z.of_nat x0) ($ OS_LOWEST_PRIO +ᵢ  Int.one)) eqn: eq1;
  simpl in *;
  try change (Int.ltu Int.zero Int.one) with true in *;
  try change (Int.ltu Int.zero Int.zero) with false in *;
  simpl in *; tryfalse.
  destruct H2; tryfalse.
  rewrite Intlt_false_is_Zge in eq1.
  change ($ OS_LOWEST_PRIO +ᵢ  Int.one) with ($ 64) in eq1.
  int auto.
  (* end of while *)
  subst.
  hoare unfold.

  (* ENTER_CRITICAL;ₛ
     attr ′ → protocol =ₑ ′ PTHREAD_PRIO_INHERIT;ₛ
      EXIT_CRITICAL;ₛ *)
  clear -H2 H3.
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
  eapply mutexattrinit_setprot_abt; eauto.
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
  eapply mutexattrinit_setprot_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }

(*******enter critical********)
  subst.
   hoare_lifts_trms_pre (AEvStructHeap, attr).
   eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold; eauto.
  hoare unfold.

 (*******attr ′ → protocol =ₑ ′ PTHREAD_PRIO_INHERIT;ₛ*********)
  hoare forward.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexattrinit_setprot_end; eauto.
  pure_auto. 
  eapply absinfer_eq.

  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold.
  exists (Vint32 i5
            :: Vint32 i4
               :: Vint32 i3 :: (V$ PTHREAD_PRIO_INHERIT) :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil).
  exists v'14 v'25.
  sep pauto.
  struct_type_match_solver.
  subst.

  assert (Heq: Set_struct'
       (v'14 ++
        (x, pthread_mutexattr_t,
        Vint32 i5
        :: Vint32 i4
           :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
        :: v'25) x protocol (V$ PTHREAD_PRIO_INHERIT) = 
       (v'14 ++
     (x, pthread_mutexattr_t,
     Vint32 i5
     :: Vint32 i4
        :: Vint32 i3 :: (V$ PTHREAD_PRIO_INHERIT) :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
     :: v'25)  ).
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
  change ( Vint32 i5
   :: Vint32 i4
      :: Vint32 i3 :: (V$ PTHREAD_PRIO_INHERIT) :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil) with
    (update_nth_val 3 ( Vint32 i5
   :: Vint32 i4
      :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil) (V$ PTHREAD_PRIO_INHERIT)).
  eapply R_Q_Data_P_muxattr; eauto.
  auto.
  pure_auto.

  (* ENTER_CRITICAL;ₛ
     attr ′ → recursive =ₑ ′ PTHREAD_MUTEX_ERRORCHECK;ₛ
      EXIT_CRITICAL;ₛ *)
  clear -H2 H3.
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
  eapply mutexattrinit_setrecurv_abt; eauto.
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
  eapply mutexattrinit_setrecurv_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }

(*******enter critical********)
  subst.
   hoare_lifts_trms_pre (AEvStructHeap, attr).
   eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold; eauto.
  hoare unfold.

 (*******attr ′ → recursive =ₑ ′ PTHREAD_MUTEX_ERRORCHECK;ₛ*********)
  hoare forward.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexattrinit_setrecurv_end; eauto.
  pure_auto. 
  eapply absinfer_eq.

  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold.
  exists (Vint32 i5
            :: Vint32 i4
               :: Vint32 i3 :: Vint32 i2 :: (V$ PTHREAD_MUTEX_ERRORCHECK) :: Vint32 i0 :: Vint32 i :: nil).
  exists v'14 v'25.
  sep pauto.
  struct_type_match_solver.
  subst.

  assert (Heq: Set_struct'
       (v'14 ++
        (x, pthread_mutexattr_t,
        Vint32 i5
        :: Vint32 i4
           :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
        :: v'25) x recursive (V$ PTHREAD_MUTEX_ERRORCHECK) = 
       (v'14 ++
     (x, pthread_mutexattr_t,
     Vint32 i5
     :: Vint32 i4
        :: Vint32 i3 :: Vint32 i2 :: (V$ PTHREAD_MUTEX_ERRORCHECK) :: Vint32 i0 :: Vint32 i :: nil)
     :: v'25)  ).
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
  change ( Vint32 i5
   :: Vint32 i4
      :: Vint32 i3 :: Vint32 i2 :: (V$ PTHREAD_MUTEX_ERRORCHECK) :: Vint32 i0 :: Vint32 i :: nil) with
    (update_nth_val 4 ( Vint32 i5
   :: Vint32 i4
      :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil) (V$ PTHREAD_MUTEX_ERRORCHECK)).
  eapply R_Q_Data_P_muxattr; eauto.
  auto.
  pure_auto.

    (* ENTER_CRITICAL;ₛ
     attr ′ → cancel_safe =ₑ ′ PTHREAD_CANCEL_UNSAFE;ₛ
      EXIT_CRITICAL;ₛ *)
  clear -H2 H3.
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
  eapply mutexattrinit_setcancelsafe_abt; eauto.
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
  eapply mutexattrinit_setcancelsafe_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }

(*******enter critical********)
  subst.
   hoare_lifts_trms_pre (AEvStructHeap, attr).
   eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold; eauto.
  hoare unfold.

 (*******attr ′ → cancel_safe =ₑ ′ PTHREAD_CANCEL_UNSAFE;ₛ*********)
  hoare forward.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexattrinit_setcancelsafe_end; eauto.
  pure_auto. 
  eapply absinfer_eq.

  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold.
  exists (Vint32 i5
            :: Vint32 i4
               :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: (V$ PTHREAD_CANCEL_UNSAFE) :: nil).
  exists v'14 v'25.
  sep pauto.
  struct_type_match_solver.
  subst.

  assert (Heq: Set_struct'
       (v'14 ++
        (x, pthread_mutexattr_t,
        Vint32 i5
        :: Vint32 i4
           :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
        :: v'25) x cancel_safe (V$ PTHREAD_CANCEL_UNSAFE) = 
       (v'14 ++
     (x, pthread_mutexattr_t,
     Vint32 i5
     :: Vint32 i4
        :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: (V$ PTHREAD_CANCEL_UNSAFE) ::  nil)
     :: v'25)  ).
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
  change ( Vint32 i5
   :: Vint32 i4
      :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: (V$ PTHREAD_CANCEL_UNSAFE) :: nil) with
    (update_nth_val 6 ( Vint32 i5
   :: Vint32 i4
      :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil) (V$ PTHREAD_CANCEL_UNSAFE)).
  eapply R_Q_Data_P_muxattr; eauto.
  auto.
  pure_auto.

   (* ENTER_CRITICAL;ₛ
     attr ′ → waitq_type =ₑ ′ 0;ₛ
      EXIT_CRITICAL;ₛ *)
  clear -H2 H3.
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
  eapply mutexattrinit_setwaittype_abt; eauto.
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
  eapply mutexattrinit_setwaittype_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }

(*******enter critical********)
  subst.
   hoare_lifts_trms_pre (AEvStructHeap, attr).
   eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold; eauto.
  hoare unfold.

 (*******attr ′ → waitq_type =ₑ ′ 0;ₛ*********)
  hoare forward.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexattrinit_setwaittype_end; eauto.
  pure_auto. 
  eapply absinfer_eq.

  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold.
  exists (Vint32 i5
            :: Vint32 i4
               :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: (V$ 0) :: Vint32 i :: nil).
  exists v'14 v'25.
  sep pauto.
  struct_type_match_solver.
  subst.
  change (Int.zero) with ($ 0).
  assert (Heq: Set_struct'
       (v'14 ++
        (x, pthread_mutexattr_t,
        Vint32 i5
        :: Vint32 i4
           :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
        :: v'25) x waitq_type (V$ 0) = 
       (v'14 ++
     (x, pthread_mutexattr_t,
     Vint32 i5
     :: Vint32 i4
        :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: (V$ 0) :: Vint32 i :: nil)
     :: v'25)  ).
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
  change ( Vint32 i5
   :: Vint32 i4
      :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: (V$ 0) :: Vint32 i :: nil) with
    (update_nth_val 5 ( Vint32 i5
   :: Vint32 i4
      :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil) (V$ 0)).
  eapply R_Q_Data_P_muxattr; eauto.
  auto.
  pure_auto.
  (* RETURN ′ 0 *)
  clear.
  assert (Hv: v = V$ 0  \/ v <> V$ 0 ) by tauto.
  destruct Hv as [Hteq | Htneq].
  2:{
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrinit_rv_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule. }
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexattrinit_rv_end; eauto.
  pure_auto.
  eapply absinfer_eq.
  hoare forward.
  Unshelve.
  exact nil.
  exact Tnull. exact Tnull.  exact nil. exact nil.
  exact Tnull. exact Tnull. exact nil. exact Tnull.
  exact nil. exact Tnull. exact nil. exact Tnull.
  exact nil. exact Tnull. exact nil.
Qed.
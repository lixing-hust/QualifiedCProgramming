Require Import os_code_defs.
Require Import sem_common.

Require Import List.
Require Import os_mutex_cap.
Require Import abs_op.
Require Import ifun_spec.

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
Require Import abs_infer_abt.

Require Import symbolic_lemmas.
Require Import OSMutex_common.

Require Import pos_list_common. 
Require Import OSTimeTickPure.
Require Import ev_aux_code.
Require Import Aarray_new_common.
Require Import mutex_pend_pure.
Require Import sempend_pure.
Require Import gjb_common.
Require Import gjb_mutex_common.
(* Require Import gjb_sem_common. *)
Require Import hoare_forward.
Require Import ucos_common.
Require Import os_ucos_h.
Require Import tv_match.
Require Import pure.
Require Import seplog_trm_tacs.
Require Import join_lib.
Require Import sem_lab.
Require Import mutex_pend_pure.
Require Import sempend_pure.
Require Import pos_list_common. 
Require Import evauxvar_lemmas.
Require Import evaux_pure.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Open Scope list_scope.
Open Scope int_scope.
Open Scope code_scope.

Lemma mutexunlock_absimp_muxerr_abt:
  forall s sch v'4 V_pos P,
    (cmpaddr Cle v'4 userAddrStart = true \/ cmpaddr Clt userAddrEnd v'4 = true) ->  
    V_pos <> Vint32 (Int.mone) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||
          (mutexunlock_muxerr (|(Vptr v'4) :: V_pos :: nil|) ??
                   mutexunlock_mutex_pos(|(Vptr v'4) :: V_pos :: nil|));;s
                       ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
 intros.
 eapply absinfer_trans; try eapply absinfer_seq_abt; eauto.
 eapply absinfer_seq; eauto.
 eapply absinfer_trans; try eapply absinfer_choice1; eauto.
 eapply absinfer_abt; eauto.
 absimp_abt_solver.
Qed.

Lemma mutexunlock_absimp_muxerr_cont: 
  forall sch V_mux V_pos s P,
    (V_mux = Vnull \/
       exists v'4, V_mux = Vptr v'4 /\ 
                     (cmpaddr Cle v'4 userAddrStart = true \/
                        cmpaddr Clt userAddrEnd v'4 = true)) ->   
    V_pos = Vint32 Int.mone -> 
    can_change_aop P -> 
    absinfer sch 
      (<||
         (mutexunlock_muxerr (|V_mux :: V_pos :: nil|) ??
                   mutexunlock_mutex_pos(|V_mux :: V_pos :: nil|));; s ||>  ** P)
      (<|| s ||> ** P).
Proof.
   intros.
   eapply absinfer_trans; try eapply absinfer_seq_end; eauto.
   eapply absinfer_seq; eauto.
   infer_solver 0%nat.
Qed.

Lemma mutexunlock_absimp_muxok_abt_null:
  forall sch s V_pos P,
    can_change_aop P ->
    V_pos <> Vint32 Int.mone -> 
    absinfer sch
      (<||
          (mutexunlock_muxerr (|Vnull :: V_pos :: nil|) ??
            mutexunlock_mutex_pos(|Vnull :: V_pos :: nil|));;
                 s ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
 intros.
 eapply absinfer_trans; try eapply absinfer_seq_abt; eauto.
 eapply absinfer_seq; eauto.
 eapply absinfer_trans; try eapply absinfer_choice1; eauto.
 eapply absinfer_abt; eauto.
 absimp_abt_solver.
Qed.

Lemma mutexunlock_absimp_mux_get_none:
  forall sch v'4 v pbls s P,
    cmpaddr Clt userAddrStart v'4 = true ->
    cmpaddr Cle v'4 userAddrEnd = true -> 
    get pbls v'4 = None -> 
    can_change_aop P ->
    absinfer sch
     (<||
      (mutexunlock_muxerr (|Vptr v'4 :: v :: nil|) ??
            mutexunlock_mutex_pos(|Vptr v'4 :: v :: nil|));;
                 s ||>  **
        Hpbls pbls ** P)
     (<|| ABORT ||>  ** Hpbls pbls ** P).
Proof.
 intros.
 assert (Hc: can_change_aop (Hpbls pbls ** P)) by can_change_aop_solver.
 eapply absinfer_trans; try eapply absinfer_seq_abt; eauto.
 eapply absinfer_seq; eauto.
 eapply absinfer_trans; try eapply absinfer_choice2; eauto.
 eapply absinfer_abt; eauto.
 absimp_abt_solver.
 right. 
 eexists; eauto. splits; eauto.
 eapply absdata_elim with (s:= s0); eauto.
Qed.

Lemma mutexunlock_absimp_mux_get_outtype_err_abt:
  forall sch v'4 v s P,
    cmpaddr Clt userAddrStart v'4 = true ->
    cmpaddr Cle v'4 userAddrEnd = true -> 
    ~(exists i, v = Vint32 i) -> 
    can_change_aop P ->
    absinfer sch
     (<||
     (mutexunlock_muxerr (|Vptr v'4 :: v :: nil|) ??
            mutexunlock_mutex_pos(|Vptr v'4 :: v :: nil|));;
                 s ||>  ** P)
     (<|| ABORT ||>  ** P). 
Proof.
 intros.
 eapply absinfer_trans; try eapply absinfer_seq_abt; eauto.
 eapply absinfer_seq; eauto.
 eapply absinfer_trans; try eapply absinfer_choice2; eauto.
 eapply absinfer_abt; eauto.
 absimp_abt_solver.
  Unshelve.
  exact None.
Qed.

Lemma mutexunlock_absimp_mux_get_pos_abt: 
  forall sch vmux pbls posv v s P , 
    cmpaddr Clt userAddrStart vmux = true ->
    cmpaddr Cle vmux userAddrEnd = true -> 
    get pbls vmux = Some posv ->
    v <> Vint32 posv -> 
    can_change_aop P ->
   absinfer sch  
     (<||
    (mutexunlock_muxerr (|Vptr vmux :: v :: nil|) ??
            mutexunlock_mutex_pos(|Vptr vmux :: v :: nil|));;
                 s ||> ** Hpbls pbls ** P)
     (<|| ABORT ||> ** Hpbls pbls ** P).
Proof.
 intros.
 assert (Hc: can_change_aop (Hpbls pbls ** P)) by can_change_aop_solver.
 eapply absinfer_trans; try eapply absinfer_seq_abt; eauto.
 eapply absinfer_seq; eauto.
 eapply absinfer_trans; try eapply absinfer_choice2; eauto.
 eapply absinfer_abt; eauto.
 absimp_abt_solver.
 right. 
 eexists; eauto. splits; eauto.
 eapply absdata_elim with (s:= s0); eauto.
 left. eexists; splits; eauto.
Qed.

Lemma mutexunlock_absimp_sem_get_pos_ok: 
  forall sch vmux pbls posv v P s, 
    cmpaddr Clt userAddrStart vmux = true ->
    cmpaddr Cle vmux userAddrEnd = true -> 
    get pbls vmux = Some posv ->
    v = Vint32 posv -> 
    can_change_aop P ->
   absinfer sch  
     (<||
    (mutexunlock_muxerr (|Vptr vmux :: v :: nil|) ??
            mutexunlock_mutex_pos(|Vptr vmux :: v :: nil|));;
                 s ||> ** Hpbls pbls ** P)
     (<|| s||> ** Hpbls pbls ** P).
Proof.
   intros.
   assert (Hc: can_change_aop (Hpbls pbls ** P)) by can_change_aop_solver.
   eapply absinfer_trans; try eapply absinfer_seq_end; eauto.
   eapply absinfer_seq; eauto.
   infer_solver 1%nat.
   repeat eexists; eauto.
   right. exists pbls. 
   splits; eauto.
   eapply absdata_elim with (s:= s0); eauto.
   left.
   eexists; splits; eauto.
Qed.

Lemma mutexunlock_absimp_poserr0:
  forall posv v1 V_ret s P sch,
    v1 = Vint32 posv ->
    (Int.ltu posv Int.zero = true \/
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) ->
    V_ret = Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch
      ( <||    mutexunlock_poserr (|v1 :: V_ret :: nil|) ?? s ||> ** P)
      ( <|| END (Some  (Vint32 (Int.repr EINVAL))) ||> ** P ).
Proof.
  intros.
  subst.
  infer_solver 0%nat.  
Qed.

Lemma mutexunlock_absimp_poserr_abt:
  forall posv v1 V_ret s P sch,
      v1 = Vint32 posv ->
    (Int.ltu posv Int.zero = true \/
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) ->
      V_ret <> (Vint32 (Int.repr EINVAL)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||   mutexunlock_poserr (|v1 :: V_ret :: nil|) ?? s ||> ** P)
      (<|| ABORT ||> ** P). 
Proof.
 intros.
 eapply absinfer_trans; try eapply absinfer_choice1; eauto.
 eapply absinfer_abt; eauto.
 absimp_abt_solver.
  Unshelve.
  exact (None).
Qed.

Lemma mutexunlock_absimp_posok_choice:
  forall s posv v1 V_ret P sch,
    (Int.ltu posv Int.zero = false /\
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = false /\ posv <> Int.repr (OS_USER_MAX_EVENTS / 3)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mutexunlock_poserr (|v1 :: V_ret :: nil|) ?? s ||> ** P) 
      (<|| s ||> ** P). 
Proof.
  introv Hrgn Hcaop.
  apply absinfer_choice2; can_change_aop_solver.
  pure_auto.
Qed.

Lemma mutexunlock_absimp_before_abt_hold: 
  forall i o x n w pi pro c mc s V_eid minfob sch P, 
    (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
    get minfob i = Some (Holder, o, x, n, pro, pi, w, c, mc) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||
         mutexunlock_ecb_ptr (|(Vint32 i) :: V_eid :: nil|);; s ||>  ** HMuxInfo minfob ** P) 
      (<|| ABORT ||>  ** HMuxInfo minfob ** P). 
Proof. 
  introv Hrgn Hsi Hcop.
  assert(can_change_aop(HMuxInfo minfob ** P)).
  can_change_aop_solver. 
  eapply absinfer_trans.
  eapply absinfer_seq; try eauto.
  instantiate (1:=ABORT).
  apply absinfer_abt.
  try can_change_aop_solver. 
  try can_change_aop_solver. 
  absimp_abt_solver.
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  right. split; auto. left. split. intro. destruct H1. inv H1. intro Hf. inv Hf.
  pure_auto.
  eapply absinfer_seq_abt; auto.
  Unshelve.
  exact None.
Qed.

Lemma mutexunlock_absimp_before_abt_out: 
  forall i eo o x n w pi pro c mc s V_eid minfob sch P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
         ((exists eid, eo = (Valid_Addr eid) /\ V_eid <> Vptr eid) \/ eo = Null /\ V_eid <> Vnull) -> 
         can_change_aop P -> 
         absinfer sch 
           (<||
              mutexunlock_ecb_ptr (|(Vint32 i) :: V_eid :: nil|);; s ||>  ** HMuxInfo minfob ** P)
           (<|| ABORT ||>  ** HMuxInfo minfob ** P). 
Proof.
  introv Hrgn Hsi Hcs Hcop.
  eapply absinfer_trans.
  assert(can_change_aop(HMuxInfo minfob ** P)).
  can_change_aop_solver. 
  eapply absinfer_seq; try eauto.
  instantiate (1:=ABORT).
  apply absinfer_abt.
  try can_change_aop_solver. 
  try can_change_aop_solver. 
  absimp_abt_solver.
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  eapply absinfer_seq_abt; eauto.
  try can_change_aop_solver. 
  try can_change_aop_solver. 
  Unshelve.
  exact None.
Qed.

Lemma mutexunlock_absimp_get_before_abt_hold: 
  forall i o x n w pi pro c mc V_eid s minfob sch P, 
    (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
    get minfob i = Some (Holder, o, x, n, pro, pi, w, c, mc) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||  mutexunlock_ecb_ptr (|(Vint32 i) :: V_eid :: nil|) ;; s ||>  ** HMuxInfo minfob ** P) 
      (<|| ABORT ||>  ** HMuxInfo minfob ** P). 
Proof. 
  introv Hrgn Hsi Hcop.
  assert(can_change_aop(HMuxInfo minfob ** P)).
  can_change_aop_solver. 
  eapply absinfer_trans.
  eapply absinfer_seq; try eauto.
  instantiate (1:=ABORT). 
  apply absinfer_abt.
  try can_change_aop_solver. 
  try can_change_aop_solver. 
  absimp_abt_solver.
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  right. split; auto. left. split. intro. destruct H1. inv H1. intro Hf. inv Hf.
  pure_auto.
  eapply absinfer_seq_abt; auto.
  Unshelve.
  exact None.
Qed.

Lemma mutexunlock_absimp_get_before_abt_out: 
  forall i eo o x n w pi pro c mc V_eid s minfob sch P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
         ((exists eid, eo = (Valid_Addr eid) /\ V_eid <> Vptr eid) \/ eo = Null /\ V_eid <> Vnull) -> 
         can_change_aop P -> 
         absinfer sch 
           (<||  mutexunlock_ecb_ptr (|(Vint32 i) :: V_eid :: nil|) ;; s ||>  ** HMuxInfo minfob ** P)
           (<|| ABORT ||>  ** HMuxInfo minfob ** P). 
Proof.
  introv Hrgn Hsi Hcs Hcop.
  eapply absinfer_trans.
  assert(can_change_aop(HMuxInfo minfob ** P)).
  can_change_aop_solver. 
  eapply absinfer_seq; try eauto.
  instantiate (1:=ABORT).
  apply absinfer_abt.
  try can_change_aop_solver. 
  try can_change_aop_solver. 
  absimp_abt_solver.
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  eapply absinfer_seq_abt; eauto.
  try can_change_aop_solver. 
  try can_change_aop_solver. 
  Unshelve.
  exact None.
Qed.

(* Open Scope int_scope. *)

Lemma mutexunlock_absimp_ecb_placeholder_abt: 
  forall (i : int32) (sch : ossched) (v v0 v1 v' : val) (P : asrt) s0 mls o x n pro pi w c mc,
    Int.ltu i Int.zero = false /\ Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> $ (OS_USER_MAX_EVENTS / 3) ->
    get mls i = Some (Holder, o, x, n, pro, pi, w, c, mc) ->
    can_change_aop P ->
    sch ⊢  <|| (mutexunlock_get_ecb_ptr1 (|Vint32 i :: v' :: nil|) ?? 
                       mutexunlock_get_ecb_ptr2 (|Vint32 i :: v' :: nil|) ?? 
                       mutexunlock_ecb_ptr_holder_abt (|Vint32 i :: nil|));; s0 ||> **  
                HMuxInfo mls ** P
               ⇒  <|| ABORT ||>  ** HMuxInfo mls ** P. 
Proof.
  intros.
  assert (Hc: can_change_aop (HMuxInfo mls ** P)) by can_change_aop_solver.
  eapply absinfer_trans;
    try eapply absinfer_seq;
    try (eapply absinfer_seq_abt; try eauto);
    try eauto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver. 2: { eauto. } can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver. 2: { eauto. } can_change_aop_solver.  
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  Unshelve.
  exact None.
Qed.

Lemma mutexunlock_absimp_get_ecb_ptr'_mismatch_abt:  
  forall i eo mls sch v' t ptrmp s0 P o x n pro pi w c mc, 
    (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
    get mls i = Some (eo, o, x, n, pro, pi, w, c, mc) ->
    ((exists eid, eo = Valid_Addr eid /\ v' <> Vptr eid) \/ eo = Null /\ v' <> Vnull) -> 
    get ptrmp t = Some (Vnull, Vnull, Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
           (<|| (mutexunlock_get_ecb_ptr1 (|Vint32 i :: v' :: nil|) ?? 
                    mutexunlock_get_ecb_ptr2 (|Vint32 i :: v' :: nil|) ?? 
                    mutexunlock_ecb_ptr_holder_abt (|Vint32 i :: nil|));; s0 ||>  ** 
             HMuxInfo mls ** HEvPtr ptrmp ** HCurTCB t ** P)  
           (<|| ABORT ||>  ** HMuxInfo mls ** HEvPtr ptrmp ** HCurTCB t ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (HMuxInfo mls ** HEvPtr ptrmp ** HCurTCB t ** P))
    by can_change_aop_solver. 
  eapply absinfer_trans;
    try eapply absinfer_seq;
    try (eapply absinfer_seq_abt; try eauto);
    try eauto.
  destruct H1 as [Hptr | Hnull].  
  - 
    eapply absinfer_trans.
    eapply absinfer_choice2.
    can_change_aop_solver. 2: eauto. can_change_aop_solver.
    eapply absinfer_trans.
    eapply absinfer_choice1.
    can_change_aop_solver. 2: eauto. can_change_aop_solver.
    eapply absinfer_abt; try eauto.
    simpljoin1.
    absimp_abt_solver.
    apply i_ge_z; auto. 
    apply i_lt_user_max_event; auto.
    instantiate (1:=HMuxInfo mls ** HCurTCB t ** P).
    instantiate (1:=mutexunlock_get_ecb_ptr2 (|Vint32 i :: v' :: nil|)).
    instantiate (1:=s).
    sep auto.
    instantiate (1:=HMuxInfo mls ** HEvPtr ptrmp ** P).
    instantiate (1:=mutexunlock_get_ecb_ptr2 (|Vint32 i :: v' :: nil|)).
    instantiate (1:=s).
    sep auto.
  -
    eapply absinfer_trans.
    eapply absinfer_choice1.
    can_change_aop_solver. 2: eauto. can_change_aop_solver. 
    eapply absinfer_abt; try eauto.
    simpljoin1.
    absimp_abt_solver.
    clear -H H5 H6.
    apply i_ge_z; auto.
    apply i_lt_user_max_event; auto.
    instantiate (1:=HMuxInfo mls ** HCurTCB t ** P).
    instantiate (1:=mutexunlock_get_ecb_ptr1 (|Vint32 i :: v' :: nil|)).
    instantiate (1:=s).
    sep auto.
    instantiate (1:=HMuxInfo mls ** HEvPtr ptrmp ** P).
    instantiate (1:=mutexunlock_get_ecb_ptr1 (|Vint32 i :: v' :: nil|)).
    instantiate (1:=s).
    sep auto. 

  Unshelve.
  exact None. exact None. 
Qed.

Lemma mutexunlock_absimp_get_ecb_ptr'_ok:
  forall i mls sch vv P s0 t ptrmp ptrmp' eo o x n pro pi w c mc, 
    (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
    get mls i = Some (eo, o, x, n, pro, pi, w, c, mc) ->
    ((exists eid, eo = (Valid_Addr eid) /\ vv = Vptr eid) \/ eo = Null /\ vv = Vnull) -> 
    get ptrmp t = Some (Vnull, Vnull, Vnull) -> 
    ptrmp' = set ptrmp t (vv, Vnull, Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
           (<|| (mutexunlock_get_ecb_ptr1 (|Vint32 i :: vv :: nil|) ??
                    mutexunlock_get_ecb_ptr2 (|Vint32 i :: vv :: nil|) ?? 
                    mutexunlock_ecb_ptr_holder_abt (|Vint32 i :: nil|));; s0 ||>  ** 
             HMuxInfo mls ** HEvPtr ptrmp ** HCurTCB t ** P) 
           (<|| s0 ||> ** HMuxInfo mls ** HEvPtr ptrmp' ** HCurTCB t ** P). 
Proof.
intros.
assert (Hc: forall ptrmp, can_change_aop (HMuxInfo mls ** HEvPtr ptrmp ** HCurTCB t ** P))
           by (intros; can_change_aop_solver).
 eapply absinfer_trans; try eapply absinfer_seq_end; [ | | | eauto ]; eauto.
 eapply absinfer_seq; eauto.
 instantiate (1:= None).
 destruct H1; simpljoin.
 -
    infer_part1 1%nat.
    eapply absinfer_prim; eauto.
    unfold absimp.
    introv Hsat.
    do 2 eexists.
    split.
    instantiate (2:=END None).
    instantiate (1:=set O evptrid (evptr (set ptrmp t (Vptr x0, Vnull, Vnull)))).
    simpl_subst_gamma.
    repeat hmstep_call_consturctor; [ idtac | idtac | idtac | apply map_join_emp | .. ];
    try apply map_join_emp;
    [ unfolds; try tri_exists_and_solver | try absinfer_side_condition_solver.. ];
   try (solve [ repeat rewrite jl_merge_emp; try apply map_join_emp ]).
   destruct s as [[[[]]]].
   repeat eexists; eauto.
   apply i_ge_z; auto.
   apply i_lt_user_max_event; auto.
   simpl_sat Hsat. simpljoin1.
   simpl in *.
   eapply join_sig_get; eauto.
   sep_lifts_trms_in Hsat evptrid. 
   simpl_sat Hsat. simpljoin1.
   simpl in *.
   eapply join_sig_get; eauto.
   sep_lifts_trms_in Hsat curtid.
   simpl_sat Hsat. simpljoin1.
   simpl in *.
   eapply join_sig_get; eauto.
   repeat simpl_absdata_sep; sep auto.
-
   lets Hs: EvAuxPtrMod.get_set_same H2.
   unfold set. unfold EvAuxPtrMap.
   rewrite Hs.
   infer_solver 0%nat.
   destruct s as [[[[]]]].
   get_hsat Hsat.
   repeat eexists; eauto.
   apply i_ge_z; auto.
   apply i_lt_user_max_event; auto.
   simpl_sat Hsat. simpljoin1.
   simpl in *.
   eapply join_sig_get; eauto.
   sep_lifts_trms_in Hsat evptrid. 
   simpl_sat Hsat. simpljoin1.
   simpl in *.
   eapply join_sig_get; eauto.
   sep_lifts_trms_in Hsat curtid.
   simpl_sat Hsat. simpljoin1.
   simpl in *.
   eapply join_sig_get; eauto.
Qed.

Lemma mutexunlock_absimp_before_ok: 
  forall i eo o x n w pi pro c mc V_eid s1 minfob sch P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
          get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
         (exists eid,  eo = (Valid_Addr eid) /\ V_eid = Vptr eid) \/ eo = Null /\ V_eid = Vnull ->
         can_change_aop P -> 
         absinfer sch 
           (<|| mutexunlock_ecb_ptr (|(Vint32 i) :: V_eid :: nil|);; s1 ||>  ** HMuxInfo minfob ** P)
           (<|| s1 ||>  ** HMuxInfo minfob ** P). 
Proof.

  introv Hrgn Hsi Heo Hcop.   
  infer_solver 0%nat.  
  do 12 eexists.
  splits;eauto.
  split.
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  eapply absdata_elim.
  instantiate (1:= P).
  instantiate (1:=mutexunlock_ecb_ptr (|Vint32 i :: V_eid :: nil|)).
  instantiate (1:=s).
  eauto.
  Unshelve. 
  exact None.
Qed.

Lemma mutexunlock_absimp_get_before_ok: 
  forall i eo o x n w pi pro c mc V_eid s1 minfob sch P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
          get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
         (exists eid,  eo = (Valid_Addr eid) /\ V_eid = Vptr eid) \/ eo = Null /\ V_eid = Vnull ->
         can_change_aop P -> 
         absinfer sch 
           (<||
            mutexunlock_ecb_ptr (|(Vint32 i) :: V_eid :: nil|) ;; s1 ||>  ** HMuxInfo minfob ** P)
           (<|| s1 ||>  ** HMuxInfo minfob ** P). 
Proof.
  introv Hrgn Hsi Heo Hcop.   
  infer_solver 0%nat.  
  do 12 eexists.
  splits;eauto.
  split.
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  eapply absdata_elim.
  instantiate (1:= P).
  instantiate (1:=mutexunlock_ecb_ptr (|Vint32 i :: V_eid :: nil|)).
  instantiate (1:=s).
  eauto.
  Unshelve. 
  exact None.
Qed. 

Lemma mutexunlock_absimp_recurtp_before_ok: 
  forall i eo o x n w pi pro c mc V_tp s1 minfob sch P, 
          get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
          V_tp =Vint32 x -> 
         can_change_aop P -> 
         absinfer sch 
           (<||  mutexunlock_recurtype(|(Vint32 i) :: V_tp :: nil|) ;; s1 ||>  ** HMuxInfo minfob ** P)
           (<||  s1 ||>  ** HMuxInfo minfob ** P). 
Proof.
  introv Hrgn Hsi Hcop.   
  infer_solver 0%nat.  
Qed. 

Lemma mutexunlock_absimp_recurtp_before_abt: 
  forall i eo o x n w pi pro c mc V_tp s1 minfob sch P, 
          get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
          V_tp <> Vint32 x ->
         can_change_aop P -> 
         absinfer sch 
           (<|| mutexunlock_recurtype(|(Vint32 i) :: V_tp :: nil|) ;; s1 ||>  ** HMuxInfo minfob ** P)
           (<|| ABORT ||>  ** HMuxInfo minfob ** P). 
Proof.
  introv Hsi Htp Hcop.
  assert(can_change_aop(HMuxInfo minfob ** P)).
  can_change_aop_solver. 
  eapply absinfer_trans.
  eapply absinfer_seq; try eauto.
  instantiate (1:=ABORT). 
  apply absinfer_abt.
  try can_change_aop_solver. 
  try can_change_aop_solver. 
  absimp_abt_solver.
  eapply absinfer_seq_abt; auto.
Qed.

Lemma mutexunlock_absimp_curprio_before_ok: 
  forall prio m st sus V_curp s1 t tls sch P, 
          TcbMod.get tls t = Some (prio,st,m, sus) ->
          V_curp =Vint32 prio ->
         can_change_aop P -> 
         absinfer sch 
           (<||  mutexunlock_curprio(| V_curp :: nil|) ;; s1 ||>  ** HTCBList tls ** HCurTCB t  ** P)
           (<||  s1 ||>  ** HTCBList tls ** HCurTCB t  ** P). 
Proof.
  intros.
  infer_solver 0%nat.  
Qed. 

Lemma mutexunlock_absimp_curprio_before_abt: 
  forall prio m st sus V_curp s1 t tls sch P, 
          TcbMod.get tls t = Some (prio,st,m, sus) ->
          V_curp <> Vint32 prio ->
         can_change_aop P -> 
         absinfer sch 
           (<||  mutexunlock_curprio(| V_curp :: nil|) ;; s1 ||>  ** HTCBList tls ** HCurTCB t  ** P)
           (<||  ABORT ||>  ** HTCBList tls ** HCurTCB t  ** P). 
Proof.
  introv Hrgn Hsi Hcop.
  assert(can_change_aop(HTCBList tls ** HCurTCB t  ** P)).
  can_change_aop_solver. 
  eapply absinfer_trans.
  eapply absinfer_seq; try eauto.
  instantiate (1:=ABORT). 
  apply absinfer_abt.
  try can_change_aop_solver. 
  try can_change_aop_solver. 
  absimp_abt_solver.
  instantiate(3:= s).
  instantiate(2:= mutexunlock_curprio (|V_curp :: nil|)).
  sep pauto.
  eapply absinfer_seq_abt; auto.
Qed.

Lemma mutexunlock_absimp_if_null_yes2_abt: 
  forall sch V_ret V_eid s1 P, 
         V_eid = Vnull -> 
         V_ret <> (Vint32 (Int.repr EINVAL)) -> 
         can_change_aop P -> 
         absinfer sch 
           (<|| mutexunlock_if_null_yes (|V_eid :: V_ret :: nil|) ?? s1 ||>  **  P)
           (<|| ABORT ||>  ** P). 
Proof.
  introv Hv Hv1 Hcop.
  eapply absinfer_trans.
 eapply absinfer_choice1; try eauto.
  eapply absinfer_abt; try can_change_aop_solver.
  unfolds; intros. eexists; exgamma.
  split. simpl_subst_gamma. hmstep_call_consturctor. 
  eapply spec_prim_step_abt.
  unfolds. do 1 eexists. splits; eauto. rewrite Hv. auto. apply map_join_emp .  
  repeat hmstep_call_consturctor.
  simpl in *. simpljoin. do 6 eexists. 
  splits ; try eauto. 
  eapply change_aop_rule; eauto. 
Qed.  

Lemma mutexunlock_absimp_if_null_yes2_end: 
  forall sch  V_ret V_eid s1 P, 
         V_eid = Vnull -> 
         V_ret = (Vint32 (Int.repr EINVAL)) -> 
         can_change_aop P -> 
         absinfer sch 
           (<||  mutexunlock_if_null_yes (|V_eid :: V_ret :: nil|) ?? s1 ||>  **  P)
           (<|| END (Some (Vint32 (Int.repr EINVAL))) ||>  ** P). 
Proof.
  introv Hv Hv1 Hcop.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto.
  instantiate (1:=P). pure_auto.
  pure_auto.
  infer_solver 0%nat.
  eexists. splits; eauto.
  rewrite Hv.
  auto.
Qed.

Lemma mutexunlock_absimp_if_null_yes_end: 
  forall sch V_ret V_eid s1 P, 
         V_eid = Vnull -> 
         V_ret = (Vint32 (Int.repr EINVAL)) -> 
         can_change_aop P -> 
         absinfer sch 
           (<|| 
                  mutexunlock_if_null_yes (|V_eid :: V_ret :: nil|) ?? s1 ||>  **  P)
           (<|| END (Some (Vint32 (Int.repr EINVAL))) ||>  ** P). 
Proof.
  introv Hv Hv1 Hcop.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto.
  instantiate (1:=P). pure_auto.
  pure_auto.
  infer_solver 0%nat.
  eexists. splits; eauto.
  rewrite Hv.
  auto.
Qed.

Lemma mutexunlock_absimp_if_null_yes_abt: 
  forall sch V_ret V_eid s1 P, 
         V_eid = Vnull -> 
         V_ret <> (Vint32 (Int.repr EINVAL)) -> 
         can_change_aop P -> 
         absinfer sch 
           (<||
                    mutexunlock_if_null_yes (|V_eid :: V_ret :: nil|) ??
                              (mutexunlock_if_null_no (|V_eid :: nil|) ;; s1) ||>  **  P)
           (<|| ABORT ||>  ** P). 
Proof.
  introv Hv Hv1 Hcop.
  eapply absinfer_trans.
 eapply absinfer_choice1; try eauto.
  eapply absinfer_abt; try can_change_aop_solver.
  unfolds; intros. eexists; exgamma.
  split. simpl_subst_gamma. hmstep_call_consturctor. 
  eapply spec_prim_step_abt.
  unfolds. do 1 eexists. splits; eauto. rewrite Hv. auto. apply map_join_emp .  
  repeat hmstep_call_consturctor.
  simpl in *. simpljoin. do 6 eexists. 
  splits ; try eauto. 
  eapply change_aop_rule; eauto. 
Qed.

Lemma mutexunlock_absimp_if_null_no: 
  forall sch V_ret V_eid s1 P, 
         (exists eid, V_eid =Vptr eid) -> 
         can_change_aop P -> 
         absinfer sch 
           (<|| mutexunlock_if_null_yes (|V_eid :: V_ret :: nil|) ??
                              (mutexunlock_if_null_no (|V_eid :: nil|) ;; s1) ||>  **  P)
           (<||  s1  ||>  ** P). 
Proof.
  introv Hv Hcop.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto.
  instantiate (1:=P). pure_auto. 
  pure_auto.
  infer_solver 0%nat.  
  destruct Hv. exists x.
  splits; eauto.
  rewrite e. 
  auto.
Qed.

(* Open Scope code_scope.
Open Scope list_scope.
Open Scope int_scope. *)

 Lemma mutexunlock_absimp_if_null_owner_no_end: 
  forall i sch qls mls o x n w pi pro c mc V_eid V_ret ow pr y wl s1 eid P, 
         V_eid =Vptr eid ->
         get mls i = Some (Valid_Addr eid, o, x, n, pro, pi, w, c, mc) ->
         get qls eid =Some (absmutexsem pr y, wl) ->
         ((y = None /\ ow = $ OS_MUTEX_AVAILABLE ) \/
         (exists t op,  y = Some (t, op) /\ ow = op)) ->
         can_change_aop P -> 
         absinfer sch 
           (<|| mutexunlock_if_null_yes (|V_eid :: V_ret :: nil|) ??
                 ( mutexunlock_if_null_owner_no (|(Vint32 i) :: V_eid :: (Vint32 ow) :: nil|) ;; s1) ||> ** HECBList qls ** HMuxInfo mls ** P)
           (<|| s1 ||>  ** HECBList qls  ** HMuxInfo mls  ** P). 
Proof.
   introv Hv Hm Hq How Hcop.
  eapply absinfer_trans.
  assert( can_change_aop (HECBList qls  ** HMuxInfo mls  ** P)).
  try can_change_aop_solver.
  eapply absinfer_choice2.
  pure_auto.
  instantiate (1:=HECBList qls ** HMuxInfo mls ** P). pure_auto. 
  pure_auto.
  infer_solver 0%nat.
  do 17 eexists.
  split. instantiate(1:=Vint32 ow).
  instantiate(1:= eid).
  instantiate(1:= i).
  rewrite Hv. auto.
  splits; eauto.
  eapply absdata_elim.
  instantiate (1:= HECBList qls ** P).
  instantiate (1:=mutexunlock_if_null_owner_no
    (|Vint32 i :: V_eid :: Vint32 ow :: nil|)).
  instantiate (1:=s).
  sep cancel 1%nat 2%nat. auto.
  eapply absdata_elim.
  instantiate (1:=  HMuxInfo mls ** P).
  instantiate (1:= mutexunlock_if_null_owner_no
    (|Vint32 i :: V_eid :: Vint32 ow :: nil|)).
  instantiate (1:=s). auto.
Qed.

 Lemma mutexunlock_absimp_if_null_owner_no_abt: 
  forall i sch qls mls o x n w pi pro c mc V_eid V_ret ow pr y wl s1 eid P rv, 
         V_eid =Vptr eid ->
         get mls i = Some (Valid_Addr eid, o, x, n, pro, pi, w, c, mc) ->
         get qls eid =Some (absmutexsem pr y, wl) ->
        (( y = None /\ ow = $ OS_MUTEX_AVAILABLE  ) \/
         (exists t op,  y = Some (t, op) /\ ow = op)) ->
         rv <> Vint32 ow ->
         can_change_aop P -> 
         absinfer sch 
           (<|| mutexunlock_if_null_yes (|V_eid :: V_ret :: nil|) ??
                 ( mutexunlock_if_null_owner_no (|(Vint32 i) :: V_eid :: rv :: nil|) ;; s1) ||> ** HECBList qls ** HMuxInfo mls ** P)
           (<|| ABORT ||>  ** HECBList qls  ** HMuxInfo mls  ** P). 
Proof.
  introv Hv Hg He How Hneq Hcop.
  assert(can_change_aop (HECBList qls ** HMuxInfo mls ** P)).
  try can_change_aop_solver.
  eapply absinfer_trans.
 eapply absinfer_choice2; try eauto.
  eapply absinfer_trans.
  eapply absinfer_seq; try eauto.
  instantiate (1:=ABORT). 
  eapply absinfer_abt; try can_change_aop_solver.
  unfolds; intros. eexists; exgamma.
  split. simpl_subst_gamma. hmstep_call_consturctor. 
  eapply spec_prim_step_abt.
  unfolds. exists i. do 16 eexists. splits; eauto.
  inverts Hv. auto.
  eapply absdata_elim.
  instantiate(2:= mutexunlock_if_null_owner_no
     (|Vint32 i :: V_eid :: rv :: nil|)).
  instantiate (2:=O).
  instantiate (2:= s).
  sep pauto.
  eapply absdata_elim.
  instantiate(2:=mutexunlock_if_null_owner_no
     (|Vint32 i :: V_eid :: rv :: nil|)).
  instantiate (2:= s).
  sep pauto.
  apply map_join_emp .  
  repeat hmstep_call_consturctor.
  sep remember (1%nat :: nil); simpl in *; simpljoin;
  do 6 eexists; splits; try eauto;
  eapply change_aop_rule; eauto.
  eapply absinfer_seq_abt;auto.
Qed.

Lemma mutexunlock_absimp_ok: 
  forall s1 s2 sch P, 
         can_change_aop P ->
         absinfer sch
           (<|| s1 ?? s2 ||> ** P)
           (<|| s1 ||>  ** P). 
Proof.
  intros.
  eapply absinfer_choice1.
  pure_auto. pure_auto.
  auto.
Qed.

Lemma mutexunlock_absimp_ok2: 
  forall s1 s2 sch P, 
         can_change_aop P ->
         absinfer sch
           (<|| s1 ?? s2 ||> ** P)
           (<|| s2 ||>  ** P). 
Proof.
  intros.
  eapply absinfer_choice2.
  pure_auto. pure_auto.
  auto.
Qed.

Lemma mutexunlock_absimp_recvcnt_decrement_oweq_end:
  forall posv s1 eid pe o x w pi pro c mc minfob cn ow priocl curp tp P sch,
    MibMod.get minfob posv = Some (pe, o, x, cn, pro, pi, w, c, mc) ->
    tp = $ PTHREAD_MUTEX_RECURSIVE ->
    (ow = curp \/ priocl = curp) ->
    can_change_aop P ->
    absinfer sch
      (<|| mutexunlock_recvcnt_decrement_oweq (|(Vint32 posv) :: (Vptr eid) :: (Vint32 ow) :: (Vint32 tp) :: (Vint32 curp) :: (Vint32 priocl) :: nil|) ;; s1 ||> ** 
              HMuxInfo minfob ** P)
      (<|| s1 ||> ** 
          HMuxInfo (MibMod.set minfob posv (pe, o, x, (Int.sub cn Int.one), pro, pi, w, c, mc)) ** P). 
Proof.
  intros.
  subst.
  infer_solver 0%nat.
Qed.

Lemma mutexunlock_absimp_prioceil_before_ok: 
  forall  i eo o x n w pi pro c mc V_priocl s1 minfob sch P, 
          get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
          V_priocl =Vint32 pi -> 
         can_change_aop P -> 
         absinfer sch 
           (<||  mutexunlock_prioceil(| (Vint32 i) :: V_priocl :: nil|) ;; s1 ||>  ** HMuxInfo minfob ** P)
           (<||  s1 ||>  ** HMuxInfo minfob ** P). 
Proof.
  intros.   
  infer_solver 0%nat.  
Qed. 

Lemma mutexunlock_absimp_priocl_before_abt: 
  forall  i eo o x n w pi pro c mc V_priocl s1 minfob sch P, 
          get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
          V_priocl  <> Vint32 pi -> 
         can_change_aop P -> 
         absinfer sch 
           (<||  mutexunlock_prioceil(| (Vint32 i) :: V_priocl :: nil|) ;; s1 ||>  ** HMuxInfo minfob ** P)
           (<||  ABORT ||>  ** HMuxInfo minfob ** P). 
Proof.
  introv Hrgn Hsi Hcop.
  assert(can_change_aop( HMuxInfo minfob ** P)).
  can_change_aop_solver. 
  eapply absinfer_trans.
  eapply absinfer_seq; try eauto.
  instantiate (1:=ABORT). 
  apply absinfer_abt.
  try can_change_aop_solver. 
  try can_change_aop_solver. 
  absimp_abt_solver.
  eapply absinfer_seq_abt; auto.
Qed.

Lemma mutexunlock_absimp_get_recurcnt_before_ok: 
  forall i eo o x n w pi pro c mc V_recnt s1 minfob sch P, 
          get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
          V_recnt =Vint32 n -> 
         can_change_aop P -> 
         absinfer sch 
           (<||  mutexunlock_get_recurcnt(|(Vint32 i) :: V_recnt :: nil|) ;; s1 ||>  ** HMuxInfo minfob ** P)
           (<||  s1 ||>  ** HMuxInfo minfob ** P). 
Proof.
  introv Hsi Heq Hcop.
  infer_solver 0%nat.
Qed. 

Lemma mutexunlock_absimp_get_recurcnt_before_abt: 
  forall i eo o x n w pi pro c mc V_recnt s1 minfob sch P, 
          get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
          V_recnt <> Vint32 n -> 
         can_change_aop P -> 
         absinfer sch 
           (<||  mutexunlock_get_recurcnt(|(Vint32 i) :: V_recnt :: nil|) ;; s1 ||>  ** HMuxInfo minfob ** P)
           (<|| ABORT ||>  ** HMuxInfo minfob ** P). 
Proof.
  introv Hsi Hneq Hcop.
  assert(can_change_aop(HMuxInfo minfob ** P)).
  can_change_aop_solver. 
  eapply absinfer_trans.
  eapply absinfer_seq; try eauto.
  instantiate (1:=ABORT). 
  apply absinfer_abt.
  try can_change_aop_solver. 
  try can_change_aop_solver. 
  absimp_abt_solver.
  eapply absinfer_seq_abt; auto.
Qed.

Lemma mutexunlock_absimp_if_rcnt_zero_neq_abt: 
  forall i eid rcnt rv sch P, 
          Int.eq rcnt Int.zero =false ->
          rv <> (Vint32 (Int.zero)) ->
         can_change_aop P -> 
         absinfer sch 
           (<||  mutexunlock_if_rcnt_zero_neq(|(Vint32 i) :: (Vptr eid) :: (Vint32 rcnt ) :: rv :: nil|) ||>  ** P)
           (<|| ABORT ||>  ** P). 
Proof.
  intros.
  eapply absinfer_abt; try can_change_aop_solver.
  unfolds; intros. eexists; exgamma.
  split. simpl_subst_gamma. hmstep_call_consturctor. 
  eapply spec_prim_step_abt.
  unfolds. do 4 eexists.  splits; eauto. apply map_join_emp .  
  repeat hmstep_call_consturctor.
  simpl in *. simpljoin. do 6 eexists. 
  splits ; try eauto. 
  eapply change_aop_rule; eauto. 
Qed.

Lemma mutexunlock_absimp_if_rcnt_zero_neq_end: 
  forall i eid rcnt rv sch P, 
          Int.eq rcnt Int.zero =false ->
          rv = (Vint32 (Int.zero)) ->
         can_change_aop P -> 
         absinfer sch 
           (<||  mutexunlock_if_rcnt_zero_neq(|(Vint32 i) :: (Vptr eid) :: (Vint32 rcnt ) :: rv :: nil|) ||>  ** P)
           (<|| END (Some (Vint32 (Int.zero))) ||>  ** P). 
Proof.
  intros.
  inverts H0.
  infer_solver 0%nat.
Qed.

Lemma mutexunlock_if_ow_curp_neq_abt: 
  forall i eid curp ow tp priocl rv sch P, 
          tp = $ PTHREAD_MUTEX_RECURSIVE ->
          Vint32 ow <> Vint32 curp ->
          Vint32 priocl <> Vint32 curp  ->
          rv <> (Vint32 (Int.repr EPERM)) ->
         can_change_aop P -> 
         absinfer sch 
           (<||  mutexunlock_if_ow_curp_neq (|(Vint32 i) :: (Vptr eid) :: (Vint32 ow) :: (Vint32 tp) :: (Vint32 curp) :: ( Vint32 priocl) :: rv :: nil|) ||>  ** P)
           (<|| ABORT ||>  ** P). 
Proof.
  intros.
  eapply absinfer_abt; try can_change_aop_solver.
  unfolds; intros. eexists; exgamma.
  split. simpl_subst_gamma. hmstep_call_consturctor. 
  eapply spec_prim_step_abt.
  unfolds. do 7 eexists.  splits; eauto. apply map_join_emp .  
  repeat hmstep_call_consturctor.
  simpl in *. simpljoin. do 6 eexists. 
  splits ; try eauto. 
  eapply change_aop_rule; eauto. 
Qed.

Lemma mutexunlock_if_ow_curp_neq_end: 
  forall i eid curp ow tp priocl rv sch P, 
          tp = $ PTHREAD_MUTEX_RECURSIVE ->
          Vint32 ow <> Vint32 curp ->
          Vint32 priocl <> Vint32 curp  ->
          rv = (Vint32 (Int.repr EPERM)) ->
         can_change_aop P -> 
         absinfer sch 
           (<||  mutexunlock_if_ow_curp_neq (|(Vint32 i) :: (Vptr eid) :: (Vint32 ow) :: (Vint32 tp) :: (Vint32 curp) :: ( Vint32 priocl) :: rv :: nil|) ||>  ** P)
           (<|| END (Some(Vint32 (Int.repr EPERM))) ||>  ** P). 
Proof.
  intros.
  inverts H2.
  infer_solver 0%nat.
Qed.

Lemma mutexunlock_absimp_after_set_ptr: 
  forall t ptrmp ptrmp' s sch P, 
         ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) -> 
         can_change_aop P -> 
         absinfer sch 
           (<||  mutexunlock_set_ptr(| nil|);; s ||> ** HCurTCB t ** HEvPtr ptrmp ** P)
           (<|| s ||> ** HCurTCB t ** HEvPtr ptrmp' ** P). 
Proof.
  intros.
  substs.
  infer_solver 0%nat.
  Unshelve.
  exact (None).
Qed.

Lemma mutexunlock_absimp_afterpost_rv1_end:
  forall v P sch s1 s2,
   Int.eq v ($ OS_ERR_NOT_MUTEX_OWNER) = true  ->
    can_change_aop P -> 
    absinfer sch
      (<|| mutexunlock_afterpost_rv1 (| Vint32 v  :: nil|) ?? s1 ?? s2 ||> ** P)
      (<|| END (Some (Vint32 (Int.repr EPERM))) ||> ** P). 
Proof.
  intros.
  subst.
  infer_solver 0%nat.
Qed.

Lemma mutexunlock_absimp_afterpost_rv2_end:
  forall v P sch s1 s3,
    Int.eq v ($ OS_ERR_NOT_MUTEX_OWNER) = false  ->
     Int.eq v ($ 0) = false ->
    can_change_aop P -> 
    absinfer sch
      (<|| s1 ?? mutexunlock_afterpost_rv2 (| Vint32 v  :: nil|) ?? s3 ||> ** P)
      (<|| END (Some (Vint32 (Int.repr EINVAL))) ||> ** P). 
Proof.
  intros.
  subst.
  infer_solver 1%nat.
Qed.

Lemma mutexunlock_absimp_afterpost_rv3_end:
  forall v P sch s1 s2,
     Int.eq v ($ OS_ERR_NOT_MUTEX_OWNER) = false  ->
     Int.eq v ($ 0) = true ->
    can_change_aop P -> 
    absinfer sch
      (<|| s1 ?? s2 ?? mutexunlock_afterpost_rv3 (| Vint32 v  :: nil|) ||> ** P)
      (<|| END (Some (Vint32 (Int.repr 0))) ||> ** P). 
Proof.
  intros.
  subst.
  infer_solver 2%nat.
Qed.

Open Scope Z_scope.

Lemma Beforepostpartproof:
forall  posv vow tp V_pevt V_ret tid v'5 j v3 v4 vp v'7 v'2 V_mux er vdom vnum,
Int.ltu posv Int.zero = false ->
Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) posv = false ->
posv <> $ (OS_USER_MAX_EVENTS / 3) ->
Int.eq posv (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) = false ->
Int.unsigned posv <= Int.max_unsigned ->
(* Int.unsigned vow <= 255 -> *)
{|OS_spec, GetHPrio, OSLInv, I,
fun v : option val =>
( <|| END v ||>  **
 p_local OSLInv tid init_lg **
 ((EX v11 : val, LV mutex @ (long) ∗ |-> v11) **
  (EX v11 : val, LV os_code_defs.x @ char_t |-> v11) **
  (EX v11 : val, LV os_code_defs.pos @ long |-> v11) **
  (EX v11 : val, LV ret @ long |-> v11) **
  (EX v11 : val, LV muxowner @ char_t |-> v11) **
  (EX v11 : val, LV ty @ long |-> v11) **
  (EX v11 : val, LV r @ long |-> v11) **
  (EX v11 : val, LV cpr @ char_t |-> v11) **
  (EX v11 : val, LV cal @ char_t |-> v11) **
  (EX v11 : val, LV pric @ long |-> v11) **
  (EX v11 : val, LV p @ OS_EVENT ∗ |-> v11) **
  (EX v0 : val, LV temp_dom @ char_t |-> v0) **
  (EX v0 : val, LV temp_num @ char_t |-> v0) ** Aemp) **
 Aie true ** Ais nil ** Acs nil ** Aisr empisr ** (EX er, Aier er)) **
A_dom_lenv
  ((mutex, (long) ∗)
   :: (os_code_defs.x, char_t)
      :: (os_code_defs.pos, long)
         :: (ret, long)
            :: (muxowner, char_t)
               :: (ty, long)
                  :: (r, long)
                     :: (cpr, char_t)
                        :: (cal, char_t)
                           :: (pric, long)
                              :: (p, OS_EVENT ∗)
                                :: (temp_dom, char_t) :: (temp_num, char_t) :: nil), Afalse|}
|- tid
{{ <|| muxpost (Vint32 posv) V_pevt V_ret ||>  **
  Aisr empisr **
  Aie true **
  Ais nil **
  Acs nil **
  Aier er **
  p_local OSLInv tid
  (logic_val (V$ 1)
     :: logic_val (V$ __EvLoc_normal)
        :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
  LV r @ long |-> v'5 **
  LV os_code_defs.x @ char_t |-> Vint32 j **
  LV cpr @ char_t |-> v3 **
  LV os_code_defs.pos @ long |-> Vint32 posv **
  LV temp_dom @ char_t |-> vdom **
  LV temp_num @ char_t |-> vnum **
  A_dom_lenv
    ((mutex, (long) ∗)
     :: (os_code_defs.x, char_t)
        :: (os_code_defs.pos, long)
           :: (ret, long)
              :: (muxowner, char_t)
                 :: (ty, long)
                    :: (r, long)
                       :: (cpr, char_t)
                          :: (cal, char_t)
                             :: (pric, long)
                                :: (p, OS_EVENT ∗)
                                    :: (temp_dom, char_t) :: (temp_num, char_t) :: nil) **
  LV pric @ long |-> v4 **
  LV p @ OS_EVENT ∗ |-> Vptr vp **
  LV ty @ long |-> Vint32 tp **
  LV muxowner @ char_t |-> Vint32 vow **
  LV cal @ char_t |-> v'7 **
  LV ret @ long |-> v'2 ** LV mutex @ (long) ∗ |-> V_mux}} ENTER_CRITICAL;ₛ
p ′ =ₑ efield (Pthread_Mutex ′ [os_code_defs.pos ′]) pevent;ₛ
OSTCBCur ′ → __OSTskMuxPtr =ₑ p ′;ₛ
EXIT_CRITICAL;ₛ
cal ′ =ᶠ OSMutexPost (·p ′·);ₛ
ENTER_CRITICAL;ₛ
OSTCBCur ′ → __OSTskMuxPtr =ₑ NULL;ₛ
EXIT_CRITICAL;ₛ
ret ′ =ₑ 〈 long 〉 cal ′;ₛ
If (ret ′ ==ₑ ′ OS_ERR_NOT_MUTEX_OWNER){RETURN ′ EPERM};ₛ
IF (ret ′ !=ₑ ′ 0){RETURN ′ EINVAL}ELSE {RETURN ′ 0} {{Afalse}}.
Proof.
  introv E1 E2 E3 Hposv_neq Hlemu.

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
    rewrite zdiv_equiv.
    rewrite Hsieq.
    auto.
    clear -Hrgn5 Hrgn6. int auto.
    clear. int auto.
  }

  hoare forward prim.
  hoare unfold. unfold EvtInv.
  hoare normal pre; hoare_ex_intro.
  hoare_assert_pure (length v'32 = (∘ (OS_USER_MAX_EVENTS / 3))).
  { get_hsat Hsat. sep_lifts_trms_in Hsat AMuxEIBs.
     eapply length_vll_apthrmux; eauto.  }
  eapply pure_split_rule'; introv Hlen_minfo.
  unfold AMuxEIBs.
  hoare normal pre; hoare_ex_intro.
  hoare unfold.

  hoare_lifts_trms_pre (Aop, APthreadMutex).
  destruct v'41.
  eapply backward_rule1.
  introv Hsat.
  eapply APthreadMutex_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned posv)).
  sep cancel APthreadMutex.
  eauto.
  rewrite Hlen_minfo.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.

  hoare unfold.

  hoare_lifts_trms_pre (Aop).
  hoare forward.
  eapply assign_rule_lvar.
  split; introv Hsat. sep cancel (Alvarmapsto p). eauto.
  sep auto.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  eapply new_array_type_vallist_match_split1 in H6; eauto.
  simpljoin; auto.
  eapply eq_vptr; eauto.
  intros. eexists. sep cancel p_local. simpl; eauto.

  lets Hmls: muxb_corr H1 H15 E1 Hlemu.
  destruct Hmls as (eo & ow' & tp' & rcnt & prot & pcp & wq & c & mc & Hget & Hmls).
  rename v'42 into mutvl.
  assert (Hcases: 
           ((exists eid,
                eo = Valid_Addr eid /\ V_OSMUXINFOPevent mutvl = Some (Vptr eid) /\ eid <> vhold_addr) \/
              eo = Null /\ V_OSMUXINFOPevent mutvl = Some Vnull) \/
             eo = Holder /\ V_OSMUXINFOPevent mutvl = Some (Vptr vhold_addr) 
         ). 
  { clear -Hmls. intuition. }
  clear Hmls.

  hoare_lifts_trms_pre (Aop, absmutinfoid).
  destruct Hcases as [ Hok | Habt ].
  2: {
    destruct Habt as (Habt1 & Habt2).
    subst eo.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutexunlock_absimp_ecb_placeholder_abt; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  (* OSTCBCur ′ → __OSTskMuxPtr =ₑ p ′;ₛ *)
  hoare_lifts_trms_pre (tcbllsegevaux,AOSTCBList, p_local).
  eapply backward_rule1.
  introv Hsat.
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre. 
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  assert (Hisptr: isptr (nth_val' 8 mutvl)).
  {
    apply new_array_type_vallist_match_mux_getp in H6. 
    clear -H6. simpljoin1. 
    unfold V_OSSINFOPevent in H.
    do 9 (destruct mutvl; simpl in H; tryfalse).  
    inverts H. simpl. auto.
  }
  hoare_assign_evaux.
  {
     apply new_array_type_vallist_match_mux_getp in H6.
     clear -H6. 
     simpljoin1.
     unfold V_OSSINFOPevent in H.
     do 9 (destruct mutvl; simpl in H; tryfalse).
     inverts H. destruct H0. subst. auto. simpljoin1.
  }
  rename v'39 into locmp.
  rename v'40 into ptrmp.
  assert (Hevptr: get ptrmp tid = Some (Vnull, Vnull, Vnull)).  
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
     join auto.
  }
  assert (Hloc: get locmp tid = Some (V$ __EvLoc_normal)).
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  rename v'10 into els.
  rename v'34 into semeibs.
  rename v'35 into muxeibs.
  rename v'36 into mqeibs.
  remember (nth_val' 8 mutvl) as V_pevt0.
  fold_evaux_mux V_pevt0.
  clear -Hisptr.  simpl. destruct Hisptr; mytac.

  assert (Hvpevt: ((exists eid,  eo = Valid_Addr eid /\ V_pevt = Vptr eid) \/ eo = Null /\ V_pevt = Vnull) 
        \/ ((exists eid, eo = Valid_Addr eid /\ V_pevt <> Vptr eid) \/ eo = Null /\ V_pevt <> Vnull)).
  {
    destruct Hok as [( eid & Heo & _) | (Heo & _)]; subst eo.
    assert (Hv: V_pevt = Vptr eid \/ V_pevt <> Vptr eid) by tauto.
    destruct Hv; [left | right]; left; eauto.
    assert (Hv: V_pevt = Vnull \/ V_pevt <> Vnull) by tauto.
    destruct Hv; [left | right]; right; eauto.
    }
  hoare_lifts_trms_pre (Aop, absmutinfoid, evptrid, curtid).
  destruct Hvpevt as [Hvpevt | Habt].
  2: {
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexunlock_absimp_get_ecb_ptr'_mismatch_abt; eauto.
        unfold CurTid.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
        }
  assert (Hvpevt_eq: V_pevt0 = V_pevt).
  { clear -Hok Hvpevt HeqV_pevt0.
     unfold V_OSMUXINFOPevent in *.
     rewrite HeqV_pevt0 in *.
     destruct Hok as [( eid & Heo & Hvp & _) | (Heo & Hvp)]; subst eo;
     eapply nth_val_nth_val'_some_eq in Hvp; rewrite Hvp;
     destruct Hvpevt as [( eid0 & Heo & Hvp1) | (Heo & Hvp1)]; inverts Heo;
     auto.
  }
  subst V_pevt0.
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutexunlock_absimp_get_ecb_ptr'_ok; eauto.
   unfold CurTid.
   can_change_aop_solver.
   eapply absinfer_eq.

   eapply backward_rule1.
   introv Hsat.
   eapply APthreadMutex_select_sn_ex_strong.
   exists v'13 (Z.to_nat (Int.unsigned posv)) v'41.
   exists mutvl.
   sep pauto.
  (* EXIT_CRITICAL *)
  lets Hset: EvAuxPtrMod.get_set_same Hevptr.
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel Aier.
  unfold p_local. unfold LINV. unfold OSLInv. sep pauto.
  2: { splits; eauto. }
  unfold EvtInv.
  unfold AMuxEIBs.
  unfold tcbllsegevaux.
  sep normal. sep eexists.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMqEIBs.
  sep cancel APthreadMutex.
  sep cancel llsegevaux.
  sep cancel AMuxCap.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep pauto; eauto.
  eapply evdel_nodup_normal_muxptr_preserve; eauto.
  eapply evcre_nodup_normal_muxptr_preserve; eauto.
  3: { destruct Hvpevt as [(eid & Heo & Hvp) | (Heo & Hvp)];
         rewrite Hvp.
         eapply sem_ecb_p_muxptr_normal_preserve; eauto.
         unfold is_mux. eapply H4; eauto. (* RH_ECBlk_EIBlk_Mux_P *)
         rewrite Hset; eauto. }
  2: {  destruct Hvpevt as [(eid & Heo & Hvp) | (Heo & Hvp)];
         rewrite Hvp.
         eapply mux_ecb_p_nuxptr_normal_preserve; eauto.
         unfold is_mux. eapply H4; eauto.
         rewrite Hset; eauto. }
  destruct Hvpevt as [(eid & Heo & Hvp) | (Heo & Hvp)];
  rewrite Hvp.
  eapply mq_ecb_p_muxptr_normal_preserve; eauto.
  unfold is_mux. eapply H4; eauto.
  rewrite Hset; eauto.
  auto.
  pure_auto.
  (* split the mutvl as mutvl = _ :: _ :: ... :: nil *)
  lets Hmut_vll: H6.
  rename H6 into Hmut_vl.
  eapply new_array_type_vallist_match_split1 in Hmut_vl; eauto.
  destruct Hmut_vl as (_ & _ & Hmut_vl).
  lets Hmut_vl_eq: struct_type_vallist_match_mutex_info_t_imp Hmut_vl.
  destruct Hmut_vl_eq as (vtp & vpro & vpcp & vwq & vcs & vow' & vrcnt & vtsk & vp' & vmc' & Hmut_vl_eq & Hvp_ptr).
  subst mutvl.
  unfold V_OSMUXINFOPevent in *.
  simpl nth_val in *.
  simpl nth_val' in *.
  subst vp'.
  (* cal ′ =ᶠ OSMutexPost (·p ′·);ₛ *)
  change (V_pevt :: V_ret :: nil) with ((V_pevt :: nil) ++ ( V_ret :: nil)).
  hoare forward.
  clear -Hvp_ptr. pure_auto.
  pure_auto.
  (* retpost OSMutexPostPost *)
  unfold retpost.  introv Hsat. inverts Hsat.
  sep destruct H6.
  sep split in H6. mytac.
  clear -Hvp_ptr. pure_auto.
  introv Hsat. sep destruct Hsat. eexists.
  sep cancel p_local. simpl; auto.
  introv Hsat. sep destruct Hsat. eexists.
  sep cancel p_local. simpl; auto.
  (* end of OSMutexPost *)
   unfold OSMutexPostPost.
  unfold OSMutexPostPost'.
  unfold getasrt.
  hoare unfold.
  inverts H6.
  rename v'35 into verr.

  (* ENTER_CRITICAL;ₛ
       OSTCBCur ′ → __OSTskMuxPtr =ₑ NULL;ₛ
       EXIT_CRITICAL;ₛ *)
    hoare forward prim.
    unfold EvtInv.
    hoare normal pre.
    hoare_ex_intro.
    hoare_split_pure_all.
    hoare_lifts_trms_pre (tcbllsegevaux,AOSTCBList,p_local).
    eapply backward_rule1.
    introv Hsat. 
    eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
    hoare normal pre. 
    hoare_ex_intro.
    hoare_split_pure_all.
    subst.

  rename v'80 into locmp'.
  rename v'81 into ptrmp'.
  rename v'51 into els'.
  rename v'75 into semeibs'.
  rename v'76 into muxeibs'.
  rename v'77 into mqeibs'.
  assert (Hevptr': get ptrmp' tid = Some (v'36, Vnull, Vnull)).  
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  hoare_assign_evaux.

  hoare_lifts_trms_pre (Aop, curtid, evptrid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexunlock_absimp_after_set_ptr; eauto.
  can_change_aop_solver.
  unfold CurTid. go.
  eapply absinfer_eq.

  (*  EXIT_CRITICAL;ₛ *)
  fold_evaux_mux Vnull.
  hoare forward prim.
  sep cancel Aier.
  sep cancel tcbdllflag.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep pauto.
  2: { splits; eauto. }
  unfold EvtInv.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  unfold tcbllsegevaux.
  sep cancel llsegevaux.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.
  eapply evdel_nodup_set_null3_preserve; eauto.
  eapply evcre_nodup_set_null3_preserve; eauto. 
  eapply mq_ecb_p_set_null3_preserve; eauto.
  eapply mux_ecb_p_set_null3_preserve; eauto.
  eapply sem_ecb_p_set_null3_preserve; eauto.
  auto.
  pure_auto.

 (*ret ′ =ₑ 〈 long 〉 cal ′;ₛ*)
  hoare forward.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_lvar.
  split; intros;
  sep cancel (Alvarmapsto ret); eauto.
  intros.
  eapply cast_rv_tint8_tint32.
  sep get rv.
  unfold cast_eval. eauto.
  pure_auto.
  simpl; eauto.
  apply assign_type_match_true. auto.
  intros.
  exists init_lg.
  sep cancel p_local.
  sep pauto.

(*******If (ret ′ ==ₑ ′ OS_ERR_NOT_MUTEX_OWNER)*******)
  hoare forward.
  pure_auto.
  hoare unfold.
  destruct (Int.eq verr ($ OS_ERR_NOT_MUTEX_OWNER)) eqn: eq1;
  simpl val_inj in *; tryfalse.

  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexunlock_absimp_afterpost_rv1_end; eauto.
  pure_auto.
  eapply absinfer_eq.
  hoare forward.

  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  destruct (Int.eq verr ($ OS_ERR_NOT_MUTEX_OWNER)) eqn: eq1;
  simpl val_inj in *; destruct H40; tryfalse.
  (*  IF (ret ′ !=ₑ ′ 0){RETURN ′ EINVAL}ELSE {RETURN ′ 0} *)
  hoare forward.
  pure_auto.
  pure_auto.
  hoare unfold.
  destruct (Int.eq verr ($ 0)) eqn: eq2;
  simpl val_inj in *; change (Int.notbool Int.one) with Int.zero in *; tryfalse.

  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexunlock_absimp_afterpost_rv2_end; eauto.
  pure_auto.
  eapply absinfer_eq.
  hoare forward.

  hoare unfold.
  destruct (Int.eq verr ($ 0)) eqn: eq2;
  simpl val_inj in *; try change (Int.notbool Int.zero) with Int.one in *; destruct H51; tryfalse.

  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexunlock_absimp_afterpost_rv3_end; eauto.
  pure_auto.
  eapply absinfer_eq.
  hoare forward.
  get_hsat Hsat.
  destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
  Unshelve.
  exact O.
Qed.

Open Scope code_scope.

(* copy form OSMutexPend_pure_ext.v *)

Lemma get_ectr_sing:
  forall qid head (els1: list os_inv.EventCtr) osevent etbl petbl,
    els1 <> nil ->
    get_ectr (Vptr qid) head els1  = None ->
    get_ectr (Vptr qid) head (els1 ++ ((osevent,etbl,petbl) :: nil))  = Some (osevent,etbl,petbl) ->
    get_last_ptr els1 = Some (Vptr qid).
Proof.
induction els1.
intros.
tryfalse.
induction els1.
unfold get_last_ptr.
simpl.
intros.
destruct a.
destruct p.
destruct head;
try inverts H1.
destruct (beq_addrval qid a); try tryfalse.
destruct (V_OSEventListPtr v0 ); try tryfalse.
destruct v2; try tryfalse.
destruct (beq_addrval qid a0) eqn: eq1.
apply beq_addrval_eq in eq1.
subst. auto.
destruct (V_OSEventListPtr osevent); try tryfalse.
destruct v2; try tryfalse. 
intros.
destruct a.
destruct p.
assert (Hn: (a0 :: els1) <> nil) by pauto.
eapply (Mbox_common.get_last_prop) in Hn.
erewrite Hn.
destruct a0.
destruct p.
eapply IHels1; try pauto;
clear IHels0 IHels1 Hn;
simpl in *;
destruct head; try tryfalse; try auto;
destruct (beq_addrval qid a) eqn: eq1; try tryfalse;
destruct (V_OSEventListPtr v3); try auto; try tryfalse;
destruct (V_OSEventListPtr v0); try tryfalse;
destruct v6; try tryfalse;
destruct (beq_addrval qid a0) eqn: eq2; try tryfalse; try eauto.
Qed.

Lemma ecblist_p_decompose_new:
  forall l1 ll1 l2 ll2 head ecbls tcbls eptr curl ecbcurl,
    length l1 = length ll1 ->
    get_ectr (Vptr eptr) head l1  = None ->
    get_ectr (Vptr eptr) head (l1 ++ (curl :: nil))  = Some curl ->
    ECBList_P head Vnull
              (l1++ (curl :: nil) ++ l2) (ll1 ++ (ecbcurl :: nil) ++ ll2) ecbls tcbls ->
    exists ecbls1 ecbls2,
      ECBList_P head (Vptr eptr) l1 ll1 ecbls1 tcbls /\
      ECBList_P (Vptr eptr) Vnull ((curl :: nil) ++ l2) ((ecbcurl :: nil) ++ ll2) ecbls2 tcbls /\
      EcbMod.join ecbls1 ecbls2 ecbls /\ 
      (get_last_ptr l1 = None \/ get_last_ptr l1 = Some (Vptr eptr)).
Proof.
introv Hl Hgptr1 Hgptr2 Hep.
assert (Hl1: l1 = nil \/ l1 <> nil) by tauto.
destruct Hl1.
subst l1.
assert (ll1 = nil) by (eapply length_zero_nil; simpl in *; auto).
subst ll1.
simpl in *.
destruct curl.
destruct p.
mytac.
destruct (beq_addrval eptr x) eqn: eq1.
Focus 2.
destruct (V_OSEventListPtr v0); try tryfalse; destruct v2; try tryfalse.
apply beq_addrval_eq in eq1.
subst x.
do 2 eexists.
splits; try eauto.
exists eptr. splits; try auto.
do 3 eexists. splits; eauto.
apply EcbMod.map_join_comm.
apply EcbMod.map_join_emp.
lets Hsp: Mbox_common.ecblist_p_decompose Hl Hep.
simpl in *.
destruct curl.
destruct p.
mytac.
lets Hx2: get_ectr_sing H Hgptr1 Hgptr2.
destruct H3; rewrite H1 in Hx2; inverts Hx2.
do 2 eexists. splits; try eauto.
exists eptr. splits; try auto.
do 3 eexists. splits; eauto.
Qed.

Require Import part_pos_rgn_proof.
Lemma OSMutexUnlockProof:  
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api pthread_mutex_unlock
              (mutexunlock,(Tint32,Tptr pthread_mutex_t::nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api pthread_mutex_unlock
              (mutexunlock,(Tint32,Tptr pthread_mutex_t::nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api pthread_mutex_unlock = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  do 15 (destruct v'; try apply absabort_rule).
  rename v'10 into newv1.
  rename v'11 into newv2.
  rename v'12 into v'10.
  rename x into V_mux.
  rename v into V_pos.
  rename v0 into V_eid.
  rename v1 into V_ow.
  rename v2 into V_tp.
  rename v3 into V_curp.
  rename v4 into V_priocl.
  rename v5 into V_pevt.
  rename v6 into V_rcnt.
  rename v7 into V_eid0.
  rename v8 into V_ret.
  rename v9 into vr_temp_dom.
  rename v10 into vr_temp_num.
  rename v11 into vr_temp_dom'.
  rename v12 into vr_temp_num'.

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

  assert (Hptr: V_mux = Vnull \/ (exists p, V_mux = Vptr p)) by tauto.

  hoare forward.
  pure_auto.
  simpl.
  destruct Hptr; simpljoin; eauto.
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
  inverts H2.

  assert (Hv: V_pos = Vint32 (Int.mone) \/ V_pos <> Vint32 (Int.mone)) by tauto.
  destruct Hv.
  2: {
    hoare abscsq.
    apply noabs_oslinv.
    inversion Hptr.
    subst.
    eapply mutexunlock_absimp_muxok_abt_null; eauto.
    can_change_aop_solver.
    destruct H2. subst.
    eapply mutexunlock_absimp_muxerr_abt; eauto.
    inversion H; tryfalse.
    simpljoin.
    inverts H2. auto.
    can_change_aop_solver.
    apply absabort_rule.
  }
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexunlock_absimp_muxerr_cont; eauto.
  inversion H.
  left. inverts H2; subst; auto.
  right.
  simpljoin. inverts H2; eauto.
  can_change_aop_solver.
  subst V_pos.

(********)

  hoare forward.
  hoare forward.

  hoare unfold.
  rewrite Int.eq_true in *.
  simpl val_inj in H0; destruct H0; tryfalse.
  rewrite Int.eq_true.
  simpl val_inj.

  eapply hoare_disj_afalseP_r_pre.
  hoare forward;
  simpl;
  pure_auto.
  hoare_split_pure_all.
  change ($ -1) with Int.mone.
  assert (Hposv: Int.ltu Int.mone Int.zero = true \/ Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) Int.mone = true \/ Int.mone = $ (OS_USER_MAX_EVENTS / 3)).
  { clear -H1 Hrgn3 Hrgn4. int auto. }
  assert (Hret: V_ret = Vint32 (Int.repr EINVAL) \/ V_ret <> Vint32 (Int.repr EINVAL)) by tauto.
  destruct Hret.
  2:{ eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexunlock_absimp_poserr_abt; eauto.
        pure_auto.
        eapply absinfer_eq.
        apply absabort_rule.
    }
  subst.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexunlock_absimp_poserr0; eauto.
  pure_auto.
  eapply absinfer_eq.
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  change (Int.ltu ($ -1) ($ 0)) with false.
  rewrite Hchg.
  simpl val_inj.
  rewrite Hdiveq.
  change ($ -1) with Int.mone. 
  assert (Het: Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) Int.mone = true).
  { clear - Hrgn3 Hrgn4. int auto. }
  rewrite Het.
  assert (Hmf: Int.eq Int.mone ($ (OS_USER_MAX_EVENTS / 3)) = false).
  { clear - Hrgn3 Hrgn4. int auto. }
  rewrite Hmf.
  simpl val_inj.
  repeat (
  try change (Int.ltu Int.zero Int.one) with true;
  try change (Int.ltu Int.zero Int.zero) with false;
  simpl val_inj).

  hoare unfold.
  destruct H3; tryfalse.

  (* ---------------------------------------------- *)
  (* second branch for conditional on x *)
  hoare unfold.
  inverts H2.
  rename x into vmux.

  hoare_lifts_trms_pre Aop.
  assert (Hv00: ~(exists i, V_pos = Vint32 i) \/ exists i, V_pos = Vint32 i) by tauto.
  inversion Hv00 as [Hex | Hex].
  hoare unfold.
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply mutexunlock_absimp_mux_get_outtype_err_abt; eauto. 
  pure_auto.
  eapply absinfer_eq. 
  apply absabort_rule.

  lzh_hoare_if; try change (Int.eq ($ 1) ($ 0)) with false in *; tryfalse.

  (* second branch: encrit; pos = *mutex; excrit *)
  (* encrit *)
  hoare forward prim.
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_lifts_trms_pre ((Alvarmapsto os_code_defs.pos), (Alvarmapsto mutex)).
  unfold EvtInv.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.

  rename v'46 into pbls.
  assert (Hor: get pbls vmux = None \/ (exists posv, get pbls vmux = Some posv)).
  {
    destruct (get pbls vmux).
    right. eexists. eauto. 
    left. auto.
  }
  destruct Hor as [Hnone | Hsome].
  (* get pbls smadr = None *)
  hoare_lifts_trms_pre (Aop, pblsid).
  eapply abscsq_rule. 
  eapply noabs_oslinv.
  eapply mutexunlock_absimp_mux_get_none; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.
  (* exists posv, get pbls smadr = Some posv *)
  destruct Hsome as (posv & Hget).

  eapply backward_rule1.
  intros.
  eapply pos_list_split_frm. 
  sep cancel APosblkList.
  sep pauto.
  eauto.
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare forward.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_lvar with (v2:=Vint32 posv). 
  split.
  instantiate (3:=long).
  intros.
  sep cancel (Alvarmapsto os_code_defs.pos).
  eauto.
  intro.
  sep cancel (Alvarmapsto os_code_defs.pos).
  auto.
  2: { instantiate (1:=long). eapply eq_int. split; ((do 2 right); auto). }
  2: { sep pauto. sep cancel p_local. sep pauto. }
  unfold node.
  introv Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  eapply nth_val_nth_val'_some_eq in H14; eauto.
  rewrite <- H14.
  simpljoin.
  inverts H12.
  eapply sem_rv; eauto.
  sep get rv.

  hoare_lifts_trms_pre (Aop, pblsid).
  assert (Hv: V_pos <> Vint32 posv \/ V_pos = Vint32 posv) by tauto.
  destruct Hv.
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply mutexunlock_absimp_mux_get_pos_abt; eauto. 
  pure_auto. eapply absinfer_eq. apply absabort_rule.

  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply mutexunlock_absimp_sem_get_pos_ok; eauto.
  pure_auto.
  eapply absinfer_eq.
  rewrite <- H12.

  (* preparation for excrit *)
  eapply backward_rule1.
  introv Hsat.
   eapply pos_sllseg_merge
    with (vsem:=vmux) (posv:=posv) (pbls:=pbls).
  sep cancel pos_sllseg.
  sep cancel node.
  sep cancel pos_sllseg.
  sep pauto; eauto.
  eauto.

  hoare forward prim.
  sep cancel CoreCommuInv.
  sep cancel Aier.
  unfold EvtInv.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel p_local.
  unfold APosblkList.
  sep normal.
  sep eexists.
  sep cancel (Agvarmapsto GJB_pos_list).
  sep cancel pos_sllseg.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.
  auto.
  pure_auto.

  clear Hv00. 
  destruct Hex as (posv & Hvpos).
  subst.
  clear - tid posv Hrgn3 Hrgn4 Hdiveq Hchg.
  hoare_ex_intro.

  (* If (′ 0 >ₑ pos ′ ||ₑ pos ′ ≥ ebinop odiv ′ OS_USER_MAX_EVENTS ′ 3) *)
  hoare forward;
  try (rewrite Hchg);
  simpl;
  pure_auto.
  rewrite Hdiveq.
  hoare unfold.
  assert (Hposv_cond: Int.ltu posv Int.zero = true \/ Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = $ (OS_USER_MAX_EVENTS / 3)).
  {
    change ($ 0) with Int.zero in *.
    destruct (Int.ltu posv Int.zero) eqn:eq1;
    simpl in *; auto.
    destruct (Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) posv) eqn: eq2;
    simpl in *; auto.
    destruct (Int.eq posv ($ (OS_USER_MAX_EVENTS / 3))) eqn: eq3;
    simpl in *; try (apply inteqeq in eq3; subst; auto).
    repeat (try change (Int.ltu Int.zero Int.zero) with false in *; simpl in *).
    tryfalse.
  }
  assert (Hrv: V_ret = Vint32(Int.repr EINVAL) \/ V_ret <> Vint32(Int.repr EINVAL)) by tauto.
  destruct Hrv.
  2: { hoare abscsq.
         apply noabs_oslinv.
         eapply mutexunlock_absimp_poserr_abt; eauto.
         can_change_aop_solver.
         apply absabort_rule.
        }
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexunlock_absimp_poserr0; eauto.
  can_change_aop_solver.
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.

  hoare unfold.
  assert (Hposv_range: Int.ltu posv Int.zero = false /\ Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) posv = false /\ posv <> Int.repr (OS_USER_MAX_EVENTS / 3)).
  {
    change ($ 0) with Int.zero in *.
    rewrite Hdiveq in H.
    destruct (Int.ltu posv Int.zero) eqn:eq1;
    destruct (Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) posv) eqn: eq2;
    destruct (Int.eq posv ($ (OS_USER_MAX_EVENTS / 3))) eqn: eq3;
    try (apply inteqeq in eq3; subst);
    simpl in *; auto;
    repeat (try change (Int.ltu Int.zero Int.zero) with false in *; 
                  try change (Int.ltu Int.zero Int.one) with true in *; simpl in *);
    try destruct H;
    tryfalse.
    splits; try apply sem_lab.semacc_int_eq_false; auto.
  }
  clear H.
  destruct Hposv_range as (E1 & E2 & E3).

  (* first get p: ENTER_CRITICAL;ₛ p ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) pevent;ₛ EXIT_CRITICAL;ₛ*)
  hoare forward prim.
  hoare unfold.
  lets Hposv_neq: Int.eq_false E3.

  unfold EvtInv.
  hoare normal pre; hoare_ex_intro.
  hoare_assert_pure (length v'57 = (∘ (OS_USER_MAX_EVENTS / 3))).
  { get_hsat Hsat. sep_lifts_trms_in Hsat AMuxEIBs.
    eapply length_vll_apthrmux; eauto.  }
  eapply pure_split_rule'; introv Hlen_minfo.
  unfold AMuxEIBs.
  hoare normal pre; hoare_ex_intro.
  hoare unfold.
  hoare_lifts_trms_pre (Aop, APthreadMutex).
  destruct v'66.
  eapply backward_rule1.
  introv Hsat.
  eapply APthreadMutex_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned posv)).
  sep cancel APthreadMutex.
  eauto.
  rewrite Hlen_minfo.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.

  hoare unfold.
  hoare normal pre.
  hoare_lifts_trms_pre (Aop).
  hoare forward.
  eapply assign_rule_lvar.
  split; introv Hsat. sep cancel (Alvarmapsto p). eauto.
  sep auto.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  eapply new_array_type_vallist_match_split1 in H6; eauto.
  simpljoin; auto.
  eapply eq_vptr; eauto.
  intros. eexists. sep cancel p_local. simpl; eauto.

  assert (Hlemu: Int.unsigned posv <= Int.max_unsigned).
  { apply Int.unsigned_range_2. }
  lets Hmls: muxb_corr H1 H15 E1 Hlemu.
  destruct Hmls as (eo & ow & tp & rcnt & prot & pcp & wq & c & mc & Hget & Hmls).
  rename v'67 into mutvl.
  assert (Hcases:
           ((exists eid,
                eo = Valid_Addr eid /\ V_OSMUXINFOPevent mutvl = Some (Vptr eid) /\ eid <> vhold_addr) \/
              eo = Null /\ V_OSMUXINFOPevent mutvl = Some Vnull) \/
             eo = Holder /\ V_OSMUXINFOPevent mutvl = Some (Vptr vhold_addr) 
         ). 
  { clear -Hmls. intuition. }
  clear Hmls.

  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mutexunlock_absimp_posok_choice;
  try eauto.
  pure_auto.
  eapply absinfer_eq.

  hoare_lifts_trms_pre (Aop, absmutinfoid).
  destruct Hcases as [ Hok | Habt ].
  2: {
    destruct Habt as (Habt1 & Habt2).
    subst eo.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutexunlock_absimp_before_abt_hold; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
    apply absabort_rule.
  }

  assert (Hveid: ((exists eid,  eo = Valid_Addr eid /\ V_eid = Vptr eid) \/ eo = Null /\ V_eid = Vnull) 
        \/ ((exists eid, eo = Valid_Addr eid /\ V_eid <> Vptr eid) \/ eo = Null /\ V_eid <> Vnull)).
  {
    destruct Hok as [( eid & Heo & _) | (Heo & _)]; subst eo.
    assert (Hv: V_eid = Vptr eid \/ V_eid <> Vptr eid) by tauto.
    destruct Hv; [left | right]; left; eauto.
    assert (Hv: V_eid = Vnull \/ V_eid <> Vnull) by tauto.
    destruct Hv; [left | right]; right; eauto.
    }
  destruct Hveid as [Hveid | Habt].
  2: {
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexunlock_absimp_before_abt_out; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
        }
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutexunlock_absimp_before_ok; eauto.
   can_change_aop_solver.
   eapply absinfer_eq.
   (* EXIT_CRITICAL *)
   eapply backward_rule1.
   introv Hsat.
   eapply APthreadMutex_select_sn_ex_strong.
   exists v'38 (Z.to_nat (Int.unsigned posv)) v'66.
   exists mutvl.
   sep pauto.

   hoare forward prim.
   sep cancel Aier.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep pauto; eauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel APthreadMutex.
   sep cancel AMqEIBs.
   sep cancel p_local.
   sep cancel APthreadAttr.
   sep cancel AMuxCap.
   sep cancel CapabilityInv.
   eauto.
   auto.
   pure_auto.
  (* split the mutvl as mutvl = _ :: _ :: ... :: nil *)
  lets Hmut_vll: H6.
  rename H6 into Hmut_vl.
  eapply new_array_type_vallist_match_split1 in Hmut_vl; eauto.
  destruct Hmut_vl as (_ & _ & Hmut_vl).
  lets Hmut_vl_eq: struct_type_vallist_match_mutex_info_t_imp Hmut_vl.
  destruct Hmut_vl_eq as (vtp & vpro & vpcp & vwq & vcs & vow & vrcnt & vtsk & vp & vmc & Hmut_vl_eq & Hvp_ptr).
  subst mutvl.
  simpl nth_val'.
  unfold V_OSMUXINFOPevent in Hok.
  simpl nth_val in Hok.
  destruct Hok as [(eid & Heo & Hvp & Heid_neq) | (Heo & Hvp)];
  subst eo; inverts Hvp.
  (* p == NULL *)
  2: { destruct Hveid as [(ed & Hf & _) | (_ & Hveid)].
         clear -Hf; inverts Hf.
         subst V_eid.
        assert (Hrv: V_ret = Vint32 (Int.repr EINVAL) \/ V_ret <> Vint32 (Int.repr EINVAL)) by tauto.
        destruct Hrv.
        2: { hoare abscsq.
               apply noabs_oslinv.
               eapply mutexunlock_absimp_if_null_yes_abt; eauto.
               can_change_aop_solver.
               apply absabort_rule. }
        subst V_ret.
        (* If (p ′ ==ₑ NULL){RETURN ′ EINVAL};ₛ *)
        hoare forward.
        hoare unfold.
        hoare abscsq.
        apply noabs_oslinv.
        eapply mutexunlock_absimp_if_null_yes_end; eauto.
        can_change_aop_solver.
        hoare forward.
        eapply hoare_disj_afalseP_l_pre.
        hoare unfold.
        destruct H6; tryfalse.
    }
  (* p == Vptr eid *)
  destruct Hveid as [(vp & Hed & Hveid) | (Hf & _)].
  2: { clear -Hf; inverts Hf. }
  inverts Hed; subst V_eid.
  destruct vp as (vp_b & vp_i).
  (*p = Vptr (vp_b, vp_i) *)
  hoare forward.
  hoare unfold.
  tryfalse.
  instantiate (1:= Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexunlock_absimp_if_null_no; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  clear -E1 E2 E3 Hposv_neq Hlemu Hrgn3 Hrgn4 Hdiveq.
  (* 2 encrit *)
  hoare forward prim.
  unfold EvtInv.
  hoare normal pre; hoare_ex_intro.
  hoare_assert_pure (length v'37 = (∘ (OS_USER_MAX_EVENTS / 3))).
  { get_hsat Hsat. sep_lifts_trms_in Hsat AMuxEIBs.
    eapply length_vll_apthrmux; eauto.  }
  eapply pure_split_rule'; introv Hlen_minfo.
  unfold AMuxEIBs.
  hoare normal pre; hoare_ex_intro.
  hoare unfold.
  hoare_lifts_trms_pre (Aop, APthreadMutex).
  destruct v'46.
  eapply backward_rule1.
  introv Hsat.
  eapply APthreadMutex_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned posv)).
  sep cancel APthreadMutex.
  eauto.
  rewrite Hlen_minfo.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.

  hoare unfold.
  hoare_lifts_trms_pre (Aop).
  hoare forward.
  eapply assign_rule_lvar.
  split; introv Hsat. sep cancel (Alvarmapsto p). eauto.
  sep auto.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  eapply new_array_type_vallist_match_split1 in H4; eauto.
  simpljoin; auto.
  eapply eq_vptr; eauto.
  intros. eexists. sep cancel p_local. simpl; eauto.

  lets Hmls: muxb_corr H H15 E1 Hlemu.
  destruct Hmls as (eo & ow & tp & rcnt & prot & pcp & wq & c & mv & Hget & Hmls).
  rename v'47 into mutvl.
  assert (Hcases:
           ((exists eid,
                eo = Valid_Addr eid /\ V_OSMUXINFOPevent mutvl = Some (Vptr eid) /\ eid <> vhold_addr) \/
              eo = Null /\ V_OSMUXINFOPevent mutvl = Some Vnull) \/
             eo = Holder /\ V_OSMUXINFOPevent mutvl = Some (Vptr vhold_addr) 
         ). 
  { clear -Hmls. intuition. }
  clear Hmls.

  hoare_lifts_trms_pre (Aop, absmutinfoid).
  destruct Hcases as [ Hok | Habt ].
  2: {
    destruct Habt as (Habt1 & Habt2).
    subst eo.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutexunlock_absimp_before_abt_hold; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
    apply absabort_rule.
  }

  assert (Hveid: ((exists eid,  eo = Valid_Addr eid /\ V_eid0 = Vptr eid) \/ eo = Null /\ V_eid0 = Vnull) 
        \/ ((exists eid, eo = Valid_Addr eid /\ V_eid0 <> Vptr eid) \/ eo = Null /\ V_eid0 <> Vnull)).
  {
    destruct Hok as [( eid & Heo & _) | (Heo & _)]; subst eo.
    assert (Hv: V_eid0 = Vptr eid \/ V_eid0 <> Vptr eid) by tauto.
    destruct Hv; [left | right]; left; eauto.
    assert (Hv: V_eid0 = Vnull \/ V_eid0 <> Vnull) by tauto.
    destruct Hv; [left | right]; right; eauto.
    }
  destruct Hveid as [Hveid | Habt].
  2: {
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexunlock_absimp_before_abt_out; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
        }
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutexunlock_absimp_before_ok; eauto.
   can_change_aop_solver.
   eapply absinfer_eq.

  unfold AECBList.
  hoare normal pre. hoare unfold.
  destruct Hok as [Heid | Hnull].
  2:{ 
  destruct Hnull as (Heon & Hpe).
  subst.
  destruct Hveid; simpljoin; tryfalse.
  eapply nth_val_nth_val'_some_eq in Hpe.
  rewrite Hpe in *.

  hoare forward.
  hoare_split_pure_all.
  change (Int.notbool Int.one) with Int.zero in *.
  simpljoin; tryfalse.
  hoare_lifts_trms_pre (Aop, absmutinfoid).
   assert (Hrv: V_ret = Vint32 (Int.repr EINVAL) \/ V_ret <> Vint32 (Int.repr EINVAL)) by tauto.
   destruct Hrv.
   2: { eapply abscsq_rule.
          apply noabs_oslinv.
          eapply mutexunlock_absimp_if_null_yes2_abt; eauto.
          can_change_aop_solver.
          eapply absinfer_eq.
          apply absabort_rule. }
    subst V_ret.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutexunlock_absimp_if_null_yes2_end; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
     (* EXIT_CRITICAL *)
    eapply backward_rule1.
    introv Hsat.
    eapply APthreadMutex_select_sn_ex_strong.
    exists v'18 (Z.to_nat (Int.unsigned posv)) v'46.
    exists mutvl.
    sep pauto.

   hoare forward prim.
   sep cancel Aier.
   unfold EvtInv.
   unfold AMuxEIBs.
   unfold AECBList.
   sep pauto; eauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel APthreadMutex.
   sep cancel AMqEIBs.
   sep cancel p_local.
   sep cancel evsllseg.
   sep cancel AMuxCap.
   sep cancel APthreadAttr.
   sep cancel CapabilityInv.
   eauto.
   auto.
   pure_auto.
   hoare forward.
   eapply hoare_disj_afalseP_l_pre.
   hoare unfold.
   apply pfalse_rule.
   }

   destruct Heid as (eid & Hv0 & Hpid & Hne).
   subst.
   destruct Hveid; simpljoin; tryfalse.
   eapply nth_val_nth_val'_some_eq in Hpid.
   rewrite Hpid in *.
   inverts H19.
   rename x into eid.

  lets Hrmut: H1.
  unfold RH_ECBlk_EIBlk_Mux_P in H2.
  rename H2 into Heic.
  lets Hgete: Hget.
  eapply Heic in Hgete; eauto.
  destruct Hgete as (pip & o & wl & Hgete). 
  lets Fget_ectr: ECBList_P_get_ectr_some Hgete H14.
  destruct Fget_ectr as (Het & Hetbl & Hpetbl & Fget_ectr).
  hoare_lifts_trms_pre evsllseg.
  eapply backward_rule1.
  introv Hsat.
  eapply get_ectr_decompose in Hsat; eauto.
  hoare unfold.

  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  hoare unfold.
  inverts H30. (* V_OSPostEventGrp ... *)
  rename v'53 into lpetbl.
  rename v'55 into vp_b1.

  hoare forward.
  2:{ hoare unfold. change (Int.notbool Int.zero) with Int.one in *. destruct H2; tryfalse. }
  hoare unfold.
  (* muxowner ′ =ₑ 〈 char_t〉 ((efield (Pthread_Mutex ′ [pos ′]) pevent) → OSEventCnt &ₑ ′ OS_MUTEX_KEEP_LOWER_8) *)
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_lvar.
  split; introv Hsat;
  sep cancel (Alvarmapsto muxowner);
  eauto.
  { introv Hsat.
     eapply cast_rv_tint32_tint8.
     eapply bop_rv.
     sep_get_rv_array_struct'.
     rewrite Hdiveq; eauto.
     rewrite Hdiveq; eauto.
     eapply new_array_type_vallist_match_split1; eauto.
     auto.
     sep get rv.
     simpl; eauto.
     pure_auto.
     simpl; auto.
     simpl; eauto.
   }
  eapply eq_int; eauto.
  intros. sep pauto. instantiate (1:=init_lg). sep cancel p_local. sep pauto.
  (* end of assign owner *)
  change ((Int.notbool Int.zero)) with Int.one.
  eapply hoare_disj_afalseP_r_pre.
  hoare unfold.
  hoare_assert_pure (length v'48 = length v'50).
  { get_hsat Hsat. sep_lifts_trms_in Hsat (evsllseg v'37).
     eapply evsllseg_list_len_eq in Hsat; auto. }
  eapply pure_split_rule'; intro Heqlen.
  lets Hels: H14.
  eapply ecblist_p_decompose_new in Hels; eauto.
  destruct Hels as (els1 & els2 & Hels1 & Hels2 & Hej & Hlast_ptr).
  lets Hcp: Hels2.
  simpl in Hcp.
  (* add Hrpetbl *)
  destruct Hcp as (eid & Hed_eq & Hretbl & Hrpetbl & (ed & els' & eptr & Heptr_eq & Hejs & Hred & Hels2')).
  inverts Hed_eq.
  unfold V_OSEventListPtr in Heptr_eq; simpl in Heptr_eq. inverts Heptr_eq.
  lets Hgete': EcbMod.join_sig_get Hejs.
  eapply EcbMod.join_get_r in  Hgete'; eauto.
  unfold get in Hgete; unfold EcbMap in Hgete.
  rewrite Hgete in Hgete'. inverts Hgete'.
  destruct v'52; lets Hred': Hred; simpl in Hred'; tryfalse.
  destruct Hred' as (Hmatch & Hrecb).
    hoare_assert_pure (v = Vint32 i3 /\ v0 = x0).
   { get_hsat Hsat.
      unfold AEventData in Hsat.
      unfold V_OSEventPtr, V_OSEventCnt in *.
      simpl nth_val in *.
      sep split in Hsat. inverts H39. inverts H40. auto.
  }
  apply pure_split_rule'; introv Hed_eq.
  destruct Hed_eq as (Heq1 & Heq2); subst v; subst v0.
  assert (How_cases: (o = None /\ (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = $ OS_MUTEX_AVAILABLE) \/
                                                        (exists t op, o = Some (t, op) /\ (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = op)).
  { clear -Hmatch.
     funfold Hmatch.
     inverts H.
     destruct (Int.eq (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ OS_MUTEX_AVAILABLE)) eqn: eq1;
      [left | right].
     eapply inteqeq in eq1.
     split; auto. eapply H3 in eq1; mytac; auto.
     eapply sem_lab.semacc_int_eq_false in eq1.
     eapply H4 in eq1; mytac; eauto.
  }
  hoare_lifts_trms_pre (Aop, absecblsid, absmutinfoid).
  assert (Hvow: V_ow = Vint32 (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) \/ V_ow <> Vint32 (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) by tauto.
  destruct Hvow.
  2: { eapply abscsq_rule.
         apply noabs_oslinv.
         eapply mutexunlock_absimp_if_null_owner_no_abt; eauto.
         can_change_aop_solver.
         eapply absinfer_eq.
         apply absabort_rule. }
  subst V_ow.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexunlock_absimp_if_null_owner_no_end; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  lets How_eq: Htmp H35.
  rewrite How_eq.
  (* EXIT_CRITICAL;ₛ *)
  (* pre condition before excrt *)
  eapply backward_rule1. 
  introv Hsat.
  eapply APthreadMutex_select_sn_ex_strong.
  exists v'18 (Z.to_nat (Int.unsigned posv)) v'46.
  exists mutvl.
  sep pauto.
     hoare forward prim.
     sep cancel Aier.
     unfold EvtInv.
     unfold AMuxEIBs.
     unfold AECBList.
     sep pauto; eauto.
     trycancel.
     sep cancel ASemEIBs.
     sep cancel AMqEIBs.
     sep cancel p_local.
     sep cancel APthreadMutex.
     sep cancel AMuxCap.
     sep cancel APthreadAttr.
     sep cancel CapabilityInv.
     eapply evsllseg_app.
     sep cancel (evsllseg v'37).
     simpl evsllseg.
     unfold AEventNode.
     unfold AOSEvent.
     unfold node.
     unfold AOSEventTbl.
     sep pauto; eauto.
     sep cancel evsllseg.
     sep cancel Aarray.
     sep cancel Astruct.
     sep cancel AOSPostEventTbl.
     eauto.
     unfold V_OSEventListPtr; simpl ;auto.
     split; auto.
     struct_type_match_solver.
     auto.
     pure_auto.
     lets How_range: postintlemma3 i3.
     (* get type:  ENTER_CRITICAL;ₛ ty ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) mutex_type;ₛ EXIT_CRITICAL;ₛ *)

    (* new code about part_pos_rgn *)
     hoare_lifts_trms_pre (Aop, os_code_defs.pos, temp_dom, temp_num, Aisr, Aie, Ais, Acs, Aier, p_local, A_dom_lenv).
     eapply part_pos_rgn_proof.
     introv Hsat; sep auto.
     pure_auto.
     can_change_aop_solver.
     simpl; auto.
     simpl; auto.
     simpl;auto.
     hoare normal pre.
     eapply ex_intro_rule; intro vtemp_num.
     eapply ex_intro_rule; intro vtemp_dom.
     (* clear v'6 v'7; rename v'8 into v'6. *)
     (* end of new code *)

     clear -E1 E2 E3 Hposv_neq Hlemu How_range Hrgn3 Hrgn4 Hdiveq.
     (* ENTER_CRITICAL;ₛ *)
     hoare forward prim.
     hoare unfold.
     (* ty ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) mutex_type;ₛ *)
      unfold EvtInv.
      hoare normal pre; hoare_ex_intro.
      hoare_assert_pure (length v'36 = (∘ (OS_USER_MAX_EVENTS / 3))).
     { get_hsat Hsat. sep_lifts_trms_in Hsat AMuxEIBs.
       eapply length_vll_apthrmux; eauto.  }
     eapply pure_split_rule'; introv Hlen_minfo.
     unfold AMuxEIBs.
     hoare normal pre; hoare_ex_intro.
     hoare unfold.

     hoare_lifts_trms_pre (Aop, APthreadMutex).
     destruct v'45.
     eapply backward_rule1.
     introv Hsat.
     eapply APthreadMutex_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned posv)).
     sep cancel APthreadMutex.
     eauto.
     rewrite Hlen_minfo.
     eapply ge_ne_lt_rgn; eauto.
     rewrite Hdiveq.
     apply Intlt_false_is_Zge; auto.
     rewrite Hdiveq; eauto.

     hoare unfold.
     hoare_lifts_trms_pre (Aop).
     hoare forward.
     eapply assign_rule_lvar.
     split; introv Hsat. sep cancel (Alvarmapsto ty). eauto.
     sep auto.
     sep_get_rv_array_struct.
     rewrite Hdiveq; eauto.
     rewrite Hdiveq; eauto.
    eapply new_array_type_vallist_match_split1 in H6; eauto.
    simpljoin; auto.
    eapply eq_int; auto.
    intros. eexists. sep cancel p_local. simpl; eauto.

    lets Hmls: muxb_corr H1 H15 E1 Hlemu. 
    destruct Hmls as (eo & ow & tp & rcnt & prot & pcp & wq & c & mc & Hget & Hmls).
    rename v'46 into mutvl.
    destruct Hmls as (_ & _ & Hvtp_eq & _).
    unfold V_OSMUXINFOType in Hvtp_eq.
    apply nth_val_nth_val'_some_eq in Hvtp_eq.
    hoare_lifts_trms_pre (Aop, absmutinfoid).
  assert (Hvtp: V_tp = Vint32 tp \/ V_tp <> Vint32 tp) by tauto.
  destruct Hvtp.
  2: { eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexunlock_absimp_recurtp_before_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
       }
  subst V_tp.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexunlock_absimp_recurtp_before_ok; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
   (* EXIT_CRITICAL *)
   eapply backward_rule1.
   introv Hsat.
   eapply APthreadMutex_select_sn_ex_strong.
   exists v'17 (Z.to_nat (Int.unsigned posv)) v'45.
   exists mutvl.
   sep pauto.

   hoare forward prim.
   sep cancel Aier.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep pauto; eauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel AMqEIBs.
   sep cancel p_local.
   sep cancel APthreadMutex.
   sep cancel AMuxCap.
   sep cancel APthreadAttr.
   sep cancel CapabilityInv.
   eauto.
   auto.
   pure_auto.
  (* split the mutvl as mutvl = _ :: _ :: ... :: nil *)
  lets Hmut_vll: H6.
  rename H6 into Hmut_vl.
  eapply new_array_type_vallist_match_split1 in Hmut_vl; eauto.
  destruct Hmut_vl as (_ & _ & Hmut_vl).
  lets Hmut_vl_eq: struct_type_vallist_match_mutex_info_t_imp Hmut_vl.
  destruct Hmut_vl_eq as (vtp & vpro & vpcp & vwq & vcs & vow & vrcnt & vtsk & vp & vmc & Hmut_vl_eq & Hvp_ptr).
  subst mutvl.
  simpl nth_val' in Hvtp_eq. inverts Hvtp_eq.
  simpl nth_val'.

  clear -E1 E2 E3 Hposv_neq Hlemu How_range Hrgn3 Hrgn4 Hdiveq.
  hoare forward.
  pure_auto.
  instantiate (1:= 
  (
  (Afalse ** [| V_curp <> Vint32 (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) /\ V_priocl <>  V_curp |])
   \\//
   (Afalse ** [| (V_curp = Vint32 (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) \/ V_priocl =  V_curp) /\ V_rcnt <> Vint32 Int.zero  |]) 
   \\//
   ( <|| mutexunlock_if_rcnt_zero_neq
          (|Vint32 posv :: Vptr (vp_b1, Int.zero) :: V_rcnt :: V_ret :: nil|)
          ?? muxpost (Vint32 posv) V_pevt V_ret ||> **
     Aisr empisr **
    (EX er, Aier er) **
    Aie true **
    Ais nil **
    Acs nil **
    p_local OSLInv tid
    (logic_val (V$ 1)
     :: logic_val (V$ __EvLoc_normal)
        :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
    LV ty @ long |-> Vint32 tp **
    LV muxowner @ char_t |-> Vint32 (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
    LV p @ OS_EVENT ∗ |-> Vptr (vp_b1, Int.zero) **
    LV os_code_defs.pos @ long |-> Vint32 posv **
    LV mutex @ (long) ∗ |-> Vptr vmux **
    LV x @ char_t |-> (V$ 1) **
    LV pric @ long |-> V_priocl **
    LV cal @ char_t |-> v'7 **
    LV cpr @ char_t |-> V_curp **
    LV r @ long |-> V_rcnt **
    LV ret @ long |-> v'2 **
   LV temp_num @ char_t |-> vtemp_dom **
   LV temp_dom @ char_t |-> vtemp_num **
    A_dom_lenv
    ((mutex, (long) ∗)
     :: (x, char_t)
        :: (os_code_defs.pos, long)
           :: (ret, long)
              :: (muxowner, char_t)
                 :: (ty, long)
                    :: (r, long)
                       :: (cpr, char_t)
                          :: (cal, char_t) :: (pric, long) :: (p, OS_EVENT ∗)
                             :: (temp_dom, char_t) :: (temp_num, char_t) :: nil) **
   [| (V_curp = Vint32 (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) \/ V_priocl =  V_curp) /\ V_rcnt = Vint32 Int.zero  |]
   )
   )).
   hoare unfold.
   destruct (Int.eq tp ($ PTHREAD_MUTEX_RECURSIVE)) eqn:eq1;
   simpl in H; tryfalse.
   eapply inteqeq in eq1; subst.

   (* ENTER_CRITICAL;ₛ cpr ′ =ₑ OSTCBCur ′ → OSTCBPrio;ₛ EXIT_CRITICAL;ₛ *)
   hoare forward prim.
   hoare unfold.
   hoare forward.
   go.
   lets Hget_t:TCBListP_head_in_tcb H11.
   destruct Hget_t as (st & sus & Hget_t).
   lets Hget_t': Hget_t.
   eapply TcbMod.join_get_r in Hget_t'; eauto.
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutexunlock_absimp_ok; eauto.
   can_change_aop_solver.
   apply absinfer_eq.

   hoare_lifts_trms_pre (Aop, abstcblist, oscurt).
   assert (Hrv: V_curp = Vint32 i4 \/ V_curp <> Vint32 i4) by tauto.
   destruct Hrv.
        2: { eapply abscsq_rule.
               apply noabs_oslinv.
               eapply mutexunlock_absimp_curprio_before_abt; eauto.
               can_change_aop_solver.
               apply absinfer_eq.
               apply absabort_rule. }
   subst.
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutexunlock_absimp_curprio_before_ok; eauto.
   can_change_aop_solver.
   apply absinfer_eq.
    (* EXIT_CRITICAL;ₛ *) 
  hoare forward prim.
  sep cancel EvtInv.
  sep cancel Aier.
  unfold AOSTCBList.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  sep pauto; eauto.
  sep cancel OS_TCB_flag.
  sep cancel dllseg.
  sep cancel dllseg.
  sep cancel p_local.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  split; auto. go.
  auto.
  pure_auto.
  (* ENTER_CRITICAL;ₛ pric ′ =ₑ efield (Pthread_Mutex ′ [os_code_defs.pos ′]) prio_ceiling;ₛ EXIT_CRITICAL;ₛ *)
    rename H19 into Hcp_rgn.
    clear -E1 E2 E3 Hposv_neq Hlemu How_range Hcp_rgn Hrgn3 Hrgn4 Hdiveq.
    hoare forward prim.
    hoare unfold.

     unfold EvtInv.
     hoare normal pre; hoare_ex_intro.
     hoare_assert_pure (length v'35 = (∘ (OS_USER_MAX_EVENTS / 3))).
     { get_hsat Hsat. sep_lifts_trms_in Hsat AMuxEIBs.
       eapply length_vll_apthrmux; eauto.  }
     eapply pure_split_rule'; introv Hlen_minfo.
     unfold AMuxEIBs.
     hoare normal pre; hoare_ex_intro.
     hoare unfold.

     hoare_lifts_trms_pre (Aop, APthreadMutex).
     destruct v'44.
     eapply backward_rule1.
     introv Hsat.
     eapply APthreadMutex_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned posv)).
     sep cancel APthreadMutex.
     eauto.
     rewrite Hlen_minfo.
     eapply ge_ne_lt_rgn; eauto.
     rewrite Hdiveq.
     apply Intlt_false_is_Zge; auto.
     rewrite Hdiveq; eauto.

     hoare unfold.
     hoare_lifts_trms_pre (Aop).
     hoare forward.
     eapply assign_rule_lvar.
     split; introv Hsat. sep cancel (Alvarmapsto pric). eauto.
     sep auto.
     sep_get_rv_array_struct.
     rewrite Hdiveq; eauto.
     rewrite Hdiveq; eauto.
     eapply new_array_type_vallist_match_split1 in H6; eauto.
     simpljoin; auto.
     eapply eq_int; auto.
     intros. eexists. sep cancel p_local. simpl; eauto.

  lets Hmls: muxb_corr H1 H15 E1 Hlemu. 
  destruct Hmls as (eo & ow & tp' & rcnt & prot & pcp & wq & c & mc & Hget & Hmls).
  rename v'45 into mutvl.
  destruct Hmls as (_ & _ & _ & _ & Hvprc_eq & _).
  unfold V_OSMUXINFOPrio_ceiling in Hvprc_eq.
  apply nth_val_nth_val'_some_eq in Hvprc_eq.
  rewrite Hvprc_eq.
  hoare_lifts_trms_pre (Aop, absmutinfoid).
  assert (Hvprc: V_priocl = Vint32 pcp \/ V_priocl <> Vint32 pcp) by tauto.
  destruct Hvprc.
  2: { eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexunlock_absimp_priocl_before_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
       }
  subst.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexunlock_absimp_prioceil_before_ok; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
   (* EXIT_CRITICAL *)
   eapply backward_rule1.
   introv Hsat.
   eapply APthreadMutex_select_sn_ex_strong.
   exists v'15 (Z.to_nat (Int.unsigned posv)) v'44.
   exists mutvl.
   sep pauto.

   hoare forward prim.
   sep cancel Aier.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep pauto; eauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel AMqEIBs.
   sep cancel p_local.
   sep cancel APthreadMutex.
   sep cancel AMuxCap.
   sep cancel APthreadAttr.
   sep cancel CapabilityInv.
   eauto.
   auto.
   pure_auto.
  (* IF (muxowner ′ ==ₑ cpr ′ ||ₑ pric ′ ==ₑ cpr ′) *)
  hoare forward;
  try solve [try eapply mund_int_a2; auto; pure_auto].
  hoare_split_pure_all.
  assert(His_owner: Int.eq (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) i4 = true \/ Int.eq pcp i4 = true).
 { clear -H14.
    destruct (Int.eq (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) i4) eqn: eq1;
    destruct (Int.eq pcp i4) eqn: eq2;
    simpl in H14; tryfalse; auto.
    change (Int.ltu Int.zero Int.zero) with false in *.
    simpl in *.
    simpljoin; tryfalse.
 }
 clear H14.
 (* process post-condition *)
 Focus 3.
 get_hsat Hsat.
 eapply adisj_intro.
 destruct Hsat as [Hsat | Hsat]; [right | left].
 sep split in Hsat.
 exact Hsat.
 sep split in Hsat.
 exact Hsat.
  (* back to if case *)
 (* −− efield (Pthread_Mutex ′ [os_code_defs.pos ′]) recursive_cnt;ₛ *)
   clear -E1 E2 E3 Hposv_neq Hlemu His_owner Hrgn3 Hrgn4 Hdiveq.
   hoare forward prim.
   hoare unfold.

     unfold EvtInv.
     hoare normal pre; hoare_ex_intro.
     hoare_assert_pure (length v'34 = (∘ (OS_USER_MAX_EVENTS / 3))).
     { get_hsat Hsat. sep_lifts_trms_in Hsat AMuxEIBs.
       eapply length_vll_apthrmux; eauto.  }
     eapply pure_split_rule'; introv Hlen_minfo.
     unfold AMuxEIBs.
     hoare normal pre; hoare_ex_intro.
     hoare unfold.

     hoare_lifts_trms_pre (Aop, APthreadMutex).
     destruct v'43.
     eapply backward_rule1.
     introv Hsat.
     eapply APthreadMutex_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned posv)).
     sep cancel APthreadMutex.
     eauto.
     rewrite Hlen_minfo.
     eapply ge_ne_lt_rgn; eauto.
     rewrite Hdiveq.
     apply Intlt_false_is_Zge; auto.
     rewrite Hdiveq; eauto.

   hoare unfold.
   lets Hmls: muxb_corr H1 H15 E1 Hlemu. 
   destruct Hmls as (eo & ow & tp' & rcnt & prot & pcp' & wq & c & mc & Hget & Hmls).
   rename v'44 into mutvl.
   destruct Hmls as (_ & _ & _ & Hvcnt_eq & _).
   apply nth_val_nth_val'_some_eq in Hvcnt_eq.
   lets Hcp: H6.
   eapply new_array_type_vallist_match_split1 in Hcp; eauto.
   destruct Hcp as (Hsp1 & Hsp2 & Hsp).

   hoare forward.
   apply struct_type_vallist_match_elim_10 in Hsp.
   simpljoin. simpl. auto with zarith.
   eapply inline_bittblfunctions.nth_val'2nth_val; eauto.
   intros. eapply bop_rv.
   sep_get_rv_array_struct.
   rewrite Hdiveq; eauto.
   rewrite Hdiveq; eauto.
   sep get rv.
   rewrite Hvcnt_eq.
   simpl; eauto.
   pure_auto.
   simpl; eauto.

  hoare_lifts_trms_pre (Aop, absmutinfoid).
  eapply abscsq_rule. apply noabs_oslinv.
  eapply mutexunlock_absimp_ok. pure_auto.
  eapply absinfer_eq.
  eapply abscsq_rule. apply noabs_oslinv.
  eapply mutexunlock_absimp_recvcnt_decrement_oweq_end; eauto.
  clear -His_owner. destruct His_owner; [left | right]; eapply inteqeq; eauto.
  pure_auto.
  eapply absinfer_eq.

    eapply backward_rule1.
    introv Hsat.
    eapply APthreadMutex_select_sn_ex_strong.
    exists v'14 (Z.to_nat (Int.unsigned posv)) v'43.
    exists (update_nth_val 6 mutvl (Vint32 (rcnt -ᵢ $ 1))).
    sep pauto.

    rewrite <- H13.
    do 2 rewrite app_length. simpl; auto.
    eapply new_array_type_vallist_match_compose_struct; eauto.
    eapply struct_type_vallist_match_hold; eauto.
    apply struct_type_vallist_match_elim_10 in Hsp.
    simpljoin. simpl. auto with zarith.

   hoare forward prim.
   sep cancel Aier.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep pauto; eauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel AMqEIBs.
   sep cancel p_local.
   sep cancel APthreadMutex.
   sep cancel AMuxCap.
   sep cancel APthreadAttr.
   sep cancel CapabilityInv.
   eauto.
   eapply eibref_distinct_mux_setrecurv_preserve; eauto.
   eapply Q_ECB_P_setrecurv_preserve_mux; eauto.
   eapply MUX_ECB_P_setrecurv_preserve_mux; eauto.
   eapply SEM_ECB_P_setrecurv_preserve_mux; eauto.
   eapply RH_ECBlk_EIBlk_Mux_P_set_recurcnt; eauto.
   eapply MuxCapArray_P_hold; eauto.
   eapply EIBMAarray_P_recurcnt_for_update_to_recurcnt'; eauto.
   apply Int.unsigned_range_2.
   unfolds. eapply inline_bittblfunctions.nth_val'2nth_val; eauto.
   auto.
   pure_auto.
   (* ENTER_CRITICAL;ₛ r ′ =ₑ efield (Pthread_Mutex ′ [os_code_defs.pos ′]) recursive_cnt;ₛ EXIT_CRITICAL;ₛ *)
    clear -E1 E2 E3 Hposv_neq Hlemu His_owner Hrgn3 Hrgn4 Hdiveq.
    hoare forward prim.
    hoare unfold.

     unfold EvtInv.
     hoare normal pre; hoare_ex_intro.
     hoare_assert_pure (length v'34 = (∘ (OS_USER_MAX_EVENTS / 3))).
     { get_hsat Hsat. sep_lifts_trms_in Hsat AMuxEIBs.
       eapply length_vll_apthrmux; eauto.  }
     eapply pure_split_rule'; introv Hlen_minfo.
     unfold AMuxEIBs.
     hoare normal pre; hoare_ex_intro.
     hoare unfold.

     hoare_lifts_trms_pre (Aop, APthreadMutex).
     destruct v'43.
     eapply backward_rule1.
     introv Hsat.
     eapply APthreadMutex_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned posv)).
     sep cancel APthreadMutex.
     eauto.
     rewrite Hlen_minfo.
     eapply ge_ne_lt_rgn; eauto.
     rewrite Hdiveq.
     apply Intlt_false_is_Zge; auto.
     rewrite Hdiveq; eauto.

     hoare unfold.
     rewrite Int.repr_unsigned.
     hoare_lifts_trms_pre (Aop).
     hoare forward.
     eapply assign_rule_lvar.
     split; introv Hsat. sep cancel (Alvarmapsto r). eauto.
     sep auto.
     sep_get_rv_array_struct.
     rewrite Hdiveq; eauto.
     rewrite Hdiveq; eauto.
    eapply new_array_type_vallist_match_split1 in H6; eauto.
    simpljoin; auto.
    eapply eq_int; auto.
    intros. eexists. sep cancel p_local. simpl; eauto.

  lets Hmls: muxb_corr H1 H15 E1 Hlemu. 
  destruct Hmls as (eo & ow & tp' & rcnt & prot & pcp' & wq & c & mc & Hget & Hmls).
  rename v'44 into mutvl.
   destruct Hmls as (_ & _ & _ & Hvcnt_eq & _).
   apply nth_val_nth_val'_some_eq in Hvcnt_eq.
   lets Hcp: H6.
   eapply new_array_type_vallist_match_split1 in Hcp; eauto.
   destruct Hcp as (Hsp1 & Hsp2 & Hsp).
   rewrite Hvcnt_eq.
   hoare_lifts_trms_pre (Aop, absmutinfoid).
  assert (Hvcnt: V_rcnt = Vint32 rcnt \/ V_rcnt <> Vint32 rcnt) by tauto.
  destruct Hvcnt.
  2: { eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexunlock_absimp_get_recurcnt_before_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
       }
  subst.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexunlock_absimp_get_recurcnt_before_ok; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
   (* EXIT_CRITICAL *)
   eapply backward_rule1.
   introv Hsat.
   eapply APthreadMutex_select_sn_ex_strong.
   exists v'14 (Z.to_nat (Int.unsigned posv)) v'43.
   exists mutvl.
   sep pauto.

   hoare forward prim.
   sep cancel Aier.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep pauto; eauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel AMqEIBs.
   sep cancel p_local.
   sep cancel APthreadMutex.
   sep cancel AMuxCap.
   sep cancel APthreadAttr.
   sep cancel CapabilityInv.
   eauto.
   auto.
   pure_auto.
   (* If (r ′ !=ₑ ′ 0){RETURN ′ 0} *)
   clear -E1 E2 E3 Hposv_neq Hlemu His_owner.
   hoare forward.
   pure_auto.
   pure_auto.
   (* process post-condition *)
   Focus 2.
   get_hsat Hsat.
   eapply adisj_intro.
   destruct Hsat as [Hsat | Hsat]; [left | right].
   sep split in Hsat.
   exact Hsat.
   change ($ 0) with Int.zero in *.
   sep_lifts_trms_in Hsat val_inj.
   eapply sep_pure_split in Hsat; destruct Hsat as (Hif & Hsat).
   destruct (Int.eq rcnt Int.zero) eqn: eq1; simpl in Hif;
   try (change (Int.notbool Int.zero) with Int.one in Hif; destruct Hif; tryfalse).
   eapply inteqeq in eq1; subst.
   sep auto.
   split; auto.
   clear -His_owner. destruct His_owner; [left | right]; eapply inteqeq in H; subst; eauto.
   (* back to if process *)
   hoare unfold.
   change ($ 0) with Int.zero in *.
   destruct (Int.eq rcnt Int.zero) eqn: eq1; simpl in *;
   try change (Int.notbool Int.one) with Int.zero in *; tryfalse.
   lets Hneq: semacc_int_eq_false eq1.
   hoare_lifts_trms_pre (Aop).
   eapply abscsq_rule. eapply noabs_oslinv.
  eapply mutexunlock_absimp_ok.
  pure_auto. unfold CurTid. go. 
  eapply absinfer_eq. 
  assert (Hv: V_ret = Vint32 Int.zero \/ V_ret <> Vint32 Int.zero) by tauto.
  destruct Hv.
  2: { eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexunlock_absimp_if_rcnt_zero_neq_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
       }
  subst.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexunlock_absimp_if_rcnt_zero_neq_end; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  hoare forward.
  simpl sat in *.
  tryfalse.
  (* not owner *)
  hoare_split_pure_all.
  assert(Hnot_owner: Int.eq (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) i4 = false /\ Int.eq pcp i4 = false).
 { clear -H14.
    destruct (Int.eq (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) i4) eqn: eq1;
    destruct (Int.eq pcp i4) eqn: eq2;
    simpl in *;
    try change (Int.ltu Int.zero Int.one) with true in *;
    simpl in *;
    destruct H14;
    tryfalse; auto.
 }
 clear H14.
 destruct Hnot_owner as (Hneq1 & Hneq2).
 eapply semacc_int_eq_false in Hneq1, Hneq2.
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule. eapply noabs_oslinv.
  eapply mutexunlock_absimp_ok2.
  pure_auto.
  eapply absinfer_eq.
  assert (Hv: V_ret = V$ EPERM \/ V_ret <> V$ EPERM) by tauto.
  destruct Hv.
  2: { eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexunlock_if_ow_curp_neq_abt; eauto.
        introv Hf; inverts Hf; tryfalse.
        introv Hf; inverts Hf; tryfalse.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
       }
  subst.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexunlock_if_ow_curp_neq_end; eauto.
  introv Hf; inverts Hf; tryfalse.
  introv Hf; inverts Hf; tryfalse.
  can_change_aop_solver.
  eapply absinfer_eq.
  hoare forward.
  (* end of if tp = PTHREAD_MUTEX_RECURSIVE *)
  hoare forward.
  hoare unfold.
  hoare forward.
  hoare forward.
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule. eapply noabs_oslinv.
  eapply mutexunlock_absimp_ok2.
  pure_auto.
  eapply absinfer_eq.
  hoare_split_pure_all.
  eapply backward_rule1;
  [idtac | eapply Beforepostpartproof; eauto].
  introv Hsat.
  sep cancel Aier.
  sep pauto.
  rewrite Hdiveq; eauto.
  hoare unfold.
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule. eapply noabs_oslinv.
  eapply mutexunlock_absimp_ok2.
  pure_auto.
  eapply absinfer_eq.
  eapply backward_rule1;
  [idtac | eapply Beforepostpartproof; eauto].
  introv Hsat.
  sep cancel Aier.
  sep pauto.
  rewrite Hdiveq; eauto.

  Unshelve.
  exact Afalse.
  exact O. exact O. exact O. exact O. exact O. exact O. exact O.
Qed.


Require Import os_code_defs.
Require Import os_mutex_cap.
Require Import abs_op.
Require Import ifun_spec.
Require Import sem_common.

Require Import Maps.
Require Import include_frm.
Require Import ucos_frmaop.
Require Import abs_step.
Require Import init_spec.

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
Require Import Aarray_new_common.

Require Import pos_list_common.
Require Import OSTimeTickPure.
Require Import ev_aux_code.
Require Import gjb_common.
Require Import gjb_mutex_common.
Require Import hoare_forward.
Require Import  ucos_common.
Require Import os_ucos_h.
Require Import tv_match.
Require Import pure.
Require Import seplog_trm_tacs.
Require Import join_lib.
Require Import evauxvar_lemmas.
Require Import evaux_pure.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Open Scope list_scope.
Open Scope Z_scope.
Open Scope code_scope.

Lemma mutextimedlock_absimp_muxerr_abt:
  forall s sch V_mux V_pos P,
    (V_mux = Vnull \/
           exists a,
             V_mux = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)) ->  
    V_pos <> Vint32 (Int.mone) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutextimedlock_muxerr (| V_mux :: V_pos :: nil|) ??
               mutextimedlock_mutex_pos(| V_mux :: V_pos :: nil|)) ;; s ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
intros.
eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_muxerr_cons:
  forall s sch V_mux V_pos P,
    (V_mux = Vnull \/
           exists a,
             V_mux = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)) ->  
    V_pos = Vint32 (Int.mone) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutextimedlock_muxerr (| V_mux :: V_pos :: nil|) ??
               mutextimedlock_mutex_pos(| V_mux :: V_pos :: nil|)) ;; s ||>  ** P)
      (<|| s ||> ** P).
Proof.
intros.
eapply absinfer_trans; try (eapply absinfer_seq_end; eauto).
eapply absinfer_seq; eauto.
infer_solver 0%nat.
Qed.

Lemma mutextimedlock_absimp_muxtex_pos_none_abt:
  forall s sch mux V_pos pbls P,
    cmpaddr Clt userAddrStart mux = true ->
    cmpaddr Cle mux userAddrEnd = true ->
    get pbls mux = None -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutextimedlock_muxerr (| Vptr mux :: V_pos :: nil|) ??
               mutextimedlock_mutex_pos(| Vptr mux :: V_pos :: nil|)) ;; s ||>  ** Hpbls pbls ** P)
      (<|| ABORT ||> ** Hpbls pbls ** P).
Proof.
intros.
assert (Hc: can_change_aop (Hpbls pbls ** P)) by can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_trans; try( eapply absinfer_choice2; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_muxtex_pos_ex_abt:
  forall s sch mux V_pos pbls  posv P,
    cmpaddr Clt userAddrStart mux = true ->
    cmpaddr Cle mux userAddrEnd = true ->
    get pbls mux = Some posv -> 
    V_pos <> Vint32 posv ->
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutextimedlock_muxerr (| Vptr mux :: V_pos :: nil|) ??
               mutextimedlock_mutex_pos(| Vptr mux :: V_pos :: nil|)) ;; s ||>  ** Hpbls pbls ** P)
      (<|| ABORT ||> ** Hpbls pbls ** P).
Proof.
intros.
assert (Hc: can_change_aop (Hpbls pbls ** P)) by can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_trans; try( eapply absinfer_choice2; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver.
left; eauto.
Qed.

Lemma mutextimedlock_absimp_muxtex_pos_type_abt:
  forall s sch mux V_pos pbls P,
    cmpaddr Clt userAddrStart mux = true ->
    cmpaddr Cle mux userAddrEnd = true ->
    ~(exists posv, V_pos = Vint32 posv) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutextimedlock_muxerr (| Vptr mux :: V_pos :: nil|) ??
               mutextimedlock_mutex_pos(| Vptr mux :: V_pos :: nil|)) ;; s ||>  ** Hpbls pbls ** P)
      (<|| ABORT ||> ** Hpbls pbls ** P).
Proof.
intros.
assert (Hor: get pbls mux = None \/ (exists posv, get pbls mux = Some posv)).
  {
    destruct (get pbls mux).
    right. eexists. eauto. 
    left. auto.
  }
  destruct Hor as [Hnone | Hsome].
  eapply mutextimedlock_absimp_muxtex_pos_none_abt;eauto.
  destruct Hsome.
  eapply mutextimedlock_absimp_muxtex_pos_ex_abt; eauto.
Qed.

Lemma mutextimedlock_absimp_muxtex_pos_cons:
  forall s sch mux V_pos pbls  posv P,
    cmpaddr Clt userAddrStart mux = true ->
    cmpaddr Cle mux userAddrEnd = true ->
    get pbls mux = Some posv -> 
    V_pos = Vint32 posv ->
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutextimedlock_muxerr (| Vptr mux :: V_pos :: nil|) ??
               mutextimedlock_mutex_pos(| Vptr mux :: V_pos :: nil|)) ;; s ||>  ** Hpbls pbls ** P)
      (<|| s ||> ** Hpbls pbls ** P).
Proof.
intros.
assert (Hc: can_change_aop (Hpbls pbls ** P)) by can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq_end; eauto).
instantiate (1:= None).
eapply absinfer_seq; eauto.
infer_solver 1%nat.
repeat eexists; eauto.
eapply absdata_elim.
instantiate (3:= mutextimedlock_mutex_pos (|Vptr mux :: V_pos :: nil|)).
instantiate (3:= s0).
sep pauto.  
left; eauto.
Qed.

Lemma mutextimedlock_absimp_poserr_abt:
  forall posv V_ret s P sch,
    (Int.ltu posv Int.zero = true \/
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) ->
      V_ret <> (Vint32 (Int.repr EINVAL)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||   mutextimedlock_poserr (|Vint32 posv :: V_ret :: nil|) ?? s ||> ** P)
      (<|| ABORT ||> ** P). 
Proof.
intros.
eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_poserr:
  forall posv V_ret s P sch,
    (Int.ltu posv Int.zero = true \/
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) ->
      V_ret = (Vint32 (Int.repr EINVAL)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||   mutextimedlock_poserr (|Vint32 posv :: V_ret :: nil|) ?? s ||> ** P)
      (<|| END Some (Vint32 (Int.repr EINVAL)) ||> ** P). 
Proof.
infer_solver 0%nat.
Qed.

Lemma mutextimedlock_absimp_timeout_abt:
  forall tmv V_ret s1 s2 P sch,
    (Int.eq tmv Int.zero = true \/ Int.ltu (Int.repr 65535) tmv = true) ->
      V_ret <> (Vint32 (Int.repr EINVAL)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||   s1 ?? mutextimedlock_timeout_err (|Vint32 tmv :: V_ret :: nil|) ?? s2 ||> ** P)
      (<|| ABORT ||> ** P). 
Proof.
intros.
eapply absinfer_trans; try( eapply absinfer_choice2; eauto).
eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_timeout_abt_new:
  forall tmv V_ret s2 P sch,
    (Int.eq tmv Int.zero = true \/ Int.ltu (Int.repr 65535) tmv = true) ->
      V_ret <> (Vint32 (Int.repr EINVAL)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||   mutextimedlock_timeout_err (|Vint32 tmv :: V_ret :: nil|) ?? s2 ||> ** P)
      (<|| ABORT ||> ** P). 
Proof.
intros.
(*eapply absinfer_trans; try( eapply absinfer_choice2; eauto).*)
eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_timeout_err:
  forall tmv V_ret s1 s2 P sch,
    (Int.eq tmv Int.zero = true \/ Int.ltu (Int.repr 65535) tmv = true) ->
      V_ret = (Vint32 (Int.repr EINVAL)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||   s1 ?? mutextimedlock_timeout_err (|Vint32 tmv :: V_ret :: nil|) ?? s2 ||> ** P)
      (<|| END Some (Vint32 (Int.repr EINVAL)) ||> ** P). 
Proof.
infer_solver 1%nat.
Qed.

Lemma mutextimedlock_absimp_timeout_err_new:
  forall tmv V_ret s2 P sch,
    (Int.eq tmv Int.zero = true \/ Int.ltu (Int.repr 65535) tmv = true) ->
      V_ret = (Vint32 (Int.repr EINVAL)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_timeout_err (|Vint32 tmv :: V_ret :: nil|) ?? s2 ||> ** P)
      (<|| END Some (Vint32 (Int.repr EINVAL)) ||> ** P). 
Proof.
infer_solver 0%nat.
Qed.

Lemma mutextimedlock_absimp_ecb_ptr_hold_abt:
  forall posv V_eid s1 s2 P sch minfob o x n pro pcp w c mc,
    get minfob posv = Some (Holder, o, x, n, pro, pcp, w, c, mc) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  s1 ?? (mutextimedlock_ecb_ptr (|Vint32 posv :: V_eid :: nil|) ;; s2) ||> ** HMuxInfo minfob ** P)
      (<|| ABORT ||> ** HMuxInfo minfob ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo minfob ** P)) by can_change_aop_solver.
eapply absinfer_trans; try( eapply absinfer_choice2; eauto).
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
Unshelve.
exact None.
Qed.

Lemma mutextimedlock_absimp_ecb_ptr_hold_abt_new:
  forall posv V_eid s2 P sch minfob o x n pro pcp w c mc,
    get minfob posv = Some (Holder, o, x, n, pro, pcp, w, c, mc) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  (mutextimedlock_ecb_ptr (|Vint32 posv :: V_eid :: nil|) ;; s2) ||> ** HMuxInfo minfob ** P)
      (<|| ABORT ||> ** HMuxInfo minfob ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo minfob ** P)) by can_change_aop_solver.
(*eapply absinfer_trans; try( eapply absinfer_choice2; eauto).*)
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
Unshelve.
exact None.
Qed.

Lemma mutextimedlock_absimp_ecb_ptr_abt:
  forall posv V_eid s1 s2 P sch minfob o x n pro pcp w c mc eo,
    get minfob posv = Some (eo, o, x, n, pro, pcp, w, c, mc) ->
    ((exists eid, eo = (Valid_Addr eid) /\ V_eid <> Vptr eid) \/ eo = Null /\ V_eid <> Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||  s1 ?? (mutextimedlock_ecb_ptr (|Vint32 posv :: V_eid :: nil|) ;; s2) ||> ** HMuxInfo minfob ** P)
      (<|| ABORT ||> ** HMuxInfo minfob ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo minfob ** P)) by can_change_aop_solver.
eapply absinfer_trans; try( eapply absinfer_choice2; eauto).
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
Unshelve.
exact None.
Qed.

Lemma mutextimedlock_absimp_ecb_ptr_abt_new:
  forall posv V_eid s2 P sch minfob o x n pro pcp w c mc eo,
    get minfob posv = Some (eo, o, x, n, pro, pcp, w, c, mc) ->
    ((exists eid, eo = (Valid_Addr eid) /\ V_eid <> Vptr eid) \/ eo = Null /\ V_eid <> Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||  (mutextimedlock_ecb_ptr (|Vint32 posv :: V_eid :: nil|) ;; s2) ||> ** HMuxInfo minfob ** P)
      (<|| ABORT ||> ** HMuxInfo minfob ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo minfob ** P)) by can_change_aop_solver.
(*eapply absinfer_trans; try( eapply absinfer_choice2; eauto).*)
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
Unshelve.
exact None.
Qed.

Lemma mutextimedlock_absimp_ecb_ptr:
  forall posv V_eid s1 s2 P sch minfob o x n pro pcp w c mc eo,
    get minfob posv = Some (eo, o, x, n, pro, pcp, w, c, mc) ->
    ((exists eid, eo = (Valid_Addr eid) /\ V_eid = Vptr eid) \/ eo = Null /\ V_eid = Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||  s1 ?? (mutextimedlock_ecb_ptr (|Vint32 posv :: V_eid :: nil|) ;; s2) ||> ** HMuxInfo minfob ** P)
      (<|| s2 ||> ** HMuxInfo minfob ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo minfob ** P)) by can_change_aop_solver.
infer_solver 1%nat.
Unshelve.
exact None.
Qed.

Lemma mutextimedlock_absimp_ecb_ptr_new:
  forall posv V_eid s2 P sch minfob o x n pro pcp w c mc eo,
    get minfob posv = Some (eo, o, x, n, pro, pcp, w, c, mc) ->
    ((exists eid, eo = (Valid_Addr eid) /\ V_eid = Vptr eid) \/ eo = Null /\ V_eid = Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||  (mutextimedlock_ecb_ptr (|Vint32 posv :: V_eid :: nil|) ;; s2) ||> ** HMuxInfo minfob ** P)
      (<|| s2 ||> ** HMuxInfo minfob ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo minfob ** P)) by can_change_aop_solver.
infer_solver 0%nat.
Unshelve.
exact None.
Qed.

Lemma mutextimedlock_absimp_ecb_ptr_hold_abt':
  forall posv V_eid s P sch minfob o x n pro pcp w c mc,
    get minfob posv = Some (Holder, o, x, n, pro, pcp, w, c, mc) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_ecb_ptr (|Vint32 posv :: V_eid :: nil|) ;; s ||> ** HMuxInfo minfob ** P)
      (<|| ABORT ||> ** HMuxInfo minfob ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo minfob ** P)) by can_change_aop_solver.
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
Unshelve.
exact None.
Qed.

Lemma mutextimedlock_absimp_ecb_ptr_abt':
  forall posv V_eid s P sch minfob o x n pro pcp w c mc eo,
    get minfob posv = Some (eo, o, x, n, pro, pcp, w, c, mc) ->
    ((exists eid, eo = (Valid_Addr eid) /\ V_eid <> Vptr eid) \/ eo = Null /\ V_eid <> Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||  (mutextimedlock_ecb_ptr (|Vint32 posv :: V_eid :: nil|) ;; s) ||> ** HMuxInfo minfob ** P)
      (<|| ABORT ||> ** HMuxInfo minfob ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo minfob ** P)) by can_change_aop_solver.
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
Unshelve.
exact None.
Qed.

Lemma mutextimedlock_absimp_ecb_ptr':
  forall posv V_eid s P sch minfob o x n pro pcp w c mc eo,
    get minfob posv = Some (eo, o, x, n, pro, pcp, w, c, mc) ->
    ((exists eid, eo = (Valid_Addr eid) /\ V_eid = Vptr eid) \/ eo = Null /\ V_eid = Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||  (mutextimedlock_ecb_ptr (|Vint32 posv :: V_eid :: nil|) ;; s) ||> ** HMuxInfo minfob ** P)
      (<|| s ||> ** HMuxInfo minfob ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo minfob ** P)) by can_change_aop_solver.
infer_solver 0%nat.
Unshelve.
exact None.
Qed.

Lemma mutextimedlock_absimp_ecb_ptr_hold_abt'':
  forall posv V_eid s1 s2 s3 P sch minfob o x n pro pcp w c mc,
    get minfob posv = Some (Holder, o, x, n, pro, pcp, w, c, mc) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  s1 ?? s2 ?? (mutextimedlock_ecb_ptr (|Vint32 posv :: V_eid :: nil|) ;; s3) ||> ** HMuxInfo minfob ** P)
      (<|| ABORT ||> ** HMuxInfo minfob ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo minfob ** P)) by can_change_aop_solver.
do 2 (eapply absinfer_trans; try( eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
Unshelve.
exact None.
Qed.

Lemma mutextimedlock_absimp_ecb_ptr_hold_abt''_new:
  forall posv V_eid s2 s3 P sch minfob o x n pro pcp w c mc,
    get minfob posv = Some (Holder, o, x, n, pro, pcp, w, c, mc) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| s2 ?? (mutextimedlock_ecb_ptr (|Vint32 posv :: V_eid :: nil|) ;; s3) ||> ** HMuxInfo minfob ** P)
      (<|| ABORT ||> ** HMuxInfo minfob ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo minfob ** P)) by can_change_aop_solver.
(*do 2 (eapply absinfer_trans; try( eapply absinfer_choice2; eauto)).*)
eapply absinfer_trans; try( eapply absinfer_choice2; eauto).
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
Unshelve.
exact None.
Qed.

Lemma mutextimedlock_absimp_ecb_ptr_abt'':
  forall posv V_eid s1 s2 s3 P sch minfob o x n pro pcp w c mc eo,
    get minfob posv = Some (eo, o, x, n, pro, pcp, w, c, mc) ->
    ((exists eid, eo = (Valid_Addr eid) /\ V_eid <> Vptr eid) \/ eo = Null /\ V_eid <> Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||  s1 ?? s2 ?? (mutextimedlock_ecb_ptr (|Vint32 posv :: V_eid :: nil|) ;; s3) ||> ** HMuxInfo minfob ** P)
      (<|| ABORT ||> ** HMuxInfo minfob ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo minfob ** P)) by can_change_aop_solver.
do 2 (eapply absinfer_trans; try( eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
Unshelve.
exact None.
Qed.

Lemma mutextimedlock_absimp_ecb_ptr_abt''_new:
  forall posv V_eid s2 s3 P sch minfob o x n pro pcp w c mc eo,
    get minfob posv = Some (eo, o, x, n, pro, pcp, w, c, mc) ->
    ((exists eid, eo = (Valid_Addr eid) /\ V_eid <> Vptr eid) \/ eo = Null /\ V_eid <> Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| s2 ?? (mutextimedlock_ecb_ptr (|Vint32 posv :: V_eid :: nil|) ;; s3) ||> ** HMuxInfo minfob ** P)
      (<|| ABORT ||> ** HMuxInfo minfob ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo minfob ** P)) by can_change_aop_solver.
eapply absinfer_trans; try( eapply absinfer_choice2; eauto).
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
Unshelve.
exact None.
Qed.

Lemma mutextimedlock_absimp_ecb_ptr'':
  forall posv V_eid s1 s2 s3 P sch minfob o x n pro pcp w c mc eo,
    get minfob posv = Some (eo, o, x, n, pro, pcp, w, c, mc) ->
    ((exists eid, eo = (Valid_Addr eid) /\ V_eid = Vptr eid) \/ eo = Null /\ V_eid = Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||  s1 ?? s2 ?? (mutextimedlock_ecb_ptr (|Vint32 posv :: V_eid :: nil|) ;; s3) ||> ** HMuxInfo minfob ** P)
      (<|| s3 ||> ** HMuxInfo minfob ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo minfob ** P)) by can_change_aop_solver.
infer_solver 2%nat.
Unshelve.
exact None.
Qed.

Lemma mutextimedlock_absimp_ecb_ptr''_new:
  forall posv V_eid s2 s3 P sch minfob o x n pro pcp w c mc eo,
    get minfob posv = Some (eo, o, x, n, pro, pcp, w, c, mc) ->
    ((exists eid, eo = (Valid_Addr eid) /\ V_eid = Vptr eid) \/ eo = Null /\ V_eid = Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| s2 ?? (mutextimedlock_ecb_ptr (|Vint32 posv :: V_eid :: nil|) ;; s3) ||> ** HMuxInfo minfob ** P)
      (<|| s3 ||> ** HMuxInfo minfob ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo minfob ** P)) by can_change_aop_solver.
infer_solver 1%nat.
Unshelve.
exact None.
Qed.

Lemma mutextimedlock_absimp_ecb_nullerr_abt:
  forall V_ret s P sch,
    V_ret <> Vint32 (Int.repr EINVAL) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_ecb_nullerr (| Vnull :: V_ret :: nil|) ?? s ||> ** P)
      (<|| ABORT ||> ** P). 
Proof.
intros.
eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_ecb_nullerr:
  forall V_ret s P sch,
    V_ret = Vint32 (Int.repr EINVAL) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_ecb_nullerr (| Vnull :: V_ret :: nil|) ?? s ||> ** P)
      (<|| END Some (Vint32 (Int.repr EINVAL)) ||> ** P). 
Proof.
infer_solver 0%nat.
Qed.

Lemma mutextimedlock_absimp_owner_abt:
  forall V_ow s1 s2 P sch posv eid o x n pro pcp w c mc pr y wl ow mls els,
    get mls posv = Some (Valid_Addr eid, o, x, n, pro, pcp, w, c, mc) ->
    get els eid =  Some (absmutexsem pr y, wl) ->
    (ow = Int.repr OS_MUTEX_AVAILABLE /\ y = None \/
      (exists t op, y = Some (t, op) /\ ow = op)) ->
    V_ow <> Vint32 ow ->
    can_change_aop P -> 
    absinfer sch 
      (<||  s1 ?? (mutextimedlock_owner (|Vint32 posv :: Vptr eid :: V_ow :: nil|) ;; s2) ||> ** HECBList els ** HMuxInfo mls ** P)
      (<|| ABORT ||> ** HECBList els ** HMuxInfo mls ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HECBList els ** HMuxInfo mls ** P)) by can_change_aop_solver.
eapply absinfer_trans; try( eapply absinfer_choice2; eauto).
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
instantiate (2:= mutextimedlock_owner (|Vint32 posv :: Vptr eid :: V_ow :: nil|)).
instantiate (2:= s).
sep pauto.
Qed.

Lemma mutextimedlock_absimp_owner_abt_new:
  forall V_ow s2 P sch posv eid o x n pro pcp w c mc pr y wl ow mls els,
    get mls posv = Some (Valid_Addr eid, o, x, n, pro, pcp, w, c, mc) ->
    get els eid =  Some (absmutexsem pr y, wl) ->
    (ow = Int.repr OS_MUTEX_AVAILABLE /\ y = None \/
      (exists t op, y = Some (t, op) /\ ow = op)) ->
    V_ow <> Vint32 ow ->
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutextimedlock_owner (|Vint32 posv :: Vptr eid :: V_ow :: nil|) ;; s2) ||> ** HECBList els ** HMuxInfo mls ** P)
      (<|| ABORT ||> ** HECBList els ** HMuxInfo mls ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HECBList els ** HMuxInfo mls ** P)) by can_change_aop_solver.
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
instantiate (2:= mutextimedlock_owner (|Vint32 posv :: Vptr eid :: V_ow :: nil|)).
instantiate (2:= s).
sep pauto.
Qed.

Lemma mutextimedlock_absimp_owner:
  forall V_ow s1 s2 P sch posv eid o x n pro pcp w c mc pr y wl ow mls els,
    get mls posv = Some (Valid_Addr eid, o, x, n, pro, pcp, w, c, mc) ->
    get els eid =  Some (absmutexsem pr y, wl) ->
    (ow = Int.repr OS_MUTEX_AVAILABLE /\ y = None \/
      (exists t op, y = Some (t, op) /\ ow = op)) ->
    V_ow = Vint32 ow ->
    can_change_aop P -> 
    absinfer sch 
      (<||  s1 ?? (mutextimedlock_owner (|Vint32 posv :: Vptr eid :: V_ow :: nil|) ;; s2) ||> ** HECBList els ** HMuxInfo mls ** P)
      (<|| s2 ||> ** HECBList els ** HMuxInfo mls ** P). 
Proof.
infer_solver 1%nat.
Qed.

Lemma mutextimedlock_absimp_owner_new:
  forall V_ow s2 P sch posv eid o x n pro pcp w c mc pr y wl ow mls els,
    get mls posv = Some (Valid_Addr eid, o, x, n, pro, pcp, w, c, mc) ->
    get els eid =  Some (absmutexsem pr y, wl) ->
    (ow = Int.repr OS_MUTEX_AVAILABLE /\ y = None \/
      (exists t op, y = Some (t, op) /\ ow = op)) ->
    V_ow = Vint32 ow ->
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutextimedlock_owner (|Vint32 posv :: Vptr eid :: V_ow :: nil|) ;; s2) ||> ** HECBList els ** HMuxInfo mls ** P)
      (<|| s2 ||> ** HECBList els ** HMuxInfo mls ** P). 
Proof.
infer_solver 0%nat.
Qed.


Lemma mutextimedlock_absimp_type_abt:
  forall V_tp s P sch posv eo o tp n pro pcp w c mc mls,
    get mls posv = Some (eo, o, tp, n, pro, pcp, w, c, mc) ->
    V_tp <> Vint32 tp ->
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_type (|Vint32 posv :: V_tp :: nil|) ;; s ||> ** HMuxInfo mls ** P)
      (<|| ABORT ||> ** HMuxInfo mls ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo mls ** P)) by can_change_aop_solver.
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_type:
  forall V_tp s P sch posv eo o tp n pro pcp w c mc mls,
    get mls posv = Some (eo, o, tp, n, pro, pcp, w, c, mc) ->
    V_tp = Vint32 tp ->
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_type (|Vint32 posv :: V_tp :: nil|) ;; s ||> ** HMuxInfo mls ** P)
      (<|| s ||> ** HMuxInfo mls ** P). 
Proof.
infer_solver 0%nat.
Qed.

Lemma mutextimedlock_absimp_typeerr_abt:
  forall tp V_ret s P sch,
    Int.eq tp (Int.repr PTHREAD_MUTEX_NORMAL) = false ->
    Int.eq tp (Int.repr PTHREAD_MUTEX_ERRORCHECK) = false ->
    Int.eq tp (Int.repr PTHREAD_MUTEX_RECURSIVE) = false ->
    V_ret <> (Vint32 (Int.repr EINVAL)) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_typeerr (|Vint32 tp :: V_ret :: nil|) ?? s ||> ** P)
      (<|| ABORT ||> ** P). 
Proof.
intros.
eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_typeerr:
  forall tp V_ret s P sch,
    Int.eq tp (Int.repr PTHREAD_MUTEX_NORMAL) = false ->
    Int.eq tp (Int.repr PTHREAD_MUTEX_ERRORCHECK) = false ->
    Int.eq tp (Int.repr PTHREAD_MUTEX_RECURSIVE) = false ->
    V_ret = (Vint32 (Int.repr EINVAL)) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_typeerr (|Vint32 tp :: V_ret :: nil|) ?? s ||> ** P)
      (<|| END Some (Vint32 (Int.repr EINVAL))  ||> ** P). 
Proof.
infer_solver 0%nat.
Qed.

Lemma mutextimedlock_absimp_curprio_abt:
  forall V_curp s1 s2 s3 P sch els tls t ct prio st m sus,
    get tls ct = Some (prio, st, m, sus) ->
    V_curp <> Vint32 prio ->
    can_change_aop P -> 
    absinfer sch 
      (<||  s1 ?? (mutextimedlock_curprio (|V_curp :: nil|) ;; s2) ?? s3 ||> ** HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
      (<|| ABORT ||> ** HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct **  P)) by can_change_aop_solver.
eapply absinfer_trans; try( eapply absinfer_choice2; eauto).
eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver;
instantiate (2:= mutextimedlock_curprio (|V_curp :: nil|));
instantiate (2:= s);
sep pauto.
Qed.

Lemma mutextimedlock_absimp_curprio_abt_new:
  forall V_curp s2 s3 P sch els tls t ct prio st m sus,
    get tls ct = Some (prio, st, m, sus) ->
    V_curp <> Vint32 prio ->
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutextimedlock_curprio (|V_curp :: nil|) ;; s2) ?? s3 ||> ** HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
      (<|| ABORT ||> ** HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct **  P)) by can_change_aop_solver.
eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver;
instantiate (2:= mutextimedlock_curprio (|V_curp :: nil|));
instantiate (2:= s);
sep pauto.
Qed.

Lemma mutextimedlock_absimp_curprio:
  forall V_curp s1 s2 s3 P sch els tls t ct prio st m sus,
    get tls ct = Some (prio, st, m, sus) ->
    V_curp = Vint32 prio ->
    can_change_aop P -> 
    absinfer sch 
      (<||  s1 ?? (mutextimedlock_curprio (|V_curp :: nil|) ;; s2) ?? s3 ||> ** HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
      (<|| s2 ||> ** HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P). 
Proof.
infer_solver 1%nat.
Qed.

Lemma mutextimedlock_absimp_prioceiling_abt:
  forall V_pcp s P sch posv eo o tp n pro pcp w c mc mls,
    get mls posv = Some (eo, o, tp, n, pro, pcp, w, c, mc) ->
    V_pcp <> Vint32 pcp ->
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_prioceiling (|Vint32 posv :: V_pcp :: nil|) ;; s ||> ** HMuxInfo mls ** P)
      (<|| ABORT ||> ** HMuxInfo mls ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo mls ** P)) by can_change_aop_solver.
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_prioceiling:
  forall V_pcp s P sch posv eo o tp n pro pcp w c mc mls,
    get mls posv = Some (eo, o, tp, n, pro, pcp, w, c, mc) ->
    V_pcp = Vint32 pcp ->
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_prioceiling (|Vint32 posv :: V_pcp :: nil|) ;; s ||> ** HMuxInfo mls ** P)
      (<|| s ||> ** HMuxInfo mls ** P). 
Proof.
infer_solver 0%nat.
Qed.

Lemma mutextimedlock_absimp_type_normal:
  forall tp s0 s1 s2 P sch,
    tp = (Int.repr PTHREAD_MUTEX_NORMAL) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  s0 ?? s1 ?? (mutextimedlock_type_normal (|Vint32 tp :: nil|) ;; s2) ||> ** P)
      (<|| s2  ||> ** P). 
Proof.
infer_solver 2%nat.
Qed.

Lemma mutextimedlock_absimp_type_normal_new:
  forall tp s0 s2 P sch,
    tp = (Int.repr PTHREAD_MUTEX_NORMAL) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  s0 ?? (mutextimedlock_type_normal (|Vint32 tp :: nil|) ;; s2) ||> ** P)
      (<|| s2  ||> ** P). 
Proof.
infer_solver 1%nat.
Qed.

Lemma mutextimedlock_absimp_type_deadlk_abt:
  forall tp ow curp pcp V_ret s P sch,
    tp = (Int.repr PTHREAD_MUTEX_ERRORCHECK) ->
    Int.eq ow curp = true \/ Int.eq pcp curp = true ->
    V_ret <> (Vint32 (Int.repr EDEADLK)) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_type_deadlk (|Vint32 tp :: Vint32 ow :: Vint32 curp :: Vint32 pcp :: V_ret :: nil|) ?? s ||> ** P)
      (<|| ABORT ||> ** P). 
Proof.
intros.
eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_type_deadlk:
  forall tp ow curp pcp V_ret s P sch,
    tp = (Int.repr PTHREAD_MUTEX_ERRORCHECK) ->
    Int.eq ow curp = true \/ Int.eq pcp curp = true ->
    V_ret = (Vint32 (Int.repr EDEADLK)) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_type_deadlk (|Vint32 tp :: Vint32 ow :: Vint32 curp :: Vint32 pcp :: V_ret :: nil|) ?? s ||> ** P)
      (<|| END Some (Vint32 (Int.repr EDEADLK))  ||> ** P). 
Proof.
infer_solver 0%nat.
Qed.

Lemma mutextimedlock_absimp_after_pend_timeout_abt:
  forall verr V_ret s P sch,
    Int.eq verr (Int.repr OS_TIMEOUT) = true ->
    V_ret <> (Vint32 (Int.repr ETIMEDOUT)) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_after_pend_timeout (|Vint32 verr :: V_ret :: nil|) ?? s ||> ** P)
      (<|| ABORT ||> ** P). 
Proof.
intros.
eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_after_pend_timeout:
  forall verr V_ret s P sch,
    Int.eq verr (Int.repr OS_TIMEOUT) = true ->
    V_ret = (Vint32 (Int.repr ETIMEDOUT)) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_after_pend_timeout (|Vint32 verr :: V_ret :: nil|) ?? s ||> ** P)
      (<|| END Some (Vint32 (Int.repr ETIMEDOUT))  ||> ** P). 
Proof.
infer_solver 0%nat.
Qed.

Lemma mutextimedlock_absimp_after_pend_fail_abt:
  forall verr V_ret s1 s2 P sch,
    Int.eq verr (Int.repr OS_TIMEOUT) = false ->
    Int.eq verr (Int.repr OS_NO_ERR) = false ->
    V_ret <> (Vint32 (Int.repr EINVAL)) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  s1 ?? mutextimedlock_after_pend_fail (|Vint32 verr :: V_ret :: nil|) ?? s2 ||> ** P)
      (<|| ABORT ||> ** P). 
Proof.
intros.
eapply absinfer_trans; try( eapply absinfer_choice2; eauto).
eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_after_pend_fail_abt_new:
  forall verr V_ret s2 P sch,
    Int.eq verr (Int.repr OS_TIMEOUT) = false ->
    Int.eq verr (Int.repr OS_NO_ERR) = false ->
    V_ret <> (Vint32 (Int.repr EINVAL)) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mutextimedlock_after_pend_fail (|Vint32 verr :: V_ret :: nil|) ?? s2 ||> ** P)
      (<|| ABORT ||> ** P). 
Proof.
intros.
eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_after_pend_fail:
  forall verr V_ret s1 s2 P sch,
    Int.eq verr (Int.repr OS_TIMEOUT) = false ->
    Int.eq verr (Int.repr OS_NO_ERR) = false ->
    V_ret = (Vint32 (Int.repr EINVAL)) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  s1 ?? mutextimedlock_after_pend_fail (|Vint32 verr :: V_ret :: nil|) ?? s2 ||> ** P)
      (<|| END Some (Vint32 (Int.repr EINVAL))  ||> ** P). 
Proof.
infer_solver 1%nat.
Qed.

Lemma mutextimedlock_absimp_after_pend_succ_null_abt:
  forall verr V_ret s P sch,
    verr = (Int.repr OS_NO_ERR) ->
    V_ret <> (Vint32 Int.zero) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_after_pend_succ_null (|Vint32 verr :: Vnull :: V_ret :: nil|) ?? s ||> ** P)
      (<|| ABORT ||> ** P). 
Proof.
intros.
eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_after_pend_succ_null:
  forall verr V_ret s P sch,
    verr = (Int.repr OS_NO_ERR) ->
    V_ret = (Vint32 Int.zero) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_after_pend_succ_null (|Vint32 verr :: Vnull :: V_ret :: nil|) ?? s ||> ** P)
      (<|| END Some (Vint32 Int.zero)  ||> ** P). 
Proof.
infer_solver 0%nat.
Qed.

Lemma mutextimedlock_absimp_after_pend_succ_ecb_abt:
  forall verr eid posv V_ret s P sch mls els o tp n pro pcp w c mc pip ow wl,
    verr = (Int.repr OS_NO_ERR) ->
    get mls posv = Some (Valid_Addr eid, o, tp, n, pro, pcp, w, c, mc) ->
    get els eid = Some (absmutexsem pip ow, wl) ->
    V_ret <> (Vint32 Int.zero) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  s ?? mutextimedlock_after_pend_succ_ecb (|Vint32 verr :: Vptr eid :: Vint32 posv :: V_ret :: nil|) ||> 
        ** HECBList els ** HMuxInfo mls ** P)
      (<|| ABORT ||> ** HECBList els ** HMuxInfo mls ** P). 
Proof.
intros.
assert(can_change_aop (HECBList els ** HMuxInfo mls ** P)) by can_change_aop_solver.
eapply absinfer_trans; try( eapply absinfer_choice2; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver;
instantiate (2:=  mutextimedlock_after_pend_succ_ecb (|Vint32 (Int.repr OS_NO_ERR) :: Vptr eid :: Vint32 posv :: V_ret :: nil|));
instantiate (2:= s0);
sep pauto.
Qed.

Lemma mutextimedlock_absimp_after_pend_succ_ecb:
  forall verr eid posv V_ret s P sch mls els o tp n pro pcp w c mc pip ow wl,
    verr = (Int.repr OS_NO_ERR) ->
    get mls posv = Some (Valid_Addr eid, o, tp, n, pro, pcp, w, c, mc) ->
    get els eid = Some (absmutexsem pip ow, wl) ->
    V_ret = (Vint32 Int.zero) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  s ?? mutextimedlock_after_pend_succ_ecb (|Vint32 verr :: Vptr eid :: Vint32 posv :: V_ret :: nil|) ||> 
        ** HECBList els ** HMuxInfo mls ** P)
      (<|| END Some (Vint32 Int.zero) ||> ** HECBList els ** HMuxInfo (set mls posv (Valid_Addr eid, ow, tp, n, pro, pcp, w, c, mc)) ** P). 
Proof.
infer_solver 1%nat.
Qed.

Lemma mutextimedlock_absimp_recurcnt_abt:
  forall V_rcnt s s1 s2 P sch posv eo o tp n pro pcp w c mc mls,
    get mls posv = Some (eo, o, tp, n, pro, pcp, w, c, mc) ->
    V_rcnt <> Vint32 n ->
    can_change_aop P -> 
    absinfer sch 
      (<||  s1 ?? (mutextimedlock_recurcnt (|Vint32 posv :: V_rcnt :: nil|) ;; s) ?? s2 ||> ** HMuxInfo mls ** P)
      (<|| ABORT ||> ** HMuxInfo mls ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo mls ** P)) by can_change_aop_solver.
eapply absinfer_trans; try( eapply absinfer_choice2; eauto).
eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_recurcnt_abt_new:
  forall V_rcnt s s2 P sch posv eo o tp n pro pcp w c mc mls,
    get mls posv = Some (eo, o, tp, n, pro, pcp, w, c, mc) ->
    V_rcnt <> Vint32 n ->
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutextimedlock_recurcnt (|Vint32 posv :: V_rcnt :: nil|) ;; s) ?? s2 ||> ** HMuxInfo mls ** P)
      (<|| ABORT ||> ** HMuxInfo mls ** P). 
Proof.
intros.
assert (Hc: can_change_aop (HMuxInfo mls ** P)) by can_change_aop_solver.
eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
eapply absinfer_trans; try( eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_recurcnt:
  forall V_rcnt s s1 s2 P sch posv eo o tp n pro pcp w c mc mls,
    get mls posv = Some (eo, o, tp, n, pro, pcp, w, c, mc) ->
    V_rcnt = Vint32 n ->
    can_change_aop P -> 
    absinfer sch 
      (<||  s1 ?? (mutextimedlock_recurcnt (|Vint32 posv :: V_rcnt :: nil|) ;; s) ?? s2 ||> ** HMuxInfo mls ** P)
      (<|| s ||> ** HMuxInfo mls ** P). 
Proof.
infer_solver 1%nat.
Qed.

Lemma mutextimedlock_absimp_recurcnt_new:
  forall V_rcnt s s2 P sch posv eo o tp n pro pcp w c mc mls,
    get mls posv = Some (eo, o, tp, n, pro, pcp, w, c, mc) ->
    V_rcnt = Vint32 n ->
    can_change_aop P -> 
    absinfer sch 
      (<|| (mutextimedlock_recurcnt (|Vint32 posv :: V_rcnt :: nil|) ;; s) ?? s2 ||> ** HMuxInfo mls ** P)
      (<|| s ||> ** HMuxInfo mls ** P). 
Proof.
infer_solver 0%nat.
Qed.

Lemma mutextimedlock_absimp_recur_incre_one_abt:
  forall posv V_ret s P sch mls e o x cn pro pip w c mc tp ow curp pcp rcnt,
    tp = Int.repr PTHREAD_MUTEX_RECURSIVE ->
    Int.eq ow curp = true \/ Int.eq pcp curp = true ->
    Int.ltu rcnt (Int.repr PTHREAD_MUTEX_RECURSIVE_MAX) = true ->
    get mls posv = Some (e, o, x, cn, pro, pip, w, c, mc) ->
    V_ret <> (Vint32 Int.zero) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_type_recur_incre_one 
                  (|Vint32 posv :: Vint32 tp :: Vint32 ow :: Vint32 curp :: Vint32 pcp :: Vint32 rcnt :: V_ret :: nil|) ?? s ||> 
        ** HMuxInfo mls ** P)
      (<|| ABORT ||> ** HMuxInfo mls ** P). 
Proof.
intros.
assert(can_change_aop (HMuxInfo mls ** P)) by can_change_aop_solver.
eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_recur_incre_one:
  forall posv V_ret s P sch mls e o x cn pro pip w c mc tp ow curp pcp rcnt,
    tp = Int.repr PTHREAD_MUTEX_RECURSIVE ->
    Int.eq ow curp = true \/ Int.eq pcp curp = true ->
    Int.ltu rcnt (Int.repr PTHREAD_MUTEX_RECURSIVE_MAX) = true ->
    get mls posv = Some (e, o, x, cn, pro, pip, w, c, mc) ->
    V_ret = (Vint32 Int.zero) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_type_recur_incre_one 
                  (|Vint32 posv :: Vint32 tp :: Vint32 ow :: Vint32 curp :: Vint32 pcp :: Vint32 rcnt :: V_ret :: nil|) ?? s ||> 
        ** HMuxInfo mls ** P)
      (<|| END Some (Vint32 Int.zero) ||> ** HMuxInfo (set mls posv (e, o, x, Int.add cn Int.one, pro, pip, w, c, mc)) ** P). 
Proof.
infer_solver 0%nat.
Qed.

Lemma mutextimedlock_absimp_recur_again_abt:
  forall V_ret s P sch tp ow curp pcp rcnt,
    tp = Int.repr PTHREAD_MUTEX_RECURSIVE ->
    Int.eq ow curp = true \/ Int.eq pcp curp = true ->
    Int.ltu rcnt (Int.repr PTHREAD_MUTEX_RECURSIVE_MAX) = false ->
    V_ret <> (Vint32 (Int.repr EAGAIN)) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  s ?? mutextimedlock_type_recur_again (| Vint32 tp :: Vint32 ow :: Vint32 curp :: Vint32 pcp :: Vint32 rcnt :: V_ret :: nil|) ||> ** P)
      (<|| ABORT ||> ** P). 
Proof.
intros.
eapply absinfer_trans; try( eapply absinfer_choice2; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextimedlock_absimp_recur_again:
  forall V_ret s P sch tp ow curp pcp rcnt,
    tp = Int.repr PTHREAD_MUTEX_RECURSIVE ->
    Int.eq ow curp = true \/ Int.eq pcp curp = true ->
    Int.ltu rcnt (Int.repr PTHREAD_MUTEX_RECURSIVE_MAX) = false ->
    V_ret = (Vint32 (Int.repr EAGAIN)) ->
    can_change_aop P -> 
    absinfer sch 
      (<||  s ?? mutextimedlock_type_recur_again (| Vint32 tp :: Vint32 ow :: Vint32 curp :: Vint32 pcp :: Vint32 rcnt :: V_ret :: nil|) ||> ** P)
      (<|| END Some (Vint32 (Int.repr EAGAIN)) ||> ** P). 
Proof.
infer_solver 1%nat.
Qed.

Lemma mutextimedlock_absimp_set_evloc_ptr:
  forall V_pevt s P sch ptrmp ct,
    can_change_aop P -> 
    absinfer sch 
      (<||  mutextimedlock_set_evloc_ptr (| V_pevt :: nil |) ;; s ||> ** HEvPtr ptrmp ** HCurTCB ct ** P)
      (<|| s ||> ** HEvPtr (set ptrmp ct (V_pevt, Vnull, Vnull)) ** HCurTCB ct ** P). 
Proof.
infer_solver 0%nat.
Unshelve.
exact None.
Qed.

(* Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope. *)

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
destruct (V_OSEventListPtr v0); try tryfalse; destruct v2; try tryfalse. (*v,v1 -> v0, v2 *)
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

Lemma PthreadMutexLockPartProof:
forall (tid : tid) (x0 : addrval) (V_pevt V_err V_afteid V_ret v'0 v'3 v'6 v'7 v'8: val)
           (posv tp ow tmv: int32) (vp_b1 : block) er vdom vnum,
   Int.ltu posv Int.zero = false ->
   Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) posv = false ->
   posv <> $ (OS_USER_MAX_EVENTS / 3) ->
   Int.eq posv (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) = false ->
   Int.unsigned posv <= Int.max_unsigned ->
   Int.eq tmv Int.zero = false ->
   Int.ltu ($ 65535) tmv = false ->
   Int.unsigned tmv <= 65535 ->
{|OS_spec, GetHPrio, OSLInv, I,
fun v : option val =>
( <|| END v ||>  **
 p_local OSLInv tid init_lg **
 ((EX v0 : val, LV os_code_defs.abs_timeout @ Int16u |-> v0) **
  (EX v0 : val, LV mutex @ (long) ∗ |-> v0) **
  (EX v0 : val, LV err @ char_t |-> v0) **
  (EX v0 : val, LV os_code_defs.pos @ long |-> v0) **
  (EX v0 : val, LV x @ char_t |-> v0) **
  (EX v0 : val, LV z @ char_t |-> v0) **
  (EX v0 : val, LV muxowner @ char_t |-> v0) **
  (EX v0 : val, LV ty @ long |-> v0) **
  (EX v0 : val, LV os_code_defs.pip @ long |-> v0) **
  (EX v0 : val, LV r @ long |-> v0) **
  (EX v0 : val, LV cpr @ char_t |-> v0) **
  (EX v0 : val, LV p @ OS_EVENT ∗ |-> v0) **
  (EX v0 : val, LV temp_dom @ char_t |-> v0) **
  (EX v0 : val, LV temp_num @ char_t |-> v0) ** Aemp) **
 Aie true ** Ais nil ** Acs nil ** Aisr empisr ** (EX er, Aier er)) **
A_dom_lenv
  ((os_code_defs.abs_timeout, Int16u)
   :: (mutex, (long) ∗)
   :: (err, char_t)
      :: (os_code_defs.pos, long)
         :: (x, char_t)
            :: (z, char_t)
               :: (muxowner, char_t)
                  :: (ty, long)
                     :: (os_code_defs.pip, long)
                        :: (r, long) :: (cpr, char_t) :: (p, OS_EVENT ∗)
                          :: (temp_dom, char_t) :: (temp_num, char_t) :: nil),
Afalse|}|- tid
{{ <||  mutextimedlock_ecb_ptr (| Vint32 posv :: V_pevt :: nil |) ;;
             mutextimedlock_set_evloc_ptr (| V_pevt :: nil |);; 
             spec_code_cons (mutexpend (V_pevt :: Vint32 tmv :: V_err :: nil))
             (mutextimedlock_set_evloc_ptr (| Vnull :: nil |);; 
               (mutextimedlock_after_pend_timeout (| V_err :: V_ret :: nil |) ??
                 mutextimedlock_after_pend_fail (| V_err :: V_ret :: nil |) ??
                    (mutextimedlock_ecb_ptr (| Vint32 posv :: V_afteid :: nil |) ;;
                            (mutextimedlock_after_pend_succ_null (| V_err :: V_afteid :: V_ret :: nil |) ??
                              mutextimedlock_after_pend_succ_ecb (| V_err :: V_afteid :: Vint32 posv :: V_ret :: nil |))))) ||>  **
  Aisr empisr **
  Aie true **
  Ais nil **
  Acs nil **
  Aier er **
  p_local OSLInv tid init_lg **
  LV ty @ long |-> Vint32 tp **
  LV muxowner @ char_t |-> Vint32 ow **
  LV p @ OS_EVENT ∗ |-> Vptr (vp_b1, Int.zero) **
  LV os_code_defs.pos @ long |-> Vint32 posv **
  LV x @ char_t |-> (V$ 1) **
  LV cpr @ char_t |-> v'8 **
  LV r @ long |-> v'7 **
  LV os_code_defs.pip @ long |-> v'6 **
  LV z @ char_t |-> v'3 **
  LV err @ char_t |-> v'0 **
  LV os_code_defs.abs_timeout @ Int16u |-> Vint32 tmv **
  LV mutex @ (long) ∗ |-> Vptr x0 **
  LV temp_dom @ char_t |-> vdom **
  LV temp_num @ char_t |-> vnum **
  A_dom_lenv
    ((os_code_defs.abs_timeout, Int16u)
     :: (mutex, (long) ∗)
     :: (err, char_t)
        :: (os_code_defs.pos, long)
           :: (x, char_t)
              :: (z, char_t)
                 :: (muxowner, char_t)
                    :: (ty, long)
                       :: (os_code_defs.pip, long)
                          :: (r, long) :: (cpr, char_t) :: (p, OS_EVENT ∗)
                            :: (temp_dom, char_t) :: (temp_num, char_t)  :: nil)}} ENTER_CRITICAL;ₛ
p ′ =ₑ efield (Pthread_Mutex ′ [os_code_defs.pos ′]) pevent;ₛ
OSTCBCur′→__OSTskMuxPtr =ₑ p′;ₛ (* new add *)
EXIT_CRITICAL;ₛ
 z′ =ᶠ OSMutexPend(·p′, os_code_defs.abs_timeout′·);ₛ
ENTER_CRITICAL;ₛ (* new add *)
OSTCBCur′→__OSTskMuxPtr =ₑ NULL;ₛ (* new add *)
EXIT_CRITICAL;ₛ (* new add *)
 If (z′ ==ₑ  ′OS_TIMEOUT){
 RETURN ′ETIMEDOUT
 };ₛ
If (z ′ ==ₑ ′ OS_NO_ERR)
{ENTER_CRITICAL;ₛ
p ′ =ₑ efield (Pthread_Mutex ′ [os_code_defs.pos ′]) pevent;ₛ
If (p ′ !=ₑ NULL)
{efield (Pthread_Mutex ′ [os_code_defs.pos ′]) mutex_owner =ₑ
 〈 char_t
 〉 ((efield (Pthread_Mutex ′ [os_code_defs.pos ′]) pevent) → OSEventCnt &ₑ
    ′ OS_MUTEX_KEEP_LOWER_8)};ₛ
EXIT_CRITICAL;ₛ
RETURN ′ 0};ₛ
RETURN ′ EINVAL {{Afalse}}.
Proof.
  introv Hpos_lt1 Hpos_lt2 Hpos_neq Hpos_neq' Hpos_range.
  introv Htmv_neq Htmv_lt Htmv_range.

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

 (* third get p: ENTER_CRITICAL;ₛ p ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) pevent;ₛ EXIT_CRITICAL;ₛ*)
  hoare forward prim.
  hoare unfold.

 (* unfold EvtInv.
 hoare normal pre; hoare_ex_intro.
 hoare_assert_pure (length v'30 = (∘ (OS_USER_MAX_EVENTS / 3))).
 { get_hsat Hsat. sep_lifts_trms_in Hsat AMuxEIBs.
   eapply length_vll_apthrmux; eauto.  }
 eapply pure_split_rule'; introv Hlen_minfo.
 unfold AMuxEIBs.
 hoare normal pre; hoare_ex_intro.
 hoare_lifts_trms_pre ( R_Q_Data_P ).
 eapply pure_split_rule'; introv Hrqdata.
 hoare unfold. *)
 unfold EvtInv.
 hoare normal pre; hoare_ex_intro.
 unfold AMuxEIBs.
 hoare normal pre; hoare_ex_intro.
 hoare_lifts_trms_pre ( R_Q_Data_P ).
 eapply pure_split_rule'; introv Hrqdata.
 hoare_lifts_trms_pre (AMuxCap).
 match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ AMuxCap ?l ?vl ** _ }} _ {{ _ }} =>
 rename l into lmux; rename vl into muxcapvl end.
 hoare_lifts_trms_pre (MuxCapArray_P, length muxcapvl).
 eapply pure_split_rule'; introv Hmuxcap_vl.
 eapply pure_split_rule'; introv Hmuxcap_len.
 destruct lmux as (lmux_b & lmux_i).
 hoare_lifts_trms_pre APthreadMutex.
 match goal with
  | |- {| _ , _, _, _, _, _ |} |- _ {{ APthreadMutex _ ?vl ** _ }} _ {{ _ }} =>
     hoare_assert_pure (length vl = (∘ (OS_USER_MAX_EVENTS / 3)))
  end.
 { get_hsat Hsat. sep_lifts_trms_in Hsat APthreadMutex.
   eapply apthreadmutex_len_frm; eauto.  }
 eapply pure_split_rule'; introv Hlen_minfo.
 hoare unfold.

  hoare_lifts_trms_pre (Aop, APthreadMutex).
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
  eapply new_array_type_vallist_match_split1 in H3; eauto.
  simpljoin; auto.
  eapply eq_vptr; eauto.
  intros. eexists. sep cancel p_local. simpl; eauto.

  lets Hmls: muxb_corr H1 H12 Hpos_lt1 Hpos_range. 
  destruct Hmls as (eo & ow' & tp' & rcnt & prot & pcp & wq & c & mc & Hget & Hmls).
  match goal with H: EIBMAarray_P _ (_ ++ ?vl :: _) _ _ |- _ => rename vl into mutvl end.
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
    eapply mutextimedlock_absimp_ecb_ptr_hold_abt'; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
    apply absabort_rule.
  }

  assert (Hvpevt: ((exists eid,  eo = Valid_Addr eid /\ V_pevt = Vptr eid) \/ eo = Null /\ V_pevt = Vnull) 
        \/ ((exists eid, eo = Valid_Addr eid /\ V_pevt <> Vptr eid) \/ eo = Null /\ V_pevt <> Vnull)).
  {
    destruct Hok as [( eid & Heo & _) | (Heo & _)]; subst eo.
    assert (Hv: V_pevt = Vptr eid \/ V_pevt <> Vptr eid) by tauto.
    destruct Hv; [left | right]; left; eauto.
    assert (Hv: V_pevt = Vnull \/ V_pevt <> Vnull) by tauto.
    destruct Hv; [left | right]; right; eauto.
    }
  destruct Hvpevt as [Hvpevt | Habt].
  2: {
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutextimedlock_absimp_ecb_ptr_abt'; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
        }
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutextimedlock_absimp_ecb_ptr'; eauto.
   can_change_aop_solver.
   eapply absinfer_eq.
   (* EXIT_CRITICAL *)
    eapply backward_rule1. 
    introv Hsat.
    eapply APthreadMutex_select_sn_ex_strong.
    eexists. exists (Z.to_nat (Int.unsigned posv)). eexists.
    exists mutvl.
    sep cancel Aarray_new.
    sep cancel Aarray_new.
    sep pauto.

    (* OSTCBCur ′ → __OSTskMuxPtr =ₑ p ′;ₛ *)
  assert (Hvpevt_eq: nth_val' 8 mutvl = V_pevt).
  { clear -Hok Hvpevt.
     unfold V_OSMUXINFOPevent in *.
     destruct Hok as [( eid & Heo & Hvp & _) | (Heo & Hvp)]; subst eo;
     eapply nth_val_nth_val'_some_eq in Hvp; rewrite Hvp;
     destruct Hvpevt as [( eid0 & Heo & Hvp1) | (Heo & Hvp1)]; inverts Heo;
     auto.
  }
  rewrite Hvpevt_eq.
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
    apply new_array_type_vallist_match_mux_getp in H3. 
    clear -H3. simpljoin1. 
    unfold V_OSSINFOPevent in H.
    do 9 (destruct mutvl; simpl in H; tryfalse).  
    inverts H. simpl. auto.
  }
  hoare_assign_evaux.
  {
     apply new_array_type_vallist_match_mux_getp in H3.
     clear -H3. 
     simpljoin1.
     unfold V_OSSINFOPevent in H.
     do 9 (destruct mutvl; simpl in H; tryfalse).
     inverts H. destruct H0. subst. auto. simpljoin1.
  }
  match goal with H: MUX_ECB_P ?loc ?ptr ?ecb ?fecbh ?fecbvl ?sem ?mux ?mq |- _ =>
  rename loc into locmp; rename ptr into ptrmp; rename ecb into els;
  rename sem into semeibs; rename mux into muxeibs; rename mq into mqeibs
  end.
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

  hoare_lifts_trms_pre (Aop, evptrid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextimedlock_absimp_set_evloc_ptr; eauto.
  can_change_aop_solver.
  unfold CurTid. go.
  eapply absinfer_eq.

  remember (nth_val' 8 mutvl) as V_pevt.

  (* preparation for EXIT_CRITICAL;ₛ *)
  fold_evaux_mux V_pevt.
  clear -Hisptr.  simpl. destruct Hisptr; mytac.

   (* EXIT_CRITICAL *)
   hoare forward prim.
   sep cancel Aier.
   unfold EvtInv.
   unfold AMuxEIBs.
   unfold p_local. unfold LINV. unfold OSLInv.
   sep normal; sep eexists.
   sep cancel AMuxCap.
   sep pauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel AMqEIBs.
   sep cancel APthreadMutex.
   sep cancel APthreadAttr.
   sep cancel CapabilityInv.
   unfold tcbllsegevaux.
   eauto.
   eapply evdel_nodup_normal_muxptr_preserve; eauto.
   eapply evcre_nodup_normal_muxptr_preserve; eauto.
   {
   destruct Hvpevt as [(eid & Heo & Hvp) | (Heo & Hvp)];
   rewrite Hvp.
   eapply mq_ecb_p_muxptr_normal_preserve; eauto.
   eapply H2; eauto.
   eapply mq_ecb_p_set_null3_preserve; eauto.
    }
   {
   destruct Hvpevt as [(eid & Heo & Hvp) | (Heo & Hvp)];
   rewrite Hvp.
   eapply mux_ecb_p_muxptr_normal_preserve; eauto.
   eapply H2; eauto.
   eapply mux_ecb_p_set_null3_preserve; eauto.
    }
   {
   destruct Hvpevt as [(eid & Heo & Hvp) | (Heo & Hvp)];
   rewrite Hvp.
   eapply sem_ecb_p_muxptr_normal_preserve; eauto.
   eapply H2; eauto.
   eapply sem_ecb_p_set_null3_preserve; eauto.
    }
    auto.
  Optimize Proof.
  Optimize Heap.
    unfold isevptr. unfold isptr. unfold isevloc.
    splits; eauto.
   auto.
   pure_auto.
  (* split the mutvl as mutvl = _ :: _ :: ... :: nil *)
  lets Hmut_vll: H3.
  rename H3 into Hmut_vl.
  eapply new_array_type_vallist_match_split1 in Hmut_vl; eauto.
  destruct Hmut_vl as (_ & _ & Hmut_vl).
  lets Hmut_vl_eq: struct_type_vallist_match_mutex_info_t_imp Hmut_vl.
  destruct Hmut_vl_eq as (vtp & vpro & vpcp & vwq & vcs & vow & vrcnt & vtsk & vp & vmc & Hmut_vl_eq & Hvp_ptr).
  subst mutvl.
  simpl nth_val' in *.
  subst vp.
  (* z ′ =ᶠ OSMutexPend (·p ′, os_code_defs.abs_timeout′·);ₛ *)
  hoare forward.
  clear -Hvp_ptr. pure_auto.
  pure_auto.
  pure_auto.
   (* retpost OSMutexPendPost *)
  unfold retpost.  introv Hsat. inverts Hsat.
  sep destruct H3.
  sep split in H3. mytac.
  clear -Hvp_ptr Htmv_range. pure_auto.
  introv Hsat. sep destruct Hsat. eexists.
  sep cancel p_local. simpl; auto.
  introv Hsat. sep destruct Hsat. eexists.
  sep cancel p_local. simpl; auto.
  (* end of OSMutexPend *)
  unfold OSMutexPendPost.
  unfold OSMutexPendPost'.
  unfold getasrt.
  hoare unfold.
  inverts H3.
  match goal with H: _ = Vnull -> Int.ltu _ ?v = true |- _ => rename v into verr end.

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

  match goal with H: MUX_ECB_P ?loc ?ptr ?ecb ?fecbh ?fecbvl ?sem ?mux ?mq |- _ =>
  rename loc into locmp'; rename ptr into ptrmp'; rename ecb into els';
  rename sem into semeibs'; rename mux into muxeibs'; rename mq into mqeibs'
  end.
  match goal with H: join (sig _ (?vp, _, _)) _ _ |- _ => rename vp into cur_evp end.
  assert (Hevptr': get ptrmp' tid = Some (cur_evp, Vnull, Vnull)).  
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  hoare_assign_evaux.

  hoare_lifts_trms_pre (Aop, evptrid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextimedlock_absimp_set_evloc_ptr; eauto.
  can_change_aop_solver.
  unfold CurTid. go.
  eapply absinfer_eq.

  fold_evaux_mux Vnull.
  hoare forward prim.
  sep cancel Aier.
  sep cancel tcbdllflag.
  sep cancel CapabilityInv.
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
  eauto.
  eapply evdel_nodup_set_null3_preserve; eauto.
  eapply evcre_nodup_set_null3_preserve; eauto. 
  eapply mq_ecb_p_set_null3_preserve; eauto.
  eapply mux_ecb_p_set_null3_preserve; eauto.
  eapply sem_ecb_p_set_null3_preserve; eauto.
  auto.
  pure_auto.

  (* If (z ′ ==ₑ ′ OS_TIMEOUT){RETURN ′ ETIMEDOUT};ₛ *)
  hoare forward.
  pure_auto.
  pure_auto.
  hoare unfold.
  destruct (Int.eq verr ($ OS_TIMEOUT)) eqn: eq1;
  simpl in H37; tryfalse.
  assert (Hrv: V_ret = Vint32 (Int.repr ETIMEDOUT) \/ V_ret <> Vint32 (Int.repr ETIMEDOUT)) by tauto.
  destruct Hrv.
  subst.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutextimedlock_absimp_after_pend_timeout; eauto.
  can_change_aop_solver.
  hoare forward.
  (* abort case *)
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutextimedlock_absimp_after_pend_timeout_abt; eauto.
  can_change_aop_solver.
  apply absabort_rule.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  destruct (Int.eq verr ($ OS_TIMEOUT)) eqn: eq1;
  simpl in H37; destruct H37; tryfalse.
  clear H37.
  (* If (z ′ ==ₑ ′ OS_NO_ERR) *)
  hoare forward.
  pure_auto.
  pure_auto.
 (* pend_fail: verr <> OS_NO_ERR *)
  2: { instantiate(1:= Afalse).
         eapply hoare_disj_afalseP_l_pre.
         hoare unfold.
         destruct (Int.eq verr ($ OS_NO_ERR)) eqn: eq2;
         simpl in H37; try (destruct H37; tryfalse).
         assert (Hrv: V_ret = Vint32 (Int.repr EINVAL) \/ V_ret <> Vint32 (Int.repr EINVAL)) by tauto.
         destruct Hrv.
         subst.
         hoare abscsq.
        apply noabs_oslinv.
        eapply mutextimedlock_absimp_after_pend_fail; eauto.
        can_change_aop_solver.
        hoare forward.
        (* abort case *)
        hoare abscsq.
        apply noabs_oslinv.
        eapply mutextimedlock_absimp_after_pend_fail_abt; eauto.
        can_change_aop_solver.
        apply absabort_rule.
     }
  (* pend_succ: verr = OS_NO_ERR *)
  hoare unfold.
  destruct (Int.eq verr ($ OS_NO_ERR)) eqn: eq2;
  simpl in H37; tryfalse.
  apply inteqeq in eq2; subst.
  clear -Hpos_lt1 Hpos_lt2 Hpos_neq Hpos_neq' Hpos_range Htmv_neq Htmv_lt Htmv_range Hrgn3 Hrgn4 Hdiveq.
  (* 4th get p: ENTER_CRITICAL;ₛ p ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) pevent;ₛ EXIT_CRITICAL;ₛ*)
  hoare forward prim.
  hoare unfold.

  (* unfold EvtInv.
  hoare normal pre; hoare_ex_intro.
  hoare_assert_pure (length v'29 = (∘ (OS_USER_MAX_EVENTS / 3))).
  { get_hsat Hsat. sep_lifts_trms_in Hsat AMuxEIBs.
     eapply length_vll_apthrmux; eauto.  }
  eapply pure_split_rule'; introv Hlen_minfo.
  unfold AMuxEIBs.
  hoare normal pre; hoare_ex_intro.
  hoare_lifts_trms_pre ( R_Q_Data_P ).
  eapply pure_split_rule'; introv Hrqdata.
  hoare unfold. *)
 
   unfold EvtInv.
   hoare normal pre; hoare_ex_intro.
   unfold AMuxEIBs.
   hoare normal pre; hoare_ex_intro.
   hoare_lifts_trms_pre ( R_Q_Data_P ).
   eapply pure_split_rule'; introv Hrqdata.
   hoare_lifts_trms_pre (AMuxCap).
   match goal with
    | |- {| _, _ , _, _, _, _ |} |- _ {{ AMuxCap ?l ?vl ** _ }} _ {{ _ }} =>
   rename l into lmux; rename vl into muxcapvl end.
   hoare_lifts_trms_pre (MuxCapArray_P, length muxcapvl).
   eapply pure_split_rule'; introv Hmuxcap_vl.
   eapply pure_split_rule'; introv Hmuxcap_len.
   destruct lmux as (lmux_b & lmux_i).
   hoare_lifts_trms_pre APthreadMutex.
   match goal with
    | |- {| _ , _, _, _, _, _ |} |- _ {{ APthreadMutex _ ?vl ** _ }} _ {{ _ }} =>
       hoare_assert_pure (length vl = (∘ (OS_USER_MAX_EVENTS / 3)))
    end.
   { get_hsat Hsat. sep_lifts_trms_in Hsat APthreadMutex.
     eapply apthreadmutex_len_frm; eauto.  }
   eapply pure_split_rule'; introv Hlen_minfo.
   hoare unfold.

  hoare_lifts_trms_pre (Aop, APthreadMutex).
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
  Optimize Proof.
  Optimize Heap.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  eapply new_array_type_vallist_match_split1 in H3; eauto.
  simpljoin; auto.
  eapply eq_vptr; eauto.
  intros. eexists. sep cancel p_local. simpl; eauto.

  lets Hmls: muxb_corr H1 H12 Hpos_lt1 Hpos_range. 
  destruct Hmls as (eo & ow' & tp' & rcnt & prot & pcp & wq & c & mc & Hget & Hmls).
  match goal with H: EIBMAarray_P _ (_ ++ ?vl :: _) _ _ |- _ => rename vl into mutvl end.
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
    eapply mutextimedlock_absimp_ecb_ptr_hold_abt''; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
    apply absabort_rule.
  }

  assert (Hveid: ((exists eid,  eo = Valid_Addr eid /\ V_afteid = Vptr eid) \/ eo = Null /\ V_afteid = Vnull) 
        \/ ((exists eid, eo = Valid_Addr eid /\ V_afteid <> Vptr eid) \/ eo = Null /\ V_afteid <> Vnull)).
  {
    destruct Hok as [( eid & Heo & _) | (Heo & _)]; subst eo.
    assert (Hv: V_afteid = Vptr eid \/ V_afteid <> Vptr eid) by tauto.
    destruct Hv; [left | right]; left; eauto.
    assert (Hv: V_afteid = Vnull \/ V_afteid <> Vnull) by tauto.
    destruct Hv; [left | right]; right; eauto.
    }
  destruct Hveid as [Hveid | Habt].
  2: {
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutextimedlock_absimp_ecb_ptr_abt''; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
        }
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutextimedlock_absimp_ecb_ptr''; eauto.
   can_change_aop_solver.
   eapply absinfer_eq.
    (* split the mutvl as mutvl = _ :: _ :: ... :: nil *)
   lets Hmut_vll: H3.
  rename H3 into Hmut_vl.
  eapply new_array_type_vallist_match_split1 in Hmut_vl; eauto.
  destruct Hmut_vl as (Hmut_vll1 & Hmut_vll2 & Hmut_vl).
  lets Hmut_vl_eq: struct_type_vallist_match_mutex_info_t_imp Hmut_vl.
  destruct Hmut_vl_eq as (vtp & vpro & vpcp & vwq & vcs & vow & vrcnt & vtsk & vp & vmc & Hmut_vl_eq & Hvp_ptr).
  subst mutvl.
  simpl nth_val'.
  unfold V_OSMUXINFOPevent in Hok.
  simpl nth_val in Hok.
  assert(Hvp_eq: vp = V_afteid).
  { clear -Hok Hveid.
     destruct Hok as [(eid & Heo & Hvp & Heid_neq) | (Heo & Hvp)];
     subst eo; inverts Hvp;
     destruct Hveid as [(eid' & Heo' & Hvp') | (Heo' & Hvp')];
     inverts Heo'; inverts Hvp'; auto. }
  subst vp.
  destruct Hvp_ptr as [Hvp_null | (eid & Hvp_eid)];
  subst V_afteid.
  (* case1: p = NULL *)
   (* If (p ′ !=ₑ NULL)*)
  hoare forward.
  change (Int.notbool Int.one) with Int.zero.
  hoare unfold. tryfalse.
  instantiate(1:= Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.

   (* EXIT_CRITICAL *)
    eapply backward_rule1. 
    introv Hsat.
    eapply APthreadMutex_select_sn_ex_strong.
    eexists. exists (Z.to_nat (Int.unsigned posv)). eexists.
    exists (Vint32 vtp
             :: Vint32 vpro
                :: Vint32 vpcp
                   :: Vint32 vwq
                      :: Vint32 vcs
                         :: Vint32 vow :: Vint32 vrcnt :: Vint32 vtsk :: Vnull :: vmc :: nil).
    sep cancel Aarray_new.
    sep cancel Aarray_new.
    sep pauto.

   hoare forward prim.
   sep cancel Aier.
   sep cancel CapabilityInv.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep normal; sep eexists.
   sep cancel AMuxCap.
   sep pauto; eauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel AMqEIBs.
   sep cancel p_local.
   sep cancel APthreadMutex.
   sep cancel APthreadAttr.
   eauto.
   auto.
   pure_auto.

  assert (Hrv: V_ret = Vint32 Int.zero \/ V_ret <> Vint32 Int.zero) by tauto.
  destruct Hrv.
  2: { hoare abscsq.
        apply noabs_oslinv.
        eapply mutextimedlock_absimp_after_pend_succ_null_abt; eauto.
        can_change_aop_solver.
        apply absabort_rule.
      }
    subst.
    hoare abscsq.
    apply noabs_oslinv.
    eapply mutextimedlock_absimp_after_pend_succ_null; eauto.
    can_change_aop_solver.
    hoare forward.
   (* end of case1 *)
   (* case2:  p = Vptr eid *)
    destruct Hveid as [(vp & Hed & Hveid) | (_ & Hf)].
  2: { clear -Hf; inverts Hf. }
  inverts Hveid; subst eo.
  destruct vp as (vp_b & vp_i).
   unfold AECBList.
   hoare unfold.
   lets Hrmut: H2.
  unfold RH_ECBlk_EIBlk_Mux_P in H2.
  rename H2 into Heic.
  lets Hgete: Hget.
  eapply Heic in Hgete; eauto.
  destruct Hgete as (pip & o & wl & Hgete). 
  lets Fget_ectr: ECBList_P_get_ectr_some Hgete H3. 
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
  match goal with H: os_inv.id_addrval' (Vptr (?b, Int.zero)) OSPostEventTbl OS_EVENT = _ |- _ =>
  rename b into vp_b end.
  (* If (p ′ !=ₑ NULL) *)
  hoare forward.
  hoare unfold.
  (* assign efield (Pthread_Mutex ′ [pos ′]) mutex_owner *)
  hoare_assign_array_struct' (Int8u).
  {
    introv Hsat.
    eapply cast_rv_tint32_tint8.
    eapply bop_rv.
    sep_lifts_trms_in Hsat (Astruct (vp_b, Int.zero)).
    sep_get_rv_array_struct'.
    rewrite Hdiveq; eauto.
    simpl; auto.
    sep get rv.
    simpl; eauto.
    pure_auto.
    pure_auto.
    simpl; eauto.
   }
    (* end of assign *)
    change (Int.notbool Int.zero) with Int.one.
    hoare forward; hoare unfold;
    [idtac | destruct H2; tryfalse].

  hoare_lifts_trms_pre (Aop, absecblsid, absmutinfoid).
  assert (Hrv: V_ret = Vint32 Int.zero \/ V_ret <> Vint32 Int.zero) by tauto.
  destruct Hrv.
  2: { eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutextimedlock_absimp_after_pend_succ_ecb_abt; eauto.
        can_change_aop_solver.
       apply absinfer_eq.
        apply absabort_rule.
      }
    subst.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutextimedlock_absimp_after_pend_succ_ecb; eauto.
    can_change_aop_solver.
    apply absinfer_eq.
   (* EXIT_CRITICAL *)
  lets How_eq: Htmp H31.
  rewrite How_eq.
  eapply backward_rule1. 
  introv Hsat.
  eapply APthreadMutex_select_sn_ex_strong.
  eexists. exists (Z.to_nat (Int.unsigned posv)). eexists.
  exists (Vint32 vtp
             :: Vint32 vpro
                :: Vint32 vpcp
                   :: Vint32 vwq
                      :: Vint32 vcs
                         :: Vint32 (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) :: Vint32 vrcnt :: Vint32 vtsk :: Vptr (vp_b, Int.zero) :: vmc :: nil).
   sep cancel Aarray_new.
   sep cancel Aarray_new.
   sep pauto.
   clear -Hlen_minfo.
   rewrite <- Hlen_minfo.
   do 2 rewrite app_length.
   simpl length. auto.
   eapply new_array_type_vallist_match_compose_struct; eauto.

     hoare forward prim.
     sep cancel Aier.
     sep cancel CapabilityInv.
     unfold EvtInv.
     unfold AMuxEIBs.
     unfold AECBList.
     sep normal; sep eexists.
     sep cancel AMuxCap.
     sep pauto; eauto.
     trycancel.
     sep cancel ASemEIBs.
     sep cancel AMqEIBs.
     sep cancel p_local.
     sep cancel APthreadMutex.
     match goal with | |- _ |= evsllseg ?head _ _ _ ** _ =>
     eapply evsllseg_app;
     sep cancel (evsllseg head) end.
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
     sep cancel APthreadAttr.
     eauto.
     unfold V_OSEventListPtr; simpl ;auto.
     split; auto.
     struct_type_match_solver.
     eapply eibref_distinct_set_pos_muxeib_gen; eauto.
     eapply Q_ECB_P_set_mux_preserve_gen; eauto.
     eapply MUX_ECB_P_set_mux_preserve_gen; eauto.
     eapply SEM_ECB_P_set_mutex_preserve_gen; eauto.
     eapply RH_ECBlk_EIBlk_Mux_P_ptr_preserve; eauto.
     unfold is_mux. eauto.
     eapply MuxCapArray_P_hold; eauto.
     (* EIBMAarray_P *)
     assert (Hup: (Vint32 vtp
    :: Vint32 vpro
       :: Vint32 vpcp
          :: Vint32 vwq
             :: Vint32 vcs
                :: Vint32 (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                   :: Vint32 vrcnt :: Vint32 vtsk :: Vptr (vp_b, Int.zero) :: vmc ::nil) 
    = update_nth_val 5 (Vint32 vtp
             :: Vint32 vpro
                :: Vint32 vpcp
                   :: Vint32 vwq
                      :: Vint32 vcs
                         :: Vint32 vow
                            :: Vint32 vrcnt
                               :: Vint32 vtsk :: Vptr (vp_b, Int.zero) :: vmc :: nil) (Vint32 (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) ).
  { simpl; auto. }
  rewrite Hup.
  match goal with H: _ |= _ |- _ => rename H into Hlen_eq; lets Hsat: Hlen_eq end.
  sep_lifts_trms_in Hlen_eq (evsllseg).
  eapply evsllseg_list_len_eq in Hlen_eq.
  lets Hels: H3.
  eapply ecblist_p_decompose_new in Hels; eauto.
  destruct Hels as (els1 & els2 & Hels1 & Hels2 & Hej & Hlast_ptr).
  lets Hcp: Hels2.
  simpl in Hcp.
  destruct Hcp as (eid & Hed_eq & Hretbl & Hrpetbl & (ed & els' & eptr & Heptr_eq & Hejs & Hred & Hels2')).
  inverts Hed_eq.
  unfold V_OSEventListPtr in Heptr_eq; simpl in Heptr_eq. inverts Heptr_eq.
  lets Hgete': EcbMod.join_sig_get Hejs.
  eapply EcbMod.join_get_r in  Hgete'; eauto.
  unfold get in Hgete; unfold EcbMap in Hgete.
  rewrite Hgete in Hgete'. inverts Hgete'.
  match goal with H: RLH_ECBData_P ?v (absmutexsem pip o, wl) |- _ => destruct v end;
  (* destruct v'47; *) lets Hred': Hred; simpl in Hred'; tryfalse.
  destruct Hred' as (Hmatch & Hrecb).
   assert (Hed_eq: v = Vint32 i2 /\ v0 = x1).
   { unfold AEventData in Hsat.
      unfold V_OSEventPtr, V_OSEventCnt in *.
      simpl nth_val in *.
      sep split in Hsat. inverts H37. inverts H38. auto.
  }
  destruct Hed_eq as (Heq1 & Heq2); subst v; subst v0.
   clear Hsat.
  assert (How_cases: ((i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = $ OS_MUTEX_AVAILABLE /\ o = None) \/
                                                        (exists t op, o = Some (t, op) /\ (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = op)).
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
  destruct How_cases as [ (How & Ho) | (t & op & Ho & How)];
  subst o; rewrite How.
  eapply EIBMAarray_P_for_update_to_owner'_n; eauto.
  split; clear -H; int auto.
  eapply EIBMAarray_P_for_update_to_owner'_y; eauto.
  split; clear -H; int auto.
  clear -Hrecb.
  assert (How_eq': Some (t, op) = Some (t, op)) by auto.
  eapply Hrecb in How_eq'.
  destruct How_eq'; auto.
  (* end of EIBMAarray_P *)
  auto.
  Optimize Proof.
  Optimize Heap.
  pure_auto.
 hoare forward.
 Unshelve.
 exact 0%nat.
 exact 0%nat.
 exact 0%nat.
Qed.

Require Import part_pos_rgn_proof.

Lemma PthreadMutexLockProof:  
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api pthread_mutex_timedlock
              (mutextimedlock,(Tint32,Tptr pthread_mutex_t :: Tint16 :: nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api pthread_mutex_timedlock
              (mutextimedlock,(Tint32,Tptr pthread_mutex_t :: Tint16 :: nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api pthread_mutex_timedlock = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  do 17 (destruct v'; try apply absabort_rule).
  rename v'10 into newv1.
  rename v'11 into newv2.
  rename v'12 into er.
  rename i into tmv.
  rename v into V_pos.
  rename v0 into V_eid0.
  rename v1 into V_eid.
  rename v2 into V_ow.
  rename v3 into V_tp.
  rename v4 into V_curp.
  rename v5 into V_pcp.
  rename v6 into V_rcnt.
  rename v7 into V_pevt.
  rename v8 into V_err.
  rename v9 into V_afteid.
  rename v10 into V_ret.
  rename v11 into vr_temp_dom.
  rename v12 into vr_temp_num.
  rename v13 into vr_temp_dom'.
  rename v14 into vr_temp_num'.

  rename H1 into Htmv_range.
  rename H2 into H1.

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

   hoare forward.
   pure_auto.
   simpl.
   clear -H1. destruct H1; subst; auto. destruct H; subst; eauto.
   pure_auto.
   unfold retpost. introv Hsat.
   inverts Hsat.
   do 2 destruct H. simpl_sat H. simpljoin1. intro Hf. inv Hf.
   do 2 destruct H. simpl_sat H. simpljoin1. intro Hf. inv Hf.
   pure_auto.

   intros.
   destruct H.
   destruct H; try (sep pauto; instantiate (1:=init_lg); sep pauto).

   intros.
   sep pauto. instantiate (1:=init_lg). sep pauto.

   hoare unfold.
   eapply backward_rule1.
   intros.
   apply disj_split in H.
   eauto.
   eapply disj_rule;
   hoare unfold;
   inverts H2.

   assert (Hv: V_pos = Vint32 (Int.mone) \/ V_pos <> Vint32 (Int.mone)) by tauto.
  destruct Hv.  
  2: {
    hoare abscsq.
    apply noabs_oslinv.
    eapply mutextimedlock_absimp_muxerr_abt; eauto.
    destruct H. inverts H; auto.
    do 2 destruct H. inverts H; eauto.
    can_change_aop_solver.
    apply absabort_rule.
  }
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutextimedlock_absimp_muxerr_cons; eauto.
  destruct H. inverts H; auto.
  do 2 destruct H. inverts H; eauto.
  can_change_aop_solver.
  subst V_pos.

  hoare forward.
  hoare forward.

  hoare unfold.
  rewrite Int.eq_true in *.
  simpl in *.
  destruct H0; tryfalse.
  rewrite Int.eq_true.

  eapply backward_rule1.
  introv Hsat.
  apply adisj_elim in Hsat.
  destruct Hsat as [Hsat | Hsat].
  eauto.
  apply astar_comm in Hsat.
  apply astar_l_apure_elim in Hsat.
  destruct Hsat as (Hsat & _).
  simpl in Hsat; destruct Hsat; tryfalse.

  hoare unfold.
  change ($ -1) with Int.mone.
  assert (Hposv: Int.ltu Int.mone Int.zero = true \/ Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) Int.mone = true \/ Int.mone = $ (OS_USER_MAX_EVENTS / 3)).
  { clear -H1 Hrgn3 Hrgn4. int auto. }
  assert (Hrv: V_ret = Vint32 (Int.repr EINVAL) \/ V_ret <> Vint32 (Int.repr EINVAL)) by tauto.
  destruct Hrv.
  2: { hoare abscsq.
          apply noabs_oslinv.
          eapply mutextimedlock_absimp_poserr_abt; eauto.
          can_change_aop_solver.
          apply absabort_rule.
        }
   subst.
   hoare abscsq.
   apply noabs_oslinv.
   eapply mutextimedlock_absimp_poserr; eauto.
   can_change_aop_solver.

  hoare forward;
  try (rewrite Hchg);
  simpl;
  pure_auto.
  hoare forward.

  hoare forward.
  rewrite int_ltu_zero_eq_false.
  rewrite Hdiveq.
  hoare unfold.
  simpl in *.
  assert (Het: Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) Int.mone = true).
  { clear - Hrgn3 Hrgn4. int auto. }
  rewrite Het in H7.
  assert (Hmf: Int.eq Int.mone ($ (OS_USER_MAX_EVENTS / 3)) = false).
  { clear - Hrgn3 Hrgn4. int auto. }
  rewrite Hmf in H7.
  simpl in *.
  rewrite int_ltu_zero_eq_false in *.
  change (Int.ltu Int.zero Int.one) with true in *.
  simpl in *.
  change (Int.ltu Int.zero Int.one) with true in *.
  simpl in *.
  destruct H7; tryfalse.

  (* second branch: encrit; pos = *sem; excrit *)
  assert (Hposv: ~(exists i, V_pos = Vint32 i) \/ exists i, V_pos = Vint32 i) by tauto.
  destruct Hposv as [Hex | Hex].

  (* ~(exists i, V_pos = Vint32 i) *)
  hoare forward;
  change (Int.eq ($ 1) ($ 0)) with false.
  hoare unfold.
  simpl in H; tryfalse.
  hoare unfold.
  (* ENTER_CRITICAL;ₛ *)
  hoare forward prim.
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).

  unfold EvtInv.
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  rename v'41 into pbls.
  hoare_lifts_trms_pre (Aop, pblsid).
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply mutextimedlock_absimp_muxtex_pos_type_abt; eauto. 
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.
  instantiate(1:= Afalse).
  instantiate(1:= Afalse).
  simpl val_inj.
  eapply backward_rule1.
  introv Hsat.
  apply adisj_elim in Hsat.
  destruct Hsat as [Hsat | Hsat];
  eapply astar_l_afalse_elim; eauto.
  apply pfalse_rule.

  (* ~(exists i, V_pos = Vint32 i) *)
  destruct Hex as (posv & Hpv).
  subst.
   hoare forward;
  change (Int.eq ($ 1) ($ 0)) with false.
  hoare unfold.
  simpl in H; tryfalse.
  hoare unfold.
  (* ENTER_CRITICAL;ₛ *)
  hoare forward prim.
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).

  unfold EvtInv.
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_lifts_trms_pre (Aop, pblsid).
  match goal with
  | |- {| _, _, _, _, _, _ |} |- _ {{_ ** Hpbls ?abs ** _}} _ {{ _ }} =>
  rename abs into pbls end.
   assert (Hor: get pbls x = None \/ (exists posv, get pbls x = Some posv)).
  {
    destruct (get pbls x).
    right. eexists. eauto. 
    left. auto.
  }
  destruct Hor as [Hnone | Hsome].
  (* get pbls smadr = None *)
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mutextimedlock_absimp_muxtex_pos_none_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.
  (* exists posv, get pbls smadr = Some posv *)
  destruct Hsome as (pv & Hget).
  eapply backward_rule1.
  intros. 
  eapply pos_list_split_frm. 
  sep cancel APosblkList.
  eauto.
  eauto.
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_lifts_trms_pre (Aop, Alvarmapsto os_code_defs.pos).
  hoare forward.
  eapply assign_rule_lvar with (v2:=Vint32 pv). 
  split.
  intros.
  sep cancel (Alvarmapsto os_code_defs.pos).
  eauto.
  intro.
  auto.
  Optimize Proof.
  Optimize Heap.
  2: { instantiate (1:=long). eapply eq_int. auto. }
  2: { sep pauto. instantiate (1:=init_lg). sep cancel p_local. sep pauto. }
  unfold node.
  introv Hsat.
  sep normal in Hsat.
  destruct Hsat as (mux_blk & Hsat).
  ssplit_apure_in Hsat.
  destruct H0 as (Heq & Hmat).
  inverts Heq.
  unfold V_posblk_pos in *.
  apply nth_val_nth_val'_some_eq in H5.
  rewrite <- H5.
  eapply sem_rv; eauto.
  sep_get_rv.

  assert (Hposv: Vint32 posv <> Vint32 pv \/ Vint32 posv = Vint32 pv) by tauto.
  hoare_lifts_trms_pre (Aop, pblsid).
  destruct Hposv.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextimedlock_absimp_muxtex_pos_ex_abt; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.

  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextimedlock_absimp_muxtex_pos_cons; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  rewrite <- H0.

  (* preparation for excrit *)
  hoare_lifts_trms_pre ( RH_TCBList_ECBList_P).
  apply pure_split_rule'; introv H_RHTE.
  hoare_lifts_trms_pre (RH_CurTCB).
  apply pure_split_rule'; introv H_RHTCB.
  hoare unfold.
  eapply backward_rule1. 
  introv Hsat.
  eapply pos_sllseg_merge
    with (vll1:=v'49) (hd:=v'45) (vsem:= x) (pbls1:=v'53) (vl:=v'51)
         (hd':=v'52) (vll2:=v'50) (pbls2:=v'55) (posv:=pv) (pbls':=v'54) (pbls:=pbls).
  sep pauto. 
  eauto. 

  (* EXIT_CRITICAL *)
  hoare_lifts_trms_pre (Aop).
  hoare forward prim.
  sep cancel Aier.
  unfold EvtInv.
  unfold APosblkList.
  sep pauto; eauto.
  trycancel.
  sep cancel pos_sllseg.
  sep cancel AMuxEIBs.
  sep cancel ASemEIBs.
  sep cancel AMqEIBs.
  sep cancel p_local.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.
  auto.
  pure_auto.
  instantiate (1:= Afalse).
  eapply hoare_disj_afalseP_l_pre.
  simpl val_inj.
  hoare unfold.

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
         eapply mutextimedlock_absimp_poserr_abt; eauto.
         can_change_aop_solver.
         apply absabort_rule.
        }
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutextimedlock_absimp_poserr; eauto.
  can_change_aop_solver.
  hoare forward.

  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.

  (* new code about part_pos_rgn *)
   hoare_lifts_trms_pre (Aop, os_code_defs.pos, temp_dom, temp_num, Aisr, Aie, Ais, Acs, Aier, p_local, A_dom_lenv).
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply absinfer_pos_rgn_choice2_cons;eauto.
   can_change_aop_solver.
   eapply absinfer_eq.
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

  assert (Hposv_range: Int.ltu posv Int.zero = false /\ Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) posv = false /\ posv <> Int.repr (OS_USER_MAX_EVENTS / 3)).
  {
    change ($ 0) with Int.zero in *.
    rewrite Hdiveq in H0.
    destruct (Int.ltu posv Int.zero) eqn:eq1;
    destruct (Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) posv) eqn: eq2;
    destruct (Int.eq posv ($ (OS_USER_MAX_EVENTS / 3))) eqn: eq3;
    try (apply inteqeq in eq3; subst);
    simpl in *; auto;
    repeat (try change (Int.ltu Int.zero Int.zero) with false in *; 
                  try change (Int.ltu Int.zero Int.one) with true in *; simpl in *);
    try destruct H0;
    tryfalse.
    splits; try apply sem_lab.semacc_int_eq_false; auto.
  }
  clear H0.

  (* If (pthread_mutex_timedlock.abs_timeout ′ ==ₑ ′ 0
    ||ₑ pthread_mutex_timedlock.abs_timeout ′ >ₑ ′ 65535) *)
  hoare forward;
  try (change (Int16.max_unsigned) with 65535);
  simpl;
  pure_auto.
  hoare unfold.
  assert (Htmv_cond: Int.eq tmv Int.zero = true \/ Int.ltu ($ 65535) tmv = true).
  {
    change ($ 0) with Int.zero in *.
    destruct (Int.eq tmv Int.zero) eqn:eq1;
    destruct (Int.ltu ($ 65535) tmv) eqn: eq2;
    simpl in *; auto; tryfalse.
  }
  assert (Hrv: V_ret = Vint32(Int.repr EINVAL) \/ V_ret <> Vint32(Int.repr EINVAL)) by tauto.
  destruct Hrv.
  2: { hoare abscsq.
         apply noabs_oslinv.
         eapply mutextimedlock_absimp_timeout_abt_new; eauto.
         can_change_aop_solver.
         apply absabort_rule.
        }
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutextimedlock_absimp_timeout_err_new; eauto.
  can_change_aop_solver.
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.

   hoare unfold.
  assert (Htmv_range': Int.eq tmv Int.zero = false /\ Int.ltu ($ 65535) tmv = false).
  {
    change ($ 0) with Int.zero in *.
    destruct (Int.eq tmv Int.zero) eqn:eq1;
    destruct (Int.ltu ($ 65535) tmv) eqn: eq2;
    simpl in *;
    try change (Int.ltu Int.zero Int.zero) with false in *; 
    try change (Int.ltu Int.zero Int.one) with true in *; simpl in *;
    destruct H0; auto; tryfalse.
  }
  clear H0.

  (* first get p: ENTER_CRITICAL;ₛ p ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) pevent;ₛ EXIT_CRITICAL;ₛ*)
  hoare forward prim.
  hoare unfold.
  rename H8 into Htmv_neq.
  rename H9 into Htmv_lt.
  lets Hposv_neq: Int.eq_false H6.

  (* unfold EvtInv.
  hoare normal pre; hoare_ex_intro.
  hoare_assert_pure (length v'36 = (∘ (OS_USER_MAX_EVENTS / 3))).
  { get_hsat Hsat. sep_lifts_trms_in Hsat AMuxEIBs.
     eapply length_vll_apthrmux; eauto.  }
  eapply pure_split_rule'; introv Hlen_minfo.
  unfold AMuxEIBs.
  hoare normal pre; hoare_ex_intro.
  hoare_lifts_trms_pre ( R_Q_Data_P ).
  eapply pure_split_rule'; introv Hrqdata.
  hoare unfold. *)

   unfold EvtInv.
   hoare normal pre; hoare_ex_intro.
   unfold AMuxEIBs.
   hoare normal pre; hoare_ex_intro.
   hoare_lifts_trms_pre ( R_Q_Data_P ).
   eapply pure_split_rule'; introv Hrqdata.
   hoare_lifts_trms_pre (AMuxCap).
   match goal with
    | |- {| _, _ , _, _, _, _ |} |- _ {{ AMuxCap ?l ?vl ** _ }} _ {{ _ }} =>
   rename l into lmux; rename vl into muxcapvl end.
   hoare_lifts_trms_pre (MuxCapArray_P, length muxcapvl).
   eapply pure_split_rule'; introv Hmuxcap_vl.
   eapply pure_split_rule'; introv Hmuxcap_len.
   destruct lmux as (lmux_b & lmux_i).
   hoare_lifts_trms_pre APthreadMutex.
   match goal with
    | |- {| _ , _, _, _, _, _ |} |- _ {{ APthreadMutex _ ?vl ** _ }} _ {{ _ }} =>
       hoare_assert_pure (length vl = (∘ (OS_USER_MAX_EVENTS / 3)))
    end.
   { get_hsat Hsat. sep_lifts_trms_in Hsat APthreadMutex.
     eapply apthreadmutex_len_frm; eauto.  }
   eapply pure_split_rule'; introv Hlen_minfo.
   hoare unfold.

  hoare_lifts_trms_pre (Aop, APthreadMutex).
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
  Optimize Proof.
  Optimize Heap.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  eapply new_array_type_vallist_match_split1 in H10; eauto.
  simpljoin; auto.
  eapply eq_vptr; eauto.
  intros. eexists. sep cancel p_local. simpl; eauto.

  assert (Hlemu: Int.unsigned posv <= Int.max_unsigned).
  { clear -H Hrgn3 Hrgn4. int auto. }
  lets Hmls: muxb_corr H8 H19 H2 Hlemu. 
  destruct Hmls as (eo & ow & tp & rcnt & prot & pcp & wq & c & mc & Hget & Hmls).
  match goal with H: EIBMAarray_P _ (_ ++ ?vl :: _) _ _ |- _ => rename vl into mutvl end.
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
    eapply mutextimedlock_absimp_ecb_ptr_hold_abt''_new; eauto.
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
        eapply mutextimedlock_absimp_ecb_ptr_abt''_new; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
        }
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutextimedlock_absimp_ecb_ptr''_new; eauto.
   can_change_aop_solver.
   eapply absinfer_eq.
   (* EXIT_CRITICAL *)
   eapply backward_rule1. 
   introv Hsat.
   eapply APthreadMutex_select_sn_ex_strong.
   eexists. exists (Z.to_nat (Int.unsigned posv)). eexists.
   exists mutvl.
   sep cancel Aarray_new.
   sep cancel Aarray_new.
   sep pauto.

   hoare forward prim.
   sep cancel Aier.
   sep cancel CapabilityInv.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep normal; sep eexists.
   sep cancel AMuxCap.
   sep pauto; eauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel APthreadMutex.
   sep cancel AMqEIBs.
   sep cancel p_local.
   sep cancel APthreadAttr.
   eauto.
   auto.
   pure_auto.
  (* split the mutvl as mutvl = _ :: _ :: ... :: nil *)
  lets Hmut_vll: H10.
  rename H10 into Hmut_vl.
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
         subst V_eid0.
        assert (Hrv: V_ret = Vint32 (Int.repr EINVAL) \/ V_ret <> Vint32 (Int.repr EINVAL)) by tauto.
        destruct Hrv.
        2: { hoare abscsq.
               apply noabs_oslinv.
               eapply mutextimedlock_absimp_ecb_nullerr_abt; eauto.
               can_change_aop_solver.
               apply absabort_rule. }
        subst V_ret.
        (* If (p ′ ==ₑ NULL){RETURN ′ EINVAL};ₛ *)
        hoare forward.
        hoare unfold.
        hoare abscsq.
        apply noabs_oslinv.
        eapply mutextimedlock_absimp_ecb_nullerr; eauto.
        can_change_aop_solver.
        hoare forward.
        eapply hoare_disj_afalseP_l_pre.
        hoare unfold.
        destruct H10; tryfalse.
    }
  (* p == Vptr eid *)
  destruct Hveid as [(vp & Hed & Hveid) | (Hf & _)].
  2: { clear -Hf; inverts Hf. }
  inverts Hed; subst V_eid0.
  destruct vp as (vp_b & vp_i).
  (*p = Vptr (vp_b, vp_i) *)
  hoare forward.
  hoare unfold.
  tryfalse.
  instantiate (1:= Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  clear -Htmv_range H1 H3 H4 H H2 H5 H6 Htmv_neq Htmv_lt Hposv_neq Hlemu Hrgn3 Hrgn4 Hdiveq.
   (* second get p: ENTER_CRITICAL;ₛ p ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) pevent;ₛ EXIT_CRITICAL;ₛ*)
  hoare forward prim.
  hoare unfold.

   unfold EvtInv.
   hoare normal pre; hoare_ex_intro.
   unfold AMuxEIBs.
   hoare normal pre; hoare_ex_intro.
   hoare_lifts_trms_pre ( R_Q_Data_P ).
   eapply pure_split_rule'; introv Hrqdata.
   hoare_lifts_trms_pre (AMuxCap).
   match goal with
    | |- {| _, _ , _, _, _, _ |} |- _ {{ AMuxCap ?l ?vl ** _ }} _ {{ _ }} =>
   rename l into lmux; rename vl into muxcapvl end.
   hoare_lifts_trms_pre (MuxCapArray_P, length muxcapvl).
   eapply pure_split_rule'; introv Hmuxcap_vl.
   eapply pure_split_rule'; introv Hmuxcap_len.
   destruct lmux as (lmux_b & lmux_i).
   hoare_lifts_trms_pre APthreadMutex.
   match goal with
    | |- {| _ , _, _, _, _, _ |} |- _ {{ APthreadMutex _ ?vl ** _ }} _ {{ _ }} =>
       hoare_assert_pure (length vl = (∘ (OS_USER_MAX_EVENTS / 3)))
    end.
   { get_hsat Hsat. sep_lifts_trms_in Hsat APthreadMutex.
     eapply apthreadmutex_len_frm; eauto.  }
   eapply pure_split_rule'; introv Hlen_minfo.
   hoare unfold.

  hoare_lifts_trms_pre (Aop, APthreadMutex).
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
  Optimize Proof.
  Optimize Heap.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  eapply new_array_type_vallist_match_split1 in H10; eauto.
  simpljoin; auto.
  eapply eq_vptr; eauto.
  intros. eexists. sep cancel p_local. simpl; eauto.

  lets Hmls: muxb_corr H8 H19 H2 Hlemu. 
  destruct Hmls as (eo & ow & tp & rcnt & prot & pcp & wq & c & mc & Hget & Hmls).
  match goal with H: EIBMAarray_P _ (_ ++ ?vl :: _) _ _ |- _ => rename vl into mutvl end.
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
    eapply mutextimedlock_absimp_ecb_ptr_hold_abt; eauto.
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
        eapply mutextimedlock_absimp_ecb_ptr_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
        }
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutextimedlock_absimp_ecb_ptr; eauto.
   can_change_aop_solver.
   eapply absinfer_eq.

  (* split the mutvl as mutvl = _ :: _ :: ... :: nil *)
  lets Hmut_vll: H10.
  rename H10 into Hmut_vl.
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
        2: { eapply abscsq_rule.
               apply noabs_oslinv.
               eapply mutextimedlock_absimp_ecb_nullerr_abt; eauto.
               can_change_aop_solver.
               eapply absinfer_eq.
               apply absabort_rule. }
        subst V_ret.
        (* IF (p ′ !=ₑ NULL){}ELSE{ EXIT_CRITICAL;ₛ RETURN ′ EINVAL};ₛ *)
       hoare forward.
        hoare unfold.
        change (Int.notbool Int.one) with Int.zero in H10; tryfalse.
        hoare_split_pure_all.
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutextimedlock_absimp_ecb_nullerr; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        (* pre condition before excrt *)
        eapply backward_rule1. 
        introv Hsat.
        eapply APthreadMutex_select_sn_ex_strong.
        eexists. exists (Z.to_nat (Int.unsigned posv)). eexists.
        exists (Vint32 vtp
             :: Vint32 vpro
                :: Vint32 vpcp
                   :: Vint32 vwq
                      :: Vint32 vcs
                         :: Vint32 vow :: Vint32 vrcnt :: Vint32 vtsk :: Vnull :: vmc :: nil).
        sep cancel Aarray_new.
        sep cancel Aarray_new.
        sep pauto.
        (* EXIT_CRITICAL *)
        hoare forward prim.
        sep cancel Aier.
        sep cancel CapabilityInv.
        unfold EvtInv.
        unfold AMuxEIBs.
        sep normal; sep eexists.
        sep cancel AMuxCap.
        sep pauto; eauto.
        trycancel.
        sep cancel ASemEIBs.
        sep cancel AMqEIBs.
        sep cancel p_local.
        sep cancel APthreadMutex.
        sep cancel APthreadAttr.
        eauto.
        auto.
        pure_auto.
        (* RETURN ′ EINVAL *)
        hoare forward.
        instantiate (1:= Afalse).
        eapply hoare_disj_afalseP_l_pre.
        hoare unfold.
        apply pfalse_rule.
    }
  (* p == Vptr eid *)
  destruct Hveid as [(vp & Hed & Hveid) | (Hf & _)].
  2: { clear -Hf; inverts Hf. }
  inverts Hed; subst V_eid.
  destruct vp as (vp_b1 & vp_i1).
  (*p = Vptr (vp_b1, vp_i1) *)
   unfold AECBList.
   hoare unfold.
   lets Hrmut: H9.
  unfold RH_ECBlk_EIBlk_Mux_P in H9.
  rename H9 into Heic.
  lets Hgete: Hget.
  eapply Heic in Hgete; eauto.
  destruct Hgete as (pip & o & wl & Hgete). 
  lets Fget_ectr: ECBList_P_get_ectr_some Hgete H10.
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
  inverts H33.
  match goal with H: os_inv.id_addrval' (Vptr (?b, Int.zero)) OSPostEventTbl OS_EVENT = Some ?l |- _ =>
  rename b into vp_b1; rename l into lpetbl end.

  hoare forward.
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
     simpl; auto.
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
  hoare unfold.
  destruct H9; tryfalse.
  instantiate(1:= Afalse).
  eapply hoare_disj_afalseP_r_pre.
  hoare unfold.
  match goal with H: ECBList_P _ _ (?vl1 ++ _ ) (?vl2 ++ _ ) _ _ |- _ =>
   hoare_assert_pure (length vl1 = length vl2) end.
  { get_hsat Hsat. sep_lifts_trms_in Hsat (evsllseg).
     eapply evsllseg_list_len_eq in Hsat; auto. }
  eapply pure_split_rule'; intro Heqlen.
  lets Hels: H10.
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
  match goal with H: RLH_ECBData_P ?v (absmutexsem _ _, _) |- _ => destruct v end;
  lets Hred': Hred; simpl in Hred'; tryfalse.
  destruct Hred' as (Hmatch & Hrecb).
    hoare_assert_pure (v = Vint32 i2 /\ v0 = x1).
   { unfold AEventData in H33.
      unfold V_OSEventPtr, V_OSEventCnt in *.
      simpl nth_val in *.
      sep split in H33. inverts H43. inverts H44. auto.
  }
  apply pure_split_rule'; introv Hed_eq.
  destruct Hed_eq as (Heq1 & Heq2); subst v; subst v0.
  (* i1 -> i2 *)
  assert (How_cases: ((i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = $ OS_MUTEX_AVAILABLE /\ o = None) \/
                                                        (exists t op, o = Some (t, op) /\ (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = op)).
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
  assert (Hvow: V_ow = Vint32 (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) \/ V_ow <> Vint32 (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) by tauto.
  destruct Hvow.
  2: { eapply abscsq_rule.
         apply noabs_oslinv.
         eapply mutextimedlock_absimp_owner_abt; eauto.
         can_change_aop_solver.
         eapply absinfer_eq.
         apply absabort_rule. }
  subst V_ow.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextimedlock_absimp_owner; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  lets How_eq: Htmp H38.
  rewrite How_eq.
  (* EXIT_CRITICAL;ₛ *)
  (* pre condition before excrt *)
   eapply backward_rule1. 
   introv Hsat.
   eapply APthreadMutex_select_sn_ex_strong.
   eexists. exists (Z.to_nat (Int.unsigned posv)). eexists.
   exists (Vint32 vtp
             :: Vint32 vpro
                :: Vint32 vpcp
                   :: Vint32 vwq
                      :: Vint32 vcs
                         :: Vint32 vow :: Vint32 vrcnt :: Vint32 vtsk :: Vptr (vp_b1, Int.zero) :: vmc :: nil).
   sep cancel Aarray_new.
   sep cancel Aarray_new.
   sep pauto.

     hoare forward prim.
     sep cancel Aier.
     sep cancel CapabilityInv.
     unfold EvtInv.
     unfold AMuxEIBs.
     unfold AECBList.
     sep normal; sep eexists.
     sep cancel AMuxCap.
     sep pauto; eauto.
     trycancel.
     sep cancel ASemEIBs.
     sep cancel AMqEIBs.
     sep cancel p_local.
     sep cancel APthreadMutex.
     eapply evsllseg_app.
     sep cancel (evsllseg).
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
     sep cancel APthreadAttr.
     eauto.
     unfold V_OSEventListPtr; simpl ;auto.
     split; auto.
     struct_type_match_solver.
     auto.
  Optimize Proof.
  Optimize Heap.
     pure_auto.
     lets How_range: postintlemma3 i2.
     (* get type:  ENTER_CRITICAL;ₛ ty ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) mutex_type;ₛ EXIT_CRITICAL;ₛ *)
     clear -Htmv_range H1 H3 H4 H H2 H5 H6 Htmv_neq Htmv_lt Hposv_neq Hlemu How_range Hrgn3 Hrgn4 Hdiveq.
     (* ENTER_CRITICAL;ₛ *)
     hoare forward prim.
     hoare unfold.
     (* ty ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) mutex_type;ₛ *)
     unfold EvtInv.
     hoare normal pre; hoare_ex_intro.
     unfold AMuxEIBs.
     hoare normal pre; hoare_ex_intro.
     hoare_lifts_trms_pre ( R_Q_Data_P ).
     eapply pure_split_rule'; introv Hrqdata.
     hoare_lifts_trms_pre (AMuxCap).
     match goal with
      | |- {| _, _ , _, _, _, _ |} |- _ {{ AMuxCap ?l ?vl ** _ }} _ {{ _ }} =>
     rename l into lmux; rename vl into muxcapvl end.
     hoare_lifts_trms_pre (MuxCapArray_P, length muxcapvl).
     eapply pure_split_rule'; introv Hmuxcap_vl.
     eapply pure_split_rule'; introv Hmuxcap_len.
     destruct lmux as (lmux_b & lmux_i).
     hoare_lifts_trms_pre APthreadMutex.
     match goal with
      | |- {| _ , _, _, _, _, _ |} |- _ {{ APthreadMutex _ ?vl ** _ }} _ {{ _ }} =>
         hoare_assert_pure (length vl = (∘ (OS_USER_MAX_EVENTS / 3)))
      end.
     { get_hsat Hsat. sep_lifts_trms_in Hsat APthreadMutex.
       eapply apthreadmutex_len_frm; eauto.  }
     eapply pure_split_rule'; introv Hlen_minfo.
     hoare unfold.

     hoare_lifts_trms_pre (Aop, APthreadMutex).
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
     split; introv Hsat. sep cancel (Alvarmapsto ty). eauto.
     sep auto.
     sep_get_rv_array_struct.
     rewrite Hdiveq; eauto.
     rewrite Hdiveq; eauto.
     eapply new_array_type_vallist_match_split1 in H10; eauto.
     simpljoin; auto.
     eapply eq_int; auto.
     intros. eexists. sep cancel p_local. simpl; eauto.

  lets Hmls: muxb_corr H8 H19 H2 Hlemu. 
  destruct Hmls as (eo & ow & tp & rcnt & prot & pcp & wq & c & mc & Hget & Hmls).
  match goal with H: EIBMAarray_P _ (_ ++ ?vl :: _) _ _ |- _ => rename vl into mutvl end.
  assert (Htp_cases: 
           (Int.eq tp ( $ PTHREAD_MUTEX_NORMAL) = false /\
            Int.eq tp ( $ PTHREAD_MUTEX_ERRORCHECK) = false /\
            Int.eq tp ( $ PTHREAD_MUTEX_RECURSIVE) = false) \/
           tp = $ PTHREAD_MUTEX_NORMAL \/
        (tp = $ PTHREAD_MUTEX_ERRORCHECK \/
        tp = $ PTHREAD_MUTEX_RECURSIVE) 
         ). 
  {  clear. 
     destruct (Int.eq tp ( $ PTHREAD_MUTEX_NORMAL)) eqn: eq1;
     destruct (Int.eq tp ( $ PTHREAD_MUTEX_ERRORCHECK)) eqn: eq2;
     destruct (Int.eq tp ( $ PTHREAD_MUTEX_RECURSIVE)) eqn: eq3;
     try eapply inteqeq in eq1; try eapply inteqeq in eq2; try eapply inteqeq in eq3;
     try subst tp; tryfalse; auto.
   }
  destruct Hmls as (_ & _ & Hvtp_eq & _).
  unfold V_OSMUXINFOType in Hvtp_eq.
  apply nth_val_nth_val'_some_eq in Hvtp_eq.
  hoare_lifts_trms_pre (Aop, absmutinfoid).
  assert (Hvtp: V_tp = Vint32 tp \/ V_tp <> Vint32 tp) by tauto.
  destruct Hvtp.
  2: { eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutextimedlock_absimp_type_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
       }
  subst V_tp.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextimedlock_absimp_type; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  (* EXIT_CRITICAL *)
  eapply backward_rule1. 
  introv Hsat.
  eapply APthreadMutex_select_sn_ex_strong.
  eexists. exists (Z.to_nat (Int.unsigned posv)). eexists.
  exists mutvl.
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep pauto.

   hoare forward prim.
   sep cancel Aier.
   sep cancel CapabilityInv.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep normal; sep eexists.
   sep cancel AMuxCap.
   sep pauto; eauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel AMqEIBs.
   sep cancel p_local.
   sep cancel APthreadMutex.
   sep cancel APthreadAttr.
   eauto.
   auto.
   pure_auto.
  (* split the mutvl as mutvl = _ :: _ :: ... :: nil *)
  lets Hmut_vll: H10.
  rename H10 into Hmut_vl.
  eapply new_array_type_vallist_match_split1 in Hmut_vl; eauto.
  destruct Hmut_vl as (_ & _ & Hmut_vl).
  lets Hmut_vl_eq: struct_type_vallist_match_mutex_info_t_imp Hmut_vl.
  destruct Hmut_vl_eq as (vtp & vpro & vpcp & vwq & vcs & vow & vrcnt & vtsk & vp & vmc & Hmut_vl_eq & Hvp_ptr).
  subst mutvl.
  simpl nth_val' in Hvtp_eq. inverts Hvtp_eq.
  simpl nth_val'.

  destruct Htp_cases as [Hdef | Htp_cases].
  (*case1: switch defalut, tp <> PTHREAD_MUTEX_NORMAL /\
                 tp <> PTHREAD_MUTEX_ERRORCHECK /\ tp <> PTHREAD_MUTEX_RECURSIVE*)
  destruct Hdef as (Hfnor & Hfchk & Hfrec).
  assert (Hrv: V_ret = Vint32 (Int.repr EINVAL) \/ V_ret <> Vint32 (Int.repr EINVAL)) by tauto.
  destruct Hrv.
  2: { hoare abscsq.
         apply noabs_oslinv.
         eapply mutextimedlock_absimp_typeerr_abt; eauto.
         can_change_aop_solver.
         apply absabort_rule. }
   subst V_ret.
   hoare abscsq.
   apply noabs_oslinv.
   eapply mutextimedlock_absimp_typeerr; eauto.
   can_change_aop_solver.
   hoare forward;
   try pure_auto.
   hoare unfold.
   hoare forward.
   eapply hoare_disj_afalseP_l_pre.
   rewrite Hfnor,Hfchk,Hfrec.
   hoare unfold.
   simpl in H10.
   repeat (change (Int.notbool Int.zero) with Int.one in H10 ;
                 change (Int.ltu Int.zero Int.one) with true in H10; simpl in H10).
  destruct H10; tryfalse.
  (* end of case1 *)
  (* tp = PTHREAD_MUTEX_NORMAL \/
      tp = PTHREAD_MUTEX_ERRORCHECK \/
      tp = PTHREAD_MUTEX_RECURSIVE *)
  assert(Htp_if_false1:  Int.eq tp ( $ PTHREAD_MUTEX_NORMAL) = true \/
                                        Int.eq tp ( $ PTHREAD_MUTEX_ERRORCHECK) = true \/
                                        Int.eq tp ( $ PTHREAD_MUTEX_RECURSIVE) = true).
 { clear -Htp_cases.
    destruct Htp_cases as [Hc1 | [Hc2 | Hc3]];
    [left | right; left | right; right]; subst; rewrite Int.eq_true; auto.
  }
  hoare forward; try pure_auto.
  clear -Htp_if_false1; hoare unfold.
  false.
  destruct (Int.eq tp ($ PTHREAD_MUTEX_NORMAL)) eqn: eq1;
  destruct (Int.eq tp ($ PTHREAD_MUTEX_ERRORCHECK)) eqn: eq2;
  destruct (Int.eq tp ($ PTHREAD_MUTEX_RECURSIVE)) eqn: eq3; 
  tryfalse; simpl in H10;
  repeat (try change (Int.notbool Int.zero) with Int.one in H10 ;
                 try change (Int.notbool Int.one) with Int.zero in H10 ;
                 try change (Int.ltu Int.zero Int.one) with true in H10;
                 try change (Int.ltu Int.zero Int.zero) with false in H10; simpl in H10);
  tryfalse.
  destruct Htp_if_false1 as [Hc | [Hc | Hc]]; tryfalse.
  instantiate (1:= Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  clear H10.
  (* case2: tp =  $ PTHREAD_MUTEX_NORMAL *)
  destruct Htp_cases as [Htp_nor | [Htp_chk | Htp_rec]];
  [ assert (Htp_if_false2: Int.eq tp  ($ PTHREAD_MUTEX_ERRORCHECK) = false
                                        /\ Int.eq tp  ($ PTHREAD_MUTEX_RECURSIVE) = false)
   by (subst tp; clear -H;
    unfold PTHREAD_MUTEX_NORMAL,PTHREAD_MUTEX_ERRORCHECK,PTHREAD_MUTEX_RECURSIVE;
    int auto) |
   assert (Htp_if_false2: Int.eq tp  ($ PTHREAD_MUTEX_ERRORCHECK) = true
                                        /\ Int.eq tp  ($ PTHREAD_MUTEX_RECURSIVE) = false)
   by (subst tp; clear -H;
    unfold PTHREAD_MUTEX_NORMAL,PTHREAD_MUTEX_ERRORCHECK,PTHREAD_MUTEX_RECURSIVE;
    int auto) |
   assert (Htp_if_false2: Int.eq tp  ($ PTHREAD_MUTEX_ERRORCHECK) = false
                                        /\ Int.eq tp  ($ PTHREAD_MUTEX_RECURSIVE) = true)
   by (subst tp; clear -H;
    unfold PTHREAD_MUTEX_NORMAL,PTHREAD_MUTEX_ERRORCHECK,PTHREAD_MUTEX_RECURSIVE;
    int auto) ]; clear Htp_if_false1;
    destruct Htp_if_false2 as (Htp_if1 & Htp_if2); subst tp.
   hoare forward; rewrite Htp_if1; simpl val_inj.
   hoare unfold; tryfalse.
   instantiate(1:= Afalse).
   eapply hoare_disj_afalseP_l_pre.
   hoare unfold.
   hoare forward; rewrite Htp_if2; simpl val_inj.
   hoare unfold; tryfalse.
   instantiate(1:= Afalse).
   eapply hoare_disj_afalseP_l_pre.
   hoare unfold.
   hoare abscsq.
   apply noabs_oslinv.
   eapply mutextimedlock_absimp_type_normal; eauto.
   can_change_aop_solver.
   (* need PartProof Lemma *)
   eapply backward_rule1;
  [idtac | eapply PthreadMutexLockPartProof; eauto].
  introv Hsat.
  sep cancel Aier.
  sep pauto.
  rewrite Hdiveq; eauto.

    (* cases3:  tp =  $ PTHREAD_MUTEX_ERRORCHECK *)
    hoare forward.
    instantiate (1:= Afalse \\//
        ( <|| mutextimedlock_type_deadlk
         (|V$ PTHREAD_MUTEX_ERRORCHECK
           :: Vint32 (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
              :: V_curp :: V_pcp :: V_ret :: nil|)
         ?? mutextimedlock_recurcnt (|Vint32 posv :: V_rcnt :: nil|);;
            (mutextimedlock_type_recur_incre_one
             (|Vint32 posv
               :: V$ PTHREAD_MUTEX_ERRORCHECK
                  :: Vint32 (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                     :: V_curp :: V_pcp :: V_rcnt :: V_ret :: nil|)
             ?? mutextimedlock_type_recur_again
                (|V$ PTHREAD_MUTEX_ERRORCHECK
                  :: Vint32 (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                     :: V_curp :: V_pcp :: V_rcnt :: V_ret :: nil|))
            ?? (mutextimedlock_ecb_ptr (| Vint32 posv :: V_pevt :: nil |) ;;
                   mutextimedlock_set_evloc_ptr (| V_pevt :: nil |);; 
             spec_code_cons (mutexpend (V_pevt :: (Vint32 tmv) :: V_err :: nil))
             (mutextimedlock_set_evloc_ptr (| Vnull :: nil |);; 
               (mutextimedlock_after_pend_timeout (| V_err :: V_ret :: nil |) ??
                 mutextimedlock_after_pend_fail (| V_err :: V_ret :: nil |) ??
                    (mutextimedlock_ecb_ptr (| Vint32 posv :: V_afteid :: nil |) ;;
                            (mutextimedlock_after_pend_succ_null (| V_err :: V_afteid :: V_ret :: nil |) ??
                              mutextimedlock_after_pend_succ_ecb (| V_err :: V_afteid :: Vint32 posv :: V_ret :: nil |)))))) ||>  **
         Aisr empisr **
         Aie true **
         Ais nil **
         Acs nil **
         Aier v'11 **
         p_local OSLInv tid init_lg **
         LV os_code_defs.pip @ long |-> V_pcp **
         LV cpr @ char_t |-> V_curp **
         LV ty @ long |-> (V$ PTHREAD_MUTEX_ERRORCHECK) **
         LV muxowner @ char_t |-> Vint32 (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
         LV p @ OS_EVENT ∗ |-> Vptr (vp_b1, Int.zero) **
         LV os_code_defs.pos @ long |-> Vint32 posv **
         LV os_code_defs.x @ char_t |-> (V$ 1) **
         LV r @ long |-> v'7 **
         LV z @ char_t |-> v'3 **
         LV err @ char_t |-> v'0 **
         LV os_code_defs.abs_timeout @ Int16u |-> Vint32 tmv **
         LV mutex @ (long) ∗ |-> Vptr x **
         LV temp_num @ char_t |-> vtemp_dom **
         LV temp_dom @ char_t |-> vtemp_num **
         A_dom_lenv
           ((os_code_defs.abs_timeout, Int16u)
            :: (mutex, (long) ∗)
            :: (err, char_t)
               :: (os_code_defs.pos, long)
                  :: (os_code_defs.x, char_t)
                     :: (z, char_t)
                        :: (muxowner, char_t)
                           :: (ty, long)
                              :: (os_code_defs.pip, long)
                                 :: (r, long)
                                    :: (cpr, char_t) :: (p, OS_EVENT ∗)
                                      :: (temp_dom, char_t) :: (temp_num, char_t) :: nil)) **
        [| Vint32 (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <> V_curp /\
            V_pcp <> V_curp |] ).
    hoare unfold.
     clear H10 H18 H22.
    (* get curprio: ENTER_CRITICAL;ₛ cpr ′ =ₑ OSTCBCur ′ → OSTCBPrio;ₛ EXIT_CRITICAL;ₛ *)
    hoare forward prim.
    hoare unfold.
    (* cpr ′ =ₑ OSTCBCur ′ → OSTCBPrio *)
    hoare forward.
    struct_type_match_solver.
    unfold EvtInv.
    hoare unfold.
    rename i4 into curp.
    lets Hget_ct: Mbox_common.TCBListP_head_in_tcb H29.
    destruct Hget_ct as (cst & sus & Hget_ct).
    eapply TcbMod.join_get_r in Hget_ct; eauto.
    hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).
    assert (Hvcp: V_curp = Vint32 curp \/ V_curp <> Vint32 curp) by tauto.
    destruct Hvcp.
    2: { eapply abscsq_rule.
           apply noabs_oslinv.
           eapply mutextimedlock_absimp_curprio_abt; eauto.
           can_change_aop_solver.
           eapply absinfer_eq.
           apply absabort_rule.
         }
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutextimedlock_absimp_curprio; eauto.
   can_change_aop_solver.
   eapply absinfer_eq.
   subst V_curp.
   rename H37 into Hcurp_range.
   (* EXIT_CRITICAL *)
   hoare forward prim.
   sep cancel Aier.
   sep cancel CapabilityInv.
   unfold EvtInv.
   sep cancel tcbdllflag.
   sep cancel p_local.
   unfold AOSTCBList.
   unfold tcbdllseg.
   unfold V_OSTCBPrev,V_OSTCBNext.
   sep pauto; eauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel AMuxEIBs.
   sep cancel AMqEIBs.
   match goal with | |- _ |= dllseg ?head _ _ _ _ _ _ _ ** _ => sep cancel (dllseg head) end.
   simpl dllseg.
   unfold node.
   sep pauto; try splits; eauto.
   sep cancel Astruct.
   sep cancel dllseg.
   sep cancel APthreadAttr.
   eauto.
   struct_type_match_solver.
   auto.
  Optimize Proof.
  Optimize Heap.
   pure_auto.
   (* get prio_ceiling: ENTER_CRITICAL;ₛ pip ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) prio_ceiling;ₛ EXIT_CRITICAL;ₛ *)
   hoare forward prim.
   hoare unfold.
   (* pip ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) prio_ceiling *)
   clear H0 H7 Hmut_vl Hmut_vll.

   unfold EvtInv.
   hoare normal pre; hoare_ex_intro.
   unfold AMuxEIBs.
   hoare normal pre; hoare_ex_intro.
   hoare_lifts_trms_pre ( R_Q_Data_P ).
   eapply pure_split_rule'; introv Hrqdata'.
   hoare_lifts_trms_pre (AMuxCap).
   match goal with
    | |- {| _, _ , _, _, _, _ |} |- _ {{ AMuxCap ?l ?vl ** _ }} _ {{ _ }} =>
   rename l into lmux; rename vl into muxcapvl' end.
   hoare_lifts_trms_pre (MuxCapArray_P, length muxcapvl').
   eapply pure_split_rule'; introv Hmuxcap_vl'.
   eapply pure_split_rule'; introv Hmuxcap_len'.
   destruct lmux as (lmux_b' & lmux_i').
   hoare_lifts_trms_pre APthreadMutex.
   match goal with
    | |- {| _ , _, _, _, _, _ |} |- _ {{ APthreadMutex _ ?vl ** _ }} _ {{ _ }} =>
       hoare_assert_pure (length vl = (∘ (OS_USER_MAX_EVENTS / 3)))
    end.
   { get_hsat Hsat. sep_lifts_trms_in Hsat APthreadMutex.
     eapply apthreadmutex_len_frm; eauto.  }
   eapply pure_split_rule'; introv Hlen_minfo'.
   hoare unfold.

   hoare_lifts_trms_pre (Aop, APthreadMutex).
   eapply backward_rule1.
   introv Hsat.
   eapply APthreadMutex_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned posv)).
   sep cancel APthreadMutex.
   eauto.
   rewrite Hlen_minfo'.
   eapply ge_ne_lt_rgn; eauto.
   rewrite Hdiveq.
   apply Intlt_false_is_Zge; auto.
   rewrite Hdiveq; eauto.

   hoare unfold.
   hoare normal pre.

   hoare_lifts_trms_pre (Aop).
   hoare forward.
   eapply assign_rule_lvar.
   split; introv Hsat. sep cancel (Alvarmapsto os_code_defs.pip). eauto.
   sep auto.
   sep_get_rv_array_struct.
   rewrite Hdiveq; eauto.
   rewrite Hdiveq; eauto.
   eapply new_array_type_vallist_match_split1 in H47; eauto.
   simpljoin; auto.
   eapply eq_int; auto.
   intros. eexists. sep cancel p_local. simpl; eauto.

  lets Hmls: muxb_corr H0 H56 H2 Hlemu.
  destruct Hmls as (eo' & ow' & tp' & rcnt' & prot' & pcp' & wq' & c' & mc' & Hget' & Hmls).
  match goal with H: EIBMAarray_P _ (_ ++ ?vl :: _) _ _ |- _ => rename vl into mutvl end.
  destruct Hmls as (_ & _ & _ & _ & Hvpcp_eq & _).
   unfold V_OSMUXINFOPrio_ceiling in Hvpcp_eq.
   apply nth_val_nth_val'_some_eq in Hvpcp_eq.
   hoare_lifts_trms_pre (Aop, absmutinfoid).
  assert (Hvpcp: V_pcp = Vint32 pcp' \/ V_pcp <> Vint32 pcp') by tauto.
  destruct Hvpcp.
  2: { eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutextimedlock_absimp_prioceiling_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
       }
  subst V_pcp.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextimedlock_absimp_prioceiling; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  rewrite Hvpcp_eq.
   (* EXIT_CRITICAL *)
   eapply backward_rule1. 
   introv Hsat.
   eapply APthreadMutex_select_sn_ex_strong.
   eexists. exists (Z.to_nat (Int.unsigned posv)). eexists.
   exists mutvl.
   sep cancel Aarray_new.
   sep cancel Aarray_new.
   sep pauto.

   hoare forward prim.
   sep cancel Aier.
   sep cancel CapabilityInv.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep normal; sep eexists.
   sep cancel AMuxCap.
   sep pauto; eauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel AMqEIBs.
   sep cancel p_local.
   sep cancel APthreadMutex.
   sep cancel APthreadAttr.
   eauto.
   auto.
   pure_auto.
  (* split the mutvl as mutvl = _ :: _ :: ... :: nil *)
  lets Hmut_vll: H47.
  rename H47 into Hmut_vl.
  eapply new_array_type_vallist_match_split1 in Hmut_vl; eauto.
  destruct Hmut_vl as (_ & _ & Hmut_vl).
  lets Hmut_vl_eq: struct_type_vallist_match_mutex_info_t_imp Hmut_vl.
  destruct Hmut_vl_eq as (vtp' & vpro' & vpcp' & vwq' & vcs' & vow' & vrcnt' & vtsk' & vp' & vmc' & Hmut_vl_eq & Hvp_ptr').
  subst mutvl.
  simpl nth_val' in Hvpcp_eq. inverts Hvpcp_eq.
  simpl nth_val'.
  (* If (muxowner ′ ==ₑ cpr ′ ||ₑ os_code_defs.pip ′ ==ₑ cpr ′){RETURN ′ EDEADLK} *)
  hoare forward.
  clear -How_range. pure_auto.
  clear -Hcurp_range. pure_auto.
  clear -H; pure_auto.
  clear -Hcurp_range; pure_auto.
  clear -H; pure_auto.
  clear -H; pure_auto.
 hoare unfold.
 assert(His_owner: Int.eq (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) curp = true \/ Int.eq pcp' curp = true).
 { clear -H47.
    destruct (Int.eq (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) curp) eqn: eq1;
    destruct (Int.eq pcp' curp) eqn: eq2;
    simpl in H47; tryfalse; auto.
 }
 clear H47 H55 H59.
  assert (Hrv: V_ret = Vint32 (Int.repr EDEADLK) \/ V_ret <> Vint32 (Int.repr EDEADLK)) by tauto.
  destruct Hrv.
  2: { hoare abscsq.
         apply noabs_oslinv.
         eapply mutextimedlock_absimp_type_deadlk_abt; eauto.
         can_change_aop_solver.
         apply absabort_rule. }
   subst V_ret.
   hoare abscsq.
   apply noabs_oslinv.
   eapply mutextimedlock_absimp_type_deadlk; eauto.
   can_change_aop_solver.
   hoare forward.
   eapply adisj_intro.
   destruct H47; [left | right].
   eapply astar_l_afalse_elim; eauto.
   sep cancel Aier.
   sep pauto.
   clear -H55.
   destruct (Int.eq (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) curp) eqn: eq1;
   destruct (Int.eq pcp' curp) eqn: eq2;
   simpl in *;
   try change (Int.ltu Int.zero Int.one) with true in *;
   try change (Int.ltu Int.zero Int.zero) with false in *;
   simpl in *; (try destruct H55; tryfalse).
   eapply sem_lab.semacc_int_eq_false in eq1.
   eapply sem_lab.semacc_int_eq_false in eq2.
   pure_auto; inverts H0; [eapply eq1 | eapply eq2]; auto.
   (* end of If (muxowner ′ ==ₑ cpr ′ ||ₑ os_code_defs.pip ′ ==ₑ cpr ′){RETURN ′ EDEADLK} *)
   rewrite Htp_if1; simpl val_inj.
   hoare forward.
   2: { hoare unfold. destruct H10; tryfalse. }
  hoare unfold.
  hoare forward.
  hoare unfold.
  (* false case: If (ty ′ ==ₑ ′ PTHREAD_MUTEX_RECURSIVE) *)
  hoare forward; rewrite Htp_if2; simpl val_inj.
  hoare unfold; tryfalse.
  instantiate(1:= Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  (* need PartProof Lemma about  OSMutexPend *)
  hoare abscsq.
  apply noabs_oslinv.
  eapply absinfer_trans;
 try( eapply absinfer_choice2; eauto; can_change_aop_solver).
  eapply backward_rule1;
  [idtac | eapply PthreadMutexLockPartProof; eauto].
  introv Hsat.
  sep cancel Aier.
  sep pauto.
  rewrite Hdiveq; eauto.
 (* end of cases3 *)
 (* cases4:  tp =  $ PTHREAD_MUTEX_RECURSIVE *)
 (* false case: If (ty ′ ==ₑ ′ PTHREAD_MUTEX_RECURSIVE) *)
  hoare forward; rewrite Htp_if1; simpl val_inj.
  hoare unfold; tryfalse.
  instantiate(1:= Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.

  hoare forward.
    instantiate (1:= Afalse \\//
        ( <|| mutextimedlock_type_deadlk
         (|V$ PTHREAD_MUTEX_RECURSIVE
           :: Vint32 (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
              :: V_curp :: V_pcp :: V_ret :: nil|)
         ?? mutextimedlock_recurcnt (|Vint32 posv :: V_rcnt :: nil|);;
            (mutextimedlock_type_recur_incre_one
             (|Vint32 posv
               :: V$ PTHREAD_MUTEX_RECURSIVE
                  :: Vint32 (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                     :: V_curp :: V_pcp :: V_rcnt :: V_ret :: nil|)
             ?? mutextimedlock_type_recur_again
                (|V$ PTHREAD_MUTEX_RECURSIVE
                  :: Vint32 (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                     :: V_curp :: V_pcp :: V_rcnt :: V_ret :: nil|))
            ?? (mutextimedlock_ecb_ptr (| Vint32 posv :: V_pevt :: nil |) ;;
                   mutextimedlock_set_evloc_ptr (| V_pevt :: nil |);; 
             spec_code_cons (mutexpend (V_pevt :: (Vint32 tmv) :: V_err :: nil))
             (mutextimedlock_set_evloc_ptr (| Vnull :: nil |);; 
               (mutextimedlock_after_pend_timeout (| V_err :: V_ret :: nil |) ??
                 mutextimedlock_after_pend_fail (| V_err :: V_ret :: nil |) ??
                    (mutextimedlock_ecb_ptr (| Vint32 posv :: V_afteid :: nil |) ;;
                            (mutextimedlock_after_pend_succ_null (| V_err :: V_afteid :: V_ret :: nil |) ??
                              mutextimedlock_after_pend_succ_ecb (| V_err :: V_afteid :: Vint32 posv :: V_ret :: nil |)))))) ||>  **
         Aisr empisr **
         Aie true **
         Ais nil **
         Acs nil **
         Aier v'11 **
         p_local OSLInv tid init_lg **
         LV os_code_defs.pip @ long |-> V_pcp **
         LV cpr @ char_t |-> V_curp **
         LV ty @ long |-> (V$ PTHREAD_MUTEX_RECURSIVE) **
         LV muxowner @ char_t |-> Vint32 (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
         LV p @ OS_EVENT ∗ |-> Vptr (vp_b1, Int.zero) **
         LV os_code_defs.pos @ long |-> Vint32 posv **
         LV os_code_defs.x @ char_t |-> (V$ 1) **
         LV r @ long |-> v'7 **
         LV z @ char_t |-> v'3 **
         LV err @ char_t |-> v'0 **
         LV os_code_defs.abs_timeout @ Int16u |-> Vint32 tmv **
         LV mutex @ (long) ∗ |-> Vptr x **
         LV temp_num @ char_t |-> vtemp_dom **
         LV temp_dom @ char_t |-> vtemp_num **
         A_dom_lenv
           ((os_code_defs.abs_timeout, Int16u)
             :: (mutex, (long) ∗)
            :: (err, char_t)
               :: (os_code_defs.pos, long)
                  :: (os_code_defs.x, char_t)
                     :: (z, char_t)
                        :: (muxowner, char_t)
                           :: (ty, long)
                              :: (os_code_defs.pip, long)
                                 :: (r, long)
                                    :: (cpr, char_t) :: (p, OS_EVENT ∗)
                                      :: (temp_dom, char_t) :: (temp_num, char_t) :: nil)) **
        [| Vint32 (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <> V_curp /\
            V_pcp <> V_curp |]).
    hoare unfold.
    clear H10 H18 H22 H23.
    (* get curprio: ENTER_CRITICAL;ₛ cpr ′ =ₑ OSTCBCur ′ → OSTCBPrio;ₛ EXIT_CRITICAL;ₛ *)
    hoare forward prim.
    hoare unfold.
    (* cpr ′ =ₑ OSTCBCur ′ → OSTCBPrio *)
    hoare forward.
    struct_type_match_solver.
    unfold EvtInv.
    hoare unfold.
    rename i4 into curp.
    lets Hget_ct: Mbox_common.TCBListP_head_in_tcb H29.
    destruct Hget_ct as (cst & sus & Hget_ct).
    eapply TcbMod.join_get_r in Hget_ct; eauto.
    hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).
    assert (Hvcp: V_curp = Vint32 curp \/ V_curp <> Vint32 curp) by tauto.
    destruct Hvcp.
    2: { eapply abscsq_rule.
           apply noabs_oslinv.
           eapply mutextimedlock_absimp_curprio_abt; eauto.
           can_change_aop_solver.
           eapply absinfer_eq.
           apply absabort_rule.
         }
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutextimedlock_absimp_curprio; eauto.
   can_change_aop_solver.
   eapply absinfer_eq.
   subst V_curp.
   rename H37 into Hcurp_range.
   (* EXIT_CRITICAL *)
   hoare forward prim.
   sep cancel Aier.
   sep cancel CapabilityInv.
   unfold EvtInv.
   sep cancel tcbdllflag.
   sep cancel p_local.
   unfold AOSTCBList.
   unfold tcbdllseg.
   unfold V_OSTCBPrev,V_OSTCBNext.
   sep pauto; eauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel AMuxEIBs.
   sep cancel AMqEIBs.
   match goal with | |- _ |= dllseg ?head _ _ _ _ _ _ _ ** _ => sep cancel (dllseg head) end.
   simpl dllseg.
   unfold node.
   sep pauto; try splits; eauto.
   sep cancel Astruct.
   sep cancel dllseg.
   sep cancel APthreadAttr.
   eauto.
   struct_type_match_solver.
   auto.
  Optimize Proof.
  Optimize Heap.
   pure_auto.
   (* get prio_ceiling: ENTER_CRITICAL;ₛ pip ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) prio_ceiling;ₛ EXIT_CRITICAL;ₛ *)
   hoare forward prim.
   hoare unfold.
   (* pip ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) prio_ceiling *)
   clear H0 H7 Hmut_vl Hmut_vll.

   unfold EvtInv.
   hoare normal pre; hoare_ex_intro.
   unfold AMuxEIBs.
   hoare normal pre; hoare_ex_intro.
   hoare_lifts_trms_pre ( R_Q_Data_P ).
   eapply pure_split_rule'; introv Hrqdata'.
   hoare_lifts_trms_pre (AMuxCap).
   match goal with
    | |- {| _, _ , _, _, _, _ |} |- _ {{ AMuxCap ?l ?vl ** _ }} _ {{ _ }} =>
   rename l into lmux; rename vl into muxcapvl' end.
   hoare_lifts_trms_pre (MuxCapArray_P, length muxcapvl').
   eapply pure_split_rule'; introv Hmuxcap_vl'.
   eapply pure_split_rule'; introv Hmuxcap_len'.
   destruct lmux as (lmux_b' & lmux_i').
   hoare_lifts_trms_pre APthreadMutex.
   match goal with
    | |- {| _ , _, _, _, _, _ |} |- _ {{ APthreadMutex _ ?vl ** _ }} _ {{ _ }} =>
       hoare_assert_pure (length vl = (∘ (OS_USER_MAX_EVENTS / 3)))
    end.
   { get_hsat Hsat. sep_lifts_trms_in Hsat APthreadMutex.
     eapply apthreadmutex_len_frm; eauto.  }
   eapply pure_split_rule'; introv Hlen_minfo'.
   hoare unfold.

     hoare_lifts_trms_pre (Aop, APthreadMutex).
     eapply backward_rule1.
     introv Hsat.
     eapply APthreadMutex_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned posv)).
     sep cancel APthreadMutex.
     eauto.
     rewrite Hlen_minfo'.
     eapply ge_ne_lt_rgn; eauto.
     rewrite Hdiveq.
     apply Intlt_false_is_Zge; auto.
     rewrite Hdiveq; eauto.

     hoare unfold.
     hoare normal pre.

     hoare_lifts_trms_pre (Aop).
     hoare forward.
     eapply assign_rule_lvar.
     split; introv Hsat. sep cancel (Alvarmapsto os_code_defs.pip). eauto.
     sep auto.
     sep_get_rv_array_struct.
     rewrite Hdiveq; eauto.
     rewrite Hdiveq; eauto.
    eapply new_array_type_vallist_match_split1 in H47; eauto.
    simpljoin; auto.
    eapply eq_int; auto.
    intros. eexists. sep cancel p_local. simpl; eauto.

  lets Hmls: muxb_corr H0 H56 H2 Hlemu. 
  destruct Hmls as (eo' & ow' & tp' & rcnt' & prot' & pcp' & wq' & c' & mc' & Hget' & Hmls).
  match goal with H: EIBMAarray_P _ (_ ++ ?vl :: _) _ _ |- _ => rename vl into mutvl end.
  destruct Hmls as (_ & _ & _ & _ & Hvpcp_eq & _).
   unfold V_OSMUXINFOPrio_ceiling in Hvpcp_eq.
   apply nth_val_nth_val'_some_eq in Hvpcp_eq.
   hoare_lifts_trms_pre (Aop, absmutinfoid).
  assert (Hvpcp: V_pcp = Vint32 pcp' \/ V_pcp <> Vint32 pcp') by tauto.
  destruct Hvpcp.
  2: { eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutextimedlock_absimp_prioceiling_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
       }
  subst V_pcp.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextimedlock_absimp_prioceiling; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  rewrite Hvpcp_eq.
   (* EXIT_CRITICAL *)
    eapply backward_rule1. 
    introv Hsat.
    eapply APthreadMutex_select_sn_ex_strong.
    eexists. exists (Z.to_nat (Int.unsigned posv)). eexists.
    exists mutvl.
    sep cancel Aarray_new.
    sep cancel Aarray_new.
    sep pauto.

   hoare forward prim.
   sep cancel Aier.
   sep cancel CapabilityInv.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep normal; sep eexists.
   sep cancel AMuxCap.
   sep pauto; eauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel AMqEIBs.
   sep cancel p_local.
   sep cancel APthreadMutex.
   sep cancel APthreadAttr.
   eauto.
   auto.
   pure_auto.
  (* split the mutvl as mutvl = _ :: _ :: ... :: nil *)
  lets Hmut_vll: H47.
  rename H47 into Hmut_vl.
  eapply new_array_type_vallist_match_split1 in Hmut_vl; eauto.
  destruct Hmut_vl as (_ & _ & Hmut_vl).
  lets Hmut_vl_eq: struct_type_vallist_match_mutex_info_t_imp Hmut_vl.
  destruct Hmut_vl_eq as (vtp' & vpro' & vpcp' & vwq' & vcs' & vow' & vrcnt' & vtsk' & vp' & vmc' & Hmut_vl_eq & Hvp_ptr').
  subst mutvl.
  simpl nth_val' in Hvpcp_eq. inverts Hvpcp_eq.
  simpl nth_val'.
  (* If (muxowner ′ ==ₑ cpr ′ ||ₑ os_code_defs.pip ′ ==ₑ cpr ′){ get rcnt } *)
  hoare forward.
  clear -How_range. pure_auto.
  clear -Hcurp_range. pure_auto.
  clear -H; pure_auto.
  clear -Hcurp_range; pure_auto.
  clear -H; pure_auto.
  clear -H; pure_auto.
 hoare unfold.
  assert(His_owner: Int.eq (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) curp = true \/ Int.eq pcp' curp = true).
 { clear -H47.
    destruct (Int.eq (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) curp) eqn: eq1;
    destruct (Int.eq pcp' curp) eqn: eq2;
    simpl in H47; tryfalse; auto.
 }
 clear H47 H55 H59.
 instantiate (1:= Afalse).
 (* get recursive_cnt: ENTER_CRITICAL;ₛ r ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) recursive_cnt;ₛ EXIT_CRITICAL;ₛ *)
   hoare forward prim.
   hoare unfold.
   (* r ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) recursive_cnt *)
   clear Hmut_vl Hmut_vll.

   unfold EvtInv.
   hoare normal pre; hoare_ex_intro.
   unfold AMuxEIBs.
   hoare normal pre; hoare_ex_intro.
   hoare_lifts_trms_pre ( R_Q_Data_P ).
   eapply pure_split_rule'; introv Hrqdata''.
   hoare_lifts_trms_pre (AMuxCap).
   match goal with
    | |- {| _, _ , _, _, _, _ |} |- _ {{ AMuxCap ?l ?vl ** _ }} _ {{ _ }} =>
   rename l into lmux; rename vl into muxcapvl'' end.
   hoare_lifts_trms_pre (MuxCapArray_P, length muxcapvl'').
   eapply pure_split_rule'; introv Hmuxcap_vl''.
   eapply pure_split_rule'; introv Hmuxcap_len''.
   destruct lmux as (lmux_b'' & lmux_i'').
   hoare_lifts_trms_pre APthreadMutex.
   match goal with
    | |- {| _ , _, _, _, _, _ |} |- _ {{ APthreadMutex _ ?vl ** _ }} _ {{ _ }} =>
       hoare_assert_pure (length vl = (∘ (OS_USER_MAX_EVENTS / 3)))
    end.
   { get_hsat Hsat. sep_lifts_trms_in Hsat APthreadMutex.
     eapply apthreadmutex_len_frm; eauto.  }
   eapply pure_split_rule'; introv Hlen_minfo''.
   hoare unfold.

     hoare_lifts_trms_pre (Aop, APthreadMutex).
     eapply backward_rule1.
     introv Hsat.
     eapply APthreadMutex_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned posv)).
     sep cancel APthreadMutex.
     eauto.
     rewrite Hlen_minfo''.
     eapply ge_ne_lt_rgn; eauto.
     rewrite Hdiveq.
     apply Intlt_false_is_Zge; auto.
     rewrite Hdiveq; eauto.

     hoare unfold.
     hoare normal pre.

     hoare_lifts_trms_pre (Aop).
     hoare forward.
     eapply assign_rule_lvar.
     split; introv Hsat. sep cancel (Alvarmapsto r). eauto.
     sep auto.
  Optimize Proof.
  Optimize Heap.
     sep_get_rv_array_struct.
     rewrite Hdiveq; eauto.
     rewrite Hdiveq; eauto.
    eapply new_array_type_vallist_match_split1 in H61; eauto.
    simpljoin; auto.
    eapply eq_int; auto.
    intros. eexists. sep cancel p_local. simpl; eauto.

  lets Hmls: muxb_corr H59 H70 H2 Hlemu. 
  destruct Hmls as (eo'' & ow'' & tp'' & rcnt'' & prot'' & pcp'' & wq'' & c'' & mc'' & Hget'' & Hmls).
  match goal with H: EIBMAarray_P _ (_ ++ ?vl :: _) _ _ |- _ => rename vl into mutvl end.
  destruct Hmls as (_ & _ & _ & Hvrcnt_eq & _).
  unfold V_OSMUXINFORecursive_cnt in Hvrcnt_eq.
  apply nth_val_nth_val'_some_eq in Hvrcnt_eq.
  hoare_lifts_trms_pre (Aop, absmutinfoid).
  assert (Hvrcnt: V_rcnt = Vint32 rcnt'' \/ V_rcnt <> Vint32 rcnt'') by tauto.
  destruct Hvrcnt.
  2: { eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutextimedlock_absimp_recurcnt_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
       }
  subst V_rcnt.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextimedlock_absimp_recurcnt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  rewrite Hvrcnt_eq.
   (* EXIT_CRITICAL *)
    eapply backward_rule1. 
    introv Hsat.
    eapply APthreadMutex_select_sn_ex_strong.
    eexists. exists (Z.to_nat (Int.unsigned posv)). eexists.
    exists mutvl.
    sep cancel Aarray_new.
    sep cancel Aarray_new.
    sep pauto.

   hoare forward prim.
   sep cancel Aier.
   sep cancel CapabilityInv.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep normal; sep eexists.
   sep cancel AMuxCap.
   sep pauto; eauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel AMqEIBs.
   sep cancel p_local.
   sep cancel APthreadMutex.
   sep cancel APthreadAttr.
   eauto.
   auto.
   pure_auto.
  (* split the mutvl as mutvl = _ :: _ :: ... :: nil *)
  lets Hmut_vll: H61.
  rename H61 into Hmut_vl.
  eapply new_array_type_vallist_match_split1 in Hmut_vl; eauto.
  destruct Hmut_vl as (_ & _ & Hmut_vl).
  lets Hmut_vl_eq: struct_type_vallist_match_mutex_info_t_imp Hmut_vl.
  destruct Hmut_vl_eq as (vtp'' & vpro'' & vpcp'' & vwq'' & vcs'' & vow'' & vrcnt'' & vtsk'' & vp'' & vmc'' & Hmut_vl_eq & Hvp_ptr'').
  subst mutvl.
  simpl nth_val' in Hvrcnt_eq. inverts Hvrcnt_eq.
  simpl nth_val'.
  (* IF (′ PTHREAD_MUTEX_RECURSIVE_MAX >ₑ r ′) *)
  hoare forward; try instantiate(1:= Afalse).
  pure_auto.
  hoare unfold.
  destruct (Int.ltu rcnt'' ($ PTHREAD_MUTEX_RECURSIVE_MAX)) eqn: eq1;
  simpl in H61; tryfalse.
  (* rcnt ++*)
  clear Hmut_vl Hmut_vll.
   hoare forward prim.
   hoare unfold.
   (* ++ efield (Pthread_Mutex ′ [pos ′]) recursive_cnt;ₛ *)

   unfold EvtInv.
   hoare normal pre; hoare_ex_intro.
   unfold AMuxEIBs.
   hoare normal pre; hoare_ex_intro.
   hoare_lifts_trms_pre ( R_Q_Data_P ).
   eapply pure_split_rule'; introv Hrqdata'''.
   hoare_lifts_trms_pre (AMuxCap).
   match goal with
    | |- {| _, _ , _, _, _, _ |} |- _ {{ AMuxCap ?l ?vl ** _ }} _ {{ _ }} =>
   rename l into lmux; rename vl into muxcapvl''' end.
   hoare_lifts_trms_pre (MuxCapArray_P, length muxcapvl''').
   eapply pure_split_rule'; introv Hmuxcap_vl'''.
   eapply pure_split_rule'; introv Hmuxcap_len'''.
   destruct lmux as (lmux_b''' & lmux_i''').
   hoare_lifts_trms_pre APthreadMutex.
   match goal with
    | |- {| _ , _, _, _, _, _ |} |- _ {{ APthreadMutex _ ?vl ** _ }} _ {{ _ }} =>
       hoare_assert_pure (length vl = (∘ (OS_USER_MAX_EVENTS / 3)))
    end.
   { get_hsat Hsat. sep_lifts_trms_in Hsat APthreadMutex.
     eapply apthreadmutex_len_frm; eauto.  }
   eapply pure_split_rule'; introv Hlen_minfo'''.
   hoare unfold.

     hoare_lifts_trms_pre (Aop, APthreadMutex).
     eapply backward_rule1.
     introv Hsat.
     eapply APthreadMutex_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned posv)).
     sep cancel APthreadMutex.
     eauto.
     rewrite Hlen_minfo'''.
     eapply ge_ne_lt_rgn; eauto.
     rewrite Hdiveq.
     apply Intlt_false_is_Zge; auto.
     rewrite Hdiveq; eauto.

     hoare unfold.
     hoare normal pre.
     (* split the mutvl as mutvl = _ :: _ :: ... :: nil *)
     match goal with H: EIBMAarray_P _ (_ ++ ?vl :: _) _ _ |- _ => rename vl into mutvl end.
     lets Hmut_vll: H78.
     rename H78 into Hmut_vl.
     eapply new_array_type_vallist_match_split1 in Hmut_vl; eauto.
    destruct Hmut_vl as (Hmut_vll1 & Hmut_vll2 & Hmut_vl).
    lets Hmut_vl_eq: struct_type_vallist_match_mutex_info_t_imp Hmut_vl.
    destruct Hmut_vl_eq as (vtp1 & vpro1 & vpcp1 & vwq1 & vcs1 & vow1 & vrcnt1 & vtsk1 & vp1 & vmc1 & Hmut_vl_eq & Hvp_ptr1).
    subst mutvl.

    hoare_lifts_trms_pre Aop.
    hoare forward.
    introv Hsat.
    eapply bop_rv.
    sep_get_rv_array_struct.
    rewrite Hdiveq; eauto.
    rewrite Hdiveq; eauto.
    sep get rv.
    simpl; eauto.
    pure_auto.
    simpl; auto.

  lets Hmls: muxb_corr H76 H87 H2 Hlemu.
  destruct Hmls as (eo1 & ow1 & tp1 & rcnt1 & prot1 & pcp1 & wq1 & c1 & mc1 & Hget1 & Hmls).
  destruct Hmls as (_ & _ & _ & Hvrcnt_eq & _).
   unfold V_OSMUXINFORecursive_cnt in Hvrcnt_eq.
   apply nth_val_nth_val'_some_eq in Hvrcnt_eq.
   simpl nth_val' in Hvrcnt_eq. inverts Hvrcnt_eq.
   hoare_lifts_trms_pre (Aop, absmutinfoid).
  assert (Hrv: V_ret = Vint32 Int.zero \/ V_ret <> Vint32 Int.zero) by tauto.
  destruct Hrv.
  2: { eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutextimedlock_absimp_recur_incre_one_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
       }
  subst V_ret.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextimedlock_absimp_recur_incre_one; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
   (* EXIT_CRITICAL *)
    eapply backward_rule1. 
    introv Hsat.
    eapply APthreadMutex_select_sn_ex_strong.
    eexists. exists (Z.to_nat (Int.unsigned posv)). eexists.
    exists (update_nth_val 6
               (Vint32 vtp1
                :: Vint32 vpro1
                   :: Vint32 vpcp1
                      :: Vint32 vwq1
                         :: Vint32 vcs1
                            :: Vint32 vow1
                               :: Vint32 rcnt1 :: Vint32 vtsk1 :: vp1 :: vmc1 :: nil)
               (Vint32 (rcnt1 +ᵢ  $ 1))).
    sep cancel Aarray_new.
    sep cancel Aarray_new.
    sep pauto.
    clear -Hlen_minfo'''.
   rewrite <- Hlen_minfo'''.
   do 2 rewrite app_length.
   simpl length. auto.
   eapply new_array_type_vallist_match_compose_struct; eauto.

   hoare forward prim.
   sep cancel Aier.
   sep cancel CapabilityInv.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep normal; sep eexists.
   sep cancel AMuxCap.
   sep pauto; eauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel AMqEIBs.
   sep cancel p_local.
   sep cancel APthreadMutex.
   sep cancel APthreadAttr.
   eauto.
   eapply eibref_distinct_set_pos_muxeib_gen; eauto.
   eapply Q_ECB_P_set_mux_preserve_gen; eauto.
   eapply MUX_ECB_P_set_mux_preserve_gen; eauto.
   eapply SEM_ECB_P_set_mutex_preserve_gen; eauto.
   eapply RH_ECBlk_EIBlk_Mux_P_set_recurcnt; eauto.
   eapply MuxCapArray_P_hold; eauto.
   eapply EIBMAarray_P_recurcnt_for_update_to_recurcnt'; eauto.
   apply Int.unsigned_range_2.
   auto.
  Optimize Proof.
  Optimize Heap.
   pure_auto.
   (* RETURN ′ 0 *)
   hoare forward.
  (* false : IF (′ PTHREAD_MUTEX_RECURSIVE_MAX >ₑ r ′) *)
   hoare unfold.
  destruct (Int.ltu rcnt'' ($ PTHREAD_MUTEX_RECURSIVE_MAX)) eqn: eq1;
  simpl in H61; destruct H61; tryfalse.
  assert (Hrv: V_ret = Vint32 (Int.repr EAGAIN) \/ V_ret <> Vint32 (Int.repr EAGAIN)) by tauto.
  destruct Hrv.
  2: { hoare abscsq.
        apply noabs_oslinv.
        eapply mutextimedlock_absimp_recur_again_abt; eauto.
        can_change_aop_solver.
        apply absabort_rule.
       }
  subst V_ret.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutextimedlock_absimp_recur_again; eauto.
  can_change_aop_solver.
  (* RETURN ′ EAGAIN *)
  hoare forward.
  destruct H61 as [Hsat | Hsat];
  eapply astar_l_afalse_elim in Hsat; auto.
  eapply adisj_intro.
  destruct H47; [left | right].
  eapply astar_l_afalse_elim; eauto.
  sep cancel Aier.
  sep pauto.
   clear -H55.
   destruct (Int.eq (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) curp) eqn: eq1;
   destruct (Int.eq pcp' curp) eqn: eq2;
   simpl in *;
   try change (Int.ltu Int.zero Int.one) with true in *;
   try change (Int.ltu Int.zero Int.zero) with false in *;
   simpl in *; (try destruct H55; tryfalse).
   eapply sem_lab.semacc_int_eq_false in eq1.
   eapply sem_lab.semacc_int_eq_false in eq2.
   pure_auto; inverts H0; [eapply eq1 | eapply eq2]; auto.
   rewrite Htp_if2; simpl val_inj.
   hoare forward.
   2: { hoare unfold. destruct H18; tryfalse. }
  hoare unfold.
  hoare forward.
  hoare unfold.
  (* need PartProof Lemma about  OSMutexPend *)
  hoare abscsq.
  apply noabs_oslinv.
  eapply absinfer_trans;
 try( eapply absinfer_choice2; eauto; can_change_aop_solver).
  eapply backward_rule1;
  [idtac | eapply PthreadMutexLockPartProof; eauto].
  introv Hsat.
  sep cancel Aier.
  sep pauto.
  rewrite Hdiveq; eauto.
  Unshelve.
  exact Aemp.
  exact 0%nat.
  exact 0%nat.
  exact 0%nat.
  exact 0%nat.
  exact 0%nat.
  exact 0%nat.
  exact 0%nat.
  exact 0%nat.
Qed.


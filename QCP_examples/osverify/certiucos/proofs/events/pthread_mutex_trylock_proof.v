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

Lemma mutextrylock_absimp_muxerr_abt:
  forall s sch V_mux V_pos P,
    (V_mux = Vnull \/
           exists a,
             V_mux = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)) ->  
    V_pos <> Vint32 (Int.mone) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||
          (mutextrylock_muxerr (|V_mux :: V_pos :: nil|) ??
                   mutextrylock_mutex_pos(|V_mux :: V_pos :: nil|));;s
                       ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
intros.
eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_trans; try( eapply absinfer_choice1; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver.
Qed.

Lemma mutextrylock_absimp_muxerr_cont: 
  forall sch V_mux V_pos s P,
    (V_mux = Vnull \/
       exists v'4, V_mux = Vptr v'4 /\ 
                     (cmpaddr Cle v'4 userAddrStart = true \/
                        cmpaddr Clt userAddrEnd v'4 = true)) ->   
    V_pos = Vint32 Int.mone -> 
    can_change_aop P -> 
    absinfer sch 
      (<||
         (mutextrylock_muxerr (|V_mux :: V_pos :: nil|) ??
                   mutextrylock_mutex_pos(|V_mux :: V_pos :: nil|));; s ||>  ** P)
      (<|| s ||> ** P).
Proof.
intros.
eapply absinfer_trans; try (eapply absinfer_seq_end; eauto).
eapply absinfer_seq; eauto.
infer_solver 0%nat.
Qed.

Lemma mutextrylock_absimp_mux_get_none:
  forall sch v'4 v pbls s P,
    cmpaddr Clt userAddrStart v'4 = true ->
    cmpaddr Cle v'4 userAddrEnd = true -> 
    get pbls v'4 = None -> 
    can_change_aop P ->
    absinfer sch
     (<||
      (mutextrylock_muxerr (|Vptr v'4 :: v :: nil|) ??
            mutextrylock_mutex_pos(|Vptr v'4 :: v :: nil|));;
                 s ||>  **
        Hpbls pbls ** P)
     (<|| ABORT ||>  ** Hpbls pbls ** P).
Proof.
intros.
assert (Hc: can_change_aop (Hpbls pbls ** P)) by can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_trans; try( eapply absinfer_choice2; eauto).
eapply absinfer_abt; eauto.
absimp_abt_solver.
right. 
eexists; eauto. splits; eauto. 
eapply absdata_elim.
instantiate(2:= mutextrylock_mutex_pos (|Vptr v'4 :: v :: nil|)).
instantiate(2:=s0).
sep pauto.
Qed.

Lemma mutextrylock_absimp_mux_get_outtype_err_abt:
  forall sch v'4 v s P,
    cmpaddr Clt userAddrStart v'4 = true ->
    cmpaddr Cle v'4 userAddrEnd = true -> 
    ~(exists i, v = Vint32 i) -> 
    can_change_aop P ->
    absinfer sch
     (<||
     (mutextrylock_muxerr (|Vptr v'4 :: v :: nil|) ??
            mutextrylock_mutex_pos(|Vptr v'4 :: v :: nil|));;
                 s ||>  ** P)
     (<|| ABORT ||>  ** P). 
Proof.
  introv Hrgn1 Hrgn2 Htp Hcop. 
  eapply absinfer_trans.
  2:{ eapply absinfer_seq_abt; eauto. }
  eapply absinfer_seq; eauto.
  eapply absinfer_trans; try( eapply absinfer_choice2; eauto).
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
  Unshelve.
  exact None. 
Qed. 

Lemma mutextrylock_absimp_mux_get_pos_abt: 
  forall sch vmux pbls posv v s P , 
    cmpaddr Clt userAddrStart vmux = true ->
    cmpaddr Cle vmux userAddrEnd = true -> 
    get pbls vmux = Some posv ->
    v <> Vint32 posv -> 
    can_change_aop P ->
   absinfer sch  
     (<||
    (mutextrylock_muxerr (|Vptr vmux :: v :: nil|) ??
            mutextrylock_mutex_pos(|Vptr vmux :: v :: nil|));;
                 s ||> ** Hpbls pbls ** P)
     (<|| ABORT ||> ** Hpbls pbls ** P).
Proof.
  introv Hlt Hle Hposv Hv Hcop.
  assert (Hc: can_change_aop (Hpbls pbls ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_trans; try( eapply absinfer_choice2; eauto).
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
  right. eexists; splits; eauto.
  pure_auto.
  eapply absdata_elim.
  instantiate(3:= mutextrylock_mutex_pos (|Vptr vmux :: v :: nil|)).
  instantiate (3:= s0).
  sep pauto.
  left. eexists; splits; eauto.
Qed.

Lemma mutextrylock_absimp_mux_get_pos_ok: 
  forall sch vmux pbls posv v P s, 
    cmpaddr Clt userAddrStart vmux = true ->
    cmpaddr Cle vmux userAddrEnd = true -> 
    get pbls vmux = Some posv ->
    v = Vint32 posv -> 
    can_change_aop P ->
   absinfer sch  
     (<||
    (mutextrylock_muxerr (|Vptr vmux :: v :: nil|) ??
            mutextrylock_mutex_pos(|Vptr vmux :: v :: nil|));;
                 s ||> ** Hpbls pbls ** P)
     (<|| s||> ** Hpbls pbls ** P).
Proof.
intros.
assert (Hc: can_change_aop (Hpbls pbls ** P)) by can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq_end; eauto).
instantiate (1:= None).
eapply absinfer_seq; eauto.
infer_solver 1%nat.
repeat eexists; eauto.
right. exists pbls. 
splits; eauto.
eapply absdata_elim. 
instantiate (2:= mutextrylock_mutex_pos (|Vptr vmux :: v :: nil|)).
instantiate (2:= s0).
sep pauto. 
left.
eexists; splits; eauto.
Qed.

Lemma mutextrylock_absimp_poserr0:
  forall posv v1 V_ret s P sch,
    v1 = Vint32 posv ->
    (Int.ltu posv Int.zero = true \/
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) ->
    V_ret = Vint32 (Int.repr EINVAL) -> 
    can_change_aop P -> 
    absinfer sch
      ( <||    mutextrylock_poserr (|v1 :: V_ret :: nil|) ?? s ||> ** P)
      ( <|| END (Some  (Vint32 (Int.repr EINVAL))) ||> ** P ).
Proof.
  infer_solver 0%nat.  
  subst v1.
  do 2 eexists. splits; eauto. 
  left. splits; auto. subst V_ret. auto.
Qed.


Lemma mutextrylock_absimp_poserr_abt:
  forall posv v1 V_ret s P sch,
      v1 = Vint32 posv ->
    (Int.ltu posv Int.zero = true \/
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) ->
      V_ret <> (Vint32 (Int.repr EINVAL)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||   mutextrylock_poserr (|v1 :: V_ret :: nil|) ?? s ||> ** P)
      (<|| ABORT ||> ** P). 
Proof. 
  introv Hv1 Hrgn Hv4 Hcaop.
  eapply absinfer_trans.
  eapply absinfer_choice1; try eauto.
  eapply absinfer_abt. try can_change_aop_solver. try can_change_aop_solver. 
  unfolds; intros. eexists; exgamma.
  split. simpl_subst_gamma. hmstep_call_consturctor. 
  eapply spec_prim_step_abt.
  unfolds. do 2 eexists. splits; eauto. rewrite Hv1. auto. apply map_join_emp .  
  repeat hmstep_call_consturctor.
  simpl in *. simpljoin. do 6 eexists. 
  splits ; try eauto.  
  eapply change_aop_rule; eauto. 
  Unshelve.
  exact (None).
Qed.

Lemma mutextrylock_absimp_posok_choice:
  forall s posv v1 V_ret P sch,
    (Int.ltu posv Int.zero = false /\
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = false /\ posv <> Int.repr (OS_USER_MAX_EVENTS / 3)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mutextrylock_poserr (|v1 :: V_ret :: nil|) ?? s ||> ** P) 
      (<|| s ||> ** P). 
Proof.
  introv Hrgn Hcaop.
  apply absinfer_choice2; can_change_aop_solver.
  pure_auto.
Qed.

Lemma mutextrylock_absimp_before_abt_hold: 
  forall i o x n pi w pro c mc s V_eid minfob sch P, 
    (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
    get minfob i = Some (Holder, o, x, n, pro, pi, w, c, mc) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||
         mutextrylock_ecb_ptr (|(Vint32 i) :: V_eid :: nil|);; s ||>  ** HMuxInfo minfob ** P) 
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


Lemma mutextrylock_absimp_before_abt_out: 
  forall i eo o x n pi w pro c mc s V_eid minfob sch P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
         ((exists eid, eo = (Valid_Addr eid) /\ V_eid <> Vptr eid) \/ eo = Null /\ V_eid <> Vnull) -> 
         can_change_aop P -> 
         absinfer sch 
           (<||
              mutextrylock_ecb_ptr (|(Vint32 i) :: V_eid :: nil|);; s ||>  ** HMuxInfo minfob ** P)
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

Lemma mutextrylock_absimp_get_before_abt_out: 
  forall i eo o x n pi w pro c mc V_eid s minfob sch P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
         ((exists eid, eo = (Valid_Addr eid) /\ V_eid <> Vptr eid) \/ eo = Null /\ V_eid <> Vnull) -> 
         can_change_aop P -> 
         absinfer sch 
           (<||
             mutextrylock_ecb_ptr (|(Vint32 i) :: V_eid :: nil|) ;; s ||>  ** HMuxInfo minfob ** P)
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

Lemma mutextrylock_absimp_before_ok: 
  forall i eo o x n pi w pro c mc V_eid s1 minfob sch P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
          get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
         (exists eid,  eo = (Valid_Addr eid) /\ V_eid = Vptr eid) \/ eo = Null /\ V_eid = Vnull ->
         can_change_aop P -> 
         absinfer sch 
           (<||   mutextrylock_ecb_ptr (|(Vint32 i) :: V_eid :: nil|);; s1 ||>  ** HMuxInfo minfob ** P)
           (<|| s1 ||>  ** HMuxInfo minfob ** P). 
Proof.
  introv Hrgn Hsi Heo Hcop.   
  infer_solver 0%nat.  
(*   destruct s as [[[[]]]]. *)
  do 12 eexists.
  splits;eauto.
  split.
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  eapply absdata_elim.
  instantiate (1:= P).
  instantiate (1:=mutextrylock_ecb_ptr (|Vint32 i :: V_eid :: nil|)).
  instantiate (1:=s).
  eauto.
  Unshelve. 
  exact None.
Qed.

Lemma mutextrylock_absimp_get_before_ok: 
  forall i eo o x n pi w pro c mc V_eid s1 minfob sch P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
          get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
         (exists eid,  eo = (Valid_Addr eid) /\ V_eid = Vptr eid) \/ eo = Null /\ V_eid = Vnull ->
         can_change_aop P -> 
         absinfer sch 
           (<||
            mutextrylock_ecb_ptr (|(Vint32 i) :: V_eid :: nil|) ;; s1 ||>  ** HMuxInfo minfob ** P)
           (<|| s1 ||>  ** HMuxInfo minfob ** P). 
Proof.
  introv Hrgn Hsi Heo Hcop.   
  infer_solver 0%nat.  
(*   destruct s as [[[[]]]]. *)
  do 12 eexists.
  splits;eauto.
  split.
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  eapply absdata_elim.
  instantiate (1:= P).
  instantiate (1:=mutextrylock_ecb_ptr (|Vint32 i :: V_eid :: nil|)).
  instantiate (1:=s).
  eauto.
  Unshelve. 
  exact None.
Qed. 

Lemma mutextrylock_absimp_recurtp_before_ok: 
  forall i eo o x n pi w pro c mc V_tp s1 minfob sch P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
          get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
          V_tp =Vint32 x -> 
         can_change_aop P -> 
         absinfer sch 
           (<||  mutextrylock_recurtype(|(Vint32 i) :: V_tp :: nil|) ;; s1 ||>  ** HMuxInfo minfob ** P)
           (<||  s1 ||>  ** HMuxInfo minfob ** P). 
Proof.
  introv Hrgn Hsi Hcop.   
  infer_solver 0%nat.  
Qed. 

Lemma mutextrylock_absimp_recurtp_before_abt: 
  forall i eo o x n pi w pro c mc V_tp s1 minfob sch P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
          get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
          V_tp <> Vint32 x ->
         can_change_aop P -> 
         absinfer sch 
           (<||      mutextrylock_recurtype(|(Vint32 i) :: V_tp :: nil|) ;; s1 ||>  ** HMuxInfo minfob ** P)
           (<|| ABORT ||>  ** HMuxInfo minfob ** P). 
Proof.
  introv Hrgn Hsi Htp Hcop.
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

Lemma mutextrylock_absimp_curprio_before_ok: 
  forall prio m st V_curp s1 t tls sch P sus, 
          TcbMod.get tls t = Some (prio,st,m, sus) ->
          V_curp =Vint32 prio ->
         can_change_aop P -> 
         absinfer sch 
           (<||  mutextrylock_curprio(| V_curp :: nil|) ;; s1 ||>  ** HTCBList tls ** HCurTCB t  ** P)
           (<||  s1 ||>  ** HTCBList tls ** HCurTCB t  ** P). 
Proof.
  intros.   
  infer_solver 0%nat.  
Qed.

Lemma mutextrylock_absimp_curprio_before_abt: 
  forall prio m st V_curp s1 t tls sch P sus, 
          TcbMod.get tls t = Some (prio,st,m, sus) ->
          V_curp <> Vint32 prio ->
         can_change_aop P -> 
         absinfer sch 
           (<||  mutextrylock_curprio(| V_curp :: nil|) ;; s1 ||>  ** HTCBList tls ** HCurTCB t  ** P)
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
  instantiate(2:= mutextrylock_curprio (|V_curp :: nil|)).
  sep pauto.
  eapply absinfer_seq_abt; auto.
Qed.

Lemma mutextrylock_absimp_if_null_yes2_abt: 
  forall i sch V_ret V_eid s1 P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         V_eid = Vnull -> 
         V_ret <> (Vint32 (Int.repr EINVAL)) -> 
         can_change_aop P -> 
         absinfer sch 
           (<|| mutextrylock_if_null_yes (|V_eid :: V_ret :: nil|) ?? s1 ||>  **  P)
           (<|| ABORT ||>  ** P). 
Proof.
  introv Hrgn Hv Hv1 Hcop.
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

Lemma mutextrylock_absimp_if_null_yes2_end: 
  forall i sch  V_ret V_eid s1 P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         V_eid = Vnull -> 
         V_ret = (Vint32 (Int.repr EINVAL)) -> 
         can_change_aop P -> 
         absinfer sch 
           (<||  mutextrylock_if_null_yes (|V_eid :: V_ret :: nil|) ?? s1 ||>  **  P)
           (<|| END (Some (Vint32 (Int.repr EINVAL))) ||>  ** P). 
Proof.
  introv Hrgn Hv Hv1 Hcop.
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

Lemma mutextrylock_absimp_if_null_yes_end: 
  forall i sch V_ret V_eid s1 P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         V_eid = Vnull -> 
         V_ret = (Vint32 (Int.repr EINVAL)) -> 
         can_change_aop P -> 
         absinfer sch 
           (<|| 
                  mutextrylock_if_null_yes (|V_eid :: V_ret :: nil|) ?? s1 ||>  **  P)
           (<|| END (Some (Vint32 (Int.repr EINVAL))) ||>  ** P). 
Proof.
  introv Hrgn Hv Hv1 Hcop.
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

Lemma mutextrylock_absimp_if_null_yes_abt: 
  forall i sch V_ret V_eid s1 P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         V_eid = Vnull -> 
         V_ret <> (Vint32 (Int.repr EINVAL)) -> 
         can_change_aop P -> 
         absinfer sch 
           (<||
                    mutextrylock_if_null_yes (|V_eid :: V_ret :: nil|) ??
                              (mutextrylock_if_null_no (|V_eid :: nil|) ;; s1) ||>  **  P)
           (<|| ABORT ||>  ** P). 
Proof.
  introv Hrgn Hv Hv1 Hcop.
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

Lemma mutextrylock_absimp_if_null_no: 
  forall i sch V_ret V_eid s1 P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         (exists eid, V_eid =Vptr eid) -> 
         can_change_aop P -> 
         absinfer sch 
           (<|| mutextrylock_if_null_yes (|V_eid :: V_ret :: nil|) ??
                              (mutextrylock_if_null_no (|V_eid :: nil|) ;; s1) ||>  **  P)
           (<||  s1  ||>  ** P). 
Proof.
  introv Hrgn Hv Hcop.
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

 Lemma mutextrylock_absimp_if_null_owner_no_end: 
  forall i sch qls mls o x n pi w pro c mc V_eid V_ret ow pr y wl s1 eid P, 
         V_eid =Vptr eid ->
         get mls i = Some (Valid_Addr eid, o, x, n, pro, pi, w, c, mc) ->
         get qls eid =Some (absmutexsem pr y, wl) ->
         (( y = None /\ow = $ OS_MUTEX_AVAILABLE ) \/
         (exists t op,  y = Some (t, op) /\ ow = op)) ->
         can_change_aop P -> 
         absinfer sch 
           (<|| mutextrylock_if_null_yes (|V_eid :: V_ret :: nil|) ??
                 ( mutextrylock_if_null_owner_no (|(Vint32 i) :: V_eid :: (Vint32 ow) :: nil|) ;; s1) ||> ** HECBList qls ** HMuxInfo mls ** P)
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
  instantiate (1:=mutextrylock_if_null_owner_no
    (|Vint32 i :: V_eid :: Vint32 ow :: nil|)).
  instantiate (1:=s).
  sep cancel 1%nat 2%nat. auto.
  eapply absdata_elim.
  instantiate (1:=  HMuxInfo mls ** P).
  instantiate (1:= mutextrylock_if_null_owner_no
    (|Vint32 i :: V_eid :: Vint32 ow :: nil|)).
  instantiate (1:=s). auto.
Qed.

 Lemma mutextrylock_absimp_if_null_owner_no_abt: 
  forall i sch qls mls o x n pi w pro c mc V_eid V_ret ow pr y wl s1 eid P rv, 
         V_eid =Vptr eid ->
         get mls i = Some (Valid_Addr eid, o, x, n, pro, pi, w, c, mc) ->
         get qls eid =Some (absmutexsem pr y, wl) ->
        (( y = None /\ ow = $ OS_MUTEX_AVAILABLE  ) \/
         (exists t op,  y = Some (t, op) /\ ow = op)) ->
         rv <> Vint32 ow ->
         can_change_aop P -> 
         absinfer sch 
           (<|| mutextrylock_if_null_yes (|V_eid :: V_ret :: nil|) ??
                 ( mutextrylock_if_null_owner_no (|(Vint32 i) :: V_eid :: rv :: nil|) ;; s1) ||> ** HECBList qls ** HMuxInfo mls ** P)
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
  instantiate(2:= mutextrylock_if_null_owner_no
     (|Vint32 i :: V_eid :: rv :: nil|)).
  instantiate (2:=O).
  instantiate (2:= s).
  sep pauto.
  eapply absdata_elim.
  instantiate(2:=mutextrylock_if_null_owner_no
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

Lemma mutextrylock_absimp_prioceil_before_ok: 
  forall  i eo o x n w pi pro c mc V_priocl s1 minfob sch P, 
          get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
          V_priocl =Vint32 pi -> 
         can_change_aop P -> 
         absinfer sch 
           (<||  mutextrylock_prioceil(| (Vint32 i) :: V_priocl :: nil|) ;; s1 ||>  ** HMuxInfo minfob ** P)
           (<||  s1 ||>  ** HMuxInfo minfob ** P). 
Proof.
  intros.   
  infer_solver 0%nat.  
Qed. 

Lemma mutextrylock_absimp_priocl_before_abt: 
  forall  i eo o x n w pi pro c mc V_priocl s1 minfob sch P, 
          get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
          V_priocl  <> Vint32 pi -> 
         can_change_aop P -> 
         absinfer sch 
           (<||  mutextrylock_prioceil(| (Vint32 i) :: V_priocl :: nil|) ;; s1 ||>  ** HMuxInfo minfob ** P)
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

Lemma mutextrylock_absimp_get_recurcnt_before_ok: 
  forall i eo o x n pi w pro c mc V_recnt s1 minfob sch P, 
          get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
          V_recnt =Vint32 n -> 
         can_change_aop P -> 
         absinfer sch 
           (<||  mutextrylock_get_recurcnt(|(Vint32 i) :: V_recnt :: nil|) ;; s1 ||>  ** HMuxInfo minfob ** P)
           (<||  s1 ||>  ** HMuxInfo minfob ** P). 
Proof.
  introv Hsi Heq Hcop.
  infer_solver 0%nat.
Qed. 

Lemma mutextrylock_absimp_get_recurcnt_before_abt: 
  forall i eo o x n pi w pro c mc V_recnt s1 minfob sch P, 
          get minfob i = Some (eo, o, x, n, pro, pi, w, c, mc) -> 
          V_recnt <> Vint32 n -> 
         can_change_aop P -> 
         absinfer sch 
           (<||      mutextrylock_get_recurcnt(|(Vint32 i) :: V_recnt :: nil|) ;; s1 ||>  ** HMuxInfo minfob ** P)
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

Lemma mutextrylock_absimp_if_lt_cnt_max_no_end: 
  forall i sch mls curp eid pe o tp ty cn n pi ow w pro c mc priocl V_ret P, 
         get mls i = Some (pe, o, ty, cn, pro, pi, w, c, mc) ->
        tp = (Int.repr PTHREAD_MUTEX_RECURSIVE) ->
        (ow = curp \/ priocl = curp) ->
         Int.ltu n (Int.repr (PTHREAD_MUTEX_RECURSIVE_MAX)) =false ->
         V_ret = (Vint32 (Int.repr EAGAIN)) -> 
         can_change_aop P -> 
         absinfer sch
           (<||mutextrylock_if_lt_cnt_max_yes (|(Vint32 i) :: (Vptr eid) :: (Vint32 ow) ::  (Vint32 tp) :: (Vint32 curp):: (Vint32 priocl) :: (Vint32 n) :: V_ret :: nil|) ??
                  mutextrylock_if_lt_cnt_max_no (|(Vint32 i) :: (Vptr eid) :: (Vint32 ow) ::  (Vint32 tp) :: (Vint32 curp) :: (Vint32 priocl) :: (Vint32 n) :: V_ret :: nil|) ||>  **
              HMuxInfo mls  ** P)
           (<|| END (Some (Vint32(Int.repr EAGAIN))) ||>  ** HMuxInfo mls ** P). 
Proof.
  intros.
  assert(can_change_aop( HMuxInfo mls ** P)).
  can_change_aop_solver. 
  eapply absinfer_trans.
  eapply absinfer_choice2; try eauto.
  infer_solver 0%nat.
Qed.

Lemma mutextrylock_absimp_if_lt_cnt_max_no_abt: 
  forall i pe sch mls curp eid o tp ty cn n pi ow w pro c mc priocl V_ret P, 
         get mls i = Some (pe, o, ty, cn, pro, pi, w, c, mc) ->
        tp = (Int.repr PTHREAD_MUTEX_RECURSIVE) ->
        (ow = curp \/ priocl = curp ) ->
         Int.ltu n (Int.repr (PTHREAD_MUTEX_RECURSIVE_MAX)) =false ->
         V_ret <> (Vint32 (Int.repr EAGAIN)) -> 
         can_change_aop P -> 
         absinfer sch 
           (<||mutextrylock_if_lt_cnt_max_yes (|(Vint32 i) :: (Vptr eid) :: (Vint32 ow) ::  (Vint32 tp) :: (Vint32 curp) :: (Vint32 priocl) :: (Vint32 n) :: V_ret :: nil|) ??
                  mutextrylock_if_lt_cnt_max_no (|(Vint32 i) :: (Vptr eid) :: (Vint32 ow) ::  (Vint32 tp) :: (Vint32 curp):: (Vint32 priocl) :: (Vint32 n) :: V_ret :: nil|)  ||>  **
              HMuxInfo mls ** P)
           (<|| ABORT ||>  ** HMuxInfo mls ** P). 
Proof.
  intros.
  assert(can_change_aop( HMuxInfo mls ** P)).
  can_change_aop_solver. 
  eapply absinfer_trans.
  eapply absinfer_choice2; try eauto.
  apply absinfer_abt.
  try can_change_aop_solver. 
  try can_change_aop_solver. 
  absimp_abt_solver.
Qed.

Lemma mutextrylock_absimp_if_lt_cnt_max_yes_end: 
  forall i sch mls curp eid pe o cn tp typ n pi ow w pro c mc priocl V_ret s1 P, 
         MibMod.get mls i = Some (pe, o, typ, cn, pro, pi, w, c, mc) ->
        tp = (Int.repr PTHREAD_MUTEX_RECURSIVE) ->
        (ow = curp \/ priocl = curp) ->
        Int.ltu n (Int.repr (PTHREAD_MUTEX_RECURSIVE_MAX)) = true -> 
         V_ret = (Vint32 (Int.repr 0)) -> 
         can_change_aop P -> 
         absinfer sch 
           (<||mutextrylock_if_lt_cnt_max_yes (|(Vint32 i) :: (Vptr eid) :: (Vint32 ow ) ::  (Vint32 tp) :: (Vint32 curp) :: (Vint32 priocl) :: (Vint32 n) :: V_ret :: nil|) ?? s1 ||>  **
              HMuxInfo mls ** P)
           (<|| END (Some (Vint32 (Int.repr 0))) ||>  ** 
            HMuxInfo (MibMod.set mls i (pe, o, typ, (Int.add cn Int.one), pro, pi, w, c, mc)) ** P). 
Proof.
  intros.
  subst.
  infer_solver 0%nat. 
Qed.

Lemma mutextrylock_absimp_if_lt_cnt_max_yes_abt: 
  forall i sch pe mls curp eid o ty cn tp n pi ow w pro c mc priocl V_ret s1 P, 
         get mls i = Some (pe, o, ty, cn, pro, pi, w, c, mc) ->
        tp = (Int.repr PTHREAD_MUTEX_RECURSIVE) ->
        (ow = curp \/ priocl = curp)->
         Int.ltu n (Int.repr (PTHREAD_MUTEX_RECURSIVE_MAX)) =true ->
         V_ret <> (Vint32 (Int.repr 0)) -> 
         can_change_aop P -> 
         absinfer sch 
           (<||mutextrylock_if_lt_cnt_max_yes (|(Vint32 i) :: (Vptr eid) :: (Vint32 ow) ::  (Vint32 tp) :: (Vint32 curp) :: (Vint32 priocl) :: (Vint32 n) :: V_ret :: nil|) ?? s1 ||>  **
              HMuxInfo mls ** P)
           (<|| ABORT ||>  ** HMuxInfo mls ** P). 
Proof.
  intros.
  assert(can_change_aop( HMuxInfo mls ** P)).
  can_change_aop_solver. 
  eapply absinfer_trans.
  eapply absinfer_choice1; try eauto.
  apply absinfer_abt.
  try can_change_aop_solver. 
  try can_change_aop_solver. 
  absimp_abt_solver.
Qed.

Lemma mutextrylock_absimp_ok: 
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

Lemma mutextrylock_absimp_ok2: 
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

Lemma mutextrylock_absimp_afteracc1_end:
  forall posv v' s1 eid els ow o x n pi w pro c mc minfob wl p e P sch,
    (Int.ltu posv Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = false /\ posv <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
    Int.eq (Int.repr 1) v' = true ->
    e = Vptr eid ->
    get minfob posv = Some (Valid_Addr eid, o, x, n, pro, pi, w, c, mc) ->
    get els eid = Some (absmutexsem p ow,wl) -> 
    can_change_aop P -> 
    absinfer sch
      (<|| mutextrylock_after_acc_1 (|(Vint32 posv) :: (Vint32 v') :: e :: nil|) ;; s1 ||> ** 
              HECBList els ** 
              HMuxInfo minfob ** P)
      (<|| s1 ||> ** 
          HECBList els ** 
          HMuxInfo (MibMod.set minfob posv (Valid_Addr eid, ow, x, n, pro, pi, w, c, mc)) ** P). 
Proof.
  intros.
  subst.
  infer_solver 0%nat.
Qed.

Lemma mutextrylock_absimp_afteracc1_rv_end:
  forall rv P sch,
    can_change_aop P -> 
    rv =(Vint32 (Int.repr 0)) ->
    absinfer sch
      (<|| mutextrylock_afteracc1_rv (| rv  :: nil|) ||> ** P)
      (<|| END (Some (Vint32 (Int.repr 0))) ||> ** P). 
Proof.
  intros.
  subst.
  infer_solver 0%nat.
Qed.

Lemma mutextrylock_absimp_afteracc1_rv_abt:
  forall rv P sch,
    can_change_aop P -> 
    rv <> (Vint32 (Int.repr 0)) ->
    absinfer sch
      (<|| mutextrylock_afteracc1_rv (| rv :: nil|) ||> ** P)
      (<|| ABORT ||> ** P). 
Proof.
  intros.
  apply absinfer_abt.
  try can_change_aop_solver. 
  try can_change_aop_solver. 
  absimp_abt_solver.
Qed.

Lemma mutextrylock_absimp_if_null_yes_afteracc_end:
  forall v rv P sch,
    v = Vnull ->
    rv = Vint32 (Int.repr 0) ->
    can_change_aop P -> 
    absinfer sch
      (<|| mutextrylock_if_null_yes_afteracc (|v :: rv:: nil|) ||> ** P)
      (<|| END (Some (Vint32 (Int.repr 0))) ||> ** P). 
Proof.
  intros.
  subst.
  infer_solver 0%nat.
Qed.

Lemma mutextrylock_absimp_if_null_yes_afteracc_abt:
  forall v rv P sch,
    v = Vnull ->
    rv <> Vint32 (Int.repr 0) ->
    can_change_aop P -> 
    absinfer sch
      (<|| mutextrylock_if_null_yes_afteracc (|v :: rv:: nil|) ||> ** P)
      (<|| ABORT ||> ** P). 
Proof.
  intros.
  subst.
  apply absinfer_abt.
  try can_change_aop_solver. 
  try can_change_aop_solver. 
  absimp_abt_solver.
Qed.

Lemma mutextrylock_absimp_afteracc2_end:
  forall  v v' P sch,
    Int.eq (Int.repr 1) v = false->
    v' = Vint32 (Int.repr EBUSY) ->
    can_change_aop P -> 
    absinfer sch
      (<||  mutextrylock_after_acc_2 (| (Vint32 v) :: v' :: nil|) ||> ** P)
      (<|| END (Some (Vint32 (Int.repr EBUSY))) ||> ** P). 
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutextrylock_absimp_afteracc2_abt:
  forall v v' P sch,
    Int.eq (Int.repr 1) v = false ->
    v' <> Vint32 (Int.repr EBUSY) ->
    can_change_aop P -> 
    absinfer sch
      (<|| mutextrylock_after_acc_2 (| (Vint32 v) :: v' :: nil|) ||> ** P)
      (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_abt; try eauto.
  unfolds; intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.
  unfolds.
  exists v.
  exists v'.
  subst.
  splits; try eauto.
  apply map_join_emp.
  repeat hmstep_call_consturctor.
  simpl in *.
  simpljoin.
  do 6 eexists.
  splits ; try eauto.
  eapply change_aop_rule; eauto.
Qed.

Lemma mutextrylock_absimp_ecb_placeholder_abt: 
  forall (i : int32) (sch : ossched) (v v0 v1 v' : val) (P : asrt) s0 mls o x n pro pi w c mc,
    Int.ltu i Int.zero = false /\ Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> $ (OS_USER_MAX_EVENTS / 3) ->
    get mls i = Some (Holder, o, x, n, pro, pi, w, c, mc) ->
    can_change_aop P ->
    sch ⊢  <|| (mutextrylock_get_ecb_ptr1 (|Vint32 i :: v' :: nil|) ?? 
                       mutextrylock_get_ecb_ptr2 (|Vint32 i :: v' :: nil|) ?? 
                       mutextrylock_ecb_ptr_holder_abt (|Vint32 i :: nil|));; s0 ||> **  
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

Lemma mutextrylock_absimp_get_ecb_ptr'_mismatch_abt:  
  forall i eo mls sch v' t ptrmp s0 P o x n pro pi w c mc, 
    (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
    get mls i = Some (eo, o, x, n, pro, pi, w, c, mc) ->
    ((exists eid, eo = Valid_Addr eid /\ v' <> Vptr eid) \/ eo = Null /\ v' <> Vnull) -> 
    get ptrmp t = Some (Vnull, Vnull, Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
           (<|| (mutextrylock_get_ecb_ptr1 (|Vint32 i :: v' :: nil|) ?? 
                    mutextrylock_get_ecb_ptr2 (|Vint32 i :: v' :: nil|) ?? 
                    mutextrylock_ecb_ptr_holder_abt (|Vint32 i :: nil|));; s0 ||>  ** 
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
    eapply absinfer_trans; try eapply absinfer_choice2; eauto.
    eapply absinfer_trans; try eapply absinfer_choice1; eauto.
    eapply absinfer_abt; try eauto.
    simpljoin.
    absimp_abt_solver;
    try (instantiate (3:=s); sep auto).
    apply i_ge_z; auto.
    apply i_lt_user_max_event; auto.
  -
    eapply absinfer_trans; try eapply absinfer_choice1; eauto.
    eapply absinfer_abt; try eauto.
    simpljoin.
    absimp_abt_solver;
    try (instantiate (3:=s); sep auto).
    apply i_ge_z; auto.
    apply i_lt_user_max_event; auto.
  Unshelve.
  exact None. trivial. trivial.
  exact None. trivial. trivial.
Qed.

Lemma mutextrylock_absimp_get_ecb_ptr'_ok:  
  forall i mls sch vv t ptrmp s0 P o x n pro pi w c mc eo ptrmp',
    (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
    get mls i = Some (eo, o, x, n, pro, pi, w, c, mc) ->
    ((exists eid, eo = Valid_Addr eid /\ vv = Vptr eid) \/ eo = Null /\ vv = Vnull) ->
    get ptrmp t = Some (Vnull, Vnull, Vnull) -> 
    ptrmp' = set ptrmp t (vv, Vnull, Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
           (<|| (mutextrylock_get_ecb_ptr1 (|Vint32 i :: vv :: nil|) ?? 
                   mutextrylock_get_ecb_ptr2 (|Vint32 i :: vv :: nil|) ?? 
                   mutextrylock_ecb_ptr_holder_abt (|Vint32 i :: nil|));; s0 ||>  **
              HMuxInfo mls ** HCurTCB t ** HEvPtr ptrmp ** P) 
           (<|| s0 ||>  ** HMuxInfo mls ** HCurTCB t ** HEvPtr ptrmp' ** P). 
Proof.
  intros.
  assert (Hc: forall ptrmp, can_change_aop (HMuxInfo mls ** HCurTCB t ** HEvPtr ptrmp ** P))
    by (intros; can_change_aop_solver).
  eapply absinfer_trans;
    try eapply absinfer_seq;
    try (eapply absinfer_seq_end; [idtac | idtac | eauto]; eauto);
    try eauto.
  instantiate (1:= None).
  destruct H1 as [Hptr | Hnull].
  -
    simpljoin.
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
   simpljoin.
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

Lemma mutextrylock_absimp_afteracc_ptr_end: 
  forall t ptrmp ptrmp' s sch P, 
         ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) -> 
         can_change_aop P -> 
         absinfer sch 
           (<||  mutextrylock_after_acc_ptr(|nil|);; s ||> ** HCurTCB t ** HEvPtr ptrmp ** P)
           (<|| s ||> ** HCurTCB t ** HEvPtr ptrmp' ** P). 
Proof.
  intros.
  substs.
  infer_solver 0%nat.
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

Lemma PthreadMutexTryLockPartProof:
forall
(V_mux:val) (v'0:val) (v'3:val) (v'6:val) (v4:val) (v'8:val) 
(v5:val) (v6:val) (v8:val) (v9:val) (v10 : val)
(i:int32) (j : int32) (v'45 : list val)
(x0 : int32) (v'93 : list val) (tid:addrval) er vdom vnum,
Int.ltu i ($ 0) = false ->
Int.ltu (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) i = false ->
Int.eq i (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) = false ->
{|OS_spec, GetHPrio, OSLInv, I,
fun v : option val =>
( <|| END v ||>  **
 p_local OSLInv tid init_lg **
 ((EX v12 : val, LV mutex @ (long) ∗ |-> v12) **
  (EX v12 : val, LV err @ char_t |-> v12) **
  (EX v12 : val, LV os_code_defs.pos @ long |-> v12) **
  (EX v12 : val, LV x @ char_t |-> v12) **
  (EX v12 : val, LV z @ char_t |-> v12) **
  (EX v12 : val, LV muxowner @ char_t |-> v12) **
  (EX v12 : val, LV ty @ long |-> v12) **
  (EX v12 : val, LV r @ long |-> v12) **
  (EX v12 : val, LV cpr @ char_t |-> v12) **
  (EX v12 : val, LV pric @ long |-> v12) **
  (EX v12 : val, LV p @ OS_EVENT ∗ |-> v12) **
  (EX v0 : val, LV temp_dom @ char_t |-> v0) **
  (EX v0 : val, LV temp_num @ char_t |-> v0) ** Aemp) **
 Aie true ** Ais nil ** Acs nil ** Aisr empisr ** (EX er, Aier er)) **
A_dom_lenv
  ((mutex, (long) ∗) :: (err, char_t)
      :: (os_code_defs.pos, long) :: (x, char_t)
            :: (z, char_t) :: (muxowner, char_t)
                  :: (ty, long) :: (r, long) :: (cpr, char_t)
                           :: (pric, long) :: (p, OS_EVENT ∗)
                          :: (temp_dom, char_t) :: (temp_num, char_t) :: nil), Afalse|}
|- tid
{{ <|| callacc (Vint32 i) v6 v8 v9 v10 ||>  **
  Aisr empisr **
  Aie true **
  Ais nil **
  Acs nil **
  Aier er **
  p_local OSLInv tid
    (logic_val (V$ 1)
     :: logic_val (V$ __EvLoc_normal)
        :: logic_val Vnull
           :: logic_val Vnull :: logic_val Vnull :: nil) **
  LV pric @ long |-> v5 **
  LV p @ OS_EVENT ∗ |-> nth_val' 8 v'45 **
  LV x @ char_t |-> Vint32 j **
  LV cpr @ char_t |-> v4 **
  LV ty @ long |-> nth_val' 0 v'93 **
  LV muxowner @ char_t |-> v'8 **
  LV os_code_defs.pos @ long |-> Vint32 i **
  LV r @ long |-> v'6 **
  LV z @ char_t |-> v'3 **
  LV err @ char_t |-> v'0 **
  LV mutex @ (long) ∗ |-> V_mux **
  LV temp_dom @ char_t |-> vdom **
  LV temp_num @ char_t |-> vnum **
  A_dom_lenv
    ((mutex, (long) ∗)
     :: (err, char_t)
        :: (os_code_defs.pos, long)
           :: (x, char_t)
              :: (z, char_t)
                 :: (muxowner, char_t)
                    :: (ty, long)
                       :: (r, long)
                          :: (cpr, char_t)
                             :: (pric, long)
                                :: (p, OS_EVENT ∗)
                            :: (temp_dom, char_t) :: (temp_num, char_t)  :: nil)}} ENTER_CRITICAL;ₛ
p ′ =ₑ efield (Pthread_Mutex ′ [os_code_defs.pos ′]) pevent;ₛ
OSTCBCur ′ → __OSTskMuxPtr =ₑ p ′;ₛ
EXIT_CRITICAL;ₛ
z ′ =ᶠ OSMutexAccept (·p ′·);ₛ
ENTER_CRITICAL;ₛ
OSTCBCur ′ → __OSTskMuxPtr =ₑ NULL;ₛ
EXIT_CRITICAL;ₛ
If (z ′ ==ₑ ′ 1)
{ENTER_CRITICAL;ₛ
p ′ =ₑ efield (Pthread_Mutex ′ [os_code_defs.pos ′]) pevent;ₛ
If (p ′ !=ₑ NULL)
{efield (Pthread_Mutex ′ [os_code_defs.pos ′]) mutex_owner =ₑ
 〈 char_t
 〉 ((efield (Pthread_Mutex ′ [os_code_defs.pos ′]) pevent)
    → OSEventCnt &ₑ ′ OS_MUTEX_KEEP_LOWER_8)};ₛ
EXIT_CRITICAL;ₛ
RETURN ′ 0};ₛ
RETURN ′ EBUSY {{Afalse}}.
Proof.
  intros.

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

  rename H into E1;
  rename H0 into E2;
  rename H1 into E3.
  change ($ 0) with Int.zero in E1.
  lets E3': E3.
  rewrite Hdiveq in E2,E3'.
  apply semacc_int_eq_false in E3'.

  hoare forward prim.
  hoare unfold.
(*enter critical*)
  hoare unfold.
  unfold EvtInv. unfold AMuxEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre APthreadMutex.

  hoare_assert_pure (length v'33 = ∘ (OS_USER_MAX_EVENTS / 3)).
  { get_hsat Hsat. eapply apthreadmutex_len_frm in Hsat; auto.  }
  eapply pure_split_rule'; introv Hlen.

  destruct v'42.
  eapply backward_rule1. intros.
  eapply APthreadMutex_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned i)).
  sep cancel APthreadMutex. eauto.
  rewrite Hlen.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.

  hoare unfold.
  assert (Hlemu: Int.unsigned i <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
   lets H00: muxb_corr H6 H4 E1 Hlemu. 
  destruct H00 as (ei & p1 & p2 & p3 & p4 & p5 & p6 & p7 & p8 & Hg' & H').

  hoare_lifts_trms_pre (Aop).
  hoare forward.
  eapply assign_rule_lvar.
  split; introv Hsat. sep cancel (Alvarmapsto p). eauto.
  sep auto.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  eapply new_array_type_vallist_match_split1 in H1; eauto.
  simpljoin; auto.
  eapply eq_vptr; eauto.
  intros. eexists. sep cancel p_local. simpl; eauto.

  lets Hisptr: new_array_type_vallist_match_mux_getp H1.
  lets Hmat: H1.
  eapply new_array_type_vallist_match_split1 in Hmat; eauto.
  destruct Hmat as (_ & _ & Hmat).
  lets Hvl: struct_type_vallist_match_elim_10 Hmat.
  destruct Hvl. do 9 destruct H3. subst.
  unfold V_OSMUXINFOPevent in *.
  simpl nth_val in *.
  rename x5 into vpevt.
  destruct Hisptr as (vp & Heq & Hisptr); inverts Heq.
  simpl nth_val'.

  hoare_lifts_trms_pre (tcbllsegevaux, AOSTCBList, p_local). 
  eapply backward_rule1.
  introv Hsat.
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre.  hoare_ex_intro.
  hoare_split_pure_all. subst.
  hoare_assign_evaux.
  clear -Hisptr; pure_auto.

  rename v'41 into ptrmp.
  assert (Hevptr: get ptrmp tid = Some (Vnull, Vnull, Vnull)).  
  {
    eapply join_get_get_r; eauto. eapply join_get_get_l; eauto.
    join auto.
  } 
  rename v'40 into locmp. 
  assert (Hloc: get locmp tid = Some (V$ __EvLoc_normal)).
  { eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto. join auto. } 

  assert (Hcas:  ((exists eid,
                ei = Valid_Addr eid /\ Some vp = Some (Vptr eid) /\ eid <> vhold_addr) \/
              ei = Null /\ Some vp = Some Vnull) \/
             ei = Holder /\ Some vp = Some (Vptr vhold_addr) ). 
  { clear -H'. intuition. } clear H'.
  destruct Hcas as [ Hok | Habt ].
  2: {
    destruct Habt as (Habt1 & Habt2).
    rewrite Habt1 in Hg'.
    hoare_lifts_trms_pre (Aop, absmutinfo).
    eapply abscsq_rule. apply noabs_oslinv.
    eapply mutextrylock_absimp_ecb_placeholder_abt; eauto.
    pure_auto. unfold CurTid. go. 
    eapply absinfer_eq. apply absabort_rule.
  }
  (* compose APthreadMutex *)
  eapply backward_rule1.
  introv Hsat.
  eapply APthreadMutex_select_sn_strong with (vll1:=v'42) (vll2:=v'43); eauto.
  sep cancel Pthread_Mutex. sep cancel Astruct. sep cancel Aarray_new. sep cancel Aarray_new.
  eauto.
  (* compose llsegevaux *)
  fold_evaux_mux vp.
  clear -Hisptr; pure_auto.

   assert (Hvvcs: v6 = vp \/ v6 <> vp) by tauto. 
  destruct Hvvcs as [Hvvcs | Habt].
  2: {
    hoare_lifts_trms_pre (Aop, absmutinfoid, evptrid, curtid). 
    eapply abscsq_rule. apply noabs_oslinv.
    eapply mutextrylock_absimp_get_ecb_ptr'_mismatch_abt; eauto.
    clear - Hok Habt.
    destruct Hok as [ ( eid & Hei & Heq & _) | (Hei & Heq) ] ;
    inverts Heq;
    subst ei; eauto.
    go. unfold CurTid. go.
    eapply absinfer_eq. eapply absabort_rule.
  }
  subst.
  hoare_lifts_trms_pre (Aop, absmutinfoid, curtid, evptrid).
  eapply abscsq_rule. apply noabs_oslinv.
  eapply mutextrylock_absimp_get_ecb_ptr'_ok; eauto.
  clear - Hok.
  destruct Hok as [ ( eid & Hei & Heq & _) | (Hei & Heq) ] ;
  inverts Heq;
  subst ei; eauto.
  go. unfold CurTid. go.
  eapply absinfer_eq.
  (* EXIT_CRITICAL;ₛ *)
  lets Hset: EvAuxPtrMod.get_set_same Hevptr.
  hoare forward prim. sep cancel tcbdllflag.
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
  sep cancel AMuxCap.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel llsegevaux.
  sep pauto; eauto.
  eapply evdel_nodup_normal_muxptr_preserve; eauto.
  eapply evcre_nodup_normal_muxptr_preserve; eauto.
  3: { destruct Hok as [( eid & Hei & Heq & _) | (Hei & Heq)]; inverts Heq;
         subst ei.
         eapply sem_ecb_p_muxptr_normal_preserve; eauto.
         unfold is_mux. eapply H9; eauto.
         rewrite Hset; eauto. }
  2: {  destruct Hok as [( eid & Hei & Heq & _) | (Hei & Heq)]; inverts Heq;
         subst ei.
         eapply mux_ecb_p_nuxptr_normal_preserve; eauto.
         unfold is_mux. eapply H9; eauto.
         rewrite Hset; eauto. }
  destruct Hok as [( eid & Hei & Heq & _) | (Hei & Heq)]; inverts Heq;
  subst ei.
  eapply mq_ecb_p_muxptr_normal_preserve; eauto.
  unfold is_mux. eapply H9; eauto.
  rewrite Hset; eauto.
  auto.
  pure_auto.
(*OSMutexAccept (·p ′·)*)
  hoare forward.
  clear -Hisptr; pure_auto.
  pure_auto.
  unfold retpost. introv Hsat. unfold getasrt in Hsat.
  unfold OSMutexAcceptPost in Hsat. unfold OSMutexAcceptPost' in Hsat.
  sep destruct Hsat. sep split in Hsat.
  simpljoin1. pure_auto.
  clear -Hisptr; pure_auto.

  introv Hsat.  sep pauto.
  sep cancel p_local. sep auto.
  introv Hsat.  sep pauto.
  sep cancel p_local.  sep auto.
  hoare unfold. inverts H23.

  (* ENTER_CRITICAL;ₛ *) 
  hoare forward prim.  hoare normal pre.
  hoare_ex_intro. hoare_split_pure_all.

  unfold EvtInv.  hoare normal pre. hoare_ex_intro.

  hoare_lifts_trms_pre (tcbllsegevaux, AOSTCBList, p_local). 
  eapply backward_rule1. 
  introv Hsat.
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre.  hoare_ex_intro.
  hoare_split_pure_all. subst.
  (* OSTCBCur ′ → __OSTskSemPtr =ₑ NULL;ₛ *) 
  hoare_assign_evaux.

  hoare_lifts_trms_pre (Aop, curtid, evptrid).
  eapply abscsq_rule. apply noabs_oslinv.
  eapply mutextrylock_absimp_afteracc_ptr_end; eauto.
  pure_auto. unfold CurTid. go.  eapply absinfer_eq.

  fold_evaux_mux Vnull.

  (* EXIT_CRITICAL *)
  hoare forward prim.
  sep cancel Aier.
  sep cancel tcbdllflag.
  unfold p_local. unfold LINV. unfold OSLInv. sep pauto.
  2: { splits; eauto. }
  unfold EvtInv.
  unfold tcbllsegevaux.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.  
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep pauto.
  eapply evdel_nodup_set_null3_preserve; eauto.
  eapply evcre_nodup_set_null3_preserve; eauto.
  3: { eapply sem_ecb_p_set_null3_preserve; eauto. }
  2: { eapply mux_ecb_p_set_null3_preserve; eauto. }
  eapply mq_ecb_p_set_null3_preserve; eauto.
  auto. go.
  (* end of EXIT CRITICAL *)

  (* discuss return value of OSMutexAccept *)
  simpl nth_val' in H25.
  destruct H28; subst v'51.
  (* case 1: z = 0 *)
  eapply abscsq_rule. apply noabs_oslinv.
  eapply mutextrylock_absimp_ok2; eauto.
  pure_auto. unfold CurTid. go.  eapply absinfer_eq.
  assert(Hv: v10 = Vint32 (Int.repr EBUSY) \/ v10 <> Vint32 (Int.repr EBUSY) ) by tauto.
  destruct Hv.
  2: { eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_afteracc2_abt;eauto. pure_auto. unfold CurTid. go.
  eapply absinfer_eq.
  eapply absabort_rule. }
  eapply abscsq_rule. apply noabs_oslinv.
  eapply mutextrylock_absimp_afteracc2_end;eauto. pure_auto. unfold CurTid. go.
  eapply absinfer_eq.

  hoare forward;
  change (Int.eq Int.zero ($ 1)) with false; simpl val_inj.
  hoare unfold. tryfalse.
  instantiate (1:= Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare forward.
  (* case 2 : z = 1 *)
  destruct Hisptr as [Hnull | (vp & Heq)]; subst.
  specialize (H25 (eq_refl _)); tryfalse.
  hoare forward;
  change (Int.eq Int.one ($ 1)) with true; simpl val_inj.
  instantiate(1:= Afalse).
  2: { eapply hoare_disj_afalseP_l_pre.
         hoare unfold.
         destruct H28; tryfalse. }
  hoare unfold.

  clear -E1 E2 E3 E3' Hlemu Hdiveq Hrgn3 Hrgn4.
(*If (z ′ ==ₑ ′ 1),  ENTER_CRITICAL;ₛ*)
  hoare forward prim.
  unfold EvtInv. unfold AMuxEIBs.
  hoare normal pre.  hoare_ex_intro.
  hoare_lifts_trms_pre APthreadMutex.
  destruct v'41.
  hoare_assert_pure (length v'32 = ∘ (OS_USER_MAX_EVENTS / 3)).
  { get_hsat Hsat. eapply apthreadmutex_len_frm in Hsat; auto.  }
  eapply pure_split_rule'; introv Hlen.

  eapply backward_rule1. intros.
  eapply APthreadMutex_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned i)).
  sep cancel APthreadMutex. eauto.
  rewrite Hlen.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.

  hoare unfold.
  hoare_lifts_trms_pre Aop.
  hoare forward.
  eapply assign_rule_lvar.
  split; introv Hsat. sep_lifts_trms_in Hsat (Alvarmapsto p); eauto.
  sep_lifts_trms (Alvarmapsto p); auto.
  { sep_get_rv_array_struct.
    rewrite Hdiveq; eauto.
    eapply new_array_type_vallist_match_split1 in H; eauto.
    mytac. 
  }
   { apply eq_vptr. do 2 eexists; splits; auto. }
   { sep pauto. sep cancel p_local. simpl;auto. }
  lets H00: muxb_corr H4 H2 E1 Hlemu. 
  destruct H00 as (eo & tp & i1' & i2' & i3' & i4' & i5' & i6' & i7' & Hget & H').
  assert (Hcases: ((exists eid,
              eo = Valid_Addr eid /\ V_OSMUXINFOPevent v'43 = Some (Vptr eid) /\ eid <> vhold_addr) \/
              eo = Null /\ V_OSMUXINFOPevent v'43 = Some Vnull) \/
              eo = Holder /\ V_OSMUXINFOPevent v'43 = Some (Vptr vhold_addr) ). 
  { clear -H'. intuition. } clear H'.
  eapply abscsq_rule. eapply noabs_oslinv.
  eapply mutextrylock_absimp_ok. pure_auto. eapply absinfer_eq.
  hoare_lifts_trms_pre (Aop, absmutinfo).
  destruct Hcases as [ Hok | Habt ].
   2: {
    destruct Habt as (Habt1 & Habt2).
    rewrite Habt1 in Hget.
    eapply abscsq_rule. apply noabs_oslinv.
    eapply mutextrylock_absimp_before_abt_hold; eauto.
    pure_auto.
    eapply absinfer_eq. apply absabort_rule.
  }
   assert (Hcases: ((exists eid,  eo = Valid_Addr eid /\ v8 = Vptr eid) \/ eo = Null /\ v8 = Vnull)
        \/ ( (exists eid,  eo = Valid_Addr eid /\ v8 <> Vptr eid) \/ eo = Null /\ v8 <> Vnull)).
  { destruct Hok as [( eid & Heo & _) | (Heo & _)]; subst eo.
    assert (Hv: v8 = Vptr eid \/ v8 <> Vptr eid) by tauto.
    destruct Hv; [left | right]; left; eauto.
    assert (Hv: v8 = Vnull \/ v8 <> Vnull) by tauto.
    destruct Hv; [left | right]; right; eauto. }
   inversion Hcases.
  2: { 
    eapply abscsq_rule. apply noabs_oslinv.
    eapply mutextrylock_absimp_get_before_abt_out; eauto.
    pure_auto.
    eapply absinfer_eq. apply absabort_rule. }
  eapply abscsq_rule. apply noabs_oslinv.
  eapply mutextrylock_absimp_before_ok; eauto.
  pure_auto.
  eapply absinfer_eq.

  unfold V_OSMUXINFOPevent in Hok.
  destruct Hok as [(eid & Heid) | Hnull].
  2:{
  destruct Hnull as (Heon & Hpe).
  apply nth_val_nth_val'_some_eq in Hpe; rewrite Hpe in *.
  subst eo.
  destruct H1 as [(eid' & Hev & _) | (_ & Hvn)]; tryfalse.
  subst.
  hoare forward; change (Int.notbool Int.one) with Int.zero.
  hoare_unfold. tryfalse.
  eapply hoare_disj_afalseP_l_pre.
  (* excrit *) 
  eapply backward_rule1. intros.
  eapply APthreadMutex_select_sn_ex_strong.
  exists v'41 (Z.to_nat (Int.unsigned i)) v'42 v'43.
  sep pauto.

  (* the actual EXIT_CRITICAL *) 
  hoare forward prim.
  sep cancel Aier.
  sep cancel p_local. 
  sep cancel tcbdllflag.
  unfold EvtInv.
  unfold AMuxEIBs. 
  sep normal. sep eexists.
  trycancel.
  sep cancel ASemEIBs. 
  sep cancel AMqEIBs.
  sep cancel APthreadMutex.
  sep cancel AMuxCap.
  sep cancel APthreadAttr. 
  sep cancel CapabilityInv.
  sep pauto.
  auto.
  pure_auto.

  eapply abscsq_rule. apply noabs_oslinv.
  eapply mutextrylock_absimp_ok. pure_auto. eapply absinfer_eq.
  assert(Hv: v10 = Vint32(Int.repr 0) \/ v10 <> Vint32 (Int.repr 0)) by tauto.
  destruct Hv.
  eapply abscsq_rule. apply noabs_oslinv.
  eapply mutextrylock_absimp_if_null_yes_afteracc_end ; auto.
  pure_auto. eapply absinfer_eq.
  hoare forward.
  eapply abscsq_rule. apply noabs_oslinv.
  eapply mutextrylock_absimp_if_null_yes_afteracc_abt; auto. pure_auto.
  eapply absinfer_eq. eapply absabort_rule. }

  unfold AECBList.
  hoare normal pre. hoare_ex_intro. hoare_split_pure_all.
  destruct Heid as (Hv0 & Hpid & Hne).
  destruct H1 as [(ei & Heo & Hv) | (eo' & vo)].
  2:{ rewrite Hv0 in eo'. tryfalse. }
  unfold RH_ECBlk_EIBlk_Mux_P in H6.
  lets Hget2 : H7 Hget Hv0.
  destruct Hget2 as (pip & o & wl & Hget2).
   lets Fget_ectr: ECBList_P_get_ectr_some Hget2 H9.
  destruct Fget_ectr as (Het & Hetbl & Hpetbl & Fget_ectr).
  hoare_lifts_trms_pre evsllseg.
  eapply backward_rule1. introv Hsat.
  eapply get_ectr_decompose in Hsat; eauto. hoare unfold.
  hoare_assert_pure (length v'44 = length v'46).
  { get_hsat Hsat. sep_lifts_trms_in Hsat evsllseg. eapply evsllseg_aux in Hsat. mytac. }
  eapply pure_split_rule'; intro Heqlen.
  lets Help: H9.
  eapply ecblist_p_decompose in H9; eauto.
  destruct H9 as (els1 & els2 & x' & H'').
  destruct H'' as (Hecbl1 & Hecbl2 & Hjo).
   hoare_assert_pure (x' = Vptr eid) .
  { get_hsat Hsat. sep_lifts_trms_in Hsat evsllseg.
    eapply ecblistp_evsllseg_tlsame; eauto. }
  hoare_split_pure_all. subst x'.
  lets Hecbl2': Hecbl2.
  simpl in Hecbl2'.
  destruct Hecbl2' as (vpe & Heq & Hretbl & Hrpetbl & 
                                        (ed & els2' & vptr & Hvptr & Hjos & Hed & Help2)).
  inverts Heq.
  lets Hget': EcbMod.join_sig_get Hjos.
  eapply EcbMod.join_get_r in Hget'; eauto.
  unfold get in Hget2. unfold EcbMap in Hget2.  
  rewrite Hget2 in Hget'. inverts Hget'.
  destruct v'48; simpl in Hed; tryfalse.
  destruct Hed as (Hmatch & Hrecb1 & Hrecb2 & Hrecb3 & Hpip_lt).
  unfold AEventNode. unfold AEventData.
  unfold AOSEvent; unfold node.
  hoare_assert_pure (struct_type_vallist_match OS_EVENT Het).
  { get_hsat Hsat. sep normal in Hsat. sep destruct Hsat. sep split in Hsat.
     mytac. }
  eapply pure_split_rule'; intro Hmat_evt.
  hoare unfold.
  inverts Heo.

  lets Hnarr: H.
  eapply new_array_type_vallist_match_split1 in H; eauto.
  destruct H as (Harra & Harra' & Hsp).
  lets Hsp': Hsp.
  apply struct_type_vallist_match_elim_10 in Hsp.
  destruct Hsp as (x1' & x2' & x3' & x4' & x5' & x6' & x7' & x8' & x9' & x10' & Hsp).
  subst.
  apply nth_val_nth_val'_some_eq in Hpid.
  unfold nth_val' in Hpid. subst.

  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule. apply noabs_oslinv.
  eapply mutextrylock_absimp_ok2; auto. pure_auto.
  eapply absinfer_eq.
  hoare_lifts_trms_pre (Aop, absecblsid, absmutinfoid).
  eapply abscsq_rule. apply noabs_oslinv.
  eapply mutextrylock_absimp_afteracc1_end ; eauto.
  pure_auto. eapply absinfer_eq.
  assert(Hv: v10 = (Vint32 (Int.repr 0)) \/ v10 <> (Vint32 (Int.repr 0))) by tauto.
  destruct Hv as [Hvy | Hvn].
  2:{
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_afteracc1_rv_abt;eauto.
  pure_auto. eapply absinfer_eq.
  eapply absabort_rule. }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_afteracc1_rv_end;eauto.
  pure_auto. eapply absinfer_eq.
  subst.
  (* If (p ′ !=ₑ NULL) *)
  hoare forward; change (Int.notbool Int.zero) with Int.one.
  hoare_split_pure_all.
  hoare_assign_array_struct' (Int8u).
  { introv Hsat.
     eapply cast_rv_tint32_tint8.
     eapply bop_rv.
     sep_get_rv_array_struct'.
     rewrite Hdiveq; eauto.
     simpl; eauto.
     sep cancel (Astruct (v'50, Int.zero)).  eauto.
     simpl; auto with zarith.
     go.
     sep get rv.
     simpl; eauto.
     go.
     simpl; eauto. simpl; eauto.
   }
   hoare forward.
   2: { hoare unfold. destruct H; tryfalse. }
   (* p != NULL *)
  funfold Hmatch. inverts H. rename x into i8.
  rename H1 into Hcnt; rename H31 into Hsome; rename H30 into Hnone.
  lets Heq: Htmp Hcnt.
  rewrite Heq. clear Heq.
 (*exit critical*)
  eapply backward_rule1. intros.
  eapply APthreadMutex_select_sn_ex_strong.
  exists v'41 (Z.to_nat (Int.unsigned i)) v'42
             (update_nth_val 5 (x10' :: x9' :: x8' :: x7' :: x1' :: x2' :: x3' :: x4' :: Vptr (v'50, Int.zero) :: x6' :: nil)
              (Vint32 (i8&ᵢ$ OS_MUTEX_KEEP_LOWER_8))). sep pauto.
  rewrite <- Hlen. simpl.
  rewrite app_length. rewrite app_length.
  simpl;auto. simpl.
  eapply new_array_type_vallist_match_compose_struct;eauto.
  clear -Hsp' Hcnt. simpl in Hsp'. mytac. go.

  fold_AEventNode_r.
  hoare forward prim.
  sep cancel Aier.
  sep cancel tcbdllflag. 
  sep cancel p_local.
  unfold EvtInv. 
  unfold AMuxEIBs.
  sep normal. sep eexists.
  trycancel.
  sep cancel APthreadMutex.
  sep cancel ASemEIBs. sep cancel AMqEIBs.
  sep cancel APthreadAttr.
  sep pauto; eauto.
  unfold AECBList. sep normal. eexists.
  sep cancel OSEventList.
  eapply lzh_evsllseg_compose.
  unfold AEventNode.
  sep cancel AOSEvent.
  sep cancel evsllseg. sep cancel evsllseg.
  sep cancel AMuxCap.
  sep cancel CapabilityInv.
  unfold AEventData.
  instantiate(4:=(DMutex (Vint32 i8) v0 )).
  sep split; eauto.
  unfolds; simpl ;eauto.
  auto. auto.
  eapply eibref_distinct_mux_setowner_preserve; eauto.
  eapply Q_ECB_P_setow_preserve_mux; eauto.
  eapply MUX_ECB_P_setow_preserve_mux; eauto.
  eapply SEM_ECB_P_setow_preserve_mux; eauto.
  eapply RH_ECBlk_EIBlk_Mux_P_set_owner; eauto.
  eapply MuxCapArray_P_hold; eauto.
  { assert(Hor: i8&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ OS_MUTEX_AVAILABLE \/
               i8&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE ) 
              by apply Classical_Prop.classic.
  destruct Hor as [Heq |Heq_n].
  rewrite Heq in *. specialize (Hnone (eq_refl _)).
  destruct Hnone as (Ho & Hv0).
  subst o.
  eapply EIBMAarray_P_for_update_to_owner'_n; eauto.
  apply Int.unsigned_range_2.
  lets Hn: Hsome Heq_n.
  destruct Hn as (tid' & Hv0 & Ho).
  lets Hlt: Hrecb2 Ho.
  destruct Hlt as (Hlt & Hop).
  subst o.
  eapply EIBMAarray_P_for_update_to_owner'_y; eauto.
  apply Int.unsigned_range_2.
   }
  auto.
  pure_auto.
  hoare forward.
  Unshelve.
  exact O. exact O. exact O.
Qed.

Require Import part_pos_rgn_proof.
Lemma OSMutexTrylockProof:  
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api pthread_mutex_trylock
              (mutextrylock,(Tint32,Tptr pthread_mutex_t::nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api pthread_mutex_trylock
              (mutextrylock,(Tint32,Tptr pthread_mutex_t::nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api pthread_mutex_trylock = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  do 17 (destruct v'; try apply absabort_rule).
  rename v'10 into newv1.
  rename v'11 into newv2.
  rename v'12 into er.
  rename v into V_pos.
  rename v0 into V_eid0.
  rename v1 into V_eid.
  rename v2 into V_ow.
  rename v3 into V_tp.
  rename v4 into V_curp.
  rename v5 into V_pcp.
  rename v6 into V_pevt.
  rename v7 into V_rcnt.
  rename v8 into V_err.
  rename v9 into V_afteid.
  rename v10 into V_ret.
  rename v11 into vr_temp_dom.
  rename v12 into vr_temp_num.
  rename v13 into vr_temp_dom'.
  rename v14 into vr_temp_num'.

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
    eapply mutextrylock_absimp_muxerr_abt; eauto.
    destruct H. inverts H; auto.
    do 2 destruct H. inverts H; eauto.
    can_change_aop_solver.
    apply absabort_rule.
  }
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_muxerr_cont; eauto.
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
          eapply mutextrylock_absimp_poserr_abt; eauto.
          can_change_aop_solver.
          apply absabort_rule.
        }
   subst.
   hoare abscsq.
   apply noabs_oslinv.
   eapply mutextrylock_absimp_poserr0; eauto.
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

  (* second branch: encrit; pos = *mutex; excrit *)
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
  rename v'40 into pbls.
  hoare_lifts_trms_pre (Aop, pblsid).
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply mutextrylock_absimp_mux_get_outtype_err_abt; eauto. 
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
  rename v'45 into pbls.
  hoare_lifts_trms_pre (Aop, pblsid).
   assert (Hor: get pbls x0 = None \/ (exists posv, get pbls x0 = Some posv)).
  {
    destruct (get pbls x0).
    right. eexists. eauto. 
    left. auto.
  }
  destruct Hor as [Hnone | Hsome].
  (* get pbls smadr = None *)
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mutextrylock_absimp_mux_get_none; eauto.
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
  eapply mutextrylock_absimp_mux_get_pos_abt; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.

  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_mux_get_pos_ok; eauto.
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
    with (vll1:=v'49) (hd:=v'45) (vsem:= x0) (pbls1:=v'53) (vl:=v'51)
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
   lzh_hoare_if;
  try (rewrite Hchg);
  simpl;
  pure_auto.
  rewrite Hchg in LHift_true.
  rewrite Hdiveq in LHift_true.
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
    simpljoin.
    tryfalse.
  }
  assert (Hrv: V_ret = Vint32(Int.repr EINVAL) \/ V_ret <> Vint32(Int.repr EINVAL)) by tauto.
  destruct Hrv.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_poserr0; eauto.
  can_change_aop_solver.  
  instantiate (1 := Afalse).
  apply absinfer_eq. 
  hoare forward.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_poserr_abt; eauto.
  can_change_aop_solver.
  instantiate (1 := Afalse).
  apply absinfer_eq. 
  apply absabort_rule.

  assert (Hposv_range: Int.ltu posv Int.zero = false /\ Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) posv = false /\ posv <> Int.repr (OS_USER_MAX_EVENTS / 3)).
  {
    change ($ 0) with Int.zero in *.
    rewrite Hchg in *.
    rewrite Hdiveq in *.
    destruct (Int.ltu posv Int.zero) eqn:eq1; simpl in *;
    destruct (Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) posv) eqn: eq2; simpl in *;
    destruct (Int.eq posv ($ (OS_USER_MAX_EVENTS / 3))) eqn: eq3; simpl in *;
    try (apply inteqeq in eq3; subst);
    simpl in *; auto;
    repeat (try change (Int.ltu Int.zero Int.zero) with false in *; 
                  try change (Int.ltu Int.zero Int.one) with true in *; simpl in *);
    try destruct Hif_false;
    tryfalse.
    splits; try apply sem_lab.semacc_int_eq_false; auto.
  }
  clear Hif_false.
  destruct Hposv_range as (E1 & E2 & E3).

  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mutextrylock_absimp_posok_choice; eauto.
  pure_auto.
  apply absinfer_eq.

  (* encrit *)
  lets Hposv_neq: Int.eq_false E3.
  hoare forward prim.

  unfold EvtInv.  unfold AMuxEIBs.
  hoare normal pre; hoare_ex_intro.
  destruct v'49.
  hoare_assert_pure (length v'40 = (∘ (OS_USER_MAX_EVENTS / 3))).
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
  hoare_lifts_trms_pre (Aop).
  hoare forward.
  eapply assign_rule_lvar.
  split; introv Hsat. sep cancel (Alvarmapsto p). eauto.
  sep auto.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  eapply new_array_type_vallist_match_split1 in H8; eauto.
  simpljoin; auto.
  eapply eq_vptr; eauto.
  intros. eexists. sep cancel p_local. simpl; eauto.
  rename v'50 into mutvl.
  assert (Hlemu: Int.unsigned posv <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
  lets H00: muxb_corr H0 H19 E1 Hlemu. 
  destruct H00 as (eo & tp & i1 & i2 & i3 & i4 & i5 & i6 & i7 & Hget & H').
  assert (Hcases: 
           ((exists eid,
                eo = Valid_Addr eid /\ V_OSMUXINFOPevent mutvl = Some (Vptr eid) /\ eid <> vhold_addr) \/
              eo = Null /\ V_OSMUXINFOPevent mutvl = Some Vnull) \/
             eo = Holder /\ V_OSMUXINFOPevent mutvl = Some (Vptr vhold_addr) 
         ). 
  { clear -H'. intuition. }
  clear H'.
  hoare_lifts_trms_pre (Aop, absmutinfoid).
  destruct Hcases as [ Hok | Habt ].
  2: {
    destruct Habt as (Habt1 & Habt2). rewrite Habt1 in Hget.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutextrylock_absimp_before_abt_hold; eauto.
    pure_auto. eapply absinfer_eq. apply absabort_rule.
  }
  assert (Hcases: 
      ((exists eid,  eo = Valid_Addr eid /\ V_eid0 = Vptr eid) \/ eo = Null /\ V_eid0 = Vnull)
        \/ ( (exists eid,  eo = Valid_Addr eid /\ V_eid0 <> Vptr eid) \/ eo = Null /\ V_eid0 <> Vnull)).
  {
    destruct Hok as [( eid & Heo & _) | (Heo & _)]; subst eo.
    assert (Hv: V_eid0 = Vptr eid \/ V_eid0 <> Vptr eid) by tauto.
    destruct Hv; [left | right]; left; eauto.
    assert (Hv: V_eid0 = Vnull \/ V_eid0 <> Vnull) by tauto.
    destruct Hv; [left | right]; right; eauto.
  }
  inversion Hcases.
  2: {
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutextrylock_absimp_before_abt_out; eauto.
    pure_auto. eapply absinfer_eq. apply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_before_ok; eauto.
  pure_auto.
  eapply absinfer_eq. 
  clear Hcases.

  (* excrit *) 
  eapply backward_rule1. intros.
  eapply APthreadMutex_select_sn_ex_strong.
  exists v'21 (Z.to_nat (Int.unsigned posv)) v'49 mutvl.
  sep pauto.

  (* the actual EXIT_CRITICAL *) 
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
  sep cancel AMuxCap.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.
  auto.
  pure_auto.
  (* split the mutvl as mutvl = _ :: _ :: ... :: nil *)
  rename H18 into Hveid.
  lets Hmut_vll: H8.
  rename H8 into Hmut_vl.
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
         subst.
        assert (Hrv: V_ret = Vint32 (Int.repr EINVAL) \/ V_ret <> Vint32 (Int.repr EINVAL)) by tauto.
        destruct Hrv.
        2: { hoare abscsq.
               apply noabs_oslinv.
               eapply mutextrylock_absimp_if_null_yes_abt; eauto.
               can_change_aop_solver.
               apply absabort_rule. }
        subst.
        (* If (p ′ ==ₑ NULL){RETURN ′ EINVAL};ₛ *)
        hoare forward.
        hoare unfold.
        hoare abscsq.
        apply noabs_oslinv.
        eapply mutextrylock_absimp_if_null_yes_end; eauto.
        can_change_aop_solver.
        hoare forward.
        eapply hoare_disj_afalseP_l_pre.
        hoare unfold.
        destruct H8; tryfalse.
    }
  (* p == Vptr eid *)
  destruct Hveid as [(vp & Hed & Hveid) | (Hf & _)].
  2: { clear -Hf; inverts Hf. }
  inverts Hed; subst.
  destruct vp as (vp_b & vp_i).
  (*p = Vptr (vp_b, vp_i) *)
  hoare forward.
  hoare unfold.
  tryfalse.
  instantiate (1:= Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.

  eapply abscsq_rule. apply noabs_oslinv.
  eapply mutextrylock_absimp_if_null_no; eauto.
  can_change_aop_solver. eapply absinfer_eq.

  clear -E1 E2 E3 Hposv_neq Hlemu Hrgn3 Hrgn4 Hdiveq.
  (* second get p: ENTER_CRITICAL;ₛ p ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) pevent;ₛ EXIT_CRITICAL;ₛ*)
  hoare forward prim.
  hoare unfold.

  unfold EvtInv. unfold AMuxEIBs.
  hoare normal pre; hoare_ex_intro.
  destruct v'46.
  hoare_assert_pure (length v'37 = (∘ (OS_USER_MAX_EVENTS / 3))).
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

  lets Hmls: muxb_corr H1 H15 E1 Hlemu.
  destruct Hmls as (eo & ow & tp & rcnt & prot & pcp & wq & c & mc & Hget & Hmls).
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
    eapply mutextrylock_absimp_before_abt_hold; eauto.
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
        eapply mutextrylock_absimp_get_before_abt_out; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
        }
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutextrylock_absimp_get_before_ok; eauto.
   can_change_aop_solver.
   eapply absinfer_eq.
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
        2: { eapply abscsq_rule.
               apply noabs_oslinv.
               eapply mutextrylock_absimp_if_null_yes2_abt; eauto.
               can_change_aop_solver.
               eapply absinfer_eq.
               apply absabort_rule. }
        subst.
        (* IF (p ′ !=ₑ NULL){}ELSE{ EXIT_CRITICAL;ₛ RETURN ′ EINVAL};ₛ *)
        hoare forward.
        hoare unfold.
        change (Int.notbool Int.one) with Int.zero in H6; tryfalse.
        hoare_split_pure_all.
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutextrylock_absimp_if_null_yes2_end; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        (* pre condition before excrt *)
        eapply backward_rule1. 
        introv Hsat.
        eapply APthreadMutex_select_sn_ex_strong.
        exists v'18 (Z.to_nat (Int.unsigned posv)) v'46.
        exists (Vint32 vtp
             :: Vint32 vpro
                :: Vint32 vpcp
                   :: Vint32 vwq
                      :: Vint32 vcs
                         :: Vint32 vow :: Vint32 vrcnt :: Vint32 vtsk :: Vnull :: vmc :: nil).
        sep pauto.
        (* EXIT_CRITICAL *)
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
  lets Hrmut: H4.
  unfold RH_ECBlk_EIBlk_Mux_P in H4.
  rename H4 into Heic.
  lets Hgete: Hget.
  eapply Heic in Hgete; eauto.
  destruct Hgete as (pip & o & wl & Hgete). 
  lets Fget_ectr: ECBList_P_get_ectr_some Hgete H6.
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
  inverts H29.
  rename v'53 into lpetbl.
  rename v'55 into vp_b1.

  hoare forward.
  hoare unfold.

  (*muxowner′ =ₑ〈Int8u〉( (efield (Pthread_Mutex′[pos′]) pevent) →OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8)*)
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
  destruct H4; tryfalse.
  instantiate(1:= Afalse).
  eapply hoare_disj_afalseP_r_pre.
  hoare unfold.
  hoare_assert_pure (length v'48 = length v'50).
  { get_hsat Hsat. sep_lifts_trms_in Hsat (evsllseg v'37).
     eapply evsllseg_list_len_eq in Hsat; auto. }
  eapply pure_split_rule'; intro Heqlen.
  lets Hels: H6.
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
  hoare_assert_pure (v = Vint32 i3 /\ v0 = x1).
  { unfold AEventData in H29.
      unfold V_OSEventPtr, V_OSEventCnt in *.
      simpl nth_val in *.
      sep split in H29. inverts H39. inverts H40. auto.
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
         eapply mutextrylock_absimp_if_null_owner_no_abt; eauto.
         can_change_aop_solver.
         eapply absinfer_eq.
         apply absabort_rule. }
  subst V_ow.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_if_null_owner_no_end; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  (* EXIT_CRITICAL;ₛ *)
  (* pre condition before excrt *)
   eapply backward_rule1. 
   introv Hsat.
   eapply APthreadMutex_select_sn_ex_strong.
   exists v'18 (Z.to_nat (Int.unsigned posv)) v'46.
   exists (Vint32 vtp
             :: Vint32 vpro
                :: Vint32 vpcp
                   :: Vint32 vwq
                      :: Vint32 vcs
                         :: Vint32 vow :: Vint32 vrcnt :: Vint32 vtsk :: Vptr (vp_b1, Int.zero) :: vmc :: nil).
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
     lets How_eq: Htmp H34.
     rewrite How_eq.

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

  (* get type:  ENTER_CRITICAL;ₛ ty ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) mutex_type;ₛ EXIT_CRITICAL;ₛ *)
  clear -E1 E2 E3 Hposv_neq Hlemu How_range Hdiveq Hrgn3 Hrgn4.
  (* ENTER_CRITICAL;ₛ *)
  hoare forward prim.
  hoare unfold.
   (* ty ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) mutex_type;ₛ *)
  unfold EvtInv. unfold AMuxEIBs.
  hoare normal pre; hoare_ex_intro.
  destruct v'45.
  hoare_assert_pure (length v'36 = (∘ (OS_USER_MAX_EVENTS / 3))).
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
  assert (Htp_cases: 
           (Int.eq tp ( $ PTHREAD_MUTEX_RECURSIVE) = false) \/
           (Int.eq tp ( $ PTHREAD_MUTEX_RECURSIVE) = true)
         ). 
  {  clear. 
     destruct (Int.eq tp ( $ PTHREAD_MUTEX_RECURSIVE)) eqn: eq1; auto.
   }
  destruct Hmls as (_ & _ & Hvtp_eq & _).
   unfold V_OSMUXINFOType in Hvtp_eq.
   apply nth_val_nth_val'_some_eq in Hvtp_eq.
   hoare_lifts_trms_pre (Aop, absmutinfoid).
  assert (Hvtp: V_tp = Vint32 tp \/ V_tp <> Vint32 tp) by tauto.
  destruct Hvtp.
  2: { eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutextrylock_absimp_recurtp_before_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
       }
  subst V_tp.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_recurtp_before_ok; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  (* EXIT_CRITICAL *)
  eapply backward_rule1. 
  introv Hsat.
  eapply APthreadMutex_select_sn_ex_strong.
  exists v'17 (Z.to_nat (Int.unsigned posv)) v'45 mutvl.
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
  destruct Htp_cases as [Htp_f | Htp_t].
  (* tp <> PTHREAD_MUTEX_RECURSIVE *)
  hoare forward; try rewrite Htp_f;
  pure_auto.
  simpl val_inj.
  hoare unfold.
  tryfalse.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_ok2; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  (* need PartProof Lemma *)
   eapply backward_rule1;
  [idtac | eapply PthreadMutexTryLockPartProof; eauto].
  introv Hsat.
  sep cancel Aier.
  sep pauto.
  instantiate (1:= (Vint32 tp
             :: Vint32 vpro
                :: Vint32 vpcp
                   :: Vint32 vwq
                      :: Vint32 vcs
                         :: Vint32 vow :: Vint32 vrcnt :: Vint32 vtsk :: vp :: vmc :: nil)).
  simpl; auto.
  instantiate (1:= (Vint32 tp
             :: Vint32 vpro
                :: Vint32 vpcp
                   :: Vint32 vwq
                      :: Vint32 vcs
                         :: Vint32 vow :: Vint32 vrcnt :: Vint32 vtsk :: Vptr (vp_b1, Int.zero) :: vmc :: nil)).
  simpl; auto.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  (* tp = PTHREAD_MUTEX_RECURSIVE *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_ok; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  hoare forward; pure_auto.
  hoare_split_pure_all.
  clear H6.
  instantiate (1:= 
          (Afalse \\//
        ( <||
          mutextrylock_get_recurcnt (|Vint32 posv :: V_rcnt :: nil|);;
          (mutextrylock_if_lt_cnt_max_yes
           (|Vint32 posv
             :: Vptr (vp_b1, Int.zero)
                :: Vint32 (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                   :: Vint32 tp
                      :: V_curp :: V_pcp :: V_rcnt :: V_ret :: nil|)
           ?? mutextrylock_if_lt_cnt_max_no
              (|Vint32 posv
                :: Vptr (vp_b1, Int.zero)
                   :: Vint32 (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                      :: Vint32 tp
                         :: V_curp :: V_pcp :: V_rcnt :: V_ret :: nil|))
          ?? callacc (Vint32 posv) V_pevt V_err V_afteid V_ret ||>  **
          Aisr empisr **
          Aier v'11 **
          Aie true **
          Ais nil **
          Acs nil **
          p_local OSLInv tid
            (logic_val (V$ 1)
             :: logic_val (V$ __EvLoc_normal)
                :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
          LV pric @ long |-> V_pcp **
          LV cpr @ char_t |-> V_curp **
          LV ty @ long |-> Vint32 tp **
          LV muxowner @ char_t |-> Vint32 (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) **
          LV p @ OS_EVENT ∗ |-> Vptr (vp_b1, Int.zero) **
          LV os_code_defs.pos @ long |-> Vint32 posv **
          LV x @ char_t |-> (V$ 1) **
          LV r @ long |-> v'6 **
          LV z @ char_t |-> v'3 **
          LV err @ char_t |-> v'0 **
          LV mutex @ (long) ∗ |-> Vptr x0 **
         LV temp_num @ char_t |-> vtemp_dom **
         LV temp_dom @ char_t |-> vtemp_num **
          A_dom_lenv
            ((mutex, (long) ∗)
             :: (err, char_t)
                :: (os_code_defs.pos, long)
                   :: (x, char_t)
                      :: (z, char_t)
                         :: (muxowner, char_t)
                            :: (ty, long)
                               :: (r, long)
                                  :: (cpr, char_t)
                                     :: (pric, long) :: (p, OS_EVENT ∗)
                                        :: (temp_dom, char_t) :: (temp_num, char_t) :: nil)) **
        [| Vint32 (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <> V_curp /\
            V_pcp <> V_curp |])).
  (* get curprio: ENTER_CRITICAL;ₛ cpr ′ =ₑ OSTCBCur ′ → OSTCBPrio;ₛ EXIT_CRITICAL;ₛ *)
    hoare forward prim.
    hoare unfold.
    (* cpr ′ =ₑ OSTCBCur ′ → OSTCBPrio *)
    hoare forward.
    struct_type_match_solver.
    unfold EvtInv.
    hoare unfold.
    rename i5 into curp.
    lets Hget_ct: Mbox_common.TCBListP_head_in_tcb H25.
    destruct Hget_ct as (cst & sus & Hget_ct).
    eapply TcbMod.join_get_r in Hget_ct; eauto.
    hoare_lifts_trms_pre (Aop, abstcblsid,curtid).
    assert (Hvcp: V_curp = Vint32 curp \/ V_curp <> Vint32 curp) by tauto.
    destruct Hvcp.
    2: { eapply abscsq_rule.
           apply noabs_oslinv.
           eapply mutextrylock_absimp_curprio_before_abt; eauto.
           can_change_aop_solver.
           eapply absinfer_eq.
           apply absabort_rule.
         }
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutextrylock_absimp_curprio_before_ok; eauto.
   can_change_aop_solver.
   eapply absinfer_eq.
   subst V_curp.
   rename H33 into Hcurp_range.
   (* EXIT_CRITICAL *)
   hoare forward prim.
   sep cancel Aier.
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
   sep cancel ( dllseg v'46).
   simpl dllseg.
   unfold node.
   sep pauto; try splits; eauto.
   sep cancel Astruct.
   sep cancel dllseg.
   sep cancel APthreadAttr.
   sep cancel CapabilityInv.
   eauto.
   struct_type_match_solver.
   auto.
   pure_auto.
   (* get prio_ceiling: ENTER_CRITICAL;ₛ pric ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) prio_ceiling;ₛ EXIT_CRITICAL;ₛ *)
   hoare forward prim.
   hoare unfold.
   (* pric ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) prio_ceiling *)
   clear H0 H2 Hmut_vl Hmut_vll Hrgn3 Hrgn4.

     unfold EvtInv.
     hoare normal pre; hoare_ex_intro.
     hoare_assert_pure (length v'117 = (∘ (OS_USER_MAX_EVENTS / 3))).
     { get_hsat Hsat. sep_lifts_trms_in Hsat AMuxEIBs.
       eapply length_vll_apthrmux; eauto.  }
     eapply pure_split_rule'; introv Hlen_minfo'.
     unfold AMuxEIBs.
     hoare unfold.

     hoare_lifts_trms_pre (Aop, APthreadMutex).
     destruct v'126.
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
     split; introv Hsat. sep cancel (Alvarmapsto pric). eauto.
     sep auto.
     sep_get_rv_array_struct.
     rewrite Hdiveq; eauto.
     rewrite Hdiveq; eauto.
     eapply new_array_type_vallist_match_split1 in H46; eauto.
     simpljoin; auto.
     eapply eq_int; auto.
     intros. eexists. sep cancel p_local. simpl; eauto.

  lets Hmls: muxb_corr H0 H55 E1 Hlemu.
  destruct Hmls as (eo' & ow' & tp' & rcnt' & prot' & pcp' & wq' & c' & mc' & Hget' & Hmls).
  rename v'127 into mutvl.
  destruct Hmls as (_ & _ & _ & _ & Hvpcp_eq & _).
   unfold V_OSMUXINFOPrio_ceiling in Hvpcp_eq.
   apply nth_val_nth_val'_some_eq in Hvpcp_eq.
   hoare_lifts_trms_pre (Aop, absmutinfoid).
  assert (Hvpcp: V_pcp = Vint32 pcp' \/ V_pcp <> Vint32 pcp') by tauto.
  destruct Hvpcp.
  2: { eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutextrylock_absimp_priocl_before_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
       }
  subst V_pcp.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_prioceil_before_ok; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  rewrite Hvpcp_eq.
   (* EXIT_CRITICAL *)
   eapply backward_rule1. 
   introv Hsat.
   eapply APthreadMutex_select_sn_ex_strong.
   exists v'98 (Z.to_nat (Int.unsigned posv)) v'126.
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
  lets Hmut_vll: H46.
  rename H46 into Hmut_vl.
  eapply new_array_type_vallist_match_split1 in Hmut_vl; eauto.
  destruct Hmut_vl as (_ & _ & Hmut_vl).
  lets Hmut_vl_eq: struct_type_vallist_match_mutex_info_t_imp Hmut_vl.
  destruct Hmut_vl_eq as (vtp' & vpro' & vpcp' & vwq' & vcs' & vow' & vrcnt' & vtsk' & vp' & vmc' & Hmut_vl_eq & Hvp_ptr').
  subst mutvl.
  simpl nth_val' in Hvpcp_eq. inverts Hvpcp_eq.
  simpl nth_val'.
  (* If (muxowner ′ ==ₑ cpr ′ ||ₑ pric ′ ==ₑ cpr ′) *)
  hoare forward.
  clear -How_range. pure_auto.
  clear -Hcurp_range. pure_auto.
  clear -H; pure_auto.
  clear -Hcurp_range; pure_auto.
  clear -H; pure_auto.
  clear -H; pure_auto.
  instantiate (1:= Afalse).
  hoare unfold.
  assert(His_owner: Int.eq (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) curp = true \/ Int.eq pcp' curp = true).
  { clear -H46.
    destruct (Int.eq (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) curp) eqn: eq1;
    destruct (Int.eq pcp' curp) eqn: eq2;
    simpl in H46; tryfalse; auto.
  }
  clear H46 H54 H58.
  (* get recursive_cnt: ENTER_CRITICAL;ₛ r ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) recursive_cnt;ₛ EXIT_CRITICAL;ₛ *)
   hoare forward prim.
   hoare unfold.
   (* r ′ =ₑ efield (Pthread_Mutex ′ [pos ′]) recursive_cnt *)
   clear Hmut_vl Hmut_vll.

     unfold EvtInv.
     hoare normal pre; hoare_ex_intro.
     hoare_assert_pure (length v'156 = (∘ (OS_USER_MAX_EVENTS / 3))).
     { get_hsat Hsat. sep_lifts_trms_in Hsat AMuxEIBs.
       eapply length_vll_apthrmux; eauto.  }
     eapply pure_split_rule'; introv Hlen_minfo''.
     unfold AMuxEIBs.
     hoare unfold.

     hoare_lifts_trms_pre (Aop, APthreadMutex).
     destruct v'165.
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
     sep_get_rv_array_struct.
     rewrite Hdiveq; eauto.
     rewrite Hdiveq; eauto.
     eapply new_array_type_vallist_match_split1 in H63; eauto.
     simpljoin; auto.
     eapply eq_int; auto.
     intros. eexists. sep cancel p_local. simpl; eauto.

  lets Hmls: muxb_corr H58 H72 E1 Hlemu. 
  destruct Hmls as (eo'' & ow'' & tp'' & rcnt'' & prot'' & pcp'' & wq'' & c'' & mc'' & Hget'' & Hmls).
  rename v'166 into mutvl.
  destruct Hmls as (_ & _ & _ & Hvrcnt_eq & _).
  unfold V_OSMUXINFORecursive_cnt in Hvrcnt_eq.
  apply nth_val_nth_val'_some_eq in Hvrcnt_eq.

  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_ok; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  hoare_lifts_trms_pre (Aop, absmutinfoid).
  assert (Hvrcnt: V_rcnt = Vint32 rcnt'' \/ V_rcnt <> Vint32 rcnt'') by tauto.
  destruct Hvrcnt.
  2: { eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutextrylock_absimp_get_recurcnt_before_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
       }
  subst V_rcnt.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_get_recurcnt_before_ok; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  rewrite Hvrcnt_eq.

  eapply backward_rule1. 
  introv Hsat.
  eapply APthreadMutex_select_sn_ex_strong.
  exists v'137 (Z.to_nat (Int.unsigned posv)) v'165.
  exists mutvl.
  sep pauto.
   (* discuss PTHREAD_MUTEX_RECURSIVE_MAX >ₑ r *)
   destruct (Int.ltu rcnt'' ($ PTHREAD_MUTEX_RECURSIVE_MAX)) eqn: eq1.
   (* EXIT_CRITICAL *)
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
  lets Hmut_vll: H63.
  rename H63 into Hmut_vl.
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
  rewrite eq1.
  hoare unfold.
  (* destruct (Int.ltu rcnt'' ($ PTHREAD_MUTEX_RECURSIVE_MAX)) eqn: eq1; *)
  simpl in H63; tryfalse.
  (* rcnt ++*)
  clear Hmut_vl Hmut_vll.
  hoare forward prim.
  hoare unfold.
  (* ++ efield (Pthread_Mutex ′ [pos ′]) recursive_cnt;ₛ *)

     unfold EvtInv.
     hoare normal pre; hoare_ex_intro.
     hoare_assert_pure (length v'195 = (∘ (OS_USER_MAX_EVENTS / 3))).
     { get_hsat Hsat. sep_lifts_trms_in Hsat AMuxEIBs.
       eapply length_vll_apthrmux; eauto.  }
     eapply pure_split_rule'; introv Hlen_minfo'''.
     unfold AMuxEIBs.
     hoare unfold.

     hoare_lifts_trms_pre (Aop, APthreadMutex).
     destruct v'204.
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
     rename v'205 into mutvl.
     lets Hmut_vll: H83.
     rename H83 into Hmut_vl.
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

  lets Hmls: muxb_corr H78 H92 E1 Hlemu. 
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
        eapply mutextrylock_absimp_if_lt_cnt_max_yes_abt; eauto.
        eapply inteqeq; eauto.
        destruct His_owner; [left | right]; eapply inteqeq; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
       }
  subst V_ret.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_if_lt_cnt_max_yes_end; eauto.
  eapply inteqeq; eauto.
  destruct His_owner; [left | right]; eapply inteqeq; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  (* EXIT_CRITICAL *)
  eapply backward_rule1. 
  introv Hsat.
  eapply APthreadMutex_select_sn_ex_strong.
  exists v'176 (Z.to_nat (Int.unsigned posv)) v'204.
  exists (update_nth_val 6
               (Vint32 vtp1
                :: Vint32 vpro1
                   :: Vint32 vpcp1
                      :: Vint32 vwq1
                         :: Vint32 vcs1
                            :: Vint32 vow1
                               :: Vint32 rcnt1 :: Vint32 vtsk1 :: vp1 :: vmc1 :: nil)
               (Vint32 (rcnt1 +ᵢ  $ 1))).
   sep pauto.
   clear -Hlen_minfo'''.
   rewrite <- Hlen_minfo'''.
   do 2 rewrite app_length.
   simpl length. auto.
   eapply new_array_type_vallist_match_compose_struct; eauto.

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
   eapply eibref_distinct_set_pos_muxeib_gen; eauto.
   eapply Q_ECB_P_set_mux_preserve_gen; eauto.
   eapply MUX_ECB_P_set_mux_preserve_gen; eauto.
   eapply SEM_ECB_P_set_mutex_preserve_gen; eauto.
   eapply RH_ECBlk_EIBlk_Mux_P_set_recurcnt; eauto.
   eapply MuxCapArray_P_hold; eauto.
   eapply EIBMAarray_P_recurcnt_for_update_to_recurcnt'; eauto.
   apply Int.unsigned_range_2.
   auto.
   pure_auto.
   (* RETURN ′ 0 *)
   hoare forward.
   rewrite eq1.
   hoare unfold.
   simpl in H63; destruct H63; tryfalse.
   destruct H63 as [Hsat | Hsat]; sep split in Hsat; simpl in Hsat; tryfalse.
  (* false : IF (′ PTHREAD_MUTEX_RECURSIVE_MAX >ₑ r ′) *)
  hoare_lifts_trms_pre (Aop, absmutinfoid).
  assert (Hrv: V_ret = Vint32 (Int.repr EAGAIN) \/ V_ret <> Vint32 (Int.repr EAGAIN)) by tauto.
  destruct Hrv.
  2: { eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutextrylock_absimp_if_lt_cnt_max_no_abt; eauto.
        eapply inteqeq; eauto.
        destruct His_owner; [left | right]; eapply inteqeq; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        apply absabort_rule.
       }
  subst V_ret.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_if_lt_cnt_max_no_end; eauto.
  eapply inteqeq; eauto.
  destruct His_owner; [left | right]; eapply inteqeq; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  (* EXIT_CRITICAL *)
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
  (* RETURN ′ EAGAIN *)
  hoare forward; try rewrite eq1; try simpl val_inj;
  pure_auto.
  hoare unfold. tryfalse.
  hoare_split_pure_all.
  hoare forward.
  destruct H71 as [Hsat | Hsat];
  eapply astar_l_afalse_elim in Hsat; simpl in Hsat; tryfalse.
  eapply adisj_intro.
  destruct H46; [left | right].
  eapply astar_l_afalse_elim; eauto.
  sep cancel Aier.
  sep pauto.
  clear -H54.
   destruct (Int.eq (i3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) curp) eqn: eq1;
   destruct (Int.eq pcp' curp) eqn: eq2;
   simpl in *;
   try change (Int.ltu Int.zero Int.one) with true in *;
   try change (Int.ltu Int.zero Int.zero) with false in *;
   simpl in *; (try destruct H54; tryfalse).
   eapply sem_lab.semacc_int_eq_false in eq1.
   eapply sem_lab.semacc_int_eq_false in eq2.
   pure_auto; inverts H0; [eapply eq1 | eapply eq2]; auto.
   rewrite Htp_t. simpl val_inj.
   hoare forward.
   2: { hoare unfold. destruct H6; tryfalse. }
  hoare unfold.
  hoare forward.
  hoare unfold.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutextrylock_absimp_ok2; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply backward_rule1;
  [idtac | eapply PthreadMutexTryLockPartProof; eauto].
  introv Hsat.
  sep cancel Aier.
  sep pauto.
  instantiate (1:= (Vint32 tp
             :: Vint32 vpro
                :: Vint32 vpcp
                   :: Vint32 vwq
                      :: Vint32 vcs
                         :: Vint32 vow :: Vint32 vrcnt :: Vint32 vtsk :: vp :: vmc :: nil)).
  simpl; auto.
  instantiate (1:= (Vint32 tp
             :: Vint32 vpro
                :: Vint32 vpcp
                   :: Vint32 vwq
                      :: Vint32 vcs
                         :: Vint32 vow :: Vint32 vrcnt :: Vint32 vtsk :: Vptr (vp_b1, Int.zero) :: vmc :: nil)).
  simpl; auto.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  Unshelve.
  exact Afalse.
  exact O. exact O. exact O. exact O. exact O. exact O. exact O.
Qed.


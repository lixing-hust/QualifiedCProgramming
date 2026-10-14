Require Import os_code_defs. 
Require Import code_notations. 
Require Import os_ucos_h.
Require Import ifun_spec.
Require Import abs_op.

Require Import abs_infer_step.
Require Import ucos_frmaop.
Require Import seplog_lemmas.
Require Import seplog_tactics.
Require Import abs_infer_abt.

Require Import evaux_pure.
Require Import ucos_include.
Require Import os_mutex.
Require Import OSMutex_common.
Require Import OSTimeTickPure.
Require Import mutex_pend_pure.
Require Import symbolic_lemmas.
Require Import Lia.
Require Import sem_lab.
Require Import OSQPostPure.
Require Import OSMutexPendPure1.
Require Import seplog_trm_tacs.
Require Import OSMutexPend_pure_ext.
Require Import gjb_common.
Require Import hoare_assign_tac_ext.
Require Import evauxvar_lemmas.
Require Import freeevtlist_lemmas.
Require Import hoare_forward_tac_ext.
Require Import gjb_mutex_common.
Require Import evtinv_lemmas.
Require Import sem_corecommu.

Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.


(*********************** mutex pend **************************************) 

Lemma mutexpend_absimp_null:
   forall sch vt v' P, 
    can_change_aop P ->
    v' = V$ OS_ERR_PEVENT_NULL ->
    absinfer sch
      (<|| mutexpend (Vnull :: vt :: v':: nil) ||> ** P)
      (<|| END (Some (V$ OS_ERR_PEVENT_NULL)) ||> ** P).
Proof.
infer_solver 0%nat.
Qed.

Lemma mutexpend_absimp_null':
   forall sch vt v' P s, 
    can_change_aop P ->
    v' = V$ OS_ERR_PEVENT_NULL ->
    absinfer sch
      (<|| spec_code_cons (mutexpend (Vnull :: vt :: v':: nil)) s ||> ** P)
      (<|| s ||> ** P).
Proof.
intros.
eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
2 : { eapply absinfer_seq_end; eauto. }
simpl.
infer_solver 0%nat.
Qed.

Lemma mutexpend_absimp_null_abt:
   forall sch vt v' P, 
    can_change_aop P ->
    v' <> V$ OS_ERR_PEVENT_NULL ->
    absinfer sch
      (<|| mutexpend (Vnull :: vt :: v':: nil) ||> ** P)
      (<|| ABORT ||> ** P).
Proof.
intros.
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma mutexpend_absimp_null_abt':
   forall sch vt v' P s, 
    can_change_aop P ->
    v' <> V$ OS_ERR_PEVENT_NULL ->
    absinfer sch
      (<|| spec_code_cons (mutexpend (Vnull :: vt :: v':: nil)) s ||> ** P)
      (<|| ABORT ||> ** P).
Proof.
intros.
simpl.
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma mutexpend_absimp_wrong_type:
   forall sch vt v' P mid els, 
    can_change_aop P ->
    ~(exists x y wls, get els mid = Some (absmutexsem x y, wls)) ->
    v' = V$ OS_ERR_EVENT_TYPE ->
    absinfer sch
      (<|| mutexpend (Vptr mid :: vt :: v':: nil) ||> ** HECBList els ** P)
      (<|| END (Some (V$ OS_ERR_EVENT_TYPE)) ||> ** HECBList els ** P).
Proof.
infer_solver 1%nat.
Qed.

Lemma mutexpend_absimp_wrong_type':
   forall sch vt v' P mid els s,
    can_change_aop P ->
    ~(exists x y wls, get els mid = Some (absmutexsem x y, wls)) ->
    v' = V$ OS_ERR_EVENT_TYPE ->
    absinfer sch
      (<|| spec_code_cons (mutexpend (Vptr mid :: vt :: v':: nil)) s ||> ** HECBList els ** P)
      (<|| s ||> ** HECBList els ** P).
Proof.
intros.
simpl.
assert (Hc : can_change_aop (HECBList els ** P)) by can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
2 : { eapply absinfer_seq_end; eauto. }
infer_solver 1%nat.
Qed.

Lemma mutexpend_absimp_wrong_type_abt:
   forall sch vt v' P mid els,
    can_change_aop P ->
    ~(exists x y wls, get els mid = Some (absmutexsem x y, wls)) ->
    v' <> V$ OS_ERR_EVENT_TYPE ->
    absinfer sch
      (<|| mutexpend (Vptr mid :: vt :: v':: nil) ||> ** HECBList els ** P)
      (<|| ABORT ||> ** HECBList els ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** P)) by can_change_aop_solver.
do 1 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma mutexpend_absimp_wrong_type_abt':
   forall sch vt v' P mid els s,
    can_change_aop P ->
    ~(exists x y wls, get els mid = Some (absmutexsem x y, wls)) ->
    v' <> V$ OS_ERR_EVENT_TYPE ->
    absinfer sch
      (<|| spec_code_cons (mutexpend (Vptr mid :: vt :: v':: nil)) s ||> ** HECBList els ** P)
      (<|| ABORT ||> ** HECBList els ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** P)) by can_change_aop_solver.
simpl.
do 1 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma mutexpend_absimp_idle_abt :
  forall a b P els tcbls tm curtid sch v', 
    can_change_aop P ->
    Int.unsigned b <= 65535 ->
    (exists st msg sus, TcbMod.get tcbls curtid = Some (Int.repr OS_IDLE_PRIO, st, msg, sus)) ->
       absinfer sch
      (<|| mutexpend (Vptr a ::Vint32 b:: v' :: nil) ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  do 3 destruct H1.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 2 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s); 
         instantiate (2 := mutexpend_idle_err (|Vptr a :: Vint32 b :: v' :: nil|));
         sep pauto).
Qed.

Lemma mutexpend_absimp_from_idle_abt' :
  forall a b P els tcbls tm curtid sch v' s, 
    can_change_aop P ->
    Int.unsigned b <= 65535 ->
    (exists st msg sus, TcbMod.get tcbls curtid = Some (Int.repr OS_IDLE_PRIO, st, msg, sus)) ->
       absinfer sch
      (<|| spec_code_cons (mutexpend (Vptr a ::Vint32 b:: v' :: nil)) s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  do 3 destruct H1.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 2 try(eapply absinfer_trans; try (eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try (eapply absinfer_choice1; try eauto).
  eapply absinfer_trans.
  Focus 2.
  eapply absinfer_seq_abt; try eauto.
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := mutexpend_idle_err (|Vptr a :: Vint32 b :: v' :: nil|));
         sep pauto).
Qed.

Lemma mutexpend_absimp_not_ready_abt :
  forall P els tcbls tm curtid st msg vt x prio sch v' sus,
    TcbMod.get tcbls curtid = Some (prio, st, msg, sus) ->
    ~ (st = rdy /\ sus = false) ->
    can_change_aop P ->
    absinfer sch
      (<|| mutexpend (Vptr x :: Vint32 vt :: v' :: nil) ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 3 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s); 
         instantiate (2 := mutexpend_not_ready_err (|Vptr x :: Vint32 vt :: v' :: nil|));
         sep pauto).
Qed.

Lemma mutexpend_absimp_not_ready_abt' :
  forall P els tcbls tm curtid st msg a b prio sch v' s sus,
    TcbMod.get tcbls curtid = Some (prio, st, msg, sus) ->
    ~ (st = rdy /\ sus = false) ->
    can_change_aop P ->
    absinfer sch
      (<|| spec_code_cons (mutexpend (Vptr a ::Vint32 b:: v' :: nil)) s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 3 try(eapply absinfer_trans; try (eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try (eapply absinfer_choice1; try eauto).
  eapply absinfer_trans.
  Focus 2.
  eapply absinfer_seq_abt; try eauto.
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := mutexpend_not_ready_err (|Vptr a :: Vint32 b :: v' :: nil|));
         sep pauto).
Qed.

Lemma mutexpend_absimp_curp_err_abt :
  forall P els tcbls tm curtid st msg vt x prio sch v' pip o wl sus,
    TcbMod.get tcbls curtid = Some (prio, st, msg, sus) ->
    EcbMod.get els x = Some (absmutexsem pip o, wl) ->
    Int.ltu pip prio = false ->
    can_change_aop P ->
    absinfer sch
      (<|| mutexpend (Vptr x :: Vint32 vt :: v' :: nil) ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 4 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s); 
         instantiate (2 := mutexpend_curp_err (|Vptr x :: Vint32 vt :: v' :: nil|));
         sep pauto).
Qed.

Lemma mutexpend_absimp_curp_err_abt' :
  forall P els tcbls tm curtid st msg vt x prio sch v' pip o wl s sus,
    TcbMod.get tcbls curtid = Some (prio, st, msg, sus) ->
    EcbMod.get els x = Some (absmutexsem pip o, wl) ->
    Int.ltu pip prio = false ->
    can_change_aop P ->
    absinfer sch
      (<|| spec_code_cons (mutexpend (Vptr x :: Vint32 vt :: v' :: nil)) s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 4 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_trans; try(eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := mutexpend_curp_err (|Vptr x :: Vint32 vt :: v' :: nil|));
         sep pauto).
Qed.

Lemma mutexpend_absimp_get_succ_abt :
  forall P els tcbls tm curtid st msg vt x prio sch v' pip sus,
    TcbMod.get tcbls curtid = Some (prio, st, msg, sus) ->
    EcbMod.get els x = Some (absmutexsem pip None, nil) ->
    Int.ltu pip prio = true ->
    v' <> (Vint32 (Int.repr OS_NO_ERR)) ->
    can_change_aop P ->
    absinfer sch
      (<|| mutexpend (Vptr x :: Vint32 vt :: v' :: nil) ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 5 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s); 
         instantiate (2 := mutexpend_get_succ (|Vptr x :: Vint32 vt :: v' :: nil|));
         sep pauto).
Qed.

Lemma mutexpend_absimp_get_succ_abt':
  forall P els tcbls tm curtid st msg vt x prio sch v' pip s sus,
    TcbMod.get tcbls curtid = Some (prio, st, msg, sus) ->
    EcbMod.get els x = Some (absmutexsem pip None, nil) ->
    Int.ltu pip prio = true ->
    v' <> (Vint32 (Int.repr OS_NO_ERR)) ->
    can_change_aop P ->
    absinfer sch
      (<|| spec_code_cons (mutexpend (Vptr x :: Vint32 vt :: v' :: nil)) s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 5 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_trans; try(eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := mutexpend_get_succ (|Vptr x :: Vint32 vt :: v' :: nil|));
         sep pauto).
Qed.

Lemma mutexpend_absimp_get_succ :
  forall P els tcbls tm curtid st msg vt x prio sch v' pip
                         tcblh tcbvl vhold v1 v2 v3 sus,
    TcbMod.get tcbls curtid = Some (prio, st, msg, sus) ->
    EcbMod.get els x = Some (absmutexsem pip None, nil) ->
    Int.ltu pip prio = true ->
    v' = (Vint32 (Int.repr OS_NO_ERR)) ->
    can_change_aop P ->
    absinfer sch
      (<|| mutexpend (Vptr x :: Vint32 vt :: v' :: nil) ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid **
           EvtInv_part2 els tcblh tcbvl vhold v1 v2 v3 ** P)
      (<|| END Some (Vint32 (Int.repr OS_NO_ERR)) ||> **
           HECBList (set els x (absmutexsem pip (Some (curtid, prio)), nil)) **
           HTCBList tcbls ** HTime tm ** HCurTCB curtid **
           EvtInv_part2 (set els x (absmutexsem pip (Some (curtid, prio)), nil)) tcblh tcbvl vhold v1 v2 v3 ** P).
Proof.
 infer_solver 5%nat.
unfold EvtInv_part2 in *.
unfold ASemEIBs in *.
unfold AMuxEIBs in *.
unfold AMqEIBs in *.
sep pauto.
eapply mq_ecb_p_mux_set_preserve; eauto.
eapply mux_ecb_p_mux_set_preserve; eauto.
eapply sem_ecb_p_mutex_set_preserve; eauto.
eapply RH_SEM_EINFO_ECB_P_mux_set_preserve; eauto.
eapply RH_MUX_EIB_ECB_P_mux_set_preserve; eauto.
eapply RH_EIB_ECB_Q_P_mux_set_preserve; eauto.
Qed.

Lemma mutexpend_absimp_get_succ' :
  forall P els tcbls tm curtid st msg vt x prio sch v' pip s
                tcblh tcbvl vhold v1 v2 v3 sus,
    TcbMod.get tcbls curtid = Some (prio, st, msg, sus) ->
    EcbMod.get els x = Some (absmutexsem pip None, nil) ->
    Int.ltu pip prio = true ->
    v' = (Vint32 (Int.repr OS_NO_ERR)) ->
    can_change_aop P ->
    absinfer sch
      (<|| spec_code_cons (mutexpend (Vptr x :: Vint32 vt :: v' :: nil)) s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid **
           EvtInv_part2 els tcblh tcbvl vhold v1 v2 v3 ** P)
      (<|| s ||> **
           HECBList (set els x (absmutexsem pip (Some (curtid, prio)), nil)) **
           HTCBList tcbls ** HTime tm ** HCurTCB curtid **
           EvtInv_part2 (set els x (absmutexsem pip (Some (curtid, prio)), nil)) tcblh tcbvl vhold v1 v2 v3 ** P).
Proof.
 infer_solver 5%nat.
unfold EvtInv_part2 in *.
unfold ASemEIBs in *.
unfold AMuxEIBs in *.
unfold AMqEIBs in *.
sep pauto.
eapply mq_ecb_p_mux_set_preserve; eauto.
eapply mux_ecb_p_mux_set_preserve; eauto.
eapply sem_ecb_p_mutex_set_preserve; eauto.
eapply RH_SEM_EINFO_ECB_P_mux_set_preserve; eauto.
eapply RH_MUX_EIB_ECB_P_mux_set_preserve; eauto.
eapply RH_EIB_ECB_Q_P_mux_set_preserve; eauto.
Qed.

Lemma mutexpend_absimp_curp_eq_owner_abt :
  forall a b P els tcbls tm curtid sch v' pip prio wl, 
    can_change_aop P ->
    EcbMod.get els a = Some (absmutexsem pip (Some (curtid, prio)), wl) ->
       absinfer sch
      (<|| mutexpend (Vptr a ::Vint32 b:: v' :: nil) ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 6 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
  try instantiate (3 := s); 
  try instantiate (4 := s); 
  try instantiate (2 := mutexpend_curp_eq_owner_err (|Vptr a :: Vint32 b :: v' :: nil|));
  try instantiate (3 := mutexpend_curp_eq_owner_err (|Vptr a :: Vint32 b :: v' :: nil|));
  sep pauto.
Qed.

Lemma mutexpend_absimp_curp_eq_owner_abt' :
  forall a b P els tcbls tm curtid sch v' pip prio wl s, 
    can_change_aop P ->
    EcbMod.get els a = Some (absmutexsem pip (Some (curtid, prio)), wl) ->
       absinfer sch
      (<|| spec_code_cons (mutexpend (Vptr a ::Vint32 b:: v' :: nil)) s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 6 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_trans;  try(eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
  try instantiate (3 := s0); 
  try instantiate (4 := s0); 
  try instantiate (2 := mutexpend_curp_eq_owner_err (|Vptr a :: Vint32 b :: v' :: nil|));
  try instantiate (3 := mutexpend_curp_eq_owner_err (|Vptr a :: Vint32 b :: v' :: nil|));
  sep pauto.
Qed.

Lemma mutexpend_absimp_owner_idle_abt :
  forall a b P els tcbls sch v' pip prio wl ot ost om sus, 
    can_change_aop P ->
    EcbMod.get els a = Some (absmutexsem pip (Some (ot, prio)), wl) ->
    TcbMod.get tcbls ot = Some ($ OS_IDLE_PRIO, ost, om, sus) ->
       absinfer sch
      (<|| mutexpend (Vptr a ::Vint32 b:: v' :: nil) ||> **
           HECBList els ** HTCBList tcbls ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** P)) .
  can_change_aop_solver.
  do 7 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
  instantiate (3 := s); 
  instantiate (2 := mutexpend_owner_idle_err (|Vptr a :: Vint32 b :: v' :: nil|));
  sep pauto.
Qed.

Lemma mutexpend_absimp_owner_idle_abt' :
  forall a b P els tcbls sch v' pip prio wl ot ost om s sus, 
    can_change_aop P ->
    EcbMod.get els a = Some (absmutexsem pip (Some (ot, prio)), wl) ->
    TcbMod.get tcbls ot = Some ($ OS_IDLE_PRIO, ost, om, sus) ->
       absinfer sch
      (<|| spec_code_cons (mutexpend (Vptr a ::Vint32 b:: v' :: nil)) s ||> **
           HECBList els ** HTCBList tcbls ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** P)) .
  can_change_aop_solver.
  do 7 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
   eapply absinfer_trans;  try(eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
  instantiate (3 := s0); 
  instantiate (2 := mutexpend_owner_idle_err (|Vptr a :: Vint32 b :: v' :: nil|));
  sep pauto.
Qed.

Lemma mutexpend_absimp_owner_not_ready_abt :
  forall a b P els tcbls sch v' pip prio wl ot ost om opt sus, 
    can_change_aop P ->
    EcbMod.get els a = Some (absmutexsem pip (Some (ot, prio)), wl) ->
    TcbMod.get tcbls ot = Some (opt, ost, om, sus) ->
    ~(ost = rdy /\ sus = false) ->
       absinfer sch
      (<|| mutexpend (Vptr a ::Vint32 b:: v' :: nil) ||> **
           HECBList els ** HTCBList tcbls ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** P)) .
  can_change_aop_solver.
  do 8 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
  instantiate (3 := s); 
  instantiate (2 := mutexpend_owner_not_ready_err (|Vptr a :: Vint32 b :: v' :: nil|));
  sep pauto.
Qed.

Lemma mutexpend_absimp_owner_not_ready_abt' :
  forall a b P els tcbls sch v' pip prio wl ot ost om opt s sus, 
    can_change_aop P ->
    EcbMod.get els a = Some (absmutexsem pip (Some (ot, prio)), wl) ->
    TcbMod.get tcbls ot = Some (opt, ost, om, sus) ->
    ~(ost = rdy /\ sus = false) ->
       absinfer sch
      (<|| spec_code_cons (mutexpend (Vptr a ::Vint32 b:: v' :: nil)) s ||> **
           HECBList els ** HTCBList tcbls ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** P)) .
  can_change_aop_solver.
  do 8 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
  instantiate (3 := s0); 
  instantiate (2 := mutexpend_owner_not_ready_err (|Vptr a :: Vint32 b :: v' :: nil|));
  sep pauto.
Qed.

Lemma mutexpend_absimp_block_lift :
  forall P els tcbls tm curtid vt mid prio sch v' pip cpt cst cm ot opt ost om wl ptls
                tcblh tcbvl vhold v1 v2 v3 sus sus',
    TcbMod.get tcbls curtid = Some (cpt, cst, cm, sus) ->
    TcbMod.get tcbls ot = Some (opt, ost, om, sus') ->
    EcbMod.get els mid = Some (absmutexsem pip  (Some (ot, prio)), wl) ->
    Int.eq opt pip = false ->
    Int.ltu cpt prio = true ->
    can_change_aop P ->
    absinfer sch
      (<|| mutexpend (Vptr mid :: Vint32 vt :: v' :: nil) ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** HPriotls ptls **
           EvtInv_part2 els tcblh tcbvl vhold v1 v2 v3 ** P)
      (<|| isched ;; mutexpend_after_sched (| Vptr mid :: Vint32 vt :: v' :: nil |);;
                             (mutexpend_timeout_err_rdy (| Vptr mid :: Vint32 vt :: v' :: nil |)
                              ?? mutexpend_block_get_succ (| Vptr mid :: Vint32 vt :: v' :: nil |)) ||> **
           HECBList (set els mid (absmutexsem pip (Some (ot, prio)), curtid :: wl)) **
           HTCBList (set (set tcbls curtid (cpt, wait (os_stat_mutexsem mid) (if (Int.eq vt Int.zero) then None else (Some vt)), cm, sus)) ot (pip,ost,om, sus')) ** HTime tm ** HCurTCB curtid ** 
           HPriotls (set (set ptls opt (Holder)) pip (Valid_Addr ot)) **
           EvtInv_part2 (set els mid (absmutexsem pip (Some (ot, prio)), curtid :: wl)) tcblh tcbvl vhold v1 v2 v3 ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid **
                                                               HPriotls ptls **
                                                               EvtInv_part2 els tcblh tcbvl vhold v1 v2 v3 **P)) .
  can_change_aop_solver.
  destruct (Int.eq vt Int.zero) eqn:eq1.
  eapply sem_lab.semacc_int_eq_true in eq1.
  subst.
  infer_part1 8%nat.
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  substs.
  infer_solver 1%nat.
  rewrite TcbMod.set_sem.
  rewrite H0.
  instantiate(1:= (if tidspec.beq curtid ot
 then (cpt, wait (os_stat_mutexsem mid) None, cm, sus)
 else (opt, ost, om, sus'))).
  destruct (tidspec.beq curtid ot); auto.
  eapply tidsame_trans; [idtac | eapply tidsame_set;eauto].
  eapply tidsame_trans; repeat try eapply tidsame_set; eauto.
unfold EvtInv_part2 in *.
unfold ASemEIBs in *.
unfold AMuxEIBs in *.
unfold AMqEIBs in *.
sep pauto.
eapply mq_ecb_p_mux_set_preserve; eauto.
eapply mux_ecb_p_mux_set_preserve; eauto.
eapply sem_ecb_p_mutex_set_preserve; eauto.
eapply RH_SEM_EINFO_ECB_P_mux_set_preserve; eauto.
eapply RH_MUX_EIB_ECB_P_mux_set_preserve; eauto.
eapply RH_EIB_ECB_Q_P_mux_set_preserve; eauto.
eapply sem_lab.semacc_int_eq_false in eq1.
  infer_part1 8%nat.
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  substs.
  infer_solver 1%nat.
  rewrite TcbMod.set_sem.
  rewrite H0.
  instantiate(1:= (if tidspec.beq curtid ot
 then (cpt, wait (os_stat_mutexsem mid) (Some vt), cm, sus)
 else (opt, ost, om, sus'))).
  destruct (tidspec.beq curtid ot); auto.
  eapply tidsame_trans; [idtac | eapply tidsame_set;eauto].
  eapply tidsame_trans; repeat try eapply tidsame_set; eauto.
unfold EvtInv_part2 in *.
unfold ASemEIBs in *.
unfold AMuxEIBs in *.
unfold AMqEIBs in *.
sep pauto.
eapply mq_ecb_p_mux_set_preserve; eauto.
eapply mux_ecb_p_mux_set_preserve; eauto.
eapply sem_ecb_p_mutex_set_preserve; eauto.
eapply RH_SEM_EINFO_ECB_P_mux_set_preserve; eauto.
eapply RH_MUX_EIB_ECB_P_mux_set_preserve; eauto.
eapply RH_EIB_ECB_Q_P_mux_set_preserve; eauto.
Qed.

Lemma mutexpend_absimp_block_lift' :
  forall P els tcbls tm curtid vt mid prio sch v' pip cpt cst cm ot opt ost om wl s ptls
                tcblh tcbvl vhold v1 v2 v3 sus sus',
    TcbMod.get tcbls curtid = Some (cpt, cst, cm, sus) ->
    TcbMod.get tcbls ot = Some (opt, ost, om, sus') ->
    EcbMod.get els mid = Some (absmutexsem pip  (Some (ot, prio)), wl) ->
    Int.eq opt pip = false ->
    Int.ltu cpt prio = true ->
    can_change_aop P ->
    absinfer sch
      (<|| spec_code_cons (mutexpend (Vptr mid :: Vint32 vt :: v' :: nil)) s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** HPriotls ptls **
           EvtInv_part2 els tcblh tcbvl vhold v1 v2 v3 ** P)
      (<|| isched ;; mutexpend_after_sched (| Vptr mid :: Vint32 vt :: v' :: nil |);;
                             (mutexpend_timeout_err_rdy (| Vptr mid :: Vint32 vt :: v' :: nil |) ;; s
                              ?? mutexpend_block_get_succ (| Vptr mid :: Vint32 vt :: v' :: nil |) ;; s) ||> **
           HECBList (set els mid (absmutexsem pip (Some (ot, prio)), curtid :: wl)) **
           HTCBList (set (set tcbls curtid (cpt, wait (os_stat_mutexsem mid) (if (Int.eq vt Int.zero) then None else (Some vt)), cm, sus)) ot (pip,ost,om, sus')) ** 
           HTime tm ** HCurTCB curtid **
           HPriotls (set (set ptls opt (Holder)) pip (Valid_Addr ot)) **
           EvtInv_part2 (set els mid (absmutexsem pip (Some (ot, prio)), curtid :: wl)) tcblh tcbvl vhold v1 v2 v3 ** P).
Proof.
  intros.
    assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid **
                                                               HPriotls ptls **
                                                               EvtInv_part2 els tcblh tcbvl vhold v1 v2 v3 ** P)) .
  can_change_aop_solver.
  destruct (Int.eq vt Int.zero) eqn:eq1.
  eapply sem_lab.semacc_int_eq_true in eq1.
  subst.
  infer_part1 8%nat.
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  infer_solver 1%nat.
  rewrite TcbMod.set_sem.
  rewrite H0.
  instantiate(1:= (if tidspec.beq curtid ot
 then (cpt, wait (os_stat_mutexsem mid) None, cm, sus)
 else (opt, ost, om, sus'))).
  destruct (tidspec.beq curtid ot); auto.
  eapply tidsame_trans; [idtac | eapply tidsame_set;eauto].
  eapply tidsame_trans; repeat try eapply tidsame_set; eauto.
unfold EvtInv_part2 in *.
unfold ASemEIBs in *.
unfold AMuxEIBs in *.
unfold AMqEIBs in *.
sep pauto.
eapply mq_ecb_p_mux_set_preserve; eauto.
eapply mux_ecb_p_mux_set_preserve; eauto.
eapply sem_ecb_p_mutex_set_preserve; eauto.
eapply RH_SEM_EINFO_ECB_P_mux_set_preserve; eauto.
eapply RH_MUX_EIB_ECB_P_mux_set_preserve; eauto.
eapply RH_EIB_ECB_Q_P_mux_set_preserve; eauto.
eapply sem_lab.semacc_int_eq_false in eq1.
  infer_part1 8%nat.
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  substs.
  infer_solver 1%nat.
  rewrite TcbMod.set_sem.
  rewrite H0.
  instantiate(1:= (if tidspec.beq curtid ot
 then (cpt, wait (os_stat_mutexsem mid) (Some vt), cm, sus)
 else (opt, ost, om, sus'))).
  destruct (tidspec.beq curtid ot); auto.
  eapply tidsame_trans; [idtac | eapply tidsame_set;eauto].
  eapply tidsame_trans; repeat try eapply tidsame_set; eauto.
unfold EvtInv_part2 in *.
unfold ASemEIBs in *.
unfold AMuxEIBs in *.
unfold AMqEIBs in *.
sep pauto.
eapply mq_ecb_p_mux_set_preserve; eauto.
eapply mux_ecb_p_mux_set_preserve; eauto.
eapply sem_ecb_p_mutex_set_preserve; eauto.
eapply RH_SEM_EINFO_ECB_P_mux_set_preserve; eauto.
eapply RH_MUX_EIB_ECB_P_mux_set_preserve; eauto.
eapply RH_EIB_ECB_Q_P_mux_set_preserve; eauto.
Qed.

Lemma mutexpend_absimp_block_no_lift :
  forall P els tcbls tm curtid vt mid prio sch v' pip cpt cst cm ot opt ost om wl
                tcblh tcbvl vhold v1 v2 v3 sus sus',
    TcbMod.get tcbls curtid = Some (cpt, cst, cm, sus) ->
    TcbMod.get tcbls ot = Some (opt, ost, om, sus') ->
    EcbMod.get els mid = Some (absmutexsem pip  (Some (ot, prio)), wl) ->
    ~(Int.eq opt pip = false /\ Int.ltu cpt prio = true) ->
    can_change_aop P ->
    absinfer sch
      (<|| mutexpend (Vptr mid :: Vint32 vt :: v' :: nil) ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid **
           EvtInv_part2 els tcblh tcbvl vhold v1 v2 v3 ** P)
      (<|| isched ;; mutexpend_after_sched (| Vptr mid :: Vint32 vt :: v' :: nil |);;
                             (mutexpend_timeout_err_rdy (| Vptr mid :: Vint32 vt :: v' :: nil |)
                              ?? mutexpend_block_get_succ (| Vptr mid :: Vint32 vt :: v' :: nil |)) ||> **
           HECBList (set els mid (absmutexsem pip (Some (ot, prio)), curtid :: wl)) **
           HTCBList (set tcbls curtid (cpt, wait (os_stat_mutexsem mid) (if (Int.eq vt Int.zero) then None else (Some vt)), cm, sus)) **
           HTime tm ** HCurTCB curtid **
           EvtInv_part2 (set els mid (absmutexsem pip (Some (ot, prio)), curtid :: wl)) tcblh tcbvl vhold v1 v2 v3 ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid **
                                                                EvtInv_part2 els tcblh tcbvl vhold v1 v2 v3 ** P)) .
  can_change_aop_solver.
  destruct (Int.eq vt Int.zero) eqn:eq1.
  eapply sem_lab.semacc_int_eq_true in eq1.
  subst.
  infer_part1 8%nat.
  infer_solver 1%nat.
  unfold EvtInv_part2 in *.
  unfold ASemEIBs in *.
  unfold AMuxEIBs in *.
  unfold AMqEIBs in *.
  sep pauto.
  eapply mq_ecb_p_mux_set_preserve; eauto.
  eapply mux_ecb_p_mux_set_preserve; eauto.
  eapply sem_ecb_p_mutex_set_preserve; eauto.
  eapply RH_SEM_EINFO_ECB_P_mux_set_preserve; eauto.
  eapply RH_MUX_EIB_ECB_P_mux_set_preserve; eauto.
  eapply RH_EIB_ECB_Q_P_mux_set_preserve; eauto.
  eapply sem_lab.semacc_int_eq_false in eq1.
  infer_part1 8%nat.
  infer_solver 1%nat.
  unfold EvtInv_part2 in *.
  unfold ASemEIBs in *.
  unfold AMuxEIBs in *.
  unfold AMqEIBs in *.
  sep pauto.
  eapply mq_ecb_p_mux_set_preserve; eauto.
  eapply mux_ecb_p_mux_set_preserve; eauto.
  eapply sem_ecb_p_mutex_set_preserve; eauto.
  eapply RH_SEM_EINFO_ECB_P_mux_set_preserve; eauto.
  eapply RH_MUX_EIB_ECB_P_mux_set_preserve; eauto.
  eapply RH_EIB_ECB_Q_P_mux_set_preserve; eauto.
Qed.

Lemma mutexpend_absimp_block_no_lift' :
  forall P els tcbls tm curtid vt mid prio sch v' pip cpt cst cm ot opt ost om wl s
                tcblh tcbvl vhold v1 v2 v3 sus sus',
    TcbMod.get tcbls curtid = Some (cpt, cst, cm, sus) ->
    TcbMod.get tcbls ot = Some (opt, ost, om, sus') ->
    EcbMod.get els mid = Some (absmutexsem pip  (Some (ot, prio)), wl) ->
    ~(Int.eq opt pip = false /\ Int.ltu cpt prio = true) ->
    can_change_aop P ->
    absinfer sch
      (<|| spec_code_cons (mutexpend (Vptr mid :: Vint32 vt :: v' :: nil)) s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid **
           EvtInv_part2 els tcblh tcbvl vhold v1 v2 v3 ** P)
      (<|| isched ;; mutexpend_after_sched (| Vptr mid :: Vint32 vt :: v' :: nil |);;
                             (mutexpend_timeout_err_rdy (| Vptr mid :: Vint32 vt :: v' :: nil |) ;; s
                              ?? mutexpend_block_get_succ (| Vptr mid :: Vint32 vt :: v' :: nil |) ;; s) ||> **
           HECBList (set els mid (absmutexsem pip (Some (ot, prio)), curtid :: wl)) **
           HTCBList (set tcbls curtid (cpt, wait (os_stat_mutexsem mid) (if (Int.eq vt Int.zero) then None else (Some vt)), cm, sus)) **
           HTime tm ** HCurTCB curtid **
           EvtInv_part2 (set els mid (absmutexsem pip (Some (ot, prio)), curtid :: wl)) tcblh tcbvl vhold v1 v2 v3 ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid **
                                                                EvtInv_part2 els tcblh tcbvl vhold v1 v2 v3 ** P)) .
  can_change_aop_solver.
  destruct (Int.eq vt Int.zero) eqn:eq1.
  eapply sem_lab.semacc_int_eq_true in eq1.
  subst.
  infer_part1 8%nat.
  infer_solver 1%nat.
  unfold EvtInv_part2 in *.
  unfold ASemEIBs in *.
  unfold AMuxEIBs in *.
  unfold AMqEIBs in *.
  sep pauto.
  eapply mq_ecb_p_mux_set_preserve; eauto.
  eapply mux_ecb_p_mux_set_preserve; eauto.
  eapply sem_ecb_p_mutex_set_preserve; eauto.
  eapply RH_SEM_EINFO_ECB_P_mux_set_preserve; eauto.
  eapply RH_MUX_EIB_ECB_P_mux_set_preserve; eauto.
  eapply RH_EIB_ECB_Q_P_mux_set_preserve; eauto.
  eapply sem_lab.semacc_int_eq_false in eq1.
  infer_part1 8%nat.
  infer_solver 1%nat.
  unfold EvtInv_part2 in *.
  unfold ASemEIBs in *.
  unfold AMuxEIBs in *.
  unfold AMqEIBs in *.
  sep pauto.
  eapply mq_ecb_p_mux_set_preserve; eauto.
  eapply mux_ecb_p_mux_set_preserve; eauto.
  eapply sem_ecb_p_mutex_set_preserve; eauto.
  eapply RH_SEM_EINFO_ECB_P_mux_set_preserve; eauto.
  eapply RH_MUX_EIB_ECB_P_mux_set_preserve; eauto.
  eapply RH_EIB_ECB_Q_P_mux_set_preserve; eauto.
Qed.

Lemma mutexpend_absimp_aftersch :
  forall mid P els tcbls tm curtid sch vt v' p st m s sus, 
    can_change_aop P ->
     TcbMod.get tcbls curtid = Some (p, st, m, sus) ->
      (st = rdy /\ sus = false
        \/ (st = wait (os_stat_mutexsem mid) (Some Int.zero) /\ sus = false)) ->
    absinfer sch
      (<|| mutexpend_after_sched (| Vptr mid :: Vint32 vt :: v' :: nil |);; s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexpend_absimp_aftersch_abt :
  forall mid P els tcbls tm curtid sch vt v' p st m s sus,
    can_change_aop P ->
     TcbMod.get tcbls curtid = Some (p, st, m, sus) ->
      ~(st = rdy /\ sus = false
        \/ (st = wait (os_stat_mutexsem mid) (Some Int.zero) /\ sus = false)) ->
    absinfer sch
      (<|| mutexpend_after_sched (| Vptr mid :: Vint32 vt :: v' :: nil |);; s ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
   eapply absinfer_trans; try(eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := mutexpend_after_sched (| Vptr mid :: Vint32 vt :: v' :: nil |));
         sep pauto).
Qed.

Lemma mutexpend_absimp_timeout_rdy :
   forall P els mid tm curtid tcbls v' prio m sch pip o wls vt
                 tcblh tcbvl vhold v1 v2 v3 sus,
    TcbMod.get tcbls curtid = Some (prio, wait (os_stat_mutexsem mid) (Some Int.zero), m, sus) ->
    EcbMod.get els mid = Some (absmutexsem pip o, wls) ->
    In curtid wls ->
    can_change_aop P ->
     v' = Vint32 (Int.repr OS_TIMEOUT) ->
    absinfer sch
      ( <||mutexpend_timeout_err_rdy (| Vptr mid :: Vint32 vt :: v' :: nil |)
               ?? mutexpend_block_get_succ (| Vptr mid :: Vint32 vt :: v' :: nil |) ||>  ** 
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid **
            EvtInv_part2 els tcblh tcbvl vhold v1 v2 v3 ** P) 
      (<||  END Some (Vint32 (Int.repr OS_TIMEOUT)) ||> **
            HECBList (EcbMod.set els mid (absmutexsem pip o, remove_tid curtid wls)) **
            HTCBList (TcbMod.set tcbls curtid (prio,rdy, m, false) ) ** 
            HTime tm ** HCurTCB curtid **
            EvtInv_part2 (EcbMod.set els mid (absmutexsem pip o, remove_tid curtid wls)) tcblh tcbvl vhold v1 v2 v3 ** P).
Proof.
  infer_solver 0%nat.
  unfold EvtInv_part2 in *.
  unfold ASemEIBs in *.
  unfold AMuxEIBs in *.
  unfold AMqEIBs in *.
sep pauto.
eapply mq_ecb_p_mux_set_preserve; eauto.
eapply mux_ecb_p_mux_set_preserve; eauto.
eapply sem_ecb_p_mutex_set_preserve; eauto.
eapply RH_SEM_EINFO_ECB_P_mux_set_preserve; eauto.
eapply RH_MUX_EIB_ECB_P_mux_set_preserve; eauto.
eapply RH_EIB_ECB_Q_P_mux_set_preserve; eauto.
Qed.

Lemma mutexpend_absimp_timeout_rdy' :
   forall P els mid tm curtid tcbls v' prio m sch pip o wls vt s
                 tcblh tcbvl vhold v1 v2 v3 sus,
    TcbMod.get tcbls curtid = Some (prio, wait (os_stat_mutexsem mid) (Some Int.zero), m, sus) ->
    EcbMod.get els mid = Some (absmutexsem pip o, wls) ->
    In curtid wls ->
    can_change_aop P ->
     v' = Vint32 (Int.repr OS_TIMEOUT) ->
    absinfer sch
      ( <||(mutexpend_timeout_err_rdy (| Vptr mid :: Vint32 vt :: v' :: nil |) ;; s)
               ?? (mutexpend_block_get_succ (| Vptr mid :: Vint32 vt :: v' :: nil |) ;; s) ||>  ** 
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid **
            EvtInv_part2 els tcblh tcbvl vhold v1 v2 v3 ** P)
      (<||  s ||> **
            HECBList (EcbMod.set els mid (absmutexsem pip o, remove_tid curtid wls)) **
            HTCBList (TcbMod.set tcbls curtid (prio,rdy, m, false) ) ** 
            HTime tm ** HCurTCB curtid **
            EvtInv_part2 (EcbMod.set els mid (absmutexsem pip o, remove_tid curtid wls)) tcblh tcbvl vhold v1 v2 v3 ** P).
Proof.
  infer_solver 0%nat.
  unfold EvtInv_part2 in *.
  unfold ASemEIBs in *.
  unfold AMuxEIBs in *.
  unfold AMqEIBs in *.
sep pauto.
eapply mq_ecb_p_mux_set_preserve; eauto.
eapply mux_ecb_p_mux_set_preserve; eauto.
eapply sem_ecb_p_mutex_set_preserve; eauto.
eapply RH_SEM_EINFO_ECB_P_mux_set_preserve; eauto.
eapply RH_MUX_EIB_ECB_P_mux_set_preserve; eauto.
eapply RH_EIB_ECB_Q_P_mux_set_preserve; eauto.
Qed.

Lemma mutexpend_absimp_timeout_rdy_abt' :
   forall P els mid tm curtid tcbls v' prio m sch pip o wls vt s sus,
    TcbMod.get tcbls curtid = Some (prio, wait (os_stat_mutexsem mid) (Some Int.zero), m, sus) ->
    EcbMod.get els mid = Some (absmutexsem pip o, wls) ->
    In curtid wls ->
    can_change_aop P ->
     v' <> Vint32 (Int.repr OS_TIMEOUT) ->
    absinfer sch
      ( <||(mutexpend_timeout_err_rdy (| Vptr mid :: Vint32 vt :: v' :: nil |) ;; s)
               ?? (mutexpend_block_get_succ (| Vptr mid :: Vint32 vt :: v' :: nil |) ;; s) ||>  ** 
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P) 
      (<||  ABORT ||> **
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
 intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_trans; try(eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := mutexpend_timeout_err_rdy (| Vptr mid :: Vint32 vt :: v' :: nil |));
         sep pauto).
Qed.

Lemma mutexpend_absimp_pend_succ :
   forall P els mid tm curtid tcbls v' prio m sch vt st sus,
    TcbMod.get tcbls curtid = Some (prio, st, m, sus) ->
    ~(exists wt, st = wait (os_stat_mutexsem mid) wt) ->
    can_change_aop P ->
     v' = Vint32 (Int.repr OS_NO_ERR) ->
    absinfer sch
      ( <||mutexpend_timeout_err_rdy (| Vptr mid :: Vint32 vt :: v' :: nil |)
               ?? mutexpend_block_get_succ (| Vptr mid :: Vint32 vt :: v' :: nil |) ||>  ** 
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P) 
      (<||  END Some (Vint32 (Int.repr OS_NO_ERR)) ||> **
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma mutexpend_absimp_pend_succ' :
   forall P els mid tm curtid tcbls v' prio m sch vt st s sus,
    TcbMod.get tcbls curtid = Some (prio, st, m, sus) ->
    ~(exists wt, st = wait (os_stat_mutexsem mid) wt) ->
    can_change_aop P ->
     v' = Vint32 (Int.repr OS_NO_ERR) ->
    absinfer sch
      ( <||(mutexpend_timeout_err_rdy (| Vptr mid :: Vint32 vt :: v' :: nil |) ;; s)
               ?? (mutexpend_block_get_succ (| Vptr mid :: Vint32 vt :: v' :: nil |) ;; s) ||>  ** 
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P) 
      (<||  s ||> **
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma mutexpend_absimp_pend_succ_abt' :
   forall P els mid tm curtid tcbls v' prio m sch vt st s sus,
    TcbMod.get tcbls curtid = Some (prio, st, m, sus) ->
    ~(exists wt, st = wait (os_stat_mutexsem mid) wt) ->
    can_change_aop P ->
     v' <> Vint32 (Int.repr OS_NO_ERR) ->
    absinfer sch
      ( <||(mutexpend_timeout_err_rdy (| Vptr mid :: Vint32 vt :: v' :: nil |) ;; s)
               ?? (mutexpend_block_get_succ (| Vptr mid :: Vint32 vt :: v' :: nil |) ;; s) ||>  ** 
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P) 
      (<||  ABORT ||> **
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
 intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  eapply absinfer_trans; try(eapply absinfer_choice2; try eauto).
  eapply absinfer_trans; try(eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := mutexpend_block_get_succ (| Vptr mid :: Vint32 vt :: v' :: nil |));
         sep pauto).
Qed.

(* Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope. *)


(*---------------------------------------copy--------------------------------------------------*)

(* use this old hoare_if to avoid large modification *)
Ltac lzh_find_ret_stmt stmts :=
  match stmts with
    | sseq ?s ?rs =>
      match s with
        | srete _ => constr:(some 1%nat)
        | _ => lzh_find_ret_stmt rs
      end
    | srete _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac lzh_hoare_if2 :=
  hoare_unfold;
  hoare forward; 
  match goal with
    | |- {|_, _, _, _, _, _|} |- ?ct {{?p ** [|?v <> Vint32 Int.zero /\
                                            ?v <> Vnull /\
                                            ?v <> Vundef|]}} ?stmts {{_}} =>
      (* idtac "if block proof"; *)
      let x := lzh_find_ret_stmt stmts in
        match x with
          | some _ => instantiate (1:=Afalse)
          | none _ => idtac
        end;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse

    | |- {|_, _, _, _, _, _|} |- ?ct {{_}} _ {{_}} => 
      (* idtac "if all"; *)
      hoare forward;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse
      (* first proof if-true condition, then proof if-false condition *)
    | _ => pauto
  end.

Hint Resolve CltEnvMod.beq_refl: brel .
Hint Resolve noabs_oslinv.
Hint Extern 2 (_ <= _) => apply Z.leb_le; trivial.
Require Import Mbox_common.
Require Import sempend_pure_ext.

Lemma TCBList_P_tcb_block_hold_mutex'_none:
  forall (ptcb : addrval) (v1 v2 v3 v4 v5 : val) (v6 : int32) 
         (v8 : val) (v9 v10 : int32) (v11 : val) (rtbl : vallist)
         (vl : list (list val)) (tcbls : TcbMod.map) (prio : int32)
         (st : taskstatus) (m : msg) (qid : addrval) (time ry : int32),
    TCBList_P (Vptr ptcb)
              ((v1
                  :: v2
                  :: v3
                  :: v4
                  :: v5
                  :: Vint32 v6
                  :: Vint32 prio
                  :: v8 :: Vint32 v9 :: Vint32 v10 :: v11 :: nil) :: vl)
              rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, false) ->
    prio_neq_cur tcbls ptcb prio ->
    st = rdy \/ (exists n, st = wait os_stat_time n) ->
    nth_val ∘(Int.unsigned v9) rtbl = Some (Vint32 ry) ->
    time = Int.zero ->
    TCBList_P (Vptr ptcb)
              ((v1
                  :: v2
                  :: Vptr qid
                  :: m
                  :: Vint32 time
                  :: V$OS_STAT_MUTEX
                  :: Vint32 prio
                  :: v8 :: Vint32 v9 :: Vint32 v10 :: v11 :: nil) :: vl)
              (update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (ry&ᵢInt.not v10)))
              (TcbMod.set tcbls ptcb (prio, wait (os_stat_mutexsem qid) None, m, false)).
Proof.
  introv  Htcb Htm Hst Hprio Hnth Hneq.
  unfolds in Htcb;fold TCBList_P in Htcb.
  mytac.
  inverts H.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds.
  fold TCBList_P.
  exists x x0.
  exists x1.
  exists (prio,wait (os_stat_mutexsem qid) None,m, false).
  splits; eauto.
  eapply tcbjoin_set; eauto.
{
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds in H;simpl in H; inverts H.
  unfolds.
  split.  
  unfolds.
  simpl.
  auto.
  funfold H2.
  swallow.
  auto.
  unfolds.
  do 6 eexists; splits; try unfolds; simpl; eauto.
  splits; eauto.
  pauto. (* new add *)
  eexists.
  splits.
  unfolds;simpl; eauto.
  introv Hf.
  destruct Hf as [Hf | Hf];
  inverts Hf.
  lets Hexa : tcbjoin_get H1 Htm.
  inverts Hexa.
  unfolds in H4.
  split.
  unfolds.
  intros.
  simpl_hyp.
  unfolds in H.
  destruct H.
  simpl_hyp.
  unfolds in H0.
  assert (prio&ᵢ$ 7 = prio&ᵢ$ 7) by auto.
  assert (Int.shru ( prio) ($ 3) =Int.shru (prio) ($ 3)) by auto.
  assert ( nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3)))
         (update_nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3))) rtbl
            (Vint32 (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
           Some (Vint32  (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth; eauto.
  lets Hr: H0 H H2 H5.
  rewrite Int.and_assoc in Hr.
  assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
  rewrite Int.and_commut.
  rewrite Int.and_not_self.
  auto.
  rewrite H6  in Hr.
  rewrite Int.and_zero in Hr.
  assert ( $ 1<<ᵢ(prio&ᵢ$ 7) <> $ 0) by (apply  math_prop_neq_zero2; try lia).
  unfold Int.zero in Hr.
  tryfalse.
  split.
  unfolds.
  intros.
  inverts H.
  (* new add *)
  split.
  unfolds.
  split; intros;
  inverts H0.
  split.
  unfolds.
  split; intros;
  inverts H.
  (* end of new add *)
  split.
  unfolds.
  splits; try solve [ unfolds; intros; inverts H0].
  splits; try solve [ unfolds; intros; inverts H0].
  unfolds.
  intros.
  unfolds in H.
  mytac.
  simpl_hyp.
  eexists.
  eauto.
  
  unfolds.
  intros.
  inverts H.
  false.
  inverts H5.
  eapply prio_update_self_not_in in Hnth; eauto.
  
  splits; try solve [ unfolds; intros; inverts H0].

  unfolds.
  splits; try solve [ unfolds; intros; inverts H].
  unfolds; intros.
  inverts H.
  splits; eauto.
  eexists.
  right. splits; eauto.
  unfolds; try splits; simpl; eauto.
  eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto.
  eapply prio_update_self_not_in; eauto.
  splits; try solve [ unfolds; intros; inverts H].
}
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac; simpl_hyp.
  funfold H2.
(* ** ac:   Locate update_rtbl_tcblist_hold. *)
  eapply OSTimeDlyPure.update_rtbl_tcblist_hold; eauto.
  unfolds in Hst.
  intros.
  lets Has : tcbjoin_get_getneq H1 H.
  destruct Has.
  eapply Hst; eauto.
  Unshelve.
  exact Int.zero.
Qed.

Lemma dllseg_Astruct_dllseg_compose :
  forall s v'43 v'5 x10 x9 i10 i9 i8 i7 i6 i5 i4 v'44 v'19 v'12 v'15,
  forall v'17 P,
  s |= Astruct (v'44, Int.zero) OS_TCB_flag
           (v'43
            :: v'5
               :: x10
                  :: x9
                     :: Vint32 i10
                        :: Vint32 i9
                           :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: nil) **
         dllseg v'43 (Vptr (v'44, Int.zero)) v'12 Vnull v'19 OS_TCB_flag
           (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
         dllseg v'15 Vnull v'5 (Vptr (v'44, Int.zero)) v'17 OS_TCB_flag
           (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) ** P ->
  struct_type_vallist_match OS_TCB_flag
  (v'43
   :: v'5
      :: x10
         :: x9
            :: Vint32 i10
               :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: nil) ->
  s |= tcbdllseg v'15 Vnull v'12 Vnull (v'17 ++((v'43
       :: v'5
          :: x10
             :: x9
                :: Vint32 i10
                   :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: nil)
      :: v'19)) ** P.
Proof.
   intros.
   unfold tcbdllseg.
   unfold V_OSTCBPrev.
   unfold V_OSTCBNext.
   eapply dllseg_compose.
   sep cancel (dllseg v'15).
   unfold dllseg. 
   sep auto.
   unfold node.
   sep auto.
   split; eauto.
Qed.

Lemma dllseg_Astruct_compose :
  forall s v'43 v'5 x10 x9 i10 i9 i8 i7 i6 i5 i4 v'44 v'19 v'12 ,
  forall  P,
  s |= Astruct (v'44, Int.zero) OS_TCB_flag
           (v'43
            :: v'5
               :: x10
                  :: x9
                     :: Vint32 i10
                        :: Vint32 i9
                           :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: nil) **
         dllseg v'43 (Vptr (v'44, Int.zero)) v'12 Vnull v'19 OS_TCB_flag
           (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) ** P ->
  struct_type_vallist_match OS_TCB_flag
  (v'43
   :: v'5
      :: x10
         :: x9
            :: Vint32 i10
               :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: nil) ->
s
|= dllseg (Vptr (v'44, Int.zero)) v'5 v'12 Vnull
     ((v'43
       :: v'5
          :: x10
             :: x9
                :: Vint32 i10
                   :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: nil)
      :: v'19) OS_TCB_flag (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) ** P.
Proof.
   intros.
   unfold dllseg. 
   sep auto.
   unfold node.
   sep auto.
   split; eauto.
Qed.

Lemma tcbdllseg_compose_tail_p:
  forall s v'22 v'21 v'8 x7 x6 i6 i5 i4 i3 i2 i1 i0 v'2 v'18 P,
    struct_type_vallist_match OS_TCB_flag  (v'21
                                         :: v'8
                                         :: x7
                                         :: x6
                                         :: Vint32 i6
                                         :: Vint32 i5
                                         :: Vint32 i4
                                         :: Vint32 i3
                                         :: Vint32 i2
                                         :: Vint32 i1 :: Vint32 i0 :: nil) ->
    s|=
     Astruct (v'22, Int.zero) OS_TCB_flag
     (v'21
        :: v'8
        :: x7
        :: x6
        :: Vint32 i6
        :: Vint32 i5
        :: Vint32 i4
        :: Vint32 i3
        :: Vint32 i2
        :: Vint32 i1 :: Vint32 i0 :: nil) **
     tcbdllseg (Vptr v'2) Vnull v'8 (Vptr (v'22, Int.zero)) v'18 ** P -> 
    s |= tcbdllseg (Vptr v'2) Vnull (Vptr (v'22, Int.zero)) v'21
      (v'18 ++
            (v'21
               :: v'8
               :: x7
               :: x6
               :: Vint32 i6
               :: Vint32 i5
               :: Vint32 i4
               :: Vint32 i3
               :: Vint32 i2 :: Vint32 i1 :: Vint32 i0  :: nil)
            :: nil) ** P.
Proof.
  intros. sep pauto.
  eapply tcbdllseg_compose_tail; eauto.
Qed.

Lemma tcbdllseg_split':
  forall x1 s P z v'32 x2 x3 xx,
    s |= tcbdllseg z xx v'32 Vnull (x1 ++ x2 :: x3) ** P ->
    s |= EX x v,
  tcbdllseg z xx x v x1 **
            tcbdllseg v x v'32 Vnull (x2 :: x3)** [|x1<>nil /\ nth_val 0 (last x1 nil) = Some v \/ x1 = nil /\ v = z |] ** P.
Proof.
  induction x1.
  intros.
  simpl List.app in H.
  unfold tcbdllseg at 1.
  simpl dllseg at 1.
  sep auto.
  unfold tcbdllseg in *.
  intros.
  rewrite <- List.app_comm_cons in H.
  unfold1 dllseg in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  sep lift 2%nat in H.
  remember (node z a OS_TCB ** P) as X.
  lets Hx:dllseg_head_isptr H.
  unfolds in Hx.
  destruct Hx.
  subst.
  remember (x1 ++ x2 :: x3 ) as X.
  destruct X.
  destruct x1;simpl in HeqX;tryfalse.
  unfold1 dllseg in H.
  sep split in H.
  tryfalse.
  destruct H3.
  subst.
  eapply IHx1 in H.
  unfold dllseg at 1.
  fold dllseg.
  sep auto.
  left.
  split;auto.
  (*introv Hf; tryfalse.*)
  destruct H3.
  simp join.
  simpl.
  destruct x1.
  simpl in H4;tryfalse.
  auto.
  destruct H3.
  subst. (* inverts H4.  *)
  simpl.
  unfolds in H0;auto.
Qed.

(*-----------------------------------------------------------------------------------------------*)

Lemma OSMutexPendPart_proof:
forall
(er: ier)
(vt : int32)
(vmp : int32)
(vpip : int32)
(vrdy : val)
(Hvt_range : Int.unsigned vt <= 65535)
(ct: addrval)
(ot: addrval)
(mid: addrval)
(s0 : spec_code)
(opv: val)
(* ================================= *) ,
{|OS_spec, GetHPrio, OSLInv, I,
fun v : option val =>
((EX v0 : val, LV os_code_defs.timeout @ Int16u |-> v0) **
 (EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
 (EX v0 : val, LV pip @ char_t |-> v0) **
 (EX v0 : val, LV mprio @ char_t |-> v0) **
 (EX v0 : val, LV os_code_defs.isrdy @ char_t |-> v0) **
 (EX v0 : val, LV ptcb @ OS_TCB ∗ |-> v0) ** Aemp) **
(EX (s : spec_code) (v'15 : val) (k : int32) (ptrv : val) (er : ier),
 Aie true **
 Ais nil **
 Acs nil **
 Aisr empisr **
 Aier er **
 [|logic_val opv :: logic_code s0 :: logic_val (Vptr mid) :: nil =
   logic_val v'15 :: logic_code s :: logic_val ptrv :: nil|] **
 [|v = Some v'15 /\
   v'15 = Vint32 k /\ 0 <= Int.unsigned k <= Byte.max_unsigned|] **
  <|| s ||>  **
 [| Vptr mid = Vnull -> Int.ltu Int.zero k = true |] **
 p_local OSLInv ct (logic_val (V$ 1) :: logic_val (V$ os_code_defs.__EvLoc_normal) 
                                        :: logic_val ptrv :: logic_val Vnull :: logic_val Vnull :: nil )) **
A_dom_lenv
  ((os_code_defs.timeout, Int16u)
   :: (pevent, OS_EVENT ∗)
      :: (pip, char_t)
         :: (mprio, char_t)
            :: (os_code_defs.isrdy, char_t) :: (ptcb, OS_TCB ∗) :: nil),
Afalse|}|- ct
{{ <||
  isched;;
  mutexpend_after_sched (|Vptr mid :: Vint32 vt :: opv :: nil|);;
  (mutexpend_timeout_err_rdy
   (|Vptr mid :: Vint32 vt :: opv :: nil|);; s0
   ?? mutexpend_block_get_succ
      (|Vptr mid :: Vint32 vt :: opv :: nil|);; s0) ||>  **
  Aisr empisr **
  Aie true **
  Ais nil **
  Acs nil **
  Aier er **
  p_local OSLInv ct (logic_val (V$ 1) :: logic_val (V$ os_code_defs.__EvLoc_normal) 
                                        :: logic_val (Vptr mid) :: logic_val Vnull :: logic_val Vnull :: nil ) **
  A_dom_lenv
    ((os_code_defs.timeout, Int16u)
     :: (pevent, OS_EVENT ∗)
        :: (pip, char_t)
           :: (mprio, char_t)
              :: (os_code_defs.isrdy, char_t) :: (ptcb, OS_TCB ∗) :: nil) **
  LV ptcb @ OS_TCB ∗ |-> Vptr ot **
  LV mprio @ char_t |-> Vint32 vmp **
  LV pip @ char_t |-> Vint32 vpip **
  LV os_code_defs.isrdy @ char_t |-> vrdy **
  LV os_code_defs.timeout @ Int16u |-> Vint32 vt **
  LV pevent @ OS_EVENT ∗ |-> Vptr mid}} 
OS_Sched (­);ₛ
ENTER_CRITICAL;ₛ
If (OSTCBCur ′ → OSTCBStat &ₑ ′ OS_STAT_MUTEX)
{OS_EventTO (­ pevent ′­);ₛ
EXIT_CRITICAL;ₛ
RETURN ′ OS_TIMEOUT};ₛ
OSTCBCur ′ → OSTCBEventPtr =ₑ NULL;ₛ
EXIT_CRITICAL;ₛ
RETURN ′ OS_NO_ERR {{Afalse}}.
Proof.
intros.
(* schedule *)
  hoare forward.
  unfold isflag; auto.
  pure_auto.
  intros. sep pauto. sep cancel p_local. simpl;auto.
  intros. sep pauto. sep cancel p_local. simpl;auto.
  
  (* ** ac: Print OS_SchedPost. *)
  unfold OS_SchedPost.
  unfold OS_SchedPost'.
  unfold getasrt.
  hoare_split_pure_all.
  lzh_inverts_logic.

(* enter critical *)  
  hoare forward prim.
  hoare_unfold.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  hoare_split_pure_all.
  mytac.

 rename v'10 into tcbls.
 rename v'26 into ct_b.
(* new add about the absstract stat after sched *)
 lets Fget: Mbox_common.TCBListP_head_in_tcb H8.
  destruct Fget as (st & sus & Fget).
  lets Fget': Fget.
  eapply TcbMod.join_get_r in Fget';eauto.
  eapply backward_rule1.
  introv Hsat.
  unfold EvtInv in Hsat.
  sep normal in Hsat. sep destruct Hsat.
  eapply fold_EvtInv_part2;
  (match goal with
   | |- _ |= _ => idtac
   | _ => sep split in Hsat; eauto
   end).
  trycancel_EvtInv.
  eapply fold_EvtInv_part1 in Hsat.
  sep pauto.
  unfold EvtInv_part1.
  hoare unfold.
  hoare_lifts_trms_pre (Aop, absecblist, abstcblist, ostm, oscurt).
  assert (Hst_cond: (st = rdy /\ sus = false \/ st = wait (os_stat_mutexsem mid) (Some Int.zero) /\ sus = false) 
                                        \/ ~(st = rdy /\ sus = false \/ st = wait (os_stat_mutexsem mid) (Some Int.zero) /\ sus = false)) by tauto.
  destruct Hst_cond.
  Focus 2.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexpend_absimp_aftersch_abt; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  eapply absabort_rule.
  (* (st = rdy \/ (st = wait (os_stat_mutexsem mid) (Some Int.zero)) *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexpend_absimp_aftersch; try eauto.
  can_change_aop_solver.
  apply absinfer_eq.

assert (Hvst: (i4 = ($ OS_STAT_MUTEX) /\ x7 = Vptr mid /\ 
                                i5 = Int.zero /\ prio_in_tbl i3 v'7) 
                              \/ (i4 = ($ OS_STAT_RDY) /\ x7 = Vnull)).
  {
    lets Hget_r: get_tcb_stat_rdy_sus H8 Fget.
    destruct sus eqn: eq1; destruct H22 as [(Hc1 & Heq) | (Hc3 & Heq)]; tryfalse;
    lets Hget_s: get_tcb_stat_mutex_zero H8 Fget;
    unfold V_OSTCBStat,V_OSTCBEventPtr,V_OSTCBDly in Hget_r,Hget_s;
    simpl in Hget_r,Hget_s.
    right.
    destruct Hget_r; try pauto.
    left.
    eapply Hget_s in Hc3; eauto.
    destruct Hc3 as (Heq1 & Heq2 & Heq3 & Hnin);
    inverts Heq1; inverts Heq2; inverts Heq3; auto.
  }
  rename opv into etype.
  lzh_hoare_if2.
  (*OS_TCBCurStat <> OS_STAT_MUTEX*)
  Focus 2.
  hoare forward.
  destruct Hvst as [(Hvi & Hvptr & Hvdly & Hnp) | (Hvi & Hvptr)];
  inverts Hvi; inverts Hvptr.
  clear - H23.
  rewrite Int.and_idem in *. unfold OS_STAT_MUTEX in *. destruct H23 ; pure_auto; tryfalse.

  assert (Hsus: sus = false).
  { clear -H8 Fget.
     funfold H8.
     inverts H.
     eapply TcbMod.join_sig_get in H1.
     rewrite H1 in Fget; inverts Fget.
     funfold H2.
     eapply oscore_common.tcb_stat_imp_sus_false with (stat:= $ OS_STAT_RDY); eauto.
  }
  subst sus.

  assert (Fget_st: ~(exists sid wt, st= wait (os_stat_mutexsem sid) wt)).
  {
    eapply low_stat_impl_high_stat_neq_mutex';
    unfold V_OSTCBStat, V_OSTCBPrio,V_OSTCBMsg; try eauto; try (simpl; auto).
  }

  hoare_lifts_trms_pre (Aop, absecblist, abstcblist, ostm, oscurt).
  assert (Het: etype = Vint32 (Int.repr OS_NO_ERR) 
                  \/ etype <> Vint32 (Int.repr OS_NO_ERR)) by tauto.
  destruct Het. 
  subst.
   (* etype = OS_NO_ERR  *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexpend_absimp_pend_succ'; try eauto.
  can_change_aop_solver.
  apply absinfer_eq.

  hoare_assert_pure (v'12 = vhold_addr).
  { get_hsat Hsat.
     unfold EvtInv_part2 in Hsat.
     sep normal in Hsat.
     sep destruct Hsat.
     sep split in Hsat.
     auto.
   }
  hoare_split_pure_all.
  subst.

  fold V_OSTCBPrev.
  fold V_OSTCBNext.
  hoare forward prim.
  sep_lifts_trms EvtInv.
  eapply fold_EvtInv_frm'.
  trycancel_EvtInv.
  sep cancel EvtInv_part2.
  sep cancel Aier.
  sep cancel p_local.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel AOSRdyGrp.
  sep cancel (dllseg v'1).
  unfold dllseg.
  fold dllseg.
  unfold node.
  sep pauto.
  sep cancel Astruct.
  sep cancel dllseg.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  exact_s.

  unfolds; simpl; auto.
  splits; try eauto.
  go.
  split; eauto.
  eauto.
  eauto.
  eauto.
  auto.
  pure_auto.
 
  hoare forward.
  introv Hf; tryfalse.
  (* etype <> OS_NO_ERR  *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexpend_absimp_pend_succ_abt'; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  eapply absabort_rule.

  (*OS_TCBCurStat = OS_STAT_MUTEX*)
   destruct Hvst as [(Hvi & Hvptr & Hvdly & Hnp) | (Hvi & Hvptr)];
  inverts Hvi; inverts Hvptr; try inverts Hvdly.
  Focus 2.
  clear - H23.
  change ($ OS_STAT_RDY) with Int.zero in *.
  rewrite Int.and_zero_l in H23.
  destruct H23. tryfalse.

  assert (Hst_eq: st = wait (os_stat_mutexsem mid) (Some Int.zero) ).
  {
    eapply low_stat_impl_high_stat_mutex_zero'; try eauto.
  }
  assert (Hsus: sus = false).
  { destruct H22 as [(Heq & _) | (Heq & Heq1)]; subst; inverts Hst_eq.
     auto.
  Optimize Proof.
  Optimize Heap.
  }
  subst sus.

  unfold AECBList.
  hoare unfold.
  assert (Hprange: 0<= Int.unsigned i3 < 64). 
  {
     lets cp : H8.
  destruct cp as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
  destruct asbs'.
  destruct p.
  destruct p.
  destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').

  funfold Hrsl'.
  pure_auto.
  }
  hoare_assert_pure (isptr v'1).
  { get_hsat Hsat.
     sep_lifts_trms_in Hsat (dllseg v'1).
     lets Hisp: oscore_common.dllseg_head_isptr' Hsat. auto.
  }
  eapply pure_split_rule'; introv Hptr.
  destruct Hptr as [Hnull | (tcb_head & Heq)];
  subst v'1. tryfalse.
  destruct mid as (mid_b & mid_off).
  assert (Fget_ectr: exists et etbl petbl, get_ectr (Vptr (mid_b, mid_off)) v'27 v'3 = Some (et,etbl, petbl)).
  {
    eapply tcb_eptr_get_ectr'; try eauto.
  }
   destruct Fget_ectr as (et & etbl & petbl & Fget_ectr).
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (evsllseg).
   lets Hnew: get_ectr_decompose Hsat Fget_ectr.
  clear Hsat.
  exact_s.
  hoare unfold.
    (* new add *)
  hoare_assert_pure ( struct_type_vallist_match OS_EVENT et ).
  {  get_hsat Hsat.
     unfold AEventNode in *.
     unfold AOSEvent in *.
     unfold node in *.
     sep normal in Hsat.
     sep destruct Hsat.
     sep split in Hsat.
     simpljoin. auto.
  }
  eapply pure_split_rule'; introv Hmat_ecb.
  (* end of new add *)
   (*start OS_EventTO*)
  hoare_lifts_trms_pre (Aisr, Ais).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  hoare forward.
  unfold  node.
  sep pauto.
  sep cancel Astruct.
  sep cancel AEventNode.
  sep cancel p_local.
  exact_s.

  split; auto.
  go.
  simpl; auto.
  eapply TCBList_P_RL_TCBblk_P with (l:= nil).
  rewrite nil_simp.
  eauto.
  pure_auto.

  intros.
  sep auto.
  intros.
  sep auto.

  unfold OS_EventTOPost.
  unfold OS_EventTOPost'.
  unfold getasrt. (* getasrt is meaning of notation PRE *)
  hoare_split_pure_all.
  (*end of OS_EventTO*)
  lzh_inverts_logic.
  mytac.
  inverts H31.
  rename v'38 into vy. rename v'39 into vbitx. rename v'40 into vbity.
  inverts H26. inverts H38. inverts H39.

  assert (Heg': exists pip o wls, EcbMod.get v'9 (mid_b, mid_off) = Some (absmutexsem pip o, wls) 
                                                        /\ In (ct_b, Int.zero) wls).
  {
    clear -H Fget'.
   funfold H.
  funfold H2.
  eapply H4; try eauto.
  }
  destruct Heg' as (pip & o & wls & Heg' & Hinwl).
  hoare unfold.

  assert (Het: etype = Vint32 (Int.repr OS_TIMEOUT) 
                  \/ etype <> Vint32 (Int.repr OS_TIMEOUT)) by tauto.
  destruct Het. 
  subst.
   (* etype = OS_TIMEOUT  *)
  hoare_lifts_trms_pre (Aop, absecblist, abstcblist, ostm, oscurt, EvtInv_part2).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexpend_absimp_timeout_rdy'; try eauto.
  can_change_aop_solver.
  apply absinfer_eq.

  hoare_assert_pure (v'12 = vhold_addr).
  { get_hsat Hsat.
     unfold EvtInv_part2 in Hsat.
     sep normal in Hsat.
     sep destruct Hsat.
     sep split in Hsat.
     auto.
   }
  hoare_split_pure_all.
  subst.

  fold V_OSTCBPrev.
  fold V_OSTCBNext.
  fold_AEventNode_r.
  hoare_assert_pure (get_last_tcb_ptr v'4 (Vptr tcb_head) = Some (Vptr (ct_b, Int.zero))).
  { get_hsat Hsat.
     sep_lifts_trms_in Hsat (dllseg (Vptr tcb_head)).
     eapply tcbdllseg_get_last_tcb_ptr; eauto.
   }
  eapply pure_split_rule'; introv Hget_last_ct.
  unfold node.
  unfold AOSTCBPrioTbl.
  hoare normal pre. hoare_ex_intro. 
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aisr,Ais,Aier).
  transform_pre add_aemp_isr_is_prop ltac:(sep cancel Aisr; sep cancel Ais; sep cancel Aier).
  hoare forward prim.
  sep cancel Aier.
  sep cancel p_local.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
(*   unfold AOSRdyGrp. *)
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel (dllseg (Vptr tcb_head)).
  unfold dllseg.
  fold dllseg.
  unfold node.
  unfold AOSTCBPrioTbl.
  sep pauto.
  sep cancel APthreadAttr.
  sep cancel dllseg.
  sep cancel (Astruct).
  sep cancel (Agvarenv' OSPlaceHolder).
  sep cancel (Aptrmapsto).
  sep cancel AOSRdyGrp.
  sep_lifts_trms tcbdllflag.
   eapply tcbdllflag_hold; [idtac | sep cancel tcbdllflag].
  eapply tcbdllflag_hold_middle.
  simpl; auto.
(*   sep_lifts_trms EvtInv. *)
  simpl update_nth_val.
  eapply evtinv_set_tcbvl_mid_preserve.
  2: { 
   eapply fold_EvtInv_frm'.
   trycancel_EvtInv.
   sep cancel EvtInv_part2.
  unfold AECBList.
  sep pauto.
  eapply evsllseg_compose;
  [idtac | idtac | idtac |
        sep cancel AEventNode;
       sep cancel (evsllseg v'27);
       sep cancel evsllseg]; try eauto.
  cancel_corecommuinv. 
  sep cancel CapabilityInv.
  
  (* PartitionInv *)
  Require Import sem_partition.
  cancel_partitioninv.
  eauto.
  (* end of PartitionInv *)

  (* ECBList_P *)
  assert (Hyx_eq: vy = i3 >>ᵢ $ 3 /\ vbitx = $ 1<<ᵢ(i3&ᵢ$ 7)).
  {
   lets cp : H8.
  destruct H8 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
  destruct asbs'.
  destruct p.
  destruct p.
  destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
  funfold Hrsl'.
  split; auto.
  }
  destruct Hyx_eq as (Hy_eq & Hbx_eq).
  subst vy. subst vbitx.
  eapply ECBList_P_hold_for_update_mux_to_rdy; try eauto.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat ( evsllseg v'27).
  eapply evsllseg_list_len_eq; try eauto.
  (* end of ECBList_P *)
  (* V_OSEventType v'41 = Some (V$ OS_EVENT_TYPE_MUTEX) *)
  unfolds; simpl.
  assert (Htp_case: i1 = (Int.repr OS_EVENT_TYPE_MUTEX) 
                                       \/ i1 <> (Int.repr OS_EVENT_TYPE_MUTEX) ) by tauto.

  destruct Htp_case as [Htp_eq | Hf].
  subst i1; auto.
  unfold AEventNode in *.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat (AEventData).
  eapply ecblist_p_decompose_new in H27; eauto.
  mytac.
  simpl in H43.
  mytac.
  eapply mutex_eventtype_neq_mutex in Hf; eauto.
  lets Heg'': EcbMod.join_sig_get H52.
  eapply EcbMod.join_get_r in Heg''; eauto.
  inverts H43.
  rewrite Heg' in Heg''; inverts Heg''.
  clear -Hf.
  sep split in Hf.
  false. eapply H; eauto.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat ( evsllseg v'27).
  eapply evsllseg_list_len_eq; try eauto.
   (* end of V_OSEventType *)
 }

  eapply TCBList_P_Combine; eauto.
  auto.
  Optimize Proof.
  Optimize Heap.
  eapply OSTimeDlyPure.R_PrioTbl_P_hold1; try eauto. eauto.
  unfolds; simpl; eauto.
  unfolds; simpl; auto.
  split; auto.
  split; eauto.
  (* first TCBList_P (Vptr (ct_b, Int.zero)) ... *)
  assert (Hyx_eq: vy = i3 >>ᵢ $ 3 /\ vbitx = $ 1<<ᵢ(i3&ᵢ$ 7)).
  {
   lets cp : H8.
  destruct H8 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
  destruct asbs'.
  destruct p.
  destruct p.
  destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
  funfold Hrsl'.
  split; auto.
  }
  destruct Hyx_eq as (Hy_eq & Hbx_eq).
  subst vy. subst vbitx.
  eapply TCBList_P_hold_for_update_rdy ; try eauto.
  (*sencond TCBList_P (Vptr tcb_head) ... *)
  Focus.
  assert (Hyx_eq: vy = i3 >>ᵢ $ 3 /\ vbitx = $ 1<<ᵢ(i3&ᵢ$ 7)).
  {
   lets cp : H8.
  destruct H8 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
  destruct asbs'.
  destruct p.
  destruct p.
  destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
  funfold Hrsl'.
  split; auto.
  }
  eauto.
  (* end 1 subgoal *)
  (* start subgoal join*)
  destruct H8 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
  inverts Hveq'.
  unfold TcbJoin in Htcj'.
  unfold TcbMod.joinsig.
  unfold join,sig,TcbMap in Htcj'.
  eapply TcbMod.joinsig_set_set; try eauto.

  unfold RH_CurTCB.
  rewrite TcbMod.map_get_set.
  eauto.
  (* RH_TCBList_ECBList_P *)
  eapply RH_TCBList_ECBList_P_hold_for_mux_to_rdy; try eauto.
  
  (* instantiate (1:= (A_dom_lenv
     ((timeout, Int16u)
      :: (pevent, OS_EVENT ∗)
         :: (os_code_defs.pip, char_t)
            :: (mprio, char_t) :: (os_code_defs.isrdy, char_t) :: (ptcb, OS_TCB ∗) :: nil) **
   LV ptcb @ OS_TCB ∗ |-> Vptr ot **
   LV mprio @ char_t |-> Vint32 vmp **
   LV os_code_defs.pip @ char_t |-> Vint32 vpip **
   LV os_code_defs.isrdy @ char_t |-> vrdy **
   LV timeout @ Int16u |-> Vint32 vt ** LV pevent @ OS_EVENT ∗ |-> Vptr (mid_b, mid_off))). *) 
  pure_auto.

  (*RETURN ′ OS_TIMEOUT*)
  hoare forward.

  (* etype <> OS_TIMEOUT  *)
  hoare_lifts_trms_pre (Aop, absecblist, abstcblist, ostm, oscurt).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexpend_absimp_timeout_rdy_abt'; try eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  eapply absabort_rule.
  Unshelve. trivial. trivial.

Qed.



Local Open Scope code_scope.

Lemma OSMutexPend_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSMutexPend
                  vl logicl OSMutexPendPre ct->
      Some r =
      BuildRetI os_internal OSMutexPend vl logicl OSMutexPendPost ct->
      exists t d1 d2 s,
        os_internal OSMutexPend = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  rename v'6 into er.
  rename v'4 into opv.
  rename i into vt.
  rename H1 into Hvt_range.
  change  ((x0 :: Vint32 vt :: nil) ++ opv :: nil) with  (x0 :: Vint32 vt :: opv :: nil).
  subst.
  inverts H0.
  rename v'5 into x0.
  destruct H2.
  (* x0 = Vnull *)
  subst.
  assert (Hopv: opv = V$ OS_ERR_PEVENT_NULL \/ opv <> V$ OS_ERR_PEVENT_NULL ) by tauto.
  destruct Hopv.
  2 :{
        hoare abscsq.
        apply noabs_oslinv.
        eapply mutexpend_absimp_null_abt'; eauto.
        can_change_aop_solver.
        eapply absabort_rule.
  }
  subst opv.
  hoare forward prim.
  hoare forward.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexpend_absimp_null'; eauto.
  can_change_aop_solver.
  hoare forward prim.
  eauto. auto.
  pure_auto.
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  destruct H1; tryfalse.
  (* x0 = Vptr mid *)
  destruct H as ((mid_b & mid_i) & H).
  subst.
  hoare forward prim.
  hoare unfold.
  hoare forward.
  hoare unfold.
  tryfalse.
(*   instantiate (1:= Afalse). *)
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.

  (* new add *)
  unfold EvtInv.
  hoare normal pre.
  hoare_ex_intro.
  hoare_lifts_trms_pre R_Q_Data_P.
  apply pure_split_rule'; introv Hrqdata.
  hoare unfold.
  rename v'41 into locmp.
  rename v'42 into ptrmp.
  rename v'12 into els.
  rename v'24 into fecbh.
  rename v'25 into fecbvl.
  rename v'36 into semeibs.
  rename v'37 into muxeibs.
  rename v'38 into mqeibs.
  hoare_assert_pure (get ptrmp ct = Some (Vptr (mid_b, mid_i), Vnull, Vnull)
                                             /\ get locmp ct = Some (V$ os_code_defs.__EvLoc_normal)).
  { get_hsat Hsat.
     sep_lifts_trms_in Hsat (evlocid, evptrid, tcbllsegevaux, AOSTCBList,p_local).
    eapply get_aux;eauto.
   }
  hoare_split_pure_all.
  destruct H2 as (Hget_ptr & Hget_loc).

  assert (Hevt: is_evt els (mid_b, mid_i) \/ ptr_in_ecblist (Vptr (mid_b, mid_i)) fecbh fecbvl).  
  { eapply mux_ecb_nml; eauto. }

  destruct Hevt as [Hevt | Hfree]. 
  Focus 2.
  (* pevent points into list of free ECBs *)
  assert (Hfecbh_eq: exists p, fecbh = Vptr p).
  {
    unfold ptr_in_ecblist in Hfree.
    lets Hptr: ptr_in_ecbsllseg_ptr Hfree.
    eauto.
  }
  destruct Hfecbh_eq as ( (fb & fi) & Heq).
  subst fecbh.
  eapply backward_rule1.
  introv Hsat.
  unfold AOSEventFreeList in Hsat.
  unfold ecbf_sll in Hsat.
  sep normal in Hsat.
  sep_lifts_trms_in Hsat ecbf_sllseg.
  eapply ecbf_sllseg_split3_frm; eauto.
  hoare unfold.

  hoare forward.
  go.
  2: {
          eapply hoare_disj_afalseP_l_pre.
          change (Int.eq ($ OS_EVENT_TYPE_UNUSED) ($ OS_EVENT_TYPE_MUTEX)) with false. 
          hoare unfold.
          simpl in H2; change (Int.notbool Int.zero) with Int.one in H2;
          destruct H2; tryfalse. }
  unfold AECBList.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Astruct, evsllseg).

  hoare_assert_pure (get els (v'42, Int.zero) = None).
  {
    get_hsat Hsat. 
    lets H00: sem_common.semcre_ecblist_star_not_inh H2 Hsat.
    auto.
  }
  hoare_split_pure_all.
  rename H13 into Hnone.

   assert (Htype_err': ~ (exists x y z, get els (v'42, Int.zero) = Some (absmutexsem x y, z))).
  { rewrite Hnone.
    introv Hf; destruct Hf as (mx & my & mz & Hf ); inverts Hf.
  }
  hoare_lifts_trms_pre (Aop, absecblist).
  assert (Hopv: opv = Vint32 (Int.repr OS_ERR_EVENT_TYPE) \/ opv <> Vint32 (Int.repr OS_ERR_EVENT_TYPE)) by tauto.
  destruct Hopv.
  2 :{
         eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexpend_absimp_wrong_type_abt'; eauto.
        can_change_aop_solver.
        apply absinfer_eq.
        eapply absabort_rule.
  }
  subst opv.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexpend_absimp_wrong_type'; eauto.
  can_change_aop_solver.
  apply absinfer_eq.

  (* EXIT_CRITICAL *)
  hoare forward prim.
  sep cancel APthreadAttr.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier.
  eapply fold_EvtInv_frm'; eauto.
  trycancel_EvtInv.
  unfold AECBList.
  sep normal.
  eexists.
  sep cancel OSEventList.
  sep cancel evsllseg.
  sep split; eauto.
  eapply fold_EvtInv_part2; eauto.
  trycancel_EvtInv.
  unfold AOSEventFreeList.
  unfold ecbf_sll.
  sep pauto; eauto.
  eapply ecbf_sllseg_compose3_frm; eauto. 
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel Aarray.
  sep cancel ecbf_sllseg.
  sep cancel ecbf_sllseg.
  eauto.
  unfolds; simpl; auto.
  go.
  auto.
  pure_auto.
  (* return OS_ERR_EVENT_TYPE *) 
  hoare forward.

  (* pevent points to an active ECB *) 
  assert (Hget: exists ecb, get els (mid_b, mid_i) = Some ecb).
  { clear -Hevt.
    unfold is_evt in Hevt.
    destruct Hevt as [Hsem | [Hmux | Hque]].
    unfold is_sem in Hsem.
    simpljoin1; eexists; eauto.
    unfold is_mux in Hmux.
    simpljoin1; eexists; eauto.
    unfold is_que in Hque.
    simpljoin1; eexists; eauto.
  }
  destruct Hget as (d & Hget).
  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_part2; eauto.
  trycancel_EvtInv.
  sep pauto.
  clear - Hvt_range H H0 H1 Hget.
  (* end of new add *)
  unfold AECBList.
  hoare unfold.
  lets Hget_ectr: ECBList_P_get_ectr_some Hget H2.
  destruct Hget_ectr as (et & etbl & petbl & Hget_ectr).
  eapply backward_rule1.
  intros.
  eapply get_ectr_decompose; eauto.
  sep cancel evsllseg. eauto.
  hoare unfold.
  inverts H11.
  rename i into pegrp.
  rename v'35 into lpetbl.
  hoare_assert_pure (length v'24 = length v'30).
  { get_hsat Hsat.
  sep_lifts_trms_in Hsat (evsllseg v'12).
  eapply evsllseg_list_len_eq in Hsat; auto.
  }
  hoare_split_pure_all.
  lets Hels_split: ecblist_p_decompose_new H4 H18 H19 H2.
  simpljoin1.
  simpl ECBList_P at 1 in H8.
  simpljoin1.
  inverts H8.
  (*if OSEventType !=ₑ ′ OS_EVENT_TYPE_MUTEX*)
  hoare forward.
  go.
  pure_auto.
  pure_auto.
  hoare unfold.
  destruct (Int.eq i1 ($ OS_EVENT_TYPE_MUTEX)) eqn:eq1.
  simpl in H8. change (Int.notbool Int.one) with Int.zero in H8. tryfalse.

  eapply backward_rule1.
  intros.
  eapply eventtype_neq_mutex; eauto.
  sep cancel AEventData. eauto.
  hoare_split_pure_all.
  rename H28 into Htype_err.

  hoare_lifts_trms_pre (Aop, absecblist).
  assert (Hopv: opv = V$ OS_ERR_EVENT_TYPE \/ opv <> V$ OS_ERR_EVENT_TYPE) by tauto.
  destruct Hopv.
  2 :{
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexpend_absimp_wrong_type_abt'; eauto.
        can_change_aop_solver.
        apply absinfer_eq.
        eapply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexpend_absimp_wrong_type'; eauto.
  can_change_aop_solver.
  apply absinfer_eq.

  fold_AEventNode_r.
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  eapply fold_EvtInv_frm'; eauto.
  trycancel_EvtInv.
  sep cancel EvtInv_part2.
  unfold AECBList.
  sep pauto;eauto.
  eapply evsllseg_compose;eauto.
  unfolds; simpl; eauto.
  auto.
  Optimize Proof.
  Optimize Heap.
  pure_auto.
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
   (* OSEventType = OS_EVENT_TYPE_MUTEX *)
  destruct (Int.eq i1 ($ OS_EVENT_TYPE_MUTEX)) eqn:eq1.
  2: { simpl in H8. change (Int.notbool Int.zero) with Int.one in H8.
          destruct H8; tryfalse. }
  eapply inteqeq in eq1.
  subst i1.
  destruct v'32;
  [ simpl AEventData | simpl AEventData | simpl AEventData | idtac | simpl AEventData];
  hoare unfold.
  hoare_assert_pure (DMutex v v0 = DMutex (Vint32 i2) x0).
  { get_hsat Hsat.
    simpl AEventData in Hsat.
    sep split in Hsat.
    inverts H32. inverts H33. auto.
  }
  hoare_split_pure_all.
  inverts H28.
  destruct x5.
  lets Hcp: H30.
  destruct e; simpl in H30; tryfalse.
  mytac.
  funfold H28.
  inverts H28.
  rename v'37 into mid_b.
  assert (Hget': get els (mid_b,Int.zero) = Some (absmutexsem (x3 >>ᵢ $ 8) o, w)).
  {
    eapply EcbMod.join_get_r; eauto.
    eapply EcbMod.join_sig_get; eauto.
  }
   lets Hprio_range: postintlemma3 x3.
   lets Hprio_range': acpt_int_lemma00 x3.
   lets Hprio_eq: mutpost_intlemma1 Hprio_range.
   unfold AOSTCBList.
   unfold tcbdllseg.
   simpl dllseg.
   hoare unfold.
   lets Hget_ct: Mbox_common.TCBListP_head_in_tcb H43.
   destruct Hget_ct as (cst & sus & Hget_ct).
   lets Hget_ct': Hget_ct.
   eapply TcbMod.join_get_r in Hget_ct; eauto.
   unfold get in Hget_ct; unfold TcbMap in Hget_ct.
   lets Htcb_rl: TCBList_P_imp_RL H43.
   simpl RL_TCBblk_P_List in Htcb_rl.
   destruct Htcb_rl as (Htcb_rl & _).
   assert (Hct_range: (Int.unsigned i4 < 64)%Z).
  { eapply tcbblk_prio_range; eauto. }
   (* curp not is a idle task *)
   hoare_lifts_trms_pre (Aop, absecblist,abstcblist,ostm,oscurt).
   assert (Hct_eq_cases: i4 <> Int.repr OS_IDLE_PRIO \/ i4 = Int.repr OS_IDLE_PRIO) by tauto.
   destruct Hct_eq_cases as [Hct_neq | Habt].
  2 :{
        subst.
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexpend_absimp_from_idle_abt'; eauto.
        can_change_aop_solver.
        apply absinfer_eq.
        eapply absabort_rule.
  }
  (* curp is rdy *)
  assert (Hct_rdy: (cst = rdy /\ sus = false) \/ ~(cst = rdy /\ sus = false)) by tauto.
  destruct Hct_rdy as [Hct_rdy | Hct_rdy].
  2 :{
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexpend_absimp_not_ready_abt'; eauto.
        can_change_aop_solver.
        apply absinfer_eq.
        eapply absabort_rule.
  }
  destruct Hct_rdy as (Hcur_st & Hcur_sus).
  subst sus.
  subst cst.
  assert (Hveq: x15 = Vnull /\ i5 = $ OS_STAT_RDY).
  {
    lets Hget_r: get_tcb_stat_rdy H43 Hget_ct'.
    unfold V_OSTCBStat,V_OSTCBEventPtr in Hget_r.
    simpl in Hget_r.
    clear -Hget_r.
    destruct Hget_r; pauto.
  }
  destruct Hveq as (Hvptr & Hvst). subst x15. subst i5.
  assert (Hor: Int.or  ($ OS_STAT_RDY) ($ OS_STAT_MUTEX) = ($ OS_STAT_MUTEX)).
  {
    change ($ OS_STAT_RDY) with (Int.zero).
    rewrite Int.or_commut.
    apply Int.or_zero.
  }
  lets Htcb_rl': Htcb_rl.
  funfold Htcb_rl'.
  rename x5 into i4.
  clear H59 H67 H66 H64.
  (* curp's prio is not higher than pip *)
  assert (Hct_lt: Int.ltu (x3 >>ᵢ $ 8) i4 = true \/ Int.ltu (x3 >>ᵢ $ 8) i4 = false) by (clear -H; int auto).
  destruct Hct_lt as [Hct_lt | Habt].
  2 :{
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexpend_absimp_curp_err_abt'; eauto.
        can_change_aop_solver.
        apply absinfer_eq.
        eapply absabort_rule.
  }
   (* If muex don't have owner *)
   hoare forward.
   go.
   pure_auto.
   rewrite Hprio_eq.
   hoare unfold.
   instantiate(1:= Afalse).
   destruct (Int.eq (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ OS_MUTEX_AVAILABLE)) eqn: eq1;
   simpl in H28; tryfalse.
   eapply inteqeq in eq1.
   lets Hnone: H38 eq1.
   destruct Hnone as (How_eq & Hx_eq).
  lets Hwl_eq: H30 How_eq.
  subst o x0 w.
  (* pevent ′ → OSEventCnt &= ′ OS_MUTEX_KEEP_UPPER_8;ₛ *)
  hoare forward.
  go.
  (* pevent ′ → OSEventCnt =ₑ pevent ′ → OSEventCnt |ₑ OSTCBCur ′ → OSTCBPrio;ₛ *)
  hoare forward.
  go.
  go.
  (* pevent ′ → OSEventPtr =ₑ 〈 (Void) ∗ 〉 OSTCBCur ′;ₛ *)
  hoare forward.
  assert (Hcnt_range: Int.unsigned (Int.or (x3&ᵢ$ OS_MUTEX_KEEP_UPPER_8) i4) <= 65535).
  { eapply acpt_intlemma6; auto with zarith. }
  hoare_lifts_trms_pre (Aop, absecblist,abstcblist,ostm,oscurt, EvtInv_part2).
  assert (Hopv: opv = V$ OS_NO_ERR \/ opv <> V$ OS_NO_ERR) by tauto.
  destruct Hopv.
  2 :{
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexpend_absimp_get_succ_abt'; eauto.
        can_change_aop_solver.
        apply absinfer_eq.
        eapply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexpend_absimp_get_succ'; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  (* EXIT_CRITICAL;ₛ *)
  fold_AEventNode_r.
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier.
  sep_lifts_trms EvtInv.
  eapply fold_EvtInv_frm'; eauto.
  trycancel_EvtInv.
  sep cancel EvtInv_part2.
  unfold AECBList.
  unfold AOSTCBList.
  unfold tcbdllseg.
  unfold V_OSTCBPrev, V_OSTCBNext.
  sep pauto; eauto.
  sep cancel (dllseg v'5).
  simpl dllseg at 1.
  unfold node.
  sep pauto.
  sep cancel dllseg.
  sep cancel OS_TCB_flag.
  eapply lzh_evsllseg_compose; eauto.
  sep cancel (evsllseg v'12).
  sep cancel evsllseg.
  unfold AEventNode.
  sep cancel AOSEvent.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  instantiate (2:=  (DMutex (Vint32 (Int.or (x3&ᵢ$ OS_MUTEX_KEEP_UPPER_8) i4)) (Vptr (v'35, Int.zero)))).
  unfold AEventData in *.
  unfold V_OSEventType,V_OSEventCnt, V_OSEventPtr in *.
  simpl nth_val in *.
  sep pauto.
  cancel_corecommuinv. 
  
  (* PartitionInv *)
  Require Import sem_partition.
  cancel_partitioninv.
  eauto.
  (* end of PartitionInv *)
  
  (* eauto. *)
  unfolds; simpl; eauto.
  split; auto.
  go.
(*   eapply RH_ECBlk_EIBlk_Mux_P_set_op; eauto. *)
  eapply OSMutex_common.RLH_ECBData_p_high_mbox_acpt_hold in Hcp.
  eapply ecblist_p_compose';
  try eapply RLH_ECBData_p_high_mbox_acpt_hold; eauto.
  eapply ecb_sig_join_sig'_set; eauto.
  assert (Hor_eq: Int.or (x3&ᵢ$ OS_MUTEX_KEEP_UPPER_8) i4 >>ᵢ $ 8 = x3 >>ᵢ $ 8).
   { eapply acpt_intlemma4; eauto. }
  rewrite Hor_eq.
  eapply EcbMod.join_set_r;eauto. 2: eauto. 2: eauto.
  unfolds.
  eexists.
  eapply EcbMod.join_sig_get; eauto.
  eapply mutex_acpt_rh_tcblist_ecblist_p_hold; eauto.
  
  (* instantiate (1:=  (LV pevent @ OS_EVENT ∗ |-> Vptr (mid_b, Int.zero) **
   LV ptcb @ OS_TCB ∗ |-> v'2 **
   LV os_code_defs.isrdy @ char_t |-> v'1 **
   LV mprio @ char_t |-> v'0 **
   LV pip @ char_t |-> v' **
   LV timeout @ Int16u |-> Vint32 vt **
   A_dom_lenv
     ((timeout, Int16u)
      :: (pevent, OS_EVENT ∗)
         :: (pip, char_t) :: (mprio, char_t) :: (os_code_defs.isrdy, char_t) :: (ptcb, OS_TCB ∗) :: nil))). *)
  pure_auto.
  (* end of EXIT_CRITICAL *)
  hoare forward.
  simpl nth_val'.
  introv Hf; tryfalse.
  eapply hoare_disj_afalseP_l_pre.
  (* muex have owner *)
  rewrite Hprio_eq.
  hoare unfold.
  destruct (Int.eq (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ OS_MUTEX_AVAILABLE)) eqn: eq1.
  simpl in H28; destruct H28; tryfalse.
  clear H28.
  eapply semacc_int_eq_false in eq1.
  lets Hsome: H39 eq1.
   destruct Hsome as ((ot_b & ot_i) & Hx_eq & How_eq).
  lets Hpip_prio_range: H32 How_eq.
  destruct Hpip_prio_range as (Hpip_lt_prio & Hprio_range'').
  subst o x0.
  (* pip ′ =ₑ 〈 char_t 〉 (pevent ′ → OSEventCnt ≫ ′ 8);ₛ *)
  hoare forward.
  go.
  pure_auto.
  assert (Hpip_range: Int.unsigned (x3 >>ᵢ $ 8) < 64).
  { clear -Hct_range Hct_lt; int auto. }
  lets Hpip_eq: mutexpost_intlemma1 Hpip_range.
  rewrite Hpip_eq.
  (* mprio ′ =ₑ 〈 char_t 〉 (pevent ′ → OSEventCnt &ₑ ′ OS_MUTEX_KEEP_LOWER_8);ₛ *)
   hoare forward.
   go.
   rewrite Hprio_eq.
  (* ptcb ′ =ₑ 〈 OS_TCB ∗ 〉 pevent ′ → OSEventPtr;ₛ *)
   hoare forward.
   go.
  (* get mutex owner task in TCBList *)
  lets Hrmux: H.
  destruct Hrmux as (_ & _ & _ & Hrmux & _).
  destruct Hrmux as (Hrmux_wtcb & Hrmux_wecb & Hrmux_ow & Hrmux_owp).
  lets Hget_ot: Hrmux_ow Hget'.
  destruct Hget_ot as ((opt & om & ost & sus' & Hget_ot) & Hot_not_wl).
  (* rename TCBList_P part *)
   rename H42 into Htcblist_subl.
   rename H43 into Htcblist_subr.
   unfold TCBList_P in Htcblist_subr.
   fold TCBList_P in Htcblist_subr.
   mytac_H.
   inverts H28; inverts H36.
   rename H42 into Htcbjoin_right.
   assert (Htmp: x9 = (i4, rdy, x14, false)).
  {
    eapply tcbjoin_get_a_my in Htcbjoin_right.
    eapply TcbMod.join_get_r in Htcbjoin_right; eauto.
    rewrite Hget_ct in Htcbjoin_right.
    inverts Htcbjoin_right. auto.
  }
  subst x9.
  rename H44 into Htcblist_subr.
  rename H43 into Htcbnode_ct.
  rename H41 into Htcbjoin_whole.
  rename v'13 into tcbls.
  rename v'29 into tcbls_l.
  rename v'32 into tcbls_r.
  rename v'35 into ct_b.
  (* curp is not the mutex owner *)
  hoare_lifts_trms_pre (Aop, absecblist,abstcblist,ostm,oscurt).
  assert (Hot_case: (ot_b,ot_i) <> (ct_b, Int.zero) \/ (ot_b,ot_i) = (ct_b, Int.zero)) by tauto.
  destruct Hot_case as [Hot_neq_ct | Habt].
  2 :{ rewrite <- Habt in *.
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexpend_absimp_curp_eq_owner_abt'; eauto.
        can_change_aop_solver.
        apply absinfer_eq.
        eapply absabort_rule.
  }
  (* owner not is a idle task *)
   assert (Hot_eq_cases: opt <> Int.repr OS_IDLE_PRIO \/ opt = Int.repr OS_IDLE_PRIO) by tauto.
   destruct Hot_eq_cases as [Hot_neq_idle | Habt].
  2 :{
        subst.
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexpend_absimp_owner_idle_abt'; eauto.
        can_change_aop_solver.
        apply absinfer_eq.
        eapply absabort_rule.
  }
  lets Hot_neq_idle': Int.eq_false Hot_neq_idle.
  (* get mutex owner location in tcblist  *)
  assert (H_where_ot_in: TcbMod.get tcbls_l (ot_b,ot_i) = Some (opt, ost, om, sus') \/
                 TcbMod.get tcbls_r (ot_b,ot_i) = Some (opt, ost, om, sus')).
  {
    clear -Hget_ot Htcbjoin_whole.
    eapply TcbMod.join_get_or; eauto.
  }
  (* case1: mutex owner is left to curp *)
  destruct H_where_ot_in as [Hot_left | Hot_right].
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (dllseg v'5).
  eapply lzh_tcb_list_split.
  unfold tcbdllseg.
  sep cancel dllseg.
  exact_s.
  eapply Hot_left.
  eauto.
  hoare unfold.
  rename H41 into Hget_last_tcb.
  rename v'38 into ot_b.
  rename H57 into Hot_node.
  rename H58 into Htcblist_sub_left.
  rename H59 into Htcblist_sub_right.

  rename H44 into Htcbjoin_sub_whole.
  rename H56 into Htcbjoin_sub_right.
  rename v'35 into tcbls_sub_l.
  rename v'36 into tcbls_sub_r.
  (* note: tcbls_sub_l ++ ot_node ++ tcbls_sub_r = tcbls_l *)
  lets Hot_node': Hot_node.
  unfold TCBNode_P in Hot_node'.
  destruct Hot_node' as (Ht1 & Ht2 & Hot_blk & Hot_stat).
  inverts Ht1; inverts Ht2.
  (* split tcblist end *)
  (* pre condition about owner's x,y,bitx,bity range *)
  lets Hot_blk': Hot_blk.
  funfold Hot_blk'.
  rename x0 into opt.
  rename H66 into Hot_vx_range.
  rename H67 into Hot_vy_range.
  rename H68 into Hot_vbitx_range.
  rename H69 into Hot_vbity_range.
  rename H75 into Hopt_range.
  lets Hot_vx_range': post_intlemma4 Hopt_range.
  lets Hot_vy_range': shru_3_lt_8 Hopt_range.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  hoare unfold.
   rename H56 into Hrtbl_len.
  rename H36 into Hrtbl_array_mat.
  rename v'10 into rtbl. 
  rename H41 into Hrgrp_range.
  assert (Hot_vy_range'': (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3)) < length rtbl)%nat ).
  rewrite Hrtbl_len; unfold OS_RDY_TBL_SIZE,nat_of_Z; clear -Hot_vy_range'; auto with zarith.
  lets Hnth_rtbl: array_int8u_nth_lt_len Hrtbl_array_mat Hot_vy_range''.
  destruct Hnth_rtbl as (rtbl_vy & Hnth_rtbl_vy & Hrtbl_vy_range).
  lets Hot_vy_range_new: shru_3_lt_8 Hpip_range.
  assert (Hot_vy_range_new': 
                      (Z.to_nat (Int.unsigned ((x3 >>ᵢ $ 8) >>ᵢ $ 3))
                      < length (update_nth_val (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3))) rtbl
                                                                          (Vint32 (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))))))%nat ).
  rewrite update_nth_val_len_eq; rewrite Hrtbl_len; unfold OS_RDY_TBL_SIZE,nat_of_Z; clear -Hot_vy_range_new; auto with zarith.
  assert (Hrtbl_array_mat': array_type_vallist_match Int8u (update_nth_val (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3))) rtbl
                                                                          (Vint32 (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))))) ).
  {  eapply array_type_vallist_match_hold; eauto.
      simpl. eapply mund_int_a2; eapply le255_and_le255; auto. }
  lets Hnth_rtbl': array_int8u_nth_lt_len Hrtbl_array_mat' Hot_vy_range_new'.
  destruct Hnth_rtbl' as (rtbl_vy' & Hnth_rtbl_vy' & Hrtbl_vy_range').
    assert (Hot_vbity_range_new: Int.unsigned ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3)) <= 255).
  { remember ((x3 >>ᵢ $ 8) >>ᵢ $ 3) as py.
    clear -Hot_vy_range_new; mauto. }
  lets Hot_vx_range_new: post_intlemma4 Hpip_range.
  assert (Hot_vbitx_range_new: Int.unsigned ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7)) <= 255).
  { remember ((x3 >>ᵢ $ 8)&ᵢ$ 7) as px.
    clear -Hot_vx_range_new; mauto. }

  (* If (ptcb ′ → OSTCBPrio !=ₑ pip ′ &&ₑ mprio ′ >ₑ OSTCBCur ′ → OSTCBPrio) *)
   unfold AOSTCBPrioTbl.
   hoare unfold.
  hoare forward.
  go.
  clear -Hpip_range; eapply mund_int_a2; auto with zarith.
  clear -H; pure_auto.
  clear -H; pure_auto.
  go.
  eapply mund_int_a2; auto.
  clear -H; pure_auto.
  clear -H; pure_auto.
  (* Int.eq opt (x3 >>ᵢ $ 8) = false /\ Int.ltu i4 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true*)
  hoare unfold.
  destruct (Int.eq opt (x3 >>ᵢ $ 8)) eqn: eq2;
  destruct (Int.ltu i4 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) eqn: eq3;
  simpl in H60;
  try change (Int.notbool Int.one) with Int.zero in H60;
  try change (Int.notbool Int.zero) with Int.one in H60;
  try change (Int.ltu Int.zero Int.one) with true in H60;
  try change (Int.ltu Int.zero Int.zero) with false in H60;
  simpl in H60; tryfalse. clear H66 H67.
  (*   IF ((OSRdyTbl ′ [ptcb ′ → OSTCBY] &ₑ ptcb ′ → OSTCBBitX) !=ₑ ′ 0) *)
  hoare_lifts_trms_pre (Aop, Astruct (ot_b, Int.zero), Alvarmapsto ptcb,
                                                 GAarray OSRdyTbl, Agvarmapsto OSRdyGrp, Alvarmapsto os_code_defs.isrdy ).
  hoare remember (1 :: 2 :: 3 :: 4 :: 5 :: 6 ::  nil)%nat pre.
  eapply seq_rule.
   instantiate(1:= (<|| spec_code_cons (mutexpend (Vptr (mid_b, Int.zero) :: Vint32 vt :: opv :: nil)) v'3 ||>  **
  Astruct (ot_b, Int.zero) OS_TCB_flag
    (v'34
     :: v'32
        :: x15
           :: om
              :: Vint32 i8
                 :: Vint32 x13
                    :: Vint32 opt
                       :: Vint32 (opt&ᵢ$ 7)
                          :: Vint32 (opt >>ᵢ $ 3)
                             :: Vint32 ($ 1<<ᵢ(opt&ᵢ$ 7))
                                :: Vint32 ($ 1<<ᵢ(opt >>ᵢ $ 3)) :: nil) **
  LV ptcb @ OS_TCB ∗ |-> Vptr (ot_b, Int.zero) **
  GAarray OSRdyTbl (Tarray char_t ∘ OS_RDY_TBL_SIZE) 
           (if Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero
             then rtbl
             else (update_nth_val (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3))) rtbl (Vint32 (rtbl_vy&ᵢ(Int.not ($ 1<<ᵢ(opt&ᵢ$ 7)))))) )   **
  GV OSRdyGrp @ char_t |-> (if Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero
                                                          then  Vint32 i
                                                         else (if Int.eq (rtbl_vy&ᵢ(Int.not ($ 1<<ᵢ(opt&ᵢ$ 7)))) Int.zero 
                                                                        then Vint32 (i&ᵢ(Int.not ($ 1<<ᵢ(opt>>ᵢ $ 3))))
                                                                        else  Vint32 i)) **
  LV os_code_defs.isrdy @ char_t |-> (if  Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero
                                                                             then V$ 0 else V$ 1) ** H66)).
  hoare forward.
  go.
  rewrite Hnth_rtbl_vy; clear -Hrtbl_vy_range; pure_auto.
  go.
  rewrite Hnth_rtbl_vy; clear -H;pure_auto.
  rewrite Hnth_rtbl_vy; clear -H; simpl;  destruct (Int.eq (rtbl_vy&ᵢ(Int.not ($ 1<<ᵢ(opt&ᵢ$ 7)))) ($ 0)); pure_auto.
  rewrite Hnth_rtbl_vy; clear -H;
  simpl;  destruct (Int.eq (rtbl_vy&ᵢ(Int.not ($ 1<<ᵢ(opt&ᵢ$ 7)))) ($ 0)); pure_auto.
  rewrite Hnth_rtbl_vy.
  change ($ 0) with Int.zero.
  simpl val_inj.
   (* Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero = false *)
  hoare_split_pure_all.
  rename H67 into Hsat_if.
  destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: vbitx_eq_cond;
  simpl in Hsat_if;
  try change (Int.notbool Int.one) with Int.zero in Hsat_if;
  try change (Int.notbool Int.zero) with Int.one in Hsat_if;
  simpl in Hsat_if; destruct Hsat_if as (Hif_rdy_cond & _ & _);tryfalse.
(*   clear Hif_rdy_cond. *)
  instantiate(1:= (<|| spec_code_cons (mutexpend (Vptr (mid_b, Int.zero) :: Vint32 vt :: opv :: nil)) v'3 ||>  **
  Astruct (ot_b, Int.zero) OS_TCB_flag
    (v'34
     :: v'32
        :: x15
           :: om
              :: Vint32 i8
                 :: Vint32 x13
                    :: Vint32 opt
                       :: Vint32 (opt&ᵢ$ 7)
                          :: Vint32 (opt >>ᵢ $ 3)
                             :: Vint32 ($ 1<<ᵢ(opt&ᵢ$ 7))
                                :: Vint32 ($ 1<<ᵢ(opt >>ᵢ $ 3)) :: nil) **
  LV ptcb @ OS_TCB ∗ |-> Vptr (ot_b, Int.zero) **
  GAarray OSRdyTbl (Tarray char_t ∘ OS_RDY_TBL_SIZE) 
                    (update_nth_val (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3))) rtbl (Vint32 (rtbl_vy&ᵢ(Int.not ($ 1<<ᵢ(opt&ᵢ$ 7)))))) **
  GV OSRdyGrp @ char_t |-> (if Int.eq (rtbl_vy&ᵢ(Int.not ($ 1<<ᵢ(opt&ᵢ$ 7)))) Int.zero 
                                                            then Vint32 (i&ᵢ(Int.not ($ 1<<ᵢ(opt>>ᵢ $ 3))))
                                                            else  Vint32 i) **
  LV os_code_defs.isrdy @ char_t |-> (V$ 1) ** H66)).
 (*  OSRdyTbl ′ [ptcb ′ → OSTCBY] &= ∼ ptcb ′ → OSTCBBitX;ₛ *)
  hoare unfold.
  hoare forward.
  go.
  rewrite Hnth_rtbl_vy; clear -Hrtbl_vy_range; pure_auto.
  go.
  rewrite Hnth_rtbl_vy; clear -Hrtbl_vy_range; pure_auto.
  go.
  rewrite Hnth_rtbl_vy.
  assert (Hot_vy_range''': Int.unsigned (opt >>ᵢ $ 3) < Z.of_nat (length rtbl)).
  clear -Hot_vy_range''; auto with zarith.
  lets Hup_rtbl_vy_eq: len_lt_update_get_eq Hot_vy_range'''.
  instantiate(1:= (Vint32 (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))))) in Hup_rtbl_vy_eq.
  (* If (OSRdyTbl ′ [ptcb ′ → OSTCBY] ==ₑ ′ 0) *)
   hoare forward.
   go.
   rewrite update_nth_val_len_eq; auto.
   rewrite Hup_rtbl_vy_eq.
   clear -Hrtbl_vy_range; simpl.
   eapply mund_int_a2; eapply le255_and_le255; auto.
    rewrite Hup_rtbl_vy_eq; simpl; clear -H; pure_auto.
   rewrite Hup_rtbl_vy_eq; simpl val_inj.
   hoare_split_pure_all.
   rename H66 into Hsat_if.
   destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: vbitx_eq_cond2;
   simpl in Hsat_if; destruct Hsat_if as (Hif_cond & _ & _); tryfalse.
   (* OSRdyGrp ′ &= ∼ ptcb ′ → OSTCBBitY *)
    hoare forward.
    clear -Hrgrp_range; pure_auto.
    go.
    (* os_code_defs.isrdy ′ =ₑ ′ 1 *)
    hoare forward;
    rewrite Hup_rtbl_vy_eq;
    hoare_split_pure_all;
    simpl in H66;
    rename H66 into Hsat_if.
    destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: vbitx_eq_cond2;
   simpl in Hsat_if; destruct Hsat_if as (Hif_cond & _  & _); tryfalse.
   hoare forward.
   sep cancel Aier.
   sep auto.
  Optimize Proof.
  Optimize Heap.
   destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: vbitx_eq_cond2;
   simpl in Hsat_if; destruct Hsat_if as [Hif_cond1 | Hif_cond2 ]; tryfalse.
    hoare forward.
    sep cancel Aier.
    sep auto.
   (* os_code_defs.isrdy ′ =ₑ ′ 0 *)
   hoare forward.
   rename H67 into Hsat.
   rewrite Hnth_rtbl_vy in Hsat.
   change ($ 0) with Int.zero in Hsat.
   simpl val_inj in Hsat.
   destruct Hsat as [Hsat | Hsat];
   destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1;
   simpl val_inj in Hsat;
   try change (Int.notbool Int.one) with Int.zero in Hsat;
   try change (Int.notbool Int.zero) with Int.one in Hsat;
   simpl val_inj in Hsat;
   sep pauto; try destruct H67; tryfalse.
    (* OSTCBPrioTbl ′ [ptcb ′ → OSTCBPrio] =ₑ 〈 OS_TCB ∗ 〉 PlaceHolder;ₛ *)
   subst H66.
   unfold PlaceHolder.
   hoare unfold.
   hoare forward.
   eapply forward_rule2.
   eapply assign_rule_array_g_aop.
   intro.
   split.
   intro.
   sep cancel A_dom_lenv.
   sep cancel (GAarray OSTCBPrioTbl); eauto.
   intro.
   sep auto.
   simpl; auto.
   2 : symbolic execution.
   {
   introv Hsat.
   eapply cast_rv_tptr.
  eapply addrof_gvar_rv.
  apply  astar_l_anotinlenv_intro.
  sep cancel Agvarenv'.
  eauto.

  sep_lifts_trms_in Hsat A_dom_lenv.
  apply astar_l_adomlenv_elim in Hsat.
  destruct Hsat as (Hsat & _).
  clear -Hsat.
  unfolds in Hsat.
  unfolds. unfold EnvMod.indom. introv Hget.
  destruct Hget as ((l & t) & Hget).
  assert (Hnot: ~ (ListSet.set_In (OSPlaceHolder, t)
        ((os_code_defs.timeout, Int16u)
          :: (pevent, OS_EVENT ∗)
             :: (pip, char_t)
                :: (mprio, char_t)
                   :: (os_code_defs.isrdy, char_t) :: (ptcb, OS_TCB ∗) :: nil))).
  unfolds. simpl. intros. repeat (destruct H; tryfalse).
  eapply Hnot.
  erewrite Hsat.
  eauto.

  simpl; auto.
  }
  go.
  auto.
  clear -Hopt_range; auto with zarith.
  eapply eq_vptr; eauto.
  rewrite H59; clear -Hopt_range; auto with zarith.
  intros.
  sep eexists. 
  sep cancel p_local.
  simpl; auto.
  eauto.
  (* end of assign PlaceHolder *)
   (* ptcb ′ → OSTCBPrio =ₑ pip ′;ₛ *)
   hoare unfold.
   hoare forward.
   clear -Hpip_range; eapply mund_int_a2; auto with zarith.
  (* ptcb ′ → OSTCBY =ₑ ptcb ′ → OSTCBPrio ≫ ′ 3;ₛ*)
   hoare forward.
   go.
   rewrite int_iwordsize_gt_3.
   simpl val_inj.
  (* ptcb ′ → OSTCBBitY =ₑ OSMapTbl ′ [ptcb ′ → OSTCBY];ₛ *)
  unfold AOSMapTbl.
  lets Hmap_vy: xmapis1shlx Hot_vy_range_new.
  hoare forward.
  go.
  rewrite Hmap_vy; simpl; eapply mund_int_a2; auto.
  rewrite Hmap_vy.
  (* ptcb ′ → OSTCBX =ₑ ptcb ′ → OSTCBPrio &ₑ ′ 7;ₛ *)
   hoare forward.
   go.
  (* ptcb ′ → OSTCBBitX =ₑ OSMapTbl ′ [ptcb ′ → OSTCBX];ₛ *)
   lets Hmap_vx: xmapis1shlx Hot_vx_range_new.
   hoare forward.
   go.
  rewrite Hmap_vx; simpl; eapply mund_int_a2; auto.
  rewrite Hmap_vx.
  (* If (os_code_defs.isrdy ′ ==ₑ ′ 1) *)
  hoare remember (1 :: 2:: 3 :: 6 :: 7 :: 8 ::  nil)%nat pre.
  eapply seq_rule.
  instantiate (1:= (<|| spec_code_cons
    (mutexpend (Vptr (mid_b, Int.zero) :: Vint32 vt :: opv :: nil)) v'3 ||>  **
  LV ptcb @ OS_TCB ∗ |-> Vptr (ot_b, Int.zero) **
  Astruct (ot_b, Int.zero) OS_TCB_flag
    (v'34
     :: v'32
        :: x15
           :: om
              :: Vint32 i8
                 :: Vint32 x13
                    :: Vint32 (x3 >>ᵢ $ 8)
                       :: Vint32 ((x3 >>ᵢ $ 8)&ᵢ$ 7)
                          :: Vint32 ((x3 >>ᵢ $ 8) >>ᵢ $ 3)
                             :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))
                                :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))
                                   :: nil) **
  GAarray OSRdyTbl (Tarray char_t ∘ OS_RDY_TBL_SIZE)
    (if Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero
     then rtbl
     else
      (update_nth_val (Z.to_nat (Int.unsigned ((x3 >>ᵢ $ 8) >>ᵢ $ 3)))
                                       (update_nth_val (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3))) rtbl
                                                                          (Vint32 (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7)))))
                                        (Vint32 (Int.or (rtbl_vy') ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7)))))  ) **
  GV OSRdyGrp @ char_t
  |-> (if Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero
       then Vint32 i
       else
        if Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero
        then Vint32 (Int.or (i&ᵢInt.not ($ 1<<ᵢ(opt >>ᵢ $ 3))) ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3)))
        else Vint32 (Int.or (i) ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))) ) **
  LV os_code_defs.isrdy @ char_t
  |-> (if Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero then V$ 0 else V$ 1) **
  H66)).
   hoare forward.
   destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1;
   simpl; clear -H; pure_auto.
   destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1;
   simpl; clear -H; pure_auto.
   hoare_split_pure_all.
   destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1;
   simpl in H67;  try change (Int.eq ($ 0) ($ 1)) with false in H67; try change (Int.eq ($ 1) ($ 1)) with true in H67;
   simpl in H67; destruct H67 as (Hif_cond & _ & _);tryfalse. (* H62 -> H67 *)
   (* OSRdyGrp ′ =ₑ OSRdyGrp ′ |ₑ ptcb ′ → OSTCBBitY;ₛ *)
    hoare unfold.
   hoare forward.
   destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: vbitx_eq_cond2;
   simpl; clear -Hrgrp_range; eapply mund_int_a2; try eapply le255_and_le255; auto. 
   go.
   destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: vbitx_eq_cond2;
   simpl; clear -H; pure_auto. 
   (* OSRdyTbl ′ [ptcb ′ → OSTCBY] =ₑ OSRdyTbl ′ [ptcb ′ → OSTCBY] |ₑ ptcb ′ → OSTCBBitX *)
    hoare forward.
    go.
    rewrite Hnth_rtbl_vy'; clear -Hrtbl_vy_range'; simpl; pure_auto.
    go.
    rewrite Hnth_rtbl_vy'; clear -H; simpl; pure_auto.
    go.
    clear -Hot_vy_range_new; unfold OS_RDY_TBL_SIZE; auto with zarith.
   (* post condition process, if isrdy == 1*)
   rename H67 into Hsat.
   rewrite Hnth_rtbl_vy' in Hsat.
   destruct Hsat as [Hsat | Hsat];
   destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1;
   simpl val_inj in Hsat;
   try change (Int.eq ($ 0) ($ 1)) with false in Hsat;
   try change (Int.eq ($ 1) ($ 1)) with true in Hsat;
   simpl val_inj in Hsat;
   sep pauto; tryfalse.
   sep auto.
   destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: vbitx_eq_cond2;
   simpl; auto.
   destruct H66;tryfalse.
   destruct H66;tryfalse.
  (* OSTCBPrioTbl ′ [pip ′] =ₑ 〈 OS_TCB ∗ 〉 ptcb ′ *)
  subst H66.
  eapply forward_rule1; [idtac | hoare forward].
  eauto.
  clear -Hpip_range; eapply mund_int_a2; auto with zarith.
  rewrite update_nth_val_len_eq; rewrite H59; clear -Hpip_range; auto with zarith.
assert (Hif_rdy_imp: Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero = false ->
                                               prio_in_tbl opt rtbl /\(*  ost = rdy /\ *) i8 = $ 0(*  /\ x13 = $ OS_STAT_RDY *)).
  { introv Hif_rdy_cond.
     assert (Hopt_case: prio_in_tbl opt rtbl \/ prio_not_in_tbl opt rtbl) by
                   (eapply prio_rtbl_dec; eauto).
    assert (Hopt_in_rtbl: prio_in_tbl opt rtbl).
    { destruct Hopt_case as [Hopt_rdy | Hfalse]; auto.
       unfolds in Hfalse.
       eapply nth_val'2nth_val in Hnth_rtbl_vy.
       clear -Hnth_rtbl_vy Hfalse Hif_rdy_cond.
       eapply Hfalse in Hnth_rtbl_vy; eauto.
       eapply eq2inteq in Hnth_rtbl_vy; change ($ 0) with Int.zero in Hnth_rtbl_vy.
       rewrite Hif_rdy_cond in Hnth_rtbl_vy; tryfalse.
     }
   assert (Hopt_rdy: RdyTCBblk (v'34
              :: v'32
                 :: x15
                    :: om
                       :: Vint32 i8
                          :: Vint32 x13
                             :: Vint32 opt
                                :: Vint32 (opt&ᵢ$ 7)
                                   :: Vint32 (opt >>ᵢ $ 3)
                                      :: Vint32 ($ 1<<ᵢ(opt&ᵢ$ 7))
                                         :: Vint32 ($ 1<<ᵢ(opt >>ᵢ $ 3)) :: nil) rtbl opt).
   { unfolds. split; auto. }
   destruct Hot_stat as (Hot_stat_rdy & _).
   eapply Hot_stat_rdy in Hopt_rdy.
   unfold V_OSTCBStat,V_OSTCBDly in Hopt_rdy; simpl nth_val in Hopt_rdy.
   destruct Hopt_rdy as (Heq1 & Heq2 (*  & (m & Heq3) *)).
  inverts Heq1. splits; eauto.
  } 
 (* case1.1 : mutex owner is left to curp, owner's priority lift to pip *)
  hoare forward.
  (* Int.eq opt (x3 >>ᵢ $ 8) = false /\ Int.ltu i4 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true*)
  hoare unfold.
  destruct (Int.eq opt (x3 >>ᵢ $ 8)) eqn: eq2; (* x1 -> x3 *)
  destruct (Int.ltu i4 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) eqn: eq3;
  simpl in H60;
  try change (Int.notbool Int.one) with Int.zero in H60;
  try change (Int.notbool Int.zero) with Int.one in H60;
  try change (Int.ltu Int.zero Int.one) with true in H60;
  try change (Int.ltu Int.zero Int.zero) with false in H60;
  simpl in H60; tryfalse. clear H66 H67.
  assert (Hpip_non_tls: prio_available (x3 >>ᵢ $ 8) tcbls).
 { destruct H as (_ & _ & _ & H).
    eapply H; eauto.
    eapply semacc_int_eq_false; eauto.
  }
  (* OSTCBCur ′ → OSTCBStat =ₑ OSTCBCur ′ → OSTCBStat |ₑ ′ OS_STAT_MUTEX;ₛ  *)
  hoare forward.
  go.
  rewrite Hor.
  (* OSTCBCur ′ → OSTCBDly =ₑ os_code_defs.timeout ′;ₛ *)
  hoare forward.
  clear -Hvt_range; pauto.
  (* OS_EventTaskWait (­ pevent ′­);ₛ *)
  hoare_lifts_trms_pre (Aisr, Ais, A_isr_is_prop, aemp_isr_is).
(*    hoare lifts (42::44::39::nil)%nat pre. *)
  transform_pre a_isr_is_prop_split ltac:(idtac).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  hoare_split_pure_all.
  assert (  RL_TCBblk_P
     (v'34
     :: v'32
        :: x15
           :: om
              :: Vint32 i8
                 :: Vint32 x13
                    :: Vint32 (x3 >>ᵢ $ 8)
                       :: Vint32 ((x3 >>ᵢ $ 8)&ᵢ$ 7)
                          :: Vint32 ((x3 >>ᵢ $ 8) >>ᵢ $ 3)
                             :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))
                                :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))
                                   :: nil)) as Hnewrltcbblkp.
  {
    unfolds.
    do 6 eexists;splits; 
    try (unfolds;simpl;eauto).
    split; auto.
    clear; int auto.
    splits; auto.
    eexists.
    split; auto.
    unfolds;simpl;auto.
  }
   assert (Hpintbl: prio_in_tbl ($ OS_IDLE_PRIO) 
                                         (update_nth_val (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3))) rtbl
                                               (Vint32 (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7)))))).
  { eapply idle_in_rtbl_hold; eauto. }
  lets Hpintbl': Hpintbl.
  eapply idle_in_rtbl_hold' in Hpintbl'; eauto.
  erewrite Hnth_rtbl_vy' in Hpintbl'.
  simpl val_inj in Hpintbl'.

  hoare unfold.
  hoare forward.

  unfold node.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  sep pauto.
  instantiate (9:= ct_b).
  sep cancel (Astruct (ct_b,Int.zero)).
  sep cancel p_local.
  instantiate  (2:= (DMutex (Vint32 x3) (Vptr (ot_b, Int.zero)))).
  unfold AEventNode.
  sep cancel AEventData.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Aarray.
  sep cancel AOSPostEventTbl.
  instantiate (2:= mid_b).
  sep cancel (Astruct (mid_b, Int.zero)).
  eauto.
  eauto.
  unfolds; simpl; eauto.
  eauto.
  eauto.
  unfold V_OSEventGrp; simpl; auto.
  eauto.
  auto.
  Optimize Proof.
  Optimize Heap.
  split; auto. go.
  (* RL_Tbl_Grp_P /\  prio_in_tbl *)
  destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1;
  try destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond2;
  split; auto;
  try eapply OSTimeDlyPure.event_wait_rl_tbl_grp; eauto.
  eapply OSTimeDlyPure.event_wait_rl_tbl_grp';eauto.
  eapply OSTimeDlyPure.event_wait_rl_tbl_grp''; eauto.
 (* end of RL_Tbl_Grp_P /\  prio_in_tbl *)
  destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1;
  try destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond2;
  eapply mund_int_a2; try eapply int_unsigned_or_prop'; try eapply le255_and_le255; auto with zarith.
  destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1;
  try destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond2;
  split; 
  try rewrite update_nth_val_len_eq; try rewrite update_nth_val_len_eq;
  try eapply array_type_vallist_match_hold; eauto;
  try eapply mund_int_a2; try eapply int_unsigned_or_prop'; 
  try eapply le255_and_le255; auto with zarith.

  split;auto. go.
  split; simpl; auto.
  eexists; split; try (unfold V_OSTCBPrio; simpl nth_val); try eapply Int.eq_false; eauto. 
  { clear -Htcb_rl; unfolds; unfolds in Htcb_rl.
     mytac.
     do 6 eexists; splits; try (unfolds; simpl; eauto).
     split;auto.
     splits; auto.
     pauto.
     eexists; split.
     unfolds; simpl; eauto.
     introv Hf; destruct Hf as [Hf | Hf]; tryfalse. }
   go.
   
  intros. sep pauto. sep cancel p_local. simpl; auto.
  intros. sep pauto. sep cancel p_local. simpl; auto.
  (* OS_EventTaskWaitPost *)
  hoare_ex_intro.
  unfold OS_EventTaskWaitPost.
  unfold OS_EventTaskWaitPost'.
  unfold getasrt.
  hoare_split_pure_all.
  inverts H66.
  unfold V_OSTCBY,V_OSTCBBitX,V_OSTCBBitY,V_OSEventGrp in H68.
  simpl in H67,H68.
  mytac_H.
  inverts H67; inverts H68; inverts H69; inverts H70; inverts H78.

  (* mutex owner is rdy *)
   hoare_lifts_trms_pre (Aop, absecblist,abstcblist,ostm,oscurt, absptlsid ,EvtInv_part2).
   assert (Host_case: (ost = rdy /\ sus' = false) \/ ~(ost = rdy /\ sus' = false)) by tauto.
   destruct Host_case as [(Host_eq & Hsus_eq) | Habt].
   2: {  eapply abscsq_rule.
           apply noabs_oslinv.
           eapply mutexpend_absimp_owner_not_ready_abt'; eauto.
           can_change_aop_solver.
           apply absinfer_eq.
           eapply absabort_rule.
         }
     subst sus'.
     subst ost.
  (* change absdata *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexpend_absimp_block_lift'; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  2:{ clear -Hot_vy_range_new; auto with zarith. }
  2:{ rewrite update_nth_val_len_eq; auto. }
  (* EXIT_CRITICAL;ₛ *)
   assert (Htlsp1: TCBList_P (Vptr (ct_b, Int.zero))
  ((x5
    :: v'15
       :: Vptr (mid_b, Int.zero)
          :: x14
             :: Vint32 vt
                :: V$ OS_STAT_MUTEX
                   :: Vint32 i4
                      :: Vint32 (i4&ᵢ$ 7)
                         :: Vint32 (i4 >>ᵢ $ 3)
                            :: Vint32 ($ 1<<ᵢ(i4&ᵢ$ 7))
                               :: Vint32 ($ 1<<ᵢ(i4 >>ᵢ $ 3)) :: nil)
   :: v'9)
  (update_nth_val ∘ (Int.unsigned (i4 >>ᵢ $ 3))
     (if Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero
      then rtbl
      else
       update_nth_val (Z.to_nat (Int.unsigned ((x3 >>ᵢ $ 8) >>ᵢ $ 3)))
         (update_nth_val (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3))) rtbl
            (Vint32 (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7)))))
         (Vint32 (Int.or rtbl_vy' ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7)))))
     (Vint32 (v'49&ᵢInt.not ($ 1<<ᵢ(i4&ᵢ$ 7))))) 
  (TcbMod.set tcbls_r (ct_b, Int.zero)
                                             (i4, wait (os_stat_mutexsem (mid_b, Int.zero)) (if Int.eq vt Int.zero then None else (Some vt)), x14, false))).
   { 
     assert (Hct_i4_neq: prio_neq_cur tcbls_r (ct_b, Int.zero) i4).
   { eapply TcbMod_join_impl_prio_neq_cur_r; eauto.
    clear -H56 Hget_ct.
    unfolds; intros; eapply H56; eauto. }
    destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1.
    destruct (Int.eq vt Int.zero) eqn: Heq_t.
    eapply semacc_int_eq_true in Heq_t.
    eapply TCBList_P_tcb_block_hold_mutex'_none; eauto.
    simpl TCBList_P.
    unfold V_OSTCBNext. simpl nth_val.
    do 4 eexists; splits; eauto.
    clear -Htcbjoin_right; unfold TcbJoin in Htcbjoin_right; auto.
    eapply semacc_int_eq_false in Heq_t.
    eapply TCBList_P_tcb_block_hold_mutex'; eauto.
    simpl TCBList_P.
    unfold V_OSTCBNext. simpl nth_val.
    do 4 eexists; splits; eauto.
    clear -Htcbjoin_right; unfold TcbJoin in Htcbjoin_right; auto.

    destruct (Int.eq vt Int.zero) eqn: Heq_t.
    eapply semacc_int_eq_true in Heq_t.
    eapply TCBList_P_tcb_block_hold_mutex'_none; eauto.
    eapply TCBList_P_rtbl_add_simpl_version;eauto.
    clear -Hpip_range; split;auto. int auto.
    unfold nat_of_Z; eapply nth_val'2nth_val;eauto.
    clear -Hpip_non_tls Htcbjoin_whole.
    intros; eapply semacc_int_eq_false; rewrite Int.eq_sym.
    eapply Hpip_non_tls; eapply TcbMod.join_get_r; eauto.
    eapply Mbox_common.TCBList_P_tcb_block_hold' with (tcs:= tcbls_l); eauto.
    eapply TcbMod.map_join_comm; eauto.
    simpl TCBList_P.
    unfold V_OSTCBNext. simpl nth_val.
    do 4 eexists; splits; eauto.
    clear -Htcbjoin_right; unfold TcbJoin in Htcbjoin_right; auto.
    eapply TcbMod_join_impl_prio_neq_cur_r; eauto.
    clear -H56 Hget_ot.
    unfolds; intros; eapply H56; eauto.
    unfold nat_of_Z; eapply nth_val'2nth_val;eauto.

    eapply semacc_int_eq_false in Heq_t.
    eapply TCBList_P_tcb_block_hold_mutex'; eauto.
    eapply TCBList_P_rtbl_add_simpl_version;eauto.
    clear -Hpip_range; split;auto. int auto.
    unfold nat_of_Z; eapply nth_val'2nth_val;eauto.
    clear -Hpip_non_tls Htcbjoin_whole.
    intros; eapply semacc_int_eq_false; rewrite Int.eq_sym.
    eapply Hpip_non_tls; eapply TcbMod.join_get_r; eauto.
    eapply Mbox_common.TCBList_P_tcb_block_hold' with (tcs:= tcbls_l); eauto.
    eapply TcbMod.map_join_comm; eauto.
    simpl TCBList_P.
    unfold V_OSTCBNext. simpl nth_val.
    do 4 eexists; splits; eauto.
    clear -Htcbjoin_right; unfold TcbJoin in Htcbjoin_right; auto.
    eapply TcbMod_join_impl_prio_neq_cur_r; eauto.
    clear -H56 Hget_ot.
    unfolds; intros; eapply H56; eauto.
    unfold nat_of_Z; eapply nth_val'2nth_val;eauto.
    }
  assert (Htlsp2: TCBList_P v'5
  (v'8 ++
   (v'34
    :: v'32
       :: x15
          :: om
             :: Vint32 i8
                :: Vint32 x13
                   :: Vint32 (x3 >>ᵢ $ 8)
                      :: Vint32 ((x3 >>ᵢ $ 8)&ᵢ$ 7)
                         :: Vint32 ((x3 >>ᵢ $ 8) >>ᵢ $ 3)
                            :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))
                               :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))
                                  :: nil) :: v'13)
  (update_nth_val ∘ (Int.unsigned (i4 >>ᵢ $ 3))
     (if Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero
      then rtbl
      else
       update_nth_val (Z.to_nat (Int.unsigned ((x3 >>ᵢ $ 8) >>ᵢ $ 3)))
         (update_nth_val (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3))) rtbl
            (Vint32 (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7)))))
         (Vint32 (Int.or rtbl_vy' ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7)))))
     (Vint32 (v'49&ᵢInt.not ($ 1<<ᵢ(i4&ᵢ$ 7))))) 
  (TcbMod.set tcbls_l (ot_b, Int.zero) (x3 >>ᵢ $ 8, rdy, om, false))).
    {
      assert (Hct_i4_neq: prio_neq_cur (TcbMod.set tcbls_l (ot_b, Int.zero) (x3 >>ᵢ $ 8, rdy, om, false))
  (ct_b, Int.zero) i4).
   { unfolds; intros.
     rewrite TcbMod.set_sem in H67.
     destruct (tidspec.beq (ot_b, Int.zero) tid) eqn: eq_td.
     inverts H67.
     clear -Hpip_non_tls Hget_ct.
     eapply semacc_int_eq_false; eapply Hpip_non_tls; eauto.
     eapply H56 in H66;eauto.
     eapply H66; eauto.
     eapply TcbMod.join_get_l;eauto.
    }
    destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1.
    eapply Mbox_common.TCBList_P_tcb_block_hold' with (prio:= i4) (tcs:= tcbls_r); eauto.
    clear -Hct_range; split; auto. int auto.
    eapply TcbMod.join_set_l; eauto.
    unfold TcbMod.indom; eauto.
    { eapply TCBList_P_Combine; eauto.
       eapply TcbMod.my_joinsig_join_set; eauto.
       simpl TCBList_P.
       unfold V_OSTCBNext. simpl nth_val.
       do 4 eexists; splits; eauto.
       eapply tcbjoin_set_my;eauto.
       simpl.
       unfold V_OSTCBMsg,V_OSTCBPrio.
       simpl nth_val.
       splits; auto.
       eapply R_TCB_Status_P_change_prio;eauto.
       clear -Hpip_range; split;auto; int auto.
       { (* prio_not_in_tbl opt rtbl *)
         unfold prio_not_in_tbl.
         intros x2' y z Heq1 Heq2 Hnth_new.
         subst x2'; subst y.
         eapply nth_val_nth_val'_some_eq in Hnth_new.
         unfold nat_of_Z in Hnth_new.
         rewrite Hnth_rtbl_vy in Hnth_new.
         inverts Hnth_new.
         change ($ 0) with Int.zero.
         eapply inteqeq; eauto. }
     }
    (* case:  Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero = false *)
    {  assert (Heq_f: false = false) by auto.
        eapply Mbox_common.TCBList_P_tcb_block_hold' with (prio:= i4) (tcs:= tcbls_r); eauto.
        clear -Hct_range . int auto.
         eapply TcbMod.join_set_l; eauto.
         unfold TcbMod.indom; eauto.
        assert(Hif_rdy_imp2: (* ost = rdy ->  *)x13 = $ OS_STAT_RDY ).
        { clear -Hot_node.  funfold Hot_node. 
          funfold H2. specialize (H0 _ _ (eq_refl _)).
         destruct H0 as (Hr & Hst & Hd).
         inverts Hst. auto. }
          subst x13.
        specialize (Hif_rdy_imp (eq_refl _)).
        destruct Hif_rdy_imp. subst i8.
         eapply tcbls_l_mutexpend';eauto.
         eapply semacc_int_eq_false; rewrite Int.eq_sym.
         eapply Hpip_non_tls; eauto.
    }
     } 
   hoare_assert_pure ( get_last_tcb_ptr v'13 v'34 = Some (Vptr (ct_b, Int.zero)) ).
   { get_hsat Hsat.
     sep_lifts_trms_in Hsat (dllseg v'34).
     eapply tcbdllseg_get_last_tcb_ptr; eauto.
   }
  hoare_split_pure_all.
  rename H66 into Hget_last_ct.

   transform_pre add_a_isr_is_prop ltac:(sep cancel Aisr;
                                        sep cancel Ais).
   transform_pre add_aemp_isr_is_prop ltac:(sep cancel Aisr;
                                        sep cancel Ais; sep cancel Aier).
  hoare forward prim.
  sep cancel Aier.
  unfold AOSMapTbl.
  sep pauto.
  sep_lifts_trms EvtInv.
  eapply fold_EvtInv_frm'; eauto.
  trycancel_EvtInv.
(*   sep_lifts_trms AECBList. *)
  eapply AECBList_fold.
  eapply lzh_evsllseg_compose; eauto.
  sep cancel AEventNode.
  2:{ unfolds; simpl; eauto. }
  sep cancel (Agvarmapsto OSEventList).
  sep cancel (evsllseg x7).
  sep cancel evsllseg.
  sep cancel APthreadAttr.
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel (Aptrmapsto).
  sep cancel (Agvarenv').
  simpl dllseg at 2.
  eapply dllseg_compose;eauto.
  sep cancel (dllseg v'5).
  unfold V_OSTCBPrev,V_OSTCBNext.
  sep pauto.
  sep cancel node.
  2 : { simpl; eauto. }
  2: { simpl; eauto. }
  sep cancel (dllseg x5).
  sep cancel p_local.
  instantiate (2:= ( (v'34
            :: v'32
               :: x15
                  :: om
                     :: Vint32 i8
                        :: Vint32 x13
                           :: Vint32 (x3 >>ᵢ $ 8)
                              :: Vint32 ((x3 >>ᵢ $ 8)&ᵢ$ 7)
                                 :: Vint32 ((x3 >>ᵢ $ 8) >>ᵢ $ 3)
                                    :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))
                                       :: Vint32
                                            ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))
                                          :: nil):: v'13)).
  simpl dllseg at 1.
  simpl nth_val.
  unfold node.
  sep pauto.
  sep cancel dllseg.
  2 : { split; eauto. go. }
   sep cancel (Astruct).
   sep_lifts_trms tcbdllflag.
   eapply tcbdllflag_hold; [idtac | sep cancel tcbdllflag; eauto].
   eapply tcbdllflag_hold_node2.
   unfolds; swallow; go.
   unfolds; swallow; go.
   unfold EvtInv_part2 in *.
   sep pauto.
   trycancel_EvtInv.
   eapply gjb_common.tcbllsegevaux_tcbvl_tcb_linked_list_same_next_preserve; eauto.
   sep cancel tcbllsegevaux.
   sep cancel CapabilityInv.
   cancel_corecommuinv. 
   cancel_partitioninv.
   eauto.
   eapply gjb_common.tcb_linked_list_same_next_split; eauto.
   eapply gjb_common.tcb_linked_list_same_next_mid; eauto.
  rewrite <- nil_simp.
   assert (Hvll_eq: forall (vl: vallist) (vll: list vallist), (vl :: vll) = (nil ++ (vl :: vll))).
   { simpl; auto. }
   rewrite Hvll_eq.
   eapply gjb_common.tcb_linked_list_same_next_mid; eauto.
   rewrite nil_simp.
   simpl TCBList_P.
   unfold V_OSTCBNext; simpl nth_val.
   clear -Htcbnode_ct Htcbjoin_right Htcblist_subr.
   do 3 eexists; exists (i4,rdy, x14, false); splits; eauto.
  eapply tcbjoin_set_my;eauto.
   eauto. eauto. eauto. (* new add *)
   (* RH_PrioTbl_P *)
   eapply RH_PrioTbl_P_update_tcb; eauto.
   clear -Hpip_range. split; auto.
   apply Int.unsigned_range_2.
   clear -H56 Hget_ot.
   destruct H56 as (_ & H & _).
   eapply H in Hget_ot. simpljoin. auto.
   eapply RH_PrioTbl_P_update_vhold; eauto.
    (* R_PrioTbl_P *)
    eapply R_PrioTbl_Pend_lift';eauto.
    (* RL_RTbl_PrioTbl_P *)
     assert (Hot_neq_hold: (ot_b, Int.zero) <> vhold_addr).
     { clear -H56 Hget_ot.
          funfold H56; eapply H0 in Hget_ot.
          destruct Hget_ot; auto. }
     destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1.
     eapply OSTimeDlyPure.rtbl_remove_RL_RTbl_PrioTbl_P_hold with (prio:= i4); eauto.
     split; auto. clear; int auto.
     eapply RL_RTbl_PrioTbl_P_set_not_rdy; eauto.
     { (* prio_not_in_tbl opt rtbl *)
     unfold prio_not_in_tbl.
     intros x2' y z Heq1 Heq2 Hnth_new.
     subst x2'; subst y.
     eapply nth_val_nth_val'_some_eq in Hnth_new.
     unfold nat_of_Z in Hnth_new.
     rewrite Hnth_rtbl_vy in Hnth_new.
     inverts Hnth_new.
     change ($ 0) with Int.zero.
     eapply inteqeq; eauto.
     }
    {    (* case: Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero = false *)
          eapply OSTimeDlyPure.rtbl_remove_RL_RTbl_PrioTbl_P_hold with (prio:= i4); eauto.
          split; auto. clear; int auto.
          eapply RL_RTbl_PrioTbl_P_set; eauto.
          rewrite update_nth_val_len_eq; auto.
          rewrite update_nth_val_len_eq; auto.
          eapply xmapis1shlx; eauto.
          eapply RL_RTbl_PrioTbl_P_set_vhold; eauto. }
    (* array_type_vallist_match /\ length *)
    split.
    eapply array_type_vallist_match_hold; eauto.
    eapply array_type_vallist_match_hold; eauto.
    rewrite H59; clear -Hopt_range; auto with zarith.
    rewrite update_nth_val_len_eq; rewrite H59; clear -Hpip_range; auto with zarith. (* H53 -> H59 *)
    do 2 rewrite update_nth_val_len_eq; auto.
    (* TCBList_P *)
    apply Htlsp1.
    (* TCBList_P contain mutex owner *)
    apply Htlsp2.
     eapply join_prop_mutexpend'';eauto.
     (* ECBList_P *)
     eapply ecblist_p_mutexpend_changeprio; eauto.
    rewrite TcbMod.set_sem.
    lets Hneq: tidspec.neq_beq_false Hot_neq_ct.
    eapply TaskLStMod.beq_sym in Hneq.
    rewrite Hneq; eauto.
    eapply ecblist_p_mutexpend';eauto.
    eapply evsllseg_aux with (s:= s); eauto.
    sep cancel (evsllseg v'12); eauto.
     assert (Hct_dly_eq: i6 = $ 0).
     { clear -Htcbnode_ct.
        funfold Htcbnode_ct.
        funfold H2.
        assert (Habs_eq: (i4, rdy, x14, false) = (i4, rdy, x14, false)) by auto.
        eapply H0 in Habs_eq.
        mytac.
        unfold V_OSTCBDly in H8; simpl in H8; inverts H8.
        auto.
  Optimize Proof.
  Optimize Heap.
       }
     subst i6; eauto.
   (* RH_ECBlk_EIBlk_Mux_P *)
(*     eapply RH_ECBlk_EIBlk_Mux_P_set_op;eauto. *)
(*     auto. *)
    (* RH_CurTCB *)
    unfold RH_CurTCB.
    rewrite TcbMod.set_sem.
    lets Hneq: tidspec.neq_beq_false Hot_neq_ct.
    rewrite Hneq.
    rewrite TcbMod.map_get_set; eauto.
    (* RH_TCBList_ECBList_P *)
    lets Hset_set: neq_set_comm Hot_neq_ct.
    erewrite <- Hset_set.
    eapply RH_TCBList_ECBList_P_high_block_hold_mutex'; eauto.
    eapply RH_TCBList_ECBList_P_pend_changeprio'; eauto.
    clear -H56. funfold H56; auto. (* H52 -> H56 *)
    rewrite TcbMod.set_sem.
    lets Hneq: tidspec.neq_beq_false Hot_neq_ct.
    rewrite Hneq. auto.
   (* end of RH_TCBList_ECBList_P *)
    eauto.

    pure_auto.
   (* end of EXIT CRITICAL *)
   (* needs partproof lemma *)
   simpl nth_val. (* new add *)
   eapply backward_rule1;
   [idtac | eapply OSMutexPendPart_proof with (vt := vt); eauto].
   introv Hsat; sep cancel Aier; sep pauto.

  (* case1.2 : mutex owner is left to curp, owner's priority no change *)
  hoare unfold.
  assert (Hno_lift_cond: ~(Int.eq opt (x3 >>ᵢ $ 8) = false 
                                                       /\ Int.ltu i4 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true)).
  { destruct (Int.eq opt (x3 >>ᵢ $ 8)) eqn: eq2;
     destruct (Int.ltu i4 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) eqn: eq3;
  simpl in H60;
  try change (Int.notbool Int.one) with Int.zero in H60;
  try change (Int.notbool Int.zero) with Int.one in H60;
  try change (Int.ltu Int.zero Int.one) with true in H60;
  try change (Int.ltu Int.zero Int.zero) with false in H60;
  simpl in H60; destruct H60; tryfalse; clear; mauto. }
 clear H60.
  (* OSTCBCur ′ → OSTCBStat =ₑ OSTCBCur ′ → OSTCBStat |ₑ ′ OS_STAT_MUTEX;ₛ  *)
  hoare forward.
  go.
  rewrite Hor.
  (* OSTCBCur ′ → OSTCBDly =ₑ os_code_defs.timeout ′;ₛ *)
  hoare forward.
  clear -Hvt_range; pauto.
  (* OS_EventTaskWait (­ pevent ′­);ₛ *)
   hoare_lifts_trms_pre (Aisr, Ais, A_isr_is_prop, aemp_isr_is).
  transform_pre a_isr_is_prop_split ltac:(idtac).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  hoare_split_pure_all.

  hoare unfold.
  hoare forward.

  unfold node.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  sep pauto.
  instantiate (9:= ct_b).
  sep cancel (Astruct (ct_b,Int.zero)).
  sep cancel p_local.
  instantiate  (2:= (DMutex (Vint32 x3) (Vptr (ot_b, Int.zero)))).
  unfold AEventNode.
  sep cancel AEventData.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Aarray.
  sep cancel AOSPostEventTbl.
  instantiate (2:= mid_b).
  sep cancel (Astruct (mid_b, Int.zero)).
  eauto.
  eauto.
  unfolds; simpl; eauto.
  eauto.
  eauto.
  unfolds; simpl; auto.
  eauto.
  auto.
  split; auto. go.
  eapply mund_int_a2; auto.
  split; auto. go.
  split; simpl; auto.
  eexists; split; try (unfold V_OSTCBPrio; simpl nth_val); try eapply Int.eq_false; eauto.
  { clear -Htcb_rl; unfolds; unfolds in Htcb_rl.
     mytac.
     do 6 eexists; splits; try (unfolds; simpl; eauto).
     split;auto.
     splits; auto.
     pauto.
     eexists; split.
     unfolds; simpl; eauto.
     introv Hf; destruct Hf as [Hf | Hf]; tryfalse. }
  pure_auto.

  intros. sep pauto. sep cancel p_local. simpl; auto.
  intros. sep pauto. sep cancel p_local. simpl; auto.
  (* OS_EventTaskWaitPost *)
  hoare_ex_intro.
  unfold OS_EventTaskWaitPost.
  unfold OS_EventTaskWaitPost'.
  unfold getasrt.
  hoare_split_pure_all.
  inverts H60.
  unfold V_OSTCBY,V_OSTCBBitX,V_OSTCBBitY,V_OSEventGrp in H67.
  simpl in H66,H67.
  mytac_H.
  inverts H66; inverts H67; inverts H68; inverts H69; inverts H76.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, absecblist,abstcblist,ostm,oscurt,EvtInv_part2).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexpend_absimp_block_no_lift'; eauto.
  can_change_aop_solver.
  apply absinfer_eq.

  (* EXIT_CRITICAL;ₛ *)
   hoare_assert_pure ( get_last_tcb_ptr v'13 v'34 = Some (Vptr (ct_b, Int.zero)) ).
   { get_hsat Hsat.
     sep_lifts_trms_in Hsat (dllseg v'34).
     eapply tcbdllseg_get_last_tcb_ptr; eauto.
   }
  apply pure_split_rule'; introv Hget_last_ct.
   transform_pre add_a_isr_is_prop ltac:(sep cancel Aisr;
                                        sep cancel Ais).
   transform_pre add_aemp_isr_is_prop ltac:(sep cancel Aisr;
                                        sep cancel Ais; sep cancel Aier).
  hoare forward prim.
  sep cancel Aier.
  sep_lifts_trms EvtInv.
  eapply fold_EvtInv_frm'; eauto.
  trycancel_EvtInv.
  eapply AECBList_fold.
  eapply lzh_evsllseg_compose; eauto.
  sep cancel AEventNode.
  2:{ unfolds; simpl; eauto. }
  sep cancel (Agvarmapsto OSEventList).
  sep cancel (evsllseg x7).
  sep cancel evsllseg.
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel (Aptrmapsto).
  sep cancel (Agvarenv').
  simpl dllseg at 2.
  eapply dllseg_compose;eauto.
  sep cancel (dllseg v'5).
  unfold V_OSTCBPrev,V_OSTCBNext.
  sep pauto.
  sep cancel node.
  2 : { simpl; eauto. }
  2: { simpl; eauto. }
  sep cancel (dllseg x5).
  sep cancel p_local.
  instantiate (2:= ((v'34
            :: v'32
               :: x15
                  :: om
                     :: Vint32 i8
                        :: Vint32 x13
                           :: Vint32 opt
                              :: Vint32 (opt&ᵢ$ 7)
                                 :: Vint32 (opt >>ᵢ $ 3)
                                    :: Vint32 ($ 1<<ᵢ(opt&ᵢ$ 7))
                                       :: Vint32 ($ 1<<ᵢ(opt >>ᵢ $ 3)) :: nil) :: v'13)).
  simpl dllseg at 1.
  simpl nth_val.
  unfold node.
  sep pauto.
   sep cancel dllseg.
   2 : { split; eauto. go. }
   sep cancel (Astruct).
   sep_lifts_trms tcbdllflag.
   eapply tcbdllflag_hold; [idtac | sep cancel tcbdllflag; eauto].
    eapply tcbdllflag_hold_node2.
    unfolds; swallow; go.
    unfolds; swallow; go.
    eapply evtinv_part2_set_tcbvl_mid_preserve.
  2: { sep cancel EvtInv_part2. cancel_corecommuinv. 
         sep cancel APthreadAttr. sep cancel CapabilityInv.
         cancel_partitioninv. eauto.
    }
     {  eapply TCBList_P_Combine.
         3: { apply Htcblist_subl. }
         2: { eauto.  }
         2: {  simpl TCBList_P.
                  unfold V_OSTCBNext. simpl nth_val.
                  do 3 eexists; exists (i4,rdy,x14, false); splits; eauto.
                  apply Htcbjoin_right.  }
     eapply get_last_tcb_ptr_split; eauto.
     eapply get_last_tcb_ptr_prop; eauto.
    unfolds; simpl; auto.
    }
     (* RH_PrioTbl_P *)
    auto.
  Optimize Proof.
  Optimize Heap.
    (* R_PrioTbl_P *)
    eapply Mbox_common.TcbMod_set_R_PrioTbl_P_hold;eauto.
   (* RL_RTbl_PrioTbl_P *)
    eapply OSTimeDlyPure.rtbl_remove_RL_RTbl_PrioTbl_P_hold with (prio:= i4);eauto.
    clear -Hct_range; split; auto. int auto.
   (* TCBList_P *)
    assert (Hct_i4_neq: prio_neq_cur tcbls_r (ct_b, Int.zero) i4).
   { eapply TcbMod_join_impl_prio_neq_cur_r; eauto.
    clear -H56 Hget_ct.
    unfolds; intros; eapply H56; eauto. }
     instantiate (1:= TcbMod.set tcbls_r (ct_b, Int.zero)
                                             (i4, wait (os_stat_mutexsem (mid_b, Int.zero))
                                                   (if Int.eq vt Int.zero then None else (Some vt)), x14, false)).
    destruct (Int.eq vt Int.zero) eqn: Heq_t.
    eapply semacc_int_eq_true in Heq_t. subst vt.
    eapply TCBList_P_tcb_block_hold_mutex'_none; eauto.
    simpl TCBList_P.
    unfold V_OSTCBNext. simpl nth_val.
    do 4 eexists; splits; eauto.
    clear -Htcbjoin_right; unfold TcbJoin in Htcbjoin_right; auto.
    eapply semacc_int_eq_false in Heq_t.
    eapply TCBList_P_tcb_block_hold_mutex'; eauto.
    simpl TCBList_P.
    unfold V_OSTCBNext. simpl nth_val.
    do 4 eexists; splits; eauto.
    clear -Htcbjoin_right; unfold TcbJoin in Htcbjoin_right; auto.
    (* TCBList_P contain mutex owner *)
    instantiate (1:= tcbls_l).
    eapply Mbox_common.TCBList_P_tcb_block_hold' with (prio:= i4) (tcs:= tcbls_r); eauto.
    clear -Hct_range; split; auto. int auto.
    eapply TcbMod_join_impl_prio_neq_cur_r; eauto.
    clear -H56 Hget_ct.
    unfolds; intros; eapply H56; eauto.
    eapply TcbMod.map_join_comm; eauto.
    eapply TcbMod.join_set_r; eauto.
    unfold TcbMod.indom; eauto.
    (* ECBList_P *)
    eapply ecblist_p_mutexpend';eauto.
    eapply evsllseg_aux with (s:= s); eauto.
    sep cancel (evsllseg v'12); eauto.
     assert (Hct_dly_eq: i6 = $ 0).
     { clear -Htcbnode_ct.
        funfold Htcbnode_ct.
        funfold H2.
        assert (Habs_eq: (i4, rdy, x14, false) = (i4, rdy, x14, false)) by auto.
        eapply H0 in Habs_eq.
        mytac.
        unfold V_OSTCBDly in H8; simpl in H8; inverts H8.
        auto.
       }
     subst i6; eauto.
   (* RH_ECBlk_EIBlk_Mux_P *)
(*     eapply RH_ECBlk_EIBlk_Mux_P_set_op;eauto. *)
(*     auto. *)
    (* RH_CurTCB *)
    unfold RH_CurTCB.
    rewrite TcbMod.map_get_set; eauto.
    (* RH_TCBList_ECBList_P *)
    eapply RH_TCBList_ECBList_P_high_block_hold_mutex'; eauto.

    pure_auto.
   (* end of EXIT CRITICAL *)
   (* needs partproof lemma *)
   simpl nth_val.
   eapply backward_rule1;
   [idtac | eapply OSMutexPendPart_proof with (vt := vt); eauto].
   introv Hsat; sep cancel Aier; sep pauto.

   (* case2: mutex owner is right to curp *)
    assert (Hot_right': TcbMod.get x8 (ot_b, ot_i) = Some (opt, ost, om, sus')).
    {  assert(Heq:  Some (opt, ost, om, sus') = TcbMod.get x8 (ot_b, ot_i)).
        { rewrite <- Hot_right.
            unfold TcbJoin in Htcbjoin_right.
           eapply TcbMod.map_join_get_none; eauto.
           eapply TcbMod.map_get_sig'; eauto.
         }
        rewrite Heq; auto.
    }
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (dllseg x5).
  eapply lzh_tcb_list_split.
  unfold tcbdllseg.
  sep cancel dllseg.
  exact_s.
  eapply Hot_right'.
  eauto.
  hoare unfold.
  rename H41 into Hget_last_tcb.
  rename v'38 into ot_b.
  rename H57 into Hot_node.
  rename H58 into Htcblist_sub_left.
  rename H59 into Htcblist_sub_right.

  rename H44 into Htcbjoin_sub_whole.
  rename H56 into Htcbjoin_sub_right.
  rename v'35 into tcbls_sub_l.
  rename v'36 into tcbls_sub_r.

  (* note: node_ct ++ tcbls_sub_l ++ ot_node ++ tcbls_sub_r = tcbls_r *)
  lets Hot_node': Hot_node.
  unfold TCBNode_P in Hot_node'.
  destruct Hot_node' as (Ht1 & Ht2 & Hot_blk & Hot_stat).
  inverts Ht1; inverts Ht2.
  (* split tcblist end *)
  (* pre condition about owner's x,y,bitx,bity range *)
  lets Hot_blk': Hot_blk.
  funfold Hot_blk'.
  rename x0 into opt.
  rename H66 into Hot_vx_range.
  rename H67 into Hot_vy_range.
  rename H68 into Hot_vbitx_range.
  rename H69 into Hot_vbity_range.
  rename H75 into Hopt_range.
  lets Hot_vx_range': post_intlemma4 Hopt_range.
  lets Hot_vy_range': shru_3_lt_8 Hopt_range.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  hoare unfold.
  rename H56 into Hrtbl_len.
  rename H36 into Hrtbl_array_mat.
  rename v'10 into rtbl. 
  rename H41 into Hrgrp_range.
  assert (Hot_vy_range'': (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3)) < length rtbl)%nat ).
  rewrite Hrtbl_len; unfold OS_RDY_TBL_SIZE,nat_of_Z; clear -Hot_vy_range'; auto with zarith.
  lets Hnth_rtbl: array_int8u_nth_lt_len Hrtbl_array_mat Hot_vy_range''.
  destruct Hnth_rtbl as (rtbl_vy & Hnth_rtbl_vy & Hrtbl_vy_range).
  lets Hot_vy_range_new: shru_3_lt_8 Hpip_range.
  assert (Hot_vy_range_new': 
                      (Z.to_nat (Int.unsigned ((x3 >>ᵢ $ 8) >>ᵢ $ 3)) 
                      < length (update_nth_val (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3))) rtbl
                                                                          (Vint32 (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))))))%nat ).
  rewrite update_nth_val_len_eq; rewrite Hrtbl_len; unfold OS_RDY_TBL_SIZE,nat_of_Z; clear -Hot_vy_range_new; auto with zarith.
  assert (Hrtbl_array_mat': array_type_vallist_match Int8u (update_nth_val (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3))) rtbl
                                                                          (Vint32 (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))))) ).
  {  eapply array_type_vallist_match_hold; eauto.
      simpl. eapply mund_int_a2; eapply le255_and_le255; auto. }
  lets Hnth_rtbl': array_int8u_nth_lt_len Hrtbl_array_mat' Hot_vy_range_new'.
  destruct Hnth_rtbl' as (rtbl_vy' & Hnth_rtbl_vy' & Hrtbl_vy_range').
    assert (Hot_vbity_range_new: Int.unsigned ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3)) <= 255).
  { remember ((x3 >>ᵢ $ 8) >>ᵢ $ 3) as py.
    clear -Hot_vy_range_new; mauto. }
  lets Hot_vx_range_new: post_intlemma4 Hpip_range.
  assert (Hot_vbitx_range_new: Int.unsigned ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7)) <= 255).
  { remember ((x3 >>ᵢ $ 8)&ᵢ$ 7) as px.
    clear -Hot_vx_range_new; mauto. }

  (* If (ptcb ′ → OSTCBPrio !=ₑ pip ′ &&ₑ mprio ′ >ₑ OSTCBCur ′ → OSTCBPrio) *)
   unfold AOSTCBPrioTbl.
   hoare unfold.
  hoare forward.
  go.
  clear -Hpip_range; eapply mund_int_a2; auto with zarith.
  clear -H; pure_auto.
  clear -H; pure_auto.
  go.
  eapply mund_int_a2; auto.
  clear -H; pure_auto.
  clear -H; pure_auto.
  (* Int.eq opt (x3 >>ᵢ $ 8) = false /\ Int.ltu i4 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true*)
  hoare unfold.
  destruct (Int.eq opt (x3 >>ᵢ $ 8)) eqn: eq2;
  destruct (Int.ltu i4 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) eqn: eq3;
  simpl in H60;
  try change (Int.notbool Int.one) with Int.zero in H60;
  try change (Int.notbool Int.zero) with Int.one in H60;
  try change (Int.ltu Int.zero Int.one) with true in H60;
  try change (Int.ltu Int.zero Int.zero) with false in H60;
  simpl in H60; tryfalse. clear H66 H67.
  (*   IF ((OSRdyTbl ′ [ptcb ′ → OSTCBY] &ₑ ptcb ′ → OSTCBBitX) !=ₑ ′ 0) *)
  hoare_lifts_trms_pre (Aop, Astruct (ot_b, Int.zero), Alvarmapsto ptcb,
                                                 GAarray OSRdyTbl, Agvarmapsto OSRdyGrp, Alvarmapsto os_code_defs.isrdy ).
  hoare remember (1 :: 2 :: 3 :: 4 :: 5 :: 6 ::  nil)%nat pre.
  eapply seq_rule.
   instantiate(1:= (<|| spec_code_cons (mutexpend (Vptr (mid_b, Int.zero) :: Vint32 vt :: opv :: nil)) v'3 ||>  **
  Astruct (ot_b, Int.zero) OS_TCB_flag
    (v'34
     :: v'32
        :: x15
           :: om
              :: Vint32 i8
                 :: Vint32 x13
                    :: Vint32 opt
                       :: Vint32 (opt&ᵢ$ 7)
                          :: Vint32 (opt >>ᵢ $ 3)
                             :: Vint32 ($ 1<<ᵢ(opt&ᵢ$ 7))
                                :: Vint32 ($ 1<<ᵢ(opt >>ᵢ $ 3)) :: nil) **
  LV ptcb @ OS_TCB ∗ |-> Vptr (ot_b, Int.zero) **
  GAarray OSRdyTbl (Tarray char_t ∘ OS_RDY_TBL_SIZE) 
           (if Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero
             then rtbl
             else (update_nth_val (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3))) rtbl (Vint32 (rtbl_vy&ᵢ(Int.not ($ 1<<ᵢ(opt&ᵢ$ 7)))))) )   **
  GV OSRdyGrp @ char_t |-> (if Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero
                                                          then  Vint32 i
                                                         else (if Int.eq (rtbl_vy&ᵢ(Int.not ($ 1<<ᵢ(opt&ᵢ$ 7)))) Int.zero 
                                                                        then Vint32 (i&ᵢ(Int.not ($ 1<<ᵢ(opt>>ᵢ $ 3))))
                                                                        else  Vint32 i)) **
  LV os_code_defs.isrdy @ char_t |-> (if  Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero
                                                                             then V$ 0 else V$ 1) ** H66)).
  hoare forward.
  go.
  rewrite Hnth_rtbl_vy; clear -Hrtbl_vy_range; pure_auto.
  go.
  rewrite Hnth_rtbl_vy; clear -H;pure_auto.
  rewrite Hnth_rtbl_vy; clear -H; simpl;  destruct (Int.eq (rtbl_vy&ᵢ(Int.not ($ 1<<ᵢ(opt&ᵢ$ 7)))) ($ 0)); pure_auto.
  rewrite Hnth_rtbl_vy; clear -H;
  simpl;  destruct (Int.eq (rtbl_vy&ᵢ(Int.not ($ 1<<ᵢ(opt&ᵢ$ 7)))) ($ 0)); pure_auto.
  rewrite Hnth_rtbl_vy.
  change ($ 0) with Int.zero.
  simpl val_inj.
   (* Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero = false *)
  hoare_split_pure_all.
  rename H67 into Hsat_if.
  destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: vbitx_eq_cond;
  simpl in Hsat_if;
  try change (Int.notbool Int.one) with Int.zero in Hsat_if;
  try change (Int.notbool Int.zero) with Int.one in Hsat_if;
  simpl in Hsat_if; destruct Hsat_if as (Hif_rdy_cond & _ & _);tryfalse.
(*   clear Hif_rdy_cond. *)
  instantiate(1:= (<|| spec_code_cons (mutexpend (Vptr (mid_b, Int.zero) :: Vint32 vt :: opv :: nil)) v'3 ||>  **
  Astruct (ot_b, Int.zero) OS_TCB_flag
    (v'34
     :: v'32
        :: x15
           :: om
              :: Vint32 i8
                 :: Vint32 x13
                    :: Vint32 opt
                       :: Vint32 (opt&ᵢ$ 7)
                          :: Vint32 (opt >>ᵢ $ 3)
                             :: Vint32 ($ 1<<ᵢ(opt&ᵢ$ 7))
                                :: Vint32 ($ 1<<ᵢ(opt >>ᵢ $ 3)) :: nil) **
  LV ptcb @ OS_TCB ∗ |-> Vptr (ot_b, Int.zero) **
  GAarray OSRdyTbl (Tarray char_t ∘ OS_RDY_TBL_SIZE) 
                    (update_nth_val (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3))) rtbl (Vint32 (rtbl_vy&ᵢ(Int.not ($ 1<<ᵢ(opt&ᵢ$ 7)))))) **
  GV OSRdyGrp @ char_t |-> (if Int.eq (rtbl_vy&ᵢ(Int.not ($ 1<<ᵢ(opt&ᵢ$ 7)))) Int.zero 
                                                            then Vint32 (i&ᵢ(Int.not ($ 1<<ᵢ(opt>>ᵢ $ 3))))
                                                            else  Vint32 i) **
  LV os_code_defs.isrdy @ char_t |-> (V$ 1) ** H66)).
 (*  OSRdyTbl ′ [ptcb ′ → OSTCBY] &= ∼ ptcb ′ → OSTCBBitX;ₛ *)
  hoare unfold.
  hoare forward.
  go.
  rewrite Hnth_rtbl_vy; clear -Hrtbl_vy_range; pure_auto.
  go.
  rewrite Hnth_rtbl_vy; clear -Hrtbl_vy_range; pure_auto.
  go.
  rewrite Hnth_rtbl_vy.
  assert (Hot_vy_range''': Int.unsigned (opt >>ᵢ $ 3) < Z.of_nat (length rtbl)).
  clear -Hot_vy_range''; auto with zarith.
  lets Hup_rtbl_vy_eq: len_lt_update_get_eq Hot_vy_range'''.
  instantiate(1:= (Vint32 (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))))) in Hup_rtbl_vy_eq.
  (* If (OSRdyTbl ′ [ptcb ′ → OSTCBY] ==ₑ ′ 0) *)
   hoare forward.
   go.
   rewrite update_nth_val_len_eq; auto.
   rewrite Hup_rtbl_vy_eq.
   clear -Hrtbl_vy_range; simpl.
   eapply mund_int_a2; eapply le255_and_le255; auto.
    rewrite Hup_rtbl_vy_eq; simpl; clear -H; pure_auto.
   rewrite Hup_rtbl_vy_eq; simpl val_inj.
   hoare_split_pure_all.
   rename H66 into Hsat_if.
   destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: vbitx_eq_cond2;
   simpl in Hsat_if; destruct Hsat_if as (Hif_cond & _ & _); tryfalse.
   (* OSRdyGrp ′ &= ∼ ptcb ′ → OSTCBBitY *)
    hoare forward.
    clear -Hrgrp_range; pure_auto.
    go.
    (* os_code_defs.isrdy ′ =ₑ ′ 1 *)
    hoare forward;
    rewrite Hup_rtbl_vy_eq;
    hoare_split_pure_all;
    simpl in H66;
    rename H66 into Hsat_if.
    destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: vbitx_eq_cond2;
   simpl in Hsat_if; destruct Hsat_if as (Hif_cond & _  & _); tryfalse.
   hoare forward.
   sep cancel Aier. (* new add *)
   sep auto.
  Optimize Proof.
  Optimize Heap.
   destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: vbitx_eq_cond2;
   simpl in Hsat_if; destruct Hsat_if as [Hif_cond1 | Hif_cond2 ]; tryfalse.
    hoare forward.
    sep cancel Aier. (* new add *)
    sep auto.
   (* os_code_defs.isrdy ′ =ₑ ′ 0 *)
   hoare forward.
   rename H67 into Hsat.
   rewrite Hnth_rtbl_vy in Hsat.
   change ($ 0) with Int.zero in Hsat.
   simpl val_inj in Hsat.
   destruct Hsat as [Hsat | Hsat];
   destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1;
   simpl val_inj in Hsat;
   try change (Int.notbool Int.one) with Int.zero in Hsat;
   try change (Int.notbool Int.zero) with Int.one in Hsat;
   simpl val_inj in Hsat;
   sep pauto; try destruct H67; tryfalse.
    (* OSTCBPrioTbl ′ [ptcb ′ → OSTCBPrio] =ₑ 〈 OS_TCB ∗ 〉 PlaceHolder;ₛ *)
   subst H66.
   unfold PlaceHolder.
   hoare unfold.
   hoare forward.
   eapply forward_rule2.
   eapply assign_rule_array_g_aop.
   intro.
   split.
   intro.
   sep cancel A_dom_lenv.
   sep cancel (GAarray OSTCBPrioTbl); eauto.
   intro.
   sep auto.
   simpl; auto.
   2 : symbolic execution.
   {
   introv Hsat.
   eapply cast_rv_tptr.
  eapply addrof_gvar_rv.
  apply  astar_l_anotinlenv_intro.
  sep cancel Agvarenv'.
  eauto.

  sep_lifts_trms_in Hsat A_dom_lenv.
  apply astar_l_adomlenv_elim in Hsat.
  destruct Hsat as (Hsat & _).
  clear -Hsat.
  unfolds in Hsat.
  unfolds. unfold EnvMod.indom. introv Hget.
  destruct Hget as ((l & t) & Hget).
  assert (Hnot: ~ (ListSet.set_In (OSPlaceHolder, t)
        ((os_code_defs.timeout, Int16u)
          :: (pevent, OS_EVENT ∗)
             :: (pip, char_t)
                :: (mprio, char_t)
                   :: (os_code_defs.isrdy, char_t) :: (ptcb, OS_TCB ∗) :: nil))).
  unfolds. simpl. intros. repeat (destruct H; tryfalse).
  eapply Hnot.
  erewrite Hsat.
  eauto.

  simpl; auto.
  }
  go.
  auto.
  clear -Hopt_range; auto with zarith.
  eapply eq_vptr; eauto.
  rewrite H59; clear -Hopt_range; auto with zarith.
  intros.
  sep eexists. 
  sep cancel p_local.
  simpl; auto.
  eauto.
  (* end of assign PlaceHolder *)
   (* ptcb ′ → OSTCBPrio =ₑ pip ′;ₛ *)
   hoare unfold.
   hoare forward.
   clear -Hpip_range; eapply mund_int_a2; auto with zarith.
  (* ptcb ′ → OSTCBY =ₑ ptcb ′ → OSTCBPrio ≫ ′ 3;ₛ*)
   hoare forward.
   go.
   rewrite int_iwordsize_gt_3.
   simpl val_inj.
  (* ptcb ′ → OSTCBBitY =ₑ OSMapTbl ′ [ptcb ′ → OSTCBY];ₛ *)
  unfold AOSMapTbl.
  lets Hmap_vy: xmapis1shlx Hot_vy_range_new.
  hoare forward.
  go.
  rewrite Hmap_vy; simpl; eapply mund_int_a2; auto.
  rewrite Hmap_vy.
  (* ptcb ′ → OSTCBX =ₑ ptcb ′ → OSTCBPrio &ₑ ′ 7;ₛ *)
   hoare forward.
   go.
  (* ptcb ′ → OSTCBBitX =ₑ OSMapTbl ′ [ptcb ′ → OSTCBX];ₛ *)
   lets Hmap_vx: xmapis1shlx Hot_vx_range_new.
   hoare forward.
   go.
  rewrite Hmap_vx; simpl; eapply mund_int_a2; auto.
  rewrite Hmap_vx.
  (* If (os_code_defs.isrdy ′ ==ₑ ′ 1) *)
  hoare remember (1 :: 2:: 3 :: 6 :: 7 :: 8 ::  nil)%nat pre.
  eapply seq_rule.
  instantiate (1:= (<|| spec_code_cons
    (mutexpend (Vptr (mid_b, Int.zero) :: Vint32 vt :: opv :: nil)) v'3 ||>  **
  LV ptcb @ OS_TCB ∗ |-> Vptr (ot_b, Int.zero) **
  Astruct (ot_b, Int.zero) OS_TCB_flag
    (v'34
     :: v'32
        :: x15
           :: om
              :: Vint32 i8
                 :: Vint32 x13
                    :: Vint32 (x3 >>ᵢ $ 8)
                       :: Vint32 ((x3 >>ᵢ $ 8)&ᵢ$ 7)
                          :: Vint32 ((x3 >>ᵢ $ 8) >>ᵢ $ 3)
                             :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))
                                :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))
                                   :: nil) **
  GAarray OSRdyTbl (Tarray char_t ∘ OS_RDY_TBL_SIZE)
    (if Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero
     then rtbl
     else
      (update_nth_val (Z.to_nat (Int.unsigned ((x3 >>ᵢ $ 8) >>ᵢ $ 3)))
                                       (update_nth_val (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3))) rtbl
                                                                          (Vint32 (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7)))))
                                        (Vint32 (Int.or (rtbl_vy') ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7)))))  ) **
  GV OSRdyGrp @ char_t
  |-> (if Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero
       then Vint32 i
       else
        if Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero
        then Vint32 (Int.or (i&ᵢInt.not ($ 1<<ᵢ(opt >>ᵢ $ 3))) ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3)))
        else Vint32 (Int.or (i) ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))) ) **
  LV os_code_defs.isrdy @ char_t
  |-> (if Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero then V$ 0 else V$ 1) **
  H66)).
   hoare forward.
   destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1;
   simpl; clear -H; pure_auto.
   destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1;
   simpl; clear -H; pure_auto.
   hoare_split_pure_all.
   destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1;
   simpl in H67;  try change (Int.eq ($ 0) ($ 1)) with false in H67; try change (Int.eq ($ 1) ($ 1)) with true in H67;
   simpl in H67; destruct H67 as (Hif_cond & _ & _);tryfalse.
   (* OSRdyGrp ′ =ₑ OSRdyGrp ′ |ₑ ptcb ′ → OSTCBBitY;ₛ *)
    hoare unfold.
   hoare forward.
   destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: vbitx_eq_cond2;
   simpl; clear -Hrgrp_range; eapply mund_int_a2; try eapply le255_and_le255; auto. 
   go.
   destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: vbitx_eq_cond2;
   simpl; clear -H; pure_auto. 
   (* OSRdyTbl ′ [ptcb ′ → OSTCBY] =ₑ OSRdyTbl ′ [ptcb ′ → OSTCBY] |ₑ ptcb ′ → OSTCBBitX *)
    hoare forward.
    go.
    rewrite Hnth_rtbl_vy'; clear -Hrtbl_vy_range'; simpl; pure_auto.
    go.
    rewrite Hnth_rtbl_vy'; clear -H; simpl; pure_auto.
    go.
    clear -Hot_vy_range_new; unfold OS_RDY_TBL_SIZE; auto with zarith.
   (* post condition process, if isrdy == 1*)
   rename H67 into Hsat.
   rewrite Hnth_rtbl_vy' in Hsat.
   destruct Hsat as [Hsat | Hsat];
   destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1;
   simpl val_inj in Hsat;
   try change (Int.eq ($ 0) ($ 1)) with false in Hsat;
   try change (Int.eq ($ 1) ($ 1)) with true in Hsat;
   simpl val_inj in Hsat;
   sep pauto; tryfalse.
   sep auto.
   destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: vbitx_eq_cond2;
   simpl; auto.
   destruct H66;tryfalse.
   destruct H66;tryfalse.
  (* OSTCBPrioTbl ′ [pip ′] =ₑ 〈 OS_TCB ∗ 〉 ptcb ′ *)
  subst H66.
  eapply forward_rule1; [idtac | hoare forward].
  eauto.
  clear -Hpip_range; eapply mund_int_a2; auto with zarith.
  rewrite update_nth_val_len_eq; rewrite H59; clear -Hpip_range; auto with zarith.

  assert (Hif_rdy_imp: Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero = false ->
                                               prio_in_tbl opt rtbl /\ (* ost = rdy /\ *) i8 = $ 0 (* /\ x13 = $ OS_STAT_RDY *)). (* x12 -> x13 *)
  { introv Hif_rdy_cond.
     assert (Hopt_case: prio_in_tbl opt rtbl \/ prio_not_in_tbl opt rtbl) by
                   (eapply prio_rtbl_dec; eauto).
    assert (Hopt_in_rtbl: prio_in_tbl opt rtbl).
    { destruct Hopt_case as [Hopt_rdy | Hfalse]; auto.
       unfolds in Hfalse.
       eapply nth_val'2nth_val in Hnth_rtbl_vy.
       clear -Hnth_rtbl_vy Hfalse Hif_rdy_cond.
       eapply Hfalse in Hnth_rtbl_vy; eauto.
       eapply eq2inteq in Hnth_rtbl_vy; change ($ 0) with Int.zero in Hnth_rtbl_vy.
       rewrite Hif_rdy_cond in Hnth_rtbl_vy; tryfalse.
     }
   assert (Hopt_rdy: RdyTCBblk (v'34
              :: v'32
                 :: x15
                    :: om
                       :: Vint32 i8
                          :: Vint32 x13
                             :: Vint32 opt
                                :: Vint32 (opt&ᵢ$ 7)
                                   :: Vint32 (opt >>ᵢ $ 3)
                                      :: Vint32 ($ 1<<ᵢ(opt&ᵢ$ 7))
                                         :: Vint32 ($ 1<<ᵢ(opt >>ᵢ $ 3)) :: nil) rtbl opt).
   { unfolds. split; auto. }
   destruct Hot_stat as (Hot_stat_rdy & _).
   eapply Hot_stat_rdy in Hopt_rdy.
   unfold V_OSTCBStat,V_OSTCBDly in Hopt_rdy; simpl nth_val in Hopt_rdy.
   destruct Hopt_rdy as (Heq1 & Heq2 (*  & (m & Heq3) *)).
  inverts Heq1. splits; eauto.
  }
 (* case2.1 : mutex owner is right to curp, owner's priority lift to pip *)
  hoare forward.
  (* Int.eq opt (x3 >>ᵢ $ 8) = false /\ Int.ltu i4 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true*)
  hoare unfold.
  destruct (Int.eq opt (x3 >>ᵢ $ 8)) eqn: eq2;
  destruct (Int.ltu i4 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) eqn: eq3;
  simpl in H60;
  try change (Int.notbool Int.one) with Int.zero in H60;
  try change (Int.notbool Int.zero) with Int.one in H60;
  try change (Int.ltu Int.zero Int.one) with true in H60;
  try change (Int.ltu Int.zero Int.zero) with false in H60;
  simpl in H60; tryfalse. clear H66 H67.
  assert (Hpip_non_tls: prio_available (x3 >>ᵢ $ 8) tcbls).
 { destruct H as (_ & _ & _ & H).
    eapply H; eauto.
    eapply semacc_int_eq_false; eauto.
  }
  (* OSTCBCur ′ → OSTCBStat =ₑ OSTCBCur ′ → OSTCBStat |ₑ ′ OS_STAT_MUTEX;ₛ  *)
  hoare forward.
  go.
  rewrite Hor.
  (* OSTCBCur ′ → OSTCBDly =ₑ os_code_defs.timeout ′;ₛ *)
  hoare forward.
  clear -Hvt_range; pauto.
  (* OS_EventTaskWait (­ pevent ′­);ₛ *)
  hoare_lifts_trms_pre (Aisr, Ais, A_isr_is_prop, aemp_isr_is).
  transform_pre a_isr_is_prop_split ltac:(idtac).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  hoare_split_pure_all.
  assert (  RL_TCBblk_P
     (v'34
     :: v'32
        :: x15
           :: om
              :: Vint32 i8
                 :: Vint32 x13
                    :: Vint32 (x3 >>ᵢ $ 8)
                       :: Vint32 ((x3 >>ᵢ $ 8)&ᵢ$ 7)
                          :: Vint32 ((x3 >>ᵢ $ 8) >>ᵢ $ 3)
                             :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))
                                :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))
                                   :: nil)) as Hnewrltcbblkp.
  {
    unfolds.
    do 6 eexists;splits; 
    try (unfolds;simpl;eauto).
    split; auto.
    clear; int auto.
    splits; auto.
    eexists.
    split; auto.
    unfolds;simpl;auto.
  }
   assert (Hpintbl: prio_in_tbl ($ OS_IDLE_PRIO) 
                                         (update_nth_val (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3))) rtbl
                                               (Vint32 (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7)))))).
  { eapply idle_in_rtbl_hold; eauto. }
  lets Hpintbl': Hpintbl.
  eapply idle_in_rtbl_hold' in Hpintbl'; eauto.
  erewrite Hnth_rtbl_vy' in Hpintbl'.
  simpl val_inj in Hpintbl'.

  hoare unfold.
  hoare forward.

  unfold node.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  sep pauto.
  instantiate (9:= ct_b).
  sep cancel (Astruct (ct_b,Int.zero)).
  sep cancel p_local.
  instantiate  (2:= (DMutex (Vint32 x3) (Vptr (ot_b, Int.zero)))).
  unfold AEventNode.
  sep cancel AEventData.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Aarray.
  sep cancel AOSPostEventTbl.
  instantiate (2:= mid_b).
  sep cancel (Astruct (mid_b, Int.zero)).
  eauto.
  eauto.
  unfolds; simpl; eauto.
  eauto.
  eauto.
  unfolds; simpl; auto.
  eauto.
  auto.
  Optimize Proof.
  Optimize Heap.
  split; auto. go.
  (* RL_Tbl_Grp_P /\  prio_in_tbl *)
  destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1;
  try destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond2;
  split; auto;
  try eapply OSTimeDlyPure.event_wait_rl_tbl_grp; eauto.
  eapply OSTimeDlyPure.event_wait_rl_tbl_grp';eauto.
  eapply OSTimeDlyPure.event_wait_rl_tbl_grp''; eauto.
 (* end of RL_Tbl_Grp_P /\  prio_in_tbl *)
  destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1;
  try destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond2;
  eapply mund_int_a2; try eapply int_unsigned_or_prop'; try eapply le255_and_le255; auto with zarith.
  destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1;
  try destruct (Int.eq (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond2;
  split; 
  try rewrite update_nth_val_len_eq; try rewrite update_nth_val_len_eq;
  try eapply array_type_vallist_match_hold; eauto;
  try eapply mund_int_a2; try eapply int_unsigned_or_prop'; 
  try eapply le255_and_le255; auto with zarith.

  split;auto. go.
  split; simpl; auto.
  eexists; split; try (unfold V_OSTCBPrio; simpl nth_val); try eapply Int.eq_false; eauto. 
  { clear -Htcb_rl; unfolds; unfolds in Htcb_rl.
     mytac.
     do 6 eexists; splits; try (unfolds; simpl; eauto).
     split;auto.
     splits; auto.
     pauto.
     eexists; split.
     unfolds; simpl; eauto.
     introv Hf; destruct Hf as [Hf | Hf]; tryfalse. }
  go.

  intros. sep pauto. sep cancel p_local. simpl; auto.
  intros. sep pauto. sep cancel p_local. simpl; auto.
  (* OS_EventTaskWaitPost *)
  hoare_ex_intro.
  unfold OS_EventTaskWaitPost.
  unfold OS_EventTaskWaitPost'.
  unfold getasrt.
  hoare_split_pure_all.
  inverts H66.
  unfold V_OSTCBY,V_OSTCBBitX,V_OSTCBBitY,V_OSEventGrp in H68.
  simpl in H67,H68.
  mytac_H.
  inverts H67; inverts H68; inverts H69; inverts H70; inverts H78.

  (* mutex owner is rdy *)
   hoare_lifts_trms_pre (Aop, absecblist,abstcblist,ostm,oscurt, absptlsid ,EvtInv_part2).
   assert (Host_case: (ost = rdy /\ sus' = false) \/ ~(ost = rdy /\ sus' = false)) by tauto.
   destruct Host_case as [(Host_eq & Hsus_eq) | Habt].
   2: { eapply abscsq_rule.
           apply noabs_oslinv.
           eapply mutexpend_absimp_owner_not_ready_abt'; eauto.
           can_change_aop_solver.
           apply absinfer_eq.
           eapply absabort_rule.
         }
     subst sus'.
     subst ost.
  (* change absdata *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexpend_absimp_block_lift'; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  2:{ clear -Hot_vy_range_new; auto with zarith. }
  2:{ rewrite update_nth_val_len_eq; auto. }
  (* EXIT_CRITICAL;ₛ *)
   assert (Htlsp1: 
                       TCBList_P (Vptr (ct_b, Int.zero))
  ((x5
    :: v'15
       :: Vptr (mid_b, Int.zero)
          :: x14
             :: Vint32 vt
                :: V$ OS_STAT_MUTEX
                   :: Vint32 i4
                      :: Vint32 (i4&ᵢ$ 7)
                         :: Vint32 (i4 >>ᵢ $ 3)
                            :: Vint32 ($ 1<<ᵢ(i4&ᵢ$ 7))
                               :: Vint32 ($ 1<<ᵢ(i4 >>ᵢ $ 3)) :: nil)
   :: (v'8 ++
       (v'34
        :: v'32
           :: x15
              :: om
                 :: Vint32 i8
                    :: Vint32 x13
                       :: Vint32 (x3 >>ᵢ $ 8)
                          :: Vint32 ((x3 >>ᵢ $ 8)&ᵢ$ 7)
                             :: Vint32 ((x3 >>ᵢ $ 8) >>ᵢ $ 3)
                                :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))
                                   :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))
                                      :: nil) :: nil) ++ v'13)
  (update_nth_val ∘ (Int.unsigned (i4 >>ᵢ $ 3))
     (if Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero
      then rtbl
      else
       update_nth_val (Z.to_nat (Int.unsigned ((x3 >>ᵢ $ 8) >>ᵢ $ 3)))
         (update_nth_val (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3))) rtbl
            (Vint32 (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7)))))
         (Vint32 (Int.or rtbl_vy' ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7)))))
     (Vint32 (v'49&ᵢInt.not ($ 1<<ᵢ(i4&ᵢ$ 7)))))
        (TcbMod.set (TcbMod.set tcbls_r (ot_b, Int.zero) (x3 >>ᵢ $ 8, rdy, om, false)) (ct_b, Int.zero)
                                             (i4, wait (os_stat_mutexsem (mid_b, Int.zero)) (if Int.eq vt Int.zero then None else (Some vt)), x14, false))).
   { 
     assert (Hct_i4_neq: prio_neq_cur (TcbMod.set tcbls_r (ot_b, Int.zero) (x3 >>ᵢ $ 8, rdy, om, false)) (ct_b, Int.zero) i4).
   { unfolds; intros.
      rewrite TcbMod.set_sem in H67.
     destruct (tidspec.beq (ot_b, Int.zero) tid) eqn: eq_td.
     inverts H67.
     clear -Hpip_non_tls Hget_ct.
     eapply semacc_int_eq_false; eapply Hpip_non_tls; eauto.
     eapply H56; eauto.
     eapply TcbMod.join_get_r;eauto. }
    assert (Hget_set: TcbMod.get (TcbMod.set tcbls_r (ot_b, Int.zero) (x3 >>ᵢ $ 8, rdy, om, false))
  (ct_b, Int.zero) = Some (i4, rdy, x14, false)).
   { rewrite TcbMod.set_a_get_a'; eauto.
      eapply tidspec.neq_beq_false; eauto.
      (* rewrite <- Hget_ct'.
      eapply TcbMod.map_get_set'; eauto. *)
    }
    destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1.
    destruct (Int.eq vt Int.zero) eqn: Heq_t.
    eapply semacc_int_eq_true in Heq_t.
    eapply TCBList_P_tcb_block_hold_mutex'_none; eauto.
    simpl TCBList_P.
    unfold V_OSTCBNext. simpl nth_val.
    do 3 eexists; exists (i4, rdy, x14, false); splits; eauto.
     lets Hnew_join:  TcbMod.map_join_comm Htcbjoin_sub_whole.
     lets Hnew_join_sig: tcb_join_joinsig_ex_joinsig Hnew_join Htcbjoin_sub_right.
     clear Hnew_join. destruct Hnew_join_sig as ( merge_tcb & Hnew_join_sig).
    eapply TcbMod.my_joinsig_join_set with (mb:= x8); eauto.
    { rewrite <- app_assoc.
       rewrite l2.
       eapply TCBList_P_Combine; eauto.
       eapply TcbMod.my_joinsig_join_set; eauto.
       simpl TCBList_P.
       unfold V_OSTCBNext. simpl nth_val.
       do 3 eexists; eexists (x3 >>ᵢ $ 8, rdy, om, false); splits; eauto.
       eapply tcbjoin_set_my;eauto.
       simpl.
       unfold V_OSTCBMsg,V_OSTCBPrio.
       simpl nth_val.
       splits; auto.
       eapply R_TCB_Status_P_change_prio;eauto.
       clear -Hpip_range; split;auto; int auto.
       { (* prio_not_in_tbl opt rtbl *)
         unfold prio_not_in_tbl.
         intros x2' y z Heq1 Heq2 Hnth_new.
         subst x2'; subst y.
         eapply nth_val_nth_val'_some_eq in Hnth_new.
         unfold nat_of_Z in Hnth_new.
         rewrite Hnth_rtbl_vy in Hnth_new.
         inverts Hnth_new.
         change ($ 0) with Int.zero.
         eapply inteqeq; eauto. } }
    eapply semacc_int_eq_false in Heq_t.
    eapply TCBList_P_tcb_block_hold_mutex'; eauto.
    simpl TCBList_P.
    unfold V_OSTCBNext. simpl nth_val.
    do 3 eexists; exists (i4, rdy, x14, false); splits; eauto.
     lets Hnew_join:  TcbMod.map_join_comm Htcbjoin_sub_whole.
     lets Hnew_join_sig: tcb_join_joinsig_ex_joinsig Hnew_join Htcbjoin_sub_right.
     clear Hnew_join. destruct Hnew_join_sig as ( merge_tcb & Hnew_join_sig).
    eapply TcbMod.my_joinsig_join_set with (mb:= x8); eauto.
    { rewrite <- app_assoc.
       rewrite l2.
       eapply TCBList_P_Combine; eauto.
       eapply TcbMod.my_joinsig_join_set; eauto.
       simpl TCBList_P.
       unfold V_OSTCBNext. simpl nth_val.
       do 3 eexists; eexists (x3 >>ᵢ $ 8, rdy, om, false); splits; eauto.
       eapply tcbjoin_set_my;eauto.
       simpl.
       unfold V_OSTCBMsg,V_OSTCBPrio.
       simpl nth_val.
       splits; auto.
       eapply R_TCB_Status_P_change_prio;eauto.
       clear -Hpip_range; split;auto; int auto.
       { (* prio_not_in_tbl opt rtbl *)
         unfold prio_not_in_tbl.
         intros x2' y z Heq1 Heq2 Hnth_new.
         subst x2'; subst y.
         eapply nth_val_nth_val'_some_eq in Hnth_new.
         unfold nat_of_Z in Hnth_new.
         rewrite Hnth_rtbl_vy in Hnth_new.
         inverts Hnth_new.
         change ($ 0) with Int.zero.
         eapply inteqeq; eauto. } }
   (* case:  Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero = false *)
    destruct (Int.eq vt Int.zero) eqn: Heq_t.
    eapply semacc_int_eq_true in Heq_t. subst.
    eapply TCBList_P_tcb_block_hold_mutex'_none; eauto.
   assert (Hvll_eq: forall (vl1 vl2: vallist) (vll2 vll3: list vallist), 
                                 vl1 :: (vll2 ++ vl2 :: nil) ++ vll3 = (vl1 :: nil) ++ (vll2 ++ (vl2 :: vll3))).
   { intros; rewrite <- app_assoc. simpl; auto. }
   rewrite Hvll_eq.
    eapply TCBList_P_Combine; eauto.
    simpl; unfold V_OSTCBNext; simpl; eauto.
    lets Hnew_join:  TcbMod.map_join_comm Htcbjoin_sub_whole.
     lets Hnew_join_sig: tcb_join_joinsig_ex_joinsig Hnew_join Htcbjoin_sub_right.
     clear Hnew_join. destruct Hnew_join_sig as ( merge_tcb & Hnew_join_sig).
    eapply TcbMod.my_joinsig_join_set with (mb:= x8); eauto.
    clear -Htcbjoin_right; unfold TcbJoin in Htcbjoin_right; eauto.
    eapply TCBList_P_rtbl_add_simpl_version;eauto.
    clear -Hpip_range; split;auto. int auto.
    unfold nat_of_Z; eapply nth_val'2nth_val;eauto.
    clear -Hpip_non_tls Htcbjoin_whole Hget_ct.
    intros; eapply semacc_int_eq_false; rewrite Int.eq_sym.
    rewrite TcbMod.sig_sem in H.
    destruct (tidspec.beq (ct_b, Int.zero) tid) eqn: eq1; tryfalse.
    inverts H.
     eapply Hpip_non_tls; eauto.
    eapply Mbox_common.TCBList_P_tcb_block_hold'  with (tcs := x8); eauto.
    clear -Htcbjoin_right; unfold TcbJoin in Htcbjoin_right; eauto.
    simpl TCBList_P.
    unfold V_OSTCBNext. simpl nth_val.
    do 4 eexists; splits; eauto.
    apply TcbMod.map_join_emp.
     clear -H56 Htcbjoin_whole Hget_ct Hget_ot.
     unfolds; intros.
      rewrite TcbMod.sig_sem in H0.
      destruct (tidspec.beq (ct_b, Int.zero) tid) eqn: eq1; tryfalse.
      inverts H0.
      eapply tidspec.beq_true_eq in eq1; subst.
      eapply H56; eauto.
       unfold nat_of_Z; eapply nth_val'2nth_val;eauto.
        assert (Heq_f: false = false) by auto.
         lets Hot_rdy_eq: Hif_rdy_imp Heq_f.
         assert(Hif_rdy_imp2: (* ost = rdy ->  *)x13 = $ OS_STAT_RDY ).
        { clear -Hot_node.  funfold Hot_node. 
          funfold H2. specialize (H0 _ _ (eq_refl _)).
         destruct H0 as (Hr & Hst & Hd).
         inverts Hst. auto. }
          subst x13.
         destruct Hot_rdy_eq as (Hopt_in_rtbl & (* Host_eq & *) Hdly_eq (* & Hst_eq *)).
         substs.
         eapply tcbls_l_mutexpend';eauto.
         eapply join_prop_mutexpend''''; eauto.
         eapply semacc_int_eq_false; rewrite Int.eq_sym.
         eapply Hpip_non_tls; eauto.
    eapply semacc_int_eq_false in Heq_t. subst.
    eapply TCBList_P_tcb_block_hold_mutex'; eauto.
   assert (Hvll_eq: forall (vl1 vl2: vallist) (vll2 vll3: list vallist), 
                                 vl1 :: (vll2 ++ vl2 :: nil) ++ vll3 = (vl1 :: nil) ++ (vll2 ++ (vl2 :: vll3))).
   { intros; rewrite <- app_assoc. simpl; auto. }
   rewrite Hvll_eq.
    eapply TCBList_P_Combine; eauto.
    simpl; unfold V_OSTCBNext; simpl; eauto.
    lets Hnew_join:  TcbMod.map_join_comm Htcbjoin_sub_whole.
     lets Hnew_join_sig: tcb_join_joinsig_ex_joinsig Hnew_join Htcbjoin_sub_right.
     clear Hnew_join. destruct Hnew_join_sig as ( merge_tcb & Hnew_join_sig).
    eapply TcbMod.my_joinsig_join_set with (mb:= x8); eauto.
    clear -Htcbjoin_right; unfold TcbJoin in Htcbjoin_right; eauto.
    eapply TCBList_P_rtbl_add_simpl_version;eauto.
    clear -Hpip_range; split;auto. int auto.
    unfold nat_of_Z; eapply nth_val'2nth_val;eauto.
    clear -Hpip_non_tls Htcbjoin_whole Hget_ct.
    intros; eapply semacc_int_eq_false; rewrite Int.eq_sym.
    rewrite TcbMod.sig_sem in H.
    destruct (tidspec.beq (ct_b, Int.zero) tid) eqn: eq1; tryfalse.
    inverts H.
     eapply Hpip_non_tls; eauto.
    eapply Mbox_common.TCBList_P_tcb_block_hold' with (tcs := x8); eauto.
    clear -Htcbjoin_right; unfold TcbJoin in Htcbjoin_right; eauto.
    simpl TCBList_P.
    unfold V_OSTCBNext. simpl nth_val.
    do 4 eexists; splits; eauto.
    apply TcbMod.map_join_emp.
     clear -H56 Htcbjoin_whole Hget_ct Hget_ot.
     unfolds; intros.
      rewrite TcbMod.sig_sem in H0.
      destruct (tidspec.beq (ct_b, Int.zero) tid) eqn: eq1; tryfalse.
      inverts H0.
      eapply tidspec.beq_true_eq in eq1; subst.
      eapply H56; eauto.
       unfold nat_of_Z; eapply nth_val'2nth_val;eauto.
        assert (Heq_f: false = false) by auto.
         lets Hot_rdy_eq: Hif_rdy_imp Heq_f.
         assert(Hif_rdy_imp2: (* ost = rdy ->  *)x13 = $ OS_STAT_RDY ).
        { clear -Hot_node.  funfold Hot_node. 
          funfold H2. specialize (H0 _ _ (eq_refl _)).
         destruct H0 as (Hr & Hst & Hd).
         inverts Hst. auto. }
          subst x13.
         destruct Hot_rdy_eq as (Hopt_in_rtbl & (* Host_eq & *) Hdly_eq (* & Hst_eq *)).
         substs.
         eapply tcbls_l_mutexpend';eauto.
         eapply join_prop_mutexpend''''; eauto.
         eapply semacc_int_eq_false; rewrite Int.eq_sym.
         eapply Hpip_non_tls; eauto.
    }
    assert (Htlsp2: TCBList_P v'5 v'7
  (update_nth_val ∘ (Int.unsigned (i4 >>ᵢ $ 3))
     (if Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero
      then rtbl
      else
       update_nth_val (Z.to_nat (Int.unsigned ((x3 >>ᵢ $ 8) >>ᵢ $ 3)))
         (update_nth_val (Z.to_nat (Int.unsigned (opt >>ᵢ $ 3))) rtbl
            (Vint32 (rtbl_vy&ᵢInt.not ($ 1<<ᵢ(opt&ᵢ$ 7)))))
         (Vint32 (Int.or rtbl_vy' ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7)))))
     (Vint32 (v'49&ᵢInt.not ($ 1<<ᵢ(i4&ᵢ$ 7))))) tcbls_l).
    {
      assert (Hct_i4_neq: prio_neq_cur tcbls_l (ct_b, Int.zero) i4).
   { unfolds; intros.
      eapply H56; eauto.
       eapply TcbMod.join_get_l;eauto.
    }
    destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1;
    eapply Mbox_common.TCBList_P_tcb_block_hold' with (prio:= i4) (tcs:= tcbls_r); eauto.
    clear -Hct_range; split; auto. int auto.
    clear -Hct_range; split; auto. int auto.
    eapply TCBList_P_rtbl_add_simpl_version;eauto.
    clear -Hpip_range; split;auto. int auto.
    unfold nat_of_Z; eapply nth_val'2nth_val;eauto.
    clear -Hpip_non_tls Htcbjoin_whole.
    intros; eapply semacc_int_eq_false; rewrite Int.eq_sym.
    eapply Hpip_non_tls; eauto.
    eapply TcbMod.join_get_l; eauto.
    eapply Mbox_common.TCBList_P_tcb_block_hold' with (tcs:= tcbls_r); eauto.
    eapply TcbMod_join_impl_prio_neq_cur_l; eauto.
    unfolds; intros.
    eapply H56; eauto.
    unfold nat_of_Z; eapply nth_val'2nth_val;eauto.
     }

   transform_pre add_a_isr_is_prop ltac:(sep cancel Aisr;
                                        sep cancel Ais).
  transform_pre add_aemp_isr_is_prop ltac:(sep cancel Aisr;
                                        sep cancel Ais; sep cancel Aier).
  hoare forward prim.
  sep cancel Aier.
  unfold AOSMapTbl.
  sep pauto.
  sep_lifts_trms EvtInv.
  eapply fold_EvtInv_frm'; eauto.
  trycancel_EvtInv.
(*   sep_lifts_trms AECBList. *)
  eapply AECBList_fold.
  eapply lzh_evsllseg_compose; eauto.
  sep cancel AEventNode.
  2:{ unfolds; simpl; eauto. }
  sep cancel (Agvarmapsto OSEventList).
  sep cancel (evsllseg x7).
  sep cancel evsllseg.
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel (Aptrmapsto).
  sep cancel (Agvarenv').
  sep cancel (dllseg v'5).
  simpl dllseg at 1.
  sep normal. sep eexists.  sep split.
  sep cancel node.
  eapply dllseg_compose;eauto.
  eapply dllseg_compose;eauto.
  sep cancel dllseg.
  sep cancel p_local.
  instantiate (3:= ((v'34
            :: v'32
               :: x15
                  :: om
                     :: Vint32 i8
                        :: Vint32 x13
                           :: Vint32 (x3 >>ᵢ $ 8)
                              :: Vint32 ((x3 >>ᵢ $ 8)&ᵢ$ 7)
                                 :: Vint32 ((x3 >>ᵢ $ 8) >>ᵢ $ 3)
                                    :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))
                                       :: Vint32
                                            ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))
                                          :: nil) :: nil)).
  simpl dllseg at 1.
  unfold node.
  sep normal. sep eexists.  sep split; auto.
  sep cancel Astruct.
  sep cancel dllseg.
  2 : { split; eauto. go. }
  2: { auto. }
  2 : { unfolds; simpl; eauto. }
  2 : { unfolds; simpl; eauto. }
   sep_lift_context tcbdllflag.
   eapply tcbdllflag_hold; [idtac | sep cancel tcbdllflag; eauto].
   rewrite <- app_assoc.
   rewrite l2.
   eapply tcbdllflag_hold_node2'.
   unfolds; swallow; go.
   unfolds; swallow; go.
   unfold EvtInv_part2 in *.
   sep pauto.
   trycancel_EvtInv.
   eapply tcbllsegevaux_tcbvl_tcb_linked_list_same_next_preserve; eauto.
   sep cancel APthreadAttr.
   sep cancel CapabilityInv.
   cancel_corecommuinv.
   cancel_partitioninv.
   eauto.
   rewrite <- app_assoc.
   rewrite l2.
   assert (Hvll_eq: forall (vl1 vl2: vallist) (vll1 vll2 vll3: list vallist), 
                                vll1 ++ vl1 :: vll2 ++ vl2 :: vll3= vll1 ++ (vl1 :: nil) ++ (vll2 ++ (vl2 :: vll3))).
   { simpl; auto. }
   
   rewrite Hvll_eq. rewrite Hvll_eq.
   eapply tcb_linked_list_same_next_split; eauto.
   eapply tcb_linked_list_same_next_self; eauto.
   eapply tcb_linked_list_same_next_split; eauto.
   simpl; auto.
   eapply tcb_linked_list_same_next_mid; eauto.
   eauto. eauto. eauto. (* new add *)
   (* RH_PrioTbl_P *)
   eapply RH_PrioTbl_P_update_tcb; eauto.
   clear -Hpip_range. split; auto.
   apply Int.unsigned_range_2.
   clear -H56 Hget_ot.
   destruct H56 as (_ & H & _).
   eapply H in Hget_ot. simpljoin. auto.
   eapply RH_PrioTbl_P_update_vhold; eauto.
    (* R_PrioTbl_P *)
    eapply R_PrioTbl_Pend_lift';eauto.
    (* RL_RTbl_PrioTbl_P *)
     assert (Hot_neq_hold: (ot_b, Int.zero) <> vhold_addr).
     { clear -H56 Hget_ot.
          funfold H56; eapply H0 in Hget_ot.
          destruct Hget_ot; auto. }
     destruct (Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero) eqn: if_rdy_cond1.
     eapply OSTimeDlyPure.rtbl_remove_RL_RTbl_PrioTbl_P_hold with (prio:= i4); eauto.
     split; auto. clear; int auto.
     eapply RL_RTbl_PrioTbl_P_set_not_rdy; eauto.
     { (* prio_not_in_tbl opt rtbl *)
     unfold prio_not_in_tbl.
     intros x2' y z Heq1 Heq2 Hnth_new.
     subst x2'; subst y.
     eapply nth_val_nth_val'_some_eq in Hnth_new.
     unfold nat_of_Z in Hnth_new.
     rewrite Hnth_rtbl_vy in Hnth_new.
     inverts Hnth_new.
     change ($ 0) with Int.zero.
     eapply inteqeq; eauto.
     }
    {    (* case: Int.eq (rtbl_vy&ᵢ($ 1<<ᵢ(opt&ᵢ$ 7))) Int.zero = false *)
          eapply OSTimeDlyPure.rtbl_remove_RL_RTbl_PrioTbl_P_hold with (prio:= i4); eauto.
          split; auto. clear; int auto.
          eapply RL_RTbl_PrioTbl_P_set; eauto.
          rewrite update_nth_val_len_eq; auto.
          rewrite update_nth_val_len_eq; auto.
          eapply xmapis1shlx; eauto.
          eapply RL_RTbl_PrioTbl_P_set_vhold; eauto. } 
    (* array_type_vallist_match /\ length *)
    split.
    eapply array_type_vallist_match_hold; eauto.
    eapply array_type_vallist_match_hold; eauto.
    rewrite H59; clear -Hopt_range; auto with zarith.
    rewrite update_nth_val_len_eq; rewrite H59; clear -Hpip_range; auto with zarith.
    do 2 rewrite update_nth_val_len_eq; auto.
    (* TCBList_P *)
    apply Htlsp1.
    (* TCBList_P *)
    apply Htlsp2.
    rewrite neq_set_comm with (a1:= (ot_b, Int.zero)) (a2:= (ct_b, Int.zero)); eauto.
    eapply TcbMod.join_set_r; eauto.
    eapply TcbMod.join_set_r; eauto.
    unfold TcbMod.indom; eauto.
    unfold TcbMod.indom; rewrite TcbMod.map_get_set'; eauto.
     (* ECBList_P *)
     eapply ecblist_p_mutexpend_changeprio; eauto.
    rewrite TcbMod.set_sem.
    lets Hneq: tidspec.neq_beq_false Hot_neq_ct.
    eapply TaskLStMod.beq_sym in Hneq.
    rewrite Hneq; eauto.
    eapply ecblist_p_mutexpend';eauto.
    eapply evsllseg_aux with (s:= s); eauto.
    sep cancel (evsllseg v'12); eauto.
     assert (Hct_dly_eq: i6 = $ 0).
     { clear -Htcbnode_ct.
        funfold Htcbnode_ct.
        funfold H2.
        assert (Habs_eq: (i4, rdy, x14, false) = (i4, rdy, x14, false)) by auto.
        eapply H0 in Habs_eq.
        mytac.
        unfold V_OSTCBDly in H8; simpl in H8; inverts H8.
        auto.
  Optimize Proof.
  Optimize Heap.
       }
     subst i6; eauto.
   (* RH_ECBlk_EIBlk_Mux_P *)
(*     eapply RH_ECBlk_EIBlk_Mux_P_set_op;eauto. *)
(*     auto. *)
    (* RH_CurTCB *)
    unfold RH_CurTCB.
    rewrite TcbMod.set_sem.
    lets Hneq: tidspec.neq_beq_false Hot_neq_ct.
    rewrite Hneq.
    rewrite TcbMod.map_get_set; eauto.
    (* RH_TCBList_ECBList_P *)
    lets Hset_set: neq_set_comm Hot_neq_ct.
    erewrite <- Hset_set.
    eapply RH_TCBList_ECBList_P_high_block_hold_mutex'; eauto.
    eapply RH_TCBList_ECBList_P_pend_changeprio'; eauto.
    clear -H56. funfold H56; auto.
    rewrite TcbMod.set_sem.
    lets Hneq: tidspec.neq_beq_false Hot_neq_ct.
    rewrite Hneq. auto.
   (* end of RH_TCBList_ECBList_P *)
    eauto.
    
    pure_auto.
   (* end of EXIT CRITICAL *)
   (* needs partproof lemma *)
   simpl nth_val. (* new add *)
   eapply backward_rule1;
   [idtac | eapply OSMutexPendPart_proof with (vt := vt); eauto].
   introv Hsat; sep cancel Aier; sep pauto.

  (* case2.2 : mutex owner is right to curp, owner's priority no change *)
  hoare unfold.
  assert (Hno_lift_cond: ~(Int.eq opt (x3 >>ᵢ $ 8) = false 
                                                       /\ Int.ltu i4 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true)).
  { destruct (Int.eq opt (x3 >>ᵢ $ 8)) eqn: eq2;
     destruct (Int.ltu i4 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) eqn: eq3;
  simpl in H60;
  try change (Int.notbool Int.one) with Int.zero in H60;
  try change (Int.notbool Int.zero) with Int.one in H60;
  try change (Int.ltu Int.zero Int.one) with true in H60;
  try change (Int.ltu Int.zero Int.zero) with false in H60;
  simpl in H60; destruct H60; tryfalse; clear; mauto. }
 clear H60.
  (* OSTCBCur ′ → OSTCBStat =ₑ OSTCBCur ′ → OSTCBStat |ₑ ′ OS_STAT_MUTEX;ₛ  *)
  hoare forward.
  go.
  rewrite Hor.
  (* OSTCBCur ′ → OSTCBDly =ₑ os_code_defs.timeout ′;ₛ *)
  hoare forward.
  clear -Hvt_range; pauto.
  (* OS_EventTaskWait (­ pevent ′­);ₛ *)
   hoare_lifts_trms_pre (Aisr, Ais, A_isr_is_prop, aemp_isr_is).
  transform_pre a_isr_is_prop_split ltac:(idtac).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  hoare_split_pure_all.

  hoare unfold.
  hoare forward.

  unfold node.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  sep pauto.
  instantiate (9:= ct_b).
  sep cancel (Astruct (ct_b,Int.zero)).
  sep cancel p_local. (* new add *)
  instantiate  (2:= (DMutex (Vint32 x3) (Vptr (ot_b, Int.zero)))).
  unfold AEventNode.
  sep cancel AEventData.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Aarray.
  sep cancel AOSPostEventTbl.
  instantiate (2:= mid_b).
  sep cancel (Astruct (mid_b, Int.zero)).
  eauto.
  eauto.
  unfolds; simpl; eauto.
  eauto.
  eauto.
  unfolds; simpl; auto.
  eauto.
  auto.
  split; auto. go.
  eapply mund_int_a2; auto.
  split; auto. go.
  split; simpl; auto.
  eexists; split; try (unfold V_OSTCBPrio; simpl nth_val); try eapply Int.eq_false; eauto. 
  { clear -Htcb_rl; unfolds; unfolds in Htcb_rl.
     mytac.
     do 6 eexists; splits; try (unfolds; simpl; eauto).
     split;auto.
     splits; auto.
     pauto.
     eexists; split.
     unfolds; simpl; eauto.
     introv Hf; destruct Hf as [Hf | Hf]; tryfalse. }
  pure_auto.

  intros. sep pauto. sep cancel p_local. simpl; auto.
  intros. sep pauto. sep cancel p_local. simpl; auto.
  (* OS_EventTaskWaitPost *)
  hoare_ex_intro.
  unfold OS_EventTaskWaitPost.
  unfold OS_EventTaskWaitPost'.
  unfold getasrt.
  hoare_split_pure_all.
  inverts H60.
  unfold V_OSTCBY,V_OSTCBBitX,V_OSTCBBitY,V_OSEventGrp in H67.
  simpl in H66,H67.
  mytac_H.
  inverts H66; inverts H67; inverts H68; inverts H69; inverts H76.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, absecblist,abstcblist,ostm,oscurt,EvtInv_part2).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexpend_absimp_block_no_lift'; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  (* EXIT_CRITICAL;ₛ *)
  hoare_assert_pure ( get_last_tcb_ptr v'7 v'5 = Some (Vptr (ct_b, Int.zero)) ).
   { get_hsat Hsat.
     sep_lifts_trms_in Hsat (dllseg v'5).
     eapply tcbdllseg_get_last_tcb_ptr; eauto.
   }
  apply pure_split_rule'; introv Hget_last_ct.
   transform_pre add_a_isr_is_prop ltac:(sep cancel Aisr;
                                        sep cancel Ais).
   transform_pre add_aemp_isr_is_prop ltac:(sep cancel Aisr;
                                        sep cancel Ais; sep cancel Aier).
  hoare forward prim.
  sep cancel Aier.
  sep_lifts_trms EvtInv.
  eapply fold_EvtInv_frm'; eauto.
  trycancel_EvtInv.
  eapply AECBList_fold.
  eapply lzh_evsllseg_compose; eauto.
  sep cancel AEventNode.
  2:{ unfolds; simpl; eauto. }
  sep cancel (Agvarmapsto OSEventList).
  sep cancel (evsllseg x7).
  sep cancel evsllseg.
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel (Aptrmapsto).
  sep cancel (Agvarenv').
  sep cancel (dllseg v'5).
  simpl dllseg at 1.
  sep normal. sep eexists.  sep split.
  sep cancel node.
  eapply dllseg_compose;eauto.
  eapply dllseg_compose;eauto.
  sep cancel dllseg.
  sep cancel p_local.
  instantiate (3:= ((v'34
            :: v'32
               :: x15
                  :: om
                     :: Vint32 i8
                        :: Vint32 x13
                           :: Vint32 opt
                              :: Vint32 (opt&ᵢ$ 7)
                                 :: Vint32 (opt >>ᵢ $ 3)
                                    :: Vint32 ($ 1<<ᵢ(opt&ᵢ$ 7))
                                       :: Vint32
                                            ($ 1<<ᵢ(opt >>ᵢ $ 3))
                                          :: nil) :: nil)).
  simpl dllseg at 1.
  unfold node.
  sep normal. sep eexists.  sep split; auto.
  sep cancel Astruct.
  sep cancel dllseg.
  2 : { split; eauto. go. }
  2: { auto. }
  2 : { unfolds; simpl; eauto. }
  2 : { unfolds; simpl; eauto. }
   sep_lift_context tcbdllflag.
   eapply tcbdllflag_hold; [idtac | sep cancel tcbdllflag; eauto].
   rewrite <- app_assoc.
   rewrite l2.
    eapply tcbdllflag_hold_node2'.
    unfolds; swallow; go.
    unfolds; swallow; go.
    eapply evtinv_part2_set_tcbvl_mid_preserve.
    2: { rewrite <- app_assoc. rewrite l2.
            sep cancel EvtInv_part2.  sep cancel APthreadAttr. cancel_corecommuinv. sep cancel CapabilityInv. 
            cancel_partitioninv. eauto. }
    { rewrite <- app_assoc. rewrite l2.
      eapply TCBList_P_Combine.
      3: { apply Htcblist_subl. }
      2: { eauto.  }
      2: {  simpl TCBList_P.
                  unfold V_OSTCBNext. simpl nth_val.
                  do 3 eexists; exists (i4,rdy,x14, false); splits; eauto.
                  apply Htcbjoin_right.  }
            auto.
  Optimize Proof.
  Optimize Heap.
    }
     (* RH_PrioTbl_P *)
    auto.
    (* R_PrioTbl_P *)
    eapply Mbox_common.TcbMod_set_R_PrioTbl_P_hold;eauto.
   (* RL_RTbl_PrioTbl_P *)
    eapply OSTimeDlyPure.rtbl_remove_RL_RTbl_PrioTbl_P_hold with (prio:= i4);eauto.
    clear -Hct_range; split; auto. int auto.
   (* TCBList_P *)
   rewrite <- app_assoc. rewrite l2.
    assert (Hct_i4_neq: prio_neq_cur tcbls_r (ct_b, Int.zero) i4).
   { eapply TcbMod_join_impl_prio_neq_cur_r; eauto.
    clear -H56 Hget_ct.
    unfolds; intros; eapply H56; eauto. }
      instantiate (1:= TcbMod.set tcbls_r (ct_b, Int.zero)
                                             (i4, wait (os_stat_mutexsem (mid_b, Int.zero))
                                                   (if Int.eq vt Int.zero then None else (Some vt)), x14, false)).
    destruct (Int.eq vt Int.zero) eqn: Heq_t.
    eapply semacc_int_eq_true in Heq_t. subst vt.
    eapply TCBList_P_tcb_block_hold_mutex'_none; eauto.
    simpl TCBList_P.
    unfold V_OSTCBNext. simpl nth_val.
    do 3 eexists; exists (i4,rdy,x14, false); splits; eauto.
    apply Htcbjoin_right.
    eapply semacc_int_eq_false in Heq_t.
    eapply TCBList_P_tcb_block_hold_mutex'; eauto.
    simpl TCBList_P.
    unfold V_OSTCBNext. simpl nth_val.
    do 3 eexists; exists (i4,rdy,x14, false); splits; eauto.
    apply Htcbjoin_right.
    (* TCBList_P *)
    instantiate (1:= tcbls_l).
    eapply Mbox_common.TCBList_P_tcb_block_hold' with (prio:= i4) (tcs:= tcbls_r); eauto.
    clear -Hct_range; split; auto. int auto.
    eapply TcbMod_join_impl_prio_neq_cur_l; eauto.
    unfolds; intros.
    eapply H56; eauto.
    eapply TcbMod.join_set_r; eauto.
    unfold TcbMod.indom; eauto.
    (* ECBList_P *)
    eapply ecblist_p_mutexpend';eauto.
    eapply evsllseg_aux with (s:= s); eauto.
    sep cancel (evsllseg v'12); eauto.
     assert (Hct_dly_eq: i6 = $ 0).
     { clear -Htcbnode_ct.
        funfold Htcbnode_ct.
        funfold H2.
        assert (Habs_eq: (i4, rdy, x14,false) = (i4, rdy, x14, false)) by auto.
        eapply H0 in Habs_eq.
        mytac.
        unfold V_OSTCBDly in H8; simpl in H8; inverts H8.
        auto.
       }
     subst i6; eauto.
   (* RH_ECBlk_EIBlk_Mux_P *)
(*     eapply RH_ECBlk_EIBlk_Mux_P_set_op;eauto. *)
(*     auto. *)
    (* RH_CurTCB *)
    unfold RH_CurTCB.
    rewrite TcbMod.map_get_set; eauto.
    (* RH_TCBList_ECBList_P *)
    eapply RH_TCBList_ECBList_P_high_block_hold_mutex'; eauto.

    pure_auto.
   (* end of EXIT CRITICAL *)
   (* needs partproof lemma *)
   simpl nth_val.
   eapply backward_rule1;
   [idtac | eapply OSMutexPendPart_proof with (vt := vt); eauto].
   introv Hsat; sep cancel Aier; sep pauto.
    (* end of case4 *)
Qed.



Require Import ucos_include.
Require Import os_code_defs.
Require Import os_ucos_h.
Require Import code_notations.
Require Import sep_lemmas_ext.
Require Import linv_solver.

Require Import protect.
Require Import Lia.

Require Import abs_infer_abt. 

Require Import inline_definitions.
Require Import inline_bittblfunctions.
Require Import inline_tactics.
Require Import symbolic_lemmas.
Require Import new_inv.
Require Import protect.
Require Import Lia.


Require Import List.
Require Import ifun_spec.
Require Import os_program.
Require Import os_task.


Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.


Fixpoint spec_code_cons (s1:spec_code) (s2:spec_code) :=
  match s1 with
  | sp1 ?? sp2 => (spec_code_cons sp1 s2) ?? (spec_code_cons sp2 s2)
  | sp1 ;; sp2 => sp1 ;; (spec_code_cons sp2 s2)
  | _ => s1 ;; s2
  end.

(* suspend *)

Definition tasksuspend_err_prio_is_idle (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_SUSPEND_IDLE))) /\
      (exists v3 v',
        vl = ((Vint32 v3)::v'::nil) /\
        (Int.eq (Int.repr OS_IDLE_PRIO) v3 = true) /\
        (v' = (Vint32 (Int.repr OS_TASK_SUSPEND_IDLE)) /\ O_opt= Some O1 \/
         v' <> (Vint32 (Int.repr OS_TASK_SUSPEND_IDLE)) /\ O_opt = None)
      )
  end.

Definition tasksuspend_err_prio_invalid (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr OS_PRIO_INVALID))) /\
      (exists v3 v',
        vl = ((Vint32 v3)::v'::nil) /\
        Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true /\
        (v' = (Vint32 (Int.repr OS_PRIO_INVALID)) /\ O_opt= Some O1 \/
         v' <> (Vint32 (Int.repr OS_PRIO_INVALID)) /\ O_opt = None)
      )
  end.

Definition tasksuspend_err_no_such_tcb (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_SUSPEND_PRIO))) /\
      (exists v3 v',
      vl = ((Vint32 v3)::v'::nil) /\
        (exists tls,
          (* get O1 abstcblsid = Some (abstcblist tls) /\ *)
          (~ exists tid st msg sus, TcbMod.get tls tid = Some (v3, st, msg, sus))
        ) /\
        (v' = (Vint32 (Int.repr OS_TASK_SUSPEND_PRIO)) /\ O_opt= Some O1 \/
         v' <> (Vint32 (Int.repr OS_TASK_SUSPEND_PRIO)) /\ O_opt = None)
      )
  end.

(* Definition OS_TASK_DELAY_ZERO := 102%Z. *)

(* Definition tasksuspend_err_delay_is_zero (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_DELAY_ZERO))) /\
      (exists v3 v',
      vl = ((Vint32 v3)::v'::nil) /\
        (exists tls tid st msg sus eid,
          TcbMod.get tls tid = Some (v3, st, msg, sus) /\
          (( st = wait (os_stat_sem eid) None)\/ ( st =wait (os_stat_q eid) None) \/
          ( st =wait (os_stat_mbox eid) None) \/ ( st =wait (os_stat_mutexsem eid) None) \/
          (st =  wait (os_stat_postq eid) None) \/
            ( st = wait (os_stat_sem eid) (Some Int.zero))\/ ( st =wait (os_stat_q eid) (Some Int.zero)) \/
          ( st =wait (os_stat_mbox eid) (Some Int.zero)) \/ ( st =wait (os_stat_mutexsem eid) (Some Int.zero)))
        ) /\
        (v' = (Vint32 (Int.repr OS_TASK_DELAY_ZERO)) /\ O_opt= Some O1 \/
         v' <> (Vint32 (Int.repr OS_TASK_DELAY_ZERO)) /\ O_opt = None)
      )
  end. *)

  Definition tasksuspend_err_delay_is_zero (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_DELAY_ZERO))) /\
      (exists v3 v',
      vl = ((Vint32 v3)::v'::nil) /\
        (* (exists tls tid st msg sus eid,
          TcbMod.get tls tid = Some (v3, st, msg, sus) /\
          (( st = wait (os_stat_sem eid) None)\/ ( st =wait (os_stat_q eid) None) \/
          ( st =wait (os_stat_mbox eid) None) \/ ( st =wait (os_stat_mutexsem eid) None) \/
          (st =  wait (os_stat_postq eid) None) \/
            ( st = wait (os_stat_sem eid) (Some Int.zero))\/ ( st =wait (os_stat_q eid) (Some Int.zero)) \/
          ( st =wait (os_stat_mbox eid) (Some Int.zero)) \/ ( st =wait (os_stat_mutexsem eid) (Some Int.zero)))
        ) /\ *)
        (v' = (Vint32 (Int.repr OS_TASK_DELAY_ZERO)) /\ O_opt= Some O1 \/
         v' <> (Vint32 (Int.repr OS_TASK_DELAY_ZERO)) /\ O_opt = None)
      )
  end.

Definition tasksuspend_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists v3 v',
      vl = ((Vint32 v3)::v'::nil) /\
        ( opv = None /\
          exists tls tid st msg sus tls',
          (* get O1 abstcblsid = Some (abstcblist tls) /\ *)
            TcbMod.get tls tid = Some (v3, st, msg, sus) /\
            tls' = set tls tid (v3, st, msg, true) /\
            O_opt = Some(set O1 abstcblsid (abstcblist tls'))           
        )      
  end.
(*
  Definition tasksuspend_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists v3 v',
      vl = ((Vint32 v3)::v'::nil) /\
        (exists tls,
          get O1 abstcblsid = Some (abstcblist tls) /\
          (exists tid st msg sus,
            TcbMod.get tls tid = Some (v3, st, msg, sus) /\
            O_opt = Some(set O1 abstcblsid (abstcblist (TcbMod.set tls tid (v3, st, msg, true))))
          ) 
        )      
  end.
*)
Definition tasksuspend_ret (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
  | (opv, O_opt) =>
  exists v',
  vl = (v'::nil) /\
      (
        opv = Some (Vint32 (Int.repr OS_NO_ERR)) /\
         ( v' = (Vint32 (Int.repr OS_NO_ERR)) /\ O_opt=Some O1
            \/ v' <> (Vint32 (Int.repr OS_NO_ERR)) /\ O_opt = None))
             
end.
(*
Definition tasksuspend_ret (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
  | (opv, O_opt) =>
  exists v',
  vl = (v'::nil) /\
      (
        opv = Some (Vint32 (Int.repr OS_NO_ERR)) /\
         ( v' = (Vint32 (Int.repr OS_NO_ERR)) /\ O_opt=Some O1
            \/ v' <> (Vint32 (Int.repr OS_NO_ERR)) /\ O_opt = None))
             
end.
*)

Definition ssus (vl : vallist) :=
  match vl with
    | (Vint32 v3) :: v' :: nil => isched ;; tasksuspend_ret (|v'::nil|)
    | _ => spec_done None
  end.


Definition tasksuspendcode (vl: vallist) :=
  ASSERT (fun O => length vl =2%nat) ;; 
  (
  tasksuspend_err_prio_is_idle (|vl|) ??
  tasksuspend_err_prio_invalid (|vl|) ??
  tasksuspend_err_no_such_tcb (|vl|) ??
  tasksuspend_err_delay_is_zero (|vl|) ?? 
  (* (tasksuspend_succ (|vl|) ;; ssus (vl)) *)
  (tasksuspend_succ (|vl|) ;; ssus (vl))
  ).

Lemma absimp_tasksus_prio_idle':
  forall P v1 v' sch s,
    v' = Vint32 (Int.repr OS_TASK_SUSPEND_IDLE) ->
    can_change_aop P ->
    Int.eq (Int.repr OS_IDLE_PRIO) v1 = true ->
    absinfer sch ( <||spec_code_cons (tasksuspendcode ((Vint32 v1) :: v' :: nil)) s ||> ** P)
             ( <|| s ||> ** P).
Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq; try(eauto).
  eapply absinfer_assert_cont; try(eauto).
  eapply absinfer_trans.
  eapply absinfer_seq_end; try (eauto).
  infer_solver 0%nat.
Qed.

Lemma absimp_tasksus_prio_idle_abt':
  forall P v1 v' sch s,
    v' <> Vint32 (Int.repr OS_TASK_SUSPEND_IDLE) ->
    can_change_aop P ->
    Int.eq (Int.repr OS_IDLE_PRIO) v1 = true ->
    absinfer sch ( <||spec_code_cons (tasksuspendcode ((Vint32 v1) :: v' :: nil)) s ||> ** P)
             ( <|| ABORT ||> ** P).
Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq; try eauto.
  eapply absinfer_assert_cont; try(eauto).
  eapply absinfer_trans.
  eapply absinfer_seq_end; try (eauto).
  eapply absinfer_trans.
  eapply absinfer_choice1; try eauto.
  eapply absinfer_trans.
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  unfolds; intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.  
  unfolds.
  split. eauto.
  exists v1 v'.
  subst.
  splits; eauto.
  apply map_join_emp.
  repeat hmstep_call_consturctor.
  simpl in *.
  simpljoin.
  do 6 eexists.
  splits ; try eauto.
  eapply change_aop_rule; eauto.
  eapply absinfer_seq_abt; try eauto.
Qed.


Lemma absimp_tasksus_prio_invalid':
  forall P v1 v' sch s,
    v' = Vint32 (Int.repr OS_PRIO_INVALID) ->
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v1 = true ->
    absinfer sch ( <||spec_code_cons (tasksuspendcode ((Vint32 v1) :: v' :: nil)) s ||> ** P)
             ( <|| s ||> ** P).
Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq; try(eauto).
  eapply absinfer_assert_cont; try(eauto).
  eapply absinfer_trans.
  eapply absinfer_seq_end; try (eauto).
  infer_solver 1%nat.
Qed.

Lemma absimp_tasksus_prio_invalid_abt':
  forall P v1 v' sch s,
    v' <> Vint32 (Int.repr OS_PRIO_INVALID) ->
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v1 = true ->
    absinfer sch ( <||spec_code_cons (tasksuspendcode ((Vint32 v1) :: v' :: nil)) s ||> ** P)
             ( <|| ABORT ||> ** P).
Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq; try eauto.
  eapply absinfer_assert_cont; try(eauto).
  eapply absinfer_trans.
  eapply absinfer_seq_end; try (eauto).
  eapply absinfer_trans.
  eapply absinfer_choice2; try eauto.
  eapply absinfer_trans.
  eapply absinfer_choice1; try eauto.
  eapply absinfer_trans.
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  unfolds; intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.  
  unfolds.
  split. eauto.
  exists v1 v'.
  subst.
  splits; eauto.
  apply map_join_emp.
  repeat hmstep_call_consturctor.
  simpl in *.
  simpljoin.
  do 6 eexists.
  splits ; try eauto.
  eapply change_aop_rule; eauto.
  eapply absinfer_seq_abt; try eauto.
Qed.

Lemma absimp_tasksus_no_such_tcb':
  forall P v1 v' sch  (tcbls : TcbMod.map) s,
    v' = Vint32 (Int.repr OS_TASK_SUSPEND_PRIO) ->
    can_change_aop P ->
    (~exists tid st msg sus, TcbMod.get tcbls tid = Some (v1, st, msg, sus)) ->
    absinfer sch ( <||spec_code_cons (tasksuspendcode ((Vint32 v1) :: v' :: nil)) s ||> **
                       HTCBList tcbls ** P)
             ( <|| s ||> **
                       HTCBList tcbls ** P).
Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq. 
  can_change_aop_solver.
  instantiate(1 := HTCBList tcbls ** P).
  can_change_aop_solver.
  eapply absinfer_assert_cont; try(eauto).
  can_change_aop_solver.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_seq_end.
  3: eauto.
  can_change_aop_solver.  
  can_change_aop_solver.
  infer_solver 2%nat.
Qed.

Lemma absimp_tasksus_no_such_tcb_abt':
  forall P v1 v' sch  (tcbls : TcbMod.map) s,
    v' <> Vint32 (Int.repr OS_TASK_SUSPEND_PRIO) ->
    can_change_aop P ->
    (~exists tid st msg sus, TcbMod.get tcbls tid = Some (v1, st, msg, sus)) ->
    absinfer sch ( <||spec_code_cons (tasksuspendcode ((Vint32 v1) :: v' :: nil)) s ||> **
                       HTCBList tcbls ** P)
             ( <|| ABORT ||> **
                       HTCBList tcbls ** P).
Proof.
intros.
simpls.
eapply absinfer_trans.
eapply absinfer_seq.
can_change_aop_solver.
instantiate(1 := HTCBList tcbls ** P).
can_change_aop_solver.
eapply absinfer_assert_cont; try(eauto).
can_change_aop_solver.
can_change_aop_solver.

eapply absinfer_trans.
eapply absinfer_seq_end.
can_change_aop_solver.
2: eauto.
can_change_aop_solver.

eapply absinfer_trans.
eapply absinfer_choice2.
can_change_aop_solver.
2: eauto.
can_change_aop_solver.

eapply absinfer_trans.
eapply absinfer_choice2.
can_change_aop_solver.
2: eauto.
can_change_aop_solver.

eapply absinfer_trans.
eapply absinfer_choice1.
can_change_aop_solver.
2: eauto.
can_change_aop_solver.

eapply absinfer_trans.
eapply absinfer_seq.
can_change_aop_solver. 
2: eapply absinfer_abt.
instantiate(1 := HTCBList tcbls ** P).
can_change_aop_solver.
can_change_aop_solver.
can_change_aop_solver.

unfolds; intros.
eexists;exgamma.
splits.
simpl_subst_gamma.
hmstep_call_consturctor.
eapply spec_prim_step_abt.  
unfolds.
split. eauto.
exists v1 v'.

splits. 
auto.
exists tcbls.
auto.
auto.

apply map_join_emp.

repeat hmstep_call_consturctor.
simpl in *.
simpljoin.
do 6 eexists.
splits ; try eauto.
do 6 eexists.
splits ; try eauto.

eapply change_aop_rule; eauto.
eapply absinfer_seq_abt; try eauto.
can_change_aop_solver.
can_change_aop_solver.
Qed.


(* Lemma absimp_tasksus_delay_is_zero':
  forall P v1 v' sch  (tcbls : TcbMod.map) s,
    v' = Vint32 (Int.repr OS_TASK_DELAY_ZERO) ->
    can_change_aop P ->
    (exists tls tid st msg sus eid,
    TcbMod.get tls tid = Some (v1, st, msg, sus) /\
    (( st = wait (os_stat_sem eid) None)\/ ( st =wait (os_stat_q eid) None) \/
    ( st =wait (os_stat_mbox eid) None) \/ ( st =wait (os_stat_mutexsem eid) None) \/
    (st =  wait (os_stat_postq eid) None) \/
      ( st = wait (os_stat_sem eid) (Some Int.zero))\/ ( st =wait (os_stat_q eid) (Some Int.zero)) \/
    ( st =wait (os_stat_mbox eid) (Some Int.zero)) \/ ( st =wait (os_stat_mutexsem eid) (Some Int.zero)))) ->
    absinfer sch ( <||spec_code_cons (tasksuspendcode ((Vint32 v1) :: v' :: nil)) s ||> **
                       HTCBList tcbls ** P)
             ( <|| s ||> **
                       HTCBList tcbls ** P).
Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq. 
  can_change_aop_solver.
  instantiate(1 := HTCBList tcbls ** P).
  can_change_aop_solver.
  eapply absinfer_assert_cont; try(eauto).
  can_change_aop_solver.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_seq_end.
  3: eauto.
  can_change_aop_solver.  
  can_change_aop_solver.
  infer_solver 3%nat.
Qed. *)

Lemma absimp_tasksus_delay_is_zero':
  forall P v1 v' sch  (tcbls : TcbMod.map) s,
    v' = Vint32 (Int.repr OS_TASK_DELAY_ZERO) ->
    can_change_aop P ->
    (* (exists tls tid st msg sus eid,
    TcbMod.get tls tid = Some (v1, st, msg, sus) /\
    (( st = wait (os_stat_sem eid) None)\/ ( st =wait (os_stat_q eid) None) \/
    ( st =wait (os_stat_mbox eid) None) \/ ( st =wait (os_stat_mutexsem eid) None) \/
    (st =  wait (os_stat_postq eid) None) \/
      ( st = wait (os_stat_sem eid) (Some Int.zero))\/ ( st =wait (os_stat_q eid) (Some Int.zero)) \/
    ( st =wait (os_stat_mbox eid) (Some Int.zero)) \/ ( st =wait (os_stat_mutexsem eid) (Some Int.zero)))) -> *)
    absinfer sch ( <||spec_code_cons (tasksuspendcode ((Vint32 v1) :: v' :: nil)) s ||> **
                       HTCBList tcbls ** P)
             ( <|| s ||> **
                       HTCBList tcbls ** P).
Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq. 
  can_change_aop_solver.
  instantiate(1 := HTCBList tcbls ** P).
  can_change_aop_solver.
  eapply absinfer_assert_cont; try(eauto).
  can_change_aop_solver.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_seq_end.
  3: eauto.
  can_change_aop_solver.  
  can_change_aop_solver.
  infer_solver 3%nat.
Qed.

(* Lemma absimp_tasksus_delay_is_zero_abt':
  forall P v1 v' sch  (tcbls : TcbMod.map) s,
    v' <> Vint32 (Int.repr OS_TASK_DELAY_ZERO) ->
    can_change_aop P ->
    (exists tls tid st msg sus eid,
    TcbMod.get tls tid = Some (v1, st, msg, sus) /\
    (( st = wait (os_stat_sem eid) (Some Int.zero))\/ ( st =wait (os_stat_q eid) (Some Int.zero)) \/
    ( st =wait (os_stat_mbox eid) (Some Int.zero)) \/ ( st =wait (os_stat_mutexsem eid) (Some Int.zero)))) ->
    absinfer sch ( <||spec_code_cons (tasksuspendcode ((Vint32 v1) :: v' :: nil)) s ||> **
                       HTCBList tcbls ** P)
             ( <|| ABORT ||> **
                       HTCBList tcbls ** P).
Proof.
intros.
simpls.
eapply absinfer_trans.
eapply absinfer_seq.
can_change_aop_solver.
instantiate(1 := HTCBList tcbls ** P).
can_change_aop_solver.
eapply absinfer_assert_cont; try(eauto).
can_change_aop_solver.
can_change_aop_solver.

eapply absinfer_trans.
eapply absinfer_seq_end.
can_change_aop_solver.
2: eauto.
can_change_aop_solver.

eapply absinfer_trans.
eapply absinfer_choice2.
can_change_aop_solver.
2: eauto.
can_change_aop_solver.

eapply absinfer_trans.
eapply absinfer_choice2.
can_change_aop_solver.
2: eauto.
can_change_aop_solver.

eapply absinfer_trans.
eapply absinfer_choice2.
can_change_aop_solver.
2: eauto.
can_change_aop_solver.

eapply absinfer_trans.
eapply absinfer_choice1.
can_change_aop_solver.
2: eauto.
can_change_aop_solver.

eapply absinfer_trans.
eapply absinfer_seq.
can_change_aop_solver. 
2: eapply absinfer_abt.
instantiate(1 := HTCBList tcbls ** P).
can_change_aop_solver.
can_change_aop_solver.
can_change_aop_solver.

unfolds; intros.
eexists;exgamma.
splits.
simpl_subst_gamma.
hmstep_call_consturctor.
eapply spec_prim_step_abt.  
unfolds.
split. eauto.
exists v1 v'.

splits. 
auto.
do 6 destruct H1.
exists x x0 x1 x2 x3 x4.
auto.
auto.

apply map_join_emp.

repeat hmstep_call_consturctor.
simpl in *.
simpljoin.
do 6 eexists.
splits ; try eauto.
do 6 eexists.
splits ; try eauto.

eapply change_aop_rule; eauto.
eapply absinfer_seq_abt; try eauto.
can_change_aop_solver.
can_change_aop_solver.
Qed. *)

Lemma absimp_tasksus_delay_is_zero_abt':
  forall P v1 v' sch  (tcbls : TcbMod.map) s,
    v' <> Vint32 (Int.repr OS_TASK_DELAY_ZERO) ->
    can_change_aop P ->
    (* (exists tls tid st msg sus eid,
    TcbMod.get tls tid = Some (v1, st, msg, sus) /\
    (( st = wait (os_stat_sem eid) (Some Int.zero))\/ ( st =wait (os_stat_q eid) (Some Int.zero)) \/
    ( st =wait (os_stat_mbox eid) (Some Int.zero)) \/ ( st =wait (os_stat_mutexsem eid) (Some Int.zero)))) -> *)
    absinfer sch ( <||spec_code_cons (tasksuspendcode ((Vint32 v1) :: v' :: nil)) s ||> **
                       HTCBList tcbls ** P)
             ( <|| ABORT ||> **
                       HTCBList tcbls ** P).
Proof.
intros.
simpls.
eapply absinfer_trans.
eapply absinfer_seq.
can_change_aop_solver.
instantiate(1 := HTCBList tcbls ** P).
can_change_aop_solver.
eapply absinfer_assert_cont; try(eauto).
can_change_aop_solver.
can_change_aop_solver.

eapply absinfer_trans.
eapply absinfer_seq_end.
can_change_aop_solver.
2: eauto.
can_change_aop_solver.

eapply absinfer_trans.
eapply absinfer_choice2.
can_change_aop_solver.
2: eauto.
can_change_aop_solver.

eapply absinfer_trans.
eapply absinfer_choice2.
can_change_aop_solver.
2: eauto.
can_change_aop_solver.

eapply absinfer_trans.
eapply absinfer_choice2.
can_change_aop_solver.
2: eauto.
can_change_aop_solver.

eapply absinfer_trans.
eapply absinfer_choice1.
can_change_aop_solver.
2: eauto.
can_change_aop_solver.

eapply absinfer_trans.
eapply absinfer_seq.
can_change_aop_solver. 
2: eapply absinfer_abt.
instantiate(1 := HTCBList tcbls ** P).
can_change_aop_solver.
can_change_aop_solver.
can_change_aop_solver.

unfolds; intros.
eexists;exgamma.
splits.
simpl_subst_gamma.
hmstep_call_consturctor.
eapply spec_prim_step_abt.  
unfolds.
split. eauto.
exists v1 v'.

splits. 
auto.
(* do 6 destruct H1.
exists x x0 x1 x2 x3 x4. *)
auto.
(* auto. *)

apply map_join_emp.

repeat hmstep_call_consturctor.
simpl in *.
simpljoin.
do 6 eexists.
splits ; try eauto.
do 6 eexists.
splits ; try eauto.

eapply change_aop_rule; eauto.
eapply absinfer_seq_abt; try eauto.
can_change_aop_solver.
can_change_aop_solver.
Qed.

Lemma absimp_tasksus_succ':
  forall P v1 v' sch  (tcbls : TcbMod.map) s,
  can_change_aop P ->
    absinfer sch ( <||spec_code_cons (tasksuspendcode ((Vint32 v1) :: v' :: nil)) s ||> **
    HTCBList tcbls ** P)
             ( <||spec_code_cons (tasksuspend_succ(|(Vint32 v1) :: v' :: nil|) ;; ssus ((Vint32 v1) :: v' :: nil)) s ||> ** HTCBList tcbls ** P).
 Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq. 
  can_change_aop_solver.
  instantiate(1 := HTCBList tcbls ** P).
  can_change_aop_solver.
  eapply absinfer_assert_cont; try(eauto).
  can_change_aop_solver.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_seq_end.
  3: eauto.
  can_change_aop_solver.  
  can_change_aop_solver.
  infer_branch 4%nat.
  apply absinfer_eq.
Qed.

Lemma abs_imp_tasksus_rdy':
  forall P v1 v' sch (tcbls : TcbMod.map) tid st msg sus s,
    can_change_aop P ->
    TcbMod.get tcbls tid = Some (v1, st, msg, sus) ->
    absinfer sch ( <||spec_code_cons (tasksuspend_succ(|(Vint32 v1) :: v' :: nil|) ;; isched ;; tasksuspend_ret (|v' :: nil|)) s ||> ** HTCBList tcbls ** P)
( <||spec_code_cons (isched ;; tasksuspend_ret (|v' :: nil|)) s ||> ** HTCBList (set tcbls tid (v1, st, msg, true)) ** P).
Proof.
  intros.
  simpls.
  add_END_if_ness.
  multi_step_handler.
  infer_part2.
Qed.

Lemma absimp_tasksuspend_ret:
  forall P v' sch s ,
    v' = Vint32 (Int.repr OS_NO_ERR) ->    
    can_change_aop P ->
    absinfer sch ( <|| tasksuspend_ret (|v' :: nil|) ;; s ||> ** P)
             (<|| s ||> **  P).
Proof. 
  intros.
  infer_solver 0%nat.
Qed.


Lemma absimp_tasksuspend_ret_abt:
  forall P v' sch s,
    can_change_aop P ->
    v' <> Vint32 (Int.repr OS_NO_ERR) ->
    absinfer sch ( <|| tasksuspend_ret (|v' :: nil|);; s ||> ** P)
      ( <|| ABORT ||> ** P).
Proof.
intros.
eapply absinfer_trans.
eapply absinfer_seq; try(eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
eapply absinfer_seq_abt; try eauto.
Qed.


Lemma OSTCBflag_des:
    forall v'11,
      struct_type_vallist_match OS_TCB_flag v'11 ->
      exists a1 a2 a3 a4 a5 a6 a7 a8 a9 a10,
        exists a11,
        v'11 = (a1::a2::a3::a4::a5::a6::Vint32 a7::a8::a9::a10::a11::nil).
  Proof.
    intros.
    destruct v'11; simpl in H; tryfalse.
    destruct v'11; simpl in H; simpljoin; tryfalse.
    destruct v'11; simpl in H; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v'11; simpl in *; simpljoin; tryfalse.
    destruct v5; tryfalse.
    repeat tri_exists_and_solver1.
  Qed. 
  

Definition OSTaskSuspendPre' (vl:vallist) (logicl:list logicvar) ct :=
  EX s v' er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v' :: logic_code s :: nil |] ** <|| spec_code_cons (tasksuspendcode (vl++(v' ::nil))) s ||> **  
       p_local OSLInv ct init_lg). 


  
Theorem OSTaskSuspendPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSTaskSuspendPre' vl ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSTaskSuspendPre : fpre :=
  fun vl ll ct => mkfunasrt (OSTaskSuspendPreGood vl ll ct).

Definition OSTaskSuspendPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v' k er, 
  (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
     [| logicl = logic_val v' :: logic_code s :: nil |] **
     [| v = Some v' /\ v' = Vint32 k  /\ 
        Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k) (Byte.max_unsigned) |] ** 
   <|| s ||> ** p_local OSLInv ct init_lg). 

Theorem OSTaskSuspendPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSTaskSuspendPost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSTaskSuspendPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSTaskSuspendPostGood vl v ll ct).



Definition OSTaskSuspend_spec : fspec:= (OSTaskSuspendPre,OSTaskSuspendPost,(Tint8, Tint8::nil)).

Definition new_osq_spec_list := 
  (((OSTaskSuspend, OSTaskSuspend_spec) :: nil) ++ osq_spec_list).

Definition new_OS_spec :=  convert_spec new_osq_spec_list.


Definition new_internal_fun_list := 
  ((OSTaskSuspend_impl :: nil) ++ internal_fun_list) %list.


Definition new_os_internal :=  convert_cfuns new_internal_fun_list.

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
Require Import ifun_tasksus_spec.


Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.



(* TaskResume *)

Definition taskresume_err_prio_invalid (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr OS_PRIO_INVALID))) /\
      (exists v3 v',
        vl = ((Vint32 v3)::v'::nil) /\
        (Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true \/ Int.eq (Int.repr OS_LOWEST_PRIO) v3 = true) /\
        (v' = (Vint32 (Int.repr OS_PRIO_INVALID)) /\ O_opt= Some O1 \/
         v' <> (Vint32 (Int.repr OS_PRIO_INVALID)) /\ O_opt = None)
      )
  end.

Definition taskresume_err_no_such_tcb (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_RESUME_PRIO))) /\
      (exists v3 v',
      vl = ((Vint32 v3)::v'::nil) /\
        (exists tls,
          (* get O1 abstcblsid = Some (abstcblist tls) /\ *)
          (~ exists tid st msg sus, TcbMod.get tls tid = Some (v3, st, msg, sus))
        ) /\
        (v' = (Vint32 (Int.repr OS_TASK_RESUME_PRIO)) /\ O_opt= Some O1 \/
         v' <> (Vint32 (Int.repr OS_TASK_RESUME_PRIO)) /\ O_opt = None)
      )
  end.

Definition taskresume_err_not_suspended (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_NOT_SUSPENDED))) /\
      (exists v3 v',
      vl = ((Vint32 v3)::v'::nil) /\
      (exists tls,
        (* get O1 abstcblsid = Some (abstcblist tls) /\ *)
        (exists tid st msg, TcbMod.get tls tid = Some (v3, st, msg, false))
        ) /\
        (v' = (Vint32 (Int.repr OS_TASK_NOT_SUSPENDED)) /\ O_opt= Some O1 \/
         v' <> (Vint32 (Int.repr OS_TASK_NOT_SUSPENDED)) /\ O_opt = None)
      )
  end.

(*
Definition taskresume_succ_ret (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr OS_NO_ERR))) /\
      (exists v3 v',
      vl = ((Vint32 v3)::v'::nil) /\
      (exists tls tid st msg sus tls',
      (* get O1 abstcblsid = Some (abstcblist tls) /\ *)
        TcbMod.get tls tid = Some (v3, st, msg, sus) /\
        tls' = set tls tid (v3, st, msg, false) /\
        O_opt = Some(set O1 abstcblsid (abstcblist tls')) 
        ) /\
        (v' = (Vint32 (Int.repr OS_NO_ERR)) /\ O_opt= Some O1 \/
         v' <> (Vint32 (Int.repr OS_NO_ERR)) /\ O_opt = None)
      )
  end.
*)
Definition taskresume_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists v3 v',
      vl = ((Vint32 v3)::v'::nil) /\
        ( opv = None /\
          exists tls tid st msg sus tls',
          (* get O1 abstcblsid = Some (abstcblist tls) /\ *)
            TcbMod.get tls tid = Some (v3, st, msg, sus) /\
            tls' = set tls tid (v3, st, msg, false) /\
            O_opt = Some(set O1 abstcblsid (abstcblist tls'))           
        )      
  end.


Definition taskresume_ret (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
  | (opv, O_opt) =>
  exists v3 v',
  vl = ((Vint32 v3)::v'::nil) /\
      (
        opv = Some (Vint32 (Int.repr OS_NO_ERR)) /\
         ( v' = (Vint32 (Int.repr OS_NO_ERR)) /\ O_opt=Some O1
            \/ v' <> (Vint32 (Int.repr OS_NO_ERR)) /\ O_opt = None))             
end.

(* Definition wait_suspend_nzero st sus :=
  sus = true /\
  ((exists eid t, st = wait (os_stat_sem eid) (Some t) -> t <> Int.zero )\/ 
  (exists eid t, st = wait (os_stat_q eid) (Some t) -> t <> Int.zero ) \/ 
  (exists eid t, st = wait (os_stat_mbox eid) (Some t) -> t <> Int.zero ) \/ 
  (exists eid t, st = wait (os_stat_mutexsem eid) (Some t) -> t <> Int.zero ) \/ 
  (exists eid t, st = wait (os_stat_port eid) (Some t) -> t <> Int.zero)).  *)

(* Definition wait_suspend_nzero st sus eid t :=
  sus = true /\
  (
    st = wait (os_stat_sem eid) (Some t) \/
    st = wait (os_stat_q eid) (Some t) \/
    st = wait (os_stat_mbox eid) (Some t) \/
    st = wait (os_stat_mutexsem eid) (Some t) \/
    st = wait (os_stat_port eid) (Some t)
  ) -> t <> Int.zero. *)

  Definition wait_suspend_nzero st sus :=    
    (forall eid t,
      sus = true /\ ((st = wait (os_stat_sem eid) (Some t) \/
      st = wait (os_stat_q eid) (Some t) \/
      st = wait (os_stat_mbox eid) (Some t) \/
      st = wait (os_stat_mutexsem eid) (Some t) \/
      st = wait (os_stat_port eid) (Some t))) -> t <> Int.zero
    ).

Definition taskresume_time_nzero (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v3 v', 
      vl = ((Vint32 v3)::v'::nil) /\
        (opv = None /\
           exists tls tid st msg sus,
             (* get O1 abstcblsid = Some (abstcblist tls) /\ *) 
             TcbMod.get tls tid = Some (v3, st, msg, sus) /\
               (wait_suspend_nzero st sus /\ O_opt = Some O1) \/
               (~wait_suspend_nzero st sus) /\ O_opt = None)
  end.

(* 
Definition sres (vl : vallist) :=
  match vl with
    | (Vint32 v3) :: v' :: nil => isched ;; taskresume_ret (|v'::nil|)
    | _ => spec_done None
  end. 
  *)

  Definition taskresumecode (vl: vallist) :=
    ASSERT (fun O => length vl =2%nat) ;; 
    (
      taskresume_err_prio_invalid (|vl|) ??
        taskresume_err_no_such_tcb (|vl|) ??
        taskresume_err_not_suspended (|vl|) ??
        (taskresume_time_nzero (|vl|);;
         ((taskresume_succ (|vl|) ;; taskresume_ret (|vl|)) ??
            (taskresume_succ (|vl|) ;; isched ;; taskresume_ret (|vl|))))
    ).



Lemma absimp_taskres_prio_invalid':
  forall P v1 v' sch s,
    v' = Vint32 (Int.repr OS_PRIO_INVALID) ->
    can_change_aop P ->
    (Int.ltu (Int.repr OS_LOWEST_PRIO) v1 = true \/ Int.eq (Int.repr OS_LOWEST_PRIO) v1 = true) ->
    absinfer sch ( <||spec_code_cons (taskresumecode ((Vint32 v1) :: v' :: nil)) s ||> ** P)
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

Lemma absimp_taskres_prio_invalid_abt':
  forall P v1 v' sch s,
    v' <> Vint32 (Int.repr OS_PRIO_INVALID) ->
    can_change_aop P ->
    (Int.ltu (Int.repr OS_LOWEST_PRIO) v1 = true \/ Int.eq (Int.repr OS_LOWEST_PRIO) v1 = true) ->
    absinfer sch ( <||spec_code_cons (taskresumecode ((Vint32 v1) :: v' :: nil)) s ||> ** P)
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

Lemma absimp_taskres_no_such_tcb':
  forall P v1 v' sch  (tcbls : TcbMod.map) s,
    v' = Vint32 (Int.repr OS_TASK_RESUME_PRIO) ->
    can_change_aop P ->
    (~exists tid st msg sus, TcbMod.get tcbls tid = Some (v1, st, msg, sus)) ->
    absinfer sch ( <||spec_code_cons (taskresumecode ((Vint32 v1) :: v' :: nil)) s ||> **
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
  infer_solver 1%nat.
Qed.

Lemma absimp_taskres_no_such_tcb_abt':
  forall P v1 v' sch  (tcbls : TcbMod.map) s,
    v' <> Vint32 (Int.repr OS_TASK_RESUME_PRIO) ->
    can_change_aop P ->
    (~exists tid st msg sus, TcbMod.get tcbls tid = Some (v1, st, msg, sus)) ->
    absinfer sch ( <||spec_code_cons (taskresumecode ((Vint32 v1) :: v' :: nil)) s ||> **
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

Lemma absimp_taskres_not_suspended':
  forall P v1 v' sch  (tcbls : TcbMod.map) s,
    v' = Vint32 (Int.repr OS_TASK_NOT_SUSPENDED) ->
    can_change_aop P ->
    (exists tid st msg, TcbMod.get tcbls tid = Some (v1, st, msg, false)) ->
    absinfer sch ( <||spec_code_cons (taskresumecode ((Vint32 v1) :: v' :: nil)) s ||> **
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


Lemma absimp_taskres_not_suspended_abt':
  forall P v1 v' sch  (tcbls : TcbMod.map) s,
    v' <> Vint32 (Int.repr OS_TASK_NOT_SUSPENDED) ->
    can_change_aop P ->
    (exists tid st msg, TcbMod.get tcbls tid = Some (v1, st, msg, false)) ->
    absinfer sch ( <||spec_code_cons (taskresumecode ((Vint32 v1) :: v' :: nil)) s ||> **
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


Lemma absimp_taskres_wait_suspend':
  forall P v1 v' sch  (tcbls : TcbMod.map) s,
  can_change_aop P ->
    absinfer sch ( <||spec_code_cons (taskresumecode ((Vint32 v1) :: v' :: nil)) s ||> ** P)
             ( <||spec_code_cons (taskresume_time_nzero (|(Vint32 v1) :: v' :: nil|);;
             ((taskresume_succ (|(Vint32 v1) :: v' :: nil|) ;; taskresume_ret (|(Vint32 v1) :: v' :: nil|)) ??
                (taskresume_succ (|(Vint32 v1) :: v' :: nil|) ;; isched ;; taskresume_ret (|(Vint32 v1) :: v' :: nil|)))) s ||> ** P).
Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq; try(eauto).
  eapply absinfer_assert_cont; try(eauto).
  eapply absinfer_trans.
  eapply absinfer_seq_end; try (eauto).
  infer_branch 3%nat.
  apply absinfer_eq.
Qed.

Lemma absimp_taskres_time_nzero':
  forall P v1 v' sch  (tcbls : TcbMod.map) s tid st msg sus,
    can_change_aop P ->
    TcbMod.get tcbls tid = Some (v1, st, msg, sus) ->
    wait_suspend_nzero st sus ->
    absinfer sch ( <||spec_code_cons (taskresume_time_nzero (|(Vint32 v1) :: v' :: nil|);;
    ((taskresume_succ (|(Vint32 v1) :: v' :: nil|) ;; taskresume_ret (|(Vint32 v1) :: v' :: nil|)) ??
       (taskresume_succ (|(Vint32 v1) :: v' :: nil|) ;; isched ;; taskresume_ret (|(Vint32 v1) :: v' :: nil|)))) s ||> ** HTCBList tcbls ** P)
             ( <||spec_code_cons ((taskresume_succ (|(Vint32 v1) :: v' :: nil|) ;; taskresume_ret (|(Vint32 v1) :: v' :: nil|)) ??
             (taskresume_succ (|(Vint32 v1) :: v' :: nil|) ;; isched ;; taskresume_ret (|(Vint32 v1) :: v' :: nil|))) s ||> ** HTCBList tcbls ** P).
Proof.
  intros.
  simpls.
  infer_solver 0%nat.
Qed.

Lemma absimp_taskres_time_nzero_abt':
  forall P v1 v' sch  (tcbls : TcbMod.map) s tid st msg sus,
    can_change_aop P ->
    TcbMod.get tcbls tid = Some (v1, st, msg, sus) ->
    ~wait_suspend_nzero st sus ->
    absinfer sch ( <||taskresume_time_nzero (|(Vint32 v1) :: v' :: nil|) ;; s ||> **
                       HTCBList tcbls ** P)
             ( <|| ABORT ||> ** HTCBList tcbls ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HTCBList tcbls ** P)) .
  can_change_aop_solver.
   eapply absinfer_trans; try(eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
  Unshelve.
  trivial. trivial. trivial.
Qed.

Lemma absimp_taskres_succ_nosched':
  forall P v1 v' sch  (tcbls : TcbMod.map) s,
  can_change_aop P ->
    absinfer sch ( <||spec_code_cons ((taskresume_succ (|(Vint32 v1) :: v' :: nil|) ;; taskresume_ret (|(Vint32 v1) :: v' :: nil|)) ??
    (taskresume_succ (|(Vint32 v1) :: v' :: nil|) ;; isched ;; taskresume_ret (|(Vint32 v1) :: v' :: nil|))) s ||> **
    HTCBList tcbls ** P)
             ( <||spec_code_cons (taskresume_succ(|(Vint32 v1) :: v' :: nil|) ;; taskresume_ret(|(Vint32 v1) :: v' :: nil|)) s ||> ** HTCBList tcbls ** P).
Proof.
  intros.
  simpls.
  infer_branch 0%nat.
  apply absinfer_eq.
Qed.

(* Lemma absimp_taskres_succ_nosched':
  forall P v1 v' sch  (tcbls : TcbMod.map) s,
  can_change_aop P ->
    absinfer sch ( <||spec_code_cons (taskresumecode ((Vint32 v1) :: v' :: nil)) s ||> **
    HTCBList tcbls ** P)
             ( <||spec_code_cons (taskresume_succ(|(Vint32 v1) :: v' :: nil|) ;; taskresume_ret(|(Vint32 v1) :: v' :: nil|)) s ||> ** HTCBList tcbls ** P).
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
  infer_branch 3%nat.
  apply absinfer_eq.
Qed. *)

Lemma absimp_taskres_rdy_nosched':
  forall P v1 v' sch (tcbls : TcbMod.map) tid st msg sus s,
    can_change_aop P ->
    TcbMod.get tcbls tid = Some (v1, st, msg, sus) ->
    absinfer sch ( <||spec_code_cons (taskresume_succ(|(Vint32 v1) :: v' :: nil|) ;; taskresume_ret(|(Vint32 v1) :: v' :: nil|)) s ||> ** HTCBList tcbls ** P)
( <||spec_code_cons (taskresume_ret(|(Vint32 v1) :: v' :: nil|)) s ||> ** HTCBList (set tcbls tid (v1, st, msg, false)) ** P).
Proof.
  intros.
  simpls.
  add_END_if_ness.
  multi_step_handler.
  infer_part2.
Qed.


Lemma absimp_taskres_succ':
  forall P v1 v' sch  (tcbls : TcbMod.map) s,
  can_change_aop P ->
    absinfer sch ( <||spec_code_cons ((taskresume_succ (|(Vint32 v1) :: v' :: nil|) ;; taskresume_ret (|(Vint32 v1) :: v' :: nil|)) ??
    (taskresume_succ (|(Vint32 v1) :: v' :: nil|) ;; isched ;; taskresume_ret (|(Vint32 v1) :: v' :: nil|))) s ||> **
    HTCBList tcbls ** P)
             ( <||spec_code_cons (taskresume_succ(|(Vint32 v1) :: v' :: nil|) ;; isched ;; taskresume_ret(|(Vint32 v1) :: v' :: nil|)) s ||> ** HTCBList tcbls ** P).
 Proof.
  intros.
  simpls.
  infer_branch 1%nat.
  apply absinfer_eq.
Qed.


(* Lemma absimp_taskres_succ':
  forall P v1 v' sch  (tcbls : TcbMod.map) s,
  can_change_aop P ->
    absinfer sch ( <||spec_code_cons (taskresumecode ((Vint32 v1) :: v' :: nil)) s ||> **
    HTCBList tcbls ** P)
             ( <||spec_code_cons (taskresume_succ(|(Vint32 v1) :: v' :: nil|) ;; isched ;; taskresume_ret(|(Vint32 v1) :: v' :: nil|)) s ||> ** HTCBList tcbls ** P).
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
Qed. *)

Lemma absimp_taskres_rdy':
  forall P v1 v' sch (tcbls : TcbMod.map) tid st msg sus s,
    can_change_aop P ->
    TcbMod.get tcbls tid = Some (v1, st, msg, sus) ->
    absinfer sch ( <||spec_code_cons (taskresume_succ(|(Vint32 v1) :: v' :: nil|) ;; isched ;; taskresume_ret(|(Vint32 v1) :: v' :: nil|)) s ||> ** HTCBList tcbls ** P)
( <||spec_code_cons (isched ;; taskresume_ret(|(Vint32 v1) :: v' :: nil|)) s ||> ** HTCBList (set tcbls tid (v1, st, msg, false)) ** P).
Proof.
  intros.
  simpls.
  add_END_if_ness.
  multi_step_handler.
  infer_part2.
Qed.



Lemma absimp_taskresume_ret:
  forall P v1 v' sch s ,
    v' = Vint32 (Int.repr OS_NO_ERR) ->    
    can_change_aop P ->
    absinfer sch ( <|| taskresume_ret(|(Vint32 v1) :: v' :: nil|) ;; s ||> ** P)
             (<|| s ||> **  P).
Proof. 
  intros.
  infer_solver 0%nat.
Qed.


Lemma absimp_taskresume_ret_abt:
  forall P v1 v' sch s,
    can_change_aop P ->
    v' <> Vint32 (Int.repr OS_NO_ERR) ->
    absinfer sch ( <|| taskresume_ret(|(Vint32 v1) :: v' :: nil|) ;; s ||> ** P)
      ( <|| ABORT ||> ** P).
Proof.
intros.
eapply absinfer_trans.
eapply absinfer_seq; try(eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
eapply absinfer_seq_abt; try eauto.
Qed.

  
Definition OSTaskResumePre' (vl:vallist) (logicl:list logicvar) ct :=
  EX s v' er, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
       [| logicl = logic_val v' :: logic_code s :: nil |] ** <|| spec_code_cons (taskresumecode (vl++(v' ::nil))) s ||> **  
       p_local OSLInv ct init_lg). 


  
Theorem OSTaskResumePreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSTaskResumePre' vl ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSTaskResumePre : fpre :=
  fun vl ll ct => mkfunasrt (OSTaskResumePreGood vl ll ct).

Definition OSTaskResumePost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v' k er, 
  (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** Aier er **
     [| logicl = logic_val v' :: logic_code s :: nil |] **
     [| v = Some v' /\ v' = Vint32 k  /\ 
        Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k) (Byte.max_unsigned) |] ** 
   <|| s ||> ** p_local OSLInv ct init_lg). 

Theorem OSTaskResumePostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSTaskResumePost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSTaskResumePost : fpost :=
  fun vl v ll ct => mkfunasrt (OSTaskResumePostGood vl v ll ct).



Definition OSTaskResume_spec : fspec:= (OSTaskResumePre,OSTaskResumePost,(Tint8, Tint8::nil)).

Definition new_osq_spec_list := 
  (((OSTaskResume, OSTaskResume_spec) :: nil) ++ osq_spec_list).

Definition new_OS_spec :=  convert_spec new_osq_spec_list.


Definition new_internal_fun_list := 
  ((OSTaskResume_impl :: nil) ++ internal_fun_list) %list.


Definition new_os_internal :=  convert_cfuns new_internal_fun_list.

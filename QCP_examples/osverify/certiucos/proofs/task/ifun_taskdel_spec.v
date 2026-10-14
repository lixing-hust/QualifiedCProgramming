Require Import ucos_include1.
Require Import os_code_defs1.
Require Import os_ucos_h1.
Require Import code_notations1.
Require Import sep_lemmas_ext1.
Require Import linv_solver1.
Require Import taskcreate_pure.
Require Import protect1.
Require Import Lia.

Require Import infer_absabt_step1. 

Require Import inline_definitions1.
Require Import inline_bittblfunctions1.
Require Import inline_tactics1.
Require Import symbolic_lemmas1.
Require Import new_inv1.
Require Import protect1.
Require Import Lia.

Require Import ifun_taskcreate.
Require Import List.
Require Import ifun_spec1.
Require Import os_program1.
Require Import os_task1.

Require Import task_pure.

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

(* task delete *)

Definition taskdel_err_prio_is_idle (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_DEL_IDLE))) /\
      (exists v3 v',
         vl= ((Vint32 v3)::v'::nil) /\
         (Int.eq (Int.repr OS_IDLE_PRIO) v3 = true  /\
         (v' = (Vint32 (Int.repr OS_TASK_DEL_IDLE)) /\ O_opt= Some O1 \/
          v' <> (Vint32 (Int.repr OS_TASK_DEL_IDLE)) /\ O_opt = None)
         )
      )
  end.


Definition taskdel_err_prio_invalid (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr OS_PRIO_INVALID))) /\
      (exists v3 v',
      vl= ((Vint32 v3)::v'::nil) /\
      Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true /\
         (v' = (Vint32 (Int.repr OS_PRIO_INVALID)) /\ O_opt= Some O1 \/
          v' <> (Vint32 (Int.repr OS_PRIO_INVALID)) /\ O_opt = None)
      )
  end.


 (* placeholder or null *)
Definition taskdel_err_no_such_tcb (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_DEL_ERR))) /\
      (
        exists v3 v',
        vl= ((Vint32 v3)::v'::nil) /\
        (exists tls,
             (*get O1 abstcblsid = Some (abstcblist tls) /\*)
             (~ exists tid st msg, TcbMod.get tls tid= Some (v3, st, msg)) 
          ) /\
          (v' = (Vint32 (Int.repr OS_TASK_DEL_ERR)) /\ O_opt= Some O1 \/
          v' <> (Vint32 (Int.repr OS_TASK_DEL_ERR)) /\ O_opt = None)
      )
  end.

Definition taskdel_err_is_some_mutex_owner (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_DEL_SOME_MUTEX_OWNER))) /\
      (
        exists v3 v',
        vl= ((Vint32 v3)::v'::nil) /\
        (exists tls els eid tid t m opr wls pr,
             (*get O1 abstcblsid = Some (abstcblist tls) /\*)
             (*get O1 absecblsid = Some (absecblist els) /\*)
             get tls tid = Some (v3, t, m) /\
             get els eid = Some (absmutexsem pr (Some (tid, opr)), wls) 
          ) /\
          (v' = (Vint32 (Int.repr OS_TASK_DEL_SOME_MUTEX_OWNER)) /\ O_opt= Some O1 \/
          v' <> (Vint32 (Int.repr OS_TASK_DEL_SOME_MUTEX_OWNER)) /\ O_opt = None)          
      )
  end.

Definition taskdel_err_has_no_next (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT))) /\
      ( exists v3 v',
      vl= ((Vint32 v3)::v'::nil) /\
      (v' = (Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT)) /\ O_opt= Some O1 \/
      v' <> (Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT)) /\ O_opt = None)
      )
  end.

(*
Definition isWait4Ecb x t :=
      x = os_stat_sem t \/ x = os_stat_q t \/ x = os_stat_mbox t \/ x = os_stat_mutexsem t.
*)

Definition taskdel_clear_waitls_bit (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
    exists v3 v',
    vl= ((Vint32 v3)::v'::nil) /\          
          (
            opv = None /\
            exists tls els tid eid st msg ehb wl els' t,
              (*get O1 abtcblsid = Some (abstcblist tls) /\*)
              (*get O1 absecblsid = Some (absecblist els) /\*)
              get tls tid = Some (v3, wait st t, msg) /\
              isWait4Ecb st eid /\
              get els eid = Some (ehb, wl) /\
              els' = set els eid (ehb, (remove_tid tid wl)) /\
              O_opt= Some (set O1 absecblsid (absecblist els'))
          )
  end.

Definition taskdel_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      exists  v',
      vl= (v' :: nil)/\
          (
            opv = Some (Vint32 (Int.repr NO_ERR)) /\
             ( v' = (Vint32 (Int.repr NO_ERR)) /\ O_opt=Some O1
                \/ v' <> (Vint32 (Int.repr NO_ERR)) /\ O_opt = None))
                 
end.

Definition sdel (vl : vallist) :=
  match vl with
    | (Vint32 v3) :: v' :: nil => spec_del (Vint32 v3) ;; isched ;; taskdel_succ (|v'::nil|)
    | _ => spec_done None
  end.

Definition taskdelcode (vl : vallist) :=
  ASSERT (fun O => length vl =2%nat) ;; 
  (
    taskdel_err_prio_invalid (|vl|)
    ?? taskdel_err_no_such_tcb (|vl|)
    ?? taskdel_err_prio_is_idle (|vl|)
    ?? taskdel_err_is_some_mutex_owner (|vl|)
    ?? taskdel_err_has_no_next (|vl|)
    ?? sdel (vl) 
    ?? (taskdel_clear_waitls_bit (|vl|) ;; sdel(vl))
  ).


Lemma absimp_taskdel_prio_invalid':
  forall P v3 v' sch s,
    v' = Vint32 (Int.repr OS_PRIO_INVALID) ->
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true ->
    absinfer sch ( <||spec_code_cons (taskdelcode ((Vint32 v3) :: v' :: nil)) s ||> ** P)
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

Lemma absimp_taskdel_prio_invalid_abt':
  forall P v3 v' sch s,
    v' <> Vint32 (Int.repr OS_PRIO_INVALID) ->
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true ->
    absinfer sch ( <||spec_code_cons (taskdelcode ((Vint32 v3) :: v' :: nil)) s ||> ** P)
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
  exists v3 v'.
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

Lemma absimp_taskdel_prio_is_idle':
forall P v3 v' sch s,
  v' = Vint32 (Int.repr OS_TASK_DEL_IDLE) ->  
  can_change_aop P ->
  Int.eq (Int.repr OS_IDLE_PRIO) v3 = true ->
    absinfer sch ( <||spec_code_cons (taskdelcode ((Vint32 v3) :: v' :: nil)) s ||> ** P)
             ( <|| s ||> ** P).
Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq; try(eauto).
  eapply absinfer_assert_cont; try(eauto).
  eapply absinfer_trans.
  eapply absinfer_seq_end; try (eauto).
  infer_solver 2%nat.
Qed.

Lemma absimp_taskdel_prio_is_idle_abt':
forall P v3 v' sch s,
  v' <> Vint32 (Int.repr OS_TASK_DEL_IDLE) ->  
  can_change_aop P ->
  Int.eq (Int.repr OS_IDLE_PRIO) v3 = true ->
    absinfer sch ( <||spec_code_cons (taskdelcode ((Vint32 v3) :: v' :: nil)) s ||> ** P)
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
  exists v3 v'.
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



Lemma absimp_taskdel_prio_no_such_tcb':
  forall P v3 v' sch mqls tls t ct s,
  v' = Vint32 (Int.repr OS_TASK_DEL_ERR) ->  
    can_change_aop P ->
    (~ exists tid st msg, TcbMod.get tls tid= Some (v3, st, msg))  ->
    absinfer sch ( <|| spec_code_cons (taskdelcode ((Vint32 v3) :: v' :: nil)) s ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| s ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq. 
  can_change_aop_solver.
  instantiate(1 := HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
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


Lemma absimp_taskdel_prio_no_such_tcb_abt':
  forall P v3 v' sch mqls tls t ct s,
  v' <> Vint32 (Int.repr OS_TASK_DEL_ERR) ->  
    can_change_aop P ->
    (~ exists tid st msg, TcbMod.get tls tid= Some (v3, st, msg))  ->
    absinfer sch ( <|| spec_code_cons (taskdelcode ((Vint32 v3) :: v' :: nil)) s ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| ABORT ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate(1 := HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
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
  instantiate(1 := HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P). 
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
  exists v3 v'.

  splits. 
  auto.
  exists tls.
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
  do 6 eexists.
  splits ; try eauto.
  do 6 eexists.
  splits ; try eauto.
  do 6 eexists.
  splits ; try eauto.    
  eapply change_aop_rule; eauto.
  eapply absinfer_seq_abt; try eauto.
  can_change_aop_solver.
  can_change_aop_solver.
Qed.


Lemma absimp_taskdel_some_mutex_owner':
  forall P v3 v' sch mqls tls t ct tid s,
    v' = Vint32 (Int.repr OS_TASK_DEL_SOME_MUTEX_OWNER) ->  
    can_change_aop P ->
    (exists x y z w tt mm , TcbMod.get tls tid = Some (v3, tt, mm) /\ EcbMod.get mqls x = Some (absmutexsem y (Some (tid, z)), w)) ->
    absinfer sch ( <|| spec_code_cons (taskdelcode ((Vint32 v3) :: v' :: nil)) s ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| s ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) .
Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq. 
  can_change_aop_solver.
  instantiate(1 := HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
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
  splits.
  eauto.
  exists v3 v'.
  splits.
  auto.
  do 6 destruct H1.
  exists tls mqls x tid x3 x4.
  exists x1 x2 x0.
  auto.
  auto.
Qed.

Lemma absimp_taskdel_some_mutex_owner_abt':
  forall P v3 v' sch mqls tls t ct tid s,
    v' <> Vint32 (Int.repr OS_TASK_DEL_SOME_MUTEX_OWNER) ->  
    can_change_aop P ->
    (exists x y z w tt mm , TcbMod.get tls tid = Some (v3, tt, mm) /\ EcbMod.get mqls x = Some (absmutexsem y (Some (tid, z)), w)) ->
    absinfer sch ( <|| spec_code_cons (taskdelcode ((Vint32 v3) :: v' :: nil)) s ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| ABORT ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) .
 Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate(1 := HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
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
  instantiate(1 := HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P). 
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
  exists v3 v'.

  splits. 
  auto.
  exists tls.
  do 6 destruct H1.
  do 8 eexists.
  eauto.
  auto.
  apply map_join_emp.
  
  repeat hmstep_call_consturctor.
  simpl in *.
  simpljoin.
  do 6 eexists.
  splits ; try eauto.
  do 6 eexists.
  splits ; try eauto.
  do 6 eexists.
  splits ; try eauto.
  do 6 eexists.
  splits ; try eauto.
  do 6 eexists.
  splits ; try eauto.    
  eapply change_aop_rule; eauto.
  eapply absinfer_seq_abt; try eauto.
  can_change_aop_solver.
  can_change_aop_solver.
Qed.


Lemma absimp_taskdel_prio_HAS_NO_NEXT':
  forall P v3 v' sch mqls tls t ct s,
    v' = Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT) ->      
    can_change_aop P ->
    absinfer sch ( <|| spec_code_cons (taskdelcode ((Vint32 v3) :: v' :: nil)) s ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| s ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) .
 Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq. 
  can_change_aop_solver.
  instantiate(1 := HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
  can_change_aop_solver.
  eapply absinfer_assert_cont; try(eauto).
  can_change_aop_solver.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_seq_end.
  3: eauto.
  can_change_aop_solver.  
  can_change_aop_solver.
  infer_solver 4%nat.
Qed.

Lemma absimp_taskdel_prio_HAS_NO_NEXT_abt':
  forall P v3 v' sch mqls tls t ct s,
    v' <> Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT) ->      
    can_change_aop P ->
    absinfer sch ( <|| spec_code_cons (taskdelcode ((Vint32 v3) :: v' :: nil)) s ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| ABORT ||>
 ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) .
 Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate(1 := HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
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
  instantiate(1 := HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P). 
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
  exists v3 v'.

  splits. 
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
  do 6 eexists.
  splits ; try eauto.
  do 6 eexists.
  splits ; try eauto.
  do 6 eexists.
  splits ; try eauto.    
  eapply change_aop_rule; eauto.
  eapply absinfer_seq_abt; try eauto.
  can_change_aop_solver.
  can_change_aop_solver.
Qed.

Lemma absimp_taskdel_succ':
  forall P v3 v' sch t tls mqls ct s,
  can_change_aop P ->
    absinfer sch ( <|| spec_code_cons (taskdelcode ((Vint32 v3) :: v' :: nil)) s ||> **
                       HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| spec_code_cons (taskdel_clear_waitls_bit (|(Vint32 v3) :: v' :: nil|) ;; sdel ((Vint32 v3) :: v' :: nil)) s ||> **  HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
 Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq. 
  can_change_aop_solver.
  instantiate(1 := HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
  can_change_aop_solver.
  eapply absinfer_assert_cont; try(eauto).
  can_change_aop_solver.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_seq_end.
  3: eauto.
  can_change_aop_solver.  
  can_change_aop_solver.
  infer_branch 6%nat.
  apply absinfer_eq.
Qed.


Lemma absimp_taskdel_rdy_succ':
forall P v3 v' sch t tls mqls ct s,
can_change_aop P ->
  absinfer sch ( <|| spec_code_cons (taskdelcode ((Vint32 v3) :: v' :: nil)) s ||> **
                     HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
           ( <|| spec_code_cons (sdel ((Vint32 v3) :: v' :: nil)) s ||> **  HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
 Proof.
  intros.
  simpls.
  eapply absinfer_trans.
  eapply absinfer_seq. 
  can_change_aop_solver.
  instantiate(1 := HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
  can_change_aop_solver.
  eapply absinfer_assert_cont; try(eauto).
  can_change_aop_solver.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_seq_end.
  3: eauto.
  can_change_aop_solver.  
  can_change_aop_solver.
  infer_branch 5%nat.
  apply absinfer_eq.
Qed.

Lemma absimp_taskdel_succ:
  forall P v' sch s ,
    v' = Vint32 (Int.repr NO_ERR) ->    
    can_change_aop P ->
    absinfer sch ( <|| taskdel_succ (|v'::nil|);; s ||> ** P)
             (<|| s ||> **  P).

Proof. 
  intros.
  infer_solver 0%nat.
Qed.


Lemma absimp_taskdel_succ_abt:
  forall P v' sch s,
    can_change_aop P ->
    v' <> Vint32 (Int.repr NO_ERR) ->
    absinfer sch ( <|| taskdel_succ (|v'::nil|);; s ||> ** P)
      ( <|| ABORT ||> ** P).
Proof.
intros.
eapply absinfer_trans.
eapply absinfer_seq; try(eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
eapply absinfer_seq_abt; try eauto.
Qed.

Lemma absimp_taskdel_cler_waitls_bit':
  forall P v3 v' sch tls els ct els' st wait_t msg eid ehb wl tid t s,
    can_change_aop P ->
    TcbMod.get tls tid = Some (v3, wait st wait_t, msg) ->
    isWait4Ecb st eid ->
    EcbMod.get els eid = Some (ehb, wl) ->
    els' = set els eid (ehb, (remove_tid tid wl)) ->
    absinfer sch 
             ( <|| spec_code_cons (taskdel_clear_waitls_bit (|((Vint32 v3) :: v'::nil)|) ;; sdel ((Vint32 v3) :: v' :: nil)) s ||> **  HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| spec_code_cons (sdel ((Vint32 v3) :: v' :: nil)) s ||> **  HECBList els' ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
 Proof.
  intros.
  simpls.
  add_END_if_ness.
  multi_step_handler.

  infer_part2.
Qed.

Lemma absimp_taskdel_ret_succ':
forall P v' sch s,
v' = Vint32 (Int.repr NO_ERR) ->      
can_change_aop P ->
  absinfer sch ( <|| taskdel_succ (|v'::nil|);; s ||> ** P)
           ( <|| s ||> ** P).
Proof.
  intros.
  infer_solver 0%nat.
Qed.

Lemma absimp_taskdel_ret_succ_abt':
forall P v' sch s,
v' <> Vint32 (Int.repr NO_ERR) ->      
can_change_aop P ->
  absinfer sch ( <|| taskdel_succ (|v'::nil|);; s ||> ** P)
           ( <|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq; try(eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
  eapply absinfer_seq_abt; try eauto.
Qed.


Lemma hl_get_ecb_can_split_ecblist:
  forall l hd tl ecbls hecbls tcbls tid he ,
    EcbMod.get hecbls tid = Some he ->
    ECBList_P hd tl l ecbls hecbls tcbls ->
    exists l1 l2 pt pt2 ecbls1 ecbls2 hecbls1 hecbls2, 
      join hecbls1 hecbls2 hecbls /\
      l = l1 ++ (pt :: l2) /\
      ecbls = ecbls1 ++ (pt2 :: ecbls2) /\
      ECBList_P hd (Vptr tid) l1 ecbls1 hecbls1 tcbls /\ 
      ECBList_P (Vptr tid) tl (pt::l2) (pt2::ecbls2) hecbls2 tcbls.
Proof.
  induction l.
  intros.
  simpl in H0.
  simpljoin.
  false.
  intros.
  unfold1 ECBList_P in H0.
  simpljoin.
  destruct ecbls.
  tryfalse.
  destruct a.
  simpljoin.
  unfold TcbJoin in H2.
  assert (get (sig x x0) tid = Some he \/ get x1 tid = Some he).
  unfold get,sig,join in *; simpl in *.
  eapply  EcbMod.join_get_or.
  exact H2.
  auto.
  destruct H5.
  Focus 2.
  lets bb: IHl H5 H4.
  repeat destruct bb.
  repeat destruct H6.
  exists ( (v,v0) :: x3).
  exists x4.
  exists x5.
  exists x6.
  exists (e::x7).
  exists x8.
  assert (exists bb, join (sig x x0) x9 bb).
  eexists.
  join auto.
  destruct H8.
  exists x11.
  exists x10.
  splits.
  join auto.
  simpl.
  simpljoin.
  simpljoin.
  auto.
  unfold1 ECBList_P.
  simpljoin.
  repeat tri_exists_and_solver1.
  simpljoin; auto.
  cut ( x = tid).
  intro.
  exists (@nil (os_inv1.EventCtr)).
  exists l.
  exists (v, v0).
  exists e.
  exists (@nil EventData).
  exists ecbls.
  do 2 eexists.
  splits.
  2:eauto.
  2:eauto.
  2:simpl.
  2:splits; auto.
  instantiate (1:= hecbls).
  join auto.
  Focus 2.
  unfold1 ECBList_P.
  repeat tri_exists_and_solver1.
  subst; auto.
  subst; auto.
  subst; auto.
  
  unfold get,sig,join in *; simpl in *.
  assert (x = tid \/ x <> tid) by tauto.
  destruct H6; auto.
  rewrite EcbMod.get_a_sig_a' in H5.
  inversion H5.
  go.
Qed.

Lemma evsllseg_split:
  forall l1 l1' l2 l2' hd tl  P,
    length l1 = length l1' ->
    evsllseg hd tl (l1 ++ l2) (l1' ++ l2')  ** P ==>
             EX pp, evsllseg hd pp l1 l1' ** evsllseg pp tl l2 l2' ** P.
Proof.
  induction l1.
  intros.
  simpl in H.
  destruct l1'; tryfalse.
  unfold evsllseg at 1.
  sep pauto.
  intros.
  destruct l1'; tryfalse.
  unfold1 evsllseg.
  destruct a.
  sep normal .
  change ( (((v, v0) ::l1 ) ++ l2) ) with ( (v,v0) :: l1++l2) in H0.
  change ( ((e ::l1' ) ++ l2') ) with ( e :: l1'++l2') in H0.
  unfold1 evsllseg in H0.
  sep normal in H0.
  sep destruct H0.
  sep lift 3%nat in H0.
  simpl in H.
  assert (length l1 = length l1') by omega.
  lets bbb: IHl1 H1 H0.
  sep destruct bbb.
  clear H0.
  sep pauto.
Qed.

Lemma ecblistp_evsllseg_tlsame:
  forall ls1 hd tl tl' ls2 hls tcbls P s,
       ECBList_P hd tl ls1 ls2 hls tcbls ->
       s |= evsllseg hd tl' ls1 ls2 ** P ->
       tl  = tl'.
Proof.
  induction ls1.
  intros.
  simpl in H.
  simpljoin.
  unfold evsllseg in H0.
  sep split in H0.
  tauto.
  intros.
  unfold1 ECBList_P in H.
  simpljoin.
  destruct ls2; tryfalse.
  destruct a; simpljoin.
  unfold1 evsllseg in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0.
  rewrite H in H5.
  inverts H5.
  eapply IHls1.
  eauto.
  sep lift 2%nat in H0.
  eauto.
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
  

Definition OSTaskDeletePre' (vl:vallist) (logicl:list logicvar) ct :=
  EX s v', 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr **
       [| logicl = logic_val v' :: logic_code s :: nil |] ** <|| spec_code_cons (taskdelcode (vl++(v' ::nil))) s ||> **  
       p_local OSLInv ct init_lg). 


  
Theorem OSTaskDeletePreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSTaskDeletePre' vl ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSTaskDeletePre : fpre :=
  fun vl ll ct => mkfunasrt (OSTaskDeletePreGood vl ll ct).

Definition OSTaskDeletePost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v' k, 
  (Aie true ** Ais nil ** Acs nil ** Aisr empisr **
     [| logicl = logic_val v' :: logic_code s :: nil |] **
     [| v = Some v' /\ v' = Vint32 k  /\ 
        Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k) (Byte.max_unsigned) |] ** 
   <|| s ||> ** p_local OSLInv ct init_lg). 

Theorem OSTaskDeletePostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSTaskDeletePost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSTaskDeletePost : fpost :=
  fun vl v ll ct => mkfunasrt (OSTaskDeletePostGood vl v ll ct).



Definition OSTaskDelete_spec : fspec:= (OSTaskDeletePre,OSTaskDeletePost,(Tint8, Tint8::nil)).

Definition new_osq_spec_list := 
  (((OSTaskDel, OSTaskDelete_spec) :: nil) ++ osq_spec_list).

Definition new_OS_spec :=  convert_spec new_osq_spec_list.


Definition new_internal_fun_list := 
  ((OSTaskDel_impl :: nil) ++ internal_fun_list) %list.


Definition new_os_internal :=  convert_cfuns new_internal_fun_list.

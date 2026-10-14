Require Import include_frm1.
Require Import NPeano.
Require Import Lia.

Require Import os_code_defs1.
Require Import code_notations1.
Require Import os_ucos_h1.
Require Import abs_op1.

Require Import ifun_taskcreate.
Require Import thread_create. 

Require Import threadcreat.
Require Import ifun_taskdel_spec. 
Require Import ifun_taskdelete.
Require Import thread_cancel.

(*
Definition pthread_cancel_impl :=
Int8u ·pthread_cancel·(⌞thread @ Int8u⌟)··{
  ⌞ ret @ Int8u ⌟;
  
    If (thread′ ==ₑ ′OS_IDLE_PRIO) {
      RETURN ′ESRCH
    };ₛ
    If (thread′ ≥ ′OS_LOWEST_PRIO) {
      RETURN ′ESRCH
    };ₛ    
    ret′ =ᶠ OSTaskDel(·thread′·);ₛ
    If (ret′ !=ₑ ′OS_NO_ERR){
      RETURN ′ESRCH
    };ₛ
    RETURN ′OS_NO_ERR
}·. 
*)

Definition threadcancel_err_idle_prio (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr ESRCH))) /\
      O_opt = Some O1 /\
      (exists v1,
      vl= ((Vint32 v1)::nil)/\
         Int.eq (Int.repr OS_IDLE_PRIO) v1 = true
      )
  end.

Definition threadcancel_err_lowest_prio (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr ESRCH))) /\
      O_opt = Some O1 /\
      (exists v1,
         vl= ((Vint32 v1)::nil)/\
         (Int.ltu (Int.repr OS_LOWEST_PRIO) v1 = true \/ 
         Int.eq (Int.repr OS_LOWEST_PRIO) v1 = true)
      )
  end.


Definition threadcancel_idle_step (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists prio rv,
      vl = (prio :: rv :: nil) /\
      opv = None /\
      (rv = prio /\ O_opt = Some O1 \/
       rv <> prio /\ O_opt = None)
end.

Definition threadcancel_err_ret (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
    opv = Some (Vint32 (Int.repr ESRCH)) /\
    exists  v',
    vl= ( v' :: nil) /\  v' <> Vint32 (Int.repr OS_NO_ERR)
        
  end.
  

Definition threadcancel_succ_ret (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
    opv = Some (Vint32 (Int.repr OS_NO_ERR)) /\
    exists  v',
    vl= ( v' :: nil) /\  v' = Vint32 (Int.repr OS_NO_ERR)        
  end.
  

Definition threadcancel (vl: vallist) :=
  match vl with
  (prio :: rv :: nil) => 
  threadcancel_err_lowest_prio (|prio :: nil|) ??
  threadcancel_err_idle_prio (|prio :: nil|) ??
  (threadcancel_idle_step (|prio :: rv :: nil|) ;; 
  spec_code_cons (taskdelcode (prio::rv::nil))
     (threadcancel_succ_ret (|rv::nil|) ??threadcancel_err_ret (|rv::nil|) 
     ))
  | _ => spec_abort
  end.

Local Open Scope code_scope.

Require Import abs_op1.
Require Import init_spec1.
Require Import inv_prop1.
Require Import hoare_tactics1.
Require Import pure_auto1.
Require Import ucos_pauto1.
Require Import seplog_tactics1.
Require Import seplog_lemmas1.
Require Import sep_cancel_ext1.
Require Import derived_rules1.
Require Import hoare_conseq1.
Require Import ucos_forward1.
Require Import sem_common1.
Local Open Scope code_scope.


Lemma threadcancel_absimp_err_idle_prio:
  forall sch P v1 rv,
    can_change_aop P ->
    Int.eq v1 ($ OS_IDLE_PRIO) = true ->
    absinfer sch
      (<|| threadcancel (Vint32 v1 :: rv :: nil) ||> ** P)
      (<|| END (Some (Vint32 (Int.repr ESRCH))) ||> ** P).
Proof.
  infer_solver 0%nat.
  splits; auto.
  exists v1.
  unfold OS_IDLE_PRIO.
  unfold OS_LOWEST_PRIO.
  int auto.
  unfold OS_IDLE_PRIO. unfold OS_LOWEST_PRIO.
  lia.
Qed.


Lemma threadcancel_absimp_err_lowest_prio:
  forall sch P v1 rv,
    can_change_aop P ->
    (Int.ltu (Int.repr OS_LOWEST_PRIO) v1 = true \/ 
         Int.eq (Int.repr OS_LOWEST_PRIO) v1 = true) ->
    absinfer sch
      (<|| threadcancel (Vint32 v1 :: rv :: nil) ||> ** P)
      (<|| END (Some (Vint32 (Int.repr ESRCH))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.


Lemma threadcancel_absimp_idle_step_abt:
  forall sch P prio rv s,
    can_change_aop P ->
    rv <> prio ->
    absinfer sch
      (<|| threadcancel_idle_step (|prio :: rv :: nil|) ;; s ||> ** P)
      (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate (1 := P).
  can_change_aop_solver.
  eapply absinfer_abt.
  can_change_aop_solver.
  can_change_aop_solver.
  absimp_abt_solver.
  can_change_aop_solver.
  apply absinfer_seq_abt; eauto.
Qed.

Lemma threadcancel_absimp_idle_step:
forall sch P prio rv s,
    can_change_aop P ->
    rv = prio ->
    absinfer sch
    (<|| threadcancel_idle_step (|prio :: rv :: nil|) ;; s ||> ** P)
    (<|| s ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate (1 := P).
  can_change_aop_solver.
  2: apply absinfer_seq_end; eauto.
  infer_solver 0%nat.
Qed.

Lemma threadcancel_absimp_err_ret:
  forall sch P ret s1,
    can_change_aop P ->
    Int.eq ret ($ OS_NO_ERR) = false ->
    absinfer sch
      (<|| s1 ?? threadcancel_err_ret (|Vint32 ret :: nil|) ||> ** P)
      (<|| END (Some (Vint32 (Int.repr ESRCH))) ||> ** P).
Proof.
  infer_solver 1%nat.
  split. auto.
  exists (Vint32 ret).
  splits; auto.
  change OS_NO_ERR with 0 in *.
  unfold not.
  intros.
  assert (forall x y,Vint32 x = Vint32 y -> x = y).
  {
    intros.
    inverts H3;auto.
  }
  apply H3 in H2.
  rewrite H2 in H0.
  invert H0.
Qed.

Open Scope Z_scope.
Lemma threadcancel_absimp_succ_ret:
  forall sch P ret s1,
    can_change_aop P ->
    Int.eq ret ($ OS_NO_ERR) = true ->
    absinfer sch
      (<|| threadcancel_succ_ret (|Vint32 ret :: nil|) ?? s1 ||> ** P)
      (<|| END (Some (Vint32 (Int.repr OS_NO_ERR))) ||> ** P).
Proof.
  infer_solver 0%nat.
  split. auto.
  exists (Vint32 ret).
  splits; auto.
  change OS_NO_ERR with 0 in *.
  assert (forall x y,x = y -> Vint32 x = Vint32 y).
  {
    intros.
    rewrite H2.
    auto.
  }
  apply H2.
  apply Inteq_true_is_Zeq in H0.
  apply ZInteq_imp_Zeq in H0.
  auto.
Qed.



Definition pthreadcancelapi :=
  (threadcancel, (Tint32, Tint32 :: nil)).

Definition new_api_spec_list :=
  ((pthread_cancel, pthreadcancelapi) :: nil) ++ api_spec_list.

Definition new_api_spec :=
  convert_api_spec new_api_spec_list.

Definition new_os_spec :=
  (new_api_spec, GetHPrio).


Require Import ifun_spec1.
Local Open Scope list_scope.


Definition os_spec_list_ext :=
  (((OSTaskDel, OSTaskDelete_spec) :: nil)
   ++ new_osq_spec_list).

Definition os_spec_ext :=
  convert_spec os_spec_list_ext.

Require Import abs_infer_step1.
Require Import ucos_frmaop1.


Definition api_fun_list_new := (pthread_cancel_impl :: nil)%list.
Definition os_api_new := convert_cfuns api_fun_list_new.

Local Ltac sifs := 
  match goal with
    | |- context[if ?e then _ else _] => destruct e; sifs
    | |- _ <> _ => try solve [simpl; intro; tryfalse]
    | _ => idtac
  end.

Lemma PthreadcancelProof:
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api_new pthread_cancel
              (threadcancel, (Tint32, Tint32 :: nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api_new pthread_cancel
              (threadcancel, (Tint32, Tint32 :: nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api_new pthread_cancel = Some (t, d1, d2, s) /\
      {|os_spec_ext, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  hoare_lift_pre Aop.
  do 2 (destruct v'; try apply absabort_rule).

  (* If (thread′ ==ₑ ′OS_IDLE_PRIO) {
      RETURN ′ESRCH
    };ₛ *)
  lzh_hoare_if; pure_auto. 

  hoare abscsq.
  apply noabs_oslinv.

  eapply threadcancel_absimp_err_idle_prio.
  go.
  auto.
 (*  If (thread′ ≥ ′OS_LOWEST_PRIO) {
      RETURN ′ESRCH
    };ₛ *)
  hoare forward.


  lzh_hoare_if; pure_auto.
  destruct LHift_true.


  assert(Int.ltu (Int.repr OS_LOWEST_PRIO) i = true \/ 
  Int.eq (Int.repr OS_LOWEST_PRIO) i = true).
  {
    clear -H.
    int auto; change OS_LOWEST_PRIO  with 63; lia.
  }


  hoare abscsq.
  apply noabs_oslinv.
  eapply threadcancel_absimp_err_lowest_prio.
  go.
  auto.
  
  hoare forward.


  assert(Int.unsigned i < 63).
  {
    clear -Hif_false Hif_false0.
    change OS_IDLE_PRIO with 63 in *.
    change OS_LOWEST_PRIO with 63 in *.  
    int auto.
    invert Hif_false0.
    int auto.
    int auto.
  }

  clear Hif_false Hif_false0.

  assert (Hrv_prio: v = Vint32 i \/ v <> Vint32 i) by tauto.
  destruct Hrv_prio as [Hrv_prio | Hrv_prio].

  2: {
    eapply abscsq_rule.
    apply noabs_oslinv.
  
    eapply absinfer_trans.
    eapply absinfer_choice2.
    can_change_aop_solver.
    2: pauto.
    can_change_aop_solver.
  
    eapply absinfer_trans.
    eapply absinfer_choice2.
    can_change_aop_solver.
    2: pauto.
    can_change_aop_solver.

    eapply threadcancel_absimp_idle_step_abt.
    go.
    auto.
    eapply absinfer_eq.
    apply absabort_rule.
  }

  eapply abscsq_rule.
  apply noabs_oslinv.

  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver.
  2: pauto.
  can_change_aop_solver.

  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver.
  2: pauto.
  can_change_aop_solver.

  eapply threadcancel_absimp_idle_step.
  go.
  auto.
  eapply absinfer_eq.

  (*  ret′ =ᶠ OSTaskDel(·thread′·);ₛ *)
  hoare forward.
  { clear - H. pure_auto. int auto. }
  {
    sep cancel Aie.
    sep cancel Ais.
    sep cancel Acs.
    sep cancel Aisr.
    sep cancel Aop.
    sep pauto.
  }  
  go.
  {
    unfold retpost. introv Hsat.
    inverts Hsat; sep auto.
    sep destruct H0. sep split in H0.
    destruct H3. rewrite H3. auto.
  }
  {
    clear - Hrv_prio H.
    inverts Hrv_prio. pure_auto. int auto.
  }
  {
    intros.
    sep destruct H0.
    eexists init_lg.
    sep pauto.
  }
  {
    intros.
    sep destruct H0.
    eexists init_lg.
    sep pauto.
  }

  (*     If (ret′ !=ₑ ′OS_NO_ERR){
      RETURN ′ESRCH
    };ₛ *)

  hoare unfold.
  hoare forward.
  {
    clear - H5.
    apply Zle_imp_le_bool in H5.
    rewrite H5. auto.
  }
  {
    clear.
    pure_auto.
  }
  {
    clear.
    pure_auto.
  }

  
  hoare_split_pure_all.
  hoare unfold.
  
  inverts H0.
  hoare abscsq.
  apply noabs_oslinv.
  eapply threadcancel_absimp_err_ret.
  go.
  clear - H2. unfold OS_NO_ERR in *. int auto.
  destruct H2.
  pure_auto.

  hoare forward.

  eapply hoare_disj_afalseP_l_pre.
  hoare_split_pure_all.
  inverts H0.
  hoare abscsq.
  apply noabs_oslinv.
  eapply threadcancel_absimp_succ_ret.
  go.
  clear - H2. unfold OS_NO_MORE_TCB in *. int auto.
  destruct H2; tryfalse.
  change OS_NO_ERR with 0. lia.
  change OS_NO_ERR with 0. lia.
  
  hoare forward.

Qed.
  
  




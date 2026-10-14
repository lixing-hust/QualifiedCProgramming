Require Import include_frm1.
Require Import NPeano.
Require Import os_code_defs1.
Require Import code_notations1.
Require Import os_ucos_h1.
Require Import abs_op1.

Require Import ifun_taskcreate.
Require Import thread_create1. 

Fixpoint Get_struct (l: (list (addrval * type * (list val)))) (a: addrval) : (option (addrval * type * (list val))) :=
  match l with 
  | nil => None
  | (ad, t, vl ) :: l' =>
    match (beq_tid ad a) with
     | true  => Some (a, t, vl )
     | false => Get_struct l' a 
    end  
end.  

Definition threadcrt_einval
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists attr,
      vl = attr :: nil /\
        (attr = Vnull \/
          exists a,
            attr = Vptr a /\ 
              (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\
      opv = (Some (Vint32 (Int.repr EINVAL))) /\
      O_opt = Some O1 
  end.

Definition threadcrt_check_attr_type
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
   | (opv, O_opt) =>
      exists attr evheap t l,
        vl = ((Vptr attr) :: nil) /\
        cmpaddr Clt userAddrStart attr = true /\
        cmpaddr Cle attr userAddrEnd = true /\
        get O1 abspthattrid = Some (abspthattr evheap) /\
        opv = None /\
        (Get_struct evheap attr = Some (attr, pthread_attr_t, l) /\
         O_opt = Some O1 \/
         ((Get_struct evheap attr = None \/
           Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_attr_t)) /\ O_opt = None)
  end.

Definition threadcrt_sched_priority_lowest_gt
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap a b n,
      vl = ((Vptr attr) :: nil) /\
      cmpaddr Clt userAddrStart attr = true /\
      cmpaddr Cle attr userAddrEnd = true /\
      get O1 abspthattrid = Some (abspthattr evheap) /\
      Get_struct evheap attr = Some (attr, pthread_attr_t, a :: b :: Vint32 n :: nil) /\
      Int.ltu (Int.repr OS_LOWEST_PRIO) n = true /\
      opv = Some (Vint32 (Int.repr EINVAL)) /\
      O_opt = Some O1 
  end.

Definition threadcrt_eagain
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap a b n,
      vl = ((Vptr attr) :: nil) /\
      cmpaddr Clt userAddrStart attr = true /\
      cmpaddr Cle attr userAddrEnd = true /\
      get O1 abspthattrid = Some (abspthattr evheap) /\
      Get_struct evheap attr = Some (attr, pthread_attr_t, a :: b :: Vint32 n :: nil) /\
      Int.ltu (Int.repr OS_LOWEST_PRIO) n = false /\
      opv = (Some (Vint32 (Int.repr EAGAIN))) /\
      O_opt = Some O1 
  end.

Definition threadcrt_get_sched_priority (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap a b prio rv_prio,
      vl = ((Vptr attr) :: rv_prio :: nil) /\
      get O1 abspthattrid = Some (abspthattr evheap) /\
      Get_struct evheap attr = Some (attr, pthread_attr_t, a :: b :: Vint32 prio :: nil) /\
      opv = None /\
      (rv_prio = Vint32 prio /\ O_opt = Some O1 \/
       rv_prio <> Vint32 prio /\ O_opt = None)
end.

Definition threadcrt_no_more_tcb
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos,
      vl = (Vint32 pos :: nil) /\
      Int.eq pos (Int.repr OS_NO_MORE_TCB) = true /\
      opv = (Some (Vint32 (Int.repr EAGAIN))) /\
      O_opt = Some O1 
  end.

Definition threadcrt_succ
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos,
      vl = (Vint32 pos :: nil) /\
      Int.eq pos (Int.repr OS_NO_MORE_TCB) = false /\
      opv = (Some (Vint32 (Int.repr OS_NO_ERR))) /\
      O_opt = Some O1 
  end.

Definition threadcrt (vl: vallist) :=
  match vl with
  (V_thread :: V_attr :: routine :: arg :: prio :: rv :: nil) => 
  threadcrt_einval (|V_attr :: nil|) ??
  threadcrt_einval (|V_thread :: nil|) ??
  threadcrt_einval (|routine :: nil|) ??
  threadcrt_check_attr_type (|V_attr :: nil|) ??
  threadcrt_sched_priority_lowest_gt (|V_attr :: nil|) ??
  threadcrt_eagain (|V_attr :: nil|) ??
    (threadcrt_get_sched_priority (|V_attr :: prio :: nil|) ;; 
     spec_code_cons (taskcrecode (routine :: arg :: prio :: rv :: nil))
     (threadcrt_no_more_tcb (|rv :: nil|) ??
      threadcrt_succ (|rv :: nil|)))
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

(* From: abs_infer_abt *)
Ltac absimp_abt_solver := 
  unfolds; intros;
  eexists; exgamma;
  (first [ splits ; 
            [ try simpl_subst_gamma;
              try hmstep_call_consturctor; try eapply spec_prim_step_abt; 
              [ unfolds; repeat eexists; subst;
                try (eapply absdata_elim; eauto with abst_solver_base); try eauto 
              | try apply map_join_emp 
              |  repeat hmstep_call_consturctor
              | .. ]
            | sep remember (1 :: nil)%nat; simpl in *; simpljoin ;
            do 6 eexists ; splits ; try eauto ; eapply change_aop_rule; eauto]
          | idtac] ).

Lemma absinfer_seq1:
  forall (p : asrt) (s1 : absop)  (s2 : spec_code) (s1' : absop) (sc : ossched),
    can_change_aop p ->
    sc ⊢  <|| s1 ||>  ** p ⇒  <|| s1' ||>  ** p ->
    sc ⊢  <|| s1;; s2 ||>  ** p ⇒  <|| s1';; s2 ||>  ** p.
Proof.
  intros.
  eapply absinfer_seq; try eauto.
Qed.

Lemma threadcrt_absimp_attrerr:
  forall sch V_thread V_attr routine arg prio rv P,
    can_change_aop P ->
    (V_attr = Vnull \/
     (exists a,
         V_attr = Vptr a /\
         (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true))) ->
    absinfer sch 
             (<|| threadcrt (V_thread :: V_attr :: routine :: arg :: prio :: rv :: nil) ||>  ** P)
             (<|| END (Some (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma threadcrt_absimp_threaderr:
  forall sch V_thread V_attr arg routine prio rv P,
    can_change_aop P ->
    (V_thread = Vnull \/
     (exists a,
         V_thread = Vptr a /\
         (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true))) ->
    absinfer sch 
             (<|| threadcrt (V_thread :: V_attr :: routine :: arg :: prio :: rv :: nil) ||>  ** P)
             (<|| END (Some (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma threadcrt_absimp_argerr:
  forall sch V_thread V_attr routine arg prio rv P,
    can_change_aop P ->
    (routine = Vnull \/
     (exists a,
         routine = Vptr a /\
         (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true))) ->
    absinfer sch 
             (<|| threadcrt (V_thread :: V_attr :: routine :: arg :: prio :: rv :: nil) ||>  ** P)
             (<|| END (Some (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 2%nat.
Qed.

Lemma threadcrt_absimp_check_type:
  forall sch V_thread attr routine arg prio rv evheap l t P,
    cmpaddr Clt userAddrStart attr = true ->
    cmpaddr Cle attr userAddrEnd = true ->
    (Get_struct evheap attr = None \/
    (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_attr_t)) ->
    can_change_aop P ->
    absinfer sch
        (<|| threadcrt (V_thread :: Vptr attr :: routine :: arg :: prio :: rv :: nil) ||> ** 
          HPthreadAttr evheap ** P)
        (<|| ABORT ||> ** 
          HPthreadAttr evheap ** P).
Proof.
  intros.
  unfold threadcrt.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver.
  instantiate (1 := HPthreadAttr evheap ** P).
  can_change_aop_solver.
  auto.

  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver.
  instantiate (1 := HPthreadAttr evheap ** P).
  can_change_aop_solver.
  auto.

  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver.
  instantiate (1 := HPthreadAttr evheap ** P).
  can_change_aop_solver.
  auto.

  eapply absinfer_trans.
  eapply absinfer_choice1.
  can_change_aop_solver.
  instantiate (1 := HPthreadAttr evheap ** P).
  can_change_aop_solver.
  auto.

  apply absinfer_abt.
  can_change_aop_solver.
  can_change_aop_solver. 
  absimp_abt_solver.
  can_change_aop_solver.
Qed.

Lemma threadcrt_absimp_sched_priority_lowest_gt:
  forall sch V_thread attr routine arg prio rv a b n x evheap v'16 v'17 v'18 tid P,
    can_change_aop P ->
    cmpaddr Clt userAddrStart attr = true ->
    cmpaddr Cle attr userAddrEnd = true ->
    Get_struct evheap attr = Some (attr, pthread_attr_t, a :: b :: Vint32 n :: nil) ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) n = true ->
    absinfer sch
      (<|| threadcrt (V_thread :: Vptr attr :: routine :: arg :: prio :: rv :: nil) ||> **
        HECBList v'16 **
        HTCBList v'17 **
        HTime v'18 **
        HCurTCB tid **
        APATTRStructs evheap **
        LV os_code_defs1.attr @ pthread_attr_t ∗ |-> Vptr x **
        HPthreadAttr evheap ** P)
      (<|| END (Some (Vint32 (Int.repr EINVAL))) ||> **
        HECBList v'16 **
        HTCBList v'17 **
        HTime v'18 **
        HCurTCB tid **
        APATTRStructs evheap **
        LV os_code_defs1.attr @ pthread_attr_t ∗ |-> Vptr x **
        HPthreadAttr evheap ** P).
Proof.
  infer_solver 4%nat.
Qed.

Lemma threadcrt_absimp_eagain:
  forall sch V_thread attr routine arg prio rv a b n evheap v'16 v'17 v'18 v'19 v'26 tid x P,
    can_change_aop P ->
    cmpaddr Clt userAddrStart attr = true ->
    cmpaddr Cle attr userAddrEnd = true ->
    Get_struct evheap attr = Some (attr, pthread_attr_t, a :: b :: Vint32 n :: nil) ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) n = false ->
    absinfer sch
      (<|| threadcrt (V_thread :: Vptr attr :: routine :: arg :: prio :: rv :: nil) ||> **
        HECBList v'16 **
        HTCBList v'17 **
        HTime v'18 **
        HCurTCB tid **
        APATTRStructs evheap **
        LV os_code_defs1.attr @ pthread_attr_t ∗ |-> Vptr x **
        PV v'19 @ char_t |-> v'26 **
        HPthreadAttr evheap ** P)
      (<|| END (Some (Vint32 (Int.repr EAGAIN))) ||> **
        HECBList v'16 **
        HTCBList v'17 **
        HTime v'18 **
        HCurTCB tid **
        APATTRStructs evheap **
        LV os_code_defs1.attr @ pthread_attr_t ∗ |-> Vptr x **
        PV v'19 @ char_t |-> v'26 **
        HPthreadAttr evheap ** P).
Proof.
  infer_solver 5%nat.
Qed.

Lemma threadcrt_absimp_no_more_tcb:
  forall sch P ret s1,
    can_change_aop P ->
    Int.eq ret ($ OS_NO_MORE_TCB) = true ->
    absinfer sch
      (<|| threadcrt_no_more_tcb (|Vint32 ret :: nil|) ?? s1 ||> ** P)
      (<|| END (Some (Vint32 (Int.repr EAGAIN))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma threadcrt_absimp_succ:
  forall sch P ret s1,
    can_change_aop P ->
    Int.eq ret ($ OS_NO_MORE_TCB) = false ->
    absinfer sch
      (<|| s1 ?? threadcrt_succ (|Vint32 ret :: nil|) ||> ** P)
      (<|| END (Some (Vint32 (Int.repr OS_NO_ERR))) ||> ** P).
Proof.
  infer_solver 1%nat.
Qed.

Definition pthreadcrtapi :=
  (threadcrt, (Tint32, Tptr Tint32 :: Tptr pthread_attr_t :: Tptr Void :: Tptr Void :: nil)).

Definition new_api_spec_list :=
  ((pthread_create, pthreadcrtapi) :: nil) ++ api_spec_list.

Definition new_api_spec :=
  convert_api_spec new_api_spec_list.

Definition new_os_spec :=
  (new_api_spec, GetHPrio).

Require Import useraddrchk_spec_proof1.
Require Import ifun_spec1.
Local Open Scope list_scope.

Definition os_spec_list_ext :=
  (((OSTaskCreate, OSTaskCreate_spec) ::
    (UserAddrCheck, UserAddrCheck_spec) :: nil)
   ++ new_osq_spec_list).

Definition os_spec_ext :=
  convert_spec os_spec_list_ext.

Require Import abs_infer_step1.
Require Import ucos_frmaop1.
  
Definition api_fun_list_new := (pthread_create_impl :: nil)%list.
Definition os_api_new := convert_cfuns api_fun_list_new.


Require Import hoare_tactics1.
Require Import pure_auto1.
Require Import ucos_pauto1.
Require Import sep_auto1.
Require Import seplog_tactics1.
Require Import seplog_lemmas1.
Require Import sep_cancel_ext1.
Require Import derived_rules1.
Require Import hoare_conseq1.
Require Import ucos_forward1. (*change*)
Require Import math_auto1.

Require Import sem_lab1.
Require Import symbolic_lemmas1.
Require Import sem_common1.

Ltac sep_lift_context_in H trm :=
  match type of H with
    | _ |= ?P =>
      match find_match_context P trm with
         | none _ => idtac 1 "no such term in the Hsat"; fail 1
         | some ?a => sep lifts (a::nil)%nat in H
      end
  end.

Ltac hoare_lift_pre trm :=
  match goal with
    | |-  {| _, _, _, _, _, _ |} |- _ {{ _ //\\ _ }} _ {{ _ //\\ _ }} =>
      let s := fresh in
      let H := fresh in
      eapply backward_rule3;
       [ intros s H; sep_lift_context_in H trm; exact H | idtac ]
    | |-  {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
      let s := fresh in
      let H := fresh in
      eapply backward_rule1;
       [ intros s H; sep_lift_context_in H trm; exact H | idtac ]
  end.

(* From OSTimeTickPure *)
Lemma beq_tid_true_eq :
  forall t1 t2, beq_tid t1 t2 = true -> t1 = t2.
Proof.
  intros.
  unfolds in H.
  destruct t1, t2.
  apply andb_true_iff in H.
  destruct H.
  rewrite beq_pos_Pos_eqb_eq in H.
  apply Peqb_true_eq in H.
  pose proof Int.eq_spec i i0.
  rewrite H0 in H1.
  substs; auto.
Qed.

(* From Mutex_common_v1 *)
Lemma APATTRStructs_unfold: 
  forall s (evheap : list (addrval * type * list val)) x vl P,
    s |= APATTRStructs evheap **
         LV os_code_defs1.attr @ pthread_attr_t ∗ |-> Vptr x ** P->
         Get_struct evheap x = Some (x, pthread_attr_t, vl) ->
    s |= EX evh1 evh2,
         Astruct x pthread_attr_t vl ** 
         [|struct_type_vallist_match pthread_attr_t vl|] **
         LV os_code_defs1.attr @ pthread_attr_t ∗ |-> Vptr x **
         [| evheap =(evh1 ++ (x, pthread_attr_t, vl) :: evh2) |] **
         APATTRStructs evh1 ** APATTRStructs evh2 ** 
         [|Get_struct evh1 x = None|] ** P.
Proof.
  introv Hsat Hget.
  inductions evheap. tryfalse. 
  destruct a. destruct p.
  rename evheap into evheap'.
  destruct t;
  try eapply astar_l_afalse_elim in Hsat;  tryfalse.
  unfold Get_struct in Hget.

  destruct (os_inv1.beq_addrval a x) eqn: eq1.
  eexists. instantiate (1:= nil).
  exists evheap'.
  sep normal in Hsat.
  change (nil ++ (x, pthread_attr_t, vl) :: evheap') with ((x, pthread_attr_t, vl) :: evheap').

  sep pauto.
  eapply beq_tid_true_eq in eq1.
  inverts Hget.
  fold APATTRStructs in Hsat.
  sep pauto.
  unfold1 APATTRStructs in Hsat.
  sep pauto.
  inverts Hget. 
  eapply beq_tid_true_eq in eq1. subst a.
  auto. 
  unfold1 APATTRStructs in Hsat.
  inverts Hget. sep pauto.
  fold Get_struct in Hget.
  unfold1 APATTRStructs in Hsat.
  sep normal in Hsat.
  sep lifts (3::4::nil)%nat in Hsat.
  eapply IHevheap in Hsat; eauto.
  sep pauto.
  3: {
    change ((a, STRUCT i ­{ d }­, l) :: ( x0 ++ (x, pthread_attr_t, vl) :: x1)) with
            (((a, STRUCT i ­{ d }­, l) :: x0 ) ++ (x, pthread_attr_t, vl) :: x1).
    eauto.
  }
  simpl APATTRStructs at 1.
  sep pauto.
  unfold1 Get_struct.
  rewrite eq1, H1.
  auto.
Qed.

Lemma APATTRStructs_succ_imp_alt :
  forall s a vll P, 
    s |= APATTRStructs (a :: vll) ** P ->
    s |= APATTRStructs (a :: nil) ** APATTRStructs vll ** P.
Proof.
  intros.
  sep pauto.
  simpl APATTRStructs in *;
  destruct a. destruct p. destruct t;
  try (eapply astar_l_afalse_intro; sep pauto).
  sep pauto.
Qed.

Lemma APATTRStructs_succ :
  forall s a vll, 
    s |= APATTRStructs (a::nil) ** APATTRStructs vll -> 
    s |= APATTRStructs (a :: vll).
Proof.
  intros.
  simpl APATTRStructs in *;
  destruct a. destruct p. destruct t;
  try (eapply astar_l_afalse_elim in H; sep pauto).
  sep pauto.
Qed.

Lemma APATTRStructs_compose :
  forall vll1 vll2 s, 
    s |= APATTRStructs vll1 ** APATTRStructs vll2 -> 
    s |= APATTRStructs (vll1 ++ vll2).
Proof.
  induction vll1; intros.
  simpl APATTRStructs in H.
  sep pauto.
  eapply APATTRStructs_succ_imp_alt in H.
  change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)).
  eapply APATTRStructs_succ.
  sep pauto.
Qed.

Lemma APATTRStructs_fold: 
  forall s x evheap P,
    s |= EX vl evh1 evh2,
           Astruct x pthread_attr_t vl ** 
           [|struct_type_vallist_match pthread_attr_t vl|] **
           LV os_code_defs1.attr @ pthread_attr_t ∗ |-> Vptr x **
           [| evheap =(evh1 ++ (x, pthread_attr_t, vl) :: evh2) |] **
           APATTRStructs evh1 ** APATTRStructs evh2 ** P->
    s |=  APATTRStructs evheap **
          LV os_code_defs1.attr @ pthread_attr_t ∗ |-> Vptr x ** P.
Proof.
  intros.
  unfold1 APATTRStructs.
  sep pauto.
  apply APATTRStructs_compose.
  sep pauto.
  unfold1 APATTRStructs.
  destruct pthread_attr_t; tryfalse.
  sep pauto.
Qed.


Lemma PthreadcrtProof:
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api_new pthread_create
              (threadcrt, (Tint32, Tptr Tint32 :: Tptr pthread_attr_t :: Tptr Void :: Tptr Void :: nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api_new pthread_create
              (threadcrt, (Tint32, Tptr Tint32 :: Tptr pthread_attr_t :: Tptr Void :: Tptr Void :: nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api_new pthread_create = Some (t, d1, d2, s) /\
      {|os_spec_ext, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  hoare_lift_pre Aop.
  do 3 (destruct v'; try apply absabort_rule).

  rename x1 into attr.
  rename x2 into thread.
  rename x0 into routine.
  rename v into prio.
  rename x into arg.
  rename v0 into rv.

  rename H1 into Hptr_arg.
  rename H2 into Hptr_routine.
  rename H3 into Hptr_attr.
  rename H4 into Hptr_thread.

  hoare forward.
  pure_auto.
  pure_auto.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aop.
  eauto.

  simpl.
  inverts Hptr_attr. eauto.
  inverts H6. eauto.
  go.
  unfold retpost. introv Hsat.
  inverts Hsat; sep auto.
  pure_auto.

  intros. do 3 destruct H. sep pauto.
  instantiate (1 := init_lg); sep pauto.
  sep pauto. instantiate (1 := init_lg); sep pauto.

  intros. sep pauto. instantiate (1 := init_lg); sep pauto.

  hoare unfold.
  eapply backward_rule1.
  intros.
  apply disj_split in H.
  eauto.
  apply disj_rule.

  (* x = 0 *)
  hoare unfold.
  inverts H1.
  hoare forward.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply threadcrt_absimp_attrerr.
  go.
  {
    destruct H. invert H. eauto.
    do 2 destruct H. inverts H. eauto.
  }
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  change (Int.eq ($ 0) ($ 0)) with true. simpl.
  hoare unfold. destruct H0; tryfalse.
  
  (* x != 0 *)
  hoare unfold.
  inverts H1.
  hoare forward.
  change (Int.eq ($ 1) ($ 0)) with false. simpl.
  hoare unfold. tryfalse.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  clear H.

  hoare forward.
  pure_auto.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aop.
  eauto.
  {
    inverts Hptr_thread. eauto.
    inverts H8. right. simpl. eauto.
  }
  go.
  unfold retpost. introv Hsat.
  inverts Hsat; sep auto.
  pure_auto.
  
  {
    intros. do 3 destruct H; sep pauto.
    instantiate (1 := init_lg); sep pauto.
    instantiate (1 := init_lg); sep pauto.
  }
  intros. destruct H. sep pauto.
  instantiate (1 := init_lg). sep pauto.
  
  hoare unfold.
  eapply backward_rule1.
  intros.
  apply disj_split in H.
  eauto.
  eapply disj_rule.

  (* y = 0 *)
  hoare unfold.
  inverts H1.
  hoare forward.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  apply threadcrt_absimp_threaderr.
  go.
  {
    destruct H. invert H. eauto.
    do 2 destruct H. inverts H. eauto.
  }
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  change (Int.eq ($ 0) ($ 0)) with true. simpl.
  hoare unfold. destruct H0; tryfalse.
  
  (* y != 0 *)
  hoare unfold.
  inverts H1.
  hoare forward.
  change (Int.eq ($ 1) ($ 0)) with false. simpl.
  hoare unfold. tryfalse.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  clear H.

  hoare forward.
  pure_auto.
  pure_auto.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aop.
  eauto.
  {
    inverts Hptr_routine. eauto.
    inverts H10. right. simpl. eauto.
  }
  go.
  unfold retpost. introv Hsat.
  inverts Hsat; sep auto.
  pure_auto.

  {
    intros. do 3 destruct H; sep pauto.
    instantiate (1 := init_lg); sep pauto.
    instantiate (1 := init_lg); sep pauto.
  }
  intros. destruct H. sep pauto.
  instantiate (1 := init_lg). sep pauto.

  hoare unfold.
  eapply backward_rule1.
  intros.
  apply disj_split in H.
  eauto.
  eapply disj_rule.

  (* z = 0 *)
  hoare unfold.
  inverts H1.
  hoare forward.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  apply threadcrt_absimp_argerr.
  go.
  {
    destruct H. invert H. eauto.
    do 2 destruct H. inverts H. eauto.
  }
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  change (Int.eq ($ 0) ($ 0)) with true. simpl.
  hoare unfold. destruct H0; tryfalse.

  (* z != 0 *)
  hoare unfold.
  inverts H1.
  hoare forward.
  change (Int.eq ($ 1) ($ 0)) with false. simpl.
  hoare unfold. tryfalse.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  clear H.

  (* ENTER CRITICAL *)
  hoare forward prim.
  hoare unfold.
  unfold APthreadAttr.
  hoare normal pre.

  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lift_pre abspthattr.
  hoare_lift_pre Aop.

  rename v'25 into evheap.
  assert (Hg: Get_struct evheap x = None \/ exists t, Get_struct evheap x = Some t).
  {
    intros.
    assert ( exists t, Get_struct evheap x = t) by eauto.
    destruct H1.
    destruct x2.
    right; eauto.
    left; eauto.
  }

  destruct Hg.
  (* Remove the case Get_struct evheap x = None *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply threadcrt_absimp_check_type; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.

  (* Show the first entry of Get_struct evheap x is x *)
  destruct H1 as (ev & Hget).
  destruct ev as (a & l).
  destruct a as (a & t).
  assert (Ha: a = x).
  {
    clear - Hget.
    inductions evheap.
    simpl in Hget; tryfalse.
    unfold1 Get_struct in Hget.
    destruct a. destruct p.
    destruct (os_inv1.beq_addrval a x) eqn: eq1.
    eapply TcbMod.option2val in Hget.
    inverts Hget; auto.
    apply IHevheap in Hget.
    auto.  
  }
  subst a.

  (* Check type *)
  assert (Ht: t = pthread_attr_t \/ t <> pthread_attr_t) by tauto.
  destruct Ht as [Hteq | Htneq].
  2: {
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply threadcrt_absimp_check_type; eauto.
    pure_auto.
    eapply absinfer_eq.
    eapply absabort_rule.
  }

  (* Expand APATTRStructs *)
  eapply backward_rule1.
  intros.
  eapply APATTRStructs_unfold. eauto. sep pauto.
  sep cancel APATTRStructs.
  sep pauto.
  instantiate (1 := l).
  rewrite Hteq in Hget.
  auto.
  hoare_split_pure_all.
  simpljoin.

  (* Figure out type of sched_priority *)
  lets Hl': struct_type_vallist_match_elim_3 H1.
  destruct Hl' as (stackaddr & stacksize & sched_priority & Hl).
  subst l.
  assert (exists v, sched_priority = Vint32 v). {
    destruct sched_priority; eauto; simpl in H1; destructs H1; tryfalse.
  }
  destruct H8.

  hoare forward.
  pure_auto.

  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  eapply APATTRStructs_fold.
  sep pauto.

  hoare abscsq.
  apply noabs_oslinv.
  eapply threadcrt_absimp_sched_priority_lowest_gt; eauto.
  go.
  { rewrite Hget. rewrite H8. eauto. }
  { clear - H10. destruct H10. pure_auto. }

  (* EXIT_CRITICAL *)
  hoare forward prim.
  unfold APthreadAttr.
  sep pauto.
  go.
  (* RETURN ′ EINVAL *)
  hoare forward.

  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.

  assert ( Int.unsigned x2 < 64 ). {
    clear - H10. unfold OS_LOWEST_PRIO in H10.
    destruct H10; int auto.
  }

  assert (rule_type_val_match OS_TCB ∗ (nth_val' (Z.to_nat (Int.unsigned x2)) v'9) = true). {
    apply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite H14. clear - H8. int auto.
  }

  assert ( nth_val' (Z.to_nat (Int.unsigned x2)) v'9 = Vnull \/
    exists p, nth_val' (Z.to_nat (Int.unsigned x2)) v'9 = Vptr p ). {
    unfold rule_type_val_match in H15.
    destruct (nth_val' (Z.to_nat (Int.unsigned x2)) v'9); eauto.
    tryfalse. tryfalse.
  }

  hoare forward.
  
  {
    apply array_type_vallist_match_imp_rule_type_val_match; eauto.
    clear - H8 H14.
    rewrite H14.
    int auto.
  }
  {
    destruct H16. rewrite H16. simpl. eauto.
    destruct H16. rewrite H16. simpl. destruct x3. eauto.
  }
  {
    destruct H16. rewrite H16. simpl. eauto.
    destruct H16. rewrite H16. simpl. destruct x3. simpl. eauto.
  }
  
  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  eapply APATTRStructs_fold.
  sep pauto.
  sep cancel APATTRStructs.
  sep cancel APATTRStructs.
  sep pauto.

  hoare abscsq.
  apply noabs_oslinv.
  eapply threadcrt_absimp_eagain.
  go.
  go.
  go.
  rewrite Hget.
  eauto.
  {
    clear - H10.
    unfolds OS_LOWEST_PRIO.
    destruct H10; int auto.
  }

  (* EXIT_CRITICAL *)
  hoare forward prim.
  unfold APthreadAttr.
  sep pauto.
  unfold AOSTCBPrioTbl.
  sep pauto.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep pauto.
  auto.
  auto.
  go.
  (* RETURN ′ EAGAIN *)
  hoare forward.

  (* prio′ =ₑ attr′→sched_priority;ₛ *)
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  hoare forward.
  hoare unfold.
  clear H17.

  eapply backward_rule1.
  intros.
  eapply APATTRStructs_fold.
  sep pauto.
  sep cancel APATTRStructs.
  sep cancel APATTRStructs.
  sep pauto.


Set Nested Proofs Allowed.
Lemma threadcrt_absimp_get_sched_prio_abt:
  forall sch P evheap attr a b prio rv_prio s,
    can_change_aop P ->
    Get_struct evheap attr = Some (attr, pthread_attr_t, a :: b :: Vint32 prio :: nil) ->
    rv_prio <> Vint32 prio ->
    absinfer sch
      (<|| threadcrt_get_sched_priority (|Vptr attr :: rv_prio :: nil|) ;; s ||> **
           HPthreadAttr evheap ** P)
      (<|| ABORT ||> **
           HPthreadAttr evheap ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate (1 := HPthreadAttr evheap ** P).
  can_change_aop_solver.
  eapply absinfer_abt.
  can_change_aop_solver.
  can_change_aop_solver.
  absimp_abt_solver.
  can_change_aop_solver.
  apply absinfer_seq_abt; eauto.
  can_change_aop_solver.
  can_change_aop_solver.
Qed.

Lemma threadcrt_absimp_get_sched_prio:
  forall sch P evheap attr a b prio rv_prio s,
    can_change_aop P ->
    Get_struct evheap attr = Some (attr, pthread_attr_t, a :: b :: Vint32 prio :: nil) ->
    rv_prio = Vint32 prio ->
    absinfer sch
    (<|| threadcrt_get_sched_priority (|Vptr attr :: rv_prio :: nil|) ;; s ||> **
         HPthreadAttr evheap ** P)
    (<|| s ||> **
         HPthreadAttr evheap ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate (1 := (HPthreadAttr evheap ** P)).
  can_change_aop_solver.
  2: apply absinfer_seq_end; eauto.
  infer_solver 0%nat.
  can_change_aop_solver.
  can_change_aop_solver.
Qed.

  Require Import seplog_pattern_tacs1.
  hoare_lifts_trms_pre (Aop, abspthattrid).
  assert (Hrv_prio: prio = Vint32 x2 \/ prio <> Vint32 x2) by tauto.
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

    eapply threadcrt_absimp_get_sched_prio_abt.
    go.
    rewrite Hget.
    go.
    go.
    eapply absinfer_eq.
    apply absabort_rule.
  }

  subst prio.
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

  eapply threadcrt_absimp_get_sched_prio.
  can_change_aop_solver.
  rewrite Hget.
  eauto.
  eauto.
  eapply absinfer_eq.

  (* EXIT_CRITICAL *)
  hoare forward prim.
  unfold AOSTCBPrioTbl.
  unfold APthreadAttr.
  sep pauto.
  sep cancel 3%nat 1%nat.
  sep cancel 3%nat 1%nat.
  sep pauto.
  go.
  go.
  go.
  
  (* ret ′ =ᶠ OSTaskCreate (·start_routine ′, arg ′, prio ′·);ₛ *)
  hoare forward.
  pure_auto.
  { clear - H8. pure_auto. int auto. }
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
    sep destruct H17. sep split in H17.
    destruct H19. rewrite H19. auto.
  }
  {
    clear - Hptr_arg H8.
    inverts Hptr_arg. pure_auto. int auto.
    destruct H. rewrite H. pure_auto. int auto. 
  }
  {
    intros.
    sep destruct H17.
    eexists init_lg.
    sep pauto.
  }
  {
    intros.
    sep destruct H17.
    eexists init_lg.
    sep pauto.
  }

  hoare unfold.
  hoare forward.
  {
    clear - H20 H21.
    apply Zle_imp_le_bool in H21.
    rewrite H21. auto.
  }
  {
    clear.
    pure_auto.
  }

  hoare_split_pure_all.
  hoare unfold.
  
  inverts H17.
  hoare abscsq.
  apply noabs_oslinv.
  eapply threadcrt_absimp_no_more_tcb.
  go.
  clear - H18. unfold OS_NO_MORE_TCB in *. int auto.
  hoare forward.

  eapply hoare_disj_afalseP_l_pre.
  hoare_split_pure_all.
  inverts H17.
  hoare abscsq.
  apply noabs_oslinv.
  eapply threadcrt_absimp_succ.
  go.
  clear - H18. unfold OS_NO_MORE_TCB in *. int auto.
  destruct H18; tryfalse.

  hoare forward.
  Unshelve.
  auto.
  exact Tnull.
Qed.

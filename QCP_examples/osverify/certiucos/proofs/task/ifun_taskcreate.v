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
(*
Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
*)

Fixpoint spec_code_cons (s1:spec_code) (s2:spec_code) :=
  match s1 with
  | sp1 ?? sp2 => (spec_code_cons sp1 s2) ?? (spec_code_cons sp2 s2)
  | sp1 ;; sp2 => sp1 ;; (spec_code_cons sp2 s2)
  | _ => s1 ;; s2
  end.

Definition taskcre_err_prio_invalid (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr PRIO_ERR))) /\
      (exists v1 v2 v3 v',
         vl= (v1::v2::(Vint32 v3)::v'::nil)/\
         (Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true) /\
            (v' = (Vint32 (Int.repr PRIO_ERR)) /\   O_opt= Some O1 \/
              v' <> (Vint32 (Int.repr PRIO_ERR)) /\ O_opt = None)
      )
  end.

Definition taskcre_err_prio_already_exists (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr OS_PRIO_EXIST))) /\
      (
        exists v1 v2 v3 v',
          vl= (v1::v2::(Vint32 v3)::v'::nil) /\
         (Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = false) /\
          ( v' = (Vint32 (Int.repr OS_PRIO_EXIST)) /\   O_opt= Some O1 \/
             v' <> (Vint32 (Int.repr OS_PRIO_EXIST)) /\ O_opt = None))
  end.


Definition taskcre_err_no_more_tcb (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      opv = (Some (Vint32 (Int.repr OS_NO_MORE_TCB))) /\ 
        (         
        exists v1 v2 v3 v',
          vl= (v1::v2::(Vint32 v3)::v'::nil) /\
         (Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = false) /\ 
         ( v' = (Vint32 (Int.repr OS_NO_MORE_TCB)) /\ O_opt = Some O1
         \/ v' <> (Vint32 (Int.repr OS_NO_MORE_TCB)) /\ O_opt = None)) 
  end.

Definition taskcre_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      exists  v',
      vl= ( v' :: nil)/\
          (
            opv = Some (Vint32 (Int.repr NO_ERR)) /\
             ( v' = (Vint32 (Int.repr NO_ERR)) /\ O_opt=Some O1
                \/ v' <> (Vint32 (Int.repr NO_ERR)) /\ O_opt = None))
                 
end.
(*
      Definition taskcre_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
        match rst with
          | (opv, O_opt) =>
            exists v1 v2 v3 v',
            vl= (v1::v2::(Vint32 v3):: v' :: nil)/\
                (
                  opv = None /\
                  Int.lt (Int.repr OS_LOWEST_PRIO) v3 = false /\ 
                  exists tls,
                    OSAbstMod.get O1 abtcblsid = Some (abstcblist tls) /\
                    (~ exists t' st msg, TcbMod.get tls t'= Some (v3,st,msg)) /\
                    exists tls' t',
                      TcbMod.join tls (TcbMod.sig t' (v3, rdy, Vnull)) tls'/\ 
                      ( v' = (Vint32 (Int.repr NO_ERR)) /\ O_opt=Some (OSAbstMod.set O1 abtcblsid (abstcblist tls'))
                      \/ v' <> (Vint32 (Int.repr NO_ERR)) /\ O_opt = None))
                       
            end.
*)
(*
Definition scrt (vl : vallist) :=
  match vl with
    | v1 :: v2 :: (Vint32 v3) :: v' :: nil => spec_crt v1 v2 (Vint32 v3)
    | _ => spec_done None
  end.
*)
Definition scrt (vl : vallist) :=
  match vl with
    | v1 :: v2 :: (Vint32 v3) :: v' :: nil => spec_crt v1 v2 (Vint32 v3);; isched;; taskcre_succ (|v'::nil|)
    | _ => spec_done None
  end.

(*
Definition taskcre_succ' (vl: vallist) :=
   ( scrt vl ;; (* taskcre_succ  (|vl|) ;;*) isched ;; ASSERT (fun O => v' = (Some (Vint32 (Int.repr NO_ERR)))) (Some (Vint32 (Int.repr NO_ERR)))).   
*)
Definition taskcrecode (vl : vallist) :=
  ASSERT (fun O => length vl =4);; 
 ( taskcre_err_prio_invalid (|vl|) ?? taskcre_err_prio_already_exists (|vl|) ?? taskcre_err_no_more_tcb (|vl|) ??  scrt (vl)).

Definition OSTaskCreatePre' (vl:vallist) (logicl:list logicvar) ct :=
  EX s v', 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr **
       [| logicl = logic_val v' :: logic_code s :: nil |] ** <|| spec_code_cons (taskcrecode (vl++(v' ::nil))) s ||> **  
       p_local OSLInv ct init_lg). 

Theorem OSTaskCreatePreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSTaskCreatePre' vl ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSTaskCreatePre : fpre :=
  fun vl ll ct => mkfunasrt (OSTaskCreatePreGood vl ll ct).

Definition OSTaskCreatePost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v' k, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr **
       [| logicl = logic_val v' :: logic_code s :: nil |] **
       [| v = Some v' /\ v' = Vint32 k  /\ 
          Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k) (Byte.max_unsigned) |] ** 
     <|| s ||> ** p_local OSLInv ct init_lg). 

Theorem OSTaskCreatePostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSTaskCreatePost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition OSTaskCreatePost : fpost :=
  fun vl v ll ct => mkfunasrt (OSTaskCreatePostGood vl v ll ct).

Require Import List.
Require Import ifun_spec1.

Local Open Scope code_scope.
Local Open Scope list_scope.

Definition OSTaskCreate_spec : fspec:= (OSTaskCreatePre,OSTaskCreatePost,(Tint8, Tptr Tvoid ::Tptr Tvoid::Tint8::nil)).

Definition new_osq_spec_list := 
  (((OSTaskCreate, OSTaskCreate_spec) :: nil) ++ osq_spec_list).


Definition new_OS_spec :=  convert_spec new_osq_spec_list.

(* modified/new in os_program.v *)
Require Import os_program1.
Require Import os_task1.

Definition new_internal_fun_list := 
  ((OSTaskCreate_impl :: nil) ++ internal_fun_list) %list.

Definition new_os_internal :=   convert_cfuns new_internal_fun_list.

(* new lemmas in absop_rules *)
Require Import abs_infer_step1.
Require Import ucos_frmaop1.
Require Import seplog_lemmas1.
Require Import seplog_tactics1.


Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

Ltac simpl_sat H := unfold sat in H; fold sat in H; simpl substmo in H; simpl getmem in H; simpl getabst in H; simpl empst in H.
(*

*)

Lemma absimp_taskcre_prio_invalid_normal:
  forall P v1 v2 v3 v' sch,
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true ->
    v' <> Vint32 (Int.repr OS_PRIO_INVALID) ->    
    can_change_aop P ->
    absimp sch ( <|| taskcre_err_prio_invalid (|v1 :: v2 :: (Vint32 v3) :: v' :: nil|) ||> ** P) ( <||ABORT ||> ** P).
Proof.
  introv  Hv' Hchaop  Hv3.
  unfold absimp.
  introv Hsat.
  simpl_sat Hsat.
  simpljoin1.
  simpl in H3. subst gamma.
  exists O. exists spec_abort.
  unfold taskcre_err_prio_invalid.
  split. 

  eapply spec_stepS. 

  instantiate (1:=O). instantiate (1:=ABORT). 
  constructors.
  splits.
  eauto.
  eexists.   eexists.   eexists.   eexists.  splits; eauto. 
  instantiate (1:=O). instantiate (1:=emp). 
  apply join_tactics1.veg.Unnamed_thm.
  constructors.
  simpl. exists x x0. exists (get_mem (get_smem s)). 
  eexists. exists O. exists O. 
  splits. eauto. eauto. eauto.
  instantiate (1:=empenv). 
  apply join_tactics1.veg.Unnamed_thm.
  splits; eauto. 
  unfold emposabst. auto.
  eapply change_aop_rule; eauto.
Qed.

Lemma absinfer_seq1:
  forall (p : asrt) (s1 : absop)  (s2 : spec_code) (s1' : absop) (sc : ossched),
                   can_change_aop p ->
                   sc ⊢  <|| s1 ||>  ** p ⇒  <|| s1' ||>  ** p ->
                   sc ⊢  <|| s1;; s2 ||>  ** p ⇒  <|| s1';; s2 ||>  ** p.
Proof.
intros.
eapply absinfer_seq; try eauto.
Qed.


Lemma absimp_taskcre_prio_invalid:
  forall P v1 v2 v3 v' sch,
    v' =  Vint32 (Int.repr OS_PRIO_INVALID) ->    
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true ->
    absinfer sch ( <||taskcrecode (v1 :: v2 :: (Vint32 v3) ::v' :: nil) ||> ** P)
             ( <|| END (Some(Vint32 (Int.repr OS_PRIO_INVALID)))||> ** P).
Proof.
  intros.
  unfold taskcrecode.
  simpl.
  eapply absinfer_trans.
  eapply absinfer_seq; try(eauto).
  eapply absinfer_assert_cont; try(eauto).
  eapply absinfer_trans.
  eapply absinfer_seq_end; try (eauto).
  infer_solver 0%nat.
Qed.

Lemma absimp_taskcre_prio_invalid':
  forall P v1 v2 v3 v' sch s,
    v' =  Vint32 (Int.repr OS_PRIO_INVALID) ->    
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true ->
    absinfer sch ( <|| spec_code_cons (taskcrecode (v1 :: v2 :: (Vint32 v3) ::v' :: nil)) s ||> ** P)
             ( <||s||> ** P).
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

Lemma taskcre_absimp_prio_invalid_abt:
  forall P v1 v2 v3 v' sch,
    v' <>  Vint32 (Int.repr OS_PRIO_INVALID) ->    
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true ->
    absinfer sch ( <||taskcrecode (v1 :: v2 :: (Vint32 v3) ::v' :: nil)||> ** P)
             ( <|| ABORT ||> ** P).
Proof.
  intros.
  unfold taskcrecode.
  simpl.
  eapply absinfer_trans.
  eapply absinfer_seq; try(eauto).
  eapply absinfer_assert_cont; try(eauto).
  eapply absinfer_trans.
  eapply absinfer_seq_end; try (eauto).
  eapply absinfer_trans.
  eapply absinfer_choice1; try eauto.
  eapply absinfer_abt; try eauto.
  unfolds; intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.  
  unfolds.
  split. eauto.
  exists v1 v2 v3 v'.
  subst.
  splits; eauto.
  apply map_join_emp.
  repeat hmstep_call_consturctor.
  simpl in *.
  simpljoin.
  do 6 eexists.
  splits ; try eauto.
  eapply change_aop_rule; eauto.
Qed.

Lemma taskcre_absimp_prio_invalid_abt':
  forall P v1 v2 v3 v' sch s,
    v' <>  Vint32 (Int.repr OS_PRIO_INVALID) ->    
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true ->
    absinfer sch ( <||spec_code_cons (taskcrecode (v1 :: v2 :: (Vint32 v3) ::v' :: nil)) s||> ** P)
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
  exists v1 v2 v3 v'.
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

Lemma absimp_taskcre_err_prio_already_exists_normal:
  forall P v1 v2 v3 v' sch,
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = false ->
    v' <>  Vint32 (Int.repr OS_PRIO_EXIST) ->    
    can_change_aop P ->
    absimp sch ( <|| taskcre_err_prio_already_exists (|v1 :: v2 :: (Vint32 v3) :: v' :: nil|) ||> ** P) ( <||ABORT ||> ** P).
Proof.
 introv  Hv' Hchaop  Hv3.
  unfold absimp.
  introv Hsat.
  simpl_sat Hsat.
  simpljoin1.
  simpl in H3. subst gamma.
  exists O. exists spec_abort.
  unfold taskcre_err_prio_already_exists.
  split. 

  eapply spec_stepS. 

  instantiate (1:=O). instantiate (1:=ABORT). 
  constructors.
  splits.
  eauto.
  eexists.   eexists.   eexists.   eexists.  splits; eauto. 
  instantiate (1:=O). instantiate (1:=emp). 
  apply join_tactics1.veg.Unnamed_thm.
  constructors.
  simpl. exists x x0. exists (get_mem (get_smem s)). 
  eexists. exists O. exists O. 
  splits; eauto.
  instantiate (1:=empenv). 
  apply join_tactics1.veg.Unnamed_thm.
  splits; eauto. 
  unfold emposabst. auto.
  eapply change_aop_rule; eauto.
Qed.

Lemma absimp_taskcre_err_prio_already_exists:
  forall P v1 v2 v3 v' sch,
    v' = Vint32 (Int.repr OS_PRIO_EXIST) ->    
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = false ->
    absinfer sch ( <||taskcrecode (v1 :: v2 :: (Vint32 v3) ::v' :: nil) ||> ** P)
             ( <|| END (Some(Vint32 (Int.repr OS_PRIO_EXIST)))||> **P).
Proof.
  intros.
  unfold taskcrecode.
  simpl.
  eapply absinfer_trans.
  eapply absinfer_seq; try eauto.

  eapply absinfer_assert_cont; try(eauto).
  eapply absinfer_trans.
  eapply absinfer_seq_end; try eauto.
  infer_solver 1%nat.
Qed.

Lemma absimp_taskcre_err_prio_already_exists':
  forall P v1 v2 v3 v' sch s,
    v' = Vint32 (Int.repr OS_PRIO_EXIST) ->    
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = false ->
    absinfer sch ( <||spec_code_cons (taskcrecode (v1 :: v2 :: (Vint32 v3) ::v' :: nil)) s ||> ** P)
             ( <||s||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq; try eauto.
  eapply absinfer_assert_cont; try(eauto).
  eapply absinfer_trans.
  eapply absinfer_seq_end; try eauto.
  infer_solver 1%nat.
Qed.

Lemma taskcre_absimp_err_prio_already_exists_abt:
  forall P v1 v2 v3 v' sch,
    v' <> Vint32 (Int.repr OS_PRIO_EXIST) ->    
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = false ->
    absinfer sch ( <||taskcrecode (v1 :: v2 :: (Vint32 v3) ::v' :: nil)||> ** P)
             ( <|| ABORT ||> ** P).
Proof.
  intros.
  unfold taskcrecode.
  simpl.
  eapply absinfer_trans.
  eapply absinfer_seq; try(eauto).
  eapply absinfer_assert_cont; try(eauto).
  eapply absinfer_trans.
  eapply absinfer_seq_end; try (eauto).
  eapply absinfer_trans.
  eapply absinfer_choice2.
   try eauto.
   try eauto.
   try eauto.
  eapply absinfer_trans.
  eapply absinfer_choice1;  try eauto.
  eapply absinfer_abt; try eauto.
  unfolds; intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.  
  unfolds.
  split. eauto.
  exists v1 v2 v3 v'.
  subst.
  splits; eauto.
  apply map_join_emp.
  repeat hmstep_call_consturctor.
  simpl in *.
  simpljoin.
  do 6 eexists.
  splits ; try eauto.
  eapply change_aop_rule; eauto.
Qed.

Lemma taskcre_absimp_err_prio_already_exists_abt':
  forall P v1 v2 v3 v' sch s,
    v' <> Vint32 (Int.repr OS_PRIO_EXIST) ->    
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = false ->
    absinfer sch ( <||spec_code_cons (taskcrecode (v1 :: v2 :: (Vint32 v3) ::v' :: nil)) s||> ** P)
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
  exists v1 v2 v3 v'.
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

Lemma absimp_taskcre_err_no_more_tcb_normal:
  forall P v1 v2 v3 v' sch,
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = false ->
    v' <> Vint32 (Int.repr OS_NO_MORE_TCB) ->    
    can_change_aop P ->
    absimp sch ( <|| taskcre_err_no_more_tcb (|v1 :: v2 :: (Vint32 v3) :: v' :: nil|) ||> ** P) ( <||ABORT ||> ** P).
Proof.
  introv  Hv' Hchaop  Hv3.
  unfold absimp.
  introv Hsat.
  simpl_sat Hsat.
  simpljoin1.
  simpl in H3. subst gamma.
  exists O. exists spec_abort.
  unfold taskcre_err_no_more_tcb.
  split. 

  eapply spec_stepS. 

  instantiate (1:=O). instantiate (1:=ABORT). 
  constructors.
  splits.
  eauto.
  do 4 eexists.  eauto. 
  instantiate (1:=O). instantiate (1:=emp). 
  apply join_tactics1.veg.Unnamed_thm.
  constructors.
  simpl. exists x x0. exists (get_mem (get_smem s)). 
  eexists. exists O. exists O. 
  splits; eauto.
  instantiate (1:=empenv). 
  apply join_tactics1.veg.Unnamed_thm.
  splits; eauto. 
  unfold emposabst. auto.
  eapply change_aop_rule; eauto.
Qed.

Lemma absimp_taskcre_err_no_more_tcb:
  forall P v1 v2 v3 v' sch,
    v' = Vint32 (Int.repr OS_NO_MORE_TCB) ->    
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = false ->
    absinfer sch ( <||taskcrecode (v1 :: v2 :: (Vint32 v3) ::v' :: nil) ||> ** P)
             ( <|| END (Some(Vint32 (Int.repr OS_NO_MORE_TCB)))||> ** P).
Proof.
  intros.
  unfold taskcrecode.
  simpl.
  eapply absinfer_trans.
  eapply absinfer_seq; try(eauto).
  eapply absinfer_assert_cont; try(eauto).
  eapply absinfer_trans.
  eapply absinfer_seq_end; try (eauto).
  infer_solver 2%nat.
Qed.

Lemma absimp_taskcre_err_no_more_tcb':
  forall P v1 v2 v3 v' sch s,
    v' = Vint32 (Int.repr OS_NO_MORE_TCB) ->    
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = false ->
    absinfer sch ( <||spec_code_cons (taskcrecode (v1 :: v2 :: (Vint32 v3) ::v' :: nil)) s ||> ** P)
             ( <||s||> ** P).
Proof.
  intros.
  simpl.
  eapply absinfer_trans.
  eapply absinfer_seq; try eauto.
  eapply absinfer_assert_cont; try(eauto).
  eapply absinfer_trans.
  eapply absinfer_seq_end; try (eauto).
  infer_solver 2%nat.
Qed.

Lemma taskcre_absimp_err_no_more_tcb_abt:
  forall P v1 v2 v3 v' sch,
    v' <> Vint32 (Int.repr OS_NO_MORE_TCB) ->    
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = false ->
    absinfer sch ( <||taskcrecode (v1 :: v2 :: (Vint32 v3) ::v' :: nil)||> ** P)
             ( <|| ABORT ||> ** P).
Proof.
  intros.
  unfold taskcrecode.
  simpl.
  eapply absinfer_trans.
  eapply absinfer_seq; try(eauto).
  eapply absinfer_assert_cont; try(eauto).
  eapply absinfer_trans.
  eapply absinfer_seq_end; try (eauto).
  eapply absinfer_trans.
  eapply absinfer_choice2.
   try eauto.
   try eauto.
   try eauto.
  eapply absinfer_trans.
  eapply absinfer_choice2;  try eauto.
  eapply absinfer_trans.
  eapply absinfer_choice1;  try eauto.
  eapply absinfer_abt; try eauto.
  unfolds; intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.  
  unfolds.
  split. eauto.
  exists v1 v2 v3 v'.
  subst.
  eauto.
  apply map_join_emp.
  repeat hmstep_call_consturctor.
  simpl in *.
  simpljoin.
  do 6 eexists.
  splits ; try eauto.
  eapply change_aop_rule; eauto.
Qed.

Lemma taskcre_absimp_err_no_more_tcb_abt':
  forall P v1 v2 v3 v' sch s,
    v' <> Vint32 (Int.repr OS_NO_MORE_TCB) ->    
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = false ->
    absinfer sch ( <||spec_code_cons (taskcrecode (v1 :: v2 :: (Vint32 v3) ::v' :: nil)) s||> ** P)
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
  exists v1 v2 v3 v'.
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

Lemma absimp_taskcre_succ:
  forall P v' sch s ,
    v' = Vint32 (Int.repr NO_ERR) ->    
    can_change_aop P ->
    (* Int.lt ($ 63) v3 = false ->
     * (* OSAbstMod.get O abtcblsid = Some (abstcblist tls) -> *)
     * ~ (exists t' st msg, TcbMod.get tls t' = Some (v3, st, msg)) ->
     * (exists t', TcbMod.join tls (TcbMod.sig t' (v3, rdy, Vnull)) tls' )-> *)
    absinfer sch ( <|| taskcre_succ (|v'::nil|);; s ||> ** P)
             (<|| s ||> **  P).

Proof. 
  intros.
  infer_solver 0%nat.
Qed.


Lemma absimp_taskcre_succ':
  forall P v1 v2 v3 v' sch s,
    can_change_aop P ->
    (*v' = Vint32 (Int.repr NO_ERR) -> *)
    (* Int.lt ($ 63) v3 = false ->
     * (* OSAbstMod.get O abtcblsid = Some (abstcblist tls) -> *)
     * ~ (exists t' st msg, TcbMod.get tls t' = Some (v3, st, msg)) ->
     * (exists t', TcbMod.join tls (TcbMod.sig t' (v3, rdy, Vnull)) tls' )-> *)
    absinfer sch ( <|| spec_code_cons (taskcrecode (v1 :: v2 :: (Vint32 v3) :: v' :: nil)) s ||> ** P)
             (<|| spec_code_cons (scrt (v1 :: v2 :: (Vint32 v3) :: v' :: nil)) s ||> ** P).

Proof.

  intros.
  simpl.
  eapply absinfer_trans.
  eapply absinfer_seq; try eauto.

  eapply absinfer_assert_cont; try eauto.
  eapply absinfer_trans.
  eapply absinfer_seq_end; try eauto.

  infer_branch 3%nat.
  eapply absinfer_eq.
Qed.

Lemma taskcre_absimp_succ_abt:
  forall P v' sch s,
    can_change_aop P ->
    v' <> Vint32 (Int.repr NO_ERR) ->
    absinfer sch ( <|| taskcre_succ (|v'::nil|);; s ||> ** P)
      ( <|| ABORT ||> ** P).
Proof.
intros.
eapply absinfer_trans.
eapply absinfer_seq; try(eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
eapply absinfer_seq_abt; try eauto.
Qed.

(*
Lemma absimp_taskcre_succ':
  forall P v1 v2 v3 v' sch s,
    can_change_aop P ->
    (* Int.lt ($ 63) v3 = false ->
     * (* OSAbstMod.get O abtcblsid = Some (abstcblist tls) -> *)
     * ~ (exists t' st msg, TcbMod.get tls t' = Some (v3, st, msg)) ->
     * (exists t', TcbMod.join tls (TcbMod.sig t' (v3, rdy, Vnull)) tls' )-> *)
    absinfer sch ( <|| spec_code_cons (taskcrecode (v1 :: v2 :: (Vint32 v3) :: v' :: nil)) s ||> ** P)
             (<|| scrt (v1 :: v2 :: (Vint32 v3) :: v' :: nil) ;;  isched ;; (END Some (Vint32 (Int.repr NO_ERR))) ||> ** P).

Proof. 
*)
Require Import abs_op1.
Require Import init_spec1.
Require Import inv_prop1. (*change*)
Require Import hoare_tactics1.
Require Import pure_auto1.
Require Import ucos_pauto1.
Require Import seplog_tactics1.
Require Import seplog_lemmas1.
Require Import sep_cancel_ext1.
Require Import derived_rules1.
Require Import hoare_conseq1.
Require Import ucos_forward1. (*change*)
Require Import sem_common1. (*delete unused Require Import absop_rules*)
Local Open Scope code_scope.
(*Require Import linv_solver.
Require Import new_inv.*)

(*
s

*)


Lemma OSTaskCreate_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI new_os_internal OSTaskCreate
                  vl logicl OSTaskCreatePre ct->
      Some r =
      BuildRetI new_os_internal OSTaskCreate vl logicl OSTaskCreatePost ct->
      exists t d1 d2 s,
        new_os_internal OSTaskCreate = Some (t, d1, d2, s) /\
        {|new_OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  hoare unfold.

  hoare forward.
  math simpls.
  destruct ( Int.ltu ($ OS_LOWEST_PRIO) i); simpl; intro; tryfalse.
  rename v'1 into opv.
  change ((x1 :: x0 :: Vint32 i :: nil) ++ opv :: nil) with (x1 :: x0 :: Vint32 i  :: opv :: nil).
  assert (Hopv: opv = Vint32 (Int.repr OS_PRIO_INVALID) \/ opv <>Vint32 (Int.repr OS_PRIO_INVALID)) by tauto.
  destruct Hopv. 
  subst.

  hoare unfold.

  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskcre_prio_invalid'.

  auto.
  can_change_aop_solver.
  unfold OS_LOWEST_PRIO in *.
  int auto.

  hoare forward.
  unfold  OS_PRIO_INVALID, OS_LOWEST_PRIO in *.
  pure_auto; int auto.

  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply taskcre_absimp_prio_invalid_abt'.
  auto.
  can_change_aop_solver.
  unfold OS_LOWEST_PRIO in *.
  int auto.
  eapply absabort_rule.

  hoare forward.
  hoare unfold.
  
  hoare forward prim.
  hoare normal pre.
  hoare unfold.
  assert (Int.unsigned i < 64).
  clear -H.

  unfold OS_LOWEST_PRIO in *.
  int auto.

  destruct H;  simpl in H; tryfalse.
  clear H.
  assert (   rule_type_val_match OS_TCB ∗ (nth_val' (Z.to_nat (Int.unsigned i)) v'7) = true).
  apply symbolic_lemmas1.array_type_vallist_match_imp_rule_type_val_match.
  rewrite H8.
  clear -H9; mauto.
  auto.

  hoare forward.
  math simpls.
  auto.
  unfolds in H.
  destruct ( nth_val' (Z.to_nat (Int.unsigned i)) v'7 ); tryfalse.
  simpl.
  intro; tryfalse.

  simpl.
  destruct a.
  intro; tryfalse.
  instantiate (1 := Afalse).
  Focus 2.
  hoare forward.
  hoare unfold.


  rename v'1 into opv.
  change ((x1 :: x0 :: Vint32 i :: nil) ++ opv :: nil) with (x1 :: x0 :: Vint32 i  :: opv :: nil).
  assert (Hopv: opv = Vint32 (Int.repr OS_PRIO_EXIST) \/ opv <>Vint32 (Int.repr OS_PRIO_EXIST)) by tauto.
  destruct Hopv. 
  subst.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskcre_err_prio_already_exists'.
  auto.
  can_change_aop_solver.
  unfold OS_LOWEST_PRIO in *.
  int auto.

  hoare forward prim.
  unfold AOSTCBPrioTbl.
  sep pauto.
  go.
  hoare forward.
  unfold  OS_PRIO_EXIST, OS_LOWEST_PRIO in *.
  pure_auto; int auto.

  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply taskcre_absimp_err_prio_already_exists_abt'.
  auto.
  can_change_aop_solver.
  unfold OS_LOWEST_PRIO in *.
  int auto.
  eapply absabort_rule.

  hoare unfold.
  hoare_assert_pure (   array_type_vallist_match Int8u v'13/\ length v'13 = ∘ OS_RDY_TBL_SIZE ) .
  unfold AOSRdyTblGrp in H13.
  unfold AOSRdyTbl in H13.
  sep normal in H13.
  sep split in H13.
  auto.
  hoare_split_pure_all.
  rename H13 into somehyp.
  protect somehyp.
  assert ((nth_val' (Z.to_nat (Int.unsigned i)) v'7) = Vnull).
  remember (nth_val' (Z.to_nat (Int.unsigned i)) v'7).
  destruct H.
  auto.
  simpljoin.
  rewrite H in *.
  simpl in *.
  destruct x; simpl in *.
  tryfalse.
  clear H10 H11 H12.
  hoare unfold.
  unfold AOSTCBList.
  hoare unfold.
  hoare forward.
  math simpls.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Aisr.
  sep cancel Acs.
  sep cancel AOSTCBFreeList.
  sep cancel Aop.
  sep cancel AOSRdyTblGrp.
  sep cancel 9%nat 1%nat.
  sep cancel 3%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  eauto.
  eauto.
  go.
  math simpl.
  clear -H9 l.
  unfold OS_LOWEST_PRIO in l.
  int auto.
  go.
  apply retpost_tcbinitpost.

  math simpl.
  clear -H1 H15.
  change Byte.max_unsigned with 255 in H15.
  lia.

  repeat intro.
  sep normal in H15.
  sep destruct H15.
  sep lift 6%nat in H15.
  disj_asrt_destruct H15.
  sep normal in H15.
  sep destruct H15.
  sep eexists.
  sep cancel p_local.
  simpl; auto.

  sep normal in H15.
  sep destruct H15.
  sep eexists.
  sep cancel p_local.
  simpl; auto.

  linv_solver.

  hoare unfold.
  hoare lift 6%nat pre.
  eapply backward_rule1.
  intro.
  intros.
  eapply disj_star_elim_disj in H15.
  eauto.
  hoare forward.
  hoare unfold.
  inverts H18.
  (* no more tcb *)
  rename v'1 into opv.
  change ((x1 :: x0 :: Vint32 i :: nil) ++ opv :: nil) with (x1 :: x0 :: Vint32 i  :: opv :: nil).
  assert (Hopv: opv = Vint32 (Int.repr OS_NO_MORE_TCB) \/ opv <>Vint32 (Int.repr OS_NO_MORE_TCB)) by tauto.
  destruct Hopv. 
  subst.

  hoare forward.
 
  hoare unfold.
  false.
  change (Int.eq ($ OS_NO_MORE_TCB) ($ OS_NO_ERR)) with false in *.
  simpl in *.
  apply H18; auto.
  hoare unfold.

  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskcre_err_no_more_tcb'.
  auto.
  can_change_aop_solver.
  unfold OS_LOWEST_PRIO, OS_NO_ERR, OS_NO_MORE_TCB in *.
  int auto.
  
  instantiate (1 :=    <|| v'0 ||>  **
                               Aisr empisr **
                               Aie true **
                               Ais nil ** Acs nil ** p_local OSLInv ct init_lg **
 
                               A_dom_lenv
                               ((prio, char_t)
                                  :: (os_code_defs1.pdata, (Void) ∗)
                                  :: (task, (Void) ∗) :: (err, char_t) :: nil) **
                               LV err @ char_t |-> (V$ OS_NO_MORE_TCB)  ** LV prio @char_t |-> Vint32 i **
                               LV os_code_defs1.pdata @ (Void) ∗ |-> x0 ** LV task @ (Void) ∗ |-> x1
              ).

  hoare forward prim.

  sep cancel tcbdllflag.
  sep cancel APthreadAttr.
  (*sep cancel ACNU.*)
  sep cancel A_dom_lenv.
  sep pauto.
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.

  sep pauto.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  sep cancel 1%nat 2%nat.
  sep pauto.
  go.
  go.
  go.
  go.
  go.
  go.
(*
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply taskcre_absimp_err_no_more_tcb_abt'.
   auto.
  can_change_aop_solver.
  unfold OS_LOWEST_PRIO, OS_NO_ERR, OS_NO_MORE_TCB in *.
  int auto.
  eapply absabort_rule.
*)
  hoare forward.
  hoare_split_pure_all.
  false.
  clear -H18.
  simpljoin.
  change (Int.eq ($ OS_NO_MORE_TCB) ($ OS_NO_ERR)) with false in *.
  simpl in *.
  apply H; auto.

  hoare forward.
  unfold  OS_NO_MORE_TCB, OS_NO_ERR, OS_LOWEST_PRIO in *.
  pure_auto; int auto.

  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply taskcre_absimp_err_no_more_tcb_abt'.
   auto.
  can_change_aop_solver.
  unfold OS_LOWEST_PRIO, OS_NO_ERR, OS_NO_MORE_TCB in *.
  int auto.
  eapply absabort_rule.

  hoare unfold.
  inverts H19.

  hoare forward.
  
  hoare unfold.
  Focus 2.
  hoare unfold.
  false.
  clear -H17.
  change (Int.eq ($ OS_NO_ERR) ($ OS_NO_ERR)) with true in H17.
  simpl in H17; destruct H17; tryfalse.

  
  

  hoare abscsq.
  apply noabs_oslinv.
  apply absimp_taskcre_succ'.
  go.

  simpl.
  hoare_assert_pure (GoodLInvAsrt OSLInv).
  unfold p_local in H21.
  unfold LINV in H21.
  sep normal in H21.
  sep split in H21.
  auto.


  
  instantiate (1 :=
  EX x, (
    POST [OS_SchedPost, nil, x,
          logic_code ( taskcre_succ (|v'1 :: nil|);;v'0) :: nil, ct] **
         LV err @ char_t |-> (V$ OS_NO_ERR) **
         LV prio @ char_t |-> Vint32 v'47 **
         LV os_code_defs1.pdata @ (Void) ∗ |-> x0 **
         LV task @ (Void) ∗ |-> x1 **
         A_dom_lenv
         ((prio, char_t)
            :: (os_code_defs1.pdata, (Void) ∗)
            :: (task, (Void) ∗) :: (err, char_t) :: nil)
  )).



  hoare_assert_pure(exists new_tcbmod, TcbJoin v'39 (v'47, rdy, Vnull) v'16 new_tcbmod).

    unfold TcbJoin.
    eexists.
    eapply map_join_comm.

    unfold join; simpl.
    eapply TcbMod.join_sig_set.
    auto.
    intro.
    eapply (join_in_or H11) in H24.
    destruct H23.
    simpljoin.
    unfolds in H27.
    inverts H27.
    destruct H24.
    gen H23.
    eapply sometcblist_lemma.
    instantiate ( 8:= s0).
    sep cancel 13%nat 1%nat.
    sep cancel 14%nat 1%nat.
    eauto.
    eauto.

    gen H23.
    eapply sometcblist_lemma.
    instantiate ( 8:= s0).
    sep cancel 13%nat 1%nat.
    sep cancel 16%nat 1%nat.
    eauto.
    eapply  tcblist_p_hold_for_upd_1.
    eauto.

    simpljoin.
    unfolds in H26.
    inverts H26.

    destruct v'40.
    inverts H28.
    inverts H28.

    destruct H24.
    gen H24.
    eapply sometcblist_lemma.
    instantiate ( 8:= s0).
    sep cancel 13%nat 1%nat.
    sep cancel 14%nat 1%nat.
    eauto.
    eapply  tcblist_p_hold_for_upd_1.
    eauto.

    gen H24.
    eapply sometcblist_lemma.
    instantiate ( 8:= s0).
    sep cancel 13%nat 1%nat.
    sep cancel 16%nat 1%nat.
    eauto.
    eauto.
  hoare_split_pure_all.
  simpljoin.

  eapply backward_rule1.
  intro.
  Set Printing Depth 999.
  intros.

  instantiate (1 :=
  (<||
     spec_crt x1 x0 (Vint32 v'47);;
     isched;;  taskcre_succ (|v'1 :: nil|);;v'0
     ||>  ** 
     (
     HECBList v'15 **
     HTime v'17 **
     AOSTCBFreeList v'29 v'30 **
     AOSMapTbl **
     GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
     (update_nth_val (Z.to_nat (Int.unsigned v'47)) v'33 (Vptr v'39)) **
     G& OSPlaceHolder @ char_t == v'48 **
     PV v'48 @ char_t |-> v'50 **
     GV OSTCBList @ OS_TCB ∗ |-> Vptr v'39 **
     node (Vptr v'39) v'44 OS_TCB_flag **
     PV get_off_addr v'39 ($ 24) @ char_t |-r-> (V$ 1) **
     tcbdllseg v'35 (Vptr v'39) v'37 (Vptr ct) v'41 **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
     tcbdllseg (Vptr ct) v'37 v'38 Vnull v'43 **
     AOSRdyTblGrp
     (update_nth_val (Z.to_nat (Int.unsigned (v'47 >>ᵢ $ 3))) v'31
                     (val_inj
                        (or
                           (nth_val' (Z.to_nat (Int.unsigned (v'47 >>ᵢ $ 3))) v'31)
                           (nth_val' (Z.to_nat (Int.unsigned (v'47&ᵢ$ 7)))
                                     OSMapVallist)))) v'46 **
     p_local OSLInv ct init_lg **
     
     LV err @ char_t |-> (V$ OS_NO_ERR) **
     AOSEventFreeList v'2 **
     AOSQFreeList v'3 **
     AOSQFreeBlk v'4 **
     AECBList v'6 v'5 v'15 v'16 **
     AOSUnMapTbl **
     AOSIntNesting **
     AOSTime (Vint32 v'17) **
     AGVars **
     APthreadAttr v'21 v'22 v'23 **
     tcbdllflag v'35 (v'40 ++ v'11 :: v'12) **
     atoy_inv' **
     LV prio @ char_t |-> Vint32 v'47 **
     LV os_code_defs1.pdata @ (Void) ∗ |-> x0 **
     LV task @ (Void) ∗ |-> x1 **
     A_dom_lenv
     ((prio, char_t)
        :: (os_code_defs1.pdata, (Void) ∗)
        :: (task, (Void) ∗) :: (err, char_t) :: nil)
     ) **
     OSLInv v'39 init_lg **
     HTCBList v'16  **
     HCurTCB ct ** 
     OS [ empisr, false, nil, (true::nil)]  
  )).
  remember (
    HECBList v'15 **
    HTime v'17 **
    AOSTCBFreeList v'29 v'30 **
    AOSMapTbl **
    GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
      (update_nth_val (Z.to_nat (Int.unsigned v'47)) v'33 (Vptr v'39)) **
    G& OSPlaceHolder @ char_t == v'48 **
    PV v'48 @ char_t |-> v'50 **
    GV OSTCBList @ OS_TCB ∗ |-> Vptr v'39 **
    node (Vptr v'39) v'44 OS_TCB_flag **
    PV get_off_addr v'39 ($ 24) @ char_t |-r-> (V$ 1) **
    tcbdllseg v'35 (Vptr v'39) v'37 (Vptr ct) v'41 **
    GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
    tcbdllseg (Vptr ct) v'37 v'38 Vnull v'43 **
    AOSRdyTblGrp
      (update_nth_val (Z.to_nat (Int.unsigned (v'47 >>ᵢ $ 3))) v'31
         (val_inj
            (or (nth_val' (Z.to_nat (Int.unsigned (v'47 >>ᵢ $ 3))) v'31)
               (nth_val' (Z.to_nat (Int.unsigned (v'47&ᵢ$ 7)))
                  OSMapVallist)))) v'46 **
    p_local OSLInv ct init_lg **
    LV err @ char_t |-> (V$ OS_NO_ERR) **
    AOSEventFreeList v'2 **
    AOSQFreeList v'3 **
    AOSQFreeBlk v'4 **
    AECBList v'6 v'5 v'15 v'16 **
    AOSUnMapTbl **
    AOSIntNesting **
    AOSTime (Vint32 v'17) **
    AGVars **
    APthreadAttr v'21 v'22 v'23 **
    tcbdllflag v'35 (v'40 ++ v'11 :: v'12) **
    atoy_inv' **
    LV prio @ char_t |-> Vint32 v'47 **
    LV os_code_defs1.pdata @ (Void) ∗ |-> x0 **
    LV task @ (Void) ∗ |-> x1 **
    A_dom_lenv
      ((prio, char_t)
       :: (os_code_defs1.pdata, (Void) ∗)
       :: (task, (Void) ∗) :: (err, char_t) :: nil)).
  sep lifts (6::8:: nil)%nat.
  eapply elim_a_isr_is_prop.

  sep pauto.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel APthreadAttr.
  sep cancel A_isr_is_prop.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  repeat sep cancel 2%nat 1%nat.
  repeat sep cancel 5%nat 3%nat.
  repeat sep cancel 4%nat 1%nat.

  unfold OSLInv.
  sep pauto.
  unfold init_lg.
  go.
  unfolds.
  left; auto.

  eapply seq_rule.
  eapply cre_rule.
  assumption.
  go.
  unfold p_local.
  go.
  unfold CurTid.
  go.
  unfold LINV.
  go.
  unfold OSLInv.
  go.
  exact H21.
  clear -H4.
  unfolds in H4.
  simpljoin.
  unfolds.
  eauto.
  intro.
  intros.
  split.
  sep get rv.
  clear -H3.
  pauto.
  split.
  sep get rv.
  clear -H2.
  pauto.
  split.
  sep get rv.
  math simpls.
  apply len_lt_update_get_eq.
  rewrite H8.
  bsimplr.
  assumption.
  unfold CurLINV.
  unfold p_local in H26.
  sep pauto.
  sep cancel LINV.
  simpl; auto.
  eapply backward_rule1.
  intro; intros.
  remember (
  HECBList v'15 **
   HTime v'17 **
   AOSTCBFreeList v'29 v'30 **
   AOSMapTbl **
   GAarray OSTCBPrioTbl
     (Tarray OS_TCB ∗ 64)
     (update_nth_val
        (Z.to_nat
           (Int.unsigned v'47)) v'33
        (Vptr v'39)) **
   G& OSPlaceHolder @ char_t == v'48 **
   PV v'48 @ char_t |-> v'50 **
   GV OSTCBList @ OS_TCB ∗
   |-> Vptr v'39 **
   node (Vptr v'39) v'44 OS_TCB_flag **
   PV get_off_addr v'39 flag_off @
   char_t |-r-> (V$ 1) **
   tcbdllseg v'35 (Vptr v'39) v'37
     (Vptr ct) v'41 **
   GV OSTCBCur @ OS_TCB ∗
   |-r-> Vptr ct **
   tcbdllseg (Vptr ct) v'37 v'38
     Vnull v'43 **
   AOSRdyTblGrp
     (update_nth_val
        (Z.to_nat
           (Int.unsigned
              (v'47 >>ᵢ $ 3))) v'31
        (val_inj
           (or
              (nth_val'
                 (Z.to_nat
                    (Int.unsigned
                     (v'47 >>ᵢ $ 3)))
                 v'31)
              (nth_val'
                 (Z.to_nat
                    (Int.unsigned
                     (v'47&ᵢ$ 7)))
                 OSMapVallist))))
     v'46 **
   p_local OSLInv ct init_lg **
   LV err @ char_t
   |-> (V$ OS_NO_ERR) **
   AOSEventFreeList v'2 **
   AOSQFreeList v'3 **
   AOSQFreeBlk v'4 **
   AECBList v'6 v'5 v'15 v'16 **
   AOSUnMapTbl **
   AOSIntNesting **
   AOSTime (Vint32 v'17) **
   AGVars **
   APthreadAttr v'21 v'22 v'23 **
   tcbdllflag v'35
     (v'40 ++ v'11 :: v'12) **
   atoy_inv' **
   LV prio @ char_t |-> Vint32 v'47 **
   LV os_code_defs1.pdata @ 
   (Void) ∗ |-> x0 **
   LV task @ (Void) ∗ |-> x1 **
   A_dom_lenv
     ((prio, char_t)
      :: (os_code_defs1.pdata,
         (Void) ∗)
         :: (task, (Void) ∗)
            :: (err,
               char_t) :: nil)).

  sep lifts (5::7::nil)%nat in H26.
      
  eapply add_a_isr_is_prop in H26.
  subst a.
  eauto.
 
  
  (***** two part ******)
  destruct H23.
    simpljoin.

    unfold tcbls_change_prev_ptr in H27.
    inverts H27.

    
    hoare forward prim.
    unfold AOSTCBPrioTbl.
    unfold AOSTCBList.
    sep pauto.
    sep cancel APthreadAttr.
    sep cancel 1%nat 5%nat.
    sep cancel 1%nat 3%nat.

    instantiate (1 :=     LV err @ char_t
                          |->(V$ OS_NO_ERR) **
                              LV prio @ char_t |-> Vint32 v'47 **
                              LV os_code_defs1.pdata @ 
                              (Void) ∗ |-> x0 **
                              LV task @ (Void) ∗ |-> x1 **
                              A_dom_lenv
                                ((prio, char_t)
                                  :: (os_code_defs1.pdata,
                                    (Void) ∗)
                                    :: (task, (Void) ∗)
                                        :: (err,
                                          char_t) :: nil)).

    sep pauto.
    sep cancel A_dom_lenv.
    Focus 10.
    hoare forward.
    unfold init_lg in H23.
    sep cancel p_local.
    sep cancel Aie.
    sep cancel Ais.
    sep cancel Aisr.
    sep cancel Acs.
    sep cancel Aop.
    eauto.
    unfolds; auto.
    go.
    linv_solver.
    linv_solver.

    unfold AECBList in *.
    sep pauto.
    sep cancel 1%nat 1%nat.
    sep cancel 4%nat 2%nat.
    instantiate (1 := (v'44 ::nil ) ++ nil).
    eapply inv_prop1.tcbdllseg_compose.
    sep cancel 3%nat 2%nat.
    change (  (((v'44 :: nil) ++ nil) ++ update_nth_val 1 v'11 (Vptr v'39) :: v'12) ) with (v'44 :: update_nth_val 1 v'11 (Vptr v'39) :: v'12) .
    unfold tcbdllseg.
    unfold dllseg.
    sep pauto.
    unfold tcbdllflag.
    remember ( update_nth_val 1 v'11 (Vptr v'39) :: v'12).
    unfold1 dllsegflag.
    sep pauto.
    sep cancel 1%nat 1%nat.
    change (nil ++ v'11 :: v'12) with (v'11 :: v'12) in H23.
    unfold tcbdllflag in H23.
    unfold dllsegflag in *.
    sep destruct H23.

    sep pauto.
    unfolds.
    eapply nth_upd_neqrev.
    lia.
    auto.
    clear -H18.
    unfolds in H18.
    simpljoin; auto.
    

    clear -H18.
    unfolds in H18.
    simpljoin; auto.

    clear -H18.
    unfolds in H18.
    simpljoin; auto.
    eapply ecblist_hold_for_add_tcb; eauto.

    

    assert (v'48 <> v'39).
    
      unfold node in H23.
      sep normal in H23.
      sep destruct H23.
      sep split in H23.
      simpljoin.
      inverts H27.
      intro.
      eapply struct_pv_overlap.
      (* ** ac:         Show. *)
      (* ** ac:         Show. *)
      rewrite H27 in H23.
      sep lift 4%nat in H23.
      sep lift 2%nat in H23.
      exact H23.

           
      eapply r_priotbl_p_hold_for_add_tcb; eauto.
      assumption.
(* ** ac:       Print TCBList_P. *)
      instantiate (1:= v'28).
      eapply tcblist_p_hold_for_add_tcb.
      clear -H9.
      int auto.
      clear -somehyp.
      unprotect somehyp.
      tauto.

      clear -somehyp.
      unprotect somehyp.
      tauto.
      assumption.

        clear -H7 H13 H11.
        unfolds in H7.
        simpljoin.
        intro.
        simpljoin.
        assert (get v'16 x = Some (v'47, x0, x1)).
        unfold get,join in *; simpl in *.
        go.

        lets bb: H0 H3.
        simpljoin.
        eapply nth_val_nth_val'_some_eq in H4.
        unfold nat_of_Z in H4.
        rewrite H4 in H13.
        inverts H13.


        instantiate (1:= (sig v'39 (v'47, rdy, Vnull))).
        eapply tcblist_p_hold_for_add_tcb''.
        clear -H9.
        int auto.
        clear -somehyp .
        unprotect somehyp.
        tauto.
        clear -somehyp .
        unprotect somehyp.
        tauto.
          instantiate (1 := v'27).
          intro.
          simpljoin.
          assert (get v'16 x = Some (v'47, x2, x3)).
          unfold get,join,sig in *; simpl in *.
          go.
          eapply not_in_priotbl_no_priotcb; eauto.
        eauto.
        auto.


        eapply TCBList_P_nil_empty in H12.
        subst v'27.
        clear.
        join auto.
        simpl in H12.
        subst v'27.
        assert (v'28 = v'16).
        clear -H11.
        join auto.
        subst v'16.
        assumption.
        unfolds.
        unfolds in H4.
        simpljoin.
        clear -H4 H21.
        do 3 eexists.
        unfold get in *; simpl in *.
        eapply TcbMod.join_get_get_r.
        exact H21.
        eauto.
        
        eapply rh_t_e_p_hold_for_add_tcb.
        eauto.
        eauto.
        go.
        assert (exists t, join (sig v'39 (v'47, rdy, Vnull)) v'27 t ).
        clear -H21 H11.
        unfold TcbJoin in H21.
        join auto.
        simpljoin.

        
        unfold tcbls_change_prev_ptr in H27.
        destruct v'40.
        clear -H23; tryfalse.
        inverts H27.

        hoare forward prim.
        unfold AOSTCBPrioTbl.
        unfold AOSTCBList.
        sep pauto.
        sep cancel APthreadAttr.
        sep cancel 1%nat 5%nat.
        sep cancel 1%nat 3%nat.

        instantiate (1 :=  (LV err @ char_t |-> (V$ OS_NO_ERR) **
                LV prio @ char_t |-> Vint32 v'47 **
                LV os_code_defs1.pdata @ (Void) ∗ |-> x0 **
                LV task @ (Void) ∗ |-> x1 **
                A_dom_lenv
                ((prio, char_t)
                  :: (os_code_defs1.pdata, (Void) ∗)
                  :: (task, (Void) ∗) :: (err, char_t) :: nil))).
        sep pauto.
        sep cancel A_dom_lenv.
        Focus 10.
        hoare forward.
        unfold init_lg in H27.
        sep cancel p_local.
        sep cancel Aie.
        sep cancel Ais.
        sep cancel Aisr.
        sep cancel Acs.
        sep cancel Aop.
        eauto.
        unfolds; auto.
        go.
        linv_solver.
        linv_solver.

        unfold AECBList in *.
        sep pauto.
        sep cancel 1%nat 1%nat.
        sep cancel 4%nat 2%nat.
        instantiate (1 := (v'44 ::nil ) ++ ( (update_nth_val 1 v (Vptr v'39) :: v'40))).
        eapply inv_prop1.tcbdllseg_compose.
        sep cancel 3%nat 2%nat.
        unfold tcbdllseg.
        unfold dllseg.
        sep pauto.
        unfold tcbdllflag.
        change ((v'44 :: nil) ++ update_nth_val 1 v (Vptr v'39) :: v'40) with (v'44 :: update_nth_val 1 v (Vptr v'39) :: v'40) .
        change (((v'44 :: update_nth_val 1 v (Vptr v'39) :: v'40) ++ v'11 :: v'12)) with (v'44 :: ((update_nth_val 1 v (Vptr v'39) :: v'40) ++ v'11 :: v'12)). 
        remember ((update_nth_val 1 v (Vptr v'39) :: v'40) ++ v'11 :: v'12).
  

        unfold1 dllsegflag.
        sep pauto.
        sep cancel 1%nat 1%nat.
        change  ((update_nth_val 1 v (Vptr v'39) :: v'40) ++ v'11 :: v'12) with  (update_nth_val 1 v (Vptr v'39) :: v'40 ++ v'11::v'12).
        change ((v :: v'40) ++ v'11 :: v'12) with (v :: v'40 ++ v'11 :: v'12) in H27.
        unfold tcbdllflag in H27.
        unfold dllsegflag in *.
        sep destruct H27.

        sep pauto.
        unfolds.
        eapply nth_upd_neqrev.
        lia.
        auto.
        clear -H18.
        unfolds in H18.
        simpljoin; auto.
  
        clear -H18.
        unfolds in H18.
        simpljoin; auto.
  
        clear -H18.
        unfolds in H18.
        simpljoin; auto.
        
      
        eapply ecblist_hold_for_add_tcb; eauto.
        
        eapply r_priotbl_p_hold_for_add_tcb; eauto.
          unfold node in H27.
          sep normal in H27.
          sep destruct H27.
          sep split in H27.
          simpljoin.
          inverts H29.
          intro.
          eapply struct_pv_overlap.
          rewrite H29 in H27.
          sep lift 4%nat in H27.
          sep lift 2%nat in H27.
          exact H27.
        assumption.
        instantiate (1:= v'28).

        assert (exists x, nth_val 1 v'11 = Some x).
        clear -H14.
        unfold1 TCBList_P in H14.
        simpljoin.
        unfolds in H2.
        destruct x2; destruct p.
        simpljoin.
        unfolds in H2.
        destruct v'11.
        inverts H2.
        destruct v'11.
        inverts H2.
        eexists.
        simpl.
        eauto.
        simpljoin.
        erewrite (update_eq v'11).

        eapply tcblist_p_hold_for_add_tcb.
        clear -H9.
        int auto.
        clear -somehyp.
        unprotect somehyp.
        tauto.
        clear -somehyp.
        unprotect somehyp.
        tauto.
        assumption.
          clear -H7 H13 H11.
          unfolds in H7.
          simpljoin.
          intro.
          simpljoin.
          assert (get v'16 x = Some (v'47, x0, x1)).
          unfold get,join in *; simpl in *.
          go.
          
          lets bb: H0 H3.
          simpljoin.
          eapply nth_val_nth_val'_some_eq in H4.
          unfold nat_of_Z in H4.
          rewrite H4 in H13.
          inverts H13.
  
        eauto.




        instantiate (1 := x). 
        eapply tcblist_p_hold_for_add_tcb''.
        clear -H9.
        int auto.
        clear -somehyp.
        unprotect somehyp.
        tauto.
        clear -somehyp.
        unprotect somehyp.
        tauto.
          instantiate (1 := v'27).
          intro.
          simpljoin.
          assert (get v'16 x2 = Some (v'47, x3, x4)).
          unfold get,join,sig in *; simpl in *.
          go.
          eapply not_in_priotbl_no_priotcb; eauto.
   
        eapply tcblist_p_hold_for_upd_1.
        eauto.
        eauto.
        go.
        clear -H21 H26 H11.
        unfold TcbJoin in H21.
        join auto.
        unfolds.
        unfolds in H4.
        simpljoin.
        clear -H4 H21.
        do 3 eexists.
        unfold get in *; simpl in *.
        eapply TcbMod.join_get_get_r.
        exact H21.
        eauto.
        
      

        eapply rh_t_e_p_hold_for_add_tcb.
        eauto.
        eauto.
        go.

  hoare forward.
  hoare unfold.
  unfold OS_SchedPost .
  unfold OS_SchedPost'.
  unfold getasrt.
  hoare unfold.
  inverts H21.
  assert (Hopv: v'1 = Vint32 (Int.repr NO_ERR) \/ v'1 <>Vint32 (Int.repr NO_ERR)) by tauto.
  destruct Hopv.

  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskcre_succ.
  go.
  go.

  hoare forward.
  split.
  eauto.
  split.
  eauto.
  unfold  NO_ERR, OS_NO_ERR in *.
  clear -H1.
  pure_auto; int auto.

  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply taskcre_absimp_succ_abt.
  can_change_aop_solver.
  auto.

  eapply absabort_rule.

  hoare_split_pure_all.
  false.
  clear -H17.
  int auto.
  destruct H17; tryfalse.

  Unshelve.
  exact (Afalse).
  exact (Afalse).
Qed.
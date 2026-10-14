Require Import abs_op.
Require Import ifun_spec.
Require Import ucos_include.
Require Import oscore_common. 
Require Import go.
Require Import OSEventTaskRdyPure. 
Require Import new_inv.
Require Import tcblist_setnode_lemmas. 
Require Import sem_lab.
Require Import Lia.

Require Import abs_infer_step.
Require Import ucos_frmaop.
(* Require Import seplog_lemmas. *)
(* Require Import seplog_tactics. *)
(* Require Import q_common. *)
Require Import evauxvar_lemmas.
Require Import evaux_pure.
Require Import freeevtlist_lemmas.
Require Import abs_infer_abt.
Require Import OSQAcceptPure.
Require Import seplog_trm_tacs.

Require Import OSTimeTickPure.
Require Import OSQPostPure.
Require Import OSQPostPure_ext.
Require Import OSTimeDlyPure.
Require Import OSETWaitPure.
(* Require Import OS_EventPostTO_proof. *)
Require Import gjb_common.
Require Import gjb_q_common.
Require Import evtinv_lemmas.
Require Import sem_corecommu.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Open Scope code_scope.
Open Scope int_scope.
Open Scope Z_scope.

(*  引入下面的定义是为了使用 lzh_hoare_if2 *)
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

(* Ltac lzh_destruct_event :=
  match goal with
    | |- context [match ?d with
                    | DMsgQ _ _ _ _ => _
                    | DSem _ => _
                    | DMbox _ => _
                    | DMutex _ _ => _
                  end] => destruct d
    | _ => fail
  end. *)

(* Ltac lzh_unfold_event := 
  try unfold AEventNode;
    try unfold AEventData; 
      try lzh_destruct_event;
      try unfold AMsgData; 
      try unfold AOSQCtr; try unfold AOSQBlk;
    try unfold AOSEvent;
      try unfold AOSEventTbl;
  try unfold node. *)

(* Ltac lzh_unfold_var x := 
   match x with
    | OSQFreeBlk =>  try unfold OSInv; try unfold AOSQFreeBlk;  unfold_qblkfsll 
    | OSQFreeList =>  try unfold OSInv; try unfold AOSQFreeList;  unfold_sll
  (*  | OSEventPtrFreeList => try unfold OSInv; try unfold AOSEventPtrFreeList;  unfold_sll
*)   
    | OSEventFreeList => try unfold OSInv; try unfold AOSEventFreeList; unfold_ecbfsll
    | OSEventList => try unfold OSInv; try unfold AECBList; unfold_msgslleg
    | OSTCBCur => try unfold OSInv; try unfold AOSTCBList;unfold_dll
    | OSTCBList => try unfold OSInv; try unfold AOSTCBList
    | OSRdyTbl => try unfold OSInv; try unfold AOSRdyTblGrp; try unfold AOSRdyTbl
    | OSRdyGrp => try unfold OSInv; try unfold AOSRdyTblGrp; try unfold AOSRdyGrp
    | OSTCBPrioTbl => try unfold OSInv; try unfold AOSTCBPrioTbl
    | OSTime => try unfold OSInv; try unfold AOSTime
    | 999%Z =>  lzh_unfold_event
    | OSIntNesting => try unfold OSInv; try unfold AOSIntNesting
    | OSRunning => try unfold OSInv; try unfold AGVars
    | _ => idtac
   end.  *) 

(* Ltac lzh_unfold_exprlist ls :=  
  match ls with 
    | ((eunop _ ?e) :: ?l)%list => unfold_exprlist ((e::l)%list)
    | ((ebinop _ ?e1 ?e2) :: ?l)%list =>  unfold_exprlist ((e1::e2::l)%list)
    | ((ederef ?e) :: ?l)%list =>  unfold_exprlist ((e::l)%list)
    | ((eaddrof ?e) :: ?l)%list =>  unfold_exprlist ((e::l)%list)
    | ((efield ?e ?id) :: ?l)%list =>  unfold_exprlist ((e::(evar 999%Z) :: l)%list)
    | ((ecast ?e _) :: ?l)%list =>  unfold_exprlist ((e::l)%list)
    | ((earrayelem ?e1 ?e2) :: ?l)%list => unfold_exprlist ((e1::e2::l)%list)
    | ((evar ?x) ::?l)%list => lzh_unfold_var x; unfold_exprlist l
    | (enull:: ?l)%list => unfold_exprlist l
    | ((econst32 _) :: ?l) => unfold_exprlist l
    | (@nil expr)%list => idtac
  end.  *)

(* Ltac lzh_hoare_unfold :=
  try unfold OSInv; try unfold_funpost;
  match goal with
    | |- {| _, _, _, _, _, _ |} |- ?ct {{ _ }} _ {{ _ }} =>
      hoare_split_pure_all;
        let x := find_first_exprs in
          lzh_unfold_exprlist x; pure_intro
    | _ => idtac
  end. *)

(* Ltac lzh_val_inj_solver :=
  intros be H;
  destruct be;
  match goal with
    | |- ?X = ?X => reflexivity
    | |- ?X = ?Y => 
        simpl in H;
        (* ** ac: idtac "X"; *)
        try (unfold Int.notbool in H);
        first [rewrite Int.eq_true in H |
               rewrite Int.eq_false in H | idtac];
        destruct H; tryfalse; auto
  end. *)

(* ** ac: Locate val_inj_impl_Vptr. *)


(* Ltac lzh_val_inj_simpl :=
  match goal with
    | H : val_inj ?e <> Vint32 Int.zero /\
          val_inj ?e <> Vnull /\
          val_inj ?e <> Vundef |- _ =>
      match e with
        | notint _ => apply val_inj_not_true in H
        | val_eq ?x Vnull => apply val_inj_impl_Vnull in H
        | val_eq ?x ?y => apply val_inj_impl_eq in H
        | _ => try apply val_inj_true in H
      end
   
    | H : val_inj ?e = Vint32 Int.zero \/
          val_inj ?e = Vnull |- _ =>
      match e with
        | notint _ => apply val_inj_not_false in H
        | val_eq ?x Vnull => 
          apply val_inj_impl_Vptr in H; destruct H; subst x
        | val_eq ?x ?y =>
          apply val_inj_impl_neq
        | _ => try apply val_inj_false in H
      end

    | _ => idtac
  end. *)


Ltac lzh_hoare_if2 :=
  lzh_hoare_unfold;
  hoare forward; 
  match goal with
    | |- {|_, _, _, _, _, _|} |- ?ct {{?p ** [|?v <> Vint32 Int.zero /\
                                       ?v <> Vnull /\
                                       ?v <> Vundef|]}} ?stmts {{_}} =>
      (* ** ac: idtac "if block proof"; *)
      let x := lzh_find_ret_stmt stmts in
        match x with
          | some _ => instantiate (1:=Afalse)
          | none _ => idtac
        end;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse

    | |- {|_, _, _, _, _, _|} |- ?ct {{_}} _ {{_}} => 
      (* ** ac: idtac "if all"; *)
      hoare forward;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse
      (* first proof if-true condition, then proof if-false condition *)
    | _ => pauto
  end.

(********************** qtimedpost*****************************)

(* Lemma absinfer_seq1:
  forall (p : asrt) (s1 : absop)  (s2 : spec_code) (s1' : absop) (sc : ossched),
                   can_change_aop p ->
                   sc ⊢  <|| s1 ||>  ** p ⇒  <|| s1' ||>  ** p ->
                   sc ⊢  <|| s1;; s2 ||>  ** p ⇒  <|| s1';; s2 ||>  ** p.
Proof.
intros.
eapply absinfer_seq; try eauto.
Qed. *)


Lemma qtimedpost_absinfer_null:
  forall qid time v_msg v' P sch s,
    qid = Vnull ->
    v' = V$ OS_ERR_PEVENT_NULL ->
    can_change_aop P -> 
    absinfer sch
       ( <|| spec_code_cons (qtimedpost (qid :: time :: v_msg :: v' :: nil)) s ||> ** P) 
       ( <|| s ||> ** P ).
Proof.
  intros. subst. simpl.
  eapply absinfer_trans; [ eapply absinfer_choice1; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ | eapply absinfer_seq_end; [ | | eauto]; pure_auto].
  eapply absinfer_seq; try pure_auto.
  infer_solver 0%nat.
Qed.

Lemma qtimedpost_absinfer_null_abt:
  forall  qid time v_msg v' P sch s,
  qid = Vnull ->
   v' <> V$ OS_ERR_PEVENT_NULL ->
   can_change_aop P -> 
   absinfer sch
       ( <|| spec_code_cons (qtimedpost (qid :: time :: v_msg :: v' :: nil)) s ||> ** P)
       ( <|| ABORT ||> ** P ).
Proof.
  intros. simpl.
  eapply absinfer_trans; [ eapply absinfer_choice1; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ | eapply absinfer_seq_abt; [ | | eauto]; pure_auto].
  eapply absinfer_seq; try pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
Qed.

Lemma qtimedpost_absinfer_msg_null':
  forall qid time v' P sch s,
    v' = V$ OS_ERR_POST_NULL_PTR ->
    can_change_aop P -> 
    absinfer sch
       ( <|| spec_code_cons (qtimedpost (Vptr qid :: time :: Vnull :: v' :: nil)) s ||> ** P) 
       ( <|| s ||> ** P ).
Proof.
  intros. subst. simpl.
  eapply absinfer_trans; [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ eapply absinfer_choice1; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ | eapply absinfer_seq_end; [ | | eauto]; pure_auto].
  eapply absinfer_seq; try pure_auto.
  infer_solver 0%nat.
Qed.

Lemma qtimedpost_absinfer_msg_null_abt:
  forall qid time v' P sch s,
    v' <> V$ OS_ERR_POST_NULL_PTR ->
    can_change_aop P -> 
    absinfer sch
       ( <|| spec_code_cons (qtimedpost (Vptr qid :: time :: Vnull :: v' :: nil)) s ||> ** P) 
       ( <|| ABORT ||> ** P ).
Proof.
  intros. simpl.
  eapply absinfer_trans; [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ eapply absinfer_choice1; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ | eapply absinfer_seq_abt; [ | | eauto]; pure_auto].
  eapply absinfer_seq; try pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
Qed.

Lemma qtimedpost_absinfer_type_err:
  forall P mqls x time v_msg v' sch s, 
    can_change_aop P ->  
    v' = V$ OS_ERR_EVENT_TYPE ->  
    ( ~ exists a b pwl wl, EcbMod.get mqls x = Some (absmsgq a b pwl, wl)) ->
    absinfer sch
      ( <|| spec_code_cons (qtimedpost (Vptr x :: time :: v_msg :: v' :: nil)) s ||>  ** 
            HECBList mqls ** P) 
      (<|| s ||>  ** HECBList mqls ** P).
Proof.
  intros. subst. simpl.
  do 2 try (eapply absinfer_trans; [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ]).
  eapply absinfer_trans; [ eapply absinfer_choice1; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ | eapply absinfer_seq_end; [ | | eauto]; pure_auto].
  eapply absinfer_seq; try pure_auto.
  infer_solver 0%nat.
Qed.

Lemma qtimedpost_absinfer_type_err_abt:
  forall P mqls time x v_msg v' sch s, 
    can_change_aop P ->  
    v' <> V$ OS_ERR_EVENT_TYPE ->  
    ( ~ exists a b pwl wl, EcbMod.get mqls x = Some (absmsgq a b pwl, wl)) ->
    absinfer sch
      ( <|| spec_code_cons (qtimedpost (Vptr x :: time :: v_msg :: v' :: nil)) s ||>  ** 
            HECBList mqls ** P) 
      (<|| ABORT ||>  ** HECBList mqls ** P).
Proof.
  intros. simpl.
  do 2 try (eapply absinfer_trans; [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ]).
  eapply absinfer_trans; [ eapply absinfer_choice1; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ | eapply absinfer_seq_abt; [ | | eauto]; pure_auto].
  eapply absinfer_seq; try pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver. pauto.
Qed.

Lemma qtimedpost_absinfer_exwt_succ: 
  forall P mqls x time v_msg v' vl n pwl wl tls t ct p st m t'  sch s tcblh tcbvl vhold v1 v2 v3 sus,
    can_change_aop P ->  
    v' = V$ OS_NO_ERR ->
    get mqls x = Some (absmsgq vl n pwl,wl) ->
    ~ wl=nil ->
    GetHWait tls wl t' ->
    get tls t' = Some (p,st,m, sus) ->
    absinfer sch
          ( <|| spec_code_cons ( qtimedpost ( (Vptr x) :: time :: v_msg :: v' :: nil)) s ||>  **
            HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct **
            EvtInv_part2 mqls tcblh tcbvl vhold v1 v2 v3 ** P) 
      (<|| isched ;; END Some (Vint32 (Int.repr OS_NO_ERR)) ;; s ||>  ** 
            HECBList (EcbMod.set mqls x (absmsgq nil n pwl, (remove_tid t' wl) ) ) **
            HTCBList (TcbMod.set tls t' (p,rdy ,v_msg, sus) ) ** HTime t ** HCurTCB ct **
            EvtInv_part2 (EcbMod.set mqls x (absmsgq nil n pwl, (remove_tid t' wl) ) ) tcblh tcbvl vhold v1 v2 v3 ** P).
Proof.
introv Hcop Hv' Hq Hwl Hhw Htlsget .
simpl.
do 3 (eapply absinfer_trans;  [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ] ).
eapply absinfer_trans; [ eapply absinfer_choice1; [ | | eauto]; pure_auto | ].
eapply absinfer_trans;[ | eapply absinfer_seq_end; [ | | eauto]; pure_auto ].
eapply absinfer_seq; pure_auto.
infer_solver 0%nat.
unfold EvtInv_part2 in *.
unfold ASemEIBs in *.
unfold AMuxEIBs in *.
unfold AMqEIBs in *.
sep pauto.
eapply mq_ecb_p_mq_set_preserve; eauto.
eapply mux_ecb_p_mq_set_preserve; eauto.
eapply sem_ecb_p_mq_set_preserve; eauto.
eapply RH_SEM_EINFO_ECB_P_mq_set_preserve; eauto.
eapply RH_MUX_EIB_ECB_P_mq_set_preserve; eauto.
eapply RH_EIB_ECB_Q_P_mq_set_preserve; eauto.
Qed.

Lemma qtimedpost_absinfer_exwt_abt: 
  forall P mqls x time v_msg v' vl n pwl wl tls sch s, 
    can_change_aop P ->  
    v' <> V$ OS_NO_ERR ->
    get mqls x = Some (absmsgq vl n pwl,wl) ->
    ~ wl=nil ->
    absinfer sch
          ( <|| spec_code_cons ( qtimedpost ( (Vptr x) :: time :: v_msg :: v' :: nil)) s ||>  **
            HECBList mqls ** HTCBList tls **  P) 
      (<|| ABORT ||>  ** 
            HECBList mqls ** HTCBList tls **  P).
Proof.
  introv Hcop Hv' Hq Hwl.
  simpl.
  do 3 (eapply absinfer_trans;  [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ] ).
  eapply absinfer_trans; [ eapply absinfer_choice1; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ | eapply absinfer_seq_abt; [ | | eauto]; pure_auto ].
  eapply absinfer_seq; pure_auto.
  eapply absinfer_trans; [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ].
  eapply absinfer_abt; pure_auto.
  absimp_abt_solver.
  can_change_aop_solver.
Qed.

Lemma qtimedpost_absinfer_not_rdy_abt :
  forall P x time v_msg v' s curtid prio st msg sch tls mqls tm sus,
    TcbMod.get tls curtid = Some (prio, st, msg, sus) ->
    ~ (st = rdy /\ sus = false) ->
    can_change_aop P ->
    absinfer sch
          ( <|| spec_code_cons (qtimedpost ((Vptr x) :: time :: v_msg :: v' :: nil)) s ||>  **
            HECBList mqls ** HTCBList tls ** HTime tm ** HCurTCB curtid ** P) 
      (<|| ABORT ||>  ** 
            HECBList mqls ** HTCBList tls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  simpl.
  do 4 (eapply absinfer_trans;  [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ] ).
  eapply absinfer_trans; [ eapply absinfer_choice1; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ | eapply absinfer_seq_abt; [ | | eauto]; pure_auto ].
  eapply absinfer_seq; pure_auto.
  eapply absinfer_abt; pure_auto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := qtimedpost_stat_not_rdy (|Vptr x :: time :: v_msg :: v' :: nil|));
         sep pauto).
  pauto.
  pure_auto.
Qed.

Lemma qtimedpost_absinfer_prio_idle_abt :
  forall P x time v_msg v' s curtid sch tls mqls tm,
    (exists st msg sus, TcbMod.get tls curtid = Some (Int.repr OS_IDLE_PRIO, st, msg, sus)) ->
    can_change_aop P ->
    absinfer sch
          ( <|| spec_code_cons (qtimedpost ((Vptr x) :: time :: v_msg :: v' :: nil)) s ||>  **
            HECBList mqls ** HTCBList tls ** HTime tm ** HCurTCB curtid ** P) 
      (<|| ABORT ||>  ** 
            HECBList mqls ** HTCBList tls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  destruct H as (st & msg0 & sus & H).
  simpl.
  do 5 (eapply absinfer_trans;  [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ] ).
  eapply absinfer_trans; [ eapply absinfer_choice1; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ | eapply absinfer_seq_abt; [ | | eauto]; pure_auto ].
  eapply absinfer_seq; pure_auto.
  eapply absinfer_abt; pure_auto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := qtimedpost_stat_not_rdy (|Vptr x :: time :: v_msg :: v' :: nil|));
         sep pauto).
  pauto.
Qed.

Lemma qtimedpost_absinfer_ovf_block:
  forall P x time v_msg v' a b pwl wl sch tls t ct p rdy m s ecbls tcblh tcbvl vhold v1 v2 v3 sus,
    Int.unsigned time <=65535 ->
    can_change_aop P ->  
    EcbMod.get ecbls x = Some (absmsgq a b pwl, wl) ->
    Z.ge (Z_of_nat (length a)) (Int.unsigned b) ->
    TcbMod.get tls ct = Some (p,rdy,m, sus) ->
    absinfer sch
      ( <|| spec_code_cons (qtimedpost (Vptr x :: Vint32 time :: v_msg :: v' :: nil)) s ||> **  
            HECBList ecbls ** HTCBList tls ** HTime t ** HCurTCB ct **
            EvtInv_part2 ecbls tcblh tcbvl vhold v1 v2 v3 ** P) 
      (<|| isched ;; qtimedpost_after_sched (|Vptr x :: Vint32 time :: v_msg :: v' :: nil|) ;;
            ( ( qtimedpost_timeout_err (|Vptr x :: Vint32 time :: v_msg :: v' :: nil|);;s ) ??
              ( qtimedpost_block_post_succ (|Vptr x :: Vint32 time :: v_msg :: v' :: nil|);;s )) ||> ** 
            HECBList (EcbMod.set ecbls x (absmsgq a b (ct::pwl), wl)) ** 
            HTCBList (TcbMod.set tls ct (p,wait (os_stat_postq x) None,v_msg, sus)) ** HTime t ** HCurTCB ct **
             EvtInv_part2 (EcbMod.set ecbls x (absmsgq a b (ct::pwl), wl)) tcblh tcbvl vhold v1 v2 v3 ** P).
Proof.
infer_solver 6%nat.
unfold EvtInv_part2 in *.
unfold ASemEIBs in *.
unfold AMuxEIBs in *.
unfold AMqEIBs in *.
sep pauto.
eapply mq_ecb_p_mq_set_preserve; eauto.
eapply mux_ecb_p_mq_set_preserve; eauto.
eapply sem_ecb_p_mq_set_preserve; eauto.
eapply RH_SEM_EINFO_ECB_P_mq_set_preserve; eauto.
eapply RH_MUX_EIB_ECB_P_mq_set_preserve; eauto.
eapply RH_EIB_ECB_Q_P_mq_set_preserve; eauto.
Qed.

Lemma qtimedpost_absinfer_p_aftersch :
  forall P x time v_msg v' s  sch tls mqls t ct p st m sus, 
    Int.unsigned time <= 65535 ->
    can_change_aop P ->
     TcbMod.get tls ct = Some (p, st, m, sus) ->
      ((st = rdy /\ sus = false )  \/ ((st = wait (os_stat_postq x) None /\ sus = false) )) ->
    absinfer sch
      (<|| qtimedpost_after_sched (|Vptr x :: Vint32 time :: v_msg :: v' :: nil|) ;; s ||> **
           HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
      (<|| s ||> **
           HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma qtimedpost_absinfer_p_aftersch_abt :
  forall P x time v_msg v' s  sch tls mqls t ct p st m sus, 
    Int.unsigned time <= 65535 ->
    can_change_aop P ->
     TcbMod.get tls ct = Some (p, st, m, sus) ->
      ~ ((st = rdy /\ sus = false)  \/ ((st = wait (os_stat_postq x) None /\ sus = false)  )) ->
    absinfer sch
      (<|| qtimedpost_after_sched (|Vptr x :: Vint32 time :: v_msg :: v' :: nil|) ;; s ||> **
           HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
      (<|| ABORT ||> **
           HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
  intros.
  eapply absinfer_trans; [ | eapply absinfer_seq_abt; [ | | eauto]; pure_auto ].
  eapply absinfer_seq; pure_auto.
  eapply absinfer_abt; pure_auto.
  absimp_abt_solver;
  try (instantiate (3 := s0); 
         instantiate (2 := qtimedpost_after_sched (|Vptr x :: Vint32 time :: v_msg :: v' :: nil|));
         sep pauto).
  pauto.
  pauto.
Qed.

Lemma qtimedpost_absinfer_timeout:
   forall P x time v_msg v' tm curtid tcbls prio m sch  a b pwl wl s ecbls tcblh tcbvl vhold v1 v2 v3 sus,
    Int.unsigned time <= 65535 ->
    TcbMod.get tcbls curtid = Some (prio, wait (os_stat_postq x) None, m, sus) ->
    EcbMod.get ecbls x = Some (absmsgq a b pwl, wl) ->
    In curtid pwl ->
    (* m = Vnull -> *)
    can_change_aop P ->
     v' = Vint32 (Int.repr OS_TIMEOUT) ->
    absinfer sch
      ( <|| (qtimedpost_timeout_err (|Vptr x :: Vint32 time :: v_msg :: v' :: nil|);; s) ??
      ( qtimedpost_block_post_succ (|Vptr x :: Vint32 time :: v_msg :: v' :: nil|);;s ) ||>  ** 
            HECBList ecbls ** HTCBList tcbls ** HTime tm ** HCurTCB curtid **
            EvtInv_part2 ecbls tcblh tcbvl vhold v1 v2 v3 ** P) 
      (<||   s ||> **
            HECBList (EcbMod.set ecbls x (absmsgq a b (remove_tid curtid pwl), wl) ) **
            HTCBList (TcbMod.set tcbls curtid (prio,rdy, Vnull, false) ) ** 
            HTime tm ** HCurTCB curtid **
            EvtInv_part2 (EcbMod.set ecbls x (absmsgq a b (remove_tid curtid pwl), wl) ) tcblh tcbvl vhold v1 v2 v3 ** P).
Proof.
infer_solver 0%nat.
unfold EvtInv_part2 in *.
unfold ASemEIBs in *.
unfold AMuxEIBs in *.
unfold AMqEIBs in *.
sep pauto.
eapply mq_ecb_p_mq_set_preserve; eauto.
eapply mux_ecb_p_mq_set_preserve; eauto.
eapply sem_ecb_p_mq_set_preserve; eauto.
eapply RH_SEM_EINFO_ECB_P_mq_set_preserve; eauto.
eapply RH_MUX_EIB_ECB_P_mq_set_preserve; eauto.
eapply RH_EIB_ECB_Q_P_mq_set_preserve; eauto.
Qed.

Lemma qtimedpost_absinfer_timeout_abt:
   forall P els x time v_msg v' tm curtid tcbls prio m sch  a b pwl wl s sus,
    Int.unsigned time <= 65535 ->
    TcbMod.get tcbls curtid = Some (prio, wait (os_stat_postq x) None, m, sus) ->
    EcbMod.get els x = Some (absmsgq a b pwl, wl) ->
    In curtid pwl ->
    (* m = Vnull -> *)
    can_change_aop P ->
     v' <> Vint32 (Int.repr OS_TIMEOUT) ->
    absinfer sch
      ( <|| (qtimedpost_timeout_err (|Vptr x :: Vint32 time :: v_msg :: v' :: nil|);; s) ??
      ( qtimedpost_block_post_succ (|Vptr x :: Vint32 time :: v_msg :: v' :: nil|);;s ) ||>  ** 
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P) 
      (<||  ABORT ||> **
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  eapply absinfer_trans; [ eapply absinfer_choice1; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ | eapply absinfer_seq_abt; [ | | eauto]; pure_auto ].
  eapply absinfer_seq; pure_auto.
  eapply absinfer_abt; pure_auto.
  absimp_abt_solver;
  try (instantiate (3 := s0); 
         instantiate (2 := qtimedpost_timeout_err (|Vptr x :: Vint32 time :: v_msg :: v' :: nil|));
         sep pauto).
  pauto.
Qed.

Lemma qtimedpost_absinfer_block_to:
   forall P els x time v_msg v' tm curtid tcbls prio st m sch s  sus,
    Int.unsigned time <= 65535 ->
    TcbMod.get tcbls curtid = Some (prio, st, m, sus) ->
    st = rdy ->
    sus = false ->
    can_change_aop P ->
     v' = Vint32 (Int.repr OS_NO_ERR) ->
    absinfer sch
      ( <|| (qtimedpost_timeout_err (|Vptr x :: Vint32 time :: v_msg :: v' :: nil|);; s) ??
      ( qtimedpost_block_post_succ (|Vptr x :: Vint32 time :: v_msg :: v' :: nil|);;s ) ||>  ** 
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P) 
      (<|| s ||> **HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma qtimedpost_absinfer_block_to_abt:
   forall P els x time v_msg v' tm curtid tcbls prio st m sch  s sus,
    Int.unsigned time <= 65535 ->
    TcbMod.get tcbls curtid = Some (prio, st, m, sus) ->
    st = rdy ->
    sus = false ->
    can_change_aop P ->
     v' <> Vint32 (Int.repr OS_NO_ERR) ->
    absinfer sch
      ( <|| (qtimedpost_timeout_err (|Vptr x :: Vint32 time :: v_msg :: v' :: nil|);; s) ??
      ( qtimedpost_block_post_succ (|Vptr x :: Vint32 time :: v_msg :: v' :: nil|);;s ) ||>  ** 
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P) 
      (<||  ABORT ||> **
            HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  intros.
  eapply absinfer_trans; [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ].
  eapply absinfer_trans; [ | eapply absinfer_seq_abt; [ | | eauto]; pure_auto ].
  eapply absinfer_seq; pure_auto.
  eapply absinfer_abt; pure_auto.
  absimp_abt_solver;
  try (instantiate (3 := s0); 
         instantiate (2 := qtimedpost_timeout_err (|Vptr x :: Vint32 time :: v_msg :: v' :: nil|));
         sep pauto).
  pauto.
Qed.

Lemma qtimedpost_absinfer_nowt_succ: 
  forall P mqls x v_msg v' a b pwl tcbls t ct sch time s tcblh tcbvl vhold v1 v2 v3, 
    can_change_aop P ->  
    v' = V$ OS_NO_ERR ->
    EcbMod.get mqls x = Some (absmsgq a b pwl,nil) ->
    Z.lt (Z_of_nat (length a)) (Int.unsigned b) ->
    absinfer sch
          ( <|| spec_code_cons ( qtimedpost (Vptr x :: Vint32 time  :: v_msg :: v' :: nil)) s ||>  **
            HECBList mqls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** 
            EvtInv_part2 mqls tcblh tcbvl vhold v1 v2 v3 ** P)
          (<||  s ||>  **
            HECBList (EcbMod.set mqls x (absmsgq (a++(v_msg::nil)) b pwl,nil))** HTCBList tcbls ** HTime t ** HCurTCB ct **
            EvtInv_part2 (EcbMod.set mqls x (absmsgq (a++(v_msg::nil)) b pwl,nil)) tcblh tcbvl vhold v1 v2 v3 ** P).
Proof.
infer_solver 7%nat.
unfold EvtInv_part2 in *.
unfold ASemEIBs in *.
unfold AMuxEIBs in *.
unfold AMqEIBs in *.
sep pauto.
eapply mq_ecb_p_mq_set_preserve; eauto.
eapply mux_ecb_p_mq_set_preserve; eauto.
eapply sem_ecb_p_mq_set_preserve; eauto.
eapply RH_SEM_EINFO_ECB_P_mq_set_preserve; eauto.
eapply RH_MUX_EIB_ECB_P_mq_set_preserve; eauto.
eapply RH_EIB_ECB_Q_P_mq_set_preserve; eauto.
Qed.

Lemma qtimedpost_absinfer_nowt_succ_abt: 
  forall P mqls x v_msg v' a b pwl tcbls t ct sch time s, 
    can_change_aop P ->  
    v' <> V$ OS_NO_ERR ->
    EcbMod.get mqls x = Some (absmsgq a b pwl,nil) ->
    Z.lt (Z_of_nat (length a)) (Int.unsigned b) ->
    absinfer sch
          ( <|| spec_code_cons ( qtimedpost (Vptr x :: Vint32 time  :: v_msg :: v' :: nil)) s ||>  **
            HECBList mqls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P) 
          (<||  ABORT ||>  **
            HECBList mqls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  intros.
  simpl.
  do 7 try (eapply absinfer_trans; [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ]).
  eapply absinfer_trans; [ | eapply absinfer_seq_abt; [ | | eauto]; pure_auto ].
  eapply absinfer_seq; pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver. pauto.
Qed.

Require Import OSMutex_common.

Lemma OSQTimedPostProof: 
  forall vl p r logicl ct, 
    Some p =
    BuildPreI os_internal OSQTimedPost vl logicl OSQTimedPostPre ct->
    Some r =
    BuildRetI os_internal OSQTimedPost vl logicl OSQTimedPostPost ct->
    exists t d1 d2 s,
      os_internal OSQTimedPost = Some (t, d1, d2, s) /\
      {|OS_spec , GetHPrio, OSLInv, I, r, Afalse |}|-ct {{p}}s {{Afalse}}.
Proof.
  init_spec.
  rename v'4 into er.
  rename H0 into Hnthvl0; rename H4 into Hvtime.
  rename v'2 into vptr; rename v'3 into v'2.
  change ((x1 :: Vint32 i :: x :: nil) ++ v'2 :: nil) with (x1 :: Vint32 i :: x :: v'2::nil).
  (*enter critical -------------------------L1*)
  hoare forward prim.
  hoare unfold.
  rename H2 into Htimele.
   rename H3 into H2; rename H4 into H3.
  (*pevent is Null pointer -------------------------L2 ~ L4*)
  lzh_hoare_if2.
  hoare forward prim.
  eauto. auto.
  pure_auto.

  assert (Hor: v'2 <> (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) \/ 
                 v'2 = (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) by tauto.
  inversion Hor.
  (* v'2 <> ... *) 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qtimedpost_absinfer_null_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule.
  
  (* v'2 = ... *) 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qtimedpost_absinfer_null; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq.
  (* return in case pevent = NULL *)
  hoare forward.

  (*msg is Null pointer -------------------------L5 ~ L7*)
  hoare forward.
  apply isptr_zh; auto.
  pauto.
  pure intro.
  assert (x=Vnull) by pauto.
  subst x.
(*   pure_auto. *)
  assert (Hor: v'2 <> (Vint32 (Int.repr OS_ERR_POST_NULL_PTR)) \/ 
                 v'2 = (Vint32 (Int.repr OS_ERR_POST_NULL_PTR))) by tauto.
  inversion Hor.
  (* v'2 <> ... *)
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qtimedpost_absinfer_msg_null_abt;eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule.
  (* exit critical*)
  hoare forward prim.
  eauto. auto.
  pure_auto.
  
  (* v'2 = ... *)
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply qtimedpost_absinfer_msg_null'.
  pure_auto.
  can_change_aop_solver.
  eapply absinfer_eq.
  (*  RETURN ′ OS_ERR_POST_NULL_PTR *)
  hoare forward.

  hoare forward.

  (* pevent not in dom legal : Lemma qpost_q_not_in_dom_abt*)
  unfold EvtInv.
  rename v'19 into vcspace.
  rename v'20 into v20. 
  rename v'21 into v21. 
  rename v'22 into v22. 

  hoare unfold.

  rename v'36 into locmp.
  rename v'37 into ptrmp.
  rename v'11 into els.
  rename v'19 into fecbh.
  rename v'20 into fecbvl.
  rename v'31 into semeibs.
  rename v'32 into muxeibs.
  rename v'33 into mqeibs.
  
  hoare_assert_pure (get ptrmp ct = Some (Vnull, Vnull, Vptr x0)
                                             /\ get locmp ct = Some (V$ os_code_defs.__EvLoc_normal)).
  { get_hsat Hsat.
     sep_lifts_trms_in Hsat (evlocid, evptrid, tcbllsegevaux, AOSTCBList,p_local).
    eapply get_aux;eauto.
   }
  hoare_split_pure_all.
  destruct H4 as (Hget_ptr & Hget_loc).

  assert (Hevt: is_evt els x0 \/ ptr_in_ecblist (Vptr x0) fecbh fecbvl).  
  { eapply mq_ecb_nml; eauto. }

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

   (*if OSEventType !=ₑ ′ OS_EVENT_TYPE_Q*)
  hoare forward.
  go. 
  2: { instantiate(1:= Afalse).
          eapply hoare_disj_afalseP_l_pre.
          change (Int.eq ($ OS_EVENT_TYPE_UNUSED) ($ OS_EVENT_TYPE_Q)) with false. 
          hoare unfold.
          simpl in H4; change (Int.notbool Int.zero) with Int.one in H4; 
          destruct H4; tryfalse. }
  
  unfold AECBList.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Astruct, evsllseg).

  hoare_assert_pure (get els (v'37, Int.zero) = None).
  {
    get_hsat Hsat. 
    lets H00: sem_common.semcre_ecblist_star_not_inh H4 Hsat.
    auto.
  }
  hoare_split_pure_all.
  rename H16 into Hnone.

   assert (Htype_err': ~ (exists x y pwl z, get els (v'37, Int.zero) = Some (absmsgq x y pwl, z))).
  { rewrite Hnone.
    introv Hf; destruct Hf as (mx & my & mp & mz & Hf ); inverts Hf.
  }

  assert (Hopv: v'2 = V$ OS_ERR_EVENT_TYPE \/ v'2 <> V$ OS_ERR_EVENT_TYPE) by tauto.
  hoare_lifts_trms_pre (Aop, absecblsid).
  destruct Hopv.
  2 :{
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply qtimedpost_absinfer_type_err_abt; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        eapply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qtimedpost_absinfer_type_err; eauto.
  can_change_aop_solver. eapply absinfer_eq.
  hoare forward prim.
  unfold EvtInv.
  unfold AECBList.
  unfold AOSEventFreeList.
  sep pauto.
  trycancel_EvtInv.
  sep cancel evsllseg.
  unfold ecbf_sll.
  eapply ecbf_sllseg_compose3_frm; eauto. 
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel Aarray.
  sep cancel ecbf_sllseg.
  sep cancel ecbf_sllseg.
  eauto.
  unfolds; simpl; auto.
  go. go. eauto. eauto. eauto. eauto. auto.
  pure_auto.
  hoare forward.
  hoare unfold.

   (* pevent points to an active ECB *) 
  assert (Hget: exists ecb, get els x0 = Some ecb).
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
  destruct d as [e w].

 (* split AECBList *)
  unfold AECBList.
  hoare unfold.
  lets Hget_ectr: ECBList_P_get_ectr_some Hget H4.
  destruct Hget_ectr as (et & etbl & petbl & Hget_ectr).
  eapply backward_rule1.
  intros.
  eapply get_ectr_decompose; eauto.
  sep cancel evsllseg. eauto.
  hoare unfold.
  hoare_assert_pure (length v'19 = length v'31).
  { get_hsat Hsat. sep_lifts_trms_in Hsat (evsllseg v'11).
     eapply evsllseg_list_len_eq in Hsat; auto.
  }
  hoare_split_pure_all.
  lets Hels_split: ucos_common.ecblist_p_decompose H13 H4.
  destruct Hels_split as (els1 & els2 & x0 & H'').
  destruct H'' as (Hecbl1 & Hecbl2 & Hjo).

  hoare_assert_pure ( x0 = Vptr (v'40, Int.zero) ).
  {  get_hsat Hsat.
  sep_lifts_trms_in Hsat  (evsllseg v'11).
  eapply ecblistp_evsllseg_tlsame; eauto. }
  hoare_split_pure_all.
  subst.
  simpl ECBList_P at 1 in Hecbl2.
  destruct Hecbl2 as (qid & Hqid & Hecbetbl & Hecbpetbl & Hmt).
  inverts Hqid.
  destruct Hmt as (absev & els' & v'' & H').
  destruct H' as (Helptr & Hjo' & Hrlh & Hecbl2). 
  inverts Helptr.
  
  assert (Habsev: get els (v'40, Int.zero) = Some absev).
  {
    assert (Hpre: join (sig (v'40, Int.zero) absev) els' els2) by join auto. 
    eapply join_sig_get in Hpre; eauto. 
    eapply join_get_r; eauto. 
  }
  assert (absev = (e, w)).
  {
    unfold get in Habsev. destruct EcbMap. 
    unfold Maps.get in Hget.
    rewrite Hget in Habsev.
    inverts Habsev. auto. 
  }
  subst absev.
  rename v'36 into letbl.
  rename v'38 into lpetbl.
  inverts H20.
  rename i1 into tp; rename i0 into egrp; rename i into pegrp.

   (*event type not q -------------------------L8 ~ L10*)
  hoare unfold.
  hoare forward; pure_auto.
  instantiate (1:=Afalse).
  pure intro.
  apply notint_neq_zero_eq in H14.
  unfold OS_EVENT_TYPE_Q in H14.

 (*  lzh_hoare_if2. *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat AEventData.
  eapply eventtype_neq_q' in Hsat; eauto. 
  hoare_split_pure_all.

    casetac v'2 (V$ OS_ERR_EVENT_TYPE) Hopveq Hopvne.
    2: {
      hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid). 
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply qtimedpost_absinfer_type_err_abt; eauto.
      go. 
      eapply absinfer_eq.
      apply absabort_rule.
    }
    hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply qtimedpost_absinfer_type_err; eauto.
    go. 
    eapply absinfer_eq.

  (*********  exit critical ***********)
  fold_AEventNode_r. 
  compose_evsllseg. 
  fold_AECBList. 
  
  hoare forward prim.
  unfold EvtInv.
  sep pauto.
  trycancel_EvtInv.
  eauto.
  go. go. go. go. go.

  hoare forward.
  hoare forward.
  pure intro.
  destruct (Int.eq tp (Int.repr OS_EVENT_TYPE_Q)) eqn: eq1;
  simpl in H14; try change (Int.notbool Int.zero) with Int.one; destruct H14; tryfalse.
  eapply semacc_int_eq_true in eq1; subst.
  destruct v'33; [ | simpl AEventData | simpl AEventData | simpl AEventData | simpl AEventData]; pure intro; tryfalse.
  hoare_assert_pure (exists qid, v = x2 /\ x2 = Vptr (qid, Int.zero)).
  { get_hsat Hsat. unfold AEventData in Hsat.
     unfold AMsgData in Hsat.
     unfold AOSQCtr in Hsat.
     unfold node in Hsat.
     sep normal in Hsat; sep destruct Hsat.
     sep split in Hsat. inverts H14.
     pauto.
   }
  pure intro.
  rename v'14 into qid.

  (* exists task waiting -------L11 ~ L16 ----------- *)

  hoare forward; pure_auto.
  instantiate (1:=Afalse).

  pure intro.
  apply notint_neq_zero_eq in H14.
  hoare forward.

  (*call OS_EventTaskRdy*)
  hoare_lifts_trms_pre (Aisr,Ais,aemp_isr_is).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  unfold AOSTCBList.
  unfold AOSTCBPrioTbl.
  hoare normal pre.
  pure_intro.
  hoare forward.
  clear -H1; pure_auto.
  (* pre conditions of OS_EventTaskRdy*)
  sep cancel AOSRdyTblGrp.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep normal.
  sep eexists.
  sep cancel AEventData.
  sep cancel OS_EVENT_TBL_SIZE.
  sep cancel AOSPostEventTbl.
  sep split; eauto.
  sep cancel OS_EVENT.
  eapply tcbdllseg_compose.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  sep cancel p_local.
  eauto.
  split; eauto. go.
  split.
  pure_auto.
  eapply semacc_int_eq_false; eauto.
  simpl; eauto.
  simpl; eauto.
  simpl. auto.
  eapply TCBList_P_Combine; eauto.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat (tcbdllseg v'4).
  eapply tcbdllseg_get_last_tcb_ptr; eauto.
  auto.
  eauto.
  auto.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat (tcbdllseg v'4, tcbdllseg (Vptr ct)).
  eapply tcbdllseg_combine_ptr_in_tcblist; eauto.
  pure_auto.
  intros.
  sep auto.
  intros.
  sep auto.
  clear -H1; pure_auto.
(*finished side conditions*)
(*   rename H42 into Hrh_priotbl_p. *)
  rename v'9 into old_rtbl; rename v'3 into old_ptbl.
  rename H22 into Hetbl_len. (* length etbl = ∘ OS_EVENT_TBL_SIZE *)
  unfold OS_EventTaskRdyPost.
  unfold OS_EventTaskRdyPost'.
  unfold getasrt.
  simpl nth_val.
  hoare unfold.
  inverts H72.
  simpl rel_edata_tcbstat in H49.
  rename H49 into Hstat_eq.
  subst.
(*   try rewrite Int.and_not_self in *. *)

  rename v'47 into etbl; rename v'46 into egrp'; rename v'45 into egrp; rename v'49 into petbl.
  rename v'41 into rtbl; rename v'44 into rgrp. (* AOSRdyTblGrp ... *)
  (*after OS_EventTaskRdy*)

  (*prove some properties used by the following reasoning*)
  
  (*1: get the range info of the event table elements*)
   lets y_le7: math_unmap_get_y H25 H50.
  assert (y_le7': (Z.to_nat (Int.unsigned v'67) < length etbl)%nat).
  {
    rewrite Hetbl_len.
    clear -y_le7. change (∘ OS_EVENT_TBL_SIZE)  with 8%nat.
    auto with zarith.
  }
   assert (y_le7'': (Z.to_nat (Int.unsigned v'67) < length rtbl)%nat).
  {
    rewrite H74.
    clear -y_le7. change (∘ OS_RDY_TBL_SIZE)  with 8%nat.
    auto with zarith.
  }
  lets erow_le255: array_int8u_nth_lt_len H15 y_le7'.
  rewrite H51 in erow_le255.
  destruct erow_le255 as (erow & Heq & erow_le255); inverts Heq.
  lets x_le7: math_unmap_get_y erow_le255 H52.
  assert (Hwait: PrioWaitInQ (Int.unsigned ((v'67<<ᵢ$ 3) +ᵢ  v'66)) etbl).
  {
    eapply prio_from_grp_tbl_PrioWaitInQ with (grp:= egrp); eauto.
    eapply semacc_int_eq_false; eauto.
  }
  assert (Hwait_range: (Int.unsigned ((v'67<<ᵢ$ 3) +ᵢ  v'66)) < 64).
  {
    clear -Hwait. funfold Hwait. auto.
  }
  assert (Hwait_range': (Int.unsigned ((v'67<<ᵢ$ 3) +ᵢ  v'66)) <= 255).
  { clear -Hwait_range.   auto with zarith. }
  rename v'9 into tcbls.
  lets Hptbl: H69.
  assert (Hwait_get_t: exists b c sus, 
                            TcbMod.get tcbls (v'84, Int.zero) = Some (((v'67<<ᵢ$ 3) +ᵢ  v'66), b, c, sus)).
  { eapply Hptbl; eauto.
     split. apply Int.unsigned_range_2. auto.
     eapply nth_val'2nth_val'; eauto.
   }
  destruct Hwait_get_t as (wait_st & wait_m & sus & Hwait_get_t).
  lets Hwait_tcj: TcbMod.map_join_get_sig Hwait_get_t.
  destruct Hwait_tcj as (wait_tls1 & Hwait_tcj).
  destruct Hptbl as (Hptbl_lh & Hptbl_hl & Hdup).
  assert (Hwait_st: exists time, wait_st = wait (os_stat_q (v'40, Int.zero)) time).
  { clear -Hdup Hwait_get_t Hecbetbl Hwait.
     destruct Hecbetbl as (Hlh_etbl & _).
     destruct Hlh_etbl as (Hlh_etbl & _).
      unfold V_OSEventType in Hlh_etbl; simpl in Hlh_etbl.
      eapply Hlh_etbl in Hwait; auto.
      simpljoin.
      rewrite Int.repr_unsigned in H.
      eapply R_Prio_No_Dup_tid_eq in H; eauto.
      simpljoin; eauto.
  }
  destruct Hwait_st as (wait_t & Hwait_st); subst wait_st.
  lets Hcp: H0.
  destruct Hcp as (Hcp & _).
  lets Hget_e: Hwait_get_t.
  eapply Hcp in Hget_e; eauto.
  destruct Hget_e as (vl & n & pwl & wl & Hget_e & Hin_pwl).
  unfold get in Habsev, Hget_e; simpl in Habsev, Hget_e.
  rewrite Habsev in Hget_e; inverts Hget_e.
  assert (Hwait_get: wl <> nil /\
       GetHWait tcbls wl (v'84, Int.zero) /\
       TcbMod.get tcbls (v'84, Int.zero) = Some (((v'67<<ᵢ$ 3) +ᵢ  v'66), wait (os_stat_q (v'40, Int.zero)) wait_t, wait_m, sus)).
  { eapply post_exwt_succ_pre; eauto.
     eapply semacc_int_eq_false; eauto.
     auto with zarith.
     auto with zarith.
  }
  destruct Hwait_get as (Hwl_nnil & Hhwait & _).
  (* change absdata *)
  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_part2; eauto.
  trycancel_EvtInv.
  sep pauto.
  hoare_lifts_trms_pre (Aop,absecblist, abstcblist, ostm, oscurt, EvtInv_part2).
  assert (Hv'2cs: v'2 <> Vint32 (Int.repr OS_NO_ERR) \/
                  v'2 = Vint32 (Int.repr OS_NO_ERR)) by tauto. 
  inversion Hv'2cs.
   (* v'1 <> ... *) 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qtimedpost_absinfer_exwt_abt; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  eapply absabort_rule.
  (* v'1 = ... *)
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply qtimedpost_absinfer_exwt_succ; eauto. 
  can_change_aop_solver.
  apply absinfer_eq.

(*L14: EXIT_CRITICAL;ₛ*)
   hoare_lifts_trms_pre (Aisr,Ais,Aier).
  transform_pre add_aemp_isr_is_prop ltac:(idtac).
 (*split the new vltcb in hoare pre*)
  lets old_tcbnode_p : TCBList_P_tcblist_get_TCBNode_P H71 H45 Hwait_get_t.
  assert (Hv63_eq: (((v'67<<ᵢ$ 3) +ᵢ  v'66) >>ᵢ $ 3) = v'67).
    { eapply math_shrl_3_eq; eauto.
      clear -y_le7.
     auto with zarith.
    }
  assert (Hv62_eq: (((v'67<<ᵢ$ 3) +ᵢ  v'66) &ᵢ $7) = v'66).
    {
     eapply math_8range_eqy; eauto.
      clear -y_le7 x_le7.
     auto with zarith.
    }
   generalize old_tcbnode_p; intro Htmp.
    destruct Htmp as (Hmsg & Hprio & Hh_tcbblk & Hh_tcbstat).
    inverts Hmsg; inverts Hprio.

  hoare_lifts_trms_pre (tcbdllseg).
  eapply set_node_elim_hoare_sus with (st':=rdy)
                     (rtbl':=update_nth_val (Z.to_nat (Int.unsigned v'67)) rtbl
                                                 (Vint32 (Int.or v'85 v'69))); eauto.
  eapply TCBNode_P_set_rdy_gen; eauto.
  split; auto. apply Int.unsigned_range_2.
  rewrite Hv63_eq. eapply nth_val'2nth_val; eauto.
  lets Hx: array_int8u_nth_lt_len H59 y_le7''.
  rewrite H22 in Hx; destruct Hx as (xi & Heq & Hr); inverts Heq; auto.
   { destruct Hstat_eq; subst.
    assert (Hsus: sus = false) by
    (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: sus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    change (Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_Q)) with ($ OS_STAT_SUSPEND).
    auto.
     }
  rewrite Hv62_eq.
  eapply math_mapval_core_prop; auto.
  (*rtbl_set_one_bit*)
{ destruct sus eqn: eq_sus; auto.
  unfolds.
  rewrite Hv63_eq. rewrite Hv62_eq.
  repeat eexists; eauto. apply Int.unsigned_range_2.
}
  unfolds; simpl; auto.
  (* actual exit *)
  assert (Heq_sus: Int.eq (v'78&ᵢInt.not ($ OS_STAT_Q)) ($ OS_STAT_RDY) = negb sus).
  { change ($ OS_STAT_RDY) with Int.zero.
    destruct Hstat_eq; subst.
    assert (Hsus: sus = false) by
    (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: sus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    change (Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_Q)) with ($ OS_STAT_SUSPEND).
    auto.
   }
  rewrite Heq_sus in *. rewrite negb_if in *.

  hoare forward prim.
  sep cancel p_local.
  sep cancel Aier.
  unfold AOSTCBList.
  sep pauto; eauto.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel (tcbdllseg v'55).
  sep cancel tcbdllseg.
  rewrite <- H47.
  sep_lifts_trms tcbdllflag. 
  eapply tcbdllflag_set_node; eauto.
  sep cancel tcbdllflag.
  sep_lifts_trms EvtInv.
  eapply fold_EvtInv_frm'.
  sep_lifts_trms EvtInv_part2.
  eapply evtinv_part2_set_node; eauto.
  sep cancel EvtInv_part2.
  trycancel_EvtInv.
  unfold AECBList.
  unfold AOSTCBPrioTbl.
  sep normal.
  sep eexists.
  sep cancel vhold_addr.
  sep cancel OSTCBPrioTbl.
  sep cancel OSPlaceHolder.
  sep cancel OSEventList.
  simpl update_nth_val in *.
  eapply evsllseg_compose; 
  [ idtac | | idtac 
    |  unfold AEventNode in *;
       sep cancel AOSEvent]; eauto.
  unfolds; simpl; eauto.
  sep cancel evsllseg.
  sep cancel evsllseg.
  sep cancel absptls.
  sep split; eauto.
  cancel_corecommuinv.
  sep cancel AEventData.
  
  (* PartitionInv *)
  Require Import sem_partition.
  cancel_partitioninv.
  eauto.
  (* end of PartitionInv*)

  eapply r_priotbl_p_set_hold; auto; eauto.
  {
  get_hsat Hsat.
  unfold AEventData in *;
  unfold AMsgData in *;
  unfold AOSQCtr,AOSQBlk in *;
  unfold node in *.
  sep normal in Hsat; sep destruct Hsat.
  sep split in Hsat.
  simpljoin.
  eapply struct_type_vallist_match_os_q in H78;
  eapply struct_type_vallist_match_os_q_freeblk in H79; 
  simpljoin.
  inverts H63; inverts H56.
  funfold H57.
  eapply ecblist_p_post_exwt_hold1 with (v'12:= egrp); eauto.
  eapply semacc_int_eq_false; eauto.
  auto with zarith.
  auto with zarith.
  assert (x_le7': Int.unsigned v'66 <= 7).
  { auto with zarith. }
  clear - H54 x_le7'.
  lets Hx: osmapvallist_prop x_le7'; simpljoin.
  rewrite H54 in H; inverts H.
  auto.
  

  }
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  clear -H3.
  unfolds.
  unfolds in H3.
  simpljoin.
  rewrite TcbMod.set_sem.
  destruct (tidspec.beq (v'84, Int.zero) ct) eqn: eq1; eauto.
  eapply rh_tcblist_ecblist_p_post_exwt; eauto.
  
  pure_auto.
  (*L15: OS_Sched (­);ₛ*)
  hoare forward.
  unfolds; eauto.
  pure_auto.
  intros.
  sep auto.
  sep cancel p_local.
  simpl; auto.
  intros.
  sep auto.
  sep cancel p_local.
  simpl; auto.

  (*L16: RETURN ′ OS_NO_ERR*)
  hoare unfold.
  inverts H46.
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule. apply noabs_oslinv.
  eapply absinfer_seq_end.
  pure_auto.
  2: eauto.
  pure_auto.
  eapply absinfer_eq.

  hoare forward.
  simpl.
  intro;tryfalse.
  splits; eauto.
  unfold OS_NO_ERR.
  clear. int auto.

  hoare forward.
  hoare_split_pure_all.
  destruct (Int.eq egrp ($ 0)) eqn: eq1;
  simpl in H14; try change (Int.notbool Int.zero) with Int.one; destruct H14; tryfalse.
  clear H14.
  change ($ 0) with Int.zero in eq1;
  eapply semacc_int_eq_true in eq1; subst.
  (* Int.eq egrp ($ 0)  = true *)

  (*L17: pq ′ =ₑ pevent ′ → OSEventPtr;ₛ*)
  hoare forward.
  pure_auto.

  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_part2; eauto.
  trycancel_EvtInv.
  sep pauto.

(*L18: If(pq ′ → OSQEntries ≥ pq ′ → OSQSize)*)
  unfold AEventData.
  hoare unfold.
  hoare forward; go; try (clear; pure_auto).
  instantiate (1 := Afalse).
  pure intro.
  assert (Hif_cond: Int.ltu i0 i = true \/ Int.eq i i0 = true).
  { clear -H14.
     destruct (Int.ltu i0 i) eqn: eq1;
     destruct (Int.eq i i0) eqn: eq2;
     try auto.
  }
  clear H14 H17 H35.

  lets Hy:ecbmod_absmsgq Hrlh; simpljoin.

  assert (Fget: exists p st msg sus, TcbMod.get v'12 ct = Some (p,st,msg, sus)).
  {
    clear -H3.
    unfold RH_CurTCB in H3.
    auto.
  }
  destruct Fget as (cur_p & cur_st & cur_msg & sus & Fget_ct).

  hoare_lifts_trms_pre (Aop , absecblsid, abstcblsid, ostmid, curtid ).
  assert (Hcur_st: ~(cur_st = rdy /\ sus = false) \/ (cur_st = rdy /\ sus = false)) by tauto.
  destruct Hcur_st as [Hcur_st | (Hcur_st & Hsus_eq)].
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qtimedpost_absinfer_not_rdy_abt; eauto.
  can_change_aop_solver. 
  eapply absinfer_eq. 
  eapply absabort_rule.
  (********* OSTCBCur is not rdy finished ****************)
  subst cur_st. subst sus.
  assert (Hcur_prio: cur_p = $ OS_IDLE_PRIO \/ cur_p <> $ OS_IDLE_PRIO) by tauto.
  destruct Hcur_prio as [Hcur_prio | Hcur_prio].
  subst cur_p.

  fold_AEventNode_r.

  hoare_lifts_trms_pre (Aop , absecblsid, abstcblsid, ostmid, curtid ).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qtimedpost_absinfer_prio_idle_abt; eauto.
  pure_auto.
  eapply absinfer_eq. 
  eapply absabort_rule.
    (********* OSTCBCur prio idle finished ****************)
  (* L19:OSTCBCur′→OSTCBStat =ₑ OSTCBCur′→OSTCBStat |ₑ ′OS_STAT_POSTQ;ₛ *)
  unfold AOSTCBList.
  hoare unfold.
  lets Fget: TCBListP_head_in_tcb H37.
  destruct Fget as (st & sus & Fget).
  lets Fget': Fget.
  eapply TcbMod.join_get_r in Fget'; eauto.
  rewrite Fget' in Fget_ct. inverts Fget_ct.
  assert (Hveq: x21 = Vnull /\ i7 = $ OS_STAT_RDY).
  {
    lets Hget_r: get_tcb_stat_rdy H37 Fget.
    unfold V_OSTCBStat,V_OSTCBEventPtr in Hget_r.
    simpl in Hget_r.
    clear -Hget_r.
    destruct Hget_r; pauto.
  }
  destruct Hveq as (Hvptr & Hvst). substs.
  
  hoare forward.
  struct_type_match_solver.
  (* L20: OSTCBCur′→OSTCBDly =ₑ timeout′;ₛ*)
  change (Int.or ($ OS_STAT_RDY) ($ OS_STAT_POSTQ)) with ($ OS_STAT_POSTQ).
  hoare forward.
  
  (* prepare pre for OS_EventTaskPostWait*)
  hoare_lifts_trms_pre (Aisr , Ais, A_isr_is_prop,aemp_isr_is).
  transform_pre a_isr_is_prop_split ltac:(idtac).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).

  hoare_split_pure_all.
  hoare_unfold.
  
  hoare forward.
  apply isptr_zh; auto.
  
  unfold node.
  unfold AEventNode.
  sep pauto.
  sep cancel Astruct.
  instantiate (3:=(DMsgQ (Vptr (v'21, Int.zero))
            (x9
             :: x8
                :: x0
                   :: x1
                      :: x2
                         :: Vint32 i0
                            :: Vint32 i :: Vptr (v'33, Int.zero) :: nil)
            (x10 :: x11 :: nil) v2)).
  unfold AOSEvent, AEventData.
  unfold AOSEventTbl.
  unfold AMsgData. 
  unfold AOSQCtr, AOSQBlk; unfold node.
  sep normal. sep eexists.
  sep cancel AOSPostEventTbl.
  sep cancel AOSRdyTblGrp.
  sep cancel p_local.
  sep cancel OS_EVENT_TBL_SIZE.
  sep cancel OS_MAX_Q_SIZE.
  sep pauto; eauto.
  sep cancel OS_Q_FREEBLK.
  sep cancel Astruct.
  sep cancel Astruct.
  eauto.
  unfolds; simpl;eauto.
  unfolds; simpl;eauto.
  unfolds; simpl;eauto.
  unfolds; simpl;eauto.
  split; auto; go.
  unfolds;simpl;eauto.
  split; auto; go.
  split; auto; go.
  split; auto; go.
  unfolds;simpl;eauto.
  split.
  unfolds;simpl;eauto.
  eexists.
  split.
  unfolds;simpl;eauto.
  eapply Int.eq_false; eauto.
  eapply tcblist_p_node_rl;eauto.
  go.
  intros.
  sep auto.
  intros.
  sep auto.
  clear -H1; pure_auto.

  (* OS_EventTaskPostWait post *)
  hoare_ex_intro.
  unfold OS_EventTaskPostWaitPost.
  unfold OS_EventTaskPostWaitPost'.
  unfold getasrt.

  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  inverts H47.
  unfold V_OSTCBY,V_OSTCBBitX,V_OSTCBBitY,V_OSEventGrp in H62.
  simpl in H62.
  simpljoin1.
  inverts H62.
  inverts H63.
  inverts H64.
  inverts H69.
  inverts H48.
  inverts H49.

(******************  function call finished **************)

  hoare_lifts_trms_pre (Aop , absecblsid, abstcblsid, ostmid, curtid, EvtInv_part2).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qtimedpost_absinfer_ovf_block;eauto.
  pure_auto.
  eapply qpost_ovf_prop1; eauto.
  clear - Hif_cond; pauto.
  apply absinfer_eq.

  unfold AOSTCBPrioTbl.
  hoare_split_pure_all.
  lets cp : H37.
  destruct cp as (td & vv & tcblss & asbs & Hveq & Hnes & Htcj & Htp & Htlis).
  destruct asbs.
  destruct p.
  destruct p.
  destruct Htp as (_ & _ & Hrsl & _).

  funfold Hrsl.
  assert (0<= Int.unsigned x < 64). 
  {
    lia.
  }

  assert (prio_neq_cur v'12 (v'41, Int.zero) x). 
  {
    eapply R_PrioTbl_P_impl_prio_neq_cur; eauto.  
  }
  inverts Hveq.

  (* ** ac: SearchAbout (A_isr_is_prop). *)
  hoare_lifts_trms_pre (Aisr , Ais, Aier).
  transform_pre add_a_isr_is_prop ltac:(idtac).
  transform_pre add_aemp_isr_is_prop ltac:(sep cancel Aisr; sep cancel Ais; sep cancel Aier).
  simpl update_nth_val.

  hoare forward prim.
  (* **exict** *)
  sep cancel p_local.
  sep cancel Aier.
  (* AOSPrioTbl *)
  unfold AOSTCBPrioTbl.
  sep pauto.
  sep cancel OSPlaceHolder.
  sep cancel vhold_addr.
  sep_lifts_trms EvtInv.
  eapply fold_EvtInv_frm'.
  trycancel_EvtInv.
  cancel_corecommuinv.
  sep_lifts_trms EvtInv_part2.
  eapply evtinv_part2_set_tcbvl_mid_preserve; [idtac | sep cancel EvtInv_part2].
  (* TCBList_P *)
  eapply TCBList_P_Combine; eauto.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat (dllseg v'4).
  eapply tcbdllseg_get_last_tcb_ptr; eauto.
    (* AOSTCBList *)
  unfold AOSTCBList.
  unfold tcbdllseg.
  unfold dllseg at 2.
  fold dllseg.
  sep pauto.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  repeat (sep cancel dllseg).
  sep cancel node.

  unfold AECBList.
  sep pauto.
  eapply evsllseg_compose;
   [idtac | idtac | idtac 
         | sep cancel AEventNode; 
           sep cancel evsllseg;
           sep cancel evsllseg]; try eauto.
  cancel_partitioninv.
  eapply tcbdllflag_hold; [idtac | sep cancel tcbdllflag; exact_s].
  eapply tcbdllflag_hold_middle.
  simpl; auto.

        (**** ecblist_P ****)
     eapply ecblist_p_compose'.
     eapply R_ECB_ETbl_P_high_tcb_block_hold_postq; eauto.
     eapply R_ECB_PETbl_P_high_tcb_block_hold_postq; eauto.
     eapply  ECBList_P_high_tcb_block_hold_postq; eauto.
     eapply ejoin_get_none_l.
     2:eauto.
     eapply EcbMod.join_get_l; eauto.
     apply EcbMod.get_a_sig_a.
     eapply TcbMod.beq_refl.
     eapply  ECBList_P_high_tcb_block_hold_postq; eauto.
     eapply ejoin_get_none_r.
     2:eauto.
     apply EcbMod.get_a_sig_a.
     eapply TcbMod.beq_refl.
     2:{ unfold EcbMod.joinsig.
           unfold join.
           simpl.
           unfold sig; simpl.
           erewrite <- EcbMod.set_sig.
           (* ** ac: Check EcbMod.join_set_l. *)
            eapply EcbMod.join_set_l.
            eauto.
            unfold EcbMod.indom; eexists.
            apply EcbMod.get_a_sig_a.
            eapply TcbMod.beq_refl.
       }
     2:{
        eapply EcbMod.join_set_r.
        eauto.
        unfold EcbMod.indom; eexists.
        eapply EcbMod.join_get_l; eauto.
        apply EcbMod.get_a_sig_a.
        eapply TcbMod.beq_refl.
        }

  assert(Hif_cond': Int.unsigned i0 <=Int.unsigned i).
  { clear -Hif_cond.
  rewrite Z.le_lteq.
  destruct Hif_cond.
  left; rewrite <- Intlt_true_is_Zlt; auto.
  right; rewrite <- Inteq_true_is_Zeq. symmetry;rewrite Int.eq_sym;auto.
  }
  assert (Hsize_eq: Int.unsigned i0 =Int.unsigned i).
  {  clear - H36 Hif_cond'.
  funfold H36. apply _mathsolver.Z_has_le.le_antisymm.
  auto. auto.
  }
     {
  clear -Hrlh Hsize_eq.
  unfolds in Hrlh.
  unfolds.
  simpljoin1; splits; eauto.
  unfold RH_ECB_P in H2.
  simpljoin1. 
  unfolds.
  splits;auto.

  unfold MatchLHMsgLength in H0.
  simpljoin1. unfold V_OSQEntries in H0;simpl in H0.
  
  unfold MatchLHMsgSize in H1. 
  simpljoin1. unfold V_OSQSize in H1; simpl in H1.
  inverts H0.
  rewrite Int.repr_unsigned in H1.
  inverts H1.
  rewrite H6 in Hsize_eq.
  rewrite Hsize_eq.
  rewrite Nat2Z.id.
  introv Hf; destruct Hf; auto.

  unfold MatchLHMsgLength in H0.
  simpljoin1. unfold V_OSQEntries in H0;simpl in H0.

  unfold MatchLHMsgSize in H1.
  simpljoin1. unfold V_OSQSize in H1; simpl in H1.
  inverts H0.
  rewrite H6 in Hsize_eq.
  rewrite Int.repr_unsigned in H1.
  inverts H1.
  rewrite Hsize_eq.
  rewrite Nat2Z.id.
  intros. auto.
}
 (* TCBList_P *)
   eapply TCBList_P_tcb_block_hold;eauto.
   eapply TcbMod_join_impl_prio_neq_cur_r; eauto.

  clear Fget'.
  eapply TCBList_P_tcb_block_hold' with (prio := x); eauto.
  eapply TcbMod_join_impl_prio_neq_cur_r; eauto.  
  eapply TcbMod.join_comm; eauto. 

  unfold join; simpl.
  eapply TcbMod.join_set_r; eauto.
  unfolds; eexists; eauto.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  (*RH_PrioTbl_P*)
  eauto.
  (*R_PrioTbl_P*)
  eapply  TcbMod_set_R_PrioTbl_P_hold ; eauto.
  (*RL_RTbl_PrioTbl_P*)
  eapply rtbl_remove_RL_RTbl_PrioTbl_P_hold ; eauto.

  eapply  RH_CurTCB_high_block_hold_postq ; eauto.
  eapply RH_TCBList_ECBList_P_high_block_hold_postq; eauto.
  pure_auto.
(******************** ex_critical finished ***********************)

  hoare forward.
  unfold isflag; auto.
  pure_auto.

  introv Hsat.
  sep destruct Hsat.
  sep eexists.
  sep cancel p_local.
  simpl;auto.

  introv Hsat.
  sep destruct Hsat.
  sep eexists.
  sep cancel p_local.
  simpl;auto.

  (* ** ac: Print OS_SchedPost. *)
  unfold OS_SchedPost.
  unfold OS_SchedPost'.
  unfold getasrt.
  hoare_split_pure_all.
  lzh_inverts_logic.

(* enter critical *)
  clear -H1 Htimele.
  hoare forward prim.
  hoare_unfold.

  rename v'18 into vcspace.
  rename v'19 into v19. 
  rename v'20 into v20. 
  rename v'22 into v22. 

  rename v'23 into v'18. 
  rename v'24 into v'19. 
  rename v'25 into v'20. 
  rename v'26 into v'22. 
  rename v'27 into v'23. 



(*   clear H47 Fget Fget'. *)
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
(*   unfold AECBList. (* used for OS_EventPostTO*) *)
  hoare_split_pure_all.
  mytac.

  (* ** ac: Check low_stat_q_impl_high_stat_q. *)
  assert (Fget: exists st sus, TcbMod.get v'22 (v'41, Int.zero) = Some (i3, st, x6, sus)).
  {
    eapply TCBListP_head_in_tcb'; try eauto.
  }
  destruct Fget as (st & sus & Fget).
  lets Fget': Fget.
  eapply TcbMod.join_get_r in Fget';eauto.

  eapply backward_rule1.
  introv Hsat.
  eapply unfold_EvtInv_frm.
  sep cancel EvtInv.
  eauto.
  unfold EvtInv_part1.
  hoare unfold.

  hoare_lifts_trms_pre (Aop,absecblist,abstcblist,ostm,oscurt).
  assert (Hst_cond: ((st = rdy /\ sus = false) \/ ((st = wait (os_stat_postq (v'40, Int.zero)) None /\ sus = false) )) 
                       \/ ~((st = rdy /\ sus = false) \/(( st = wait (os_stat_postq (v'40, Int.zero)) None /\ sus = false) ))) by tauto.
  destruct Hst_cond as [Hst_cond | Habt].
  Focus 2.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qtimedpost_absinfer_p_aftersch_abt; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  eapply absabort_rule.
  (* ((st = rdy ) \/ ((st = wait (os_stat_postq (v'38, Int.zero)) Int.zero) ))  *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qtimedpost_absinfer_p_aftersch; try eauto.
  can_change_aop_solver.
  apply absinfer_eq.

  lzh_hoare_if2.
(******OSTCBCur->OSTCBEventPtr != null , timeout *******************)
  Focus.
  destruct H23 as (Hif & _).
  destruct H13 as [Hptr | ((eptr_b & eptr_i) & Hptr)]; subst;
  simpl in Hif; try change (Int.notbool Int.one) with Int.zero in Hif; tryfalse.
  destruct Hst_cond as [(Hrdy & Hsus_eq) | (Hwait & Hsus_eq)]; subst.
  (* st = rdy *)
  {
     false.
     eapply get_tcb_stat_rdy in Fget; eauto.
     destruct Fget as (_ & Hf).
     inverts Hf.
  }
  (* st = wait os_stat_postq *)
  assert (Hvst: (i4 = ($ OS_STAT_POSTQ) /\ Vptr (eptr_b, eptr_i) = Vptr (v'40, Int.zero) /\ 
                                i5 = Int.zero /\ prio_not_in_tbl i3 v'8)    ).
  {
  eapply get_tcb_stat_postq in Fget; eauto.
  clear -Fget.
  simpljoin.
  inverts H; inverts H0; inverts H1.
  auto.
  }

  unfold AECBList.
  hoare unfold.
  assert (Hprange: 0 <= Int.unsigned i3 < 64). 
  {
  lets cp : H9.
  destruct cp as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
  destruct asbs'.
  destruct p.
  destruct p.
  destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').

  funfold Hrsl'.
  eauto.
  }
  hoare_assert_pure (isptr v'3).
  { get_hsat Hsat.
     sep_lifts_trms_in Hsat (dllseg v'3).
     lets Hisp: oscore_common.dllseg_head_isptr' Hsat. auto.
  }
  eapply pure_split_rule'; introv Hptr.
  destruct Hptr as [Hnull | (tcb_head & Heq)];
  subst v'3. tryfalse.
  rename v'40 into pid.
  assert (Fget_ectr: exists et etbl petbl, get_ectr (Vptr (pid, Int.zero)) v'26 v'4 = Some (et,etbl, petbl)).
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

  (*call OS_PostEventTO*)
  hoare_lifts_trms_pre (Aisr,Ais,aemp_isr_is).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  hoare forward.
  unfold  node.
  sep cancel AEventNode.
  sep cancel p_local.
  sep pauto.
  sep cancel Astruct.
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

  unfold OS_EventPostTOPost.
  unfold OS_EventPostTOPost'.
  unfold getasrt.
  hoare_split_pure_all.
  (* getasrt is meaning of notation PRE *)
  (*end of OS_EventTO*)
  lzh_inverts_logic.

  mytac.
  inverts H28.
  rename v'38 into vy. rename v'39 into vbitx. rename v'40 into vbity.
  inverts H26. inverts H35. inverts H36.

  assert (Heg': exists ml size pwl wls, EcbMod.get v'10 (pid, Int.zero) = Some (absmsgq ml size pwl, wls) 
                                                        /\ In (v'41, Int.zero) pwl).
  {
  clear -H Fget'.
  funfold H.
  funfold H.
  eapply H6; try eauto.
  }
  destruct Heg' as (ml & size & pwl & wls & Heg' & Hinpwl).

 (* new add about rgrp update *)
  hoare unfold.
  hoare forward.
  clear -H43. pauto.
  struct_type_match_solver.
  lets Hcp': H40.
  eapply nth_upd_eq in H40. subst v'38.
  (* end of rgrp update *)
  (* new add about rtbl update *)
  assert (Hvyx_range: Int.unsigned vy < 8 /\ Int.unsigned vbitx <= 128).
  {
     lets cp : H9.
  destruct cp as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
  destruct asbs'.
  destruct p.
  destruct p.
  destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
   eapply OSETWaitPure.range_ostcby; eauto.
  }
  destruct Hvyx_range as (Hy_range & Hbx_range).
  rename H22 into Hrtbl_len; rename v'8 into rtbl.
  assert (Hy_range': (Z.to_nat (Int.unsigned vy) < length rtbl)%nat).
  {
    rewrite Hrtbl_len.  clear -Hy_range.
    change (∘ OS_RDY_TBL_SIZE) with 8%nat.
    auto with zarith.
  }
  assert (Hy_range'':  Int.unsigned vy <= 7).
  {
    auto with zarith.
  }

  assert (exists i, nth_val' (Z.to_nat (Int.unsigned vy)) rtbl = Vint32 i /\
                    Int.unsigned i <= 255) as nth_val_rtbl.
  {
    lets Hx: array_int8u_nth_lt_len H3.
    eapply Hx.
    rewrite Hrtbl_len.
    clear -Hy_range.
    change (∘ OS_RDY_TBL_SIZE) with 8%nat.
    auto with zarith.
  }
  destruct nth_val_rtbl as [rrow [nth_val_rtbl rrow_le_255]].

  unfold AOSTCBPrioTbl.
  hoare unfold.
  assert (nth_val ∘ (Int.unsigned i3) v' = Some (Vptr (v'25, Int.zero)) 
                  /\ (v'25, Int.zero) <> v'13) as nth_val_ptbl.
  {
    clear -Fget' H40.
    funfold H40.
    eapply H0; eauto.
  }
  destruct nth_val_ptbl as [nth_val_ptbl ct_neq_vhold].

  hoare unfold.
  hoare forward.

  struct_type_match_solver.
  rewrite nth_val_rtbl.
  rtmatch_solve.
  struct_type_match_solver.
  rewrite nth_val_rtbl. simpl. pauto.
  struct_type_match_solver.

  (* end of rtbl update *)
  
  hoare_lifts_trms_pre (Aop,absecblist,abstcblist,ostm, oscurt, EvtInv_part2).
  
  assert (Het: v'2 = Vint32 (Int.repr OS_TIMEOUT) 
                  \/ v'2 <> Vint32 (Int.repr OS_TIMEOUT)) by tauto.
  destruct Het. 
  subst.
   (* v'2 = OS_TIMEOUT  *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qtimedpost_absinfer_timeout; try eauto.
  can_change_aop_solver.
  apply absinfer_eq.

  fold V_OSTCBPrev.
  fold V_OSTCBNext.
  fold_AEventNode_r.
  
  (* EXIT_CRITICAL;ₛ  *)
  hoare_lifts_trms_pre (Aisr,Ais,Aier).
  transform_pre add_aemp_isr_is_prop ltac:(sep cancel Aier; sep cancel Aisr; sep cancel Ais).
  hoare forward prim.
  sep_lifts_trms EvtInv.
  eapply fold_EvtInv_frm'.
  (*AECBList*)
  unfold AECBList.
  sep pauto.

  eapply evsllseg_compose;
  [idtac | idtac | idtac |
  sep cancel AEventNode;
  sep cancel evsllseg;
  sep cancel evsllseg]; try eauto.
  
  unfold V_OSEventListPtr.
  eapply nth_upd_neqrev; try pauto.
  trycancel_EvtInv.
  cancel_corecommuinv.
  sep cancel Aier.
  eapply evtinv_part2_set_tcbvl_mid_preserve; [idtac | sep cancel EvtInv_part2].
  eapply TCBList_P_Combine; eauto.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat (tcbdllseg (Vptr tcb_head) ).
  eapply tcbdllseg_get_last_tcb_ptr with (s:= s); eauto.
  unfold tcbdllseg.
  sep cancel  (dllseg (Vptr tcb_head)).
  eauto.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel (dllseg (Vptr tcb_head)).
  unfold dllseg.
  fold dllseg.
  unfold node.
  unfold AOSTCBPrioTbl.
  sep pauto.
  sep cancel dllseg.
  sep cancel Astruct.
  sep cancel p_local.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  cancel_partitioninv.
  eapply tcbdllflag_hold; [idtac | sep cancel tcbdllflag; exact_s].
  eapply tcbdllflag_hold_middle.
  simpl; auto.
  eauto.
  eapply R_PrioTbl_P_hold1'; try eauto.

  eapply rl_rtbl_priotbl_p_set_hold; try eauto.
  eapply tcbnode_rl_prop; try eauto.
  eapply nth_val'_imply_nth_val; try eauto.
  rewrite nth_val_rtbl; simpl; auto.

  unfolds; simpl; auto.
  unfolds; simpl; auto.
  split; auto.
  
  split.
  rewrite nth_val_rtbl.
  unfold or. unfold val_inj.
  eapply event_wait_rl_tbl_grp; try eauto.
  eapply tcbnode_rl_prop; try eauto.
  eapply idle_in_rtbl_hold'; try eauto.
  rtmatch_solve.

  clear -H43 H21.
  eapply int_unsigned_or_prop'; auto.
  split.
  eapply array_type_vallist_match_int8u_update_hold'; try eauto.
  rewrite update_nth_val_len_eq. auto.

  {
  assert (Hyx_eq: vy = i3 >>ᵢ $ 3 /\ vbitx = $ 1<<ᵢ(i3&ᵢ$ 7)).
  {
   lets cp : H9.
  destruct H9 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
  destruct asbs'.
  destruct p.
  destruct p.
  destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
  funfold Hrsl'.
  split; auto.
  }
  destruct Hyx_eq as (Hy_eq & Hbx_eq).
  subst vy. subst vbitx. clear Fget'.
  remember (v'23 :: v'18 :: Vptr (v'39, Int.zero) :: x6 :: Vint32 Int.zero
                        :: V$ OS_STAT_POSTQ :: Vint32 i3 :: Vint32 i2 :: Vint32 (i3 >>ᵢ $ 3)
                        :: Vint32 ($ 1<<ᵢ(i3&ᵢ$ 7)) :: Vint32 vbity :: nil) as tcbcur.
  lets Hlem: TCBList_P_hold_for_update_postq_to_rdy.
  specialize Hlem with (tcurl:= tcbcur). subst tcbcur.
  simpl update_nth_val in Hlem.
  eapply Hlem;try eauto.
}

  (*sencond TCBList_P (Vptr tcb_head) ... *)
  {
  assert (Hyx_eq: vy = i3 >>ᵢ $ 3 /\ vbitx = $ 1<<ᵢ(i3&ᵢ$ 7)).
  {
   lets cp : H9.
  destruct H9 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
  destruct asbs'.
  destruct p.
  destruct p.
  destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
  funfold Hrsl'.
  split; auto.
  }
  destruct Hyx_eq as (Hy_eq & Hbx_eq).
  rewrite nth_val_rtbl. unfold or. unfold val_inj.
  fold nat_of_Z.
  subst vy. subst vbitx.
  eapply TCBList_P_rtbl_add_simpl_version; try eauto.
  eapply nth_val'2nth_val. unfold nat_of_Z. auto.

  clear - H7 H8 H9 Fget H40.
  apply TcbMod.map_join_comm in H7.
  destruct H9 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
  destruct asbs'.
  destruct p.
  inverts Hveq'.
  unfold TcbJoin in Htcj'.
  lets Hget: TcbMod.join_sig_get Htcj'.
  rewrite Hget in Fget. inverts Fget.
  lets Hjoin: join_join_merge H7 Htcj'.
  eapply TCBList_P_rtbl_add_lemma_1.
  eauto.
  apply TcbMod.map_join_comm in Htcj'.
  eauto.
  unfold TcbJoin.
  auto with jdb.
  unfold TcbJoin.
  eauto.
  funfold H40. auto.
  }

  (* start subgoal join*)
  destruct H9 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
  inverts Hveq'.
  unfold TcbJoin in Htcj'.
  unfold TcbMod.joinsig.
  unfold join,sig,TcbMap in Htcj'.
  eapply TcbMod.joinsig_set_set; try eauto.

  (* ECBList_P *)
  assert (Hyx_eq: vy = i3 >>ᵢ $ 3 /\ vbitx = $ 1<<ᵢ(i3&ᵢ$ 7)).
  {
   lets cp : H9.
  destruct H9 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
  destruct asbs'.
  destruct p.
  destruct p.
  destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
  funfold Hrsl'.
  split; auto.
  }
  destruct Hyx_eq as (Hy_eq & Hbx_eq).
  subst vy. subst vbitx.
  eapply ECBList_P_hold_for_update_postq_to_rdy'; try eauto.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat (evsllseg).
  eapply evsllseg_list_len_eq; try eauto.
  (* end of ECBList_P *)
  unfold RH_CurTCB.
  rewrite TcbMod.map_get_set.
  eauto.
  (* RH_TCBList_ECBList_P *)
  eapply RH_TCBList_ECBList_P_hold_for_postq_to_rdy'; try eauto.
  pure_auto.

  (*RETURN ′ OS_TIMEOUT*)
  hoare forward.
  
  (* etype <> OS_TIMEOUT  *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qtimedpost_absinfer_timeout_abt; try eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  eapply absabort_rule.
  
  (******TCBMsg <> null , post to *******************)
  assert (x7 = Vnull). 
  { clear - H13 H23. 
    destruct H13 as [Hnull | ((pb & pf) & Hf)]; subst;
    simpl in H23; auto.
    change (Int.notbool Int.zero) with Int.one in *;
    destruct H23; tryfalse.
  }
 subst.
  destruct Hst_cond as [(Hst & Hsus_eq) | (Hst & Hsus_eq)]; subst sus.
  2:{ eapply get_tcb_stat_postq in Hst; eauto.
        destruct Hst as (_ & Hf & _); inverts Hf.
  }
  lets Hget: Fget.
  eapply get_tcb_stat_rdy in Hget; eauto.
  destruct Hget as (Hstat & _); inverts Hstat.
  subst st.
  hoare forward.

  hoare_lifts_trms_pre (Aop,absecblist, abstcblist,ostm,oscurt).

  assert (Het: v'2 = Vint32 (Int.repr OS_NO_ERR) 
                  \/ v'2 <> Vint32 (Int.repr OS_NO_ERR)) by tauto.
  destruct Het. 
  2:{
   (* v'2 <> OS_NO_ERR  *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qtimedpost_absinfer_block_to_abt; try eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  eapply absabort_rule.
  }
  (* v'2 = OS_NO_ERR  *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qtimedpost_absinfer_block_to; try eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  subst.

  (* EXIT_CRITICAL;ₛ  *)
  hoare forward prim.
  sep cancel p_local.
  sep cancel Aier.
  sep_lifts_trms EvtInv.
  eapply fold_EvtInv_frm'.
  sep cancel EvtInv_part2.
  trycancel_EvtInv.
  cancel_corecommuinv.
  unfold AOSTCBList.
  unfold tcbdllseg.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  sep pauto; eauto.
  simpl dllseg at 2.
  unfold node.
  sep cancel AOSRdyGrp.
  sep pauto; eauto.
  sep cancel Astruct.
  sep cancel dllseg.
  sep cancel dllseg.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.

  unfolds ;simpl;auto.
  unfolds ;simpl;auto.
  split;auto.
  struct_type_match_solver.
  auto.
  pure_auto.
  (*RETURN ′ OS_NO_ERR*)
  hoare forward.
  simpl.
  intro;tryfalse.
  splits; eauto.
  unfold OS_NO_ERR.
  clear. int auto.

  (*elim afalse*)
  hoare forward.
  (* ∗ pq ′ → OSQIn =ₑ message ′;ₛ*)
  lets Hx: osq_same_blk_st_in' H36.
  destruct Hx as (qin_off & Heq); subst.
  simpl in H34; inverts H34.
  lets Hy: wellq_in_props H38 Hrlh H36;eauto.
  simpljoin.

  hoare forward; eauto.
  go.
  apply isptr_zh;auto.

  (*  pq ′ → OSQIn =ₑ pq ′ → OSQIn +ₑ ′ 1;ₛ*)
  hoare forward.
  go.
  (*  pq ′ → OSQEntries =ₑ pq ′ → OSQEntries +ₑ ′ 1;ₛ*)
  hoare forward.
  go.

  (*L37: If(pq ′ → OSQIn ==ₑ pq ′ → OSQEnd)*)
  pure intro.
  lets Hx: wellformedosq_ens_add_1 H38 Hrlh H36.
  assert (Hqend: exists qend_off, x0 = Vptr (v'33, qend_off)).
  { clear -H36.
     funfold H36.
     destruct x1. destruct x6.
     funfold H8.
     funfold H0.
     simpl in H5; inverts H5.
     destruct ((b =? b0)%positive) eqn: eq1; tryfalse.
     eapply Peqb_true_eq in eq1; subst.
     eauto.
  }
  destruct Hqend as (qend_off & Heq); subst.
  hoare remember (1:: 2:: 3:: nil)%nat pre.
  eapply seq_rule.
  instantiate (1:= (<||
  spec_code_cons
    (qtimedpost (Vptr (v'40, Int.zero) :: Vint32 Int.zero :: x :: v'2 :: nil)) v'1
  ||>  **
  LV pq @ OS_Q ∗ |-> Vptr (v'21, Int.zero) **
  Astruct (v'21, Int.zero) OS_Q
    (x9
     :: x8
        :: Vptr (v'33, qend_off)
           :: (if Int.eq (qin_off +ᵢ  Int.mul ($ 1) ($ 4)) qend_off
              then x8
              else Vptr (v'33, qin_off +ᵢ  Int.mul ($ 1) ($ 4)))
              :: x2
                 :: Vint32 i0 :: Vint32 (i +ᵢ  $ 1) :: Vptr (v'33, Int.zero) :: nil) **
  H48)).
  subst.
  hoare forward.
  go.
  go.
  pure_auto.
  (*L38: pq ′ → OSQIn =ₑ pq ′ → OSQStart*)
  hoare forward.
  go.
  get_hsat Hsat.
  rewrite peq_true in Hsat.
  destruct Hsat as [Hsat | Hsat];
  sep_lifts_trms_in Hsat val_inj;
  eapply sep_pure_split in Hsat; destruct Hsat as (Hif & Hsat);
  destruct (Int.eq (qin_off +ᵢ  Int.mul ($ 1) ($ 4)) qend_off) eqn: eq1;
  simpl in Hif;  destruct Hif; tryfalse;
  sep pauto.
  subst.

  (*high level step*)
  lets Hx1: ecbmod_absmsgq Hrlh.
  lets Hx2: EcbMod.join_joinsig_get Hjo  Hjo' .
  simpljoin.
  assert (Hwl: x5 = nil).
  { eapply rlh_ecb_nowait_prop with (i:= Int.zero); eauto. }
  subst.
  assert (Hif: Int.ltu i0 i = false /\ Int.eq i i0 = false).
  { clear -H37.
     destruct (Int.ltu i0 i) eqn: eq1;
     destruct (Int.eq i i0) eqn: eq2;
     simpl in H37; try change (Int.ltu Int.zero Int.one) with true in H37;
     simpl in H37; destruct H37; auto; tryfalse.
   }
  assert (Hif': Int.ltu i i0 = true).
  { clear -Hif.
     simpljoin.
     eapply int_ltu_prop; eauto.
     eapply semacc_int_eq_false; rewrite Int.eq_sym; eauto.
  }
  assert (Hlt: Z.of_nat (length x0) < Int.unsigned x1).
  { eapply qpost_no_wait_prop'; eauto. }

  hoare_lifts_trms_pre (Aop , absecblsid, abstcblsid, ostmid, curtid,EvtInv_part2).
  assert (Hor: v'2 <> (Vint32 (Int.repr OS_NO_ERR)) \/ 
                 v'2 = (Vint32 (Int.repr OS_NO_ERR))) by tauto.
  inversion Hor.
  (* v'2 <> ... *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qtimedpost_absinfer_nowt_succ_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule.
  (* v'2 = ... *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qtimedpost_absinfer_nowt_succ; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  (*L39: EXIT_CRITICAL;ₛ*)
  destruct H1 as [Hnull | ((xb & xoff) & Hxid)]; subst;
  simpl in H11; destruct H11; tryfalse.
  hoare forward prim.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel tcbdllflag.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eapply fold_EvtInv_frm'.
  sep cancel EvtInv_part2.
  cancel_corecommuinv.
  trycancel_EvtInv.
  unfold AECBList.
  sep normal.
  eexists.
  sep cancel OSEventList.
  sep split.
  eapply evsllseg_compose with
       (l:= (V$ OS_EVENT_TYPE_Q :: Vint32 Int.zero :: Vint32 i2 :: Vptr (v'21, Int.zero) :: x3 :: v'' :: Vint32 pegrp :: x6 :: nil))
       (msgq:= (DMsgQ (Vptr (v'21, Int.zero))
                        (x9
                          :: x8
                             :: Vptr (v'33, qend_off)
                                :: (if Int.eq (qin_off +ᵢ  Int.mul ($ 1) ($ 4)) qend_off
                                     then x8
                                     else Vptr (v'33, qin_off +ᵢ  Int.mul ($ 1) ($ 4)))
                                 :: x2 :: Vint32 i0 :: Vint32 (i +ᵢ  $ 1) :: Vptr (v'33, Int.zero) :: nil)
                        (x10 :: x11 :: nil)
                        (update_nth_val
                          (Z.to_nat ((Int.unsigned qin_off - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
                          v2 (Vptr (xb,xoff))))); eauto.
  unfolds; simpl; eauto.
  sep cancel evsllseg.
  sep cancel evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold AEventData.
  unfold AMsgData.
  unfold AOSQCtr.
  unfold AOSQBlk.
  unfold AOSEventTbl.
  unfold node.
  sep pauto.
  sep cancel AOSPostEventTbl.
  sep cancel OS_MAX_Q_SIZE.
  sep cancel OS_EVENT_TBL_SIZE.
  sep cancel OS_Q_FREEBLK.
  sep cancel OS_EVENT.
  sep cancel Astruct.
  cancel_partitioninv.
  eauto.
  eauto.
  unfolds; simpl; eauto.
  eauto.
  eauto.
  unfolds; simpl; eauto.
  eauto.
  auto.
  split; auto. go.
  unfolds; simpl; eauto.
  { (* WellformedOSQ *)
     destruct (Int.eq (qin_off +ᵢ  Int.mul ($ 1) ($ 4)) qend_off) eqn: eq1.
     eapply get_wellformedosq_in_setst; eauto.
     rewrite peq_true; rewrite eq1; pure_auto.
     eapply get_wellformedosq_in_setst'; eauto.
     introv Hf; invert Hf; introv Hf; subst.
     rewrite Int.eq_true in eq1; tryfalse.
  }
  split; auto.
  destruct (Int.eq (qin_off +ᵢ  Int.mul ($ 1) ($ 4)) qend_off) eqn: eq1;
  go.
  eauto.
  split; auto. go.
(*   ECBList_P *)
  eapply msgqlist_p_compose'; eauto.
  { (* RLH_ECBData_P *)
    destruct (Int.eq (qin_off +ᵢ  Int.mul ($ 1) ($ 4)) qend_off) eqn: eq1.
    eapply semacc_int_eq_true in eq1; subst qend_off.
    eapply rlh_ecbdata_in_end;eauto.
    eapply rlh_ecbdata_in_noend; eauto.
    introv Hf; invert Hf; introv Hf; subst.
    rewrite Int.eq_true in eq1; tryfalse.
  }
  eapply EcbMod.joinsig_set;eauto.
  eapply EcbMod.joinsig_set_set;eauto.
  eapply rh_tcbls_mqls_p_setmsg_hold;eauto.
  pure_auto.

  (*L40: RETURN ′ OS_NO_ERR*)
  hoare forward.
  unfold rev; simpl.
  intro. tryfalse.
  splits; eauto.
  unfold Int.zero.
  clear. int auto.

  Unshelve.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
Qed.

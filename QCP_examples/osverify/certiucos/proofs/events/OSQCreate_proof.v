Require Import ucos_include.
(* Require Import absop_rules. *)
Require Import OSQCreatePure.
Require Import Lia.

Require Import abs_op.

Require Import os_ucos_h.
Require Import seplog_tactics.
(* new lemmas about q postnew in absop_rules *)
Require Import abs_infer_step.
Require Import ucos_frmaop.
Require Import seplog_lemmas.
Require Import seplog_tactics.
(* Require Import q_common. *)
Require Import sem_lab.
Require Import abs_step.
Require Import abs_infer_abt.
Require Export os_inv.
Require Import evtinv_lemmas.
Require Import hoare_assign_tac_ext.

Lemma  vaj_inj_isptr2_or :
  forall  p q, 
    isptr p -> 
    isptr q -> 
    val_inj
      (bool_and (val_inj (notint (val_inj (val_eq p Vnull))))
                (val_inj (notint (val_inj (val_eq q Vnull))))) =
    Vint32 Int.zero \/
    val_inj
      (bool_and (val_inj (notint (val_inj (val_eq p Vnull))))
                (val_inj (notint (val_inj (val_eq q Vnull))))) = Vnull -> 
    p = Vnull \/ q = Vnull. 
Proof.
  intros.
  unfold isptr in *.
  destruct H, H0;simp join; simpl in *;try(auto).
  destruct x0, x in H1.
  simpl in H1.
  destruct H1; 
    false.
Qed.

Lemma  vaj_inj_isptr2 :
  forall  p q, 
    isptr p -> 
    isptr q -> 
    val_inj
      (bool_and (val_inj (notint (val_inj (val_eq p Vnull))))
                (val_inj (notint (val_inj (val_eq q Vnull))))) <>
    Vint32 Int.zero -> exists x y, p = Vptr x /\ q = Vptr y. 
Proof.
  intros.
  unfold isptr in *.
  destruct H, H0; simp join;  simpl in *; tryfalse.
  unfold Int.notbool in H1.
  false.
  int auto.
  destruct x.
  simpl in H1.
  false.
  int auto.
  destruct x.
  simpl in H1.
  false.
  int auto.
  destruct x0, x.
  eauto.
Qed.


(*  Lemma isptr_zh :    *)
Lemma isptr_zh :
  forall x, isptr x ->
            match x with
              | Vundef => false
              | Vnull => true
              | Vint32 _ => false
              | Vptr _ => true
            end = true.
Proof.
  intros.
  unfolds in H; destruct H.
  substs; auto.
  destruct H; substs; auto.
Qed.

Ltac mytac_getret_l :=
   match goal with
   | |- _ ==> (_ \\// _ ) => intros; eapply adisj_intro; left
   | |- _ |= _ -> _ |= _ ** _ => try eapply astar_mono; try mytac_getret_l
   | |- _ ==> _ ** _ => try eapply astar_mono; try mytac_getret_l; try eauto
   | _ => idtac
 end.

Ltac mytac_getret_r :=
   match goal with
   | |- _ ==> (_ \\// _ ) => intros; eapply adisj_intro; right
   | |- _ |= _ -> _ |= _ ** _ => try eapply astar_mono; try mytac_getret_r
   | |- _ ==> _ ** _ => try eapply astar_mono; try mytac_getret_r; try eauto
   | _ => idtac
 end.

 Ltac mytac_getret_l' :=
 match goal with
 | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
        eapply r_conseq_rule;
        introv; mytac_getret_l; eauto
 | _ => idtac
 end.

 Ltac mytac_getret_r' :=
 match goal with
 | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
        eapply r_conseq_rule;
        introv; mytac_getret_r; eauto
 | _ => idtac
 end.

Require Import sem_common.

Local Open Scope code_scope.

Ltac mytac_lift_absop :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
          match find_aop P with
            | none _ => idtac 1 "no absop in the pre-condition"; fail 1
            | some ?a => hoare lifts (a::nil) pre
          end
  end.

Ltac sep_lift_context_in H trm :=
  match type of H with
    | _ |= ?P =>
      match find_match_context P trm with
         | none _ => idtac 1 "no such term in the Hsat"; fail 1
         | some ?a => sep lifts (a::nil)%nat in H
      end
  end.

Ltac sep_lift_context trm :=
  match goal with
    | |- _ |= ?P =>
      match find_match_context P trm with
         | none _ => idtac 1 "no such term in the Hsat"; fail 1
         | some ?a => sep lifts (a::nil)%nat 
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

(* Lemma ordered_lst: *)
(*   forall lst a b lst', lst = (a, b) :: lst' -> EcbMod.is_orderset lst -> EcbMod.is_orderset lst'. *)
(* Proof. *)
(*   intros. *)
(*   subst lst. *)
(*   simpl in H0. *)
(*   destruct H0; auto. *)
(* Qed. *)

Lemma sum_int_30:
    ($ 4 +ᵢ
     ($ 1 +ᵢ
      ($ 1 +ᵢ
       ($ 1 +ᵢ
        ($ 1 +ᵢ
         ($ 1 +ᵢ
          ($ 1 +ᵢ
           ($ 1 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  Int.zero)))))))))))))) = $31. 
Proof.
  asserts_rewrite ($ 4 +ᵢ  Int.zero = $4). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 4 = $8). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 8 = $12). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 12 = $16). int auto.
  asserts_rewrite ($ 2 +ᵢ  $ 16 = $18). int auto.
  asserts_rewrite ($ 2 +ᵢ  $ 18 = $20). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 20 = $21). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 21 = $22). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 22 = $23). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 23 = $24). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 24 = $25). int auto.
  int auto. int auto. int auto. int auto.
Qed.  

Lemma sum_int_25:
  ($ 1 +ᵢ
     ($ 1 +ᵢ
      ($ 1 +ᵢ
       ($ 1 +ᵢ
        ($ 1 +ᵢ
         ($ 1 +ᵢ  ($ 2 +ᵢ  ($ 2 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  Int.zero)))))))))))) = $26. 
Proof.
  asserts_rewrite ($ 4 +ᵢ  Int.zero = $4). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 4 = $8). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 8 = $12). int auto.
  asserts_rewrite ($ 4 +ᵢ  $ 12 = $16). int auto.
  asserts_rewrite ($ 2 +ᵢ  $ 16 = $18). int auto.
  asserts_rewrite ($ 2 +ᵢ  $ 18 = $20). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 20 = $21). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 21 = $22). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 22 = $23). int auto.
  asserts_rewrite ($ 1 +ᵢ  $ 23 = $24). int auto.
    asserts_rewrite ($ 1 +ᵢ  $ 24 = $25). int auto.
  int auto.
Qed.

Require Import seplog_trm_tacs.
Require Import evauxvar_lemmas.
Require Import evaux_pure. 
Require Import sem_corecommu.

Require Import hoare_forward.
Require Import inv_prop.

 Require Import freeevtlist_lemmas.  

Open Scope code_scope.
Open Scope int_scope.
Open Scope Z_scope.


Lemma absimp_qcre_err_return1 :
  forall P i  sch s, 
    can_change_aop P -> 
    (Int.unsigned i <=? 65535 = true) -> 
    absinfer sch ( <|| qcre (Vint32 i :: Vnull :: nil) ;; s||> ** P) ( <|| s ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq. 

  pure_auto. 
  instantiate (1:=P).
  pure_auto. 
    2 : { eapply absinfer_seq_end; try can_change_aop_solver; try eauto. }
  infer_solver 0%nat. 
Qed.

Lemma absimp_qcre_err_return1_abt :
  forall P i rv sch s, 
    can_change_aop P -> 
    rv<>Vnull ->
    absinfer sch ( <|| qcre (Vint32 i :: rv :: nil) ;; s||> ** P) 
                      ( <|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq. 
  pure_auto. 
  instantiate (1:=P).
  pure_auto. 

  eapply absinfer_choice1. pure_auto.
  pure_auto. auto.
  eapply absinfer_trans.
  eapply absinfer_seq. can_change_aop_solver.
    instantiate (1:=P). can_change_aop_solver.
  eapply absinfer_abt; try eauto; can_change_aop_solver.
  absimp_abt_solver.
    eapply absinfer_seq_abt; can_change_aop_solver. eauto.
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

Lemma absimp_qcre_ecb_avail:
  forall P sch s n els qid  vqid locmp locmp' ptrmp ptrmp' ct muxp semp qp, 
    can_change_aop P ->
    get els qid = None ->
    locmp' = set locmp ct (Vint32 ($__EvLoc_ecbcre1)) ->
    get ptrmp ct = Some (muxp, semp, qp) ->
    ptrmp' = set ptrmp ct (muxp, semp, Vptr qid) ->
    absinfer sch
             (<|| qcre(Vint32 n :: vqid :: nil) ;; s ||> 
                ** HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P) 
             (<|| ( qcre_err(|Vint32 n :: vqid :: nil|) ??qcre_ecb_activate (|Vint32 n :: vqid :: nil|)) ;; s ||> 
                ** HECBList els ** HEvLoc locmp' ** HEvPtr ptrmp' ** HCurTCB ct ** P).  
Proof. 
  introv Hcp Hget Hlmp' Hgtp Hpmp'.
  eapply absinfer_trans.
  unfold qcre.
  eapply absinfer_seq1.  
  can_change_aop_solver.
  eapply absinfer_choice2; can_change_aop_solver.
  intros. auto.
  eapply absinfer_seq.
  can_change_aop_solver.
  can_change_aop_solver.
  infer_solver 0%nat.
Qed.

(* Lemma absimp_qcre_ecb_avail_abt: *)
(*   forall P sch s n els qid v' locmp locmp' ptrmp ptrmp' ct muxp semp qp,  *)
(*     can_change_aop P -> *)
(*     get els qid = None -> *)
(*     (* v' <> Vptr qid ->  *) *)
(*     locmp' = set locmp ct (Vint32 ($__EvLoc_ecbcre1)) -> *)
(*     get ptrmp ct = Some (muxp, semp, qp) -> *)
(*     ptrmp' = set ptrmp ct (muxp, semp, Vptr qid) -> *)
(*     absinfer sch *)
(*              (<|| qcre(Vint32 n :: v' :: nil) ;; s ||>  *)
(*                 ** HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P)  *)
(*              (<|| ABORT ||>  *)
(*                 ** HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P). *)
(* Proof. *)
(*   introv Hcp Hget Hv' Hlmp' Hgtp Hpmp'. *)
(*   eapply absinfer_trans. *)
(*   unfold qcre. *)
(*   eapply absinfer_seq1.   *)
(*   can_change_aop_solver. *)
(*   eapply absinfer_choice2; can_change_aop_solver. *)
(*   intros; auto. *)
(*   eapply absinfer_trans. *)
(*   eapply absinfer_seq1. *)
(*   can_change_aop_solver. *)
(*   eapply absinfer_seq1. *)
(*   can_change_aop_solver. *)
(*   eapply absinfer_abt; can_change_aop_solver. *)
(*   absimp_abt_solver. *)
(*   instantiate (1:=HECBList els ** HEvPtr ptrmp ** HCurTCB ct ** P).  instantiate (1:=locmp). *)
(*   instantiate (1:=qcre_ecb_available (|Vptr qid :: nil|)). instantiate (1:=s0). sep auto. *)
(*   instantiate (1:=HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** P). *)
(*   instantiate (1:=qcre_ecb_available (|Vptr qid :: nil|)). *)
(*   instantiate (1:=s0). *)
(*   sep auto. *)
(*   instantiate (1:=HECBList els ** HEvLoc locmp ** HCurTCB ct ** P). *)
(*   instantiate (1:=qcre_ecb_available (|v' :: nil|)). *)
(*   instantiate (1:=s0).  *)
(*   sep auto. *)
(*   can_change_aop_solver. *)
(*   eapply absinfer_trans. *)
(*   eapply absinfer_seq1. can_change_aop_solver. *)
(*   eapply absinfer_seq_abt; can_change_aop_solver. *)
(*   intros; auto. *)
(*   eapply absinfer_seq_abt; can_change_aop_solver. *)
(*   intros; auto. *)
(* Qed. *)

Lemma absimp_qcre_ecb_avail_abt2:
  forall P sch s n els qid v' locmp locmp' ptrmp ptrmp' ct muxp semp qp, 
    can_change_aop P ->
    get els qid = None ->
    (exists t', tsk_normal_ev locmp ptrmp t' qid) -> 
    locmp' = set locmp ct (Vint32 ($__EvLoc_ecbcre1)) ->
    get ptrmp ct = Some (muxp, semp, qp) ->
    ptrmp' = set ptrmp ct (muxp, semp, Vptr qid) ->
    absinfer sch
             (<|| qcre(Vint32 n :: v' :: nil) ;; s ||> 
                ** HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P) 
             (<|| ABORT ||> 
                ** HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P).
Proof.
  introv Hcp Hget Hnormal Hlmp' Hgtp Hpmp'. 
  eapply absinfer_trans.
  unfold qcre.
  eapply absinfer_seq1.  
  can_change_aop_solver.
  eapply absinfer_choice2; can_change_aop_solver.
  intros; auto.
  eapply absinfer_trans.
  eapply absinfer_seq1.
  can_change_aop_solver.
  eapply absinfer_seq1.
  can_change_aop_solver.
  eapply absinfer_abt; can_change_aop_solver.
  absimp_abt_solver.
  instantiate (1:=HECBList els ** HEvPtr ptrmp ** HCurTCB ct ** P).  
  instantiate (1:=qcre_ecb_available (|v' :: nil|)). instantiate (1:=s0). sep auto.
  instantiate (1:=HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** P).
  instantiate (1:=qcre_ecb_available (|v' :: nil|)).
  instantiate (1:=s0).
  sep auto.
  instantiate (1:=HECBList els ** HEvLoc locmp ** HCurTCB ct ** P).
  instantiate (1:=qcre_ecb_available (|v' :: nil|)).
  instantiate (1:=s0). 
  sep auto.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_seq1. can_change_aop_solver.
  eapply absinfer_seq_abt; can_change_aop_solver.
  intros; auto.
  eapply absinfer_seq_abt; can_change_aop_solver.
  intros; auto.
Qed.  

Lemma absimp_qcre_ecb_activate: 
  forall sch n qid s locmp locmp' ct P els els' v',       
    can_change_aop P ->
    (* Int.ltu ($ Q_SIZE) n  = false ->  *)
    get els qid = None -> 
    els' = (set els qid (absmsgq (nil:list val) n (nil:list tid), nil:list tid)) -> 
    locmp' = set locmp ct (Vint32 ($__EvLoc_ecbcre2)) ->
    v' = Vptr qid ->
    absinfer sch
      (<|| ( qcre_err(|Vint32 n :: v' :: nil|) ?? qcre_ecb_activate (|Vint32 n :: v' :: nil|)) ;; s ||> **
                   HECBList els **  HEvLoc locmp ** HCurTCB ct ** P)
      (<|| s ||> ** HECBList els' ** HEvLoc locmp' ** HCurTCB ct ** P). 
Proof.
  introv Hcop  (* Hlt *)  Hnone Hels' Hlmp' Hv'.
  subst els'. subst locmp'.
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_choice2; can_change_aop_solver.
  auto.
  subst. 
  infer_solver 0%nat.
Qed.   

Lemma absimp_qcre_ecb_activate_abt: 
  forall sch n qid s locmp ct P els v',    
    can_change_aop P ->
    (* Int.ltu ($ Q_SIZE) n  = false ->  *)
    get els qid = None -> 
    v' <> Vptr qid -> 
    absinfer sch
      (<|| ( qcre_err(|Vint32 n :: v' :: nil|) ?? qcre_ecb_activate (|Vint32 n :: v' :: nil|)) ;; s ||> **
                   HECBList els **  HEvLoc locmp ** HCurTCB ct ** P)
      (<|| ABORT  ||> ** HECBList els ** HEvLoc locmp ** HCurTCB ct ** P). 
Proof.
  introv Hcop  (* Hlt *)  Hnone Hv'.
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_choice2; can_change_aop_solver.
  auto.

  eapply absinfer_trans.
  eapply absinfer_seq1.
  can_change_aop_solver.
  instantiate (1:=ABORT).
  eapply absinfer_abt.
  can_change_aop_solver.
  can_change_aop_solver.
  absimp_abt_solver.
  instantiate (1:=HECBList els ** HCurTCB ct ** P).
  instantiate (1:=locmp).
  instantiate (1:=qcre_ecb_activate (|Vint32 n :: v' :: nil|)).
  instantiate (1:=s0).
  sep auto.

  instantiate (1:=HECBList els ** HEvLoc locmp ** P).
  instantiate (1:=ct).
  instantiate (1:=qcre_ecb_activate (|Vint32 n :: v' :: nil|)).
  instantiate (1:=s0).
  sep auto.

  can_change_aop_solver.

  eapply absinfer_seq_abt; can_change_aop_solver. 
  auto. 

Qed.     


Lemma absimp_qcre_err: 
  forall sch n v' s locmp locmp' ptrmp ptrmp' ct qid P els ,       
    can_change_aop P ->
    v' = Vnull -> 
    locmp' = set locmp ct (Vint32 ($__EvLoc_normal)) ->
    get ptrmp ct = Some (Vnull, Vnull, Vptr qid) ->
    ptrmp' = set ptrmp ct (Vnull, Vnull, Vnull) -> 
    absinfer sch
      (<|| ( qcre_err(|Vint32 n :: v' :: nil|) ?? qcre_ecb_activate (|Vint32 n :: v' :: nil|)) ;; s ||> **
             HECBList els **  HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P)
      (<|| s ||> ** HECBList els ** HEvLoc locmp' **  HEvPtr ptrmp' ** HCurTCB ct ** P).  
Proof.
  introv Hcop Hv' Hlmp' Hpmp Hpmp'.
  subst. 
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_choice1; can_change_aop_solver.
  auto.
  infer_solver 0%nat.
Qed.  

Lemma absimp_qcre_err_abt: 
  forall sch n v' s locmp  ptrmp ct qid P els ,  
    can_change_aop P ->
    v' <> Vnull -> 
    get ptrmp ct = Some (Vnull, Vnull, Vptr qid) -> 
    absinfer sch
             (<|| ( qcre_err(|Vint32 n :: v' :: nil|) ?? qcre_ecb_activate (|Vint32 n :: v' :: nil|)) ;; s ||> ** 
                   HECBList els **  HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P)
             (<|| ABORT ||> ** HECBList els ** HEvLoc locmp **  HEvPtr ptrmp** HCurTCB ct ** P). 
Proof.
  introv Hcop Hv' Hpmp.
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  instantiate (1:=ABORT).
  2: { eapply absinfer_seq_abt. can_change_aop_solver. can_change_aop_solver. go. }
  eapply absinfer_trans.
  eapply absinfer_choice1.
  can_change_aop_solver.
  2: eauto.
  can_change_aop_solver.
  eapply absinfer_abt.
  can_change_aop_solver.
  can_change_aop_solver.
  absimp_abt_solver.
  instantiate (1:=HECBList els ** HEvPtr ptrmp ** HCurTCB ct ** P).
  instantiate (1:=locmp).
  instantiate (1:=qcre_err (|Vint32 n :: v' :: nil|)).
  instantiate (1:=s0).
  sep auto.
  instantiate (1:=HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** P).
  instantiate (1:=qcre_err (|Vint32 n :: v' :: nil|)).
  instantiate (1:=s0).
  sep auto.
  instantiate (1:=HECBList els ** HEvLoc locmp ** HCurTCB ct ** P).
  instantiate (1:=qcre_err (|Vint32 n :: v' :: nil|)).
  instantiate (1:=s0).
  sep auto.
  can_change_aop_solver.
Qed.

Ltac get_hsat Hs := 
  match goal with
    H: _ |= _ |- _ => rename H into Hs
  end.

Ltac forward_qp_assg ct :=
  combine_evaux (get_off_addr ct qptr_off);
  forward_evaux ct ltac:(eapply eq_vptr). 

Lemma semecb_preserve_cre1:
  forall locmp ptrmp ecbls hd' vl vll semeibs muxeibs qeibs ct sid, 
    SEM_ECB_P locmp ptrmp ecbls (Vptr sid) (vl::vll) semeibs muxeibs qeibs -> 
    get ecbls sid = None -> 
    V_OSEventListPtr vl = Some hd' -> 
    isptr hd' -> 
    ~ptr_in_ecblist (Vptr sid) hd' vll -> 
    RH_SEM_EINFO_ECB_P ecbls semeibs -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 sid) ->
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 sid) -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_normal sid) -> 
    (* (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel sid) ->    *)
    SEM_ECB_P (set locmp ct (V$ __EvLoc_ecbcre1)) (set ptrmp ct (Vnull, Vnull, Vptr sid))
              ecbls hd' vll semeibs muxeibs qeibs.  
Proof.
  introv Hsep Hnone Hnxtptr Hisptr Hnotin Hsem Hmux Hque Hncre1 Hncre2.
  introv Hnnm.
  (* introv Hndel. *)
  unfold SEM_ECB_P in *.
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - subst t.
    rewrite set_a_get_a.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
(*     left.
    splits; auto.
    eapply inactive_ecb_no_eib_ref; eauto. *)
  - rewrite set_a_get_a' in Hgetp'; auto.
    lets H00: Hsep Hgetp'.
    clear Hsep.
    rewrite set_a_get_a'; auto.
    destruct H00 as [Hcre1 | [Hcre2 | Hnrm]].
    + left.
      destructs Hcre1.
      splits; auto.
      unfold isptr in Hisptr.
      destruct Hisptr.
      subst hd'. introv Hf. unfold ptr_in_ecblist in Hf. destruct vll; tryfalse.
      destruct H4. subst hd'. 
      eapply n_ptr_in_ecblist_tail; eauto.
    + right. left. 
      auto.
    + right. right.
      destructs Hnrm.
      splits; auto.
      destruct H1.
      left; auto.
      right.
      assert (Hneq: eptr <> sid).
      {
        introv Heq. apply Hnnm.
        subst.
        exists t. unfold tsk_loc_ev. splits; auto.
        do 3 eexists. splits; eauto.
      }
      eapply ptr_in_ecblist_tail; eauto.
Qed.       

Lemma muxecb_preserve_cre1:
  forall locmp ptrmp ecbls hd' vl vll semeibs muxeibs qeibs ct sid, 
    MUX_ECB_P locmp ptrmp ecbls (Vptr sid) (vl::vll) semeibs muxeibs qeibs -> 
    get ecbls sid = None -> 
    V_OSEventListPtr vl = Some hd' -> 
    isptr hd' -> 
    ~ptr_in_ecblist (Vptr sid) hd' vll -> 
    RH_SEM_EINFO_ECB_P ecbls semeibs -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 sid) ->
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 sid) -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_normal sid) -> 
    MUX_ECB_P (set locmp ct (V$ __EvLoc_ecbcre1)) (set ptrmp ct (Vnull, Vnull, Vptr sid))
              ecbls hd' vll semeibs muxeibs qeibs.  
Proof.
  introv Hmep Hnone Hnxtptr Hisptr Hnotin Hsem Hmux Hque Hncre1 Hncre2.
  introv Hnnm.
  (* introv Hndel. *)
  unfold MUX_ECB_P in *.
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - subst t.    
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'. 
  - rewrite set_a_get_a' in Hgetp'; auto.
    rewrite set_a_get_a'; auto.
    lets H00: Hmep Hgetp'.
    clear Hmep.

    destruct H00 as [Hcre1 | [Hcre2 | Hnrm]].
    + left.
      destructs Hcre1.
      splits; auto.
      unfold isptr in Hisptr.
      destruct Hisptr.
      subst hd'. introv Hf. unfold ptr_in_ecblist in Hf. destruct vll; tryfalse.
      destruct H4. subst hd'. 
      eapply n_ptr_in_ecblist_tail; eauto.
    + right. left. 
      auto.
    + right. right.
      destructs Hnrm.
      splits; auto.
      destruct H1.
      left; auto.
      right.
      assert (Hneq: eptr <> sid).
      {
        introv Heq. apply Hnnm.
        subst.
        exists t. unfold tsk_loc_ev. splits; auto.
        do 3 eexists. splits; eauto.
      }
      eapply ptr_in_ecblist_tail; eauto.
Qed.       

Lemma qecb_preserve_cre1:
  forall locmp ptrmp ecbls hd' vl vll semeibs muxeibs qeibs ct sid, 
    Q_ECB_P locmp ptrmp ecbls (Vptr sid) (vl::vll) semeibs muxeibs qeibs -> 
    get ecbls sid = None -> 
    V_OSEventListPtr vl = Some hd' -> 
    isptr hd' -> 
    ~ptr_in_ecblist (Vptr sid) hd' vll -> 
    RH_SEM_EINFO_ECB_P ecbls semeibs -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 sid) ->
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 sid) -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_normal sid) -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel sid) ->
    Q_ECB_P (set locmp ct (V$ __EvLoc_ecbcre1)) (set ptrmp ct (Vnull, Vnull, Vptr sid))
            ecbls hd' vll semeibs muxeibs qeibs.  
Proof.
  introv Hqep Hnone Hnxtptr Hisptr Hnotin Hsem Hmux Hque Hncre1 Hncre2.
  introv Hnnm Hndel.
  (* introv Hndel. *)
  unfold Q_ECB_P in *.
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - subst t.
    rewrite set_a_get_a.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
    split.
    *
      left.
      splits; auto.
      eapply inactive_ecb_no_eib_ref; eauto.
    *
      introv Hf. inverts Hf.
  - rewrite set_a_get_a' in Hgetp'; auto.
    lets H00: Hqep Hgetp'.
    clear Hqep.
    rewrite set_a_get_a'; auto.
    split.
    +
      destruct H00 as [[Hcre1 | [Hcre2 | Hnrm]] Hdel].
      * left. 
        destructs Hcre1. 
        splits; auto.
        unfold isptr in Hisptr.
        destruct Hisptr.
        subst hd'. introv Hf. unfold ptr_in_ecblist in Hf. destruct vll; tryfalse.
        destruct H4. subst hd'. 
        eapply n_ptr_in_ecblist_tail; eauto.
      * right. left.
        auto.
      * right. right.
        destructs Hnrm.
        splits; auto.
        destruct H1.
        left; auto.
        right.
        assert (Hneq: eptr <> sid).
        {
          destruct H0.
          introv Heq. apply Hnnm. subst.
          exists t. unfold tsk_loc_ev. splits; auto.
          do 3 eexists. splits; eauto.
          introv Heq. apply Hndel. subst.
          exists t. unfold tsk_loc_ev. splits; auto.
          do 3 eexists. splits; eauto.        
        }
        eapply ptr_in_ecblist_tail; eauto.
    +
      introv Hdel.
      destruct H00 as (H' & Hdel0).
      lets H00: Hdel0 Hdel.
      destructs H00.
      splits; auto.
      introv Hf. apply H1. 
      destruct Hf as (t0 & Hor & Hep).
      assert (Hneq: eptr <> sid).
      {
        introv Heq.
        subst.
        unfold is_que in H0.
        destruct H0 as (x & y  & pwl & qws & Hget).
        unfold get in Hnone. unfold EcbMap in Hnone.
        unfold get in Hget. unfold EcbMap in Hget.
        rewrite Hnone in Hget. inverts Hget. 
      }
      assert (Hneqct: t0 <> ct).
      {
        intro. subst.
        unfold evptr_of_tsk in Hep. 
        destruct Hep.
        do 2 destruct H3. rewrite set_a_get_a in H3. inverts H3.
        destruct H3.
        do 2 destruct H3. rewrite set_a_get_a in H3. inverts H3. apply Hneq; auto.
        do 2 destruct H3. rewrite set_a_get_a in H3. inverts H3. auto.
      }
      rewrite set_a_get_a' in Hor; eauto.
      exists t0.
      splits; auto.
      unfold evptr_of_tsk in *.
      rewrite set_a_get_a' in Hep; auto.
Qed. 

Lemma evcre_nodup_cre1_preserve:
  forall locmp ptrmp eid ct, 
    evcre_nodup locmp ptrmp ->
    ~(exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid) ->
    ~(exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid) -> 
    evcre_nodup (set locmp ct (V$ __EvLoc_ecbcre1)) (set ptrmp ct (Vnull, Vnull, Vptr eid)). 
Proof.
  introv Hndp Hnex1 Hnex2.
  unfold evcre_nodup.
  introv Hneqt Hget1 Hget2 Hptr1 Hptr2.
  assert (H: t1 = ct \/ t1 <> ct) by tauto.  
  destruct H.
  -
    subst.
    assert (eptr1 = eid). 
    {
      unfold evptr_of_tsk in Hptr1.    
      destruct Hptr1.
      simpljoin1. rewrite set_a_get_a in H. inverts H.
      destruct H.
      simpljoin1. rewrite set_a_get_a in H. inverts H. auto.
      simpljoin1. rewrite set_a_get_a in H. inverts H. auto.
    }
    subst.
    rewrite set_a_get_a' in Hget2; eauto.
    unfold evptr_of_tsk in Hptr2.
    rewrite set_a_get_a' in Hptr2; eauto.
    introv Heqp.
    subst.
    destruct Hptr2.  
    simpljoin1.
    destruct Hget2.
    apply Hnex1. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    apply Hnex2. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    destruct H.
    simpljoin1.
    destruct Hget2.
    apply Hnex1. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    apply Hnex2. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    simpljoin1.
    destruct Hget2.
    apply Hnex1. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    apply Hnex2. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
  -
    assert (H': t2 = ct \/ t2 <> ct) by tauto.
    destruct H'.
    +
      subst.
      assert (eptr2 = eid).
      {
        unfold evptr_of_tsk in Hptr2.
        destruct Hptr2.
        simpljoin1. rewrite set_a_get_a in H0. inverts H0.
        destruct H0.
        simpljoin1. rewrite set_a_get_a in H0. inverts H0. auto.
        simpljoin1. rewrite set_a_get_a in H0. inverts H0. auto.
      }
      subst.
      rewrite set_a_get_a' in Hget1; eauto.
      unfold evptr_of_tsk in Hptr1.
      rewrite set_a_get_a' in Hptr1; eauto.
      introv Heqp.
      subst.
      destruct Hptr1.
      simpljoin1.
      destruct Hget1.
      apply Hnex1. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
      apply Hnex2. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
      destruct H0.
      simpljoin1.
      destruct Hget1.
      apply Hnex1. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
      apply Hnex2. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
      simpljoin1.
      destruct Hget1.
      apply Hnex1. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
      apply Hnex2. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    +
      rewrite set_a_get_a' in Hget1; eauto.
      rewrite set_a_get_a' in Hget2; eauto.
      unfold evcre_nodup in Hndp.
      lets H00: Hndp Hneqt Hget1 Hget2.
      eapply H00; eauto.
      unfold evptr_of_tsk in Hptr1. rewrite set_a_get_a' in Hptr1; eauto.
      unfold evptr_of_tsk in Hptr2. rewrite set_a_get_a' in Hptr2; eauto.
Qed.  

Lemma evdel_nodup_cre1_preserve: 
  forall locmp ptrmp eid ct, 
    evdel_nodup locmp ptrmp ->
    ~(exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid) ->
    ~(exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid) -> 
    evdel_nodup (set locmp ct (V$ __EvLoc_ecbcre1)) (set ptrmp ct (Vnull, Vnull, Vptr eid)). 
Proof.
  introv Hevdel Hnex1 Hnex2.
  unfold evdel_nodup.
  introv Hneqt Hdel1 Hdel2 Hptr1 Hptr2.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  subst.
  rewrite set_a_get_a in Hdel1. inverts Hdel1.
  rewrite set_a_get_a' in Hdel1; eauto.
  assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst.
  rewrite set_a_get_a in Hdel2. inverts Hdel2.
  rewrite set_a_get_a' in Hdel2; eauto.
  lets H00: Hevdel Hneqt Hdel1 Hdel2.  
  eapply H00; eauto.
  unfold evptr_of_tsk in Hptr1. rewrite set_a_get_a' in Hptr1; eauto.
  unfold evptr_of_tsk in Hptr2. rewrite set_a_get_a' in Hptr2; eauto. 
Qed.  

Lemma evdel_nodup_cre2_preserve: 
  forall locmp ptrmp ct, 
    evdel_nodup locmp ptrmp ->
    evdel_nodup (set locmp ct (V$ __EvLoc_ecbcre2)) ptrmp. 
Proof.
  introv Hdnp.
  unfold evdel_nodup in*.
  introv Hneqt Hget1 Hget2 Hp1 Hp2.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  subst t1.
  rewrite set_a_get_a in Hget1.
  inverts Hget1.
  assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst t2.
  rewrite set_a_get_a in Hget2.
  inverts Hget2.
  rewrite set_a_get_a' in Hget1, Hget2; eauto.
Qed.   

Lemma cre_nodup_no_cre1: 
  forall locmp ptrmp ct sid, 
    evcre_nodup locmp ptrmp ->  
    get locmp ct = Some (V$ __EvLoc_ecbcre1) -> 
    get ptrmp ct = Some (Vnull , Vnull, Vptr sid) -> 
    ~exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 sid. 
Proof.
  introv Hndp Hcre1 Hp.
  introv Hex.
  destruct Hex as (t & (Hneq & Htle)).
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hl & (mp & sp & qp & Hp' & Hor)).
  unfold evcre_nodup in Hndp.
  destruct Hor.
  - 
    subst mp.
    assert (Hf: sid <> sid).
    {
      apply Hndp with (t1 := t) (t2 := ct); auto.
      unfold evptr_of_tsk. left. do 2 eexists; eauto.
      unfold evptr_of_tsk. right. right. do 2 eexists; eauto.
    }
    apply Hf; auto.
  -
    destruct H.
    +
      subst sp.
      assert (Hf: sid <> sid). 
      {
        apply Hndp with (t1 := t) (t2 := ct); auto.
        unfold evptr_of_tsk. right. left. do 2 eexists; eauto.
        unfold evptr_of_tsk. right. right. do 2 eexists; eauto.
      }
      apply Hf; auto.
    +
      subst qp.
      assert (Hf: sid <> sid).
      {
        apply Hndp with (t1 := t) (t2 := ct); auto.
        unfold evptr_of_tsk. right. right. do 2 eexists; eauto.
        unfold evptr_of_tsk. right. right. do 2 eexists; eauto.
      }
      apply Hf; auto.
Qed.  

Lemma cre_nodup_no_cre2: 
  forall locmp ptrmp ct sid, 
    evcre_nodup locmp ptrmp ->  
    get locmp ct = Some (V$ __EvLoc_ecbcre1) -> 
    get ptrmp ct = Some (Vnull, Vnull, Vptr sid) -> 
    ~exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 sid. 
Proof.
  introv Hndp Hcre1 Hp.
  introv Hex.
  destruct Hex as (t & (Hneq & Htle)).
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hl & (mp & sp & qp & Hp' & Hor)).
  unfold evcre_nodup in Hndp.
  destruct Hor.
  - 
    subst mp.
    assert (Hf: sid <> sid).
    {
      apply Hndp with (t1 := t) (t2 := ct); auto.
      unfold evptr_of_tsk. left. do 2 eexists; eauto.
      unfold evptr_of_tsk. right. right. do 2 eexists; eauto.
    }
    apply Hf; auto.
  -
    destruct H.
    +
      subst sp.
      assert (Hf: sid <> sid). 
      {
        apply Hndp with (t1 := t) (t2 := ct); auto.
        unfold evptr_of_tsk. right. left. do 2 eexists; eauto.
        unfold evptr_of_tsk. right. right. do 2 eexists; eauto.
      }
      apply Hf; auto.
    +
      subst qp.
      assert (Hf: sid <> sid).
      {
        apply Hndp with (t1 := t) (t2 := ct); auto.
        unfold evptr_of_tsk. right. right. do 2 eexists; eauto.
        unfold evptr_of_tsk. right. right. do 2 eexists; eauto.
      }
      apply Hf; auto.
Qed.  

Lemma evcre_nodup_cre2_preserve: 
  forall locmp ptrmp ct sid,  
    evcre_nodup locmp ptrmp ->
    get ptrmp ct = Some (Vnull, Vnull, Vptr sid) -> 
    (~exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 sid) -> 
    (~exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 sid) -> 
    evcre_nodup (set locmp ct (V$ __EvLoc_ecbcre2)) ptrmp. 
Proof. 
  introv Hndp Hp Hnex1 Hnex2.
  unfold evcre_nodup in *.
  introv Hneq Hget1 Hget2 Hp1 Hp2 Heq.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  -
    subst t1.
    assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
    destruct Hor2.
    + 
      subst t2.
      apply Hneq; auto.
    +
      rewrite set_a_get_a' in Hget2; eauto.
      destruct Hget2.
      *
        apply Hnex1.
        exists t2. splits; auto.
        unfold tsk_loc_ev.
        splits; auto.
        subst eptr2.
        assert (eptr1 = sid).
        {
          unfold evptr_of_tsk  in Hp1.
          destruct Hp1.
          simpljoin1.
          rewrite Hp in H1. inverts H1.
          destruct H1.
          simpljoin1. rewrite Hp in H1. inverts H1. auto.
          simpljoin1. rewrite Hp in H1. inverts H1. auto.
        }
        subst eptr1.
        unfold evptr_of_tsk in Hp2.
        destruct Hp2.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        destruct H1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
      *
        apply Hnex2.
        exists t2. splits; auto.
        unfold tsk_loc_ev.
        splits; auto.
        subst eptr2.
        assert (eptr1 = sid).
        {
          unfold evptr_of_tsk  in Hp1.
          destruct Hp1.
          simpljoin1.
          rewrite Hp in H1. inverts H1.
          destruct H1.
          simpljoin1. rewrite Hp in H1. inverts H1. auto.
          simpljoin1. rewrite Hp in H1. inverts H1. auto.
        }
        subst eptr1.
        unfold evptr_of_tsk in Hp2.
        destruct Hp2.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        destruct H1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
  -
    assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
    destruct Hor2.
    + 
      subst t2.
      rewrite set_a_get_a' in Hget1; eauto.
      destruct Hget1.
      * 
        apply Hnex1.
        exists t1. splits; auto.
        unfold tsk_loc_ev.
        splits; auto.
        subst eptr1.
        assert (eptr2 = sid).
        {
          unfold evptr_of_tsk  in Hp2.
          destruct Hp2.
          simpljoin1.
          rewrite Hp in H1. inverts H1.
          destruct H1.
          simpljoin1. rewrite Hp in H1. inverts H1. auto.
          simpljoin1. rewrite Hp in H1. inverts H1. auto.
        }
        subst eptr2.
        unfold evptr_of_tsk in Hp1.
        destruct Hp1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        destruct H1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
      *
        apply Hnex2.
        exists t1. splits; auto.
        unfold tsk_loc_ev.
        splits; auto.
        subst eptr1.
        assert (eptr2 = sid).
        {
          unfold evptr_of_tsk  in Hp2.
          destruct Hp2.
          simpljoin1.
          rewrite Hp in H1. inverts H1.
          destruct H1.
          simpljoin1. rewrite Hp in H1. inverts H1. auto.
          simpljoin1. rewrite Hp in H1. inverts H1. auto.
        }
        subst eptr2.
        unfold evptr_of_tsk in Hp1.
        destruct Hp1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        destruct H1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
    +
      rewrite set_a_get_a' in Hget1, Hget2; eauto.
      lets H00: Hndp Hneq Hget1 Hget2 Hp1 Hp2.
      apply H00 in Heq. 
      auto.
Qed.  

Lemma sem_ecb_cre2_setq_preserve: 
  forall locmp ptrmp ecbls fecbh ecbvl ct n eptr semeibs muxeibs qeibs, 
    SEM_ECB_P locmp ptrmp ecbls fecbh ecbvl semeibs muxeibs qeibs ->  
    get ptrmp ct = Some (Vnull, Vnull, Vptr eptr) -> 
    get ecbls eptr = None ->  
    (* RH_SEM_EINFO_ECB_P ecbls semeibs ->  *)
    (* RH_ECBlk_EIBlk_Mux_P muxeibs ecbls ->  *)
    (* RH_EIBlk_ECBlk_Q_P ecbls qeibs ->  *)
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eptr) -> 
    SEM_ECB_P (set locmp ct (V$ __EvLoc_ecbcre2)) ptrmp (set ecbls eptr (absmsgq nil n nil, nil))
              fecbh ecbvl semeibs muxeibs qeibs.  
Proof.
  introv Hsep  Hgetp Hnone (* Hsem Hmux Hq *) Hnex.
  unfold SEM_ECB_P in *.
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - (* t = ct *)
    subst t.
    rewrite Hgetp in Hgetp'. inverts Hgetp'.
  - (* t <> ct *)
    rewrite set_a_get_a'; eauto.
    lets H00: Hsep Hgetp'.
    clear Hsep.
    destruct H00 as [Hcre1 | [Hcre2 | Hnml]].
    + 
      left.
      simpljoin1. splits; auto.
      rewrite set_a_get_a'; auto.
      introv Heqptr.
      subst eptr.
      apply Hnex.
      exists t. splits; auto. 
      unfold tsk_loc_ev.
      splits; auto.
      do 3 eexists. eauto.
    +
      right. left.
      simpljoin1.
      splits; auto.
      casetac eptr eptr0 Heqep Hneqep.
      * (* = *)
        subst.  unfold is_sem. rewrite set_a_get_a.
        unfold is_sem in H2.
        simpljoin1.
        unfold get in Hnone, H2.
        unfold EcbMap in Hnone, H2.
        rewrite H2 in Hnone.
        inverts Hnone.
      * (* <> *)
        unfold is_sem. rewrite set_a_get_a'; eauto. 
    +
      right. right.
      simpljoin1.
      splits; auto.
      destruct H1.
      2: { right; auto. }
      left. 
      unfold is_evt in *. 
      assert (Hor': eptr = eptr0 \/ eptr <> eptr0) by tauto.
      destruct Hor'.
      subst.
      right; right. unfold is_que. 
      rewrite set_a_get_a. do 2 eexists; eauto. 
      unfold is_sem, is_mux, is_que.
      rewrite set_a_get_a'; eauto.
Qed.    


Lemma mux_ecb_cre2_setq_preserve:
  forall locmp ptrmp ecbls fecbh ecbvl ct n eptr semeibs muxeibs qeibs,
    MUX_ECB_P locmp ptrmp ecbls fecbh ecbvl semeibs muxeibs qeibs ->
    get ptrmp ct = Some (Vnull, Vnull, Vptr eptr) ->
    get ecbls eptr = None ->
    (* RH_SEM_EINFO_ECB_P ecbls semeibs -> *)
    (* RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> *)
    (* RH_EIBlk_ECBlk_Q_P ecbls qeibs -> *)
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eptr) ->
    MUX_ECB_P (set locmp ct (V$ __EvLoc_ecbcre2)) ptrmp (set ecbls eptr (absmsgq nil n nil, nil))
              fecbh ecbvl semeibs muxeibs qeibs.
Proof.
  introv Hmep (* Hgetl *) Hgetp Hnone (* Hsem Hmux Hq *) Hnex1.
  unfold MUX_ECB_P in *.
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - (* t = ct *)
    subst t.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
  - (* t <> ct *)
    rewrite set_a_get_a'; eauto.
    lets H00: Hmep Hgetp'.
    clear Hmep.
    destruct H00 as [Hcre1 | [Hcre2 | Hnml]].
    +
      left.
      simpljoin1. splits; auto.
      rewrite set_a_get_a'; auto.
      introv Heqptr.
      subst eptr.
      apply Hnex1.
      exists t. splits; auto.
      unfold tsk_loc_ev.
      splits; auto.
      do 3 eexists. eauto.
    +
      right. left.
      simpljoin1.
      splits; auto.
      casetac eptr eptr0 Heqep Hneqep.
      * subst.
        unfold is_mux in H2.
        simpljoin1.
        unfold get, EcbMap in Hnone, H2.
        rewrite H2 in Hnone.
        inverts Hnone.
      * 
        unfold is_mux.
        rewrite set_a_get_a'; eauto.
    +
      right. right.
      simpljoin1.
      splits; auto.
      destruct H1.
      2: { right; auto. }
      left.
      unfold is_evt in *.
      assert (Hor': eptr = eptr0 \/ eptr <> eptr0) by tauto.
      destruct Hor'.
      subst.
      right; right.
      unfold is_que. 
      rewrite set_a_get_a. do 2 eexists; eauto.
      unfold is_sem, is_mux, is_que.
      rewrite set_a_get_a'; eauto.
Qed.

Lemma q_ecb_cre2_setq_preserve: 
  forall locmp ptrmp ecbls fecbh ecbvl ct n eptr semeibs muxeibs qeibs,
    Q_ECB_P locmp ptrmp ecbls fecbh ecbvl semeibs muxeibs qeibs ->
    get locmp ct = Some (V$ __EvLoc_ecbcre1) ->
    get ptrmp ct = Some (Vnull, Vnull, Vptr eptr) -> 
    get ecbls eptr = None ->
    (* RH_SEM_EINFO_ECB_P ecbls semeibs -> *)
    (* RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> *)
    (* RH_EIBlk_ECBlk_Q_P ecbls qeibs -> *)
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eptr) ->
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eptr) ->
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel eptr) ->
    Q_ECB_P (set locmp ct (V$ __EvLoc_ecbcre2)) ptrmp (set ecbls eptr (absmsgq nil n nil, nil))
              fecbh ecbvl semeibs muxeibs qeibs.
Proof.
  introv Hqep Hgetl Hgetp Hnone (* Hsem Hmux Hq *) Hnex1 Hnex2 Hnex3.
  unfold Q_ECB_P in *.
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - (* t = ct *)
    subst t.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
    split.
    +
      right. left.
      lets H00: Hqep Hgetp.
      destruct H00 as (Hor3 & Hdel).
      destruct Hor3 as [Hcre1 | [Hcre2 | Hnml]].
      simpljoin1. 
      rewrite set_a_get_a.
      splits; auto.
      unfold is_que.
      rewrite set_a_get_a. do 4 eexists; eauto.
      simpljoin1.
      rewrite set_a_get_a.    
      splits; auto.
      unfold is_que.
      rewrite set_a_get_a. do 4 eexists; eauto.
      rewrite Hgetl in Hnml.
      simpljoin1.
      destruct H; tryfalse. 
    +
      introv Hget.
      rewrite set_a_get_a in Hget.
      inverts Hget.
  - (* t <> ct *)
    rewrite set_a_get_a'; eauto.
    lets H00: Hqep Hgetp'.
    clear Hqep.
    destruct H00 as (Hor3 & Hdel).
    split.
    destruct Hor3 as [Hcre1 | [Hcre2 | Hnml]].
    * left.
      simpljoin1. splits; auto.
      rewrite set_a_get_a'; auto.
      introv Heqptr.
      subst eptr.
      apply Hnex1.
      exists t. splits; auto.
      unfold tsk_loc_ev.
      splits; auto.
      do 3 eexists. eauto.
    * right. left.
      simpljoin1.
      splits; auto.
      casetac eptr eptr0 Heqep Hneqep.
      subst.
      unfold is_que. rewrite set_a_get_a. repeat eexists.
      unfold is_que. rewrite set_a_get_a'; eauto.
    * simpljoin1. 
      right. right.
      split; auto.
      destruct H1.
      2: { right. auto. }
      left.
      unfold is_evt in *.
      assert (Hor': eptr = eptr0 \/ eptr <> eptr0) by tauto.
      destruct Hor'.
      subst.
      right; right. 
      unfold is_que. rewrite set_a_get_a. do 2 eexists; eauto.
      unfold is_sem, is_mux, is_que.
      rewrite set_a_get_a'; eauto.
    *
      introv Hlocdel.
      lets H00: Hdel Hlocdel.
      unfold is_que. rewrite set_a_get_a'; eauto.
      simpljoin1.
      splits; auto.
      2: { (* eptr <> eptr0 *)
        introv Heqptr.  subst eptr.
        apply Hnex3.
        exists t. split; auto.
        unfold tsk_loc_ev.
        split; auto.
        do 3 eexists; eauto.
      }
      introv Hex.
      apply H1.
      destruct Hex as (t' & Hcre12 & Hevptr).
      assert (t' = ct \/ t' <> ct) by tauto.
      destruct H3.
      subst.
      exists ct.
      split; auto.
      rewrite set_a_get_a' in Hcre12; eauto.
Qed.

Lemma RH_SEM_EINFO_ECB_P_semcre_preserve: 
  forall ecbls sid embls absem, 
    get ecbls sid = None -> 
    RH_SEM_EINFO_ECB_P ecbls embls -> 
    RH_SEM_EINFO_ECB_P (set ecbls sid absem) embls.  
Proof.
  introv Hnone Hrh.
  unfold RH_SEM_EINFO_ECB_P in *.
  introv Hget.
  apply Hrh with (eid := eid) in Hget.
  assert (eid = sid \/ eid <> sid) by tauto.
  destruct H.
  subst.
  unfold get in Hnone, Hget.
  unfold EcbMap in Hnone, Hget.
  rewrite Hnone in Hget.
  simpljoin1. tryfalse.
  rewrite set_a_get_a'; eauto.
Qed.  

Lemma ASemEIBs_set_els_preserve: 
  forall s ecbls sid infol scapl embls vhold absem P, 
    get ecbls sid = None -> 
    s |= ASemEIBs infol scapl embls ecbls vhold ** P -> 
    s |= ASemEIBs infol scapl embls (set ecbls sid absem) vhold ** P. 
Proof.
  introv Hnone Haei.
  sep cancel P.
  unfold ASemEIBs in *.
  sep split in Haei.
  sep split; auto.
  sep destruct Haei.
  eexists.
  sep cancel ASemCap.
  sep cancel ASeminfo.
  sep auto.
  eapply RH_SEM_EINFO_ECB_P_semcre_preserve; eauto.
Qed. 

Lemma RH_EIBlk_ECBlk_Q_P_preserve: 
  forall ecbls sid qeibs absem, 
    get ecbls sid = None -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    RH_EIBlk_ECBlk_Q_P (set ecbls sid absem) qeibs.  
Proof.
  introv Hnone Hrh.
  unfold RH_EIBlk_ECBlk_Q_P in *.
  introv Hget.
  apply Hrh in Hget.
  assert (Hor: sid = eid \/ sid <> eid) by tauto.
  destruct Hor.
  subst.
  rewrite Hnone in Hget.
  simpljoin1. tryfalse.
  rewrite set_a_get_a'; eauto.
Qed.  

Lemma AMqEIBs_set_els_preserve: 
  forall s ecbls sid qattrl qcapl qeibs vhold absem, 
    get ecbls sid = None -> 
    s |= AMqEIBs qattrl qcapl qeibs ecbls vhold -> 
    s |= AMqEIBs qattrl qcapl qeibs (set ecbls sid absem) vhold.  
Proof.
  introv Hnone Hsat.
  unfold AMqEIBs in *.
  sep split in Hsat.
  sep split; auto.
  sep destruct Hsat.
  eexists.
  sep cancel AMqAttr.
  sep cancel AMqCap.
  sep auto.
  eapply RH_EIBlk_ECBlk_Q_P_preserve; eauto.
Qed. 


Lemma RH_ECBlk_EIBlk_Mux_P_semcre_preserve: 
  forall muxeibs ecbls sid absem, 
    get ecbls sid = None -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs (set ecbls sid absem).  
Proof.
  introv Hnone Hrh.
  unfold RH_ECBlk_EIBlk_Mux_P in *.
  introv Hget Htp.
  lets H00: Hrh Hget Htp.
  assert (Hor: sid = eid \/ sid <> eid) by tauto.
  destruct Hor.
  subst.
  rewrite Hnone in H00.
  simpljoin1. tryfalse.
  rewrite set_a_get_a'; eauto. 
Qed.  

Lemma AMuxEIBs_set_els_preserve:
  forall s ecbls sid minfol mcapl muxeibs vhold absem P, 
    get ecbls sid = None -> 
    s |= AMuxEIBs minfol mcapl muxeibs ecbls vhold ** P -> 
    s |= AMuxEIBs minfol mcapl muxeibs (set ecbls sid absem) vhold ** P.  
Proof.
  introv Hnone Haeiba.
  sep cancel P. 
  unfold AMuxEIBs in *.
  sep split in Haeiba.
  sep split; auto.
  sep destruct Haeiba.
  eexists.
  sep cancel APthreadMutex.
  sep cancel AMuxCap .
  sep auto.
  eapply RH_ECBlk_EIBlk_Mux_P_semcre_preserve; eauto.
Qed.  

  (* same lemma as the one used for proof of sem_init *) 
Lemma evdel_nodup_normal_null_preserve:
  forall locmp ptrmp ct,
    evdel_nodup locmp ptrmp -> 
    evdel_nodup (set locmp ct (V$ __EvLoc_normal)) (set ptrmp ct (Vnull, Vnull, Vnull)). 
Proof.
  introv Hdnp.
  unfold evdel_nodup in *.
  introv Hneqt Hget1 Hget2 Hp1 Hp2.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  subst t1.
  rewrite set_a_get_a in Hget1.
  inverts Hget1.
  assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst t2.
  rewrite set_a_get_a in Hget2.
  inverts Hget2.
  rewrite set_a_get_a' in Hget1, Hget2; eauto.
  unfold evptr_of_tsk in Hp1, Hp2.
  rewrite set_a_get_a' in Hp1, Hp2; eauto.
Qed.   

Lemma evcre_nodup_normal_null_preserve:
  forall locmp ptrmp ct,
    evcre_nodup locmp ptrmp -> 
    evcre_nodup (set locmp ct (V$ __EvLoc_normal)) (set ptrmp ct (Vnull, Vnull, Vnull)). 
Proof.
  introv Hdnp.
  unfold evcre_nodup in *.
  introv Hneqt Hget1 Hget2 Hp1 Hp2.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  subst t1.
  rewrite set_a_get_a in Hget1.
  inverts Hget1; tryfalse.
  assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst t2.
  rewrite set_a_get_a in Hget2.
  inverts Hget2; tryfalse.
  rewrite set_a_get_a' in Hget1, Hget2; eauto.
  unfold evptr_of_tsk in Hp1, Hp2.
  rewrite set_a_get_a' in Hp1, Hp2; eauto.
Qed.

Lemma mux_ecb_cre_normal_preserve:
  forall locmp ptrmp ecbls fecbh ecbvl vl ct  eptr semeibs muxeibs qeibs,
    MUX_ECB_P locmp ptrmp ecbls fecbh ecbvl semeibs muxeibs qeibs ->
    get locmp ct = Some (V$ __EvLoc_ecbcre1) -> 
    get ptrmp ct = Some (Vnull, Vnull, Vptr eptr) ->
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eptr) ->
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eptr) ->
    V_OSEventListPtr vl = Some fecbh ->
    isptr fecbh -> 
    MUX_ECB_P (set locmp ct (V$ __EvLoc_normal)) (set ptrmp ct (Vnull, Vnull, Vnull)) ecbls
      (Vptr eptr) (vl::ecbvl) semeibs muxeibs qeibs.
Proof.
  introv Hmep Hgetl Hgetp Hnex1 Hnex2 Hnxt Hptr.
  unfold MUX_ECB_P in *.
  introv Hgetp'.
  casetac ct t Heqt Hnet.
  -
    subst. rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    rewrite set_a_get_a'; eauto.
    lets H00 : Hmep Hgetp'.
    clear Hmep.
    destruct H00 as [Hcre1 | [Hcre2 | Hnml]].
    +
      left. simpljoin1. splits; eauto.
      introv Hin.
      apply H0.
      eapply ptr_in_ecblist_tail; eauto.
      introv Heq.
      subst.
      apply Hnex1.
      exists t.
      splits; auto.
      unfold tsk_loc_ev. splits; auto.
      do 3 eexists. splits; eauto. 
    +
      right; left.
      simpljoin1.
      splits; auto.
    +
      right; right.
      simpljoin1.
      splits; auto.
      destruct H0.
      left. auto.
      right.
      unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg.
      destruct (beq_val (Vptr eptr0) (Vptr eptr)); auto.
      rewrite Hnxt.
      auto.
Qed.       

Lemma sem_ecb_cre_normal_preserve:
  forall locmp ptrmp ecbls fecbh ecbvl vl ct  eptr semeibs muxeibs qeibs,
    SEM_ECB_P locmp ptrmp ecbls fecbh ecbvl semeibs muxeibs qeibs ->
    get locmp ct = Some (V$ __EvLoc_ecbcre1) -> 
    get ptrmp ct = Some (Vnull, Vnull, Vptr eptr) ->
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eptr) ->
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eptr) ->
    V_OSEventListPtr vl = Some fecbh ->
    isptr fecbh -> 
    SEM_ECB_P (set locmp ct (V$ __EvLoc_normal)) (set ptrmp ct (Vnull, Vnull, Vnull)) ecbls
      (Vptr eptr) (vl::ecbvl) semeibs muxeibs qeibs.
Proof.
  introv Hsep Hgetl Hgetp Hnex1 Hnex2 Hnxt Hptr.
  unfold SEM_ECB_P in *.
  introv Hgetp'.
  casetac ct t Heqt Hnet.
  -
    subst. rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    rewrite set_a_get_a'; eauto.
    lets H00 : Hsep Hgetp'.
    clear Hsep.
    destruct H00 as [Hcre1 | [Hcre2 | Hnml]].
    +
      left. simpljoin1. splits; eauto.
      introv Hin.
      apply H0.
      eapply ptr_in_ecblist_tail; eauto.
      introv Heq.
      subst.
      apply Hnex1.
      exists t.
      splits; auto.
      unfold tsk_loc_ev. splits; auto.
      do 3 eexists. splits; eauto. 
    +
      right; left.
      simpljoin1.
      splits; auto.
    +
      right; right.
      simpljoin1.
      splits; auto.
      destruct H0.
      left. auto.
      right.
      unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg.
      destruct (beq_val (Vptr eptr0) (Vptr eptr)); auto.
      rewrite Hnxt.
      auto.
Qed.

Lemma mq_ecb_cre_normal_preserve:
  forall locmp ptrmp ecbls fecbh ecbvl vl ct  eptr semeibs muxeibs qeibs,
    Q_ECB_P locmp ptrmp ecbls fecbh ecbvl semeibs muxeibs qeibs ->
    get locmp ct = Some (V$ __EvLoc_ecbcre1) -> 
    get ptrmp ct = Some (Vnull, Vnull, Vptr eptr) ->
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eptr) ->
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eptr) ->
    V_OSEventListPtr vl = Some fecbh ->
    isptr fecbh -> 
    Q_ECB_P (set locmp ct (V$ __EvLoc_normal)) (set ptrmp ct (Vnull, Vnull, Vnull)) ecbls
      (Vptr eptr) (vl::ecbvl) semeibs muxeibs qeibs.
Proof.
  introv Hqep Hgetl Hgetp Hnex1 Hnex2 Hnxt Hptr.
  unfold Q_ECB_P in *.
  introv Hgetp'.
  casetac ct t Heqt Hnet.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hqep Hgetp'.
    clear Hqep.
    destruct H00 as (Hor3 & Hdel).
    split.
    destruct Hor3 as [Hcre1 | [Hcre2 | Hnml]].
    +
      simpljoin1.
      left.
      splits; auto.
      introv Hin.
      apply H0.
      eapply ptr_in_ecblist_tail; eauto.
      introv Heq.
      subst.
      apply Hnex1.
      exists t. split; auto.
      unfold tsk_loc_ev. splits; auto. do 3 eexists; splits; eauto.
    +
      simpljoin1.
      right; left.
      splits; auto.
    +
      simpljoin1.
      right; right.
      split; auto.
      destruct H0.
      left; auto.
      right.
      unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg.
      destruct (beq_val (Vptr eptr0) (Vptr eptr)); auto.
      rewrite Hnxt.
      auto.
    +
      introv Hdel'.
      apply Hdel in Hdel'.
      clear Hdel.
      simpljoin1.
      splits; auto.
      introv Hex. apply H0.
      simpljoin1.
      casetac ct x Ht Hf.
      * subst.
        rewrite set_a_get_a in H2.
        destruct H2; tryfalse.
      * rewrite set_a_get_a' in H2; eauto.
        exists x.
        splits; auto.
        unfold evptr_of_tsk in H3.
        unfold evptr_of_tsk.
        rewrite set_a_get_a' in H3; eauto.
Qed.


Lemma OSQCreateProof: 
  forall vl p r logicl ct, 
    Some p =
    BuildPreI os_internal OSQCreate vl logicl OSQCreatePre ct->
    Some r =
    BuildRetI os_internal OSQCreate vl logicl OSQCreatePost ct->
    exists t d1 d2 s,
      os_internal OSQCreate = Some (t, d1, d2, s) /\
      {|OS_spec , GetHPrio, OSLInv, I, r, Afalse |}|-ct {{p}}s {{Afalse}}.
Proof.
  init_spec. 
  rename v'5 into ier.
  rename v'4 into vqid.
  change ((Vint32 i :: nil) ++ (vqid :: nil)) with (Vint32 i :: vqid :: nil).
  subst logicl. 

    (* If (size ′ >ₑ ′ OS_MAX_Q_SIZE ||ₑ size ′ ==ₑ ′ 0) *)
  hoare forward;pure_auto.
  hoare unfold pre.
  hoare_lifts_trms_pre (Aop).
  assert (Hvqid: vqid <> Vnull \/ vqid =Vnull)by tauto.
  destruct Hvqid.
  (*vqid <> Vnull *)
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absimp_qcre_err_return1_abt;pure_auto.
    eapply absinfer_eq.
    eapply absabort_rule.
  (*vqid = Vnull *)
  subst. hoare normal pre. hoare_ex_intro.
  hoare abscsq.
  apply noabs_oslinv.
  eapply  absimp_qcre_err_return1; eauto.
  go.
  pure_auto.
  (*size err RETURN 〈 OS_EVENT ∗ 〉 NULL*)
  hoare forward.
  splits;auto. unfolds. left;auto.
  (*elim the false case*)
  hoare forward.
  
  (*  OS_ENTER_CRITICAL();*)
  hoare forward prim;pure_auto.

  (*: pevent = OSEventFreeList; new add*)
  hoare unfold pre.
  hoare_lifts_trms_pre EvtInv.
  unfold EvtInv.

  rename v'20 into vcspace.
  rename v'21 into v21. 
  rename v'22 into v22. 
  rename v'23 into v23. 

  hoare normal pre.
  hoare_ex_intro.
  hoare_lifts_trms_pre (AOSQFreeList, AOSQFreeBlk, AECBList, absecblist).
  eapply backward_rule1.
  introv Hsat. eauto.
(*   eapply fold_EvtInv_part1; eauto. *)
(*   hoare_lifts_trms_pre ( R_Q_Data_P ).
  eapply pure_split_rule'; introv Hrqdata.   *)
  (*: pevent = OSEventFreeList;*)
  unfold AOSEventFreeList.
  hoare unfold.
  hoare forward; pure_auto.
  assert(Hszle: Int.ltu ($ OS_MAX_Q_SIZE) i = false).
  {clear -H2. destruct (Int.ltu ($ OS_MAX_Q_SIZE) i) .
  destruct H2. destruct (Int.eq i ($ 0)) in H. tryfalse. tryfalse. 
  destruct (Int.eq i ($ 0)) in H. tryfalse. tryfalse. auto. }
   assert (Hszneq : Int.eq i ($ 0) = false).
  {clear -H2.  destruct ( Int.eq i ($ 0)) .
  destruct H2.
  destruct (Int.ltu ($ OS_MAX_Q_SIZE) i) in H. tryfalse. tryfalse.
  destruct (Int.ltu ($ OS_MAX_Q_SIZE) i) in H. tryfalse. tryfalse. 
  auto. }
  
  clear H2.  rename H11 into H2. 
  rename H3 into Hrqdata; rename H5 into Hsemecb.
  rename H6 into Hmuxecb; rename H7 into Hqecb.
  rename H8 into Hevcre; rename H9 into Hevdel; rename H10 into Heibref.
  destruct v'21; hoare unfold pre. 
(*********** OSEventFreeList = Null ****************)
  lzh_hoare_if;
  match goal with
    | H: Vint32 (Int.notbool Int.one) <> Vint32 Int.zero /\
         Vint32 (Int.notbool Int.one) <> Vnull /\
         Vint32 (Int.notbool Int.one) <> Vundef |- _ =>
      destruct H as (H & _);
      unfold Int.notbool in H;
      rewrite Int.eq_false in H; eauto;
      tryfalse
    | _ => idtac
  end.
  hoare forward prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  unfold EvtInv.
  sep pauto.
  trycancel_EvtInv.
  unfold AOSEventFreeList.
  unfold ecbf_sll.
  sep cancel OSEventFreeList.
  sep cancel Aier.
  sep cancel p_local.
  instantiate (2:= nil ).
  simpl ecbf_sllseg.
  sep pauto.
  auto. auto. auto. auto.
  go.
  
  assert (Hvret: vqid =Vnull \/ vqid <> Vnull) by tauto. 
  destruct Hvret. 
  subst.

  2: {
    (* vqid <> Vnull  *)
(*     unfold ACNU. hoare normal pre. hoare_ex_intro. *)
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absimp_qcre_err_return1_abt;pure_auto.
    eapply absinfer_eq.
    eapply absabort_rule.
  }

  (* vqid = Vnull  *)
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply absimp_qcre_err_return1; pure_auto.
  eapply absinfer_eq.
  
  (*  L8: If (pevent ′ !=ₑ NULL)  *)
  lzh_hoare_if.
  change (Int.notbool Int.one) with Int.zero in LHift_true.
  destruct LHift_true. tryfalse.
  instantiate (1:= Afalse).
  eapply pfalse_rule.
  
  hoare forward.
  
(************ OSEventFreeList <> Null ******************)
  rename v'43 into pevent_block. 
  rename v'39 into pevent_event_tbl.
  rename v'41 into pevent_event_ptbl.
(*   unfold ACNU. *)hoare normal pre. hoare_ex_intro. 
  pure intro.
  hoare_assert_pure (EcbMod.get v'12 (pevent_block, Int.zero) = None). 
  {
    get_hsat Hsat. 
    unfold AECBList in Hsat.
    sep normal in Hsat.
    destruct Hsat.
    get_hsat Hsat.
    sep split in Hsat.
    eapply qcre_ecblist_star_not_inh; eauto.
    instantiate (3:= s0).
    sep pauto.
  }
  hoare_split_pure_all.
  rename H4 into Hnone.

  hoare_assert_pure (notIncoreSemQ (pevent_block, Int.zero)).
  { get_hsat Hsat.
     sep_lifts_trms_in Hsat (CoreCommuInv).
     unfold CoreCommuInv,DynamicRefactorINV in *.
     sep normal in Hsat.
     sep destruct Hsat.
     sep split in Hsat.
     unfold notIncoreSemQ.
     clear -H4 H7 H18 Hnone.
     funfold H18.
     unfold is_que,is_sem in *.
     unfold get in *. unfold EcbMap in *.
     splits; introv Hf; try rewrite Hf in *; try  eapply H in Hf; try  eapply H0 in Hf;
     try rewrite Hnone in *; simpljoin; tryfalse.
   }
  hoare_split_pure_all.
  rename H4 into Hcre_nincore.

  hoare_lifts_trms_pre tcbllsegevaux. 
  eapply backward_rule1. 
  introv Hsat. 
  eapply tcbllsegevaux_split3_join2_frm in Hsat; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  hoare_assert_pure (Vptr v'51 = v'6).
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat (llsegevaux, AOSTCBList).
    eapply tcblist_llsegaux_match_tn_frm in Hsat; eauto.
  }
  hoare_split_pure_all.
  subst v'6.

  hoare_assert_pure (ct = v'51). 
  {
    get_hsat Hsat.
    unfold AOSTCBList in Hsat. 
    sep normal in Hsat. sep destruct Hsat. sep split in Hsat.
    simpljoin1.
    congruence.
  }
  hoare_split_pure_all.
  (* rename H4 into Hcteq. *) (* ct = ... *)
  subst v'51.

  unfold p_local at 2. 
  unfold OSLInv at 3.
  unfold LINV. 
  hoare_split_pure_all.

  inverts H4. inverts H21. (* logiv_val ... :: ... = logic_val ... :: ... *) 

  hoare_assert_pure (Vnull = v'41). { gen_eq_semp. }
  hoare_split_pure_all. subst v'41. 
  hoare_assert_pure (Vnull = v'39). { gen_eq_muxp. }
  hoare_split_pure_all. subst v'39.
  hoare_assert_pure (Vnull = v'43). { gen_eq_mqp. }
  hoare_split_pure_all. subst v'43.  

   assert (Hnull: get v'38 ct = Some (Vnull, Vnull, Vnull)).
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }

  
  assert (Hncre1: ~(exists t, tsk_loc_ev v'37 v'38 t __EvLoc_ecbcre1 (pevent_block, Int.zero))).
  {
    match goal with
      H: Q_ECB_P _ _ _ _ (?v :: ?vl) _ _ _ |- _ => remember v as hv; remember vl as tvl
    end.
    assert (Hptrin: ptr_in_ecblist (Vptr (pevent_block, Int.zero)) (Vptr (pevent_block, Int.zero)) (hv :: tvl)).
    {
      unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg. simpl.
      asserts_rewrite (beq_pos pevent_block pevent_block = true).
      {
        rewrite beq_pos_Pos_eqb_eq. 
        apply Pos.eqb_refl.
      }
      change (Int.eq Int.zero Int.zero) with true.
      simpl. auto.
    }
     eapply ptr_in_freelist_notcre1; eauto. 
  }

  assert (Hnormal:
            (~(exists t, tsk_normal_ev v'37 v'38 t (pevent_block, Int.zero))) \/
            (exists t, tsk_normal_ev v'37 v'38 t (pevent_block, Int.zero))) by tauto.
  destruct Hnormal as [Hnnml | Hnml]. 
  2: {
    (* there exist tasks using the queue being created *)
    (* violation of assumption about the user *) 
    hoare_lifts_trms_pre (Aop, absecblsid, evlocid, evptrid, curtid).
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absimp_qcre_ecb_avail_abt2; eauto.
    go. unfold CurTid. go. 
    eapply absinfer_eq.
    apply absabort_rule.
  } 

  (* there does not exist any task using the queue being created *)
  hoare normal pre. hoare_ex_intro.  
  hoare_lifts_trms_pre (Aop, absecblsid, evlocid, evptrid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply absimp_qcre_ecb_avail; pure_auto.
  unfold CurTid. go. 
  eapply absinfer_eq. 
  
  lzh_hoare_if;
  match goal with
    | H: Vint32 (Int.notbool Int.zero) = Vint32 Int.zero \/
         Vint32 (Int.notbool Int.zero) = Vnull |- _ =>
      unfold Int.notbool in H; simpl in H;
      rewrite Int.eq_true in H; auto;
      destruct H; tryfalse
    | _ => idtac
  end.
  (* OSEventFreeList ′ =ₑ 〈 OS_EVENT ∗ 〉 OSEventFreeList ′ → OSEventListPtr *) 
  hoare forward; pure_auto.
  instantiate (1:=logic_val (V$1) :: logic_val (V$ __EvLoc_normal) :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil).
  unfold p_local; unfold LINV;  unfold OSLInv.
  sep normal. sep eexists.
  try_cancel_evaux_asst.
  sep cancel flag_off.
  sep cancel CurTid.
  sep split; auto.
  sep pauto.
  
  clear LHift_true.

  (*OSTCBCur ′ → __OSTskQPtr =ₑ pevent ′;ₛ*)
  hoare_assign_evaux.

  (*OSTCBCur ′ → __OSTskEvLoc =ₑ ′ __EvLoc_ecbcre1*)
  hoare_assign_evaux.
  
  unfold isevloc ;auto.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (get_off_addr ct evloc_off).
  apply sep_combine_lemmas.PV_separate_rw_frm in Hsat.
  eauto.
  
  fold_evaux_q_loc (V$ __EvLoc_ecbcre1) (Vptr (pevent_block, Int.zero)).
  
 (* prepare for EXIT_CRITICAL;ₛ *) 

  assert (Hncre2: ~exists t, tsk_loc_ev v'37 v'38 t __EvLoc_ecbcre2 (pevent_block, Int.zero)). 
  {
    eapply not_in_els_notcre2; eauto. 
  }

  hoare_assert_pure (isptr v'15).
  {
    get_hsat Hsat. 
    sep_lifts_trms_in Hsat ecbf_sllseg.
    lets H00: isptr_ecbf_sllseg_frm Hsat.
    auto.
  }
  hoare_split_pure_all.
  hoare_assert_pure (~ptr_in_ecblist (Vptr (pevent_block, Int.zero)) v'15 v'21).
  {
    match goal with H: isptr _ |- _ => rename H into Hisptr end.
    unfold isptr in Hisptr.
    destruct Hisptr.
    subst v'15. unfolds.
    introv Hf. unfold ptr_in_ecblist in Hf. destruct v'21; tryfalse.
    destruct H4. subst v'15.
    get_hsat Hsat. 
    sep_lifts_trms_in Hsat (Astruct, ecbf_sllseg). 
    apply hd_not_in_evt_freelist in Hsat; auto.
  }
  hoare_split_pure_all.
  match goal with
    H: Q_ECB_P _ _ _ _ (?v :: ?vl) _ _ _ |- _ => remember v as hv; remember vl as tvl
  end.  
  assert (Hin: ptr_in_ecblist (Vptr (pevent_block, Int.zero)) (Vptr (pevent_block, Int.zero)) (hv :: tvl)).
  {
    unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg. simpl.
    asserts_rewrite (beq_pos pevent_block pevent_block = true).
    {
      rewrite beq_pos_Pos_eqb_eq. 
      apply Pos.eqb_refl.
    }
    change (Int.eq Int.zero Int.zero) with true.
    simpl. auto.
  }
  
  assert (Hptr: V_OSEventListPtr hv = Some v'15).
  { subst hv; unfolds; simpl; auto. }
  unfold ASemEIBs.
  unfold AMuxEIBs.
  unfold AMqEIBs.

(*
  hoare_lifts_trms_pre (RH_SEM_NOT_IN_CORE_P, RH_Q_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hsem_nc.
  eapply pure_split_rule'; introv Hq_nc.
  *)
  hoare_split_pure_all.
  rename H40 into Hsem_nc.
  rename H31 into Hq_nc.
  rename H27 into H31.
  rename H36 into H27.
  rename H28 into HH28.
  rename H39 into H28.
  rename H29 into HH29.
  rename H32 into H29.
  rename H30 into H32.
  rename H35 into H30.
  rename H34 into HH34.
  rename H33 into HH33.
  rename H37 into HH37.

  rename v'6 into v6.
  rename v'39 into v39.
  rename v'41 into v41.


  eapply backward_rule1. 
  introv Hsat.
  eapply fold_EvtInv_frm'.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AECBList.
  sep cancel absecblist.
  eapply fold_EvtInv_part2; try sep cancel evloc; try sep cancel evptr; eauto.
  eapply semecb_preserve_cre1; eauto.
  eapply muxecb_preserve_cre1; eauto.
  eapply qecb_preserve_cre1; eauto.
  eapply not_in_els_notdel; eauto.
  eapply evcre_nodup_cre1_preserve; eauto.
  eapply evdel_nodup_cre1_preserve; eauto.

  unfold ASemEIBs.
  unfold AMuxEIBs.
  unfold AMqEIBs.
  unfold AOSEventFreeList.
  unfold ecbf_sll.
  sep cancel ecbf_sllseg.
  sep normal.
  do 3 eexists.
  sep cancel ASeminfo.
  sep cancel APthreadMutex.
  sep cancel AMqAttr.
  unfold tcbllsegevaux.
  sep pauto; eauto.
  
  (* EXIT_CRITICAL;ₛ *) 
  hoare forward prim. 
  sep cancel EvtInv.
  sep cancel CoreCommuInv.
  sep cancel tcbdllflag.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep normal.
  sep eexists.
  sep cancel Aier.
  sep split; eauto.
  sep cancel CurTid.
  sep cancel flag_off.
  try_cancel_evaux_asst.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  eauto.
  splits; eauto.
  unfold isevloc. pure_auto.
  pure_auto.  pure_auto.
  (* end of EXIT_CRITICAL;ₛ *)
  (*If (pevent ′ !=ₑ NULL)*)
  lzh_hoare_if;
  match goal with
    | H: Vint32 (Int.notbool Int.zero) = Vint32 Int.zero \/
         Vint32 (Int.notbool Int.zero) = Vnull |- _ =>
      unfold Int.notbool in H; simpl in H;
      rewrite Int.eq_true in H; auto;
      destruct H; tryfalse
    | _ => idtac
  end.
   
  instantiate (1:=
        (<|| v'3 ||>  **
         Aisr empisr **
         ( EX ier , Aier ier) **
         Aie true **
         Ais nil **
         Acs nil **
         p_local OSLInv ct
         (logic_val (V$ 1)
                    :: logic_val (V$ __EvLoc_ecbcre2)
                    :: logic_val Vnull
                    :: logic_val Vnull:: logic_val (Vptr (pevent_block, Int.zero))  :: nil) **
         A_dom_lenv
        ((size, Int16u)
         :: (pevent, OS_EVENT ∗)
            :: (pq, OS_Q ∗) :: (pqblk, OS_Q_FREEBLK ∗) :: (start, ((Void) ∗) ∗) :: nil) **
         LV pevent @ OS_EVENT ∗ |-> Vptr (pevent_block, Int.zero) **
        (EX  v1 v2 v3, 
         LV start @ ((Void) ∗) ∗ |-> v1 **
         LV pqblk @ OS_Q_FREEBLK ∗ |-> v2 **
         LV pq @ OS_Q ∗ |-> v3 ) **  
         LV size @ Int16u |-> Vint32 i **
         [| vqid = Vptr (pevent_block, Int.zero) |])  
         \\//
         (<|| v'3 ||>  **
         Aisr empisr **
         ( EX ier , Aier ier) **
         Aie true **
         Ais nil **
         Acs nil **
         p_local OSLInv ct
         (logic_val (V$ 1)
                    :: logic_val (V$ __EvLoc_normal)
                    :: logic_val Vnull
                    :: logic_val Vnull:: logic_val Vnull  :: nil) **
         A_dom_lenv
        ((size, Int16u)
         :: (pevent, OS_EVENT ∗)
            :: (pq, OS_Q ∗) :: (pqblk, OS_Q_FREEBLK ∗) :: (start, ((Void) ∗) ∗) :: nil) **
         LV pevent @ OS_EVENT ∗ |-> Vnull **
         (EX v1 v2 v3, 
         LV start @ ((Void) ∗) ∗ |->  v1 **
         LV pqblk @ OS_Q_FREEBLK ∗ |->  v2 **
         LV pq @ OS_Q ∗ |-> v3) **  
         LV size @ Int16u |-> Vint32 i ** 
         [| vqid = Vnull |] )
    ).

  2: {
    (****** return pevent (at the end) ******)
    hoare unfold pre.
    hoare forward.
    
    hoare unfold pre.
    hoare forward; pure_auto.
    right. splits; eauto. introv Hf; tryfalse.

    hoare unfold pre.
    hoare forward.
  }
  
  (****** ENTER_CRITICAL;  ******) 
  hoare forward prim;  pure_auto.
  
  (*  pq ′ =ₑ OSQFreeList ′;  *) 
  hoare unfold pre.
  rename v'63 into vcspace1.
  rename v'64 into v64. 
  rename v'65 into v65. 
  rename v'66 into v66. 
 
  hoare_assert_pure ( v'58 = vhold_addr).
  { get_hsat Hsat. 
    unfold EvtInv in Hsat.
    sep normal in Hsat; sep destruct Hsat.
   sep split in Hsat; eauto.
  }
  hoare_split_pure_all.
  subst. 
  
  eapply backward_rule1.
  introv Hsat.
  unfold EvtInv in Hsat.
  sep normal in Hsat; sep destruct Hsat.
  eapply fold_EvtInv_part2; 
  (match goal with 
    | |- _ |= _ => idtac
    | _ => sep split in Hsat; eauto
    end
  ).
  trycancel_EvtInv.
  eapply fold_EvtInv_part1 in Hsat.
  sep pauto.
  unfold EvtInv_part1.
  rename H38 into HH38.
  hoare unfold pre.
  hoare forward.
  pure_auto.
  (* pqblk ′ =ₑ OSQFreeBlk ′; *) 
  hoare unfold pre.
  hoare forward.
  pure_auto.

  (* IF (pq ′ !=ₑ NULL &&ₑ pqblk ′ !=ₑ NULL) ... *) 
  hoare unfold pre.
  hoare forward;pure_auto.

  (* first branch of inner-most "if"  --- succeeding case *) 
  hoare unfold pre.

  clear H48 H49. 
  rename H45 into HH45.
  rename H38 into H45.
  lets Has :  vaj_inj_isptr2 H45 H46 H47.
  simp join.
  destruct v'63.
  simpl qblkf_sllseg.
  hoare unfold pre. 
  inverts H46.
  tryfalse.
  tryfalse.
  destruct v'58.
  simpl sllseg .
  hoare unfold pre.

  rename H38 into H48.

  rename H39 into H38.
  rename H40 into H39.
  rename H41 into H40.
  rename H42 into H41.
  rename H43 into H42.
  rename H44 into H43.

  inverts H48.
  unfold_qblkfsll.
  unfold_sll.
  
Ltac hoare_split_pure_all2 :=
  hoare normal pre;
   repeat (apply ex_intro_rule; intros);
   hoare_split_pure_all'.
Ltac hoare_unfold_pre2 := 
   try unfold OSInv; try unfold_funpost;
   match goal with
   | H: _ |- {|_ , _, _, _, _, _|}|- _ {{_}} _ {{_}} =>
      hoare_split_pure_all2;

       let x := find_first_exprs in
       unfold_exprlist x;

       hoare_split_pure_all2;
                   isptr_intro';
                   array_leneq_intro;
                   hoare_split_pure_all; 
                   simpljoin;
                   struct_type_vallist_match_elim ; 
                   simpl_field_eq
   | _ => idtac
   end.
hoare_unfold_pre2.


rename H64 into H65.
rename H63 into H64.
rename H62 into H63.
rename H61 into H62.
rename H60 into H61.
rename H59 into H60.
rename H58 into H59.
rename H57 into H58.
rename H56 into H57.
rename H55 into H56.
rename H54 into H55.
rename H53 into H54.
rename H52 into H53.
rename H51 into H52.

  
  instantiate (1:= <|| v'3 ||>  **
         Aisr empisr **
         Aie true **
         Ais nil **
         Acs nil **
         (EX ier, Aier ier )**
         p_local OSLInv ct
         (logic_val (V$ 1)
                    :: logic_val (V$ __EvLoc_ecbcre2)
                    :: logic_val Vnull
                    :: logic_val Vnull:: logic_val (Vptr (pevent_block, Int.zero))  :: nil) ** 
         A_dom_lenv
    ((size, Int16u)
     :: (pevent, OS_EVENT ∗)
        :: (pq, OS_Q ∗) :: (pqblk, OS_Q_FREEBLK ∗) :: (start, ((Void) ∗) ∗) :: nil) **
         LV pevent @ OS_EVENT ∗ |-> Vptr (pevent_block, Int.zero) **
         (EX v1 v2 v3, 
         LV start @ ((Void) ∗) ∗ |-> v1 **
         LV pqblk @ OS_Q_FREEBLK ∗ |-> v2 **
         LV pq @ OS_Q ∗ |-> v3) **
         LV size @ Int16u |-> Vint32 i ** 
       [| vqid = Vptr (pevent_block, Int.zero) |]).  

  hoare forward.  
  go. 
  hoare unfold pre.
  hoare forward; pure_auto.
  hoare unfold pre.

  (* EXIT_CRITICAL; *)  
  hoare forward prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv. 
  eapply fold_EvtInv_frm'.
  sep cancel EvtInv_part2.
  sep cancel tcbdllflag.
  sep cancel CoreCommuInv.
  unfold AOSQFreeList.
  unfold AOSQFreeBlk.
  unfold qblkf_sll.
  unfold os_inv.sll.
  sep cancel AECBList.
  sep pauto.
  sep cancel qblkf_sllseg.
  sep cancel sllseg.
  sep cancel Aier.
  sep cancel p_local.

  sep pauto. pure_auto.
  go.
  
  (* pq ′ → qfreeblk =ₑ pqblk ′; *)
  hoare forward;pure_auto.
  (* start ′ =ₑ pqblk ′ → msgqueuetbl; *) 
  hoare forward.
  eauto.
  (* pq ′ → OSQStart =ₑ start ′; *)
  hoare forward;pure_auto.
  
  (* pq ′ → OSQEnd =ₑ &ₐ start ′ [size ′] *) 
  hoare unfold pre.
  simpl in H52; inverts H52.
  
  hoare forward. 
  pure_auto.

  (* pq ′ → OSQIn =ₑ start ′; *) 
  hoare forward.
  (* pq ′ → OSQOut =ₑ start ′; *) 
  hoare forward.
  (* pq ′ → OSQSize =ₑ size ′; *)
  hoare forward.
  pure_auto.
  (* pq ′ → OSQEntries =ₑ ′ 0; *)
  hoare forward.
  hoare unfold pre.

  (* pevent ′ → OSEventType =ₑ ′ OS_EVENT_TYPE_Q; *)
  hoare forward.
  (* pevent ′ → OSEventCnt =ₑ ′ 0; *)
  hoare forward.
  (* pevent ′ → OSEventPtr =ₑ pq ′; *)
  hoare forward.

  (* OS_EventWaitListInit (­ pevent ′­); *) 
  hoare forward.
  
  remember (Aarray (v'68, Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))
          (Tarray (Void) ∗ ∘ OS_MAX_Q_SIZE) v'67) as Hr.
  simpl in H6; inverts H6.
  simpl in H5; inverts H5.
  sep cancel Aarray.
  sep pauto.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aier.
  sep cancel 1%nat 1%nat.
  sep cancel p_local.
  sep pauto.
  splits;simpl; auto.
  pure_auto.
  sep auto.
  sep auto.
  hoare unfold pre.

rename H66 into H67.

rename H51 into H52.
rename H50 into H51.
rename H49 into H50.
rename H48 into H49.


  inverts H67. (* eq. on logic_val *) 

  (* ENTER_CRITICAL; *) 
  hoare forward prim.
  pure_auto.
  hoare normal pre.
  hoare_ex_intro.
  hoare unfold.
  (* pevent ′ → OSEventListPtr =ₑ OSEventList ′; *)
  eapply backward_rule1.
  introv Hsat.
  unfold EvtInv in Hsat.
  sep normal in Hsat; sep destruct Hsat.
  eapply fold_EvtInv_part2; 
  (match goal with 
    | |- _ |= _ => idtac
    | _ => sep split in Hsat; eauto
    end
  ).
  trycancel_EvtInv.
  eapply fold_EvtInv_part1 in Hsat.
  sep pauto.
  unfold EvtInv_part1.

  rename v'90 into vcspace2.
  rename v'91 into v91. 
  rename v'92 into v92. 
  rename v'93 into v93. 

  hoare unfold pre.
  hoare forward.
  pure_auto.

  hoare_assert_pure (EcbMod.get v'82 (v'71, Int.zero) = None). 
  {
    eapply qcre_ecblist_star_not_inh; eauto.
    instantiate (3:= s0).
    sep pauto.
  }
  hoare_split_pure_all.

  (* OSEventList ′ =ₑ pevent ′; *) 
  hoare unfold.
  hoare forward.
  fold_AEventNode_r. 
  
  unfold EvtInv_part2.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (tcbllsegevaux, AOSTCBList, p_local). 
  eapply backward_rule1. 
  introv Hsat. 
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  
  hoare_assign_evaux.
  unfold isevloc;auto.
  rename v'108 into locmp.
  rename v'109 into ptrmp.
  rename v'71 into vp.

  assert (Hptr: get ptrmp ct = Some (Vnull, Vnull , Vptr (vp, Int.zero))). 
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }  
  assert (Hloc: get locmp ct = Some (V$ __EvLoc_ecbcre1)). 
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto. 
  }
  
  assert (Hncre1': ~exists t, t <> ct /\ tsk_loc_ev  locmp ptrmp t __EvLoc_ecbcre1 (vp, Int.zero)).
  {
    eapply cre_nodup_no_cre1; eauto.
  }
  assert (Hncre2': ~exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 (vp, Int.zero)).
  {
    eapply cre_nodup_no_cre2; eauto.
  }
  assert (Hndel: ~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel (vp, Int.zero)).
  {
    eapply not_in_els_notdel; eauto.
  }
  (* execute absop *)
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (Aop, absecblsid, evlocid, curtid).
  casetac vqid (Vptr (vp, Int.zero)) Hqeq Hqne. 
  2: {
    (* vqid <> Vptr (..., ...) *) 
    eapply abscsq_rule.
    apply noabs_oslinv. 
    eapply absimp_qcre_ecb_activate_abt; auto. 
    go. unfold CurTid. go.
    eauto. auto. 
    eapply absinfer_eq.
    eapply absabort_rule. 
  }
  (* vqid = Vptr (vp, Int.zero) *) 
  subst vqid. 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absimp_qcre_ecb_activate; auto.
  go. unfold CurTid. go. 
  auto.
  eapply absinfer_eq. 

(* prepare to exit from critical section *) 
  fold_evaux_loc (V$ __EvLoc_ecbcre2).
  unfold ASemEIBs.
  unfold AMuxEIBs.
  unfold AMqEIBs.
  hoare_split_pure_all.
  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_frm'.
  trycancel_EvtInv.
  unfold AECBList.
  sep normal.
  sep eexists.
  sep cancel OSEventList.
  
  instantiate (9 :=
                 (DMsgQ (Vptr  (v'70, Int.zero))  
                    (v'69
            :: Vptr (v'68, Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))
               :: Vptr (v'68, (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero)) +ᵢ  Int.mul ($ 4) i)
                  :: Vptr (v'68, Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))
                     :: Vptr (v'68, Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))
                        :: Vint32 i :: V$ 0 :: Vptr (v'68, Int.zero) :: nil)
                    (v'65 :: x5 :: nil)  v'67) :: v'93). 
  
  instantiate (9:= ((V$ OS_EVENT_TYPE_Q
             :: Vint32 Int.zero
                :: V$ 0
                   :: Vptr (v'70, Int.zero)  :: v'75 :: v'94 :: Vint32 Int.zero :: v'79 :: nil), INIT_EVENT_TBL, INIT_EVENT_PTBL) :: v'90).
  simpl evsllseg at 1.
  unfold AEventNode.
  unfold AOSEvent.
  unfold AEventData.
  unfold AOSEventTbl.
  unfold AOSPostEventTbl.
  sep normal.
  sep eexists.
  sep cancel node.
  sep cancel Aarray.
  sep cancel Aarray.
  sep cancel evsllseg.
  sep split; eauto.
  unfold AMsgData.
  unfold AOSQCtr.
  unfold_msg.
  sep pauto.
  sep cancel x5.
  sep cancel Aarray.
  sep cancel Astruct.
  
  eapply fold_EvtInv_part2; try sep cancel evloc; try sep cancel evptr; eauto.
  
  eapply sem_ecb_cre2_setq_preserve ; eauto. 
  eapply mux_ecb_cre2_setq_preserve; eauto. 
  eapply q_ecb_cre2_setq_preserve; eauto. 
  {  introv Hnex.
    destruct Hnex as (t & Hneqt & Htle).
    apply Hndel. exists t. auto. }
  eapply evcre_nodup_cre2_preserve; eauto.
  eapply evdel_nodup_cre2_preserve; eauto.
  
  unfold ASemEIBs.
  unfold AMuxEIBs.
  unfold AMqEIBs.
  sep cancel AOSEventFreeList.
  sep normal.
  do 3 eexists.

  sep cancel ASeminfo.
  sep cancel APthreadMutex.
  sep cancel AMqAttr.
  unfold tcbllsegevaux.
  sep pauto; eauto.
  eapply RH_SEM_EINFO_ECB_P_semcre_preserve; eauto.
  go.
  eapply RH_ECBlk_EIBlk_Mux_P_semcre_preserve; eauto.  
  eapply RH_EIBlk_ECBlk_Q_P_preserve; eauto.
  go.

  { (* WellformedOSQ *)
      apply WLF_OSQ_prop; auto.
      rewrite Hszle.
      rewrite Hszneq.
      left. simpl.
      change (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.zero) with false.
      simpl. auto.
    }
  { split; auto. go. }
  auto.
  {split; auto. go. }
  {
    eapply ECBList_OSQCRT_prop; eauto.
  }
  { apply RL_Tbl_init_prop. }
  auto.
  simpl; splits; auto.
  apply RL_Tbl_init_prop. 
  auto.
 simpl; splits; auto.
  
  (* EXIT_CRITICAL *)
  hoare forward prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep cancel Aier.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep cancel CurTid.
  sep normal. sep eexists.
  sep split; eauto.
  try_cancel_evaux_asst.
  sep cancel flag_off.
  cancel_corecommuinv. 
  
  (* PartitionInv *)
  Require Import sem_partition.
  cancel_partitioninv.
  eauto.
  (* end of PartitionInv *)

  splits; eauto. unfold isevloc. auto. 
  apply OSQCRT_TCB_prop; auto. 

  go.
  sep pauto.
  sep cancel Aier.
  sep pauto.
  
  (****** second branch of the inner "if" -- failing case *******)
  
  instantiate (1 := 
      <|| v'3 ||>  **
     Aisr empisr **
     Aie true **
     Ais nil **
     Acs nil **
     (EX ier , Aier ier) **
     p_local OSLInv ct
       (logic_val (V$ 1)
        :: logic_val (V$ __EvLoc_normal)
           :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
     A_dom_lenv
       ((size, Int16u)
        :: (pevent, OS_EVENT ∗)
           :: (pq, OS_Q ∗) :: (pqblk, OS_Q_FREEBLK ∗) :: (start, ((Void) ∗) ∗) :: nil) **
     LV pevent @ OS_EVENT ∗ |-> Vnull **
     (EX v1 v2 v3 : val,
      LV start @ ((Void) ∗) ∗ |-> v1 **
      LV pqblk @ OS_Q_FREEBLK ∗ |-> v2 ** LV pq @ OS_Q ∗ |-> v3) **
     LV size @ Int16u |-> Vint32 i ** [|vqid = Vnull|]).

  hoare unfold pre.
  
  (* pevent ′ → OSEventListPtr =ₑ 〈 (Void) ∗ 〉 OSEventFreeList ′ *)
  hoare_lifts_trms_pre EvtInv_part2.
  unfold EvtInv_part2.
  hoare normal pre.
  hoare_ex_intro.

  unfold AOSEventFreeList.
  hoare unfold pre.
  hoare forward; pure_auto.
  (* OSEventFreeList ′ =ₑ pevent ′; *)
  hoare forward.


(*OSTCBCur ′ → __OSTskQPtr =ₑ Null ′;ₛ*)

  hoare_lifts_trms_pre (tcbllsegevaux, AOSTCBList, p_local). 
  eapply backward_rule1. 
  introv Hsat. 
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  
  hoare_assign_evaux.
(*   OSTCBCur ′ → __OSTskEvLoc =ₑ′ os_code_defs.__EvLoc_normal;ₛ *)
  hoare_assign_evaux.

  rename v'80 into locmp.
  rename v'81 into ptrmp.

  assert (Hptr: get ptrmp ct = Some (Vnull, Vnull , Vptr (pevent_block, Int.zero))). 
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }  
  assert (Hloc: get locmp ct = Some (V$ __EvLoc_ecbcre1)). 
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto. 
  }
  
  assert (Hncre1': ~ (exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 (pevent_block, Int.zero))).
  {
    eapply cre_nodup_no_cre1; eauto.    
  }
  assert (Hncre2': ~ (exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 (pevent_block, Int.zero))).
  {
    eapply cre_nodup_no_cre2; eauto.    
  }  
  
  casetac vqid Vnull Hqeq Hqne.
  2: {
    (* vqid <> Vnull *) 
    hoare_lifts_trms_pre (Aop, absecblsid, evlocid, evptrid, curtid).
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absimp_qcre_err_abt; auto.
    go. unfold CurTid. go.
    eauto. 
    eapply absinfer_eq.  
    apply absabort_rule.
  }

  (* vqid = Vnull *)
  subst vqid.
  hoare_lifts_trms_pre (Aop, absecblsid, evlocid, evptrid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absimp_qcre_err; auto. 
  go. unfold CurTid. go.
  eauto. 
  eapply absinfer_eq.  

(* prepare to exit from critical section *) 
  fold_evaux_q_loc (V$ __EvLoc_normal)(Vnull).


  hoare forward prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  unfold EvtInv.
  sep pauto.
  trycancel_EvtInv.
  unfold AOSEventFreeList.
  unfold_ecbfsll.
  unfold AOSQFreeList.
  unfold_sll.
  unfold AOSQFreeBlk.
  unfold qblkf_sll.
  sep pauto.
  sep cancel qblkf_sllseg.
  sep cancel sllseg.
  sep cancel Aier.
  instantiate (3:=
                 ((V$ OS_EVENT_TYPE_UNUSED
                     :: Vint32 i1 :: Vint32 i3 :: x0 :: x1 :: v'67 :: Vint32 i0 :: x4 :: nil) :: v'68)).
    unfold_ecbfsll.  
  sep pauto.
  sep cancel  ecbf_sllseg.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel Aarray.
  unfold tcbllsegevaux.
  sep cancel llsegevaux.
  unfold p_local, LINV, OSLInv.
  sep pauto.
  splits; eauto. 
  auto. auto.
  unfolds;simpl;auto.
  split; auto. go. 
  eapply evdel_nodup_normal_null_preserve; eauto.
  eapply evcre_nodup_normal_null_preserve; eauto.
  
  2:{ eapply mux_ecb_cre_normal_preserve; eauto. }
  2: { eapply sem_ecb_cre_normal_preserve; eauto. }  
  eapply mq_ecb_cre_normal_preserve; eauto.
  auto. go.

  (*  pevent ′ =ₑ 〈 OS_EVENT ∗ 〉 NULL *)
  hoare forward. 
  sep cancel Aier.
  sep pauto.
  (*  *)
  get_hsat Hsat.
  destruct Hsat as [Hsat | Hsat].
  left.
  sep pauto. 
  right.
  sep pauto. 

  Unshelve.
  exact Afalse.
  trivial.
  
Qed. 

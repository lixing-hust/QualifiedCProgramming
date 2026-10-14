
(* new inOSSemPostProof.v *)
(* Require Import OSSemPost.
Require Import OSSemPost_spec. *)

Require Import ucos_include.
(* Require Import absop_rules. *)
Require Import symbolic_lemmas.
Require Import os_ucos_h.
(* Require Import oscore_common. *)

Require Import sem_common.
(* Require Import sem_common_ext. *) 
Require Import sem_corecommu.
Require Import sempend_pure.
Require Import sempost_pure.
Require Import tcblist_setnode_lemmas.
Require Import OSQPostPure.
Require Import evtinv_lemmas.

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.

(* basically the same tac or lemma in OSSemPostProof.v *)

Lemma absinfer_seq1:
  forall (p : asrt) (s1 : absop)  (s2 : spec_code) (s1' : absop) (sc : ossched),
                   can_change_aop p ->
                   sc ⊢  <|| s1 ||>  ** p ⇒  <|| s1' ||>  ** p ->
                   sc ⊢  <|| s1;; s2 ||>  ** p ⇒  <|| s1';; s2 ||>  ** p.
Proof.
intros.
eapply absinfer_seq; try eauto.
Qed.


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

Hint Resolve noabs_oslinv.
Hint Extern 2 (_ <= _) => apply Z.leb_le; trivial.

Require Import abs_infer_abt.
(* Require Import seplog_pattern_tacs. *)

Lemma absimp_sem_post_null_return:
  forall sid v' P sch s,
    sid = Vnull ->
    v' = (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) ->  
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (sem_post (sid :: v' :: nil)) s ||> ** P) 
      (<|| s ||> ** P ). 
Proof.
  introv Hsid Hv' Hcop.
  eapply absinfer_trans. 
  simpl.
  eapply absinfer_choice1.
  3: eauto. 
  pure_auto. pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1. pure_auto.
  instantiate (1:=END (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))).
  infer_solver 0%nat. 
  eexists.
  splits; eauto.
  subst sid. auto. 
  eapply absinfer_seq_end; try pure_auto.
Qed.

Lemma absimp_sem_post_null_return_abt:
  forall sid v' P sch s,
    sid = Vnull ->
    v' <> (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) -> 
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (sem_post (sid :: v' :: nil)) s ||> ** P) 
      (<|| ABORT ||> ** P ). 
Proof.
  introv Hsid Hv' Hcop.
  simpl.
  eapply absinfer_trans. 
  eapply absinfer_choice1.
  3: eauto. pure_auto. pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1; try pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  eapply absinfer_seq_abt; try pure_auto.
Qed.

Lemma absinfer_sem_post_no_active_evt_err: 
  forall a P els sch k s,
    can_change_aop P ->
    EcbMod.get els a = None ->
    k = V$ OS_ERR_EVENT_TYPE -> 
    absinfer sch
      (<|| spec_code_cons (sem_post (Vptr a :: k :: nil)) s ||> ** HECBList els ** P)
      (<|| s ||> ** HECBList els ** P). 
Proof.
  introv Hcop Hnone Hk.
  subst.
  simpl spec_code_cons.
  infer_solver 1%nat.
Qed.

Lemma absinfer_sem_post_no_active_evt_err_abt: 
  forall a P els sch k s,
    can_change_aop P ->
    EcbMod.get els a = None ->
    k <> V$ OS_ERR_EVENT_TYPE -> 
    absinfer sch
      (<|| spec_code_cons (sem_post (Vptr a :: k :: nil)) s ||> ** HECBList els ** P)
      (<|| ABORT ||> ** HECBList els ** P). 
Proof.
  introv Hcop Hnone Hne.
  simpl spec_code_cons.
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
  instantiate (1:=HECBList els ** P).
  can_change_aop_solver.
  instantiate (1:=ABORT).
  eapply absinfer_abt.
  can_change_aop_solver.
  can_change_aop_solver.
  absimp_abt_solver.
  can_change_aop_solver.
  eapply absinfer_seq_abt. 
  can_change_aop_solver.
  can_change_aop_solver.
  intros; auto. 
Qed. 

(* Lemma absimp_sem_post_pevent_not_in_dom_abt:  *)
(*   forall sid els qid v' P sch s, *)
(*     sid = Vptr qid -> *)
(*     get els qid = None ->  *)
(*     can_change_aop P ->  *)
(*     absinfer sch *)
(*       (<|| spec_code_cons (sem_post (sid :: v' :: nil)) s ||> ** HECBList els ** P)  *)
(*       (<|| ABORT ||> ** HECBList els ** P ).   *)
(* Proof. *)
(*   introv Hsid Hnone Hcop. *)
(*   simpl. *)
(*   eapply absinfer_trans. *)
(*   eapply absinfer_choice2. *)
(*   3: eauto. pure_auto. pure_auto. *)
(*   eapply absinfer_trans. *)
(*   eapply absinfer_choice1. *)
(*   3: eauto. pure_auto. pure_auto.  *)
(*   eapply absinfer_trans. *)
(*   eapply absinfer_seq1. *)
(*   pure_auto. *)
(*   eapply absinfer_abt; try pure_auto. *)
(*   absimp_abt_solver. *)
(*   pure_auto. *)
(*   eapply absinfer_seq_abt; try pure_auto.  *)
(* Qed. *)

Lemma absimp_sem_post_wrong_type_return:
  forall P els v' s sid sch,  
    can_change_aop P ->
    (exists d,
      EcbMod.get els sid = Some d /\ ~ (exists n wls, d = (abssem n, wls))) -> 
    v' = Vint32 (Int.repr OS_ERR_EVENT_TYPE) -> 
    absinfer sch
      (<|| spec_code_cons (sem_post ((Vptr sid) :: v' :: nil)) s ||> ** HECBList els ** P) 
      (<|| s ||> ** HECBList els ** P). 
Proof.
  introv Hcop Hnsem Hv'.
  eapply absinfer_trans.
  simpl.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2. 
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto. 2: eauto. pure_auto.
  infer_solver 0%nat. 
Qed. 

Lemma absimp_sem_post_wrong_type_abt:
  forall P els v' s sid sch,  
    can_change_aop P ->
    (exists d,
      EcbMod.get els sid = Some d /\ ~ (exists n wls, d = (abssem n, wls))) -> 
    v' <> Vint32 (Int.repr OS_ERR_EVENT_TYPE) -> 
    absinfer sch
      (<|| spec_code_cons (sem_post ((Vptr sid) :: v' :: nil)) s ||> ** HECBList els ** P) 
      (<|| ABORT ||> ** HECBList els ** P).  
Proof.
  introv Hcop Hnsem Hv'.
  destruct Hnsem. destruct H.
  simpl.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2. 
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto. 2: eauto. pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1; try pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  can_change_aop_solver.
  eapply absinfer_seq_abt; try pure_auto. 
Qed.   

Lemma absimp_sem_post_put_sem_return: 
  forall P els sid n wls sch v' s, 
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65535) = true ->
    v' = (Vint32 (Int.repr OS_NO_ERR)) -> 
    absinfer sch
      ( <|| spec_code_cons (sem_post ((Vptr sid) :: v' :: nil)) s ||> ** HECBList els ** P) 
      ( <|| s ||> ** HECBList (EcbMod.set els sid (abssem (Int.add n Int.one), wls)) ** P).          
Proof.
  introv Hcop Habsem Hrgn Hv'.
  simpl.
  do 6 (
       eapply absinfer_trans;
       [eapply absinfer_choice2; [  | instantiate (1:=HECBList els ** P) | ]; pure_auto | ]).  
  infer_solver 0%nat.   
Qed.

Lemma absimp_sem_post_put_sem_abt:  
  forall P els sid n wls sch v' s, 
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65535) = true ->
    v' <> (Vint32 (Int.repr OS_NO_ERR)) -> 
    absinfer sch
      ( <|| spec_code_cons (sem_post ((Vptr sid) :: v' :: nil)) s ||> ** HECBList els ** P) 
      ( <|| ABORT ||> ** HECBList els ** P).   
Proof. 
  introv Hcop Habsem Hrgn Hv'.
  simpl.
  repeat
    (try eapply absinfer_trans;
     [eapply absinfer_choice2; [ | instantiate (1:=HECBList els ** P) | ]; pure_auto | ]).
  eapply absinfer_trans.
  eapply absinfer_seq1; try pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  can_change_aop_solver.
  eapply absinfer_seq_abt; try pure_auto. 
Qed.

Lemma absimp_sem_bin_assm_violation_abt:
  forall sch absems eid v'1 s P,
    can_change_aop P ->
    (exists posv, get absems posv = Some (infotid eid, Int.one, repeat Int.zero 61)) ->
    absinfer sch
             (<|| spec_code_cons (sem_post (Vptr eid :: v'1 :: nil)) s ||> **
                  HSEMInfo absems ** P) 
             (<|| ABORT ||> ** HSEMInfo absems ** P). 
Proof.
  introv Hcop Hexbin.
  simpl.
  eapply absinfer_trans.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  3: eauto. pure_auto. pure_auto.
  do 4 (
       eapply absinfer_trans;
       [ eapply absinfer_choice2; [ | | eauto ]; pure_auto | ]).
  eapply absinfer_choice1.
  3: eauto. pure_auto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_abt; try pure_auto.
  destruct Hexbin as (posv & H').
  absimp_abt_solver.
  can_change_aop_solver.
  eapply absinfer_seq_abt; try pure_auto.
  Unshelve.
  exact None.
Qed.

(* Lemma absimp_sem_bin_assm_violation_abt:  *)
(*   forall sch ecbls absems muxeibs qeibs eid v'1 infol minfol qattrl vhold pbls tcblh tcbvl fecbh fecbvl s P,  *)
(*     can_change_aop P ->  *)
(*     (exists posv, get absems posv = Some (infotid eid, Int.one)) ->   *)
(*     absinfer sch  *)
(*              (<|| spec_code_cons (sem_post (Vptr eid :: v'1 :: nil)) s ||> ** *)
(*                   ACNU infol minfol qattrl absems muxeibs qeibs ecbls vhold pbls tcblh tcbvl fecbh fecbvl ** P) *)
(*              (<|| ABORT ||> ** *)
(*                   ACNU infol minfol qattrl absems muxeibs qeibs ecbls vhold pbls tcblh tcbvl fecbh fecbvl ** P). *)
(* Proof. *)
(*   introv Hcop Hexbin.  *)
(*   simpl.  *)
(*   eapply absinfer_trans. *)
(*   eapply absinfer_trans.  *)
(*   eapply absinfer_choice2.  *)
(*   3: eauto. pure_auto. pure_auto.   *)
(*   do 4 ( *)
(*        eapply absinfer_trans; *)
(*        [ eapply absinfer_choice2; [ | | eauto ]; pure_auto | ]).  *)
(*   eapply absinfer_choice1. *)
(*   3: eauto. pure_auto. pure_auto.  *)
(*   eapply absinfer_trans. *)
(*   eapply absinfer_seq1. *)
(*   pure_auto. *)
(*   eapply absinfer_abt; try pure_auto.  *)
(*   destruct Hexbin as (posv & H').  *)
(*   absimp_abt_solver. *)
(*   instantiate (2:=sem_post_assumes_not_bin (|Vptr eid :: nil|)). *)
(*   instantiate (2:=s0). *)
(*   unfold ACNU in H. *)
(*   sep normal in H. *)
(*   sep destruct H. *)
(*   sep_lifts_trms_in H seminfoid.  *)
(*   sep cancel 1%nat 1%nat. *)
(*   sep auto. *)
(*   can_change_aop_solver.  *)
(*   eapply absinfer_seq_abt; try pure_auto.  *)
(*   Unshelve. *)
(*   exact None.  *)
(* Qed.    *)

Lemma absimp_sem_post_ovf_err_return:
  forall P els eid n wls sch v'1 s,  
    can_change_aop P ->
    EcbMod.get els eid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65535) = false ->
    v'1 = Vint32 (Int.repr OS_SEM_OVF) ->  
    absinfer sch
      (<|| spec_code_cons (sem_post (Vptr eid :: v'1 :: nil)) s ||> ** HECBList els ** P) 
      (<|| s ||> ** HECBList els ** P).     
Proof.
  introv Hcop Hget Hltu Hv'1.
  simpl.
  infer_solver 3%nat.   
Qed. 

Lemma absimp_sem_post_ovf_err_abt: 
  forall P els eid n wls sch v'1 s,  
    can_change_aop P ->
    EcbMod.get els eid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65535) = false ->
    v'1 <> Vint32 (Int.repr OS_SEM_OVF) -> 
    absinfer sch
      (<|| spec_code_cons (sem_post (Vptr eid :: v'1 :: nil)) s ||> ** HECBList els ** P) 
      (<|| ABORT ||> ** HECBList els ** P).   
Proof.
  introv Hcop Hget Hltu Hneq.
  simpl.
  do 3 (
       eapply absinfer_trans;
       [ eapply absinfer_choice2; [ | | eauto ]; pure_auto | ]
     ).
  eapply absinfer_trans. 
  eapply absinfer_choice1.
  3: eauto. pure_auto. pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  can_change_aop_solver.
  eapply absinfer_seq_abt; try pure_auto.
Qed.   

(* Require Import ucos_frmaop. *)
(* Require Import abs_step. *)

Lemma absimp_sem_post_ex_wt_succ_return:
  forall P els sid tls t' n wls p st m sch v' s t ct sus,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    ~ wls = nil ->
    GetHWait tls wls t' ->
    TcbMod.get tls t' = Some (p, st, m, sus) ->
    v' = V$ OS_NO_ERR -> 
    absinfer sch
             ( <|| spec_code_cons (sem_post ((Vptr sid) :: v' :: nil)) s ||> ** 
                             HECBList els ** HTCBList tls **
                             HTime t ** HCurTCB ct ** P ) 
             ( <|| isched;; END (Some (Vint32 (Int.repr OS_NO_ERR))) ;; s ||> **
                             HECBList (EcbMod.set els sid (abssem n, (remove_tid t' wls))) **
                             HTCBList (TcbMod.set tls t' (p, rdy, Vnull, sus)) **
                             HTime t ** HCurTCB ct ** P ). 
Proof.
  introv Hcop Hget Heq Hhw Htlsget Hv'.
  simpl.
  do 4 (
       eapply absinfer_trans; 
       [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ]
     ).
  eapply absinfer_trans. 
  eapply absinfer_choice1. 3: eauto. pure_auto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto. 
  instantiate (1:=HECBList (EcbMod.set els sid (abssem n, (remove_tid t' wls))) **
                           HTCBList (TcbMod.set tls t' (p, rdy, Vnull, sus)) ** HTime t ** HCurTCB ct ** P ).
  pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto. 
  instantiate (1:=HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
  pure_auto. pure_auto.
  instantiate (1:=END (Some (Vint32 (Int.repr OS_NO_ERR)))).
  infer_solver 0%nat. 

  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_eq. 
  eapply absinfer_seq_end; try pure_auto. 
Qed.

Lemma absimp_sem_post_ex_wt_succ_abt:
  forall P els sid tls n wls sch v' s,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    ~ wls = nil ->
    v' <> V$ OS_NO_ERR -> 
    absinfer sch
             ( <|| spec_code_cons (sem_post ((Vptr sid) :: v' :: nil)) s ||> **
                   HECBList els ** HTCBList tls ** P )  
             ( <|| ABORT ||> ** HECBList els ** HTCBList tls ** P ). 
Proof.
  introv Hcop Hget Hneq Hv'.
  simpl.
  do 4 (
       eapply absinfer_trans; 
       [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ]
     ).
  eapply absinfer_trans. 
  eapply absinfer_choice1.
  3: eauto. pure_auto. pure_auto.
  eapply absinfer_trans. 
  eapply absinfer_seq1. pure_auto.
  eapply absinfer_choice2; try pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1. pure_auto. 
  eapply absinfer_abt; pure_auto.
  absimp_abt_solver.
  instantiate (1:=HECBList els ** P).
  instantiate (2:=sem_post_ex_wt_succ (|Vptr sid :: v' :: nil|)). 
  instantiate (2:=s0).
  sep pauto.
  can_change_aop_solver.
  eapply absinfer_seq_abt; try pure_auto. 
Qed. 

Require Import OSTimeTickPure. 
Require Import sem_lab.

Require Import evauxvar_lemmas.
Require Import evaux_pure.
Require Import freeevtlist_lemmas.

Require Import gjb_sem_common. 
Require Import gjb_common.
Require Import seplog_tactics.
Require Import hoare_forward_tac_ext.
Require Import seplog_trm_tacs.
Ltac get_hsat Hs := 
  match goal with
    H: _ |= _ |- _ => rename H into Hs
  end.

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.

Lemma OSSemPost_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSSemPost
                  vl logicl OSSemPostPre ct->
      Some r =
      BuildRetI os_internal OSSemPost vl logicl OSSemPostPost ct->
      exists t d1 d2 s,
        os_internal OSSemPost = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.

  hoare forward prim.
  hoare unfold.
  
  lzh_hoare_if2. 
  hoare forward prim.
  sep cancel EvtInv. sep cancel tcbdllflag. sep cancel p_local. sep cancel Aier.
  sep pauto.
  auto.
  pure_auto.

  assert (Hor: v'2 <> (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) \/ 
                 v'2 = (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) by tauto. 
  inversion Hor.
  (* v'2 <> ... *) 
  eapply abscsq_rule.
  pure_auto.
  (* change ((x :: nil) ++ v'1 :: nil) with (x::v'1::nil). *)
  eapply absimp_sem_post_null_return_abt; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq. 
  eapply absabort_rule.
  (* v'2 = ... *)  
  eapply abscsq_rule.
  pure_auto.
  eapply absimp_sem_post_null_return; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq.
  (* return in case pevent = NULL *)
  hoare forward. 

  rename v'12 into els.
  
  hoare unfold.
  unfold EvtInv.

  rename v'20 into vcspace.
  rename v'21 into v21. 
  rename v'22 into v22. 
  rename v'23 into v23. 

  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst. (* addr of placeholder is now vhold_addr *) 

  rename v'35 into locmp.
  rename v'36 into ptrmp.
  rename v'1 into fecbh.
  rename v'12 into fecbvl. 
  rename v'30 into semeibs.
  rename v'31 into muxeibs.
  rename v'32 into mqeibs.

  hoare_assert_pure (get ptrmp ct = Some (Vnull, Vptr x, Vnull)
                                             /\ get locmp ct = Some (V$ os_code_defs.__EvLoc_normal)).
  { get_hsat Hsat.
     sep_lifts_trms_in Hsat (evlocid, evptrid, tcbllsegevaux, AOSTCBList,p_local).
    eapply get_aux;eauto.
   }
  hoare_split_pure_all.
  destruct H0 as (Hget_ptr & Hget_loc).

  assert (Hevt: is_evt els x \/ ptr_in_ecblist (Vptr x) fecbh fecbvl).  
  { eapply sem_ecb_nml; eauto. }

  destruct Hevt as [Hevt | Hfree].
  Focus 2.
  (* pevent points into list of free ECBs *)
  hoare_assert_pure (exists p, fecbh = Vptr p). 
  {
    unfold ptr_in_ecblist in Hfree.
    lets Hptr: ptr_in_ecbsllseg_ptr Hfree.
    eauto.
  }
  hoare_split_pure_all.
  destruct v'1 as (fb & fi).
  subst.
  eapply backward_rule1.
  introv Hsat.
  unfold AOSEventFreeList in Hsat.
  unfold ecbf_sll in Hsat.
  sep normal in Hsat.
  sep_lifts_trms_in Hsat ecbf_sllseg.
  eapply ecbf_sllseg_split3_frm; eauto.
  hoare unfold.
  lzh_hoare_if.
  2: {
    change (Int.eq ($ OS_EVENT_TYPE_UNUSED) ($ OS_EVENT_TYPE_SEM)) with false in Hif_false. 
    inverts Hif_false.
  }
  unfold AECBList.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Astruct, evsllseg).

  hoare_assert_pure (get els (v'37, Int.zero) = None).
  {
    get_hsat Hsat. 
    lets H00: semcre_ecblist_star_not_inh H0 Hsat. 
    auto.
  }
  hoare_split_pure_all.
  rename H10 into Hnone.
  rename v'2 into etype. 
  casetac etype (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) Heeq Hene.
  2: {
    hoare_lifts_trms_pre (Aop, absecblsid).  
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absinfer_sem_post_no_active_evt_err_abt; try pure_auto.
    go. unfold CurTid. go.
    eapply absinfer_eq. 
    apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, absecblsid).  
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_post_no_active_evt_err; eauto. 
  go. unfold CurTid. go.
  eapply absinfer_eq.

  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_part1.
  trycancel_EvtInv1.
  unfold AECBList.
  sep pauto.
  sep cancel evsllseg. sep pauto.
  eauto.
  eapply backward_rule1.
  introv Hsat.  
  eapply fold_EvtInv_part2;eauto.
  trycancel_EvtInv2.
  unfold AOSEventFreeList.
  sep pauto.
  unfold ecbf_sll.
  sep_lifts_trms ecbf_sllseg.
  eapply ecbf_sllseg_compose3_frm; eauto. 
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel ecbf_sllseg.
  sep cancel ecbf_sllseg.
  sep cancel Aarray.
  sep pauto.

  auto.
  pure_auto.
  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_frm;eauto.
  sep cancel EvtInv_part1. sep cancel EvtInv_part2. sep pauto.
  
  (* EXIT_CRITICAL *) 
  hoare forward prim. 

  sep cancel Aier.
  sep cancel EvtInv.
  sep cancel p_local.
  sep cancel tcbdllflag.
  eauto.
  auto.
  go.

  (* return OS_ERR_EVENT_TYPE *) 
  hoare forward.

  (* pevent points to an active ECB *) 
  unfold AECBList.
  hoare unfold.
  rename H0 into H_elp. (* ECBList_P ... *)  
  assert (Hecb: exists ecb, get els x = Some ecb). 
  {
    unfold is_evt in Hevt.
    destruct Hevt as [Hsem | [Hmux | Hque]].
    unfold is_sem in Hsem.
    simpljoin1; eexists; eauto.
    unfold is_mux in Hmux.
    simpljoin1; eexists; eauto.
    unfold is_que in Hque.
    simpljoin1; eexists; eauto.
  }
  destruct Hecb as (ecb & Hgetecb).
  destruct ecb. 
  lets Hctr: ECBList_P_get_ectr_some Hgetecb H_elp.
  destruct Hctr as (evl & etbl & petbl & Hgetectr).
  
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat evsllseg.
  eapply get_ectr_decompose; eauto.
  hoare unfold.

  hoare_assert_pure (length v'15 = length v'31). 
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg. 
    eapply evsllseg_aux in Hsat. 
    destruct Hsat.
    eauto. 
  }
  eapply pure_split_rule'; introv Heqlen. 
  lets H00: ecblist_p_decompose H_elp; eauto. 
  destruct H00 as (els1 & els2 & x' & H''). 
  destruct H'' as (Hecbl1 & Hecbl2 & Hjo).      
  hoare_assert_pure (x' = Vptr (v'40, Int.zero)).  
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg. 
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  hoare_split_pure_all; subst. 
  
  assert (Hecbl' := Hecbl2).
  (* do 2 (rewrite ele_lst_cons in Hecbl').  *)
  unfold ECBList_P in Hecbl'.
  fold ECBList_P in Hecbl'.
  destruct Hecbl' as (qid & Hqid & Hecbetbl & Hex).
  inverts Hqid. 
  destruct Hex as (Hrpetbl & absmq & mqls' & v'' & Helptr & Hjo' & Hrlh & Hecbl20).
  unfold V_OSEventListPtr in Helptr.
  inverts Helptr.
  
  lzh_hoare_if.
  pure_auto.
  pure_auto.
  
  (* the concrete type is not OS_EVENT_TYPE_SEM *) 
  hoare_assert_pure (~exists n wls, get els (v'40, Int.zero) = Some (abssem n, wls)).
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply semacc_eventtype_neq_sem in Hsat; eauto.
    sep split in Hsat.
    auto.
    go.
  }
  hoare_split_pure_all.

  rename v'2 into etype. 
  casetac etype (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) Heeq Hene.
  2: {
    hoare_lifts_trms_pre (Aop, absecblsid).  
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absimp_sem_post_wrong_type_abt; eauto. 
    go. unfold CurTid. go.
    unfold get, EcbMap in Hgetecb.
    unfold get, EcbMap in H0.
    rewrite Hgetecb in H0. 
    exists (e, w). simpljoin1. splits; auto.
    introv Hf. apply H0. simpljoin1. do 2 eexists; eauto. 
    eapply absinfer_eq.
    apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, absecblsid).  
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absimp_sem_post_wrong_type_return; eauto.  
  go. unfold CurTid. go.
  unfold get, EcbMap in Hgetecb.
  unfold get, EcbMap in H0.
  rewrite Hgetecb in H0.
  exists (e, w). simpljoin1. splits; auto.
  introv Hf. apply H0. simpljoin1. do 2 eexists; eauto.   
  eapply absinfer_eq.

  fold_AEventNode_r. 
  eapply backward_rule1.
  introv Hsat.  
  eapply fold_EvtInv_part1.
  trycancel_EvtInv1.

  sep_lifts_trms_in Hsat (AEventNode, (evsllseg v'1), (evsllseg v'')).
  eapply lzh_evsllseg_compose in Hsat; eauto.
  sep_lifts_trms_in Hsat (evsllseg, OSEventList).
  eapply AECBList_fold in Hsat; eauto. 
  eapply backward_rule1.
  introv Hsat.  
  eapply fold_EvtInv_part2;eauto.
  trycancel_EvtInv2.
  unfold AOSEventFreeList.
  sep pauto.

  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_frm;eauto.
  sep cancel EvtInv_part1. sep cancel EvtInv_part2. sep pauto.
  
  (* EXIT_CRITICAL *)
  hoare forward prim.
  sep cancel Aier.
  
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep pauto.
  go.
  go.
  
  (* return OS_ERR_EVENT_TYPE *) 
  hoare forward.
  
  (* the concrete type is OS_EVENT_TYPE_SEM *)
  apply semacc_int_eq_true in Hif_false. 
  subst.
  hoare_assert_pure (exists wls, v'35 = DSem i2 /\ absmq = (abssem i2, wls)).  
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply semacc_triangle_sem in Hsat; eauto.
    2: go. 
    sep split in Hsat.
    auto.
  }
  hoare_split_pure_all.
  destruct H0 as (Hdsem & Habssem). 
  match type of Habssem with
    _ = (?e, ?w) =>
    assert (Hsem: get els (v'40, Int.zero) = Some (e, w)) 
  end.
  {
    eapply join_get_r; eauto.
    eapply join_get_l; eauto.
    rewrite get_a_sig_a; eauto. subst. auto.
  }

  subst.
  
  hoare_unfold.
  lzh_hoare_if2.

  Focus 2.
  lzh_hoare_if2. 
  
  lzh_simpl_int_eq.
  unfold AOSTCBPrioTbl.
  hoare_split_pure_all.
  assert (Hnil : v'12 = nil).
  {
    lets Fnil: sempost_grp_wls_nil' H0 Hecbetbl; eauto.  
  }
  subst v'12.
  hoare forward. 
  struct_type_match_solver.
  
  assert (Hret: v'2 <> Vint32 (Int.repr OS_NO_ERR) \/ v'2 = Vint32 (Int.repr OS_NO_ERR)) 
    by tauto.
  inversion Hret as [Hretcase | Hretcase]. 
  (* v'2 <> ... *)
  hoare_lifts_trms_pre (Aop, absecblsid). 
  eapply abscsq_rule.
  pure_auto. 
  eapply absimp_sem_post_put_sem_abt; eauto. 
  go. unfold CurTid. go. 
  eapply absinfer_eq. 
  eapply absabort_rule.
  (* v'2 = ... *)  
  (* bin sem? *)  
  remember (
      exists posv, 
        get semeibs posv = Some (infotid (v'40, Int.zero), Int.one, repeat Int.zero 61)) as X.   
  assert (Hor: X \/ ~X) by tauto. 
  subst X. 
  inversion Hor as [Hcs | Hcs].
  (* bin sem *)
  destruct Hcs as (posv & H''); eauto. 
  (* hoare lifts (1::27::nil)%nat pre. *)
  hoare_lifts_trms_pre (Aop, seminfoid).
  eapply abscsq_rule.
  pure_auto. 
  eapply absimp_sem_bin_assm_violation_abt; eauto. 
  go. unfold CurTid. go. 
  eapply absinfer_eq. 
  eapply absabort_rule.
  clear Hor. 
  (* not bin sem *) 
  hoare_lifts_trms_pre (Aop, absecblsid). 
  eapply abscsq_rule.
  pure_auto. 
  eapply absimp_sem_post_put_sem_return; eauto. 
  go. unfold CurTid. go. 
  eapply absinfer_eq. 

  transform_pre sempost_inc_cnt_prop ltac:(sep cancel AEventData). 
  hoare_split_pure_all. 
  clear Hrlh Hecbetbl. 
  
  eapply backward_rule1.
  introv Hsat.  
  eapply fold_EvtInv_part2;eauto.
  trycancel_EvtInv2.
(*   unfold AOSEventFreeList. *)
  sep pauto.


  hoare forward prim.
  sep cancel Aier.
  unfold AOSTCBPrioTbl.
  sep pauto.
  sep cancel 6%nat 1%nat. (* PV vhold_addr ... *)
  sep cancel p_local.
  sep cancel OSPlaceHolder.
    sep cancel APthreadAttr.
  sep cancel CapabilityInv.

  eapply fold_EvtInv_frm.
  instantiate(2:= (EcbMod.set els (v'40, Int.zero) (abssem (i2 +ᵢ  Int.one), nil)) ).
  unfold EvtInv_part1.
  unfold AECBList.
  sep pauto.
  eapply lzh_evsllseg_compose.
  sep cancel evsllseg.
  sep cancel evsllseg.
  unfold AEventNode.
  sep cancel AEventData.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  instantiate(9:= etbl).
  sep pauto; eauto.
  sep cancel Astruct.
  sep cancel Aarray.

(*   7: { splits; eauto. } *)
  trycancel_EvtInv.
  sep cancel AOSPostEventTbl.
  unfold EvtInv_part2 in *.
  sep pauto.
  sep cancel AOSEventFreeList.
  unfold ASemEIBs in *.
  sep pauto. 
  sep cancel ASeminfo. 
  sep cancel ASemCap. 
  2: { eapply RH_SEM_EINFO_ECB_P_sem_inc; eauto. }
  eapply AMuxEIBs_sem_inc_preserve; eauto. 
  sep cancel AMuxEIBs.
  eapply AMqEIBs_sem_inc_preserve; eauto.
  cancel_corecommuinv. 
  sep cancel AMqEIBs.
  
   (* PartitionInv *)
   Require Import sem_partition.
   cancel_partitioninv.
   eauto.
  (* end of PartitionInv *)

  auto. auto.
  eauto. (* EIBArray_P ... *)

  eapply mq_ecb_p_sem_inc_preserve; eauto.
  eapply mux_ecb_p_sem_inc_preserve; auto.
  eapply sem_ecb_p_sem_inc_preserve; auto. 
  
  split; [auto | eapply sempost_struct_type_vallist_match_sem; auto (* struct_type_vallist_match *)].
  unfolds; simpl. auto.
  eauto.
  eauto.
  
  assert (Heget: EcbMod.get els (v'40, Int.zero) = Some (abssem i2, nil)) by auto.
  assert (Hjsig: EcbMod.joinsig (v'40, Int.zero) (abssem i2, nil) mqls' els2) by auto. 
  lets Hnewjoin: ecb_get_set_join_join Heget Hjsig Hjo. 
  destruct Hnewjoin as [? [? ?]]. 
  eapply semacc_compose_EcbList_P; eauto.
  
  auto.
  auto. eauto.

  eapply sempost_inc_RH_TCBList_ECBList_P_hold; eauto.
  pauto.
  (* RETURN ′ OS_NO_ERR *) 
  hoare forward.
  introv Hf. simpl in Hf. inverts Hf.
  
  (********************** cnt = 65535, overflow! ************************)
  lzh_simpl_int_eq. 
  unfold AOSTCBPrioTbl.
  hoare_split_pure_all.
  assert (Hnil : v'12 = nil).
  {
    lets Fnil: sempost_grp_wls_nil' H0 Hecbetbl; eauto.
  }
  subst v'12.

  assert (Hv'1cs: v'2 <> Vint32 (Int.repr OS_SEM_OVF) \/
                  v'2 = Vint32 (Int.repr OS_SEM_OVF)) by tauto. 
  inversion Hv'1cs.
  (* v'2 <> ... *) 
  hoare_lifts_trms_pre (Aop, absecblsid). 
  (* hoare lifts (29::20::nil)%nat pre.  *)
  eapply abscsq_rule.
  pure_auto.
  eapply absimp_sem_post_ovf_err_abt; eauto.
  go. unfold CurTid. go. 
  eapply absinfer_eq. 
  eapply absabort_rule.
  (* v'2 = ... *)
  hoare_lifts_trms_pre (Aop, absecblsid). 
  (* hoare lifts (29::20::nil)%nat pre.  *)
  eapply abscsq_rule.
  pure_auto.
  eapply absimp_sem_post_ovf_err_return; eauto.
  go. unfold CurTid. go. 
  eapply absinfer_eq. 

  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.
  
  eapply backward_rule1.
  introv Hsat.  
  eapply fold_EvtInv_part1.
  trycancel_EvtInv1.
  sep pauto.

  eapply backward_rule1.
  introv Hsat.  
  eapply fold_EvtInv_part2;eauto.
  trycancel_EvtInv2.
  sep pauto.
  eapply backward_rule1.
  introv Hsat.  
  eapply fold_EvtInv_frm;eauto.
  sep cancel EvtInv_part1. sep cancel EvtInv_part2. sep pauto.
  

  hoare forward prim. 
  sep cancel p_local.
  unfold AOSTCBPrioTbl.
  sep pauto.
  sep cancel OSPlaceHolder.
  sep cancel EvtInv.
  sep cancel Aier.
  sep cancel vhold_addr.
  eauto.
  auto.
  auto. (* RL_RTbl_PrioTbl *)
  auto. (* RL_RTbl_PrioTbl_P *)
  auto.
  go.

  hoare forward. 

  (******************************* OSEventGrp != 0 ******************************) 

  inverts Hsem. 
  
  hoare_lifts_trms_pre (Aisr, Ais, A_isr_is_prop,aemp_isr_is).  
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  
  hoare forward.

  hoare_unfold. 
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.
  hoare_split_pure_all.
  destruct H11.
  subst.
(****************************** L2: event_task_rdy ******************************)
  destruct H34.
  hoare forward.

  unfold_msg.
  sep cancel AEventData.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.

  sep cancel AOSPostEventTbl.
  sep cancel AOSRdyTblGrp.
  instantiate (3:= (v'7 ++ v'8 :: v'9)). 
  eapply tcbdllseg_compose.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  sep cancel p_local.
  eauto.

  eauto.
  unfolds; simpl; eauto.
  eauto. eauto.
  unfolds; simpl; eauto.
  eauto. eauto.
  splits; eauto. 
  struct_type_match_solver.

  split.
  unfold V_OSEventGrp; simpl; eauto.
  lzh_simpl_int_eq. auto.
  simpl; eauto.
  simpl; eauto.
  pure_auto.

  (* ** ac: SearchAbout TCBList_P. *)
  (* ** ac: Locate tcbdllseg_get_last_tcb_ptr. *)
  (* ** ac: Check tcbdllseg_get_last_tcb_ptr. *)
  eapply TCBList_P_Combine.
  eapply tcbdllseg_get_last_tcb_ptr.
  instantiate (5:=s).
  sep cancel (tcbdllseg v'5).
  sep pauto.
  2:eauto.
  2:eauto.
  eauto.
  
  eauto.
  eauto.
  eauto.

  eapply tcbdllseg_combine_ptr_in_tcblist.
  instantiate (7:=s).
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  eauto.

  pure_auto.
  pure_auto.

  intros.
  sep auto.

  intros.
  sep auto.

  (** event task rdy precondition finished **)
  hoare unfold.


  remember (spec_code_cons
                                              (sem_post ((Vptr (v'40, Int.zero) :: nil) ++ v'2 :: nil)) v'0) as abs_code.
  inverts H69.
  subst v'60.

  (** renameing **)
  rename v'40 into pevent_addr.
  rename ct into ctcb.
  rename v'90 into htcb_addr. (** highest tcb in pevent waitlist **)
  rename H42 into Hhtcb. 
  rename H63 into Hctcb_in_tcblist. 
  rename v'61 into tcblist_head. 
  rename v'7 into tcblist_seg1.
  rename v'8 into ctcb_node.
  rename v'9 into tcblist_seg2.
  rename H46 into Hrel_et. 

  (* ** ac: Print prio_in_tbl. *)
  rename v'47 into rtbl. 
  (* ** ac: Print TCBList_P. *)

  rename v'43 into tcbls. 
  rename v'37 into tcbls1. 
  rename v'41 into tcbls2.
  (** tcbls = tcbls1 ++ tcbls2, tcbls2 = cur_node ++ tcbls2' **)
  
  remember (tcblist_seg1 ++ ctcb_node :: tcblist_seg2) as tcblist.
  
  rename v'85 into hprio. 
  assert (exists hprio', hprio = Vint32 hprio'). 
  {
    clear - H73. (** struct_type_vallist_match **)
    rename H73 into H. 
    unfold struct_type_vallist_match in H.
    unfold OS_TCB_flag in H.
    unfold struct_type_vallist_match' in H.
    mytac.
    clear - H5.
    (* ** ac: SearchAbout (rule_type_val_match Int8u _). *)
    apply rule_type_val_match_int8u_elim in H5.
    mytac.
  }
    
  hoare_lifts_trms_pre (Aisr, Ais,Aier). 
  transform_pre add_aemp_isr_is_prop ltac:(idtac). 
    
  destruct H40.
  subst hprio.
  rename x into hprio.
  
  rename v'79 into hnext. 
  rename v'86 into htcbx.
  rename v'87 into htcby.
  rename v'88 into hbitx.
  rename v'89 into hbity. 

  (* ** ac: Check tcblist_get_TCBList_P_get. *)
  (* ** ac: Check sem_post_get_tcb_stat. *)
  (* ** ac: Check rh_tcblist_ecblist_p_post_exwt_aux_sem. *)
  (* ** ac: Check rh_tcblist_ecblist_p_post_exwt_sem. *)
  assert (Hhtcb_get: exists st m sus, get tcbls (htcb_addr, Int.zero) = Some (hprio, st, m, sus)).
  {
    eapply tcblist_get_TCBList_P_get.
    eauto.
    pure_auto.
    eauto.
  }

  destruct Hhtcb_get as (st & msg & sus & Hhtcb_get).

  assert (Hs1: Int.unsigned v'73 <= 7). 
  {
    (* ** ac: Check osunmapvallist_prop. *)
    clear - H47 H22. 
    apply osunmapvallist_prop in H22.
    mytac.
    rewrite H in H47.
    inverts H47. 
    pure_auto.
  }
  
  assert (Hs2: Int.unsigned v'74 <= 255).
  {
    (* ** ac: Check array_int8u_nth_lt_len. *)
    clear - H48 Hs1 H59 H19. 
    assert (Z.to_nat (Int.unsigned v'73) < length v'53)%nat. 
    {
      rewrite H19; unfold OS_EVENT_TBL_SIZE.
      mauto.
    }
    lets Hx: array_int8u_nth_lt_len H59 H.
    mytac.
    rewrite H48 in H0.
    inverts H0.
    auto.
  }

  assert (Hs3: Int.unsigned v'72 <= 7). 
  {
    clear - H49 Hs2. 
    lets Hx: osunmapvallist_prop Hs2.
    mytac.
    rewrite H in H49; inverts H49. 
    pure_auto.
  }

  rename v'12 into pwls. 
  (* ** ac: Check post_exwt_succ_pre_sem. *)
  generalize Hhtcb_get; intro Hhtcb_join.
  apply map_join_get_sig in Hhtcb_join.
  destruct Hhtcb_join as (tcbls' & Hhtcb_join).
  assert (Hpre: pwls <> nil /\ GetHWait tcbls pwls (htcb_addr, Int.zero) /\
                TcbMod.get tcbls (htcb_addr, Int.zero) = Some (hprio, st, msg, sus) /\
                hprio = ((v'73<<ᵢ$ 3) +ᵢ  v'72)). 
  {
    apply map_join_get_sig in Hhtcb_get.
    destruct Hhtcb_get.
    (* ** ac: Check post_exwt_succ_pre_sem. *)
    apply semacc_int_eq_false in H0. 
    eapply post_exwt_succ_pre_sem; eauto.
  }

  destruct Hpre as [ ? [? [? ?]]].
  subst hprio.

  assert (Hv'1cs: v'2 <> Vint32 (Int.repr OS_NO_ERR) \/
                  v'2 = Vint32 (Int.repr OS_NO_ERR)) by tauto. 
  inversion Hv'1cs.
  (* v'2 <> ... *)
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).  
  eapply abscsq_rule.
  auto.
  eapply absimp_sem_post_ex_wt_succ_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule.
  (* v'2 = ... *) 
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).  
  eapply abscsq_rule.
  auto.
  eapply absimp_sem_post_ex_wt_succ_return; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  unfold AEventData.
  unfold_msg.
  hoare_split_pure_all.
  destruct H45.
  inverts H45.
  rename v'7 into pevent_addr.

  unfolds in H53; simpl in H53; inverts H53.
  (* ** ac: Check sem_post_get_tcb_stat. *)
  rename v'53 into etbl. 

  rename H68 into Htcblist_p.
  lets Hhtcb_node: TCBList_P_tcblist_get_TCBNode_P Htcblist_p Hhtcb Hhtcb_get.
  generalize Hhtcb_node; intro Htmp.
  unfolds in Htmp.
  mytac.
  inverts H45; inverts H53.

  rename H68 into Hh_tcbblk.
  rename H69 into Hh_tcbstat. 
  unfolds in Hh_tcbblk.
  mytac.
  inverts H44. 
  inverts H45. inverts H53. inverts H68. inverts H69. inverts H75. inverts H82.
  inverts H61.

  rename v'73 into p1.
  rename v'72 into p2. 
  remember ((p1<<ᵢ$ 3) +ᵢ  p2) as hprio.
  
  (* ** ac: Check sem_post_get_tcb_stat. *)

  assert (Hx: x7 = $ OS_STAT_SEM  \/ x7 = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)).
  {
    clear - Hrel_et.
    unfolds in Hrel_et.
    auto.
  }
(*   subst x7. *)

  assert (Hp1: (hprio >>ᵢ $ 3) =  p1).
  {
    subst hprio.
    clear - Hs1 Hs2 Hs3.
    clear Hs2.
    mauto.
  }

  assert (Hp2: hprio &ᵢ ($ 7) = p2).
  {
    subst hprio.
    clear - Hs1 Hs3.
    mauto.
  }

  assert (Hs4: Int.unsigned v'91 <= 255). 
  {
    clear - Hs1 H39 H71 H56. 
    assert (Z.to_nat (Int.unsigned p1) < length rtbl)%nat.
    {
      rewrite H71. 
      unfold OS_RDY_TBL_SIZE.
      mauto.
    }
    lets Htmp: array_int8u_nth_lt_len H56 H. 
    mytac.
    rewrite H39 in H0. 
    inverts H0.
    auto.
  }
  
  (* ** ac: Check set_node_elim_hoare. *)
  
  assert (Htmp: v'75 = $ 1 <<ᵢ p2). 
  {
    eapply math_mapval_core_prop.
    clear - Hs3.
    mauto.
    auto.
  }
  subst v'75.
  
  assert (Hno_dup: R_Prio_No_Dup tcbls).
  {
    clear - H66.
    unfolds in H66.
    mytac.
  }
  (** zhang hui's lemma **)
  hoare_lifts_trms_pre tcbdllseg. 
  eapply set_node_elim_hoare_sus with (tid:=ctcb) (tcbls:=tcbls); eauto.
  {
    eapply TCBNode_P_set_rdy_gen; auto.
    2:eauto.
    rewrite Hp1.
    apply nth_val'2nth_val; eauto.
    2: eauto.
    destruct Hx; subst x7.
    assert (Hsus: sus = false) by
    (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: sus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    change (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_SEM)) with ($ OS_STAT_SUSPEND).
    auto.
  }
  { destruct sus eqn: eq1; auto.
    unfolds.
    rewrite Hp1.
    rewrite Hp2.
    do 2 eexists.
    splits; eauto.
  }
  {
    unfolds.
    unfold V_OSTCBNext , V_OSTCBPrev.
    simpl.
    auto.
  }

  (************************* exit critical ***********************************)
  assert (Heq_sus: Int.eq (x7&ᵢInt.not ($ OS_STAT_SEM)) ($ OS_STAT_RDY) = negb sus).
  { change ($ OS_STAT_RDY) with Int.zero.
    destruct Hx; subst x7.
    assert (Hsus: sus = false) by
    (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: sus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    change (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_SEM)) with ($ OS_STAT_SUSPEND).
    auto.
   }

  hoare_split_pure_all.
  subst hprio.
  rewrite Hp1 in *.
  rewrite Hp2 in *.
  Ltac hoare_exit_critical2 :=
    match goal with
    | |- {|_ , _, ?li , _, _, _|}|- _ {{?P}} (sprim excrit) {{_}} =>
      match find_aop P with
      | some ?n =>
        hoare lifts (n::nil) pre;
        eapply excrit1_rule'_ISnil_ISRemp'''_lg(* excrit1_rule'_ISnil_ISRemp''' *);
        [ intros; try (unfold OldOSInvWL); (*sep pauto;*)trycancel
        | idtac
        ]
      | _ => fail 1
      end
    end.
  Ltac hoare_forward_prim'2 :=
    let s := fresh in
    let H := fresh in
    match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} (sseq _ _) {{ _ }} =>
      eapply seq_rule; [ hoare_forward_prim'2
                       | try hoare_invchange ]
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
      eapply forward_rule2; [ first [ hoare_enter_critical
                                    | hoare_exit_critical2
                                    | idtac ]
                            | first [ intros s H; exact H
                                    | sep pauto ] ]
    end.
  hoare_forward_prim'2.
  (*hoare forward prim.*)
  sep normal.
  sep eexists.
  sep cancel AOSMapTbl.
  sep cancel AOSUnMapTbl.
  sep cancel AOSTCBFreeList.
  sep cancel AOSTime.
  sep cancel AGVars.
  sep cancel A_isr_is_prop.
  sep cancel abstcblsid.
  sep cancel ostmid. 
  sep cancel curtid.
  sep cancel Aier.
  sep split; auto.
  sep cancel p_local.
  
  sep cancel AOSRdyTblGrp.
  sep cancel IntInv.
  sep cancel TmrInv.
  (* sep cancel CoreCommuInv. *)
  (* sep cancel PartitionInv. *)
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.

  unfold EvtInv.
  sep normal.
  sep eexists.
  sep pauto.
  
  sep cancel AOSEventFreeList. 
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.

  (** AECBList **)
  unfold AECBList.
  sep normal.
  sep eexists.
  sep cancel OSEventList. 
  eapply lzh_evsllseg_compose.
  sep cancel evsllseg.
  sep cancel evsllseg.
  unfold AEventNode.
  unfold_msg.
  sep normal.
  sep eexists.
  sep split; auto.
  sep cancel Astruct.
  sep cancel Aarray.
  instantiate (23 := DSem i2). 
  unfold AEventData.
  sep split; auto.

  sep cancel AOSPostEventTbl.
  sep_lifts_trms AOSTCBPrioTbl.
  (** AOSTCBPrioTbl **)
  unfold AOSTCBPrioTbl.
  sep normal.
  sep eexists.
  sep split; auto.
  sep cancel vhold_addr. (* PV vhold_addr .. *)
  sep cancel GAarray.
  sep cancel OSPlaceHolder.
  sep cancel absptls.

  sep_lifts_trms AOSTCBList.
  (** AOSTCBList **)
  unfold AOSTCBList.
  sep normal.
  sep eexists.
  sep split; auto.
  sep cancel OSTCBList. 
  sep cancel tcbdllseg.
  sep cancel OSTCBCur. 
  sep cancel tcbdllseg.
  
  (** tcbdllflag **) 
  get_hsat Hsat.
  sep_lifts_trms_in Hsat tcbdllflag.
  unfold AEventData in Hsat. 
  eapply tcbdllflag_set_node in Hsat; eauto.
  sep cancel tcbdllflag.
  2: { unfold same_prev_next. simpl. splits; auto. }

  unfold tcbllsegevaux in *.
  sep_lifts_trms llsegevaux.
  eapply llsegevaux_set_node; eauto.
  2: { unfold same_prev_next. simpl. splits; auto. }
  sep cancel llsegevaux.
  eapply ASemEIBs_sem_set_wls'_preserve; eauto. 
  sep cancel ASemEIBs.
  eapply AMuxEIBs_sem_set_wls'_preserve; eauto.
  sep cancel AMuxEIBs. 
  eapply AMqEIBs_sem_set_wls'_preserve; eauto. 
  sep cancel AMqEIBs. 
  cancel_corecommuinv. 
  cancel_partitioninv.
  eauto.
  
  (** TCBList_P **)
  rewrite Heq_sus. rewrite negb_if.
  eauto.
  rewrite Heq_sus. rewrite negb_if.
  eauto.
  eauto.
  split; auto.

(*RH_PrioTbl_P*)
  eauto.
  (** R_PrioTbl_P **)
  eapply r_priotbl_p_set_hold; auto; eauto.
  eauto.
  split; auto.

  clear - H23.
  int auto.

  (** ecblist_p **)
  eapply ecblist_p_post_exwt_hold_sem
    with (v'12:=v'51) (v'39:=p2) (v'69:=v'74) (v'38:=p1) (v'13:=etbl) (v'36:=v'46); eauto. 
  
  eapply rl_etbl_ptbl_p; auto; eauto.

  lzh_simpl_int_eq; auto.
  
  clear - Hs3.
  mauto.

  (* RL_Tbl_Grp_P *)
  eauto.
  go. eauto.
  go.
  go. eauto. eauto.
  split; auto.
  go.
  simpl. eauto. eauto.

  eapply mq_ecb_p_sem_set_wls'_preserve; eauto. 
  eapply mux_ecb_p_sem_set_wls'_preserve; eauto.
  eapply sem_ecb_p_sem_set_wls'_preserve; eauto.

  assert (Htmp: ctcb = (htcb_addr, Int.zero) \/ ctcb <> (htcb_addr, Int.zero)) by tauto.
  destruct Htmp.
  subst ctcb.
  unfolds.
  unfold get; simpl.
  rewrite TcbMod.set_a_get_a.
  eauto.
  apply tidspec.eq_beq_true; auto.
  eapply rh_curtcb_set_nct; auto.

  assert (Hst: exists xl, st = wait (os_stat_sem (pevent_addr, Int.zero)) xl).
  {
    eapply rh_tcblist_ecblist_p_post_exwt_aux_sem ;eauto.
    clear -H42. 
    unfolds in H42; mytac; auto. 
  }
  destruct Hst as (t_opt & Hst).
  subst st.

  eapply rh_tcblist_ecblist_p_post_exwt_sem;eauto.
  (* ** ac: Check rh_tcblist_ecblist_p_post_exwt_sem. *)
  clear -H42.
  unfolds in H42; mytac; auto.

  (* unfold AEventData. *)
  pure_auto.

  (* crit. region exited *)

  hoare_split_pure_all.

  Ltac hoare_call2 :=
    match goal with
    | |- {| _, _, ?li, _, _, _ |} |- ?ct {{ ?P }} scall _ ?el {{ _ }} =>
      match find_aop P with
      | some ?n =>
        hoare lifts (n::nil)%nat pre;
        eapply call_rule';
        [intuition eauto |
         intros;
         do 5 try (apply rvl_elim;[ symbolic_execution | ]);
         first [apply rvl_nil | simpl;auto] |
         intros;unfold_spec(*;sep pauto*) |
         idtac |
         sep_unfold_funpost |
         sep_unfold_funpre |
         simpl;eauto
        ]
      | none _ => idtac
      end
    end.
  eapply seq_rule; eapply forward_rule2.
  1: hoare_call2.
  5: try sep_unfold_funpost; sep pauto.
  6: sep pauto.
  (*hoare forward.*)

  sep normal.
  sep eexists.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel Aop. 
  sep cancel Aier.
  sep cancel p_local.
  sep split; auto.
  exact_s.
  unfolds; auto.
  go.
  intros.
  get_hsat Hsat. sep destruct Hsat.
  eexists.
  sep cancel p_local.
  sep auto.

  intros.
  get_hsat Hsat. sep destruct Hsat. 
  eexists.
  sep cancel p_local. 
  sep auto.

  hoare unfold.
  inverts H77. (* logic_code ... *)

  hoare_lifts_trms_pre Aop. 
  eapply abscsq_rule.
  pure_auto.
  eapply absinfer_seq_end.
  pure_auto.
  2: eauto.
  pure_auto.
  eapply absinfer_eq.

  eapply forward_rule2.
  1: eapply rete_rule'; [symbolic execution | intros].
  2: try sep_unfold_funpost; sep pauto.
  (*hoare forward.*)
  
  sep cancel A_dom_lenv.
  sep normal.
  exists (Vptr (pevent_addr, Int.zero)).
  eexists.
  exists v'0.
  sep eexists.
  sep cancel Aop. 
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel p_local.
  sep cancel x.
  sep cancel pevent.
  sep cancel Aier.
  sep pauto.

  introv Hp. simpl in Hp. inverts Hp.

  Unshelve.
  auto.
  auto.
  auto.
  auto. auto. auto.
Qed.


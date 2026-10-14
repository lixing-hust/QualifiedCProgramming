From Coq Require Import Lia.

Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import os_ucos_h.

Require Import os_q.
Require Import evtinv_lemmas.
Require Import hoare_assign_tac_ext.
(* Require Import sem_common.
Require Import sem_common_ext.  *)
(* Require Import tcblist_setnode_lemmas.
Import OSQPostPure.
 *)
Require Import include_frm. 
Require Import abs_infer_step.
Require Import ucos_frmaop.
Require Import seplog_lemmas.
Require Import seplog_tactics.
Require Import abs_infer_abt.
Require Import seplog_trm_tacs.
Require Import q_common.
Require Import evauxvar_lemmas.
Require Import evaux_pure.
Require Import freeevtlist_lemmas.

Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

(*********************** sem acc **************************************)

Ltac simpl_sat H := unfold sat in H; fold sat in H; simpl substmo in H; simpl getmem in H; simpl getabst in H; simpl empst in H.

Lemma absinfer_seq1:
  forall (p : asrt) (s1 : absop)  (s2 : spec_code) (s1' : absop) (sc : ossched),
                   can_change_aop p ->
                   sc ⊢  <|| s1 ||>  ** p ⇒  <|| s1' ||>  ** p ->
                   sc ⊢  <|| s1;; s2 ||>  ** p ⇒  <|| s1';; s2 ||>  ** p.
Proof.
intros.
eapply absinfer_seq; try eauto.
Qed.


Lemma qacc_absimp_null_abt:
  forall sid v_ret P sch s,
    sid = Vnull ->
    v_ret <> Vnull ->
    can_change_aop P ->
    absinfer sch (<|| spec_code_cons (qacceptnew (sid :: v_ret :: nil)) s ||> ** P) 
               (<||ABORT||> ** P).
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



Lemma qacc_absimp_null:
  forall sid v_ret P sch s,
    sid = Vnull ->
    v_ret = Vnull ->
    can_change_aop P -> 
    absinfer sch ( <|| spec_code_cons (qacceptnew (sid :: v_ret :: nil)) s ||> ** P) 
                 ( <|| s ||> ** P ).
Proof.
  introv Hsid Hv' Hcop.
  eapply absinfer_trans. 
  simpl.
  eapply absinfer_choice1.
  3: eauto. 
  pure_auto. pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1. pure_auto.
  instantiate (1:=END (Some Vnull)).
  infer_solver 0%nat. 
  eexists.
  splits; eauto.
  subst sid. auto. 
  eapply absinfer_seq_end; try pure_auto.
Qed.

Lemma qacc_absimp_no_q:
  forall P qls sid v' sch s,
    can_change_aop P ->
    (~ exists x y pwl wls,get qls sid = Some (absmsgq x y pwl,wls) ) ->
    v' = Vnull ->
    absinfer sch
      (<|| spec_code_cons (qacceptnew ((Vptr sid) :: v' :: nil)) s ||> ** HECBList qls ** P) 
      (<|| s ||> ** HECBList qls ** P). 
Proof.
  introv Hcop Hnsem Hv'.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.

  eapply absinfer_trans.
  eapply absinfer_choice1. 
  pure_auto. 2: eauto. pure_auto.
  infer_solver 0%nat. 
Qed.

Lemma qacc_absimp_no_q_abt:
  forall P qls sid v' sch s,
    can_change_aop P ->
    (~ exists x y pwl wls,get qls sid = Some (absmsgq x y pwl,wls) ) ->
    v' <> Vnull ->
    absinfer sch
      (<|| spec_code_cons (qacceptnew ((Vptr sid) :: v' :: nil)) s ||> ** HECBList qls ** P) 
      (<|| ABORT ||> ** HECBList qls ** P). 
Proof.
  introv Hcop Hnsem Hv'.
  eapply absinfer_trans.
  simpl.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
(*   eapply absinfer_trans.
  simpl.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto. *)
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

Lemma qacc_absimp_no_msg:
  forall P qls n pwl sid v' wls sch s,
    can_change_aop P ->
    get qls sid =Some (absmsgq nil n pwl,wls) ->
    v' = Vnull ->
    absinfer sch
      (<|| spec_code_cons (qacceptnew ((Vptr sid) :: v' :: nil)) s ||> ** HECBList qls ** P) 
      (<|| s ||> ** HECBList qls ** P). 
Proof.
  introv Hcop Hnsem Hv'.
  eapply absinfer_trans.
  simpl.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
(*   eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto. *)
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice1. 
  pure_auto. 2: eauto. pure_auto.
  infer_solver 0%nat. 
Qed.

Lemma qacc_absimp_no_msg_abt:
  forall P qls n pwl sid v' wls sch s,
    can_change_aop P ->
    get qls sid =Some (absmsgq nil n pwl,wls) ->
    v' <> Vnull ->
    absinfer sch
      (<|| spec_code_cons (qacceptnew ((Vptr sid) :: v' :: nil)) s ||> ** HECBList qls ** P) 
      (<|| ABORT ||> ** HECBList qls ** P). 
Proof.
  introv Hcop Hnsem Hv'.
  eapply absinfer_trans.
  simpl.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
(*   eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto. *)
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

Lemma  neq_set_get:
  forall (A B T : Type) (MC: PermMap A B T) x y b tcbls,
    x <> y ->
     get (set tcbls y b) x =  get tcbls x.
Proof.
  intros.
  jeauto2.
Qed.

(* Lemma RH_ECB_EINFO_P_Q_set :
forall qls sid msg mls n pwl wls embls ,
(* EcbMod.get qls eid = Some (abssem n, wls) -> *)
EcbMod.get qls sid = Some (absmsgq (msg::mls) n pwl, wls) ->
RH_ECB_EINFO_P qls embls ->
RH_ECB_EINFO_P (set qls sid (absmsgq mls n pwl, wls)) embls.
Proof.
  intros.
  unfold RH_ECB_EINFO_P.
  intros.
  assert (eid = sid \/ eid <> sid) by tauto.
  destruct H2.
  rewrite H2 in H1.
  assert (get (set qls sid (absmsgq mls n pwl, wls)) sid = Some (absmsgq mls n pwl, wls)).
  eapply map_get_set.
  unfold get in H1.
  unfold get in H3.
  unfold set in H1.
  unfold set in H3.
  unfold EcbMap in H1, H3.
  rewrite H3 in H1.
  tryfalse.

  unfold RH_ECB_EINFO_P in H0.
  eapply H0.
  eapply neq_set_get in H2.
  erewrite H2 in H1.
  eapply H1.

Qed. *)

(* Lemma RH_SEM_EINFO_ECB_P_Q_set :
forall qls sid msg mls n pwl wls embls ,
EcbMod.get qls sid = Some (absmsgq (msg::mls) n pwl, wls) ->
RH_SEM_EINFO_ECB_P qls embls ->
RH_SEM_EINFO_ECB_P (set qls sid (absmsgq mls n pwl, wls)) embls.
Proof.
  unfold RH_SEM_EINFO_ECB_P.
  intros.
  assert (Hi: eid = sid \/ eid <> sid) by tauto.
  destruct Hi.  
  eapply H0 in H1.
  do 2 destruct H1.
  unfold get in  *.
  unfold EcbMap in *.
  inverts H2.
  rewrite H1 in H.
  tryfalse.

  eapply H0 in H1.
  do 2 destruct H1.
  exists x. exists x0.
  assert (get (set qls sid (absmsgq mls n pwl, wls)) eid = get qls eid).
  {
    eapply neq_set_get.
    auto.
  }
  rewrite H3.
  eapply H1.
Qed.


Lemma RH_EIBlk_ECBlk_Q_P_set :
forall qls sid msg mls n pwl wls qattrb,
EcbMod.get qls sid = Some (absmsgq (msg::mls) n pwl, wls)  ->
RH_EIBlk_ECBlk_Q_P qls qattrb ->
RH_EIBlk_ECBlk_Q_P (set qls sid (absmsgq mls n pwl, wls)) qattrb.
Proof.
  unfold RH_EIBlk_ECBlk_Q_P.
  intros.
  assert (Hi: eid = sid \/ eid <> sid) by tauto.
  destruct Hi.
  subst.
  exists mls n pwl wls.
  eapply EcbMod.set_a_get_a.
  eapply tidspec.eq_beq_true.
  auto.
  assert (Hg: get (set qls sid (absmsgq mls n pwl, wls)) eid = get qls eid).
  eapply EcbMod.set_a_get_a'.
  eapply tidspec.neq_beq_false.
  eauto.
  rewrite Hg.
  eauto.
Qed.

Lemma RH_ECBlk_EIBlk_Mux_P_Q_set :
forall qls sid msg mls n pwl wls qattrb,
EcbMod.get qls sid = Some (absmsgq (msg::mls) n pwl, wls)  ->
RH_ECBlk_EIBlk_Mux_P qattrb qls->
RH_ECBlk_EIBlk_Mux_P qattrb (set qls sid (absmsgq mls n pwl, wls)) .
Proof.
  unfold RH_ECBlk_EIBlk_Mux_P.
  intros.
  assert (Hi: eid = sid \/ eid <> sid) by tauto.
  destruct Hi.
  subst.
  eapply H0 in H1;eauto.
  simpljoin1.
  unfold get in H1. unfold EcbMap in H1.
  rewrite H1 in H.
  tryfalse.
  eapply H0 in H1;eauto.
  do 3 destruct H1.
  exists x x0 x1.
  assert (get (set qls sid (absmsgq mls n pwl, wls)) eid = get qls eid).
  {
    eapply neq_set_get.
    auto.
  }
  rewrite H4.
  eapply H1.
Qed. *)




(* Lemma qacc_absimp_succ:
  forall P qls sid msg mls n pwl wl v' sch infol embls vhold pbls ebls qattrl qattr,
    can_change_aop P ->
    EcbMod.get qls sid =Some (absmsgq (msg::mls) n pwl,wl) ->
    v' = msg ->
    absinfer sch
      ( <||  qacceptnew (Vptr sid :: v' :: nil) ||> **
        HECBList qls **
        ACNU (infol) embls qls vhold pbls ebls qattrl qattr ** P)
      ( <|| END Some msg ||> **
        HECBList (set qls sid (absmsgq mls n pwl,wl)) **
        ACNU infol embls (set qls sid (absmsgq mls n pwl,wl)) vhold pbls ebls qattrl qattr ** P).
Proof.
intros.
unfold qacceptnew.
simpl.
assert (can_change_aop (HECBList qls ** ACNU infol embls qls vhold pbls ebls qattrl qattr ** P)) .
can_change_aop_solver.

infer_solver 4%nat.
unfold ACNU in *.
unfold AEINFO in *.
unfold AMqEIBAarray in *.
sep pauto.
unfold R_ECBlk_EIBlk_Q_P.
split.
eapply RH_ECBlk_EIBlk_Q_P_set; eauto. eapply H8.
eapply RH_EIBlk_ECBlk_Q_P_set. eauto. eapply H8.
eapply RH_EINFO_ECB_All_Q_P_set; eauto.
Qed. *)

Lemma qacc_absimp_pwl_is_nil:
  forall P qls n pwl msg mls sid v' wl sch s,
    can_change_aop P ->
    get qls sid = Some (absmsgq (msg::mls) n pwl ,wl) ->
    pwl = nil ->
    absinfer sch
      (<|| spec_code_cons (qacceptnew ((Vptr sid) :: v' :: nil)) s ||> ** HECBList qls ** P) 
      (<|| qacc_succ (|Vptr sid :: v' :: nil|);; s ||> ** HECBList qls ** P). 
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  infer_solver 0%nat.
Qed.

Lemma qacc_absimp_pwl_is_nil_abt:
  forall P qls n pwl msg mls sid v' wl sch s,
    can_change_aop P ->
    get qls sid = Some (absmsgq (msg::mls) n pwl ,wl) ->
    pwl <> nil ->
    absinfer sch
      (<|| spec_code_cons (qacceptnew ((Vptr sid) :: v' :: nil)) s ||> ** HECBList qls ** P) 
      (<|| ABORT ||> ** HECBList qls ** P). 
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto. 2: eauto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate (1:= HECBList qls ** P).
  can_change_aop_solver.
  instantiate (1:= ABORT).
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  can_change_aop_solver.
  eapply absinfer_seq_abt; try pure_auto. 
Qed.

Lemma qacc_absimp_succ':
  forall P qls sid msg mls n pwl wl v' sch vhold v1 v2 v3 tcblh tcbvl s,
  
    can_change_aop P ->
    EcbMod.get qls sid =Some (absmsgq (msg::mls) n pwl,wl) ->
    v' = msg ->
    absinfer sch
      ( <|| qacc_succ (|Vptr sid :: v' :: nil|);; s ||> **
        HECBList qls ** EvtInv_part2 qls tcblh tcbvl vhold v1 v2 v3 **  P)
      ( <|| s ||> **
        HECBList (set qls sid (absmsgq mls n pwl,wl)) **
        EvtInv_part2 (set qls sid (absmsgq mls n pwl,wl)) tcblh tcbvl vhold v1 v2 v3 ** P).
Proof.
  intros.
    infer_solver 0%nat. 
  unfold EvtInv_part2 in *.
  unfold ASemEIBs in *.
  unfold AMuxEIBs in *.
  unfold AMqEIBs in *.
  sep pauto.
  eapply q_ecb_p_que_all_preserve;eauto.
  eapply mux_ecb_p_que_all_preserve;eauto.
  eapply sem_ecb_p_que_all_preserve; eauto.
  eapply RH_SEM_EINFO_ECB_P_Q_set'. eauto. eauto.  
  eapply RH_MUX_AMuxEIBs_ECB_P_Q_set'; eauto.  
  eapply RH_EIBlk_ECBlk_Q_P_set';eauto.
Qed.

Lemma qacc_absimp_succ_abt'':
  forall P qls sid msg mls n pwl wl v' sch s,
    can_change_aop P ->
    EcbMod.get qls sid =Some (absmsgq (msg::mls) n pwl,wl) ->
    v' <> msg ->
    absinfer sch
      ( <|| qacc_succ (|Vptr sid :: v' :: nil|);; s ||> ** HECBList qls ** P)
      ( <|| ABORT ||> **  HECBList qls ** P).
Proof.
intros.
assert (Hc: can_change_aop (HECBList qls ** P)) .
can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_seq1; try pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  eapply absinfer_seq_abt; try pure_auto. 
Qed.

(* 
(* new in OSSemAcceptProof.v *) *)

Require Import abs_op.
Require Import init_spec.
Require Import inv_prop. (*change*)
Require Import hoare_tactics.
Require Import pure_auto.
Require Import ucos_pauto.
Require Import seplog_tactics.
Require Import seplog_lemmas.
Require Import sep_cancel_ext.
Require Import derived_rules.
Require Import hoare_conseq.
Require Import ucos_forward. (*change*)
Require Import sem_corecommu.

Fixpoint get_ectr (eid:val) (head:val) (ectrl:list EventCtr) :=
  match eid,head,ectrl with
    | (Vptr e),(Vptr e'),(osevent, etbl,petbl)::vll =>
      match beq_addrval e e' with
        | true => Some (osevent,etbl, petbl)
        | false => match V_OSEventListPtr osevent with
                     | Some vn => get_ectr eid vn vll
                     | _ => None
                   end
      end
    | _,_,_ => None
  end.

Ltac mytac :=
  heat; jeauto2.

Lemma joinsig_beq_addrval_false_get : forall a a1 x x1 m1 m2,
  joinsig a x m1 m2 -> EcbMod.get m2 a1 = Some x1 -> a <> a1 -> EcbMod.get m1 a1 = Some x1. 
Proof.
  intros.
  unfold joinsig in H.
  pose proof H a1.
  rewrite EcbMod.get_sig_none in H2; auto.
  rewrite H0 in H2.
  destruct (EcbMod.get m1 a1); tryfalse.
  substs; auto.
Qed.

Lemma beq_pos_true : forall p, beq_pos p p = true.
Proof.
  inductions p.
  unfolds.
  fold beq_pos.
  rewrite IHp; auto.
  unfolds.
  fold beq_pos.
  rewrite IHp; auto.
  simpl; auto.
Qed.

Lemma beq_addrval_false_neq : forall a1 a2, beq_addrval a1 a2 = false -> a1 <> a2.
Proof.
  intros.
  unfolds in H.
  destruct a1, a2.
  intro.
  inverts H0.
  rewrite beq_pos_true in H.
  rewrite Int.eq_true in H.
  simpl in H; tryfalse.
Qed.


(* Lemma ECBList_P_get_ectr_some : forall (l:list EventCtr) tl ecbls mqls tcbls a x v,
  EcbMod.get mqls a = Some x -> ECBList_P v tl l ecbls mqls tcbls ->
  exists et etbl, get_ectr (Vptr a) v l = Some (et, etbl).
Proof.
  inductions l; intros.
  simpl in H0; mytac.
  unfolds in H; simpl in H; tryfalse.
  simpl in H0.
  destruct ecbls; mytac; tryfalse.
  destruct a; mytac.
  simpl.
  destruct (beq_addrval a0 x0) eqn : eq1.
  eauto.
  rewrite H0.
  assert (EcbMod.get x2 a0 = Some x).
  apply beq_addrval_false_neq in eq1.
  eapply joinsig_beq_addrval_false_get; eauto.
  clear H.
  eapply IHl; eauto.
Qed. *)

Lemma ECBList_P_get_ectr_some : forall (l:list EventCtr) tl ecbls mqls tcbls a x v,
  EcbMod.get mqls a = Some x -> ECBList_P v tl l ecbls mqls tcbls ->
  exists et etbl, get_ectr (Vptr a) v l = Some (et, etbl).
Proof.
  inductions l; intros.
  simpl in H0; mytac.
  unfolds in H; simpl in H; tryfalse.
  simpl in H0.
  destruct ecbls; mytac; tryfalse.
  destruct a; destruct p; mytac.
  simpl.
  destruct (beq_addrval a0 x0) eqn : eq1.
  eauto.
  rewrite H0.
  assert (EcbMod.get x2 a0 = Some x).
  apply beq_addrval_false_neq in eq1.
  eapply joinsig_beq_addrval_false_get; eauto.
  clear H.
  eapply IHl; eauto.
Qed.


Lemma beq_addrval_eq: forall a b, beq_addrval a b = true -> a = b.
Proof.
  introv HeqX.
  unfold beq_addrval in HeqX.
  destruct b, a.
  rewrite andb_true_iff in HeqX.
  destruct HeqX.
  rewrite beq_pos_Pos_eqb_eq in H.
  apply Peqb_true_eq in H.
  lets Hx: Int.eq_spec i0 i.
  rewrite H0 in Hx.
  subst.
  auto.
Qed.

Lemma eq_beq_addrval: forall a, beq_addrval a a = true.
Proof.
  unfold beq_addrval.
  destruct a.
  rewrite andb_true_iff.
  split.
  rewrite beq_pos_Pos_eqb_eq.
  apply Pos.eqb_refl.
  apply Int.eq_true.
Qed.

Ltac xunfold' H:=
  let M:= fresh in  
  match type of H with
    | match ?X with
        | _ => _
      end = Some _ => remember X as M;destruct M;tryfalse;auto
    | _ => idtac
  end.

Lemma get_ectr_decompose:
  forall qptrl s P msgqls l x y p eid,
    s |= evsllseg p Vnull qptrl msgqls ** P ->
    get_ectr (Vptr eid) p qptrl = Some ((l,x),y) ->
    s |= EX vn qptrl1 qptrl2 msgqls1 msgqls2 msgq, 
  [| V_OSEventListPtr l = Some vn /\
     qptrl = qptrl1 ++ (((l, x), y) :: nil) ++ qptrl2 /\
     msgqls = msgqls1 ++ (msgq :: nil) ++ msgqls2 /\ get_ectr (Vptr eid) p qptrl1 = None /\
   (get_ectr  (Vptr eid) p (qptrl1++ (((l, x) ,y) :: nil)) = Some ((l,x),y)) /\ p <> Vnull /\ forall l,In l qptrl1 -> exists x,V_OSEventListPtr (fst (fst l)) = Some (Vptr x)|] **
                                                     AEventNode (Vptr eid) l x y msgq **
                                                     evsllseg p (Vptr eid) qptrl1 msgqls1 ** evsllseg vn Vnull qptrl2 msgqls2 ** P.
Proof.
  induction qptrl.
  intros.
  simpl evsllseg in *.
  sep split in H.
  destruct H1;subst.
  simpl in H0.
  tryfalse.
  intros.
  simpl evsllseg in *.
  destruct msgqls.
  simpl in H;mytac;tryfalse.
  destruct a as (osevent,petbl).
  destruct osevent as (osevent, etbl).
  sep normal in H.
  sep destruct H.
  sep split in H.
  simpl in H0.
  destruct p;tryfalse.
  remember (beq_addrval eid a) as X.
  destruct X.
  inverts H0.
  sep lift 2%nat in H.
  exists x0 (nil:list EventCtr) qptrl.
  exists (nil:list EventData) msgqls e.
  simpl evsllseg.
  symmetry in HeqX.
  apply beq_addrval_eq in HeqX.
  subst.
  sep auto.
  simpl;splits;auto.
  rewrite eq_beq_addrval.
  auto.
  intro;tryfalse.
  intros.
  tryfalse.
  xunfold' H0.
  inverts H1.
  sep lift 2%nat in H.
  lets Hx: IHqptrl H H0.
  sep normal in Hx.
  clear H.
  sep destruct Hx.
  sep split in Hx.
  mytac.
  clear IHqptrl.
  sep auto.
  Focus 2.
  splits;simpl.
  eauto.
  instantiate (1:=x3).
  instantiate (1:= (osevent, etbl, petbl) :: x2).
  simpl.
  auto.
  instantiate (1:= x5).
  instantiate (1:= x6).
  instantiate (1:= e :: x4).
  simpl;auto.
  simpl.
  rewrite <- HeqX.
  rewrite <- HeqH2.
  auto.
  simpl.
  rewrite <- HeqX.
  rewrite <- HeqH2.
  auto.
  intro;tryfalse.
  intros.
  simpl in H1.
  destruct H1;auto.
  subst.
  simpl.
  rewrite <- HeqH2.
  destruct eid;tryfalse.
  destruct x2;destruct x0;simpl in H4;tryfalse;eexists;auto.
  simpl evsllseg at 1.
  sep auto.
Qed.

Lemma evsllseg_aux:
  forall l1 s a b l2 P,
    s |= evsllseg a b l1 l2 ** P ->
    (a = b /\ l1 = nil \/ get_last_ptr l1 = Some b) /\ length l1 = length l2.
Proof.
  inductions l1.
  intros.
  simpl in H.
Import DeprecatedTactic.
  mytac.
  left.
  auto.
  auto.
  intros.
  unfold evsllseg in H.
  fold evsllseg in H.
  destruct l2.
  simpl in H.
  mytac; tryfalse.
  destruct a.
  destruct p.
  sep normal in H.
  sep destruct H.
  sep lift 3%nat in H.
  lets Hxax: IHl1 H.
  mytac.
  2: simpl; auto.
  destruct H0.
  mytac.
  right.
  unfolds.
  simpl.
  sep split in H.
  auto.
  right.
  unfolds.
  simpl.
  destruct l1.
  unfolds in H0.
  simpl in H0.
  unfolds in H0.
  unfold nth_val in H0.
  tryfalse.
  simpl.
  auto.
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
  destruct a;destruct p; simpljoin.
  unfold1 evsllseg in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0.
  rewrite H in H6.
  inverts H6.
  eapply IHls1.
  eauto.
  sep lift 2%nat in H0.
  eauto.
Qed.



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

Ltac lzh_destruct_event :=
  match goal with
    | |- context [match ?d with
                    | DMsgQ _ _ _ _ => _
                    | DSem _ => _
                    | DMbox _ => _
                    | DMutex _ _ => _
                  end] => destruct d
    | _ => fail
  end.

Ltac lzh_unfold_event := 
  try unfold AEventNode;
    try unfold AEventData; 
      try lzh_destruct_event;
      try unfold AMsgData; 
      try unfold AOSQCtr; try unfold AOSQBlk;
    try unfold AOSEvent;
      try unfold AOSEventTbl;
  try unfold node. 

Ltac lzh_unfold_var x := 
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
   end.  
  
Ltac lzh_unfold_exprlist ls :=  
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
  end. 

Ltac lzh_hoare_unfold :=
  try unfold OSInv; try unfold_funpost;
  match goal with
    | |- {| _, _, _, _, _, _ |} |- ?ct {{ _ }} _ {{ _ }} =>
      hoare_split_pure_all;
        let x := find_first_exprs in
          lzh_unfold_exprlist x; pure_intro
    | _ => idtac
  end.

Ltac lzh_val_inj_solver :=
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
  end.

Lemma val_inj_true:
  forall (be : bool),
    val_inj
      (if be
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)) <> Vint32 Int.zero /\
    val_inj
      (if be
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)) <> Vnull /\
    val_inj
      (if be
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)) <> Vundef ->
    be = true.
  lzh_val_inj_solver.
Qed.

Lemma val_inj_false:
  forall (be : bool),
     val_inj
       (if be
        then Some (Vint32 Int.one)
        else Some (Vint32 Int.zero)) = Vint32 Int.zero \/
     val_inj
       (if be
        then Some (Vint32 Int.one)
        else Some (Vint32 Int.zero)) = Vnull ->
     be = false.
  lzh_val_inj_solver.
Qed.

Lemma val_inj_not_true:
  forall (be : bool),
    val_inj
      (notint
         (val_inj
            (if be
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) <> Vint32 Int.zero /\
       val_inj
         (notint
            (val_inj
               (if be
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) <> Vnull /\
       val_inj
         (notint
            (val_inj
               (if be
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) <> Vundef ->
    be = false.
  lzh_val_inj_solver.
Qed.

Lemma val_inj_not_false:
  forall (be : bool),
     val_inj
       (notint
          (val_inj
             (if be
              then Some (Vint32 Int.one)
              else Some (Vint32 Int.zero)))) = Vint32 Int.zero \/
     val_inj
       (notint
          (val_inj
             (if be
              then Some (Vint32 Int.one)
              else Some (Vint32 Int.zero)))) = Vnull ->
     be = true.
  lzh_val_inj_solver.
Qed.

(* ** ac: Locate val_inj_impl_Vptr. *)

(* val_inj_impl_eq is exists *)

Lemma val_inj_impl_neq:
  forall x y,
    val_inj (val_eq x y) = Vint32 Int.zero \/
    val_inj (val_eq x y) = Vnull ->
    x <> y.
  (* 对x y做destruct，需要编写通用的tactic来解决这类问题 *)
  intros.
  assert (x = y \/ x <> y) by tauto.
  destruct H0.
  subst.
  unfold val_eq in H.
  destruct y.
  unfold val_inj in H.
  destruct H; tryfalse.
  unfold val_inj in H; destruct H; tryfalse.
  rewrite Int.eq_true in H.
  unfold val_inj in H; destruct H; tryfalse.
  destruct a.
  destruct (peq b b).
  rewrite Int.eq_true in H; unfold val_inj in H; destruct H; tryfalse.
  tryfalse.
  auto.
Qed.


Ltac lzh_val_inj_simpl :=
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

Ltac exact_s :=
  match goal with
    | H : ?s |= _ |- ?s |= _ =>
      exact H
  end.

Ltac transform_pre lemma cancel_tac :=
  eapply backward_rule1;
  [ intros; 
    eapply lemma; 
    match goal with
      | |- ?s |= _ => 
        cancel_tac;
        try exact_s;
        sep pauto
      | _ => solve [eauto;auto | pauto]
    end  
   | idtac ].

Local Open Scope int_scope.


Lemma qacc_eventtype_neq_q:
   forall s P a msgq mq t,
    s |= AEventData a msgq ** P ->
    RLH_ECBData_P msgq mq ->
    V_OSEventType a = Some (Vint32 t) ->
    Int.eq t ($ OS_EVENT_TYPE_Q) = false ->
    s |= AEventData a msgq **
         [| (~ exists m n pwl wl, mq = (absmsgq m n pwl,wl)) |] ** P.
  intros.

  unfold AEventData in *.
  destruct msgq eqn:Hmsgq.
  sep split in H.
  sep auto.
  sep split in H.
  rewrite H4 in H1.
  inverts H1.
  rewrite Int.eq_true in H2.
  tryfalse.

  sep split in H.
  sep auto.
  unfold RLH_ECBData_P in H0.
  destruct mq; destruct e eqn:Hmq; tryfalse.
  unfold not; intros; mytac; tryfalse.

  sep split in H.
  sep auto.
  unfold RLH_ECBData_P in H0.
  destruct mq; destruct e eqn:Hmq; tryfalse.
  unfold not; intros; mytac; tryfalse.

  sep split in H.
  sep auto.
  unfold RLH_ECBData_P in H0.
  destruct mq; destruct e eqn:Hmq; tryfalse.
  unfold not; intros; mytac; tryfalse.
  
  sep split in H.
  sep auto.
  unfold RLH_ECBData_P in H0.
  destruct mq; destruct e eqn:Hmq; tryfalse.
  unfold not; intros; mytac; tryfalse.
Qed.

Require Import sem_lab.


Lemma osq_same_blk_st_out'
: forall (qptr qst qend qin qout qsz qen : val) 
         (b : block) (i : int32),
    WellformedOSQ
      (qptr
         :: qst :: qend :: qin :: qout :: qsz :: qen :: Vptr (b,i) :: nil) ->
    exists i', qout = Vptr (b, i').
Proof.
  introv Hwf.
  funfold Hwf.
  simpl in H5.
  funfold H9.
  funfold H10.
  unfold ptr_offset_right in *.
  unfold ptr_minus in *.
  inverts H5.
  unfolds in H8.
  simpl in *.
  simp join.
  rewrite H5 in *.
  destruct x1.
  destruct x2.
  remember ((b0 =? b)%positive ) as Hbool.
  destruct Hbool; tryfalse.
  simp join.
  rewrite Pos2Z.inj_eqb in HeqHbool.
  apply eq_sym in HeqHbool.
  apply Z.eqb_eq in HeqHbool.
  apply eq_sym in HeqHbool.
  inverts HeqHbool.
  remember ((b1 =? b0)%positive ) as Hbool.
  destruct Hbool; tryfalse.
  simp join.
  rewrite Pos2Z.inj_eqb in HeqHbool.
  apply eq_sym in HeqHbool.
  apply Z.eqb_eq in HeqHbool.
  inverts HeqHbool.
  eauto.
Qed.


Open Scope Z_scope.

Lemma wellq_props:
  forall x12 x11 x5 x6 v'49 x i2 i1  v'47 x13 x14 v2 v'46,
    length v2 = ∘OS_MAX_Q_SIZE ->
    Int.ltu ($ 0) i1 = true ->
    RLH_ECBData_P
      (DMsgQ (Vptr (v'47, Int.zero))
             (x12
                :: x11
                :: x5
                :: x6
                :: Vptr (v'49, x)
                :: Vint32 i2
                :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil)
             (x13 :: x14 :: nil) v2) v'46 ->
    WellformedOSQ
      (x12
         :: x11
         :: x5
         :: x6
         :: Vptr (v'49, x)
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) ->
    Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) <= Int.unsigned x /\
    4 * ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4) =
    Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) /\
    (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 < 20 /\
    (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 < Z.of_nat (length v2) /\
    rule_type_val_match (Void) ∗
                        (nth_val'
                           (Z.to_nat
                              ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4))
                           v2) = true.
Proof.
  introv Hlen Hint Hrl  Hwf.
  Definition auxand P Q :=  P /\ Q.
  assert (auxand (Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) <= Int.unsigned x)
                 (4 * ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4) =
                  Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) /\
                  (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 < 20 /\
                  (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 <
                  Z.of_nat (length v2) /\
                  rule_type_val_match (Void) ∗
                                      (nth_val'
                                         (Z.to_nat
                                            ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4))
                                         v2) = true
                 )).
  funfold Hwf.
  unfold arrayelem_addr_right in *.
  unfold qend_right, ptr_offset_right,ptr_minus,  distance in *.
  simp join.
  fsimpl.
  inverts H5.
  unfolds in Hrl.
  destruct v'46.
  destruct e; tryfalse.
  destruct Hrl as (Hm1 & Hm2 & Hm3).
  destruct Hm3 as (Hm3 & _).
  funfold Hm1.
  funfold Hm2.
  funfold Hm3.
  unfold distance in *.
  simpl in H7, H10, H19, H21, H22.
  rewrite Int.repr_unsigned in *.
  assert ((Int.zero+ᵢ($ 4+ᵢInt.zero)) = $4).
  clear -x.
  mauto.
  rewrite H1 in *.
  clear H1.
  assert (Int.unsigned ($ 4) =4).
  clear -x.
  mauto.
  rewrite H1 in *.
  clear H1.
  splits.
  clear -H.
  int auto.
  apply eq_sym.
  eapply Z_div_exact_2; try lia.
  eapply math_prop_int_modu; eauto.
  eapply math_prop_ltu_20; eauto.
  rewrite Hlen.
  unfold OS_MAX_Q_SIZE.
  simpl.
  eapply math_prop_ltu_20; eauto.
  assert (Int.unsigned ($4) = 4). 
  clear -x.
  mauto.
  assert ( Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) >
           Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4))  \/
         Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) <
         Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4)) \/
         Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) =
           Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4))) by lia.
  lets Hes : int_nat_ltu_lt H5 Hint. 
  lets Hls : list_length_lt Hes.
  destruct Hls as (xx & ll & lt).
  subst l.
  destruct H9 as [Ha1 | [ Ha2 | Ha3]].
  apply H19 in Ha1.
  lets Has : vallist_seg_prop_eq Ha1.
  lets Heq :  math_out_start_eq'   H13; try eapply H; eauto.

  rewrite H1 in *.
    rewrite <- Heq.
  rewrite <- Has.
  simpl in H20.
  destruct H20.
  simpl.
  clear - H9.
  pauto.
  apply H21 in Ha2.
  lets Heq :  math_out_start_eq'   H13; try eapply H; eauto.
  rewrite H1 in *.
  rewrite <- Heq.
  remember (vallist_seg 0 ∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) v2) as ls.
  assert ( (∘( ( Int.unsigned m)) <= length v2)%nat).
  eapply list_maxsize_le; eauto.
  lets Hdas: vallist_seg_prop H2 H9; eauto.
  lets Hsp : list_append_split Hdas Ha2.
  simp join.
  simpl in H20.
  destruct H20.
  apply vallist_seg_prop_eq in H17.
  rewrite <- H17.
  simpl.
  clear -H7.
  pauto.
  apply H22 in Ha3.
  lets Heq :  math_out_start_eq'   H13; try eapply H; eauto.
  destruct Ha3 as [Haa | Ha3].
  simp join; tryfalse.
  destruct Ha3 as (Heqa & Ha3).
  rewrite H1 in *.
  rewrite <- Heq.
  remember (vallist_seg 0 ∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) v2) as ls.
  assert ( (∘( ( Int.unsigned m)) <= length v2)%nat).
  eapply list_maxsize_le; eauto.
  lets Hdas: vallist_seg_prop H2 H9; eauto.
  lets Hsp : list_append_split Hdas Ha3.
  simp join.
  simpl in H20.
  destruct H20.
  apply vallist_seg_prop_eq in H17.
  rewrite <- H17.
  simpl.
  clear -H7.
  pauto.
  auto.
Qed.

Require Import Lia.

Lemma h_has_same_msg: 
  forall b qptr qst qend qin outi qsize qens qblk sti l  qblkm vl hml,
    Int.ltu ($ 0) qens = true ->
    id_addrval qblk msgqueuetbl os_ucos_h.OS_Q_FREEBLK = Some (b, sti) ->
    length vl = ∘OS_MAX_Q_SIZE ->
    WellformedOSQ
      (qptr
         :: qst
         :: qend
         :: qin
         :: Vptr (b, outi)
         :: qsize :: Vint32 qens :: Vptr qblk:: nil) ->
    RLH_ECBData_P (DMsgQ l
                         (qptr
                            :: qst
                            :: qend
                            :: qin
                            :: Vptr (b, outi)
                            :: qsize :: Vint32 qens :: Vptr qblk:: nil) 
                         qblkm vl) hml -> 
    exists vl' max wml wl , hml = (absmsgq ((nth_val' (Z.to_nat ((Int.unsigned outi - Int.unsigned sti) / 4)) vl) :: vl')  max wml , wl).
Proof.
  introv Hint Hid  Hlen Hwl Hrl .
  funfold Hwl.
  rename H13 into H11;
  rename H12 into Hsize.
  unfold arrayelem_addr_right in *.
  unfold qend_right, ptr_offset_right,ptr_minus,  distance in *.
  simp join.
  fsimpl.
  simpl in *.
  destruct x5.
  apply eq_sym in Hid.
   inverts Hid.
  remember ( i2+ᵢ($ 4+ᵢInt.zero)) as k.
  inverts H5.
  destruct hml.
  destruct e; tryfalse.
  destruct Hrl as (Hm1 & Hm2 & Hm3).
  destruct Hm3 as (Hm3 & _).
  funfold Hm1.
  funfold Hm2.
  funfold Hm3.
  unfold distance in *.
  simpl in *.
  rewrite Int.repr_unsigned in *.
  lets Hes : int_nat_ltu_lt H7 Hint.
  lets Hls : list_length_lt Hes.
  destruct Hls as (xx & ll & lt).
  subst l0.
  assert ( Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) >
       Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) \/
          Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) <
          Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) \/
          Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) =
        Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) ) by lia.
  destruct H5 as [Ha1 | [Ha2 | Ha3] ].
  apply H19 in Ha1.
  lets Has : vallist_seg_prop_eq Ha1.
  lets Heq :  math_out_start_eq'  H10 H2 H11; eauto.
  rewrite <- Heq.
  subst xx.
  do 3 eexists; eauto.
  apply H21 in Ha2.
  lets Heq :  math_out_start_eq' H10 H2  H11; eauto.
  rewrite <- Heq.
  remember (vallist_seg 0 ∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) vl) as ls.
  assert ( (∘(Int.unsigned m) <= length vl)%nat).
  eapply list_maxsize_le; eauto.
  lets Hdas: vallist_seg_prop  H2 H5.
  lets Hsp : list_append_split Hdas Ha2.
  simp join.
  rewrite app_comm_cons in Ha2.
  apply app_inv_tail in Ha2.
  lets Has : vallist_seg_prop_eq Ha2.
  subst xx.
  do 3 eexists; eauto.
  apply H22 in Ha3.
  destruct Ha3.
  simp join; tryfalse.
  destruct H5.
  lets Heq :  math_out_start_eq' H10 H2  H11; eauto.
  rewrite <- Heq.
  remember (vallist_seg 0 ∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) vl) as ls.
  assert ( (∘(Int.unsigned m) <= length vl)%nat).
  eapply list_maxsize_le; eauto.
  lets Hdas: vallist_seg_prop  H2 H16.
  lets Hsp : list_append_split Hdas H9.
  simp join.
  rewrite app_comm_cons in H9.
  apply app_inv_tail in H9.
  lets Has : vallist_seg_prop_eq H9.
  subst xx.
  do 3 eexists; eauto.
Qed.

Ltac sep_lift_absdata' H :=
  match type of H with
    | _ |= ?P =>
      match find_aop P with
        | none _ =>
          idtac 1 "no absop in the pre-condition"; fail 1
        | some ?a =>
          match find_absdata P absecblsid with
            | none _ =>
              idtac 2 "no HECBList in the pre-condition";
                fail 2
            | some ?b =>
              match find_absdata P abstcblsid with
                | none _ => 
                  idtac 3 "no HTCBList in the pre-condition"; fail 3
                | some ?c =>
                  match find_absdata P ostmid with
                    | none _ =>
                      idtac 4 "no HTime in the pre-condition"; fail 4
                    | some ?e =>
                      match find_absdata P curtid with
                        | none _ =>
                          idtac 5 "no HCurTCB in the pre-condition"; fail 5
                        | some ?f =>
                          sep lifts (a::b::c::e::f::nil)  in H
                      end
                  end
              end
          end
      end
    end.

Lemma get_wellformedosq_end:
  forall x qptr st b i qin qout size  qfr, 
    Int.ltu Int.zero x = true ->  
    WellformedOSQ
      (qptr
         :: st
         :: Vptr (b, i  +ᵢ Int.mul ($ 1) ($ 4))
         :: qin :: qout :: size :: Vint32 x :: qfr :: nil) -> 
    WellformedOSQ
      (qptr
         :: st
         :: Vptr (b, i +ᵢ Int.mul ($ 1) ($ 4))
         :: qin
         :: st
         :: size
         :: Vint32 (x -ᵢ $1)
         :: qfr :: nil).
Proof.
  intros.
  unfold WellformedOSQ in *.
  simp join.
  unfold V_OSQEnd in *.
  unfold V_OSQSize in *.
  unfold V_OSQStart in *.
  unfold V_OSQOut in *.
  unfold V_qfreeblk in *.
  simpl in *.
  rename H13 into HV_OSQEntries.
  rename H14 into Hsize.
  unfold V_OSQIn in *;simpl in *.
  inverts H3.
  inverts H4.
  inverts H5.
  inverts H6.
  inverts H1.
  do 8 eexists;splits;eauto.
  splits;auto.
  unfolds.
  exists 0%nat.
  inverts H2.
  splits;try unfolds;simpl;auto.
  destruct x5.
  rewrite Pos.eqb_refl.
  rewrite Int.sub_idem.
  unfold Int.modu.
  rewrite Int.unsigned_repr.
  unfold Int.zero.
  rewrite Int.unsigned_repr.
  assert (0 mod 4 = 0).
  unfold Z.modulo.
  unfold Z.div_eucl.
  auto.
  rewrite H1.
  split.
  unfolds.
  remember (zlt (Int.unsigned i0) (Int.unsigned i0)) as X.
  destruct X;auto.
  lia.
  auto.
  rewrite max_unsigned_val.
  lia.
  rewrite max_unsigned_val.
  lia.
  destruct x5.
  rewrite Pos.eqb_refl.
  simpl.
  assert ((Int.unsigned (Int.divu (i0 -ᵢ i0) ($ 4))) = 0).
  rewrite Int.sub_idem.
  unfold Int.divu.
  unfold Int.zero.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr.
  auto.
  rewrite max_unsigned_val.
  lia.
  rewrite max_unsigned_val.
  lia.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr.
  assert (0/4 =0).
  auto.
  rewrite H1.
  rewrite max_unsigned_val.
  lia.
  rewrite max_unsigned_val.
  lia.
  rewrite max_unsigned_val.
  lia.
  destruct x6.
  rewrite H1.
  simpl.
  auto.
  clear -H7.
  remember (Int.unsigned x4) as X.
  clear -H7.
  unfold nat_of_Z.
  assert (Z.to_nat 1 = 1%nat).
  simpl; auto.
  rewrite <- H.
  eapply Z2Nat.inj_le; try lia.
  unfold os_inv.V_OSQEntries in *.
  simpl .  eauto.
  unfold os_inv.V_OSQEntries in H12.
  simpl in H12.
  inverts H12.
  clear -HV_OSQEntries H.
  int_auto.
  split;int_auto.
Qed.


(* Lemma get_wellformedosq_end:
  forall x qptr st b i qin qout size ens qfr, 
    ens = Vint32 x ->
    Int.ltu Int.zero x = true ->  
    WellformedOSQ
      (qptr
         :: st
         :: Vptr (b, i  +ᵢ Int.mul ($ 1) ($ 4))
         :: qin :: qout :: size :: ens :: qfr :: nil) -> 
    WellformedOSQ
      (qptr
         :: st
         :: Vptr (b, i +ᵢ Int.mul ($ 1) ($ 4))
         :: qin
         :: st
         :: size
         :: val_inj (memory.sub ens (Vint32 (Int.repr 1)) Tint16)
         :: qfr :: nil).
Proof.
  intros.
  unfold WellformedOSQ in *.
  simp join.
  unfold V_OSQEnd in *.
  unfold V_OSQSize in *.
  unfold V_OSQStart in *.
  unfold V_OSQOut in *.
  unfold V_qfreeblk in *.
  simpl in *.
  rename H13 into V_OSQEntries.
  rename H14 into Hsize.
  unfold V_OSQIn in *;simpl in *.
  inverts H3.
  inverts H4.
  inverts H5.
  inverts H6.
  inverts H1.
  do 8 eexists;splits;eauto.
  splits;auto.
  unfolds.
  exists 0%nat.
  inverts H2.
  splits;try unfolds;simpl;auto.
  destruct x5.
  rewrite Pos.eqb_refl.
  rewrite Int.sub_idem.
  unfold Int.modu.
  rewrite Int.unsigned_repr.
  unfold Int.zero.
  rewrite Int.unsigned_repr.
  assert (0 mod 4 = 0).
  unfold Z.modulo.
  unfold Z.div_eucl.
  auto.
  rewrite H.
  split.
  unfolds.
  remember (zlt (Int.unsigned i0) (Int.unsigned i0)) as X.
  destruct X;auto.
  lia.
  auto.
  rewrite max_unsigned_val.
  lia.
  rewrite max_unsigned_val.
  lia.
  destruct x5.
  rewrite Pos.eqb_refl.
  simpl.
  assert ((Int.unsigned (Int.divu (i0 -ᵢ i0) ($ 4))) = 0).
  rewrite Int.sub_idem.
  unfold Int.divu.
  unfold Int.zero.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr.
  auto.
  rewrite max_unsigned_val.
  lia.
  rewrite max_unsigned_val.
  lia.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr.
  assert (0/4 =0).
  auto.
  rewrite H.
  rewrite max_unsigned_val.
  lia.
  rewrite max_unsigned_val.
  lia.
  rewrite max_unsigned_val.
  lia.
  destruct x6.
  rewrite H.
  simpl.
  auto.
  clear -H8.
  remember (Int.unsigned x4) as X.
  clear -H8.
  unfold nat_of_Z.
  assert (Z.to_nat 1 = 1%nat).
  simpl; auto.
  rewrite <- H.
  eapply Z2Nat.inj_le; try lia.
  unfold os_inv.V_OSQEntries in *.
  simpl .  eauto.
  unfold os_inv.V_OSQEntries in V_OSQEntries.
  simpl in V_OSQEntries.
  inverts V_OSQEntries.
  clear -Hsize H0.
  int_auto.
  split;int_auto.
Qed.
 *)

Lemma msgqlist_p_compose:
  forall  p qid mqls qptrl1 qptrl2 i i1 a x3 p' v'41 v'100
          msgqls1 msgqls2 msgq mqls1 mqls2 mq mqls' tcbls i2 x5,
    R_ECB_ETbl_P qid
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 i :: Vint32 i1 :: Vptr a :: x3 :: p' :: nil, v'41, v'100) tcbls ->
    R_ECB_PETbl_P qid
  (V$ OS_EVENT_TYPE_Q :: Vint32 i :: Vint32 i1 :: Vptr a :: x3 :: p' :: Vint32 i2 :: x5 :: nil, v'41, v'100)
  tcbls ->
    ECBList_P p (Vptr qid) qptrl1 msgqls1 mqls1 tcbls->
    ECBList_P p' Vnull qptrl2 msgqls2 mqls2 tcbls->
    RLH_ECBData_P msgq mq ->
    EcbMod.joinsig qid mq mqls2 mqls'->
    EcbMod.join mqls1 mqls' mqls ->
    ECBList_P p Vnull (qptrl1 ++ ((V$OS_EVENT_TYPE_Q
                                    :: Vint32 i :: Vint32 i1 :: Vptr a :: x3 :: p' :: Vint32 i2 :: x5 :: nil, v'41, v'100)::nil) ++ qptrl2) (msgqls1 ++ (msgq::nil) ++msgqls2) mqls tcbls.
Proof.
  intros.
  simpl.
  eapply ecblist_p_compose; eauto.
  simpl.
  eexists; splits; eauto.
  do 3 eexists; splits; eauto.
  unfolds; simpl; auto.
Qed.

(* Lemma msgqnode_p_hold_end:
  forall b sti qens outi qend qptr qst qin qsize qblk  mblk ml hml hsize pwl wl l,
    id_addrval qblk msgqueuetbl os_ucos_h.OS_Q_FREEBLK = Some (b, sti) -> 
    Int.ltu ($ 0) qens =true ->
    qend = Vptr (b, (outi +ᵢ  Int.mul ($ 1) ($ 4))) -> 
    WellformedOSQ
      (qptr
         :: qst
         :: qend
         :: qin
         :: Vptr (b, outi)
         :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil) -> 
    RLH_ECBData_P
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: Vptr (b, outi)
                :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil)
             mblk ml)
      (absmsgq (nth_val' (Z.to_nat ((Int.unsigned outi - Int.unsigned sti) / 4)) ml
                         :: hml) hsize pwl , wl) ->
    RLH_ECBData_P 
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: qst
                :: Vint32 qsize
                :: Vint32 (qens -ᵢ $ 1) :: Vptr qblk :: nil)
             mblk ml ) (absmsgq hml hsize pwl, wl).
Proof.
  introv Hid Hint Hqend Hwl Hrl .
  funfold Hwl.
  destruct Hrl.
  destruct H0 as (Hm1 & Hm2 & Hm3 & Hecb & Hm5 & Hm6). (* change by yss *) 
  funfold H.
  funfold Hm1.
  funfold Hm2.
  unfold arrayelem_addr_right in *.
  unfold qend_right, ptr_offset_right,ptr_minus,  distance in *.
  simp join.
  fsimpl.
  simpl in *.
  destruct x5.
  apply eq_sym in H5.
  subst i.
  inverts Hid.
  remember ( i1+ᵢ($ 4+ᵢInt.zero)) as k.
  inverts H5.
  assert (Int.mul ($ 1) ($ 4) = $ 4).
  clear -i0.
  mauto.
  rewrite H5 in *.
  rewrite <- H4 in *.
  rewrite Int.repr_unsigned in *.
  assert (Int.unsigned ($ 4) = 4)%Z.
  clear -i0.
  mauto.
  rewrite H8 in *.
  clear H5 H8.
  splits.
  unfolds.
  do 7 eexists;splits; try solve [  unfolds; simpl; eauto].
  assert (Int.unsigned (Int.divu ($ 4-ᵢ$ 4) ($ 4)) = 0)%Z.
  clear.
  int auto.
  int auto.
  rewrite Zdiv_0_l.
  lia.
  simpl.
  rewrite Zdiv_0_l.
  lia.
  rewrite H5 in *.
  clear H5.
  splits.
  splits.
  introv Hlt.
  lets Hed :  math_le_xyz H1 H  H22; eauto.
  rewrite Int.repr_unsigned; eauto.    
  destruct Hed as   (Has & Hass & Hsd) .
  apply z_split in Has.
  destruct Has as [Has1 | Has2].
  lets Hef : int_ltu_eq_false Hint.
  apply H15 in Has1.
  destruct Has1.
  rewrite Hef in H5.
  destruct H5; tryfalse.
  destruct H5 as (Hs1 & Hs2).
  rewrite <- Hass in Hs2.
 
  remember ( ∘(Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)))) as N.
  remember (∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))))  as M.
   destruct H13 as (His & Hsi).
  lets Hlss : isptr_length_nth His.
  rewrite vallist_seg_Sn in Hs2.
  simpl in Hs2.
  inverts Hs2; auto.
  rewrite Int.unsigned_repr in Hsd.
  rewrite <- Hsd in Hlss.
  auto.
  clear -N.
  mauto.
  apply H14 in Has2.
  rewrite <- Hass in Has2.
  rewrite vallist_seg_Sn in Has2.
  simpl in Has2.
  inverts Has2; auto.
  rewrite Int.unsigned_repr in Hsd.
  rewrite Hsd .
   destruct H13 as (His & Hsi).
  lets Hlss : isptr_length_nth His.
  auto.
  clear -l.
  mauto.
  introv Hf.
  assert ( 0 <= Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) )%Z.
  apply Int.unsigned_range.
  false.
  lia.
  introv Hf.
  lets Hed :  math_le_xyz H1 H  H22; eauto.
  rewrite Int.repr_unsigned; auto.
  rewrite Hf in *.
  assert (0<=Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) )%Z as Has.
  apply Int.unsigned_range.
  assert (0<Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) \/
          0=Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) )%Z as Hc.
  lia.
  destruct Hc as [Hc1 | Hc2].
  apply H14 in Hc1.
  destruct Hed as (He1 & He2 & He3).
  rewrite vallist_seg_eqnil in *.
  rewrite <- He2 in Hc1.
  rewrite vallist_seg_Sn in Hc1.
  simpl in Hc1.
  inverts Hc1.
  left.
  splits; auto.
  simpl in H0.
  clear - H0.
  mauto.
  destruct H13 as (His & Hsi).
  lets Hlss : isptr_length_nth His.
  rewrite He3.
  rewrite Int.unsigned_repr.
  auto.
  clear -l.
  mauto.
  apply H15 in Hc2.
  left.
  destruct Hc2.
  destruct H5.
  inverts H8.
  destruct H5.
  destruct Hed as (He1 & He2 & He3).
  rewrite vallist_seg_eqnil in *.
  rewrite <- He2 in H8.
  rewrite vallist_seg_Sn in H8.
  simpl in H8.
  inverts H8.
  simpl in H0.
  split; auto.
  clear - H0.
  mauto.
  destruct H13 as (His & Hsi).
  lets Hlss : isptr_length_nth His.
  rewrite He3.
  rewrite Int.unsigned_repr.
  auto.
  clear -l.
  mauto.
  destruct H13.
  auto.
  unfolds.
  eexists.
  splits.
  unfolds; simpl; auto.
  eapply int_list_length_dec; auto.
  unfolds.
  eexists.
  splits; try unfolds; simpl; eauto.
  rewrite Int.repr_unsigned; auto.
  intros.
  eapply Hm3.
  introv Hf. tryfalse.
  intros.
  apply Hecb in H5.
  tryfalse.
  (* 处理新增等待发送列表相关*)
  intros.
  eapply Hm5.
  introv Hf.
  tryfalse.
  
Admitted. *)
Lemma msgqnode_p_hold_end:
  forall b sti qens outi qend qptr qst qin qsize qblk  mblk ml hml hsize wl l,
    id_addrval qblk msgqueuetbl os_ucos_h.OS_Q_FREEBLK = Some (b, sti) -> 
    Int.ltu ($ 0) qens =true ->
    qend = Vptr (b, (outi +ᵢ  Int.mul ($ 1) ($ 4))) -> 
    WellformedOSQ
      (qptr
         :: qst
         :: qend
         :: qin
         :: Vptr (b, outi)
         :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil) -> 
    RLH_ECBData_P
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: Vptr (b, outi)
                :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil)
             mblk ml)
      (absmsgq (nth_val' (Z.to_nat ((Int.unsigned outi - Int.unsigned sti) / 4)) ml
                         :: hml) hsize nil , wl) ->
    RLH_ECBData_P 
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: qst
                :: Vint32 qsize
                :: Vint32 (qens -ᵢ $ 1) :: Vptr qblk :: nil)
             mblk ml ) (absmsgq hml hsize nil, wl).
Proof.
  introv Hid Hint Hqend Hwl Hrl .
  funfold Hwl.
  destruct Hrl.
  destruct H0 as (Hm1 & Hm2 & Hm3 & Hecb & Hm5 & Hm6). (* change by yss *) 
  rename H12 into Hsize.
  rename H13 into H11.
  funfold H.
  funfold Hm1.
  funfold Hm2.
  unfold arrayelem_addr_right in *.
  unfold qend_right, ptr_offset_right,ptr_minus,  distance in *.
  simp join.
  fsimpl.
  simpl in *.
  destruct x5.
  apply eq_sym in H5.
  subst i.
  inverts Hid.
  remember ( i1+ᵢ($ 4+ᵢInt.zero)) as k.
  inverts H5.
  assert (Int.mul ($ 1) ($ 4) = $ 4).
  clear -i0.
  mauto.
  rewrite H5 in *.
  rewrite <- H4 in *.
  rewrite Int.repr_unsigned in *.
  assert (Int.unsigned ($ 4) = 4)%Z.
  clear -i0.
  mauto.
  rewrite H8 in *.
  clear H5 H8.
  splits.
  unfolds.
  do 7 eexists;splits; try solve [  unfolds; simpl; eauto].
  assert (Int.unsigned (Int.divu ($ 4-ᵢ$ 4) ($ 4)) = 0)%Z.
  clear.
  int auto.
  int auto.
  rewrite Zdiv_0_l.
  lia.
  simpl.
  rewrite Zdiv_0_l.
  lia.
  rewrite H5 in *.
  clear H5.
  splits.
  splits.
  introv Hlt.
  lets Hed :  math_le_xyz H1 H  H22; eauto.
  rewrite Int.repr_unsigned; eauto.    
  destruct Hed as   (Has & Hass & Hsd) .
  apply z_split in Has.
  destruct Has as [Has1 | Has2].
  lets Hef : int_ltu_eq_false Hint.
  apply H15 in Has1.
  destruct Has1.
  rewrite Hef in H5.
  destruct H5; tryfalse.
  destruct H5 as (Hs1 & Hs2).
  rewrite <- Hass in Hs2.
 
  remember ( ∘(Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)))) as N.
  remember (∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))))  as M.
   destruct H13 as (His & Hsi).
  lets Hlss : isptr_length_nth His.
  rewrite vallist_seg_Sn in Hs2.
  simpl in Hs2.
  inverts Hs2; auto.
  rewrite Int.unsigned_repr in Hsd.
  rewrite <- Hsd in Hlss.
  auto.
  clear -N.
  mauto.
  apply H14 in Has2.
  rewrite <- Hass in Has2.
  rewrite vallist_seg_Sn in Has2.
  simpl in Has2.
  inverts Has2; auto.
  rewrite Int.unsigned_repr in Hsd.
  rewrite Hsd .
   destruct H13 as (His & Hsi).
  lets Hlss : isptr_length_nth His.
  auto.
  clear -l.
  mauto.
  introv Hf.
  assert ( 0 <= Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) )%Z.
  apply Int.unsigned_range.
  false.
  lia.
  introv Hf.
  lets Hed :  math_le_xyz H1 H  H22; eauto.
  rewrite Int.repr_unsigned; auto.
  rewrite Hf in *.
  assert (0<=Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) )%Z as Has.
  apply Int.unsigned_range.
  assert (0<Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) \/
          0=Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) )%Z as Hc.
  lia.
  destruct Hc as [Hc1 | Hc2].
  apply H14 in Hc1.
  destruct Hed as (He1 & He2 & He3).
  rewrite vallist_seg_eqnil in *.
  rewrite <- He2 in Hc1.
  rewrite vallist_seg_Sn in Hc1.
  simpl in Hc1.
  inverts Hc1.
  left.
  splits; auto.
  simpl in H0.
  clear - H0.
  mauto.
  destruct H13 as (His & Hsi).
  lets Hlss : isptr_length_nth His.
  rewrite He3.
  rewrite Int.unsigned_repr.
  auto.
  clear -l.
  mauto.
  apply H15 in Hc2.
  left.
  destruct Hc2.
  destruct H5.
  inverts H8.
  destruct H5.
  destruct Hed as (He1 & He2 & He3).
  rewrite vallist_seg_eqnil in *.
  rewrite <- He2 in H8.
  rewrite vallist_seg_Sn in H8.
  simpl in H8.
  inverts H8.
  simpl in H0.
  split; auto.
  clear - H0.
  mauto.
  destruct H13 as (His & Hsi).
  lets Hlss : isptr_length_nth His.
  rewrite He3.
  rewrite Int.unsigned_repr.
  auto.
  clear -l.
  mauto.
  destruct H13.
  auto.
  unfolds.
  eexists.
  splits.
  unfolds; simpl; auto.
  eapply int_list_length_dec; auto.
  unfolds.
  eexists.
  splits; try unfolds; simpl; eauto.
  rewrite Int.repr_unsigned; auto.
  intros.
  eapply Hm3.
  introv Hf. tryfalse.
  intros.
  apply Hecb in H5.
  tryfalse.
  (* 处理新增等待发送列表相关*)
  intros.
  auto.
  introv Hf.
  tryfalse.
Qed.


(* Lemma msgqnode_p_hold_no_end: 
  forall b sti qens outi qend qptr qst qin qsize qblk mblk ml hml hsize wl l pwl,
    id_addrval qblk msgqueuetbl os_ucos_h.OS_Q_FREEBLK = Some (b, sti) -> 
    length ml = ∘OS_MAX_Q_SIZE ->
    WellformedOSQ
      (qptr
         :: qst
         :: qend
         :: qin
         :: Vptr (b, outi)
         :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil) -> 
    RLH_ECBData_P
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: Vptr (b, outi)
                :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil)
             mblk ml)
      (absmsgq (nth_val' (Z.to_nat ((Int.unsigned outi - Int.unsigned sti) / 4)) ml
                         :: hml) hsize pwl, wl) ->
    RLH_ECBData_P 
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: Vptr (b, outi  +ᵢ  Int.mul ($ 1) ($ 4))
                :: Vint32 qsize
                :: Vint32 (qens  -ᵢ  $ 1) :: Vptr qblk :: nil)
             mblk ml ) (absmsgq hml hsize pwl, wl).
Proof.
Admitted. *)
Lemma msgqnode_p_hold_no_end: 
  forall b sti qens outi qend qptr qst qin qsize qblk mblk ml hml hsize wl l,
    id_addrval qblk msgqueuetbl os_ucos_h.OS_Q_FREEBLK = Some (b, sti) -> 
    length ml = ∘OS_MAX_Q_SIZE ->
    WellformedOSQ
      (qptr
         :: qst
         :: qend
         :: qin
         :: Vptr (b, outi)
         :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil) -> 
    RLH_ECBData_P
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: Vptr (b, outi)
                :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil)
             mblk ml)
      (absmsgq (nth_val' (Z.to_nat ((Int.unsigned outi - Int.unsigned sti) / 4)) ml
                         :: hml) hsize nil, wl) ->
    RLH_ECBData_P 
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: Vptr (b, outi  +ᵢ  Int.mul ($ 1) ($ 4))
                :: Vint32 qsize
                :: Vint32 (qens  -ᵢ  $ 1) :: Vptr qblk :: nil)
             mblk ml ) (absmsgq hml hsize nil, wl).
Proof.
  introv Hid  Hlen Hwl Hrl .
  funfold Hwl.
  destruct Hrl.
  destruct H0 as (Hm1 & Hm2 & Hm3 & Hecb & Hm5 & Hm6).
  rename H13 into H11.
  rename H12 into Hsize.
  funfold H.
  funfold Hm1.
  funfold Hm2.
  unfold arrayelem_addr_right in *.
  unfold qend_right, ptr_offset_right,ptr_minus,  distance in *.
  simp join.
  fsimpl.
  simpl in *.
  destruct x5.
  apply eq_sym in H5.
  subst i0.
  inverts Hid.
  remember ( i2+ᵢ($ 4+ᵢInt.zero)) as k.
  inverts H5.
  assert (Int.mul ($ 1) ($ 4) = $ 4).
  clear -i.
  mauto.
  rewrite H5 in *.
  rewrite <- H4 in *.
  rewrite Int.repr_unsigned in *.
  assert (Int.unsigned ($ 4) = 4).
  clear -i.
  mauto.
  rewrite H8 in *.
  clear H5 H8.
  splits.
  unfolds.
  do 7 eexists;splits; try solve [  unfolds; simpl; eauto].
  splits.
  splits.
  introv Hlt.

  
  lets Hed :  math_xyz_prop2'  H1 H  Hlt; eauto.
  destruct Hed as   (Has & Hass & Hsd) .
  lets Hls : H12 Has.
  assert ( Int.unsigned ($ 4) = 4).
  clear -i.
  mauto.
  rewrite H5 in *.
  clear H5.
  rewrite  <- Hsd in Hls.
  rewrite <- Hass .
  eapply  vallistseg_n_m_split; eauto.
  unfold nat_of_Z.
  apply le_change.
  eapply Z2Nat.inj_le; try lia;try apply Int.unsigned_range.
  destruct H13.
  rewrite Hlen.
  unfold OS_MAX_Q_SIZE in H11.
  unfold Pos.to_nat.
  simpl.
  eapply math_le_trans; eauto.
  introv Hf.
  lets Heas :math_xyz_prop3' Hf; eauto.
  destruct Heas as (Hdisj & Hseq & He).
  assert ( Int.unsigned ($ 4) = 4).
  clear -i.
  mauto.
  rewrite H5 in *.
  clear H5.
  rewrite <- Hseq in *.
  rewrite <- He in *.
  destruct Hdisj as [Hd1 | Hd2].
  lets Hls : H14 Hd1.
  eapply vallist_seg_ltunm_prop; eauto.
  eapply list_maxsize_le; eauto.
  lets Hrs : H15 Hd2.
  destruct Hrs.
  destruct H5 as (Hf1 & Hf2).
  inverts Hf2.
  destruct H5 as (Hf1 & Hf2).
  rewrite Hd2 in *.
  eapply vallist_seg_ltunm_prop; eauto.
  eapply list_maxsize_le; eauto.
  introv Hf.
  lets Heas :math_xyz_prop4' Hf; eauto.
  destruct Heas as (Hdisj & Hseq & He).
  assert ( Int.unsigned ($ 4) = 4).
  clear -i.
  mauto.
  rewrite H5 in *.
  clear H5.
  rewrite Hf.
  rewrite <- Hseq in *.
  rewrite <- He in *.
  lets Hres : H12 Hdisj.
  rewrite Hf in Hres.
  rewrite <- Hseq in Hres.
  rewrite vallist_seg_Sn in Hres.
  inverts Hres.
  left.
  simpl in H0.
  splits; auto.
  clear - H0.
  mauto.
  rewrite Hseq.
  rewrite <- Hf.
  rewrite Hlen.
  unfold OS_MAX_Q_SIZE in H11.
  unfold Pos.to_nat.
  simpl.
  eapply  math_le_trans; eauto.
  destruct H13; auto.
  unfolds.
  eexists.
  splits.
  unfolds; simpl;  eauto.
  eapply int_list_length_dec; auto.
  unfolds.
  eexists.
  splits; try unfolds; simpl; eauto.
  rewrite Int.repr_unsigned; auto.
  intros.
  eapply Hm3.
  introv Hf; tryfalse.
  intros.
  apply Hecb in H5.
  tryfalse.
  intro. auto.
  intro. tryfalse.
Qed.

Lemma get_wellformedosq_end':
  forall x qptr st b i qin size  qfr qend, 
        Int.ltu Int.zero x = true ->  
    qend <> Vptr (b, i +ᵢ Int.mul ($ 1) ($ 4)) ->
    WellformedOSQ
      (qptr
         :: st
         :: qend
         :: qin :: Vptr (b, i) :: size :: Vint32 x :: qfr :: nil) -> 
    WellformedOSQ
      (qptr
         :: st
         :: qend
         :: qin
         :: Vptr (b, i +ᵢ Int.mul ($ 1) ($ 4))
         :: size
         :: Vint32 (x -ᵢ $1)
         :: qfr :: nil).
Proof.  
  introv Hltu Hq.
  intros.
  funfold H.
  unfold WellformedOSQ in *.  
  rename H12 into Hsize.
  rename H13 into H11.
  do 8 eexists;splits;eauto;try  unfolds; simpl; eauto.
  splits;auto.
  unfolds.
  unfold qend_right in *.
  unfold arrayelem_addr_right  in *.
  destruct H9.
  destruct H10.
  unfold ptr_offset_right in *.
  unfold ptr_minus in *.
  destruct x1.
  destruct x2.
  destruct x5.
  destruct x6.
  simpl in H5.
  inverts H5.
  remember ((b =? b2)%positive ) as Hbool.
  destruct Hbool; simp join; tryfalse.
  rewrite Pos2Z.inj_eqb in HeqHbool.
  apply eq_sym in HeqHbool.
  apply Z.eqb_eq in HeqHbool.
  inverts HeqHbool.
  remember ((b1 =? b2)%positive ) as Hbool.
  destruct Hbool; simp join; tryfalse.
  rewrite Pos2Z.inj_eqb in HeqHbool.
  apply eq_sym in HeqHbool.
  apply Z.eqb_eq in HeqHbool.
  inverts HeqHbool.
   remember ((b0 =? b2)%positive ) as Hbool.
  destruct Hbool; simp join; tryfalse.
  rewrite Pos2Z.inj_eqb in HeqHbool.
  apply eq_sym in HeqHbool.
  apply Z.eqb_eq in HeqHbool.
  inverts HeqHbool.
  simpl in *.
  rewrite H7 in *.
  clear H7.
  assert (Int.mul ($ 1) ($ 4) = $ 4 ).
  clear - i.
  int auto.
  rewrite H7 in *.
  exists ( ∘(Int.unsigned (Int.divu ((i+ᵢ$ 4)-ᵢ$ 4) ($ 4)))).
  invertsall.
  assert (i0 <> i+ᵢ$ 4).
  intro Hf.
  apply Hq.
  subst .
  auto.
  lets (Hrs1 & Hrs2 & Hrs3) : math_lt_mod_lt   H0  H3 H1 H11; eauto.
  splits;eauto.
  rewrite H4; auto.
  unfold V_OSQEntries; simpl; eauto.
  clear -Hltu Hsize.
  int_auto. split; int_auto.
Qed.


(* Lemma get_wellformedosq_end':
  forall x qptr st b i qin size ens qfr qend, 
    ens = Vint32 x ->
        Int.ltu Int.zero x = true ->  
    qend <> Vptr (b, i +ᵢ Int.mul ($ 1) ($ 4)) ->
    WellformedOSQ
      (qptr
         :: st
         :: qend
         :: qin :: Vptr (b, i) :: size :: ens :: qfr :: nil) -> 
    WellformedOSQ
      (qptr
         :: st
         :: qend
         :: qin
         :: Vptr (b, i +ᵢ Int.mul ($ 1) ($ 4))
         :: size
         :: val_inj (memory.sub ens (Vint32 (Int.repr 1)) Tint16)
         :: qfr :: nil).
Proof.  
  introv Hens Hltu Hq.
  intros.
  funfold H.
  unfold WellformedOSQ in *.  
  rename H12 into Hsize.
  rename H13 into H11.
  do 8 eexists;splits;eauto;try  unfolds; simpl; eauto.
  splits;auto.
  unfolds.
  unfold qend_right in *.
  unfold arrayelem_addr_right  in *.
  destruct H9.
  destruct H10.
  unfold ptr_offset_right in *.
  unfold ptr_minus in *.
  destruct x1.
  destruct x2.
  destruct x5.
  destruct x6.
  simpl in H5.
  inverts H5.
  remember ((b =? b2)%positive ) as Hbool.
  destruct Hbool; simp join; tryfalse.
  rewrite Pos2Z.inj_eqb in HeqHbool.
  apply eq_sym in HeqHbool.
  apply Z.eqb_eq in HeqHbool.
  inverts HeqHbool.
  remember ((b1 =? b2)%positive ) as Hbool.
  destruct Hbool; simp join; tryfalse.
  rewrite Pos2Z.inj_eqb in HeqHbool.
  apply eq_sym in HeqHbool.
  apply Z.eqb_eq in HeqHbool.
  inverts HeqHbool.
   remember ((b0 =? b2)%positive ) as Hbool.
  destruct Hbool; simp join; tryfalse.
  rewrite Pos2Z.inj_eqb in HeqHbool.
  apply eq_sym in HeqHbool.
  apply Z.eqb_eq in HeqHbool.
  inverts HeqHbool.
  simpl in *.
  rewrite H7 in *.
  clear H7.
  assert (Int.mul ($ 1) ($ 4) = $ 4 ).
  clear - i.
  int auto.
  rewrite H7 in *.
  exists ( ∘(Int.unsigned (Int.divu ((i+ᵢ$ 4)-ᵢ$ 4) ($ 4)))).
  invertsall.
  assert (i0 <> i+ᵢ$ 4).
  intro Hf.
  apply Hq.
  subst .
  auto.
  lets (Hrs1 & Hrs2 & Hrs3) : math_lt_mod_lt   H0  H3 H1 H11; eauto.
  splits;eauto.
  rewrite H4; auto.
  unfold V_OSQEntries; simpl; eauto.
  clear -Hltu Hsize.
  int_auto. split; int_auto.
Qed. *)


Lemma rh_tcbls_mqls_p_getmsg_hold:
  forall mqls tcbls ct a v vl qmax pwl wl,
    RH_TCBList_ECBList_P mqls tcbls ct ->
    (* EcbMod. *)get mqls a =
    Some
      (absmsgq (v:: vl) qmax pwl, wl) -> 
    RH_TCBList_ECBList_P ((* EcbMod. *)set mqls a (absmsgq vl qmax pwl, wl)) tcbls ct.
Proof.
  intros.
  unfold RH_TCBList_ECBList_P in *.
  destruct H as (Hr1 & Hr2 & Hr3 & Hr4 & Hr5).
  splits.
  destruct Hr1 as (Hrr1 & Hrr2 & Hrr3 & Hrr4).
  splits; intros.
(* add by yss*)
(* 解决exists prio m n,
get tcbls tid = Some (prio, wait (os_stat_q eid) n, m)*)
  destruct (tidspec.beq a eid) eqn : eq1.
  unfold get in *; simpl in *.
  lets Hts :  tidspec.beq_true_eq  eq1 .
  substs.
  rewrite EcbMod.set_a_get_a in H; auto.
  destruct H; inverts H; eauto.
  rewrite EcbMod.set_a_get_a' in H; auto.
  eapply Hrr1; eauto.
(* 解决exists prio m n,
get tcbls tid = Some (prio, wait (os_stat_postq eid) n, m)*)
  destruct (tidspec.beq a eid) eqn : eq1.
  unfold get in *; simpl in *.
  lets Hts :  tidspec.beq_true_eq  eq1 .
  substs.
  rewrite EcbMod.set_a_get_a in H; auto.
  destruct H; inverts H; eauto.
  rewrite EcbMod.set_a_get_a' in H; auto.
  eapply Hrr2; eauto.
(*解决 exists x y pqwaitset qwaitset,
get (EcbMod.set mqls a (absmsgq vl qmax pwl, wl)) eid =
Some (absmsgq x y pqwaitset, qwaitset) /\ In tid qwaitset*)
  destruct (tidspec.beq a eid) eqn : eq1.
  lets Hts :  tidspec.beq_true_eq  eq1 .
  substs.
  rewrite EcbMod.set_a_get_a; auto.
  apply Hrr3 in H; auto.
  do 5 destruct H.
  unfold get in *; simpl in *.
  rewrite H in H0; inverts H0.
  repeat tri_exists_and_solver1.
  rewrite EcbMod.set_a_get_a'; auto.
  eapply Hrr3; eauto.
(*解决 exists x y pqwaitset qwaitset,
get (EcbMod.set mqls a (absmsgq vl qmax pwl, wl)) eid =
Some (absmsgq x y pqwaitset, qwaitset) /\ In tid qwaitset*)
  destruct (tidspec.beq a eid) eqn : eq1.
  lets Hts :  tidspec.beq_true_eq  eq1 .
  substs.
  rewrite EcbMod.set_a_get_a; auto.
  apply Hrr4 in H; auto.
  do 5 destruct H.
  unfold get in *; simpl in *.
  rewrite H in H0; inverts H0.
  repeat tri_exists_and_solver1.
  rewrite EcbMod.set_a_get_a'; auto.
  eapply Hrr4; eauto.
  
  destruct Hr2.
  splits; intros.
  destruct (tidspec.beq a eid) eqn : eq1.
    lets Hts :  tidspec.beq_true_eq  eq1; substs.
  rewrite EcbMod.set_a_get_a in H2; auto.
  destruct H2; inverts H2; eauto.
  rewrite EcbMod.set_a_get_a' in H2; auto.
  eapply H; eauto.
  destruct (tidspec.beq a eid) eqn : eq1.
    lets Hts :  tidspec.beq_true_eq  eq1 ; subst.
  rewrite EcbMod.set_a_get_a; auto.
  apply H1 in H2; auto.
  do 3 destruct H2.
  unfold get in *; simpl in *.
  rewrite H2 in H0; inverts H0.
  eauto.
  rewrite EcbMod.set_a_get_a'; auto.
  eapply H1; eauto.
  
  destruct Hr3.
  splits; intros.
  destruct (tidspec.beq a eid) eqn : eq1.
  lets Hts :  tidspec.beq_true_eq  eq1; substs.
  rewrite EcbMod.set_a_get_a in H2; auto.
  destruct H2; inverts H2; eauto.
  rewrite EcbMod.set_a_get_a' in H2; auto.
  eapply H; eauto.
  destruct (tidspec.beq a eid) eqn : eq1.
      lets Hts :  tidspec.beq_true_eq  eq1; substs.
  rewrite EcbMod.set_a_get_a; auto.
  apply H1 in H2; auto.
  do 3 destruct H2.
  unfold get in *; simpl in *.
rewrite H2 in H0; inverts H0.
  eauto.
  rewrite EcbMod.set_a_get_a'; auto.
  eapply H1; eauto.
  destruct Hr4.
  splits; intros.
  destruct (tidspec.beq a eid) eqn : eq1.
  lets Hts :  tidspec.beq_true_eq  eq1; substs.
  rewrite EcbMod.set_a_get_a in H2; auto.
  destruct H2; inverts H2; eauto.
  rewrite EcbMod.set_a_get_a' in H2; auto.
  eapply H; eauto.
  destruct (tidspec.beq a eid) eqn : eq1.
  lets Hts :  tidspec.beq_true_eq  eq1; substs.
  rewrite EcbMod.set_a_get_a; auto.
  apply H1 in H2; auto.
  do 4 destruct H2.
  unfold get in *; simpl in *.
  rewrite H2 in H0; inverts H0.
  eauto.
  rewrite EcbMod.set_a_get_a'; auto.
  eapply H1; eauto.

  
  elim H1; intros.
  unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
  intros.

  assert (eid = a \/ eid <> a) by tauto.
  destruct H5; intros.
  subst eid.
  rewrite EcbMod.set_a_get_a in H4.
  inversion H4.
  apply CltEnvMod.beq_refl.
  rewrite EcbMod.set_a_get_a' in H4.
  eapply H3; eauto.
  apply tidspec.neq_beq_false; auto.
  
  
  simpljoin1.
  clear -H3.
  unfold RH_TCBList_ECBList_MUTEX_OWNER_P in *.
  simpljoin1.
  splits.
  intros.
  assert(eid = a \/ eid <> a) by tauto.
  destruct H3. inverts H3.
  rewrite EcbMod.set_a_get_a in H2.
  tryfalse.
  eapply TcbMod.beq_refl.
  rewrite EcbMod.set_a_get_a' in H2.
  eapply H in H2;auto.
  apply tidspec.neq_beq_false; auto.
  intros.
  assert(eid = a \/ eid <> a) by tauto.
  destruct H6. inverts H6.
  rewrite EcbMod.set_a_get_a in H2.
  tryfalse.
  eapply TcbMod.beq_refl.
  rewrite EcbMod.set_a_get_a' in H2.
  eapply H0 in H2;eauto.
  apply tidspec.neq_beq_false; auto.
  intros.
  
  assert(eid1 = a \/ eid1 <> a) by tauto.
  destruct H5. subst eid1.
  rewrite EcbMod.set_a_get_a in H2. 2:   eapply TcbMod.beq_refl.
  tryfalse.
  assert(eid2 = a \/ eid2 <> a) by tauto.
  destruct H6. subst eid2.
  rewrite EcbMod.set_a_get_a in H3. 2:   eapply TcbMod.beq_refl.
  tryfalse.
  rewrite EcbMod.set_a_get_a' in H2.
  rewrite EcbMod.set_a_get_a' in H3.
  lets : H1 H2 H3 H4. auto.
  apply tidspec.neq_beq_false; auto.
  apply tidspec.neq_beq_false; auto.
  
  destruct Hr5.
  splits; intros.
  destruct (tidspec.beq a eid) eqn : eq1.
    lets Hts :  tidspec.beq_true_eq  eq1; substs.
  rewrite EcbMod.set_a_get_a in H2; auto.
  destruct H2; inverts H2; eauto.
  rewrite EcbMod.set_a_get_a' in H2; auto.
  eapply H; eauto.
  destruct (tidspec.beq a eid) eqn : eq1.
    lets Hts :  tidspec.beq_true_eq  eq1 ; subst.
  rewrite EcbMod.set_a_get_a; auto.
  apply H1 in H2; auto.
  do 2 destruct H2.
  unfold get in *; simpl in *.
  rewrite H2 in H0; inverts H0.
  eauto.
  rewrite EcbMod.set_a_get_a'; auto.
  eapply H1; eauto.
Qed.

Open Scope int_scope.
Lemma msgqnode_p_nomsg:
  forall qptr qst qend qin qout size qens qblk mblk ml A l ,
    Int.ltu ($ 0) qens = false ->
    RLH_ECBData_P
      ( 
        DMsgQ l (qptr
                   :: qst
                   :: qend
                   :: qin
                   :: qout
                   :: Vint32 size :: Vint32 qens :: Vptr qblk :: nil)
              mblk ml) A ->
    exists qmax pwl wl, A = (absmsgq nil qmax pwl,wl).
Proof.
  intros.
  unfolds in H0.
  destruct A.
  destruct e; tryfalse.
  simp join.
  funfold H0.
  funfold H1.
  funfold H2.
  lets Heq : int_ltu_false_eq0 H.
  rewrite Heq in H1.
  apply eq_sym in H1.
  apply zof_nat_eq_zero_zero in H1.
  apply length_zero_nil in H1.
  subst l0.
  eauto.
Qed.

Require Import hoare_forward_tac_ext.
Local Open Scope code_scope.

Lemma OSQAccept_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSQAccept
                  vl logicl OSQAcceptPre ct->
      Some r =
      BuildRetI os_internal OSQAccept vl logicl OSQAcceptPost ct->
      exists t d1 d2 s,
        os_internal OSQAccept = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  simpl in H0.
  inverts H0.
  rename v'4 into er.
  rename v'3 into x.
  rename v'2 into opv.
  change ((x :: nil) ++ opv :: nil) with (x :: opv :: nil).
(*   subst. (* add about logicl *) *)
 (* L1 - L2 *)
  (* qacc (Vnull :: opv :: nil)  *)

  hoare forward prim.

  (* semacc (Vnull :: Vint32 Int.zero :: nil) *)
  hoare unfold.
(*   rename v'26 into ebls. *)
  hoare forward; pauto.
  hoare_split_pure_all.

  assert (Hopv: opv = Vnull \/ opv <> Vnull) by tauto.
  destruct Hopv. 
  subst.

(*   subst. *)
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  
(*   eapply absinfer_seq1. can_change_aop_solver. *)
  eapply qacc_absimp_null.
  pure_auto.
  auto.
  can_change_aop_solver.
  hoare forward prim.
  sep pauto. auto.
  pure_auto; int auto.
  hoare forward.

  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  
(*   eapply absinfer_seq1. can_change_aop_solver. *)
  eapply qacc_absimp_null_abt.
  pure_auto.
  auto.
  can_change_aop_solver.
  eapply absabort_rule.

  eapply backward_rule1.
  intros.
  destruct H.
  sep split in H.
  tryfalse.
  eauto.
  hoare_split_pure_all.
  rename v'18 into vcspace.
  rename v'19 into v19. 
  rename v'20 into v20. 
  rename v'21 into v21. 

  assert(x <> Vnull).
  { 
    pure_auto.
    rewrite H3 in H.
    unfold val_eq in H.
    unfold val_inj in H.
    destruct H; tryfalse.
  }

  rename v'10 into ecbls. 
  destruct x; destruct H1; tryfalse. destruct H1. tryfalse. destruct H1. tryfalse.
  destruct H1.
  assert (Hcases: get ecbls a = None \/ exists d, get ecbls a = Some d).
  {
    destruct (get ecbls a).
    right. eexists; eauto.
    left; eauto.
  }
  inversion Hcases as [H_ecbls_qid | H_ecbls_qid].
  {
    hoare unfold.
    unfold EvtInv.
    hoare normal pre.
    hoare_ex_intro.
    hoare_split_pure_all.
    subst. (* addr of placeholder is now vhold_addr *)

    hoare_lifts_trms_pre (tcbllsegevaux, AOSTCBList, p_local).
    eapply backward_rule1. 
    introv Hsat. 
    eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
    hoare normal pre.
    hoare_ex_intro.
    hoare_split_pure_all.
    subst.

  unfold p_local at 2. 
  unfold OSLInv at 3.
  unfold LINV.
  hoare_split_pure_all.
  inverts H4. inverts H17. (* logiv_val ... :: ... = logic_val ... :: ... *) 
  rename v'35 into ptrmp. 
  assert (Hevptr: get ptrmp ct = Some (Vnull, Vnull, Vptr x)).
  {
    (* clear -H6 H8 Hcteq. *) 
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
     join auto.
  }
  rename v'34 into locmp.
  assert (Hevloc: get locmp ct = Some (V$ os_code_defs.__EvLoc_normal)). 
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  rename ecbls into els.
  rename v'10 into fecbh.
  rename v'18 into fecbvl.
  rename v'29 into semeibs.
  rename v'30 into muxeibs.
  rename v'31 into mqeibs.
  assert (Hevt: is_evt els x \/ ptr_in_ecblist (Vptr x) fecbh fecbvl).  
  { eapply mq_ecb_nml; eauto. }

  destruct Hevt as [Hevt | Hfree].
  {
     unfold is_evt in Hevt.
     destruct Hevt.
     unfold is_sem in H4.
     simpljoin1. unfold get in *. unfold EcbMap in *. rewrite H4 in H_ecbls_qid.
     tryfalse.
     destruct H4.
     unfold is_mux in H4.
     simpljoin1. unfold get in *. unfold EcbMap in *. rewrite H4 in H_ecbls_qid.
     tryfalse.
     unfold is_que in H4.
     simpljoin1. unfold get in *. unfold EcbMap in *. rewrite H4 in H_ecbls_qid.
     tryfalse.
  }
    (* pevent points into list of free ECBs *)
  hoare_assert_pure (exists p, fecbh = Vptr p).
  {
    unfold ptr_in_ecblist in Hfree.
    lets Hptr: ptr_in_ecbsllseg_ptr Hfree.
    eauto.
  }
  hoare_split_pure_all.
  subst. 
  eapply backward_rule1.
  introv Hsat.
  unfold AOSEventFreeList in Hsat.
  unfold ecbf_sll in Hsat.
  sep normal in Hsat.
  sep_lifts_trms_in Hsat ecbf_sllseg.
  eapply ecbf_sllseg_split3_frm; eauto.
  hoare unfold.
  Set Printing Depth 99.
  lzh_hoare_if. 
  2: {
    change (Int.eq ($ OS_EVENT_TYPE_UNUSED) ($ OS_EVENT_TYPE_Q)) with false in Hif_false. 
    inverts Hif_false.
  }
  unfold AECBList.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Astruct, evsllseg).

  rename H_ecbls_qid into Hnone.
  
  casetac opv (Vnull) Hopveq Hopvne.
  2: {
    hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid). 
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply qacc_absimp_no_q_abt; eauto.
    go. unfold CurTid. go.
    introv Hex. destruct Hex as (n& n1 & n2 & wls & Hmq).
    unfold get, EcbMap in Hnone.
    unfold get in Hmq. unfold EcbMap in Hmq.
    rewrite Hnone in Hmq. tryfalse.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qacc_absimp_no_q; eauto.
  go. unfold CurTid. go.
  introv Hex.
  destruct Hex as (n& n1 & n2 & wls & Hmq).
  unfold get, EcbMap in Hnone.
  unfold get in Hmq. unfold EcbMap in Hmq.
  rewrite Hnone in Hmq. tryfalse.
  eapply absinfer_eq.

  (* EXIT_CRITICAL *) 
  hoare forward prim. 
  sep cancel Aier.
  unfold EvtInv.
  unfold AECBList.
  sep pauto.
  sep cancel evsllseg.
  unfold p_local. sep normal. sep cancel CurTid.
  unfold LINV, OSLInv.
  sep pauto.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  trycancel_EvtInv.
  instantiate (2:=(v'10 ++
        (V$ OS_EVENT_TYPE_UNUSED
         :: Vint32 i0
            :: Vint32 i2
               :: x1 :: x2 :: v'34 :: Vint32 i :: x5 :: nil)
        :: v'29)).
  instantiate (2:=Vptr v'4).
  unfold AOSEventFreeList.
  sep normal.
  sep cancel OSEventFreeList.
  unfold ecbf_sll.
  sep_lifts_trms ecbf_sllseg. 
  eapply ecbf_sllseg_compose3_frm; eauto. 
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel Aarray.
  sep cancel ecbf_sllseg.
  sep cancel ecbf_sllseg.
  unfold tcbllsegevaux.
  eapply llsegevaux_merge2_frm; eauto.
  sep cancel llsegevaux.
  eapply llsegevaux_merge_hd; eauto.
  go. go. 
  splits; eauto.
  auto.  auto.  auto. auto. auto. go.
  (* return 0 *) 
  hoare forward.
  eauto.
  }

  destruct H_ecbls_qid as (d & Hget).
  destruct d as [e w].
  unfold EvtInv.
  unfold AECBList.
  hoare normal pre. 
  hoare unfold.
  lets Hectr: ECBList_P_get_ectr_some H4; eauto.
  destruct Hectr as (et & etbl & Hgetectr).
  destruct et as (et & petbl).
  hoare lift 2%nat pre. 
  eapply backward_rule1. 
  intros. 
  eapply get_ectr_decompose; eauto. 

  hoare unfold.
  eapply backward_rule1.
  intros.
  match goal with
  | H: _ |= ?P |- _ => instantiate (1:=[| length v'37 = length v'39 |]** P)
  end.  
  sep lift 5%nat in H1.
  assert (H1' := H1).
  eapply evsllseg_aux in H1.
  destruct H1. 
  sep pauto. 
  eapply pure_split_rule'; intro Heqlen.
  assert (H4' := H4). 
  eapply ecblist_p_decompose in H4'; eauto. 
  destruct H4' as (els1 & els2 & x & H'').
  destruct H'' as (Hecbl1 & Hecbl2 & Hjo).

  rename x2 into x4.
  rename x1 into x3.
  change (((Vint32 i1
              :: Vint32 i0 :: Vint32 i2 :: x3 :: x4 :: v'13 :: Vint32 i :: x5 :: nil,
             petbl, etbl) :: nil) ++ v'38) with 
                  ((Vint32 i1 :: Vint32 i0 :: Vint32 i12 :: x3 :: x4 :: v'13 :: nil,
             etbl) :: v'38).
  unfold ECBList_P in Hecbl2.
  fold ECBList_P in Hecbl2.
  destruct Hecbl2 as (qid & Hx & Hecbetbl & Hecbpetbl & Hmt).
  change ((v'41 :: nil) ++ v'40) with (v'41 :: v'40) in Hmt.
  simpl in Hmt.
  destruct Hmt as (absev & els' & v'' & H').
  destruct H' as (Helptr & Hjo' & Hrlh & Hecbl2). 
  unfold V_OSEventListPtr in Helptr.
  simpl in Helptr.
  inverts Helptr. 
  eapply backward_rule1. intros.
  assert (H1' := H1).
   match goal with
    H: _ |= ?P |- _ => instantiate (1:=[| x = (Vptr (v'46, Int.zero)) |] ** P)
  end.
  sep lift 5%nat in H1.
  eapply ecblistp_evsllseg_tlsame with (tl:=x) in H1.
  sep pauto. clear H1 H1'. eauto.
  eapply pure_split_rule'; intro Hxeq.
  rewrite Hxeq in Hx. inverts Hx.
  subst x.

  assert (Habsev: get ecbls (v'46, Int.zero) = Some absev).
  {
    assert (Hpre: join (sig (v'46, Int.zero) absev) els' els2) by join auto. 
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

  lzh_hoare_if2.
  transform_pre qacc_eventtype_neq_q ltac:(sep cancel AEventData).
  hoare_split_pure_all.

 assert (Hres: opv <> Vnull
                \/ opv = Vnull) by tauto.
  inversion Hres as [Hres_case | Hres_case]. 
  (* opt <> ... *)
  hoare_lifts_trms_pre (Aop, absecblsid).
  eapply abscsq_rule.
  pure_auto.
  eapply qacc_absimp_no_q_abt; eauto.
  can_change_aop_solver. 
  unfold not.
  intros.
  do 4 destruct H16.
  unfold get in H16,Habsev.
  unfold EcbMap in H16,Habsev.
  rewrite H16 in Habsev.
  assert ((absmsgq x x0 x1, x2) =  (e, w)).  inverts Habsev. auto.
  rewrite <- H33 in H6.
  unfold not in H6.
  apply H6.
  exists x x0 x1 x2. auto.
  eapply absinfer_eq. 
  eapply absabort_rule.
  (* v'1 = ... *)
  hoare_lifts_trms_pre (Aop, absecblsid).
  eapply abscsq_rule. 
  pure_auto. 
  eapply qacc_absimp_no_q; eauto.
  can_change_aop_solver. 
  unfold not.
  intros.
  do 4 destruct H16.
  unfold get in H16,Habsev.
  unfold EcbMap in H16,Habsev.
  rewrite H16 in Habsev.
  assert ((absmsgq x x0 x1, x2) =  (e, w)).  inverts Habsev. auto.
  rewrite <- H33 in H6.
  unfold not in H6.
  apply H6.
  exists x x0 x1 x2. auto.
  eapply absinfer_eq. 

  (*********  exit critical ***********)
  fold_AEventNode_r. 
  compose_evsllseg. 
  fold_AECBList. 
  
  hoare forward prim.
  unfold EvtInv.
  sep pauto.
  trycancel_EvtInv.
  sep cancel p_local.
  sep cancel Aier.
  eauto.
  pauto. auto. auto. auto. pauto.
  hoare forward. 
  auto.

  (*get the pointer of OSEVENT -------------- L11 *)
  pure intro. 
  hoare forward.
  simpl;split;pauto.

  (*check if has message ------------------ L12 *)
  eapply semacc_int_eq_true in H1.
  subst i1.
  unfold AEventData.
  destruct v'41.

  2:{
  hoare_split_pure_all.
  unfolds in H1;simpl in H1.
  inverts H1.
  }
  2:{
  hoare_split_pure_all.
  unfolds in H1;simpl in H1.
  inverts H1.
  }

  2:{
  hoare lift 5%nat pre.
  apply backward_rule1 with Afalse.
  intros.
  sep split in H1.
  clear - H6.
  unfolds in H6.
  simpl in H6.
  inverts H6.

  apply pfalse_rule.

  }
  
  (* new add port*)
  2:{
  hoare_split_pure_all.
  unfolds in H1;simpl in H1.
  inverts H1.
  }

  unfold AMsgData.
  unfold AOSQCtr.
  unfold AOSQBlk.
  hoare unfold.
  
  simpl in H1.
  inverts H1.

  assert (exists i', x6 = Vptr (v'22, i')).
  eapply osq_same_blk_st_out';eauto.
  simpljoin1.
  
  hoare forward.
  simpl;splits;pauto.
  destruct (Int.ltu ($ 0) i1);simpl;auto.

  (* get message ------------------------ L13*)
  pure intro.
  clear H16 H33.
  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_part2; eauto.
  trycancel_EvtInv.
  sep pauto.

  hoare lift 4%nat pre.
  remember ( Int.ltu ($ 0) i1 ) as Hbo.
  destruct Hbo;simpl in H1; tryfalse.
  apply eq_sym in HeqHbo.
  lets Hx: wellq_props HeqHbo Hrlh H6 ;eauto.
  simpljoin1.
  hoare forward;auto.
  simpl;splits;pauto.

  hoare forward; pauto.

  (* decrease the number of entrys ---------L14*)
  hoare forward;pauto.
  hoare unfold.

  (* check if needs to reset OSQOut -------------- L15 ~ L16 *)
  lets Hx: h_has_same_msg Hrlh;eauto.
  simpl;auto.
  destruct Hx as (vl' & max & vml & wl & Hx).
  rewrite Hx in *.

  assert(vml <> nil \/ vml = nil) by tauto.
  destruct H47 as [Hpwl | Hpwl].
  hoare_lifts_trms_pre (Aop, absecblsid).
  eapply abscsq_rule. 
  pure_auto. 
  eapply qacc_absimp_pwl_is_nil_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq. 
  eapply absabort_rule.
  
  hoare_lifts_trms_pre (Aop, absecblsid).
  eapply abscsq_rule. 
  pure_auto. 
  eapply qacc_absimp_pwl_is_nil; eauto.
  can_change_aop_solver.
  eapply absinfer_eq. 
  
  assert (Hcase: opv = nth_val'
               (Z.to_nat
                  ((Int.unsigned x3 -
                    Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4)) v2 \/ 
                opv <> nth_val'
               (Z.to_nat
                  ((Int.unsigned x3 -
                    Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4)) v2
    ). tauto.
  destruct Hcase as [H_msg | H_msg].
  2:{
  eapply abscsq_rule. 
  pure_auto. 
  eapply qacc_absimp_succ_abt''; eauto.
  can_change_aop_solver.
  eapply absinfer_eq. 
  eapply absabort_rule.
  }  

  eapply forward_rule2.
  eapply abscsq_rule''.
  apply noabs_oslinv.

(*   Focus 2. *)
  2:{
  hoare forward.
  simpl;splits;pauto.

  simpl;splits;pauto.

  clear -H39.
  unfold isptr in H39.
  destruct H39.
  subst;simpl;auto.
  destruct H.
  subst x1.
  destruct x.
  pauto.

  hoare_lifts_trms_pre (Aop, absecblsid, EvtInv_part2).
  hoare forward.
  simpl;splits;pauto.
   }
  eapply absinfer_disj.
  eapply absinfer_conseq_pre.
  2:{

  intros.
   sep_lift_absdata' H47. 
  sep lifts (1::2::8::nil)%nat in H47. 
  exact H47. 
  }

  eapply qacc_absimp_succ'; pauto. 


  eapply absinfer_conseq_pre.
  2:{
     intros.
     sep_lift_absdata' H47.
     sep lifts (1::2::10::nil)%nat in H47.
     exact H47.
  }

  eapply qacc_absimp_succ'; pauto. 
  intros. destruct H47.

  sep remember (8::10::11::12::13::14::nil)%nat in H47.
  unfold AOSEventTbl in H47.

  assert (s|= AEventNode (Vptr (v'46, Int.zero)) 
             (V$OS_EVENT_TYPE_Q :: Vint32 i0 :: Vint32 i2 :: Vptr (v'41,Int.zero) :: x4 :: v'' :: Vint32 i :: x5 :: nil)
              petbl etbl
             (DMsgQ (Vptr (v'41,Int.zero)) 
                    (x11
                       :: x10
                       :: x1
                       :: x2
                       :: x10
                       :: Vint32 i3
                       :: Vint32 (i1-ᵢ$ 1) :: Vptr (v'22, Int.zero) :: nil)
                   (x :: x0 :: nil) v2) ** H48).
  unfold_msg.
  subst H48.
  sep semiauto;eauto.

  unfold AEventData.
  unfold AMsgData.
  unfold AOSQCtr.
  unfold AOSQBlk.
  unfold node.
  sep auto.

  unfold V_qfreeblk;simpl;auto.

  assert (x1=Vptr (v'22,(x3 +ᵢ Int.mul ($ 1) ($ 4)))). 
  clear -H57 H39.
  unfold isptr in*.
  destruct H39.
  subst x1.
  unfold val_inj in H57;tryfalse.
  destruct H;subst x1.
  destruct x.
  destruct (peq v'22 b);tryfalse.
  subst b.
  remember ( Int.eq (x3 +ᵢ Int.mul ($ 1) ($ 4)) i) as X.
  destruct X;unfold val_inj in H57;tryfalse.
  symmetry in HeqX.
  lets H100: Int.eq_spec (x3  +ᵢ Int.mul ($ 1) ($ 4)) i.
  rewrite HeqX in H100.
  subst i;auto.
  unfold val_inj in H57;tryfalse.
  subst x1.
  eapply get_wellformedosq_end with (x:=i1);eauto.
 
  simpl;splits;pauto.
  simpl;auto.
  simpl;splits;pauto.
  simpl;auto.
  simpl;splits;pauto.

  subst H48.
  remember H47 as H388.
  clear HeqH388 H47.
  remember H388 as H47.
  clear HeqH47 H388.
  sep_lifts_trms_in H49 (AEventNode, (evsllseg v'36), (evsllseg v'')).
  eapply evsllseg_compose in H49;eauto.
  clear H47.
sep_lifts_trms_in H49 (AOSEventFreeList).
  instantiate (1:= (
  (EX vl' max vml' wl xx,
         HECBList
           (set ecbls (v'46, Int.zero) (absmsgq vl' max vml', wl))**
         EvtInv_part2
           (set ecbls (v'46, Int.zero) (absmsgq vl' max vml', wl))
           v'3 (v'5 ++ v'6 :: v'7) vhold_addr v19 v20 v21 **
        AECBList (v'37 ++
            ((V$ OS_EVENT_TYPE_Q
              :: Vint32 i0
                 :: Vint32 i2
                    :: Vptr (v'41, Int.zero)
                       :: x4 :: v'' :: Vint32 i :: x5 :: nil,
             petbl, etbl) :: nil) ++ v'38)
           (v'39 ++
            (DMsgQ (Vptr (v'41, Int.zero))
               (x11
                :: x10
                   :: x1
                      :: x2
                         :: xx
                            :: Vint32 i3
                               :: Vint32 (i1 -ᵢ $ 1)
                                  :: Vptr (v'22, Int.zero) :: nil)
               (x :: x0 :: nil) v2 :: nil) ++ v'40) (EcbMod.set ecbls (v'46, Int.zero) (absmsgq vl' max vml', wl)) v'11 **
         [|RH_TCBList_ECBList_P (set ecbls (v'46, Int.zero) (absmsgq vl' max vml', wl)) v'11 ct|] ) **  
        <|| v'1 ||>  **
           LV pq @ OS_Q ∗ |-> Vptr (v'41, Int.zero) **
           LV message @ (Void) ∗
           |-> nth_val'
                 (Z.to_nat
                    ((Int.unsigned x3 -
                      Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
                 v2 **
         LV pevent @ OS_EVENT ∗ |-> Vptr (v'46, Int.zero) **
            HTCBList v'11 **
            HTime v'12 **
            HCurTCB ct **
            
         AOSQFreeList v'20 **
         AOSQFreeBlk v'21 **
         AOSMapTbl **
         AOSUnMapTbl **
         AOSTCBPrioTbl v'2 v'8 v'11 v'16 vhold_addr **
         AOSTCBList v'3 v'4 v'5 (v'6 :: v'7) v'8 ct v'11 **
         AOSTCBFreeList v'14 v'15 **
         AOSRdyTblGrp v'8 v'9 **
         AOSTime (Vint32 v'12) **
         AGVars **
         APthreadAttr v'17 **
         A_isr_is_prop **
         IntInv **
         TmrInv **
         CoreCommuInv ecbls**
         PartitionInv ecbls **
         CapabilityInv vcspace **
         tcbdllflag v'3 (v'5 ++ v'6 :: v'7) **
         p_local OSLInv ct
           (logic_val (V$ 1)
            :: logic_val (V$ os_code_defs.__EvLoc_normal)
               :: logic_val Vnull
                  :: logic_val Vnull
                     :: logic_val (Vptr (v'46, Int.zero)) :: nil) **
         Aisr empisr **
         Aie false **
         Ais nil **
         Acs (true :: nil) **
         Aier er **
         aemp_isr_is **
         A_dom_lenv
           ((pevent, OS_EVENT ∗)
            :: (message, (Void) ∗) :: (pq, OS_Q ∗) :: nil) **
              [|isptr
                 (nth_val'
                    (Z.to_nat
                       ((Int.unsigned x3 -
                         Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
                    v2)|] **
             [|opv =
               nth_val'
                 (Z.to_nat
                    ((Int.unsigned x3 -
                      Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
                 v2|] )).  
  sep semiauto.
  sep cancel EvtInv_part2.
  unfold AECBList.
  sep auto.

  eapply msgqnode_p_hold_end in Hrlh;eauto.
  lets Hnewjoin: ecb_get_set_join_join Hget Hjo' Hjo.
  destruct Hnewjoin as (ml1n & Hj1 & Hj2).

  eapply msgqlist_p_compose; eauto.
  clear - H57 H39.
  unfold isptr in*.
  destruct H39.
  subst x1.
  unfold val_inj in H57;tryfalse.
  destruct H;subst x1.
  destruct x.
  destruct (peq v'22 b);tryfalse.
  subst b.
  remember (Int.eq (x3 +ᵢ  Int.mul ($ 1) ($ 4)) i) as X.
  destruct X;unfold val_inj in H57;tryfalse.
  symmetry in HeqX.
  lets H100: Int.eq_spec (x3+ᵢInt.mul ($ 1) ($ 4)) i.
  rewrite HeqX in H100.
  subst i;auto.
  unfold val_inj in H57;tryfalse. 
  sep split in H32. 
  auto.

  eapply rh_tcbls_mqls_p_getmsg_hold;eauto.
  (*****not end*****)

  sep split in H47.
  assert (x1 <> Vptr(v'22,(x3 +ᵢInt.mul ($ 1) ($ 4)))).
  clear -H48 H39. 
  unfold isptr in *.
  destruct H39.
  subst x1;auto.
  destruct H;subst x1.
  destruct x.
  destruct (peq v'22 b);auto.
  subst b.
  intro.
  inverts H.
  rewrite Int.eq_true in H48.
  destruct H48;tryfalse.
  intro;inverts H;tryfalse.

  inverts Hpwl.
  eapply msgqnode_p_hold_no_end in Hrlh;eauto.
  lets Hnewjoin: ecb_get_set_join_join Hget Hjo' Hjo.
  destruct Hnewjoin as (ml1n & Hj1 & Hj2).

  lets Hmqlsp: msgqlist_p_compose Hecbetbl Hrlh Hj1 Hj2;eauto.
  sep semiauto; eauto.
  unfold AECBList.
  sep pauto.
  eapply evsllseg_compose; eauto.
  unfolds; simpl; eauto.
  sep cancel EvtInv_part2.
  sep cancel (evsllseg v'36).
  sep cancel (evsllseg v'').

  unfold AEventNode.
  unfold AEventData.
  unfold_msg.
  sep semiauto;eauto.
  sep cancel (OS_Q_FREEBLK).
  sep cancel (OS_EVENT).
  sep cancel AOSPostEventTbl.
  sep cancel (Aarray v'42).
  instantiate (2:= (v'41)).
  sep cancel (Astruct (v'41, Int.zero)).
  sep pauto.
  split; eauto. go.
  unfold V_qfreeblk;simpl;auto.

  eapply get_wellformedosq_end';eauto.
  simpl;splits;pauto.
  simpl;auto.
  simpl;splits;pauto.

  apply Hmqlsp.
  eapply rh_tcbls_mqls_p_getmsg_hold;eauto.

  (*--------------no msg L17 -----------------------*)
  pure intro.
  remember (Int.ltu ($ 0) i1) as X.
  destruct H1;destruct X;tryfalse.

  clear H1.

  lets Hnomsg: msgqnode_p_nomsg Hrlh;eauto.
  simpljoin1.
  lets Hgetnomsg: EcbMod.join_joinsig_get Hjo Hjo'.

  hoare_lifts_trms_pre (Aop, absecblsid).
  assert( Hcase: opv <> Vnull \/ opv = Vnull ). tauto.
  destruct Hcase.
  
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qacc_absimp_no_msg_abt;  pauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule.

  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply qacc_absimp_no_msg;  pauto.
  eapply absinfer_eq.

  eapply backward_rule1.
  intros.
  match goal with
  | H: _ |= ?p |-_=> instantiate (1:= p **  [| opv = Vnull |] )
  end.
  sep auto.
  hoare forward.
  
  apply disj_rule.
  hoare_split_pure_all.
  hoare forward prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eapply fold_EvtInv_frm; eauto.
  sep cancel (EvtInv_part2).
  sep cancel Aier.
  sep cancel p_local.
  sep cancel tcbdllflag.
  eapply fold_EvtInv_part1; eauto.
  trycancel_EvtInv1.
  cancel_corecommuinv. 
  
  (* PartitionInv *)
  Require Import sem_partition.
  cancel_partitioninv.
  eauto.
  (* end of PartitionInv *)

  { unfold is_que. 
    unfold RLH_ECBData_P in Hrlh.
    destruct e; tryfalse.
    do 4 eexists. eauto. }
  { unfold is_que. 
    unfold RLH_ECBData_P in Hrlh.
    destruct e; tryfalse.
    do 4 eexists. eauto. }
  eauto.

  go.
  unfold isptr in H16.
  destruct H16 as [Hnull | Hvptr].

  hoare forward.
  clear -Hnull.
  rewrite Hnull. auto.
  destruct Hvptr.
  hoare forward.
  clear -H16.
  rewrite H16. auto.
  split; eauto.
  hoare_split_pure_all.
  hoare forward prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eapply fold_EvtInv_frm; eauto.
  eapply fold_EvtInv_part1; eauto.
  trycancel_EvtInv.
  sep_lifts_trms (EvtInv_part2).
  eapply fold_EvtInv_part2; eauto.
  trycancel_EvtInv.
  unfold AECBList.
  sep cancel Aier.
  sep pauto.
  sep cancel p_local.
  
  instantiate (2:=(v'39 ++
        (DMsgQ (Vptr (v'41, Int.zero))
           (x11
            :: x10
               :: x1
                  :: x2
                     :: Vptr (v'22, x3)
                        :: Vint32 i3
                           :: Vint32 i1 :: Vptr (v'22, Int.zero) :: nil)
           (x :: x0 :: nil) v2 :: nil) ++ v'40)).

 instantiate (2:=(v'37 ++
        ((V$ OS_EVENT_TYPE_Q
          :: Vint32 i0
             :: Vint32 i2
                :: Vptr (v'41, Int.zero)
                   :: x4 :: v'' :: Vint32 i :: x5 :: nil, petbl, etbl)
         :: nil) ++ v'38)).
  eapply evsllseg_compose;eauto.
  instantiate (1:=v'').
  simpl;auto.
  sep cancel (evsllseg v'36).
  sep cancel (evsllseg v'').
  unfold AEventNode.
  unfold AEventData.
  unfold_msg.
  sep pauto.
  sep cancel (OS_Q_FREEBLK).
  sep cancel (OS_Q).
  sep cancel (OS_EVENT).
  sep cancel AOSPostEventTbl.
  sep cancel petbl.
  sep cancel OS_MAX_Q_SIZE.
  exact H33.
  eauto.
  simpl;auto.
  eauto.
  eauto.
  eauto.
  pure_auto.
  simpl;splits;pauto.
  unfold V_qfreeblk;simpl;auto.
  simpl;splits;pauto.
  simpl;auto.
  split;auto.
  simpl;splits;pauto.
  eapply msgqlist_p_compose;eauto.
  pauto.
  go.
  (*--------------------------L15 ~ L16--------------------------------*)

  hoare forward.

  Unshelve.
  exact (xH, Int.zero).
  exact (xH, Int.zero).
  exact (xH, Int.zero).
  exact (xH, Int.zero).
  exact (xH, Int.zero).
Qed.  




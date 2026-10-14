Require Export ucos_include.

Require Import oscore_common.
Require Import new_inv.
Require Import Lia.
Require Import OSQPostPure.
Require Import OSTimeTickPure.

Open Scope int_scope.
Open Scope Z_scope.
Open Scope code_scope.

(* Set Nested Proofs Allowed. *)

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


Ltac mytac :=
  heat; jeauto2.
(* from certiucos/ucos_lib/OSMutex_common.v *) 
Lemma evsllseg_aux:
  forall l1 s a b l2 P,
    s |= evsllseg a b l1 l2 ** P ->
    (a = b /\ l1 = nil \/ get_last_ptr l1 = Some b) /\ length l1 = length l2.
Proof.
  inductions l1.
  intros.
  simpl in H.
  mytac.
  swallow.
  left.
  auto.
  auto.
  intros.
  unfold evsllseg in H.
  fold evsllseg in H.
  destruct l2.
  simpl in H.
  mytac; tryfalse.
  destruct a. destruct p.
  sep normal in H.
  sep destruct H.
  sep lift 3%nat in H.
  lets Hxax: IHl1 H.
  mytac.
  swallow.
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


(* from certiucos/proof/task/taskdelete.v *)
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
  destruct p;simpljoin.
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
(*-----------OS Q Post-------------------*)

Lemma R_PrioTbl_P_hold1':
  forall vl tcb tid prio st msg st' msg' adrv sus sus',
    R_PrioTbl_P vl tcb adrv ->
    TcbMod.get tcb tid = Some (prio, st, msg, sus) ->
    R_PrioTbl_P vl (TcbMod.set tcb tid (prio, st', msg', sus')) adrv.
Proof.
  intros.
  unfold R_PrioTbl_P in *.
  simpljoin;try splits.
  intros.
  lets H100 : H H3 H4 H5.
  simpljoin;try splits.
  rewrite TcbMod.set_sem.
  unfold get in H6; simpl in H6.
  rewrite H6.
  remember (tidspec.beq tid tcbid) as bool; destruct bool.
  symmetry in Heqbool; apply tidspec.beq_true_eq in Heqbool.
  subst.
  rewrite H0 in H6.  
  inverts H6.
  eauto.
  eauto.
  intros.
  rewrite TcbMod.set_sem in H3.
  remember (tidspec.beq tid tcbid) as bool; destruct bool.
  inverts H3.
  symmetry in Heqbool; apply tidspec.beq_true_eq in Heqbool.
  subst.
  eapply H1; eauto.
  eapply H1; eauto.
  eapply R_Prio_NoChange_Prio_hold; eauto.
Qed.



Lemma eventtype_neq_q':
  forall v'38 v'21 i1 i0 i2 x2 x3 (* v'42 *) v'40 v'22 v'23 v'41 v'24 v'34 v'35 v'49 s P v'43 v'45 v'44 v'46 v'100 v'' i x6, (*add v'100*)
    length v'21 = length v'23-> 
    ECBList_P v'38 Vnull
              (v'21 ++
                    ((Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'' :: Vint32 i :: x6 :: nil,
                      v'40, v'100) :: nil) ++ v'22) (v'23 ++ (v'41 :: nil) ++ v'24) v'34 v'35 ->
    ECBList_P v'38 (Vptr (v'49, Int.zero)) v'21 v'23 v'43 v'35 ->
    EcbMod.join v'43 v'45 v'34 ->
    EcbMod.joinsig (v'49, Int.zero) v'46 v'44 v'45 ->
    Int.eq i1 ($ OS_EVENT_TYPE_Q) = false ->
    s|= AEventData
     (Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'' :: Vint32 i :: x6 :: nil) v'41 ** P ->
    s |= AEventData
      (Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'' :: Vint32 i :: x6 :: nil) v'41 **
      [|~ exists x y pwl z, EcbMod.get v'34 (v'49,Int.zero) = Some (absmsgq x y pwl, z) |] ** P.
Proof.
  intros.

  apply ecblist_p_decompose in H0;auto.
  simp join.

  assert (x1 = Vptr (v'49, Int.zero) /\ x = v'43).
  eapply ecblist_p_eqh;eauto.
  instantiate (1:=v'34).
  eapply EcbMod.join_sub_l;eauto.
  eapply EcbMod.join_sub_l;eauto.
  destruct H8;subst.
  destruct v'41.
  unfold AEventData in *.
  sep normal in H5.
  sep split in H5.
  unfolds in H9;simpl in H9.
  inverts H9.
  rewrite Int.eq_true in H4;tryfalse.
  sep auto.
  simpl in H6.
  simp join.
  destruct x1.
  destruct e;tryfalse.
  simp join.
  intro.
simp join.
  inverts H6.
  lets Hx:EcbMod.join_joinsig_get H7 H11.
  rewrite H12 in Hx.
  tryfalse.
  sep auto.
  simpl in H6.
  simp join.
  destruct x1.
  destruct e;tryfalse.
  simp join.
  intro.
  simp join.
  inverts H6.
  lets Hx:EcbMod.join_joinsig_get H7 H11.
  rewrite H12 in Hx.
  tryfalse.
  sep auto.
  simpl in H6.
  simp join.
  destruct x1.
  destruct e;tryfalse.
  simp join.
  intro.
  simp join.
  inverts H6.
  lets Hx:EcbMod.join_joinsig_get H7 H11.
  rewrite H15 in Hx.
  tryfalse.

  (* add about DPort *)
  sep auto.
  simpl in H6.
  simp join.
  destruct x1.
  destruct e;tryfalse.
  simp join.
  intro.
  simp join.
  inverts H6.
  lets Hx:EcbMod.join_joinsig_get H7 H11.
  rewrite H14 in Hx.
  tryfalse.
Qed.

Lemma TCBListP_head_in_tcb:
  forall v'51 v'52 v'22 x9 x8 i9 i8 i6 i5 i4 i3 v'33 v'34 v'50 xx,
    TCBList_P (Vptr v'52)
          ((v'51
            :: v'22
               :: x9
                  :: x8
                     :: Vint32 i9
                        :: Vint32 i8
                           :: Vint32 xx
                              :: Vint32 i6
                                 :: Vint32 i5
                                    :: Vint32 i4 :: Vint32 i3 :: nil) :: v'33)
          v'34 v'50 ->
        exists st sus, TcbMod.get v'50 v'52 = Some ( xx, st, x8, sus).
Proof.
  intros.
  unfolds in H.
  fold TCBList_P in H.
  mytac.
  unfolds in H2.
  destruct x2; destruct p.
  destruct p.
  mytac.
  unfolds in H2.
  unfolds in H4.
  simpl in H2.
  simpl in H4.
  inverts H2.
  inverts H4.
  inverts H.
  unfolds in H0; simpl in H0.
  inverts H0.
  unfold TcbJoin in H1.
  unfold join in H1; simpl in H1.
  unfolds in H6.
  do 2 eexists.
  eapply TcbMod.join_get_l.
  eauto.
  eapply TcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.
Qed.

Lemma get_tcb_stat_rdy
: forall tcur tcurl tcblist rtbl tcbls prio st msg,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
  (st = rdy \/ (exists wt, st = wait os_stat_time wt)) ->
  V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_RDY)) /\
  V_OSTCBEventPtr tcurl = Some Vnull.
Proof.
intros.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H6.
rename H6 into Hsus1; rename H10 into Hsus2;
rename H11 into H6; rename H12 into H10.
funfold H10.
rename H21 into Hhlport. rename H22 into Hhlport_sus.
rename H15 into Hrhl_postq.
funfold H4.
funfold  H10.
funfold H2.
destruct H1.
subst t;assert(RdyTCBblk tcurl rtbl p /\
     V_OSTCBStat tcurl = Some (V$ OS_STAT_RDY) /\
     V_OSTCBDly tcurl = Some (V$ 0)) by (eapply H2; eauto);
unfold V_OSTCBStat,V_OSTCBEventPtr in *;
mytac.
rewrite H28 in *;
rewrite H27;inverts H4;
split; try pauto.
destruct H32; auto.
destruct H1; subst t.
specialize (H10 _ _ _ (eq_refl _)).
destruct H10 as (t & eq & Hw & Hlt & Hst).
splits; eauto.
unfold V_OSTCBStat,V_OSTCBEventPtr in *;
mytac;
rewrite H28 in *;
inverts Hst;inverts H27.
destruct H32; eauto.
Qed.

(* new add *)
Lemma get_tcb_stat_rdy_sus
: forall tcur tcurl tcblist rtbl tcbls prio st msg sus,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
  (st = rdy \/ (exists wt, st = wait os_stat_time wt)) ->
  V_OSTCBStat tcurl = Some (Vint32 (if sus then ($ OS_STAT_SUSPEND) else ($ OS_STAT_RDY))) /\
  V_OSTCBEventPtr tcurl = Some Vnull.
Proof.
intros.
destruct sus.
2: eapply get_tcb_stat_rdy; eauto.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H6.
assert (Hst: V_OSTCBStat tcurl = Some (V$ OS_STAT_SUSPEND)).
{  destruct H10 as (Hrdy & Hwt).
   destruct H1; simpljoin; subst.
   eapply Hrdy; eauto.
   specialize (Hwt _ _ _ (eq_refl _)).
   simpljoin; auto.
 }
split; auto.
funfold H4.
unfold V_OSTCBEventPtr.
rewrite H20 in H22; inverts H22.
rewrite H21.
destruct H25; auto.
Qed.

Lemma get_tcb_stat_postq
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid t_opt,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
  st = wait (os_stat_postq sid) t_opt ->
  V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_POSTQ)) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 Int.zero) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H4.
rename H4 into Hsus1; rename H9 into Hsus2;
rename H10 into H4; rename H11 into H9.
funfold H9.
funfold  H14.
specialize (H14 _ _ _ _ (eq_refl _)).
unfold WaitTCBblk in *.
pauto.
Qed.

(* new add *)

Lemma get_tcb_stat_postq_sus
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid t_opt sus,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
  st = wait (os_stat_postq sid) t_opt ->
  V_OSTCBStat tcurl = Some (Vint32 (if sus then (Int.or ($ OS_STAT_POSTQ) ($ OS_STAT_SUSPEND)) else ($ OS_STAT_POSTQ)))  /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 Int.zero) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
destruct sus.
2: eapply get_tcb_stat_postq; eauto.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H4.
funfold H11.
specialize (H19 _ _ _ _ (eq_refl _)).
simpljoin.
funfold H24.
splits; auto.
Qed.

Lemma get_tcb_stat_postq_none
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
  st = wait (os_stat_postq sid) None ->
  V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_POSTQ)) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 Int.zero) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H4.
rename H4 into Hsus1; rename H9 into Hsus2;
rename H10 into H4; rename H11 into H9.
funfold H9.
funfold H14.
specialize (H14 _ _ _ _ (eq_refl _)).
simpljoin.
unfold WaitTCBblk in *.
simpljoin.
splits; auto.
Qed.

Lemma get_tcb_stat_postq_none_sus
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid sus,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
  st = wait (os_stat_postq sid) None ->
  V_OSTCBStat tcurl = Some (Vint32 (if sus then (Int.or ($ OS_STAT_POSTQ) ($ OS_STAT_SUSPEND)) else ($ OS_STAT_POSTQ))) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 Int.zero) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
destruct sus.
2: eapply get_tcb_stat_postq_none; eauto.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H4.
funfold H11.
specialize (H19 _ _ _ _ (eq_refl _)).
simpljoin.
funfold H24.
splits; auto.
Qed.

(******OSQPend**********)
Lemma tcblist_p_node_rl:
  forall v'47 v'39 v'19 x15 x10 i10 i9 i8 i7 i6 i5 i1 v'31 v'32 v'36 i,
    TCBList_P (Vptr (v'47, Int.zero))
              ((v'39
                  :: v'19
                  :: x15
                  :: x10
                  :: Vint32 i10
                  :: Vint32 i9
                  :: Vint32 i8
                  :: Vint32 i7
                  :: Vint32 i6
                  :: Vint32 i5 :: Vint32 i1 :: nil) :: v'31)
              v'32 v'36 ->
    RL_TCBblk_P
      (v'39
         :: v'19
         :: x15
         :: Vnull
         :: Vint32 i
         :: V$OS_STAT_POSTQ
         :: Vint32 i8
         :: Vint32 i7
         :: Vint32 i6 :: Vint32 i5 :: Vint32 i1 :: nil).
Proof.
  introv Ht.
  simpl in Ht.
  simpljoin1;simpl_hyp.
  inverts H.
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  simpljoin1; simpl_hyp.
  funfold H2.
  unfolds.
  do 6 eexists;splits; try unfolds; simpl;  eauto.
  splits; auto.  right. right. right. right. right. eauto.
  eexists.
  splits.
  unfolds.
  simpl; eauto.
  introv Hf.
  destruct Hf as [Hf | Hf];
  inverts Hf.
Qed.

Lemma ECBList_P_high_tcb_block_hold_postq:
  forall  ectrl head tail msgql ecbls tcbls ptcb prio  m qid time m' sus sus',
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, rdy, m, sus) ->
    EcbMod.get ecbls qid = None ->
    ECBList_P head tail ectrl msgql ecbls 
              (TcbMod.set tcbls ptcb (prio, wait (os_stat_postq qid) time, m', sus')).
Proof.
  inductions ectrl.
  intros.
  simpl.
  simpl in H.
  simpljoin1.
  splits; auto.
  
  intros.
  simpl in H.
  simpljoin1. rename H3 into Hrecbpetblp; rename H4 into H3.
  destruct msgql; tryfalse.
  destruct a.  destruct p.
  simpljoin1.
  simpl.
  exists x.
  splits; auto.
  unfolds.
  destruct H2 as (Hr1 & Hr2 & Hr3).
  destruct Hr1 as (Hra1 & Hra2 & Hra3 & Hra4 & Hra5).
  destruct Hr2 as (Hrb1 & Hrb2 & Hrb3 & Hrb4 & Hrb5).
  simpl in Hr3.
  splits.
  unfolds.
  splits.
  unfolds. 
  intros.
  eapply Hra1 in H6;eauto.
  simpljoin1.
  assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
  destruct H7.
  subst.
  unfolds in H6; simpl in H6.
  rewrite H0 in H6.
  inverts H6.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  unfolds.
  intros.
  eapply Hra2 in H6;eauto.
  simpljoin1.
  assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
  destruct H7.
  subst.
  unfolds in H6; simpl in H6.
  rewrite H0 in H6.
  inverts H6.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  unfolds.
  intros.
  eapply Hra3 in H6;eauto.
  simpljoin1.
  assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
  destruct H7.
  subst.
  unfolds in H6; simpl in H6.
  rewrite H0 in H6.
  inverts H6.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  unfolds.
  intros.
  eapply Hra4 in H6;eauto.
  simpljoin1.
  assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
  destruct H7.
  subst.
  unfolds in H6; simpl in H6.
  rewrite H0 in H6.
  inverts H6.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  (* add port *)
  unfolds.
  intros.
  eapply Hra5 in H6;eauto.
  simpljoin1.
  assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
  destruct H7.
  subst.
  unfolds in H6; simpl in H6.
  rewrite H0 in H6.
  inverts H6.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  unfolds.
  splits.
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
(*   apply ecbmod_joinsig_get in H3.
  rewrite H3 in H1.
  tryfalse. *)
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto.
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto.
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto.
   unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto.
  (* add port *)
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto.

  simpl; auto.
  
  unfolds.
  destruct Hrecbpetblp as (Hra1 & Hrb1 ).

  splits.
  unfolds. rename H2 into Hrecbetblp.

  intros.
  eapply Hra1 in H6;eauto.
  simpljoin1.
  assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
  destruct H7.
  subst.
  unfolds in H6; simpl in H6.
  rewrite H0 in H6.
  inverts H6.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  unfolds. rename H2 into Hrecbetblp.

  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  apply ecbmod_joinsig_get in H3.
  rewrite H3 in H1.
  tryfalse.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto.
  
  do 3 eexists; splits; eauto.
  eapply IHectrl; eauto.
  eapply  ecbmod_joinsig_get_none; eauto.
Qed.

Lemma ejoin_get_none_r : forall ma mb mc x a, EcbMod.get ma x = Some a -> EcbMod.join ma mb mc -> EcbMod.get mb x = None.
Proof.
  intros.
  unfolds in H0.
  lets adf : H0 x.
  destruct (EcbMod.get ma x).
  destruct (EcbMod.get mb x).
  tryfalse.
  auto.
  destruct (EcbMod.get mb x).
  tryfalse.
  auto.
Qed.

Lemma ejoin_get_none_l : forall ma mb mc x a, EcbMod.get mb x = Some a -> EcbMod.join ma mb mc -> EcbMod.get ma x = None.
Proof.
  intros.
  apply EcbMod.join_comm in H0.
  eapply ejoin_get_none_r; eauto.
Qed.

Lemma TcbMod_set_R_PrioTbl_P_hold :
  forall ptbl tcbls ptcb pr st m st' m' av sus sus',
    R_PrioTbl_P ptbl tcbls av ->
    TcbMod.get tcbls ptcb = Some (pr, st, m, sus) ->
    R_PrioTbl_P ptbl (TcbMod.set tcbls ptcb (pr,st',m', sus')) av.
Proof.
  intros.
  unfold R_PrioTbl_P in *.
  simpljoin1; splits.
  intros.
  lets H100 : H H3 H4 H5.
  simpljoin1.
  rewrite TcbMod.set_sem.
  unfold get in H6; simpl in H6.
  rewrite H6.
  remember (tidspec.beq ptcb tcbid) as bool; destruct bool.
  symmetry in Heqbool; apply tidspec.beq_true_eq in Heqbool.
  subst.
  rewrite H0 in H6.  
  inverts H6.
  eauto.
  eauto.
  intros.
  rewrite TcbMod.set_sem in H3.
  remember (tidspec.beq ptcb tcbid) as bool; destruct bool.
  inverts H3.
  symmetry in Heqbool; apply tidspec.beq_true_eq in Heqbool.
  subst.
  eapply H1; eauto.
  eapply H1; eauto.
  eapply  R_Prio_NoChange_Prio_hold; eauto.
Qed.

Lemma rtbl_remove_RL_RTbl_PrioTbl_P_hold :
  forall prio y bitx rtbl ry ptbl vhold,
    0 <= Int.unsigned prio < 64 ->
    y = Int.shru (prio) ($ 3) ->
    bitx = ($ 1) <<ᵢ (Int.and (prio) ($ 7)) ->
    nth_val ∘(Int.unsigned y) rtbl = Some (Vint32 ry) ->
    RL_RTbl_PrioTbl_P rtbl ptbl vhold->
    RL_RTbl_PrioTbl_P
     (update_nth_val ∘(Int.unsigned y) rtbl (Vint32 (ry&ᵢInt.not bitx))) ptbl vhold.
Proof.
  introv Hpr Hy Hbit Hnth Hrl.
  subst.
  unfolds. 
  unfolds in Hrl.
  intros.
  assert (p = prio \/ p <> prio) by tauto.
  destruct H1.
  subst.
  unfolds in H0.
  assert ( prio&ᵢ$ 7  =  prio&ᵢ$ 7 ) by auto.
  assert (Int.shru prio ($ 3)  =  Int.shru prio ($ 3)) by auto.
  lets Hf : H0  (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))) H1 H2.
  assert ( (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7)))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 1<<ᵢ(prio&ᵢ$ 7)).
  apply Hf.
  eapply update_nth; eauto.
  rewrite Int.and_assoc in H3.
  assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
  rewrite Int.and_commut. 
  rewrite Int.and_not_self; auto.
  rewrite H4 in H3.
  rewrite Int.and_zero in H3.
  assert ($ 1<<ᵢ(prio&ᵢ$ 7) <> $ 0) by (apply math_prop_neq_zero2; eauto).
  unfold Int.zero in H3.
  tryfalse.
  eapply Hrl; auto.
  eapply prio_neq_in_tbl with (prio0 :=p)(prio:=prio); eauto.
Qed.  


Lemma R_ECB_ETbl_P_high_tcb_block_hold_postq :
  forall l  vl pegrp v1 v2 v3 v4 v5 v6 etbl petbl tcbls ptcb prio m m' y bity bitx ey time av sus sus',
    Int.unsigned prio < 64 ->
    R_PrioTbl_P vl tcbls av->
    R_ECB_ETbl_P l
                 (V$OS_EVENT_TYPE_Q
                    :: v1
                    :: v2 :: v3 :: v4 :: v5 :: Vint32 pegrp :: v6 ::nil,
                  etbl,petbl) tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, rdy, m, sus) ->
    y = Int.shru (prio) ($ 3) ->
    bity = ($ 1) <<ᵢ y ->
    bitx = ($ 1) <<ᵢ (Int.and (prio) ($ 7)) ->
    nth_val ∘(Int.unsigned y) petbl = Some (Vint32 ey) ->
    R_ECB_ETbl_P l
                 (V$OS_EVENT_TYPE_Q
                    :: v1
                    :: v2 :: v3 :: v4 :: v5 :: Vint32 (Int.or pegrp bity) :: v6:: nil,
                  etbl, update_nth_val ∘(Int.unsigned y) petbl (Vint32 (Int.or ey bitx)))
                 (TcbMod.set tcbls ptcb
                             (prio, wait (os_stat_postq l) time, m', sus')).
Proof.
  introv Hran Hrs  Hre Htc Hy Hb1 Hb2 Hnth.
  subst.
  unfolds in Hre.
  destruct Hre as (Hre1 & Hre2 & Het).
  unfolds.
  splits.
  unfolds.
  splits.
  
(*RLH_ECB_ETbl_Q_P*)
  unfolds.
  intros.
  destruct Hre1 as (Hre1 & _).
  destruct Hre2 as (Hre2 & _).
  unfolds in Hre1.
  unfolds in Hre2.
  assert (prio = $ prio0 \/ prio <> $ prio0) by tauto.
  destruct H1.
  subst.
  apply Hre1 in H.
  destruct H as (cur_t & cur_q & cur_m & sus0 & H).

  exists cur_t cur_q cur_m.
  eexists.
  assert (cur_t =ptcb \/ cur_t <> ptcb )by tauto.
  destruct H1.
  inverts H1.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true;eauto.
  unfold get in H. unfold TcbMap in H.
  rewrite H in Htc. 
  inverts Htc.
  
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false;eauto.
  unfolds; simpl;auto.
  
  apply Hre1 in H.
  destruct H as (cur_t & cur_q & cur_m & sus0 & H).

  exists cur_t cur_q cur_m.
  eexists.
  assert (cur_t =ptcb \/ cur_t <> ptcb )by tauto.
  destruct H2.
  inverts H2.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true;eauto.
  unfold get in H. unfold TcbMap in H.
  rewrite H in Htc. 
  inverts Htc.
  
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false;eauto.
  unfolds; simpl;auto.
  
  unfolds.
  intros.
  usimpl H0.
  unfolds.
  intros.
  usimpl H0.
  unfolds.
  intros.
  usimpl H0.
  (* add about RLH_ECB_ETbl_PORT_P *)
  unfolds.
  intros.
  usimpl H0.
  
  (*RHL_ECB_ETbl_P*)
  unfolds.
  splits.
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  splits.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  unfolds;simpl;auto.
  
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  unfolds in Hre2.
  destruct Hre2 as (Hre2 & _).
  lets Hasd : Hre2  H. 
  auto.

  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  destruct Hre2 as (_&Hre2&_).
  apply Hre2 in H. 
  auto.
  
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  destruct Hre2 as (_&_&Hre2&_).
  apply Hre2 in H.
  auto.
  
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  destruct Hre2 as (_&_& _ &Hre2 & _).
  apply Hre2 in H.
  destruct H.
  usimpl H1.
  

  (* add about port *)
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  destruct Hre2 as (_&_& _ &_ & Hre2).
  apply Hre2 in H.
  auto.

  simpl.
  unfolds.
  left.
  unfolds; simpl; auto.
Qed.

 
Lemma R_ECB_PETbl_P_high_tcb_block_hold_postq :
  forall l  vl pegrp v1 v2 v3 v4 v5 v7 etbl petbl tcbls ptcb prio st m m' y bity bitx ey time av sus sus',
    Int.unsigned prio < 64 ->
    R_PrioTbl_P vl tcbls av->
    R_ECB_PETbl_P l
                 (V$OS_EVENT_TYPE_Q
                    :: v1
                    :: v2 :: v3 :: v4 :: v5 :: Vint32 pegrp :: v7 ::nil,
                  etbl,petbl) tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    y = Int.shru (prio) ($ 3) ->
    bity = ($ 1) <<ᵢ y ->
    bitx = ($ 1) <<ᵢ (Int.and (prio) ($ 7)) ->
    nth_val ∘(Int.unsigned y) petbl = Some (Vint32 ey) ->
    R_ECB_PETbl_P l
                 (V$OS_EVENT_TYPE_Q
                    :: v1
                    :: v2 :: v3 :: v4 :: v5 :: Vint32 (Int.or pegrp bity) :: nil,
                  etbl, update_nth_val ∘(Int.unsigned y) petbl (Vint32 (Int.or ey bitx)))
                 (TcbMod.set tcbls ptcb
                             (prio, wait (os_stat_postq l) time, m', sus')).
Proof.
  introv Hran Hrs  Hre Htc Hy Hb1 Hb2 Hnth.
  subst.
  unfolds in Hre.
  destruct Hre as (Hre1 & Hre2).
  unfolds.
  splits.

  unfolds.
  intros.
  unfolds in Hre1.
  unfolds in Hre2.
  assert (prio = $ prio0 \/ prio <> $ prio0) by tauto.
  destruct H1.
  subst.
  exists ptcb time m'.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  lets Hres : prio_wt_inq_keep Hran H1 Hnth .
  destruct Hres.
  apply H2 in H.
  apply Hre1 in H.
  simpljoin1.
  exists x x0 x1.
  assert (x = ptcb \/ x <> ptcb) by tauto.
  destruct H4.
  subst.
  unfolds in H; simpl in H.
  rewrite Htc in H.
  inverts H.
  tryfalse.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.
  unfolds. 
  simpl; auto.
  

  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  splits.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  unfolds.
  rewrite Int.repr_unsigned.
  exists ( prio0&ᵢ$ 7).
  exists (Int.shru prio0 ($3)).
  exists ((Int.or ey ($ 1<<ᵢ(prio0&ᵢ$ 7)))).
  splits; eauto.
  clear - Hran.
  int auto.
  Require Import pure_lib.
  eapply update_nth; eauto.
  rewrite Int.and_commut.
  rewrite Int.or_commut.
  unfold Int.one.
  rewrite Int.and_or_absorb.
  auto.
  unfolds; simpl; auto.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  lets Hasd : Hre2  H.
   destruct Hasd as (Has1 & Has2).
  splits.
  eapply prio_wt_inq_keep; eauto.
  rewrite Int.repr_unsigned.
  unfolds  in Hrs.
  destruct Hrs.
  destruct H2.
  unfolds in H3.
  lets Hdd : H3 H0 H Htc.
  eauto.
  unfolds; simpl; auto.
Qed.

Open Scope int_scope.
Open Scope Z_scope.
Open Scope code_scope.

Lemma TCBList_P_tcb_block_hold :
    forall ptcb v1 v2 v3 v4 v5 v6 v8 v9 v10 v11 rtbl vl
           tcbls prio st m qid ry m',
    TCBList_P (Vptr ptcb) ((v1::v2::v3::v4::v5::(Vint32 v6)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, false) ->
    prio_neq_cur tcbls ptcb ( prio) ->
    st = rdy \/ (exists n, st = wait os_stat_time n) -> 
    nth_val (nat_of_Z (Int.unsigned v9)) rtbl = Some (Vint32 ry) ->
    TCBList_P (Vptr ptcb) ((v1::v2::(Vptr qid)::m'::(Vint32 Int.zero)::(V$ OS_STAT_POSTQ)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) 
(update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (Int.and ry (Int.not v10)))) 
 (TcbMod.set tcbls ptcb ( prio, wait (os_stat_postq qid) None , m', false)).
Proof.
  introv  Htcb Htm Hst Hprio Hnth.
  unfolds in Htcb;fold TCBList_P in Htcb.
  mytac.
  inverts H.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds.
  fold TCBList_P.
  exists x x0.
  exists x1.
  exists (prio,wait (os_stat_postq qid) None ,m', false).
  splits; eauto.
  eapply tcbjoin_set; eauto.
  {
    unfolds in H2.
    destruct x2.
    destruct p.
    destruct p.
    mytac.
    unfolds in H0.
    simpl in H0; inverts H0.
    unfolds in H;simpl in H; inverts H.
    unfolds.
    split.  
    unfolds.
    simpl.
    auto.
    funfold H2.
    split.
    auto.
    split.
    unfolds.
    do 6 eexists; splits; try unfolds; simpl; eauto.
    splits; eauto. right;eauto.
    tauto.
    eexists.
    splits.
    unfolds;simpl; eauto.
    introv Hf.
    destruct Hf as [Hf | Hf];
    inverts Hf.
    lets Hexa : tcbjoin_get H1 Htm.
    inverts Hexa.
    unfolds in H4.
    split.
    unfolds.
    intros.
    simpl_hyp.
    unfolds in H.
    destruct H.
    simpl_hyp.
    unfolds in H0.
    assert (prio&ᵢ$ 7 = prio&ᵢ$ 7) by auto.
    assert (Int.shru ( prio) ($ 3) =Int.shru (prio) ($ 3)) by auto.
    assert ( nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3)))
                     (update_nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3))) rtbl
                                     (Vint32 (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
             Some (Vint32  (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))).
    eapply pure_lib.update_nth; eauto.
    lets Hr: H0 H H2 H5.
    rewrite Int.and_assoc in Hr.
    assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
    rewrite Int.and_commut.
    rewrite Int.and_not_self.
    auto.
    rewrite H6  in Hr.
    rewrite Int.and_zero in Hr.
    assert ( $ 1<<ᵢ(prio&ᵢ$ 7) <> $ 0) by (apply  math_prop_neq_zero2; try lia).
    unfold Int.zero in Hr.
    tryfalse.
    split.
    unfolds.
    intros.
    inverts H.

    (* new add *)
  split.
  unfolds.
  split; intros;
  inverts H0.
  split.
  unfolds.
  split; intros;
  inverts H.
  (* end of new add *)
  split.
  unfolds.
  splits; try solve [ unfolds; intros; inverts H0].
  splits; try solve [ unfolds; intros; inverts H0].
  unfolds.
  intros.
  unfolds in H.
  mytac.
  simpl_hyp.
  repeat eexists.
  eauto.
  splits; try solve [ unfolds; intros; inverts H0].

  unfolds.
  splits; try solve [ unfolds; intros; inverts H].
  unfolds; intros.
  inverts H.
  repeat eexists; eauto.
  unfolds.
  intros.
  subst.
  apply nth_upd_eq in H2.
  inverts H2.
  rewrite Int.and_assoc.
  assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
  rewrite Int.and_commut.
  rewrite Int.and_not_self.
  auto.
  rewrite H.
  rewrite  Int.and_zero.
  auto.
  splits; try solve [ unfolds; intros; inverts H].
  }
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac; simpl_hyp.
  funfold H2.
  
  Require Import OSTimeDlyPure.
  
  eapply update_rtbl_tcblist_hold; eauto.
  unfolds in Hst.
  intros.
  lets Has : tcbjoin_get_getneq H1 H.
  destruct Has.
  eapply Hst; eauto.
Qed.

Open Scope int_scope.
Open Scope Z_scope.
Open Scope code_scope.

Lemma TCBList_P_tcb_block_hold_sus :
    forall ptcb v1 v2 v3 v4 v5 v6 v8 v9 v10 v11 rtbl vl
           tcbls prio st m qid ry m' sus stat,
    TCBList_P (Vptr ptcb) ((v1::v2::v3::v4::v5::(Vint32 v6)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    prio_neq_cur tcbls ptcb ( prio) ->
    st = rdy \/ (exists n, st = wait os_stat_time n) -> 
    nth_val (nat_of_Z (Int.unsigned v9)) rtbl = Some (Vint32 ry) ->
    stat = (if sus then Int.or ($ OS_STAT_POSTQ) ($ OS_STAT_SUSPEND) else ($ OS_STAT_POSTQ))  ->
    TCBList_P (Vptr ptcb) ((v1::v2::(Vptr qid)::m'::(Vint32 Int.zero)::(Vint32 stat)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) 
(update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (Int.and ry (Int.not v10)))) 
 (TcbMod.set tcbls ptcb ( prio, wait (os_stat_postq qid) None , m', sus)).
Proof.
  introv  Htcb Htm Hst Hprio Hnth Hstat.
  destruct sus; subst.
  2: eapply TCBList_P_tcb_block_hold; eauto.
  unfolds in Htcb;fold TCBList_P in Htcb.
  mytac.
  inverts H.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds.
  fold TCBList_P.
  exists x x0.
  exists x1.
  exists (prio,wait (os_stat_postq qid) None,m', true).
  splits; eauto.
  eapply tcbjoin_set; eauto.
{
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds in H;simpl in H; inverts H.
  unfolds.
  split.
  unfolds.
  simpl.
  auto.
  funfold H2.
  splits.
  auto.
  unfolds.
  do 6 eexists; splits; try unfolds; simpl; eauto.
  splits; eauto.
  pauto.
  eexists.
  splits.
  unfolds;simpl; eauto.
  introv Hf.
  destruct Hf as [Hf | Hf];
  inverts Hf.
  lets Hexa : tcbjoin_get H1 Htm.
  inverts Hexa.
  unfolds in H4.
  split.
  unfolds.
  intros.
  simpl_hyp.
  unfolds in H.
  destruct H.
  simpl_hyp.
  unfolds in H0.
  assert (prio&ᵢ$ 7 = prio&ᵢ$ 7) by auto.
  assert (Int.shru ( prio) ($ 3) =Int.shru (prio) ($ 3)) by auto.
  assert ( nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3)))
         (update_nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3))) rtbl
            (Vint32 (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
           Some (Vint32  (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth; eauto.
  lets Hr: H0 H H2 H5.
  rewrite Int.and_assoc in Hr.
  assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
  rewrite Int.and_commut.
  rewrite Int.and_not_self.
  auto.
  rewrite H6  in Hr.
  rewrite Int.and_zero in Hr.
  assert ( $ 1<<ᵢ(prio&ᵢ$ 7) <> $ 0) by (apply  math_prop_neq_zero2; try lia).
  unfold Int.zero in Hr.
  tryfalse.
  split.
  unfolds.
  intros.
  inverts H.
  (* new add *)
  split.
  unfolds.
  split; intros;
  inverts H0.
  split.
  unfolds.
  split; intros;
  inverts H.
  (* end of new add *)
  split.
  unfolds.
  splits; try solve [ unfolds; intros; inverts H0].
  splits; try solve [ unfolds; intros; inverts H0].
  unfolds; intros.
  unfolds in H.
  mytac.
  simpl_hyp.
  eauto.
  splits; try solve [ unfolds; intros; inverts H0].
(*   eexists. *)
(*   eexists. *)
(*   splits; eauto. *)
  unfolds.
  splits; try solve [ unfolds; intros; inverts H].
  splits; try solve [ unfolds; intros; inverts H].
  unfolds.
  intros.
  inverts H.
  repeat eexists; eauto.
  unfolds.
  intros.
  subst.
  apply nth_upd_eq in H2.
  inverts H2.
  rewrite Int.and_assoc.
  assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
  rewrite Int.and_commut.
  rewrite Int.and_not_self.
  auto.
  rewrite H.
  rewrite  Int.and_zero.
  auto.
}
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac; simpl_hyp.
  funfold H2.
   eapply OSTimeDlyPure.update_rtbl_tcblist_hold; eauto.
  unfolds in Hst.
  intros.
  lets Has : tcbjoin_get_getneq H1 H.
  destruct Has.
  eapply Hst; eauto.
Qed.

Lemma TCBList_P_tcb_block_hold'' :
  forall v ptcb rtbl vl y bitx
         tcbls prio ry x1 tcs tcs' t m sus,
    0 <= Int.unsigned prio < 64 ->
    TcbMod.join (TcbMod.sig ptcb (prio, t, m, sus)) x1 tcs ->
    TcbMod.join tcbls tcs tcs' -> 
    TCBList_P v vl rtbl tcbls ->
    y = Int.shru prio ($ 3) ->
    bitx = ($ 1) <<ᵢ (Int.and prio ($ 7)) ->
    prio_neq_cur tcbls ptcb  prio ->
    nth_val (nat_of_Z (Int.unsigned y)) rtbl = Some (Vint32 ry) ->
    TCBList_P v vl (update_nth_val ∘(Int.unsigned y) rtbl (Vint32 (Int.and ry (Int.not bitx)))) tcbls.
Proof.
  introv Hran Htc Hy Hb Hpro Hnth.
  eapply TCBList_P_tcb_dly_hold'; eauto.
Qed.


Lemma TCBList_P_tcb_block_hold':
  forall v ptcb rtbl vl y bitx
         tcbls prio ry tcs tcs' t m sus,
    0 <= Int.unsigned prio < 64 ->
    TcbMod.get tcs ptcb = Some (prio, t, m, sus)->
    TcbMod.join tcbls tcs tcs' -> 
    TCBList_P v vl rtbl tcbls ->
    y = Int.shru prio ($ 3) ->
    bitx = ($ 1) <<ᵢ (Int.and prio ($ 7)) ->
    prio_neq_cur tcbls ptcb  prio ->
    nth_val (nat_of_Z (Int.unsigned y)) rtbl = Some (Vint32 ry) ->
    TCBList_P v vl (update_nth_val ∘(Int.unsigned y) rtbl (Vint32 (Int.and ry (Int.not bitx)))) tcbls.
Proof.
  intros.
  lets Hx:tcb_get_join H0.
  simpljoin1.
  eapply TCBList_P_tcb_block_hold'';eauto.
Qed.


Lemma RH_CurTCB_high_block_hold_postq :
  forall ptcb tcbls prio st m qid time m' sus sus',
    RH_CurTCB ptcb tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    RH_CurTCB ptcb (TcbMod.set tcbls ptcb
        (prio, wait (os_stat_postq qid) time, m', sus')).
Proof.
  introv Hr Ht.
  unfolds in Hr.
  simpljoin1.
  unfolds in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  unfolds.
  do 4 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; eauto.
Qed.

Lemma  Mutex_owner_hold_for_set_tcb: forall x y pcur a b c sus,  RH_TCBList_ECBList_MUTEX_OWNER x y ->  RH_TCBList_ECBList_MUTEX_OWNER x (TcbMod.set y pcur (a, b, c, sus)).
Proof.
  intros.
  unfold   RH_TCBList_ECBList_MUTEX_OWNER  in *.
  intros.
  assert ( pcur = tid  \/ pcur <> tid ) by tauto.
  elim H1; intros.
  subst pcur.
  rewrite TcbMod.set_a_get_a; auto.
  eapply H in H0.
  destruct H0.
  split; eauto.
  go.
  rewrite TcbMod.set_a_get_a'; auto.
  eapply H; eauto.
  go.
Qed.

 Lemma  Mutex_owner_set: forall x y z t, (~exists aa bb cc, t = (absmutexsem aa bb, cc))->   RH_TCBList_ECBList_MUTEX_OWNER x y ->  RH_TCBList_ECBList_MUTEX_OWNER (EcbMod.set x z t) y.
  Proof.
    intros.
    unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
    intros.
    assert ( eid = z \/ eid <> z).
    tauto.
    elim H2; intros.
    subst eid.
    rewrite EcbMod.set_a_get_a in H1.
    inverts H1.
    false.
    apply H.
    eauto.
    go.

    rewrite EcbMod.set_a_get_a' in H1.
    eapply H0; eauto.
    go.
  Qed.


Lemma RH_TCBList_ECBList_P_high_block_hold :
  forall ecbls tcbls pcur qid m ml max wl prio  time m' pwl sus sus',
    RH_TCBList_ECBList_P ecbls tcbls pcur ->
    EcbMod.get ecbls qid = Some (absmsgq ml max pwl, wl) ->
    TcbMod.get tcbls pcur = Some (prio, rdy, m, sus) ->
    RH_TCBList_ECBList_P (EcbMod.set ecbls qid (absmsgq ml max pwl, pcur::wl)) (TcbMod.set tcbls pcur (prio, wait (os_stat_q qid) time, m', sus')) pcur. 
Proof.
  introv Hr Ht He.
  unfolds in Hr.
  destruct Hr as (Hr1 & Hr2 & Hr3 & Hr4 & Hr5).
  unfolds.
  splits.
  unfolds.
  splits.
  intros.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  simpl in H0.
  destruct H0.
  do 4 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; auto.
  assert (EcbMod.get ecbls eid = Some (absmsgq x y pqwaitset, wl) /\ In tid wl) by eauto.
  apply Hr1 in H0.
  simpljoin1.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H1.
  do 4 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; auto.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmsgq x y pqwaitset, qwaitset) /\ In tid qwaitset) by eauto.
  apply Hr1 in H2.
  simpljoin1.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfolds in H2; simpl in H2.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.

  unfold RH_TCBList_ECBList_Q_P in Hr1.
  destruct Hr1 as  (Hr11 & Hr12 & Hr13 & Hr14).
  intros.

  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
(*   inverts H. *)
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct H1.
  inverts H1.
  assert(pqwaitset = pwl). inverts H;eauto.
  inverts H1.
  assert (EcbMod.get ecbls eid =Some (absmsgq ml max pwl, wl) /\ In tid pwl) by eauto.
  lets Hx : Hr12 H1.
  simpljoin1.
  unfold get in H4; unfold TcbMap in H4.
  rewrite H4 in He; tryfalse.
  assert(pqwaitset = pwl). inverts H;eauto.
  inverts H2.
  assert (EcbMod.get ecbls eid =Some (absmsgq ml max pwl, wl) /\ In tid pwl) by eauto.
  lets Hx : Hr12 H2.
  simpljoin1.
  do 3 eexists;
  rewrite TcbMod.set_sem ;
  rewrite tidspec.neq_beq_false; eauto.
  
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmsgq x y pqwaitset, qwaitset) /\ In tid pqwaitset) by eauto.
  apply Hr12 in H2.
  simpljoin1.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfolds in H2; simpl in H2.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.

  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  exists ml max pwl.
  exists (tid::wl).
  splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; eauto.
  simpl; left; auto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr1 in H.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  do 4 eexists; splits; eauto.
  unfolds in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  simpl.
  right; auto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 4 eexists; splits; eauto.
  
 intros.
  destruct Hr1 as  (Hr11 & Hr12 & Hr13 & Hr14 ).
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.

(*   simpl; left; auto. *)
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr14 in H.
  simpljoin1.
  unfold get in H; unfold EcbMap in H.
  rewrite H in Ht.
  inverts Ht.
  exists ml max pwl.
  exists (pcur::wl).
  splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr14 in H.
  simpljoin1.
  unfold get in H; unfold EcbMap in H.
  exists x x0 x1 x2.
  splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  
  splits.
  intros.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid =Some (abssem n, wls) /\ In tid wls) by eauto.
  apply Hr2 in H2.
  simpljoin1.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfolds in H2; simpl in H2.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr2 in H.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfolds in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists; splits; eauto.
  splits.
  intros.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmbox n, wls) /\ In tid wls) by eauto.
  apply Hr3 in H2.
  simpljoin1.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfolds in H2; simpl in H2.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr3 in H.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfolds in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists; splits; eauto.
  splits.
  intros.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmutexsem n1 n2, wls) /\ In tid wls) by eauto.
  apply Hr4 in H2.
  simpljoin1.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfolds in H2; simpl in H2.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr4 in H.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfolds in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; splits; eauto.
  apply Mutex_owner_hold_for_set_tcb.
  eapply Mutex_owner_set; eauto.
  intro; simpljoin1.
  unfolds in Hr4.
  simpljoin1.
  auto.
  
  destruct Hr4 as (_ & _ & _ & Hrb).
  eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_ecb;
  try eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
  pure_auto.
  do 2 destruct H.
  inverts H.

  (* add about port *)
  splits.
  intros.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid =Some (absport, wls) /\ In tid wls) by eauto.
  apply Hr5 in H2.
  simpljoin1.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfolds in H2; simpl in H2.
  rewrite H2 in He.
  inverts He. 
  do 4 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr5 in H.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfolds in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eexists; splits; eauto.
Qed.


Lemma RH_TCBList_ECBList_P_high_block_hold_postq :
  forall ecbls tcbls pcur qid m ml max pwl wl prio  time m' sus sus',
    RH_TCBList_ECBList_P ecbls tcbls pcur ->
    EcbMod.get ecbls qid = Some (absmsgq ml max pwl, wl) ->
    TcbMod.get tcbls pcur = Some (prio, rdy, m, sus) ->
    RH_TCBList_ECBList_P (EcbMod.set ecbls qid (absmsgq ml max (pcur::pwl), wl)) (TcbMod.set tcbls pcur (prio, wait (os_stat_postq qid) time, m', sus')) pcur. 
Proof.
  introv Hr Ht He.
  unfolds in Hr.
  destruct Hr as (Hr1 & Hr2 & Hr3 & Hr4 & Hr5).
  unfolds.
  splits.
  unfolds.
  splits.
  
  unfold RH_TCBList_ECBList_Q_P in Hr1.
  destruct Hr1 as  (Hr11 & Hr12 & Hr13 & Hr14).
  intros.

  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct H1.
  inverts H1.
  assert(qwaitset = wl). inverts H;eauto.
  inverts H1.
  assert (EcbMod.get ecbls eid =Some (absmsgq ml max pwl, wl) /\ In tid wl) by eauto.
  lets Hx : Hr11 H1.
  simpljoin1.
  unfold get in H4; unfold TcbMap in H4.
  rewrite H4 in He; tryfalse.
  assert(qwaitset = wl). inverts H;eauto.
  inverts H2.
  assert (EcbMod.get ecbls eid =Some (absmsgq ml max pwl, wl) /\ In tid wl) by eauto.
  lets Hx : Hr11 H2.
  simpljoin1.
  do 3 eexists;
  rewrite TcbMod.set_sem ;
  rewrite tidspec.neq_beq_false; eauto.
  
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmsgq x y pqwaitset, qwaitset) /\ In tid qwaitset) by eauto.
  apply Hr11 in H2.
  simpljoin1.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfolds in H2; simpl in H2.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  
  intros.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  simpl in H0.
  destruct H0.
  do 4 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; auto.
  assert (EcbMod.get ecbls eid = Some (absmsgq x y pwl, qwaitset) /\ In tid pwl) by eauto.
  apply Hr1 in H0.
  simpljoin1.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H1.
  do 4 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; auto.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmsgq x y pqwaitset, qwaitset) /\ In tid pqwaitset) by eauto.
  apply Hr1 in H2.
  simpljoin1.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfolds in H2; simpl in H2.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.

  intros.
  destruct Hr1 as  (Hr11 & Hr12 & Hr13 & Hr14).
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.

(*   simpl; left; auto. *)
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr13 in H.
  simpljoin1.
  unfold get in H; unfold EcbMap in H.
  rewrite H in Ht.
  inverts Ht.
  exists ml max .
  exists (pcur::pwl). exists wl.
  splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr13 in H.
  simpljoin1.
  unfold get in H; unfold EcbMap in H.
  exists x x0 x1 x2.
  splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  exists ml max .
  exists (tid::pwl). exists wl.
  splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; eauto.
  simpl; left; auto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr1 in H.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  do 4 eexists; splits; eauto.
  unfolds in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  simpl.
  right; auto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 4 eexists; splits; eauto.
  
  splits.
  intros.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid =Some (abssem n, wls) /\ In tid wls) by eauto.
  apply Hr2 in H2.
  simpljoin1.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfolds in H2; simpl in H2.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr2 in H.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfolds in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists; splits; eauto.
  splits.
  intros.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmbox n, wls) /\ In tid wls) by eauto.
  apply Hr3 in H2.
  simpljoin1.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfolds in H2; simpl in H2.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr3 in H.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfolds in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists; splits; eauto.
  splits.
  intros.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmutexsem n1 n2, wls) /\ In tid wls) by eauto.
  apply Hr4 in H2.
  simpljoin1.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfolds in H2; simpl in H2.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr4 in H.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfolds in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; splits; eauto.

  apply Mutex_owner_hold_for_set_tcb.
  eapply Mutex_owner_set; eauto.
  intro; simpljoin1.
  unfolds in Hr4.
  simpljoin1.
  auto.
  
  destruct Hr4 as (_ & _ & _ & Hrb ).
  eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_ecb;
  try eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
  pure_auto.
  do 2 destruct H.
  inverts H.

  (* add about port *)
  splits.
  intros.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid =Some (absport, wls) /\ In tid wls) by eauto.
  apply Hr5 in H2.
  simpljoin1.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfolds in H2; simpl in H2.
  rewrite H2 in He.
  inverts He. 
  do 4 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr5 in H.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfolds in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eexists; splits; eauto.
Qed.

Lemma low_stat_q_impl_high_stat_q
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) (msg : val),
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     V_OSTCBMsg tcurl = Some msg ->
     exists prio st sus,
       TcbMod.get tcbls tcur = Some (prio, st, msg, sus).
Proof.
  introv Ht Hv.
  simpl in Ht.
  mytac.
  inverts H.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  unfolds in H.
  rewrite H in H4.
  inverts H4.
  apply tcbjoin_get_a in H1.
  do 2 eexists; eauto.
Qed.

Lemma TCBListP_head_in_tcb':
  forall tcbls tcur tcurl tcblist rtbl prio msg,
    TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
    V_OSTCBMsg tcurl = Some msg ->
     exists st sus, TcbMod.get tcbls tcur = Some (prio, st, msg, sus).
Proof.
intros.
funfold H.
fold TCBList_P in H5.
inverts H.
funfold H4.
destruct x2.
destruct p.
destruct p.
 mytac.
unfold V_OSTCBPrio, V_OSTCBMsg in *.
rewrite H in H7. inverts H7.
rewrite H0 in H6. inverts H6.
unfold TcbJoin in H3.
unfold join in H3; unfold sig in H3; simpl in H3.
do 2 eexists.
eapply TcbMod.join_get_l.
eauto.
eapply TcbMod.get_a_sig_a.
apply CltEnvMod.beq_refl.
Qed.

Lemma low_stat_q_impl_high_stat_q'
 : forall tcbls tcur tcurl tcblist rtbl prio ,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     exists st msg sus,
       TcbMod.get tcbls tcur = Some (prio, st, msg, sus).
Proof.
  introv Ht Hv.
  simpl in Ht.
  mytac.
  inverts H.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  unfolds in H0.
  rewrite H0 in H4.
  inverts H4.
  apply tcbjoin_get_a in H1.
  do 2 eexists; eauto.
Qed.

Lemma rl_rtbl_priotbl_p_set_hold:
  forall next pre eptr msg stat dly i1 i2 i3 i4 i5  v1 v3 ptbl x rtbl vhold,
    x <> vhold ->
    RL_TCBblk_P
      (next
         :: pre
         :: eptr
         :: msg
         :: stat
         :: dly
         :: Vint32 i1
         :: Vint32 i2
         :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: nil) ->
    nth_val (Z.to_nat (Int.unsigned i3)) rtbl = Some v1  ->
    or v1 (Vint32 i4) = Some v3 ->
    RL_RTbl_PrioTbl_P rtbl ptbl vhold ->
    nth_val (nat_of_Z (Int.unsigned i1)) ptbl = Some (Vptr x) ->
    RL_RTbl_PrioTbl_P (update_nth_val (Z.to_nat (Int.unsigned i3)) rtbl v3) ptbl vhold.
Proof.
  introv Hnvhold Hrl Hnth Hor Hrb Htn.
  unfolds in Hrl.
  mytac.
  simpl_hyp.
  remember ((Int.shru x0 ($ 3))) as py.
  remember ((x0&ᵢ$ 7)) as px.
  unfolds in Hor.
  destruct v1; tryfalse.
  inverts Hor.
  unfolds in Hrb.
  unfolds.
  introv Hra Hpr.
  assert (p = x0 \/ p <> x0) by tauto.
  destruct H.
  subst.
  eauto.
  eapply Hrb; eauto.
  subst py.
  eapply prio_set_rdy_in_tbl_rev with (prio:= x0); eauto.
  subst px.
  auto.
Qed.

Import TcbMod.

Lemma join_join_merge :
  forall m1 m2 m3 m4 m5,
    join m1 m2 m3 -> join m4 m5 m1 -> join m4 (merge m5 m2) m3.
Proof.
  intros.
  unfolds; intros.
  pose proof H a.
  pose proof H0 a.
  rewrite merge_sem.
  destruct(get m1 a);
  destruct(get m2 a);
  destruct(get m3 a);
  destruct(get m4 a);
  destruct(get m5 a);
  tryfalse; substs; auto.
Qed.

Lemma RL_TCBblk_P_hold_for_update :
forall tcurl,
RL_TCBblk_P tcurl ->
RL_TCBblk_P (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY)).
Proof.
intros.
funfold H.
unfold RL_TCBblk_P.
unfold V_OSTCBX,V_OSTCBPrio,V_OSTCBY,V_OSTCBBitX,V_OSTCBBitY,V_OSTCBStat,V_OSTCBEventPtr in *.
repeat eexists;
try (eapply update_nth); try (eapply nth_upd_neqrev; try pauto);
try (eapply update_nth); try (eapply nth_upd_neqrev; try pauto); try eauto.
Qed.


Lemma nth_upd_eqrev:
  forall (vl : vallist) (n m : nat) (x y : val),
    nth_val n vl = Some y ->
    nth_val n (update_nth_val n vl x) = Some x.
Proof.
  inductions vl.
  intros.
  simpl in *. tryfalse.
  
  intros; simpl in *.
  destruct n.
  simpl.
  simpl ; auto.
  simpl.
  eapply IHvl. exact n.
  eauto.
Qed.

Lemma RL_TCBblk_P_hold_for_update' :
forall tcurl,
RL_TCBblk_P tcurl ->
RL_TCBblk_P (update_nth_val 5 (update_nth_val 3 (update_nth_val 2 tcurl Vnull) Vnull ) (V$ OS_STAT_RDY)).
Proof.
intros.
funfold H.
unfold RL_TCBblk_P.
unfold V_OSTCBX,V_OSTCBPrio,V_OSTCBY,V_OSTCBBitX,V_OSTCBBitY,V_OSTCBStat,V_OSTCBEventPtr in *.
repeat eexists; 
try (eapply update_nth); try (eapply nth_upd_neqrev; try pauto);
try (eapply update_nth); try (eapply nth_upd_neqrev; try pauto); try eauto.
  eapply nth_upd_neqrev;auto.
  eapply nth_upd_neqrev;auto.
  eapply nth_upd_neqrev;auto.
  eapply nth_upd_neqrev;auto.
  eapply nth_upd_neqrev;auto.
  eapply nth_upd_eqrev;auto. exact O.
  eauto.

Qed.

Lemma TCBList_P_hold_for_update_postq_to_rdy :
forall tcbls tcur tcurl tcblist rtbl prio st msg ptbl tcbls' tcbls'' head tcblist' vhold sus,
  0 <= Int.unsigned prio < 64 ->
  array_type_vallist_match char_t rtbl ->
  length rtbl = ∘ OS_RDY_TBL_SIZE ->
V_OSTCBDly tcurl = Some (Vint32 Int.zero) ->
TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
R_PrioTbl_P ptbl tcbls'' vhold ->
TcbMod.join tcbls' tcbls tcbls'' ->
TCBList_P head tcblist' rtbl tcbls' ->
TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
TCBList_P (Vptr tcur) 
                      ((update_nth_val 5 ( update_nth_val 3 (update_nth_val 2 tcurl Vnull) Vnull) (V$ OS_STAT_RDY))::tcblist) 
                       (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                                (val_inj
                                 (or (nth_val' (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl) (Vint32 ($ 1<<ᵢ(prio &ᵢ$ 7)))))
                             )
(TcbMod.set tcbls tcur (prio, rdy, Vnull, false)).
Proof.
  simpl TCBList_P.
  intros.
  destruct H7 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
  destruct asbs'.
  destruct p.
  destruct p.
  exists td' vv' tcblss' (prio, rdy, Vnull, false).
  inverts Hveq'.
    unfold sig in *. unfold TcbMap in *.
  assert (Heq1: (prio, st, msg, sus) = (p, t, m, s)).
  eapply TcbMod.map_get_unique.
  eauto.
  eapply TcbMod.join_sig_get. eauto.
  inverts Heq1.
  lets Hex :   int_usigned_tcb_range H.
    destruct Hex as (He1 & He2).
    assert (He1': 0 <= Int.unsigned (p >>ᵢ $ 3) <= 7) by auto with zarith.
      lets Hgrp: array_type_match_get_value He1' H0 H1.
      destruct Hgrp as [grp]. rename H7 into Hgrp.
  splits; try auto.
  unfold V_OSTCBNext in *;
  try (eapply nth_upd_neqrev; try pauto);
  try (eapply nth_upd_neqrev; try pauto);
  try (eapply nth_upd_neqrev; try pauto).
  unfold TcbMod.join in *.
  intros.
  specialize Htcj' with (a:= a).
  erewrite TcbMod.sig_sem in *.
  rewrite TcbMod.set_sem in *.
  pure_auto.
  Focus 2.
  eapply TCBList_P_rtbl_add_lemma_2; try pauto.
  auto with zarith.
  fold nat_of_Z.
  eapply TCBList_P_rtbl_add_simpl_version; try eauto.
  lets Hget: TcbMod.join_get_r H5 H3.
  lets Hjs: TcbMod.map_join_get_sig Hget.
  destruct Hjs as [x'].
  apply TcbMod.map_join_comm in H5.
  apply TcbMod.map_join_comm in Htcj'.
  lets Hjoin: join_join_merge H5 Htcj'.
  apply TcbMod.map_join_comm in Hjoin.
  eapply TCBList_P_rtbl_add_lemma_1.
  eauto.
  apply TcbMod.map_join_comm.
  apply TcbMod.join_merge_disj.
  eapply TcbMod.join_join_disj_r. eauto. eauto.
  unfold TcbJoin.
  auto with jdb. 
  unfold TcbJoin.
  unfold join. unfold sig. unfold TcbMap. eauto.
  funfold H4. auto.
  (*  TCBNode_P *)
  destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
  unfold TCBNode_P.
  unfold V_OSTCBMsg,V_OSTCBPrio in *.
  splits.
  try (eapply nth_upd_neqrev; try pauto). 
  try (eapply nth_upd_eqrev; try pauto). exact O.
  try (eapply nth_upd_neqrev; try pauto).
  try (eapply nth_upd_neqrev; try pauto).  
    try (eapply nth_upd_neqrev; try pauto).
      try (eapply nth_upd_neqrev; try pauto).
  try (eapply nth_upd_neqrev; try pauto).
  
  apply RL_TCBblk_P_hold_for_update'; auto.

    funfold Hrtsl'.
    lets Hgrp': nth_val_nth_val'_some_eq Hgrp.
  rewrite Hgrp'.
  unfold or. simpl val_inj.

  unfold R_TCB_Status_P.
  splits. unfold RLH_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  assert (Hneq1: 6%nat <> 5%nat /\ 6%nat <> 3%nat /\ 6%nat <> 2%nat /\ 4%nat <> 5%nat /\ 4%nat <> 2%nat) by pauto.
  destruct Hneq1 as (nq1 & nq2 & nq3 & nq4& nq5).
  destruct H2.
  lets Heq1: nth_upd_neq nq1 H2.
  lets Heq2: nth_upd_neq nq2 Heq1.
  lets Heq3: nth_upd_neq nq3 Heq2.
  rewrite Heq3 in Hvp.
  inverts Hvp.   funfold Hrsl'.
  split.
  eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto.
  left.
  split.
  eapply update_nth; try eapply nth_upd_neqrev; try eapply nth_upd_neqrev; eauto.
  eauto.

  unfold RHL_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  inverts H2.
  funfold Hrsl'.
  splits; try splits; try eapply update_nth; try eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto. eapply nth_upd_neqrev;eauto.
  eapply prio_in_tbl_orself. eapply nth_upd_neqrev;eauto.

  (* RLH_Suspend_P *)
  unfolds.
  split; introv Hwt Hst;
  eapply nth_upd_eq in Hst; inverts Hst.
 (* RHL_Suspend_P *)
  unfolds.
  split; introv Hst; inverts Hst.

  lets Hnotp: prio_notin_tbl_orself H19 Hgrp.

  unfolds.
  splits; try solve [unfolds; introv Hwt Hst; eapply nth_upd_eq in Hst; inverts Hst].

  unfolds.
  introv Hwt Hst.
  unfolds in Hwt.
  destruct Hwt as (Hp & Hf & Hdly).
  eapply nth_upd_neq in Hp; eauto.
  eapply nth_upd_neq in Hp; eauto.
  eapply nth_upd_neq in Hp; eauto.
  rewrite Hvp in Hp; inverts Hp.
  tryfalse.

  splits; try solve [unfolds; introv Hwt Hst; eapply nth_upd_eq in Hst; inverts Hst].
  splits; try solve [unfolds; introv Hwt Hst; eapply nth_upd_eq in Hst; inverts Hst].
  splits; try solve [unfolds; introv Hst; inverts Hst].
  splits; try solve [unfolds; introv Hst; inverts Hst].
Qed.

(* *** FIX ME TODO 
    Require Import OSMutexPend_pure_ext.
Lemma TCBList_P_hold_for_update_postq_to_rdy' :
forall tcbls tcur tcurl tcblist rtbl prio st msg ptbl tcbls' tcbls'' head tcblist' vhold sus,
  0 <= Int.unsigned prio < 64 ->
  array_type_vallist_match char_t rtbl ->
  length rtbl = ∘ OS_RDY_TBL_SIZE ->
V_OSTCBDly tcurl = Some (Vint32 Int.zero) ->
TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
R_PrioTbl_P ptbl tcbls'' vhold ->
TcbMod.join tcbls' tcbls tcbls'' ->
prio_in_tbl prio rtbl ->
TCBList_P head tcblist' rtbl tcbls' ->
TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
TCBList_P (Vptr tcur) 
                      ((update_nth_val 5 ( update_nth_val 3 (update_nth_val 2 tcurl Vnull) Vnull) (V$ OS_STAT_RDY))::tcblist) 
                       rtbl 
(TcbMod.set tcbls tcur (prio, rdy, Vnull, false)).
Proof.
  simpl TCBList_P.
  intros.
  destruct H8 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
  destruct asbs'.
  destruct p.
  destruct p.
  exists td' vv' tcblss' (prio, rdy, Vnull, false).
  inverts Hveq'.
    unfold sig in *. unfold TcbMap in *.
  assert (Heq1: (prio, st, msg, sus) = (p, t, m, s)).
  eapply TcbMod.map_get_unique.
  eauto.
  eapply TcbMod.join_sig_get. eauto.
  inverts Heq1.
  lets Hex :   int_usigned_tcb_range H.
    destruct Hex as (He1 & He2).
    assert (He1': 0 <= Int.unsigned (p >>ᵢ $ 3) <= 7) by auto with zarith.
      lets Hgrp: array_type_match_get_value He1' H0 H1.
      destruct Hgrp as [grp]. rename H7 into Hgrp.
  splits; try auto.
  unfold V_OSTCBNext in *;
  try (eapply nth_upd_neqrev; try pauto);
  try (eapply nth_upd_neqrev; try pauto);
  try (eapply nth_upd_neqrev; try pauto).
  unfold TcbMod.join in *.
  intros.
  specialize Htcj' with (a:= a).
  erewrite TcbMod.sig_sem in *.
  rewrite TcbMod.set_sem in *.
  pure_auto.
  (*  TCBNode_P *)
  destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
  unfold TCBNode_P.
  unfold V_OSTCBMsg,V_OSTCBPrio in *.
  splits.
  try (eapply nth_upd_neqrev; try pauto). 
  try (eapply nth_upd_eqrev; try pauto). exact O.
  try (eapply nth_upd_neqrev; try pauto).
  try (eapply nth_upd_neqrev; try pauto).  
    try (eapply nth_upd_neqrev; try pauto).
      try (eapply nth_upd_neqrev; try pauto).
  try (eapply nth_upd_neqrev; try pauto).
  
  apply RL_TCBblk_P_hold_for_update'; auto.

  unfold R_TCB_Status_P.
  splits. unfold RLH_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  assert (Hneq1: 6%nat <> 5%nat /\ 6%nat <> 3%nat /\ 6%nat <> 2%nat /\ 4%nat <> 5%nat /\ 4%nat <> 2%nat) by pauto.
  destruct Hneq1 as (nq1 & nq2 & nq3 & nq4& nq5).
  destruct H7.
  lets Heq1: nth_upd_neq nq1 H7.
  lets Heq2: nth_upd_neq nq2 Heq1.
  lets Heq3: nth_upd_neq nq3 Heq2.
  rewrite Heq3 in Hvp.
  inverts Hvp.   funfold Hrsl'.
  split.
  eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto.
  left.
  split.
  eapply update_nth; try eapply nth_upd_neqrev; try eapply nth_upd_neqrev; eauto.
  eauto.

  unfold RHL_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  inverts H7.
    unfolds in Hrtsl'. destruct Hrtsl' as (_ & Hhlrdy & _).
    unfold RHL_RdyI_P in Hhlrdy.
(*     specialize (Hhlrdy _ _ (eq_refl _)). *)
  funfold Hrsl'.
  splits; try splits; try eapply update_nth; try eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto. eapply nth_upd_neqrev;eauto.
  eapply nth_upd_neqrev;eauto.

  (* RLH_Suspend_P *)
  unfolds.
  split; introv Hwt Hst;
  eapply nth_upd_eq in Hst; inverts Hst.
 (* RHL_Suspend_P *)
  unfolds.
  split; introv Hst; inverts Hst.

  unfolds.
   splits; try unfolds; try introv Hif; try introv Hst; try introv Hptr;
   try ( unfold V_OSTCBStat in Hst; eapply nth_upd_eq in Hst; inverts Hst).
   unfold WaitTCBblk in Hif;
  destruct Hif as (Hvp' & Hw1 & _);
  assert (Hneq1: 6%nat <> 5%nat /\ 6%nat <> 3%nat /\ 6%nat <> 2%nat) by pauto;
  destruct Hneq1 as (nq1 & nq2 & nq3);
  lets Heq1: nth_upd_neq nq1 Hvp';
  lets Heq2: nth_upd_neq nq2 Heq1;
  lets Heq3: nth_upd_neq nq3 Heq2;
  rewrite Heq3 in Hvp; inverts Hvp; tryfalse.
  assert(~ (prio_in_tbl p rtbl)).
    eapply prio_not_in_tbl_imp; eauto. tryfalse.
   splits; try unfolds; try introv Hif Hst; try introv Hptr;
   try ( unfold V_OSTCBStat in Hst; eapply nth_upd_eq in Hst; inverts Hst).

  unfolds.
  splits; try solve [unfolds; introv Hst; inverts Hst].
  splits; try solve [unfolds; introv Hst; inverts Hst].
Qed. *)

Require Import Maps.

Lemma RLH_ECB_ETbl_P_hold_for_update_postq_to_st
: forall tcbls ct p qid wt msg osevent etbl petbl ey pegrp' st sus sus',
    Int.unsigned p < 64 ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_postq qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) petbl = Vint32 ey ->
    RLH_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls ->
    RLH_ECB_ETbl_P qid
     (update_nth_val 6 osevent (Vint32 pegrp'), etbl,
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) petbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))))
      (TcbMod.set tcbls ct (p, st, msg, sus')).
Proof.
introv Hpr Htg Hey Hre;
destruct Hre as (Hra1 & Hra2 & Hra3 & Hra4 & Hra5);
unfolds;
splits;
unfolds;
[ funfold Hra1 | funfold Hra2 | funfold Hra3 | funfold Hra4 | funfold Hra5].
unfold V_OSEventType in *;
intros.
eapply Hra1 in H.
simpljoin1.
exists x x0 x1.
assert (x = ct \/ x <> ct) by tauto.
destruct H1.
subst.
unfold get in H;simpl in H.
rewrite Htg in H.
inverts H.
rewrite TcbMod.set_sem;
rewrite tidspec.neq_beq_false; eauto.
unfold update_nth_val in H0.
simpl in H0.
destruct osevent.
auto.
simpl in H0.
simpl;auto.

unfold V_OSEventType in *;
intros.
eapply Hra2 in H.
simpljoin1.
exists x x0 x1.
assert (x = ct \/ x <> ct) by tauto.
destruct H1.
subst.
unfold get in H;simpl in H.
rewrite Htg in H.
inverts H.
rewrite TcbMod.set_sem;
rewrite tidspec.neq_beq_false; eauto.
unfold update_nth_val in H0.
simpl in H0.
destruct osevent.
auto.
simpl in H0.
simpl;auto.

unfold V_OSEventType in *;
intros.
eapply Hra3 in H.
simpljoin1.
exists x x0 x1.
assert (x = ct \/ x <> ct) by tauto.
destruct H1.
subst.
unfold get in H;simpl in H.
rewrite Htg in H.
inverts H.
rewrite TcbMod.set_sem;
rewrite tidspec.neq_beq_false; eauto.
unfold update_nth_val in H0.
simpl in H0.
destruct osevent.
auto.
simpl in H0.
simpl;auto.

unfold V_OSEventType in *;
intros.
eapply Hra4 in H.
simpljoin1.
exists x x0 x1.
assert (x = ct \/ x <> ct) by tauto.
destruct H1.
subst.
unfold get in H;simpl in H.
rewrite Htg in H.
inverts H.
rewrite TcbMod.set_sem;
rewrite tidspec.neq_beq_false; eauto.
unfold update_nth_val in H0.
simpl in H0.
destruct osevent.
auto.
simpl in H0.
simpl;auto.

unfold V_OSEventType in *;
intros.
eapply Hra5 in H.
simpljoin1.
exists x x0 x1.
assert (x = ct \/ x <> ct) by tauto.
destruct H1.
subst.
unfold get in H;simpl in H.
rewrite Htg in H.
inverts H.
rewrite TcbMod.set_sem;
rewrite tidspec.neq_beq_false; eauto.
unfold update_nth_val in H0.
simpl in H0.
destruct osevent.
auto.
simpl in H0.
simpl;auto.
Qed.


Lemma RLH_ECB_ETbl_P_hold_for_update_postq_to_st'
: forall tcbls ct p qid wt msg osevent etbl petbl ey pegrp' st sus sus',
    Int.unsigned p < 64 ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_postq qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) petbl = Vint32 ey ->
    RLH_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls ->
    RLH_ECB_ETbl_P qid
     (update_nth_val 6 osevent (Vint32 pegrp'), etbl,
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) petbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))))
      (TcbMod.set tcbls ct (p, st, Vnull, sus')).
Proof.
introv Hpr Htg Hey Hre;
destruct Hre as (Hra1 & Hra2 & Hra3 & Hra4 & Hra5);
unfolds;
splits;
unfolds;
[ funfold Hra1 | funfold Hra2 | funfold Hra3 | funfold Hra4 | funfold Hra5].
unfold V_OSEventType in *;
intros.
eapply Hra1 in H.
simpljoin1.
exists x x0 x1.
assert (x = ct \/ x <> ct) by tauto.
destruct H1.
subst.
unfold get in H;simpl in H.
rewrite Htg in H.
inverts H.
rewrite TcbMod.set_sem;
rewrite tidspec.neq_beq_false; eauto.
unfold update_nth_val in H0.
simpl in H0.
destruct osevent.
auto.
simpl in H0.
simpl;auto.

unfold V_OSEventType in *;
intros.
eapply Hra2 in H.
simpljoin1.
exists x x0 x1.
assert (x = ct \/ x <> ct) by tauto.
destruct H1.
subst.
unfold get in H;simpl in H.
rewrite Htg in H.
inverts H.
rewrite TcbMod.set_sem;
rewrite tidspec.neq_beq_false; eauto.
unfold update_nth_val in H0.
simpl in H0.
destruct osevent.
auto.
simpl in H0.
simpl;auto.

unfold V_OSEventType in *;
intros.
eapply Hra3 in H.
simpljoin1.
exists x x0 x1.
assert (x = ct \/ x <> ct) by tauto.
destruct H1.
subst.
unfold get in H;simpl in H.
rewrite Htg in H.
inverts H.
rewrite TcbMod.set_sem;
rewrite tidspec.neq_beq_false; eauto.
unfold update_nth_val in H0.
simpl in H0.
destruct osevent.
auto.
simpl in H0.
simpl;auto.

unfold V_OSEventType in *;
intros.
eapply Hra4 in H.
simpljoin1.
exists x x0 x1.
assert (x = ct \/ x <> ct) by tauto.
destruct H1.
subst.
unfold get in H;simpl in H.
rewrite Htg in H.
inverts H.
rewrite TcbMod.set_sem;
rewrite tidspec.neq_beq_false; eauto.
unfold update_nth_val in H0.
simpl in H0.
destruct osevent.
auto.
simpl in H0.
simpl;auto.

unfold V_OSEventType in *;
intros.
eapply Hra5 in H.
simpljoin1.
exists x x0 x1.
assert (x = ct \/ x <> ct) by tauto.
destruct H1.
subst.
unfold get in H;simpl in H.
rewrite Htg in H.
inverts H.
rewrite TcbMod.set_sem;
rewrite tidspec.neq_beq_false; eauto.
unfold update_nth_val in H0.
simpl in H0.
destruct osevent.
auto.
simpl in H0.
simpl;auto.
Qed.

Lemma RHL_ECB_ETbl_P_hold_for_update_postq_to_rdy
: forall tcbls ct p qid wt msg osevent etbl ey pegrp' ptbl vhold petbl sus sus',
    Int.unsigned p < 64 ->
    R_PrioTbl_P ptbl tcbls vhold ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_postq qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) petbl = Vint32 ey ->
    RHL_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls ->
    RHL_ECB_ETbl_P qid
     (update_nth_val 6 osevent (Vint32 pegrp'), etbl,
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) petbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))))
      (TcbMod.set tcbls ct (p, rdy, msg, sus')).
Proof.

  introv Hpr Hrpt Htg Hey Hre.
  destruct Hre as (Hra1 & Hra2 & Hra3 & Hra4 & Hra5);
  unfolds;
  splits;
  unfolds;
  [ funfold Hra1 | funfold Hra2 | funfold Hra3 | funfold Hra4 | funfold Hra5].

  unfold V_OSEventType in *.
  destruct Hrpt as (_ & _ & Hrpt).
  funfold Hrpt.
  intros.
  unfold get in *; unfold TcbMap in *.
  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H;
  try (subst;
  rewrite TcbMod.beq_refl in H;
  inverts H).
  eapply neq_set_get  with (MC := TcbMap)in H0 .
  unfold get in H0. simpl in H0.
  rewrite H0 in H.
  eapply Hra1 in H.
  destruct H.
  splits.
  auto.
  destruct osevent;
  simpl;simpl in H1;auto.
  
  unfold V_OSEventType in *.
  destruct Hrpt as (_ & _ & Hrpt).
  funfold Hrpt.
  intros.
  unfold get in *; unfold TcbMap in *.
  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H;
  try (subst;
  rewrite TcbMod.beq_refl in H;
  inverts H).
  eapply neq_set_get  with (MC := TcbMap)in H0 .
  unfold get in H0. simpl in H0.
  rewrite H0 in H.
  eapply Hra2 in H.
  destruct H.
  splits.
  auto.
  destruct osevent;
  simpl;simpl in H1;auto.
  
  unfold V_OSEventType in *.
  destruct Hrpt as (_ & _ & Hrpt).
  funfold Hrpt.
  intros.
  unfold get in *; unfold TcbMap in *.
  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H;
  try (subst;
  rewrite TcbMod.beq_refl in H;
  inverts H).
  eapply neq_set_get  with (MC := TcbMap)in H0 .
  unfold get in H0. simpl in H0.
  rewrite H0 in H.
  eapply Hra3 in H.
  destruct H.
  splits.
  auto.
  destruct osevent;
  simpl;simpl in H1;auto.
  
  unfold V_OSEventType in *.
  destruct Hrpt as (_ & _ & Hrpt).
  funfold Hrpt.
  intros.
  unfold get in *; unfold TcbMap in *.
  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H;
  try (subst;
  rewrite TcbMod.beq_refl in H;
  inverts H).
  eapply neq_set_get  with (MC := TcbMap)in H0 .
  unfold get in H0. simpl in H0.
  rewrite H0 in H.
  eapply Hra4 in H.
  destruct H.
  splits.
  auto.
  destruct osevent;
  simpl;simpl in H1;auto.
  
  unfold V_OSEventType in *.
  destruct Hrpt as (_ & _ & Hrpt).
  funfold Hrpt.
  intros.
  unfold get in *; unfold TcbMap in *.
  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H;
  try (subst;
  rewrite TcbMod.beq_refl in H;
  inverts H).
  eapply neq_set_get  with (MC := TcbMap)in H0 .
  unfold get in H0. simpl in H0.
  rewrite H0 in H.
  eapply Hra5 in H.
  destruct H.
  splits.
  auto.
  destruct osevent;
  simpl;simpl in H1;auto.
Qed.

Lemma RHL_ECB_ETbl_P_hold_for_update_postq_to_rdy'
: forall tcbls ct p qid wt msg osevent etbl ey pegrp' ptbl vhold petbl sus sus',
    Int.unsigned p < 64 ->
    R_PrioTbl_P ptbl tcbls vhold ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_postq qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) petbl = Vint32 ey ->
    RHL_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls ->
    RHL_ECB_ETbl_P qid
     (update_nth_val 6 osevent (Vint32 pegrp'), etbl,
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) petbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))))
      (TcbMod.set tcbls ct (p, rdy, Vnull, sus')).
Proof.

  introv Hpr Hrpt Htg Hey Hre.
  destruct Hre as (Hra1 & Hra2 & Hra3 & Hra4 & Hra5);
  unfolds;
  splits;
  unfolds;
  [ funfold Hra1 | funfold Hra2 | funfold Hra3 | funfold Hra4 | funfold Hra5].

  unfold V_OSEventType in *.
  destruct Hrpt as (_ & _ & Hrpt).
  funfold Hrpt.
  intros.
  unfold get in *; unfold TcbMap in *.
  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H;
  try (subst;
  rewrite TcbMod.beq_refl in H;
  inverts H).
  eapply neq_set_get  with (MC := TcbMap)in H0 .
  unfold get in H0. simpl in H0.
  rewrite H0 in H.
  eapply Hra1 in H.
  destruct H.
  splits.
  auto.
  destruct osevent;
  simpl;simpl in H1;auto.
  
  unfold V_OSEventType in *.
  destruct Hrpt as (_ & _ & Hrpt).
  funfold Hrpt.
  intros.
  unfold get in *; unfold TcbMap in *.
  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H;
  try (subst;
  rewrite TcbMod.beq_refl in H;
  inverts H).
  eapply neq_set_get  with (MC := TcbMap)in H0 .
  unfold get in H0. simpl in H0.
  rewrite H0 in H.
  eapply Hra2 in H.
  destruct H.
  splits.
  auto.
  destruct osevent;
  simpl;simpl in H1;auto.
  
  unfold V_OSEventType in *.
  destruct Hrpt as (_ & _ & Hrpt).
  funfold Hrpt.
  intros.
  unfold get in *; unfold TcbMap in *.
  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H;
  try (subst;
  rewrite TcbMod.beq_refl in H;
  inverts H).
  eapply neq_set_get  with (MC := TcbMap)in H0 .
  unfold get in H0. simpl in H0.
  rewrite H0 in H.
  eapply Hra3 in H.
  destruct H.
  splits.
  auto.
  destruct osevent;
  simpl;simpl in H1;auto.
  
  unfold V_OSEventType in *.
  destruct Hrpt as (_ & _ & Hrpt).
  funfold Hrpt.
  intros.
  unfold get in *; unfold TcbMap in *.
  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H;
  try (subst;
  rewrite TcbMod.beq_refl in H;
  inverts H).
  eapply neq_set_get  with (MC := TcbMap)in H0 .
  unfold get in H0. simpl in H0.
  rewrite H0 in H.
  eapply Hra4 in H.
  destruct H.
  splits.
  auto.
  destruct osevent;
  simpl;simpl in H1;auto.
  
  unfold V_OSEventType in *.
  destruct Hrpt as (_ & _ & Hrpt).
  funfold Hrpt.
  intros.
  unfold get in *; unfold TcbMap in *.
  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H;
  try (subst;
  rewrite TcbMod.beq_refl in H;
  inverts H).
  eapply neq_set_get  with (MC := TcbMap)in H0 .
  unfold get in H0. simpl in H0.
  rewrite H0 in H.
  eapply Hra5 in H.
  destruct H.
  splits.
  auto.
  destruct osevent;
  simpl;simpl in H1;auto.
Qed.

Lemma Event_Type_P_hold_for_update
: forall osevent v n,
    n <> 0%nat ->
    Event_Type_P osevent ->
    Event_Type_P (update_nth_val n osevent (Vint32 v)).
Proof.
unfold Event_Type_P.
unfold V_OSEventType.
intros.
destruct H0 as [H1 | [H1 | [H1 | [H1 | H1]]]];
[left | right; left | do 2 right; left | do 3 right; left | do 4 right];
eapply nth_upd_neqrev; try pauto.
Qed.

Lemma R_ECB_ETbl_P_hold_for_update_postq_to_rdy
: forall tcbls ct p qid wt msg osevent etbl petbl y ey pegrp' bitx ptbl vhold sus sus',
      Int.unsigned p < 64 ->
      y = p >>ᵢ $ 3 ->
      bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
      R_PrioTbl_P ptbl tcbls vhold ->
      TcbMod.get tcbls ct = Some (p, wait (os_stat_postq qid) wt, msg, sus) ->
      R_ECB_ETbl_P qid (osevent, etbl,petbl) tcbls ->
      nth_val' (Z.to_nat (Int.unsigned y)) petbl = Vint32 ey ->
      R_ECB_ETbl_P qid
       (update_nth_val 6 osevent (Vint32 pegrp'), etbl,
         update_nth_val (Z.to_nat (Int.unsigned y)) petbl (Vint32 (ey&ᵢInt.not bitx)))
       (TcbMod.set tcbls ct (p, rdy, msg, sus')).
Proof.
introv Hpr Hy Hbitx Hrpt Htg Hre Hey.
funfold Hre.
unfolds.
splits.
eapply RLH_ECB_ETbl_P_hold_for_update_postq_to_st; try eauto.
eapply RHL_ECB_ETbl_P_hold_for_update_postq_to_rdy; try eauto.
simpl in *.
eapply Event_Type_P_hold_for_update; try auto.
Qed.

Lemma R_ECB_ETbl_P_hold_for_update_postq_to_rdy'
: forall tcbls ct p qid wt msg osevent etbl petbl y ey pegrp' bitx ptbl vhold sus sus',
      Int.unsigned p < 64 ->
      y = p >>ᵢ $ 3 ->
      bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
      R_PrioTbl_P ptbl tcbls vhold ->
      TcbMod.get tcbls ct = Some (p, wait (os_stat_postq qid) wt, msg, sus) ->
      R_ECB_ETbl_P qid (osevent, etbl,petbl) tcbls ->
      nth_val' (Z.to_nat (Int.unsigned y)) petbl = Vint32 ey ->
      R_ECB_ETbl_P qid
       (update_nth_val 6 osevent (Vint32 pegrp'), etbl,
         update_nth_val (Z.to_nat (Int.unsigned y)) petbl (Vint32 (ey&ᵢInt.not bitx)))
       (TcbMod.set tcbls ct (p, rdy, Vnull, sus')).
Proof.
introv Hpr Hy Hbitx Hrpt Htg Hre Hey.
funfold Hre.
unfolds.
splits.
eapply RLH_ECB_ETbl_P_hold_for_update_postq_to_st'; try eauto.
eapply RHL_ECB_ETbl_P_hold_for_update_postq_to_rdy'; try eauto.
simpl in *.
eapply Event_Type_P_hold_for_update; try auto.
Qed.

Lemma RLH_ECB_PETbl_P_hold_for_update_postq_to_st
: forall tcbls ct p qid wt msg osevent etbl petbl ey pegrp' st sus sus',
    Int.unsigned p < 64 ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_postq qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) petbl = Vint32 ey ->
    RLH_ECB_PETbl_Q_P qid (osevent,etbl,petbl) tcbls ->
    RLH_ECB_PETbl_Q_P qid
     (update_nth_val 6 osevent (Vint32 pegrp'), etbl,
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) petbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))))
      (TcbMod.set tcbls ct (p, st, msg, sus')).
Proof.
  introv Hpr Htg Hey Hre;
  rename Hre into Hra1.
  unfolds. unfold RLH_ECB_PETbl_Q_P in Hra1.
  unfold V_OSEventType in *;
  intros.
  assert (Hpr1: 0 <= prio /\ prio <= Int.max_unsigned) by (funfold H; clear -H H5; int auto).
  destruct Hpr1 as (Hpr1 & Hpr2);
  lets Hvp: int_usign_eq Hpr1 Hpr2;
  rewrite <- Hvp in H;
  pose proof prio_wt_inq_tid_neq;
  specialize H1 with (prio':= $ prio);
  lets Hpi: H1 Hey Hpr;
  rewrite Hpi in H;
  clear H1 Hpi;
  rewrite Hvp in H;
  destruct H;
  assert (nq1: 0%nat <> 6%nat) by pauto.
  lets Heq1: nth_upd_neq nq1 H0.
  lets Hst: Hra1 H Heq1.
  destruct Hst as [tid]; do 3 destruct H2.
  unfold get in *; unfold TcbMap in *.
  exists tid x x0.
  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H3;
  try (subst;
  rewrite Htg in H2;
  inverts H2);
  rewrite TcbMod.set_sem;
  rewrite tidspec.neq_beq_false; eauto.
Qed.

Lemma RLH_ECB_PETbl_P_hold_for_update_postq_to_st'
: forall tcbls ct p qid wt msg osevent etbl petbl ey pegrp' st sus sus',
    Int.unsigned p < 64 ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_postq qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) petbl = Vint32 ey ->
    RLH_ECB_PETbl_Q_P qid (osevent,etbl,petbl) tcbls ->
    RLH_ECB_PETbl_Q_P qid
     (update_nth_val 6 osevent (Vint32 pegrp'), etbl,
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) petbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))))
      (TcbMod.set tcbls ct (p, st, Vnull, sus')).
Proof.
  introv Hpr Htg Hey Hre;
  rename Hre into Hra1.
  unfolds. unfold RLH_ECB_PETbl_Q_P in Hra1.
  unfold V_OSEventType in *;
  intros.
  assert (Hpr1: 0 <= prio /\ prio <= Int.max_unsigned) by (funfold H; clear -H H5; int auto).
  destruct Hpr1 as (Hpr1 & Hpr2);
  lets Hvp: int_usign_eq Hpr1 Hpr2;
  rewrite <- Hvp in H;
  pose proof prio_wt_inq_tid_neq;
  specialize H1 with (prio':= $ prio);
  lets Hpi: H1 Hey Hpr;
  rewrite Hpi in H;
  clear H1 Hpi;
  rewrite Hvp in H;
  destruct H;
  assert (nq1: 0%nat <> 6%nat) by pauto.
  lets Heq1: nth_upd_neq nq1 H0.
  lets Hst: Hra1 H Heq1.
  destruct Hst as [tid]; do 3 destruct H2.
  unfold get in *; unfold TcbMap in *.
  exists tid x x0.
  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H3;
  try (subst;
  rewrite Htg in H2;
  inverts H2);
  rewrite TcbMod.set_sem;
  rewrite tidspec.neq_beq_false; eauto.
Qed.


Lemma RHL_ECB_PETbl_P_hold_for_update_postq_to_rdy
: forall tcbls ct p qid wt msg osevent etbl ey pegrp' ptbl vhold petbl sus sus',
    Int.unsigned p < 64 ->
    R_PrioTbl_P ptbl tcbls vhold ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_postq qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) petbl = Vint32 ey ->
    RHL_ECB_PETbl_Q_P qid (osevent,etbl,petbl) tcbls ->
    RHL_ECB_PETbl_Q_P qid
     (update_nth_val 6 osevent (Vint32 pegrp'), etbl,
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) petbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))))
      (TcbMod.set tcbls ct (p, rdy, msg, sus')).
Proof.
  introv Hpr Hrpt Htg Hey Hre.
  rename Hre into Hra1.
  unfolds. unfold RHL_ECB_PETbl_Q_P in Hra1.
  unfold V_OSEventType in *.
destruct Hrpt as (_ & _ & Hrpt).
funfold Hrpt;
intros;
unfold get in *; unfold TcbMap in *;
assert (tid = ct \/ tid <> ct) by tauto;
destruct H0;
rewrite TcbMod.set_sem in H;
try (subst;
rewrite TcbMod.beq_refl in H;
inverts H);
rewrite tidspec.neq_beq_false in H; try auto;
pose proof prio_wt_inq_tid_neq;
specialize H1 with (prio':= prio);
lets Hpi: H1 Hey Hpr;
rewrite Hpi;
clear Hpi;
lets Hnp: Hrpt H0 H Htg;
try eapply Hra1 in H .
splits; try eapply nth_upd_neqrev; try pauto.
Qed.

Lemma RHL_ECB_PETbl_P_hold_for_update_postq_to_rdy'
: forall tcbls ct p qid wt msg osevent etbl ey pegrp' ptbl vhold petbl sus sus',
    Int.unsigned p < 64 ->
    R_PrioTbl_P ptbl tcbls vhold ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_postq qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) petbl = Vint32 ey ->
    RHL_ECB_PETbl_Q_P qid (osevent,etbl,petbl) tcbls ->
    RHL_ECB_PETbl_Q_P qid
     (update_nth_val 6 osevent (Vint32 pegrp'), etbl,
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) petbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))))
      (TcbMod.set tcbls ct (p, rdy, Vnull, sus')).
Proof.
  introv Hpr Hrpt Htg Hey Hre.
  rename Hre into Hra1.
  unfolds. unfold RHL_ECB_PETbl_Q_P in Hra1.
  unfold V_OSEventType in *.
destruct Hrpt as (_ & _ & Hrpt).
funfold Hrpt;
intros;
unfold get in *; unfold TcbMap in *;
assert (tid = ct \/ tid <> ct) by tauto;
destruct H0;
rewrite TcbMod.set_sem in H;
try (subst;
rewrite TcbMod.beq_refl in H;
inverts H);
rewrite tidspec.neq_beq_false in H; try auto;
pose proof prio_wt_inq_tid_neq;
specialize H1 with (prio':= prio);
lets Hpi: H1 Hey Hpr;
rewrite Hpi;
clear Hpi;
lets Hnp: Hrpt H0 H Htg;
try eapply Hra1 in H .
splits; try eapply nth_upd_neqrev; try pauto.
Qed.

Lemma R_ECB_PETbl_P_hold_for_update_postq_to_rdy
: forall tcbls ct p qid wt msg osevent etbl petbl y ey pegrp' bitx ptbl vhold sus sus',
      Int.unsigned p < 64 ->
      y = p >>ᵢ $ 3 ->
      bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
      R_PrioTbl_P ptbl tcbls vhold ->
      TcbMod.get tcbls ct = Some (p, wait (os_stat_postq qid) wt, msg, sus) ->
      R_ECB_PETbl_P qid (osevent, etbl,petbl) tcbls ->
      nth_val' (Z.to_nat (Int.unsigned y)) petbl = Vint32 ey ->
      R_ECB_PETbl_P qid
       (update_nth_val 6 osevent (Vint32 pegrp'), etbl,
         update_nth_val (Z.to_nat (Int.unsigned y)) petbl (Vint32 (ey&ᵢInt.not bitx)))
       (TcbMod.set tcbls ct (p, rdy, msg, sus')).
Proof.
introv Hpr Hy Hbitx Hrpt Htg Hre Hey.
funfold Hre.
unfolds.
splits.
eapply RLH_ECB_PETbl_P_hold_for_update_postq_to_st; try eauto.
eapply RHL_ECB_PETbl_P_hold_for_update_postq_to_rdy; try eauto.
Qed.

Lemma R_ECB_PETbl_P_hold_for_update_postq_to_rdy'
: forall tcbls ct p qid wt msg osevent etbl petbl y ey pegrp' bitx ptbl vhold sus sus',
      Int.unsigned p < 64 ->
      y = p >>ᵢ $ 3 ->
      bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
      R_PrioTbl_P ptbl tcbls vhold ->
      TcbMod.get tcbls ct = Some (p, wait (os_stat_postq qid) wt, msg, sus) ->
      R_ECB_PETbl_P qid (osevent, etbl,petbl) tcbls ->
      nth_val' (Z.to_nat (Int.unsigned y)) petbl = Vint32 ey ->
      R_ECB_PETbl_P qid
       (update_nth_val 6 osevent (Vint32 pegrp'), etbl,
         update_nth_val (Z.to_nat (Int.unsigned y)) petbl (Vint32 (ey&ᵢInt.not bitx)))
       (TcbMod.set tcbls ct (p, rdy, Vnull, sus')).
Proof.
introv Hpr Hy Hbitx Hrpt Htg Hre Hey.
funfold Hre.
unfolds.
splits.
eapply RLH_ECB_PETbl_P_hold_for_update_postq_to_st'; try eauto.
eapply RHL_ECB_PETbl_P_hold_for_update_postq_to_rdy'; try eauto.
Qed.

Lemma EcbMod_get_join_sig_set:
forall  qls qid a qls1 b,
  EcbMod.join (EcbMod.sig qid b) qls1 qls ->
  EcbMod.get qls1 qid = None ->
  EcbMod.join (EcbMod.sig qid a) qls1 (EcbMod.set qls qid a).
Proof.
  intros.
  unfold EcbMod.join.
  intros.
  rewrite EcbMod.sig_sem.
  rewrite EcbMod.set_sem.
  assert (qid = a0 \/ qid <> a0) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.beq_refl.
  rewrite H0. auto.
  eapply tidspec.neq_beq_false in H1.
  rewrite H1.
  destruct (EcbMod.get qls1 a0) eqn: eq2.
  lets Htg: EcbMod.join_get_r H  eq2.
  rewrite Htg.
  auto.
  assert (EcbMod.get qls a0 = EcbMod.get qls1 a0).
  eapply EcbMod.map_join_get_none; try eauto.
  rewrite EcbMod.sig_sem.
  rewrite H1. auto.
  rewrite H2. rewrite eq2. auto.
Qed.

Lemma RLH_ECBData_P_hold_postq
: forall n ct w ecbcurl m pw,
  RLH_ECBData_P ecbcurl (absmsgq m n pw, w) ->
RLH_ECBData_P ecbcurl (absmsgq m n ( remove_tid ct pw), w).
Proof.
  intros.
  unfolds.
  unfolds in H.
  destruct ecbcurl; try tryfalse.
  splits; pauto.
  simpl in *.
  mytac.
  splits; intros.
  apply H2 in H6. auto.
  apply H3 in H6. auto.
  apply H4 in H6. 
  destruct pw.
  simpl;auto.
  inverts H6.
  eapply H5;auto.
  destruct pw.
  simpl in H6;tryfalse. auto.
Qed.

Lemma ECBList_P_high_tcb_block_hold_postq_to_rdy:
  forall  ectrl head tail msgql ecbls tcbls ptcb prio  m qid time sus sus',
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, wait (os_stat_postq qid) time, m, sus) ->
    EcbMod.get ecbls qid = None ->
    ECBList_P head tail ectrl msgql ecbls 
              (TcbMod.set tcbls ptcb (prio, rdy, m, sus')).
Proof.
  inductions ectrl.
  intros.
  simpl.
  simpl in H.
  auto.
  intros.
  simpl in H.
  mytac.
  destruct msgql; tryfalse.
  destruct a.
  destruct p.
  mytac.
  simpl.
  exists x.
  splits; auto.
  unfolds.
  destruct H2 as (Hr1 & Hr2 & Hr3).
  destruct Hr1 as (Hra3 & Hra1 & Hra2 & Hra4 & Hra5).
  destruct Hr2 as (Hrb3 & Hrb1 & Hrb2 & Hrb4 & Hrb5).
  simpl in Hr3.
  splits.
  unfolds.
  splits;
  unfolds;
  intros;
  rename H3 into H3';
  rename H4 into H3;
  rename H5 into H4;
  rename H6 into H5;
  rename H7 into H6;
  [eapply Hra3 in H6 | eapply Hra1 in H6 | eapply Hra2 in H6 | eapply Hra4 in H6 | eapply Hra5 in H6];
  mytac;
   assert (x3 = ptcb \/ x3 <> ptcb) by tauto;
  destruct H7;
  try (subst;
    unfold get in H6; simpl in H6;
    rewrite H0 in H6;
    inverts H6;
    eapply EcbMod.join_sig_get in H3;
    rewrite H3 in H1;
    inverts H1);
    try (subst;
    unfold get in H6; simpl in H6;
    rewrite H0 in H6;
    inverts H6);
    repeat eexists;
    rewrite TcbMod.set_sem;
    rewrite tidspec.neq_beq_false; eauto.
   rename H3 into H3';
  rename H4 into H3;
  rename H5 into H4;
  rename H6 into H5;
  unfolds;
  splits;
  unfolds;
  intros;
  assert (tid = ptcb \/ tid <> ptcb) by tauto;
    destruct H6;
    try subst;
    rewrite TcbMod.set_sem in H2;
    try (rewrite TcbMod.beq_refl in H2; inverts H2);
    rewrite tidspec.neq_beq_false in H2; eauto.
    simpl; auto.
    
  unfolds;
  splits;
  unfolds;
  intros.
  unfold R_ECB_PETbl_P in H3.
  simpljoin1.
  unfold RLH_ECB_PETbl_Q_P in H3.
  eapply H3 in H7.
  2:eauto.
  simpljoin1.
  exists x3 x4 x5.
  assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
  destruct H10.
  subst.
  unfold get in H7;simpl in H7.
  rewrite H0 in H7.
  inverts H7.
  eapply EcbMod.join_sig_get in H4.
    rewrite H4 in H1;
    inverts H1.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false. eauto.
  eauto.
  unfold R_ECB_PETbl_P in H3.
  simpljoin1.
  unfold RHL_ECB_PETbl_Q_P in H8.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H9.
  subst.
  rewrite TcbMod.set_sem in H7.
  rewrite TcbMod.beq_refl in H7; inverts H7.
  rewrite TcbMod.set_sem in H7.
  rewrite tidspec.neq_beq_false in H7; eauto.
  do 3 eexists; splits; eauto.
  eapply IHectrl; eauto.
  eapply  ecbmod_joinsig_get_none; eauto.
Qed.

Lemma ECBList_P_high_tcb_block_hold_postq_to_rdy':
  forall  ectrl head tail msgql ecbls tcbls ptcb prio  m qid time sus sus',
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, wait (os_stat_postq qid) time, m, sus) ->
    EcbMod.get ecbls qid = None ->
    ECBList_P head tail ectrl msgql ecbls 
              (TcbMod.set tcbls ptcb (prio, rdy, Vnull, sus')).
Proof.
  inductions ectrl.
  intros.
  simpl.
  simpl in H.
  auto.
  intros.
  simpl in H.
  mytac.
  destruct msgql; tryfalse.
  destruct a.
  destruct p.
  mytac.
  simpl.
  exists x.
  splits; auto.
  unfolds.
  destruct H2 as (Hr1 & Hr2 & Hr3).
  destruct Hr1 as (Hra3 & Hra1 & Hra2 & Hra4 & Hra5).
  destruct Hr2 as (Hrb3 & Hrb1 & Hrb2 & Hrb4 & Hrb5).
  simpl in Hr3.
  splits.
  unfolds.
  splits;
  unfolds;
  intros;
  rename H3 into H3';
  rename H4 into H3;
  rename H5 into H4;
  rename H6 into H5;
  rename H7 into H6;
  [eapply Hra3 in H6 | eapply Hra1 in H6 | eapply Hra2 in H6 | eapply Hra4 in H6 | eapply Hra5 in H6];
  mytac;
   assert (x3 = ptcb \/ x3 <> ptcb) by tauto;
  destruct H7;
  try (subst;
    unfold get in H6; simpl in H6;
    rewrite H0 in H6;
    inverts H6;
    eapply EcbMod.join_sig_get in H3;
    rewrite H3 in H1;
    inverts H1);
    try (subst;
    unfold get in H6; simpl in H6;
    rewrite H0 in H6;
    inverts H6);
    repeat eexists;
    rewrite TcbMod.set_sem;
    rewrite tidspec.neq_beq_false; eauto.
   rename H3 into H3';
  rename H4 into H3;
  rename H5 into H4;
  rename H6 into H5;
  unfolds;
  splits;
  unfolds;
  intros;
  assert (tid = ptcb \/ tid <> ptcb) by tauto;
    destruct H6;
    try subst;
    rewrite TcbMod.set_sem in H2;
    try (rewrite TcbMod.beq_refl in H2; inverts H2);
    rewrite tidspec.neq_beq_false in H2; eauto.
    simpl; auto.
    
  unfolds;
  splits;
  unfolds;
  intros.
  unfold R_ECB_PETbl_P in H3.
  simpljoin1.
  unfold RLH_ECB_PETbl_Q_P in H3.
  eapply H3 in H7.
  2:eauto.
  simpljoin1.
  exists x3 x4 x5.
  assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
  destruct H10.
  subst.
  unfold get in H7;simpl in H7.
  rewrite H0 in H7.
  inverts H7.
  eapply EcbMod.join_sig_get in H4.
    rewrite H4 in H1;
    inverts H1.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false. eauto.
  eauto.
  unfold R_ECB_PETbl_P in H3.
  simpljoin1.
  unfold RHL_ECB_PETbl_Q_P in H8.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H9.
  subst.
  rewrite TcbMod.set_sem in H7.
  rewrite TcbMod.beq_refl in H7; inverts H7.
  rewrite TcbMod.set_sem in H7.
  rewrite tidspec.neq_beq_false in H7; eauto.
  do 3 eexists; splits; eauto.
  eapply IHectrl; eauto.
  eapply  ecbmod_joinsig_get_none; eauto.
Qed.

Lemma get_last_prop:
  forall (l : list EventCtr)  x v y,
    l <> nil -> 
    (get_last_ptr ((x, v) :: l)  =   y <->
     get_last_ptr  l =  y).
Proof.
  destruct l.
  intros.
  tryfalse.
  intros.
  unfolds get_last_ptr.
  simpl.
  destruct l; splits;auto.
Qed.

Lemma get_ectr_sing:
  forall qid head (els1: list os_inv.EventCtr) osevent etbl petbl,
    els1 <> nil ->
    get_ectr (Vptr qid) head els1  = None ->
    get_ectr (Vptr qid) head (els1 ++ ((osevent,etbl,petbl) :: nil))  = Some (osevent,etbl,petbl) ->
    get_last_ptr els1 = Some (Vptr qid).
Proof.
induction els1.
intros.
tryfalse.
induction els1.
unfold get_last_ptr.
simpl.
intros.
destruct a.
destruct p.
destruct head;
try inverts H1.
destruct (beq_addrval qid a); try tryfalse.
destruct (V_OSEventListPtr v0); try tryfalse.
destruct v2; try tryfalse.
destruct (beq_addrval qid a0) eqn: eq1.
apply beq_addrval_eq in eq1.
subst. auto.
destruct (V_OSEventListPtr osevent); try tryfalse.
destruct v2; try tryfalse.
intros.
destruct a.
destruct p.
assert (Hn: (a0 :: els1) <> nil) by pauto.
eapply (get_last_prop) in Hn.
erewrite Hn.
destruct a0.
destruct p.
eapply IHels1; try pauto;
clear IHels0 IHels1 Hn;
simpl in *;
destruct head; try tryfalse; try auto;
destruct (beq_addrval qid a) eqn: eq1; try tryfalse;
destruct (V_OSEventListPtr v3); try auto; try tryfalse;
destruct (V_OSEventListPtr v0); try tryfalse;
destruct v6; try tryfalse;
destruct (beq_addrval qid a0) eqn: eq2; try tryfalse; try eauto.
Qed.

Lemma ecblist_p_decompose' :
  forall  y1 z1  x y2 z2 t z ,
    length y1 = length y2 ->
    ECBList_P x Vnull (y1++z1) (y2++z2) t z ->
    exists x1 t1 t2,
      ECBList_P x x1 y1 y2 t1 z /\ ECBList_P x1 Vnull z1 z2 t2 z /\
      EcbMod.join t1 t2 t /\  (get_last_ptr y1 = None \/ get_last_ptr y1  = Some x1).
Proof.
  inductions y1; inductions y2.
  simpl.
  intros.
  do 3 eexists; splits; eauto.
  eapply EcbMod.join_emp; eauto.
  intros.
  simpl in H.
  tryfalse.
  intros.
  simpl in H; tryfalse.
  intros.
  simpl in H.
  inverts H.
  simpl in H0.
  DeprecatedTactic.mytac.
  rename H1 into HP.
  destruct a.
  destruct p.
  DeprecatedTactic.mytac.
  lets Hx : IHy1 H2 H4.
  mytac.
  lets Hex : joinsig_join_ex H1 H7.
  mytac.
  do 3 eexists.
  splits.
  simpl.
  eexists; splits; eauto.
  do 3 eexists; splits.
  eauto.
  2: eauto.
  3: eauto.
  2 : eauto.
  eauto.
  eauto.
  assert (y1 = nil \/ y1 <> nil) by tauto.
  destruct H11.
  subst y1.  
  right.
  simpl in H2.
  apply eq_sym in H2.
  apply length_zero_nil in H2.
  subst y2.
  simpl in H5.
  DeprecatedTactic.mytac.
  unfolds.
  simpl.
  auto.
  destruct H8.
  left.
  eapply  get_last_prop in H11.
  eapply H11; eauto.
  eapply  get_last_prop in H11.
  right.
  eapply H11; eauto.
Qed.  

Lemma ECBList_P_hold_for_update_postq_to_rdy
: forall head (els1 els2: list os_inv.EventCtr) osevent etbl osevent' petbl petbl' ecblist1 ecblist2 ecbcurl ecbls 
              tcbls ct p wt msg ey pegrp' y bitx qid ptbl vhold ml size pwl wls sus sus',
    Int.unsigned p < 64 ->
   y = p >>ᵢ $ 3 ->
   bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
  R_PrioTbl_P ptbl tcbls vhold ->
  length els1 = length ecblist1 ->
  RH_TCBList_ECBList_P ecbls tcbls ct ->
  TcbMod.get tcbls ct = Some (p, wait (os_stat_postq qid) wt, msg, sus) ->
  EcbMod.get ecbls qid = Some (absmsgq ml size pwl, wls) ->
  In ct pwl ->
  get_ectr (Vptr qid) head els1  = None ->
  get_ectr (Vptr qid) head (els1 ++ ((osevent,etbl,petbl) :: nil))  = Some (osevent,etbl,petbl) ->
  ECBList_P head Vnull (els1 ++ ((osevent,etbl,petbl) :: nil) ++ els2) 
                        (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2) ecbls tcbls ->
  nth_val' (Z.to_nat (Int.unsigned y)) petbl = Vint32 ey ->
  osevent' = update_nth_val 6 osevent (Vint32 pegrp') ->
  petbl' = update_nth_val (Z.to_nat (Int.unsigned y)) petbl (Vint32 (ey&ᵢInt.not bitx)) ->
  ECBList_P head Vnull (els1 ++ ((osevent',etbl,petbl') :: nil) ++ els2) 
                        (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2)
                         (EcbMod.set ecbls qid (absmsgq ml size (remove_tid ct pwl), wls))
                        (TcbMod.set tcbls ct (p, rdy, msg, sus')).
Proof.

  introv Hpr Hy Hbitx Hrpt Hl Hrte Htg Heg Hi Hgptr1.
  introv Hgptr2 Hep Hey Het' Hpetbl'.
  assert (Hels1: els1 = nil \/ els1 <> nil) by tauto.
  destruct Hels1.
  subst els1.
  assert (ecblist1 = nil) by (eapply length_zero_nil; simpl in *; auto).
  subst ecblist1.
  simpl in *.
  mytac.
  destruct (beq_addrval qid x) eqn: eq1.
  Focus 2.
  destruct (V_OSEventListPtr osevent); try tryfalse; destruct v; try tryfalse.
  apply beq_addrval_eq in eq1.
  subst x.
  exists qid.
  splits; try auto.
  eapply R_ECB_ETbl_P_hold_for_update_postq_to_rdy; try eauto.
  eapply R_ECB_PETbl_P_hold_for_update_postq_to_rdy; try eauto.
  exists  (absmsgq ml size (remove_tid ct pwl), wls) x1 x2.
  splits; try auto.
  unfold V_OSEventListPtr in *.
  eapply nth_upd_neqrev; try pauto.
  unfold sig. unfold EcbMap.
  eapply EcbMod_get_join_sig_set; try eauto.
  eapply ejoin_get_none_r; [idtac | eauto].
  eapply EcbMod.map_get_sig.
  lets Heg': EcbMod.join_sig_get H3.
  destruct x0.
  rewrite Heg in Heg'.
  inverts Heg'.
  eapply RLH_ECBData_P_hold_postq; auto.
  eapply ECBList_P_high_tcb_block_hold_postq_to_rdy; try eauto.
  eapply ejoin_get_none_r; [idtac | eauto].
  eapply EcbMod.map_get_sig.
  (* els1 <> nil *)
  lets Hsp: ecblist_p_decompose' Hl Hep.
  simpl in *.
  mytac.
  lets Hx2: get_ectr_sing H Hgptr1 Hgptr2.
  destruct H3;rewrite H1 in Hx2; inverts Hx2.
  eapply ecblist_p_compose; try eauto.
  Focus 2.
  eapply ECBList_P_high_tcb_block_hold_postq_to_rdy; try eauto.
  eapply ejoin_get_none_l; [idtac | eauto].
  eapply EcbMod.join_sig_get;eauto.
  eapply EcbMod.my_joinsig_join_set; try eauto.
  simpl.
  exists qid.
  splits; try auto.
  eapply R_ECB_ETbl_P_hold_for_update_postq_to_rdy; try eauto.
  eapply R_ECB_PETbl_P_hold_for_update_postq_to_rdy; try eauto.
exists (absmsgq ml size (remove_tid ct pwl), wls) x4 x5.
  splits; try auto.
  unfold V_OSEventListPtr in *.
  eapply nth_upd_neqrev; try pauto.
  unfold sig. unfold EcbMap.
  eapply EcbMod_get_join_sig_set; try eauto.
  eapply ejoin_get_none_r; [idtac | eauto].
  eapply EcbMod.map_get_sig.
  lets Heg': EcbMod.join_sig_get H7.
  destruct x3.
  lets Heg2: EcbMod.join_get_r H2 Heg'.
  rewrite Heg in Heg2.
  inverts Heg2.
  eapply RLH_ECBData_P_hold_postq; auto.
  eapply ECBList_P_high_tcb_block_hold_postq_to_rdy; try eauto.
  eapply ejoin_get_none_r; [idtac | eauto].
  eapply EcbMod.map_get_sig.
Qed.

Lemma ECBList_P_hold_for_update_postq_to_rdy'
: forall head (els1 els2: list os_inv.EventCtr) osevent etbl osevent' petbl petbl' ecblist1 ecblist2 ecbcurl ecbls 
              tcbls ct p wt msg ey pegrp' y bitx qid ptbl vhold ml size pwl wls sus sus',
    Int.unsigned p < 64 ->
   y = p >>ᵢ $ 3 ->
   bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
  R_PrioTbl_P ptbl tcbls vhold ->
  length els1 = length ecblist1 ->
  RH_TCBList_ECBList_P ecbls tcbls ct ->
  TcbMod.get tcbls ct = Some (p, wait (os_stat_postq qid) wt, msg, sus) ->
  EcbMod.get ecbls qid = Some (absmsgq ml size pwl, wls) ->
  In ct pwl ->
  get_ectr (Vptr qid) head els1  = None ->
  get_ectr (Vptr qid) head (els1 ++ ((osevent,etbl,petbl) :: nil))  = Some (osevent,etbl,petbl) ->
  ECBList_P head Vnull (els1 ++ ((osevent,etbl,petbl) :: nil) ++ els2) 
                        (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2) ecbls tcbls ->
  nth_val' (Z.to_nat (Int.unsigned y)) petbl = Vint32 ey ->
  osevent' = update_nth_val 6 osevent (Vint32 pegrp') ->
  petbl' = update_nth_val (Z.to_nat (Int.unsigned y)) petbl (Vint32 (ey&ᵢInt.not bitx)) ->
  ECBList_P head Vnull (els1 ++ ((osevent',etbl,petbl') :: nil) ++ els2) 
                        (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2)
                         (EcbMod.set ecbls qid (absmsgq ml size (remove_tid ct pwl), wls))
                        (TcbMod.set tcbls ct (p, rdy, Vnull, sus')).
Proof.

  introv Hpr Hy Hbitx Hrpt Hl Hrte Htg Heg Hi Hgptr1.
  introv Hgptr2 Hep Hey Het' Hpetbl'.
  assert (Hels1: els1 = nil \/ els1 <> nil) by tauto.
  destruct Hels1.
  subst els1.
  assert (ecblist1 = nil) by (eapply length_zero_nil; simpl in *; auto).
  subst ecblist1.
  simpl in *.
  mytac.
  destruct (beq_addrval qid x) eqn: eq1.
  Focus 2.
  destruct (V_OSEventListPtr osevent); try tryfalse; destruct v; try tryfalse.
  apply beq_addrval_eq in eq1.
  subst x.
  exists qid.
  splits; try auto.
  eapply R_ECB_ETbl_P_hold_for_update_postq_to_rdy'; try eauto.
  eapply R_ECB_PETbl_P_hold_for_update_postq_to_rdy'; try eauto.
  exists  (absmsgq ml size (remove_tid ct pwl), wls) x1 x2.
  splits; try auto.
  unfold V_OSEventListPtr in *.
  eapply nth_upd_neqrev; try pauto.
  unfold sig. unfold EcbMap.
  eapply EcbMod_get_join_sig_set; try eauto.
  eapply ejoin_get_none_r; [idtac | eauto].
  eapply EcbMod.map_get_sig.
  lets Heg': EcbMod.join_sig_get H3.
  destruct x0.
  rewrite Heg in Heg'.
  inverts Heg'.
  eapply RLH_ECBData_P_hold_postq; auto.
  eapply ECBList_P_high_tcb_block_hold_postq_to_rdy'; try eauto.
  eapply ejoin_get_none_r; [idtac | eauto].
  eapply EcbMod.map_get_sig.
  (* els1 <> nil *)
  lets Hsp: ecblist_p_decompose' Hl Hep.
  simpl in *.
  mytac.
  lets Hx2: get_ectr_sing H Hgptr1 Hgptr2.
  destruct H3;rewrite H1 in Hx2; inverts Hx2.
  eapply ecblist_p_compose; try eauto.
  Focus 2.
  eapply ECBList_P_high_tcb_block_hold_postq_to_rdy'; try eauto.
  eapply ejoin_get_none_l; [idtac | eauto].
  eapply EcbMod.join_sig_get;eauto.
  eapply EcbMod.my_joinsig_join_set; try eauto.
  simpl.
  exists qid.
  splits; try auto.
  eapply R_ECB_ETbl_P_hold_for_update_postq_to_rdy'; try eauto.
  eapply R_ECB_PETbl_P_hold_for_update_postq_to_rdy'; try eauto.
exists (absmsgq ml size (remove_tid ct pwl), wls) x4 x5.
  splits; try auto.
  unfold V_OSEventListPtr in *.
  eapply nth_upd_neqrev; try pauto.
  unfold sig. unfold EcbMap.
  eapply EcbMod_get_join_sig_set; try eauto.
  eapply ejoin_get_none_r; [idtac | eauto].
  eapply EcbMod.map_get_sig.
  lets Heg': EcbMod.join_sig_get H7.
  destruct x3.
  lets Heg2: EcbMod.join_get_r H2 Heg'.
  rewrite Heg in Heg2.
  inverts Heg2.
  eapply RLH_ECBData_P_hold_postq; auto.
  eapply ECBList_P_high_tcb_block_hold_postq_to_rdy'; try eauto.
  eapply ejoin_get_none_r; [idtac | eauto].
  eapply EcbMod.map_get_sig.
Qed.

Lemma rh_tcblist_ecblist_mutex_owner_set'_rmpwl:
  forall els tls t ml size pwl wl eid,
    RH_TCBList_ECBList_MUTEX_OWNER els tls ->
    EcbMod.get els eid = Some (absmsgq ml size pwl, wl) ->
    RH_TCBList_ECBList_MUTEX_OWNER (EcbMod.set els eid (absmsgq ml size (remove_tid t pwl),  wl)) tls .
Proof.
  intros.
  unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
  intros.
  assert (eid=eid0 \/ eid <> eid0 ) by tauto.
  destruct H2.
  subst eid0.
  rewrite EcbMod.set_a_get_a in H1.
  inverts H1.
  apply TcbMod.beq_refl.
  
  rewrite EcbMod.set_a_get_a' in H1.
  eapply H;eauto.
  apply tidspec.neq_beq_false; auto.
Qed.

Lemma RH_TCBList_ECBList_P_hold_for_postq_to_rdy
: forall tcbls ct p qid wt msg ecbls ml size pwl wls sus sus',
  TcbMod.get tcbls ct = Some (p, wait (os_stat_postq qid) wt, msg, sus) ->
  EcbMod.get ecbls qid = Some (absmsgq ml size pwl, wls) ->
  In ct pwl ->
  RH_TCBList_ECBList_P ecbls tcbls ct ->
  RH_TCBList_ECBList_P (EcbMod.set ecbls qid (absmsgq ml size (remove_tid ct pwl), wls) )
                                                    (TcbMod.set tcbls ct (p, rdy, msg, sus')) ct.
Proof.

introv Htg Heg Hi Hrte.
  destruct Hrte as (Hr1 & Hr2 & Hr3 & Hr4 & Hr5).
  unfolds;
  splits;
  unfolds;
  [ funfold Hr1 | funfold Hr2 | funfold Hr3 | funfold Hr4 | funfold Hr5];
  try splits;
  intros; try( rename H0 into H'; rename H1 into H0;
  rename H2 into H0' ; rename H3 into H1);
  try (assert (eid = qid \/ eid <> qid) by tauto;
   rewrite EcbMod.set_sem in H1;
  destruct H2;
  try (subst;
  rewrite EcbMod.beq_refl in H1;
  destruct H1;
  inverts H1);
  try (rewrite tidspec.neq_beq_false in H1; try auto;
  eapply H in H1;
  do 4 destruct H1;
  rewrite TcbMod.set_sem;
  assert (Ht: tid = ct \/ tid <> ct) by tauto;
  destruct Ht;
  try (subst;
  unfold get in *; unfold TcbMap,EcbMap in *;
  rewrite Htg in H1;
  inverts H1);
  rewrite tidspec.neq_beq_false; try eauto)).
  Focus 2.
  {
    rewrite TcbMod.set_sem.
    assert (ct = tid \/ ct <> tid) by tauto.
    destruct H1.
    subst. eapply in_remove_tid_false in H2. tryfalse.
    rewrite tidspec.neq_beq_false; try auto.
    eapply H'.
    split; try eauto.
    eapply tidneq_inwt_in with (x1:= pwl) in H1.
    rewrite H1 in H2. auto.
  }
  Unfocus.
  
  4:{
  rewrite TcbMod.set_sem in *;
  rewrite EcbMod.set_sem;
  assert (ct = tid \/ ct <> tid) by tauto;
  destruct H2;
  try(subst;
  rewrite TcbMod.beq_refl in *;
  tryfalse);
  rewrite tidspec.neq_beq_false in H1; try auto.
  eapply H0' in H1.
  do 4 destruct H1.
   assert (eid = qid \/ eid <> qid) by tauto.
  destruct H3.
  subst.
  unfold get in *; unfold TcbMap,EcbMap in *;
  rewrite Heg in H1.
  destruct H1; inverts H1.
  rewrite EcbMod.beq_refl.
  exists x x0 (remove_tid ct x1) x2.
  split; auto.
  eapply tidneq_inwt_in with (x1:= x1) in H2.
  rewrite <- H2 in H3. auto.
  rewrite tidspec.neq_beq_false; try eauto.
  }

  4:{
  rewrite TcbMod.set_sem in *;
  rewrite EcbMod.set_sem;
  assert (ct = tid \/ ct <> tid) by tauto;
  destruct H2;
  try(subst;
  rewrite TcbMod.beq_refl in *;
  tryfalse);
  rewrite tidspec.neq_beq_false in H1; try auto;
  try (eapply H0 in H1;
  do 2 destruct H1;
   assert (eid = qid \/ eid <> qid) by tauto;
  destruct H3;
  try (subst;
  unfold get in *; unfold TcbMap,EcbMap in *;
  rewrite Heg in H1;
  destruct H1;
  tryfalse);
  rewrite tidspec.neq_beq_false; try eauto).
  }
  4:
  {
  rewrite TcbMod.set_sem in *;
  rewrite EcbMod.set_sem;
  assert (ct = tid \/ ct <> tid) by tauto;
  destruct H2;
  try(subst;
  rewrite TcbMod.beq_refl in *;
  tryfalse);
  rewrite tidspec.neq_beq_false in H1; try auto;
  try (eapply H0 in H1;
  do 2 destruct H1;
   assert (eid = qid \/ eid <> qid) by tauto;
  destruct H3;
  try (subst;
  unfold get in *; unfold TcbMap,EcbMap in *;
  rewrite Heg in H1;
  destruct H1;
  tryfalse);
  rewrite tidspec.neq_beq_false; try eauto).
  }
  4:{
  rewrite TcbMod.set_sem in *;
  rewrite EcbMod.set_sem;
  assert (ct = tid \/ ct <> tid) by tauto;
  destruct H2;
  try(subst;
  rewrite TcbMod.beq_refl in *;
  tryfalse).
  rewrite tidspec.neq_beq_false in H1; try auto;
  try (eapply H' in H1;
  do 3 destruct H1;
   assert (eid = qid \/ eid <> qid) by tauto;
  destruct H3;
  try (subst;
  unfold get in *; unfold TcbMap,EcbMap in *;
  rewrite Heg in H1;
  destruct H1;
  tryfalse);
  rewrite tidspec.neq_beq_false; try eauto).
  }
  
  3:{
  rewrite TcbMod.set_sem in *;
  rewrite EcbMod.set_sem;
  assert (ct = tid \/ ct <> tid) by tauto;
  destruct H2;
  try(subst;
  rewrite TcbMod.beq_refl in *;
  tryfalse);
  rewrite tidspec.neq_beq_false in H1; try auto.
  eapply H0 in H1.
  do 4 destruct H1.
   assert (eid = qid \/ eid <> qid) by tauto.
  destruct H3.
  subst.
  unfold get in *; unfold TcbMap,EcbMap in *.
  rewrite Heg in H1.
  destruct H1.
  inverts H1.
  rewrite TcbMod.beq_refl.
  exists x x0  (remove_tid ct x1) x2.
  splits;eauto.
  rewrite tidspec.neq_beq_false; try eauto.
  }
  
  {
  intros.
  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H1.
  subst.
  assert (EcbMod.get ecbls qid = Some (absmsgq x y pwl, qwaitset) /\ In ct qwaitset).
  splits;eauto.
  apply H in H1.
  simpljoin1.
  unfold get in H1; unfold TcbMap in H1.
  rewrite H1 in Htg. inverts Htg.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  assert (EcbMod.get ecbls qid = Some (absmsgq x y pwl, qwaitset) /\ In tid qwaitset).
    splits;eauto.
  apply H in H3.
  simpljoin1.
  do 3 eexists; eauto.
  }
  {
  rewrite tidspec.neq_beq_false in H1;eauto.
  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H3.
  subst.
  apply H' in H1.
  simpljoin1.
  unfold get in H1; unfold TcbMap in H1.
  rewrite H1 in Htg. 
  inversion Htg. tryfalse.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  apply H' in H1.
  simpljoin1.
  do 3 eexists; eauto.
  }
  
  eapply rh_tcblist_ecblist_mutex_owner_set'_rmpwl; eauto.
  apply Mutex_owner_hold_for_set_tcb; auto.
  

  eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_ecb;
  try eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
  pure_auto.
  do 2 destruct H3.
  inverts H3.
  
  (* new add port *)
  rewrite TcbMod.set_sem in *;
  rewrite EcbMod.set_sem;
  assert (ct = tid \/ ct <> tid) by tauto;
  destruct H2;
  try(subst;
  rewrite TcbMod.beq_refl in *;
  tryfalse);
  rewrite tidspec.neq_beq_false in H1; try auto;
  try (eapply H0 in H1;
  destruct H1;
   assert (eid = qid \/ eid <> qid) by tauto;
  destruct H3;
  try (subst;
  unfold get in *; unfold TcbMap,EcbMap in *;
  rewrite Heg in H1;
  destruct H1;
  tryfalse);
  rewrite tidspec.neq_beq_false; try eauto).
Qed.

Lemma RH_TCBList_ECBList_P_hold_for_postq_to_rdy'
: forall tcbls ct p qid wt msg ecbls ml size pwl wls sus sus',
  TcbMod.get tcbls ct = Some (p, wait (os_stat_postq qid) wt, msg, sus) ->
  EcbMod.get ecbls qid = Some (absmsgq ml size pwl, wls) ->
  In ct pwl ->
  RH_TCBList_ECBList_P ecbls tcbls ct ->
  RH_TCBList_ECBList_P (EcbMod.set ecbls qid (absmsgq ml size (remove_tid ct pwl), wls) )
                                                    (TcbMod.set tcbls ct (p, rdy, Vnull, sus')) ct.
Proof.

  introv Htg Heg Hi Hrte.
  destruct Hrte as (Hr1 & Hr2 & Hr3 & Hr4 & Hr5).
  unfolds;
  splits;
  unfolds;
  [ funfold Hr1 | funfold Hr2 | funfold Hr3 | funfold Hr4 | funfold Hr5];
  try splits;
  intros; try( rename H0 into H'; rename H1 into H0;
  rename H2 into H0' ; rename H3 into H1);

  try (assert (eid = qid \/ eid <> qid) by tauto;
   rewrite EcbMod.set_sem in H1;
  destruct H2;
  try (subst;
  rewrite EcbMod.beq_refl in H1;
  destruct H1;
  inverts H1);
  try (rewrite tidspec.neq_beq_false in H1; try auto;
  eapply H in H1;
  do 4 destruct H1;
  rewrite TcbMod.set_sem;
  assert (Ht: tid = ct \/ tid <> ct) by tauto;
  destruct Ht;
  try (subst;
  unfold get in *; unfold TcbMap,EcbMap in *;
  rewrite Htg in H1;
  inverts H1);
  rewrite tidspec.neq_beq_false; try eauto)).
  Focus 2.
  {
  (*   rename H0' into H2;rename H0 into H1;rename H' into H0. *)
    rewrite TcbMod.set_sem.
    assert (ct = tid \/ ct <> tid) by tauto.
    destruct H1.
    subst. eapply in_remove_tid_false in H2. tryfalse.
    rewrite tidspec.neq_beq_false; try auto.
    eapply H'.
    split; try eauto.
    eapply tidneq_inwt_in with (x1:= pwl) in H1.
    rewrite H1 in H2. auto.
  }
  Unfocus.
  
  4:{
  rewrite TcbMod.set_sem in *;
  rewrite EcbMod.set_sem;
  assert (ct = tid \/ ct <> tid) by tauto;
  destruct H2;
  try(subst;
  rewrite TcbMod.beq_refl in *;
  tryfalse);
  rewrite tidspec.neq_beq_false in H1; try auto.
  eapply H0' in H1.
  do 4 destruct H1.
   assert (eid = qid \/ eid <> qid) by tauto.
  destruct H3.
  subst.
  unfold get in *; unfold TcbMap,EcbMap in *;
  rewrite Heg in H1.
  destruct H1; inverts H1.
  rewrite EcbMod.beq_refl.
  exists x x0 (remove_tid ct x1) x2.
  split; auto.
  eapply tidneq_inwt_in with (x1:= x1) in H2.
  rewrite <- H2 in H3. auto.
  rewrite tidspec.neq_beq_false; try eauto.
  }

  4:{
  rewrite TcbMod.set_sem in *;
  rewrite EcbMod.set_sem;
  assert (ct = tid \/ ct <> tid) by tauto;
  destruct H2;
  try(subst;
  rewrite TcbMod.beq_refl in *;
  tryfalse);
  rewrite tidspec.neq_beq_false in H1; try auto;
  try (eapply H0 in H1;
  do 2 destruct H1;
   assert (eid = qid \/ eid <> qid) by tauto;
  destruct H3;
  try (subst;
  unfold get in *; unfold TcbMap,EcbMap in *;
  rewrite Heg in H1;
  destruct H1;
  tryfalse);
  rewrite tidspec.neq_beq_false; try eauto).
  }
  4:
  {
  rewrite TcbMod.set_sem in *;
  rewrite EcbMod.set_sem;
  assert (ct = tid \/ ct <> tid) by tauto;
  destruct H2;
  try(subst;
  rewrite TcbMod.beq_refl in *;
  tryfalse);
  rewrite tidspec.neq_beq_false in H1; try auto;
  try (eapply H0 in H1;
  do 2 destruct H1;
   assert (eid = qid \/ eid <> qid) by tauto;
  destruct H3;
  try (subst;
  unfold get in *; unfold TcbMap,EcbMap in *;
  rewrite Heg in H1;
  destruct H1;
  tryfalse);
  rewrite tidspec.neq_beq_false; try eauto).
  }
  4:{
  rewrite TcbMod.set_sem in *;
  rewrite EcbMod.set_sem;
  assert (ct = tid \/ ct <> tid) by tauto;
  destruct H2;
  try(subst;
  rewrite TcbMod.beq_refl in *;
  tryfalse);
  rewrite tidspec.neq_beq_false in H1; try auto;
  try (eapply H' in H1;
  do 3 destruct H1;
   assert (eid = qid \/ eid <> qid) by tauto;
  destruct H3;
  try (subst;
  unfold get in *; unfold TcbMap,EcbMap in *;
  rewrite Heg in H1;
  destruct H1;
  tryfalse);
  rewrite tidspec.neq_beq_false; try eauto).
  }
  
  3:{
  rewrite TcbMod.set_sem in *;
  rewrite EcbMod.set_sem;
  assert (ct = tid \/ ct <> tid) by tauto;
  destruct H2;
  try(subst;
  rewrite TcbMod.beq_refl in *;
  tryfalse);
  rewrite tidspec.neq_beq_false in H1; try auto.
  eapply H0 in H1.
  do 4 destruct H1.
   assert (eid = qid \/ eid <> qid) by tauto.
  destruct H3.
  subst.
  unfold get in *; unfold TcbMap,EcbMap in *.
  rewrite Heg in H1.
  destruct H1.
  inverts H1.
  rewrite TcbMod.beq_refl.
  exists x x0  (remove_tid ct x1) x2.
  splits;eauto.
  rewrite tidspec.neq_beq_false; try eauto.
  }
  {
  intros.
  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H1.
  subst.
  assert (EcbMod.get ecbls qid = Some (absmsgq x y pwl, qwaitset) /\ In ct qwaitset).
  splits;eauto.
  apply H in H1.
  simpljoin1.
  unfold get in H1; unfold TcbMap in H1.
  rewrite H1 in Htg. inverts Htg.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  assert (EcbMod.get ecbls qid = Some (absmsgq x y pwl, qwaitset) /\ In tid qwaitset).
    splits;eauto.
  apply H in H3.
  simpljoin1.
  do 3 eexists; eauto.
  }
  
  rewrite tidspec.neq_beq_false in H1;eauto.
  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H3.
  subst.
  apply H' in H1.
  simpljoin1.
  unfold get in H1; unfold TcbMap in H1.
  rewrite H1 in Htg. 
  inversion Htg. tryfalse.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  apply H' in H1.
  simpljoin1.
  do 3 eexists; eauto.
  
  eapply rh_tcblist_ecblist_mutex_owner_set'_rmpwl; eauto.
  apply Mutex_owner_hold_for_set_tcb; auto.
  
  eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_ecb;
  try eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
  pure_auto.
  do 2 destruct H3.
  inverts H3.
  
  (* new add port *)
  rewrite TcbMod.set_sem in *;
  rewrite EcbMod.set_sem;
  assert (ct = tid \/ ct <> tid) by tauto;
  destruct H2;
  try(subst;
  rewrite TcbMod.beq_refl in *;
  tryfalse);
  rewrite tidspec.neq_beq_false in H1; try auto;
  try (eapply H0 in H1;
  destruct H1;
   assert (eid = qid \/ eid <> qid) by tauto;
  destruct H3;
  try (subst;
  unfold get in *; unfold TcbMap,EcbMap in *;
  rewrite Heg in H1;
  destruct H1;
  tryfalse);
  rewrite tidspec.neq_beq_false; try eauto).
Qed.



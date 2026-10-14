
(*Require Export mathlib. *)
Require Export ucos_include.
Require Export OSQAcceptPure.
Require Export OSTimeDlyPure.
Require Import Lia.
Require Import Mbox_common. 

Local Open Scope int_scope.
Local Open Scope Z_scope.
Local Open Scope code_scope.

(*=====================OSQPend=================================*)

Lemma OSQOut_elim :
  forall osq b,
    WellformedOSQ osq ->
    V_qfreeblk osq = Some (Vptr (b, Int.zero)) ->
    exists iout,
      (V_OSQOut  osq = Some (Vptr (b, iout)) /\ 
       4 <= Int.unsigned iout /\
       4 * ((Int.unsigned iout - 4) / 4) = Int.unsigned iout - 4 /\
       (Int.unsigned iout - 4) / 4 < OS_MAX_Q_SIZE).
Proof.
  introv Hwf Hvq.
  funfold Hwf.
  unfold arrayelem_addr_right in *.
  unfold qend_right in *.
  unfold ptr_offset_right in *.
  unfold  ptr_minus in *.
  fsimpl.
  simpl in H8; inverts H8.
  unfold V_OSQOut.
  simpl in H5.
  destruct x5.
  remember ( i0+ᵢ($ 4+ᵢInt.zero)) as Ha.
  inversion H5.
  subst.
(*   rewrite H13 in H12. *)
(*   inverts H12. *)
  rewrite H14 in H11; inverts H11.
  exists i.
  splits; eauto.
  clear -H.
  int auto.
  simpl in H20. (* H18 -> H20 *)
  eapply math_prop_ltu_mod; eauto.
  eapply math_prop_divu_zle; eauto.
Qed.

Lemma OSQEnd_elim :
  forall osq b qsize,
    WellformedOSQ osq ->
    V_qfreeblk osq = Some (Vptr (b, Int.zero)) ->
    V_OSQSize  osq = Some (Vint32 qsize) ->
    V_OSQEnd   osq = Some (Vptr (b, Int.mul qsize ($ 4) +ᵢ ($ 4))).
Proof.
  introv Hwf Hvq Hvs.
  funfold Hwf.
  unfold arrayelem_addr_right in *.
  unfold qend_right in *.
  unfold ptr_offset_right in *.
  unfold  ptr_minus in *.
  fsimpl.
  simpl in H8; inverts H8.
  unfold V_OSQEnd.
  rewrite H2.
  simpl in H5.
  destruct x5.
  remember ( i0+ᵢ($ 4+ᵢInt.zero)) as Ha.
  inversion H5.
  subst.
  rewrite H24 in *.
  rewrite H11 in H15.
  inverts H15.
  rewrite H14 in H7.
  inverts H7.
  simpl in H23.
  lets Heq :  math_prop_divu_ltmod  H6 H13 H17 H19 H23.
  subst i2.
  auto.
Qed.


Lemma OSQStart_elim :
  forall osq b qsize,
    WellformedOSQ osq ->
    V_qfreeblk osq = Some (Vptr (b, Int.zero)) ->
    V_OSQSize  osq = Some (Vint32 qsize) ->
    V_OSQStart osq = Some (Vptr (b, ($ 4))).
Proof.
  introv Hw Hv1 Hv2.
  unfolds in Hw.
  simpljoin1.
  simpl in H5.
  destruct x5.
  inverts H5.
  rewrite H.
  rewrite H4 in Hv1.
  inverts Hv1.
  clear -b.
  int auto.
  int auto.
Qed.


Lemma RLH_ECBData_P_impl_high_ecb_msg_nil :
  forall  (qptr qst qend qin qout : val) (size : int32) 
          (qblk : addrval) (mblk ml : vallist) (A : absecb.B) 
          (l : val),
    RLH_ECBData_P
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: qout ::Vint32 size :: Vint32 Int.zero :: Vptr qblk :: nil)
             mblk ml) A -> exists qmax pwl wl, A = (absmsgq nil qmax pwl, wl).
Proof.
  intros.
  eapply msgqnode_p_nomsg; eauto.
  clear - l.
  int auto.
Qed.

Lemma TCBList_P_impl_high_tcbcur_Some :  
  forall tcbls tcur tcurl tcblist rtbl,
    TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
    exists prio st m, TcbMod.get tcbls tcur = Some (prio, st, m).
Proof.
  introv Htcb.
  simpl in Htcb.
  simpljoin1.
  inverts H.
  apply tcbjoin_get_a in H1.
  destruct x2.
  destruct p.
  eauto.
Qed.


Lemma TCBList_P_impl_high_tcbcur_Some' :  
  forall tcbls tcur tcurl tcblist rtbl prio,
    TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
    exists st m sus, TcbMod.get tcbls tcur = Some (prio, st, m, sus).
Proof.
  introv Htcb.
  simpl in Htcb.
  fsimpl.
  inverts H.
  introv Hv.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
  fsimpl.
  unfolds in H0.
  rewrite H0 in H4.
  invertsall.
  apply tcbjoin_get_a in H1.
  eauto.
Qed.


Lemma AOSTCBPrioTbl_high_tcblist_get_msg :
  forall tcbls p prio st m vl rtbl m' s P av ptls sus sus',
    TcbMod.get tcbls p = Some (prio, st, m, sus) ->
    s|= AOSTCBPrioTbl vl rtbl tcbls ptls av ** P ->
    s|= AOSTCBPrioTbl vl rtbl (TcbMod.set tcbls p (prio, st, m', sus')) ptls av ** P.
Proof.
  introv Htcb Hs.
  sep cancel 2%nat 2%nat.
  unfold AOSTCBPrioTbl  in Hs.
  unfold AOSTCBPrioTbl.
  sep cancel 1%nat 1%nat.
  sep split in Hs.
  sep split; eauto.
  rename H2 into Hth_ptls. (* new add *)
  unfolds.
  unfolds  in H1.
  unfolds in   H0.
  splits.
  intros.
  destruct H1.
  lets Hrs : H1 H2 H3 H4.
  simpljoin1.
  assert (tcbid = p \/ tcbid <> p) by tauto.
  destruct H10.
  subst.
  unfolds in H6; simpl in H6.
  rewrite Htcb in H6.
  inverts H6.
  exists  x m'.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  exists x x0.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (tcbid = p \/ tcbid <> p) by tauto.
  destruct H3.
  subst.
  rewrite TcbMod.set_sem in H2.
  erewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  destruct H1.
  eapply H2; eauto.
  rewrite TcbMod.set_sem in H2.
  erewrite tidspec.neq_beq_false in H2; eauto.
  destruct H1.
  eapply H4; eauto.
  destruct H1.
  destruct H2.
  eapply R_Prio_NoChange_Prio_hold; eauto.
Qed.

(* relation hold lemmas *)
Lemma R_ECB_ETbl_P_high_tcb_get_msg_hold :
  forall l ecb tcbls ptcb prio st m m' sus sus',
    R_ECB_ETbl_P l ecb tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    R_ECB_ETbl_P l ecb (TcbMod.set tcbls ptcb (prio, st, m', sus')).
Proof.
  introv Hr Ht.
  unfolds in Hr.
  unfolds.
  destruct Hr  as (Hr1 & Hr2 & Hty).
  unfolds in Hr1.
  destruct Hr1 as (Hrr1 & Hrr2 & Hrr3 & Hrr4 & Hrr5).
  destruct ecb.
  destruct p. (* new add *)
  splits.
  unfolds.
  splits.
  unfolds.
  intros.
  apply (Hrr1 prio0 H) in H0.
  simpljoin1.
  assert (ptcb = x \/ ptcb <> x) by tauto.
  destruct H1.
  subst.
  unfolds in H0; simpl in H0.
  rewrite H0 in Ht.
  inverts Ht.
  exists x x0 m'.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  exists x.
  exists x0 x1.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.

  unfolds.
  intros.
  apply (Hrr2 prio0 H) in H0.
  simpljoin1.
  assert (ptcb = x \/ ptcb <> x) by tauto.
  destruct H1.
  subst.
  unfolds in H0; simpl in H0.
  rewrite H0 in Ht.
  inverts Ht.
  exists x x0 m'.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  exists x.
  exists x0 x1.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.

  unfolds.
  intros.
  apply (Hrr3 prio0 H) in H0.
  simpljoin1.
  assert (ptcb = x \/ ptcb <> x) by tauto.
  destruct H1.
  subst.
  unfolds in H0; simpl in H0.  
  rewrite H0 in Ht.
  inverts Ht.
  exists x x0 m'.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  exists x.
  exists x0 x1.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.

   unfolds.
  intros.
  apply (Hrr4 prio0 H) in H0.
  simpljoin1.
  assert (ptcb = x \/ ptcb <> x) by tauto.
  destruct H1.
  subst.
  unfolds in H0; simpl in H0.
  rewrite H0 in Ht.
  inverts Ht.
  exists x x0 m'.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  exists x.
  exists x0 x1.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.

  unfolds.
  intros.
  apply (Hrr5 prio0 H) in H0.
  simpljoin1.
  assert (ptcb = x \/ ptcb <> x) by tauto.
  destruct H1.
  subst.
  unfolds in H0; simpl in H0.  
  rewrite H0 in Ht.
  inverts Ht.
  exists x x0 m'.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  exists x.
  exists x0 x1.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.

  destruct Hr2 as (Hrc1 & Hrc2 & Hrc3 & Hrc4 & Hrc5).
  unfolds.
  splits.

  unfolds.
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto.
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  eapply Hrc1; eauto.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.

  unfolds.
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto.
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  eapply Hrc2; eauto.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.

  unfolds.
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto.
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  eapply Hrc3; eauto.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.

  unfolds.
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto.
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  eapply Hrc4; eauto.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.

  unfolds.
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto.
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  eapply Hrc5; eauto.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.

  auto.
Qed.

Lemma R_ECB_ETbl_P_high_tcb_block_hold :
  forall l  vl egrp v2 v3 v4 v5 etbl tcbls ptcb prio st m m' y bity bitx ey time av petbl pegrp petbl_addr sus sus',
    Int.unsigned prio < 64 ->
    R_PrioTbl_P vl tcbls av->
    R_ECB_ETbl_P l
                 (V$OS_EVENT_TYPE_Q
                    :: Vint32 egrp
                    :: v2 :: v3 :: v4 :: v5 :: Vint32 pegrp :: petbl_addr :: nil,
                  etbl,petbl) tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    y = Int.shru (prio) ($ 3) ->
    bity = ($ 1) <<ᵢ y ->
    bitx = ($ 1) <<ᵢ (Int.and (prio) ($ 7)) ->
    nth_val ∘(Int.unsigned y) etbl = Some (Vint32 ey) ->
    R_ECB_ETbl_P l
                 (V$OS_EVENT_TYPE_Q
                    :: Vint32 (Int.or egrp bity)
                    :: v2 :: v3 :: v4 :: v5 :: Vint32 pegrp :: petbl_addr :: nil,
                  update_nth_val ∘(Int.unsigned y) etbl (Vint32 (Int.or ey bitx)),petbl)
                 (TcbMod.set tcbls ptcb
                             (prio, wait (os_stat_q l) time, m', sus')).
Proof.
  introv Hran Hrs  Hre Htc Hy Hb1 Hb2 Hnth.
  subst.
  unfolds in Hre.
  destruct Hre as (Hre1 & Hre2 & Het).
  unfolds.
  splits.
  unfolds.
  splits.

  unfolds.
  intros.
  destruct Hre1 as (Hre1 & _).
  destruct Hre2 as (Hre2 & _).
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
  usimpl H0.

  unfolds.
  intros.
  usimpl H0.

  unfolds.
  intros.
  usimpl H0.

  unfolds.
  intros.
  usimpl H0.

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
  unfolds in Hre2.
  destruct Hre2 as (Hre2 & _).
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
  destruct H.
  usimpl H1.

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
  destruct H.
  usimpl H1.

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
  destruct Hre2 as (_&_& _ &Hre2&_).
  apply Hre2 in H.
  destruct H.
  usimpl H1.

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
  destruct Hre2 as (_&_&_&_&Hre2).
  apply Hre2 in H.
  destruct H.
  usimpl H1.

  simpl.
  unfolds.
  left.
  unfolds; simpl; auto.
Qed.


Lemma  ecb_etbl_set_hold:
  forall x y tcbls prio st m ptcb m' sus sus',
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    R_ECB_ETbl_P x y tcbls  ->
    R_ECB_ETbl_P x y  (TcbMod.set tcbls ptcb (prio, st, m', sus')).
Proof.
  introv Htc Hr.
  unfolds in Hr.
  destruct Hr as (Hr1 & Hr2 & Hr3).
  destruct Hr1 as (Hra1 & Hra2 & Hra3 & Hra4 & Hra5).
  destruct Hr2 as (Hrb1 & Hrb2 & Hrb3 & Hrb4 & Hrb5).
  unfolds.
  splits.

  unfolds.
  splits.

  unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  eapply Hra1 in H0; eauto.
  simpljoin1.
  assert (ptcb = x0 \/ ptcb <> x0) by tauto.
  destruct H1.
  subst.
  unfolds in H0; simpl in H0.
  rewrite H0 in Htc.
  inverts Htc.
  exists x0.
  exists x1 m'.
  eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  exists x0.
  exists x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  eapply Hra2 in H0; eauto.
  simpljoin1.
  assert (ptcb = x0 \/ ptcb <> x0) by tauto.
  destruct H1.
  subst.
  unfolds in H0; simpl in H0.
  rewrite H0 in Htc.
  inverts Htc.
  exists x0.
  exists x1 m'.
  eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  exists x0.
  exists x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  eapply Hra3 in H0; eauto.
  simpljoin1.
  assert (ptcb = x0 \/ ptcb <> x0) by tauto.
  destruct H1.
  subst.
  unfolds in H0; simpl in H0.  
  rewrite H0 in Htc.
  inverts Htc.
  exists x0.
  exists x1 m'.
  eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  exists x0.
  exists x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  eapply Hra4 in H0; eauto.
  simpljoin1.
  assert (ptcb = x0 \/ ptcb <> x0) by tauto.
  destruct H1.
  subst.
  unfolds in H0; simpl in H0.
  rewrite H0 in Htc.
  inverts Htc.
  exists x0.
  exists x1 m'.
  eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  exists x0.
  exists x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  eapply Hra5 in H0; eauto.
  simpljoin1.
  assert (ptcb = x0 \/ ptcb <> x0) by tauto.
  destruct H1.
  subst.
  unfolds in H0; simpl in H0.
  rewrite H0 in Htc.
  inverts Htc.
  exists x0.
  exists x1 m'.
  eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  exists x0.
  exists x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  unfolds.
  splits.

  unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto. 
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrb1; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.

  unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto. 
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrb2; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.

  unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto. 
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrb3; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.

  unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto. 
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrb4; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.

  unfolds.
  destruct y.
  destruct p. (* new add *)
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto. 
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrb5; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
    
  auto.
Qed.

Lemma ECBList_P_high_tcb_get_msg_hold:
  forall  ectrl head tail msgql ecbls tcbls ptcb prio st m m' sus sus',
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    ECBList_P head tail ectrl msgql ecbls 
              (TcbMod.set tcbls ptcb (prio, st, m', sus')).
Proof.
  inductions ectrl.
  intros.
  simpl in H.
  simpljoin1.
  simpl; splits; auto.
  intros.
  simpl in H.
  simpljoin1.
  destruct msgql; tryfalse.
  destruct a.
  destruct p. (* new add *)
  simpljoin1.
  simpl.
  eexists.
  splits; eauto.
  eapply ecb_etbl_set_hold; eauto.
   eapply ecb_petbl_set_hold; eauto. (* new add *)
  do 3 eexists; splits; eauto.
Qed.


Lemma ECBList_P_high_tcb_block_hold:
  forall  ectrl head tail msgql ecbls tcbls ptcb prio  m qid time m' sus sus',
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, rdy, m, sus) ->
    EcbMod.get ecbls qid = None ->
    ECBList_P head tail ectrl msgql ecbls 
              (TcbMod.set tcbls ptcb (prio, wait (os_stat_q qid) time, m', sus')).
Proof.
  inductions ectrl.
  intros.
  simpl.
  simpl in H.
  simpljoin1.
  splits; auto.
  
  intros.
  simpl in H.
  simpljoin1.
  destruct msgql; tryfalse.
  destruct a.
  destruct p. (* new add *)
  rename H3 into Hpetbl. (* new add *)
  rename H4 into H3. (* new add *)
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
  apply ecbmod_joinsig_get in H3.
  rewrite H3 in H1.
  tryfalse.
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
  (* new add about postq *)
  eapply R_ECB_PETbl_P_set_tcb_wait_hold; eauto.
  introv Hf. destruct Hf as (qd & wt & Hf). inverts Hf.
  (* end of new add *)
  do 3 eexists; splits; eauto.
  eapply IHectrl; eauto.
  eapply  ecbmod_joinsig_get_none; eauto.
Qed.
  
Local Open Scope int_scope.
Local Open Scope Z_scope.
Local Open Scope code_scope.

Lemma TCBList_P_tcb_get_msg_hold :
    forall ptcb v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 rtbl vl
           tcbls prio st m m' sus,
    TCBList_P (Vptr ptcb) ((v1::v2::v3::v4::v5::v6::v7::v8::v9::v10::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    TCBList_P (Vptr ptcb) ((v1::v2::v3::m'::v5::v6::v7::v8::v9::v10::v11::nil)::vl) rtbl (TcbMod.set tcbls ptcb (prio, st, m', sus)).
Proof.
  introv Htc Hget.
  unfolds in Htc.
  simpljoin1.
  simpl_hyp.
  inverts H.
  fold TCBList_P in H3.
  unfolds.
  fold TCBList_P.
  do 4 eexists; splits; eauto.
  unfolds; simpl; auto.
  instantiate (1:=(prio,st,m', sus)).
  eapply tcbjoin_set; eauto.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
   lets Heq : tcbjoin_get H1 Hget.
  inverts Heq.
  simpljoin1.
  simpl_hyp.
  unfolds.
  splits; try unfolds; simpl; auto.
  splits.
  funfold H4.
  clear - H.
  funfold H.
  unfolds.
  intros.
   assert (RdyTCBblk
        (x0
         :: v2
            :: v3
               :: m
                  :: v5 :: v6 :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil)
        rtbl prio0).
  unfolds.
  funfold H0; simpl; auto.
  apply H in H1.
  destruct H1.
  splits; try unfolds;simpl; eauto.
(*   
  destruct H2;
  [left | right;left | right;right;left | right;right;right];
  destruct H2;
  split;auto;
  [destruct H3 | do 2 destruct H3 |do 2 destruct H3 |destruct H3; destruct H2];
  [inverts H3| inverts H3| inverts H3| inverts H2]; 
  eexists; eauto.
   *)
   
  destruct H2.
  left;
  destruct H2;
  split;auto;
  destruct H3;
  inverts H3;
  eexists; eauto.
  
  destruct H2.
  right;left;
  destruct H2;
  split;auto;
  do 2 destruct H3;
  inverts H3;
  eexists; eauto.
  
  destruct H2.
  right;right;left.
  destruct H2.
  split;auto.
  do 2 destruct H3.
  inverts H3.
  eexists; eauto.

  destruct H2.
  right;right;right;left.
  destruct H2.
  split;auto.
  do 2 destruct H3.
  inverts H3.
  eexists; eauto.
  
  destruct H2.
  right;right;right;right.
  do 2 destruct H3.
  split;auto.
  inverts H3.
  eexists; eauto.
  
  {
  destruct H4 as (_ & Hhl & _).
  unfolds in Hhl.
  unfolds.
  intros.
  inverts H.
  assert ( (prio0, rdy, m, false) = (prio0, rdy, m, false)) by auto. 
  apply Hhl in H.
  simpljoin1; try unfolds;simpl; auto.
  }
  (* new add *)
  destruct H4 as (_ & _ & Hhl & _).
  unfolds in Hhl.
  unfolds.
  simpljoin1.
  split; intros; simpl_hyp.
  assert (Hwt: WaitTCBblk
         (x0
          :: v2
             :: v3
                :: m
                   :: v5
                      :: V$OS_STAT_SUSPEND
                         :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil)
         rtbl prio0 Int.zero).
  unfolds; simpl; auto.
  apply H in Hwt.
  destruct Hwt as (m0 & Heq); inverts Heq.
  eauto.
  unfolds; simpl; auto.
  assert (Hwt: WaitTCBblk
         (x0
          :: v2
             :: v3
                :: m
                   :: v5
                      :: V$OS_STAT_SUSPEND
                         :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil)
         rtbl prio0 t).
  unfolds; simpl; auto.
  apply H0 in Hwt; auto.
  destruct Hwt as (m0 & Heq); inverts Heq.
  eauto.

  unfolds.
  split; introv Heq; inverts Heq.
  eapply H4; eauto.
  eapply H4; eauto.
  (* end of new add *)
  destruct H4 as (_ & _ & _ & _ & Hhl & _).
  unfolds in Hhl.
  unfolds.
  simpljoin1; splits; (* try unfolds;simpl; auto; *)
  try (introv Hwt' Hs;
  try introv Hptr;
  assert (Hstat: V_OSTCBStat (x0 :: v2 :: v3 :: m' :: v5 :: v6 :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil) =
                                V_OSTCBStat (x0 :: v2 :: v3 :: m :: v5 :: v6 :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil))
                       by (unfolds; simpl; auto);
  rewrite Hstat in Hs).


  eapply H in Hs; eauto.
  simpljoin1; eexists; eauto.

  eapply H0 in Hs; eauto.
  destruct Hs as (msg & Hs); try (unfolds; simpl; eauto).
  destruct Hs as [ (Hnoteq & Hst) | (Heq & Hst) ];
  inverts Hst.
  eexists; left;split;auto.
  eexists; right;split;auto.
  eapply H4 in Hs; eauto.
  destruct Hs as (msg & Hs); try (unfolds; simpl; eauto).
  inverts Hs.
  eauto.

  eapply H5 in Hs; eauto.
  destruct Hs as (msg & Hs); try (unfolds; simpl; eauto).
  destruct Hs as [ (Hnoteq & Hst) | (Heq & Hst) ];
  inverts Hst.
  eexists; left;split;auto.
  eexists; right;split;auto.
  eapply H6 in Hs; eauto.
  destruct Hs as (msg & Hs); try (unfolds; simpl; eauto).
  inverts Hs.
  eauto.

  eapply H7 in Hs; eauto.
  destruct Hs as (msg & Hs); try (unfolds; simpl; eauto).
  destruct Hs as [ (Hnoteq & Hst) | (Heq & Hst) ];
  inverts Hst.
  eexists; left;split;auto.
  eexists; right;split;auto.
  eapply H8 in Hs; eauto.
  destruct Hs as (msg & Hs); try (unfolds; simpl; eauto).
  inverts Hs.
  eauto.


  splits;
  try (introv Hwt' Hs;
  try introv Hptr;
  assert (Hstat: V_OSTCBStat (x0 :: v2 :: v3 :: m' :: v5 :: v6 :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil) =
                                V_OSTCBStat (x0 :: v2 :: v3 :: m :: v5 :: v6 :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil))
                       by (unfolds; simpl; auto);
  rewrite Hstat in Hs).

  eapply H9 in Hs; eauto.
  destruct Hs as (msg & Hs); try (unfolds; simpl; eauto).
  destruct Hs as [ (Hnoteq & Hst) | (Heq & Hst) ];
  inverts Hst.
  eexists; left;split;auto.
  eexists; right;split;auto.
  eapply H10 in Hs; eauto.
  destruct Hs as (msg & Hs); try (unfolds; simpl; eauto).
  inverts Hs.
  eauto.
  (* postq *)
  eapply H11 in Hs; eauto.
  destruct Hs as (Ht & msg & Hs); try (unfolds; simpl; eauto).
  inverts Hs.
  eauto.
  (* suspend *)
  eapply H12 in Hs; eauto.
  destruct Hs as ( msg & opt & Hs & Hc); try (unfolds; simpl; eauto).
  inverts Hs.
  eauto.
  eapply H13 in Hs; eauto.
  destruct Hs as ( msg & opt & Hs & Hc); try (unfolds; simpl; eauto).
  inverts Hs.
  eauto.
  eapply H14 in Hs; eauto.
  destruct Hs as ( Ht & msg & Hs); try (unfolds; simpl; eauto).
  inverts Hs.
  eauto.
  eapply H15 in Hs; eauto.
  destruct Hs as ( msg & opt & Hs & Hc); try (unfolds; simpl; eauto).
  inverts Hs.
  eauto.

  split.
  assert (Hstat: V_OSTCBStat (x0 :: v2 :: v3 :: m' :: v5 :: v6 :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil) =
                                V_OSTCBStat (x0 :: v2 :: v3 :: m :: v5 :: v6 :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil))
                       by (unfolds; simpl; auto).
  introv Hwt' Hs.
  introv Hptr. 
  rewrite Hstat in Hs.

  eapply H16 in Hs; eauto.
  destruct Hs as ( msg & opt & Hs & Hc). try (unfolds; simpl; eauto).
  inverts Hs.
  eauto.

  splits.

  unfold RLH_WaitPort_P.
  intros.
  simpl_hyp.
  assert ( WaitTCBblk
  (x0
   :: v2
      :: Vptr eid
         :: m
            :: v5
               :: V$OS_STAT_PORT
                  :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil)
  rtbl prio0 t).
  funfold H20.
  unfolds; simpl; eauto.
  eapply H17 in H21.
  destruct H21.
  unfolds; simpl; eauto.
  unfolds; simpl; eauto.
  destruct H21 as [(Heq & Hs)|(Hneq & Hs)];
  inverts Hs; eauto.

  unfold RLH_WaitPort_TO_P.
  intros.
  funfold H18.
  eapply H18 in H20; eauto.
  destruct H20 as (m0 & Hst).
  inverts Hst; eauto.
  unfolds; simpl; eauto.

  unfold RLH_WaitPort_Suspend_P.
  intros.
  eapply H19 in H22; eauto.
  simpljoin.
  eauto.

  unfolds.
  splits;
  try solve [unfolds; intros; inverts H; eapply H4; eauto].
  splits;
  try solve [unfolds; intros; inverts H; eapply H4; eauto].
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
  forall prio y bitx rtbl ry ptbl av,
    0 <= prio < 64 ->
    y = Int.shru ($ prio) ($ 3) ->
    bitx = ($ 1) <<ᵢ (Int.and ($ prio) ($ 7)) ->
    nth_val ∘(Int.unsigned y) rtbl = Some (Vint32 ry) ->
    RL_RTbl_PrioTbl_P rtbl ptbl av->
    RL_RTbl_PrioTbl_P
      (update_nth_val ∘(Int.unsigned y) rtbl (Vint32 (ry&ᵢInt.not bitx))) ptbl av.
Proof.
  introv Hpr Hy Hb Hnth Hrl.
  unfolds in Hrl.
  unfolds.
  introv Hp Hpro.
  subst .
  eapply Hrl; eauto.
  remember ($ prio) as pri.
  assert ( 0 <= Int.unsigned pri < 64).
  clear -Hpr Heqpri.
  subst.
  int auto.
  clear Heqpri Hpr.
  assert (p = pri \/ p <> pri) by tauto.
  destruct H0.
  subst p.
  eapply  prio_update_self_not_in in Hpro; eauto.
  tryfalse.
  eapply prio_neq_in_tbl; eauto.
Qed.



Lemma TCBList_P_tcb_block_hold :
    forall ptcb v1 v2 v3 v4 v5 v6 v8 v9 v10 v11 rtbl vl
           tcbls prio st m qid time ry m',
    TCBList_P (Vptr ptcb) ((v1::v2::v3::v4::v5::(Vint32 v6)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, false) ->
    prio_neq_cur tcbls ptcb ( prio) ->
    st = rdy \/ (exists n, st = wait os_stat_time n) -> 
    nth_val (nat_of_Z (Int.unsigned v9)) rtbl = Some (Vint32 ry) ->
    time <> Int.zero ->
    TCBList_P (Vptr ptcb) ((v1::v2::(Vptr qid)::m'::(Vint32 time)::(Vint32 ($ OS_STAT_Q))::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) 
(update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (Int.and ry (Int.not v10)))) 
 (TcbMod.set tcbls ptcb ( prio, wait (os_stat_q qid) (Some time), m', false)).
Proof.
  introv  Htcb Htm Hst Hprio Hnth Htime.
  unfolds in Htcb;fold TCBList_P in Htcb.
  simpljoin1.
  inverts H.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds.
  fold TCBList_P.
  exists x x0.
  exists x1.
  exists (prio,  wait (os_stat_q qid) (Some time) ,m', false).
  splits; eauto.
  eapply tcbjoin_set; eauto.
  
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  simpljoin1.
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
  unfolds.
  intros.
  unfolds in H.
  simpljoin.
  simpl_hyp.
  eexists.
  eauto.
  unfolds.
  intros.
  inverts H.
  false.
  inverts H5.
  eapply prio_update_self_not_in in Hnth; eauto. 
  splits; try solve [ unfolds; intros; inverts H0].
  splits; try solve [ unfolds; intros; inverts H0].
  unfolds.
  splits; try solve [ unfolds; intros; inverts H].
  unfolds; intros.
  inverts H.
  splits; eauto.
  eexists.
  left. splits; eauto. left.
   splits; eauto.
  unfolds; try splits; simpl; eauto.
  eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto.
  eapply prio_update_self_not_in; eauto.
  splits; try solve [ unfolds; intros; inverts H].

  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  simpljoin; simpl_hyp.
  funfold H2.
  eapply update_rtbl_tcblist_hold; eauto.
  unfolds in Hst.
  intros.
  lets Has : tcbjoin_get_getneq H1 H.
  destruct Has.
  eapply Hst; eauto.
Qed.

Lemma TCBList_P_tcb_block_hold2 :
    forall ptcb v1 v2 v3 v4 v5 v6 v8 v9 v10 v11 rtbl vl
           tcbls prio st m qid time ry m',
    TCBList_P (Vptr ptcb) ((v1::v2::v3::v4::v5::(Vint32 v6)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, false) ->
    prio_neq_cur tcbls ptcb ( prio) ->
    st = rdy \/ (exists n, st = wait os_stat_time n) -> 
    nth_val (nat_of_Z (Int.unsigned v9)) rtbl = Some (Vint32 ry) ->
    time = Int.zero ->
    TCBList_P (Vptr ptcb) ((v1::v2::(Vptr qid)::m'::(Vint32 time)::(Vint32 ($ OS_STAT_Q))::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) 
(update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (Int.and ry (Int.not v10)))) 
 (TcbMod.set tcbls ptcb ( prio, wait (os_stat_q qid) (None), m', false)).
Proof.
  introv  Htcb Htm Hst Hprio Hnth Htime.
  unfolds in Htcb;fold TCBList_P in Htcb.
  simpljoin1.
  inverts H.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds.
  fold TCBList_P.
  exists x x0.
  exists x1.
  exists (prio,  wait (os_stat_q qid) (None) ,m', false).
  splits; eauto.
  eapply tcbjoin_set; eauto.
  
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  simpljoin1.
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
  unfolds.
  intros.
  unfolds in H.
  simpljoin.
  simpl_hyp.
  eexists.
  eauto.
  unfolds.
  intros.
  inverts H.
  false.
  inverts H5.
  eapply prio_update_self_not_in in Hnth; eauto. 
  splits; try solve [ unfolds; intros; inverts H0].
  splits; try solve [ unfolds; intros; inverts H0].

  unfolds.
  splits; try solve [ unfolds; intros; inverts H].
  unfolds; intros.
  inverts H.
  splits; eauto.
  eexists.
  right. splits; eauto.
  unfolds; try splits; simpl; eauto.
  eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto.
  eapply prio_update_self_not_in; eauto.
  splits; try solve [ unfolds; intros; inverts H].

  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  simpljoin; simpl_hyp.
  funfold H2.
  eapply update_rtbl_tcblist_hold; eauto.
  unfolds in Hst.
  intros.
  lets Has : tcbjoin_get_getneq H1 H.
  destruct Has.
  eapply Hst; eauto.
  Unshelve. trivial.
Qed.

(* new add *)

Lemma TCBList_P_tcb_block_hold_sus :
    forall ptcb v1 v2 v3 v4 v5 v6 v8 v9 v10 v11 rtbl vl
           tcbls prio st m qid time ry m' sus stat,
    TCBList_P (Vptr ptcb) ((v1::v2::v3::v4::v5::(Vint32 v6)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    prio_neq_cur tcbls ptcb ( prio) ->
    st = rdy \/ (exists n, st = wait os_stat_time n) -> 
    nth_val (nat_of_Z (Int.unsigned v9)) rtbl = Some (Vint32 ry) ->
    time <> Int.zero ->
    stat = (if sus then Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND) else ($ OS_STAT_Q))  ->
    TCBList_P (Vptr ptcb) ((v1::v2::(Vptr qid)::m'::(Vint32 time)::(Vint32 stat)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) 
(update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (Int.and ry (Int.not v10)))) 
 (TcbMod.set tcbls ptcb ( prio, wait (os_stat_q qid) (Some time), m', sus)).
Proof.
  introv  Htcb Htm Hst Hprio Hnth Hneq Hstat.
  destruct sus; subst.
  2: eapply TCBList_P_tcb_block_hold; eauto.
  unfolds in Htcb;fold TCBList_P in Htcb.
  simpljoin.
  inverts H.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds.
  fold TCBList_P.
  exists x x0.
  exists x1.
  exists (prio,wait (os_stat_q qid) (Some time),m', true).
  splits; eauto.
  eapply tcbjoin_set; eauto.
{
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  simpljoin.
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
  simpljoin.
  simpl_hyp.
  eexists.
  eexists.
  splits; eauto.
  splits; try solve [ unfolds; intros; inverts H0].

  unfolds.
  splits; try solve [ unfolds; intros; inverts H].
  splits; try solve [ unfolds; intros; inverts H].
  unfolds.
  intros.
  inverts H.
  splits; eauto.
  left. eexists.
  splits; eauto.
  unfolds; try splits; simpl; eauto.
  eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto.
  eapply prio_update_self_not_in; eauto.
}
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  simpljoin; simpl_hyp.
  funfold H2.
  eapply update_rtbl_tcblist_hold; eauto.
  unfolds in Hst.
  intros.
  lets Has : tcbjoin_get_getneq H1 H.
  destruct Has.
  eapply Hst; eauto.
Qed.

Lemma TCBList_P_tcb_block_hold2_sus :
    forall ptcb v1 v2 v3 v4 v5 v6 v8 v9 v10 v11 rtbl vl
           tcbls prio st m qid time ry m' sus stat,
    TCBList_P (Vptr ptcb) ((v1::v2::v3::v4::v5::(Vint32 v6)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    prio_neq_cur tcbls ptcb ( prio) ->
    st = rdy \/ (exists n, st = wait os_stat_time n) -> 
    nth_val (nat_of_Z (Int.unsigned v9)) rtbl = Some (Vint32 ry) ->
    time = Int.zero ->
    stat = (if sus then Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND) else ($ OS_STAT_Q))  ->
    TCBList_P (Vptr ptcb) ((v1::v2::(Vptr qid)::m'::(Vint32 time)::(Vint32 stat)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) 
(update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (Int.and ry (Int.not v10)))) 
 (TcbMod.set tcbls ptcb ( prio, wait (os_stat_q qid) (None), m', sus)).
Proof.
  introv  Htcb Htm Hst Hprio Hnth Hneq Hstat.
  destruct sus; subst.
  2: eapply TCBList_P_tcb_block_hold2; eauto.
  unfolds in Htcb;fold TCBList_P in Htcb.
  simpljoin.
  inverts H.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds.
  fold TCBList_P.
  exists x x0.
  exists x1.
  exists (prio,wait (os_stat_q qid) None,m', true).
  splits; eauto.
  eapply tcbjoin_set; eauto.
{
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  simpljoin.
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
  simpljoin.
  simpl_hyp.
  eexists.
  eexists.
  splits; eauto.
  splits; try solve [ unfolds; intros; inverts H0].

  unfolds.
  splits; try solve [ unfolds; intros; inverts H].
  splits; try solve [ unfolds; intros; inverts H].
  unfolds.
  intros.
  inverts H.
  splits; eauto.
  right.
  splits; eauto.
  unfolds; try splits; simpl; eauto.
  eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto.
  eapply prio_update_self_not_in; eauto.
}
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  simpljoin; simpl_hyp.
  funfold H2.
  eapply update_rtbl_tcblist_hold; eauto.
  unfolds in Hst.
  intros.
  lets Has : tcbjoin_get_getneq H1 H.
  destruct Has.
  eapply Hst; eauto.
Qed.
(* end of new add *)

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
    TcbMod.get  tcs ptcb = Some (prio, t, m, sus)->
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


Lemma RH_CurTCB_high_get_msg_hold :
  forall ptcb tcbls prio st m m' sus sus',
    RH_CurTCB ptcb tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    RH_CurTCB ptcb (TcbMod.set tcbls ptcb (prio, st, m', sus')).
Proof.
  introv Hrh Htc.
  unfolds in Hrh.
  simpljoin1.
  unfolds.
  unfolds in H; simpl in H.
  rewrite H in Htc.
  inverts Htc.
  exists prio st m'.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; eauto.
Qed.


Lemma RH_CurTCB_high_block_hold :
  forall ptcb tcbls prio st m qid time m' sus sus',
    RH_CurTCB ptcb tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    RH_CurTCB ptcb (TcbMod.set tcbls ptcb
        (prio, wait (os_stat_q qid) time, m', sus')).
Proof.
  introv Hr Ht.
  unfolds in Hr.
  simpljoin1.
  unfolds in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  unfolds.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; eauto.
Qed.

Lemma RH_TCBList_ECBList_P_high_get_msg_hold :
  forall ecbls tcbls pcur qid m ml max wl prio  m' pwl sus sus',
    RH_TCBList_ECBList_P ecbls tcbls pcur ->
    EcbMod.get ecbls qid = Some (absmsgq (m::ml) max pwl, wl) ->
    TcbMod.get tcbls pcur = Some (prio, rdy, m', sus) ->
    RH_TCBList_ECBList_P (EcbMod.set ecbls qid (absmsgq ml max pwl, wl)) (TcbMod.set tcbls pcur (prio, rdy, m, sus')) pcur. 
Proof.
  introv Hr Ht He.
  unfolds in Hr.
  destruct Hr as (Hr1 & Hr2 & Hr3 & Hr4 & Hr5).
  unfolds.
  splits.
  splits.  

  intros.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H0.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  inverts H0.
  assert ( EcbMod.get ecbls eid = Some (absmsgq (m :: x) y pqwaitset, qwaitset) /\ In tid qwaitset).
  splits; auto.
  apply Hr1 in H.
  simpljoin1.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  unfolds in H; simpl in H.
  rewrite He in H; inverts H.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; eauto.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hr1 in H.
  simpljoin1.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H1.
  subst.
  unfolds in H; simpl in H.
  rewrite He in H; inverts H.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; eauto.

 (* new add about postq *)
  intros.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H0.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  inverts H0.
  assert ( EcbMod.get ecbls eid = Some (absmsgq (m :: x) y pqwaitset, qwaitset) /\ In tid pqwaitset).
  splits; auto.
  apply Hr1 in H.
  simpljoin1.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  unfolds in H; simpl in H.
  rewrite He in H; inverts H.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; eauto.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hr1 in H.
  simpljoin1.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H1.
  subst.
  unfolds in H; simpl in H.
  rewrite He in H; inverts H.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; eauto.

 (* end of new add *)
  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hr1 in H.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfolds in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  do (* 3 *) 4 eexists; splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do (* 3 *) 4 eexists; splits; eauto.

  (* new add bout postq *)
   intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hr1 in H.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfolds in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  do (* 3 *) 4 eexists; splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do (* 3 *) 4 eexists; splits; eauto.

  (* end of new add *)
  splits.  
  intros.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H0.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  inverts H0.
  destruct H as (Ha & Hb).
  rewrite EcbMod.set_sem in Ha.
  rewrite tidspec.neq_beq_false in Ha; auto.
  assert ( EcbMod.get ecbls eid = Some (abssem n, wls)/\ In tid wls).
  splits; auto.
  apply Hr2 in H.
  simpljoin1.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H1.
  subst.
  unfolds in H; simpl in H.
  rewrite He in H; inverts H.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; eauto.

  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
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
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H0.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  inverts H0.
  destruct H as (Ha & Hb).
  rewrite EcbMod.set_sem in Ha.
  rewrite tidspec.neq_beq_false in Ha; auto.
  assert ( EcbMod.get ecbls eid =Some (absmbox n, wls)/\ In tid wls).
  splits; auto.
  apply Hr3 in H.
  simpljoin1.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H1.
  subst.
  unfolds in H; simpl in H.
  rewrite He in H; inverts H.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; eauto.

  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
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
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H0.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  inverts H0.
  destruct H as (Ha & Hb).
  rewrite EcbMod.set_sem in Ha.
  rewrite tidspec.neq_beq_false in Ha; auto.
  assert ( EcbMod.get ecbls eid =Some (absmutexsem n1 n2, wls)/\ In tid wls).
  splits; auto.
  apply Hr4 in H.
  simpljoin1.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H1.
  subst.
  unfolds in H; simpl in H.
  rewrite He in H; inverts H.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; eauto.

  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
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

  3:{
    splits.  
    intros.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H0.
    subst.
    rewrite EcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; auto.
    inverts H.
    inverts H0.
    destruct H as (Ha & Hb).
    rewrite EcbMod.set_sem in Ha.
    rewrite tidspec.neq_beq_false in Ha; auto.
    assert ( EcbMod.get ecbls eid =Some (absport, wls)/\ In tid wls).
    splits; auto.
    apply Hr5 in H.
    simpljoin1.
    assert (tid = pcur \/ tid <> pcur) by tauto.
    destruct H1.
    subst.
    unfolds in H; simpl in H.
    rewrite He in H; inverts H.
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
    eexists; eauto.
  
    intros.
    assert (tid = pcur \/ tid <> pcur) by tauto.
    destruct H0.
    subst.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; auto.
    inverts H.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; auto.
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
  }

  apply Mutex_owner_hold_for_set_tcb.
  eapply Mutex_owner_set; eauto.
  intro; simpljoin1.
  unfolds in Hr4.
  simpljoin1.
  eauto.
  (* new add about RH_TCBList_ECBList_MUTEX_OWNER_P *)
  destruct Hr4 as (_ & _ & _ & Hrb).
  eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_ecb;
  try eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
  pure_auto.
  do 2 destruct H.
  inverts H.
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
  do 4 eexists;
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

  (* new add about postq *)
  intros.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H0.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  inverts H0.
  assert ( EcbMod.get ecbls eid = Some (absmsgq x y pqwaitset, wl) /\ In tid pqwaitset).
  splits; auto.
  apply Hr1 in H.
  simpljoin1.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  unfolds in H; simpl in H.
  rewrite He in H; inverts H.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; eauto.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hr1 in H.
  simpljoin1.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H1.
  subst.
  unfolds in H; simpl in H.
  rewrite He in H; inverts H.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; eauto.

 (* end of new add *)
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  exists ml max.
  exists pwl. (* new add *)
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
  do (* 3 *) 4 eexists; splits; eauto.
  unfolds in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  simpl.
  right; auto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do (* 3 *) 4 eexists; splits; eauto.

  (* new add bout postq *)
   intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hr1 in H.
  simpljoin1.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfolds in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  do (* 3 *) 4 eexists; splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do (* 3 *) 4 eexists; splits; eauto.
  (* end of new add *)

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
  2:{
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
    assert (EcbMod.get ecbls eid = Some (absport, wls) /\ In tid wls) by eauto.
    apply Hr5 in H2.
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
  }
  
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
  (* new add about RH_TCBList_ECBList_MUTEX_OWNER_P *)
  destruct Hr4 as (_ & _ & _ & Hrb).
  eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_ecb;
  try eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
  pure_auto.
  do 2 destruct H.
  inverts H.
Qed.


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
         :: V$OS_STAT_Q
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
  splits; auto.
  eexists.
  splits.
  unfolds.
  simpl; eauto.
  introv Hf.
  destruct Hf as [Hf | Hf];
  inverts Hf.
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
  simpljoin1.
  inverts H.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
  simpljoin1.
  unfolds in H.
  rewrite H in H4.
  inverts H4.
  apply tcbjoin_get_a in H1.
  do 2 eexists; eauto.
Qed.

Lemma r_tcb_status_p_nrdy:
  forall v'39 v'19 x15 x10 i10 i9 i8 i7 i6 i5 i1 p t m sus v'32,
    R_TCB_Status_P
      (v'39
         :: v'19
         :: x15
         :: x10
         :: Vint32 i10
         :: Vint32 i9
         :: Vint32 i8
         :: Vint32 i7
         :: Vint32 i6 :: Vint32 i5 :: Vint32 i1 :: nil)
      v'32 (p, t, m, sus) ->
    Int.eq i9 ($ OS_STAT_RDY) = false \/ Int.eq i10 ($ 0) = false ->
    ~ (t =rdy /\ sus = false).
Proof.
  intros.
  eapply low_stat_nordy_imp_high; eauto.
Qed.

Lemma TCBList_P_impl_high_tcbcur_rdy:
  forall (tcbls : TcbMod.map) (tcur : addrval) 
         (tcurl : vallist) (tcblist : list vallist)
         (rtbl : vallist) v'39 v'19 x15 x10 i10 i9 i8 i7 i6 i5 i1,
    Int.eq i9 ($ OS_STAT_RDY) = true ->
    Int.eq i10 ($ 0) = true ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    TCBList_P (Vptr tcur) ((v'39
                              :: v'19
                              :: x15
                              :: x10
                              :: Vint32 i10
                              :: Vint32 i9
                              :: Vint32 i8
                              :: Vint32 i7
                              :: Vint32 i6
                              :: Vint32 i5 :: Vint32 i1 :: nil) :: tcblist) rtbl tcbls ->
    exists prio m, TcbMod.get tcbls tcur = Some (prio, rdy, m, false).
Proof.
  introv Heq1 Heq2 Harr Hlen Htc Htsp.
  lets Hs : TCBList_P_impl_high_tcbcur_Some  Htsp.
  simpljoin1.
  unfolds in Htsp.
  fold TCBList_P in Htsp.
  simpljoin1.
  simpl_hyp.
  unfolds in H3.
  destruct x5.
  destruct p.
  destruct p.
  simpljoin1.
  simpl_hyp.
  lets Hsd : low_stat_rdy_imp_high H5 H6 Heq2 Harr; eauto.
  subst.
  inverts H0.
  apply tcbjoin_get_a in H2.
  rewrite H2 in H.
  inverts H.
  assert(x1 = false).
  { eapply oscore_common.tcb_stat_imp_sus_false with (stat:= i9); eauto.
     eapply Inteq_true_is_Zeq in Heq2.
     eapply unsigned_inj in Heq2.
     subst; auto.
  }
 subst.
  do 2 eexists; eauto.
  Unshelve. trivial. trivial. trivial. trivial. trivial.
Qed.


Lemma TCBList_P_impl_high_tcbcur_rdy':
  forall (tcbls : TcbMod.map) (tcur : addrval) 
         (tcurl : vallist) (tcblist : list vallist)
         (rtbl : vallist) v'39 v'19 x15 x10 i10 i9 i8 i7 i6 i5 i1,
    Int.eq i9 ($ OS_STAT_RDY) = true ->
    Int.eq i10 ($ 0) = true ->
     array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    TCBList_P (Vptr tcur) ((v'39
                              :: v'19
                              :: x15
                              :: x10
                              :: Vint32 i10
                              :: Vint32 i9
                              :: Vint32 i8
                              :: Vint32 i7
                              :: Vint32 i6
                              :: Vint32 i5 :: Vint32 i1 :: nil) :: tcblist) rtbl tcbls ->
    exists  m, TcbMod.get tcbls tcur = Some (i8, rdy, m, false).
Proof.
  introv Heq1 Heq2 Harr Hlen Htc Htsp.
  lets Hs : TCBList_P_impl_high_tcbcur_Some  Htsp.
  simpljoin1.
  unfolds in Htsp.
  fold TCBList_P in Htsp.
  simpljoin1.
  simpl_hyp.
  unfolds in H3.
  destruct x5.
  destruct p.
  destruct p.
  simpljoin1.
  simpl_hyp.
  lets Hsd : low_stat_rdy_imp_high H5 H6 Heq2 Harr; eauto.
  subst.
  inverts H0.
  apply tcbjoin_get_a in H2.
  rewrite H2 in H.
  inverts H.
  assert(x1 = false).
  { eapply oscore_common.tcb_stat_imp_sus_false with (stat:= i9); eauto.
     eapply Inteq_true_is_Zeq in Heq2.
     eapply unsigned_inj in Heq2.
     subst; auto.
  }
  subst.
  eexists; eauto.
  Unshelve. trivial. trivial. trivial. trivial. trivial.
Qed.

Lemma event_type_n_match:
  forall s P i1 i0 i2 x2 x3 v'42 i10 pegrp petbl_addr,
    s|= AEventData
     (Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'42 :: Vint32 pegrp :: petbl_addr :: nil)
     (DSem i10) ** P ->
    Int.eq i1 ($ OS_EVENT_TYPE_Q) = true ->
    False.
Proof.
  intros.
  unfold AEventData in H.
  sep normal in H.
  sep split in H.
  unfolds in H1;simpl in H1;inverts H1.
  rewrite Int.eq_false in H0.
  tryfalse.
  auto.
Qed.

Lemma xx:forall x16,isptr x16 -> val_inj (notint (val_inj (val_eq x16 Vnull))) = Vint32 Int.zero -> x16=Vnull.
Proof.
  intros.
  unfolds in H0.
  remember (val_eq x16 Vnull) as X.
  unfolds in H.
  destruct H;subst.
  simpl in H0;auto.
  simpljoin1.
  simpl in H0.
  destruct x.
  simpl in H0.
  tryfalse.
Qed.

Lemma xx':forall x16,isptr x16 -> val_inj (notint (val_inj (val_eq x16 Vnull))) = Vnull -> False.
Proof.
  intros.
  unfolds in H0.
  remember (val_eq x16 Vnull) as X.
  unfolds in H.
  destruct H;subst.
  simpl in H0;auto.
  tryfalse.
  simpljoin1.
  simpl in H0.
  destruct x.
  simpl in H0.
  tryfalse.
Qed.


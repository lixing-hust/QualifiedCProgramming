Require Export sem_common.
Require Import Lia.

Open Scope code_scope.
Hint Resolve CltEnvMod.beq_refl: brel .


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

Lemma low_stat_rdy_imp_high:
  forall a b c d e f g h i j k l st rtbl p t m sus,
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    RL_TCBblk_P  (a
                    :: b
                    :: c
                    :: d
                    :: Vint32 e
                    :: Vint32 st
                    :: Vint32 f
                    :: g
                    :: h :: i :: j :: k :: l :: nil)
    ->
    R_TCB_Status_P
      (a
         :: b
         :: c
         :: d
         :: Vint32 e
         :: Vint32 st
         :: Vint32 f
         :: g
         :: h :: i :: j :: k :: l :: nil)
      rtbl (p, t, m, sus) -> Int.eq st ($ OS_STAT_RDY) = true ->
    Int.eq e ($ 0) = true ->
    t = rdy .
Proof.
  introv Hz Hlen  Ht  Hr Heq Heqq.
  funfold Ht.
  unfolds in Hr.
  simpljoin;try splits.
  clear H0 H1 H2 H4.
  unfolds in H.
  unfolds in H3.
  simpljoin;try splits.
  rename H19 into Hwp.
  rename H20 into Hwpt.
  rename H21 into Hwps.

  unfolds in H0.
  unfolds in H1.
  unfolds in H2.
  unfolds in H3.
  unfolds in H4.
  unfold RdyTCBblk in *.
  unfold V_OSTCBStat in *; simpl in *.
  unfold WaitTCBblk in *; simpl in *.
  unfold V_OSTCBPrio,  V_OSTCBDly , V_OSTCBEventPtr in *; simpl in *.
  assert (Some (Vint32 x) = Some (Vint32 x)).
  auto.
  unfold Pos.to_nat in Hlen.
  simpl in Hlen.
  assert ( 0 <= Int.unsigned x < 64 ) by lia.
  lets Hdis : prio_rtbl_dec  Hz Hlen; eauto.
  assert (if Int.eq x4 ($ OS_STAT_RDY) then  x4  =($ OS_STAT_RDY)
          else x4 <> ($ OS_STAT_RDY)).
  apply Int.eq_spec.
  rewrite Heq in H21.
  subst.
  destruct Hdis as [Hd1 | Hd2].
  assert (Some (Vint32 x) = Some (Vint32 x) /\
          prio_in_tbl x rtbl). 
  split;eauto.
  eapply H in H21.
  destruct H21 as ( Had & H21).
  destruct H21.
  destruct H21.
  rename H22 into Hzd.
  (* destruct Hzd. inverts H9. *)
  destruct Hzd as (m0 & H22).
  (* eapply H3 in H9. *)
  inverts H22; auto.
  assert (Some (Vint32 e) = Some (Vint32 e)).
  auto.
  
  destruct H21.
  destruct H21.
  tryfalse.
  destruct H21.
  destruct H21.
  tryfalse.
  destruct H21.
  destruct H21.
  tryfalse.
  destruct H21.
  tryfalse.

  
  assert (Some (Vint32 x) = Some (Vint32 x) /\
          prio_not_in_tbl x  rtbl/\Some (Vint32 e) = Some (Vint32 e)).   
  splits; auto.
  eapply H0 in H21;auto.
  simpljoin;try splits.
  eapply ltu_eq_false in H21.
  unfold Int.zero in H21.
  rewrite Heqq in H21.
  tryfalse.
Qed.

Lemma sempend_TCBListP_head_in_tcb_rdy:
  forall v'51 v'52 v'22 x9 x8 i9 i8 i6 i5 i4 i3 v'33 v'50 xx rtbl,
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
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
              rtbl v'50 ->
    i9 = $ 0 ->
    i8 = $ OS_STAT_RDY ->
    TcbMod.get v'50 v'52 = Some ( xx, rdy, x8, false).
Proof.
  intros.
  unfolds in H1.
  fold TCBList_P in H1.
  mytac_H.
  unfolds in H6.
  destruct x2; destruct p.
  destruct p.
  mytac_H.
  unfolds in H4; unfolds in H2; unfolds in H3.
  simpl in H2; simpl in H4; simpl in H3.
  inverts H2; inverts H4; inverts H3.
  assert (t = rdy).
    eapply low_stat_rdy_imp_high; eauto.
  inverts H2.
  inverts H1.
  assert ( s = false).
  { destruct s; auto.
     destruct H8 as (_ & _ & _ & Hf & _).
     destruct Hf as (Hf & _).
     specialize (Hf _ _ (eq_refl _)).
     destruct Hf as (_ & Hf).
     inverts Hf.
   }
 subst.
  unfold TcbJoin in H5.
  eapply TcbMod.join_get_l.
  eauto.
  eapply TcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.
  Unshelve.
  trivial. trivial. trivial. trivial. trivial.
Qed.

Lemma tcblist_p_node_rl_sem:
  forall v'33 v'49 v'42 v'47 v'21 x10 x9 i i8 i7 i6 i5 i4 i3 i1 v'32 ,
    TCBList_P (Vptr (v'49, Int.zero))
          ((v'47
            :: v'21
               :: x10
                  :: x9
                     :: Vint32 i8
                        :: Vint32 i7
                           :: Vint32 i6
                              :: Vint32 i5
                                 :: Vint32 i4
                                    :: Vint32 i3 :: Vint32 i1 :: nil) :: v'32)
          v'33 v'42 ->
    RL_TCBblk_P
     (v'47
      :: v'21
         :: x10
            :: x9
               :: Vint32 i
                  :: V$OS_STAT_SEM
                     :: Vint32 i6
                        :: Vint32 i5
                           :: Vint32 i4 :: Vint32 i3 :: Vint32 i1 :: nil).
Proof.
  introv Ht.
  simpl in Ht.
  mytac;simpl_hyp.
  inverts H.
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac; simpl_hyp.
  funfold H2.
  unfolds.
  do 6 eexists;splits; try unfolds; simpl;  eauto.
  splits; auto.
  eexists.
  splits.
  unfolds.
  simpl; eauto.
  introv Hf; destruct Hf as [Hf | Hf];
  inverts Hf.
Qed.

(* same copy from Mbox_common.v *)
Lemma R_ECB_PETbl_P_set_tcb_wait_hold:
forall tcbls ptcb prio m st m' x v0 v1 v prio' sus sus',
~(exists qid time, st = wait (os_stat_postq qid) time) ->
TcbMod.get tcbls ptcb = Some (prio, rdy, m, sus) ->
R_ECB_PETbl_P x (v0, v1, v) tcbls ->
R_ECB_PETbl_P x (v0, v1, v)
  (TcbMod.set tcbls ptcb (prio', st, m', sus')).
Proof.
intros.
funfold H1.
unfolds; splits; unfolds; intros.
eapply H1 in H4; eauto.
mytac.
unfold get in *; unfold TcbMap in *.
assert (Hc: ptcb = x0 \/ ptcb <> x0) by tauto.
destruct Hc.
subst.
rewrite H0 in H4; inverts H4.
repeat eexists.
rewrite TcbMod.set_a_get_a'; eauto.
eapply tidspec.neq_beq_false; eauto.
unfold get in *; unfold TcbMap in *.
assert (Hc: ptcb = tid \/ ptcb <> tid) by tauto.
destruct Hc.
subst.
rewrite TcbMod.map_get_set in H3.
inverts H3.
false. eapply H; eauto.
rewrite TcbMod.map_get_set' in H3; auto.
eapply H2; eauto.
Qed.
  
Lemma ECBList_P_high_tcb_block_hold_sem:
  forall  ectrl head tail msgql ecbls tcbls ptcb prio  m qid time sus sus',
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, rdy, m, sus) ->
    EcbMod.get ecbls qid = None ->
    ECBList_P head tail ectrl msgql ecbls 
              (TcbMod.set tcbls ptcb (prio, wait (os_stat_sem qid) time, m, sus')).
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
  destruct p. (* new add *)
  rename H3 into Hpetbl; rename H4 into H3. (* new add *)
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
  splits.
  Focus 2.
  {
    unfolds.
    intros.
    eapply Hra1 in H6;eauto.
    mytac.
    assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
    destruct H7.
    subst.
    unfold get in H6; simpl in H6.
    rewrite H0 in H6.
    inverts H6.
    exists x3 x4 x5.
    rewrite TcbMod.set_sem.
    rewrite tidspec.neq_beq_false; eauto.
  }
  Unfocus.
  Focus 2.
  {
    unfolds.
    intros.
    eapply Hra2 in H6;eauto.
    mytac.
    assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
    destruct H7.
    subst.
    unfold get in H6; simpl in H6.
    rewrite H0 in H6.
    inverts H6.
    exists x3 x4 x5.
    rewrite TcbMod.set_sem.
    rewrite tidspec.neq_beq_false; eauto.
  }
  Unfocus.
  Focus 3.
  {
    unfolds.
    intros.
    eapply Hra5 in H6;eauto.
    mytac.
    assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
    destruct H7.
    subst.
    unfold get in H6; simpl in H6.
    rewrite H0 in H6.
    inverts H6.
    exists x3 x4 x5.
    rewrite TcbMod.set_sem.
    rewrite tidspec.neq_beq_false; eauto.
  }
  Unfocus.
  {
    unfolds.
    intros.
    eapply Hra3 in H6;eauto.
    mytac.
    assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
    destruct H7.
    subst.
    unfold get in H6; simpl in H6.
    rewrite H0 in H6.
    inverts H6.
    exists x3 x4 x5.
    rewrite TcbMod.set_sem.
    rewrite tidspec.neq_beq_false; eauto.
  }
  {
    unfolds.
    intros.
    eapply Hra4 in H6;eauto.
    mytac.
    assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
    destruct H7.
    subst.
    unfold get in H6; simpl in H6.
    rewrite H0 in H6.
    inverts H6.
    exists x3 x4 x5.
    rewrite TcbMod.set_sem.
    rewrite tidspec.neq_beq_false; eauto.
  }
  unfolds.
  splits.
  Focus 2.
  {
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
  }
  Unfocus.

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
  3:{
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
  }
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
  (* new add about petbl *)
  eapply R_ECB_PETbl_P_set_tcb_wait_hold; eauto.
  introv Hf. destruct Hf as (qd & wt & Hf). inverts Hf.
  (* end of new add *)
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

Lemma R_ECB_ETbl_P_high_tcb_block_hold:
  forall (l : addrval) (vl : vallist) (egrp : int32) 
    (v2 v3 v4 v5 : val) (etbl : vallist) (tcbls : TcbMod.map)
    (ptcb : tidspec.A) (prio : int32) (st : taskstatus) 
    (m : msg) sus sus' (y bity bitx ey : int32) time (av : addrval) petbl pegrp petbl_addr,
  Int.unsigned prio < 64 ->
  R_PrioTbl_P vl tcbls av ->
  R_ECB_ETbl_P l
    (V$OS_EVENT_TYPE_SEM :: Vint32 egrp :: v2 :: v3 :: v4 :: v5 :: Vint32 pegrp :: petbl_addr :: nil, etbl, petbl)
    tcbls ->
  TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
  y = Int.shru prio ($ 3) ->
  bity = Int.shl ($ 1) y ->
  bitx = Int.shl ($ 1) (prio &ᵢ $ 7) ->
  nth_val ∘(Int.unsigned y) etbl = Some (Vint32 ey) ->
  R_ECB_ETbl_P l
    (V$OS_EVENT_TYPE_SEM
     :: Vint32 (Int.or egrp bity) :: v2 :: v3 :: v4 :: v5 :: Vint32 pegrp :: petbl_addr :: nil,
    update_nth_val ∘(Int.unsigned y) etbl (Vint32 (Int.or ey bitx)), petbl)
    (TcbMod.set tcbls ptcb (prio, wait (os_stat_sem l) time, m, sus'))
.
Proof.
  introv Hran Hrs  Hre Htc Hy Hb1 Hb2 Hnth.
  subst.
  unfolds in Hre.
  destruct Hre as (Hre1 & Hre2 & Het).
  unfolds.
  splits.
  unfolds.
  splits.
  Focus 2.
  {
    unfolds.
    intros.
    destruct Hre1 as (_ & Hre1 & _ & _).
    destruct Hre2 as (_ & Hre2 & _ & _).
    unfolds in Hre1.
    unfolds in Hre2.
    assert (prio = $ prio0 \/ prio <> $ prio0) by tauto.
    destruct H1.
    subst.
    exists ptcb time m.
    rewrite TcbMod.set_sem.
    erewrite tidspec.eq_beq_true; eauto.
    lets Hres : prio_wt_inq_keep Hran H1 Hnth .
    destruct Hres.
    apply H2 in H.
    apply Hre1 in H.
    mytac.
    exists x x0 x1.
    assert (x = ptcb \/ x <> ptcb) by tauto.
    destruct H4.
    subst.
    unfold get in H; simpl in H.
    rewrite Htc in H.
    inverts H.
    tryfalse.
    rewrite TcbMod.set_sem.
    erewrite tidspec.neq_beq_false; eauto.
    unfolds. 
    simpl; auto.
  }
  Unfocus.
  Focus 2.
  {
    unfolds.
    intros.
    usimpl H0.
  }
  Unfocus.
  Focus 3.
  {
    unfolds.
    intros.
    usimpl H0.
  }
  Unfocus.
  {
    unfolds.
    intros.
    usimpl H0.
  }
  {
    unfolds.
    intros.
    usimpl H0.
  }
  unfolds.
  splits.
  Focus 2.
  {
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
    exists ( prio0 &ᵢ $ 7).
    exists (Int.shru prio0 ($3)).
    exists ((Int.or ey ($ 1<<ᵢ(prio0 &ᵢ $ 7)))).
    splits; eauto.
    clear - Hran.
    int auto.
    eapply pure_lib.update_nth; eauto.
    rewrite Int.and_commut.
    rewrite Int.or_commut.
    unfold Int.one.
    rewrite Int.and_or_absorb.
    auto.
    unfolds; simpl; auto.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.neq_beq_false in H; eauto.
    unfolds in Hre2.
    destruct Hre2 as (_ & Hre2 & _ & _).
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
  }
  Unfocus.
  Focus 2.
  {
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
  }
  Unfocus.
  Focus 3.
  {
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
    destruct Hre2 as (_&_& _ &_&Hre2).
    apply Hre2 in H.
    destruct H.
    usimpl H1.
  }
  Unfocus.
  {
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
    destruct Hre2 as (Hre2&_).
    apply Hre2 in H.
    destruct H.
    usimpl H1.
  }
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
  simpl.
  unfolds.
  branch 2.
  unfolds; simpl; auto.
Qed.

(* copy from task_pure.v *)

Lemma Z_and_onebitmask:
  forall a b,
    0<=b ->
    Z.land a (Z.shiftl 1 b) = Z.shiftl 1 b \/ Z.land a (Z.shiftl 1 b) = 0.
Proof.
  intros.
  
  assert (Z.testbit a b = true \/ Z.testbit a b= false).
  destruct (Z.testbit a b); tauto.
  destruct H0.

  left.
  eapply Byte.equal_same_bits.
  intros.
  rewrite Z.land_spec.

  assert ( b = i \/ b <> i).
  tauto.
  destruct H2.
  subst.
  rewrite H0.
  simpl.
  auto.
  assert (i = (i-b)+b).
  lia.
  rewrite H3 at 2 3.
  rewrite Z.shiftl_spec_alt.
  rewrite Byte.Ztestbit_1.
  assert (i - b <> 0).
  lia.
  remember ( zeq (i - b) 0 ).
  destruct s.
  tryfalse.
  simpl.
  rewrite andb_false_r.
  reflexivity.
  auto.
  
  right.

  eapply Byte.equal_same_bits.
  intros.
  assert (i = (i-b)+b).
  lia.
  rewrite Z.land_spec.
  rewrite H2 at 2 .
  rewrite Z.shiftl_spec_alt.
  rewrite Byte.Ztestbit_1.
  rewrite Byte.Ztestbit_0.
  assert ( i = b \/ i <> b).
  tauto.
  destruct H3.
  subst.
  rewrite H0.
  simpl.
  reflexivity.

  remember ( zeq (i - b) 0 ).
  destruct s.
  assert (i = b).
  lia.
  tryfalse.
  simpl.
  rewrite andb_false_r.
  reflexivity.
  auto.

Qed.

Lemma and_onebitmask:
  forall z x ,
    Int.unsigned x <= 7 ->
    z&ᵢ($ 1 <<ᵢ x) = $ 1 <<ᵢ x \/ z&ᵢ($ 1 <<ᵢ x) = $ 0.
Proof.
  intros.
  unfold Int.and.
  unfold Int.shl.
  repeat ur_rewriter.
  Focus 2.
  mauto.
  assert (0 <= Int.unsigned x).
  int auto.

  lets bb: Z_and_onebitmask (Int.unsigned z) (Int.unsigned x) H0.
  destruct bb.
  left.
  rewrite H1.
  auto.
  right.
  rewrite H1.
  auto.
Qed.

Lemma not_prio_in_tbl_is_prio_not_in_tbl:
  forall p rtbl,
    ~prio_in_tbl p rtbl ->
    prio_not_in_tbl p rtbl.
Proof.
  intros.
  unfold prio_in_tbl in H.
  unfold prio_not_in_tbl.
  intros.
  assert (z&ᵢ($ 1 <<ᵢ x) = $ 1 <<ᵢ x \/ z&ᵢ($ 1 <<ᵢ x) = $ 0).
  apply and_onebitmask.
  subst.
  rewrite Int.and_commut.
  eapply Z.le_trans.

  apply Int.and_le. 
  clear.
  int auto.

  destruct H3.

  false.
  apply H.
  intros.
  rewrite <- H4 in H0.
  subst.
  rewrite H6 in H2.
  inverts H2.
  auto.
  auto.
Qed.
(* end of copy *)

Lemma TCBList_P_tcb_block_hold :
  forall ptcb v1 v2 v3 v5 v6 v8 v9 v10 v11 rtbl vl
    tcbls prio st m qid time ry,
    TCBList_P (Vptr ptcb) ((v1::v2::v3::m::v5::(Vint32 v6)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, false) ->
    prio_neq_cur tcbls ptcb ( prio) ->
    st = rdy \/ (exists n, st = wait os_stat_time n) -> 
    nth_val (nat_of_Z (Int.unsigned v9)) rtbl = Some (Vint32 ry) ->
    time <> Int.zero ->
    TCBList_P (Vptr ptcb)
              ((v1::v2::(Vptr qid)::m::(Vint32 time)::(Vint32 ($ OS_STAT_SEM))::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)
                 ::vl) 
              (update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (Int.and ry (Int.not v10)))) 
              (TcbMod.set tcbls ptcb ( prio, wait (os_stat_sem qid) (Some time), m, false)).
Proof.
  introv  Htcb Htm Hst Hprio Hnth Hneq.
  unfolds in Htcb;fold TCBList_P in Htcb.
  mytac.
  inverts H.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds.
  fold TCBList_P.
  exists x x0.
  exists x1.
  exists (prio,wait (os_stat_sem qid) (Some time),m, false).
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
  unfolds.
  intros.
  unfolds in H.
  mytac.
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

(* new add *)
Lemma TCBList_P_tcb_block_hold' :
    forall ptcb v1 v2 v3 v5 v6 v8 v9 v10 v11 rtbl vl
           tcbls prio st m sus qid time ry stat,
    TCBList_P (Vptr ptcb) ((v1::v2::v3::m::v5::(Vint32 v6)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    prio_neq_cur tcbls ptcb ( prio) ->
    st = rdy \/ (exists n, st = wait os_stat_time n) -> 
    nth_val (nat_of_Z (Int.unsigned v9)) rtbl = Some (Vint32 ry) ->
    time <> Int.zero ->
    stat = (if sus then Int.or (Int.repr OS_STAT_SEM) (Int.repr OS_STAT_SUSPEND) else (Int.repr OS_STAT_SEM))  ->
    TCBList_P (Vptr ptcb)
              ((v1::v2::(Vptr qid)::m::(Vint32 time)::(Vint32 stat)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)  ::vl) 
              (update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (Int.and ry (Int.not v10))))
              (TcbMod.set tcbls ptcb ( prio, wait (os_stat_sem qid) (Some time), m, sus)).
Proof.
  introv  Htcb Htm Hst Hprio Hnth Hneq Hstat.
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
  exists (prio,wait (os_stat_sem qid) (Some time),m, true).
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
  eexists.
  eexists.
  splits; eauto.
  splits; try solve [ unfolds; intros; inverts H0].
  unfolds.
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
  splits; try solve [ unfolds; intros; inverts H].
}
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac; simpl_hyp.
  funfold H2.
  eapply update_rtbl_tcblist_hold; eauto.
  unfolds in Hst.
  intros.
  lets Has : tcbjoin_get_getneq H1 H.
  destruct Has.
  eapply Hst; eauto.
Qed.

Lemma TCBList_P_tcb_block_hold_none :
  forall ptcb v1 v2 v3 v5 v6 v8 v9 v10 v11 rtbl vl
    tcbls prio st m qid time ry,
    TCBList_P (Vptr ptcb) ((v1::v2::v3::m::v5::(Vint32 v6)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, false) ->
    prio_neq_cur tcbls ptcb ( prio) ->
    st = rdy \/ (exists n, st = wait os_stat_time n) -> 
    nth_val (nat_of_Z (Int.unsigned v9)) rtbl = Some (Vint32 ry) ->
    time = Int.zero ->
    TCBList_P (Vptr ptcb)
              ((v1::v2::(Vptr qid)::m::(Vint32 time)::(Vint32 ($ OS_STAT_SEM))::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)
                 ::vl) 
              (update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (Int.and ry (Int.not v10)))) 
              (TcbMod.set tcbls ptcb ( prio, wait (os_stat_sem qid) None, m, false)).
Proof.
  introv  Htcb Htm Hst Hprio Hnth Hneq.
  unfolds in Htcb;fold TCBList_P in Htcb.
  mytac.
  inverts H.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds.
  fold TCBList_P.
  exists x x0.
  exists x1.
  exists (prio,wait (os_stat_sem qid) None,m, false).
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
  unfolds.
  intros.
  unfolds in H.
  mytac.
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
  }
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac; simpl_hyp.
  funfold H2.
  eapply update_rtbl_tcblist_hold; eauto.
  unfolds in Hst.
  intros.
  lets Has : tcbjoin_get_getneq H1 H.
  destruct Has.
  eapply Hst; eauto.
  Unshelve.
  exact Int.zero. 
Qed.

Lemma TCBList_P_tcb_block_hold_none' :
    forall ptcb v1 v2 v3 v5 v6 v8 v9 v10 v11 rtbl vl
           tcbls prio st m sus qid time ry stat,
    TCBList_P (Vptr ptcb) ((v1::v2::v3::m::v5::(Vint32 v6)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    prio_neq_cur tcbls ptcb ( prio) ->
    st = rdy \/ (exists n, st = wait os_stat_time n) -> 
    nth_val (nat_of_Z (Int.unsigned v9)) rtbl = Some (Vint32 ry) ->
    time = Int.zero ->
    stat = (if sus then Int.or (Int.repr OS_STAT_SEM) (Int.repr OS_STAT_SUSPEND) else (Int.repr OS_STAT_SEM))  ->
    TCBList_P (Vptr ptcb)
              ((v1::v2::(Vptr qid)::m::(Vint32 time)::(Vint32 stat)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)  ::vl) 
              (update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (Int.and ry (Int.not v10))))
              (TcbMod.set tcbls ptcb ( prio, wait (os_stat_sem qid) None, m, sus)).
Proof.
  introv  Htcb Htm Hst Hprio Hnth Hneq Hstat.
  destruct sus; subst.
  2: eapply TCBList_P_tcb_block_hold_none; eauto.
  unfolds in Htcb;fold TCBList_P in Htcb.
  mytac.
  inverts H.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds.
  fold TCBList_P.
  exists x x0.
  exists x1.
  exists (prio,wait (os_stat_sem qid) None,m, true).
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
  eexists.
  eexists.
  splits; eauto.
  splits; try solve [ unfolds; intros; inverts H0].
  unfolds.
  splits; try solve [ unfolds; intros; inverts H].
  unfolds.
  intros.
  inverts H.
  splits; eauto.
  right. eexists.
  eauto.
  unfolds; try splits; simpl; eauto.
  eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto.
  eapply prio_update_self_not_in; eauto.
  splits; try solve [ unfolds; intros; inverts H].
}
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac; simpl_hyp.
  funfold H2.
  eapply update_rtbl_tcblist_hold; eauto.
  unfolds in Hst.
  intros.
  lets Has : tcbjoin_get_getneq H1 H.
  destruct Has.
  eapply Hst; eauto.
Qed.

Lemma RH_CurTCB_high_block_hold_sem :
  forall ptcb tcbls prio st qid time m sus sus',
    RH_CurTCB ptcb tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    RH_CurTCB ptcb (TcbMod.set tcbls ptcb
        (prio, wait (os_stat_sem qid) time, m, sus')).
Proof.
  introv Hr Ht.
  unfolds in Hr.
  mytac.
  unfold get in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  unfolds.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; eauto.
Qed.

Lemma RH_TCBList_ECBList_P_high_block_hold_sem :
  forall ecbls tcbls pcur qid m cnt wl prio  time sus sus',
    RH_TCBList_ECBList_P ecbls tcbls pcur ->
    EcbMod.get ecbls qid = Some (abssem cnt, wl) ->
    TcbMod.get tcbls pcur = Some (prio, rdy, m, sus) ->
    RH_TCBList_ECBList_P (EcbMod.set ecbls qid (abssem cnt, pcur::wl)) (TcbMod.set tcbls pcur (prio, wait (os_stat_sem qid) time, m, sus')) pcur. 
Proof.
  introv Hr Ht He.
  unfolds in Hr.
  destruct Hr as (Hr3 & Hr1 & Hr2 & Hr4 & Hr5).
  unfolds.
  splits.
  Focus 2.
  {
    unfolds.
    splits.
    intros.
    mytac.
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
    assert (EcbMod.get ecbls eid = Some (abssem n, wl) /\ In tid wl) by eauto.
    apply Hr1 in H0.
    mytac.
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
    assert (EcbMod.get ecbls eid = Some (abssem n, wls) /\ In tid wls) by eauto.
    apply Hr1 in H2.
    mytac.
    assert (pcur = tid \/ pcur <> tid) by tauto.
    destruct  H3.
    subst.
    unfold get in H2; simpl in H2.
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
    exists cnt.
    exists (tid::wl).
    splits; eauto.
    rewrite EcbMod.set_sem.
    rewrite tidspec.eq_beq_true; eauto.
    simpl; left; auto.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; eauto.
    apply Hr1 in H.
    mytac.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H2.
    subst.
    rewrite EcbMod.set_sem.
    rewrite tidspec.eq_beq_true; auto.
    do 2 eexists; splits; eauto.
    unfold get in H; simpl in H.
    rewrite H in Ht.
    inverts Ht.
    simpl.
    right; auto.
    rewrite EcbMod.set_sem.
    rewrite tidspec.neq_beq_false; auto.
    do 2 eexists; splits; eauto.
  }
  Unfocus.
  Focus 2.
  {
    splits.
    intros.
    mytac.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H1.
    subst.
    rewrite EcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; auto.
    inverts H.
    rewrite EcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; auto.
    assert (EcbMod.get ecbls eid =Some (absmbox n, wls) /\ In tid wls) by eauto.
    apply Hr2 in H2.
    mytac.
    assert (pcur = tid \/ pcur <> tid) by tauto.
    destruct  H3.
    subst.
    unfold get in H2; simpl in H2.
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
    apply Hr2 in H.
    mytac.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H2.
    subst.
    unfold get in H; simpl in H.
    rewrite H in Ht.
    inverts Ht.
    rewrite EcbMod.set_sem.
    rewrite tidspec.neq_beq_false; auto.
    do 2 eexists; splits; eauto.
  }
  Unfocus.
  Focus 3.
  {
    splits.
    intros.
    mytac.
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
    mytac.
    assert (pcur = tid \/ pcur <> tid) by tauto.
    destruct  H3.
    subst.
    unfold get in H2; simpl in H2.
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
    mytac.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H2.
    subst.
    unfold get in H; simpl in H.
    rewrite H in Ht.
    inverts Ht.
    rewrite EcbMod.set_sem.
    rewrite tidspec.neq_beq_false; auto.
    eexists; splits; eauto.
  }
  Unfocus.
  {
    splits.
    intros.
    mytac.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H1.
    subst.
    rewrite EcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; auto.
    inverts H.
    rewrite EcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; auto.
    assert (EcbMod.get ecbls eid = Some (absmsgq x y pqwaitset, qwaitset) /\ In tid qwaitset) by eauto.
    apply Hr3 in H2.
    mytac.
    assert (pcur = tid \/ pcur <> tid) by tauto.
    destruct  H3.
    subst.
    unfold get in H2; simpl in H2.
    rewrite H2 in He.
    inverts He. 
    do 4 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
    (* new add about postq *)
    intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmsgq x y pqwaitset, qwaitset) /\ In tid pqwaitset) by eauto.
  apply Hr3 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 4 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
    (* end of new add *)
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
    mytac.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H2.
    subst.
    unfold get in H; simpl in H.
    rewrite H in Ht.
    inverts Ht.
    rewrite EcbMod.set_sem.
    rewrite tidspec.neq_beq_false; auto.
    do (* 3 *) 4 eexists; splits; eauto.
    (* new add about postq *)
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
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do (* 3 *) 4 eexists; splits; eauto.
  (* end of new add *)
  }
  {
    splits.
    intros.
    mytac.
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
    mytac.
    assert (pcur = tid \/ pcur <> tid) by tauto.
    destruct  H3.
    subst.
    unfold get in H2; simpl in H2.
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
    apply Hr4 in H.
    mytac.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H2.
    subst.
    unfold get in H; simpl in H.
    rewrite H in Ht.
    inverts Ht.
    rewrite EcbMod.set_sem.
    rewrite tidspec.neq_beq_false; auto.
    do 3 eexists; splits; eauto.

    apply Mutex_owner_hold_for_set_tcb.
    eapply Mutex_owner_set; eauto.
    intro; mytac.
    tryfalse.

    inverts Hr4.
    apply H0.

    (* new add about RH_TCBList_ECBList_MUTEX_OWNER_P *)
    funfold Hr4.
    eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_ecb;
    try eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
    intro Hf.
    destruct Hf as (vpip & vo & Hf).
    inverts Hf.
  }
Qed.



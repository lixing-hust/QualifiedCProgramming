
Require Import base_tac. 
Require Import memory. 
Require Import if_language.
Require Import if_opsem.
Require Import mq_apispecs.
Require Import buffer_apispecs. 
Require Import osspecs. 
Require Import properties.

Require Import if_assms.
Require Import sem_prop.
Require Import if_succ_gen.
Require Import if_common_lemmas. 
Require Import spec_aux_defs. 
Require Import confidentiality_tactics.
Require Import confidentiality_lemmas. 

Require Import FunctionalExtensionality.

Require Import math_auto. 
Require Import seplog_lemmas. 

Require Import equiv_prop.
Require Import ct_pp_lemmas. 

Set Keyed Unification.  


Lemma buf_in_dom_impl:
  forall O1 O2 v, 
    data_equiv_schd O1 O2 -> 
    (forall (td : taskdom) (eid : addrval),
        dom_cur_tsk O1 td -> v = Vptr eid -> buf_in_dom eid td = false) ->
    (forall (td : taskdom) (eid : addrval),
        dom_cur_tsk O2 td -> v = Vptr eid -> buf_in_dom eid td = false). 
Proof.
  introv Hdes Hbid1.
  introv Hdct Hv.
  lets H__: data_equiv_schd_dom_equiv Hdes; eauto.  
  eapply H__ in Hdct; eauto. 
Qed. 

Lemma buf_in_dom_contra:
  forall O1 O2 v, 
    data_equiv_schd O1 O2 -> 
    (forall (td : taskdom) (eid : addrval),
        dom_cur_tsk O1 td -> v = Vptr eid -> buf_in_dom eid td = false) ->
    ~(forall (td : taskdom) (eid : addrval),
          dom_cur_tsk O2 td -> v = Vptr eid -> buf_in_dom eid td = false) ->
    False. 
Proof.
  introv Hdes Hbid1.
  introv Hf.
  lets H_: buf_in_dom_impl Hdes Hbid1; eauto. 
Qed. 

Lemma n_buf_in_dom_false_dest:
  forall v O pr t,
    task_prio_id O pr t ->
    get O curtid = Some (oscurt t) -> 
    (~
       (forall (td : taskdom) (eid : addrval),
           dom_cur_tsk O td -> v = Vptr eid -> buf_in_dom eid td = false)) ->
    v = Vnull \/ (exists a, v = Vptr a) -> 
    buffer_indom v O pr. 
Proof.
  introv Htpi Hgct Hn Hv.
  unfolds.
  destruct Hv.
  - left; auto.
  - simpljoin.
    right.
    eexists.
    split; eauto.
    destruct (buf_in_dom x (dom_for_prio pr)) eqn: E.
    + auto.
    + false.
      apply Hn.
      introv Hd Hveq.
      inverts Hveq.
      unfolds in Hd.
      simpljoin.
      l_rew12_inv2 (get O curtid).
      apply2 (task_prio_id O) (task_prio_id O) prio_unique.
      auto. 
Qed. 

Lemma buffer_equiv_noque_false_: 
  forall vp v0 O1 O2 pr, 
    buffer_equiv (dom_for_prio pr) O1 O2 ->
    buffer_indom vp O1 pr -> 
    (exists qid els,
        vp = Vptr qid /\
          v0 <> Vnull /\
          get O1 absecblsid = Some (absecblist els) /\
          ~ (exists x y pwl wls, get els qid = Some (absmsgq x y pwl, wls))) ->
    (exists qid els,
        vp = Vptr qid /\
          v0 <> Vnull /\
          get O2 absecblsid = Some (absecblist els) /\
          ~ (exists x y pwl wls, get els qid = Some (absmsgq x y pwl, wls))). 
Proof.
  introv Hbe Hbi1 Hex.
  unfolds in Hbe.
  simpljoin.
  unfolds in Hbi1.
  rem_dis.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  match goal with H: forall _, _ |- _ => specializes H; eauto end.
  l_rew12_inv2 (get O1 absecblsid).
  simpljoin.
  do 2 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  introv Hex.
  match goal with H: ~_ |- _ => apply H end.
  match goal with
    H1: context [absecblist ?x1], H2: context [absecblist ?x2] |- _ =>
      rename x1 into els1; rename x2 into els2
  end.
  match goal with H: buf_in_dom ?x _ = true |- _ => rename x into eid end.
  simpljoin.
  assert (Hex: exists ed ws, get els2 eid = Some (ed, ws))
    by (do 2 eexists; eauto).
  match goal with H: _ <-> _ |- _ => apply H in Hex end.
  simpljoin.
  match goal with H: forall _, _ |- _ => specializes H; eauto end.
  simpljoin.
  unfold mq_ed_equiv in *.
  simpljoin.
  do 4 eexists; eauto. 
Qed.       
      
Lemma buffer_equiv_noque_false: 
  forall vp v0 O1 O2 pr, 
    buffer_equiv (dom_for_prio pr) O1 O2 ->
    buffer_indom vp O1 pr -> 
    (exists qid els,
        vp = Vptr qid /\
          v0 <> Vnull /\
          get O1 absecblsid = Some (absecblist els) /\
          ~ (exists x y pwl wls, get els qid = Some (absmsgq x y pwl, wls))) ->
    ~(exists qid els,
          vp = Vptr qid /\
            v0 <> Vnull /\
            get O2 absecblsid = Some (absecblist els) /\
            ~ (exists x y pwl wls, get els qid = Some (absmsgq x y pwl, wls))) ->
    False. 
Proof.
  introv Hbe Hbi Hex Hnex.
  lets H__: buffer_equiv_noque_false_ Hex; eauto. 
Qed.

    
Ltac symexe :=
  match goal with
    H: spec_step _ _ _ _ _ _ |- _ => inverts H; symexe 
  | H: nabt (set _ _ (curs (hapi_code (ABORT)), _)) |- _ =>
      apply nabt_abt_false in H; solve [false]; symexe 
  | H: ~(exists _, END _ = END _) /\ _ |- _ =>
      let hf := fresh in (destruct H as (hf & _); false; apply hf; eexists; eauto); symexe 
  | H: _ /\ (ABORT <> ABORT) |- _ => 
      let hf := fresh in (destruct H as (_ & hf)); false; apply hf; auto; symexe
  | H1: ?P, H2: ~(?P) |- _ => try solve [false]
  | H: ?x1 <> ?x2 |- _ => unify x1 x2; try solve [false]
  | H1: join ?O01 ?Of1 ?O1, H1': join ?O01 ?Of1 ?O1',
        H2: join ?O02 ?Of2 ?O2, H2': join ?O02 ?Of2 ?O2' |- _ =>
      (assert (O1 = O1') by join auto; subst);
      (assert (O2 = O2') by join auto; subst)
  | act: action, H1: ?f _ ?O1 ?act (_, Some ?O1'), H2: ?f _ ?O2 ?act (_, Some ?O2') |- _ => 
      (assert (O1 = O1') by eauto with oeq_lemmas; subst);
      (assert (O2 = O2') by eauto with oeq_lemmas; subst); 
      symexe 
  | H1: ?P, H2: ~(?P') |- _ => 
      try solve [
          match goal with
            H: context[buffer_equiv] |- _ => 
              eapply buffer_equiv_sym in H; eauto;
              false; eapply buffer_equiv_noque_false; eauto
          end |
          false; eapply buffer_equiv_noque_false; eauto
        ] 
  | _ => idtac
  end. 

Ltac solve_bufferpost_eq Hlenvl Hlenvl1 Hlenvl2 k :=
  unfolds;
  match type of Hlenvl with length ?vl = _ => exists vl end; 
  match type of Hlenvl1 with length ?vl = _ => exists vl end; 
  match type of Hlenvl2 with length ?vl = _ => exists vl end; 
  exists k%nat; 
  split; [simpl; auto | 
           split; [ simpl; auto | 
                    split;  [ simpl; auto | 
                              split;  [ simpl; auto | 
                                        simpl; auto]]]].

Lemma cmd_equiv_ret_val_anno:
  forall i0 O1 O2 pr (v v0: val)
         (Hlenvl : length (v :: v0 :: nil) = 2%nat)
         (Hlenvl1 : length (Vint32 i0 :: nil) = 1%nat)
         (Hlenvl2 : length (Vint32 i0 :: nil) = 1%nat),
    cmd_equiv pr
      (curs (hapi_code ((ar_true, (Vint32 i0) :: nil) # ret_val [|Vint32 i0 :: nil|])))
      (curs (hapi_code ((ar_true, (Vint32 i0) :: nil) # ret_val [|Vint32 i0 :: nil|]))) O1 O2.
Proof.
  intros.
  unfold cmd_equiv.
  right.
  do 2 eexists. split; eauto. split; eauto.
  split. simpl. auto.
  split. simpl. auto.
  split.
  (* vl_equiv *)
  eapply veq_vlequiv; eauto.
  simpl. eauto.
  simpl. eauto.
  (* stmt_equiv *)
  unfold stmt_equiv.
  right.
  split.
  introv Hf. simpljoin. tryfalse.
  right. right. right. right. right. right. right. left.
  solve_bufferpost_eq Hlenvl Hlenvl1 Hlenvl2 6%nat.
Qed.

Lemma buffer_equiv_qlen_impl_: 
  forall vp O1 O2 pr v0,
    buffer_equiv (dom_for_prio pr) O1 O2 ->
    buffer_indom vp O1 pr -> 
    (exists qid qls ml n pwl wl,
        vp = Vptr qid /\
          v0 <> Vnull /\
          get O1 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq ml n pwl, wl) /\
          Z.of_nat (length ml) >= Int.unsigned n) ->
    (exists qid qls ml n pwl wl,
        vp = Vptr qid /\
          v0 <> Vnull /\
          get O2 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq ml n pwl, wl) /\
          Z.of_nat (length ml) >= Int.unsigned n). 
Proof.
  introv Hbe Hbi Hlen1.
  destruct Hlen1 as (qid & qls & ml & n & pwl & wl & Hvp1 & Hne & Hget & Hgetq & Hlge).
  unfolds in Hbe.
  unfold buffer_indom in *.
  rem_dis.
  match goal with H: (Vptr _ = Vptr _)  |- _ => inverts H end.
  match goal with H: forall _, _ |- _ => specializes H; eauto; destruct H as (Hiff & Ha) end.
  destruct Hiff as (Hlr & Hrl).
  l_rew21_inv1 (get O1 absecblsid).
  specializes Hlr; eauto.
  simpljoin. 
  specializes Ha; eauto.
  destruct Ha as (Hme & Hte).
  unfolds in Hme.
  simpljoin.
  match goal with H: absmsgq _ _ _ = absmsgq _ _ _ |- _ => inverts H end.
  do 6 eexists.
  split; eauto.  
Qed.

Lemma buffer_equiv_qlen_impl:
  forall vp O1 O2 pr v0,
    buffer_equiv (dom_for_prio pr) O1 O2 ->
    buffer_indom vp O1 pr -> 
    (exists qid qls ml n pwl wl,
        vp = Vptr qid /\
          v0 <> Vnull /\
          get O1 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq ml n pwl, wl) /\
          Z.of_nat (length ml) >= Int.unsigned n) ->
    (~(exists qid qls ml n pwl wl,
        vp = Vptr qid /\
          v0 <> Vnull /\
          get O2 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq ml n pwl, wl) /\
          Z.of_nat (length ml) >= Int.unsigned n)) ->
    False. 
Proof.
  introv Hbe Hbi Hlen Hnlen.
  lets H__: buffer_equiv_qlen_impl_ Hlen; eauto.
Qed.

Lemma buffer_equiv_qlen_lt_impl_:
  forall vp O1 O2 pr v0,
    buffer_equiv (dom_for_prio pr) O1 O2 ->
    buffer_indom vp O1 pr -> 
    (exists qls qid ml n pwl,
        vp = Vptr qid /\
          v0 <> Vnull /\
          get O1 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq ml n pwl, nil) /\
          Z.of_nat (length ml) < Int.unsigned n) ->
    (exists qls qid ml n pwl,
        vp = Vptr qid /\
          v0 <> Vnull /\
          get O2 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq ml n pwl, nil) /\
          Z.of_nat (length ml) < Int.unsigned n). 
Proof.
  introv Hbe Hbi Hlt.
  destruct Hlt as (qls & qid & ml & n & pwl & Hvp1 & Hne & Hget & Hgetq & Hlge).
  unfolds in Hbe.
  unfold buffer_indom in *.
  simpljoin. 
  rem_dis.
  match goal with H: (Vptr _ = Vptr _)  |- _ => inverts H end.
  match goal with H: forall _, _ |- _ => specializes H; eauto; destruct H as (Hiff & Ha) end.
  destruct Hiff as (Hlr & Hrl).
  l_rew21_inv1 (get O1 absecblsid).
  specializes Hlr; eauto.
  simpljoin. 
  specializes Ha; eauto.
  destruct Ha as (Hme & Hte).
  unfolds in Hme.
  simpljoin.
  match goal with H: absmsgq _ _ _ = absmsgq _ _ _ |- _ => inverts H end.
  unfolds in Hte.
  destruct Hte as (Heql & _).
  match type of Heql with _ = length ?x => destruct x; simpl in Heql; tryfalse end.
  do 6 eexists.
  split; eauto.
  split; eauto.
Qed.

Lemma buffer_equiv_qlen_lt_impl:
  forall vp O1 O2 pr v0,
    buffer_equiv (dom_for_prio pr) O1 O2 ->
    buffer_indom vp O1 pr -> 
    (exists qls qid ml n pwl,
        vp = Vptr qid /\
          v0 <> Vnull /\
          get O1 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq ml n pwl, nil) /\
          Z.of_nat (length ml) < Int.unsigned n) ->
    (~(exists qls qid ml n pwl,
           vp = Vptr qid /\
             v0 <> Vnull /\
             get O2 absecblsid = Some (absecblist qls) /\
             get qls qid = Some (absmsgq ml n pwl, nil) /\
             Z.of_nat (length ml) < Int.unsigned n)) ->
    False. 
Proof.
  introv Hbe Hbi Hlt Hnlt.
  lets H__: buffer_equiv_qlen_lt_impl_ Hlt; eauto. 
Qed. 

Lemma qpost_nowt_succ_cpid_same:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O cspaceid = get O' cspaceid.  
Proof.
  introv Hpost Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed. 

Lemma qpost_nowt_succ_ret: 
  forall vp v i O act v' O', 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O act (v', Some O') ->
    i = $OS_NO_ERR.
Proof. 
  introv Hpost.
  inverts Hpost.
  inverts H.
  simpljoin.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ :: _ = _ |- _ => inverts H end. 
  auto.
Qed. 

Require Import hasrt_sat_preserve. 
Lemma qpost_nowt_succ_mqref_preserve0: 
  forall vp v i O v' O' act, 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O act (v', Some O') ->
    mq_ref_preserved O O'. 
Proof.
  introv Hpost.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  rewrite set_a_get_a' in Hget'; eauto.
  2: { introv Hf; inverts Hf. }
  l_rew21_inv1 (get O absmqattrid).
  introv Hg.
  simpljoin.
  do 6 eexists; eauto. 
Qed.

Lemma qpost_nowt_succ_mqref_preserve: 
  forall vp v i O v' O' O0 O0' Of act, 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ref_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hor: get O0 absmqattrid = Some (absmqattr mqs)
               \/ get Of absmqattrid = Some (absmqattr mqs)).
  {
    eapply join_get_or; eauto. 
  }
  destruct Hor as [Hl | Hr].
  -
    eapply join_get_get_l with (a:=absmqattrid) (b:=absmqattr mqs) in Hjo'; eauto.
    2: { 
      rewrite set_a_get_a'; eauto.
      introv Hf; inverts Hf. 
    }
    l_rew21_inv1 (get O' absmqattrid).
    introv Hg. auto. 
  -
    assert (get O' absmqattrid = Some (absmqattr mqs)).
    { eapply join_get_get_r; eauto. }
    l_rew21_inv1 (get O' absmqattrid).
    introv Hg. auto. 
Qed.

Lemma qpost_nowt_succ_qprt_preserve: 
  forall vp v i O v' O' O0 O0' Of act, 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    qprt_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hor: get O0 osdomainportid = Some (osdomainport dpl)
               \/ get Of osdomainportid = Some (osdomainport dpl)).
  {
    eapply join_get_or; eauto. 
  }
  destruct Hor as [Hl | Hr].
  -
    eapply join_get_get_l with (a:=osdomainportid) (b:=osdomainport dpl) in Hjo'; eauto.
    2: { 
      rewrite set_a_get_a'; eauto.
      introv Hf; inverts Hf. 
    }
    l_rew21_inv1 (get O' osdomainportid).
    introv Hg. auto. 
  -
    assert (get O' osdomainportid = Some (osdomainport dpl)).
    { eapply join_get_get_r; eauto. }
    l_rew21_inv1 (get O' osdomainportid).
    introv Hg. auto. 
Qed.

Lemma qpost_nowt_succ_body_ctid_equiv_preserve2:
  forall td O1 O2 vp1 vp2 v0 i1 i2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2', 
    ctid_equiv td O1 O2 -> 
    qpost_nowt_succ_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_nowt_succ_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    ctid_equiv td O1' O2'. 
Proof.
  introv Hctide Hpost1 Hpost2 Hjo1 Hjo2 Hjo1' Hjo2'.
  unfold ctid_equiv in *.
  unfold qpost_nowt_succ_body in *.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end. 
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end.
  assert (Hupd1: get O10 curtid = get O10' curtid).
  {
    match goal with H: Some O10' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  } 
  lets Hct1': join_upd_get_same H1. 
  specializes Hct1'; eauto.
  assert (Hupd2: get O20 curtid = get O20' curtid).
  {
    match goal with H: Some O20' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hct2': join_upd_get_same H14. 
  specializes Hct2'; eauto. 
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Htpi1' Htpi2' Htd.
  assert (Hupd1': get O10' abstcblsid = get O10 abstcblsid).
  {
    match goal with H: Some O10' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Htpi1: tpi_upd_frm_preserved Htpi1' Hjo1' Hupd1' Hjo1.
  assert (Hupd2': get O20' abstcblsid = get O20 abstcblsid).
  {
    match goal with H: Some O20' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Htpi2: tpi_upd_frm_preserved Htpi2' Hjo2' Hupd2' Hjo2.
  lets H__: H15 Htpi1 Htpi2. eapply H__; eauto.
Qed.

Lemma qpost_nowt_succ_body_ibufs_equiv_preserve2:
  forall td O1 O2 vp1 vp2 v0 i1 i2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2',
    ibufs_equiv td O1 O2 ->
    qpost_nowt_succ_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_nowt_succ_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    ibufs_equiv td O1' O2'.
Proof.
  introv Hibfe Hpost1 Hpost2 Hjo1 Hjo2 Hjo1' Hjo2'. 
  unfold ibufs_equiv in *. 
  unfold qpost_nowt_succ_body in *.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end. 
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end.
  assert (Hupd1: get O10 ibufsid = get O10' ibufsid).
  {
    match goal with H: Some O10' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hbf1': join_upd_get_same H1. 
  specializes Hbf1'; eauto.
  assert (Hupd2: get O20 ibufsid = get O20' ibufsid).
  {
    match goal with H: Some O20' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hbf2': join_upd_get_same H14. 
  specializes Hbf2'; eauto.
Qed. 

Lemma qpost_nowt_succ_body_obufs_equiv_preserve2:
  forall td O1 O2 vp1 vp2 v0 i1 i2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2',
    obufs_equiv td O1 O2 ->
    qpost_nowt_succ_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_nowt_succ_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    obufs_equiv td O1' O2'.
Proof.
  introv Hobfe Hpost1 Hpost2 Hjo1 Hjo2 Hjo1' Hjo2'. 
  unfold obufs_equiv in *. 
  unfold qpost_nowt_succ_body in *.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end. 
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end.
  assert (Hupd1: get O10 obufsid = get O10' obufsid).
  {
    match goal with H: Some O10' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hbf1': join_upd_get_same H1. 
  specializes Hbf1'; eauto.
  assert (Hupd2: get O20 obufsid = get O20' obufsid).
  {
    match goal with H: Some O20' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hbf2': join_upd_get_same H14. 
  specializes Hbf2'; eauto.
Qed.                          

Lemma qpost_nowt_succ_body_bufs_equiv_preserve2:
  forall td O1 O2 vp1 vp2 v0 i1 i2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2',
    bufs_equiv td O1 O2 ->
    qpost_nowt_succ_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_nowt_succ_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    bufs_equiv td O1' O2'.
Proof.
  introv Hbfe Hpost1 Hpost2 Hjo1 Hjo2 Hjo1' Hjo2'.
  unfolds in Hbfe.
  destruct Hbfe as (Hibe & Hobe).
  split.
  lets H1_: qpost_nowt_succ_body_ibufs_equiv_preserve2
              Hibe Hpost1 Hpost2.
  specializes H1_; eauto.
  lets H2_: qpost_nowt_succ_body_obufs_equiv_preserve2 
              Hobe Hpost1 Hpost2. 
  specializes H2_; eauto. 
Qed.

Lemma qpost_nowt_succ_body_get_tcbid_eq:
  forall vp v i act v' O O', 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O act (v', Some O') ->
    get O abstcblsid = get O' abstcblsid. 
Proof.
  introv Hr.
  inverts Hr.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  inverts H1.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf. 
Qed.


Lemma mq_equiv_buffer_ref_preserve2:
  forall td mq1 mq2 O1 O2 O1' O2' els1 els2 els1' els2' eid ecb1 ecb2 pr mqs1 idx, 
    mq_equiv td mq1 mq2 O1 O2 ->
    get O1 absecblsid = Some (absecblist els1) ->
    get O2 absecblsid = Some (absecblist els2) ->
    get O1' absecblsid = Some (absecblist els1') ->
    get O2' absecblsid = Some (absecblist els2') ->
    els1' = set els1 eid ecb1 ->
    els2' = set els2 eid ecb2 ->
    get O1 absmqattrid = Some (absmqattr mqs1) ->
    get mqs1 idx = Some mq1 ->
    buffer_indom (Vptr eid) O1 pr ->
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' -> 
    mq_equiv td mq1 mq2 O1' O2'.
Proof.
  introv Hme Hge1 Hge2 Hge1' Hge2' He1' He2' Hmqs Hmq Hbi. 
  introv Hpp1 Hpp2.
  unfold mq_equiv in *.
  simpljoin.
  unfolds in Hbi.
  match goal with
    H: _ \/ _ \/ _ |- _ => destruct H as [Hf | [Hf | Hf]]; simpljoin; tryfalse
  end.
  - rem_dis. do 8 eexists; eauto.
  - rem_dis.
    do 8 eexists.
    split; eauto. 
  - rem_dis.
    match goal with H: Vptr _ = Vptr _ |- _ => inverts H  end.
    do 8 eexists.
    split; eauto.
    split; eauto.
    right. right.
    match goal with
      H: buf_in_dom ?x _ = _, H1: get _ ?x' = _, H2: get _ ?x' = _ |- _ =>
        rename x into eid; rename x' into eid'
    end.
    casetac eid eid' Ht Hf.
    + subst.
      false. lets H__: not_both_mq_and_buffer Hmqs Hmq; eauto.
    +
      l_rew21_inv1 (get O1 absecblsid).
      l_rew21_inv1 (get O2 absecblsid).
      do 7 eexists.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      rewrite set_a_get_a'; eauto.
      rewrite set_a_get_a'; eauto.
      split; eauto.
      split; eauto.
      split.
      unfold mq_ed_equiv in *.
      simpljoin.
      do 4 eexists. split; eauto. split; eauto.
      eapply tidls_equiv_pp_preserve2; eauto.
      eapply tidls_equiv_pp_preserve2; eauto.
Qed.

Definition same_prt_ecbs O O' := 
  forall els els',
    get O absecblsid = Some (absecblist els) ->
    get O' absecblsid = Some (absecblist els') ->
    (forall eid tls, get els eid = Some (absport, tls) <-> get els' eid = Some (absport, tls)). 

Lemma ports_equiv_same_prts_preserve2: 
  forall td O1 O2 O1' O2', 
    ports_equiv td O1 O2 ->
    get O1 osdomainportid = get O1' osdomainportid ->
    get O2 osdomainportid = get O2' osdomainportid ->
    get O1 oskportid = get O1' oskportid ->
    get O2 oskportid = get O2' oskportid ->
    same_prt_ecbs O1 O1' ->
    same_prt_ecbs O2 O2' ->
    dom_impl O1 O1' ->
    dom_impl O2 O2' ->
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' -> 
    ports_equiv td O1' O2'. 
Proof.
  introv Hpe Hgeq1 Hgeq2 Hkpe1 Hkpe2 Hsp1 Hsp2 Hdi1 Hdi2.
  introv Hpp1 Hpp2.
  unfold ports_equiv in *.
  simpljoin.
  rewrite H in Hgeq1; symmetry in Hgeq1.
  rewrite H0 in Hgeq2; symmetry in Hgeq2.
  unfold same_prt_ecbs in *.
  unfolds in Hdi1.
  specialize (Hdi1 absecblsid). 
  rewrite H1 in Hdi1.
  destruct Hdi1 as (els1' & Hgels1').
  unfolds in Hdi2.
  specialize (Hdi2 absecblsid).
  rewrite H2 in Hdi2.
  destruct Hdi2 as (els2' & Hgels2').
  do 4 eexists.
  splits; eauto.
  introv Hid.
  match goal with H: forall _, _ |- _ => specialize (H _ Hid); rename H into Ha end.
  destruct Ha as (Hgeq & Hiff & Hwteq). 
  split; auto.
  split.
  {
    specializes Hsp1 a; eauto.
    specializes Hsp2 a; eauto.
    split.
    - 
      introv Hex1.
      destruct Hex1 as (tls1 & Hiff1).
      eapply Hsp1 in Hiff1; eauto.
      assert (Hex: exists tls, get x1 a = Some (absport, tls)).
      { eexists; eauto. }
      apply Hiff in Hex.
      destruct Hex as (tls & Hg2).
      eapply Hsp2 in Hg2; eauto.
    -
      introv Hex2.
      destruct Hex2 as (tls2 & Hiff2).
      eapply Hsp2 in Hiff2; eauto. 
      assert (Hex: exists tls, get x2 a = Some (absport, tls)).
      { eexists; eauto. }
      apply Hiff in Hex.
      destruct Hex as (tls & Hg1).
      eapply Hsp1 in Hg1; eauto.
  }
  (* forall ..., ... -> tidls_equiv *)
  introv Hge1 Hge2. 
  lets Hgeqv1: Hsp1 H1 Hgels1' a. 
  lets Hgeqv2: Hsp2 H2 Hgels2' a. 
  eapply Hgeqv1 in Hge1.
  eapply Hgeqv2 in Hge2.
  lets H__: Hwteq Hge1 Hge2.
  eapply tidls_equiv_pp_preserve2; eauto. 
Qed.

Lemma qpost_nowt_succ_dpid_same: 
  forall vp v i O0 act v' O0' Of O O', 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O osdomainportid = get O' osdomainportid. 
Proof.
  introv Hpost Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed. 

Lemma qpost_nowt_succ_kpid_same:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O oskportid = get O' oskportid.  
Proof.
  introv Hpost Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed.

Lemma qpost_nowt_succ_same_prt_ecbs:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    same_prt_ecbs O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds.
  introv Hg Hg'.
  intros.
  inverts Hpost.
  simpljoin. 
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  split.
  -
    introv Hge.
    assert (Hget0: get O absecblsid = Some (absecblist x2)).
    { eapply join_get_get_l; eauto. }
    l_rew21_inv1 (get O absecblsid).
    match type of Hjo' with
      context[ (set O0 absecblsid (absecblist ?els')) ] =>
        assert (H__: get (set O0 absecblsid (absecblist els')) absecblsid = Some (absecblist els'))
    end.
    rewrite set_a_get_a. auto.
    match type of H__ with
      context [Some (absecblist ?els')] => 
        assert (Hge': get O' absecblsid = Some (absecblist els'))
    end.
    eapply join_get_get_l; eauto.
    clear H__.
    l_rew21_inv1 (get O' absecblsid).
    casetac x eid Ht Hf.
    + subst. rewrite Hge in H3. tryfalse. 
    + rewrite set_a_get_a'; eauto. 
  -
    introv Hge.
    assert (Hget0: get O absecblsid = Some (absecblist x2)).
    { eapply join_get_get_l; eauto. }
    l_rew21_inv1 (get O absecblsid).
    match type of Hjo' with
      context[ (set O0 absecblsid (absecblist ?els')) ] =>
        assert (H__: get (set O0 absecblsid (absecblist els')) absecblsid = Some (absecblist els'))
    end.
    rewrite set_a_get_a. auto.
    match type of H__ with
      context [Some (absecblist ?els')] => 
        assert (Hge': get O' absecblsid = Some (absecblist els'))
    end.
    eapply join_get_get_l; eauto.
    clear H__.
    l_rew21_inv1 (get O' absecblsid).
    casetac x eid Ht Hf.
    + subst. rewrite set_a_get_a in Hge. inverts Hge.
    + rewrite set_a_get_a' in Hge; eauto. 
Qed. 

Lemma qpost_nowt_succ_dom_impl:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds.
  intro x.
  inverts Hpost.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  destruct (get O x) eqn: E.
  2: {                    
    assert (get O0 x = None).
    { eapply join_get_none_rev1; eauto. }
    assert (get Of x = None).
    { clear -Hjo E. eapply join_get_none_rev2; eauto. }
    eapply map_join_get_none'''; eauto.
    casetac absecblsid x Ht Hf.
    - subst. l_rew21_inv1 (get O0 absecblsid).
    - rewrite set_a_get_a'; eauto. 
  }
  destruct a eqn: E'; 
    try (
        assert (Heq: get O x = get O' x)
        by
        (lets H__: join_get_same_l Hjo Hjo'; eauto; 
         casetac absecblsid x Ht Hf; 
         [ subst; 
           eapply join_get_get_l with (m:=O) in H2; eauto; 
           l_rew21_inv1 (get O absecblsid)
         |
           rewrite set_a_get_a'; eauto]); 
        rewrite E in Heq; 
        eexists; symmetry; eauto;
        fail).
  assert (Hor: get O0 x = Some (absecblist m) \/ get Of x = Some (absecblist m)).
  {
    eapply join_get_or; eauto. 
  }
  destruct Hor as [Hl | Hr].
  2: {
    eexists; eapply join_get_get_r; eauto.
  }
  casetac absecblsid x Ht Hf.
  -
    subst. eexists. 
    eapply join_get_get_l; eauto.
    rewrite set_a_get_a; eauto.
  -
    exists m.
    eapply join_get_get_l; eauto. 
    rewrite set_a_get_a'; eauto.
Qed.   

Lemma qpost_nowt_succ_mqptr_impl: 
  forall vp v i O act v' O' O0 O0' Of, 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hpost Hjo Hjo' Hmp'.
  unfold mq_ptr in *.
  inverts Hpost.
  simpljoin.
  match goal with H: _ = _ /\ Some _ = Some _ \/ _ |- _ => destruct H as [(Heq & Hsome) | Hf] end.
  inverts Hsome.
  2: { simpljoin; tryfalse. }
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (get O absmqattrid = get O' absmqattrid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf. 
  }
  rewrite H0 in H.
  do 8 eexists; eauto.
Qed.

Lemma qpost_nowt_succ_mqptr_iff: 
  forall vp v i O act v' O' O0 O0' Of, 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp.
Proof.
  introv Hpost Hjo Hjo'.
  intros.
  split.
  - eapply qpost_nowt_succ_mqptr_impl; eauto.
  - introv Hmp.
    unfold mq_ptr in *.
    inverts Hpost.
    simpljoin.
    match goal with H: _ = _ /\ Some _ = Some _ \/ _ |- _ => destruct H as [(Heq & Hsome) | Hf] end.
    inverts Hsome.
    2: { simpljoin; tryfalse. }
    match goal with H: _ :: _ = _ |- _ => inverts H end.
    assert (get O absmqattrid = get O' absmqattrid).
    {
      lets H__: join_get_same_l Hjo Hjo'; eauto.
      rewrite set_a_get_a'; eauto.
      introv Hf; inverts Hf. 
    }
    l_rew12_inv2 (get O absmqattrid). 
    do 8 eexists; eauto.
Qed.     

Lemma kme_qpost_nowt_succ_buffer_indom_preserve2: 
  forall td O1 O2 O10 O20 Of1 Of2 vp v0 i1 i2 act v1 v2 O10' O20' O1' O2' pr, 
    kernel_mq_equiv td O1 O2 ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 -> 
    qpost_nowt_succ_body (vp :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_nowt_succ_body (vp :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    buffer_indom vp O1 pr -> 
    kernel_mq_equiv td O1' O2'.
Proof.
  introv Hkme Hjo1 Hjo2 Hqn1 Hqn2 Hjo1' Hjo2' Hbi.
  lets Hpp1: qpost_nowt_succ_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qpost_nowt_succ_prio_preserved Hqn2; eauto.
  specializes Hpp2; eauto. 
  inverts Hqn1.
  inverts Hqn2.
  simpljoin.
  do 2 inv_lst.
  do 2 rem_dis.
  do 2 inv_some.
  unfold kernel_mq_equiv in *.
  simpljoin.
  assert (get O1 absmqattrid = get O1' absmqattrid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp. auto. 
  }
  assert (get O2 absmqattrid = get O2' absmqattrid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp. auto. 
  }
  match goal with
    H: get O1 absmqattrid = Some (absmqattr ?x) |- _ =>
      assert (get O1' absmqattrid = Some (absmqattr x)) by congruence 
  end.
  match goal with
    H: get O2 absmqattrid = Some (absmqattr ?x) |- _ =>
      assert (get O2' absmqattrid = Some (absmqattr x)) by congruence 
  end.
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  match goal with H: forall _, _ |- _ => lets H__: H Hd; eauto end.
  destruct H__ as (Hiff & Ha).
  split; auto.
  introv Hgm1 Hgm2.
  specializes Ha; eauto. 
  kvext_h Hjo1' absecblsid O1'.
  kvext_h Hjo2' absecblsid O2'.
  kvext O10 absecblsid O1.
  kvext O20 absecblsid O2.

  eapply mq_equiv_buffer_ref_preserve2; eauto.
Qed.           

Ltac inv_vint32 :=
  match goal with H: Vint32 _ = _ |- _ => inverts H end.

Ltac inv_msgq :=
  match goal with H: absmsgq _ _ _ = _ |- _ => inverts H end.

Ltac inv_vptr :=
  match goal with H: Vptr _ = _ |- _ => inverts H end.      

Lemma mq_ed_equiv_pp_preserve2:
  forall ed1 ed2 O1 O2 O1' O2', 
    mq_ed_equiv ed1 ed2 O1 O2 ->
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' ->
    mq_ed_equiv ed1 ed2 O1' O2'. 
Proof.
  introv Hmee Hpp1 Hpp2.
  unfold mq_ed_equiv in *.
  simpljoin.
  do 4 eexists.
  splits; eauto.
  eapply tidls_equiv_pp_preserve2; eauto.
Qed.

Lemma buffer_equiv_qpost_nowt_succ_preserve2:
  forall td O1 O2 i1 i2 vp v0 v1 v2 act pr Of1 Of2 O10 O20 O10' O20' O1' O2',  
    buffer_equiv td O1 O2 ->
    buffer_equiv (dom_for_prio pr) O1 O2 ->
    join O10 Of1 O1 -> 
    join O20 Of2 O2 ->       
    qpost_nowt_succ_body (vp :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_nowt_succ_body (vp :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10' Of1 O1' -> 
    join O20' Of2 O2' -> 
    buffer_indom vp O1 pr -> 
    buffer_equiv td O1' O2'.
Proof.
  introv Hbe Hbe' Hjo1 Hjo2 Hqn1 Hqn2 Hjo1' Hjo2' Hbid.
  lets Hpp1: qpost_nowt_succ_prio_preserved Hqn1 Hjo1 Hjo1'; eauto.
  lets Hpp2: qpost_nowt_succ_prio_preserved Hqn2 Hjo2 Hjo2'; eauto. 
  inverts Hqn1.
  inverts Hqn2.
  simpljoin.
  do 2 inv_lst.
  do 2 rem_dis.
  do 2 inv_some.
  do 2 inv_vint32.
  kvext_h Hjo1' absecblsid O1'.
  kvext_h Hjo2' absecblsid O2'.
  unfold buffer_equiv in *.
  destruct Hbe as (els1 & els2 & Hge1 & Hge2 & Ha).
  kvext O10 absecblsid O1.
  kvext O20 absecblsid O2.
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid).
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  specializes Ha; eauto.
  destruct Ha as (Hiff & Ha).
  casetac x eid Ht Hf.
  - subst.
    repeat rewrite set_a_get_a.
    split.
    + split; 
        introv Hex; simpljoin; do 2 eexists; eauto.
    + introv Hso1 Hso2.
      inverts Hso1.
      inverts Hso2.
      specializes Ha; eauto.
      destruct Ha as (Hme & Hte).
      split.
      *
        unfold mq_ed_equiv in *.
        simpljoin.
        do 2 inv_msgq. 
        do 4 eexists. split; eauto. split; eauto.
        eapply tidls_equiv_pp_preserve2; eauto.
      *
        eapply tidls_equiv_pp_preserve2; eauto.
  -
    repeat (rewrite set_a_get_a'; eauto).
    split.
    + auto.
    + introv Hg1 Hg2.
      specializes Ha; eauto.
      simpljoin.
      split.
      * eapply mq_ed_equiv_pp_preserve2; eauto. 
      * eapply  tidls_equiv_pp_preserve2; eauto. 
Qed. 

Lemma qpost_nowt_succ_body_dteq_preserve2:
  forall td cst1 cst2 O1 O2 pr vp v0 i1 i2 v1 v2 O10 O20 O10' O20' O1' O2' act Of1 Of2, 
    data_equiv_tskd td cst1 cst2 O1 O2 -> 
    buffer_equiv (dom_for_prio pr) O1 O2 -> 
    buffer_indom vp O1 pr -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    qpost_nowt_succ_body (vp :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_nowt_succ_body (vp :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    data_equiv_tskd td cst1 cst2 O1' O2'. 
Proof.
  introv Hde Hbfe_ Hbi Hjo1 Hjo2 Hpost1 Hpost2.
  introv Hjo1' Hjo2'.
  unfold data_equiv_tskd in *.
  destruct Hde as (Hctide & Hbfe & Hkde & Hcde).
  split.
  lets H__: qpost_nowt_succ_body_ctid_equiv_preserve2 Hctide Hpost1 Hpost2.
  specializes H__; eauto.
  split.
  lets H__: qpost_nowt_succ_body_bufs_equiv_preserve2 Hbfe Hpost1 Hpost2.
  specializes H__; eauto.
  split.
  2: {
    eapply cde_prio_preserved_preserve2; eauto.
    lets H__: qpost_nowt_succ_prio_preserved Hpost1; eauto.
    lets H__: qpost_nowt_succ_prio_preserved Hpost2; eauto.
  }
  unfold kernel_data_equiv.

  split.
  { (* kernel_task_equiv *)
    destructs Hkde.
    eapply knl_tsk_equiv_same_tls_preserve2; eauto.
    lets H__: join_get_same_l abstcblsid Hjo1 Hjo1'.
    eapply qpost_nowt_succ_body_get_tcbid_eq; eauto.
    auto.
    lets H__: join_get_same_l abstcblsid Hjo2 Hjo2'.
    eapply qpost_nowt_succ_body_get_tcbid_eq; eauto.
    auto.
  }
  split.
  {
    (* kernel_mq_equiv *)
    destructs Hkde.
    eapply kme_qpost_nowt_succ_buffer_indom_preserve2; eauto. 
  }
  split.
  { (* ports_equiv *)
    destructs Hkde.
    eapply ports_equiv_same_prts_preserve2; eauto.
    
    lets H__: qpost_nowt_succ_dpid_same Hjo1 Hjo1'; eauto.
    lets H__: qpost_nowt_succ_dpid_same Hjo2 Hjo2'; eauto.
    lets H__: qpost_nowt_succ_kpid_same Hjo1 Hjo1'; eauto.
    lets H__: qpost_nowt_succ_kpid_same Hjo2 Hjo2'; eauto.
    lets H__: qpost_nowt_succ_same_prt_ecbs Hjo1 Hjo1'; eauto.
    lets H__: qpost_nowt_succ_same_prt_ecbs Hjo2 Hjo2'; eauto.
    lets H__: qpost_nowt_succ_dom_impl Hjo1 Hjo1'; eauto.
    lets H__: qpost_nowt_succ_dom_impl Hjo2 Hjo2'; eauto.
    lets H__: qpost_nowt_succ_prio_preserved Hjo1 Hjo1'; eauto.
    lets H__: qpost_nowt_succ_prio_preserved Hjo2 Hjo2'; eauto.
  }

  split.
  (* buffer_equiv *)
  destructs Hkde.        
  eapply buffer_equiv_qpost_nowt_succ_preserve2; eauto. 
  
  (* cap_equiv *)
  destructs Hkde.
  eapply cap_equiv_preserve2; eauto.
  lets H__: qpost_nowt_succ_cpid_same Hjo1 Hjo1'; eauto.
  lets H__: qpost_nowt_succ_cpid_same Hjo2 Hjo2'; eauto.
  lets H__: qpost_nowt_succ_mqptr_iff Hjo1 Hjo1'; eauto.
  lets H__: qpost_nowt_succ_mqptr_iff Hjo2 Hjo2'; eauto.
Qed. 

Lemma qpost_exwt_succ_cpid_same:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O cspaceid = get O' cspaceid.  
Proof.
  introv Hpost Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf. 
Qed. 

Lemma qpost_exwt_succ_mqref_preserve: 
  forall vp v i O v' O' O0 O0' Of act, 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ref_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hor: get O0 absmqattrid = Some (absmqattr mqs)
               \/ get Of absmqattrid = Some (absmqattr mqs)).
  {
    eapply join_get_or; eauto. 
  }
  destruct Hor as [Hl | Hr].
  -
    eapply join_get_get_l with (a:=absmqattrid) (b:=absmqattr mqs) in Hjo'; eauto.
    2: { 
      rewrite set_a_get_a'; eauto.
      2: introv Hf; inverts Hf.
      rewrite set_a_get_a'; eauto.
      introv Hf; inverts Hf.
    }
    l_rew21_inv1 (get O' absmqattrid).
    introv Hg. auto. 
  -
    assert (get O' absmqattrid = Some (absmqattr mqs)).
    { eapply join_get_get_r; eauto. }
    l_rew21_inv1 (get O' absmqattrid).
    introv Hg. auto. 
Qed.

Lemma qpost_exwt_succ_qprt_preserve: 
  forall vp v i O v' O' O0 O0' Of act, 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    qprt_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hor: get O0 osdomainportid = Some (osdomainport dpl)
               \/ get Of osdomainportid = Some (osdomainport dpl)).
  {
    eapply join_get_or; eauto. 
  }
  destruct Hor as [Hl | Hr].
  -
    eapply join_get_get_l with (a:=osdomainportid) (b:=osdomainport dpl) in Hjo'; eauto.
    2: {
      repeat rewsimp. auto.
    }
    l_rew21_inv1 (get O' osdomainportid).
    introv Hg. auto. 
  -
    assert (get O' osdomainportid = Some (osdomainport dpl)).
    { eapply join_get_get_r; eauto. }
    l_rew21_inv1 (get O' osdomainportid).
    introv Hg. auto. 
Qed.

Lemma qpost_exwt_succ_ctid_equiv_preserve2:
  forall td O1 O2 vp1 vp2 v0 i1 i2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2', 
    ctid_equiv td O1 O2 -> 
    qpost_exwt_succ_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_exwt_succ_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    ctid_equiv td O1' O2'. 
Proof.
  introv Hctide Hpost1 Hpost2 Hjo1 Hjo2 Hjo1' Hjo2'.
  lets H1_: qpost_exwt_succ_prio_preserved Hjo1 Hjo1'; eauto.
  lets H2_: qpost_exwt_succ_prio_preserved Hjo2 Hjo2'; eauto. 
  
  unfold ctid_equiv in *.
  unfold qpost_exwt_succ_body in *.
  simpljoin.
  do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
  do 2 (match goal with H: _ :: _ = _ |- _ => inverts H end). 
  assert (Hupd1: get O10 curtid = get O10' curtid).
  {
    match goal with H: Some O10' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a'; eauto. 
    introv Hf; inverts Hf.
    introv Hf; inverts Hf.
  } 
  lets Hct1': join_upd_get_same H1. 
  specializes Hct1'; eauto.
  assert (Hupd2: get O20 curtid = get O20' curtid).
  {
    match goal with H: Some O20' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.
    introv Hf; inverts Hf.
  }
  lets Hct2': join_upd_get_same H22. 
  specializes Hct2'; eauto. 
  do 2 eexists.
  split; eauto.
  split; eauto.
  do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
  introv Htpi1' Htpi2' Htd.

  lets Htpi1_: prio_preserved_tpi Htpi1' H1_.
  lets Htpi2_: prio_preserved_tpi Htpi2' H2_.
  lets H__: H23 Htpi1_ Htpi2_ Htd.
  auto.
  
Qed.   

Lemma qpost_exwt_succ_bufs_same:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    (get O' ibufsid = get O ibufsid /\ get O' obufsid = get O obufsid). 
Proof.
  introv Hpost Hjo Hjo'.
  inverts Hpost.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  split.
  -
    symmetry. 
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewrite set_a_get_a'; eauto.
    2: introv Hf; inverts Hf.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.
  -
    symmetry.
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewrite set_a_get_a'; eauto.
    2: introv Hf; inverts Hf.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.
Qed.             

Lemma qpost_exwt_succ_dpid_same: 
  forall vp v i O0 act v' O0' Of O O', 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O osdomainportid = get O' osdomainportid. 
Proof.
  introv Hpost Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf. 
Qed.

Lemma qpost_exwt_succ_kpid_same:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O oskportid = get O' oskportid.  
Proof.
  introv Hpost Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed.

Lemma qpost_exwt_succ_same_prt_ecbs:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    same_prt_ecbs O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds.
  introv Hg Hg'.
  intros.
  inverts Hpost.
  simpljoin. 
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  split.
  -
    introv Hge.
    assert (Hget0: get O absecblsid = Some (absecblist x2)).
    { eapply join_get_get_l; eauto. }
    l_rew21_inv1 (get O absecblsid).
    match type of Hjo' with 
      context[ absecblist ?els' ] => assert (H__: get O' absecblsid = Some (absecblist els'))
    end.
    eapply join_get_get_l; eauto.
    rewrite set_a_get_a.
    auto. 
    l_rew21_inv1 (get O' absecblsid).
    casetac x eid Ht Hf.
    + subst. unfold get in *. unfold EcbMap in *.
      l_rew21_inv1 (EcbMod.get els eid).
    + rewrite set_a_get_a'; eauto. 
  -
    introv Hge.
    assert (Hget0: get O absecblsid = Some (absecblist x2)).
    { eapply join_get_get_l; eauto. }
    l_rew21_inv1 (get O absecblsid).
    match type of Hjo' with
      context [ absecblist ?els' ] => assert (get O' absecblsid = Some (absecblist els'))
    end.
    eapply join_get_get_l; eauto.
    rewrite set_a_get_a. auto.            
    l_rew21_inv1 (get O' absecblsid).
    casetac x eid Ht Hf.
    + subst. rewrite set_a_get_a in Hge. inverts Hge.
    + rewrite set_a_get_a' in Hge; eauto. 
Qed. 

Lemma qpost_exwt_succ_dom_impl:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds.
  intro x.
  inverts Hpost.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  destruct (get O x) eqn: E.
  2: {                    
    assert (get O0 x = None).
    { eapply join_get_none_rev1; eauto. }
    assert (get Of x = None).
    { clear -Hjo E. eapply join_get_none_rev2; eauto. }
    eapply map_join_get_none'''; eauto.
    casetac absecblsid x Ht Hf.
    - subst. l_rew21_inv1 (get O0 absecblsid).
    - rewrite set_a_get_a'; eauto.
      casetac abstcblsid x Ht_ Hf_.
      + subst.
        assert (get O0 abstcblsid = None).
        { eapply join_get_none_rev1; eauto. }
        l_rew21_inv1 (get O0 abstcblsid).
        tryfalse.
      + rewrite set_a_get_a'; eauto. 
  }
  destruct a eqn: E';
    try (
        assert (Heq: get O x = get O' x) by
        (lets H__: join_get_same_l Hjo Hjo'; eauto; 
         casetac absecblsid x Ht Hf;
         [ subst; 
           eapply join_get_get_l with (m:=O) in H3; eauto; 
           l_rew21_inv1 (get O absecblsid) |
           rewrite set_a_get_a'; eauto; 
           casetac abstcblsid x Ht_ Hf_;
           [ subst; 
             eapply join_get_get_l with (m:=O) in H2; eauto; 
             l_rew21_inv1 (get O abstcblsid) | 
             rewrite set_a_get_a'; eauto ]]); 
        rewrite E in Heq; 
        eexists; symmetry; eauto; fail).             
  {
    assert (Hor: get O0 x = Some (abstcblist m) \/ get Of x = Some (abstcblist m)).
    { eapply join_get_or; eauto. }
    destruct Hor as [Hl | Hr].
    2: { eexists; eapply join_get_get_r; eauto. }
    casetac absecblsid x Ht Hf.
    -
      subst.
      l_rew21_inv1 (get O0 absecblsid).
    -
      casetac abstcblsid x Ht_ Hf_.
      +
        subst. eexists.
        eapply join_get_get_l; eauto. 
        rewrite set_a_get_a'; eauto.
        rewrite set_a_get_a. eauto.
      +
        eexists.
        eapply join_get_get_l; eauto.
        rewrite set_a_get_a'; eauto.
        rewrite set_a_get_a'; eauto.
  }
  {
    assert (Hor: get O0 x = Some (absecblist m) \/ get Of x = Some (absecblist m)).
    { eapply join_get_or; eauto. }
    destruct Hor as [Hl | Hr].
    2: { eexists; eapply join_get_get_r; eauto. }
    casetac absecblsid x Ht Hf.
    -
      subst.
      l_rew21_inv1 (get O0 absecblsid).
      eexists. eapply join_get_get_l; eauto.
      rewrite set_a_get_a. eauto. 
    -
      casetac abstcblsid x Ht_ Hf_.
      +
        subst.
        l_rew21_inv1 (get O0 abstcblsid).
      +
        eexists.
        eapply join_get_get_l; eauto.
        rewrite set_a_get_a'; eauto.
        rewrite set_a_get_a'; eauto.            
  }          
Qed.

Lemma qpost_exwt_succ_mqattr_same:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O absmqattrid = get O' absmqattrid.  
Proof.
  introv Hpost Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf. 
Qed.

Lemma qpost_exwt_succ_mqptr_impl: 
  forall vp v i O act v' O' O0 O0' Of, 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hpost Hjo Hjo' Hmp'.
  unfold mq_ptr in *.
  assert (Hp := Hpost).
  inverts Hpost.
  simpljoin.
  match goal with H: _ = _ /\ Some _ = Some _ \/ _ |- _ => destruct H as [(Heq & Hsome) | Hf] end.
  inverts Hsome.
  2: { simpljoin; tryfalse. }
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (get O absmqattrid = get O' absmqattrid).
  {
    lets H__: qpost_exwt_succ_mqattr_same Hjo Hjo'; eauto.   
  }
  rewrite H0 in H.
  do 8 eexists; eauto.
Qed.

Lemma qpost_exwt_succ_mqptr_iff: 
  forall vp v i O act v' O' O0 O0' Of, 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp.  
Proof.
  introv Hpost Hjo Hjo'.
  intros.
  split.
  - eapply qpost_exwt_succ_mqptr_impl; eauto. 
  -  
    introv Hmp'.
    unfold mq_ptr in *.
    assert (Hp := Hpost).
    inverts Hpost.
    simpljoin.
    match goal with H: _ = _ /\ Some _ = Some _ \/ _ |- _ => destruct H as [(Heq & Hsome) | Hf] end.
    inverts Hsome.
    2: { simpljoin; tryfalse. }
    match goal with H: _ :: _ = _ |- _ => inverts H end.
    assert (get O absmqattrid = get O' absmqattrid).
    {
      lets H__: qpost_exwt_succ_mqattr_same Hjo Hjo'; eauto.   
    }
    rewrite H0 in H.
    do 8 eexists; eauto.
Qed.

Lemma kme_qpost_exwt_succ_buffer_indom_preserve2: 
  forall td O1 O2 O10 O20 Of1 Of2 vp v0 i1 i2 act v1 v2 O10' O20' O1' O2' pr, 
    kernel_mq_equiv td O1 O2 ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 -> 
    qpost_exwt_succ_body (vp :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_exwt_succ_body (vp :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    buffer_indom vp O1 pr -> 
    kernel_mq_equiv td O1' O2'.
Proof.
  introv Hkme Hjo1 Hjo2 Hqn1 Hqn2 Hjo1' Hjo2' Hbi.
  lets Hpp1: qpost_exwt_succ_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qpost_exwt_succ_prio_preserved Hqn2; eauto.
  specializes Hpp2; eauto. 
  inverts Hqn1.
  inverts Hqn2.
  simpljoin.
  do 2 inv_lst.
  do 2 rem_dis.
  do 2 inv_some.
  unfold kernel_mq_equiv in *.
  simpljoin.
  assert (get O1 absmqattrid = get O1' absmqattrid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp. auto. 
  }
  assert (get O2 absmqattrid = get O2' absmqattrid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp. auto. 
  }
  match goal with
    H: get O1 absmqattrid = Some (absmqattr ?x) |- _ =>
      assert (get O1' absmqattrid = Some (absmqattr x)) by congruence 
  end.
  match goal with
    H: get O2 absmqattrid = Some (absmqattr ?x) |- _ =>
      assert (get O2' absmqattrid = Some (absmqattr x)) by congruence 
  end.
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  match goal with H: forall _, _ |- _ => lets H__: H Hd; eauto end.
  destruct H__ as (Hiff & Ha).
  split; auto.
  introv Hgm1 Hgm2.
  specializes Ha; eauto. 
  kvext_h Hjo1' absecblsid O1'.
  kvext_h Hjo2' absecblsid O2'.
  kvext O10 absecblsid O1.
  kvext O20 absecblsid O2.

  eapply mq_equiv_buffer_ref_preserve2; eauto.
Qed.   

Lemma be_kte_gethwait_eq: 
  forall O1 O2 x pr tcbs1 tcbs2 ecbs1 ecbs2
         ms1 ms2 ml1 ml2 pwl1 pwl2 wl1 wl2 t1 t2,
    kernel_task_equiv (dom_for_prio pr) O1 O2 ->
    buffer_equiv (dom_for_prio pr) O1 O2 -> 
    buffer_indom (Vptr x) O1 pr -> 
    get O1 abstcblsid = Some (abstcblist tcbs1) ->
    get O1 absecblsid = Some (absecblist ecbs1) ->
    get O2 abstcblsid = Some (abstcblist tcbs2) ->
    get O2 absecblsid = Some (absecblist ecbs2) ->
    get ecbs1 x = Some (absmsgq ms1 ml1 pwl1, wl1) ->
    get ecbs2 x = Some (absmsgq ms2 ml2 pwl2, wl2) -> 
    GetHWait tcbs1 wl1 t1 ->
    GetHWait tcbs2 wl2 t2 ->
    (exists pr0,
        task_prio_id O1 pr0 t1 /\ task_prio_id O2 pr0 t2
        /\ dom_for_prio pr0 = dom_for_prio pr). 
Proof.
  introv Hkte Hbe Hbi Hgt1 Hge1 Hgt2 Hge2.
  introv He1 He2 Hgw1 Hgw2.
  unfolds in Hbe.
  unfolds in Hbi.
  simpljoin.
  rem_dis.
  inv_vptr.
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid). 
  specializes H1; eauto.
  destruct H1 as (Hiff & Ha).
  specializes Ha; eauto.
  unfold mq_equiv in Ha.
  simpljoin.
  lets H__: kte_tidls_eq_gethwait_eq Hkte Hgt1 Hgt2 Hgw1 Hgw2.
  specializes H__; eauto.
  {
    introv Hin.  
    lets H__: buffer_part_consistent O1 wl1 pwl1. 
    specializes H__; eauto.
  }
  {
    introv Hin.
    lets H__: buffer_part_consistent O2 wl2 pwl2. 
    specializes H__; eauto. 
  }
Qed.

Lemma knl_mq_equiv_postexwt_preserve2:
  forall td O1 O2 vp v0 i1 i2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2' pr, 
    kernel_data_equiv td O1 O2 -> 
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    buffer_equiv (dom_for_prio pr) O1 O2 -> 
    buffer_indom vp O1 pr -> 
    qpost_exwt_succ_body (vp :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_exwt_succ_body (vp :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    (kernel_task_equiv td O1' O2' /\ buffer_equiv td O1' O2').     
Proof.
  introv Hkde Hkte Hbe Hbi Hpost1 Hpost2. 
  introv Hjo1 Hjo2 Hjo1' Hjo2'.
  lets Hpp1: qpost_exwt_succ_prio_preserved Hjo1 Hjo1'; eauto. 
  lets Hpp2: qpost_exwt_succ_prio_preserved Hjo2 Hjo2'; eauto.

  assert (Hkte_ := Hkte).
  unfolds in Hkte.
  simpljoin. 
  assert (Hpost1_:= Hpost1).
  assert (Hpost2_ := Hpost2). 
  inverts Hpost1. 
  inverts Hpost2. 
  simpljoin.
  do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
  do 2 (match goal with H: _ :: _ = _ |- _ => inverts H end).
  do 2 (match goal with H: Some _ = Some _ |- _ => inversion H; clear H end).
  assert (Hgeq1: get O1 absmqattrid = get O1' absmqattrid).
  {
    lets H__: qpost_exwt_succ_mqattr_same Hpost1_; eauto. 
  }
  assert (Hgeq2: get O2 absmqattrid = get O2' absmqattrid).
  {
    lets H__: qpost_exwt_succ_mqattr_same Hpost2_; eauto. 
  }
  kvext O10 abstcblsid O1.
  kvext O20 abstcblsid O2.
  l_rew21_inv1 (get O1 abstcblsid).
  l_rew21_inv1 (get O2 abstcblsid).
  match goal with
    H: context [set O10 _ (abstcblist ?tcbs)] |- _ =>
      assert (get O1' abstcblsid = Some (abstcblist tcbs))
  end.
  {
    eapply join_get_get_l; eauto. subst O10'.
    repeat rewsimp. auto. 
  }
  match goal with
    H: context [set O20 _ (abstcblist ?tcbs)] |- _ =>
      assert (get O2' abstcblsid = Some (abstcblist tcbs))
  end.
  {    
    eapply join_get_get_l; eauto. subst O20'.
    repeat rewsimp. auto. 
  }
  
  split.
  -
    unfolds in Hkde.
    destruct Hkde as (Hkte & _ & _ & Hbe_ & _).
    unfolds in Hkte.
    destruct Hkte as (tcbs1 & tcbs2 & Hgtcbs1 & Hgtcbs2 & Hall). 
    unfold kernel_task_equiv.    
    do 2 eexists. 
    split; eauto.
    split; eauto.
    introv Hd.
    lets H__: Hall Hd. clear Hall.
    destruct H__ as ((Htpi12 & Htpi21) & Hall).
    split.
    + (* eq. for task_prio_id *) 
      split.
      * 
        introv Htpi1'.
        assert (Hex: exists t, task_prio_id O1 pr0 t).
        {
          destruct Htpi1' as (t_ & Htpi1').
          eexists.
          eapply prio_preserved_tpi; eauto. 
        }
        apply Htpi12 in Hex.
        destruct Hex as (t_ & Htpi_). 
        eexists. eapply prio_preserved_tpi; eauto. 
        apply prio_preserved_sym; auto. 
      *
        introv Htpi2'.
        assert (Hex: exists t, task_prio_id O2 pr0 t).
        {
          destruct Htpi2' as (t_ & Htpi2').
          eexists.
          eapply prio_preserved_tpi; eauto. 
        }
        apply Htpi21 in Hex.
        destruct Hex as (t_ & Htpi_). 
        eexists. eapply prio_preserved_tpi; eauto. 
        apply prio_preserved_sym; auto. 
    + 
      introv Hg1' Hg2'.
      assert (Htpi1': task_prio_id O1' pr0 t1).
      { unfolds. do 5 eexists. split; eauto. }
      assert (Htpi2': task_prio_id O2' pr0 t2).
      { unfolds. do 5 eexists. split; eauto. }
      assert (Htpi1_: task_prio_id O1 pr0 t1).
      {
        eapply prio_preserved_tpi; eauto.
      }
      assert (Htpi2_: task_prio_id O2 pr0 t2).
      {
        eapply prio_preserved_tpi; eauto.
      }
      unfolds in Htpi1_. unfolds in Htpi2_.
      simpljoin.
      do 2 l_rew21_inv1 (get O1 abstcblsid).
      do 2 l_rew21_inv1 (get O2 abstcblsid).

      kvext O10 absecblsid O1.
      kvext O20 absecblsid O2. 
      lets H__: be_kte_gethwait_eq Hkte_ Hbe Hbi.
      specializes H__; eauto.
      match goal with
        H1: GetHWait _ _ ?x1, H2: GetHWait _ _ ?x2 |- _ =>
          rename x1 into t1_; rename x2 into t2_
      end.
      destruct H__ as (pr0_ & Htpi1_ & Htpi2_ & Hdd).
      match goal with
        H: get tcbs1 t1_ = Some (_, ?x1) |- _ => rename x1 into pr10
      end.
      match goal with
        H: get tcbs2 t2_ = Some (_, ?x2) |- _ => rename x2 into pr20
      end.
      assert (task_prio_id O1 pr10 t1_).
      { do 5 eexists; eauto. }
      apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.  
      assert (task_prio_id O2 pr20 t2_).
      { do 5 eexists; eauto. }
      apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.
      assert (Hor: t1_ = t1 /\ t2_ = t2 \/ t1_ <> t1 /\ t2_ <> t2).
      {
        eapply prio_tid_corr_ext; eauto.
      }
      destruct Hor as [(Heq1 & Heq2) | (Hneq1 & Hneq2)].
      * subst.
        rewrite set_a_get_a in Hg1'. inverts Hg1'.
        rewrite set_a_get_a in Hg2'. inverts Hg2'.
        match goal with
          H1: get tcbs1 t1 = _, H2: get tcbs1 t1 = _ |- _ => rewrite H2 in H1; inverts H1
        end.
        match goal with
          H1: get tcbs2 t2 = _, H2: get tcbs2 t2 = _ |- _ => rewrite H2 in H1; inverts H1
        end.
        specializes Hall; eauto.
        simpljoin.
        splits; auto.
      * rewrite set_a_get_a' in Hg1'; eauto.
        rewrite set_a_get_a' in Hg2'; eauto.
  - (* buffer_equiv *)
    unfolds in Hkde.
    destruct Hkde as (Hkte & _ & _ & Hbe_ & _).
    destruct Hbe_ as (els1 & els2 & Hge1 & Hge2 & Hall).
    subst O10'. subst O20'.
    kvext_h Hjo1' absecblsid O1'.
    kvext_h Hjo2' absecblsid O2'.
    kvext O10 absecblsid O1.
    kvext O20 absecblsid O2.
    unfolds.
    do 2 eexists.
    split; eauto.
    split; eauto.
    introv Hd.
    specializes Hall; eauto.
    destruct Hall as (Hiff & Ha).
    l_rew21_inv1 (get O1 absecblsid).
    l_rew21_inv1 (get O2 absecblsid).

    casetac x1 eid Ht Hf.
    + (* x1 = eid *)
      subst.
      repeat rewrite set_a_get_a.
      split.
      * split; introv Hex; simpljoin; do 2 eexists; eauto.
      * introv Hso1 Hso2.
        inverts Hso1.
        inverts Hso2.
        specializes Ha; eauto.
        destruct Ha as (Hme & Hte).
        unfold mq_ed_equiv. 
        unfold mq_ed_equiv in Hme.
        destruct Hme as (ms & mlen & pws1 & pwl2 & Hq1 & Hq2 & Heq).
        inverts Hq1. inverts Hq2.
        split.
        ** 
          do 4 eexists. split; eauto. split; eauto.
          eapply tidls_equiv_pp_preserve2; eauto.
        **
          lets H__: be_kte_gethwait_eq Hkte_ Hbe Hbi.
          specializes H__; eauto.
          destruct H__ as (pr0 & Htpi1 & Htpi2 & Hdeq).
          match goal with
            H: get els1 eid = _ |- _ => lets H1_: distinct_wait_tids H; eauto
          end.
          match goal with
            H: get els2 eid = _ |- _ => lets H2_: distinct_wait_tids H; eauto
          end.
          simpljoin.
          eapply tidls_equiv_rm_preserve2; eauto.
          eapply gethwait_in; eauto.
          eapply gethwait_in; eauto.
    + (* x1<> eid *)
      repeat (rewrite set_a_get_a'; eauto).
      split.
      * (* _ <-> _ *)
        auto.
      *
        introv Hg1 Hg2.
        specializes Ha; eauto.
        destruct Ha as (Hme & Hte).
        split.
        **
          unfold mq_ed_equiv in *.
          simpljoin.
          do 4 eexists.
          split; eauto.
          split; eauto.
          eapply tidls_equiv_pp_preserve2; eauto.
        **
          eapply tidls_equiv_pp_preserve2; eauto.
Qed. 

Lemma qpost_exwt_succ_dteq_preserve2:
  forall td cst1 cst2 O1 O2 pr vp v0 i1 i2 v1 v2 O10 O20 O10' O20' O1' O2' act Of1 Of2, 
    data_equiv_tskd td cst1 cst2 O1 O2 -> 
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    buffer_equiv (dom_for_prio pr) O1 O2 -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    qpost_exwt_succ_body (vp :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') -> 
    qpost_exwt_succ_body (vp :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') -> 
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    buffer_indom vp O1 pr -> 
    data_equiv_tskd td cst1 cst2 O1' O2'.
Proof.
  introv Hde Hkte Hbe_ Hjo1 Hjo2 Hpost1 Hpost2.
  introv Hjo1' Hjo2' Hbi.
  unfold data_equiv_tskd in *. 
  destruct Hde as (Hctide & Hbfe & Hkde & Hcde).
  lets H__: knl_mq_equiv_postexwt_preserve2 Hkde Hkte Hbe_ Hbi.
  lets H_: H__ Hpost1 Hpost2. clear H__.
  specializes H_; eauto. 
  splits.
  -
    lets H__: qpost_exwt_succ_ctid_equiv_preserve2 Hctide Hpost1 Hpost2; eauto.
  -
    lets H1__: qpost_exwt_succ_bufs_same Hpost1 Hjo1 Hjo1'.
    lets H2__: qpost_exwt_succ_bufs_same Hpost2 Hjo2 Hjo2'.
    simpljoin. 
    lets H__: bufs_equiv_preserve2 O1 O2 O1' O2' Hbfe.
    specializes H__; eauto. 
  -
    unfold kernel_data_equiv.
    splits.
    + (* kernel_task_equiv *)
      destructs H_. auto. 

    + (* kernel_mq_equiv *)
      destructs Hkde. 
      eapply kme_qpost_exwt_succ_buffer_indom_preserve2; eauto. 

    + (* ports_equiv *)
      destructs Hkde. 
      eapply ports_equiv_same_prts_preserve2; eauto.          
      lets H__: qpost_exwt_succ_dpid_same Hjo1 Hjo1'; eauto. 
      lets H__: qpost_exwt_succ_dpid_same Hjo2 Hjo2'; eauto. 
      lets H__: qpost_exwt_succ_kpid_same Hjo1 Hjo1'; eauto.
      lets H__: qpost_exwt_succ_kpid_same Hjo2 Hjo2'; eauto.
      lets H__: qpost_exwt_succ_same_prt_ecbs Hjo1 Hjo1'; eauto.
      lets H__: qpost_exwt_succ_same_prt_ecbs Hjo2 Hjo2'; eauto.
      lets H__: qpost_exwt_succ_dom_impl Hjo1 Hjo1'; eauto.
      lets H__: qpost_exwt_succ_dom_impl Hjo2 Hjo2'; eauto.
      lets H__: qpost_exwt_succ_prio_preserved Hjo1 Hjo1'; eauto.
      lets H__: qpost_exwt_succ_prio_preserved Hjo2 Hjo2'; eauto.

    + (* buffer_equiv *) 
      destructs H_. auto. 

    + (* cap_equiv *)
      destructs Hkde.
      eapply cap_equiv_preserve2; eauto.
      lets H__: qpost_exwt_succ_cpid_same Hjo1 Hjo1'; eauto.
      lets H__: qpost_exwt_succ_cpid_same Hjo2 Hjo2'; eauto.

      lets H__: qpost_exwt_succ_mqptr_iff Hjo1 Hjo1'; eauto.
      lets H__: qpost_exwt_succ_mqptr_iff Hjo2 Hjo2'; eauto.
      
  -
    eapply cde_prio_preserved_preserve2; eauto.
    lets H__: qpost_exwt_succ_prio_preserved Hjo1 Hjo1'; eauto.
    lets H__: qpost_exwt_succ_prio_preserved Hjo2 Hjo2'; eauto.
Qed. 


      
Lemma hidapistep_hidapistep_bufferpost_lemma:
  forall
    (pc0 : progunit) (T1 T2 : tasks) (O1 O2 : osabst) (O1' O2' : osabst)
    (cst1' cst2' : clientst) (act: action) (i : taskdom) 
    (pr : priority) (t1 t2 : addrval) (cd1 cd2 cd' cd'0: spec_code) 
    (ks0 ks1 ks1_ : stmtcont) (ke0: exprcont)
    (Hncfid : no_common_fid pc0 (api_spec, int_spec, get_hprio_d))
    (Hpu : pu_noabs pc0)
    (Hrch1 : reachable (pc0, (api_spec, int_spec, get_hprio_d)) T1 cst1' O1)
    (Hrch2 : reachable (pc0, (api_spec, int_spec, get_hprio_d)) T2 cst2' O2)
    (Hfloweq : flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
            obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1 O2)
    (Hsceq : obsr_equiv get_hprio_d SchedDom T1 T2 cst1' cst2' O1 O2)
    (Htmeq : obsr_equiv get_hprio_d TransDom T1 T2 cst1' cst2' O1 O2)
    (Htdeq : obsr_equiv_tskd get_hprio_d i T1 T2 cst1' cst2' O1 O2)
    (Hact : act = TauAct \/ act = SendAct \/ act = RecvAct)
    (Hnint1 : ~ in_intr T1 O1)
    (Hcurt1 : get O1 curtid = Some (oscurt t1))
    (Htpi1 : task_prio_id O1 pr t1)
    (Hnabt1 : nabt (set T1 t1 (curs (hapi_code cd'), (ke0, ks1_))))
    (Hnint2 : ~ in_intr T2 O2)
    (Hcurt2 : get O2 curtid = Some (oscurt t2))
    (Hdomeq : dom_for_prio pr = dom_for_prio pr)
    (Htpi2 : task_prio_id O2 pr t2)
    (Hnabt2 : nabt (set T2 t2 (curs (hapi_code cd'0), (ke0, ks1))))
    (HC1 : get T1 t1 = Some (curs (hapi_code cd1), (ke0, ks1_)))
    (HC2 : get T2 t2 = Some (curs (hapi_code cd2), (ke0, ks1)))
    (Hceq : forall (pr0 : priority) (t1 t2 : tid),
         dom_for_prio pr0 = dom_for_prio pr ->
         task_prio_id O1 pr0 t1 ->
         task_prio_id O2 pr0 t2 ->
         exists c1 c2 ke ks1 ks2,
         get T1 t1 = Some (c1, (ke, ks1)) /\
         get T2 t2 = Some (c2, (ke, ks2)) /\
         cmd_equiv pr0 c1 c2 O1 O2 /\ cont_equiv pr0 ks1 ks2 O1 O2)
    (Hd'eq : obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1 O2)
    (Hstepdm : flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i))
    (Hfa : forall pr1 pr2 : priority,
        task_prio_id O1 pr1 t1 ->
        task_prio_id O2 pr2 t2 -> dom_for_prio pr1 = dom_for_prio pr -> pr1 = pr2)
    (Hbufe : bufs_equiv (dom_for_prio pr) O1 O2)
    (Hkde : kernel_data_equiv (dom_for_prio pr) O1 O2)
    (Hcde : client_data_equiv (dom_for_prio pr) cst1' cst2' O1 O2)
    (Hkte : kernel_task_equiv (dom_for_prio pr) O1 O2)
    (Hkme : kernel_mq_equiv (dom_for_prio pr) O1 O2)
    (Hprte : ports_equiv (dom_for_prio pr) O1 O2)
    (Hbfe: buffer_equiv (dom_for_prio pr) O1 O2)
    (Hctide_ : ctid_equiv (dom_for_prio pr) O1 O2)
    (H : spec_step get_hprio_d cd1 O1 cd' O1' act)
    (H0 : spec_step get_hprio_d cd2 O2 cd'0 O2' act)
    (Hcpe : cap_equiv (dom_for_prio pr) O1 O2)
    (Hhsat1 : head_asrt_sat pr cd1 O1)
    (Hhsat2 : head_asrt_sat pr cd2 O2)
    (Hvleq : vl_equiv cd1 cd2)
    (Hnex : ~ (exists vo1 vo2, cd1 = END vo1 /\ cd2 = END vo2))
    (Hbpost : bufferpost_equiv cd1 cd2)
    (Hcont : cont_equiv pr ks1_ ks1 O1 O2), 

    code_equiv_tskd i
      (set T1 t1 (curs (hapi_code cd'), (ke0, ks1_)))
      (set T2 t2 (curs (hapi_code cd'0), (ke0, ks1))) O1' O2' /\
      data_equiv_tskd i cst1' cst2' O1' O2'. 
Proof.
  intros.
  match goal with H: spec_step _ cd1 _ ?cd' _ _ |- _ => rename cd' into cd1'; rename H into Hstep1 end.
  match goal with H: spec_step _ cd2 _ ?cd' _ _ |- _ => rename cd' into cd2'; rename H into Hstep2 end.
  
  unfolds in Hbpost.
  destruct Hbpost as (vl & vl1 & vl2 & k & Hlenvl & Hlenvl1 & Hlenvl2 & Hnth1 & Hnth2).
  do 3 try destruct vl; tryfalse.
  do 2 try destruct vl1; tryfalse.
  do 2 try destruct vl2; tryfalse.
  simpl in Hnth1.
  destruct v1; simpl in Hnth1;
    try (eapply abt_succs_contra in Hnth1; inverts Hstep1; tryfalse; fail).
  simpl in Hnth2.
  destruct v2; simpl in Hnth2;
    try (eapply abt_succs_contra in Hnth2; inverts Hstep2; tryfalse; fail).

  unfold obsr_equiv_tskd in Htdeq.
  destruct Htdeq as (Hce & Hde).
  unfolds in Hsceq.
  unfolds in Hsceq.
  destruct Hsceq as (Hce_sch & Hde_sch).

  unfolds in Htmeq.
  
  destruct k.
  (* k=0 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  symexe.
  {
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    unfold cmd_equiv.
    right.
    do 2 eexists. split; eauto. split; eauto.
    simpljoin.
    split. simpl. auto.
    split. simpl. auto.
    split.
    introv Hhvl1 Hhvl2.
    simpl in Hhvl1.
    inverts Hhvl1.
    introv Hf. rewrite nth_error_nil in Hf. tryfalse.
    (* stmt_equiv *)
    unfold stmt_equiv.
    right.
    split.
    introv Hf. simpljoin. tryfalse.
    right. right. right. right. right. right. right. left.
    solve_bufferpost_eq Hlenvl Hlenvl1 Hlenvl2 1%nat.
  }

  destruct k.
  (* k=1 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  symexe.
  {
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    unfold cmd_equiv.
    right.
    do 2 eexists. split; eauto. split; eauto.
    split. simpl. auto.
    split. simpl. auto.
    split.
    introv Hhvl1 Hhvl2.
    simpl in Hhvl1.
    inverts Hhvl1.
    introv Hf. rewrite nth_error_nil in Hf. tryfalse.
    (* stmt_equiv *)
    unfold stmt_equiv.
    right.
    split. introv Hf. simpljoin. tryfalse.
    right. right. right. right. right. right. right. left.
    solve_bufferpost_eq Hlenvl Hlenvl1 Hlenvl2 2%nat.
  }
  {
    apply data_equiv_schd_sym in Hde_sch; eauto.
    lets H__: buf_in_dom_contra Hde_sch;  eauto.
    specializes H__; eauto.
    false.
  }
  {
    lets H__: buf_in_dom_contra Hde_sch;  eauto.
    specializes H__; eauto.
    false.
  }
  {
    simpl in Hhsat1.
    simpl in Hhsat2.
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    unfold cmd_equiv.
    right.
    do 2 eexists. split; eauto. split; eauto.
    split. simpl.
    eapply n_buf_in_dom_false_dest; eauto.
    split. simpl.
    eapply n_buf_in_dom_false_dest; eauto.
    split.
    introv Hhvl1 Hhvl2.
    simpl in Hhvl1.
    inverts Hhvl1.
    introv Hf. rewrite nth_error_nil in Hf. tryfalse.
    (* stmt_equiv *)
    unfold stmt_equiv.
    right.
    split.
    introv Hf. simpljoin. tryfalse.
    right. right. right. right. right. right. right. left.
    solve_bufferpost_eq Hlenvl Hlenvl1 Hlenvl2 3%nat.
  }
  
  destruct k.
  (* k=2 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  symexe.
  {
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto.
    match goal with
      H1: ret_val _ _ _ _, H2: ret_val _ _ _ _ |- _ =>
        lets H1_: rv_veq H1; lets H2_: rv_veq H2; subst
    end.
    apply cmd_equiv_end.
  }

  destruct k.
  (* k=3 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  simpl in Hhsat1.
  simpl in Hhsat2.
  symexe.
  {
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    Set Nested Proofs Allowed. 
    Lemma aar_veq12: 
      forall v1 v2 O act v O', 
        asrt_and_ret (v1 :: v2 :: nil) O act (v, Some O') ->
        v1 = v2. 
    Proof.
      introv Haar.
      unfolds in Haar.
      simpljoin.
      match goal with H: _ :: _ :: nil = _ |- _ => inverts H end.
      match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
    Qed.

    apply11 asrt_and_ret asrt_and_ret aar_veq12 H1_ H2_.
    do 2 inv_vint32.
    eapply cmd_equiv_ret_val_anno; eauto. 
  }
  {
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    apply11 asrt_and_ret asrt_and_ret aar_veq12 H1_ H2_.
    do 2 inv_vint32.    
    eapply cmd_equiv_ret_val_anno; eauto. 
  }
  {
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    apply11 asrt_and_ret asrt_and_ret aar_veq12 H1_ H2_.
    do 2 inv_vint32. 
    eapply cmd_equiv_ret_val_anno; eauto. 
  }
  {
    apply buffer_equiv_sym in Hbfe.
    false. eapply buffer_equiv_noque_false; eauto.    
  }
  {
    false. eapply buffer_equiv_noque_false; eauto.    
  }
  {
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    apply11 asrt_and_ret asrt_and_ret aar_veq12 H1_ H2_.
    do 2 inv_vint32.     
    eapply cmd_equiv_ret_val_anno; eauto. 
  }
  {
    eapply buffer_equiv_sym in Hbfe.
    false. eapply buffer_equiv_qlen_impl; eauto. 
  }
  {
    eapply buffer_equiv_sym in Hbfe.
    false. eapply buffer_equiv_qlen_impl; eauto.     
  }
  {
    false. eapply buffer_equiv_qlen_impl; eauto.     
  }
  {
    (* qpost_nowt_succ_body *) 
    lets Hpp1: qpost_nowt_succ_prio_preserved O1 O1' O0 O'0; eauto.
    specializes Hpp1; eauto.
    lets Hpp2: qpost_nowt_succ_prio_preserved O2 O2' O O'; eauto.
    specializes Hpp2; eauto. 
    apply11 qpost_nowt_succ_body qpost_nowt_succ_body
      qpost_nowt_succ_cpid_same Hcpeq2 Hcpeq1.
    specializes Hcpeq1; eauto.
    specializes Hcpeq2; eauto. 
    split.
    - (* code_equiv *)
      eapply code_equiv_upd2_preserve_st'; eauto.
      {
        (* cmd_equiv *)
        match goal with
          H: context [qpost_nowt_succ_body] |- _ =>
            eapply qpost_nowt_succ_ret in H; eauto
        end.
        match goal with
          H: context [qpost_nowt_succ_body] |- _ =>
            eapply qpost_nowt_succ_ret in H; eauto
        end.
        subst. 
        eapply cmd_equiv_ret_val_anno; eauto.         
      }
      
      eapply cont_equiv_qref_preserve; eauto. 
      eapply qpost_nowt_succ_mqref_preserve; eauto.
      eapply qpost_nowt_succ_mqref_preserve with (O0:=O) (O0':=O'); eauto.
      eapply qpost_nowt_succ_qprt_preserve; eauto.
      eapply qpost_nowt_succ_qprt_preserve with (O0:=O) (O0':=O'); eauto.
      eapply eqdom_frm_domimpl; eauto.
      eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.

      lets H__: code_equiv_hsat_neq_st'; eauto.
      eapply H__; eauto.
      eapply qpost_nowt_succ_mqref_preserve; eauto.
      eapply qpost_nowt_succ_mqref_preserve with (O0:=O) (O0':=O'); eauto.
      eapply qpost_nowt_succ_qprt_preserve; eauto.
      eapply qpost_nowt_succ_qprt_preserve with (O0:=O) (O0':=O'); eauto.              
      eapply eqdom_frm_domimpl; eauto.
      eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
      
    - (* data_equiv *) 
      eapply qpost_nowt_succ_body_dteq_preserve2; eauto. 
  }
  {
    eapply buffer_equiv_sym in Hbfe; eauto.
    false. eapply buffer_equiv_qlen_lt_impl; eauto.       
  }
  {
    false. eapply buffer_equiv_qlen_impl; eauto.         
  }
  {
    false. eapply buffer_equiv_qlen_lt_impl; eauto.           
  }
  {
    (* qpost_exwt_succ_body *)
    lets Hpp1: qpost_exwt_succ_prio_preserved O1 O1' O0 O'0; eauto.
    specializes Hpp1; eauto.
    lets Hpp2: qpost_exwt_succ_prio_preserved O2 O2' O O'; eauto.
    specializes Hpp2; eauto. 
    apply11 qpost_exwt_succ_body qpost_exwt_succ_body
      qpost_exwt_succ_cpid_same Hcpeq2 Hcpeq1.
    specializes Hcpeq1; eauto.
    specializes Hcpeq2; eauto.
    split.   
    - (* code_equiv_tskd *)
      eapply code_equiv_upd2_preserve_st'; eauto.
      {
        (* cmd_equiv *)
        unfolds.
        right.
        do 2 eexists.
        split; eauto. split; eauto.
        split. simpl; auto. split. simpl; auto.
        split.
        eapply vl_equiv_nil; eauto.
        unfolds.
        right. 
        split. introv Hf. simpljoin. tryfalse.
        right. right. right. right. right. right. right. left.
        solve_bufferpost_eq Hlenvl Hlenvl1 Hlenvl2 4%nat. 
      }
      eapply cont_equiv_qref_preserve; eauto. 
      eapply qpost_exwt_succ_mqref_preserve; eauto.
      eapply qpost_exwt_succ_mqref_preserve with (O0:=O) (O0':=O'); eauto.
      eapply qpost_exwt_succ_qprt_preserve; eauto.
      eapply qpost_exwt_succ_qprt_preserve with (O0:=O) (O0':=O'); eauto.      
      eapply eqdom_frm_domimpl; eauto.
      eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.    

      lets H__: code_equiv_hsat_neq_st'; eauto.
      eapply H__; eauto.
      eapply qpost_exwt_succ_mqref_preserve; eauto.
      eapply qpost_exwt_succ_mqref_preserve with (O0:=O) (O0':=O'); eauto.
      eapply qpost_exwt_succ_qprt_preserve; eauto.
      eapply qpost_exwt_succ_qprt_preserve with (O0:=O) (O0':=O'); eauto.                    
      eapply eqdom_frm_domimpl; eauto.
      eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

    - (*data_equiv_tskd *)
    eapply qpost_exwt_succ_dteq_preserve2; eauto. 
  }

  destruct k.
  (* k=4 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  simpl in Hhsat1.
  simpl in Hhsat2.
  symexe. 
  {
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    unfold cmd_equiv.
    right.
    do 2 eexists. split; eauto. split; eauto.
    split. simpl. auto.
    split. simpl. auto.
    split.
    introv Hhvl1 Hhvl2.
    simpl in Hhvl1.
    inverts Hhvl1.
    introv Hf. rewrite nth_error_nil in Hf. tryfalse.
    (* stmt_equiv *)
    unfold stmt_equiv.
    right.
    split.
    introv Hf. simpljoin. tryfalse.
    right. right. right. right. right. right. right. left.
    solve_bufferpost_eq Hlenvl Hlenvl1 Hlenvl2 5%nat.    
  }
  
  destruct k.
  (* k=5 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  simpl in Hhsat1.
  simpl in Hhsat2.
  symexe. 
  {
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    apply11 asrt_and_ret asrt_and_ret aar_veq12 H1_ H2_.
    do 2 inv_vint32.
    eapply cmd_equiv_ret_val_anno; eauto.     
  }

  destruct k.
  (* k=6 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  simpl in Hhsat1.
  simpl in Hhsat2.
  symexe. 
  {
    split; auto.
    eapply vlequiv_veq in Hvleq; eauto.
    2: { simpl. eauto. }
    2: { simpl. eauto. }
    subst. 
    apply11 ret_val ret_val rv_veq H1_ H2_.
    subst.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    eapply cmd_equiv_end; eauto. 
  }

  simpl in Hnth2.
  rewrite nth_error_nil in Hnth2.
  false. 

Qed. 
      

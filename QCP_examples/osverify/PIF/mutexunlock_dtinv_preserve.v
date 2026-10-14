
Require Import PIF_sys.
Require Import PIF_spec.
Require Import PIF_language.
Require Import PIF_Modules.
Require Import List.
Require Import PIF_opsem.
Require Import Coqlib.
Require Import Maps.
Require Import PIF_memory.
Require Import PIF_assertion.
Require Import init_and_inv_PIF.
Require Import inv_hold_init.
Open Scope nat_scope.
Require Import PIF_LibTactics.
Require Import Integers.
Require Import PIF_os_code_defs. 

Require Import PIF_os_ucos_h.
Require Import aux_lemmas.

Require Import mux_succ_gen. 
Require Import pif_lemmas. 
Require Import pif_tacs. 

Open Scope int_scope.

Require Import seplog_lemmas. 
Require Import int_auto.

Require Import protect. 
Require Import join_lib.

Ltac some_none_tac Hs :=
  match Hs with
    (pnil, ?hyp) => 
      match type of hyp with
        ?P /\ ?Q => let h1 := fresh "h" in let h2 := fresh "h" in destruct hyp as (h1 & h2); some_none_tac pnil
      | ?P \/ ?Q =>
          let h1 := fresh "h" in
          let h2 := fresh "h" in
          destruct hyp as [h1 | h2];
          [some_none_tac (pnil, h1) | some_none_tac (pnil, h2)]
      | Some _ = None => solve [false]
      | exists _, _ => let x := fresh "x" in let h1 := fresh "h" in destruct hyp as (x & h1); some_none_tac (pnil, h1)
      | _ => idtac
      end
  | pnil =>
      match goal with
        h: context [Some ?t1 = None] |- _ => some_none_tac (pnil, h)
      | h: context [Some ?t1 = Some ?t2] |- _ => some_none_tac (pnil, h) 
      | h: _ |- _ => idtac
      end
  end.
  
Ltac end_abt H tac := 
  match type of H with
    ?P /\ ?Q => let h1 := fresh in let h2 := fresh in destruct H as (h1 & h2); tac h1; tac h2
  | ?P \/ ?Q => let h1 := fresh in let h2 := fresh in destruct H as [h1 | h2]; [tac h1 | tac h2]
  | ABORT <> ABORT => solve [false]
  | ~exists vo, END ?vo_ = END vo => solve [false; apply H; eexists; eauto]
  end. 
       
Ltac end_abt_tac H := 
  match type of H with
    context [ABORT <> ABORT] => end_abt H end_abt_tac
  | context [~exists vo, END ?vo1 = END vo] => end_abt H end_abt_tac
  end.
       
Ltac symexe0 := 
  match goal with
    H: has_succ0 _ _ |- _ =>
      inverts H;
      try (
          match goal with
            H_: has_succ0 _ _ |- _ =>
              protect H_;
              try (match goal with
                     H__: spec_step _ _ _ _ _ |- _ => protect H__
                   end)
          end); symexe0
  | H: spec_step _ _ _ _ _ |- _ => inverts H; symexe0
  | H: ?r _ _ (_, _) |- _ => inverts H; simpljoin; tryfalse; some_none_tac pnil; symexe0
  | H: context[ABORT <> ABORT] |- _ => end_abt_tac H
  | H: context[~exists vo, END ?vo1 = END vo] |- _ => end_abt_tac H
  | H: Some _ = Some _ |- _ => inverts H; symexe0 
  | H: GOOD_DT ?O |- GOOD_DT ?O => solve[auto]
  | Hjo1: join ?O ?Of ?OO, Hjo2: join ?O ?Of ?OO' |- _ =>
      assert (OO = OO') by join auto; subst; symexe0 
  | H: _ |- _ => idtac
  end.

Ltac symexe :=
  match goal with
    H1: ProtectWrapper _, H2: ProtectWrapper _ |- _ =>
      unprotect H1; unprotect H2;
      symexe0
  | _ => symexe0
  end.

Set Nested Proofs Allowed.

Lemma good_dt_mutexunlock_nowt_ret_succ_preserved: 
  forall
    (O' O : OSAbstMod.map)
    (O0 Of : OSAbstMod.map)
    (x : addrval)
    (x2 : EcbMod.map)
    (x3 : TcbMod.map)
    (x6 x7 : int32)
    (x8 : taskstatus)
    (x9 : msg)
    (x10 : addrval)
    (x11 : PtbMod.map)
    (x13 : susstatus)
    (H10 : join
             (set
                (set
                   (set O0 abtcblsid (abstcblist (set x3 x10 (x7, x8, x9, x13))))
                   absecblsid (absecblist (set x2 x (absmutexsem x6 None, nil))))
                absptlsid (absptls (set (set x11 x7 (Valid_Addr x10)) x6 Holder)))
             Of O')
    (H9 : join O0 Of O)
    (H1 : GOOD_DT O)
    (H0 : NO_NEST_PENDING_O O)
    (Hnest : NO_NEST_PENDING_O O')        
    (H2 : get O0 curtid = Some (oscurt x10))
    (H3 : get O0 absecblsid = Some (absecblist x2))
    (H4 : get O0 abtcblsid = Some (abstcblist x3))
    (H5 : get O0 absptlsid = Some (absptls x11))
    (H6 : get x2 x = Some (absmutexsem x6 (Some (x10, x7)), nil))
    (H7 : get x3 x10 = Some (x6, x8, x9, x13)),
    GOOD_DT O'. 
Proof.
  intros.
  assert (get O absecblsid = Some (absecblist x2)) as Hels.
  eapply join_get_get_l;eauto.
  assert (get O abtcblsid = Some (abstcblist x3)) as Htls.
  eapply join_get_get_l;eauto.
  assert (get O curtid = Some (oscurt x10)) as Hcurt.
  eapply join_get_get_l;eauto.
  assert (get O absptlsid = Some (absptls x11)) as Hptls.
  eapply join_get_get_l;eauto.

  assert (O'=set (set
                    (set O abtcblsid
                       (abstcblist (set x3 x10 (x7, x8, x9, x13))))
                    absecblsid
                    (absecblist
                       (set x2 x (absmutexsem x6 None, nil))))
               absptlsid
               (absptls
                  (set (set x11 x7 (Valid_Addr x10)) x6 Holder))).
  eapply join_get_set_eq_3;eauto.
  clear H2 H3 H4 H5.
  remember O as Ox.
  clear HeqOx.
  subst O'.

  unfolds.
  intros.
  rewrite abst_set_get_neq in H, H2, H3;auto.
  rewrite OSAbstMod.map_get_set in H4.
  inverts H4.
  rewrite OSAbstMod.map_get_set in H.
  inverts H.
  rewrite abst_set_get_neq in H2, H3;auto.
  rewrite OSAbstMod.map_get_set in H2.
  inverts H2.
  rewrite abst_set_get_neq in H3;auto.

  unfolds in H1.
  lets Hgoodst: H1 Hels Htls H3 Hptls.
  destruct Hgoodst as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6).
  splits; auto.
  unfolds.
  unfolds in Hg1.
  splits.
  simpljoin.
  intros.
  (*   assert(Hor: x10 = t \/ x10 <> t) by tauto.
  destruct Hor as [Heq | Hneq].
  subst x10.
  rewrite TcbMod.map_get_set in H5.
  inverts H5. *)
  unfolds.
  intros.
  unfolds in H8.
  mytac.
  assert (Hor: x = x0 \/ x<>x0 ) by tauto.
  destruct Hor as [He | Hn].
  (*   eapply tidspec.eq_beq_true in He. *)
  (*   rewrite EcbMod.map_eq in H8. *)
  subst x.
  rewrite PIF_language.EcbMap_obligation_21 in H8.
  inverts H8; tryfalse.

  rewrite EcbMod.set_a_get_a' in H8.
  assert(Hor: x10 = t \/ x10 <> t) by tauto.
  destruct Hor as [ Heq| Hneq].
  subst x10.
  rewrite TcbMod.map_get_set in H5.
  inverts H5.
  eapply H in H7; eauto.
  eapply H7.
  unfolds.
  do 4 eexists; splits; eauto.
  rewrite TcbMod.map_get_set' in H5; eauto.
  eapply H in H5; eauto.
  eapply H5.
  unfolds; do 4 eexists; splits; eauto.
  eapply tidspec.neq_beq_false ; eauto.

  simpljoin.
  intros.
  assert(Hor: x10 = t \/ x10 <> t) by tauto.
  destruct Hor as [ Heq | Hnq].
  subst x10.
  rewrite TcbMod.map_get_set in H5.
  inverts H5.
  eapply H2 in H7; eauto.
  clear -H7 H6.
  unfolds in H7.
  simpljoin.
  assert(Hor: x = eid \/ x <> eid) by tauto.
  destruct Hor as [He | Hne].
  subst x.
  unfold get in H6; simpl in H6.
  rewrite H in H6.
  inverts H6; tryfalse.
  unfolds.
  rewrite EcbMod.map_get_set'; eauto.
  
  rewrite TcbMod.map_get_set' in H5; eauto.
  eapply H2 in H5.
  unfolds.
  clear -H5 H6.
  unfolds in H5.
  assert(Hor: x = eid \/ x <> eid) by tauto.
  destruct Hor as [He | Hn].
  subst x.
  mytac.
  unfold get in H6; simpl in H6.
  rewrite H6 in H.
  inverts H; tryfalse.
  rewrite EcbMod.map_get_set'; eauto.

  simpljoin.
  intros.
  unfolds in H5.
  assert(Hor: x = eid \/ x <> eid) by tauto.
  destruct Hor as [He | Hn].
  subst x.
  rewrite EcbMod.map_get_set in H5.
  mytac. inverts H5; tryfalse.
  rewrite EcbMod.map_get_set' in H5; eauto.
  eapply H4 in H5.
  clear -H7 H5 Hn.
  assert(Hor: x10 = t \/ x10 <> t) by tauto.
  destruct Hor as [Heq | Hneq].
  subst x10.
  mytac.
  unfold get in H7; simpl in H7.
  rewrite H7 in H.
  inverts H.
  rewrite TcbMod.map_get_set.
  do 3 eexists; eauto.
  rewrite TcbMod.map_get_set'; eauto.
  
  (*owner_prio_prop*)
  unfolds.
  intros.
  (*   clear -H6 H7 Hg2 H H2 H0. *)
  assert(Hor2: x = eid \/ x <> eid) by tauto.
  destruct Hor2 as [Heq | Hneq].
  subst x.
  rewrite EcbMod.map_get_set in H2. 
  inverts H2.
  assert(Hor1: x10 = t \/ x10 <> t) by tauto.
  destruct Hor1 as [He | Hn].
  subst x10.
  rewrite TcbMod.map_get_set in H; eauto.
  inverts H.
  rewrite EcbMod.map_get_set' in H2; eauto.
  unfolds in H0.
  eapply H0 in Hels; eauto.
  unfolds in Hels.
  assert(Hnn: TcbMod.get x3 t <> None).
  unfold get in H7; simpl in H7; rewrite H7; auto.
  apply Hels with (qid:= eid)  in Hnn; eauto.
  destruct Hnn.
  destruct H4.
  exists x. splits; eauto.
  unfolds; do 3 eexists; eauto.
  unfolds; do 3 eexists; eauto.
  
  rewrite TcbMod.map_get_set' in H; eauto.
  rewrite EcbMod.map_get_set' in H2; eauto.
  (*task_stat_prop*)
  unfolds.
  intros.
  assert(Hor: x10 = t \/ x10 <> t) by tauto.
  destruct Hor as [He | Hn].
  subst x10.
  rewrite TcbMod.map_get_set in H.
  inverts H.
  eapply Hg3 in H7; eauto.
  rewrite TcbMod.map_get_set' in H; eauto.

  (**wait_prop**)
  unfolds.
  intros.
  assert(Hor: x10 <> t).
  unfolds; intros.
  subst x10.
  rewrite TcbMod.map_get_set in H. inverts H.
  unfolds in Hg1. mytac.
  lets Hx: H2 H7.
  unfolds in H0.
  eapply H0 in Hels; eauto.
  unfolds in Hels.
  assert(Hr: TcbMod.get x3 t <> None).
  unfolds; intros.
  unfold get in H7; simpl in H7; rewrite H7 in H5; inverts H5.
  apply Hels with (qid:= x) in Hr.
  destruct Hr.
  destruct H5.
  unfolds.
  unfolds in Hx. mytac.
  do 4 eexists; splits; eauto.
  do 3 eexists; eauto.
  
  unfolds in Hg4.
  rewrite TcbMod.map_get_set' in H.
  lets Hx: Hg4 H.
  mytac.
  exists x0.
  assert(x0 <> x10).
  unfolds; intros.
  subst x0.
  assert (Hr: eid = x \/ eid <> x)by tauto.
  destruct Hr as [He | Hn].
  subst eid.
  unfolds in Hg1. mytac.
  lets Hy: H12 H.
  unfolds in Hy. mytac.
  unfold get in H6; simpl in H6; rewrite H6 in H14; inverts H14.
  simpl in H15; tryfalse.

  unfolds in H0.
  eapply H0 in Hels; eauto.
  unfolds in Hels.
  assert(Hr: TcbMod.get x3 x10 <> None).
  unfolds; intros.
  unfold get in H7;simpl in H7.
  rewrite H7 in H11; inverts H11.
  eapply Hels in Hr; eauto.
  destruct Hr.
  destruct H12.
  exists x.
  splits; eauto.
  unfolds.
  do 3 eexists; eauto.

  assert(Hr: eid = x \/ eid <> x) by tauto.
  destruct Hr as [He | Hn].
  subst eid.
  unfolds in Hg1. mytac.
  lets Hy: H13 H.
  unfolds in Hy. mytac.
  unfolds in H6; simpl in H6.
  rewrite H6 in H15.
  inverts H15.
  inverts H16.

  do 3 eexists.
  splits; eauto.
  unfolds.
  unfolds in H2. mytac.
  rewrite EcbMod.map_get_set' ; eauto.
  rewrite TcbMod.map_get_set' ; eauto.
  intros.
  eapply H8; eauto.
  unfolds.
  intros.
  unfolds in H12.
  assert(Hr: x10 = t \/ x10 <> t) by tauto.
  destruct Hr as [He | Hne].
  subst x10; tryfalse.
  (*   rewrite TcbMod.map_get_set in H12 ; eauto. *)
  destruct H12; auto. mytac.
  rewrite TcbMod.map_get_set'; auto.
  simpljoin.

  assert(x12 <> x).
  unfolds; intros.
  subst x12.
  unfolds in H12.
  mytac.
  rewrite EcbMod.map_get_set in H12; eauto.
  inverts H12.

  left.
  exists x12.
  unfolds.
  unfolds in H12. 
  mytac.
  rewrite EcbMod.map_get_set' in H12; eauto.
  right.
  simpljoin. splits.
  inverts H14.
  unfolds; intros. destruct H12. mytac.
  exists x16.
  assert(x16 <> x).
  unfolds; intros.
  subst x16.
  unfolds in H12. mytac.  
  unfold get in H6; simpl in H6.
  rewrite H6 in H12; inverts H12; tryfalse.
  unfolds in H12.
  unfolds. mytac.
  rewrite EcbMod.map_get_set'; eauto.
  rewrite TcbMod.map_get_set' in H14; eauto. auto.

  (*op_p_prop*)
  unfolds. intros.
  (*   eapply Hg5; eauto. *)
  assert(Hr: x10 = t \/ x10 <> t) by tauto.
  destruct Hr as [He | Hn].
  subst x10.
  rewrite TcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true; auto].
  inverts H.
  unfolds in H2.

  assert(TcbMod.get (set x3 t (p, st, m, sus)) t <> None).
  rewrite TcbMod.map_get_set; auto.
  apply H2 in H.
  destruct H2.
  mytac.
  rewrite TcbMod.map_get_set; auto.
  destruct H2.
  assert(x0 <> x).
  unfolds; intros.
  subst x0.
  unfolds in H2. mytac.
  rewrite EcbMod.map_get_set in H2.
  inverts H2.
  unfolds in H2.
  rewrite EcbMod.map_get_set' in H2.
  mytac.
  
  unfolds in H0.
  eapply H0 in Hels; eauto.
  unfolds in Hels.
  assert(TcbMod.get x3 t <> None).  
  unfolds; intros.
  unfold get in H7; simpl in H7; rewrite H7 in H5.
  inverts H5.
  apply Hels with (qid:= x) in H5.
  destruct H5.
  destruct H8.
  exists x0.
  split; auto;
    unfolds; do 3 eexists; eauto.
  unfolds; do 3 eexists; eauto.
  eauto.
  destruct H2.
  rewrite TcbMod.map_get_set in H4. mytac.
  inverts H4.
  right; rewrite Int.eq_true; eauto.
  rewrite TcbMod.map_get_set' in H. mytac.
  eapply Hg5; eauto.
  eapply post_nowt_return_getop_t; eauto.
  auto.

  (*nowner_prio_prop*)
  unfold nowner_prio_prop in *.
  intros.
  assert (Hr: t = x10 \/ t <> x10 ) by tauto.
  destruct Hr. subst.
  rewrite TcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
  inverts H.
  unfolds in H4.
  assert (TcbMod.get (set x3 x10 (p, st, m, sus)) x10 <> None).
  rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  auto.
  apply H4 in H.

  destruct H. mytac.
  assert (x0 <> x). intro.
  subst x0.
  unfolds in H. mytac.
  rewrite EcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
  inverts H. unfolds in H.
  rewrite EcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto].
  mytac.

  unfolds in H0.
  eapply H0 in Hels; eauto.
  unfolds in Hels.
  assert(TcbMod.get x3 x10 <> None).  
  intro.
  unfold get in *; simpl in *; rewrite H7 in H8;tryfalse.
  apply Hels with (qid:=x) in H8.
  destruct H8 as (Hst & Hnq).
  destruct Hnq.
  exists x0.
  split;auto.
  unfolds;do 3 eexists;eauto.
  unfolds;do 3 eexists;eauto.
  destruct H.
  rewrite TcbMod.set_a_get_a in H5;[ | apply tidspec.eq_beq_true;auto]. 
  mytac.
  inverts H5. auto.
  
  rewrite TcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto].
  eapply Hg6;eauto.
  intro. 
  eapply H2. mytac.
  exists x0.
  assert (x0 <> x).
  intro. subst x0.
  unfolds in H8.
  mytac.
  unfold get in *; simpl in *; rewrite H8 in H6; inverts H6; tryfalse.
  unfolds in H8.
  unfolds.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto]. 
  mytac.
  do 3 eexists;eauto.
  eapply post_nowt_return_getop_t;eauto.
Qed.

Lemma good_dt_mutexunlock_nowt_noret_succ_preserved:
  forall 
    (O' O : OSAbstMod.map)
    (O0 Of : OSAbstMod.map)
    (x : addrval)
    (x2 : PtbMod.map)
    (x4 : EcbMod.map)
    (x7 : int32)
    (H10 : join
             (set
                (set O0 absecblsid
                   (absecblist (set x4 x (absmutexsem x7 None, nil)))) absptlsid
                (absptls (set x2 x7 Holder))) Of O')
    (H9 : join O0 Of O)
    (H1 : GOOD_DT O)
    (H0 : NO_NEST_PENDING_O O)
    (Hnest : NO_NEST_PENDING_O O')
    (x5 : TcbMod.map)
    (x8 x9 : int32)
    (x10 : taskstatus)
    (x11 : msg)
    (sus : susstatus)
    (x12 : addrval)
    (H2 : get O0 curtid = Some (oscurt x12))
    (H3 : get O0 absecblsid = Some (absecblist x4))
    (H4 : get O0 abtcblsid = Some (abstcblist x5))
    (H5 : get O0 absptlsid = Some (absptls x2))
    (H6 : get x4 x = Some (absmutexsem x7 (Some (x12, x8)), nil))
    (H7 : get x5 x12 = Some (x9, x10, x11, sus))
    (H8 : Int.eq x9 x7 = false), 
    GOOD_DT O'. 
Proof.
  intros.
  assert (get O absecblsid = Some (absecblist x4)) as Hels.
  eapply join_get_get_l;eauto.
  assert (get O abtcblsid = Some (abstcblist x5)) as Htls.
  eapply join_get_get_l;eauto.
  assert (get O curtid = Some (oscurt x12)) as Hcurt.
  eapply join_get_get_l;eauto.
  assert (get O absptlsid = Some (absptls x2)) as Hptls.
  eapply join_get_get_l;eauto.

  assert (O'=set
               (set O absecblsid
                  (absecblist
                     (set x4 x (absmutexsem x7 None, nil))))
               absptlsid (absptls (set x2 x7 Holder))).
  eapply join_get_set_eq_2;eauto.
  clear H2 H3 H4 H5.
  remember O as Ox.
  clear HeqOx.
  subst O'.

  unfolds.
  intros.
  rewrite abst_set_get_neq in H, H2, H3;auto.
  rewrite OSAbstMod.map_get_set in H4.
  inverts H4.
  rewrite OSAbstMod.map_get_set in H.
  inverts H.
  rewrite abst_set_get_neq in H2, H3;auto.
  (*   rewrite OSAbstMod.map_get_set in H2.
  inverts H2.
  rewrite abst_set_get_neq in H3;auto. *)
  unfold get in Htls; simpl in Htls; rewrite Htls in H2; inverts H2.
  
  unfolds in H1.
  lets Hgoodst: H1 Hels Htls H3 Hptls.
  destruct Hgoodst as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6).
  splits; auto.
  (*rdy_notin_wl*)
  unfolds.
  unfolds in Hg1.
  simpljoin. splits.
  intros.
  (*   assert(Hor: x10 = t \/ x10 <> t) by tauto.
  destruct Hor as [Heq | Hneq].
  subst x10.
  rewrite TcbMod.map_get_set in H5.
  inverts H5. *)
  unfolds.
  intros.
  unfolds in H11.
  mytac.
  assert (Hor: x = x0 \/ x<>x0 ) by tauto.
  destruct Hor as [He | Hn].
  (*   eapply tidspec.eq_beq_true in He. *)
  (*   rewrite EcbMod.map_eq in H8. *)
  subst x.
  rewrite PIF_language.EcbMap_obligation_21 in H11.
  inverts H11; tryfalse.

  rewrite EcbMod.map_get_set' in H11.
  eapply H in H5; eauto.
  eapply H5.
  unfolds.
  do 4 eexists; splits; eauto. auto.
  intros.
  unfolds.
  assert(x <> eid).
  unfolds;intros.
  subst x.
  eapply H2 in H5; eauto.
  unfolds in H5.
  mytac.
  unfold get in H6; simpl in H6; rewrite H6 in H5; inverts H5; tryfalse.
  rewrite EcbMod.map_get_set'.
  eapply H2 in H5; eauto. auto.
  intros.
  eapply H4; eauto.
  unfolds in H5. 
  assert(Hor: x = eid \/ x <> eid) by tauto.
  destruct Hor as [He | Hn].
  subst x. mytac.
  rewrite EcbMod.map_get_set in H5. inverts H5; tryfalse.
  rewrite EcbMod.map_get_set' in H5.
  unfolds.  eauto. auto.
  
  (*owner_prio_prop*)
  unfolds; intros.
  assert(Hr: x = eid \/ x <> eid) by tauto.
  destruct Hr as [He | Hn].
  subst x. rewrite EcbMod.map_get_set in H2. inverts H2.
  rewrite EcbMod.map_get_set' in H2.
  eapply Hg2; eauto. auto.

  (**wait_prop**)
  unfold wait_prop in *.
  intros.
  assert(t <> x12).
  unfolds; intros.
  subst t.
  unfolds in Hg1.
  destruct Hg1 as (Ha & Hb & Hc).
  eapply Hb in H.
  unfolds in H0.
  eapply H0 in Hels; eauto.
  unfolds in Hels.
  assert(Hr: TcbMod.get tls x12 <> None).
  unfolds; intros.
  unfold get in H7; simpl in H7; rewrite H2 in H7; inverts H7.
  apply Hels with (qid:= x) in Hr.
  destruct Hr as (Ha1 & Hb1).
  destruct Ha1.
  unfolds.
  unfolds in H.
  mytac.
  do 4 eexists; split; eauto.
  unfolds. do 3 eexists; eauto.

  lets Hx: Hg4 H.
  destruct Hx as (t' & po & m' & sus' & Ha1 & Hb1 & Hc1 & Hd1).
  exists t'.
  assert(t' <> x12).
  unfolds; intros.
  subst t'.
  assert(Hor: eid = x \/ eid <> x) by tauto.
  destruct Hor as [He | Hne].
  subst x.
  unfolds in Hg1.
  destruct Hg1 as (Ha & Hb & Hc).
  eapply Hb in H.
  unfolds in H.
  destruct H as (p_q & ow & wl & Heg & Hin).
  unfold get in H6; simpl in H6; rewrite Heg in H6; inverts H6; tryfalse.

  unfolds in H0.
  eapply H0 in Hels; eauto.
  unfolds in Hels.
  assert(Hr: TcbMod.get tls x12 <> None).
  unfolds; intros.
  unfold get in H7; simpl in H7; rewrite H4 in H7; inverts H7.
  apply Hels with (qid:= x) in Hr.
  destruct Hr as (He1 & He2).
  destruct He2.
  exists eid.
  splits; eauto.
  unfolds.
  do 3 eexists; eauto.

  assert(Hr: eid = x \/ eid <> x ) by tauto.
  destruct Hr as [He | Hne].
  subst x.
  unfolds in Hg1.
  destruct Hg1 as (Ha & Hb & Hc).
  eapply Hb in H.
  unfolds in H.
  destruct H as (p_q & oe & wl & Heg & Hin).
  unfold get in H6; simpl in H6; rewrite H6 in Heg; inverts Heg; tryfalse.
  do 3 eexists.
  splits;eauto.
  unfolds.
  unfolds in Ha1.
  simpljoin.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;eauto.

  intros.
  apply Hd1.
  unfolds.
  intro.
  unfolds in H5.
  lets Hx: H5 H11.
  destruct Hx.
  mytac.
  assert (x0 <> x).
  unfolds; intros.
  subst x0.
  unfolds in H12.
  mytac.
  rewrite EcbMod.set_a_get_a in H12;[ | apply tidspec.eq_beq_true;auto].
  inverts H12.

  left. 
  exists x0.
  unfolds.
  unfolds in H12.
  mytac.
  rewrite EcbMod.set_a_get_a' in H12;[ | apply tidspec.neq_beq_false;auto].
  do 2 eexists.
  eauto.
  right.
  simpljoin. splits.
  intro.
  destruct H12.
  mytac.
  exists x5.
  assert (x5 <> x).
  intro.
  subst x5.
  unfolds in H12.
  mytac.
  unfold get in H6; simpl in H6; rewrite H12 in H6; inverts H6; tryfalse.
  unfolds in H12.
  unfolds.
  mytac.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;eauto.
  do 2 eexists;eauto.

  (*op_p_prop*)
  unfold op_p_prop in *.
  intros.
  eapply Hg5; eauto.
  (* unfolds in H2. *)
  assert (Hr: t = x12 \/ t <> x12) by tauto.
  destruct Hr as [He | Hne].
  subst t.
  unfolds; intros.  
  left.
  exists x.
  unfolds.
  unfolds in H2.
  lets Hx: H2 H4.
  destruct Hx.
  mytac.
  unfolds in H5.
  assert (Hr: x0 = x \/ x0 <> x) by tauto.
  destruct Hr as [He | Hne].
  subst x0.
  mytac.
  rewrite EcbMod.set_a_get_a in H5;[ | apply tidspec.eq_beq_true;auto].
  inverts H5.
  rewrite EcbMod.set_a_get_a' in H5;[ | apply tidspec.neq_beq_false;auto].
  unfolds in H0.
  (*   
  assert(Hr: TcbMod.get tls x12 <> None).
  unfolds; intros.
  rewrite H in H5; inverts H5. *)
  eapply H0 in Hels; eauto.
  unfolds in Hels.
  eapply Hels with (qid:= x) in H4; eauto.
  destruct H4.
  destruct H11.
  exists x0.
  splits; auto. 
  unfolds.
  mytac; do 3 eexists;eauto.
  mytac; unfolds; do 3 eexists; eauto.
  destruct H5 as (Hf & (st' & m' & sus' & Ht)).
  rewrite Ht in H; inverts H.
  unfolds in Hg2.
  lets Hx: Hg2 Ht H6.
  unfold get in H7; simpl in H7; rewrite H7 in Ht; inverts Ht.
  destruct Hx as ([Heq | Hneq ] & Hlt).
  subst.
  clear -H8; int auto.
  subst x8.
  do 2 eexists; eauto.

  unfolds; intros.
  unfolds in H2.
  lets Hx: H2 H4.
  destruct Hx.
  left.
  destruct H5 as (qid & Ho).
  assert(Hn: qid <> x).
  unfolds; intros.
  subst qid.
  unfolds in Ho.
  rewrite EcbMod.set_a_get_a in Ho;[ | apply tidspec.eq_beq_true;auto].
  destruct Ho as (p_q & wl & Heg). inverts Heg.
  unfolds in Ho.
  rewrite EcbMod.set_a_get_a' in Ho;[ | apply tidspec.neq_beq_false;auto].
  destruct Ho as (p_q & wl & Heg). inverts Heg.
  exists qid. unfolds.
  do 2 eexists;eauto.

  right.
  destruct H5 as (Hf & Ht).
  splits; eauto.
  intro.
  destruct Hf.
  mytac.
  exists x0.
  unfolds in H5.
  unfolds.
  mytac.
  assert(Hn: x <> x0).
  intro.
  subst x.
  unfold get in H6; simpl in H6; rewrite H5 in H6; inverts H6; tryfalse.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists; eauto.
  
  (*nowner_prio_prop*)
  unfold nowner_prio_prop in *.
  intros.
  assert (Hr: t = x12 \/ t <> x12) by tauto.
  destruct Hr.
  subst t.
  unfolds in H4.
  assert (TcbMod.get tls x12 <> None). intro.
  rewrite H in H5; tryfalse.
  lets Hx:H4 H5.
  destruct Hx. mytac.
  assert (Hr: x0 = x \/ x0 <> x) by tauto.
  destruct Hr. subst x0.
  unfolds in H11. mytac.
  rewrite EcbMod.set_a_get_a in H11;[ | apply tidspec.eq_beq_true;auto].
  inverts H11.
  unfolds in H0.
  eapply H0 in Hels; eauto.
  unfolds in Hels.
  eapply Hels with (qid:= x0) in H5; eauto.
  destruct H5 as (Hst & Hnq).
  destruct Hnq.
  exists x;split;eauto.
  unfolds.
  do 3 eexists;eauto.
  unfolds in H11.
  unfolds. mytac.
  rewrite EcbMod.set_a_get_a' in H11;[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;eauto.

  destruct H11. mytac.
  rewrite H12 in H; inverts H; auto.

  eapply Hg6;eauto. intro.
  destruct H2. mytac.
  exists x0.
  unfolds in H2. mytac.
  unfolds.
  assert (x0 <> x).
  intro. subst x0.
  unfold get in *; simpl in *; rewrite H2 in H6.
  inverts H6; tryfalse.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;eauto.

  unfolds; intro.
  unfolds in H4.
  lets Hx: H4 H11.
  destruct Hx. mytac.
  assert (x0 <> x).
  intro.
  subst x0.
  unfolds in H12. mytac.
  rewrite EcbMod.set_a_get_a in H12;[ | apply tidspec.eq_beq_true;auto].
  inverts H12.
  
  left. exists x0.
  unfolds.
  unfolds in H12. mytac.
  rewrite EcbMod.set_a_get_a' in H12;[ | apply tidspec.neq_beq_false;auto].
  do 2 eexists. eauto.
  right. simpljoin. splits. intro.
  destruct H12. mytac.
  exists x5.
  assert (x5 <> x).
  intro. subst x5.
  unfolds in H12. mytac.
  unfold get in *; simpl in *; rewrite H12 in H6; inverts H6; tryfalse.
  unfolds in H12. unfolds.
  mytac.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;eauto.
  do 2 eexists;eauto.      
Qed.

Lemma good_dt_mutexlock_exwt_ret_succ_preserved:
  forall
    (O' O : OSAbstMod.map)
    (O0 Of : OSAbstMod.map)
    (x : addrval)
    (x2 : EcbMod.map)
    (x3 : TcbMod.map)
    (x7 : PtbMod.map)
    (x9 x10 x11 : int32)
    (x12 : taskstatus)
    (x13 : msg)
    (x14 : list tid)
    (x15 : tid)
    (x18 : addrval)
    (x19 x20 : susstatus)
    (H10 : join
             (set
                (set
                   (set O0 abtcblsid
                      (abstcblist
                         (set (set x3 x18 (x11, x12, x13, x19)) x15
                            (x10, rdy, Vnull, x20)))) absecblsid
                   (absecblist
                      (set x2 x
                         (absmutexsem x9 (Some (x15, x10)), remove_tid x15 x14))))
                absptlsid (absptls (set (set x7 x11 (Valid_Addr x18)) x9 Holder)))
             Of O')
    (H9 : join O0 Of O)
    (H1 : GOOD_DT O)
    (H0 : NO_NEST_PENDING_O O)
    (Hnest : NO_NEST_PENDING_O O')
    (x16 : taskstatus)
    (x17 : msg)
    (H2 : get O0 curtid = Some (oscurt x18))
    (H3 : get O0 absecblsid = Some (absecblist x2))
    (H4 : get O0 abtcblsid = Some (abstcblist x3))
    (H5 : get O0 absptlsid = Some (absptls x7))
    (H6 : get x2 x = Some (absmutexsem x9 (Some (x18, x11)), x14))
    (H7 : x14 <> nil)
    (H8 : GetHWait x3 x14 x15)
    (H11 : get x3 x18 = Some (x9, x12, x13, x19))
    (H12 : get x3 x15 = Some (x10, x16, x17, x20)), 
    GOOD_DT O'. 
Proof.
  intros.
  assert (get O absecblsid = Some (absecblist x2)) as Hels.
  eapply join_get_get_l;eauto.
  assert (get O abtcblsid = Some (abstcblist x3)) as Htls.
  eapply join_get_get_l;eauto.
  assert (get O curtid = Some (oscurt x18)) as Hcurt.
  eapply join_get_get_l;eauto.
  assert (get O absptlsid = Some (absptls x7)) as Hptls.
  eapply join_get_get_l;eauto.

  assert (O'=set
               (set
                  (set O abtcblsid
                     (abstcblist
                        (set (set x3 x18 (x11, x12, x13, x19)) x15
                           (x10, rdy, Vnull, x20)))) absecblsid
                  (absecblist
                     (set x2 x
                        (absmutexsem x9 (Some (x15, x10)),
                          remove_tid x15 x14)))) absptlsid
               (absptls
                  (set (set x7 x11 (Valid_Addr x18)) x9 Holder))).
  eapply join_get_set_eq_3;eauto.
  clear H2 H3 H4 H5.
  remember O as Ox.
  clear HeqOx.
  subst O'.
  unfold GOOD_DT in *.
  intros.
  unfolds in Hnest.
  lets Hnest': Hnest H H2.
  clear Hnest.
  unfolds in H0.
  lets Hnn: H0 Hels Htls.
  clear H0.

  rewrite abst_set_get_neq in H, H2, H3;auto.
  rewrite OSAbstMod.map_get_set in H4.
  inverts H4.
  rewrite OSAbstMod.map_get_set in H.
  inverts H.
  rewrite abst_set_get_neq in H2, H3;auto.
  rewrite OSAbstMod.map_get_set in H2. inverts H2.
  rewrite abst_set_get_neq in H3;auto.
  lets Hgoodst: H1 Hels Htls H3 Hptls.
  destruct Hgoodst as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6).

  assert(x18 <> x15) as Hneq.
  intro.
  subst x18.
  unfolds in Hnn.
  assert(Hn: TcbMod.get x3 x15 <> None).
  intro.
  unfold get in H11; simpl in H11; rewrite H in H11; inverts H11.
  eapply Hnn with (qid:= x) in Hn.
  mytac.
  destruct H. unfolds. do 4 eexists; split; eauto.
  unfolds in H8.
  mytac; auto.
  unfolds; do 3 eexists; eauto.

  assert (~ ST_WAIT_T x18 x2) as Hctnwait.
  intro.
  unfolds in Hnn.
  assert (TcbMod.get x3 x18 <> None).
  intro.
  unfold get in H11; simpl in H11; rewrite H11 in H0;tryfalse.
  apply Hnn with (qid:=x) in H0.
  simpljoin.
  destruct H0. auto.
  unfolds. do 3 eexists;eauto.
  
  (*rdy_notin_wl*)
  lets Hg1': Hg1.
  unfold rdy_notin_wl in Hg1.
  unfold rdy_notin_wl.
  simpljoin. splits.
  splits. intros.
  assert (Hr: t = x18 \/ t <> x18) by tauto.
  destruct Hr.
  subst t.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.
  apply H in H11.
  intro.

  destruct H11.
  eapply post_iswait;eauto.
  assert (Hr: t = x15 \/ t <> x15) by tauto.
  destruct Hr.
  subst x15.
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.

  eapply nnp_remove_nwait;eauto.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  apply H in H4.
  intro.
  destruct H4.
  eapply remove_is_wait_neq;eauto.
  
  intros.
  assert (Hr: t = x18 \/ t <> x18) by tauto.
  destruct Hr.
  subst t.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.
  lets Hx:H0 H11.
  unfolds in Hnn.
  assert (TcbMod.get x3 x18 <> None).
  intro.
  unfold get in H11; simpl in H11; rewrite H11 in H4;tryfalse.
  apply Hnn with(qid:=x)in H4.
  destruct H4 as (Hs & Hi).
  destruct Hs.
  unfolds in Hx;mytac;unfolds;do 4 eexists;eauto.
  unfolds;do 3 eexists;eauto.

  assert (t <> x15).
  intro.
  subst x15.
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  apply H0 in H4.
  eapply post_iswait' in H13;eauto.
  destruct H13;eauto.

  intros.
  assert (Hr: t = x18 \/ t <> x18) by tauto.
  destruct Hr.
  subst t.
  assert (IS_WAITING_E x18 eid x2).
  eapply post_iswait';eauto.
  unfolds in Hnn.
  assert (TcbMod.get x3 x18 <> None).
  intro.
  unfold get in H11; simpl in H11. rewrite H13 in H11;tryfalse.
  apply Hnn with(qid:=x)in H13.
  destruct H13 as (Hs & Hi).
  destruct Hs.
  unfolds in H5;mytac;unfolds;do 4 eexists;eauto.
  unfolds;do 3 eexists;eauto.

  assert (Hr: t = x15 \/ t <> x15) by tauto.
  destruct Hr.
  subst t.
  rename H8 into Hhig.
  lets Hx: nnp_remove_nwait Hnn Hg1' Hhig H6 H12.
  destruct Hx.
  unfolds in H4; mytac.
  unfolds;do 4 eexists;split;eauto.
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  eapply H2; eauto.
  eapply post_iswait';eauto.

  (*owner_prio_prop*)
  unfold owner_prio_prop in *.
  intros.

  assert (Hr: t = x18 \/ t <> x18 ) by tauto.
  destruct Hr.
  subst t.

  assert (eid <> x).
  intro.
  subst x.
  rewrite EcbMod.set_a_get_a in H5;[ | apply tidspec.eq_beq_true;auto].
  inverts H5;tryfalse.

  unfolds in Hnn.
  rewrite EcbMod.set_a_get_a' in H5; [ | apply tidspec.neq_beq_false;auto].
  assert (TcbMod.get x3 x18 <> None).
  intro.
  unfold get in H11; simpl in H11; rewrite H11 in H14;tryfalse.
  apply Hnn with (qid:=eid) in H14.
  destruct H14 as (Hs & Hi).
  destruct Hs.
  destruct Hi.
  exists x.
  split;auto.
  unfolds;do 3 eexists;eauto.
  unfolds;do 3 eexists;eauto.

  (*--------------*)
  assert (Hr: t <> x15 \/ t = x15) by tauto.
  destruct Hr.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  eapply Hg2;eauto.
  assert (eid <> x).
  intro.
  subst x.
  rewrite EcbMod.set_a_get_a in H5;[ | apply tidspec.eq_beq_true;auto].
  inverts H5;tryfalse.
  rewrite EcbMod.set_a_get_a' in H5;[ | apply tidspec.neq_beq_false;auto].
  eauto.

  subst x15.
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.

  assert (Hr: eid = x \/ eid <> x ) by tauto.
  destruct Hr.
  subst x.
  rewrite  EcbMod.set_a_get_a in H5;[ | apply tidspec.eq_beq_true;auto].
  inverts H5.
  split;auto.
  unfolds in Hg4.
  assert (Hw: IS_WAITING_E t eid x2).
  unfolds.
  do 3 eexists;split;eauto.
  unfolds in H8;mytac;auto.
  apply H2 in Hw.
  destruct Hw as (p & tm & m & su & Ht).
  unfold get in H12; simpl in H12; rewrite Ht in H12;inverts H12.
  apply Hg4 in Ht.
  destruct Ht as (t' & po' & m' & sus' & Hi & Ht' & [ Hl | Heq] & Hop);
    unfolds in Hi;
    destruct Hi as (p_q & p_ow & wl & Heg);
    unfold get in H6; simpl in H6; rewrite Heg in H6;inverts H6.
  unfold get in H11; simpl in H11; rewrite H11 in Ht'; inverts Ht'.
  auto.
  unfold get in H11; simpl in H11; rewrite H11 in Ht'; inverts Ht'. auto.
  rewrite EcbMod.set_a_get_a' in H5;[ | apply tidspec.neq_beq_false;auto].
  eauto.

  (*task_stat_prop*)
  unfolds; intros.
  assert (Hr: t = x18 \/ t <> x18 ) by tauto.
  destruct Hr.
  subst t.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4; auto.
  apply Hg3 in H11;auto.

  assert (Hr: t = x15 \/ t <> x15 ) by tauto.
  destruct Hr.
  subst t.
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4;auto.

  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  apply Hg3 in H4; auto.

  (*wait_prop*)
  unfolds; intros.
  assert (Hr: t = x18 \/ t <> x18 ) by tauto.
  destruct Hr.
  subst.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.
  unfolds in Hnn.
  assert ( TcbMod.get x3 x18 <> None ).
  intro.
  unfold get in H11; simpl in H11; rewrite H11 in H4;tryfalse.
  apply Hnn with (qid:=x) in H4.
  destruct H4 as (Hst & Hnq).
  destruct Hst.
  apply H0 in H11.
  unfolds.
  unfolds in H11.
  mytac.
  do 4 eexists;split;eauto.
  unfolds;do 3 eexists;eauto.

  assert ( Hr: t <> x15 \/ t = x15) by tauto.
  destruct Hr.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  lets Hx:Hg4 H4.
  destruct Hx as (t' & po' & m' & sus' & Hi & Hlt & Hop).
  
  assert (Hr: t' = x18 \/ t' <> x18) by tauto.
  destruct Hr.
  subst t'.
  lets Hy:H0 H4.
  unfolds in Hy.
  destruct Hy as (p_q & ow & wl & Heg & Hin).
  unfolds in Hi.
  destruct Hi as (p_q' & p_ow & wl' & Heg').

  assert (Hr: eid = x \/ eid <> x) by tauto.
  destruct Hr.
  subst x.
  rewrite Heg' in Heg; inverts Heg.
  unfold get in H6; simpl in H6; rewrite Heg' in H6; inverts H6.
  unfold get in H11; simpl in H11; rewrite H11 in Hlt.
  inverts Hlt.
  exists x15 x10 Vnull x20.
  simpljoin. splits.
  unfolds.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;eauto.
  rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  auto.
  unfolds in H8.
  lets Hx: H0 H4.
  unfolds in Hx.
  simpljoin.
  rewrite H15 in Heg'; inverts Heg'.
  eapply H18 with (t':=t) in Hin;eauto.
  unfold get in *;simpl in *.
  rewrite H17 in H12;inverts H12.
  mytac.
  rewrite H4 in H12;inverts H12;auto.

  introv Hget.
  unfolds in Hget.
  apply H14.
  unfolds; intro.
  rewrite TcbMod.set_a_get_a' in Hget;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a' in Hget;[ | apply tidspec.neq_beq_false;auto].
  apply Hget in H15.
  destruct H15.
  left. mytac.
  unfolds in H15. mytac.
  assert (eid <> x).
  intro.
  subst eid.
  rewrite EcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
  inverts H15. tryfalse.
  rewrite EcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
  exists x;unfolds.
  do 2 eexists;eauto.

  right. simpljoin. splits. intro.
  destruct H15. mytac.
  exists x4. unfolds.
  assert (x4 <> eid).
  intro. subst x4.
  unfolds in H15. mytac.
  rewrite H15 in Heg'; inverts Heg'. tryfalse.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  unfolds in H15;mytac.
  do 3 eexists;eauto.
  do 2 eexists;eauto.

  rewrite Heg in Heg'; inverts Heg'.
  unfolds in Hnn.
  assert (TcbMod.get x3 x18 <> None).
  intro.
  rewrite H15 in Hlt; tryfalse.
  apply Hnn with (qid:=eid) in H15.
  destruct H15 as (Hst & Hf).
  destruct Hf.
  exists x;split;auto.
  unfolds;do 3 eexists;eauto.
  unfolds;do 3 eexists;eauto.

  exists t'.
  assert (t' <> x15).
  intro. subst t'.
  unfolds in Hnn.
  assert (TcbMod.get x3 x15  <> None).
  intro.
  rewrite Hlt in H15;tryfalse.
  apply Hnn with (qid:=eid) in H15.
  destruct H15 as (Hst & Hf).
  destruct Hst.
  unfolds. exists x.
  do 3 eexists;split;eauto.
  unfolds in H8;mytac;auto. auto.
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;splits;eauto.
  unfolds in Hi; unfolds. simpljoin.
  assert (x <> eid).
  intro. subst x.
  unfold get in *; simpl in *; rewrite H16 in H6;inverts H6;tryfalse.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;eauto.
  mytac; auto.

  intros.
  unfolds in H16.
  destruct Hop as (Hop & Hopp).
  apply Hopp.
  unfolds; intro.
  rewrite TcbMod.set_a_get_a' in H16;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a' in H16;[ | apply tidspec.neq_beq_false;auto].
  apply H16 in H17.
  destruct H17 as [Hng | Hg].
  left. mytac.
  unfolds in H17. mytac.
  assert (x0 <> x). intro.
  subst x0.
  rewrite EcbMod.set_a_get_a in H17;[ | apply tidspec.eq_beq_true;auto].
  inverts H17; tryfalse.
  rewrite EcbMod.set_a_get_a' in H17;[ | apply tidspec.neq_beq_false;auto].
  exists x0; unfolds.
  do 2 eexists;eauto.

  right. simpljoin. splits. intro.
  destruct H17.
  mytac.
  exists x5. unfolds.
  assert (x5 <> x).
  intro. subst x.
  unfolds in H17.
  simpljoin.
  unfold get in *; simpl in *; rewrite H17 in H6;inverts H6. tryfalse.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  unfolds in H17;mytac.
  do 3 eexists;eauto.
  do 2 eexists;eauto.

  subst t.
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.

  (*op_p_prop*)
  unfold op_p_prop in *.
  intros.
  assert (Hr: t= x18 \/ t <> x18) by tauto.
  destruct Hr. subst.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.
  unfolds in H5.

  assert ( TcbMod.get
             (set (set x3 x18 (p, st, m, sus)) x15 (x10, rdy, Vnull,x20))
             x18 <> None ).
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto]. auto.
  apply H5 in H4. destruct H4.
  mytac.
  assert (x0 <> x). intro.
  subst x0.
  unfolds in H4. mytac.
  rewrite EcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4;tryfalse.
  unfolds in H4.
  rewrite EcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  mytac.

  unfolds in Hnn.
  assert (TcbMod.get x3 x18 <> None). intro.
  unfold get in *; simpl in *; rewrite H14 in H11;tryfalse.
  apply Hnn with (qid:=x) in H14.
  destruct H14 as (Hst & Hf).
  destruct Hf.
  exists x0.
  split;auto.
  unfolds;do 3 eexists;eauto.
  unfolds;do 3 eexists;eauto.
  destruct H4.
  rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto]. 
  mytac.
  inverts H13.
  right.
  clear; int auto.

  assert (Hr: t <> x15 \/ t = x15) by tauto.
  destruct Hr.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  eapply Hg5;eauto.

  unfolds; intro.
  unfolds in H5.
  assert (TcbMod.get (set (set x3 x18 (x11, x12, x13,x19)) x15
                        (x10, rdy, Vnull,x20)) t <> None).
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto]. auto.
  apply H5 in H16.
  destruct H16. mytac.
  left.
  exists x0.
  assert (x0 <> x). intro.
  subst x0.
  unfolds in H16.
  rewrite EcbMod.set_a_get_a in H16;[ | apply tidspec.eq_beq_true;auto].
  mytac.
  inverts H16;tryfalse.
  unfolds in H16.
  mytac.
  rewrite EcbMod.set_a_get_a' in H16;[ | apply tidspec.neq_beq_false;auto].
  unfolds.
  do 2 eexists;eauto.
  right.
  rewrite TcbMod.set_a_get_a' in H16;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a' in H16;[ | apply tidspec.neq_beq_false;auto].
  simpljoin. splits.
  intro.
  destruct H16.
  mytac.
  exists x5.
  unfolds in H16.
  mytac.
  unfolds.
  assert (x <> x5).
  intro.
  subst x5.
  unfold get in *; simpl in *; rewrite H16 in H6; inverts H6; tryfalse.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;eauto.
  do 2 eexists;eauto.

  subst t.
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.
  unfolds in H5.
  assert (TcbMod.get (set (set x3 x18 (x11, x12, x13,x19)) x15
                        (p, rdy, Vnull, sus)) x15 <> None ).
  rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto]. auto.
  apply H5 in H4.
  destruct H4.
  mytac.
  assert (Hr: x <> x0 \/ x = x0) by tauto.
  destruct Hr.
  unfolds in Hnest'.
  assert (TcbMod.get (set (set x3 x18 (x11, x12, x13,x19)) x15
                        (p, rdy, Vnull,sus)) x15 <> None).
  intro.
  rewrite TcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
  tryfalse.
  apply Hnest' with (qid:=x) in H15.
  mytac.
  destruct H16.
  exists x0. split;auto.
  unfolds in H4.
  mytac. unfolds.
  do 3 eexists;eauto.
  unfolds.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;eauto.
  subst x0.
  unfolds in H4. mytac.
  rewrite EcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.
  right;clear;int auto.

  destruct H4.
  destruct H4.
  exists x.
  unfolds.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;eauto.

  (*no_owner_prio_prop*)
  unfold nowner_prio_prop in *.
  intros.
  assert (Hr: t = x18 \/ t <> x18) by tauto.
  destruct Hr. subst.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.
  unfolds in H13.
  assert ( TcbMod.get (set (set x3 x18 (p, st, m, sus)) x15 (x10, rdy, Vnull, x20))
             x18 <> None).
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  auto.
  apply H13 in H4.

  destruct H4. mytac.
  assert (x0 <> x).
  intro. subst x0.
  unfolds in H4.
  mytac.
  rewrite EcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4; tryfalse.
  unfolds in H4.
  rewrite EcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  mytac.

  unfolds in Hnn.
  assert (Hn: TcbMod.get x3 x18 <> None).
  intro.
  unfold get in *; simpl in *; rewrite H15 in H11;tryfalse.
  apply Hnn with (qid:=x) in Hn.
  destruct Hn as (Hi & Hf).
  destruct Hf.
  exists x0.
  split;auto.
  unfolds;do 3 eexists;eauto.
  unfolds;do 3 eexists;eauto.
  
  destruct H4.
  rewrite TcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto]. 
  mytac.
  inverts H14.
  auto.

  assert (Hr: t = x15 \/ t <> x15) by tauto.
  destruct Hr.
  subst t.
  destruct H5.
  exists x.
  unfolds.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;eauto.

  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  eapply Hg6;eauto.
  intro.
  destruct H5. mytac.
  exists x0.
  assert (x0 <> x).
  intro. subst x0.
  unfolds in H5. mytac.
  unfold get in *; simpl in *; rewrite H6 in H5;inverts H5. tryfalse.
  unfolds in H5. unfolds.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto]. 
  mytac. do 3 eexists;eauto.

  unfolds.
  unfolds in H13.
  intros.

  rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
  apply H13 in H16.
  destruct H16.
  left. mytac.
  unfolds in H16. mytac.
  assert (x0 <> x). intro.
  subst x0.
  rewrite EcbMod.set_a_get_a in H16;[ | apply tidspec.eq_beq_true;auto].
  inverts H16. tryfalse.
  rewrite EcbMod.set_a_get_a' in H16;[ | apply tidspec.neq_beq_false;auto].
  exists x0;unfolds.
  do 2 eexists;eauto.

  right.
  simpljoin. splits.
  intro.
  destruct H16.
  mytac. exists x5.
  unfolds.
  assert (x5 <> x). intro.
  subst x.
  unfolds in H16. mytac.
  unfold get in *; simpl in *; rewrite H16 in H6;inverts H6.
  tryfalse.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  unfolds in H16;mytac.
  do 3 eexists;eauto.
  do 2 eexists;eauto.
Qed.

Lemma good_dt_mutexlock_exwt_noret_succ_preserved:
  forall
    (O' O : OSAbstMod.map)
    (O0 Of : OSAbstMod.map)
    (x : addrval)
    (x2 : EcbMod.map)
    (x3 : TcbMod.map)
    (x7 : PtbMod.map)
    (x9 x10 : int32)
    (x15 : list tid)
    (x16 : tid)
    (x20 : susstatus)
    (H10 : join
             (set
                (set
                   (set O0 abtcblsid
                      (abstcblist (set x3 x16 (x10, rdy, Vnull, x20)))) absecblsid
                   (absecblist
                      (set x2 x
                         (absmutexsem x9 (Some (x16, x10)), remove_tid x16 x15))))
                absptlsid (absptls (set x7 x9 Holder))) Of O')
    (H9 : join O0 Of O)
    (H1 : GOOD_DT O)
    (H0 : NO_NEST_PENDING_O O)
    (Hnest : NO_NEST_PENDING_O O')
    (x6 : addrval)
    (x11 x12 : int32)
    (x13 : taskstatus)
    (x14 : msg)
    (x17 : taskstatus)
    (x18 : msg)
    (x19 : susstatus)
    (H2 : get O0 curtid = Some (oscurt x6))
    (H3 : get O0 absecblsid = Some (absecblist x2))
    (H4 : get O0 abtcblsid = Some (abstcblist x3))
    (H5 : get O0 absptlsid = Some (absptls x7))
    (H6 : get x2 x = Some (absmutexsem x9 (Some (x6, x12)), x15))
    (H7 : x15 <> nil)
    (H8 : GetHWait x3 x15 x16)
    (H11 : Int.eq x11 x9 = false)
    (H12 : get x3 x6 = Some (x11, x13, x14, x19))
    (H13 : get x3 x16 = Some (x10, x17, x18, x20)),
    GOOD_DT O'. 
Proof.
  intros.
  assert (get O absecblsid = Some (absecblist x2)) as Hels.
  eapply join_get_get_l;eauto.
  assert (get O abtcblsid = Some (abstcblist x3)) as Htls.
  eapply join_get_get_l;eauto.
  assert (get O curtid = Some (oscurt x6)) as Hcurt.
  eapply join_get_get_l;eauto.
  assert (get O absptlsid = Some (absptls x7)) as Hptls.
  eapply join_get_get_l;eauto.

  assert (O'=set
               (set
                  (set O abtcblsid
                     (abstcblist
                        (set x3 x16 (x10, rdy, Vnull, x20))))
                  absecblsid
                  (absecblist
                     (set x2 x
                        (absmutexsem x9 (Some (x16, x10)),
                          remove_tid x16 x15)))) absptlsid
               (absptls (set x7 x9 Holder))).
  eapply join_get_set_eq_3;eauto.
  clear H2 H3 H4 H5.
  remember O as Ox.
  clear HeqOx.
  subst O'.
  unfold GOOD_DT in *.
  intros.
  unfolds in Hnest.
  lets Hnest': Hnest H H2.
  clear Hnest.
  unfolds in H0.
  lets Hnn: H0 Hels Htls.
  clear H0.

  rewrite abst_set_get_neq in H, H2, H3;auto.
  rewrite OSAbstMod.map_get_set in H4.
  inverts H4.
  rewrite OSAbstMod.map_get_set in H.
  inverts H.
  rewrite abst_set_get_neq in H2, H3;auto.
  rewrite OSAbstMod.map_get_set in H2. inverts H2.
  rewrite abst_set_get_neq in H3;auto.
  lets Hgoodst: H1 Hels Htls H3 Hptls.
  destruct Hgoodst as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6).

  assert(x6 <> x16) as Hneq.
  intro.
  subst x16.
  unfolds in Hnn.
  assert(Hn: TcbMod.get x3 x6 <> None).
  intro.
  unfold get in H12; simpl in H12; rewrite H in H12; inverts H12.
  eapply Hnn with (qid:= x) in Hn.
  mytac.
  destruct H. unfolds. do 4 eexists; split; eauto.
  unfolds in H8.
  mytac; auto.
  unfolds; do 3 eexists; eauto.

  (*rdy_notin_wl*)
  unfold rdy_notin_wl in *.
  simpljoin; splits.
  splits. 
  intros.
  assert (Hr: t = x6 \/ t <> x6) by tauto.
  destruct Hr.
  subst t.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  apply H in H4.
  intro. destruct H4.
  eapply post_iswait;eauto.
  assert (Hr: t = x16 \/ t <> x16) by tauto.
  destruct Hr.
  subst x16.
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.

  eapply nnp_remove_nwait;eauto.
  unfolds;splits;eauto.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  apply H in H4.
  intro.
  destruct H4.
  eapply remove_is_wait_neq;eauto.

  intros.
  assert (Hr: t = x6 \/ t <> x6) by tauto.
  destruct Hr.
  subst t.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  lets Hx:H0 H4.
  unfolds in Hnn.
  assert (TcbMod.get x3 x6 <> None).
  intro.
  rewrite H5 in H4;tryfalse.
  apply Hnn with(qid:=x)in H5.
  destruct H5 as (Hst & Hf).
  destruct Hst.
  unfolds in Hx;mytac;unfolds;do 4 eexists;eauto.
  unfolds;do 3 eexists;eauto.

  assert (t <> x16).
  intro.
  subst x16.
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  apply H0 in H4.
  eapply post_iswait' in H14;eauto.
  destruct H14; eauto.

  intros.
  assert (Hr: t = x6 \/ t <> x6) by tauto.
  destruct Hr.
  subst t.
  assert (IS_WAITING_E x6 eid x2).
  eapply post_iswait';eauto.
  unfolds in Hnn.
  assert (TcbMod.get x3 x6 <> None).
  intro.
  unfold get in *; simpl in *; rewrite H12 in H14;tryfalse.
  apply Hnn with(qid:=x)in H14.
  destruct H14 as (Hst & Hf).
  destruct Hst.
  unfolds in H5;mytac;unfolds;do 4 eexists;eauto.
  unfolds;do 3 eexists;eauto.

  assert (Hr: t = x16 \/ t <> x16) by tauto.
  destruct Hr.
  subst t.
  eapply nnp_remove_nwait in H13; eauto. 
  destruct H13.
  unfolds in H4;mytac.
  unfolds; do 4 eexists; split; eauto.
  unfolds; splits; auto.
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  eapply H2;eauto.
  eapply post_iswait';eauto.

  (*owner_prio_prop*)
  unfold owner_prio_prop in *.
  intros.
  assert (Hr: t = x6 \/ t <> x6 ) by tauto.
  destruct Hr.
  subst t.
  
  assert (eid <> x).
  intro.
  subst x.
  rewrite EcbMod.set_a_get_a in H5;[ | apply tidspec.eq_beq_true;auto].
  inverts H5;tryfalse.

  unfolds in Hnn.
  rewrite EcbMod.set_a_get_a' in H5;[ | apply tidspec.neq_beq_false;auto].
  assert (TcbMod.get x3 x6 <> None).
  intro.
  unfold get in *; simpl in *; rewrite H15 in H12;tryfalse.
  apply Hnn with (qid:=eid) in H15.
  destruct H15 as (Hst & Hf).
  destruct Hf.
  exists x.
  split;auto.
  unfolds;do 3 eexists;eauto.
  unfolds;do 3 eexists;eauto.

  assert (Hr: t <> x16 \/ t = x16) by tauto.
  destruct Hr.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  eapply Hg2; eauto.
  assert (eid <> x).
  intro. subst x.
  rewrite EcbMod.set_a_get_a in H5;[ | apply tidspec.eq_beq_true;auto].
  inverts H4;tryfalse.
  rewrite EcbMod.set_a_get_a' in H5;[ | apply tidspec.neq_beq_false;auto].
  eauto.

  subst x16.
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.

  assert (Hr: eid = x \/ eid <> x ) by tauto.
  destruct Hr.
  subst x.
  rewrite  EcbMod.set_a_get_a in H5;[ | apply tidspec.eq_beq_true;auto].
  inverts H5.
  split;auto.
  unfolds in Hg4.
  assert (IS_WAITING_E t eid x2).
  unfolds.
  do 3 eexists;split;eauto.
  unfolds in H8;mytac;auto.
  apply H2 in H4.
  mytac.
  unfold get in *; simpl in *; rewrite H4 in H13;inverts H13.
  apply Hg4 in H4.
  mytac.
  unfolds in H4.
  mytac.
  rewrite H4 in H6;inverts H6.
  rewrite H5 in H12;inverts H12.
  auto.

  lets Hx:Hg2 H5 H4.
  destruct Hx.
  destruct H6;subst.
  auto.
  clear -H12 H13.
  int auto.
  
  rewrite EcbMod.set_a_get_a' in H5;[ | apply tidspec.neq_beq_false;auto].
  eauto.

  (*task_stat_prop*)
  unfolds.
  intros.
  assert (Hr: t = x6 \/ t <> x6 ) by tauto.
  destruct Hr.
  subst t.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  apply Hg3 in H4;auto.

  assert (Hr: t = x16 \/ t <> x16 ) by tauto.
  destruct Hr.
  subst t.
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4;auto.

  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  apply Hg3 in H4; auto.

  (*wait_prop*)
  unfold wait_prop in *.
  intros.
  assert (Hr: t = x6 \/ t <> x6 ) by tauto.
  destruct Hr.
  subst.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  unfolds in Hnn.
  assert ( TcbMod.get x3 x6 <> None ).
  intro.
  rewrite H4 in H5;tryfalse.
  apply Hnn with (qid:=x) in H5.
  mytac.
  destruct H5. mytac.
  apply H0 in H4.
  unfolds. unfolds in H4. mytac.
  do 4 eexists;split;eauto.
  unfolds;do 3 eexists;eauto.

  assert (Hr: t <> x16 \/ t = x16) by tauto.
  destruct Hr.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  lets Hx:Hg4 H4. mytac.
  
  assert (Hr: x0 = x6 \/ x0 <> x6) by tauto.
  destruct Hr.
  subst x0.
  lets Hy:H0 H4.
  unfolds in Hy.
  mytac.
  unfolds in H15.
  mytac.
  assert (Hr: eid = x \/ eid <> x) by tauto.
  destruct Hr.
  subst x.
  rewrite H19 in H15. inverts H15.
  unfold get in *; simpl in *; rewrite H19 in H6;inverts H6.
  rewrite H16 in H12; inverts H12.
  exists x16 x10 Vnull x20.
  splits.
  unfolds.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;eauto.
  rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  auto.
  unfolds in H8.
  lets Hx: H0 H4.
  unfolds in Hx.
  destruct Hx as (p_q & ow & wl & Heg & Hin).
  rewrite Heg in H19;inverts H19.
  destruct H8 as (Hin1 & Hin2). mytac.
  eapply H8 with (t':=t) in Hin;eauto.
  unfold get in *;simpl in *.
  rewrite H13 in H6;inverts H6.
  mytac.
  rewrite H4 in H6;inverts H6;auto.
  
  intros.
  unfolds in H6.
  apply H18.
  unfolds.
  intro.
  rewrite TcbMod.set_a_get_a' in H6;[ | apply tidspec.neq_beq_false;auto].
  apply H6 in H12.
  destruct H12.
  left.
  mytac.
  unfolds in H12.
  mytac.
  assert (eid <> x).
  intro.
  subst eid.
  rewrite EcbMod.set_a_get_a in H12;[ | apply tidspec.eq_beq_true;auto].
  inverts H12.
  tryfalse.
  rewrite EcbMod.set_a_get_a' in H12;[ | apply tidspec.neq_beq_false;auto].
  exists x;unfolds.
  do 2 eexists;eauto.

  right.
  simpljoin. splits.
  intro.
  destruct H12.
  mytac.
  exists x4.
  unfolds.
  assert (x4 <> eid).
  intro.
  subst x4.
  unfolds in H12.
  mytac.
  rewrite H19 in H12;inverts H12.
  tryfalse.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  unfolds in H12;mytac.
  do 3 eexists;eauto.
  do 2 eexists;eauto.

  rewrite H15 in H19;inverts H19.
  unfolds in Hnn.
  assert (Hn: TcbMod.get x3 x6 <> None).
  intro.
  rewrite H19 in H16;tryfalse.
  apply Hnn with (qid:=eid) in Hn.
  destruct Hn as (Hst & Hf).
  destruct Hf.
  exists x;split;auto.
  unfolds;do 3 eexists;eauto.
  unfolds;do 3 eexists;eauto.

  exists x0.
  assert (x0 <> x16).
  intro.
  subst x0.
  unfolds in Hnn.
  assert (Hn: TcbMod.get x3 x16  <> None).
  intro.
  rewrite H20 in H16;tryfalse.
  apply Hnn with (qid:=eid) in Hn.
  destruct Hn as (Hst & Hn).
  destruct Hst.
  unfolds.
  exists x.
  do 3 eexists;split;eauto.
  unfolds in H8;mytac;auto.
  auto.
  
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;splits;eauto.
  unfolds in H15;unfolds. mytac.
  assert (x <> eid).
  intro. subst x.
  unfold get in *; simpl in *; rewrite H15 in H6;inverts H6;tryfalse.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;eauto.

  intros.
  unfolds in H21.
  assert (x0 <> x16).
  intro.
  subst x0.
  unfolds in Hnn.
  assert (Hn: TcbMod.get x3 x16 <> None).
  intro.
  rewrite H16 in H22;tryfalse.
  apply Hnn with (qid:=eid) in Hn.
  destruct Hn as (Hst & Hf).
  destruct Hst.
  unfolds.
  do 4 eexists;split;eauto.
  unfolds in H8;mytac;auto. auto.
  apply H18.
  unfolds.
  intro.
  rewrite TcbMod.set_a_get_a' in H21;[ | apply tidspec.neq_beq_false;auto].
  apply H21 in H23.
  destruct H23.
  left. mytac.
  unfolds in H23.
  simpljoin.
  assert (x8 <> x).
  intro.
  subst x8.
  rewrite EcbMod.set_a_get_a in H23;[ | apply tidspec.eq_beq_true;auto].
  inverts H23. tryfalse.
  rewrite EcbMod.set_a_get_a' in H23;[ | apply tidspec.neq_beq_false;auto].
  exists x8;unfolds.
  do 2 eexists;eauto.

  right. simpljoin. splits.
  intro.
  destruct H23.
  mytac.
  exists x23.
  unfolds.
  assert (x23 <> x).
  intro. subst x.
  unfolds in H23.
  mytac.
  unfold get in *; simpl in *; rewrite H23 in H6;inverts H6.
  tryfalse.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  unfolds in H23;mytac.
  do 3 eexists;eauto.
  do 2 eexists;eauto.

  subst t.
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.

  (*op_p_prop*)
  unfold op_p_prop in *.
  intros.
  assert (Hr: t = x6 \/ t <> x6) by tauto.
  destruct Hr. subst.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  unfolds in H5.

  assert (TcbMod.get (set x3 x16 (x10, rdy, Vnull,x20)) x6 <> None).
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  intro.
  rewrite H14 in H4;tryfalse.
  apply H5 in H14.
  destruct H14.
  mytac.
  assert (x0 <> x).
  intro.
  subst x0.
  unfolds in H14.
  mytac.
  rewrite EcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
  inverts H14;tryfalse.
  unfolds in H14.
  rewrite EcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
  mytac.

  unfolds in Hnn.
  assert (Hn: TcbMod.get x3 x6 <> None).
  intro.
  rewrite H16 in H4;tryfalse.
  apply Hnn with (qid:=x) in Hn.
  destruct Hn as (Hst & Hf).
  destruct Hf.
  exists x0.
  split;auto.
  unfolds;do 3 eexists;eauto.
  unfolds;do 3 eexists;eauto.
  destruct H14.
  rewrite TcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].

  mytac.
  unfold get in *; simpl in *; rewrite H4 in H15; inverts H15.
  right.
  clear.
  int auto.

  assert (Hr: t <> x16 \/ t = x16) by tauto.
  destruct Hr.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  eapply Hg5;eauto.

  unfolds.
  intro.
  unfolds in H5.
  assert (  TcbMod.get (set x3 x16 (x10, rdy, Vnull, x20)) t <> None).
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  auto.
  apply H5 in H17.
  destruct H17.
  mytac.
  left.
  exists x0.
  assert (x0 <> x).
  intro.
  subst x0.
  unfolds in H17.
  rewrite EcbMod.set_a_get_a in H17;[ | apply tidspec.eq_beq_true;auto].
  mytac.
  inverts H17;tryfalse.
  unfolds in H17.
  mytac.
  rewrite EcbMod.set_a_get_a' in H17;[ | apply tidspec.neq_beq_false;auto].
  unfolds.
  do 2 eexists;eauto.
  right.
  rewrite TcbMod.set_a_get_a' in H17;[ | apply tidspec.neq_beq_false;auto].
  simpljoin. splits.
  intro.
  destruct H17.
  mytac.
  exists x5.
  unfolds in H17.
  mytac.
  unfolds.
  assert (x <> x5).
  intro.
  subst x5.
  unfold get in *; simpl in *; rewrite H17 in H6;inverts H6.
  tryfalse.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;eauto.
  do 2 eexists;eauto.

  subst t.
  rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.
  unfolds in H5.
  assert (TcbMod.get (set x3 x16 (p, rdy, Vnull, sus)) x16 <> None ).
  rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  auto.
  apply H5 in H4.
  destruct H4.
  mytac.
  assert (Hr: x <> x0 \/ x = x0) by tauto.
  destruct Hr.
  unfolds in Hnest'.
  assert (TcbMod.get (set x3 x16 (p, rdy, Vnull, sus)) x16 <> None).
  intro.
  rewrite TcbMod.set_a_get_a in H16;[ | apply tidspec.eq_beq_true;auto].
  tryfalse.
  apply Hnest' with (qid:=x) in H16.
  mytac.
  destruct H17.
  exists x0.
  split;auto.
  unfolds in H4.
  mytac. unfolds.
  do 3 eexists;eauto.
  unfolds.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;eauto.
  subst x0.
  unfolds in H4.
  mytac.
  rewrite EcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.
  right;clear;int auto.

  destruct H4.
  destruct H4.
  exists x.
  unfolds.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;eauto.

  (*no_owner_prio_prop*)
  unfold nowner_prio_prop in *.
  intros.
  assert (Hr: t = x6 \/ t <> x6 ) by tauto.
  destruct Hr.
  subst.
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  unfolds in H14.
  assert (TcbMod.get (set x3 x16 (x10, rdy, Vnull, x20)) x6 <> None).
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  intro.
  rewrite H4 in H15;tryfalse.

  apply H14 in H15.
  destruct H15.
  mytac.
  assert (x0 <> x).
  intro.
  subst x0.
  unfolds in H15.
  mytac.
  rewrite EcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
  inverts H15.
  tryfalse.
  unfolds in H15.
  rewrite EcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
  mytac.

  unfolds in Hnn.
  assert (Hn: TcbMod.get x3 x6 <> None).
  intro.
  rewrite H17 in H4;tryfalse.
  apply Hnn with (qid:=x) in Hn.
  destruct Hn as (Hst & Hf).
  destruct Hf.
  exists x0.
  split;auto.
  unfolds;do 3 eexists;eauto.
  unfolds;do 3 eexists;eauto.
  
  destruct H15.
  rewrite TcbMod.set_a_get_a' in H16;[ | apply tidspec.neq_beq_false;auto].
  mytac.
  rewrite H16 in H4; inverts H4; auto.

  assert (Hr: t = x16 \/ t <> x16) by tauto.
  destruct Hr.
  subst t.
  destruct H5.
  exists x.
  unfolds.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;eauto.

  
  rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  eapply Hg6;eauto.
  intro.
  destruct H5.
  mytac.
  exists x0.
  assert (x0 <> x).
  intro.
  subst x0.
  unfolds in H5.
  mytac.
  unfold get in *; simpl in *; rewrite H5 in H6; inverts H6.
  tryfalse.
  unfolds in H5.
  unfolds.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto]. 
  mytac.
  do 3 eexists;eauto.

  unfolds.
  unfolds in H14.
  intros.

  rewrite TcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
  apply H14 in H17.
  destruct H17.
  left.
  mytac.
  unfolds in H17.
  mytac.
  assert (x0 <> x).
  intro.
  subst x0.
  rewrite EcbMod.set_a_get_a in H17;[ | apply tidspec.eq_beq_true;auto].
  inverts H17.
  tryfalse.
  rewrite EcbMod.set_a_get_a' in H17;[ | apply tidspec.neq_beq_false;auto].
  exists x0;unfolds.
  do 2 eexists;eauto.

  right.
  simpljoin. splits.
  intro.
  destruct H17.
  mytac.
  exists x5.
  unfolds.
  assert (x5 <> x).
  intro.
  subst x.
  unfolds in H17.
  mytac.
  unfold get in *; simpl in *; rewrite H17 in H6; inverts H6.
  tryfalse.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  unfolds in H17;mytac.
  do 3 eexists;eauto.
  do 2 eexists;eauto.
Qed.
    
Lemma mutexunlock_dtinv_preserve:
  forall sc vl cd O cd' O', 
    has_succ (mutexunlock vl) cd ->
    NO_NEST_PENDING_O O ->
    GOOD_DT O ->
    spec_step sc cd O cd' O' -> 
    NO_NEST_PENDING_O O' ->
    GOOD_DT O'.
Proof.
  introv Hhs Hnn Hgd Hsp Hnn'.
  repeat des_vl.
  simpl in Hhs. destruct vl.
  2: { eapply abt_no_succ in Hhs; eauto. subst. inverts Hsp. }

  inverts Hhs.
  inverts Hsp; (auto).

  repeat symexe. 
  repeat symexe. 
  repeat symexe.
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { eapply good_dt_mutexunlock_nowt_ret_succ_preserved; eauto. }
  { eapply good_dt_mutexunlock_nowt_noret_succ_preserved; eauto. }
  { eapply good_dt_mutexlock_exwt_ret_succ_preserved; eauto. }
  { eapply good_dt_mutexlock_exwt_noret_succ_preserved; eauto. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { eapply good_dt_mutexunlock_nowt_ret_succ_preserved; eauto. }
  { eapply good_dt_mutexunlock_nowt_noret_succ_preserved; eauto. }
  { eapply good_dt_mutexlock_exwt_ret_succ_preserved; eauto. }
  { eapply good_dt_mutexlock_exwt_noret_succ_preserved; eauto. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }

Qed. 

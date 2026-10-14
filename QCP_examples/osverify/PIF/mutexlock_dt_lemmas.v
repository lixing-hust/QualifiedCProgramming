
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
Require Import join_lib.


Lemma good_dt_muxpend_get_succ_preserved:
  forall
    (O' O : OSAbstMod.map)
    (O0 Of : OSAbstMod.map)
    (x : addrval)
    (x3 : EcbMod.map)
    (x5 x8 : int32)
    (x9 : addrval)
    (H10 : join (set O0 absecblsid (absecblist (set x3 x (absmutexsem x8 (Some (x9, x5)), nil)))) Of O')
    (H9 : join O0 Of O)
    (H1 : GOOD_DT O)
    (H0 : NO_NEST_PENDING_O O)
    (Hnest : NO_NEST_PENDING_O O')
    (x0 : val)
    (x4 : TcbMod.map)
    (x6 : msg)
    (x7 : susstatus)
    (H2 : get O0 curtid = Some (oscurt x9))
    (H3 : get O0 absecblsid = Some (absecblist x3))
    (H4 : get O0 abtcblsid = Some (abstcblist x4))
    (H5 : get x3 x = Some (absmutexsem x8 None, nil))
    (H6 : get x4 x9 = Some (x5, rdy, x6, x7))
    (H7 : Int.ltu x8 x5 = true),
    GOOD_DT O'. 
Proof.
  intros.
  assert (get O curtid = Some (oscurt x9)) as Hct.
  eapply join_get_get_l;eauto.
  assert (get O absecblsid = Some (absecblist x3)) as Hels.
  eapply join_get_get_l;eauto.
  assert (get O abtcblsid = Some (abstcblist x4)) as Htls.
  eapply join_get_get_l;eauto.
  
  assert (O'= set O absecblsid (absecblist
                                  (set x3 x (absmutexsem x8 (Some (x9, x5)), nil)))).
  eapply join_get_set_eq;eauto.
  clear H2 H3 H4.
  remember O as Ox.
  clear HeqOx.
  subst O'.

  unfolds. intros.
  unfolds in Hnest.
  lets Hnest':Hnest H H2.
  clear Hnest.
  rewrite OSAbstMod.map_get_set in H.
  inverts H.
  rewrite abst_set_get_neq in H2,H3, H4;auto.
  unfold get in *;simpl in *.
  rewrite H2 in Htls;inverts Htls.
  unfolds in H1.
  lets Hgoodst: H1 Hels H2 H3 H4.
  destruct Hgoodst as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6).
  assert (rdy_notin_wl x4 (set x3 x (absmutexsem x8 (Some (x9, x5)), nil))) as Hrdynotintwl.
  {
    unfolds.
    unfolds in Hg1.
    destruct Hg1 as (Hst & Hiswt & Hiswt').
    splits; intros.
    eapply Hst in H.
    intro.
    destruct H.
    unfold ST_WAIT_T in *. mytac.
    assert (Hr: x = x1 \/ x <> x1) by tauto.
    destruct Hr as [He | Hn].
    subst x.
    rewrite EcbMod.set_a_get_a in H.
    2: apply tidspec.eq_beq_true;auto.
    inverts H. tryfalse.
    rewrite EcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto].
    do 4 eexists;splits;eauto.
    
    (*---------------*)
    unfolds; intros.
    apply Hiswt in H.
    unfold IS_WAITING_E in *. mytac.
    assert (Hr: x = eid \/ x <> eid) by tauto.
    destruct Hr as [He | Hn].
    subst x.
    rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    rewrite H5 in H; inverts H. tryfalse.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    do 3 eexists;splits;eauto.
    (*----------------*)
    assert (IS_WAITING_E t eid x3).
    unfold IS_WAITING_E in *.
    mytac.
    assert (Hr: x = eid \/ x <> eid) by tauto.
    destruct Hr as [He | Hn].
    subst x.
    rewrite EcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
    inverts H. tryfalse.
    rewrite EcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto].
    do 3 eexists;splits;eauto.
    eapply Hiswt' in H8;eauto.
  }
  {
    simpljoin. splits.
    (* rdy_notin_wl *)
    auto.

    (*owner_prio_prop*)
    unfold owner_prio_prop in *.
    intros.
    assert (Hr: x = eid \/ x <> eid) by tauto.
    destruct Hr as [He | Hn].
    subst x.
    rewrite EcbMod.set_a_get_a in H8;[ | apply tidspec.eq_beq_true;auto].
    inverts H8.
    rewrite H in H6;inverts H6.
    split;auto.
    rewrite EcbMod.set_a_get_a' in H8;[ | apply tidspec.neq_beq_false;auto].
    eapply Hg2;eauto.

    (*task_stat_prop*)
    auto.

    (*wait_prop*)
    unfold wait_prop in *.
    intros.
    assert (TcbMod.get x4 t = Some (p, wait (os_stat_mutexsem eid) tm, m, sus)) as Ht;auto.
    apply Hg4 in Ht. mytac.
    do 4 eexists;splits;eauto.
    unfold IS_OWNER in *.
    assert (Hr: x = eid \/ x <> eid) by tauto.
    destruct Hr as [He | Hn].
    subst.
    destruct H8 as (p_q & p_owner & wl & Heget).
    rewrite Heget in H5; inverts H5.
    mytac.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    do 3 eexists;eauto.
    assert (Hr: t = x9 \/ t <> x9) by tauto.
    destruct Hr.
    subst t.
    intros.
    eapply H13.
    
    rewrite H in H6;inverts H6.
    intros.
    eapply H13.
    eapply set_neq_getop_eq;eauto.
    intro.
    rewrite H in H16;tryfalse.

    (*op_p_prop*)
    unfold op_p_prop in *.
    intros.
    eapply Hg5;eauto.
    assert (Hr: t = x9 \/ t <> x9) by tauto.
    destruct Hr.
    2: {
      eapply set_neq_getop_eq;eauto.
      intro.
      rewrite H in H12;tryfalse.
    }
    subst t.
    rewrite H in H6;inverts H6.
    lets Hnoowner: no_nest_pending_set_none H H5 Hnest'.
    lets Heq: no_nest_pending_set_prio_eq Hnest' H8 H.
    subst op.
    unfolds. intro.
    right.
    split;auto.
    do 2 eexists;eauto.

    (*no_owner_prio_prop*)      
    unfold nowner_prio_prop in *.
    intros.
    assert (Hr: t = x9 \/ t <> x9 ) by tauto.
    destruct Hr.
    subst t.
    rewrite H in H6; inverts H6.
    eapply no_nest_pending_set_prio_eq;eauto.
    eapply Hg6;eauto.
    intro.
    unfolds in H8. destruct H8.
    mytac;eexists;eapply is_owner_set_other;eauto.
    eapply set_neq_getop_eq;eauto.
    intro.
    rewrite H13 in H;tryfalse.
  }
Qed.

Lemma good_dt_muxpend_blocknolift_preserved:
  forall
    (O' O : OSAbstMod.map)
    (O0 Of : OSAbstMod.map)
    (x : addrval)
    (x3 : option int32)
    (x5 : TcbMod.map)
    (x7 : EcbMod.map)
    (x9 : list addrval)
    (x10 : int32)
    (x11 : tid)
    (x12 x13 : int32)
    (x15 : addrval)
    (x16 : msg)
    (x18 : susstatus)
    (H10 : join
             (set
                (set O0 abtcblsid (abstcblist (set x5 x15 (x13, wait (os_stat_mutexsem x) x3, x16, x18))))
                absecblsid (absecblist (set x7 x (absmutexsem x10 (Some (x11, x12)), x15 :: x9)))) Of O')
    (H9 : join O0 Of O)
    (H1 : GOOD_DT O)
    (H0 : NO_NEST_PENDING_O O)
    (Hnest : NO_NEST_PENDING_O O')
    (x0 : int32)
    (x2 : val)
    (x4 : taskstatus)
    (x14 : int32)
    (x17 : msg)
    (x19 : susstatus)
    (H2 : get O0 curtid = Some (oscurt x15))
    (H3 : get O0 absecblsid = Some (absecblist x7))
    (H4 : get O0 abtcblsid = Some (abstcblist x5))
    (H5 : get x7 x = Some (absmutexsem x10 (Some (x11, x12)), x9))
    (H6 : get x5 x15 = Some (x13, rdy, x16, x18))
    (H7 : get x5 x11 = Some (x14, x4, x17, x19))
    (H8 : ~ (Int.eq x14 x10 = false /\ Int.ltu x13 x12 = true))
    (H11 : Int.ltu x10 x13 = true)
    (H12 : x3 = Some x0 /\ x0 <> Int.zero \/ x3 = None /\ x0 = Int.zero),
    GOOD_DT O'.
Proof.
  intros.
  assert (get O curtid = Some (oscurt x15)) as Hct.
  eapply join_get_get_l;eauto.
  assert (get O absecblsid = Some (absecblist x7)) as Hels.
  eapply join_get_get_l;eauto.
  assert (get O abtcblsid = Some (abstcblist x5)) as Htls.
  eapply join_get_get_l;eauto.

  assert (O' = set (set O abtcblsid
                      (abstcblist
                         (set x5 x15 (x13, wait (os_stat_mutexsem x) x3, x16, x18))))
                 absecblsid
                 (absecblist
                    (set x7 x (absmutexsem x10 (Some (x11, x12)), x15 :: x9)))).
  eapply join_get_set_eq_2;eauto.
  clear H2 H3 H4.
  remember O as Ox.
  clear HeqOx.
  subst O'.

  unfold GOOD_DT in *.
  intros.
  unfolds in Hnest.
  lets Hnest': Hnest H H2.
  clear Hnest.
  rewrite OSAbstMod.map_get_set in H.
  inverts H.
  rewrite abst_set_get_neq in H2, H3, H4;auto.
  rewrite OSAbstMod.map_get_set in H2.
  inverts H2.
  rewrite abst_set_get_neq in H3, H4;auto.
  lets Hgooddt: H1 Hels Htls H3 H4.
  clear H1.
  unfold get in *;simpl in *.
  destruct Hgooddt as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6).
  splits.
  (*rdy_notin_wl*)
  unfold rdy_notin_wl in *.
  simpljoin.  splits.  intros;auto.
  assert (Hr: t = x15 \/ t <> x15) by tauto.
  destruct Hr.
  subst t.
  rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
  inverts H13.
  rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
  apply H in H13.
  intro.
  destruct H13.
  eapply pend_no_lift_iswating;eauto.
  (*----------------------*)
  intros.
  assert (Hr: t = x15 \/ t <> x15) by tauto.
  destruct Hr.
  subst t.
  unfolds.
  rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
  inverts H13.
  do 3 eexists;split;auto.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  auto.
  simpl;auto.
  rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
  apply H1 in H13.
  unfolds in H13.
  unfolds. mytac.
  assert (Hr: x = eid \/ x <> eid) by tauto.
  destruct Hr.
  subst x.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  rewrite H13 in H5.
  inverts H5.
  do 3 eexists;split;auto.
  simpl.
  right;auto.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;split;eauto.

  intros.
  assert (Hr: t = x15 \/ t <> x15) by tauto.
  destruct Hr.
  subst t.
  rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  unfolds in H13.
  assert (Hr: x = eid \/ x <> eid) by tauto.
  destruct Hr.
  subst x.
  rewrite EcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
  mytac.
  do 3 eexists;eauto.
  apply H in H6.
  rewrite EcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
  destruct H6.
  unfolds.
  mytac.
  do 4 eexists;split;eauto.
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  apply H2.
  unfold IS_WAITING_E in *.
  assert (Hr: x = eid \/ x <> eid) by tauto.
  destruct Hr.
  subst x.
  rewrite EcbMod.set_a_get_a in H13; [ | apply tidspec.eq_beq_true;auto].
  mytac.
  inverts H13.
  do 3 eexists;split;eauto.
  simpl in H15.
  destruct H15; auto; tryfalse.
  rewrite EcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
  auto.

  (*owner_prio_prop*)
  unfold owner_prio_prop in *.
  intros.
  assert (Hr: t = x15 \/ t <> x15) by tauto.
  destruct Hr.
  subst t.
  rewrite TcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
  inverts H.
  assert (Hr: x=eid \/ x<>eid) by tauto.
  destruct Hr.
  subst x.
  rewrite EcbMod.set_a_get_a in H1;[ | apply tidspec.eq_beq_true;auto].
  inverts H1.
  rewrite H6 in H7;inverts H7.
  eapply Hg2;eauto.
  rewrite EcbMod.set_a_get_a' in H1;[ | apply tidspec.neq_beq_false;auto].
  eapply Hg2;eauto.

  rewrite TcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto].
  assert (Hr: x=eid \/ x<>eid) by tauto.
  destruct Hr.
  subst x.
  rewrite EcbMod.set_a_get_a in H1;[ | apply tidspec.eq_beq_true;auto].
  inverts H1.
  eapply Hg2;eauto.
  rewrite EcbMod.set_a_get_a' in H1;[ | apply tidspec.neq_beq_false;auto].
  eapply Hg2;eauto.

  (*task_stat_prop*)
  unfold task_stat_prop in *.
  intros.
  assert (Hr: t = x15 \/ t <> x15) by tauto.
  destruct Hr.
  subst t.
  rewrite TcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
  inverts H.
  right.
  do 2 eexists;auto.
  rewrite TcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto].
  eapply Hg3;eauto.

  (*wait_prop*)
  unfold wait_prop in *.
  intros.

  assert (Hr: t=x15 \/ t<>x15) by tauto.
  destruct Hr.
  subst t.
  rewrite TcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
  inverts H.
  exists x11 x14 x17 x19.
  splits.
  unfolds.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;auto.
  assert (Hn: x11 <> x15).
  intro.
  subst x11.
  unfolds in Hnest'.
  assert (TcbMod.get
            (TcbMod.set x5 x15 (p, wait (os_stat_mutexsem eid) tm, m, sus)) x15 <>
            None).
  rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  auto.
  unfold set in *; simpl in *.
  eapply Hnest' with (qid:=eid) in H.
  destruct H as (Hst & Hne).
  destruct Hst.
  unfolds.
  exists eid.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;split;auto.
  simpl;left;auto.
  unfolds.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;auto.
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  assert (Hisow: IS_OWNER x11 eid x7).
  unfolds.
  do 3 eexists;eauto.
  unfolds in H0.
  lets Hxx:H0 Hels Htls.
  unfolds in Hxx.
  assert (TcbMod.get x5 x11 <> None).
  intro.
  rewrite H in H7;tryfalse.
  lets Hx:Hxx H Hisow.
  unfolds in Hg3.
  lets Hy: Hg3 H7.
  destruct Hy;subst;auto.
  (*add*)
  mytac; subst.
  eapply Hg1 in H7; mytac; eauto.
  unfolds in H7.
  mytac.
  false; eapply H2.
  unfolds.
  do 4 eexists; eauto.
  
  eapply Classical_Prop.not_and_or in H8.

  lets Hx: Hg2 H7 H5.
  destruct H8 as [Hr1 | Hr2].
  assert(He: Int.eq x14 x10 = true).
  { clear -Hr1. int auto. }
  clear -H11 He Hx.
  { destruct Hx as ([ He1 | He2] & [ Hltu | He3]);
      subst; int auto. }
  assert(Hf: Int.ltu p x12 = false).
  { clear -Hr2; int auto. }
  clear -H11 Hf Hx.
  { destruct Hx as ([ He1 | He2] & [ Hltu | He3]);
      subst; int auto. }

  intros.
  unfolds in H.
  assert (TcbMod.get
            (TcbMod.set x5 x15 (p, wait (os_stat_mutexsem eid) tm, m, sus)) x15 <>
            None ).
  rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  auto.
  apply H in H1.
  clear H.
  destruct H1.
  destruct H as (qid & Hisow).
  unfolds in Hnest'.
  assert (He: TcbMod.get
                (TcbMod.set x5 x15 (p, wait (os_stat_mutexsem eid) tm, m, sus)) x15 <>
                None).
  rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  auto.

  apply Hnest' with (qid:=qid)in He.
  destruct He as (Hst & How).
  destruct Hst.
  unfolds.
  exists eid.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;split;auto.
  simpl;left;auto.
  unfolds in Hisow.
  unfolds. mytac.
  do 3 eexists;eauto.
  destruct H.
  rewrite TcbMod.set_a_get_a in H1;[ | apply tidspec.eq_beq_true;auto].
  mytac.
  inverts H1. auto.
  (*----------*)
  rewrite TcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto].
  apply Hg4 in H.
  mytac.
  exists x1.
  do 3 eexists;splits;eauto.
  clear -H H5.
  assert (Hr: x = eid \/ x <> eid) by tauto.
  destruct Hr.
  subst x.
  unfold IS_OWNER in *.
  mytac.
  rewrite H in H5;inverts H5.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;auto.
  unfold IS_OWNER in *.
  mytac.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;eauto.

  assert (x1 <> x15).
  intro;subst x1.
  unfolds in Hnest'.
  assert (Hn: TcbMod.get
                (TcbMod.set x5 x15 (x13, wait (os_stat_mutexsem x) x3, x16, x18)) x15 <>
                None).
  rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  auto.
  eapply Hnest' with (qid:=eid) in Hn.
  destruct Hn as (Hst & Hisow).
  destruct Hst.
  unfolds.
  exists x.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;split;auto.
  simpl;left;auto.
  
  clear -H H5.
  assert (Hr: x = eid \/ x <> eid) by tauto.
  destruct Hr.
  subst x.
  unfold IS_OWNER in *.
  mytac.
  rewrite H in H5;inverts H5.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;auto.
  unfold IS_OWNER in *.
  mytac.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;eauto.
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  eauto.

  intros.
  apply H14.
  unfold set in *; simpl in *.
  eapply pend_no_lift_getop with (ct:=x15);eauto.
  
  (*op_p_prop*)
  unfold op_p_prop in *.
  intros.
  assert (Hr: t = x15 \/ t <> x15) by tauto.
  destruct Hr.
  2:{
    rewrite TcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto].
    eapply Hg5;eauto.
    eapply pend_no_lift_getop with (ct:=x15);eauto. }

  subst t.
  rewrite TcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
  inverts H.
  eapply Hg5;eauto.        
  unfolds.

  unfolds in H1.
  rewrite TcbMod.set_a_get_a in H1;[ | apply tidspec.eq_beq_true;auto].
  assert (Some (p, wait (os_stat_mutexsem x) x3, m,sus) <> None) by auto.
  apply H1 in H.
  destruct H.
  intros.
  unfolds in Hnest'.
  assert (TcbMod.get
            (TcbMod.set x5 x15 (p, wait (os_stat_mutexsem x) x3, m, sus)) x15 <>
            None).
  rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  auto.
  destruct H as (qid & Hst).
  eapply Hnest' with (qid:=qid) in H13;eauto.
  destruct H13.
  destruct H.
  unfolds.
  exists x.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto]. 
  do 3 eexists;split;simpl;auto.
  simpl;left;auto.
  unfolds.
  unfolds in Hst.
  mytac.
  do 3 eexists;eauto.
  destruct H.
  mytac.
  inverts H2.
  intros.
  right.
  unfolds in Hnest'.
  assert (TcbMod.get
            (TcbMod.set x5 x15 (op, wait (os_stat_mutexsem x) x3, x6, x8)) x15 <>
            None).
  rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  auto.
  split.
  intro.
  destruct H.
  mytac.
  exists x1.
  unfold IS_OWNER in *.
  mytac.
  assert (Hr: x= x1 \/ x <> x1) by tauto.
  destruct Hr.
  subst x.
  rewrite H in H5;inverts H5.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto]. 
  do 3 eexists;simpl;auto.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto]. 
  do 3 eexists;simpl;eauto.
  do 2 eexists;eauto.
  
  (*nowner_prio_prop*)
  unfold nowner_prio_prop in *.
  intros.
  assert (Hr: t = x15 \/ t <> x15 ) by tauto.
  destruct Hr.
  (*------------*)
  subst t.
  rewrite TcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
  inverts H.
  lets Hx:pend_no_lift_getop H6 H5 H2.
  eapply Hg6;eauto.
  intro.
  mytac.
  unfolds in Hnest'.
  assert (TcbMod.get
            (TcbMod.set x5 x15 (p, wait (os_stat_mutexsem x) x3, m, sus)) x15 <>
            None).
  rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  auto.
  apply Hnest' with (qid:=x1) in H13.
  destruct H13 as (Hst & Hisow). 
  destruct Hst.
  unfolds.
  exists x.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;auto.
  split;auto.
  simpl;left;auto.

  clear -H H5.
  assert (Hr: x = x1 \/ x <> x1) by tauto.
  destruct Hr.
  subst x1.
  unfold IS_OWNER in *.
  mytac.
  rewrite H in H5;inverts H5.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;auto.
  unfold IS_OWNER in *.
  mytac.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;eauto.

  (*-----------------*)
  rewrite TcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto].
  eapply Hg6;eauto.
  intro.
  destruct H1.
  mytac.
  exists x1.

  clear -H1 H5.
  assert (Hr: x = x1 \/ x <> x1) by tauto.
  destruct Hr.
  subst x.
  unfold IS_OWNER in *.
  mytac.
  rewrite H in H5;inverts H5.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;auto.
  unfold IS_OWNER in *.
  mytac.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;eauto.
  eapply pend_no_lift_getop with (ct := x15);eauto. 
Qed.

Lemma good_dt_muxpend_blocklift_preserved: 
  forall
    (O' O : OSAbstMod.map)
    (O0 Of : OSAbstMod.map)
    (x : addrval)
    (x3 : option int32)
    (x4 : TcbMod.map)
    (x7 : EcbMod.map)
    (x9 : list addrval)
    (x10 : int32)
    (x11 : tid)
    (x12 x13 x14 : int32)
    (x15 : addrval)
    (x16 x17 : msg)
    (x18 : PtbMod.map)
    (x20 x21 : susstatus)
    (H10 : join
             (set
                (set
                   (set O0 abtcblsid
                      (abstcblist
                         (set (set x4 x15 (x13, wait (os_stat_mutexsem x) x3, x16, x20)) x11
                            (x10, rdy, x17, x21)))) absecblsid
                   (absecblist (set x7 x (absmutexsem x10 (Some (x11, x12)), x15 :: x9)))) absptlsid
                (absptls (set (set x18 x14 Holder) x10 (Valid_Addr x11)))) Of O')
    (H9 : join O0 Of O)
    (H1 : GOOD_DT O)
    (H0 : NO_NEST_PENDING_O O)
    (Hnest : NO_NEST_PENDING_O O')
    (x0 : int32)
    (x2 : val)
    (H2 : get O0 curtid = Some (oscurt x15))
    (H3 : get O0 absecblsid = Some (absecblist x7))
    (H4 : get O0 abtcblsid = Some (abstcblist x4))
    (H5 : get O0 absptlsid = Some (absptls x18))
    (H6 : get x7 x = Some (absmutexsem x10 (Some (x11, x12)), x9))
    (H7 : get x4 x15 = Some (x13, rdy, x16, x20))
    (H8 : get x4 x11 = Some (x14, rdy, x17, x21))
    (H11 : Int.eq x14 x10 = false)
    (H12 : Int.ltu x13 x12 = true)
    (H13 : Int.ltu x10 x13 = true)
    (H14 : x3 = Some x0 /\ x0 <> Int.zero \/ x3 = None /\ x0 = Int.zero),
    GOOD_DT O'.
Proof.
  intros. 
  assert (get O curtid = Some (oscurt x15)) as Hct.
  eapply join_get_get_l;eauto.
  assert (get O absecblsid = Some (absecblist x7)) as Hels.
  eapply join_get_get_l;eauto.
  assert (get O abtcblsid = Some (abstcblist x4)) as Htls.
  eapply join_get_get_l;eauto.
  assert (get O absptlsid = Some (absptls x18)) as Hpls.
  eapply join_get_get_l;eauto.

  assert (O' = (set (set (set O abtcblsid
                            (abstcblist (set (set x4 x15
                                                (x13, wait (os_stat_mutexsem x) x3, x16, x20)) x11
                                           (x10, rdy, x17, x21)))) absecblsid (absecblist
                                                                                 (set x7 x (absmutexsem x10 (Some (x11, x12)),
                                                                                      x15 :: x9)))) absptlsid (absptls
                                                                                                                 (set (set x18 x14 Holder) x10 (Valid_Addr x11))))).
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
  rewrite OSAbstMod.map_get_set in H4.
  inverts H4.
  rewrite abst_set_get_neq in H, H2, H3;auto.
  rewrite OSAbstMod.map_get_set in H.
  inverts H.
  rewrite abst_set_get_neq in H2, H3;auto.
  rewrite OSAbstMod.map_get_set in H2.
  inverts H2.
  rewrite abst_set_get_neq in H3;auto.
  lets Hgooddt: H1 Hels Htls H3 Hpls.
  clear H1.
  unfold get in *;simpl in *.
  destruct Hgooddt as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6).
  
  { 
    rename x15 into ct.
    assert (x11 <> ct) as Hneq.
    intro Hneq.
    subst x11.
    unfolds in Hnest'.
    assert (Hn: TcbMod.get (set
                              (set x4 ct (x13, wait (os_stat_mutexsem x) x3,
                                   x16, x20)) ct (x10, rdy, x17, x21)) ct <> None).
    rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    auto.
    apply Hnest' with (qid:=x) in Hn.
    destruct Hn as (Hst & Hisow).
    destruct Hst.
    unfolds.
    exists x.
    rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    do 3 eexists;split;auto.
    simpl;left;auto.
    unfolds.
    rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    do 3 eexists;split;auto.
    unfold get in *;simpl in *.
    mytac.

    (*rdy_notin_wl*)
    {
      unfold rdy_notin_wl in *.
      simpljoin; splits. splits; intros;auto.
      (*------------*)
      assert (Hr: t = ct \/ t <> ct) by tauto.
      destruct Hr.
      subst t.
      rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
      rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
      inverts H4.

      assert (Hr: t = x11 \/ t <> x11) by tauto.
      destruct Hr.
      subst t.

      rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
      inverts H4.
      apply H in H8.
      intro.
      destruct H8.
      eapply pend_no_lift_iswating;eauto.

      rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
      rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
      apply H in H4.
      intro.
      destruct H4.
      eapply pend_no_lift_iswating with (ct:=ct);eauto.
      (*----------------------*)
      assert (Hr: t = ct \/ t <> ct) by tauto.
      destruct Hr.
      subst t.
      unfolds.
      rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
      rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
      inverts H4.
      do 3 eexists;split;auto.
      rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
      auto.
      simpl;auto.

      assert (Hr: t = x11 \/ t <> x11) by tauto.
      destruct Hr.
      subst.
      rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
      inverts H4.

      rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
      rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
      apply H1 in H4.
      unfolds in H4.
      unfolds.
      mytac.
      assert (Hr: x = eid \/ x <> eid) by tauto.
      destruct Hr.
      subst x.
      rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
      rewrite H4 in H6.
      inverts H6.
      do 3 eexists;split;auto.
      simpl.
      right;auto.
      rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
      do 3 eexists;split;eauto.
      (*-------------------*)
      assert (Hr: t = ct \/ t <> ct) by tauto.
      destruct Hr.
      subst t.
      rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
      rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
      unfolds in H4.
      assert (Hr: x = eid \/ x <> eid) by tauto.
      destruct Hr.
      subst x.
      rewrite EcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
      mytac.
      do 3 eexists;eauto.
      apply H in H7.
      rewrite EcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
      destruct H7.
      unfolds.
      mytac.
      do 4 eexists;split;eauto.

      assert (Hr: t=x11 \/ t<>x11) by tauto.
      destruct Hr.
      subst.
      rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
      assert (IS_WAITING_E x11 eid x7).
      unfold IS_WAITING_E in *.
      assert (Hr: x = eid \/ x <> eid) by tauto.
      destruct Hr.
      subst x.
      rewrite EcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
      mytac.
      inverts H4.
      do 3 eexists;split;eauto.
      simpl in H15.
      destruct H15;auto;tryfalse.
      rewrite EcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
      auto.
      apply H2 in H15.
      mytac.
      rewrite H8 in H15;inverts H15.

      rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
      rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
      apply H2.
      unfold IS_WAITING_E in *.
      assert (Hr: x = eid \/ x <> eid) by tauto.
      destruct Hr.
      subst x.
      rewrite EcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
      mytac.
      inverts H4.
      do 3 eexists;split;eauto.
      simpl in H16.
      destruct H16;auto;tryfalse.
      rewrite EcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
      auto.

      (*owner_prio_prop*)
      { unfold owner_prio_prop in *.
        intros.
        assert (Hr: t = ct \/ t <> ct) by tauto.
        destruct Hr.
        subst t.
        rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
        inverts H4.
        assert (Hr: x=eid \/ x<>eid) by tauto.
        destruct Hr.
        subst x.
        rewrite EcbMod.set_a_get_a in H5;[ | apply tidspec.eq_beq_true;auto].
        inverts H5.
        rewrite H8 in H7;inverts H7.
        eapply Hg2;eauto.
        rewrite EcbMod.set_a_get_a' in H5;[ | apply tidspec.neq_beq_false;auto].
        eapply Hg2;eauto.

        assert (Hr: t = x11 \/ t <> x11) by tauto.
        destruct Hr.
        subst t.
        rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
        inverts H4.
        assert (Hr: x=eid \/ x<>eid) by tauto.
        destruct Hr.
        subst x.
        rewrite EcbMod.set_a_get_a in H5;[ | apply tidspec.eq_beq_true;auto].
        inverts H5.
        lets Hx: Hg2 H8 H6.
        destruct Hx.
        split;auto.
        rewrite EcbMod.set_a_get_a' in H5;[ | apply tidspec.neq_beq_false;auto].
        unfolds in H0.
        lets Hx:H0 Hels Htls.
        unfolds in Hx.
        assert (How: IS_OWNER x11 eid x7).
        unfolds.
        do 3 eexists;eauto.
        lets Hy:Hx How.
        intro.
        rewrite H16 in H8;tryfalse.
        destruct Hy.
        destruct H17.
        exists x;split;auto.
        unfolds;do 3 eexists;eauto.
        
        rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
        assert (Hr: x=eid \/ x<>eid) by tauto.
        destruct Hr.
        subst x.
        rewrite EcbMod.set_a_get_a in H5;[ | apply tidspec.eq_beq_true;auto].
        inverts H5.
        eapply Hg2;eauto.
        rewrite EcbMod.set_a_get_a' in H5;[ | apply tidspec.neq_beq_false;auto].
        eapply Hg2;eauto. }

      {  (*task_stat_prop*)
        unfold task_stat_prop in *.
        intros.
        assert (Hr: t = ct \/ t <> ct) by tauto.
        destruct Hr.
        subst t.
        rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
        inverts H4.
        right.
        do 2 eexists;auto.

        assert (Hr: t=x11\/t<>x11) by tauto.
        destruct Hr.
        subst t.
        rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
        inverts H4.
        eapply Hg3;eauto.
        
        rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
        eapply Hg3;eauto. }

      {
        (*wait_prop*)
        unfold wait_prop in *.
        intros.
        assert (Hr: t=ct \/ t<>ct) by tauto.
        destruct Hr.
        subst t.
        rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
        inverts H4.
        exists x11 x10 x17 x21.
        splits.
        unfolds.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        auto.

        introv Hget_op.
        unfolds in Hget_op.
        assert (TcbMod.get
                  (TcbMod.set
                     (TcbMod.set x4 ct (p, wait (os_stat_mutexsem eid) tm, m, sus)) x11
                     (x10, rdy, x17, x21)) ct <> None).
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        apply Hget_op in H4.
        clear Hget_op.
        destruct H4.
        destruct H4.
        unfolds in Hnest'.
        assert (Hn: TcbMod.get
                      (TcbMod.set
                         (TcbMod.set x4 ct (p, wait (os_stat_mutexsem eid) tm, m, sus)) x11
                         (x10, rdy, x17, x21)) ct <> None).
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.

        apply Hnest' with (qid:=x)in Hn.
        destruct Hn as (Hst & Hisow).
        destruct Hst.
        unfolds.
        exists eid.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;split;auto.
        simpl;left;auto.
        unfolds in H4.
        unfolds.
        mytac.
        do 3 eexists;eauto.
        destruct H4.
        rewrite TcbMod.set_a_get_a' in H5;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a in H5;[ | apply tidspec.eq_beq_true;auto].
        mytac.
        inverts H5.
        auto.
        (*----------*)
        assert (Hr: t <> x11 \/ t = x11) by tauto.
        destruct Hr.
        rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
        assert (TcbMod.get x4 t = Some (p, wait (os_stat_mutexsem eid) tm, m, sus)) as Hgett.
        auto.
        apply Hg4 in H4.
        mytac.
        
        assert (Hr: x1<>x11 \/ x1 = x11) by tauto.
        destruct Hr as [Hn | He].
        exists x1.
        do 3 eexists;splits;eauto.
        clear -H4 H6.
        assert (Hr: x = eid \/ x <> eid) by tauto.
        destruct Hr.
        subst x.
        unfold IS_OWNER in *.
        simpljoin.
        rewrite H in H6;inverts H6.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        unfold IS_OWNER in *.
        mytac.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;eauto.

        assert ( x1 <> ct).
        intro;subst x1.
        unfolds in Hnest'.
        assert (Hnn: TcbMod.get
                       (TcbMod.set
                          (TcbMod.set x4 ct (x13, wait (os_stat_mutexsem x) x3, x16, x20))
                          x11 (x10, rdy, x17, x21)) ct <> None).
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        eapply Hnest' with (qid:=eid) in Hnn.
        destruct Hnn as (Hst & Hisow).
        destruct Hst.
        unfolds.
        exists x.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;split;auto.
        simpl;left;auto.
        
        clear -H4 H6.
        assert (Hr: x = eid \/ x <> eid) by tauto.
        destruct Hr.
        subst x.
        unfold IS_OWNER in *.
        mytac.
        rewrite H in H6; inverts H6.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        unfold IS_OWNER in *.
        simpljoin.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;eauto.
        
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        eauto.

        intros.
        apply H18.
        eapply pend_lift_getop_t with (ct:=ct);eauto.
        (*--------------*)
        subst x1.
        assert (Hr: x <> eid \/ x = eid) by tauto.
        destruct Hr.
        unfolds in Hnest'.
        assert ( Hn: TcbMod.get (set
                                   (set x4 ct (x13,
                                        wait (os_stat_mutexsem x) x3,
                                        x16, x20)) x11 (x10, rdy, x17, x21)) x11 <> None).

        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        apply Hnest' with (qid:=eid) in Hn.
        destruct Hn as (Hst & Hisow).
        destruct Hisow.
        exists x.
        split;auto.
        unfold IS_OWNER in *.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        mytac;do 3 eexists;auto.
        unfold IS_OWNER in *.
        mytac.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;eauto.
        subst x.
        
        exists x11 x10 x17 x21.
        splits.
        unfolds.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.

        assert (IS_OWNER x11 eid x7).
        unfolds.
        do 3 eexists;eauto.
        auto.
        auto.
        unfolds in H0.
        lets Hxx:H0 Hels Htls.
        unfolds in Hxx.
        assert (TcbMod.get x4 x11 <> None).
        intro.
        rewrite H20 in H8;tryfalse.
        lets Hx:Hxx H20 H4.
        unfolds in Hg3.
        lets Hy: Hg3 H8.
        destruct Hy;simpljoin;subst;auto;tryfalse.
        mytac.

        rewrite H16 in H8;inverts H8.
        unfolds in Hg2.
        lets Hx:Hg2 H16 H6.
        clear -Hx H11 H12 H13 H17.
        destruct Hx as ([He1 | He2 ] & [Hlt | Heq]);
          subst; int auto.

        intros.
        apply H18.
        eapply pend_lift_getop_t with (ct:=ct) (x10:=x11) in H19;eauto.

        (*--------------*)
        subst t.
        rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
        inverts H4. }

      { (*op_p_prop*)
        unfold op_p_prop in *.
        intros.
        assert (Hr: t = ct \/ t <> ct) by tauto.
        destruct Hr.
        2:{
          assert (Hr: t <> x11 \/ t = x11) by tauto.
          destruct Hr.
          rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
          rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
          eapply Hg5;eauto.
          eapply pend_lift_getop_t with (ct:=ct) (x10:=x11);eauto.

          subst t.
          unfolds in H5.
          assert (TcbMod.get
                    (TcbMod.set
                       (TcbMod.set x4 ct (x13, wait (os_stat_mutexsem x) x3, x16, x20)) x11
                       (x10, rdy, x17, x21)) x11 <> None).
          rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
          auto.
          lets Hx: H5 H16.
          clear H5.
          destruct Hx as [Hisow | Hne].
          destruct Hisow.
          assert (Hr: x1 = x \/ x1 <> x) by tauto.
          destruct Hr.
          subst x1.
          unfolds in H5.
          rewrite EcbMod.set_a_get_a in H5;[ | apply tidspec.eq_beq_true;auto].
          mytac.
          inverts H5.
          rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
          inverts H4.
          left.
          clear -H11 H12 H13;int auto.

          unfolds in Hnest'.
          assert (IS_OWNER x11 x1
                    (EcbMod.set x7 x (absmutexsem x10 (Some (x11, x12)), ct :: x9))).
          unfolds.
          unfolds in H5.
          mytac.
          do 3 eexists;eauto.
          lets Hx:Hnest' H16 H18.
          destruct Hx as (Hst & Hn).
          destruct Hn.
          exists x.
          split;auto.
          unfolds.
          rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
          do 3 eexists;auto.

          destruct Hne as (Hisow & Hget).
          destruct Hisow.
          exists x.
          unfolds.
          rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
          do 3 eexists;auto.  }
        (*---------------*)
        subst t.
        rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
        inverts H4.
        eapply Hg5;eauto.        
        unfolds.

        unfolds in H5.
        rewrite TcbMod.set_a_get_a' in H5;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a in H5;[ | apply tidspec.eq_beq_true;auto].
        assert (Some (p, wait (os_stat_mutexsem x) x3, m, sus) <> None) by auto.
        apply H5 in H4.
        destruct H4.
        intros.
        unfolds in Hnest'.
        assert (TcbMod.get
                  (TcbMod.set
                     (TcbMod.set x4 ct (p, wait (os_stat_mutexsem x) x3, m, sus)) x11
                     (x10, rdy, x17, x21)) ct <>
                  None).
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        destruct H4.
        eapply Hnest' with (qid:=x1) in H16;eauto.
        destruct H16 as (Hst & Hisow).
        destruct Hst.
        unfolds.
        exists x.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto]. 
        do 3 eexists;split;simpl;auto.
        simpl;left;auto.
        unfolds.
        unfolds in H4.
        mytac.
        do 3 eexists;eauto.
        destruct H4.
        mytac.
        inverts H15.
        intros.
        right.
        unfolds in Hnest'.
        assert ( TcbMod.get
                   (TcbMod.set
                      (TcbMod.set x4 ct (op, wait (os_stat_mutexsem x) x3, x5, x6))
                      x11 (x10, rdy, x17, x21)) ct <>
                   None).
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        split.
        intro.
        destruct H4.
        mytac.
        exists x1.
        unfold IS_OWNER in *.
        mytac.
        assert (Hr: x= x1 \/ x <> x1) by tauto.
        destruct Hr.
        subst x.
        rewrite H6 in H4;inverts H4.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto]. 
        do 3 eexists;simpl;auto.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto]. 
        do 3 eexists;simpl;eauto.
        do 2 eexists;eauto. }

      { (*nowner_prio_prop*)
        unfold nowner_prio_prop in *.
        intros.
        assert (Hr: t = ct \/ t <> ct ) by tauto.
        destruct Hr.
        (*------------*)
        subst t.
        rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
        inverts H4.

        lets Hx:pend_lift_getop_ct H7 H6 H15;eauto.
        eapply Hg6;eauto.
        intro.
        mytac.
        unfolds in Hnest'.
        assert (Hn: TcbMod.get
                      (TcbMod.set
                         (TcbMod.set x4 ct (p, wait (os_stat_mutexsem x) x3, m, sus)) x11
                         (x10, rdy, x17, x21)) ct <>
                      None).
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        apply Hnest' with (qid:=x1) in Hn.
        destruct Hn as (Hst & Hisow).
        destruct Hst.
        unfolds.
        exists x.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        split;auto.
        simpl;left;auto.

        clear -H4 H6.
        assert (Hr: x = x1 \/ x <> x1) by tauto.
        destruct Hr.
        subst x1.
        unfold IS_OWNER in *.
        mytac.
        rewrite H in H6;inverts H6.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        unfold IS_OWNER in *.
        mytac.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;eauto.

        (*-----------------*)
        assert (Hr: t <> x11 \/ t = x11) by tauto.
        destruct Hr.
        rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
        eapply Hg6;eauto.
        intro.
        destruct H5.
        mytac.
        exists x1.

        clear -H5 H6.
        assert (Hr: x = x1 \/ x <> x1) by tauto.
        destruct Hr.
        subst x.
        unfold IS_OWNER in *.
        mytac.
        rewrite H in H6;inverts H6.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        unfold IS_OWNER in *.
        mytac.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;eauto.
        eapply pend_lift_getop_t with (ct:=ct);eauto.
        
        (*------------------*)
        subst t.
        destruct H5.
        exists x.
        unfolds.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto. 
      }
    }
  }
Qed.

Lemma in_neq_remove_in: forall tid wl t, t <> tid -> In tid wl -> In tid (remove_tid t wl).
Proof.
  intros.
  gen tid t H H0.
  inductions wl; intros.
  simpl in H0; auto.
  simpl in H0.
  destruct H0.
  substs.
  simpl.
  destruct(beq_tid t tid) eqn : eq1.
  apply beq_tid_true_eq in eq1.
  tryfalse.
  simpl; left; auto.
  simpl.
  destruct(beq_tid t a) eqn: eq1.
  apply beq_tid_true_eq in eq1.
  auto.
  simpl.
  right.
  apply IHwl; auto.
Qed.

Lemma good_dt_muxpend_timeouterr_preserved:
  forall
    (O' O : OSAbstMod.map)
    (O0 Of : OSAbstMod.map)
    (x : addrval)
    (x3 : TcbMod.map)
    (x4 : priority)
    (x5 : addrval)
    (x6 : msg)
    (x8 : EcbMod.map)
    (x10 : int32)
    (x11 : owner)
    (x12 : list addrval)
    (H10 : join
             (set (set O0 abtcblsid (abstcblist (set x3 x5 (x4, rdy, x6, false)))) absecblsid
                (absecblist (set x8 x (absmutexsem x10 x11, remove_tid x5 x12)))) Of O')
    (H9 : join O0 Of O)
    (H1 : GOOD_DT O)
    (H0 : NO_NEST_PENDING_O O)
    (Hnest : NO_NEST_PENDING_O O')
    (x0 : int32)
    (x7 : susstatus)
    (H2 : get O0 curtid = Some (oscurt x5))
    (H3 : get O0 abtcblsid = Some (abstcblist x3))
    (H4 : get x3 x5 = Some (x4, wait (os_stat_mutexsem x) (Some Int.zero), x6, x7))
    (H5 : get O0 absecblsid = Some (absecblist x8))
    (H6 : get x8 x = Some (absmutexsem x10 x11, x12))
    (H7 : In x5 x12),
    GOOD_DT O'.
Proof.
  intros. 
  assert (get O curtid = Some (oscurt x5)) as Hct.
  eapply join_get_get_l;eauto.
  assert (get O abtcblsid = Some (abstcblist x3)) as Htcb.
  eapply join_get_get_l;eauto.
  assert (get O absecblsid = Some (absecblist x8)) as Hecb.
  eapply join_get_get_l;eauto.

  assert (O'= set (set O abtcblsid (abstcblist
                                      (set x3 x5 (x4, rdy, x6, false)))) absecblsid
                (absecblist (set x8 x (absmutexsem x10 x11, remove_tid x5 x12)))).
  eapply join_get_set_eq_2;eauto.
  clear H2 H3 H5.
  remember O as Ox.
  clear HeqOx.
  subst O'.

  unfolds; intros.
  unfolds in Hnest.
  lets Hnest': Hnest H H2.
  clear Hnest.

  rewrite OSAbstMod.map_get_set in H.
  inverts H.
  rewrite abst_set_get_neq in H2, H3, H5;auto.
  rewrite OSAbstMod.map_get_set in H2.
  inverts H2.
  rewrite abst_set_get_neq in H3, H5;auto.
  lets Hgooddt: H1 Hecb Htcb H3 H5.
  clear H1.
  unfold get in *;simpl in *.
  destruct Hgooddt as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6).
  rename x5 into ct.
  splits; eauto.

  { (*rdy_notin_wl*)
    destruct Hg1 as (Hg11 & Hg12 & Hg13).
    unfold rdy_notin_wl in *.
    simpljoin.  splits. intros;auto.
    (*------------*)
    assert (Hr: t = ct \/ t <> ct) by tauto.
    destruct Hr.
    subst t.
    rewrite TcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
    inverts H. 
    eapply remove_wait; eauto.
    unfolds; mytac; auto.

    rewrite TcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto].
    eapply Hg11 in H; eauto.
    eapply remove_is_wait_neq'; eauto.

    (*IS_WAITING_E*)
    intros.
    destruct (tidspec.beq t ct) eqn : eq1.
    pose proof tidspec.beq_true_eq _ _ eq1; substs.
    rewrite TcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
    inverts H.
    rewrite TcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto].
    eapply Hg12 in H; eauto.
    destruct (tidspec.beq x eid) eqn: eq2.
    pose proof tidspec.beq_true_eq _ _ eq2; substs.
    unfolds.
    rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    do 3 eexists; split; eauto.
    unfolds in H.
    mytac.
    rewrite H6 in H; inverts H.
    eapply in_neq_remove_in; auto.
    eapply tidspec.beq_false_neq in eq1; auto.
    unfolds.
    rewrite EcbMod.set_a_get_a' ; [ | apply tidspec.neq_beq_false;auto].
    unfolds in H; mytac.
    do 3 eexists; eauto.
    eapply tidspec.beq_false_neq in eq2; auto.
    eapply tidspec.beq_false_neq in eq1; auto.

    intros.
    destruct (tidspec.beq x eid) eqn : eq1.
    unfolds in H.
    pose proof tidspec.beq_true_eq _ _ eq1; substs. mytac.
    
    rewrite EcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
    inverts H.
    destruct (tidspec.beq t ct) eqn : eq2.
    pose proof tidspec.beq_true_eq _ _ eq2; substs. 
    eapply In_remove_tid_false in H1; tryfalse.
    rewrite TcbMod.set_a_get_a' ; [ | apply tidspec.neq_beq_false;auto].
    eapply Hg13; eauto.
    unfolds.
    do 3 eexists; splits; eauto.
    eapply In_remove_tid; eauto.
    eapply tidspec.beq_false_neq in eq2; auto.
    
    unfolds in H.
    rewrite EcbMod.set_a_get_a' in H; [ | apply tidspec.neq_beq_false;auto].
    destruct (tidspec.beq t ct) eqn: eq2.
    pose proof tidspec.beq_true_eq _ _ eq2; substs.
    eapply Hg13 in H; auto.
    mytac.
    rewrite H4 in H; inverts H.
    rewrite TcbMod.beq_refl in eq1; tryfalse.
    rewrite TcbMod.set_a_get_a'; [ | apply tidspec.neq_beq_false;auto].
    eapply Hg13 in H; auto.
    mytac. 
    eapply tidspec.beq_false_neq in eq2; auto.
    eapply tidspec.beq_false_neq in eq1; auto.
  }

  { (*owner_prio_prop*)
    unfold owner_prio_prop in *.
    intros.
    destruct (tidspec.beq t ct) eqn : eq1.
    pose proof tidspec.beq_true_eq _ _ eq1; substs. 
    rewrite TcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
    inverts H.
    destruct (tidspec.beq x eid) eqn : eq2.
    pose proof tidspec.beq_true_eq _ _ eq2; substs. 
    rewrite EcbMod.set_a_get_a in H1;[ | apply tidspec.eq_beq_true;auto].
    inverts H1.
    destruct Hg1 as (Hrdy & Hiswt & Htwt).
    eapply Hg2; eauto.
    rewrite EcbMod.set_a_get_a' in H1; [ | apply tidspec.neq_beq_false;auto].
    eapply Hg2; eauto.
    eapply tidspec.beq_false_neq in eq2; auto.
    rewrite TcbMod.set_a_get_a' in H; [ | apply tidspec.neq_beq_false;auto].
    destruct (tidspec.beq x eid) eqn : eq2.
    pose proof tidspec.beq_true_eq _ _ eq2; substs. 
    rewrite EcbMod.set_a_get_a in H1;[ | apply tidspec.eq_beq_true;auto].
    inverts H1.
    eapply Hg2; eauto.
    rewrite EcbMod.set_a_get_a' in H1; [ | apply tidspec.neq_beq_false;auto].
    eapply Hg2; eauto.
    eapply tidspec.beq_false_neq in eq2; auto.
    eapply tidspec.beq_false_neq in eq1; auto.
  }

  { (*task_stat_prop*)
    unfolds; intros.
    destruct (tidspec.beq t ct) eqn : eq1.
    pose proof tidspec.beq_true_eq _ _ eq1; substs. 
    rewrite TcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
    inverts H. auto.
    rewrite TcbMod.set_a_get_a' in H; [ | apply tidspec.neq_beq_false;auto].
    eapply Hg3; eauto.
    eapply tidspec.beq_false_neq in eq1; auto.
  }

  3:{ (*nowner_prio_prop*)
    unfold nowner_prio_prop in *; intros.
    assert (Hr: t = ct \/ t <> ct ) by tauto.
    destruct Hr. subst.
    rewrite TcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
    inverts H.
    unfolds in H2.
    assert (TcbMod.get (set x3 ct (p, rdy, m, false)) ct <> None).
    rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    auto.
    apply H2 in H.

    destruct H. mytac.
    clear - H H1.
    unfold IS_NOT_OWNER in H1.
    unfold IS_OWNER_P in *.
    unfold IS_OWNER in *.
    mytac.
    false.
    eapply H1.
    exists x1; do 3 eexists; eauto.

    destruct H.
    rewrite TcbMod.set_a_get_a in H8;[ | apply tidspec.eq_beq_true;auto]. 
    mytac.
    inverts H8. auto.

    rewrite TcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto].
    eapply Hg6;eauto.
    intro. 
    eapply H1. mytac.
    exists x1.
    assert (x1 <> x).
    intro. subst x1.
    unfolds in H11.
    mytac.
    unfold get in *; simpl in *. rewrite H6 in H11; inverts H11; tryfalse.
    eapply H1; eauto.
    clear -H6.
    unfold IS_OWNER.
    exists x.
    rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto]. 
    do 3 eexists. eauto.

    unfolds.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto]. 
    unfold IS_OWNER in H11. mytac.
    do 3 eexists;eauto.
    eapply pend_timeout_get_opt;eauto.
  }

  2:{ (*op_p_prop*)
    unfold op_p_prop in *. intros.
    destruct (tidspec.beq t ct) eqn : eq1.
    pose proof tidspec.beq_true_eq _ _ eq1; substs. 
    rewrite TcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
    inverts H.
    (* unfold GET_ORP in *. *)
    unfold GET_ORP in *.
    rewrite TcbMod.set_a_get_a in H1;[ | apply tidspec.eq_beq_true;auto].
    destruct H1; auto.
    unfold IS_OWNER_P in *.
    mytac.
    assert(Hr: x = x1 \/ x <> x1) by tauto.
    destruct Hr; subst.
    rewrite EcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
    inverts H.
    eapply Hg5; eauto.
    rewrite EcbMod.set_a_get_a' in H; [ | apply tidspec.neq_beq_false;auto].
    eapply Hg5; eauto.
    mytac. inverts H1; right. rewrite Int.eq_true. eauto.

    rewrite TcbMod.set_a_get_a' in H; [ | apply tidspec.neq_beq_false;auto].
    assert(Hn:TcbMod.get (set x3 ct (x4, rdy, x6, false)) t <> None).
    rewrite TcbMod.set_a_get_a'; [ | apply tidspec.neq_beq_false;auto].
    rewrite H; auto.
    eapply tidspec.beq_false_neq in eq1; auto.
    eapply H1 in Hn; eauto.
    eapply Hg5; eauto.
    eapply pend_timeout_get_opt; eauto.
    eapply tidspec.beq_false_neq in eq1; auto.
    eapply tidspec.beq_false_neq in eq1; auto.
  }

  { (*wait_prop*)
    unfolds; intros.
    destruct (tidspec.beq t ct) eqn : eq1.
    pose proof tidspec.beq_true_eq _ _ eq1; substs. 
    rewrite TcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
    inverts H. 
    rewrite TcbMod.set_a_get_a' in H; [ | apply tidspec.neq_beq_false;auto].
    unfold wait_prop in Hg4.
    lets Hgt: H.
    eapply Hg4 in H; eauto.
    destruct H as (t' & po & m' & sus' & Hispw & Hget & Hpr & Hget_op).
    exists t' po m' sus'.
    splits; eauto.
    destruct (tidspec.beq x eid) eqn : eq2.
    pose proof tidspec.beq_true_eq _ _ eq2; substs.
    unfold IS_OWNER in *. mytac.
    rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    rewrite H6 in H; inverts H.
    do 3 eexists;  eauto.
    unfold IS_OWNER in *. mytac.
    rewrite EcbMod.set_a_get_a'; [ | apply tidspec.neq_beq_false;auto].
    do 3 eexists; eauto.
    eapply tidspec.beq_false_neq in eq2; auto.
    
    destruct (tidspec.beq t' ct) eqn : eq3.
    pose proof tidspec.beq_true_eq _ _ eq3; substs. 
    rewrite H4 in Hget; inverts Hget.
    rewrite TcbMod.set_a_get_a'; [ | apply tidspec.neq_beq_false;auto]; eauto.
    eapply tidspec.beq_false_neq in eq3; auto.

    introv Hgop.
    (*     eapply Hget_op.
    unfold GET_ORP in *. 
    intros. *)
    assert (Hn: TcbMod.get (set x3 ct (x4, rdy, x6, false)) t <> None).
    rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    rewrite Hgt; auto.
    eapply tidspec.beq_false_neq in eq1; auto.
    eapply Hgop in Hn.
    destruct Hn as [Hisow | Hnow].
    unfold IS_OWNER_P in *. mytac.
    destruct (tidspec.beq x x1) eqn : eq2.
    rewrite EcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto].
    inverts H.
    eapply tidspec.beq_true_eq in eq2.
    subst x1.
    (*exists qid, IS_OWNER_P t qid x7 op*)
    eapply Hget_op; eauto.
    eapply pend_timeout_get_opt; eauto.
    eapply tidspec.beq_false_neq in eq1; auto.
    eapply tidspec.beq_true_eq in eq2; eauto.

    rewrite EcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto].
    eapply Hget_op; eauto.
    unfolds.
    intros.
    unfolds in Hgop.
    assert (Hn:TcbMod.get (set x3 ct (x4, rdy, x6, false)) t <> None).
    rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    auto. 

    eapply tidspec.beq_false_neq in eq1; auto.
    eapply Hgop in Hn; eauto.
    destruct Hn as [Hisow | Hnow].
    mytac.
    
    left. 
    assert(Hr: x = x9 \/ x <> x9) by tauto.
    destruct Hr. subst.
    exists x1; do 2 eexists; eauto.
    unfolds in H2.
    rewrite EcbMod.set_a_get_a' in H2;[ | apply tidspec.neq_beq_false;auto].
    mytac; do 3 eexists; eauto.
    
    right.
    destruct Hnow as (Hnow & Hst).
    rewrite TcbMod.set_a_get_a' in Hst;[ | apply tidspec.neq_beq_false;auto]. 
    splits; eauto.
    unfold IS_OWNER in *.
    intro; eapply Hnow.
    mytac.
    assert(Hr: x = x9 \/ x <> x9) by tauto.
    destruct Hr.
    mytac.
    exists x9.
    rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    rewrite H6 in H2; inverts H2.
    eauto.
    exists x9.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    eauto.
    eapply tidspec.beq_false_neq in eq1; auto.
    eapply tidspec.beq_false_neq in eq2; auto.

    eapply Hget_op; eauto.
    eapply pend_timeout_get_opt; eauto.
    eapply tidspec.beq_false_neq in eq1; auto.
    eapply tidspec.beq_false_neq in eq1; auto.
  }
Qed.

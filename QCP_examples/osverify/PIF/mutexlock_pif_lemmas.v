
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

Require Import protect. 
Require Import join_lib.

Require Import int_auto. 

Lemma pif_mutexpend_get_succ:
  forall
    (O O' : OSAbstMod.map)
    (O0 Of : osabst)
    (x : addrval)
    (x3 : EcbMod.map)
    (x5 x8 : int32)
    (x9 : addrval)
    (H7 : join
            (set O0 absecblsid
               (absecblist (set x3 x (absmutexsem x8 (Some (x9, x5)), nil)))) Of O')
    (H6 : join O0 Of O)
    (Hnonesto : NO_NEST_PENDING_O O)
    (Hnonesto' : NO_NEST_PENDING_O O')
    (Hgooddt : GOOD_DT O)
    (Hpif : PIF O)
    (x0 : val)
    (x4 : TcbMod.map)
    (x6 : msg)
    (x7 : susstatus)
    (H0 : get O0 curtid = Some (oscurt x9))
    (H1 : get O0 absecblsid = Some (absecblist x3))
    (H2 : get O0 abtcblsid = Some (abstcblist x4))
    (H3 : get x3 x = Some (absmutexsem x8 None, nil))
    (H4 : get x4 x9 = Some (x5, rdy, x6, x7))
    (H5 : Int.ltu x8 x5 = true),
    PIF O'. 
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
  clear H0 H1 H2.
  remember O as Ox.
  clear HeqOx.
  subst O'.

  unfolds. intros.
  rewrite OSAbstMod.map_get_set in H.
  inverts H.
  rewrite abst_set_get_neq in H0, H1, H2, H8;auto.
  unfold get in *;simpl in *.
  destruct H11.
  rewrite Hct in H1; inverts H1.
  
  exists x.
  unfolds.
  do 3 eexists.
  rewrite EcbMod.set_a_get_a. auto.
  apply tidspec.eq_beq_true;auto.
Qed.

Lemma pif_mutexpend_block_nolift:
  forall
    (O O' : OSAbstMod.map)
    (* (Hgooddt' : GOOD_DT O') *)
    (O0 Of : osabst)
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
    (H7 : join
            (set
               (set O0 abtcblsid
                  (abstcblist
                     (set x5 x15 (x13, wait (os_stat_mutexsem x) x3, x16, x18))))
               absecblsid
               (absecblist
                  (set x7 x (absmutexsem x10 (Some (x11, x12)), x15 :: x9)))) Of O')
    (H6 : join O0 Of O)
    (Hnonesto : NO_NEST_PENDING_O O)
    (Hnonesto' : NO_NEST_PENDING_O O')
    (Hgooddt : GOOD_DT O)
    (Hpif : PIF O)
    (x0 : int32)
    (x2 : val)
    (x4 : taskstatus)
    (x14 : int32)
    (x17 : msg)
    (x19 : susstatus)
    (H0 : get O0 curtid = Some (oscurt x15))
    (H1 : get O0 absecblsid = Some (absecblist x7))
    (H2 : get O0 abtcblsid = Some (abstcblist x5))
    (H3 : get x7 x = Some (absmutexsem x10 (Some (x11, x12)), x9))
    (H4 : get x5 x15 = Some (x13, rdy, x16, x18))
    (H5 : get x5 x11 = Some (x14, x4, x17, x19))
    (H8 : ~ (Int.eq x14 x10 = false /\ Int.ltu x13 x12 = true))
    (H9 : Int.ltu x10 x13 = true)
    (H10 : x3 = Some x0 /\ x0 <> Int.zero \/ x3 = None /\ x0 = Int.zero),
    PIF O'.
Proof.
  intros.
  assert (get O curtid = Some (oscurt x15)) as Hct.
  eapply join_get_get_l;eauto.
  assert (get O absecblsid = Some (absecblist x7)) as Hels.
  eapply join_get_get_l;eauto.
  assert (get O abtcblsid = Some (abstcblist x5)) as Htls.
  eapply join_get_get_l;eauto.

  assert (O' = (set (set O abtcblsid (abstcblist
                                        (set x5 x15 (x13, wait (os_stat_mutexsem x) x3,
                                             x16, x18)))) absecblsid (absecblist (set x7 x
                                                                                    (absmutexsem x10 (Some (x11, x12)), x15 :: x9))))).
  eapply join_get_set_eq_2;eauto.
  clear H0 H1 H2.
  remember O as Ox.
  clear HeqOx.
  subst O'.
  unfold PIF.  intros.
  rewrite OSAbstMod.map_get_set in H; inverts H.
  rewrite abst_set_get_neq in H0, H1, H2, H11; auto.
  rewrite OSAbstMod.map_get_set in H0; inverts H0.
  rewrite abst_set_get_neq in H1, H2, H11;auto.
  unfold get in *; simpl in *.
  rewrite H1 in Hct; inverts Hct.
  unfolds in H13.
  mytac.
  
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply tidspec.eq_beq_true;auto.    
Qed.

Lemma pif_mutexpend_blocklift:
  forall 
    (O O' : OSAbstMod.map)
    (* Hgooddt' : GOOD_DT O' *)
    (O0 Of : osabst)
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
    (H7 : join
            (set
               (set
                  (set O0 abtcblsid
                     (abstcblist
                        (set
                           (set x4 x15
                              (x13, wait (os_stat_mutexsem x) x3, x16, x20)) x11
                           (x10, rdy, x17, x21)))) absecblsid
                  (absecblist
                     (set x7 x (absmutexsem x10 (Some (x11, x12)), x15 :: x9))))
               absptlsid (absptls (set (set x18 x14 Holder) x10 (Valid_Addr x11))))
            Of O')
    (H6 : join O0 Of O)
    (Hnonesto : NO_NEST_PENDING_O O)
    (Hnonesto' : NO_NEST_PENDING_O O')
    (Hgooddt : GOOD_DT O)
    (Hpif : PIF O)
    (x0 : int32)
    (x2 : val)
    (H0 : get O0 curtid = Some (oscurt x15))
    (H1 : get O0 absecblsid = Some (absecblist x7))
    (H2 : get O0 abtcblsid = Some (abstcblist x4))
    (H3 : get O0 absptlsid = Some (absptls x18))
    (H4 : get x7 x = Some (absmutexsem x10 (Some (x11, x12)), x9))
    (H5 : get x4 x15 = Some (x13, rdy, x16, x20))
    (H8 : get x4 x11 = Some (x14, rdy, x17, x21))
    (H9 : Int.eq x14 x10 = false)
    (H10 : Int.ltu x13 x12 = true)
    (H11 : Int.ltu x10 x13 = true)
    (H12 : x3 = Some x0 /\ x0 <> Int.zero \/ x3 = None /\ x0 = Int.zero),
    PIF O'. 
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

  assert (O' = (set (set (set O abtcblsid (abstcblist
                                             (set (set x4 x15 (x13, wait (os_stat_mutexsem x) x3, x16, x20))
                                                x11 (x10, rdy, x17, x21)))) absecblsid
                       (absecblist (set x7 x
                                      (absmutexsem x10 (Some (x11, x12)), x15 :: x9))))
                  absptlsid (absptls (set (set x18 x14 Holder) x10 (Valid_Addr x11))))).
  eapply join_get_set_eq_3;eauto.
  clear H0 H1 H2 H3.
  remember O as Ox.
  clear HeqOx.
  subst O'.

  unfold get in *;simpl in *.
  unfold PIF in *.
  intros.
  lets Hnest': Hnonesto' H H0.
  rewrite OSAbstMod.map_get_set in H3.
  inverts H3.
  rewrite abst_set_get_neq in H, H0, H1, H2;auto.
  rewrite OSAbstMod.map_get_set in H.
  inverts H.
  rewrite abst_set_get_neq in H0, H1, H2;auto.
  rewrite OSAbstMod.map_get_set in H0.
  inverts H0.
  rewrite abst_set_get_neq in H1, H2;auto.
  rewrite H1 in Hct; inverts Hct.
  rename x15 into ct.
  unfolds in H14.
  mytac.
  assert (Hr: x11 = ct \/ x11 <> ct) by tauto.
  destruct Hr; try subst x11.

  unfolds in Hnest'.
  assert (Hn: TcbMod.get (set
                            (set x4 ct (x13, wait (os_stat_mutexsem x) x3, x16, x20))
                            ct (x10, rdy, x17, x21)) ct <> None).
  intro.
  unfold set in *;simpl in *.
  rewrite H3 in H;tryfalse.
  unfolds in H13.
  
  eapply Hnest' with (qid:= x) in Hn.
  destruct Hn as (Hnwt & Hnow).
  destruct Hnwt.
  unfolds.
  do 4 eexists.
  split.
  rewrite EcbMod.set_a_get_a;eauto.
  apply tidspec.eq_beq_true;auto.
  simpl;auto.
  unfolds.
  do 3 eexists.
  rewrite EcbMod.set_a_get_a;eauto.
  apply tidspec.eq_beq_true;auto.
  
  rewrite TcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto].
  rewrite TcbMod.set_a_get_a in H.
  inverts H.
  apply tidspec.eq_beq_true;auto.
Qed.

Lemma pif_mutexpend_timeout_err:
  forall
    (O O' : OSAbstMod.map)
    (O0 Of : osabst)
    (x : addrval)
    (x3 : TcbMod.map)
    (x4 : priority)
    (x5 : addrval)
    (x6 : msg)
    (x8 : EcbMod.map)
    (x10 : int32)
    (x11 : owner)
    (x12 : list addrval)
    (H7 : join
            (set (set O0 abtcblsid (abstcblist (set x3 x5 (x4, rdy, x6, false))))
               absecblsid
               (absecblist (set x8 x (absmutexsem x10 x11, remove_tid x5 x12)))) Of
            O')
    (H6 : join O0 Of O)
    (Hnonesto : NO_NEST_PENDING_O O)
    (Hnonesto' : NO_NEST_PENDING_O O')
    (Hgooddt : GOOD_DT O)
    (Hpif : PIF O)
    (Hgooddt' : GOOD_DT O')
    (x0 : int32)
    (x7 : susstatus)
    (H0 : get O0 curtid = Some (oscurt x5))
    (H1 : get O0 abtcblsid = Some (abstcblist x3))
    (H2 : get x3 x5 = Some (x4, wait (os_stat_mutexsem x) (Some Int.zero), x6, x7))
    (H3 : get O0 absecblsid = Some (absecblist x8))
    (H4 : get x8 x = Some (absmutexsem x10 x11, x12))
    (H5 : In x5 x12), 
    PIF O'.  
Proof.
  intros.
  assert (get O curtid = Some (oscurt x5)) as Hct.
  eapply join_get_get_l;eauto.
  assert (get O abtcblsid = Some (abstcblist x3)) as Htcb.
  eapply join_get_get_l;eauto.
  assert (get O absecblsid = Some (absecblist x8)) as Hecb.
  eapply join_get_get_l;eauto.

  assert (O'= set (set O abtcblsid (abstcblist (set x3 x5 (x4, rdy, x6, false))))
                absecblsid (absecblist
                              (set x8 x (absmutexsem x10 x11, remove_tid x5 x12)))).
  eapply join_get_set_eq_2;eauto.
  clear H0 H1 H3.
  remember O as Ox.
  clear HeqOx.
  subst O'.

  unfolds; intros.
  rewrite OSAbstMod.map_get_set in H.
  inverts H.
  rewrite abst_set_get_neq in H0, H1, H3, H8;auto.
  rewrite OSAbstMod.map_get_set in H0.
  inverts H0.
  rewrite abst_set_get_neq in H1, H3, H8;auto.
  unfold get in *;simpl in *.
  assert (HighestRdy (set x3 x5 (x4, rdy, x6, false)) ct) as Hhighest by auto.
  unfolds in H10. mytac.
  unfolds in Hgooddt'.
  rewrite OSAbstMod.map_get_set in Hgooddt'.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite OSAbstMod.map_get_set in Hgooddt'.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite abst_set_get_neq in Hgooddt';auto.

  assert (He:
           Some (absecblist
                   (set x8 x (absmutexsem x10 x11, remove_tid x5 x12))) =
             Some (absecblist
                     (set x8 x (absmutexsem x10 x11, remove_tid x5 x12)))) by auto.
  assert(He1:
          Some (abstcblist (set x3 x5 (x4, rdy, x6, false)))
          = Some (abstcblist (set x3 x5 (x4, rdy, x6, false)))) by auto.
  lets Hgoodstx:Hgooddt' He He1 H3 H8.
  rewrite Hct in H1; inverts H1.
  clear Hgooddt' He He1.
  destruct Hgoodstx as (Hrdy&Howp&Htkp&Hwtp&Hopp&Hnoowp).
  unfolds in Htkp.
  assert (exists p st m sus, TcbMod.get (set x3 ct (x4, rdy, x6, false)) t= Some (p,st,m,sus)).
  remember (TcbMod.get (set x3 ct (x4, rdy, x6, false)) t) as X;destruct X;tryfalse.
  destruct b. destruct p. destruct p.
  do 3 eexists;eauto.
  destruct H1;auto. mytac.

  assert (TcbMod.get x3 t = Some (x5, x13, x14, x15)).
  rewrite TcbMod.set_a_get_a' in H1;[ | apply tidspec.neq_beq_false;auto];auto.
  lets Htaskstp':Htkp H1.
  unfold set in *; simpl in *.

  destruct Htaskstp' as [Hrdy' | Hwt]; subst.
  eapply H0 in H1; eauto.
  unfolds in Hopp.

  assert(Hst: TcbMod.get (TcbMod.set x3 ct (x4, rdy, x6, false)) t =
                Some (x5, rdy, x14, x15)).
  { rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto];auto. }
  eapply Hopp in Hst; eauto.
  unfolds in Hnoowp.
  lets Hct': H2.
  unfolds in Hwtp.
  assert(Hn: TcbMod.get (TcbMod.set x3 ct (x4, rdy, x6, false)) ct =
               Some (x4, rdy, x6, false)).
  rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto];auto.
  eapply Hopp in Hn; eauto.
  rewrite TcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto];auto.
  inverts H.

  assert(x1 = p_ct).
  {
    clear -H2 H4 H5 H11 H9 H12 Hrdy Hnoowp H10 Hct'.
    assert(Hn: TcbMod.get (TcbMod.set x3 ct (x1, rdy, x2, false)) ct =
                 Some (x1, rdy, x2, false)).
    rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto];auto.
    eapply Hnoowp in Hn; eauto.
  }
  subst.
  clear -H1 Hst Hn.
  destruct Hn; int auto. 
  
  mytac.
  unfolds in Hnoowp.
  lets Hct': H2.
  unfolds in Hwtp.
  assert(x4 = p_ct).
  {
    clear -H2 H4 H5 H11 H9 H12 Hrdy Hnoowp H10 Hct'.
    assert(Hn: TcbMod.get (TcbMod.set x3 ct (x4, rdy, x6, false)) ct =
                 Some (x4, rdy, x6, false)).
    rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto];auto.
    eapply Hnoowp in Hn; eauto.
  }
  lets Htt: H14.

  assert(p_t = x5).
  {
    eapply Hwtp in H1; eauto.
    mytac.
  }

  lets Hx:Hwtp H1. mytac.
  rewrite TcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto];auto.
  inverts H.
  unfolds in Howp.
  unfolds in H18; mytac.
  assert(Hr: ct = x13 \/ ct <> x13) by tauto.
  destruct Hr; subst.
  rewrite TcbMod.set_a_get_a in H19;[ | apply tidspec.eq_beq_true;auto];auto.
  inverts H19.
  unfolds in H11.
  false.
  eapply H11.
  unfold IS_OWNER.
  do 4 eexists; eauto.
  eapply H0 in H19; eauto. 
  clear -H19 H20. int auto. 
Qed.


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
Require Import Integers.
Open Scope int_scope.
Require Import int_auto. 

Require Import PIF_LibTactics.
Require Import PIF_os_ucos_h.

Require Import aux_lemmas.
Require Import mux_succ_gen. 
Require Import pif_lemmas. 
Require Import pif_tacs. 

Require Import seplog_lemmas. 
Require Import protect. 
Require Import join_lib.

Require Import mutexinit_pif_preserve. 
Require Import mutexdestroy_pif_preserve.
Require Import mutexlock_pif_preserve.
Require Import mutextrylock_pif_preserve. 
Require Import mutextimedlock_pif_preserve.
Require Import mutexunlock_pif_preserve.
Require Import mutexattrinit_pif_preserve.
Require Import mutexattrdestroy_pif_preserve.
Require Import mutexattrsettype_pif_preserve.
Require Import mutexattrgettype_pif_preserve.
Require Import mutexattrsetprioceiling_pif_preserve.
Require Import mutexattrgetprioceiling_pif_preserve.

Lemma good_dt_set_curtid:
  forall O t, 
    GOOD_DT O -> 
    GOOD_DT (set O curtid (oscurt t)). 
Proof.
  introv Hgdt.
  unfold GOOD_DT in *.
  introv Hge' Hgt' Hgm' Hgp'.
  eapply Hgdt; eauto.
  rewrite OSAbstMod.set_a_get_a' in Hge'; eauto.
  rewrite OSAbstMod.set_a_get_a' in Hgt'; eauto.
  rewrite OSAbstMod.set_a_get_a' in Hgm'; eauto.
  rewrite OSAbstMod.set_a_get_a' in Hgp'; eauto.
Qed. 

Set Nested Proofs Allowed.
Lemma pif_set_hprio:
  forall 
    (T : TasksMod.map)
    (O : OSAbstMod.map)
    (cst' : clientst)
    (Hnonesto : NO_NEST_PENDING_O O)
    (t' t : tid)
    (ke : exprcont)
    (ks : stmtcont)
    (s : spec_code)
    (H6 : OSAbstMod.get O curtid = Some (oscurt t))
    (x : exprcont)
    (x0 : stmtcont)
    (x1 : spec_code)
    (Hnonesto' : NO_NEST_PENDING_O (set O curtid (oscurt t')))
    (Hgooddt : GOOD_DT O)
    (Hpif : PIF O)
    (Hgooddt' : GOOD_DT (set O curtid (oscurt t')))
    (pc : progunit)
    (H H0: True)
    (H1 : forall (t0 : tid) (c : cureval) (ke0 : exprcont) (ks0 : stmtcont),
        TasksMod.get (set T t (curs (hapi_code s), (ke, ks))) t0 =
          Some (c, (ke0, ks0)) -> c <> curs (hapi_code (ABORT)))
    (H3 : GetHPrio O t')
    (H5 : TasksMod.get T t = Some (curs (hapi_code (sched;; s)), (ke, ks)))
    (H2 : t' <> t), 
    PIF (set O curtid (oscurt t')). 
Proof.
  intros. 
  unfolds. intros.
  rewrite OSAbstMod.map_get_set in H8;inverts H8.
  unfolds in H3. mytac.

  unfold get in *;unfold set in *;simpl in *.
  unfolds in Hgooddt'.
  lets Hgooddtx: Hgooddt' H4 H7 H9 H10.
  
  rewrite abst_set_get_neq in H4, H7, H9, H10;auto.
  rewrite H3 in H7;inverts H7.
  destruct Hgooddtx as (Hrdy&Howp&Htkp&Hwtp&Hopp&Hnoowp).
  unfolds in Htkp.
  assert (exists p st m sus, TcbMod.get tls t0 = Some (p, st, m, sus)).
  remember (TcbMod.get tls t0) as X;destruct X;tryfalse.
  destruct b. destruct p. destruct p.
  do 3 eexists;eauto. mytac.
  lets Htaskstp':Htkp H7.

  unfolds in Hnoowp.
  lets Hx:Hnoowp H8 H13 H11.
  subst x3.
  
  destruct Htaskstp'.
  subst x6.
  assert (isrdy rdy).
  unfolds. auto.
  unfolds in H12. mytac.
  lets Hx: H21 H14 H7.
  rewrite H12 in H8; inverts H8.
  unfolds in Hopp.
  lets Hy:Hopp H7 H16.
  clear - Hx Hy.
  destruct Hy;int auto.
  mytac;subst.
  unfolds in Hwtp.
  lets Hx:Hwtp H7. mytac.
  assert (x6 <> ct). intro.
  subst x6.
  destruct H13.
  eexists;eauto.
  assert (isrdy rdy). unfolds. auto.
  unfolds in H12. mytac.
  lets Hx: H26 H24 H21.
  rewrite H12 in H8; inverts H8.
  lets Hy:H23 H16.
  clear -H22 Hy Hx. subst x2.
  int auto.
Qed.

Lemma no_nest_pif_hpstepok_preserve:
  forall client_code T cst O T' cst' O',
    NO_NEST_PENDING_O O ->
    NO_NEST_PENDING_O O' ->
    goodtasks_h T -> 
    GOOD_DT O ->
    PIF O ->
    hpstepok (client_code, os_spec') T cst O T' cst' O' ->
    PIF O'.
Proof.
  introv Hnn Hnn' Hgts Hgdt Hpif Hhpsp.
  inverts Hhpsp.
  match goal with H: context[hpstep] |- _ => inverts H end.
  - (* htstep *)
    match goal with H: context[htstep] |- _ => inverts H end.
    + (* cstep *)
      auto.
    + (* hapistep *)
      match goal with H: get T _ = _ |- _ => rename H into HgT end.
      match goal with H: (_, _) = _ |- _ => inverts H end.
      match goal with H: context[hapistep] |- _ => inverts H end.
      * (* api enter *)
        auto.
      * (* id api *)
        lets H__: Hgts HgT; eauto.
        unfolds in H__.
        destruct H__ as (Hgevl & Hgks).
        simpl in Hgevl.
        match goal with
          H: context[hmstep] |- _ => rename H into Hsp
        end.
        
        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexunlock_pif_preserve; eauto. 
        
        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexlock_pif_preserve; eauto.

        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutextimedlock_pif_preserve; eauto.
        
        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutextrylock_pif_preserve; eauto.
        
        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexinit_pif_preserve; eauto.

        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexdestroy_pif_preserve; eauto.

        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexattrinit_pif_preserve; eauto.

        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexattrdestroy_pif_preserve; eauto.

        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexattrsettype_pif_preserve; eauto.

        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexattrgettype_pif_preserve; eauto.

        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexattrsetprioceiling_pif_preserve; eauto.

        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexattrgetprioceiling_pif_preserve; eauto.

        destruct Hgevl as[Habt | Hend].
        subst cd. inverts Hsp.
        simpljoin.
        inverts Hsp.

      * (*  *)
        auto.
      * (*  *)
        auto. 

  - (* htistep *)
    match goal with H: (_, _) = _ |- _ => inverts H end.
    match goal with H: context[htistep] |- _ => inverts H end.
    unfold int_spec', int_spec_list' in H.
    simpl in H.
    tryfalse.

  - (* sched *)
    match goal with H: (_, _) = _ |- _ => inverts H end.
    lets Hgooddt': good_dt_set_curtid t' Hgdt; eauto.
    casetac t t' Ht Hf.
    + subst. rewrite OSAbstMod.get_set_same;auto.
    + eapply pif_set_hprio; eauto. 
Qed.       

Require Import sound_include.
Require Import int_lock.
Require Import symbolic_lemmas.
Require Import Lia.
Require Import join_lib.

Lemma dintp_rule_sound :
  forall Spec sd  I r ri isr ier is cs aop pa t P irqLine Hier Hier' v,
      GoodFrm P ->
      P ==> CurLINV pa t ->
      Hier' = ierupd Hier (Z.to_nat (Int.unsigned v)) false ->
      RuleSem Spec sd pa I r ri 
            ( <|| int_disable_pic_aop(|nil|) ;; aop||> 
              ** OS[isr, ier, false, is, cs] 
              ** LV irqLine @ Tint32 |-> (Vint32 v) ** Aabsdata ierid (hier Hier) ** P
            )
            (sprim (dintp irqLine))
            (<||aop||> ** OS[isr, ierupd ier (Z.to_nat (Int.unsigned v)) false, false, is, cs]
              ** LV irqLine @ Tint32 |-> (Vint32 v) ** Aabsdata ierid (hier Hier') ** P) t.
Proof.
  introv Hgood Himp Hthier.
  unfolds. 
  introv Hsat.
  destruct Hsat as (Hsat1 & Hsat2).
  destruct o as [[[[[G E] M] irr] ierr] aux].
  destruct aux as [[iee iss] css].
  sep split in Hsat1.
  simpl in H,H0,H1,H2,H3,H4.
  subst.
  simpl in Hsat1.
  simp join.
  assert (x0 = x6) by join auto.
  subst x0.
  clear H5.
  assert (x13 = x) by join auto.
  subst x13.
  clear H11.
  unfold emposabst in *.
  subst x15 x16.
  assert (x2 = empenv) by join auto.
  subst x2.
  assert (x3 = O) by join auto.
  subst x3.
  clear H2 H13.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.
  introv Hrawfalse.
  destruct Hrawfalse as (_&Hrawfalse&_).
  false.
  apply Hrawfalse.
  unfold IsDintp.
  do 2 eexists.
  eauto.
  introv Hinv Hjm2 Hdisj Hjo Hnabt Hstep.
  apply Hstep.
  destruct o2 as [[[[[]]]]].
  destruct l as [[]].
  do 2 eexists.
  eapply dintp_stepp; eauto.
  unfolds in Hjm2.
  unfold joinmem in Hjm2.
  simpljoin.
  apply H14.
  assert(rule_type_val_match Tint32 (Vint32 v) = true) by auto.
  assert(Int.unsigned Int.zero = 0%Z) by auto.
  rewrite H1 in H15.
  lets Hloadv : mapstoval_load H H15.
  unfolds in Hjm2.
  unfold joinmem in Hjm2.
  simpljoin.
  lets Hj1 : join_join_merge23_join H0 j0.
  lets Hj2 : join_join_merge23_join Hj1 j.
  lets Hloadd : load_mono Hj2 Hloadv.
  rewrite Hloadv in Hloadd.
  apply Hloadd.
  simpl substaskst in *. 
  introv Hinv Hjm1 Hjm2 Hstep Hnabt Hlenv Hmem Hget Hload.
  invertstep idtac.
  unfolds in Hjm1.
  unfold joinmem in Hjm1. 
  simp join.
  eexists.
  exists aop OO.
  unfold get_smem in Hget.
  unfold get_lenv in Hget.
  rewrite H2 in Hget; inverts Hget.
  exists (set OO ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) false))).
  exists (x3, x4, x14, x8, ierupd x10 (Z.to_nat (Int.unsigned x0)) false, (false, is, cs)).
  exists Ms (set O ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) false))) Os.
  splits; eauto.
  constructors.
  unfolds.
  exists Hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) false).
  splits;auto.
  eapply join_comm in H7.
  eapply dintp_joinsig_join_get; eauto.
  unfold get_smem in Hload.
  unfold get_mem in Hload.
  rewrite Hload in H3.
  assert(x0 = x1).
  congruence.
  subst x1.
  unfolds; unfold joinmem; join auto.
  eapply join_comm in H7.
  eapply dintp_join_Hier; eauto.
  assert (satp (x3, x4, x6, x8, x10, (false, is, cs)) x9 (CurLINV pa t)).
  eapply local_inv_aop_irev with (int_disable_pic_aop (|nil|);; aop); auto.
  remember (set O ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) false))) as OK.
  remember (sig ierid (hier Hier)) as Oier.
  assert ( join x9 (set Oier ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) false))) OK) as Haps.
  eapply join_comm in H7.
  eapply dintp_join_Hier'; eauto.
  assert (satp (x3, x4, x14, x8, x10, (false, is, cs)) OK (CurLINV pa t)).
  eapply join_comm in H0.
  eapply join_satp_local_inv with (M:=x) (Of:= (set Oier ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) false)))); eauto.
  unfold joinmem.
  exists x3 x4 x6 x14 x8.
  exists x10 (false, is, cs).
  splits; eauto.
  eapply Linv_igore; eauto.

  constructors; introv Hfalse; tryfalse.
  intros; invertstep idtac.
  inverts Hfalse.
  trysimplsall.
  introv Hds Hdss Hddss Hnabt'.
  exists aop OO0 (set O ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) false))) Os0. 
  splits; eauto.
  constructors.
  assert (satp (x3, x4, x6, x8, x10, (false, is, cs)) x9 (CurLINV pa t)).
  eapply local_inv_aop_irev with (int_disable_pic_aop (|nil|);; aop); auto.
  remember (set O ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) false))) as OK.
  remember (sig ierid (hier Hier)) as Oier.
  assert ( join x9 (set Oier ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) false))) OK) as Haps.
  eapply join_comm in H7.
  eapply dintp_join_Hier'; eauto.
  assert (satp (x3, x4, x14, x8, x10, (false, is, cs)) OK (CurLINV pa t)).
  eapply join_comm in H0.
  eapply join_satp_local_inv with (M:=x) (Of:= (set Oier ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) false)))); eauto.
  unfold joinmem.
  exists x3 x4 x6 x14 x8.
  exists x10 (false, is, cs).
  splits; eauto.
  eapply Linv_igore; eauto.

  unfold lift.
  sep split; try solve [simpl; auto].
  simpl.
  exists x x6 x14 empabst (set O ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) false))) (set O ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) false))).
  splits; eauto.
  join auto.
  exists x18 empmem x x.
  exists empabst empabst empabst.
  splits; eauto.
  join auto.
  join auto.
  exists x18.
  splits; eauto.
  unfold emposabst; auto.
  unfold emposabst; auto.
  exists empmem x6 x6.
  exists (sig ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned v)) false))) x9 (set O ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) false))).
  splits; eauto.
  join auto.
  assert(rule_type_val_match Tint32 (Vint32 v) = true) by auto.
  assert(Int.unsigned Int.zero = 0%Z) by auto.
  rewrite H1 in H15.
  lets Hloadv : mapstoval_load H H15.
  rewrite H14 in H2.
  assert(x18 = b).
  congruence.
  subst x18.
  lets Hj1 : join_join_merge23_join H0 H8.
  lets Hj2 : join_join_merge23_join Hj1 H5.
  lets Hloadd : load_mono Hj2 Hloadv.
  rewrite Hloadv in Hloadd.
  assert(x0 = v).
  congruence.
  subst v.
  eapply join_comm.
  eapply join_comm in H7.
  eapply dintp_join_Hier''; eauto.
  eapply goodfrm_prop; eauto.
  unfold gettaskst.
  unfold getier.
  assert(rule_type_val_match Tint32 (Vint32 v) = true) by auto.
  assert(Int.unsigned Int.zero = 0%Z) by auto.
  rewrite H1 in H15.
  lets Hloadv : mapstoval_load H H15.
  rewrite H14 in H2.
  assert(x18 = b).
  congruence.
  subst x18.
  lets Hj1 : join_join_merge23_join H0 H8.
  lets Hj2 : join_join_merge23_join Hj1 H5.
  lets Hloadd : load_mono Hj2 Hloadv.
  rewrite Hloadv in Hloadd.
  assert(x0 = v).
  congruence.
  subst v.
  auto.
  destruct Hfalse as ( _ & _&Hfff&_).
  false.
  apply Hfff.
  eexists; eauto.
Qed.

Lemma rintp_rule_sound :
forall Spec sd  I r ri isr ier is cs aop pa t P irqLine Hier Hier' v,
      GoodFrm P ->
      P ==> CurLINV pa t ->
      Hier' = ierupd Hier (Z.to_nat (Int.unsigned v)) true ->
      RuleSem Spec sd pa I r ri 
            ( <|| int_enable_pic_aop(|nil|) ;; aop||> 
              ** OS[isr, ier, false, is, cs] 
              ** LV irqLine @ Tint32 |-> (Vint32 v) ** Aabsdata ierid (hier Hier) ** P
            )
            (sprim (rintp irqLine))
            (<||aop||> ** OS[isr, ierupd ier (Z.to_nat (Int.unsigned v)) true, false, is, cs]
              ** LV irqLine @ Tint32 |-> (Vint32 v) ** Aabsdata ierid (hier Hier') ** P) t.
Proof.
  introv Hgood Himp Hthier.
  unfolds. 
  introv Hsat.
  destruct Hsat as (Hsat1 & Hsat2).
  destruct o as [[[[[G E] M] irr] ierr] aux].
  destruct aux as [[iee iss] css].
  sep split in Hsat1.
  simpl in H,H0,H1,H2,H3,H4.
  subst.
  simpl in Hsat1.
  simp join.
  assert (x0 = x6) by join auto.
  subst x0.
  clear H5.
  assert (x13 = x) by join auto.
  subst x13.
  clear H11.
  unfold emposabst in *.
  subst x15 x16.
  assert (x2 = empenv) by join auto.
  subst x2.
  assert (x3 = O) by join auto.
  subst x3.
  clear H2 H13.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.
  introv Hrawfalse.
  destruct Hrawfalse as (_&_&_&Hrawfalse&_).
  false.
  apply Hrawfalse.
  unfold IsRintp.
  do 2 eexists.
  eauto.
  introv Hinv Hjm2 Hdisj Hjo Hnabt Hstep.
  apply Hstep.
  destruct o2 as [[[[[]]]]].
  destruct l as [[]].
  do 2 eexists.
  eapply rintp_stepp; eauto.
  unfolds in Hjm2.
  unfold joinmem in Hjm2.
  simpljoin.
  apply H14.
  assert(rule_type_val_match Tint32 (Vint32 v) = true) by auto.
  assert(Int.unsigned Int.zero = 0%Z) by auto.
  rewrite H1 in H15.
  lets Hloadv : mapstoval_load H H15.
  unfolds in Hjm2.
  unfold joinmem in Hjm2.
  simpljoin.
  lets Hj1 : join_join_merge23_join H0 j0.
  lets Hj2 : join_join_merge23_join Hj1 j.
  lets Hloadd : load_mono Hj2 Hloadv.
  rewrite Hloadv in Hloadd.
  apply Hloadd.
  simpl substaskst in *. 
  introv Hinv Hjm1 Hjm2 Hstep Hnabt Hlenv Hmem Hget Hload.
  invertstep idtac.
  unfolds in Hjm1.
  unfold joinmem in Hjm1. 
  simp join.
  eexists.
  exists aop OO.
  unfold get_smem in Hget.
  unfold get_lenv in Hget.
  rewrite H2 in Hget; inverts Hget.
  exists (set OO ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) true))).
  exists (x3, x4, x14, x8, ierupd x10 (Z.to_nat (Int.unsigned x0)) true, (false, is, cs)).
  exists Ms (set O ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) true))) Os.
  splits; eauto.
  constructors.
  unfolds.
  exists Hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) true).
  splits;auto.
  eapply join_comm in H7.
  eapply dintp_joinsig_join_get; eauto.
  unfold get_smem in Hload.
  unfold get_mem in Hload.
  rewrite Hload in H3.
  assert(x0 = x1).
  congruence.
  subst x1.
  unfolds; unfold joinmem; join auto.
  eapply join_comm in H7.
  eapply rintp_join_Hier; eauto.
  assert (satp (x3, x4, x6, x8, x10, (false, is, cs)) x9 (CurLINV pa t)).
  eapply local_inv_aop_irev with (int_enable_pic_aop (|nil|);; aop); auto.
  remember (set O ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) true))) as OK.
  remember (sig ierid (hier Hier)) as Oier.
  assert ( join x9 (set Oier ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) true))) OK) as Haps.
  eapply join_comm in H7.
  eapply rintp_join_Hier'; eauto.
  assert (satp (x3, x4, x14, x8, x10, (false, is, cs)) OK (CurLINV pa t)).
  eapply join_comm in H0.
  eapply join_satp_local_inv with (M:=x) (Of:= (set Oier ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) true)))); eauto.
  unfold joinmem.
  exists x3 x4 x6 x14 x8.
  exists x10 (false, is, cs).
  splits; eauto.
  eapply Linv_igore; eauto.

  constructors; introv Hfalse; tryfalse.
  intros; invertstep idtac.
  inverts Hfalse.
  trysimplsall.
  introv Hds Hdss Hddss Hnabt'.
  exists aop OO0 (set O ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) true))) Os0. 
  splits; eauto.
  constructors.
  assert (satp (x3, x4, x6, x8, x10, (false, is, cs)) x9 (CurLINV pa t)).
  eapply local_inv_aop_irev with (int_enable_pic_aop (|nil|);; aop); auto.
  remember (set O ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) true))) as OK.
  remember (sig ierid (hier Hier)) as Oier.
  assert ( join x9 (set Oier ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) true))) OK) as Haps.
  eapply join_comm in H7.
  eapply rintp_join_Hier'; eauto.
  assert (satp (x3, x4, x14, x8, x10, (false, is, cs)) OK (CurLINV pa t)).
  eapply join_comm in H0.
  eapply join_satp_local_inv with (M:=x) (Of:= (set Oier ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) true)))); eauto.
  unfold joinmem.
  exists x3 x4 x6 x14 x8.
  exists x10 (false, is, cs).
  splits; eauto.
  eapply Linv_igore; eauto.

  unfold lift.
  sep split; try solve [simpl; auto].
  simpl.
  exists x x6 x14 empabst (set O ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) true))) (set O ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) true))).
  splits; eauto.
  join auto.
  exists x18 empmem x x.
  exists empabst empabst empabst.
  splits; eauto.
  join auto.
  join auto.
  exists x18.
  splits; eauto.
  unfold emposabst; auto.
  unfold emposabst; auto.
  exists empmem x6 x6.
  exists (sig ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned v)) true))) x9 (set O ierid (hier (ierupd Hier (Z.to_nat (Int.unsigned x0)) true))).
  splits; eauto.
  join auto.
  assert(rule_type_val_match Tint32 (Vint32 v) = true) by auto.
  assert(Int.unsigned Int.zero = 0%Z) by auto.
  rewrite H1 in H15.
  lets Hloadv : mapstoval_load H H15.
  rewrite H14 in H2.
  assert(x18 = b).
  congruence.
  subst x18.
  lets Hj1 : join_join_merge23_join H0 H8.
  lets Hj2 : join_join_merge23_join Hj1 H5.
  lets Hloadd : load_mono Hj2 Hloadv.
  rewrite Hloadv in Hloadd.
  assert(x0 = v).
  congruence.
  subst v.
  eapply join_comm.
  eapply join_comm in H7.
  eapply rintp_join_Hier''; eauto.
  eapply goodfrm_prop; eauto.
  unfold gettaskst.
  unfold getier.
  assert(rule_type_val_match Tint32 (Vint32 v) = true) by auto.
  assert(Int.unsigned Int.zero = 0%Z) by auto.
  rewrite H1 in H15.
  lets Hloadv : mapstoval_load H H15.
  rewrite H14 in H2.
  assert(x18 = b).
  congruence.
  subst x18.
  lets Hj1 : join_join_merge23_join H0 H8.
  lets Hj2 : join_join_merge23_join Hj1 H5.
  lets Hloadd : load_mono Hj2 Hloadv.
  rewrite Hloadv in Hloadd.
  assert(x0 = v).
  congruence.
  subst v.
  auto.
  destruct Hfalse as ( _ & _&Hfff&_).
  false.
  apply Hfff.
  eexists; eauto.
Qed.

Lemma dint_rule_sound :
  forall Spec sd  I r ri isr ier is cs pa t P level v Hier,
    GoodFrm P ->  
    P ==> CurLINV pa t ->
    RuleSem Spec sd pa I r ri 
          ( <|| int_lock_aop(|nil|)||> ** OS[isr, ier, false, is, cs]   **  
            LV level @ Tint32 |-> v ** Aabsdata ierid (hier Hier) ** P
          )
          (sprim (dint level))
          (<||(END (Some (Vint32(getLevel ier intStart Int.zero intStartInt))))||> ** OS[isr, empupd ier, false, is, cs]  **  
            LV level @ Tint32 |-> (Vint32 (getLevel ier intStart Int.zero intStartInt))  ** 
            Aabsdata ierid (hier (empupd Hier)) ** P) t.
Proof.
  introv Hgood Himp.
  unfolds. 
  introv Hsat.
  destruct Hsat as (Hsat1 & Hsat2).
  destruct o as [[[[[G E] M] irr] ierr] aux].
  destruct aux as [[iee iss] css].
  sep split in Hsat1.
  simpl in H,H0,H1,H2,H3,H4.
  subst.
  simpl in Hsat1.
  simp join.
  assert (x13 = x) by join auto.
  subst x13.
  clear H11.
  assert (x6 = x0) by join auto.
  subst x6.
  clear H5.
  unfold emposabst in *.
  subst x15 x16.
  assert (x2 = empabst) by join auto.
  subst x2.
  assert (x3 = O) by join auto.
  subst x3.
  clear H2 H13.
  unfold nilcont.
  lets Hksimp : Himp H9.
  constructors; introv Hfalse; tryfalse.
  introv Hrawfalse.
  destruct Hrawfalse as (Hrawfalse&_).
  false.
  apply Hrawfalse.
  unfold IsDint.
  do 2 eexists.
  eauto.
  introv Hj Hj2 Hinvv Hjo Hnabt Hstep.
  apply Hstep.
  destruct o2 as [[[[[]]]]].
  destruct l as [[]].
  unfolds in Hj2.
  unfold joinmem in Hj2.
  simp join.
  lets Hsdd : store_exist_join' (Vint32 (getLevel x7 intStart (Int.repr 0) intStartInt))  H15 H0.  
  simp join.
  lets Hsdss : store_mono H5 H.
  simp join.
  lets Hsdsss : store_mono H3 H1.
  simp join.
  do 2 eexists.
  eapply dint_step ; eauto.
  simpl substaskst in *. 
  introv Hinv Hjm1 Hjm2 Hstep Hnabt.
  invertstep idtac.
  unfolds in Hjm1.
  unfold joinmem in Hjm1. 
  simp join.
  rewrite H2 in H14; inverts H14.
  lets Hres : store_join_map_join H5 H8 H0 H3; eauto.
  simp join.
  eexists.
  exists OO.
  exists (set OO ierid (hier (empupd Hier))).
  exists (x2, x3, x10, x6, empupd x7, (false, is, cs)).
  exists Ms (set O ierid (hier (empupd Hier))) Os x7.
  splits; eauto.
  constructors.
  unfolds.
  exists Hier.
  splits;auto.
  eapply join_comm in H7.
  eapply dintp_joinsig_join_get; eauto.
  unfolds.
  unfold joinmem. join auto.
  eapply join_comm in H7.
  eapply dint_join_Hier; eauto.
  remember (set O ierid (hier (empupd Hier))) as OK.
  remember (sig ierid (hier Hier)) as Oier.
  assert (satp (x2, x3, x10, x6, x7, (false, is, cs)) OK (CurLINV pa t)).
  assert ( join x9 (set Oier ierid (hier (empupd Hier))) OK) as Haps.
  eapply join_comm in H7.
  eapply dint_join_Hier'; eauto.
  assert (joinmem (x2, x3, x10, x6, x7, (false, is, cs)) empmem (x2, x3, x10, x6, x7, (false, is, cs))) as Hjm.
  unfolds.
  join auto.
  assert (satp (x2, x3, x0, x6, x7, (false, is, cs)) x9 (CurLINV pa t)).
  eapply absinfer_sound.local_inv_aop_irev with (int_lock_aop (|nil|)).
  auto.
  eapply join_satp_local_inv with (M:=x1) (Of:= (set Oier ierid (hier (empupd Hier)))); eauto.
  unfold joinmem; join auto.
  splits; eauto.
  eapply Linv_igore; eauto.
  constructors; introv Hfalse; tryfalse.
  intros; invertstep idtac.
  inverts Hfalse.
  trysimplsall.
  introv Hds Hdss Hddss.
  exists (END Some (Vint32 (getLevel x7 intStart Int.zero intStartInt))) OO0 (set O ierid (hier (empupd Hier))) Os0. 
  splits; eauto.
  constructors.
  subst OK; auto.
  assert (satp (x2, x3, x10, x6, x7, (false, is, cs)) OK (CurLINV pa t)).
  assert ( join x9 (set Oier ierid (hier (empupd Hier))) OK) as Haps.
  eapply join_comm in H7.
  eapply dint_join_Hier'; eauto.
  assert (joinmem (x2, x3, x10, x6, x7, (false, is, cs)) empmem (x2, x3, x10, x6, x7, (false, is, cs))) as Hjm.
  unfolds.
  join auto.
  assert (satp (x2, x3, x0, x6, x7, (false, is, cs)) x9 (CurLINV pa t)).
  eapply absinfer_sound.local_inv_aop_irev with (int_lock_aop (|nil|)).
  auto.
  eapply join_satp_local_inv with (M:=x1) (Of:= (set Oier ierid (hier (empupd Hier)))); eauto.
  unfold joinmem; join auto.
  subst OK.
  auto.
  eapply Linv_igore; eauto.
  unfold lift.
  sep split; eauto.
  substs.
  remember (Vint32 (getLevel x7 intStart Int.zero intStartInt)) as ret_level.
  remember (set O ierid (hier (empupd Hier))) as OK.
  exists x1 x0 x10 empabst OK OK.
  unfold substmo; unfold substaskst.
  (*trysimplsall.*)
  splits; auto.
  join auto.
  simpl.
  exists x18 empmem x1 x1 empabst.
  exists empabst empabst.
  splits; eauto.
  join auto.
  join auto.
  exists x18.
  splits; eauto.
  unfolds; auto.
  rewrite Heqret_level.
  eauto.
  unfolds; eauto.
  remember (Vint32 (getLevel x7 intStart Int.zero intStartInt)) as ret_level'.
  simpl.
  exists empmem x0 x0.
  exists (sig ierid (hier (empupd Hier))) x9 OK.
  splits; eauto.
  join auto.
  rewrite HeqOK.
  eapply join_comm in H7.
  eapply join_comm.
  eapply dint_join_Hier''; eauto.
  eapply goodfrm_prop; eauto.
  destruct Hfalse as ( _ & _&Hfff&_).
  false.
  apply Hfff.
  eexists; eauto.
Qed.

Lemma rint_rule_sound :
  forall Spec sd  I r ri isr ier is cs aop pa t P level Hier Hier' v,
      GoodFrm P -> 
      P ==> CurLINV pa t ->
      Hier' = ierupds_int Hier v ->
      RuleSem Spec sd pa I r ri 
          ( <|| int_unlock_aop(|nil|) ;; aop||> 
            ** OS[isr, ier, false, is, cs] 
            ** LV level @ Tint32 |-> (Vint32 v) ** Aabsdata ierid (hier Hier) ** P
          )
          (sprim (rint level))
          (<||aop||> ** OS[isr, ierupds_int ier v, false, is, cs] 
            ** LV level @ Tint32 |-> (Vint32 v) ** Aabsdata ierid (hier Hier') ** P) t.
Proof.
  introv Hgood Himp Hthier.
  unfolds. 
  introv Hsat.
  destruct Hsat as (Hsat1 & Hsat2).
  destruct o as [[[[[G E] M] irr] ierr] aux].
  destruct aux as [[iee iss] css].
  sep split in Hsat1.
  simpl in H,H0,H1,H2,H3,H4.
  subst.
  simpl in Hsat1.
  simp join.
  assert(x6 = x0) by join auto.
  subst x6.
  assert(x13 = x) by join auto.
  subst x13.
  unfold emposabst in *.
  subst x15 x16.
  assert(x2 = empenv) by join auto.
  subst x2.
  assert(x3 = O) by join auto.
  subst x3.
  clear H2 H11 H13 H5.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.
  introv Hrawfalse.
  destruct Hrawfalse as (_&_&Hrawfalse&_).
  false.
  apply Hrawfalse.
  unfold IsRint.
  do 2 eexists.
  eauto.
  introv Hinv Hjm2 Hdisj Hjo Hnabt Hstep.
  apply Hstep.
  destruct o2 as [[[[[]]]]].
  destruct l as [[]].
  do 2 eexists.
  eapply rint_stepp ; eauto.
  unfolds in Hjm2.
  unfold joinmem in Hjm2.
  simpljoin.
  apply H14.
  assert(rule_type_val_match Tint32 (Vint32 v) = true) by auto.
  assert(Int.unsigned Int.zero = 0%Z) by auto.
  rewrite H1 in H15.
  lets Hloadv : mapstoval_load H H15.
  unfolds in Hjm2.
  unfold joinmem in Hjm2.
  simpljoin.
  lets Hj1 : join_join_merge23_join H0 j0.
  lets Hj2 : join_join_merge23_join Hj1 j.
  lets Hloadd : load_mono Hj2 Hloadv.
  rewrite Hloadv in Hloadd.
  apply Hloadd.

  simpl substaskst in *. 
  introv Hinv Hjm1 Hjm2 Hstep Hnabt Hlenv Hmem Hget Hload.
  invertstep idtac.
  unfolds in Hjm1.
  unfold joinmem in Hjm1. 
  simp join.
  eexists.
  exists aop OO.
  exists (set OO ierid (hier (ierupds_int Hier x2))).
  exists (x4, x5, x14, x8, ierupds_int x10 x2, (false, is, cs)).
  exists Ms (set O ierid (hier (ierupds_int Hier x2))) Os.
  splits; eauto.
  constructors.
  unfolds.
  exists Hier (ierupds_int Hier x2).
  splits;auto.
  eapply join_comm in H7.
  eapply dintp_joinsig_join_get; eauto.
  unfold get_smem in Hload.
  unfold get_mem in Hload.
  unfold get_smem in Hget.
  unfold get_lenv in Hget.
  assert(b=b0).
  congruence.
  subst b0.
  assert(x2=x1).
  congruence.
  subst x2.
  auto.
  unfolds.
  unfold joinmem. join auto.
  eapply join_comm in H7.
  eapply rint_join_Hier; eauto.
  assert (satp (x4, x5, x0, x8, x10, (false, is, cs)) x9 (CurLINV pa t)).
  eapply local_inv_aop_irev with (int_unlock_aop (|nil|);; aop); auto.
  remember (set O ierid (hier (ierupds_int Hier x2))) as OK.
  remember (sig ierid (hier Hier)) as Oier.
  assert ( join x9 (set Oier ierid (hier (ierupds_int Hier x2))) OK) as Haps.
  eapply join_comm in H7.
  eapply rint_join_Hier'; eauto.
  assert (satp (x4, x5, x14, x8, x10, (false, is, cs)) OK (CurLINV pa t)).
  eapply join_comm in H0.
  eapply join_satp_local_inv with (M:=x) (Of:= ((set Oier ierid (hier (ierupds_int Hier x2))))); eauto.
  unfold joinmem.
  exists x4 x5 x0 x14 x8.
  exists x10 (false, is, cs).
  splits; eauto.
  eapply Linv_igore; eauto.

  constructors; introv Hfalse; tryfalse.
  introv Hrawlostep.
  intros; invertstep idtac.
  inverts Hfalse.
  trysimplsall.
  introv Hds Hdss Hddss Hnabt'.
  exists aop OO0 (set O ierid (hier (ierupds_int Hier x2))) Os0. 
  splits; eauto.
  constructors.
  remember (set O ierid (hier (ierupds_int Hier x2))) as OK.
  remember (sig ierid (hier Hier)) as Oier.
  assert ( join x9 (set Oier ierid (hier (ierupds_int Hier x2))) OK) as Haps.
  eapply join_comm in H7.
  eapply rint_join_Hier'; eauto.
  assert (satp (x4, x5, x0, x8, x10, (false, is, cs)) x9 (CurLINV pa t)).
  eapply local_inv_aop_irev with (int_unlock_aop (|nil|);; aop); auto.
  assert (satp (x4, x5, x14, x8, x10, (false, is, cs)) OK (CurLINV pa t)).
  eapply join_comm in H0.
  eapply join_satp_local_inv with (M:=x) (Of:= ((set Oier ierid (hier (ierupds_int Hier x2))))); eauto.
  unfold joinmem.
  exists x4 x5 x0 x14 x8.
  exists x10 (false, is, cs).
  splits; eauto.
  eapply Linv_igore; eauto.

  unfold lift.
  sep split; auto.
  simpl.
  exists x x0 x14 empabst (set O ierid (hier (ierupds_int Hier x2))) (set O ierid (hier (ierupds_int Hier x2))).
  splits; eauto.
  join auto.
  exists x18 empmem x x.
  exists empabst empabst empabst.
  splits; eauto.
  join auto.
  join auto.
  exists x18.
  splits; eauto.
  unfold emposabst.
  auto.
  unfold emposabst.
  auto.
  exists empmem x0 x0 (sig ierid (hier (ierupds_int Hier v))) x9 (set O ierid (hier (ierupds_int Hier x2))).
  splits; eauto.
  join auto.
  assert(rule_type_val_match Tint32 (Vint32 v) = true) by auto.
  assert(Int.unsigned Int.zero = 0%Z) by auto.
  rewrite H1 in H15.
  lets Hloadv : mapstoval_load H H15.
  rewrite H14 in H2.
  assert(x18 = b0).
  congruence.
  subst x18.
  lets Hj1 : join_join_merge23_join H0 H8.
  lets Hj2 : join_join_merge23_join Hj1 H5.
  lets Hloadd : load_mono Hj2 Hloadv.
  rewrite Hloadv in Hloadd.
  assert(x2 = v).
  congruence.
  subst v.
  eapply join_comm.
  eapply join_comm in H7.
  eapply rint_join_Hier''; eauto.
  eapply goodfrm_prop; eauto.
  unfold gettaskst.
  unfold getier.
  assert(rule_type_val_match Tint32 (Vint32 v) = true) by auto.
  assert(Int.unsigned Int.zero = 0%Z) by auto.
  rewrite H1 in H15.
  lets Hloadv : mapstoval_load H H15.
  rewrite H14 in H2.
  assert(x18 = b0).
  congruence.
  subst x18.
  lets Hj1 : join_join_merge23_join H0 H8.
  lets Hj2 : join_join_merge23_join Hj1 H5.
  lets Hloadd : load_mono Hj2 Hloadv.
  rewrite Hloadv in Hloadd.
  assert(x2 = v).
  congruence.
  subst v.
  auto.
  destruct Hfalse as ( _ & _&Hfff&_).
  false.
  apply Hfff.
  eexists; eauto.
Qed.

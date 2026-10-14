Require Import symbolic_lemmas2.
Require Import Lia.
Require Import sound_include2.
Require Import os_inv2.
Require Import join_lib2.
Require Import joinmemLib2.

Import DeprecatedTactic.
Open Scope Z_scope.

Lemma eoint_ieon_rule_sound:
  forall Spec sd I r ri isr ier is id cs vi i aop li t P,  
    0 <= Int.unsigned id < Z_of_nat INUM ->
    i = Z.to_nat (Int.intval id) ->  
    GoodFrm P -> 
    P ==> CurLINV li t ->
    isr i = true ->
    RuleSem Spec sd li I r ri 
            (<|| aop ||> ** OS [isr, ier, true, i::is, cs] ** 
                 getinv (I i) ** GV vi @ Tint32 |-r-> (Vint32 id) ** P)
            (sprim (eoint vi))
            (<|| aop ||> ** OS [isrupd isr i false, ier, true, i::is, cs] **
                 GV vi @ Tint32 |-r-> (Vint32 id) ** P) t.
Proof.
  introv Hp1 Hp2 Hgood Himp Hisr Hsat.
  unfold Int.unsigned in *.
  destruct Hsat as (Hsat1 & Hsat2).
  destruct o as [[[[[G E] M] iis] ierr] ax].
  destruct ax as [[ie iss] css].
  sep split in Hsat1.
  simpl in H,H0,H1,H2,H3,H4.
  subst.
  simpl in Hsat1.
  simp join.
  assert (x13 = x5) by join auto.
  subst x13.
  clear H10.
  unfold emposabst in *.
  subst x15 x16.
  assert (x8 = empenv) by join auto.
  subst x8.
  assert (x9 = x3) by join auto.
  subst x9.
  clear H7 H12.
  constructors; introv Hff; tryfalse.
  unfold nilcont.
  introv Hloststep Hinv Hjm1 Hjm2 Hstep.
  invertstep idtac.
  unfolds in Hjm1.
  unfold joinmem in Hjm1.
  simp join.
  rewrite H13 in H4.
  inverts H4.
  assert(rule_type_val_match Tint32 (Vint32 id) = true) by auto.
  assert(Int.unsigned Int.zero = 0%Z) by auto.
  rewrite H4 in H14.
  lets Hloadv : mapstoval_load H H14.
  apply map_join_comm in H0.
  lets Hjm : join_join_merge23_join H5 H0.
  lets Hjm' : join_join_merge23_join Hjm H15.
  lets Hjm'' : join_join_merge23_join Hjm' H11.  
  lets Hloadd : load_mono Hjm'' Hloadv.
  rewrite H6 in Hloadd; rewrite Hloadv in Hloadd.
  (* inverts Hloadd. *)
  assert(id=i) by congruence; subst; clear Hloadd.
 
  lets Hks : Hinv aop.
  simpl substaskst in *.
  remember (Z.to_nat (Int.intval i)) as m.
  unfold INV in Hks.
  unfold sat in Hks; fold sat in Hks.
  trysimplall.
  simp join.

  lets Hle: Zle_imply_natle H1 H20.
  
  remember (Z.to_nat (Int.intval i)) as m.
  destruct H18 as [Hon | Hoff].
  unfold inv_ieon in Hon.
  sep split in Hon.
  unfold invlth_isr  in Hon.
  replace (INUM - 0)%nat  with (INUM) in * by omega.
  clear H.
  exists aop OO.
  assert (exists Mss, join x0 Mss x8 /\ join x Ms Mss).
  clear -H0 H15.
  join auto.
  assert (exists Oss, join x3 Oss OO /\ join x2 Os Oss).
  clear -H2 Hjm2.
  join auto.
  destruct H as (Mss & Hj1 & Hj2).
  destruct H12 as (Oss & Hjj1 & Hjj2).

  exists (x4, x7, x0, isrupd x10 (Z.to_nat (Int.intval i)) false, x11,
          (true, m :: is, cs)).
  exists Mss x3 Oss.
  unfold INV in *.
  assert (exists j, INUM = S j).
  destruct INUM.
  omega.
  eauto.
  destruct H as (j & Hinum).
  rewrite Hinum in *.
  splits; eauto.
  constructors.
  unfolds.
  unfold joinmem; jeat.
  simpl substaskst.
  unfolds.
  intros.
  assert (exists k, join x1 k Mss /\ join x x12 k).
  clear -H10 Hj2.
  join auto.
  assert (exists k, join x14 k Oss /\ join x2 x16 k).
  clear -H16 Hjj2.
  join auto.
  simp join.
  exists x1 x17 Mss x14 x13 Oss.
  splits;eauto.
  simpl substmo.
  destruct (prec (I (S (S j)))) as [Hp1 Hp2].
  destruct Hp2 as [Hp2 _ _ _].
  lets Hsd : Hp2 H17.
  simpl in Hsd.
  lets Hks : Hsd (Z.to_nat (Int.intval i)).
  eapply good_inv_prop; eauto.
  apply (invp (I (S (S j)))).
  simpl substmo.
  left.
  unfold inv_ieon.
  sep split; auto.
  unfold invlth_isr.
  rewrite Hinum in *.
  replace (S j - 0)%nat with (S j) by omega.
  remember (Z.to_nat (Int.intval i)) as m.
  destruct m.
  unfold starinv_isr in Hon; fold starinv_isr in Hon.
  simpl in Hon.
  mytac.
  destruct H26.
  mytac.
  exists x x12 x17 x2 x16 x13.
  splits; eauto.
  simpl substmo.
  exists (isrupd x24 0%nat false).
  right.
  exists empmem x x empabst x2 x2.
  trysimplsall.
  splits; mytac;eauto.
  splits;simpl;mytac;eauto.
  eapply good_inv_prop; eauto.
  apply (invp (I 0%nat)).
  destruct (prec (I 0%nat)) as [Hp1 Hp2].
  destruct Hp2 as [Hp2 _ _ _].
  lets Hsd : Hp2 H3.
  eapply Hsd; eauto.
  simpl substmo.
  eapply starinv_isr_prop4.
  eapply inv_isr_prop ; eauto.
  simp join.
  tryfalse.
  lets Hisnum : sm_nat_exist Hle.
  destruct Hisnum as (k & Heqk).
  rewrite Heqk in *.
  assert (S (S k) = ((S m%nat) + (S (k-m)))%nat) by omega.
  rewrite H22 in *.
  lets Hres :  starinv_isr_prop_intro3  Hon.
  eapply starinv_isr_prop_elim.
  simpl in Hres.
  simp join.
  destruct H32.
  mytac.
  assert (exists k, join x18 k x17 /\ join x x19 k).
  clear -H21 H24.
  join auto.
  assert (exists k, join x21 k x13 /\ join x2 x22 k).
  clear -H18 H26.
  join auto.
  simp join.
  exists x18 x20 x17 x21 x10 x13.
  splits; eauto.
  simpl substmo.
  replace (S m) with (S( m + 0))%nat  in * by omega.
  eapply  starinv_isr_prop5; eauto.
  eapply inv_isr_prop; eauto.
  simpl substmo.
  exists x x19 x20 x2 x22 x10.
  splits; eauto.
  simpl.
  exists  (isrupd x30 (S m) false).
  right.
  exists empmem x x empabst x2 x2.
  splits; eauto.
  join auto.
  join auto.
  splits; eauto.
  splits; auto.
  unfolds.
  rewrite <- beq_nat_refl;auto.
  unfolds; auto.
  unfolds; auto.

  eapply good_inv_prop; eauto.
  apply (invp (I (S m))).
  destruct (prec(I (S m))) as [Hp1 Hp2].
  destruct Hp2 as [Hp2 _ _ _].
  lets Hsd : Hp2 H3.
  eapply Hsd; eauto.
  simpl substmo.
  eapply starinv_isr_prop4; eauto.
  eapply inv_isr_prop; eauto.
  simp join; tryfalse.
  lets Hks : Himp H9.
  assert (join x6 x5 x0) by join auto.
  eapply join_satp_local_inv with
    (o:=(x4, x7, x6, isrupd x10 (Z.to_nat (Int.intval i)) false, x11, (true, m :: is, cs)))
    (M:=x5) (O:=x3) (Of:=empabst); 
    [unfolds; join auto | join auto | idtac].
  eapply Linv_igore; eauto.
  unfolds.
  intros.
  eapply absinfer_sound2.local_inv_aop_irev; eauto.

  constructors; introv Hfalse; tryfalse.
  intros; invertstep idtac.
  inverts Hfalse.
  trysimplsall.
  introv Hds Hdss Hddss.
  exists aop OO0 x3 Os0. 
  splits; eauto.
  constructors.
  lets Hks : Himp H9.
  eapply join_satp_local_inv with
    (o:=(x4, x7, x6, isrupd x10 (Z.to_nat (Int.intval i)) false, x11, (true, m :: is, cs)))
    (M:=x5) (O:=x3) (Of:=empabst); 
    [unfolds; join auto | join auto | idtac].
  eapply Linv_igore; eauto.
  unfolds.
  intros.
  eapply absinfer_sound2.local_inv_aop_irev; eauto.
  unfold lift.
  sep split; simpl; auto.
  exists x5 x6 x0 empabst x3 x3.
  splits; auto. jeat.
  exists b; exists empmem x5 x5 empabst empabst empabst.
  splits; auto; jeat; auto; unfold emposabst; auto.
  eapply goodfrm_prop; eauto.
  subst m.
  auto.
  destruct Hfalse as (_ & _&Hfff&_).
  false.
  apply Hfff.
  eexists; eauto.
  unfold inv_ieoff in Hoff.
  sep split in Hoff.
  simpl in H; tryfalse.
  introv Hjj1 Hjj2 Hinv.
  introv Hstep.
  apply Hstep.
  destruct o2 as  [[[[]]]].
  do 2 eexists.
  unfold nilcont.
  eapply eoint_step; eauto.
  unfolds in Hjj2.
  unfold joinmem in Hjj2.
  simpljoin.
  eauto.
  assert(rule_type_val_match Tint32 (Vint32 id) = true) by auto.
  assert(Int.unsigned Int.zero = 0%Z) by auto.
  rewrite H1 in H14.
  lets Hloadv : mapstoval_load H H14.
  unfolds in Hjj2.
  unfold joinmem in Hjj2.
  simpljoin.
  assert(join x0 x x15) by join auto.
  lets Hj1 : join_join_merge23_join H5 H4.
  lets Hj2 : join_join_merge23_join Hj1 H11.
  lets Hj3 : join_join_merge23_join Hj2 H8.
  lets Hloadd : load_mono Hj3 Hloadv.
  rewrite Hloadv in Hloadd.
  auto.
Qed.

Lemma eoint_ieoff_rule_sound: 
  forall Spec sd I r ri isr ier is id vi i cs aop t P li,  
    0 <= Int.unsigned id < Z_of_nat INUM ->
    i = Z.to_nat (Int.unsigned id) ->  
    GoodFrm P -> 
    RuleSem Spec sd li I r ri 
            (<|| aop ||>  ** OS [isr, ier, false, i :: is, cs] ** 
              GV vi @ Tint32 |-r-> (Vint32 id) ** P)
            (sprim (eoint vi))
            ( <|| aop ||>  **
              OS [isrupd isr i false, ier, false, i :: is, cs] ** 
              GV vi @ Tint32 |-r-> (Vint32 id) ** P) t.
Proof.
  introv Hp1 Hp2 Hgood Hsat.
  unfold Int.unsigned in *.
  destruct Hsat as (Hsat1 & Hsat2).
  destruct o as [[[[[G E] M] iis] ierr] ax].
  destruct ax  as [[ie iss] css].
  sep split in Hsat1.
  simpl in H,H0,H1,H2,H3,H4.
  subst.
  simpl in Hsat1.
  simpljoin1.
  constructors; introv Hff; tryfalse.
  unfold nilcont.
  introv Hloststep Hinv Hjm1 Hjm2 Hstep.
  invertstep idtac.
  unfolds in Hjm1.
  unfold joinmem in Hjm1.
  simp join.
  assert(rule_type_val_match Tint32 (Vint32 id) = true) by auto.
  assert(Int.unsigned Int.zero = 0%Z) by auto.
  rewrite H6 in H9.
  lets Hloadv : mapstoval_load H H9.
  lets Hjm : join_join_merge23_join H0 H12.
  lets Hjm' : join_join_merge23_join Hjm H10.
  lets Hloadd : load_mono Hjm' Hloadv.
  rewrite H8 in H2; inverts H2.
  rewrite H3 in Hloadd; rewrite Hloadv in Hloadd.
  (* inverts Hloadd. *)
  assert(id=i) by congruence; subst; clear Hloadd.

  lets Hks : Hinv aop.
  simpl substaskst in *.
  remember (Z.to_nat (Int.intval i)) as m.
  unfold INV in Hks.
  unfold sat in Hks; fold sat in Hks.
  trysimplall.
  simp join.

  exists aop OO (x2, x3, x11, isrupd x6 (Z.to_nat (Int.unsigned i)) false, x7,
                 (false, Z.to_nat (Int.intval i) :: is, cs)).
  exists Ms O Os.
  splits; eauto.
  constructors.
  unfolds.
  unfold joinmem; jeat.
  simpl substaskst.
  unfolds.
  intros.
  unfold INV.
  exists x1 x8 Ms x10 x12 Os.
  splits; eauto.
  simpl substmo.
  eapply good_inv_prop; eauto.
  apply (invp (I (S INUM))).
  destruct (prec(I (S INUM))) as [Hp1 Hp2].
  destruct Hp2 as [Hp2 _ _ _].
  lets Hsd : Hp2 H16.
  eapply Hsd; eauto. 
  simpl substmo.
  right.
  destruct H17.
  unfold inv_ieon in H2.
  sep split in H2.
  simpl in H7; tryfalse.
  unfold inv_ieoff in *.
  sep split in H2.
  sep destruct H2.
  sep split in H2.
  sep split; auto.
  simpl in H17.
  subst x9.
  exists (Z.to_nat (Int.intval i)).
  destruct H2.
  sep split; auto.
  left.
  sep split in H2.
  sep split; auto.
  unfold invlth_isr in *.
  unfold Int.unsigned in *.
  remember (Z.to_nat (Int.intval i)) as m.
  replace (m+1)%nat with (S m) in * by omega.
  eapply starinv_isr_prop4; eauto.
  eapply inv_isr_prop; eauto.
  sep split; auto.
  right.
  sep split in H2.
  simpl in H2.
  simp join.
  simpl.
  splits; eauto.
  eapply Linv_igore; eauto.
  constructors; introv Hfalse; tryfalse.
  intros; invertstep idtac.
  inverts Hfalse.
  trysimplsall.
  introv Hds Hdss Hddss.
  exists aop OO0 O Os0. 
  splits; eauto.
  constructors.
  eapply Linv_igore; eauto.
  unfold lift.
  sep split; auto.
  simpl.
  exists x x0 x11 empabst O O; splits; auto.
  apply join_emp; reflexivity.
  exists b; exists empmem x x empabst empabst empabst; splits; auto.
  apply join_emp; reflexivity.
  apply join_emp; reflexivity.
  exists b; splits; auto.
  unfold emposabst; reflexivity.
  unfold emposabst; reflexivity.
  eapply goodfrm_prop; eauto.
  destruct Hfalse as (_ & _&Hfff&_).
  false.
  apply Hfff.
  eexists; eauto.
  introv Hjj1 Hjj2 Hinv.
  introv Hstep.
  apply Hstep.
  destruct o2 as [[[[[]]]]].
  do 2 eexists.
  unfold nilcont.
  eapply eoint_step; eauto.
  unfolds in Hjj2.
  unfold joinmem in Hjj2.
  simpljoin.
  eauto.
  assert(rule_type_val_match Tint32 (Vint32 id) = true) by auto.
  assert(Int.unsigned Int.zero = 0%Z) by auto.
  rewrite H1 in H9.
  lets Hloadv : mapstoval_load H H9.
  unfolds in Hjj2.
  unfold joinmem in Hjj2.
  simpljoin.
  lets Hj1 : join_join_merge23_join H0 H10.
  lets Hj2 : join_join_merge23_join Hj1 H6.
  lets Hloadd : load_mono Hj2 Hloadv.
  rewrite Hloadv in Hloadd.
  auto.
Qed.

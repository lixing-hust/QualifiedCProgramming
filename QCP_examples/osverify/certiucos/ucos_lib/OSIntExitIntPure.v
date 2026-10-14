Require Import ucos_include.
Require Import Lia.
Require Import oscore_common.
Require Import symbolic_lemmas.
Require Import ios_int. 

Import DeprecatedTactic.

Set Nested Proofs Allowed.
Lemma eq_true_equal:
  forall x y, Int.eq x y = true -> x = y.
Proof.
  intros; unfold Int.eq. case (Int.eq_dec x y); intro.
  apply e.
  apply Int.eq_false in n. rewrite n in H. discriminate H.
Qed.

Lemma simpl_inv_excrit'
: forall P i,
    Aisr empisr ** OSInv ** aemp_isr_is ** P ==>
         Aisr empisr ** invlth_isr I 0%nat i ** P.
Proof.
   intros.
   sep cancel 4%nat 3%nat.
   destruct i.

   unfold invlth_isr.
   unfold starinv_isr.
   rewrite NPeano.Nat.sub_0_r in *.
   unfold I in *.
   unfold getinv in *.

   sep normal in H; sep destruct H; sep split in H.
   sep split; auto.

   unfold sat. fold sat.
   sep lift 2%nat in H.
   destruct_s s; trysimplall; mytac.
   apply aemp_isr_elim in H.
   exists empisr.
   right.
   do 6 eexists; mytac; eauto.

   unfold invlth_isr.
   unfold starinv_isr.
   rewrite NPeano.Nat.sub_0_r in *.
   fold starinv_isr.
   unfold I in *.
   unfold getinv in *.
   sep normal in H; sep destruct H; sep split in H.
   sep split; auto.
   unfold sat in *; fold sat in *;
   destruct_s s; trysimplall; mytac.
   do 6 eexists;mytac;eauto.
   exists empisr.
   right.
   do 6 eexists;splits;eauto;mytac.
   unfolds. auto.
   fold starinv_isr.
   clear -H5.
   induction i.
   unfold starinv_isr.
   unfold getinv.
   unfold aemp_isr_is.
   exists empisr.
   right.
   unfold A_isr_is_prop.
   simpl in H5.
   mytac.

   do 6 eexists;splits;simpl;eauto;mytac.
   mytac.
   eauto.
   mytac.
   auto.
   do 6 eexists;splits;eauto;mytac.
   instantiate (1:=empmem).
  mytac.
  eauto.
  instantiate (1:=empabst).
  mytac.
  do 8 eexists;splits;eauto.
  mytac.
  join auto. join auto.
  mytac.
  do 6 eexists;splits;mytac.
  mytac.
  mytac.
  eauto.
  unfolds.
  unfold empisr.
  intros;auto.

  eapply starinv_prop1_rev.
  fold I in *.
  unfold starinv_isr at 2.
  simpl.
  do 6 eexists;splits;eauto;mytac.
  exists empisr.
  right.
  do 6 eexists;splits;eauto;mytac.
  mytac.
  mytac.
  unfold empisr;eauto.
  do 6 eexists;splits;eauto;mytac.
  mytac.
  mytac.
  do 8 eexists;splits;eauto;mytac.
  mytac.
  mytac.
  do 6 eexists;splits;eauto;mytac.
  mytac.
  eauto.
  unfolds.
  unfold empisr.
  intros;auto.
Qed.

Lemma A_isr_is_prop_elim':forall s P, s|=  A_isr_is_prop ** P -> s|=A_isr_is_prop ** A_isr_is_prop ** P.
  Proof.
    intros.
    sep cancel 2%nat 3%nat.
    unfold A_isr_is_prop in *.
    sep auto.
  Qed.
Lemma A_isr_is_prop_elim_help:forall s P, s|=  A_isr_is_prop ** A_isr_is_prop ** P -> s|=A_isr_is_prop  ** P.
  Proof.
    intros.
    sep cancel 2%nat 3%nat.
    unfold A_isr_is_prop in *.
    sep auto.
Qed.
Lemma A_isr_is_prop_elim:forall s P, s|=OSInv ** P -> s |= OSInv ** A_isr_is_prop ** P.
Proof.
  intros.
  sep cancel 2%nat 3%nat.
  unfold OSInv in *.
  sep normal in H.
  sep destruct H.
  sep normal.
  sep eexists.
  sep lifts (15::21::nil)%nat.
  eapply A_isr_is_prop_elim'.
  sep auto.
Qed.
Lemma A_isr_is_prop_elim'':forall s , s|=OSInv -> s |= OSInv ** A_isr_is_prop.
Proof.
  intros.
  unfold OSInv in *.
  sep normal in H.
  sep destruct H.
  sep normal.
  sep eexists.
  sep lifts (15::21::nil)%nat.
  eapply A_isr_is_prop_elim'.
  sep auto.
Qed.
Lemma A_isr_is_prop_elim''':forall s , s|=OSInv ** A_isr_is_prop -> s |= OSInv .
Proof.
  intros.
  unfold OSInv in *.
  sep normal in H.
  sep destruct H.
  sep normal.
  sep eexists.
  sep lifts (15::21::nil)%nat in H.
  eapply A_isr_is_prop_elim_help in H.
  sep auto.
Qed.
Lemma A_isr_is_prop_elim'''':forall s P , s|=OSInv ** A_isr_is_prop ** P -> s |= OSInv ** P.
Proof.
  intros.
  sep cancel 3%nat 2%nat.
  unfold OSInv in *.
  sep normal in H.
  sep destruct H.
  sep normal.
  sep eexists.
  sep lifts (15::21::nil)%nat in H.
  eapply A_isr_is_prop_elim_help in H.
  sep auto.
Qed.
Lemma atopis_eq:
forall s i x si P,
  s |= ATopis x ** Ais (i :: si) ** P -> x= i.
Proof.
  intros.
  destruct_s s.
  simpl in H.
  mytac.
  simpl;auto.
Qed.
Lemma  xxx: forall m s P X x0,
                  (forall j : nat, (0 <= j < 2)%nat -> getisr (gettaskst s) j = false) ->
                  (m<2)%nat ->
                  s |= (([|x0 m%nat = true|] //\\
                                             Aisr x0) \\//
                                                      ([|x0 m%nat = false|] //\\
                                                                            Aisr x0) ** X) ** P ->
                  s |= X ** P.
    Proof.
      intros.
      destruct_s s.
      simpl in *;mytac.
      destruct H5;mytac.
      assert (0 <= m < 2)%nat by omega.
      apply H in H2.
      tryfalse.
      do 6 eexists;splits;eauto;mytac.
Qed.
Lemma invlth_isr_invlth_isr'_imp:
  forall s x si P i,
    s|=ATopis x ** invlth_isr I 0%nat x ** Ais (i::si) ** isrclr ** P ->
    s|=OSInv **  aemp_isr_is **  Ais (i::si) ** Aisr empisr ** P.
Proof.
  intros.
  sep lift 4%nat in H.
  apply isrclr_imp in H.
  
  sep lifts (2::4::nil)%nat in H.
  lets Hx:atopis_eq H.
  subst x.
  apply astar_l_atopis_elim in H.
  destruct H.
  sep cancel 4%nat 5%nat.
  destruct i.
  unfold invlth_isr in *.
  unfold starinv_isr in *.
  rewrite NPeano.Nat.sub_0_r in *.
  unfold I in *.
  unfold getinv in *.

  sep normal in H0; sep destruct H0; sep split in H0.
  sep split; auto.
  destruct H0.
  simpl in H0.
  mytac.
  rewrite H3 in H0.
  unfold empisr ;tryfalse.
  sep normal in H0.
  unfold aemp_isr_is. 
  sep normal.
  eapply A_isr_is_prop_elim''.
  remember OSInv as X.
  clear HeqX.
  destruct_s H1.
  unfold sat in *; fold sat in *;
  destruct_s s; trysimplall; mytac.
  auto.

  unfold invlth_isr in H0.
  unfold starinv_isr in H0.
  rewrite NPeano.Nat.sub_0_r in *.
  fold starinv_isr in H0.
  unfold I in *.
  unfold getinv in *.
  sep lift 3%nat in H0.
  sep normal in H0.
  sep destruct H0.
  apply xxx in H0;auto.
  Focus 2.
  sep split in H0.
  intros.
  rewrite H3.
  unfolds;auto.
  eapply astar_mono.
  intros;eauto.
  2:exact H0.
  intros.
  clear -H2.
  sep cancel 1%nat 2%nat.
  destruct_s s0.
  sep split in H2.
  simpl in H.
  subst.
  sep split.
  2:simpl;auto.
  induction i.
  unfold starinv_isr in *.
  unfold getinv in *.
  simpl in H2.
  mytac.
  destruct H.
  mytac.
  unfolds in H;tryfalse.
  mytac.
  simpl.
  do 6 eexists;splits;eauto;mytac.
  mytac.
  mytac.
  do 8 eexists;splits;eauto;mytac.
  mytac.
  mytac.
  do 6 eexists;splits;eauto;mytac.
  mytac.
  apply IHi.
  clear IHi.
  
  apply starinv_prop1 in H2.
  sep cancel 1%nat 1%nat.
  simpl in H2.
  mytac.
  destruct H0.
  mytac.
  simpl;auto.
  destruct_s H.
  mytac;simpl in *.
  mytac.
Qed.
Lemma elim_a_isr_is_prop': forall isr is s P , isr_is_prop isr is -> s |= Aisr isr **
                                                                      Ais is **
                                                                      A_isr_is_prop ** P -> s|= Aisr isr ** Ais is ** P .
Proof.
  intros.
  unfold A_isr_is_prop in H0.
  sep auto.
Qed.

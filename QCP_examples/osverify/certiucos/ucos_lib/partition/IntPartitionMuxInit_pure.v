Require Import include_frm.
Require Import os_code_defs.
Require Import code_notations.
Require Import seplog_trm_tacs.
Require Import inv_prop.
Require Import pure_lib.
Require Import int_auto.
Require Import os_inv.
Require Import inline_bittblfunctions.
Require Import partition_aux_code.

Local Open Scope code_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Lemma IntPartMux_P_split:
  forall n vl1 vl2 v1 v2, 
  IntPartMux_P (Z.of_nat n) vl1 vl2 -> 
  nth_val ∘ (Z.of_nat n) vl1 = Some v1 ->
  nth_val ∘ (Z.of_nat n) vl2 = Some v2 -> 
  Some v1 = Some v2 -> 
  IntPartMux_P (Z.of_nat (S n)) vl1 vl2.
Proof.
  unfold IntPartMux_P.
  intros.
  assert (Hcond: 0 <= i < Z.of_nat n \/ i = Z.of_nat n).
  clear -H3.
  assert (Hc: i = Z.of_nat n \/ i <> Z.of_nat n) by tauto.
  destruct Hc; auto.
  left.
  auto with zarith.
  destruct Hcond as [Hc1 | Hc2].
  eapply H with (v1 := v0) in Hc1; eauto.
  subst.
  rewrite H0 in H4.
  rewrite H1 in H5.
  rewrite <- H4.
  rewrite <- H5.
  eauto.
Qed.

Lemma IntPartMux_P_succ_split:
  forall n vl1 vl2, 
  IntPartMux_P (Z.of_nat n) vl1 vl2 -> 
  (Z.of_nat n < 11) ->
  length vl1 = ∘ 11 ->
  IntPartMux_P (Z.of_nat (S n)) vl1 (update_nth_val (Z.to_nat (Int.unsigned ($ Z.of_nat n))) vl2
     (nth_val' (Z.to_nat (Int.unsigned ($ Z.of_nat n))) vl1)).
Proof.
  unfold IntPartMux_P.
  intros.
  assert ((Int.unsigned ($ Z.of_nat n)) = Z.of_nat n).
  {
   eapply int_usign_eq. 
   auto with zarith.
   unfold Int.max_unsigned, Int.modulus; simpl.
   auto with zarith.
  }
  assert (Hcond: 0 <= i < Z.of_nat n \/ i = Z.of_nat n).
  clear -H2.
  int auto.
  destruct Hcond as [Hc1 | Hc2].
  eapply H with (v1 := v1) in Hc1; eauto.
  eapply nth_upd_neq.
  instantiate (1:=(Z.to_nat (Int.unsigned ($ Z.of_nat n)))).
  rewrite H5.
  unfold nat_of_Z.
  eapply Nat.lt_neq.
  eapply Z2Nat.inj_lt.
  auto with zarith.
  auto with zarith.
  auto with zarith.
  instantiate (1:=(nth_val' (Z.to_nat (Int.unsigned ($ Z.of_nat n))) vl1)).
  eauto.
  subst.
  rewrite <- H3.
  eapply nth_val'_imply_nth_val.
  rewrite H1.
  unfold nat_of_Z.
  eapply Z2Nat.inj_lt.
  auto with zarith.
  auto with zarith.
  auto with zarith.
  eapply nth_upd_eq.
  instantiate (1:=vl2).
  instantiate (1:=∘ (Z.of_nat n)).
  assert ((Z.to_nat (Int.unsigned ($ Z.of_nat n))) = ∘ (Z.of_nat n)).
  unfold nat_of_Z.
  rewrite Z2Nat.inj_iff.
  eauto.
  rewrite H5.
  auto with zarith.
  auto with zarith.
  rewrite H6 in H4.
  eauto.
Qed.

Lemma set_idm_to_ipm_alt :
  forall n vls1 vls2 b b2,
  (Z.of_nat (S n)) <= Int.max_unsigned ->
  get vls1 ($ (Z.of_nat (S n))) = Some b ->
  get vls2 ($ (Z.of_nat (S n))) = Some b2 ->
  set_idm_to_ipm (S n) vls2 vls1 =
  set (set_idm_to_ipm n vls2 vls1) ($ (Z.of_nat (S n))) b2.
Proof.
  unfold get,set. simpl.
  induction n.
  simpl.
  intros.
  rewrite H1.
  destruct (IntrDomMod.get vls2 ($ 0)) eqn: eq1.
  unfold set. simpl.
  eauto.
  eauto.
  intros.
  destruct (IntrDomMod.get vls2 ($ Z.pos (Pos.of_succ_nat (S n)))) eqn: eq1.
  inverts H1.
  eauto.
  inverts H1.
Qed.

Lemma set_idm_to_ipm_get_same_n:
  forall n vls1 vls2 b b2,
  (Z.of_nat n) <= Int.max_unsigned ->
  get vls1 ($ (Z.of_nat n)) = Some b ->
  get vls2 ($ (Z.of_nat n)) = Some b2 ->
  get (set_idm_to_ipm n vls2 vls1) ($ (Z.of_nat n)) = get vls2 ($ (Z.of_nat n)).
Proof.
  unfold get. simpl.
  induction n.
  simpl.
  intros.
  rewrite H1.
  rewrite IntPMuxMod.map_get_set.
  eauto.
  intros.
  simpl.
  simpl in H0, H1.
  rewrite H1.
  change ($ Z.pos (Pos.of_succ_nat n)) with ($ Z.of_nat (S n)) in *.
  rewrite IntPMuxMod.map_get_set.
  eauto.
Qed.

Lemma set_idm_to_ipm_get:
  forall n i vls1 vls2 b b2,
  (i <= n)%nat ->
  (Z.of_nat n) <= Int.max_unsigned ->
  get vls1 ($ (Z.of_nat i)) = Some b ->
  get vls2 ($ (Z.of_nat i)) = Some b2 ->
  IntPMuxMod.get (set_idm_to_ipm n vls2 vls1) ($ (Z.of_nat i)) =
  get vls2 ($ (Z.of_nat i)).
Proof.
  induction n.
  intros.
  assert(Ht0: (i < 0)%nat \/ (i = 0)%nat).
  auto with zarith.
  destruct Ht0 as [Ht0 | Ht0].
  false.
  auto with zarith.
  inverts Ht0.
  eapply set_idm_to_ipm_get_same_n; eauto.
  intros.
  assert(Htsn: (i <= n)%nat \/ (i = S n)%nat).
  eapply Nat.le_succ_r in H;
  destruct H;
  auto with zarith.
  destruct Htsn as [Htsn | Htsn].
  assert (Htn: (i < n)%nat \/ (i = n)%nat).
  eapply NPeano.Nat.lt_eq_cases; eauto.
  destruct Htn as [Htn | Htn].
  simpl set_idm_to_ipm.
  destruct (IntrDomMod.get vls2 ($ Z.pos (Pos.of_succ_nat n))) eqn: eq1.
  rewrite IntPMuxMod.map_get_set'; eauto.
  assert (Z.of_nat n <= Int.max_unsigned) by auto with zarith.
  eapply IHn in Htsn; eauto.
  introv Hf.
  eapply Int.repr_eq_unsigned in Hf; eauto.
  rewrite <- Hf in *.
  auto with zarith.
  split; auto with zarith.
  split; auto with zarith.
  eapply IHn; eauto.
  auto with zarith.

  subst.
  simpl set_idm_to_ipm.
  destruct (IntrDomMod.get vls2 ($ Z.pos (Pos.of_succ_nat n))) eqn: eq1.
  change ($ Z.pos (Pos.of_succ_nat n)) with ($ Z.of_nat (S n)) in *. 
  rewrite IntPMuxMod.map_get_set'.
  assert ((Z.of_nat n) <= Int.max_unsigned). 
  auto with zarith.
  eapply set_idm_to_ipm_get_same_n; eauto.
  introv Hf.
  eapply Int.repr_eq_unsigned in Hf; eauto.
  rewrite <- Hf in *.
  auto with zarith.
  split; auto with zarith.
  split; auto with zarith.
  assert ((Z.of_nat n) <= Int.max_unsigned). 
  auto with zarith.
  eapply set_idm_to_ipm_get_same_n; eauto.

  subst.
  eapply set_idm_to_ipm_get_same_n; eauto.
Qed.

Lemma set_idm_to_ipm_get_none:
  forall n i vls1 vls2,
  ~(0 <= (Z.of_nat i) <= Z.of_nat n) ->
  Z.of_nat i <= Int.max_unsigned ->
  (Z.of_nat n) <= Int.max_unsigned ->
  get vls1 ($ (Z.of_nat i)) = None ->
  get vls2 ($ (Z.of_nat i)) = None ->
  IntPMuxMod.get (set_idm_to_ipm n vls2 vls1) ($ (Z.of_nat i)) = None.
Proof.
  induction n.
  intros.
  simpl set_idm_to_ipm.
  destruct (IntrDomMod.get vls2 ($ 0)) eqn: eq1.
  rewrite IntPMuxMod.map_get_set'. eauto.

  rewrite Nat2Z.inj_0 in H.
  assert (0 <= Z.of_nat i <= 0 <-> 0 = Z.of_nat i).
  { split. intros.
    eapply ZMicromega.eq_le_iff in H4. 
    auto with zarith.
    intros.
    eapply ZMicromega.eq_le_iff.
    auto with zarith.
  }
  rewrite H4 in H.

  introv Hf.
  eapply Int.repr_eq_unsigned in Hf; eauto.
  auto with zarith.
  int auto.
  
  eauto.

  intros.
  simpl set_idm_to_ipm.
  destruct (IntrDomMod.get vls2 ($ Z.pos (Pos.of_succ_nat n))) eqn: eq1.
  rewrite IntPMuxMod.map_get_set'.
  eapply IHn; eauto.
  auto with zarith.
  auto with zarith.

  introv Hf.
  eapply Int.repr_eq_unsigned in Hf; eauto.
  rewrite <- Hf in *.
  auto with zarith.
  split; auto with zarith.
  auto with zarith.
  eapply IHn; eauto.
  auto with zarith.
  auto with zarith.
Qed.

Lemma RLH_IntPartMux_P_succ_split:
  forall intrvl vl1 vl2 vls1 vls2,
  RHL_IntPartMux_P vl1 vls1 ->
  length intrvl = Pos.to_nat 11 ->
  IntPartMux_P 11 intrvl vl2 ->
  RHL_intrDomainMux_P intrvl vls2 ->
  RLH_IntPartMux_P vl2 (set_idm_to_ipm (Z.to_nat (USER_INT_MAX_N - 1)) vls2 vls1).
Proof.
  intros.
  unfold RHL_intrDomainMux_P in *.
  unfold RLH_IntPartMux_P.
  unfold IntPartMux_P in *.
  unfold RHL_IntPartMux_P in *.
  destruct H.
  destruct H2.
  splits; introv Hi; try introv Hnth. 
  unfold USER_INT_MAX_N in *.
  change (Z.to_nat (11 - 1)) with 10%nat.
  lets Hlem: set_idm_to_ipm_get 10%nat (Z.to_nat(Int.unsigned i)).
  rewrite Z2Nat.id in Hlem.
  rewrite Int.repr_unsigned in Hlem.
  2:{ destruct Hi; auto. }
  destruct (get vls1 i) eqn:eq1.
  2:{ eapply H3 in eq1. tryfalse. }
  destruct (get vls2 i) eqn:eq2.
  2:{ eapply H2 in eq2. tryfalse. }
  lets Hget: H4 eq2.
  destruct Hget as (_ & Hnth').
  eapply H1 in Hnth'; eauto.
  inverts Hnth'.
  rewrite <- eq2.
  eapply Hlem; eauto.
  change (Z.to_nat (Int.unsigned i) <= 10)%nat with 
         (Z.to_nat (Int.unsigned i) <= (Z.to_nat (Z.of_nat 10)))%nat.
  eapply Zle_natle. 
  auto with zarith.
  unfold Int.max_unsigned, Int.modulus; simpl.
  auto with zarith.

  unfold USER_INT_MAX_N in *.
  change (Z.to_nat (11 - 1)) with 10%nat.
  lets Hlem: set_idm_to_ipm_get_none 10%nat (Z.to_nat(Int.unsigned i)).
  rewrite Z2Nat.id in Hlem.
  rewrite Int.repr_unsigned in Hlem.
  2: { int auto. }
  eapply Hlem; eauto.
  auto with zarith.
  int auto.
  int auto.

  destruct (get vls1 i) eqn:eq1; auto.
  eapply H in eq1. 
  destruct eq1.
  tryfalse.
  destruct (get vls2 i) eqn:eq2; auto.
  eapply H4 in eq2.
  destruct eq2.
  tryfalse.
Qed.

Lemma RHL_IntPartMux_P_succ_split:
  forall intrvl vl1 vl2 vls1 vls2,
  RHL_IntPartMux_P vl1 vls1 -> 
  length intrvl = Pos.to_nat 11 ->
  array_type_vallist_match char_t vl2 ->
  length vl2 = ∘ USER_INT_MAX_N ->
  IntPartMux_P 11 intrvl vl2 ->
  RHL_intrDomainMux_P intrvl vls2 ->
  RHL_IntPartMux_P vl2 (set_idm_to_ipm (Z.to_nat (USER_INT_MAX_N - 1)) vls2 vls1).
Proof.
  intros.
  unfold RHL_IntPartMux_P in H.
  unfold RHL_intrDomainMux_P in H4.
  unfold IntPartMux_P in H3.
  destruct H, H4.
  splits; introv Hi. 
  unfold USER_INT_MAX_N in *.
  change (Z.to_nat (11 - 1)) with 10%nat in Hi.
  
  assert (0 <= Int.unsigned i < 11).
  destruct (get vls1 i) eqn:eq1.
  eapply H in eq1.
  destruct eq1; auto.
  destruct (get vls2 i) eqn:eq2.
  eapply H6 in eq2.
  destruct eq2; auto.
  
  lets Hget: H4 eq2.
  lets Hlem: set_idm_to_ipm_get_none 10%nat (Z.to_nat(Int.unsigned i)).
  rewrite Z2Nat.id in Hlem.
  rewrite Int.repr_unsigned in Hlem.
  eapply Hlem in eq2; eauto.
  rewrite eq2 in Hi; tryfalse.
  auto with zarith.
  int auto. 
  int auto.
  int auto.
  
  split; auto.
  destruct (get vls1 i) eqn:eq1.
  2:{ eapply H5 in eq1. tryfalse. }
  destruct (get vls2 i) eqn:eq2.
  2:{ eapply H4 in eq2. tryfalse. }
  lets Hlem: set_idm_to_ipm_get 10%nat (Z.to_nat(Int.unsigned i)).
  rewrite Z2Nat.id in Hlem.
  rewrite Int.repr_unsigned in Hlem.
  lets Hcp: eq2.
  eapply Hlem in Hcp; eauto.
  rewrite Hi in Hcp.
  unfold get in eq2,Hcp. simpl in eq2, Hcp.
  rewrite eq2 in Hcp.
  inverts Hcp.
  eapply H6 in eq2.
  destruct eq2.

  eapply nthval'_has_value with (n := Z.to_nat (Int.unsigned i)) in H1; eauto.
  destruct H1 as (x & Hnth & Hr).
  eapply H3 in H9; eauto.
  2: { eapply nth_val'2nth_val; eauto. }
  inverts H9.
  eapply nth_val'2nth_val; eauto.
  unfold nat_of_Z.
  auto with zarith.
  auto with zarith.
  int auto.
  int auto.

  unfold USER_INT_MAX_N in *.
  change (Z.to_nat (11 - 1)) with 10%nat in Hi.
  destruct (get vls1 i) eqn:eq1.
  destruct (get vls2 i) eqn:eq2.
  lets Hrgn: eq2.
  eapply H6 in Hrgn.
  destruct Hrgn as (Hrgn & _).
  lets Hlem: set_idm_to_ipm_get 10%nat (Z.to_nat(Int.unsigned i)).
  rewrite Z2Nat.id in Hlem.
  rewrite Int.repr_unsigned in Hlem.
  lets Hcp: eq2.
  eapply Hlem in Hcp; eauto.
  rewrite Hi in Hcp.
  unfold get in eq2,Hcp. simpl in eq2, Hcp.
  rewrite eq2 in Hcp.
  inverts Hcp.
  auto with zarith.
  auto with zarith.
  int auto.
  int auto.
  
  eapply H4; eauto.
  eapply H5; eauto.
Qed.

Require Import include_frm.
Require Import base_tac.
Require Import sep_auto.
Require Import os_code_defs.
Require Import os_ucos_h.
Require Import ios_int.
Require Import Integers.
Require Import Lia.
Require Import tv_match.
(*Require Import zh_lemmas.*)

Require Import evt_spec_defs. 
Require Import ios_cap_defs.
Set Nested Proofs Allowed.

(*-----------------------------------------------------------------------------------*)
(* low level data struct assertion used in os_tcb                                    *)
(*-----------------------------------------------------------------------------------*)
(* tcb vallist *)
Definition V_OSTCBNext     (vl:vallist) := nth_val 0 vl.
Definition V_OSTCBPrev     (vl:vallist) := nth_val 1 vl.
Definition V_OSTCBEventPtr (vl:vallist) := nth_val 2 vl.
Definition V_OSTCBMsg      (vl:vallist) := nth_val 3 vl.
Definition V_OSTCBDly      (vl:vallist) := nth_val 4 vl.
Definition V_OSTCBStat     (vl:vallist) := nth_val 5 vl.
Definition V_OSTCBPrio     (vl:vallist) := nth_val 6 vl.
Definition V_OSTCBX        (vl:vallist) := nth_val 7 vl.
Definition V_OSTCBY        (vl:vallist) := nth_val 8 vl.
Definition V_OSTCBBitX     (vl:vallist) := nth_val 9 vl.
Definition V_OSTCBBitY     (vl:vallist) := nth_val 10 vl.
Definition V_OSTCBflag     (vl:vallist) := nth_val 11 vl.

Open Scope code_scope.
Definition OS_TCB_flag : type := 
  STRUCT os_tcb_flag ­{
                  ⌞OSTCBNext @ STRUCT os_tcb ⋆;
                  OSTCBPrev @ STRUCT os_tcb ⋆ ;
                  OSTCBEventPtr @ OS_EVENT ∗ ; 
                  OSTCBMsg @ Void ∗ ;
                  OSTCBDly @ Int16u ;
                  OSTCBStat @ Int16u ;
                  OSTCBPrio @ Int8u ;
                  OSTCBX @ Int8u ;
                  OSTCBY @ Int8u ; 
                  OSTCBBitX @ Int8u;
                  OSTCBBitY @ Int8u
                  (*OSTCBMutexOwn @ OS_EVENT ∗*) ⌟
         }­.

Close Scope code_scope.

Open Scope Z_scope.
Open Scope int_scope.

Lemma join_sig_eq_auto :
  forall (A B T : Type) (MC : PermMap A B T) l a b m1 m2 m3 x1 x2,
    usePerm = true ->
    isRw a = false ->
    isRw b = false ->
    join (sig l a) x1 m1 ->
    join (sig l b) x2 m2 ->
    join m1 m2 m3 ->
    a = b.
  intros.
  let i := calc_ins_for_context in
  infer' i l; crush.
Qed.  
  
Lemma join_sig_eq :
  forall l a b m1 m2 m3 x1 x2,
    join (sig l (false, a)) x1 m1 ->
    join (sig l (false, b)) x2 m2 ->
    join m1 m2 m3 ->
    a = b.
  intros.
  assert ((false, a) = (false, b)).
  {
    eapply join_sig_eq_auto; ica.
  }
  inverts H2; auto.
Qed.  

Lemma ptomvallistr_disjoint_vl_eq :
  forall vl1 vl2 l m1 m2 m3,
    ptomvallist l false vl1 m1 ->
    ptomvallist  l  false  vl2 m2 ->
    length vl1 = length vl2 ->
    join m1 m2 m3 ->
    vl1 = vl2.
Proof.
  inductions vl1; intros.
  destruct vl2; auto.
  simpl in H1; inversion H1.

  destruct vl2.
  simpl in H1; inversion H1.

  simpl in H1; inverts H1.
  simpl in H; destruct l.

  do 3 destruct H; destruct H1.
  simpl in H0; do 3 destruct H0; destruct H5.

  unfold ptomval in H1, H5; substs.
  assert(a = m).
  eapply join_sig_eq; eauto.

  substs.
  assert(vl1 = vl2).
  assert(exists mx, join x0 x2 mx).
  geat.
  destruct H1.
  apply IHvl1 with (m1:=x0) (m2:=x2) (m3:=x) (l:=(b,o+1)); auto.
  substs; auto.
Qed.

Lemma join_sig_false_sig_true_auto :
  forall (A B T : Type) (MC : PermMap A B T) l a m1 m2 m x1 x2 x,
    usePerm = true ->
    isRw a = false ->
    join m1 m2 m ->
    join (sig l a) x1 m1 ->
    join (sig l a) x2 m2 ->
    join x1 x2 x ->
    join (sig l (flip a)) x m.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed.
  
Lemma join_sig_false_sig_true :
  forall l a m1 m2 m x1 x2 x,
    join m1 m2 m ->
    join (sig l (false, a)) x1 m1 ->
    join (sig l (false, a)) x2 m2 ->
    join x1 x2 x ->
    join (sig l (true, a)) x m.
Proof.
  intros.
  change (join (sig l (flip (false, a))) x m).
  eapply join_sig_false_sig_true_auto; ica.
Qed.
  
Lemma ptomvallistr_ptomvallist :
  forall vl l m1 m2 m3,
    ptomvallist l false vl m1 ->
    ptomvallist l false vl m2 ->
    join m1 m2 m3 ->
    ptomvallist l true  vl m3.
Proof.
  inductions vl; intros.
  simpl in *; substs.
  geat.

  destruct l.
  unfold ptomvallist in H, H0; fold ptomvallist in H, H0.
  do 3 destruct H; destruct H2.
  do 3 destruct H0; destruct H4.
  unfold ptomval  in *.
  
  substs.
  assert(exists m, join x0 x2 m).
  geat.
  destruct H2.
  unfold ptomvallist; fold ptomvallist.
  exists (sig (b, o) (true, a)) x.
  split.

  eapply join_sig_false_sig_true; eauto.
  split.
  unfolds; auto.
  lets Hx: IHvl H3 H5 H2; auto.
Qed.

Lemma byte_repr_int_unsigned_eq :
  forall i1 i2,
    Int.unsigned i1 <= Byte.max_unsigned ->
    Int.unsigned i2 <= Byte.max_unsigned ->
    Byte.repr (Int.unsigned i1) = Byte.repr (Int.unsigned i2) ->
    i1 = i2.
Proof.
  intros.
  assert(Byte.unsigned (Byte.repr (Int.unsigned i1)) = Byte.unsigned (Byte.repr (Int.unsigned i2))).
  rewrite H1; auto.
  do 2 rewrite Byte.unsigned_repr in H2.
  assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i2)).
  rewrite H2; auto.
  do 2 rewrite Int.repr_unsigned in H3.
  auto.
  split; auto.
  pose proof Int.unsigned_range i2.
  destruct H3; auto.
  split; auto.
  pose proof Int.unsigned_range i1.
  destruct H3; auto.
  split; auto.
  pose proof Int.unsigned_range i1.
  destruct H3; auto.
Qed.

Lemma byte_repr_eq :
  forall z1 z2,
    0 <= z1 <= Byte.max_unsigned ->
    0 <= z2 <= Byte.max_unsigned ->
    Byte.repr z1 = Byte.repr z2 ->
    z1 = z2.
Proof.
  intros.
  assert(Byte.unsigned (Byte.repr z1) = Byte.unsigned (Byte.repr z2)).
  rewrite H1; auto.
  do 2 rewrite Byte.unsigned_repr in H2; auto.
Qed.

Lemma div_256_byte_repr_eq :
  forall z1 z2,
    z1 / 256 = z2 / 256 ->
    Byte.repr z1 = Byte.repr z2 ->
    z1 = z2.
Proof.
  intros.
  assert (Byte.unsigned (Byte.repr z1) = Byte.unsigned (Byte.repr z2)).
  rewrite H0; auto.
  do 2 rewrite Byte.unsigned_repr_eq in H1.
  unfold Byte.modulus in H1.
  unfold two_power_nat in H1; simpl in H1.
  clear H0.
  assert(256 <> 0) by lia.
  pose proof Z.div_mod z1 256 H0.
  pose proof Z.div_mod z2 256 H0.
  rewrite H in H2.
  rewrite H1 in H2.
  rewrite <- H2 in H3.
  auto.
Qed.

Lemma z_le_int16_max_div_256_byte_max :
  forall z,
    z <= Int16.max_unsigned ->
    z / 256  <= Byte.max_unsigned.
Proof.
  intros.
  unfold Int16.max_unsigned in H.
  simpl in H.
  unfold Byte.max_unsigned; simpl.
  
  replace 255 with (65535 / 256).
  apply Z.div_le_mono.
  lia.
  auto.
  compute; auto.
Qed.

Lemma zero_le_int_unsigned_div_256 :
  forall i,
    0 <= Int.unsigned i / 256.
Proof.
  intros.
  pose proof Int.unsigned_range i.
  destruct H.
  replace 0 with (0 / 256).
  apply Z.div_le_mono.
  lia.
  auto.
  compute; auto.
Qed.

Lemma zero_le_int_unsigned_div_256_256_256 :
  forall i,
    0 <= Int.unsigned i / 256 / 256 / 256.
Proof.
  intros.
  pose proof Int.unsigned_range i.
  destruct H.
  replace 0 with (0 / 256 / 256 / 256).
  apply Z.div_le_mono.
  lia.
  apply Z.div_le_mono.
  lia.
  apply Z.div_le_mono.
  lia.
  auto.
  compute; auto.
Qed.

Lemma z_le_int_max_div_256_256_256_byte_max :
  forall z,
    z <= Int.max_unsigned ->
    z / 256 / 256 / 256 <= Byte.max_unsigned.
Proof.
  intros.
  unfold Int.max_unsigned in H.
  simpl in H.
  unfold Byte.max_unsigned; simpl.
  
  replace 255 with (4294967295 / 256 / 256 / 256).
  apply Z.div_le_mono.
  lia.
  apply Z.div_le_mono.
  lia.
  apply Z.div_le_mono.
  lia.
  auto.
  compute; auto.
Qed.

Lemma rule_type_val_match_encode_val_eq :
  forall t v1 v2,
    rule_type_val_match t v1 = true ->
    rule_type_val_match t v2 = true ->
    encode_val t v1 = encode_val t v2 ->
    v1 = v2.
Proof.
  intros.
  destruct t, v1, v2;
    simpl in H, H0; tryfalse;
    auto;
    simpl in H1; try solve [destruct a; tryfalse]; try solve [destruct a0; tryfalse]; tryfalse.
  remember(Byte.repr (Int.unsigned i)) as X;
    remember(Byte.repr (Int.unsigned i0)) as Y.
  inversion H1; substs.
  
  destruct (Int.unsigned i <=? Byte.max_unsigned) eqn : eq1; tryfalse.
  destruct (Int.unsigned i0 <=? Byte.max_unsigned) eqn : eq2; tryfalse.    
  apply byte_repr_int_unsigned_eq in H3; substs; auto.
  apply Z.leb_le in eq1.
  auto.
  apply Z.leb_le in eq2.
  auto.

  remember (Byte.repr (Int.unsigned i)) as X1.
  remember (Byte.repr (Int.unsigned i / 256)) as X2.
  remember (Byte.repr (Int.unsigned i0)) as Y1.
  remember (Byte.repr (Int.unsigned i0 / 256)) as Y2.
  inverts H1; substs.

  destruct (Int.unsigned i <=? Int16.max_unsigned) eqn : eq1; tryfalse.
  destruct (Int.unsigned i0 <=? Int16.max_unsigned) eqn : eq2; tryfalse.
  apply Z.leb_le in eq1.
  apply Z.leb_le in eq2.
  
  apply byte_repr_eq in H3.

  assert(Int.unsigned i = Int.unsigned i0).
  eapply div_256_byte_repr_eq; eauto.
  assert(Int.repr (Int.unsigned i) = Int.repr (Int.unsigned i0)).
  rewrite H1; auto.
  do 2 rewrite Int.repr_unsigned in H4.
  substs; auto.
  
  split.
  apply zero_le_int_unsigned_div_256; auto.
  apply z_le_int16_max_div_256_byte_max; auto.

  split.
  apply zero_le_int_unsigned_div_256; auto.
  apply z_le_int16_max_div_256_byte_max; auto.

  remember (Byte.repr (Int.unsigned i)) as X1.
  remember (Byte.repr (Int.unsigned i / 256)) as X2.
  remember (Byte.repr (Int.unsigned i / 256 / 256)) as X3.
  remember (Byte.repr (Int.unsigned i / 256 / 256 / 256)) as X4.    
  remember (Byte.repr (Int.unsigned i0)) as Y1.
  remember (Byte.repr (Int.unsigned i0 / 256)) as Y2.
  remember (Byte.repr (Int.unsigned i0 / 256 / 256)) as Y3.
  remember (Byte.repr (Int.unsigned i0 / 256 / 256 / 256)) as Y4.
  inverts H1; substs.

  apply byte_repr_eq in H5.
  lets Hx: div_256_byte_repr_eq H5 H4.
  lets Hx1: div_256_byte_repr_eq Hx H3.
  lets Hx2: div_256_byte_repr_eq Hx1 H2.
  assert(Int.repr (Int.unsigned i) = Int.repr (Int.unsigned i0)).
  rewrite Hx2; auto.
  do 2 rewrite Int.repr_unsigned in H1; substs; auto.

  split.
  apply zero_le_int_unsigned_div_256_256_256.

  apply z_le_int_max_div_256_256_256_byte_max; auto.
  apply Int.unsigned_range_2.

  split.
  apply zero_le_int_unsigned_div_256_256_256.
  apply z_le_int_max_div_256_256_256_byte_max; auto.
  apply Int.unsigned_range_2.

  destruct a; destruct a0;
  inverts H1; substs; auto.
  destruct a; destruct a0;
  inverts H1; substs; auto.
Qed.

(******************************************************************************)
(** ugly begin **)
(** paste from inv_prop, in order to proof node_OS_TCB_dup_false **)
Ltac simpl_map1 :=
  match goal with
    | H:exists _, _ |- _ => destruct H; simpl_map1
    | H:_ /\ _ |- _ => destruct H; simpl_map1

    | H: emposabst _ |- _ => unfold emposabst in H; subst; simpl_map1

    | H:join empenv _ _ |- _ => apply map_join_comm in H; apply map_join_emp' in H; subst; simpl_map1
    | H:join _ empenv _
      |- _ =>
      apply map_join_emp' in H; subst; simpl_map1
    | |- join empenv _ _ => apply map_join_comm; apply map_join_emp; simpl_map1
    | |- join _ empenv _ => apply map_join_emp; simpl_map1
    | H:join ?a ?b ?ab |- join ?b ?a ?ab => apply map_join_comm; auto
    | H:(_, _) = (_, _) |- _ => inversion H; clear H; simpl_map1
    | H:?x = ?x |- _ => clear H; simpl_map1
    | |- ?x = ?x => reflexivity
    | |- join _ ?a ?a => apply map_join_comm; simpl_map1
    | |- join ?a _ ?a => apply map_join_emp; simpl_map1
    | |- empenv = _ => reflexivity; simpl_map1
    | |- _ = empenv => reflexivity; simpl_map1
    | H:True |- _ => clear H; simpl_map1
    | |- True => auto
    | _ => try (progress subst; simpl_map1)
  end.

Ltac simpljoin1 := repeat progress simpl_map1.

Lemma struct_type_vallist_match_os_tcb_flag :
  forall v, struct_type_vallist_match OS_TCB_flag v ->
            exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10, exists v11, v = v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: nil.
Proof.
  intros.
  unfold OS_TCB_flag in H.
  simpl in H.
  unfolds in H.
  destruct v; tryfalse.
  destruct v0; simpljoin1; tryfalse.
  destruct v1; simpljoin1; tryfalse.
  destruct v2; simpljoin1; tryfalse.
  destruct v3; simpljoin1; tryfalse.
  destruct v4; simpljoin1; tryfalse.
  destruct v5; simpljoin1; tryfalse.
  destruct v6; simpljoin1; tryfalse.
  destruct v7; simpljoin1; tryfalse.
  destruct v8; simpljoin1; tryfalse.
  destruct v9; simpljoin1; tryfalse.
  destruct v10; simpljoin1; tryfalse.
  do 11 eexists; eauto.
Qed.

(** in order to prove node_os_tcb_dup_false, I must move lots lemmas and definitions from ucos_common,
    Very Very Ugly!!!!
    This file should be all of definitions of os invariant, not the auxiliary lemmas!
 **)
Definition array_struct t :=
  (exists t1 n, t = Tarray t1 n) \/ (exists id dl, t = Tstruct id dl) \/ 
  (exists id dl, t = Tunion id dl) \/( t = Tvoid).

Lemma type_encode_nnil :
  forall t v,  ~array_struct t  -> encode_val t v <> nil.
Proof.
  inductions t; unfold encode_val in *;
  try solve [destruct v; simpl in *; intuition (try destruct a; tryfalse)].
  intros.
  false.
  apply H.
  branch 4; eauto.
  intros.
  false.
  apply H.
  branch 1; 
    do 2 eexists; eauto.
  intros.
  false.
  apply H.
  branch 2; 
    do 2 eexists; eauto.
  intros.
  false.
  apply H.
  branch 3; 
  do 2 eexists; eauto.
Qed.

Lemma ptomval_nnil_neq_auto :
  forall (A B T : Type) (MC : PermMap A B T) x1 x2 m b1 b2 a1 a2 x4 x0,
    usePerm = true ->
    join x1 x2 m ->
    isRw b1 = true ->
    isRw b2 = true ->
    join (sig a1 b1) x4 x1 ->
    join (sig a2 b2) x0 x2 ->
    a1 <> a2.
  intros.
  let l := calc_ins in
  infer' l a1; crush.
Qed.

Lemma ptomval_nnil_neq_auto' :
  forall (A B T : Type) (MC : PermMap A B T) x1 x2 m b1 b2 a1 a2 x4 x0,
    usePerm = true ->
    join x1 x2 m ->
    isRw b1 = true ->
    join (sig a1 b1) x4 x1 ->
    join (sig a2 b2) x0 x2 ->
    a1 <> a2.
Proof.
  intros.
  let l := calc_ins in
  infer' l a1; crush.
Qed.

Lemma ptomval_nnil_neq:
  forall v1 v2 x y  x1 x2 m,
    v1 <> nil ->
    v2 <> nil ->
    join x1 x2 m ->
    ptomvallist x true v1 x1 ->
    ptomvallist y true v2 x2 ->
    x <> y.
Proof.
  introv Hn1 Hn2 Hj  Hpto1 Hpto2.
  destruct v1; destruct v2; tryfalse.
  unfolds in Hpto1.
  unfolds in Hpto2.
  destruct x.
  destruct y.
  simp join.
  unfold ptomval in *.
  subst.
  eapply ptomval_nnil_neq_auto with (b1 := (true, m0)) (b2 := (true, m1)); auto.
  exact Hj.
  eauto.
  eauto.
Qed.

Lemma ptomval_nnil_neq':
  forall v1 v2 x y  x1 x2 m b,
    v1 <> nil ->
    v2 <> nil ->
    join x1 x2 m ->
    ptomvallist x true v1 x1 ->
    ptomvallist y b v2 x2 ->
    x <> y.
Proof.
  introv Hn1 Hn2 Hj  Hpto1 Hpto2.
  destruct v1; destruct v2; tryfalse.
  unfolds in Hpto1.
  unfolds in Hpto2.
  destruct x.
  destruct y.
  simp join.
  unfold ptomval in *.
  subst.
  eapply ptomval_nnil_neq_auto' with (b1 := (true, m0)) (b2 := (b, m1)); auto.
  exact Hj.
  eauto.
  eauto.
Qed.

Lemma pv_false :
  forall s x y t1 t2 v1 v2 P,
   ~array_struct t1 ->
      ~ array_struct t2 ->
    s  |= PV  x @ t1 |-> v1 ** PV y  @ t2 |-> v2 ** P-> x <> y.
Proof.
  introv Ht1 Ht2 H.
  sep lift 3%nat in H.
  assert (x = y \/ x <> y) by tauto.
  destruct H0; auto; subst y.
  remember ( PV x @ t1 |-> v1 ** PV x @ t2 |-> v2) as Hs.
  sep destroy H.
  subst.
  destruct_s x1.
  simpl in H1.
  simp join.
  unfolds in H4.
  unfolds in H5.
  simp join.
  remember (addrval_to_addr x)  as xx.
  lets Hneq1 : type_encode_nnil v1 Ht1.
  lets Hneq2 : type_encode_nnil v2 Ht2.
  lets Hz :  ptomval_nnil_neq H5 H4; eauto.
Qed.

Lemma pv_false_onehalf :
  forall s x y t1 t2 v1 v2 P,
   ~array_struct t1 ->
      ~ array_struct t2 ->
    s  |= PV  x @ t1 |-> v1 ** PV y  @ t2 |-r-> v2 ** P-> x <> y.
Proof.
  introv Ht1 Ht2 H.
  sep lift 3%nat in H.
  assert (x = y \/ x <> y) by tauto.
  destruct H0; auto; subst y.
  remember ( PV x @ t1 |-> v1 ** PV x @ t2 |-r-> v2) as Hs.
  sep destroy H.
  subst.
  destruct_s x1.
  simpl in H1.
  simp join.
  unfolds in H4.
  unfolds in H5.
  simp join.
  remember (addrval_to_addr x)  as xx.
  lets Hneq1 : type_encode_nnil v1 Ht1.
  lets Hneq2 : type_encode_nnil v2 Ht2.
  lets Hz :  ptomval_nnil_neq' H5 H4; eauto.
Qed.

Lemma node_OS_TCB_dup_false :
  forall p a1 a2 P s,
    s |= node p a1 OS_TCB_flag ** node p a2 OS_TCB_flag ** P ->
    False.
Proof.
  unfold node.
  intros.
  sep normal in H.
  sep destruct H.
  sep split in H.
  heat.

  eapply struct_type_vallist_match_os_tcb_flag in H3.
  eapply struct_type_vallist_match_os_tcb_flag in H2.
  heat.
  inverts H1.
  
  unfold Astruct in H.
  unfold OS_TCB_flag in H.
  unfold Astruct' in H.
  sep normal in H.
  sep lift 5%nat in H.
  sep lift 16%nat in H.

  (* ** ac: Check pv_false. *)
  remember (x,
            Int.add
              (Int.add
                 (Int.add
                    (Int.add Int.zero
                       (Int.repr
                          (Z.of_nat (typelen (Tcom_ptr os_tcb)))))
                    (Int.repr
                       (Z.of_nat (typelen (Tcom_ptr os_tcb)))))
                 (Int.repr (Z.of_nat (typelen (Tptr OS_EVENT)))))
              (Int.repr (Z.of_nat (typelen (Tptr Tvoid))))) as xx.

  assert (xx <> xx).
  {
    eapply pv_false.
    3: eauto.
    unfold not.
    intros.
    unfold array_struct in H0.
    destruct H0 as [? | [? | [? | ?]]]; heat; inverts H0.
    
    unfold not.
    intros.
    unfold array_struct in H0.
    destruct H0 as [? | [? | [? | ?]]]; heat; inverts H0.
  }
  tryfalse.
Qed.
(** ugly end **)
(******************************************************************************)
Require Import sep_join_lemmas.

Lemma join_sig_false_true :
  forall l a,
    join (sig l (false, a)) (sig l (false, a)) (sig l (true, a)).
Proof.
  intros.
  change (join (sig l (false, a)) (sig l (false, a)) (sig l (flip (false, a)))).
  eapply join_false_is_true_auto; ica.
Qed.

Lemma join_split :
  forall (m1:mem) m2 m m11 m12 m21 m22,
    join m1 m2 m ->
    join m11 m12 m1 ->
    join m21 m22 m2 ->
    exists mx1 mx2, join m11 m21 mx1 /\ join m12 m22 mx2 /\ join mx1 mx2 m.
  intros.
  geat.
Qed.  

Lemma ptomvallist_split :
  forall vl l m,
    ptomvallist l true  vl m ->
    exists m1 m2, ptomvallist l false vl m1 /\ ptomvallist  l false  vl m2 /\ join m1 m2 m.
Proof.
  inductions vl; intros.
  simpl in H; substs.
  simpl.
  do 2 eexists; splits; eauto.
  geat.

  unfold ptomvallist in H; fold ptomvallist in H; destruct l.
  simpljoin.
  unfold ptomvallist; fold ptomvallist.

  unfold ptomval in H0.
  
  lets Hx: join_sig_false_true (b, o) a.
  lets Hx1: IHvl H1.
  simpljoin.
  
  lets Hx2: join_split H Hx H4.
  simpljoin.
  unfold ptomval.
  exists x x3.
  split.
  do 2 eexists; splits; eauto.
  split; auto.
  do 2 eexists;  eauto.
Qed.

Lemma read_only_split_vptr:
  forall s x t v P,
    s |= GV x @ Tptr t |-> Vptr v ** P ->
    s |= (GV x @ Tptr t |-r-> Vptr v) **
      (GV x @ Tptr t |-r-> Vptr v) ** P.
Proof.
  intros.
  destruct_s s.
  simpl in H.
  simpljoin.
  unfold mapstoval in H9.
  simpljoin.
  
  lets Hx: ptomvallist_split H1.
  simpljoin.
  simpl.
  assert(x8 = x0).
  geat.
  substs.
  
  assert(exists xx, join x2 xx m /\ join x5 x1 xx).
  geat.
  destruct H9.
  destruct H9.
  exists x2 x6 m x3 x4 o.
  splits; eauto.
  exists x13 empmem x2 x2 empabst empabst; exists x3.
  splits; eauto.
  geat.
  unfold emposabst in *.
  substs.
  geat.
  eexists.
  splits; eauto.
  unfolds; auto.
  unfolds.
  eexists; splits; eauto.
  unfolds; auto.

  exists x5 x1 x6 empabst o o.
  splits; eauto.
  unfold emposabst in *.
  substs.
  geat.
  geat.

  exists x13 empmem x5 x5 empabst empabst; exists empabst.
  splits; eauto.
  geat.
  geat.
  eexists; splits; eauto.
  unfolds; auto.
  unfolds; eexists; splits; eauto.
  unfolds; auto.
  unfold emposabst in *; subst.
  assert(x4 = o).
  geat.
  substs; auto.
Qed.

Lemma ptomvalr_join_eq :
  forall l v1 v2 m1 m2 m3,
    ptomval l false v1 m1 -> ptomval l false v2 m2 ->
    join m1 m2 m3 -> v1 = v2.
Proof.
  intros.
  unfold ptomval in *.
  substs.
  unfold join in H1.
  simpl in H1.
  unfold HalfPermMap.join in H1.
  destruct H1.
  pose proof H l.
  unfold sig in H1; simpl in H1.
  pose proof map_get_sig l (false, v1).
  unfold get in H2; simpl in H2.
  unfold HalfPermMap.get in H2.
  unfold sig in H2; simpl in H2.
  rewrite H2 in H1.
  pose proof map_get_sig l (false, v2).
  unfold get in H3; simpl in H3.
  unfold HalfPermMap.get in H3.
  unfold sig in H3; simpl in H3.
  rewrite H3 in H1.
  auto.
Qed.
(* end *)

Local Open Scope int_scope.
Local Open Scope Z_scope.

Definition RL_TCBblk_P vl := 
  exists prio x y bitx bity stat, 
    V_OSTCBPrio vl = Some (Vint32 prio) /\
    V_OSTCBX vl = Some (Vint32 x) /\ V_OSTCBY vl = Some (Vint32 y) /\
    V_OSTCBBitX vl = Some (Vint32 bitx) /\ V_OSTCBBitY vl = Some (Vint32 bity) /\
    V_OSTCBStat vl = Some (Vint32 stat) /\
    0 <= Int.unsigned prio < 64 /\
    prio &ᵢ ($ 7) = x /\
    prio >>ᵢ ($ 3) = y /\
    ($ 1) <<ᵢ x = bitx /\ ($ 1) <<ᵢ y = bity /\
    (
      (stat = ($ OS_STAT_RDY) \/ stat = ($ OS_STAT_SUSPEND) \/
       stat = ($ OS_STAT_SEM) \/ stat = ($ OS_STAT_Q) \/
       stat = ($ OS_STAT_MBOX) \/ stat = ($ OS_STAT_MUTEX) \/
       stat = ($ OS_STAT_POSTQ) \/ stat = ($ OS_STAT_PORT) \/
       stat = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND) \/
       stat = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND) \/
       stat = Int.or ($ OS_STAT_POSTQ) ($ OS_STAT_SUSPEND) \/
       stat = Int.or ($ OS_STAT_MBOX) ($ OS_STAT_SUSPEND) \/
       stat = Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND) \/ 
       stat = Int.or ($ OS_STAT_PORT) ($ OS_STAT_SUSPEND) 
      ) /\
      exists eptr, V_OSTCBEventPtr vl = Some eptr /\
                   (stat = ($ OS_STAT_RDY) \/ stat = ($ OS_STAT_SUSPEND) -> eptr = Vnull)
    ) .

Definition prio_in_tbl (prio:int32) (tbl:vallist) :=
  forall x y z,
    x = prio &ᵢ ($ 7) -> y = Int.shru prio  ($ 3) ->
    nth_val (nat_of_Z (Int.unsigned y)) tbl = Some (Vint32 z) -> 
    z &ᵢ (($ 1) <<ᵢ x) = (($ 1) <<ᵢ x).

Definition prio_not_in_tbl (prio:int32) (tbl:vallist) :=
  forall x y z,
    x = prio &ᵢ ($ 7) -> y = Int.shru prio ($ 3) ->
    nth_val (nat_of_Z (Int.unsigned y)) tbl = Some (Vint32 z) -> 
    z &ᵢ (($ 1) <<ᵢ x) = $ 0.

(* TCB is ready: tcb_blk's prio is in tbl, and tcb_blk's dly is 0 *)
Definition RdyTCBblk vl rtbl (prio : priority) := 
  V_OSTCBPrio vl = Some (Vint32 prio) /\ prio_in_tbl prio rtbl .

(* Definition RLH_RdyI_P vl rtbl abstcb:= 
  forall prio , RdyTCBblk vl rtbl prio ->
                V_OSTCBStat vl = Some (V$ OS_STAT_RDY) /\
                V_OSTCBDly vl = Some (V$ 0) /\
                exists (m:msg), abstcb =  (prio,rdy,m). *)

Definition RLH_RdyI_P vl rtbl abstcb:= 
  forall prio,
    RdyTCBblk vl rtbl prio ->
    V_OSTCBDly vl = Some (V$ 0) /\
      ((V_OSTCBStat vl = Some (V$ OS_STAT_RDY) /\     
          exists (m:msg), abstcb =  (prio,rdy,m,false)) \/
         (V_OSTCBStat vl = Some (V$ OS_STAT_SEM) /\ 
            (exists m eid, abstcb = (prio, wait (os_stat_sem eid) (Some Int.zero), m, false)) \/
            (V_OSTCBStat vl = Some (V$ OS_STAT_MUTEX) /\
               (exists m eid, abstcb = (prio, wait (os_stat_mutexsem eid) (Some Int.zero), m, false))) \/ 
            (V_OSTCBStat vl = Some (V$ OS_STAT_Q)) /\
              (exists m eid, abstcb = (prio, wait (os_stat_q eid) (Some Int.zero), m, false)) \/
            (V_OSTCBStat vl = Some (V$ OS_STAT_PORT)) /\
              (exists m eid, abstcb = (prio, wait (os_stat_port eid) (Some Int.zero), m, false))  
              )).

Definition RHL_RdyI_P  vl rtbl abstcb := 
  forall prio (m:msg),  abstcb =  (prio,rdy,m,false)->
                (RdyTCBblk vl rtbl prio/\ 
                 V_OSTCBStat vl = Some (V$ OS_STAT_RDY)/\ 
                 V_OSTCBDly vl = Some (V$ 0)).

Definition WaitTCBblk vl rtbl (prio : priority) t:= 
  V_OSTCBPrio vl = Some (Vint32 prio) /\ prio_not_in_tbl prio rtbl /\ 
  V_OSTCBDly vl = Some (Vint32 t).

Definition RLH_Wait_P vl rtbl abstcb := 
  forall prio t,
    WaitTCBblk vl rtbl prio t ->
    V_OSTCBStat vl = Some (V$ OS_STAT_RDY) ->
    Int.ltu Int.zero t = true  /\
      exists (m:msg), abstcb = (prio,wait os_stat_time (Some t),m,false).

Definition RHL_Wait_P vl rtbl abstcb := 
  forall prio t_opt (m:msg),
    abstcb = (prio,wait os_stat_time t_opt,m,false)->
    exists t, 
      t_opt = Some t /\  
        WaitTCBblk vl rtbl prio t /\
        Int.ltu Int.zero t = true  /\
        V_OSTCBStat vl = Some (V$ OS_STAT_RDY).

Definition RLH_Suspend_P vl rtbl abstcb :=
  (forall prio,    WaitTCBblk vl rtbl prio Int.zero ->
                    V_OSTCBStat vl = Some (V$ OS_STAT_SUSPEND) ->
                    exists (m:msg), abstcb = (prio,rdy,m,true)) /\
  (forall prio t,  WaitTCBblk vl rtbl prio t ->
                    V_OSTCBStat vl = Some (V$ OS_STAT_SUSPEND) ->
                    Int.ltu Int.zero t = true ->
                    exists (m:msg), abstcb = (prio,wait os_stat_time (Some t),m,true)).

Definition RHL_Suspend_P vl rtbl abstcb := 
  (forall prio (m:msg), abstcb = (prio,rdy,m,true) ->
                        WaitTCBblk vl rtbl prio Int.zero /\
                        V_OSTCBStat vl = Some (V$ OS_STAT_SUSPEND)) /\
  (forall prio t_opt (m:msg), abstcb = (prio,wait os_stat_time t_opt,m,true) ->
                         (exists t, t_opt = Some t /\
                          WaitTCBblk vl rtbl prio t /\
                          Int.ltu Int.zero t = true /\
                          V_OSTCBStat vl = Some (V$ OS_STAT_SUSPEND))).

(* wait for sem. 't' means the time to remaining time to wait*)
Definition RLH_WaitS_P vl rtbl abstcb := 
  forall prio t eid,
    WaitTCBblk vl rtbl prio t ->
    V_OSTCBStat vl = Some (V$ OS_STAT_SEM) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    exists (m:msg),
      t <> Int.zero /\ abstcb = (prio,(wait (os_stat_sem eid) (Some t)),m,false) \/
        t = Int.zero /\ abstcb = (prio,(wait (os_stat_sem eid) None),m,false).

Definition RLH_WaitS_TO_P vl rtbl abstcb :=
  forall prio eid,
    RdyTCBblk vl rtbl prio ->
    V_OSTCBStat vl = Some (V$ OS_STAT_SEM) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    exists (m: msg),
      abstcb = (prio,(wait (os_stat_sem eid) (Some Int.zero)),m,false). 

Definition RHL_WaitS_P vl rtbl abstcb := 
  forall prio eid t_opt (m:msg),
    abstcb =  (prio,wait (os_stat_sem eid) t_opt,m,false)->
    ((exists t,
         (t_opt = Some t /\
            (t <> Int.zero /\ WaitTCBblk vl rtbl prio t \/
               t = Int.zero /\ RdyTCBblk vl rtbl prio /\ V_OSTCBDly vl = Some (Vint32 Int.zero)))
         \/ t_opt = None /\ WaitTCBblk vl rtbl prio Int.zero) /\
       V_OSTCBEventPtr vl = Some (Vptr eid)/\
       V_OSTCBStat vl = Some (V$ OS_STAT_SEM)).

Definition RLH_WaitS_Suspend_P vl rtbl abstcb :=
  forall prio t eid,
    WaitTCBblk vl rtbl prio t ->
    V_OSTCBStat vl = Some (Vint32 (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND))) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    exists (m:msg) t_opt,
                  abstcb = (prio,(wait (os_stat_sem eid) t_opt),m,true) /\
                  (( t = Int.zero /\ (t_opt = Some Int.zero \/ t_opt = None)) \/
                     ( t <> Int.zero /\ t_opt = Some t)).

Definition RHL_WaitS_Suspend_P vl rtbl abstcb :=
  forall prio eid t_opt (m:msg), abstcb = (prio,wait (os_stat_sem eid) t_opt,m,true)->
                             (((exists t, t_opt = Some t /\ WaitTCBblk vl rtbl prio t) \/
                                 (t_opt = None /\ WaitTCBblk vl rtbl prio Int.zero)) /\
                              V_OSTCBEventPtr vl = Some (Vptr eid)/\
                              V_OSTCBStat vl = Some (Vint32 (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)))).

(* wait for massage queue. *)
Definition RLH_WaitQ_P vl rtbl abstcb := 
  forall prio t eid, 
    WaitTCBblk vl rtbl prio t ->
    V_OSTCBStat vl = Some (V$ OS_STAT_Q) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    exists (m:msg),
      t <> Int.zero /\ abstcb  = (prio,wait (os_stat_q eid) (Some t),m,false) \/
        t = Int.zero /\ abstcb = (prio, wait (os_stat_q eid) None, m,false). 

Definition RLH_WaitQ_TO_P vl rtbl abstcb :=
  forall prio eid,
    RdyTCBblk vl rtbl prio -> 
    V_OSTCBStat vl = Some (V$ OS_STAT_Q) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    exists (m: msg),
      abstcb = (prio, wait (os_stat_q eid) (Some Int.zero), m,false). 

Definition RHL_WaitQ_P vl rtbl abstcb := 
  forall prio  eid t_opt (m:msg),
    abstcb = (prio,wait (os_stat_q eid) t_opt,m,false)->
    ((exists t,
         (t_opt = Some t /\
            (t <> Int.zero /\ WaitTCBblk vl rtbl prio t \/
               t = Int.zero /\ RdyTCBblk vl rtbl prio /\ V_OSTCBDly vl = Some (Vint32 Int.zero)))
         \/ t_opt = None /\ WaitTCBblk vl rtbl prio Int.zero) /\ 
     V_OSTCBEventPtr vl = Some (Vptr eid)/\
     V_OSTCBStat vl = Some (V$ OS_STAT_Q)).

Definition RLH_WaitPostQ_P vl rtbl abstcb := 
  forall prio t eid, 
    WaitTCBblk vl rtbl prio t ->
    V_OSTCBStat vl = Some (V$ OS_STAT_POSTQ) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    t = Int.zero /\ 
    exists (m:msg), abstcb  = (prio,wait (os_stat_postq eid) None,m,false).

Definition RHL_WaitPostQ_P vl rtbl abstcb := 
  forall prio eid t (m:msg), 
    abstcb = (prio,wait (os_stat_postq eid) t,m,false)->
    (t = None /\
       WaitTCBblk vl rtbl prio Int.zero /\ 
       V_OSTCBEventPtr vl = Some (Vptr eid)/\
       V_OSTCBStat vl = Some (V$ OS_STAT_POSTQ)).

Definition RLH_WaitPostQ_Suspend_P vl rtbl abstcb :=
  forall prio t eid,
    WaitTCBblk vl rtbl prio t ->
    V_OSTCBStat vl = Some (Vint32 (Int.or ($ OS_STAT_POSTQ) ($ OS_STAT_SUSPEND))) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    t = Int.zero /\
    exists (m:msg), abstcb = (prio,(wait (os_stat_postq eid) None),m,true).

Definition RHL_WaitPostQ_Suspend_P vl rtbl abstcb :=
  forall prio eid t_opt (m:msg), abstcb = (prio,wait (os_stat_postq eid) t_opt,m,true)->
                              t_opt = None /\
                              WaitTCBblk vl rtbl prio Int.zero /\
                              V_OSTCBEventPtr vl = Some (Vptr eid)/\
                              V_OSTCBStat vl = Some (Vint32 (Int.or ($ OS_STAT_POSTQ) ($ OS_STAT_SUSPEND))).

Definition RLH_WaitQ_Suspend_P vl rtbl abstcb :=
  forall prio t eid,
    WaitTCBblk vl rtbl prio t ->
    V_OSTCBStat vl = Some (Vint32 (Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND))) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    exists (m:msg) t_opt,
                  abstcb = (prio,(wait (os_stat_q eid) t_opt),m,true) /\
                  (( t = Int.zero /\ (t_opt = Some Int.zero \/ t_opt = None)) \/
                     ( t <> Int.zero /\ t_opt = Some t)).

Definition RHL_WaitQ_Suspend_P vl rtbl abstcb :=
  forall prio eid t_opt (m:msg), abstcb = (prio,wait (os_stat_q eid) t_opt,m,true)->
                             ((exists t, t_opt = Some t /\ WaitTCBblk vl rtbl prio t) \/
                                 (t_opt = None /\ WaitTCBblk vl rtbl prio Int.zero)) /\
                              V_OSTCBEventPtr vl = Some (Vptr eid)/\
                              V_OSTCBStat vl = Some (Vint32 (Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND))).

(* wait for mail box *)
Definition RLH_WaitMB_P vl rtbl abstcb := 
  forall prio t eid, 
    WaitTCBblk vl rtbl prio t ->
    V_OSTCBStat vl = Some (V$ OS_STAT_MBOX) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    exists (m:msg),
      t <> Int.zero /\ abstcb = (prio,(wait (os_stat_mbox eid) (Some t)),m,false) \/
        t = Int.zero /\ abstcb = (prio,(wait (os_stat_mbox eid) None),m,false).

Definition RLH_WaitMB_TO_P vl rtbl abstcb :=
  forall prio eid,
    RdyTCBblk vl rtbl prio ->
    V_OSTCBStat vl = Some (V$ OS_STAT_MBOX) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    exists (m: msg),
      abstcb = (prio,(wait (os_stat_mbox eid) (Some Int.zero)),m,false).

Definition RHL_WaitMB_P vl rtbl abstcb := 
  forall prio eid t_opt (m:msg),
    abstcb =  (prio,wait (os_stat_mbox eid) t_opt,m,false)->
    ((exists t,
         (t_opt = Some t /\
            (t <> Int.zero /\ WaitTCBblk vl rtbl prio t \/
               t = Int.zero /\ RdyTCBblk vl rtbl prio /\ V_OSTCBDly vl = Some (Vint32 Int.zero)))
         \/ t_opt = None /\ WaitTCBblk vl rtbl prio Int.zero) /\
       V_OSTCBEventPtr vl = Some (Vptr eid)/\
       V_OSTCBStat vl = Some (V$ OS_STAT_MBOX)).

Definition RLH_WaitMB_Suspend_P vl rtbl abstcb :=
  forall prio t eid,
    WaitTCBblk vl rtbl prio t ->
    V_OSTCBStat vl = Some (Vint32 (Int.or ($ OS_STAT_MBOX) ($ OS_STAT_SUSPEND))) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    exists (m:msg) t_opt,
                  abstcb = (prio,(wait (os_stat_mbox eid) t_opt),m,true) /\
                  (( t = Int.zero /\ (t_opt = Some Int.zero \/ t_opt = None)) \/
                     ( t <> Int.zero /\ t_opt = Some t)).

Definition RHL_WaitMB_Suspend_P vl rtbl abstcb :=
  forall prio eid t_opt (m:msg), abstcb = (prio,wait (os_stat_mbox eid) t_opt,m,true)->
                             ((exists t, t_opt = Some t /\ WaitTCBblk vl rtbl prio t) \/
                                 (t_opt = None /\ WaitTCBblk vl rtbl prio Int.zero)) /\
                              V_OSTCBEventPtr vl = Some (Vptr eid)/\
                              V_OSTCBStat vl = Some (Vint32 (Int.or ($ OS_STAT_MBOX) ($ OS_STAT_SUSPEND))).

(* wait for mutex sem *)
Definition RLH_WaitMS_P vl rtbl abstcb := 
  forall prio t eid, 
    WaitTCBblk vl rtbl prio t ->
    V_OSTCBStat vl = Some (V$ OS_STAT_MUTEX) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    exists (m:msg),
      t <> Int.zero /\ abstcb  = (prio,wait (os_stat_mutexsem eid) (Some t),m,false) \/
        t = Int.zero /\ abstcb = (prio, wait (os_stat_mutexsem eid) None, m,false).       

Definition RLH_WaitMS_TO_P vl rtbl abstcb :=
  forall prio eid,
    RdyTCBblk vl rtbl prio ->
    V_OSTCBStat vl = Some (V$ OS_STAT_MUTEX) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    exists (m: msg),
      abstcb = (prio, wait (os_stat_mutexsem eid) (Some Int.zero), m,false) . 
  
Definition RHL_WaitMS_P vl rtbl abstcb := 
  forall prio eid t_opt (m:msg),
    abstcb = (prio,wait (os_stat_mutexsem eid) t_opt,m,false)-> 
    ((exists t,
         (t_opt = Some t /\
            (t <> Int.zero /\ WaitTCBblk vl rtbl prio t \/
               t = Int.zero /\ RdyTCBblk vl rtbl prio /\ V_OSTCBDly vl = Some (Vint32 Int.zero)))
         \/ t_opt = None /\ WaitTCBblk vl rtbl prio Int.zero) /\ 
       V_OSTCBEventPtr vl = Some (Vptr eid)/\
       V_OSTCBStat vl = Some (V$ OS_STAT_MUTEX)).

Definition RLH_WaitMS_Suspend_P vl rtbl abstcb :=
  forall prio t eid,
    WaitTCBblk vl rtbl prio t ->
    V_OSTCBStat vl = Some (Vint32 (Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND))) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    exists (m:msg) t_opt,
                  abstcb = (prio,(wait (os_stat_mutexsem eid) t_opt),m,true) /\
                  (( t = Int.zero /\ (t_opt = Some Int.zero \/ t_opt = None)) \/
                     ( t <> Int.zero /\ t_opt = Some t)).

Definition RHL_WaitMS_Suspend_P vl rtbl abstcb :=
  forall prio eid t_opt (m:msg), abstcb = (prio,wait (os_stat_mutexsem eid) t_opt,m,true)->
                             ((exists t, t_opt = Some t /\ WaitTCBblk vl rtbl prio t) \/
                                 (t_opt = None /\ WaitTCBblk vl rtbl prio Int.zero)) /\
                              V_OSTCBEventPtr vl = Some (Vptr eid)/\
                              V_OSTCBStat vl = Some (Vint32 (Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND))).
       
(* wait for port. *)
Definition RLH_WaitPort_P vl rtbl abstcb := 
  forall prio t eid, 
    WaitTCBblk vl rtbl prio t ->
    V_OSTCBStat vl = Some (V$ OS_STAT_PORT) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    exists (m:msg),
      t <> Int.zero /\ abstcb  = (prio,wait (os_stat_port eid) (Some t),m,false) \/
        t = Int.zero /\ abstcb = (prio, wait (os_stat_port eid) None, m,false). 

Definition RLH_WaitPort_TO_P vl rtbl abstcb :=
  forall prio eid,
    RdyTCBblk vl rtbl prio -> 
    V_OSTCBStat vl = Some (V$ OS_STAT_PORT) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    exists (m: msg),
      abstcb = (prio, wait (os_stat_port eid) (Some Int.zero), m,false).       
      
Definition RHL_WaitPort_P vl rtbl abstcb := 
  forall prio  eid t_opt (m:msg),
    abstcb = (prio,wait (os_stat_port eid) t_opt,m,false)->
    (((exists t,t_opt = Some t /\
            (t <> Int.zero /\ WaitTCBblk vl rtbl prio t \/
               t = Int.zero /\ RdyTCBblk vl rtbl prio /\ V_OSTCBDly vl = Some (Vint32 Int.zero)))
         \/ t_opt = None /\ WaitTCBblk vl rtbl prio Int.zero) /\ 
     V_OSTCBEventPtr vl = Some (Vptr eid)/\
     V_OSTCBStat vl = Some (V$ OS_STAT_PORT)).
    
Definition RLH_WaitPort_Suspend_P vl rtbl abstcb :=
  forall prio t eid,
    WaitTCBblk vl rtbl prio t ->
    V_OSTCBStat vl = Some (Vint32 (Int.or ($ OS_STAT_PORT) ($ OS_STAT_SUSPEND))) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    exists (m:msg) t_opt,
                  abstcb = (prio,(wait (os_stat_port eid) t_opt),m,true) /\
                  (( t = Int.zero /\ (t_opt = Some Int.zero \/ t_opt = None)) \/
                     ( t <> Int.zero /\ t_opt = Some t)).

Definition RHL_WaitPort_Suspend_P vl rtbl abstcb :=
  forall prio eid t_opt (m:msg), abstcb = (prio,wait (os_stat_port eid) t_opt,m,true)->
                             ((exists t, t_opt = Some t /\ WaitTCBblk vl rtbl prio t) \/
                                 (t_opt = None /\ WaitTCBblk vl rtbl prio Int.zero)) /\
                              V_OSTCBEventPtr vl = Some (Vptr eid)/\
                              V_OSTCBStat vl = Some (Vint32 (Int.or ($ OS_STAT_PORT) ($ OS_STAT_SUSPEND))).
                              

Definition RLH_TCB_Status_Wait_P vl rtbl abstcb :=
  RLH_Wait_P  vl rtbl abstcb /\
    RLH_WaitS_P   vl rtbl abstcb /\ 
    RLH_WaitS_TO_P vl rtbl abstcb /\ 
    RLH_WaitQ_P   vl rtbl abstcb /\
    RLH_WaitQ_TO_P vl rtbl abstcb /\ 
    RLH_WaitMB_P   vl rtbl abstcb /\
    RLH_WaitMB_TO_P   vl rtbl abstcb /\
    RLH_WaitMS_P   vl rtbl abstcb  /\
    RLH_WaitMS_TO_P vl rtbl abstcb /\ 
    RLH_WaitPostQ_P   vl rtbl abstcb /\
    RLH_WaitS_Suspend_P  vl rtbl abstcb /\ 
    RLH_WaitQ_Suspend_P  vl rtbl abstcb /\
    RLH_WaitPostQ_Suspend_P  vl rtbl abstcb /\
    RLH_WaitMB_Suspend_P vl rtbl abstcb /\
    RLH_WaitMS_Suspend_P vl rtbl abstcb /\ 
    RLH_WaitPort_P   vl rtbl abstcb /\
    RLH_WaitPort_TO_P vl rtbl abstcb /\ 
    RLH_WaitPort_Suspend_P  vl rtbl abstcb.

Definition RHL_TCB_Status_Wait_P  vl rtbl abstcb :=
  RHL_Wait_P  vl rtbl abstcb /\
  RHL_WaitS_P   vl rtbl abstcb /\ 
  RHL_WaitQ_P   vl rtbl abstcb /\
  RHL_WaitMB_P   vl rtbl abstcb /\
  RHL_WaitMS_P   vl rtbl abstcb /\ 
  RHL_WaitPostQ_P   vl rtbl abstcb /\
  RHL_WaitS_Suspend_P  vl rtbl abstcb /\ 
  RHL_WaitQ_Suspend_P  vl rtbl abstcb /\
  RHL_WaitPostQ_Suspend_P  vl rtbl abstcb /\
  RHL_WaitMB_Suspend_P vl rtbl abstcb /\
  RHL_WaitMS_Suspend_P vl rtbl abstcb /\ 
  RHL_WaitPort_P   vl rtbl abstcb /\
  RHL_WaitPort_Suspend_P  vl rtbl abstcb.

Definition R_TCB_Status_P  vl rtbl abstcb :=
  RLH_RdyI_P vl rtbl abstcb /\
  RHL_RdyI_P vl rtbl abstcb /\
  RLH_Suspend_P vl rtbl abstcb /\
  RHL_Suspend_P vl rtbl abstcb /\
  RLH_TCB_Status_Wait_P  vl rtbl abstcb /\ 
  RHL_TCB_Status_Wait_P  vl rtbl abstcb.

(* Low tcbmsg <-> High tcbmsg *)

Definition TCBNode_P vl  (rtbl : vallist) (abstcb:priority * taskstatus * msg * susstatus):=
  match abstcb with
    |(p,st,m,sus) =>
     V_OSTCBMsg vl = Some m /\  
     V_OSTCBPrio vl = Some (Vint32 p) /\ 
     RL_TCBblk_P vl /\ 
     R_TCB_Status_P vl rtbl abstcb 
(*/\ 
     V_OSTCBflag vl = Some (Vint32 (Int.repr 1))
*)
  end.

Notation TcbJoin:= joinsig.  

(*
Definition TCB_AUX_LIST:=  (dcons OSTCBflag Tint8 dnil).

Fixpoint map_tcb_aux (l:list vallist):=
  match l with
    | nil => nil
    | vl::l'=> (Vint32 (Int.repr 1%Z)::nil) :: map_tcb_aux l'
  end.

Definition tcbdllseg  (head headprev tail tailnext : val) (l : list vallist) :=
               dllseg_aux  head headprev tail tailnext l (map_tcb_aux l) OS_TCB  TCB_AUX_LIST V_OSTCBPrev V_OSTCBNext .
*)
  
Fixpoint TCBList_P (v: val) (l:list vallist) (rtbl : vallist) (tcbls : TcbMod.map) 
         {struct l} : Prop :=
  match l with
    | nil =>  tcbls = emp 
    | vl :: l' =>   exists tid  v' tcbls' abstcb, 
                      v = Vptr tid /\
                      V_OSTCBNext vl = Some v' /\
                      TcbJoin tid abstcb tcbls' tcbls/\
                      TCBNode_P vl rtbl abstcb /\ 
                      TCBList_P v' l' rtbl tcbls'
  end.                                   

Notation flag_off:= (Int.repr 25%Z).

Notation evloc_off := (Int.repr 30%Z).
Notation muxptr_off := (Int.repr 31%Z).
Notation semptr_off := (Int.repr 35%Z). 
Notation qptr_off := (Int.repr 39%Z). 

Fixpoint dllsegflag (head tailnext : val) (l:list vallist) 
          (next: vallist -> option val):=
  match l with
    | nil => [| head = tailnext |]  ** [|l = nil|]
    | vl::l' =>
      (
       EX a vn,
         [|head = Vptr a|] **
         [|next vl = Some vn|] ** 
         PV (get_off_addr a flag_off) @ Tint8 |-r-> (Vint32 (Int.repr 1%Z)) **
         dllsegflag vn tailnext l' next
      )
   end.

Definition tcbdllflag head l := dllsegflag head Vnull l V_OSTCBNext.

Definition tcbdllseg  (head headprev tail tailnext : val) (l : list vallist) :=
  dllseg  head headprev tail tailnext l OS_TCB_flag  V_OSTCBPrev V_OSTCBNext .


(*************** mem assertions for ghost vars *****************)

Definition evaux_node a v1 v2 v3 v4 :=
      PV (get_off_addr a evloc_off) @ Tint8 |-r-> v1 **  
      PV (get_off_addr a muxptr_off) @ (Tptr OS_EVENT) |-r-> v2 ** 
      PV (get_off_addr a semptr_off) @ (Tptr OS_EVENT) |-r-> v3 ** 
      PV (get_off_addr a qptr_off) @ (Tptr OS_EVENT) |-r-> v4 ** 
      [| rule_type_val_match Tint8 v1 = true |] ** 
      [| rule_type_val_match (Tptr OS_EVENT) v2 = true |] ** 
      [| rule_type_val_match (Tptr OS_EVENT) v3 = true |] ** 
      [| rule_type_val_match (Tptr OS_EVENT) v4 = true |]. 

Fixpoint llsegevaux 
         (head tailnext: val) 
         (l: list vallist)
         (locmp: EvAuxLocMod.map) 
         (ptrmp: EvAuxPtrMod.map)  
         (next: vallist->option val) :=
  match l with
    nil => [| head = tailnext |]  ** [| l = nil |] ** [| locmp = emp /\ ptrmp = emp |]  
  | vl :: l' => (
    EX a vn v1 v2 v3 v4 locmp' ptrmp',
      [| head = Vptr a |] **
      [| next vl = Some vn |] ** 
      evaux_node a v1 v2 v3 v4 ** 
      [| joinsig a v1 locmp' locmp |] ** 
      [| joinsig a (v2, v3, v4) ptrmp' ptrmp |] ** 
      llsegevaux vn tailnext l' locmp' ptrmp' next 
    )
  end. 

Definition tcbllsegevaux
           (tcbh: val) (vll: list vallist) (locmp: EvAuxLocMod.map) (ptrmp: EvAuxPtrMod.map)  := 
  llsegevaux tcbh Vnull vll locmp ptrmp V_OSTCBNext. 

(*************** end mem assertions for ghost vars *****************) 


Definition AOSTCBList_old (p1 p2: val) (l1 l2:list vallist) (rtbl : vallist)
           (hcurt:addrval)(tcbls : TcbMod.map) :=
  EX tail1 tail2 tcbls1 tcbls2,
  (GV OSTCBList @ (Tptr OS_TCB) |-> p1) **
                                        tcbdllseg p1 Vnull tail1 p2 l1 ** 
                                        (GV OSTCBCur @ (Tptr OS_TCB) |-> p2) **
                                        tcbdllseg  p2 tail1 tail2 Vnull l2 **
                                        [|p1 <> Vnull /\ p2 = Vptr hcurt|] ** 
                                        [| join tcbls1 tcbls2 tcbls|] **
                                        [| TCBList_P p1 l1 rtbl tcbls1 |]**
                                        [| TCBList_P p2 l2 rtbl tcbls2 |].

Fixpoint sllsegfreeflag (head tailnext : val) (l : list vallist)
       (next : vallist -> option val) {struct l} : asrt :=
   match l with
  | nil => [|head = tailnext|]
  | vl :: l' =>
    (
      EX a vn v1 v2 v3 v4, 
       [|head = Vptr a|] **
       [|next vl = Some vn|] **
       PV (get_off_addr a flag_off) @ Tint8 |-> (Vint32 (Int.repr 0%Z)) **
       PV (get_off_addr a evloc_off) @ Tint8 |-> v1 ** 
       PV (get_off_addr a muxptr_off) @ (Tptr OS_EVENT) |-> v2 ** 
       PV (get_off_addr a semptr_off) @ (Tptr OS_EVENT) |-> v3 ** 
       PV (get_off_addr a qptr_off) @ (Tptr OS_EVENT) |-> v4 ** 
       sllsegfreeflag vn tailnext l' next
    ) 
  end.

Definition sllfreeflag head l := sllsegfreeflag head Vnull l V_OSTCBNext.

Definition TCBFree_Not_Eq p ct l:=
  [| p <> Vptr ct |]
    ** sll p l OS_TCB_flag V_OSTCBNext ** sllfreeflag p l.

Definition prio_not_in_tcbls p (tcbls:TcbMod.map) :=
  ~ exists t st msg sus, get tcbls t = Some (p,st,msg,sus).

Definition TCBFree_Eq p ct l tcbls:=
  EX l' vl p',
  [| p = Vptr ct /\ l = vl :: l' /\ V_OSTCBNext vl = Some p' |]**
  Astruct ct OS_TCB_flag vl ** [| struct_type_vallist_match OS_TCB_flag vl /\ RL_TCBblk_P vl /\ exists prio, V_OSTCBPrio vl = Some (Vint32 prio) /\ (*prio_not_in_tbl prio rtbl /\*) prio_not_in_tcbls prio tcbls |] **
  PV (get_off_addr ct flag_off)@Tint8 |-r-> (Vint32 (Int.repr 0%Z)) **
  (EX v1 v2 v3 v4,  
      PV (get_off_addr ct evloc_off) @ Tint8 |-r-> v1 ** 
      PV (get_off_addr ct muxptr_off) @ (Tptr OS_EVENT) |-r-> v2 **  
      PV (get_off_addr ct semptr_off) @ (Tptr OS_EVENT) |-r-> v3 ** 
      PV (get_off_addr ct qptr_off) @ (Tptr OS_EVENT) |-r-> v4 
  )
  ** sll p' l' OS_TCB_flag V_OSTCBNext ** sllfreeflag p' l'.

Definition AOSTCBFreeList (p:val) (l:list vallist)  :=
  (GV OSTCBFreeList @ (Tptr OS_TCB) |-> p)
    ** sll p l OS_TCB_flag  V_OSTCBNext **  sllfreeflag p l.

Definition AOSTCBFreeList' (p:val) (l:list vallist) (ct:addrval) tcbls:=
  (GV OSTCBFreeList @ (Tptr OS_TCB) |-> p) **  (TCBFree_Not_Eq p ct l  \\// TCBFree_Eq p ct l tcbls).

(* OSRdyTbl & OSRdyGrp *)
Definition AOSRdyTbl (vl:vallist) := 
  GAarray OSRdyTbl (Tarray Tint8 (nat_of_Z OS_RDY_TBL_SIZE)) vl **  
          [| array_type_vallist_match Tint8 vl /\ length vl = (nat_of_Z OS_RDY_TBL_SIZE)|].

Definition AOSRdyGrp (v:val) := GV OSRdyGrp @ Tint8 |-> v ** [| rule_type_val_match Tint8 v = true |].

(* OSUnMapTbl & OSMapTbl *)
Definition OSMapVallist :=
  V$1::V$2::V$4::V$8::V$16::V$32::V$64::V$128::nil.

Definition AOSMapTbl :=
  GAarray OSMapTbl (Tarray Tint8 8) OSMapVallist.

Definition OSUnMapVallist :=
  V$0::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$4::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$5::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$4::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$6::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$4::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$5::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$4::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$7::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$4::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$5::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$4::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$6::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$4::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$5::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$4::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::nil.

Definition AOSUnMapTbl :=
  GAarray OSUnMapTbl (Tarray Tint8 256) OSUnMapVallist.

Definition RL_RTbl_PrioTbl_P rtbl ptbl vhold:= 
  forall p,
    0 <= Int.unsigned p < 64 ->
    prio_in_tbl p rtbl -> 
    exists tid,
      nth_val (Z.to_nat (Int.unsigned p)) ptbl = Some (Vptr tid) /\ tid <> vhold. 

Definition R_Prio_No_Dup (tcbls : TcbMod.map) :=
  forall tid tid' prio st m prio' st' m' sus sus',
    tid <> tid' ->
    get tcbls tid = Some (prio, st, m, sus) ->
    get tcbls tid' = Some (prio',st',m', sus') ->
    prio <> prio'.
              
Definition R_PrioTbl_P (ptbl : vallist) (tcbls : TcbMod.map) (vhold:addrval):=
  (forall prio tcbid,
      (0<=Int.unsigned prio<64) ->
      nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some (Vptr tcbid) ->
      tcbid <> vhold ->
      exists st m sus, get tcbls tcbid = Some (prio,st,m,sus)) /\
  (forall tcbid prio st m sus,
      get tcbls tcbid = Some (prio,st,m,sus) ->
      nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some (Vptr tcbid) /\ tcbid <> vhold) /\
  R_Prio_No_Dup tcbls.

(* OSTCBPrioTbl *)


(********correspondence between low/high-level OSTCBPrioTbl ********)

Definition RLH_PrioTbl_P (ptbl : vallist) (ptls : PtbMod.map) (vhold:addrval):=
(forall prio,
      ~ (0<=Int.unsigned prio <64) ->
        get ptls prio = None) /\
(forall prio,
      (0<=Int.unsigned prio <64) ->
      nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some Vnull ->
        get ptls prio = Some Null) /\
(forall prio,
      (0<=Int.unsigned prio <64) ->
      nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some (Vptr vhold) ->
        get ptls prio = Some Holder) /\
(forall prio tcbid,
      (0<=Int.unsigned prio <64) ->
      nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some (Vptr tcbid) ->
      tcbid <> vhold ->
        get ptls prio = Some (Valid_Addr tcbid)).

Definition RHL_PrioTbl_P (ptbl : vallist) (ptls : PtbMod.map) (vhold:addrval):=
(forall prio,
        get ptls prio = None ->
        ~ (0<=Int.unsigned prio <64)) /\
(forall prio,
        get ptls prio = Some Null ->
        (0<=Int.unsigned prio <64) /\
      nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some Vnull) /\
(forall prio,
        get ptls prio = Some Holder ->
        (0<=Int.unsigned prio <64) /\
      nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some (Vptr vhold) ) /\
(forall prio tcbid,
        get ptls prio = Some (Valid_Addr tcbid) ->
        (0<=Int.unsigned prio <64) /\
      nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some (Vptr tcbid) /\
      tcbid <> vhold).

Definition RH_PrioTbl_P (ptbl : vallist) (ptls : PtbMod.map) (vhold:addrval):=
  RLH_PrioTbl_P ptbl ptls vhold /\ RHL_PrioTbl_P ptbl ptls vhold.

Notation HPriotls ptls:= (Aabsdata absptlsid (absptls  ptls)).

(********end correspondence between low/high-level OSTCBPrioTbl ********)


Definition AOSTCBPrioTbl (vl:vallist) (rtbl:vallist) (tcbls:TcbMod.map) (ptls: PtbMod.map) (vhold:addrval):=
  GAarray OSTCBPrioTbl (Tarray (Tptr OS_TCB) 64) vl **
  (G& OSPlaceHolder @ Tint8 == vhold ** (EX v, PV vhold @ Tint8 |-> v)) **
  [| array_type_vallist_match (Tptr OS_TCB) vl /\ length vl = 64%nat |] **
  [|RL_RTbl_PrioTbl_P rtbl vl vhold|] ** [| R_PrioTbl_P vl tcbls vhold|] ** 
  [| RH_PrioTbl_P vl ptls vhold |] ** HPriotls ptls.

Definition AOSTime (t:val) := GV OSTime @ Tint32 |-> t.  

(* OSIntNesting *)
Definition AOSIntNesting:= EX v, GV OSIntNesting @ Tint32 |-> (Vint32 v).

(*-----------------------------------------------------------------------------------*)
(* relation in low level                                                             *)
(*-----------------------------------------------------------------------------------*)
(* Low tbl grp *)

Definition RL_Tbl_Grp_P (tbl:vallist) (grp:val):= 
  (forall n v v', (0<=n<8)%nat -> nth_val n tbl = Some (Vint32 v) -> grp = Vint32 v' ->
                 ((v' &ᵢ (($ 1) <<ᵢ ($ (Z_of_nat n))) = $0 <-> v = $0) /\ 
                  (v' &ᵢ (($ 1) <<ᵢ ($ (Z_of_nat n))) = (($ 1) <<ᵢ ($ (Z_of_nat n))) <->
                   Int.ltu ($ 0) v = true ))) .

(* OSRdyTbl & OSRdyGrp *)
Definition AOSRdyTblGrp (vl:vallist) (v:val) :=
  AOSRdyTbl vl ** AOSRdyGrp v ** [|RL_Tbl_Grp_P vl v /\ prio_in_tbl (Int.repr OS_IDLE_PRIO) vl|].

(* high level assertion *)
Notation HTCBList tcbls:= (Aabsdata abstcblsid (abstcblist tcbls)).

Notation HTime t := (Aabsdata ostmid (ostm t)).

Notation HCurTCB tid:= (Aabsdata curtid (oscurt tid)).

Notation HECBList ecbls:= (Aabsdata absecblsid (absecblist  ecbls)).

Notation Hhier Hier := (Aabsdata ierid (hier Hier)).

Definition AGVars:=
  (GV OSRunning @ (Tint8) |-> Vint32 (Int.repr 1)) ** 
  (EX v, GV OSPrioHighRdy @ (Tint8) |-> Vint32 v ** [| Int.unsigned v <= 63 |]) ** 
  (EX v, GV OSCtxSwCtr @ (Tint32) |-> Vint32 v) ** 
  (EX v,GV OSTCBHighRdy  @ (Tptr OS_TCB) |-> Vptr v) **  
  (EX v, GV OSPrioCur @ (Tint8) |-> Vint32 v ** [| Int.unsigned v <= 63 |])  **
  (EX v, GV OSIntExitY @ (Tint8) |-> Vint32 v) **
  (EX v, GV CGEM_regs_INTMUX1 @ (Tint32) |-> Vint32 v) **
  (EX v, GV CGEM_regs_INTMUX2 @ (Tint32) |-> Vint32 v) **
  (EX v, GV CGEM_regs_INTMUX3 @ (Tint32) |-> Vint32 v) **
  (EX v, GV INT_MUX_L @ (Tint32) |-> Vint32 v) **
  (EX v, GV INT_MUX_H @ (Tint32) |-> Vint32 v) ** 
  (EX v, GV OSIntNesting @ Tint32 |-> (Vint32 v)) ** 
  (EX v, GV OSLockNesting @ Tint32 |-> (Vint32 v)).

Definition RH_CurTCB ct (tcbls:TcbMod.map) := exists p st msg sus, get tcbls ct = Some (p,st,msg,sus) (*/\ isrdy st*).
(*-----------------------------------------------------------------------------------*)
(* relation of low level and high level                                              *)
(*-----------------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------------------*)
(* os_event vallist                                                                  *)
(*-----------------------------------------------------------------------------------*)
Definition V_OSEventType (vl:vallist) := nth_val 0 vl.
Definition V_OSEventGrp  (vl:vallist) := nth_val 1 vl.
Definition V_OSEventCnt  (vl:vallist) := nth_val 2 vl.
Definition V_OSEventPtr  (vl:vallist) := nth_val 3 vl.
Definition V_OSEventListPtr (vl:vallist) := nth_val 5 vl.
Definition V_OSPostEventGrp  (vl:vallist) := nth_val 6 vl.

(*-----------------------------------------------------------------------------------*)
(* os_q vallist                                                                      *)
(*-----------------------------------------------------------------------------------*)
Definition V_OSQPtr      (vl:vallist) := nth_val 0 vl.
Definition V_OSQStart    (vl:vallist) := nth_val 1 vl.
Definition V_OSQEnd      (vl:vallist) := nth_val 2 vl.
Definition V_OSQIn       (vl:vallist) := nth_val 3 vl.
Definition V_OSQOut      (vl:vallist) := nth_val 4 vl.
Definition V_OSQSize     (vl:vallist) := nth_val 5 vl.
Definition V_OSQEntries  (vl:vallist) := nth_val 6 vl.
Definition V_qfreeblk    (vl:vallist) := nth_val 7 vl.

(*-----------------------------------------------------------------------------------*)
(* os_q_freeblk vallist                                                              *)
(*-----------------------------------------------------------------------------------*)
Definition V_nextblk     (vl:vallist) := nth_val 0 vl.

(*-----------------------------------------------------------------------------------*)
(* os_q_ptr vallist                                                                  *)
(*-----------------------------------------------------------------------------------*)
Definition V_next        (vl:vallist) := nth_val 0 vl.
Definition V_qeventptr   (vl:vallist) := nth_val 1 vl.

(*-----------------------------------------------------------------------------------*)
(* low level data struct assertion used in os_q                                      *)
(*-----------------------------------------------------------------------------------*)
Open Scope int_scope.

Definition EVENT_TBL_INIT_VL:= 
  Vint32 (Int.zero) :: 
  Vint32 (Int.zero):: 
  Vint32 (Int.zero)::
  Vint32 (Int.zero):: 
  Vint32 (Int.zero)::
  Vint32 (Int.zero)::
  Vint32 (Int.zero)::
  Vint32 (Int.zero)::nil.

Definition id_addrval' (v : val) (id :var) (t : type):=
     match v with
     | Vptr av => id_addrval av id t
     | _ => None
    end.

Fixpoint ecbf_sllseg (head tailnext : val)  (l:list vallist) (t:type) (next: vallist -> option val):=
  match l with
    | nil => [| head = tailnext |]
    | vl::l' => EX  vn ltbl vla lpetbl petbl,
                [|next vl = Some vn|] **
                node head vl t ** 
                [| id_addrval' head OSEventTbl OS_EVENT = Some ltbl |]** 
                Aarray ltbl (Tarray Tint8 (nat_of_Z OS_EVENT_TBL_SIZE)) vla**
                [| id_addrval' head OSPostEventTbl OS_EVENT = Some lpetbl |] **
                Aarray lpetbl (Tarray Tint8 (nat_of_Z OS_EVENT_TBL_SIZE)) petbl **
                [| V_OSEventType vl = Some (V$OS_EVENT_TYPE_UNUSED) |] ** 
                ecbf_sllseg vn tailnext l' t next
  end.

Definition ecbf_sll := 
  fun (head : val) (l : list vallist) (t : type) (next : vallist -> option val) =>
    ecbf_sllseg head Vnull l t next.

Definition sll head l t next := sllseg head Vnull l t next.

Definition AOSEventFreeList p (l:list vallist) :=
  (GV OSEventFreeList @ (Tptr OS_EVENT) |-> p) ** 
       ecbf_sll p l OS_EVENT V_OSEventListPtr. 
                                                   
Notation beq_addrval := beq_tid.
(*
Definition beq_addrval := 
fun n m : addrval => 
  let (b, i) := n in let (b', i') := m in beq_pos b b' && Int.eq i i'.
 *)

Lemma addrval_eq_dec: forall x y: addrval, {x=y} + {x<>y}.
Proof.
  intros. destruct (beq_addrval x y) eqn:E.
  + apply  tidspec.beq_true_eq in E. tauto.
  + apply  tidspec.beq_false_neq in E. tauto.
Qed.

Definition beq_val (v1:val) (v2:val) :=
  match v1, v2 with
    | Vundef, Vundef => true
    | Vnull, Vnull => true
    | Vint32 i1, Vint32 i2 => Int.eq i1 i2
    | Vptr p1, Vptr p2 => beq_addrval p1 p2
    | _, _ => false                              
  end.

Fixpoint ptr_in_ecbsllseg (p:val) (head:val) (l:list vallist) : Prop :=
  match l with
  | nil => False
  | h::l' =>
    match head with
      Vnull => False
    | Vptr a => 
      if (beq_val p head)
      then True
      else
        match (V_OSEventListPtr h) with 
        | None => False
        | Some next => ptr_in_ecbsllseg p next l'
        end
    | _ => False
    end
  end. 

Definition ptr_in_ecblist := ptr_in_ecbsllseg.  


Definition AOSQFreeList (l:list vallist):=
  EX p,(GV OSQFreeList @ (Tptr OS_Q) |-> p) **  sll p l OS_Q V_OSQPtr. 

Fixpoint qblkf_sllseg (head tailnext : val)  (l:list vallist) (t:type) (next: vallist -> option val):=
  match l with
    | nil => [| head = tailnext |]
    | vl::l' => EX vn ltbl vla,
                [|next vl = Some vn|] **
                node head vl t ** 
                [| id_addrval' head msgqueuetbl OS_Q_FREEBLK = Some ltbl |]** 
                Aarray ltbl (Tarray (Tptr Tvoid) (nat_of_Z OS_MAX_Q_SIZE)) vla**
                qblkf_sllseg vn tailnext l' t next
  end.

Definition qblkf_sll := 
  fun (head : val) (l : list vallist) (t : type) (next : vallist -> option val) =>
    qblkf_sllseg head Vnull l t next.

Definition AOSQFreeBlk (l:list vallist):=
  EX p,(GV OSQFreeBlk @ (Tptr OS_Q_FREEBLK) |-> p) 
         **  qblkf_sll p l OS_Q_FREEBLK V_nextblk.
 
(*-----------------------------------------------------------------------------------*)
(* wellformed OSQ                                                                    *)
(*-----------------------------------------------------------------------------------*)
Open Scope Z_scope.
Open Scope int_scope.
Definition ptr_minus (l1 l2:addrval) (t:type) :=
  let (b1,i1):=l1 in
  let (b2,i2):=l2 in
  if (b1=? b2)%positive then
    Some (nat_of_Z (Int.unsigned (Int.divu (Int.sub i1 i2) (Int.repr (Z_of_nat (typelen t))))))
  else None. 

Definition ptr_offset_right (l1 l2:addrval) (t:type) :=
  let (b1,i1):=l1 in
  let (b2,i2):=l2 in
  if (b1=? b2)%positive then
    Int.ltu i1 i2 = false /\
    Int.modu (Int.sub i1 i2) ($ (Z_of_nat (typelen t))) = $ 0
  else False. 

Definition qend_right qend qtbl qsize :=
  snd qtbl = Int.repr 4 /\
  ptr_offset_right qend qtbl (Tptr Tvoid) /\
  ptr_minus qend qtbl (Tptr Tvoid) = Some (nat_of_Z (Int.unsigned qsize)).

Definition arrayelem_addr_right p qtbl qsize :=
  exists n, ptr_offset_right p qtbl (Tptr Tvoid) /\
            ptr_minus p qtbl (Tptr Tvoid) = Some n /\ 
            (n < (nat_of_Z (Int.unsigned qsize)))%nat.

Definition WellformedOSQ (osq:vallist):=
  exists qstart qend qin qout qsize qtbl qblk qentries,
    V_OSQStart osq = Some (Vptr qstart) /\ 
    V_OSQEnd osq = Some (Vptr qend) /\ 
    V_OSQIn osq = Some (Vptr qin) /\
    V_OSQOut osq = Some (Vptr qout) /\
    V_OSQSize osq = Some (Vint32 qsize) /\
    V_qfreeblk osq = Some (Vptr qblk) /\
    id_addrval qblk msgqueuetbl OS_Q_FREEBLK = Some qtbl /\
    0 < Int.unsigned qsize <= OS_MAX_Q_SIZE /\ qstart = qtbl /\ 
    qend_right qend qtbl qsize /\
    arrayelem_addr_right qin qtbl qsize /\ 
    arrayelem_addr_right qout qtbl qsize /\ 
    V_OSQEntries osq = Some (Vint32 qentries) /\
    Int.unsigned qentries <= Int.unsigned qsize .

Close Scope Z_scope.

Definition EventCtr := ((vallist * vallist) * vallist)%type.

Open Scope Z_scope.

Definition RH_ECB_P (msgq : absecb.B) := 
  match msgq with
    |(ed,waitset) =>
     match ed with
       | absmsgq msgl qsize pwl => 
         (msgl <> nil -> waitset = nil) /\
         (waitset <> nil -> msgl = nil) /\ 
         (length msgl <> Z.to_nat (Int.unsigned qsize) -> pwl = nil) /\
         (pwl <> nil -> length msgl = Z.to_nat (Int.unsigned qsize)) 
       | abssem z => 
         (Int.ltu Int.zero z = true -> waitset = nil) /\
         (waitset <> nil -> Int.eq Int.zero z = true)
       | absmbox msg=>
         (msg <> Vnull -> waitset = nil) /\
         (waitset <> nil -> msg = Vnull)
       | absmutexsem pr owner  =>
         (owner = None -> waitset = nil) /\
         (forall tid opr,
            owner = Some (tid,opr) ->
            Int.ltu pr opr = true /\ Int.unsigned opr < 64) /\
         (waitset <> nil -> owner <> None) /\ (Int.unsigned pr < 64)
       | absport => True 
     end
  end.

Definition offset_zero (l:addrval) := exists b, l = (b,Int.zero).

Definition AOSEventTbl letbl etbl := 
  Aarray letbl (Tarray Tint8 (nat_of_Z OS_EVENT_TBL_SIZE)) etbl 
         ** [| array_type_vallist_match Tint8 etbl |].

Definition AOSPostEventTbl lpetbl petbl := 
  Aarray lpetbl (Tarray Tint8 (nat_of_Z OS_EVENT_TBL_SIZE)) petbl 
         ** [| array_type_vallist_match Tint8 petbl |].

Definition AOSEvent losevent osevent etbl petbl := 
  EX letbl egrp lpetbl pegrp,
  node losevent osevent OS_EVENT  (*包含除了结构体和数组外的其他值*)
          ** AOSEventTbl letbl etbl ** 
          [| id_addrval' losevent OSEventTbl OS_EVENT = Some letbl |] ** 
          [| V_OSEventGrp osevent = Some egrp |] ** [|RL_Tbl_Grp_P etbl egrp|]
          ** AOSPostEventTbl lpetbl petbl ** 
          [| id_addrval' losevent OSPostEventTbl OS_EVENT = Some lpetbl |] ** 
          [| V_OSPostEventGrp osevent = Some pegrp |] ** 
          [|RL_Tbl_Grp_P petbl pegrp|].

Definition AOSQCtr losq osq :=
  node losq osq OS_Q  **
       [| WellformedOSQ osq |].

Definition AOSQBlk losqblk osqblk  msgtbl :=
  EX lmsgtbl,
  node losqblk  osqblk OS_Q_FREEBLK **
          [| id_addrval' losqblk msgqueuetbl OS_Q_FREEBLK = Some lmsgtbl |] ** 
          Aarray lmsgtbl (Tarray (Tptr Tvoid) (nat_of_Z OS_MAX_Q_SIZE)) msgtbl.

(* Low etbl -> High msgq High tcb *)

Definition distance (v1 v2:addrval) :=
  Int.unsigned (Int.divu (Int.sub (snd v2) (snd v1)) (Int.repr (Z_of_nat (typelen (Tptr Tvoid))))).

(* Remove the initial elements from vl *)
Fixpoint vallist_post (first:nat) (vl:vallist) :=
  match first with
    | 0%nat => vl
    | S n => match vl with 
               | nil => nil
               | v::vl' => vallist_post n vl'
             end
  end.

(* Take the initial elements from vl *)
Fixpoint vallist_pre (last:nat) (vl:vallist):= 
  match last with
    | 0%nat=> nil
    | S n => match vl with
               | nil => nil
               | v::vl' => v::(vallist_pre n vl')
             end
  end.

Definition vallist_seg (first last:nat) (vl:vallist) :=
  vallist_post first (vallist_pre last vl).

Fixpoint isptr_list vl:=
  match vl with
    | nil => True
    | v::vl' => isptr v /\ isptr_list vl'
  end.

Definition MatchLHMsgList osq msgtbl msgl := 
  exists  qstart qin qout qsize d1 d2 qens,
    V_OSQStart osq = Some (Vptr qstart) /\ 
    V_OSQIn osq = Some (Vptr qin) /\
    V_OSQOut osq = Some (Vptr qout) /\ 
    V_OSQSize osq = Some (Vint32 qsize) /\
    V_OSQEntries osq = Some (Vint32 qens) /\
    d1 = distance qstart qout /\ 
    d2 = distance qstart qin /\
    (
      ( d2 > d1->
        vallist_seg (nat_of_Z d1) (nat_of_Z d2) msgtbl = msgl)
      /\ 
      ( d2 < d1 ->
        (vallist_seg (nat_of_Z d1) 
                                (nat_of_Z (Int.unsigned qsize)) msgtbl)++
                                                                       (vallist_seg 0 (nat_of_Z d2)
                                                                                    msgtbl) = msgl) /\
      (d2 = d1 ->
       (Int.eq qens Int.zero = true /\ msgl = nil) \/
       (Int.eq qens qsize = true /\
        (vallist_seg (nat_of_Z d1) 
                     (nat_of_Z (Int.unsigned qsize)) msgtbl)++
                                                            (vallist_seg 0 (nat_of_Z d2)
                                                                         msgtbl) = msgl) ))
    /\ isptr_list msgl. 

Definition MatchLHMsgLength osq (msgl : vallist):=
  exists qents, 
    V_OSQEntries osq = Some (Vint32 qents)/\
    Int.unsigned qents = Z_of_nat (List.length msgl). 

Definition MatchLHMsgSize  osq qmaxlen :=
  exists qsize,  V_OSQSize osq = Some (Vint32 qsize) /\
                 qsize = ($ qmaxlen) /\ 0<=qmaxlen <= Int.max_unsigned.

(* Low msgtbl <-> High msgl *)

Definition MatchMutexSem (x y : val) (pr : priority) (o : owner) :=
  exists v op, x = Vint32 v /\ Int.unsigned v <= 65535 /\
                  pr = (Int.shru v ($ 8)) /\ 
                  op = (Int.and v ($ OS_MUTEX_KEEP_LOWER_8)) /\
                  (op = $ OS_MUTEX_AVAILABLE -> o = None /\ y = Vnull) /\
                  (op <> $ OS_MUTEX_AVAILABLE -> exists tid,  y = Vptr tid /\ o = Some (tid, op)).

Definition  RLH_ECBData_P (lecb: EventData) (hecb:absecb.B) :=
  match lecb , hecb with
    | (DMsgQ a osq osqblk msgtbl), ((absmsgq msgl qmaxlen  pqwaitset),qwaitset) =>
      MatchLHMsgList osq msgtbl msgl /\
      MatchLHMsgLength osq msgl/\
      MatchLHMsgSize osq (Int.unsigned qmaxlen) /\  RH_ECB_P hecb       
    | (DSem n1), (abssem n2, waitset) => 
      n1 = n2 /\ RH_ECB_P hecb
    | (DMbox a), (absmbox b,waitset) =>
      a = b /\ RH_ECB_P hecb
    | (DMutex x y), (absmutexsem pr own, waitset) =>
      MatchMutexSem x y pr own /\ RH_ECB_P hecb
    | (DPort), (absport, wt) => RH_ECB_P hecb
    | _ , _ => False
  end.

(* Definition  RLH_ECBData_P (lecb: EventData) (hecb:absecb.B) := *)
(*   match lecb , hecb with *)
(*     | (DMsgQ a osq osqblk msgtbl), ((absmsgq msgl qmaxlen),qwaitset) => *)
(*       MatchLHMsgList osq msgtbl msgl /\ *)
(*       MatchLHMsgLength osq msgl/\ *)
(*       MatchLHMsgSize osq (Int.unsigned qmaxlen) /\  RH_ECB_P hecb        *)
(*     | (DSem n1), (abssem n2, waitset) =>  *)
(*       n1 = n2 /\ RH_ECB_P hecb *)
(*     | (DMbox a), (absmbox b,waitset) => *)
(*       a = b /\ RH_ECB_P hecb *)
(*     | (DMutex x y), (absmutexsem pr own, waitset) => *)
(*       MatchMutexSem x y pr own /\ RH_ECB_P hecb *)
(*     | _ , _ => False *)
(*   end. *)

Definition RH_TCBList_ECBList_Q_P (ecbls:EcbMod.map) (tcbls:TcbMod.map) (ct:tid):=  
  (forall eid x y pqwaitset qwaitset tid,
     (get ecbls eid = Some (absmsgq x y pqwaitset,qwaitset) /\
      In tid qwaitset)  -> 
     exists prio m n sus, get tcbls tid = Some (prio,wait (os_stat_q eid) n,m,sus)) /\
  (forall eid x y pqwaitset qwaitset tid,
     (get ecbls eid = Some (absmsgq x y pqwaitset,qwaitset) /\
      In tid pqwaitset)  -> 
     exists prio m n sus, get tcbls tid = Some (prio,wait (os_stat_postq eid) n,m,sus)) /\  
  (forall  p tid eid n m sus,  
     get tcbls tid = Some (p,wait (os_stat_q eid) n,m,sus)-> 
     (exists x y pqwaitset qwaitset, 
        get ecbls eid = Some (absmsgq x y pqwaitset,qwaitset) /\ 
        In tid qwaitset)) /\
  (forall  p tid eid n m sus,  
     get tcbls tid = Some (p,wait (os_stat_postq eid) n,m,sus)-> 
     (exists x y pqwaitset qwaitset, 
        get ecbls eid = Some (absmsgq x y pqwaitset,qwaitset) /\ 
        In tid pqwaitset)).

(* Definition RH_TCBList_ECBList_Q_P (ecbls:EcbMod.map) (tcbls:TcbMod.map) (ct:tid):=   *)
(*   (forall eid x y qwaitset tid, *)
(*      (get ecbls eid = Some (absmsgq x y,qwaitset) /\ *)
(*       In tid qwaitset)  ->  *)
(*      exists prio m n, get tcbls tid = Some (prio,wait (os_stat_q eid) n,m)) /\    *)
(*   (forall  p tid eid n m,   *)
(*      get tcbls tid = Some (p,wait (os_stat_q eid) n,m)->  *)
(*      (exists x y qwaitset,  *)
(*         get ecbls eid = Some (absmsgq x y,qwaitset) /\  *)
(*         In tid qwaitset)). *)

Definition RH_TCBList_ECBList_SEM_P (ecbls:EcbMod.map) (tcbls:TcbMod.map) (ct:tid) :=
  (forall eid n wls tid,
     (get ecbls eid = Some (abssem n, wls) /\ In tid wls) ->
     (exists prio msg t sus, 
        get tcbls tid = Some (prio, wait (os_stat_sem eid) t, msg, sus))) /\
  (forall p tid eid t msg sus,
     get tcbls tid = Some (p, wait (os_stat_sem eid) t, msg, sus) ->
     (exists n wls,
        get ecbls eid = Some (abssem n, wls) /\
        In tid wls)).

Definition RH_TCBList_ECBList_MBOX_P (ecbls:EcbMod.map) (tcbls:TcbMod.map) (ct:tid) :=
  (forall eid n wls tid,
     (get ecbls eid = Some (absmbox n, wls) /\ In tid wls) ->
     (exists prio msg t sus, 
        get tcbls tid = Some (prio, wait (os_stat_mbox eid) t, msg, sus))) /\
  (forall p tid eid t msg sus,
     get tcbls tid = Some (p, wait (os_stat_mbox eid) t, msg, sus) ->
     (exists n wls,
        get ecbls eid = Some (absmbox n, wls) /\
        In tid wls)).

(*Definition RH_TCBList_ECBList_MUTEX_NODUP (ecbls:EcbMod.map) (tcbls:TcbMod.map) :=
        forall tid eid prio state msg pr owner,
        TcbMod.get tcbls tid = Some (prio, state, msg) ->
        EcbMod.get ecbls eid = Some (absmutexsem pr owner, nil) ->
        prio <> pr.
*)

(* copy from abs_op.v *)
Definition prio_available prio tls:=
  forall t p x y s, get tls t = Some (p, x, y, s) -> Int.eq prio p = false.

Definition RH_TCBList_ECBList_MUTEX_OWNER_P ecbls (tcbls:TcbMod.map) :=
  (forall eid pip wls,
     get ecbls eid = Some (absmutexsem pip None, wls) ->
     prio_available pip tcbls) /\
  (forall eid pip wls tid pt st m prio sus,
     get ecbls eid = Some (absmutexsem pip (Some (tid,pt)), wls) ->
     get tcbls tid = Some (prio, st, m, sus) ->
     ~(In tid wls) ->
     prio <> pip ->
     prio_available pip tcbls) /\
  (forall eid1 eid2 pip1 pip2 ow1 ow2 wls1 wls2, 
             get ecbls eid1 = Some (absmutexsem pip1 ow1, wls1) ->
             get ecbls eid2 = Some (absmutexsem pip2 ow2, wls2) ->
              eid1 <> eid2 ->
              pip1 <> pip2).

Definition RH_TCBList_ECBList_MUTEX_OWNER ecbls (tcbls:TcbMod.map) :=
  forall eid pr wls opr tid,
     (get ecbls eid = Some (absmutexsem pr (Some (tid, opr)), wls)) ->
     (exists prio msg st sus, get tcbls tid = Some (prio, st, msg, sus))
     /\ ~(In tid wls).
        
Definition RH_TCBList_ECBList_MUTEX_P (ecbls:EcbMod.map) (tcbls:TcbMod.map) (ct:tid) :=
  (forall eid n1 n2 wls tid,
     (get ecbls eid = Some (absmutexsem n1 n2, wls) /\ In tid wls) ->
     (exists prio msg t sus, 
        get tcbls tid = Some (prio, wait (os_stat_mutexsem eid) t, msg, sus))) /\
  (forall p tid eid t msg sus,
     get tcbls tid = Some (p, wait (os_stat_mutexsem eid) t, msg, sus) ->
     (exists n1 n2 wls,
        get ecbls eid = Some (absmutexsem n1 n2, wls) /\
        In tid wls)) /\
  RH_TCBList_ECBList_MUTEX_OWNER ecbls tcbls /\ 
  RH_TCBList_ECBList_MUTEX_OWNER_P ecbls tcbls. 
(* /\
  RH_TCBList_ECBList_MUTEX_NODUP ecbls tcbls.*)

Definition RH_TCBList_ECBList_PORT_P (ecbls:EcbMod.map) (tcbls:TcbMod.map) (ct:tid) :=
  (forall eid wls tid,
     (get ecbls eid = Some (absport, wls) /\ In tid wls) ->
     (exists prio msg t sus, 
        get tcbls tid = Some (prio, wait (os_stat_port eid) t, msg, sus))) /\
  (forall p tid eid t msg sus,
     get tcbls tid = Some (p, wait (os_stat_port eid) t, msg, sus) ->
     (exists wls,
        get ecbls eid = Some (absport, wls) /\
        In tid wls)).

Definition RH_TCBList_ECBList_P ecbls tcbls ct:=
  RH_TCBList_ECBList_Q_P ecbls tcbls ct /\
  RH_TCBList_ECBList_SEM_P ecbls tcbls ct /\ 
  RH_TCBList_ECBList_MBOX_P ecbls tcbls ct /\
  RH_TCBList_ECBList_MUTEX_P ecbls tcbls ct /\ 
  RH_TCBList_ECBList_PORT_P ecbls tcbls ct.

(*-----------------------------------------------------------------------------------*)
(* Low qptrlist <-----> High mqls                                                    *)
(*-----------------------------------------------------------------------------------*)

Definition AMsgData losq osq osqblk msgtbl:=
      EX losqblk, 
      AOSQCtr losq osq **
              [| V_qfreeblk osq = Some losqblk |] ** 
              AOSQBlk losqblk osqblk msgtbl.

Definition AEventData:=
  fun (osevent : vallist) (d : EventData) =>
    match d with
      | DMsgQ a osq osqblk msgtbl =>
        [|V_OSEventPtr osevent = Some a|] **
                                          [|V_OSEventType osevent = Some (V$OS_EVENT_TYPE_Q)|] **
                                          AMsgData a osq osqblk msgtbl
                            
      | DSem z =>  [|V_OSEventType osevent = Some (V$OS_EVENT_TYPE_SEM)|] **
                   [| V_OSEventCnt osevent = Some (Vint32 z) |] ** [| Int.ltu z (Int.repr 65536) = true |]
                                                                          
      | DMbox msg => [|V_OSEventType osevent = Some (V$OS_EVENT_TYPE_MBOX)|] **
                     [| V_OSEventPtr osevent = Some msg |]
                                                                             
      | DMutex a b => [|V_OSEventType osevent = Some (V$OS_EVENT_TYPE_MUTEX)|] **
                      [| V_OSEventCnt osevent = Some a |] **  [| V_OSEventPtr osevent = Some b|]
      | DPort => [|V_OSEventType osevent = Some (V$OS_EVENT_TYPE_PORT)|]
    end.

Definition AEventNode:=
  fun (v : val) (osevent etbl petbl : vallist) (d : EventData) =>
    AOSEvent v osevent etbl petbl ** AEventData osevent d.

Fixpoint evsllseg (head  tailnext : val) (vl:list EventCtr)
         (ecbls : list EventData) {struct vl}: asrt :=
  match vl with
    | nil => [|head = tailnext /\ ecbls = nil|]
    | l::vl'=>
      match ecbls with
        | nil => Afalse
        | enode :: ecbls' =>
          match l with
            | (osevent, etbl, petbl) =>
              EX vn, 
                 [|V_OSEventListPtr osevent = Some vn|] **
                 AEventNode head osevent etbl petbl enode ** 
                 evsllseg vn tailnext vl' ecbls'
          end
      end
  end. 

Definition PrioWaitInQ prio etbl := 
  exists x y z,  
    0<=prio<64 /\
    x = Int.and ($ prio) ($ 7) /\ y = Int.shru ($ prio) ($ 3) /\
                                  nth_val (nat_of_Z (Int.unsigned y)) etbl = Some (Vint32 z) /\
                                  Int.and z (Int.shl Int.one x) = (Int.shl Int.one x).

Definition RLH_ECB_ETbl_Q_P (l:addrval) (ecb : EventCtr) tcbls :=
  match ecb with
    | (osevent,etbl,petbl) => 
      forall prio, PrioWaitInQ prio etbl ->
                   V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_Q)) ->
                   (exists tid n m sus,
                      get tcbls tid = Some ((Int.repr prio),wait (os_stat_q l) n,m,sus))
  end.

Definition RLH_ECB_ETbl_SEM_P (l:addrval) (ecb : EventCtr) tcbls :=
  match ecb with
    | (osevent,etbl,petbl) => 
      forall prio, PrioWaitInQ prio etbl ->
                   V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_SEM)) ->
                   (exists tid n m sus,
                      get tcbls tid = Some ((Int.repr prio),wait (os_stat_sem l) n,m,sus))
  end.

Definition RLH_ECB_ETbl_MBOX_P (l:addrval) (ecb : EventCtr) tcbls :=
  match ecb with
    | (osevent,etbl,petbl) => 
      forall prio, PrioWaitInQ prio etbl ->
                   V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_MBOX)) ->
                   (exists tid n m sus,
                      get tcbls tid = Some ((Int.repr prio),wait (os_stat_mbox l) n,m,sus))
  end.

Definition RLH_ECB_ETbl_MUTEX_P (l:addrval) (ecb : EventCtr) tcbls :=
  match ecb with
    | (osevent,etbl,petbl) => 
      forall prio, PrioWaitInQ prio etbl ->
                   V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_MUTEX)) ->
                   (exists tid n m sus,
                      get tcbls tid = Some ((Int.repr prio),wait (os_stat_mutexsem l) n,m,sus))
  end.

Definition RLH_ECB_ETbl_PORT_P (l:addrval) (ecb : EventCtr) tcbls :=
  match ecb with
    | (osevent,etbl,petbl) => 
      forall prio, PrioWaitInQ prio etbl ->
                   V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_PORT)) ->
                   (exists tid n m sus,
                      get tcbls tid = Some ((Int.repr prio),wait (os_stat_port l) n,m,sus))
  end.

Definition RHL_ECB_ETbl_Q_P (l:addrval) (ecb : EventCtr)  tcbls :=
  match ecb with
    | (osevent, etbl, petbl) => 
      forall prio m n tid sus, get tcbls tid = Some (prio,wait (os_stat_q l) n,m,sus) ->
                         PrioWaitInQ (Int.unsigned prio) etbl /\ V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_Q))
  end.

Definition RHL_ECB_ETbl_SEM_P (l:addrval) (ecb : EventCtr)  tcbls :=
  match ecb with
    | (osevent, etbl, petbl) => 
      forall prio m n tid sus, get tcbls tid = Some (prio,wait (os_stat_sem l) n,m,sus) ->
                         PrioWaitInQ (Int.unsigned prio) etbl /\ V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_SEM))
  end.

Definition RHL_ECB_ETbl_MBOX_P (l:addrval) (ecb : EventCtr)  tcbls :=
  match ecb with
    | (osevent, etbl, petbl) => 
      forall prio m n tid sus, get tcbls tid = Some (prio,wait (os_stat_mbox l) n,m,sus) ->
                         PrioWaitInQ (Int.unsigned prio) etbl /\ V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_MBOX))
  end.

Definition RHL_ECB_ETbl_MUTEX_P (l:addrval) (ecb : EventCtr)  tcbls :=
  match ecb with
    | (osevent, etbl, petbl) => 
      forall prio m n tid sus,
        get tcbls tid = Some (prio,wait (os_stat_mutexsem l) n,m,sus) ->
        PrioWaitInQ (Int.unsigned prio) etbl /\
        V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_MUTEX))
  end.

Definition RHL_ECB_ETbl_PORT_P (l:addrval) (ecb : EventCtr)  tcbls :=
  match ecb with
    | (osevent, etbl, petbl) => 
      forall prio m n tid sus,
        get tcbls tid = Some (prio,wait (os_stat_port l) n,m,sus) ->
        PrioWaitInQ (Int.unsigned prio) etbl /\
        V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_PORT))
  end.

Definition RLH_ECB_PETbl_Q_P (l:addrval) (ecb : EventCtr) tcbls :=  (*add OSPostEventTbl*)
  match ecb with
    | (osevent,etbl,petbl) => 
      forall prio, PrioWaitInQ prio petbl ->
                   V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_Q)) ->
                   (exists tid n m sus,
                      get tcbls tid = Some ((Int.repr prio),wait (os_stat_postq l) n,m,sus))
  end.
  
Definition RHL_ECB_PETbl_Q_P (l:addrval) (ecb : EventCtr)  tcbls := (*add OSPostEventTbl*)
  match ecb with
    | (osevent, etbl, petbl) => 
      forall prio m n tid sus, get tcbls tid = Some (prio,wait (os_stat_postq l) n,m,sus) ->
                         PrioWaitInQ (Int.unsigned prio) petbl /\ V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_Q))
  end.

Definition RLH_ECB_ETbl_P l ecb tcbls := 
  RLH_ECB_ETbl_Q_P l ecb tcbls /\
  RLH_ECB_ETbl_SEM_P l ecb tcbls /\
  RLH_ECB_ETbl_MBOX_P l ecb tcbls /\
  RLH_ECB_ETbl_MUTEX_P l ecb tcbls /\ 
  RLH_ECB_ETbl_PORT_P l ecb tcbls.

Definition RHL_ECB_ETbl_P l ecb tcbls := 
  RHL_ECB_ETbl_Q_P l ecb tcbls /\ 
  RHL_ECB_ETbl_SEM_P l ecb tcbls /\
  RHL_ECB_ETbl_MBOX_P l ecb tcbls /\
  RHL_ECB_ETbl_MUTEX_P l ecb tcbls/\ 
  RHL_ECB_ETbl_PORT_P l ecb tcbls.

Definition Event_Type_P osevent :=
  V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_Q)) \/  
  V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_SEM)) \/   
  V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_MBOX)) \/   
  V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_MUTEX)) \/ 
  V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_PORT)).

Definition R_ECB_ETbl_P (l:addrval) (ecb : EventCtr)  tcbls :=
  RLH_ECB_ETbl_P l ecb tcbls /\
  RHL_ECB_ETbl_P  l ecb tcbls /\
  Event_Type_P (fst (fst ecb)).

Definition R_ECB_PETbl_P (l:addrval) (ecb : EventCtr)  tcbls := (*add OSPostEventTbl*)
  RLH_ECB_PETbl_Q_P l ecb tcbls /\
  RHL_ECB_PETbl_Q_P  l ecb tcbls .

Fixpoint ECBList_P (v tl: val) (l:list EventCtr) (ecbls : list EventData) (mqls: EcbMod.map) 
         (tcbls : TcbMod.map) 
         {struct l} : Prop :=
  match l with
    | nil =>  ecbls=nil /\ mqls = emp /\ v = tl
    | vl :: l' =>  
      exists qid,
        v = Vptr qid /\ R_ECB_ETbl_P  qid vl tcbls /\ R_ECB_PETbl_P qid vl tcbls /\ 
        match ecbls with
          | nil => False
          | enode ::ecbls' =>
            match vl with
              | (osevent,etbl,petbl) =>
                exists  absmq mqls' v', 
                  V_OSEventListPtr osevent = Some v' /\
                  joinsig qid absmq mqls' mqls /\
                  RLH_ECBData_P enode absmq /\
                  ECBList_P v' tl l' ecbls' mqls' tcbls 
          end
      end
  end.

Definition AECBList  (l : list EventCtr)
           (ecbls : list EventData)   (els: EcbMod.map) (tcbls : TcbMod.map)
: asrt := 
  (EX p, (GV OSEventList @ (Tptr OS_EVENT) |-> p **  
                                                evsllseg p Vnull l ecbls) **[| ECBList_P p Vnull l ecbls els tcbls|]). 

(*-----------------------------------------------------------------------------------*)
(* Inv used in certifying OS *)
(*-----------------------------------------------------------------------------------*)
Definition isr_is_prop isr is:=
  forall (x:hid), ~(List.In x is) -> isr x =false.

Definition A_isr_is_prop :=EX isr is,Aisr isr ** Ais is ** [|isr_is_prop isr is|]. 

(* **
                   [| Mutex_TCBList_ECBList_P p1 (tcbl1 ++ (tcbcur::tcbl2)) ecbls|] *)

(*new inv defined by zhanghui*)

Fixpoint ptr_in_tcbdllseg (p:val) (head:val) (l:list vallist) : Prop :=
  match l with
    | nil => False
    | h::l' =>
      if (beq_val p head)
      then True
      else
        match (V_OSTCBNext h) with
          | None => False
          | Some next => ptr_in_tcbdllseg p next l'
        end
  end.

Definition tcblist (head headprev tail tailnext:val) (l:list vallist) (rtbl:vallist) (tcbls:TcbMod.map) :=
  tcbdllseg head headprev tail tailnext l ** [|TCBList_P head l rtbl tcbls|].

(*used in the new inv, hide the tcbdllseg*)
Definition ptr_in_tcblist := ptr_in_tcbdllseg.

(*ptrs of the dll does not change*)
Definition same_prev_next (vl1 vl2 : vallist) : Prop :=
  match (V_OSTCBNext vl1), (V_OSTCBNext vl2) with
    | (Some p1), (Some p2) =>
      p1 = p2 /\
      match (V_OSTCBPrev vl1), (V_OSTCBPrev vl2) with
        | (Some p3), (Some p4) => p3 = p4
        | _, _ => False
      end
    | _, _ => False
  end.

Definition TCB_Not_In ct head tcbl :=
 [|(~ptr_in_tcblist ct head tcbl) /\ exists a, ct = Vptr (a,Int.zero)|].

                   (* AOSTCBList' p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls ptfree ** *)
Definition AOSTCBList' (p1 p2: val) (l1 l2:list vallist) (rtbl : vallist)
           (hcurt:addrval)(tcbls : TcbMod.map) (pf : val) :=
  (
    EX tail1 tail2 tcbls1 tcbls2,
    (GV OSTCBList @ (Tptr OS_TCB) |-> p1) **
    tcbdllseg p1 Vnull tail1 p2 l1 ** 
    (GV OSTCBCur @ (Tptr OS_TCB) |-r-> p2) **
    tcbdllseg  p2 tail1 tail2 Vnull l2 **
    [|p1 <> Vnull /\ p2 = Vptr hcurt|] ** 
    [| join tcbls1 tcbls2 tcbls|] **
    [| TCBList_P p1 l1 rtbl tcbls1 |]**
    [| TCBList_P p2 l2 rtbl tcbls2 |]**
    tcbdllflag p1 (l1 ++ l2) **
    [|p2 <> pf|]
  ) \\//
  (
    EX tail,
    (
      GV OSTCBList @ (Tptr OS_TCB) |-> p1 **
      GV OSTCBCur @ (Tptr OS_TCB) |-r-> p2 **
      tcblist p1 Vnull tail Vnull (l1++l2) rtbl tcbls **
      TCB_Not_In p2 p1 (l1 ++ l2) **
      tcbdllflag p1 (l1 ++ l2) **
      [|p1 <> Vnull /\ p2 = Vptr hcurt|] ** 
      [|p2 = pf|]
    )
  ) .
  
Definition isflag (v : val) := v = Vint32 (Int.repr 1%Z) \/ v = Vint32 (Int.repr 0%Z).

Definition isevloc (v: val) :=
  (
    v = Vint32 (Int.repr __EvLoc_normal) \/
    v = Vint32 (Int.repr __EvLoc_ecbcre1) \/
    v = Vint32 (Int.repr __EvLoc_ecbcre2) \/
    v = Vint32 (Int.repr __EvLoc_ecbdel) 
  ).

Definition isevptr (v: val) := isptr v.

Definition OSLInv t lg :=
  EX v evloc muxptr semptr qptr, 
  PV (get_off_addr t flag_off) @ Tint8 |-r-> v **
  PV (get_off_addr t evloc_off) @ Tint8 |-r-> evloc ** 
  PV (get_off_addr t muxptr_off) @ (Tptr OS_EVENT) |-r-> muxptr ** 
  PV (get_off_addr t semptr_off) @ (Tptr OS_EVENT) |-r-> semptr ** 
  PV (get_off_addr t qptr_off) @ (Tptr OS_EVENT) |-r-> qptr ** 
  [| lg = logic_val  v :: logic_val evloc :: logic_val muxptr :: logic_val semptr :: logic_val qptr :: nil /\ 
      isflag v /\ isevloc evloc /\ isevptr muxptr /\ isevptr semptr /\ isevptr qptr |].  

(* Definition OSLInv t lg :=  EX v, PV (get_off_addr t flag_off) @ Tint8 |-r-> v **[|lg = logic_val  v :: nil /\ isflag v |]. *)
  (*OSLInv ct (logic_val 0 :: nil)*)
Definition AOSTCBList (p1 p2: val) (l1 l2:list vallist) (rtbl : vallist)
           (hcurt:addrval)(tcbls : TcbMod.map) :=
  EX tail1 tail2 tcbls1 tcbls2,
  (GV OSTCBList @ (Tptr OS_TCB) |-> p1) **
                                        tcbdllseg p1 Vnull tail1 p2 l1 ** 
                                        (GV OSTCBCur @ (Tptr OS_TCB) |-r-> p2) **
                                        tcbdllseg  p2 tail1 tail2 Vnull l2 **
                                        [|p1 <> Vnull /\ p2 = Vptr hcurt|] ** 
                                        [| join tcbls1 tcbls2 tcbls|] **
                                        [| TCBList_P p1 l1 rtbl tcbls1 |]**
                                        [| TCBList_P p2 l2 rtbl tcbls2 |].
     
Notation Hhinthandler Hinthandler := (Aabsdata inthandlerid (hinthandler Hinthandler)).
Notation HhinthandlerParam HinthandlerParam := (Aabsdata inthandlerParamid (hinthandlerParam HinthandlerParam)).
Notation Hhexchandler Hexchandler := (Aabsdata exchandlerid (hexchandler Hexchandler)).
(*Definition HinthandlerToInt (inthandler : Hinthandler) (num : int) : int32 :=
  match num with
  | _ => if Int.ltu num int_min then Int.zero
         else if Int.ltu int_max num then Int.zero
         else inthandler num 
  end.
Definition HinthandlerToInt (inthandler : Hinthandler) (num : int) : int32 :=
  match num with
  | _ => inthandler num 
  end.
Definition HinthandlerToAddrval (inthandlerParam : HinthandlerParam) (num : int) : addrval :=
  match num with
  | _ => inthandlerParam num 
  end.*)
Definition ZToInt (na : Z) : int:=
  match na with 
  | _ => Int.repr na
  end.
Definition IntToZ (n:int) : Z :=
  match n with
  | _ => if Int.eq Int.zero n then 0 else 1
  end.
Definition HinthandlerToListval (inthandler: Hinthandler) : vallist :=
  V$(IntToZ(inthandler (ZToInt 5)))::
  V$(IntToZ(inthandler (ZToInt 6)))::
  V$(IntToZ(inthandler (ZToInt 7)))::
  V$(IntToZ(inthandler (ZToInt 8)))::
  V$(IntToZ(inthandler (ZToInt 9)))::
  V$(IntToZ(inthandler (ZToInt 10))):: 
  V$(IntToZ(inthandler (ZToInt 11)))::
  V$(IntToZ(inthandler (ZToInt 12)))::
  V$(IntToZ(inthandler (ZToInt 13)))::
  V$(IntToZ(inthandler (ZToInt 14)))::
  V$(IntToZ(inthandler (ZToInt 15)))::nil. 
Definition AOSInthandler (inthandler: Hinthandler) :=
  GAarray IntHandler (Tarray Tint32 11) (HinthandlerToListval inthandler).
Definition Param5 := Vptr.
Definition Param6 := Vptr.
Definition Param7 := Vptr.
Definition Param8 := Vptr.
Definition Param9 := Vptr.
Definition Param10 := Vptr.
Definition Param11 := Vptr.
Definition Param12 := Vptr.
Definition Param13 := Vptr.
Definition Param14 := Vptr.
Definition Param15 := Vptr.
Definition HinthandlerParamToListval (inthandlerParam: HinthandlerParam) : vallist :=
  (Param5(inthandlerParam (ZToInt 5)))::
  (Param6(inthandlerParam (ZToInt 6)))::
  (Param7(inthandlerParam (ZToInt 7)))::
  (Param8(inthandlerParam (ZToInt 8)))::
  (Param9(inthandlerParam (ZToInt 9)))::
  (Param10(inthandlerParam (ZToInt 10)))::
  (Param11(inthandlerParam (ZToInt 11)))::
  (Param12(inthandlerParam (ZToInt 12)))::
  (Param13(inthandlerParam (ZToInt 13)))::
  (Param14(inthandlerParam (ZToInt 14)))::
  (Param15(inthandlerParam (ZToInt 15)))::nil.
Definition AOSInthandlerParam (inthandlerParam: HinthandlerParam) :=
  GAarray IntHandlerParam (Tarray (Tptr Tvoid) 11) (HinthandlerParamToListval inthandlerParam).
Definition AOSExchandler (exc:val) := GV exception_handler @ Tint32 |-> exc.

(*
Definition AOSRunning :=  GV OSRunning @ Tint32 |-> Vint32 (Int.one).
Definition AOSLockNesting := EX v, GV OSLockNesting @ Tint32 |-> (Vint32 v).
Definition AIntNumCurrent (v:val):=  GV IntNumCurrent @ Tint32 |-r-> v.
*)

Definition IntInv :=
  EX ier inthandler inthandlerParam exchandler,
                   Hhier ier **
                   Hhinthandler inthandler ** AOSInthandler inthandler ** 
                   HhinthandlerParam inthandlerParam ** AOSInthandlerParam inthandlerParam **
                   AOSExchandler (Vint32 exchandler) ** Hhexchandler exchandler.


(*************arrays for event information blocks*************)

(* Sem_info *)
Definition ASeminfo (l: addrval) (vll :list vallist) := 
  GV Sem_info @ (Tptr sem_info_t) |-> (Vptr l) **
  Aarray_new l (Tarray sem_info_t (nat_of_Z (OS_USER_MAX_EVENTS/3))) vll **  
  [| new_array_type_vallist_match sem_info_t vll /\ length vll = (nat_of_Z (OS_USER_MAX_EVENTS/3))|].

(* Pthread_Mutex *)
Definition APthreadMutex (l: addrval) (vll :list vallist) := 
  GV Pthread_Mutex @ (Tptr pthread_mutex_info_t) |-> (Vptr l) **
  Aarray_new l (Tarray pthread_mutex_info_t (nat_of_Z (OS_USER_MAX_EVENTS/3))) vll **  
  [| new_array_type_vallist_match pthread_mutex_info_t vll /\ length vll = (nat_of_Z (OS_USER_MAX_EVENTS/3))|].

(* Mq_Attr *)
Definition AMqAttr (l: addrval) (vll :list vallist) :=  
  GV Mq_Attr @ (Tptr mq_attr_t) |-> (Vptr l) **
  Aarray_new l (Tarray mq_attr_t (nat_of_Z (OS_USER_MAX_EVENTS/3))) vll **  
  [| new_array_type_vallist_match mq_attr_t vll /\ length vll = (nat_of_Z (OS_USER_MAX_EVENTS/3))|].

(*************end arrays for event information blocks*************) 

(*************start data structures for capability blocks*************)

(* Corresponds to struct cap_t.

   If type = CAP_CATEGORY_TYPE, then the first two fields are
   category_content and category_right. If type = CAP_OBJECT_TYPE,
   then the first field is object_right and third field is objec_t.
*)
Definition ACap (l: addrval) (v: int32 * cap_content_type) :=
    match v with 
    | (cap_type, (x, y, z)) =>
    let (b, i) := l in 
        PV l @ Tint32 |-> (Vint32 cap_type) **
        PV (b, i +ᵢ $ 4) @ Tint32 |-> Vint32 x **
        PV (b, i +ᵢ $ 8) @ Tint32 |-> Vint32 y ** 
        PV (b, i +ᵢ $ 12) @ Tptr Tvoid |-> z **
        [|isptr z|]
    end. 

(* Corresponds to an array of slot_t objects.

   Each slot_t object consists of slot type and capability
   (of type cap_t).
*)
Fixpoint ASlots (l: addrval) (n : nat) vl :=
  match vl, n with 
  | nil, 0%nat => Aemp
  | (slot_type, slot_cap)::vl', S n' =>
    let (b, i) := l in 
    PV l @ Tint32 |-> Vint32 slot_type **
    ACap (b, i +ᵢ $ 4) slot_cap **
    ASlots (b, i +ᵢ $ 20) n' vl'
  | _, _ => Afalse
  end.

(* Corresponds to struct cte_t.

   The three fields are guide_num, slot_num, and an array of slot_t
   objects.
*)
Definition Acnode (l: addrval)(vl: cnode_val_type) :=
  match vl with 
  | (guide_num, slot_num, slots)
  => let (b, i) := l in 
      PV (b, i)@ Tint32 |-> Vint32 guide_num **
      PV (b, i +ᵢ $ 4)@ Tint32 |-> Vint32 slot_num **
      ASlots (b, i +ᵢ $ 8) (Z.to_nat SLOT_NUM) slots **
      [|length slots = (Z.to_nat SLOT_NUM)|]
  end. 


(*CSpace Module*)

Notation CSpaceJoin := CSpaceptr2prioMod.joinsig.  

Definition CSPACENode (n: nat) abscspace :=
  (Int.repr (Z.of_nat n)) = abscspace.


(* ptrvl is a list of pointers to CSpace objects.
   cspacels is a mapping from CSpace pointers to the corresponding priority.

   TODO: what is the role of n?
*)
Fixpoint CSPACEList_P (ptrvl: vallist) (n : nat) (cspacels: CSpaceptr2prioMod.map) :=
  match ptrvl with
  | nil => cspacels = emp 
  | p :: ptrvl' => exists tid cspacels' abscspace', 
                      p = Vptr tid /\
                      CSpaceJoin tid abscspace' cspacels' cspacels /\
                      CSPACENode n abscspace' /\
                      CSPACEList_P ptrvl' (S n) cspacels'
  end. 

(* If some value in list lv is Vptr cspaceid, then that cspace id must exist
   in cspacels, with corresponding priority in range.
   
   这个是用来描述一种单向关系，就是children中的所有指针都在cspacels的键中
   但是cspacels的键不一定都在children中
*)
Definition ptrlv_in_cspace_ls (lv: vallist) (cspacels: CSpaceptr2prioMod.map) :=
  forall index cspaceid,
  nth_val (nat_of_Z (Int.unsigned index)) lv = Some (Vptr cspaceid) ->
  exists idx, get cspacels cspaceid = Some idx /\ (Int.unsigned idx < 64). 

Definition children_not_null lv n :=
  (forall i,(0 <= i < n)%nat -> 
  (exists v, (nth_val' i lv) = Vptr v)) /\
  (forall i,(n <= i < length lv)%nat -> (nth_val' i lv) = Vnull).

(* States that the pointer at l describes the OS_CSpace object vl. *)
Definition ACSpace (l: addrval) (vl: cspace_val_type) (cspacels: CSpaceptr2prioMod.map) :=
  match vl with 
  | (cnode, childnum, lv, v, prio) =>
      let (b, i) := l in 
        Acnode (b, i) cnode **
        PV (b, i +ᵢ Int.repr(Z.of_nat(typelen(Cte)))) @ Tint32 |-> Vint32 childnum **
        [|Int.unsigned childnum <= 64 /\ Int.unsigned prio < OS_LOWEST_PRIO|] **
        Aarray (b, i +ᵢ Int.repr(Z.of_nat(typelen(Cte))) +ᵢ (Int.repr 4)) (Tarray (Tcom_ptr cspace) (Z.to_nat(MaxChildNum))) lv **
        [|ptrlv_in_cspace_ls lv cspacels|] **  (*所有的这个指针都在map中*)
        [|array_type_vallist_match (Tcom_ptr cspace) lv |] **
        [|children_not_null lv (Z.to_nat (Int.unsigned childnum)) |] ** 
        PV (b, i +ᵢ Int.repr(Z.of_nat(typelen(Cte))) +ᵢ (Int.repr 4) +ᵢ
         Int.mul(Int.repr MaxChildNum)(Int.repr (Z.of_nat (typelen(Tcom_ptr cspace)))))@(Tptr CSPACE) |-> v **
         PV (b, i +ᵢ Int.repr(Z.of_nat(typelen(Cte))) +ᵢ (Int.repr 4) +ᵢ
         Int.mul(Int.repr MaxChildNum)(Int.repr (Z.of_nat (typelen(Tcom_ptr cspace)))) +ᵢ (Int.repr(Z.of_nat(typelen(Tptr CSPACE)))))@(Tint32) |-> Vint32 prio
  end. 

(* States that the list of pointers describes the list of OS_CSpace objects vl. *)
Fixpoint ACSpaceAarrayTptr (n : nat) (ptrvl: vallist) (vl: list cspace_val_type)
                           (cspacels: CSpaceptr2prioMod.map) :=
  match ptrvl, vl, n with 
  | nil, nil, 0%nat => Aemp
  | Vptr p :: ptrvl', v::vl', S n' => 
    ACSpace p v cspacels ** ACSpaceAarrayTptr  n' ptrvl' vl' cspacels
  | Vnull :: ptrvl',  v::vl', S n' =>
    ACSpaceAarrayTptr  n' ptrvl' vl' cspacels
  |_, _, _ => Afalse
  end.


(*描述一种双向关系,就是指针数组都是cspacels的键，cspacels的键都在指针数组中*)
Definition ptrvl_to_cspace_to_ptrvl ptrvl cspacels :=
  (forall index cspaceid,
  nth_val (nat_of_Z (Int.unsigned index)) ptrvl = Some (Vptr cspaceid) ->
  get cspacels cspaceid = Some index) /\
  (
    forall cspaceid index, 
    get cspacels cspaceid = Some index ->
    nth_val (nat_of_Z (Int.unsigned index)) ptrvl = Some (Vptr cspaceid)
  ). 

(* OSCSpacePrioTbl is a mapping from priorities to CSpace objects. *)
Definition AOSCSpacePrioTbl (l: addrval) (ptrvl: list val) (vl: list cspace_val_type)
                            (cspacels: CSpaceptr2prioMod.map) := 
  G& OSCSpacePrioTbl @ (Tarray (Tptr CSPACE) 64) == l ** 
  Aarray l (Tarray (Tptr CSPACE) 64) ptrvl ** 
  ACSpaceAarrayTptr 64%nat ptrvl vl cspacels **
  (*ptrvl_to_cspace_to_ptrvl ptrvl cspacels ** *)
  [|length ptrvl = 64%nat /\ length vl = 64%nat /\ array_type_vallist_match (Tptr CSPACE) ptrvl|].


(*-----------------------------------------------------------------------------------*)
(*  members of an EIB for semaphores                                            *)
(*-----------------------------------------------------------------------------------*)
Definition V_OSSINFOType (vl:vallist) := nth_val 0 vl.
Definition V_OSSINFOName (vl:vallist) := nth_val 1 vl.
Definition V_OSSINFOMaxvalue (vl:vallist) := nth_val 2 vl.
Definition V_OSSINFOCurvalue (vl:vallist) := nth_val 3 vl.
Definition V_OSSINFOOpencut (vl:vallist) := nth_val 4 vl.
Definition V_OSSINFOLinked (vl:vallist) := nth_val 5 vl.
Definition V_OSSINFOBlock (vl:vallist) := nth_val 6 vl.
Definition V_OSSINFOPevent (vl:vallist) := nth_val 7 vl.
(* 定义冗余，因此删除定义V_OSSINFOSemCap及定义RHL_EINFO_P中的相关条件*)
(* Definition V_OSSINFOSemCap (vl:vallist) := vallist_post 8 vl. *)

(*-----------------------------------------------------------------------------------*)
(* members of an EIB for mutexes                                                  *) 
(*-----------------------------------------------------------------------------------*)
Definition V_OSMUXINFOType (vl:vallist) := nth_val 0 vl.
Definition V_OSMUXINFOProtocol  (vl:vallist) := nth_val 1 vl.
Definition V_OSMUXINFOPrio_ceiling  (vl:vallist) := nth_val 2 vl.
Definition V_OSMUXINFOWaitq_type  (vl:vallist) := nth_val 3 vl.
Definition V_OSMUXINFOCancel_safe  (vl:vallist) := nth_val 4 vl.
Definition V_OSMUXINFOOwner  (vl:vallist) := nth_val 5 vl.
Definition V_OSMUXINFORecursive_cnt  (vl:vallist) := nth_val 6 vl.
Definition V_OSMUXINFOTasks_blocked  (vl:vallist) := nth_val 7 vl.
Definition V_OSMUXINFOPevent (vl:vallist) := nth_val 8 vl.
(* 定义冗余，因此删除定义V_OSSINFOSemCap及定义RHL_EIBlk_Mux_P中的相关条件*)
(* Definition V_OSMUXINFOMuxCap (vl:vallist) := vallist_post 9 vl. *)

(*-----------------------------------------------------------------------------------*)
(* members of an EIB for message queues                                      *) 
(*-----------------------------------------------------------------------------------*)
Definition V_QATTRmq_waittype (vl:vallist) := nth_val 0 vl.
Definition V_QATTRmq_flags (vl:vallist) := nth_val 1 vl.
Definition V_QATTRmq_maxmsg (vl:vallist) := nth_val 2 vl.
Definition V_QATTRmq_msgsize (vl:vallist) := nth_val 3 vl.
Definition V_QATTRmq_curmsgs (vl:vallist) := nth_val 4 vl.
Definition V_QATTRpevent (vl:vallist) := nth_val 5 vl.
(* 定义冗余，因此删除定义V_OSSINFOSemCap及定义RHL_EIBlk_Q_P中的相关条件*)
(* Definition V_QATTRmq_cap (vl:vallist) := vallist_post 6 vl. *)

(* Any semaphore in the sinfols mapping must have a corresponding
   entry in ecbls. *)
Definition RH_SEM_EINFO_ECB_P (ecbls: EcbMod.map) (sinfols: EmbMod.map) := 
  forall pos tp sc eid,
    get sinfols pos = Some (infotid eid, tp, sc) ->
    exists n wls, get ecbls eid = Some (abssem n, wls).


(* move from core communication for definition of notIncoreSemQ *)
Parameter OSSendSem_val : list ecbid.
Parameter OSIPCSem_val : list ecbid.
Parameter OSSemShared_val : ecbid.

(* move from original ifun_spec.v *)

Definition notIncoreSemQ (x: ecbid) := 
  ~ In x OSIPCSem_val /\ ~ In x OSSendSem_val /\ x <> OSSemShared_val /\ x <> dynrefcmsgQ_addr.

Definition Qdel_notcoresem (x: val) (O : osabst) : Prop :=
  match x with 
  | Vptr eid => notIncoreSemQ eid 
  | _ => True 
end.

Definition RH_SEM_NOT_IN_CORE_P (sinfols: EmbMod.map) 
  := 
    forall pos tp sc eid,
      get sinfols pos = Some (infotid eid, tp, sc) ->
      notIncoreSemQ eid.

(* Refinement relation for sem_info *)
Definition RHL_EINFO_P (vl: vallist) (absemb: infoeid * sem_tp * sem_cap_ty) (vhold: addrval) :=
  forall eid_opt tp sc,
    absemb = (eid_opt, tp, sc) ->
    V_OSSINFOType vl = Some (Vint32 tp) /\
      (
        (exists eid, eid_opt = infotid eid /\ V_OSSINFOPevent vl = Some (Vptr eid) /\ eid <> vhold) \/
          (eid_opt = infohold /\ V_OSSINFOPevent vl = Some (Vptr vhold)) \/
          (eid_opt = infonull /\ V_OSSINFOPevent vl = Some Vnull)
      ) (* /\ *)
    (* V_OSSINFOSemCap vl = List.map Vint32 sc *).

(* Refinement relation for list of sem_info *)
Fixpoint EIBArray_P (v: val) (l: list vallist) (embls: EmbMod.map) (vhold: addrval)
  {struct l} : Prop :=
    match l with
    | nil => embls = emp
    | vl :: l' => (
        exists pos embls' absemb v',
          v = Vint32 pos /\
          v' = Vint32 (Int.add pos Int.one) /\
          joinsig pos absemb embls' embls /\
          RHL_EINFO_P vl absemb vhold /\
          EIBArray_P v' l' embls'  vhold 
    )
    end.

Fixpoint AEvtCap (l: addrval) capl fieldname eibtype := 
  match l with
    (b, o) => 
      match capl with
        vl :: capl' => (
          EX l', 
          Aarray l' (Tarray Tint8 (nat_of_Z (OS_MAX_TASKS-OS_N_SYS_TASKS))) vl
            ** [| id_addrval l fieldname eibtype = Some l' |]
            ** [| array_type_vallist_match Tint8 vl |]
            ** [| length vl = nat_of_Z (OS_MAX_TASKS-OS_N_SYS_TASKS) |] 
            ** AEvtCap (b, Int.add o ($(Z_of_nat (typelen eibtype)))) capl' fieldname eibtype
        )
      | nil => Aemp
      end
  end.

Definition ASemCap l capl := AEvtCap l capl sem_cap sem_info_t.

(* Fixpoint ASemCap (l: addrval) capl := *)
(*   match l with *)
(*     (b, o) =>  *)
(*       match capl with *)
(*         vl :: capl' => *)
(*           match id_addrval l sem_cap sem_info_t with  *)
(*             Some l' =>  *)
(*               Aarray l'  (Tarray Tint8 (nat_of_Z (OS_MAX_TASKS-OS_N_SYS_TASKS))) vl *)
(*                 ** [| array_type_vallist_match Tint8 vl |] *)
(*                 ** [| length vl = nat_of_Z (OS_MAX_TASKS-OS_N_SYS_TASKS) |]  *)
(*                 ** ASemCap (b, Int.add o ($(Z_of_nat (typelen sem_info_t)))) capl'  *)
(*           | None => Afalse *)
(*           end *)
(*       | nil => Aemp *)
(*       end *)
(*   end. *)  

Definition RHL_EINFO_CAP_P vl (absemb: infoeid * sem_tp * sem_cap_ty) := 
  exists eo tp intvl,
    absemb = (eo, tp, intvl) /\ vl = List.map Vint32 intvl.

Fixpoint SemCapArray_P (v: val) (l: list vallist) (embls: EmbMod.map)
  {struct l} : Prop :=
  match l with
  | nil =>  embls = emp
  | vl :: l' => (
                 exists pos embls' absemb v',
                   v = Vint32 pos /\
                     v' = Vint32 (Int.add pos Int.one) /\
                     joinsig pos absemb embls' embls /\
                     RHL_EINFO_CAP_P vl absemb /\
                     SemCapArray_P v' l' embls'
               )
  end.

Definition ASemEIBs (infol scapl: list vallist) (embls: EmbMod.map) (ecbls: EcbMod.map) (vhold: addrval) :=  
  EX l, 
    ASeminfo l infol ** 
    ASemCap l scapl ** 
    [| EIBArray_P (Vint32 Int.zero) infol embls vhold |] **
    [| SemCapArray_P (Vint32 Int.zero) scapl embls |] ** 
    [| length scapl = nat_of_Z (OS_USER_MAX_EVENTS / 3) |] ** 
    [| RH_SEM_EINFO_ECB_P ecbls embls |] **
    [| RH_SEM_NOT_IN_CORE_P embls |]. 

(* Definition ASemEIBs (infol: list vallist) (embls: EmbMod.map) (ecbls: EcbMod.map) (vhold: addrval) :=   *)
(*   ASeminfo infol ** *)
(*     [| EIBArray_P (Vint32 Int.zero) infol embls vhold |] ** *)
(*     [| RH_SEM_EINFO_ECB_P ecbls embls |]  ** *)
(*     [| RH_SEM_NOT_IN_CORE_P embls |] *)
(*     (* [| RH_EINFO_ECB_All_P ecbls embls fecbh fecbvl locmp posmp ptrmp |] *). *)

(* Any mutex in absmuxinfob mapping must have a corresponding entry
   in ecbls. *)
Definition RH_ECBlk_EIBlk_Mux_P (absmuxinfob: MibMod.map) (ecbls : EcbMod.map) := 
  (forall pos eid_tp eid o z n pro pip w c mc,
      get absmuxinfob pos = Some (eid_tp, o, z, n, pro, pip, w, c, mc) -> 
      eid_tp = Valid_Addr eid ->
      (exists x y wls, get ecbls eid = Some (absmutexsem x y,wls))). 

(* Refinement relation for mutex_info *)
Definition RHL_EIBlk_Mux_P 
           (vl: vallist) 
           (absmuxinfob: eid_type * owner * muxtype * rec_cnt * prot * prioc * wq * cnsa * mux_cap_ty)
           (vhold: addrval)
  :=
    forall eid_t o x n pro pip w c mc,
      absmuxinfob = (eid_t, o, x, n, pro, pip, w, c, mc) ->
      (((eid_t = Null /\ V_OSMUXINFOPevent vl =Some Vnull) \/  
        (eid_t = Holder /\ V_OSMUXINFOPevent vl =Some (Vptr vhold)) \/
        (exists eid,
            eid_t = (Valid_Addr eid) /\ V_OSMUXINFOPevent vl =Some (Vptr eid) /\ eid <> vhold)) /\ 
       ((exists t opr,
            o = Some (t, opr) /\ 
            (Int.unsigned opr < 64 /\ V_OSMUXINFOOwner vl = Some (Vint32 opr))) \/ 
        (o = None /\ V_OSMUXINFOOwner vl = Some (Vint32 (Int.repr OS_MUTEX_AVAILABLE)))) /\
       V_OSMUXINFOType vl = Some (Vint32 x) /\  
       V_OSMUXINFORecursive_cnt vl = Some (Vint32 n) /\
       V_OSMUXINFOPrio_ceiling vl = Some (Vint32 pip) /\
       V_OSMUXINFOProtocol vl = Some (Vint32 pro) /\ 
       V_OSMUXINFOWaitq_type vl = Some (Vint32 w) /\
       V_OSMUXINFOCancel_safe vl = Some (Vint32 c) (* /\
       V_OSMUXINFOMuxCap vl = List.map Vint32 mc *)).

(* Refinement relation for list of mutex_info *)
Fixpoint EIBMAarray_P (v: val) (l:list vallist) (minfob : MibMod.map)(vhold: addrval)
         {struct l} : Prop :=
  match l with
  | nil =>  minfob = emp
  | vl :: l' => (
      exists  v' minfob' pos absminfob, 
        v = Vint32 pos /\ 
        joinsig pos absminfob minfob' minfob/\ 
        RHL_EIBlk_Mux_P vl absminfob vhold/\ 
        v' = Vint32 (Int.add pos Int.one) /\
        EIBMAarray_P v' l' minfob' vhold
    )
  end. 

Definition AMuxCap (l: addrval) (capl: list vallist) :=
  AEvtCap l capl mutex_cap pthread_mutex_info_t.  

Definition RHL_MUX_CAP_P
  vl (absminfob: eid_type * owner * muxtype * rec_cnt * prot * prioc * wq * cnsa * mux_cap_ty) :=  
  exists eo ow mt rc prt pri w cs intvl,
    absminfob = (eo, ow, mt, rc, prt, pri, w, cs, intvl) /\
      vl = List.map Vint32 intvl. 

Fixpoint MuxCapArray_P (v: val) (l: list vallist) (minfo: MibMod.map)
  {struct l} : Prop :=
  match l with
  | nil =>  minfo = emp
  | vl :: l' => (
                 exists pos minfo' absminfob v',
                   v = Vint32 pos /\
                     v' = Vint32 (Int.add pos Int.one) /\
                     joinsig pos absminfob minfo' minfo /\
                     RHL_MUX_CAP_P vl absminfob /\
                     MuxCapArray_P v' l' minfo'
               )
  end.

Definition AMuxEIBs (minfol mcapl: list vallist) (minfob: MibMod.map) ecbls (vhold: addrval) :=
  EX l, 
    APthreadMutex l minfol **  
      AMuxCap l mcapl **
      [| EIBMAarray_P (Vint32 (Int.zero)) minfol minfob vhold|] ** 
      [| MuxCapArray_P (Vint32 (Int.zero)) mcapl minfob |] ** 
      [| length mcapl = nat_of_Z (OS_USER_MAX_EVENTS / 3) |] ** 
      [| RH_ECBlk_EIBlk_Mux_P minfob ecbls |].  

(* Any queue in absqttrb mapping must have a corresponding
   entry in ecbls. *)
Definition RH_EIBlk_ECBlk_Q_P (ecbls : EcbMod.map) (absqattrb: MqattrMod.map) :=
  forall pos eid waittype flags maxmsg msgsize curmsgs mqc,
    get absqattrb pos = Some (Valid_Addr eid, waittype, flags, maxmsg, msgsize, curmsgs, mqc) ->
    (exists x y pwl wls, get ecbls eid = Some (absmsgq x y pwl, wls)).

Definition RH_Q_NOT_IN_CORE_P (absqattrb: MqattrMod.map) 
  := 
    forall pos eid waittype flags maxmsg msgsize curmsgs mqc,
             get absqattrb pos=Some ((Valid_Addr eid), waittype, flags, maxmsg, msgsize, curmsgs, mqc) ->
             notIncoreSemQ  eid.

(* Refinement relation for mq_attr *)
Definition RHL_EIBlk_Q_P
      (vl: vallist)
      (absqattrb: eid_type * q_waittype * q_flags * q_maxmsg * q_msgsize * q_curmsgs * mq_cap_ty)
      (vhold: addrval) :=
  forall eid_t waittype flags maxmsg msgsize curmsgs mqc,
    absqattrb = (eid_t, waittype, flags, maxmsg, msgsize, curmsgs, mqc) ->
    (((eid_t=Null /\ V_QATTRpevent vl = Some Vnull) \/  
      (eid_t = Holder /\ V_QATTRpevent vl =Some  (Vptr vhold))  \/ 
      (exists eid, eid_t = (Valid_Addr eid) /\ V_QATTRpevent vl = Some (Vptr eid) /\ eid <> vhold)) /\ 
      V_QATTRmq_waittype vl = Some (Vint32 waittype) /\
      V_QATTRmq_flags vl = Some (Vint32 flags) /\
      V_QATTRmq_maxmsg vl = Some (Vint32 maxmsg) /\
      V_QATTRmq_msgsize vl = Some (Vint32 msgsize) /\
      V_QATTRmq_curmsgs vl = Some (Vint32 curmsgs) (* /\
      V_OSMUXINFOMuxCap vl = List.map Vint32 mqc *)).

(* Refinement relation for list of mq_attr *)
Fixpoint MqEIBAarray_P (v: val) (l:list vallist) (qattrb: MqattrMod.map)  (vhold: addrval)
         {struct l} : Prop :=
  match l with
  | nil =>  qattrb = emp
  | vl :: l' => (
      exists  v' qattrb'  absqattrb pos, 
        v = Vint32 pos /\ 
        v' = Vint32 (Int.add pos Int.one) /\
        joinsig pos absqattrb qattrb' qattrb /\ 
        RHL_EIBlk_Q_P vl absqattrb vhold /\
        MqEIBAarray_P v' l' qattrb' vhold
    )
  end.

Definition AMqCap (l: addrval) (capl: list vallist) :=
  AEvtCap l capl mq_cap mq_attr_t.  

Definition RHL_MQ_CAP_P
  vl (absqattrb: eid_type * q_waittype * q_flags * q_maxmsg * q_msgsize * q_curmsgs * mq_cap_ty) :=  
  exists eo qwt qflg qmm qms qcm intvl,
    absqattrb = (eo, qwt, qflg, qmm, qms, qcm, intvl) /\ 
      vl = List.map Vint32 intvl. 

Fixpoint MqCapArray_P (v: val) (l: list vallist) (qattrs: MqattrMod.map)
  {struct l} : Prop :=
  match l with
  | nil =>  qattrs = emp
  | vl :: l' => (
                 exists pos qattrs' qattr v',
                   v = Vint32 pos /\
                     v' = Vint32 (Int.add pos Int.one) /\
                     joinsig pos qattr qattrs' qattrs /\ 
                     RHL_MQ_CAP_P vl qattr /\
                     MqCapArray_P v' l' qattrs' 
               )
  end.

Definition AMqEIBs (qattrl qcapl: list vallist) (qattr : MqattrMod.map) ecbls (vhold:addrval) :=
  EX l, 
    AMqAttr l qattrl **
      AMqCap l qcapl **
      [| MqEIBAarray_P (Vint32 (Int.zero)) qattrl qattr vhold |] ** 
      [| MqCapArray_P (Vint32 (Int.zero)) qcapl qattr |] ** 
      [| length qcapl = nat_of_Z (OS_USER_MAX_EVENTS / 3) |] **       
      [| RH_EIBlk_ECBlk_Q_P ecbls qattr |] ** [| RH_Q_NOT_IN_CORE_P qattr |].


Notation HSEMInfo semifo := (Aabsdata seminfoid (seminfo semifo)).
Notation HMuxInfo muxifo := (Aabsdata absmutinfoid (absmutinfo muxifo)).
Notation HQAttr mqattr := (Aabsdata absmqattrid (absmqattr mqattr)). 

(* posblk *) 
Notation Hpbls pbls:= (Aabsdata pblsid (pblist pbls)).
(* errblk *)
Notation Hebls ebls:= (Aabsdata eblsid (eblist ebls)).

Notation HPthreadAttr pattrb := (Aabsdata abspthattrid (abspthattr  pattrb)).

Require Import ev_aux_code.
(* Require Import seplog_pattern_tacs.  *)

Fixpoint pos_sllseg (head tailnext : val)  (vll: list vallist) (pbls: PbMod.map) :=
  match vll with
  | nil => [| head = tailnext |] ** [| pbls = emp |] 
  | vl::vll' =>      
      node head vl gjb_pos_blk_t **
      (EX l,
        [| head = Vptr l |] **
          (EX posv,
            [| get pbls l = Some posv /\ V_posblk_pos vl = Some (Vint32 posv) |] ** 
                     (EX pbls', [| joinsig l posv pbls' pbls |] **
                                 (EX vn, [|V_posblk_next vl = Some vn|] **
                                          pos_sllseg vn tailnext vll' pbls'))))
  end.

Definition APosblkList (pbls: PbMod.map) : asrt :=
  (EX p, (GV GJB_pos_list @ (Tptr gjb_pos_blk_t) |-> p **
            EX vll, pos_sllseg p Vnull vll pbls)).

Fixpoint err_sllseg (head tailnext : val)  (vll: list vallist) (ebls: EbMod.map) :=
  match vll with
  | nil => [| head = tailnext |] ** [| ebls = emp |] 
  | vl::vll' =>      
      node head vl gjb_err_blk_t **
      (EX l,
        [| head = Vptr l |] **
          (EX errv,
            [| get ebls l = Some errv /\ V_errblk_err vl = Some (Vint32 errv) |] ** 
                     (EX ebls', [| joinsig l errv ebls' ebls |] **
                                 (EX vn, [|V_errblk_next vl = Some vn|] **
                                          err_sllseg vn tailnext vll' ebls'))))
  end.

Definition AErrblkList (ebls: EbMod.map) : asrt :=
  (EX p, (GV GJB_err_list @ (Tptr gjb_err_blk_t) |-> p **
            EX vll, err_sllseg p Vnull vll ebls)).

(****************** atom struct array heaps  *******************)

(*-----------------------------------------------------------------------------------*)
(* members of a pthread mutex attr block                                   *) 
(* --> spec/evt_spec_defs.v *) 
(* Definition V_muxattr_isinit     (vl:vallist) := nth_val 0 vl. *)
(* Definition V_muxattr_procshared (vl:vallist) := nth_val 1 vl. *)
(* Definition V_muxattr_prioceiling (vl:vallist) := nth_val 2 vl. *)
(* Definition V_muxattr_protocol       (vl:vallist) := nth_val 3 vl. *)
(* Definition V_muxattr_recursive      (vl:vallist) := nth_val 4 vl. *)
(* Definition V_muxattr_waitq     (vl:vallist) := nth_val 5 vl. *)
(* Definition V_muxattr_cancelsafe      (vl:vallist) := nth_val 6 vl. *)

Notation HEvAtomHeap evatoms := (Aabsdata evatomheapid (evatomheap  evatoms)).
Notation HEvStructHeap evstructheapb := (Aabsdata evstructheapid (evstructheap  evstructheapb)).
Notation HEvArrayHeap evarrays  := (Aabsdata evarrayheapid (evarrayheap evarrays)).

Fixpoint AEvAtomHeap  (evHeape : list (addrval * type * val)) := 
  match evHeape with
  | nil => Aemp
  | (l, Tvoid, v) :: evHeape'  => PV l @ Tvoid |-> v ** [| rule_type_val_match Tvoid v = true|] ** AEvAtomHeap evHeape'
  | (l, Tint8, v) :: evHeape'  => PV l @ Tint8 |-> v ** [| rule_type_val_match Tint8 v = true|] ** AEvAtomHeap evHeape'
  | (l, Tint16, v) :: evHeape'  => PV l @ Tint16 |-> v ** [| rule_type_val_match Tint16 v = true|] ** AEvAtomHeap evHeape'
  | (l, Tint32, v) :: evHeape'  => PV l @ Tint32 |-> v ** [| rule_type_val_match Tint32 v = true|] ** AEvAtomHeap evHeape'
  | (l, (Tptr t), v) :: evHeape'  => PV l @ (Tptr t) |-> v ** [| rule_type_val_match (Tptr t) v = true|] ** AEvAtomHeap evHeape'
  | _  => Afalse
  end.

Definition R_MutexAttr_P (tp:type) (vl:list val) :=
tp = pthread_mutexattr_t ->
(exists prioc, V_muxattr_prioceiling vl = Some (Vint32 prioc) /\
                                 (0 <= Int.unsigned prioc < 64)).


Fixpoint AEvStructHeap  (evHeap : list (addrval * type * (list val))) :=
  match evHeap with
  | nil => Aemp
  | (l, (Tstruct id decl), vl) :: evHeapl'  =>  Astruct l (Tstruct id decl) vl **
                                                                                     [|struct_type_vallist_match (Tstruct id decl) vl|] **
                                                                                     [| R_MutexAttr_P (Tstruct id decl) vl |] **
                                                                                     AEvStructHeap evHeapl'
  | _  => Afalse
  end.

Fixpoint AEvArrayHeap  (evarrays : list (addrval * nat * (list val))) :=
  match evarrays with
  | nil => Aemp
  | (l, n, vl) :: evarrays'  =>  Aarray l (Tarray Tint8 n) vl **
                                                      [|array_type_vallist_match Tint8 vl |] **
                                                      AEvArrayHeap evarrays' 
  end.

Definition R_Q_Data_P evstructs evarrays :=
  forall  qid qdata_vl,
     Get_struct evstructs qid = Some (qid , OS_Q_DATA, qdata_vl) ->
     exists (qletbl:addrval) (qetbl:list val) qegrp,
     id_addrval' (Vptr qid) OSEventTbl OS_Q_DATA = Some qletbl /\
     (exists b i, qid = (b,i) /\ i = $ 0) /\
     Get_array evarrays qletbl = Some (qletbl, Z.to_nat OS_EVENT_TBL_SIZE, qetbl) /\
     nth_val 4 qdata_vl = Some qegrp /\
     RL_Tbl_Grp_P qetbl qegrp.

(****************** heaps  end*******************)

(* (* mapping from task priorities to program locations in the abstract state *)  *)
Notation HEvLoc locmp := (Aabsdata evlocid (evloc locmp)).
(* (* mapping from task priorities to indices of event info blocks in the abstract state *)   *)
Notation HEvPtr ptrmp := (Aabsdata evptrid (evptr ptrmp)).

Definition evptr_of_tsk t ptrmp eptr := 
  (exists semp qp, get ptrmp t = Some (Vptr eptr, semp, qp)) \/
  (exists muxp qp, get ptrmp t = Some (muxp, Vptr eptr, qp)) \/
  (exists muxp semp, get ptrmp t = Some (muxp, semp, Vptr eptr)).

Definition semeib_ref semeibs eptr :=
  exists pos tp sc, get semeibs pos = Some (infotid eptr, tp, sc). 

Definition muxeib_ref muxeibs eptr :=
  exists pos owr tp cnt pr prc wq cs mc,
    get muxeibs pos = Some (Valid_Addr eptr, owr, tp, cnt, pr, prc, wq, cs, mc).

Definition mqeib_ref mqeibs eptr :=
  exists pos tp flgs mms msz cms mqc,
    get mqeibs pos = Some (Valid_Addr eptr, tp, flgs, mms, msz, cms, mqc).

Definition eib_ref semeibs muxeibs mqeibs eptr := 
  semeib_ref semeibs eptr \/
  muxeib_ref muxeibs eptr \/
  mqeib_ref mqeibs eptr.

Definition evref_same_type eptr
           (semeibs: EmbMod.map) (muxeibs: MibMod.map) (mqeibs: MqattrMod.map) :=
  (semeib_ref semeibs eptr ->
   (~muxeib_ref muxeibs eptr /\ ~mqeib_ref mqeibs eptr)) /\
  (muxeib_ref muxeibs eptr ->
   (~semeib_ref semeibs eptr /\ ~mqeib_ref mqeibs eptr)) /\
  (mqeib_ref mqeibs eptr ->
   (~semeib_ref semeibs eptr /\ ~muxeib_ref muxeibs eptr)).

Definition semref_distinct semeibs eptr :=
  forall pos1 pos2 tp1 tp2 sc1 sc2,
    get semeibs pos1 = Some (infotid eptr, tp1, sc1) ->
    get semeibs pos2 = Some (infotid eptr, tp2, sc2) ->
    pos1 = pos2.

Definition muxref_distinct muxeibs eptr :=
  forall pos1 pos2 owr1 owr2 tp1 tp2 cnt1 cnt2 pr1 pr2 prc1 prc2 wq1 wq2 cs1 cs2 mc1 mc2,
    get muxeibs pos1 = Some (Valid_Addr eptr, owr1, tp1, cnt1, pr1, prc1, wq1, cs1, mc1) ->
    get muxeibs pos2 = Some (Valid_Addr eptr, owr2, tp2, cnt2, pr2, prc2, wq2, cs2, mc2) ->
    pos1 = pos2.

Definition mqref_distinct mqeibs eptr :=
  forall pos1 pos2 tp1 tp2 flgs1 flgs2 mms1 mms2 msz1 msz2 cms1 cms2 mqc1 mqc2,
    get mqeibs pos1 = Some (Valid_Addr eptr, tp1, flgs1, mms1, msz1, cms1, mqc1) ->
    get mqeibs pos2 = Some (Valid_Addr eptr, tp2, flgs2, mms2, msz2, cms2, mqc2) ->
    pos1 = pos2.

Definition eibref_distinct semeibs muxeibs mqeibs :=
  forall eptr, (
      evref_same_type eptr semeibs muxeibs mqeibs /\
      semref_distinct semeibs eptr /\
      muxref_distinct muxeibs eptr /\
      mqref_distinct mqeibs eptr
    ).

Definition is_sem ecbls eptr := 
  exists n wl, get ecbls eptr = Some (abssem n, wl).

Definition is_mux ecbls eptr :=
  exists n1 n2 wls, get ecbls eptr = Some (absmutexsem n1 n2, wls).

Definition is_que ecbls eptr :=
  exists x y pwl qwaitset, get ecbls eptr = Some (absmsgq x y pwl, qwaitset).

Definition is_evt ecbls eptr :=
  is_sem ecbls eptr \/ is_mux ecbls eptr \/ is_que ecbls eptr.

Definition evcre_nodup locmp ptrmp :=
  forall t1 t2 eptr1 eptr2,
    t1 <> t2 -> 
    (get locmp t1 = Some (Vint32 (Int.repr __EvLoc_ecbcre1)) \/
     get locmp t1 = Some (Vint32 (Int.repr __EvLoc_ecbcre2))) ->
    (get locmp t2 = Some (Vint32 (Int.repr __EvLoc_ecbcre1)) \/
     get locmp t2 = Some (Vint32 (Int.repr __EvLoc_ecbcre2))) ->
    evptr_of_tsk t1 ptrmp eptr1 -> 
    evptr_of_tsk t2 ptrmp eptr2 -> 
    eptr1 <> eptr2. 

Definition evdel_nodup locmp ptrmp :=
  forall t1 t2 eptr1 eptr2,
    t1 <> t2 -> 
    get locmp t1 = Some (Vint32 (Int.repr __EvLoc_ecbdel)) ->
    get locmp t2 = Some (Vint32 (Int.repr __EvLoc_ecbdel)) ->
    evptr_of_tsk t1 ptrmp eptr1 ->  
    evptr_of_tsk t2 ptrmp eptr2 -> 
    eptr1 <> eptr2.  

Definition SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl
           (semeibs: EmbMod.map) (muxeibs: MibMod.map) (mqeibs: MqattrMod.map) :=  
  forall (t: tid) (eptr: addrval) muxp qp,
    get ptrmp t = Some (muxp, Vptr eptr, qp) ->
    (
      (get locmp t = Some (Vint32 (Int.repr __EvLoc_ecbcre1)) /\
       (~ptr_in_ecblist (Vptr eptr) fecbh fecbvl) /\ (~eib_ref semeibs muxeibs mqeibs eptr)
       /\ get ecbls eptr = None) 
      \/
      (get locmp t = Some (Vint32 (Int.repr __EvLoc_ecbcre2)) /\ 
       (~eib_ref semeibs muxeibs mqeibs eptr) /\ is_sem ecbls eptr)
      \/
      (get locmp t = Some (Vint32 (Int.repr __EvLoc_normal)) /\
       (is_evt ecbls eptr \/ ptr_in_ecblist (Vptr eptr) fecbh fecbvl)
      )
    ). 

Definition MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl
           (semeibs: EmbMod.map) (muxeibs: MibMod.map) (mqeibs: MqattrMod.map) :=  
  forall (t: tid) (eptr: addrval) semp qp,
    get ptrmp t = Some (Vptr eptr, semp, qp) -> 
    (
      (get locmp t = Some (Vint32 (Int.repr __EvLoc_ecbcre1)) /\
       (~ptr_in_ecblist (Vptr eptr) fecbh fecbvl) /\ (~eib_ref semeibs muxeibs mqeibs eptr)
       /\ get ecbls eptr = None)
      \/
      (get locmp t = Some (Vint32 (Int.repr __EvLoc_ecbcre2)) /\
       (~eib_ref semeibs muxeibs mqeibs eptr) /\ is_mux ecbls eptr)
      \/
      (get locmp t = Some (Vint32 (Int.repr __EvLoc_normal)) /\
       (is_evt ecbls eptr \/ ptr_in_ecblist (Vptr eptr) fecbh fecbvl) 
      )
    ). 
      
Definition Q_ECB_P locmp ptrmp ecbls fecbh fecbvl 
           (semeibs: EmbMod.map) (muxeibs: MibMod.map) (mqeibs: MqattrMod.map) :=  
  forall (t: tid) (eptr: addrval) muxp semp,
    get ptrmp t = Some (muxp, semp, Vptr eptr) -> (
    (
      (get locmp t = Some (Vint32 (Int.repr __EvLoc_ecbcre1)) /\ 
       (~ptr_in_ecblist (Vptr eptr) fecbh fecbvl) /\ (~eib_ref semeibs muxeibs mqeibs eptr)
       /\ get ecbls eptr = None)
      \/
      (get locmp t = Some (Vint32 (Int.repr __EvLoc_ecbcre2)) /\
       (~eib_ref semeibs muxeibs mqeibs eptr) /\ is_que ecbls eptr)
      \/
      (get locmp t = Some (Vint32 (Int.repr __EvLoc_normal)) 
       \/ get locmp t = Some (Vint32 (Int.repr __EvLoc_ecbdel))) /\ 
      (is_evt ecbls eptr \/ ptr_in_ecblist (Vptr eptr) fecbh fecbvl)
    )
    /\
    (get locmp t = Some (Vint32 (Int.repr __EvLoc_ecbdel)) -> 
     (is_que ecbls eptr /\ 
      (~exists t,
            (get locmp t = Some (Vint32 (Int.repr __EvLoc_ecbcre1)) \/
             get locmp t = Some (Vint32 (Int.repr __EvLoc_ecbcre2)))
            /\ evptr_of_tsk t ptrmp eptr) /\ 
      (~eib_ref semeibs muxeibs mqeibs eptr)))).


Definition EvtInv ecbls tcblh tcbvl tcbls (vhold: addrval) scapl mcapl qcapl :=

  (EX fecbh eventl ectrl osql qblkl msgql evatoms evstructs evarrays
     sinfol minfol qattrl semeibs muxeibs qeibs pbls ebls locmp ptrmp,
   
                    AOSEventFreeList fecbh eventl ** AOSQFreeList osql ** 
                    AOSQFreeBlk qblkl ** (* free lists *)
                    AECBList ectrl msgql ecbls  tcbls ** (* msgq *)
                    HECBList ecbls **
                    
                    Hebls ebls ** AErrblkList ebls **
                    Hpbls pbls ** APosblkList pbls **
                    HEvAtomHeap evatoms **  AEvAtomHeap evatoms **
                    HEvStructHeap evstructs **  AEvStructHeap evstructs **
                    HEvArrayHeap evarrays **  AEvArrayHeap evarrays **
                    [| R_Q_Data_P evstructs evarrays |] **
                    HSEMInfo semeibs ** ASemEIBs sinfol scapl semeibs ecbls vhold ** 
                    HMuxInfo muxeibs ** AMuxEIBs minfol mcapl muxeibs ecbls vhold **
                    HQAttr qeibs ** AMqEIBs qattrl qcapl qeibs ecbls vhold ** 
                    [| vhold = vhold_addr |] ** 
                    [| SEM_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs |] **
                    [| MUX_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs |] **
                    [| Q_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs |] **
                    [| evcre_nodup locmp ptrmp |] ** 
                    [| evdel_nodup locmp ptrmp |] ** 
                    [| eibref_distinct semeibs muxeibs qeibs |] **
                    HEvLoc locmp ** HEvPtr ptrmp ** 
                    tcbllsegevaux tcblh tcbvl locmp ptrmp).


(*-----------------------------------------------------------------------------------*)
(* add    for timer and core commu                                                   *)
(*-----------------------------------------------------------------------------------*)

Definition V_OSRSVD0    (vl:vallist) := nth_val 0 vl.
Definition V_OSEMUMGT     (vl:vallist) := nth_val 1 vl.
Definition V_OSRSVD1 (vl:vallist) := nth_val 2 vl.
Definition V_OSCNTLO    (vl:vallist) := nth_val 3 vl.
Definition V_OSCNTHI      (vl:vallist) := nth_val 4 vl.
Definition V_OSPRDLO     (vl:vallist) := nth_val 5 vl.
Definition V_OSPRDHI     (vl:vallist) := nth_val 6 vl.
Definition V_OSTCRreg        (vl:vallist) := nth_val 7 vl.
Definition V_OSTGCR        (vl:vallist) := nth_val 8 vl.
Definition V_OSWDTCR   (vl: vallist) := nth_val 9 vl.

Parameter tmrRegsAddr : addrval.

(* this addr is the start address of the timer regs*)
 
Definition timer_RSVD0  (n: int32) := get_off_addr tmrRegsAddr (Int.mul n ($ 65536)).
Definition timer_EMUMGT_CLKSPD (n: int32) := get_off_addr (get_off_addr tmrRegsAddr ($ 4)) (Int.mul n ($65536)).
Definition timer_RSVD1 (n: int32) := get_off_addr (get_off_addr tmrRegsAddr ($ 8)) (Int.mul n ($65536)).
Definition timer_CNTLO (n: int32) := get_off_addr (get_off_addr tmrRegsAddr ($ 16)) (Int.mul n ($65536)).
Definition timer_CNTHI (n: int32) := get_off_addr (get_off_addr tmrRegsAddr ($ 20)) (Int.mul n ($65536)).
Definition timer_PRDLO (n: int32) := get_off_addr (get_off_addr tmrRegsAddr ($ 24)) (Int.mul n ($65536)).
Definition timer_PRDHI (n: int32) := get_off_addr (get_off_addr tmrRegsAddr ($ 28)) (Int.mul n ($65536)).
Definition timer_TCR (n: int32) := get_off_addr (get_off_addr tmrRegsAddr ($ 32))  (Int.mul n ($65536)).
Definition timer_TGCR (n: int32) := get_off_addr (get_off_addr tmrRegsAddr ($ 36))  (Int.mul n ($65536)).
Definition timer_WDTCR (n: int32) := get_off_addr (get_off_addr tmrRegsAddr ($ 40))  (Int.mul n ($65536)).

Definition pre28bits (tgcr : int32 ) := tgcr &ᵢ ($ 4294967280).

Definition AOSTMRNode (n: int32) (tmr : vallist):=
  EX v0 v1 v2 v3 v4 v5 v6 v7 v8 v9,
  [| tmr = (Vint32 v0)::(Vint32 v1)::v2::(Vint32 v3)::(Vint32 v4)::
  (Vint32 v5)::(Vint32 v6)::(Vint32 v7)::(Vint32 v8):: (Vint32 v9) :: nil |] **
  PV (timer_RSVD0 n) @ (Tint32) |-> Vint32 v0 **
  PV (timer_EMUMGT_CLKSPD n) @ (Tint32) |-> Vint32 v1 **
  (* PV (timer_RSVD1 n) @ (Tptr (Tarray Tint32 2)) |->  v2 ** *)
  PV (timer_CNTLO n) @ (Tint32) |-> Vint32 v3 **
  PV (timer_CNTHI n) @ (Tint32) |-> Vint32 v4 ** 
  PV (timer_PRDLO n) @ (Tint32) |-> Vint32 v5 **
  PV (timer_PRDHI n) @ (Tint32) |-> Vint32 v6 **
  PV (timer_TCR n) @ (Tint32) |-> Vint32 v7 **
  PV (timer_TGCR n) @ (Tint32) |-> Vint32 v8 **
  PV (timer_WDTCR n) @ (Tint32) |-> Vint32 v9 **
  [| (pre28bits v8) = Int.zero |].

Definition isGPtmr (tmr : vallist) : bool :=
  match (V_OSTGCR tmr) with 
  | Some (Vint32 tgcr) => Int.eq (tgcr &ᵢ ($ 12)) ($ 0) 
  | _ => false
  end.
Definition isWDtmr (tmr : vallist) : bool :=
  match (V_OSTGCR tmr) with 
  | Some (Vint32 tgcr) => Int.eq (tgcr &ᵢ ($ 12)) ($ 8) 
  | _ => false
  end.

Definition isgptmr  (abstmr:timer * timerstatus *  timertick * outMode ) :bool :=
match abstmr with
| (gp_t _ _, _, _, _) => true
| (wd_t _,_,_,_) => false
end.

Definition iswdtmr  (abstmr:timer * timerstatus *  timertick * outMode ) :bool :=
match abstmr with
| (gp_t _ _, _, _, _) => false
| (wd_t _,_,_,_) => true
end.

Definition  IsGPtmr tmr abstmr : bool := andb (isGPtmr tmr) (isgptmr abstmr) .
Definition  IsWDtmr tmr abstmr : bool := andb (isWDtmr tmr) (iswdtmr abstmr) .


Definition AOSTMRList' (tmrl : list vallist)  := 
 EX tmr0 tmr1 tmr2 tmr3 tmr4 tmr5 tmr6 tmr7 tmr8 tmr9 tmr10 tmr11 tmr12 tmr13 tmr14 tmr15, 
 [| tmrl = tmr0::tmr1::tmr2::tmr3::tmr4::tmr5::tmr6::tmr7::tmr8::tmr9::tmr10:: tmr11::tmr12::tmr13::tmr14::tmr15::nil |]  **
  AOSTMRNode ($ 0) tmr0 **  AOSTMRNode ($ 1) tmr1 **  AOSTMRNode ($ 2) tmr2 **  AOSTMRNode ($ 3) tmr3 ** 
  AOSTMRNode ($ 4) tmr4 **  AOSTMRNode ($ 5) tmr5 **  AOSTMRNode ($ 6) tmr6 **  AOSTMRNode ($ 7) tmr7 ** 
  AOSTMRNode ($ 8) tmr8 **  AOSTMRNode ($ 9) tmr9 **  AOSTMRNode ($ 10) tmr10 **  AOSTMRNode ($ 11) tmr11 ** 
  AOSTMRNode ($ 12) tmr12 **  AOSTMRNode ($ 13) tmr13 **  AOSTMRNode ($ 14) tmr14 **  AOSTMRNode ($ 15) tmr15 .

(* for 8 ~ 15 timerid, record whether there exists this tmr  *)
Definition AOSTMRIDUsed (tmrused : list val) : asrt :=
  GAarray OS_timerid_used (Tarray Tint8 8%nat) tmrused **
  [|array_type_vallist_match Tint8 tmrused /\ length tmrused = 8%nat /\ 
  Forall (fun x => x = Vint32 ($ 0) \/ (x = Vint32 ($ 1))) tmrused|]. 

Definition TIMMODE (tgcr : int32) : int32 :=
  tgcr &ᵢ ($ 12). (*1100*)
Definition TCR_ENAMODE (tcr : int32) : int32 :=
  tcr &ᵢ ($ 192). (*11000000*)
Definition TIMHIRS_TIMLORS (tgcr : int32) : int32 :=
  tgcr &ᵢ ($ 3). (* 000000000011 *)
Definition WDEN (wdtcr: int32) : int32 :=
  wdtcr &ᵢ ($ 16384). (*100000000000000*)
Definition CPLO (tcr : int32) : int32 :=
  tcr &ᵢ ($ 8). (*1000*)

Definition TMRNode_Pmode vl (abstmr:timer * timerstatus *  timertick * outMode):=
  match abstmr with
    |(gp_t _ onetime, _ , _ , _) => exists tgcr tcr,
                                        V_OSTGCR vl = Some (Vint32 tgcr) /\
                                        V_OSTCRreg vl = Some (Vint32 tcr) /\
                                        tgcr &ᵢ ($ 12) = $ 0 /\ 
                                        tcr &ᵢ ($ 192) = $ 64
    |(gp_t _ continuously, _ , _ , _) => exists tgcr tcr,
                                        V_OSTGCR vl = Some (Vint32 tgcr) /\
                                        V_OSTCRreg vl = Some (Vint32 tcr) /\
                                        tgcr &ᵢ ($ 12) = $ 0 /\ 
                                        tcr &ᵢ ($ 192) = $ 128
    |(wd_t _, _, _,_) => exists tgcr,
                            V_OSTGCR vl = Some (Vint32 tgcr) /\
                            tgcr &ᵢ ($ 12) = $ 8                              
  end.
  
Definition TMRNode_Pcnt vl (abstmr:timer * timerstatus *  timertick * outMode):=
  match abstmr with
    |(_ , _ , tk, _) => exists cntl cnth,
                              cntl =  (Int.repr tk) /\
                              cnth = (Int.repr (Z.div tk Int.modulus)) /\ 
                              V_OSCNTLO vl = Some (Vint32 cntl) /\
                              V_OSCNTHI vl = Some (Vint32 cnth)
  end.

Definition TMRNode_Pprd vl (abstmr:timer * timerstatus *  timertick * outMode):=
  match abstmr with
    |(gp_t prd  _, _ , _ , _) => exists prdl prdh,
                            prdl =  (Int.repr prd) /\
                            prdh = (Int.repr (Z.div prd Int.modulus)) /\
                            V_OSPRDLO vl = Some (Vint32 prdl) /\ 
                            V_OSPRDHI vl = Some (Vint32 prdh)
    |(wd_t prd , _ , _ , _) => exists prdl prdh,
                            prdl =  (Int.repr prd) /\
                            prdh = (Int.repr (Z.div prd Int.modulus)) /\
                            V_OSPRDLO vl = Some (Vint32 prdl) /\ 
                            V_OSPRDHI vl = Some (Vint32 prdh) 
  end.

Definition TMRNode_Pstatus vl (abstmr:timer * timerstatus *  timertick * outMode ):=
  match abstmr with
    |(gp_t _ _ , tm_idle , _ , _) => exists  tgcr,
                                 V_OSTGCR vl = Some (Vint32 tgcr) /\
                                 tgcr &ᵢ ($ 3) = $ 0
    |(gp_t _ _ , tm_start , _ , _) => exists  tgcr,
                                 V_OSTGCR vl = Some (Vint32 tgcr) /\
                                 tgcr &ᵢ ($ 3) = $ 3
    (*The watchdog timer mode is enabled when WDEN = 1 in WDTCR.*)
    |(wd_t _, tm_idle , _ , _) => exists  wdtcr,
                                 V_OSWDTCR vl = Some (Vint32 wdtcr) /\
                                 wdtcr &ᵢ ($ 16384) = $ 0
    |(wd_t _, tm_start , _ , _) => exists  wdtcr,
                                 V_OSWDTCR vl = Some (Vint32 wdtcr) /\
                                 wdtcr &ᵢ ($ 16384) = $ 16384
  end.

Definition TMRNode_Poutmode vl (abstmr:timer * timerstatus *  timertick * outMode ) :=
  match abstmr with
    |(gp_t _ _ , _ , _ , om_pulse) => exists  tcr,
                                 V_OSTCRreg vl = Some (Vint32 tcr) /\
                                 tcr &ᵢ ($ 8) = $ 0
    |(gp_t _ _ , _ , _ , om_clock) => exists  tcr,
                                 V_OSTCRreg vl = Some (Vint32 tcr) /\
                                 tcr &ᵢ ($ 8) = $ 8
    (*In the watchdog timer mode (TIMMODE = 10b), the pulse mode is selected automatically*)
    |(wd_t _ , _ , _ , om_pulse) => True
    |(wd_t _ , _ , _ , om_clock) => False
  end.

Definition TMRNode_P vl abstmr:= 
  TMRNode_Pmode vl abstmr /\ TMRNode_Pcnt vl abstmr /\ TMRNode_Pprd vl abstmr /\ 
  TMRNode_Pstatus vl abstmr /\ TMRNode_Poutmode vl abstmr.

Fixpoint TMRList_P_sys (n: nat) (l:list vallist) (tmrls : TmrMod.map) 
         {struct l} : Prop :=
  match l with
    | nil =>  tmrls = emp 
    | vl :: l' =>  exists abstmr tmrls', (* IsWDtmr vl abstmr = true /\ *)
                      TMRNode_P vl abstmr /\
                      join (sig (Z.of_nat n) abstmr) tmrls' tmrls /\ 
                      TMRList_P_sys (S n) l' tmrls' 
  end. 

Definition RLH_TMRList_P_sys (l:list vallist) (tmrls : TmrMod.map) := TMRList_P_sys 0%nat l tmrls.

Definition TMR_used (tmrid: nat) (tmrused : list val) : Prop :=
   nth_error tmrused tmrid = Some (Vint32 ($ 1)).

Fixpoint TMRList_P_user (n: nat) (l:list vallist) (tmrused : list val) (tmrls : TmrMod.map) 
         {struct l} : Prop :=
  match l, tmrused with
    | nil, nil =>  tmrls = emp 
    | vl :: l', Vint32 rflag :: tmrused' => ((  Int.eq rflag ($ 1) = true /\ 
                      exists abstmr tmrls', IsGPtmr vl abstmr = true /\ TMRNode_P vl abstmr /\
                      join (sig (Z.of_nat (n + 8)%nat) abstmr) tmrls' tmrls /\ 
                      TMRList_P_user (S n) l' tmrused' tmrls' ) \/ 
                    (Int.eq rflag ($ 0) = true /\ 
                    V_OSTGCR vl = Some (V$ 0) /\
                    ~ indom tmrls (Z.of_nat (n + 8)%nat) /\ 
                    TMRList_P_user (S n) l' tmrused' tmrls)) 
    | _ , _ => False
  end. 

Definition RLH_TMRList_P_user (l:list vallist) (tmrused : list val) (tmrls : TmrMod.map) := TMRList_P_user 0%nat l tmrused tmrls.

Definition AOSTMRList_TMRused (systmrl: list vallist) (usertmrl: list vallist) (tmrused : list val)  (otmrls: option TmrMod.map)  := 
  GV __timerregs @ (Tptr Tint32) |-> Vptr tmrRegsAddr **
  AOSTMRList' (systmrl ++ usertmrl) ** AOSTMRIDUsed tmrused **
  [| length systmrl = 8%nat /\ length usertmrl =8%nat |] **
  [| (exists tmrls, otmrls = Some tmrls /\ 
     exists tmrls1 tmrls2, join tmrls1 tmrls2 tmrls /\ 
     RLH_TMRList_P_sys systmrl tmrls1 /\ RLH_TMRList_P_user usertmrl tmrused tmrls2) \/ 
     otmrls = None |].


Notation HTMRList tmrls:= (Aabsdata ostmrid (ostmr tmrls)).

Notation HClkRate cRate:= (Aabsdata osclkrateid (osrate cRate)).

Definition AOSClkRate (clkrate: val) := GV OS_TICKS_PER_SEC_SYS @ Tint32 |-> clkrate.

Notation HCoreHeap cHeapl cHeape cHeapt:= (Aabsdata oscoreheapid (oscoreheap (cHeapl, cHeape, cHeapt))).

Definition HEAP_MAX_LENGTH := IPC_STEP. (* 10240*)

Fixpoint AOScoreheapl  (cHeapl : list (addrval * nat * (list val))) :=
  match cHeapl with
  | nil => Aemp
  | (l, n, vl) :: cHeapl'  =>  Aarray l (Tarray Tint8 n) vl  ** [| array_type_vallist_match Tint8 vl /\ (n <= (Z.to_nat HEAP_MAX_LENGTH ))%nat|] ** AOScoreheapl cHeapl' 
  end.

Fixpoint AOScoreheape  (cHeape : list (addrval * type * val)) := 
  match cHeape with
  | nil => Aemp
  | (l, t, v) :: cHeape'  => PV l @ t |-> v ** AOScoreheape cHeape' 
  end.

Definition simple_struct(d:type):=
  match d with
  | Tstruct id (dcons d t ds) => ~ array_struct t
  | _ => False
  end.

Fixpoint AOScoreheapt  (cHeapt : list (addrval * type * list val)) := 
  match cHeapt with
  | nil => Aemp
  | (l, t, vl) :: cHeapt'  => Astruct l t vl ** [| struct_type_vallist_match t vl /\ simple_struct t|] ** AOScoreheapt cHeapt' 
  end.
(*add for core communication -----------------------------*)

Notation HcurCore curcore' := (Aabsdata curcoreid (oscurtcore curcore')).
Notation HipcsendHeap sendh := (Aabsdata ipcsendid (ossend sendh)).
Notation HipcrecvHeap recvh := (Aabsdata ipcrecvid (osrecv recvh)).
Notation Hipcsem ipcsem := (Aabsdata ipcsemid (osipcsem ipcsem)).
Notation Hipcsendsem sem :=(Aabsdata ipcsendsemid (osipcsendsem sem)).
Notation Hipcsemshared sem := (Aabsdata ipcsemshareid (osipcsemshared sem)).
Notation Hipcbroad c := (Aabsdata ipcbroadid (osipcbroad c)).
Notation Hipcgr ipcgr := (Aabsdata ipcgrid (osipcgr (Vint32 ipcgr))).

Notation Hcapspace cspace := (Aabsdata cspaceid (capcspace cspace)).

Fixpoint isvptr_list vl:=
  match vl with
    | nil => True
    | Vptr _ ::vl' =>  isvptr_list vl'
    | _ :: _ => False
  end.


Definition curcore : nat := Z.to_nat DNUM.

Definition Memory_Node (n:nat) (cl: addrval) (meml: vallist):=
     (* (Astruct (get_off_addr cl (Int.mul ($ Z.of_nat n)($ IPC_STEP))) dyn_refac_cfg meml
  ** [| struct_type_vallist_match dyn_refac_cfg meml |]) \\// *)
    (Aarray (get_off_addr cl (Int.mul ($ Z.of_nat n)($ IPC_STEP)))  (Tarray Tint8 (Z.to_nat HEAP_MAX_LENGTH)) meml
  ** [| array_type_vallist_match Tint8 meml /\  length meml = (Z.to_nat HEAP_MAX_LENGTH)|]  ). 
  
Fixpoint Memory_sigcore_aux (n:nat) (p: addrval) (memls: list vallist):=
  match memls with 
  | nil => Aemp
  | meml::memls' => Memory_Node n p meml ** Memory_sigcore_aux (S n) p memls'
  end.

Definition Memory_sigcore (p: addrval) (memls: list vallist):=
   Memory_sigcore_aux O p memls ** [| length memls = 7%nat|]. 

Fixpoint AOSIPCMem_aux (pl : list val) (memlls:list (list vallist)):=
  match pl with 
  | nil => match memlls with nil => Aemp | _ => Afalse end 
  | Vptr p::pl' => match memlls with 
                  | nil => Afalse 
                  | memls :: memlls' => Memory_sigcore p memls  ** AOSIPCMem_aux pl' memlls' 
                  end 
  | _ :: _ => Afalse
  end.

Definition AOSIPCMem (pl:list val) (memlls:list (list vallist)): asrt := 
  GAarray IPCMem (Tarray (Tptr Tint8) 8%nat) pl ** AOSIPCMem_aux pl memlls ** 
    [| isvptr_list pl /\ length pl = 8%nat /\ length memlls = 8%nat|].   

Definition compute_step (srcCore: nat) (dstCore : nat) : nat :=
  if (dstCore <? srcCore)%nat then (srcCore - 1) else srcCore.

Definition compute_sendheap_aux (dstCore : nat) (meml : list vallist) :=
  if Nat.eqb curcore dstCore then None 
  else let step := compute_step curcore dstCore in 
  nth_error meml step.

Definition is_some (x: option (vallist)) := match x with None => false | _ => true end.  
Definition somex2x (x: option (vallist)) := match x with None => nil | Some x' => x' end.
Definition compute_sendheap (sh: list (option vallist)) := map somex2x (filter is_some sh).

Definition RH_IPCMem_P_meml (meml: (list vallist)) :=
  length meml = (Z.to_nat CORENUM - 1)%nat /\
  forall mem, In mem meml ->
  array_type_vallist_match Tint8 mem /\ 
  length meml = (Z.to_nat HEAP_MAX_LENGTH).

Definition RH_IPCMem_P (memll: list (list vallist)) :=
  length memll = Z.to_nat CORENUM /\
  forall meml, In meml memll ->
    RH_IPCMem_P_meml meml.

Fixpoint match_sendheap (step: nat) (memll: list (list vallist)) (vll: list vallist) :=
  match memll, vll with
  | nil, nil => True
  | meml :: memll, vl :: vll =>
      nth_error meml step = Some vl /\
      match_sendheap step memll vll
  | _, _ => False
  end.

Definition RLH_IpcSendHeap_P (memll: list (list vallist)) (sh: list (list val)) :=
  match_sendheap (curcore - 1)%nat (firstn curcore memll) (firstn curcore sh) /\
  match_sendheap curcore (skipn (S curcore) memll) (skipn curcore sh).

Definition RLH_IpcRecvHeap_P  (memlls:list (list vallist)) (rh: list (list val)) := nth_error memlls curcore = Some rh.


Definition AOSIPCSem (pl: vallist)  := 
  GAarray IPCSem (Tarray (Tptr OS_EVENT) 8%nat) pl **
  [| isvptr_list pl /\ length pl = 8%nat |].
Definition AOSIPCSendSem (pl: vallist) := 
  GAarray IPCSendSem (Tarray (Tptr OS_EVENT) 8%nat) pl **
  [| isvptr_list pl /\ length pl = 8%nat |].
Definition AOSIPCSemShared l :=
  GV IPCSemShared @ (Tptr OS_EVENT) |-> Vptr l.
(* ptrl : list pointer 这些semaphore实际上不会改变所以这里使用parameter
OS_EXT 	  OS_EVENT* IPCSem[CORENUM];
OS_EXT 	  OS_EVENT* IPCSendSem[CORENUM];
OS_EXT 	  OS_EVENT* IPCSemShared;
 *)
 
(* Parameter OSSendSem_val : list ecbid.
Parameter OSIPCSem_val : list ecbid.
Parameter OSSemShared_val : ecbid.  *)
Definition IPCSem_ptrl := map (fun x => Vptr x) OSIPCSem_val.
Definition IPCSendSem_ptrl := map (fun x => Vptr x) OSSendSem_val.

Definition unsigned2nat v :=
  match v with 
  | Vint32 v => Z.to_nat (Int.unsigned v)
  | _ => 0%nat
  end.

Definition error_broad_stack : list nat :=
  (Z.to_nat CORENUM) :: nil.

Definition legal_broad_element v :=
  match v with 
  | Vint32 v => (Int.lt ($ -1) v = true) /\  (Int.lt v ($ 8) = true ) /\ (Int.eq v ($ DNUM) = false)
  | _ => False
  end.

Definition legal_broadlist z (vl: vallist) :=
  Forall legal_broad_element (firstn (Z.to_nat z) vl).

Definition RLH_BROAD_P z bvl bstack :=
  exists bstack', rev (firstn (Z.to_nat z) bvl)  = bstack' /\ 
  bstack = map unsigned2nat (bstack').


(*  全局视角，能知道发送核只会给一个核发送一个broad, 这是由硬件信号量保证的，但是接受核并不知道这个信息， 加入assert*)
Definition AOSIPCBroadList bvl bstack:= 
  EX z, GV IPCBroad_pointer @ (Tint8) |-> Vint32 ($ z) **
  [| 0 <= z <= CORENUM |] **
  GAarray IPCBroad_Core_Current (Tarray Tint32 8%nat) bvl **
  [| array_type_vallist_match Tint32 bvl /\ length bvl = 8%nat /\ legal_broadlist z bvl|]
  ** [| RLH_BROAD_P z bvl bstack |].

Definition AOSIPCGRinfo m:= 
  GV iIPCGRInfo @ (Tptr Tint32) |-> Vptr ipcgr_addr ** PV ipcgr_addr @ Tint32 |=> (Vint32 m) @ true.

(*add end -------------------------------------------------------------------------*)

(*add for dynamic refactor -----------------------------*)

Definition V_dyn_refac_cfg_dstcoreid (vl:vallist) := nth_val 0 vl.
Definition V_dyn_refac_cfg_prio (vl:vallist) := nth_val 1 vl.
Definition V_dyn_refac_cfg_pdata (vl:vallist) := nth_val 2 vl.
Definition V_dyn_refac_cfg_elf (vl:vallist) := nth_val 3 vl.
Definition V_dyn_refac_cfg_Next     (vl:vallist) := nth_val 4 vl.

Definition V_e_type (vl:vallist):= nth_val 0 vl.
Definition V_e_machine(vl:vallist):= nth_val 1 vl.
Definition V_e_version (vl:vallist):= nth_val 2 vl.
Definition V_e_entry (vl:vallist):= nth_val 3 vl.
Definition V_e_phoff (vl:vallist):=nth_val 4 vl.
Definition V_e_shoff (vl:vallist):=nth_val 5 vl.
Definition V_e_flags (vl:vallist):= nth_val 6 vl.
Definition V_e_ehsize (vl:vallist):= nth_val 7 vl.
Definition V_e_ephentsize (vl:vallist):= nth_val 8 vl.
Definition V_e_phnum (vl:vallist):= nth_val 9 vl.
Definition V_e_shentsize (vl:vallist):= nth_val 10 vl.
Definition V_e_shnum (vl:vallist):= nth_val 11 vl.
Definition V_e_shstrndx (vl:vallist):= nth_val 12 vl.

Definition V_p_type (vl:vallist):= nth_val 0 vl.
Definition V_p_offset (vl:vallist):= nth_val 1 vl.
Definition V_p_vaddr (vl:vallist):= nth_val 2 vl.
Definition V_p_paddr (vl:vallist):= nth_val 3 vl.
Definition V_p_filesz (vl:vallist):= nth_val 4 vl.
Definition V_p_memsz (vl:vallist):= nth_val 5 vl.
Definition V_p_flags (vl:vallist):= nth_val 6 vl.
Definition V_p_align (vl:vallist):= nth_val 7 vl.

Notation Hfreedyn p n := (Aabsdata freedynid (osfreedyn p n)).

Notation Hdynheap h := (Aabsdata dynheapid (osdynheap h)).

Definition AdynrefaccfgFreeList (p:val)(l:list vallist):=
GV dynrefaccfgFreeList @ (Tptr dyn_refac_cfg) |-> p **  sll p l dyn_refac_cfg V_dyn_refac_cfg_Next .

Definition RLH_dynrefaccfgFreeList_freedyn_P (l:list vallist) (n:nat) :=
  length l = n.

Fixpoint Adynheap  (Heapt : list (addrval * list val)) := 
  match Heapt with
  | nil => Aemp
  | (l, vl) :: Heapt'  => Astruct l dyn_refac_cfg vl ** [| struct_type_vallist_match dyn_refac_cfg vl |] ** Adynheap Heapt' 
  end.

Inductive PhdrArray_Pure: list vallist -> list (option vallist) -> list (option vallist) -> list (option vallist) -> Prop:=
  | PhdrArray_Pure_nil: PhdrArray_Pure nil nil nil nil
  | PhdrArray_Pure_NOT_LOAD: forall vll' filevll' memvll' dstvll' vl t,
      PhdrArray_Pure vll' filevll' memvll' dstvll' ->
      V_p_type vl = Some (Vint32 t) ->
       t <> $ PT_LOAD ->
      PhdrArray_Pure (vl::vll') (None::filevll') (None:: memvll') (None::dstvll')
  
  | PhdrArray_PURE_LOAD1:  forall vll' filevll' memvll' dstvll' vl t pfilesz pmemsz pvaddr poffset,
     V_p_type vl = Some (Vint32 t) ->
     V_p_filesz vl = Some (Vint32 pfilesz) ->
     V_p_memsz vl = Some (Vint32 pmemsz) ->
     V_p_vaddr vl = Some (Vptr pvaddr) ->
     V_p_offset vl = Some (Vint32 poffset) ->
     t = $ PT_LOAD ->
     Int.eq pfilesz Int.zero = true ->
     Int.lt pfilesz pmemsz = false ->
     PhdrArray_Pure vll' filevll' memvll' dstvll' ->
     PhdrArray_Pure (vl::vll') (None::filevll') (None:: memvll') (None::dstvll')
     
    | PhdrArray_PURE_LOAD2:  forall vll' filevll' memvll' dstvll' vl t pfilesz pmemsz pvaddr poffset filevl dstvl,
     V_p_type vl = Some (Vint32 t) ->
     V_p_filesz vl = Some (Vint32 pfilesz) ->
     V_p_memsz vl = Some (Vint32 pmemsz) ->
     V_p_vaddr vl = Some (Vptr pvaddr) ->
     V_p_offset vl = Some (Vint32 poffset) ->
     t = $ PT_LOAD ->
     Int.eq pfilesz Int.zero = false ->
     Int.lt pfilesz pmemsz = false ->
     PhdrArray_Pure vll' filevll' memvll' dstvll' ->
     PhdrArray_Pure (vl::vll') (Some filevl::filevll') (None:: memvll') (Some dstvl::dstvll')
     
   | PhdrArray_PURE_LOAD3:  forall vll' filevll' memvll' dstvll' vl t pfilesz pmemsz pvaddr poffset memvl,
     V_p_type vl = Some (Vint32 t) ->
     V_p_filesz vl = Some (Vint32 pfilesz) ->
     V_p_memsz vl = Some (Vint32 pmemsz) ->
     V_p_vaddr vl = Some (Vptr pvaddr) ->
     V_p_offset vl = Some (Vint32 poffset) ->
     t = $ PT_LOAD ->
     Int.eq pfilesz Int.zero = true ->
     Int.lt pfilesz pmemsz = true ->
     PhdrArray_Pure vll' filevll' memvll' dstvll' ->
     PhdrArray_Pure (vl::vll') (None::filevll') (Some memvl:: memvll') (None::dstvll')
     
   | PhdrArray_PURE_LOAD4:  forall vll' filevll' memvll' dstvll' vl t pfilesz pmemsz pvaddr poffset filevl memvl dstvl,
     V_p_type vl = Some (Vint32 t) ->
     V_p_filesz vl = Some (Vint32 pfilesz) ->
     V_p_memsz vl = Some (Vint32 pmemsz) ->
     V_p_vaddr vl = Some (Vptr pvaddr) ->
     V_p_offset vl = Some (Vint32 poffset) ->
     t = $ PT_LOAD ->
     Int.eq pfilesz Int.zero = false ->
     Int.lt pfilesz pmemsz = true ->
     PhdrArray_Pure vll' filevll' memvll' dstvll' ->
     PhdrArray_Pure (vl::vll') (Some filevl::filevll') (Some memvl:: memvll') (Some dstvl::dstvll')
.

Definition PhdrSingle file vl filevl memvl dstvl:=
  ( EX ptype pfilesz pmemsz pvaddr poffset, 
              [| V_p_type vl = Some (Vint32 ptype) |] **
              [| V_p_filesz vl = Some (Vint32 pfilesz) |] ** 
              [| V_p_memsz vl = Some(Vint32 pmemsz) |] **
              [| V_p_vaddr vl = Some (Vptr pvaddr) |] **
              [| V_p_offset vl = Some (Vint32 poffset) |] **
               (match filevl, dstvl with
               |  Some filevlv, Some dstvlv => Aarray pvaddr (Tarray Tint8 (Z.to_nat (Int.unsigned pfilesz))) dstvlv **
                                                                          Aarray (get_off_addr file poffset) (Tarray Tint8 (Z.to_nat (Int.unsigned pfilesz))) filevlv  
               | None, None => Aemp
               | _,_ => Afalse
               end
               ) ** 
               (match memvl with
               | None => Aemp
               | Some memvlv =>  Aarray (get_off_addr pvaddr pfilesz) (Tarray Tint8 (Z.to_nat (Int.unsigned (Int.sub pmemsz pfilesz)))) memvlv  
               end )
               ).

Fixpoint PhdrArray(file:addrval)(p:addrval)(vll:list vallist) (filevll memvll dstvll:list (option vallist)):=        
        match vll, filevll, memvll, dstvll with
        | nil, nil, nil, nil => Aemp
        | vl::vll', filevl::filevll', memvl::memvll', dstvl::dstvll' => 
              Astruct p Elf32_Phdr vl ** [|struct_type_vallist_match Elf32_Phdr vl|] **
              PhdrSingle file vl filevl memvl dstvl **
              PhdrArray file (get_off_addr p ($ size_of_Elf32_Phdr))  vll' filevll' memvll'  dstvll'  
        | _ ,_ , _ ,_  => Afalse
        end.

(*add end -------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------------------*)
(* add partition                                                  *)
(*-----------------------------------------------------------------------------------*)
Notation Hkernelport kportl := (Aabsdata oskportid (oskport kportl)).
Notation Hchannell chanl := (Aabsdata oschannelid (oschannel chanl)).
Notation Hdomainportl dportl := (Aabsdata osdomainportid (osdomainport dportl)).
Notation Hcoreportpl cportpl := (Aabsdata oscoreportplid (oscoreportpl cportpl)).
(* Astruct for OS_Port's port part *)

Open Scope code_scope.
Definition OS_Port_Seg_dls:decllist:=
                  ⌞
                   domain @ Int32u;
                   maxMsgSize @ Int8u;
                   coreNum @ Int8u;
                   portID @ Int32u;
                   direction @ port_direction_t;
                   mode @ port_mode_t;
                   refreshRate @ Int32u;
                   status @ port_ctrl_status_t;
                   msgInTick @ Int32u;
                   msgOutTick @ Int32u;
                   OSEventPtrPort @ Void ∗;
                   nextPort @ Void ∗;
                   OSQStart @ OSMsg_t ∗;
                   OSQEnd @ OSMsg_t ∗;
                   OSQIn @ OSMsg_t ∗;
                   OSQOut @ OSMsg_t ∗;
                   OSQSize @ Int16u;
                   OSQEntries @ Int16u
                  ⌟ .
Close Scope code_scope.

Definition APortStruct (p: addrval) (vl: vallist) :=
  Astruct' (get_off_addr p ($29)) OS_Port_Seg_dls vl.

(* OS_Port  OS_Port_Seg_dls vallist *)
Definition OS_Port_V_domain        (vl:vallist) := nth_val 0 vl.
Definition OS_Port_V_maxMsgSize    (vl:vallist) := nth_val 1 vl.
Definition OS_Port_V_coreNum       (vl:vallist) := nth_val 2 vl.
Definition OS_Port_V_portID        (vl:vallist) := nth_val 3 vl.
Definition OS_Port_V_direction     (vl:vallist) := nth_val 4 vl.
Definition OS_Port_V_mode          (vl:vallist) := nth_val 5 vl.
Definition OS_Port_V_refreshRate   (vl:vallist) := nth_val 6 vl.
Definition OS_Port_V_status        (vl:vallist) := nth_val 7 vl.
Definition OS_Port_V_msgInTick     (vl:vallist) := nth_val 8 vl.
Definition OS_Port_V_msgOutTick    (vl:vallist) := nth_val 9 vl.
Definition OS_Port_V_OSEventPtrPort(vl:vallist) := nth_val 10 vl.
Definition OS_Port_V_nextPort      (vl:vallist) := nth_val 11 vl.
Definition OS_Port_V_OSQStart      (vl:vallist) := nth_val 12 vl.
Definition OS_Port_V_OSQEnd        (vl:vallist) := nth_val 13 vl.
Definition OS_Port_V_OSQIn         (vl:vallist) := nth_val 14 vl.
Definition OS_Port_V_OSQOut        (vl:vallist) := nth_val 15 vl.
Definition OS_Port_V_OSQSize       (vl:vallist) := nth_val 16 vl.
Definition OS_Port_V_OSQEntries    (vl:vallist) := nth_val 17 vl.

(* OS_K_Port vallist *)
Definition OS_K_Port_V_portID     (vl:vallist) := nth_val 0 vl.
Definition OS_K_Port_V_channelID  (vl:vallist) := nth_val 1 vl.
Definition OS_K_Port_V_dmport     (vl:vallist) := nth_val 2 vl.
Definition OS_K_Port_V_channel    (vl:vallist) := nth_val 3 vl.
Definition OS_K_Port_V_coreNum    (vl:vallist) := nth_val 4 vl.
Definition OS_K_Port_V_status     (vl:vallist) := nth_val 5 vl.
Definition OS_K_Port_V_OSEventPtr (vl:vallist) := nth_val 6 vl.

(* OS_Channel vallist *)
Definition OS_Channel_V_channelID   (vl:vallist) := nth_val 0 vl.
Definition OS_Channel_V_srcPortsNum (vl:vallist) := nth_val 1 vl.
Definition OS_Channel_V_dstPortsNum (vl:vallist) := nth_val 2 vl.
Definition OS_Channel_V_semaphore   (vl:vallist) := nth_val 3 vl.
Definition OS_Channel_V_dstPortsHead(vl:vallist) := nth_val 4 vl.
Definition OS_Channel_V_dstPortsTail(vl:vallist) := nth_val 5 vl.
Definition OS_Channel_V_srcPort     (vl:vallist) := nth_val 6 vl.
Definition OS_Channel_V_OSEventPtr  (vl:vallist) := nth_val 7 vl.

(* OSKernelPortFreeList *)
Fixpoint kportf_sllseg (head tailnext : val)  (l:list vallist) (t:type) (next: vallist -> option val):=
  match l with
    | nil => [| head = tailnext |]
    | vl::l' => EX vn,
                [| next vl = Some vn |] **
                node head vl t ** 
                [| OS_K_Port_V_portID vl = Some (V$ DEFAULT_PORTID) |]**
                [| OS_K_Port_V_OSEventPtr vl = Some vn |]**
                [| OS_K_Port_V_coreNum vl = Some (V$ DEFAULT_CORENUM) |]**
                [| OS_K_Port_V_channelID vl = Some (V$ DEFAULT_CHANELID) |]**
                [| OS_K_Port_V_dmport vl = Some Vnull |]**
                [| OS_K_Port_V_channel vl = Some Vnull |]**
                [| OS_K_Port_V_status vl = Some (V$ DEFAULT_PORTSTATE) |]**
                kportf_sllseg vn tailnext l' t next
  end.

Definition kportf_sll := 
  fun (head : val) (l : list vallist) (t : type) (next : vallist -> option val) =>
    kportf_sllseg head Vnull l t next.

Definition AOSKernelPortFreeList p (l:list vallist) :=
  (GV OSKernelPortFreeList @ (Tptr OS_K_Port) |-> p) ** 
      kportf_sll p l OS_K_Port OS_K_Port_V_OSEventPtr.

(* OSKernelPortIDTbl *)
Open Scope code_scope.
Definition OS_K_Port_Seg_dls:decllist:=
    ⌞portID @ Int8u;
    channelID @ Int8u;
    dmport @ OS_Port ∗; 
    channel @ Void ∗;
    coreNum @ Int8u;
    status @ port_ctrl_status_t
    ⌟.
Close Scope code_scope.

Fixpoint kportNode_P (kportvl: vallist) (kportl: list vallist):=
  match kportvl, kportl with
    | nil, nil => Aemp
    | v::vl, l::vl' => 
      (
        ( [| v = Vnull /\ l = nil |] ) \\//
        (
          (* node v l OS_K_Port ** *)
          EX b, 
            [| v= Vptr (b,Int.zero) /\ struct_type_vallist_match OS_K_Port l |] ** 
            Astruct' (b,Int.zero) OS_K_Port_Seg_dls (firstn 6 l) 
        )
      ) **
      kportNode_P vl vl'
    | _, _ => Afalse
  end.

Definition AOSKernelPortIDTbl (vl:vallist) (l: list vallist):=
  GAarray OSKernelPortIDTbl (Tarray (Tptr OS_K_Port) (nat_of_Z PORT_NUMS)) vl ** 
  kportNode_P vl l **
  [| array_type_vallist_match (Tptr OS_K_Port) vl /\ length vl = (nat_of_Z PORT_NUMS)|] **
  [| forall id1 id2 p1 p2, id1 <> id2 -> nth_val id1 vl = Some (Vptr p1) -> 
    nth_val id2 vl = Some (Vptr p2) -> p1 <> p2 |].

(* RLH about KernelPortIDTbl  *)
Definition Kernelport_nat_P (vl: vallist) (port: KPort): Prop :=
  match port with
  | (Hid, _, _, HcoreNum, Hstatus) =>
    exists Lid LcoreNum Lstatus,
      OS_K_Port_V_portID vl = Some (Vint32 Lid) /\ nat_of_Z (Int.unsigned Lid) = Hid /\
      OS_K_Port_V_coreNum vl = Some (Vint32 LcoreNum) /\ nat_of_Z (Int.unsigned LcoreNum) = HcoreNum /\
      OS_K_Port_V_status vl = Some (Vint32 Lstatus) /\ nat_of_Z (Int.unsigned Lstatus) = Hstatus 
  end.

Definition Kernelport_dmport_P (vl: vallist) (port: KPort): Prop :=
  match port with
  | (_, None, _, _, _) =>
    OS_K_Port_V_dmport vl = None
  | (_, Some dmport, _, _, _) => 
    OS_K_Port_V_dmport vl = Some (Vptr dmport)
  end.

Definition Kernelport_channel_P (vl: vallist) (port: KPort): Prop :=
  match port with
  | (_, _, None, _, _) =>
    OS_K_Port_V_channel vl = Some (Vnull)
  | (_, _, Some channel, _, _) => 
    OS_K_Port_V_channel vl = Some (Vptr channel)  (* channelID? *)
  end.

Definition KernelportNode_P (vl: vallist) (port: KPort): Prop :=
  Kernelport_nat_P vl port /\ Kernelport_dmport_P vl port /\ Kernelport_channel_P vl port.

Fixpoint RLH_Kernelport (kportvl: vallist) (kportl: list vallist) (kportls : KernelPMod.map): Prop :=
  match kportvl, kportl with
    | nil, nil => kportls = emp
    | v::vl, l::vl' => 
        (v = Vnull /\ l = nil /\ RLH_Kernelport vl vl' kportls) \/
        (
          exists pptr port kportls',
          v = Vptr pptr /\ 
          join (sig pptr port) kportls' kportls /\ 
          KernelportNode_P l port /\
          RLH_Kernelport vl vl' kportls'
        )
    | _, _ => False
  end.

(* OSKernelPortTbl *)
Definition AOSKernelPortTbl (vl:vallist) :=
  GAarray OSKernelPortTbl (Tarray (OS_K_Port) (nat_of_Z PORT_NUMS)) vl **
  [| array_type_vallist_match (OS_K_Port) vl /\ length vl = (nat_of_Z PORT_NUMS)|].

(* OSChannelFreeList *)
Fixpoint channelf_sllseg (head tailnext : val)  (l:list vallist) (t:type) (next: vallist -> option val):=
  match l with
    | nil => [| head = tailnext |]
    | vl::l' => EX  vn,
                [|next vl = Some vn|] **
                node head vl t ** 
                [| OS_Channel_V_channelID vl = Some (V$ DEFAULT_CHANELID) |] **
                [| OS_Channel_V_srcPortsNum vl = Some (V$ 0) |] **
                [| OS_Channel_V_dstPortsNum vl = Some (V$ 0) |] **
                [| OS_Channel_V_semaphore vl = Some (V$ DEFAULT_CHANNLE_SEMAPHROE) |] **
                [| OS_Channel_V_dstPortsHead vl = Some Vnull |] **
                [| OS_Channel_V_dstPortsTail vl = Some Vnull |] **
                [| OS_Channel_V_OSEventPtr vl = Some vn |] **
                channelf_sllseg vn tailnext l' t next
  end.

Definition channelf_sll := 
  fun (head : val) (l : list vallist) (t : type) (next : vallist -> option val) =>
    channelf_sllseg head Vnull l t next.

Definition AOSChannelFreeList p (l : list vallist) :=
  (GV OSChannelFreeList @ (Tptr OS_Channel) |-> p) **
    channelf_sll p l OS_Channel OS_Channel_V_OSEventPtr.

(* OSChannelIDTbl *)
Fixpoint Channel_dstkport_get (head: val) (tail: val) (num: nat) (dl: list addrval): asrt:=
  match dl, num with
  | nil, 0%nat => [| head = tail |]
  | d::dl', S n =>  [| head = (Vptr d) |] **
                    EX vl vn ,
                      [| struct_type_vallist_match OS_K_Port vl |] **
                      PV (get_off_addr d (Int.repr 12)) @ (Tptr Tvoid) |-> vn **
                      (* node head vl OS_K_Port ** *)
                      [| OS_K_Port_V_OSEventPtr vl = Some vn |] **
                      Channel_dstkport_get vn tail n dl'
  | _, _ => Afalse
  end.

Fixpoint ChannelNode (channelvl: vallist) (channell: list vallist) (dstkportll: list (list addrval)):=
  match channelvl, channell, dstkportll with
    | nil, nil, nil => Aemp
    | v::vl, l::vl', dl::dll' =>
        (
          ( [| v = Vnull /\ l = nil /\ dl = nil |] ) \\//
          (
            node v l OS_Channel **
            (
              EX head num,
                [| OS_Channel_V_dstPortsHead l = Some head |] **
                [| OS_Channel_V_dstPortsNum l = Some (Vint32 num) |] **
                Channel_dstkport_get head Vnull (Z.to_nat (Int.unsigned num)) dl
            )
          )
        ) **
        ChannelNode vl vl' dll'
    | _, _, _ => Afalse
  end.

Definition AOSChannelIDTbl (vl:vallist) (channell: list vallist) (dstkportll: list (list addrval)):=
  GAarray OSChannelIDTbl (Tarray (Tptr OS_Channel) (nat_of_Z CHANNEL_NUMS)) vl **
  ChannelNode vl channell dstkportll **
  [| array_type_vallist_match (Tptr OS_Channel) vl /\ length vl = (nat_of_Z CHANNEL_NUMS)|] **
  [| forall id1 id2 p1 p2, id1 <> id2 -> nth_val id1 vl = Some (Vptr p1) -> 
    nth_val id2 vl = Some (Vptr p2) -> p1 <> p2 |].

Definition Channel_nat_P (vl: vallist) (channel: Channel) (dstkportl: list addrval): Prop :=
  match channel with
  | (Hid, Hdstnum, _, _) =>
    exists Lid Ldstnum,
      OS_Channel_V_channelID vl = Some (Vint32 Lid) /\ nat_of_Z (Int.unsigned Lid) = Hid /\
      OS_Channel_V_dstPortsNum vl = Some (Vint32 Ldstnum) /\ 
      nat_of_Z (Int.unsigned Ldstnum) = Hdstnum /\
      nat_of_Z (Int.unsigned Ldstnum) = length dstkportl
  end.

Fixpoint Channel_dstkport_Queue_IncoreC (otherppl: list addrval) (chanptr: addrval) (dstkportl: list addrval) (kportls: KernelPMod.map) (dportls: DomainPortMod.map): Prop :=
  match dstkportl with
  | nil => True
  | dstkport::dstkportl' =>
      (exists pid pptr kpst pd pst pin pout, exists sz pm nextdst,
        get kportls dstkport = Some (pid, Some pptr, Some chanptr, nat_of_Z DNUM, kpst) /\
        get dportls pptr = Some (nat_of_Z DNUM, pd, pid, DestinationP nextdst, pst, pin, pout, QueuePort sz pm) /\
        ~ In pptr otherppl ) /\
      Channel_dstkport_Queue_IncoreC otherppl chanptr dstkportl' kportls dportls
  end.

Fixpoint Channel_dstkport_Sample_IncoreC (otherppl: list addrval) (chanptr: addrval) (dstkportl: list addrval) (kportls: KernelPMod.map) (dportls: DomainPortMod.map): Prop :=
  match dstkportl with
  | nil => True
  | dstkport::dstkportl' =>
      (exists pid pptr kpst pd pst pin pout, exists pm nextdst,
        get kportls dstkport = Some (pid, Some pptr, Some chanptr, nat_of_Z DNUM, kpst) /\
        get dportls pptr = Some (nat_of_Z DNUM, pd, pid, DestinationP nextdst, pst, pin, pout, SamplePort pm) /\
        ~ In pptr otherppl ) /\
      Channel_dstkport_Sample_IncoreC otherppl chanptr dstkportl' kportls dportls
  end.

Fixpoint Channel_dstkport_Queue_OutcoreC (otherppl: list addrval) (chanptr: addrval) (dstkportl: list addrval) (kportls: KernelPMod.map) (dportls: DomainPortMod.map): Prop :=
  match dstkportl with
  | nil => True
  | dstkport::dstkportl' =>
      (exists pid pptr pcn kpst pd pst pin pout, exists sz pm nextdst,
        get kportls dstkport = Some (pid, Some pptr, Some chanptr, pcn, kpst) /\
        get dportls pptr = Some (pcn, pd, pid, DestinationP nextdst, pst, pin, pout, QueuePort sz pm) /\
        (pcn <> nat_of_Z DNUM)%nat /\ In pptr otherppl ) /\
      Channel_dstkport_Queue_OutcoreC otherppl chanptr dstkportl' kportls dportls
  end.

Fixpoint Channel_dstkport_Sample_OutcoreC (otherppl: list addrval) (chanptr: addrval) (dstkportl: list addrval) (kportls: KernelPMod.map) (dportls: DomainPortMod.map): Prop :=
  match dstkportl with
  | nil => True
  | dstkport::dstkportl' =>
      (exists pid pptr pcn kpst pd pst pin pout, exists pm nextdst,
        get kportls dstkport = Some (pid, Some pptr, Some chanptr, pcn, kpst) /\
        get dportls pptr = Some (pcn, pd, pid, DestinationP nextdst, pst, pin, pout, SamplePort pm) /\
        (pcn <> nat_of_Z DNUM)%nat /\ In pptr otherppl ) /\
      Channel_dstkport_Sample_OutcoreC otherppl chanptr dstkportl' kportls dportls
  end.

Definition Channel_srckport_Sample (chanptr: addrval) (vl: vallist) (kportls: KernelPMod.map) (dportls: DomainPortMod.map): Prop :=
  ( OS_Channel_V_srcPort vl = Some Vnull /\
    OS_Channel_V_srcPortsNum vl = Some (Vint32 (Int.repr 0))) \/
  ( exists srckport,
      OS_Channel_V_srcPort vl = Some (Vptr srckport) /\
      OS_Channel_V_srcPortsNum vl = Some (Vint32 (Int.repr 1)) /\
      (exists pid pptr kpst pd pst pin pout, exists pm,
          get kportls srckport = Some (pid, Some pptr, Some chanptr, nat_of_Z DNUM, kpst) /\
          get dportls pptr = Some (nat_of_Z DNUM, pd, pid, SourceP, pst, pin, pout, SamplePort pm))).

Definition Channel_srckport_Queue (chanptr: addrval) (vl: vallist) (kportls: KernelPMod.map) (dportls: DomainPortMod.map): Prop :=
  ( OS_Channel_V_srcPort vl = Some Vnull /\
    OS_Channel_V_srcPortsNum vl = Some (Vint32 (Int.repr 0))) \/
  ( exists srckport,
      OS_Channel_V_srcPort vl = Some (Vptr srckport) /\
      OS_Channel_V_srcPortsNum vl = Some (Vint32 (Int.repr 1)) /\
      (exists pid pptr kpst pd pst pin pout, exists sz pm,
          get kportls srckport = Some (pid, Some pptr, Some chanptr, nat_of_Z DNUM, kpst) /\
          get dportls pptr = Some (nat_of_Z DNUM, pd, pid, SourceP, pst, pin, pout, QueuePort sz pm))).

(* dportls1: 本核, dportls2: 其他核 *)
Definition Channel_type_P (otherppl: list addrval) (vl: vallist) (channel: Channel) (chanptr: addrval) (dstkportl: list addrval) (kportls: KernelPMod.map) (dportls1: DomainPortMod.map) (dportls2: DomainPortMod.map): Prop :=
  match channel with
  | (_, _, Hdstkport, IncoreC) =>
      OS_Channel_V_semaphore vl = Some (Vint32 (Int.repr DEFAULT_CHANNLE_SEMAPHROE)) /\
      Hdstkport = dstkportl /\
      ( (Channel_dstkport_Sample_IncoreC otherppl chanptr dstkportl kportls dportls1 /\
          Channel_srckport_Sample chanptr vl kportls dportls1) \/
        (Channel_dstkport_Queue_IncoreC otherppl chanptr dstkportl kportls dportls1 /\
          Channel_srckport_Queue chanptr vl kportls dportls1) )
  | (_, _, Hdstkport, OutcoreC csem) =>
      OS_Channel_V_semaphore vl = Some (Vint32 ($ (Z.of_nat csem))) /\ 
      (Int.eq ($ (Z.of_nat csem)) ($ DEFAULT_CHANNLE_SEMAPHROE) = false) /\
      Hdstkport = dstkportl /\
      ( (Channel_dstkport_Sample_OutcoreC otherppl chanptr dstkportl kportls dportls2 /\
          Channel_srckport_Sample chanptr vl kportls dportls1) \/
        (Channel_dstkport_Queue_OutcoreC otherppl chanptr dstkportl kportls dportls2 /\
          Channel_srckport_Queue chanptr vl kportls dportls1) )
  end.

Definition ChannelNode_P (otherppl: list addrval) (vl: vallist) (channel: Channel) (chanptr: addrval) (dstkportl: list addrval) (kportls: KernelPMod.map) (dportls1: DomainPortMod.map) (dportls2: DomainPortMod.map): Prop :=
  Channel_nat_P vl channel dstkportl /\ Channel_type_P otherppl vl channel chanptr dstkportl kportls dportls1 dportls2 /\ NoDup dstkportl.

Fixpoint RLH_Channel (otherppl: list addrval) (channelvl: vallist) (channell: list vallist) (dstkportll: list (list addrval)) (channells : ChannelMod.map) (kportls: KernelPMod.map) (dportls1: DomainPortMod.map) (dportls2: DomainPortMod.map): Prop :=
  match channelvl, channell, dstkportll with
    | nil, nil, nil => channells = emp
    | v::vl, l::vl', dl::dll' => 
        (
          v = Vnull /\ l = nil /\ dl = nil /\
          RLH_Channel otherppl vl vl' dll' channells kportls dportls1 dportls2
        ) \/
        (
          exists cptr channel channells',
          v = Vptr cptr /\ 
          join (sig cptr channel) channells' channells /\ 
          ChannelNode_P otherppl l channel cptr dl kportls dportls1 dportls2 /\
          RLH_Channel otherppl vl vl' dll' channells' kportls dportls1 dportls2
        )
    | _, _, _ => False
  end.

(* OSCorePortPtrList *)
Fixpoint cportp_sllseg (head tailnext : val)  (l:list vallist) (t:type) (next: vallist -> option val):=
  match l with
    | nil => [| head = tailnext |]
    | vl::l' => EX  vn,
                [|next vl = Some vn|] **
                node head vl t ** 
                [| OS_Port_V_OSEventPtrPort vl = Some vn |] **
                cportp_sllseg vn tailnext l' t next
  end.

Definition option_addrval_to_val (v: option addrval): val :=
  match v with
  | None => Vnull
  | Some v => Vptr v
  end.

Fixpoint RH_CorePortPtrList (headptr: val) (cportpl:list addrval)(dportls1:DomainPortMod.map):=
  match cportpl with
  | nil => headptr = Vnull
  | p::pl => exists pcn pd pid nexthd pst pin pout pt, 
            headptr = Vptr p /\ 
            get dportls1 p = Some (pcn, pd, pid, DestinationP nexthd, pst, pin, pout, pt) /\
            RH_CorePortPtrList (option_addrval_to_val nexthd) pl dportls1
  end.

Definition AOSCorePortPtrList p (pl : list addrval) (dportls1:DomainPortMod.map):=
  (GV OSCorePortPtrList @ (Tptr OS_Port) |-> p) **
  [| RH_CorePortPtrList p pl dportls1 |].

(* OSDomainPortPtrList *)
Definition dmportp_sllseg_sampleport_msg (qstart: addrval) vll :=
  EX vl,
    [| vll = vl :: nil |] **
    PV qstart @ Tint8 |-> (Vint32 ($ (Z.of_nat (length vl)))) ** 
    (EX vl2, [| (length vl + length vl2 = nat_of_Z CHANNEL_CACHE_SZIE)%nat /\
                array_type_vallist_match Tint8 (vl++vl2) |] **
    Aarray (get_off_addr qstart (Int.one)) (Tarray Tint8 (nat_of_Z CHANNEL_CACHE_SZIE)) (vl ++ vl2)).

Definition msg_distance (v1 v2:addrval) :=
  Int.unsigned (Int.divu (Int.sub (snd v2) (snd v1)) (Int.repr (Z_of_nat (typelen OSMsg_t)))).

Definition dmportp_sllseg_qport_msg_next (pnow qstart qend: addrval): addrval :=
  if (msg_distance pnow qend) =? 1
  then qstart
  else let (b,i) := pnow in (b, (Int.add i (Int.repr (Z_of_nat (typelen OSMsg_t))))).

Fixpoint dmportp_sllseg_qport_msg (pnow pend qstart qend: addrval) (qentries: nat) (vll: list vallist) :=
  match vll, qentries with
  | nil, 0%nat => [| pnow = pend |]
  | vl::vll', S n =>
      PV pnow @ Tint8 |-> (Vint32 ($ (Z.of_nat (length vl)))) ** 
      (EX vl2, [| (length vl + length vl2 = nat_of_Z CHANNEL_CACHE_SZIE)%nat /\
                  array_type_vallist_match Tint8 (vl++vl2)|] **
      Aarray (get_off_addr pnow (Int.one)) (Tarray Tint8 (nat_of_Z CHANNEL_CACHE_SZIE)) (vl++vl2)) **
      dmportp_sllseg_qport_msg (dmportp_sllseg_qport_msg_next pnow qstart qend) pend qstart qend n vll' 
  | _, _ => Afalse
  end.

Definition Qport_msg_ptrs_P (qstart qend qout qin : addrval) (qsize: Z) :=
  let (b, i) := qstart in i = Int.zero /\
  qend = get_off_addr qstart (Int.mul ($ qsize) ($ (Z_of_nat (typelen OSMsg_t))))  /\ 
  exists z1 z2, qout = get_off_addr qstart (Int.mul ($ z1) ($ (Z_of_nat (typelen OSMsg_t)))) /\ 
                qin = get_off_addr qstart (Int.mul ($ z2) ($ (Z_of_nat (typelen OSMsg_t)))) /\ 
                0 <= z1 < qsize /\ 0 <= z2 < qsize.

Fixpoint dmportp_sllseg (head tailnext : val) (l:list vallist) (msglist:list (list vallist)) (next: vallist -> option val):=
  match l, msglist with
    | nil, nil => [| head = tailnext |]
    | l::l', vl::vl' => EX vn headptr qstart,
                          [| head = Vptr headptr |] **
                          [| next l = Some vn |] **
                          APortStruct headptr l **
                          [| struct_type_vallist_match' OS_Port_Seg_dls l |] **
                          [| OS_Port_V_OSQStart l = Some (Vptr qstart) |] **
                          (
                            (
                              [| OS_Port_V_mode l = Some (Vint32 (ZToInt SAMPLE)) |] **
                              dmportp_sllseg_sampleport_msg qstart vl
                            ) \\//
                            (
                              EX qend qin qout qsize qentries vl2,
                              [| OS_Port_V_mode l = Some (Vint32 (ZToInt QUEUE)) |] **
                              [| OS_Port_V_OSQEnd l = Some (Vptr qend) |] **
                              [| OS_Port_V_OSQIn l = Some (Vptr qin) |] **
                              [| OS_Port_V_OSQOut l = Some (Vptr qout) |] **
                              [| OS_Port_V_OSQSize l = Some (Vint32 qsize) /\ Int.unsigned qsize <= 65535 |] **
                              [| OS_Port_V_OSQEntries l = Some (Vint32 qentries) /\ Int.unsigned qentries <= Int.unsigned qsize |] **
                              [| Qport_msg_ptrs_P qstart qend qout qin (Int.unsigned qsize) |] **
                              (* valid msg list from qout to qin *)
                              dmportp_sllseg_qport_msg qout qin qstart qend (nat_of_Z (Int.unsigned qentries)) vl **
                              (* invalid msg list from qin to qout *)
                              dmportp_sllseg_qport_msg qin qout qstart qend (nat_of_Z (Int.unsigned qsize - Int.unsigned qentries)) vl2
                            )
                          ) **
                          dmportp_sllseg vn tailnext l' vl' next
    | _, _ => Afalse
  end.

Definition dmportp_sll := 
  fun (head : val) (l : list vallist) (msglist : list (list vallist)) (next : vallist -> option val) =>
    dmportp_sllseg head Vnull l msglist next.

Definition AOSDomainPortPtrList p (l : list vallist) (msglist : list (list vallist)):=
  (GV OSDomainPortPtrList @ (Tptr OS_Port) |-> p) **
    dmportp_sll p l msglist OS_Port_V_nextPort.

Definition Domainport_nat_P vl (port: Port) :=
  match port with
  | (port_corenum, port_domain, port_id, _, port_status, port_intick, port_outick, _) =>
      exists domain id status intick outick, 
        OS_Port_V_coreNum vl = Some (Vint32 (Int.repr DNUM)) /\ nat_of_Z DNUM = port_corenum /\
        OS_Port_V_domain vl = Some (Vint32 domain) /\ nat_of_Z (Int.unsigned domain) = port_domain /\
        OS_Port_V_portID vl = Some (Vint32 id) /\ nat_of_Z (Int.unsigned id) = port_id /\ Int.unsigned id < PORT_NUMS /\
        OS_Port_V_status vl = Some (Vint32 status) /\ nat_of_Z (Int.unsigned status) = port_status /\
        OS_Port_V_msgInTick vl = Some (Vint32 intick) /\ nat_of_Z (Int.unsigned intick) = port_intick /\
        OS_Port_V_msgOutTick vl = Some (Vint32 outick) /\ nat_of_Z (Int.unsigned outick) = port_outick
  end.

Definition Domainport_direction_P vl (port: Port) :=
  match port with
  | (_, _, _, SourceP, _, _, _, _) => OS_Port_V_direction vl = Some (Vint32 (Int.repr SOURCE))
  | (_, _, _, DestinationP nextdst, _, _, _, _) => OS_Port_V_direction vl = Some (Vint32 (Int.repr DESTINATION)) /\
      match nextdst with
      | None => OS_Port_V_OSEventPtrPort vl = Some Vnull
      | Some p => OS_Port_V_OSEventPtrPort vl = Some (Vptr p)
      end
  end.

Definition Domainport_Portt_P vl (port: Port) (msgl: list vallist) :=
  match port with
  | (_, _, _, _, _, _, _, SamplePort msg) => 
      exists msgsig, msg = Some msgsig /\ msgl = msgsig :: nil /\ 
      OS_Port_V_mode vl = Some (Vint32 (Int.repr SAMPLE))
  | (_, _, _, _, _, _, _, QueuePort sz msgs) => 
      msgs = msgl /\ OS_Port_V_OSQSize vl = Some (Vint32 (Int.repr (Z.of_nat sz))) /\ 
      OS_Port_V_mode vl = Some (Vint32 (Int.repr QUEUE))
  end.

Definition DomainportNode_P vl port msgl : Prop :=
  Domainport_nat_P vl port /\ Domainport_direction_P vl port /\ Domainport_Portt_P vl port msgl.

Fixpoint RLH_Domainportl headptr dportl (msglist : list (list vallist)) (dportls : DomainPortMod.map) : Prop :=
  match dportl, msglist with 
  | nil, nil => headptr = Vnull  /\ dportls = emp
  | dport :: dportl', msgl :: msglist' => exists pptr port dportls',
                                          headptr = Vptr pptr /\ 
                                          join (sig pptr port) dportls' dportls /\ 
                                          DomainportNode_P dport port msgl /\
                                          (exists hd', 
                                            OS_Port_V_nextPort dport = Some hd' /\ 
                                            RLH_Domainportl hd' dportl' msglist' dportls')
  | _, _ => False
  end.

Fixpoint RL_PortPtrList (headptr: val) (dportl: list vallist)  (dpptrl: list addrval)  : Prop :=
  match dportl, dpptrl with 
  | nil, nil => headptr = Vnull 
  | dport :: dportl',  pptr:: dpptrl' => headptr = Vptr pptr /\ 
                                         exists hd',  OS_Port_V_nextPort dport = Some hd' /\
                                                      RL_PortPtrList hd' dportl' dpptrl' 
  | _, _ => False
end.

Definition RLH_PortPtrINecb  headptr dportl dpptrl (ecbls : EcbMod.map) : Prop :=
  RL_PortPtrList headptr dportl dpptrl /\ 
  Forall (fun x : addrval => exists wt, get ecbls x = Some (absport, wt)) dpptrl.

Fixpoint OtherPortPtrList (otherppl: list addrval) (otherpl: list vallist) (othermsgll: list (list vallist)) := 
  match otherppl, otherpl, othermsgll with
  | nil, nil, nil => Aemp
  | portp :: otherppl', port :: otherpl', msgl :: othermsgll'  =>
      EX qstart, 
        APortStruct portp port **
        [| struct_type_vallist_match' OS_Port_Seg_dls port |] **
        [| OS_Port_V_OSQStart port = Some (Vptr qstart) |] **
        (
          (
            [| OS_Port_V_mode port = Some (Vint32 (Int.repr SAMPLE)) |] **
            dmportp_sllseg_sampleport_msg qstart msgl
          ) \\//
          (
            EX qend qin qout qsize qentries vl2,
            [| OS_Port_V_mode port = Some (Vint32 (Int.repr QUEUE)) |] **
            [| OS_Port_V_OSQEnd port = Some (Vptr qend) |] **
            [| OS_Port_V_OSQIn port = Some (Vptr qin) |] **
            [| OS_Port_V_OSQOut port = Some (Vptr qout) |] **
            [| OS_Port_V_OSQSize port = Some (Vint32 qsize) /\ Int.unsigned qsize <= 65535 |] **
            [| OS_Port_V_OSQEntries port = Some (Vint32 qentries) /\ Int.unsigned qentries <= Int.unsigned qsize |] **
            [| Qport_msg_ptrs_P qstart qend qout qin (Int.unsigned qsize) |] **
            (* valid msg list from qout to qin *)
            dmportp_sllseg_qport_msg qout qin qstart qend (nat_of_Z (Int.unsigned qentries)) msgl **
            (* invalid msg list from qin to qout *)
            dmportp_sllseg_qport_msg qin qout qstart qend (nat_of_Z (Int.unsigned qsize - Int.unsigned qentries)) vl2
          )
        ) **
      OtherPortPtrList otherppl' otherpl' othermsgll'
  | _, _, _ => Afalse
  end.

Definition OtherPort_nat_P vl (port: Port) :=
  match port with
  | (port_corenum, port_domain, port_id, _, port_status, port_intick, port_outick, _) =>
      exists corenum domain id status intick outick, 
        OS_Port_V_coreNum vl = Some (Vint32 corenum) /\ (nat_of_Z (Int.unsigned corenum)) = port_corenum /\
        (Int.unsigned corenum) <> DNUM /\
        OS_Port_V_domain vl = Some (Vint32 domain) /\ nat_of_Z (Int.unsigned domain) = port_domain /\
        OS_Port_V_portID vl = Some (Vint32 id) /\ nat_of_Z (Int.unsigned id) = port_id /\ Int.unsigned id < PORT_NUMS /\
        OS_Port_V_status vl = Some (Vint32 status) /\ nat_of_Z (Int.unsigned status) = port_status /\
        OS_Port_V_msgInTick vl = Some (Vint32 intick) /\ nat_of_Z (Int.unsigned intick) = port_intick /\
        OS_Port_V_msgOutTick vl = Some (Vint32 outick) /\ nat_of_Z (Int.unsigned outick) = port_outick
  end.

Definition OtherPort_direction_P vl (port: Port) :=
  match port with
  | (_, _, _, SourceP, _, _, _, _) => OS_Port_V_direction vl = Some (Vint32 (Int.repr SOURCE))
  | (_, _, _, DestinationP nextdst, _, _, _, _) => OS_Port_V_direction vl = Some (Vint32 (Int.repr DESTINATION)) /\ 
                                                   match nextdst with
                                                   | None => OS_Port_V_OSEventPtrPort vl = Some Vnull
                                                   | Some p => OS_Port_V_OSEventPtrPort vl = Some (Vptr p)
                                                   end
  end.

Definition OtherPort_Portt_P vl (port: Port) (msgl: list vallist) :=
  match port with
  | (_, _, _, _, _, _, _, SamplePort msg) => 
      exists msgsig, msg = Some msgsig /\ msgl = msgsig :: nil /\ 
      OS_Port_V_mode vl = Some (Vint32 (Int.repr SAMPLE))
  | (_, _, _, _, _, _, _, QueuePort sz msgs) => 
      msgs = msgl /\ OS_Port_V_OSQSize vl = Some (Vint32 (Int.repr (Z.of_nat sz))) /\ 
      OS_Port_V_mode vl = Some (Vint32 (Int.repr QUEUE))
  end.

Definition OtherPortNode_P vl port msgl : Prop :=
  OtherPort_nat_P vl port /\ OtherPort_direction_P vl port /\ OtherPort_Portt_P vl port msgl.

Fixpoint RLH_OtherPortPtrList otherppl otherpl othermsgll (dportls : DomainPortMod.map) : Prop :=
  match otherppl, otherpl, othermsgll with 
  | nil, nil, nil => dportls = emp
  | portp :: otherppl', port :: otherpl', msgl :: othermsgll'  =>
    exists porth dportls',
      join (sig portp porth) dportls' dportls /\ 
      OtherPortNode_P port porth msgl /\
      RLH_OtherPortPtrList otherppl' otherpl' othermsgll' dportls'
  | _, _, _ => False
  end.

(* 端口根据提供的参数表创建后 direction  mode 等实际上不会改变所以这里使用parameter *)
Parameter OSPortAttrTblDir: (addrval ->  val).
Parameter OSPortAttrTblMode: (addrval ->  val).
Definition OS_Port_V_direction'     (vl:vallist) := nth_val' 4 vl.
Definition OS_Port_V_mode'     (vl:vallist) := nth_val' 5 vl.
Definition RL_PortAttr  (dpptrl : list addrval) dportl : Prop :=
  map OS_Port_V_direction' dportl = map OSPortAttrTblDir dpptrl /\ 
  map OS_Port_V_mode' dportl = map OSPortAttrTblMode dpptrl.

(* domainport -> kernelport *)
Fixpoint R_Kernelport_DomainPort (kportvl: vallist) (kportl: list vallist) (dportl: list vallist) (dpptrl: list addrval): Prop :=
  match dportl, dpptrl with
  | nil, nil => True
  | dport :: dportl', dpptr :: ddptrl' => 
      exists id kportptr kport,
        OS_Port_V_portID dport = Some (Vint32 id) /\
        nth_error kportvl (nat_of_Z (Int.unsigned id)) = Some (Vptr kportptr) /\ 
        nth_error kportl (nat_of_Z (Int.unsigned id)) = Some kport /\
        struct_type_vallist_match OS_K_Port kport /\
        OS_K_Port_V_portID kport = Some (Vint32 id) /\
        OS_K_Port_V_dmport kport = Some (Vptr dpptr) /\
        OS_K_Port_V_coreNum kport = OS_Port_V_coreNum dport /\
        R_Kernelport_DomainPort kportvl kportl dportl' ddptrl'
  | _, _ => False
  end.

Fixpoint nth_addrlist (n : nat) (vl : list(list addrval)) {struct vl} : option (list addrval) :=
  match vl with
  | nil => None
  | v :: vl' => match n with
                | 0%nat => Some v
                | S n' => nth_addrlist n' vl'
                end
  end.

Definition R_KernelPortIDTbl_ChannelIDTbl_kport_Vnull (kportv: val) (kport: vallist): Prop := 
  (kportv = Vnull /\ kport = nil).

Definition R_KernelPortIDTbl_ChannelIDTbl_chan_Vnull (kport: vallist): Prop:=
  OS_K_Port_V_channelID kport = Some (Vint32 ($ DEFAULT_CHANELID)) /\ OS_K_Port_V_channel kport = Some Vnull.

Definition R_KernelPortIDTbl_ChannelIDTbl_scr (kportptr: addrval) (dstpportl: list addrval) (chan: vallist) (d: language.direction) (pptr: addrval) (pcn:nat) (pid:nat) (dportls:DomainPortMod.map): Prop :=
  exists pd pst pin pout pt,
    get dportls pptr = Some (pcn, pd, pid, d, pst, pin, pout, pt) /\
    OS_Channel_V_srcPort chan = Some (Vptr kportptr) /\
  (~ In kportptr dstpportl) /\ 
  OS_Channel_V_srcPortsNum chan = Some (Vint32 ($ 1)) /\
  d = SourceP.

Definition R_KernelPortIDTbl_ChannelIDTbl_dst (kportptr: addrval) (dstkportl: list addrval) (chan: vallist) (d: language.direction) (pptr: addrval) (pcn:nat) (pid:nat) (dportls:DomainPortMod.map): Prop :=
  exists num pd pst pin pout pt nextdst,
    get dportls pptr = Some (pcn, pd, pid, d, pst, pin, pout, pt) /\
    OS_Channel_V_srcPort chan <> Some (Vptr kportptr) /\
    (In kportptr dstkportl) /\ 
    OS_Channel_V_dstPortsNum chan = Some (Vint32 num) /\
    (Int.unsigned num >= 1) /\
    d = DestinationP nextdst.

Definition R_KernelPortIDTbl_ChannelIDTbl_IncoreC (kportptr: addrval) (dstkportl: list addrval) (chan: vallist) (d: language.direction) (pptr: addrval) (pcn:nat) (pid:nat) (dportls1:DomainPortMod.map): Prop :=
  OS_Channel_V_semaphore chan = Some (Vint32 (Int.repr DEFAULT_CHANNLE_SEMAPHROE)) /\ 
  ( R_KernelPortIDTbl_ChannelIDTbl_scr kportptr dstkportl chan d pptr pcn pid dportls1 \/
    R_KernelPortIDTbl_ChannelIDTbl_dst kportptr dstkportl chan d pptr pcn pid dportls1).

Definition R_KernelPortIDTbl_ChannelIDTbl_OutcoreC (kportptr: addrval) (dstkportl: list addrval) (chan: vallist) (d: language.direction) (pptr: addrval) (pcn:nat) (pid:nat) (dportls1:DomainPortMod.map) (dportls2:DomainPortMod.map): Prop :=
  exists csem,
  OS_Channel_V_semaphore chan = Some (Vint32 csem) /\ 
  (Int.eq (csem) ($ DEFAULT_CHANNLE_SEMAPHROE) = false) /\
  ( R_KernelPortIDTbl_ChannelIDTbl_scr kportptr dstkportl chan d pptr pcn pid dportls1\/
    R_KernelPortIDTbl_ChannelIDTbl_dst kportptr dstkportl chan d pptr pcn pid dportls2).

Definition R_KernelPortIDTbl_ChannelIDTbl_chan_Vptr (kportptr: addrval) (kport: vallist) (chanvl: vallist) (chanl: list vallist) (chandstkportll: list (list addrval)) (kportls: KernelPMod.map) (dportls1: DomainPortMod.map) (dportls2: DomainPortMod.map): Prop := 
  exists chanid chanptr chan dstkportl pid pptr pcn kpst d,
    OS_K_Port_V_channelID kport = Some (Vint32 chanid) /\
    OS_K_Port_V_channel kport = Some (Vptr chanptr) /\
    nth_error chanvl (nat_of_Z (Int.unsigned chanid)) = Some (Vptr chanptr) /\
    nth_error chanl (nat_of_Z (Int.unsigned chanid))  = Some chan /\
    nth_error chandstkportll (nat_of_Z (Int.unsigned chanid)) = Some dstkportl /\
    OS_Channel_V_channelID chan = Some (Vint32 chanid) /\
    get kportls kportptr = Some (pid, Some pptr, Some chanptr, pcn, kpst) /\
    ( R_KernelPortIDTbl_ChannelIDTbl_IncoreC kportptr dstkportl chan d pptr pcn pid dportls1 \/
      R_KernelPortIDTbl_ChannelIDTbl_OutcoreC kportptr dstkportl chan d pptr pcn pid dportls1 dportls2  ).

Definition R_KernelPortIDTbl_ChannelIDTbl_kport_Vptr (kportv: val) (kport: vallist) (chanvl: vallist) (chanl: list vallist) (chandstkportll: list (list addrval)) (kportls: KernelPMod.map) (dportls1: DomainPortMod.map) (dportls2: DomainPortMod.map): Prop := 
  exists kportptr,
    kportv = Vptr kportptr /\ struct_type_vallist_match OS_K_Port kport /\
    ( R_KernelPortIDTbl_ChannelIDTbl_chan_Vnull kport \/ 
      R_KernelPortIDTbl_ChannelIDTbl_chan_Vptr kportptr kport chanvl chanl chandstkportll kportls dportls1 dportls2 ).

Fixpoint R_KernelPortIDTbl_ChannelIDTbl (kportvl: vallist) (kportl: list vallist) (chanvl: vallist) (chanl: list vallist) (chandstkportll: list (list addrval)) (kportls: KernelPMod.map) (dportls1: DomainPortMod.map) (dportls2: DomainPortMod.map): Prop :=
  match kportvl, kportl with
  | nil, nil => True
  | kportv :: kportvl' , kport :: kportl' =>
      (
        R_KernelPortIDTbl_ChannelIDTbl_kport_Vnull kportv kport \/
        R_KernelPortIDTbl_ChannelIDTbl_kport_Vptr kportv kport chanvl chanl chandstkportll kportls dportls1 dportls2
      ) /\
      R_KernelPortIDTbl_ChannelIDTbl kportvl' kportl' chanvl chanl chandstkportll kportls dportls1 dportls2
  | _, _ => False
  end.  

Definition nodup_dport (kportls :KernelPMod.map) :=
  forall kpv1 kpv2, kpv1 <> kpv2  ->
    match (get kportls kpv1), (get kportls kpv2) with 
    | (Some (_ , Some pv1, _, _, _)), Some (_ , Some pv2, _, _, _) => pv1 <> pv2
    | _,_=>  True
    end.

(* predicate for timer module *)
Definition HeapInv' :=
  EX cHeapl cHeape cHeapt,
  HCoreHeap cHeapl cHeape cHeapt **
  AOScoreheapl cHeapl ** 
  AOScoreheape cHeape **
  AOScoreheapt cHeapt **
  [|NoDup (map fst (map fst cHeapl))|] **
  [|NoDup (map fst (map fst cHeape))|] **
  [|NoDup (map fst (map fst cHeapt))|].
  
Definition TmrInv' :=
  EX clkrate systmrl utmrl tmrusedl tmrls,
  AOSClkRate (Vint32 clkrate) **
  HClkRate clkrate **
  AOSTMRList_TMRused systmrl utmrl tmrusedl tmrls **
  HTMRList tmrls.
Definition TmrInv := TmrInv' ** HeapInv'.

Definition DynamicRefactorINV ecbls :=
 EX dyncfgp dyncfgl freedynn dynheap, 
 (* Free list *)
 AdynrefaccfgFreeList dyncfgp dyncfgl **
 Hfreedyn dyncfgp freedynn **
 (* dyn_refac_cfg_heap *)
 Adynheap dynheap **
 Hdynheap dynheap **
 [| RLH_dynrefaccfgFreeList_freedyn_P dyncfgl freedynn |] **
 [| is_que ecbls dynrefcmsgQ_addr |] **
 GV dynrefcmsgQ @ (Tptr OS_EVENT) |-> Vptr dynrefcmsgQ_addr
 .

Definition CORESEM_INECB_P ecbls :=
  (forall eid, In eid OSIPCSem_val -> is_sem ecbls eid) /\ 
  (forall eid, In eid OSSendSem_val -> is_sem ecbls eid) /\ 
  (is_sem ecbls OSSemShared_val ).

(* predicate for corecommunication module *)
Definition CoreCommuInv (ecbls :EcbMod.map) := 
  EX sendh recvh ipcbroadl broadvl cptrl memlls ipcgrm ,
  HcurCore curcore **
  HipcsendHeap sendh **
  HipcrecvHeap recvh **
  Hipcsem OSIPCSem_val **
  Hipcsendsem OSSendSem_val **
  [| length OSIPCSem_val  = 8%nat |] **
  [| length OSSendSem_val  = 8%nat |] **
  [| CORESEM_INECB_P ecbls |] **
  Hipcsemshared OSSemShared_val **
  Hipcbroad ipcbroadl **
  Hipcgr ipcgrm **
  AOSIPCMem cptrl memlls**
  [| RLH_IpcSendHeap_P memlls sendh |] **
  [| RLH_IpcRecvHeap_P memlls recvh |] **
  AOSIPCSem IPCSem_ptrl **
  AOSIPCSendSem IPCSendSem_ptrl **
  AOSIPCSemShared OSSemShared_val **
  AOSIPCBroadList broadvl ipcbroadl **
  AOSIPCGRinfo ipcgrm ** 
  DynamicRefactorINV ecbls
.

(* content about RootTaskStk[PARTITION_NUM][2*PTHREAD_STACK_MIN/4] *)

Parameter RootTaskStk_head: addrval.

Definition ARootTaskStk' rtsk_vll :=
GV RootTaskStk @ (Tptr (Tarray Tint32 (nat_of_Z (2 * PTHREAD_STACK_MIN/4 )))) |-> (Vptr RootTaskStk_head) **
Aarray_new RootTaskStk_head (Tarray (Tarray Tint32 (nat_of_Z (2 * PTHREAD_STACK_MIN/4 )))
                                                                               (nat_of_Z (PARTITION_NUM))) rtsk_vll **
[| new_array_type_vallist_match (Tarray Tint32 (nat_of_Z (2 * PTHREAD_STACK_MIN/4 ))) rtsk_vll |] **
[| length rtsk_vll = (nat_of_Z (PARTITION_NUM)) |] **
[| (forall n vl, nth_vallist n rtsk_vll = Some vl -> length vl = (nat_of_Z (2 * PTHREAD_STACK_MIN/4 )))|].

Notation Hrootsk absrtsk := (Aabsdata rootskid (rootsk absrtsk)).

Definition R_RootTaskStk_P (rtsk_vll: list vallist) (absrtsk: list (list int32)):=
rtsk_vll = List.map (List.map Vint32)  absrtsk.

Definition ARootTaskStk rtsk_vll absrtsk:=
ARootTaskStk' rtsk_vll ** Hrootsk absrtsk ** [| R_RootTaskStk_P rtsk_vll absrtsk |].

(* content about MPAX *)
(* csl_xmc_xmpaxh vallist *)
Definition V_mpaxh_bAddr     (vl:vallist) := nth_val 0 vl.
Definition V_mpaxh_segSize   (vl:vallist) := nth_val 1 vl.

(* csl_xmc_xmpaxl vallist *)
Definition V_mpaxl_rAddr     (vl:vallist) := nth_val 0 vl.
Definition V_mpaxl_sr   (vl:vallist) := nth_val 1 vl.
Definition V_mpaxl_sw   (vl:vallist) := nth_val 2 vl.
Definition V_mpaxl_sx   (vl:vallist) := nth_val 3 vl.
Definition V_mpaxl_ur   (vl:vallist) := nth_val 4 vl.
Definition V_mpaxl_uw   (vl:vallist) := nth_val 5 vl.
Definition V_mpaxl_ux   (vl:vallist) := nth_val 6 vl.

(* csl_msmc_sesmpaxh vallist *)
Definition V_sesmpaxh_bAddr     (vl:vallist) := nth_val 0 vl.
Definition V_sesmpaxh_segSz   (vl:vallist) := nth_val 1 vl.

(* csl_msmc_sesmpaxl vallist *)
Definition V_sesmpaxl_rAddr     (vl:vallist) := nth_val 0 vl.
Definition V_sesmpaxl_sr   (vl:vallist) := nth_val 1 vl.
Definition V_sesmpaxl_sw   (vl:vallist) := nth_val 2 vl.
Definition V_sesmpaxl_sx   (vl:vallist) := nth_val 3 vl.
Definition V_sesmpaxl_ur   (vl:vallist) := nth_val 4 vl.
Definition V_sesmpaxl_uw   (vl:vallist) := nth_val 5 vl.
Definition V_sesmpaxl_ux   (vl:vallist) := nth_val 6 vl.

(* csl_msmc_smsmpaxh vallist *)
Definition V_smsmpaxh_bAddr     (vl:vallist) := nth_val 0 vl.
Definition V_smsmpaxh_segSz   (vl:vallist) := nth_val 1 vl.

(* csl_msmc_smsmpaxl vallist *)
Definition V_smsmpaxl_rAddr     (vl:vallist) := nth_val 0 vl.
Definition V_smsmpaxl_sr   (vl:vallist) := nth_val 1 vl.
Definition V_smsmpaxl_sw   (vl:vallist) := nth_val 2 vl.
Definition V_smsmpaxl_sx   (vl:vallist) := nth_val 3 vl.
Definition V_smsmpaxl_ur   (vl:vallist) := nth_val 4 vl.
Definition V_smsmpaxl_uw   (vl:vallist) := nth_val 5 vl.
Definition V_smsmpaxl_ux   (vl:vallist) := nth_val 6 vl.

(* smsmpax *)
Notation Hsms_mpax sms_mpax := (Aabsdata sms_mpaxid (ossms_mpax sms_mpax)).

Definition Asms_mpaxinfo sms_mpaxvl:=
    Aarray sms_mpax_addr (Tarray Tint32 (nat_of_Z 16)) sms_mpaxvl  ** 
    [| array_type_vallist_match Tint32 sms_mpaxvl |].

Definition RH_SMS_Mpax_P (sms_mpax: SmsMod.map) :=
    (forall index, ~ (0 <= Int.unsigned index < 8) -> get sms_mpax index = None) /\ 
    (forall index, (0 <= Int.unsigned index < 8) -> exists mpaxl mpaxh, get sms_mpax index = Some (mpaxl, mpaxh)).

Definition RHL_SMS_Mpax_P sms_mpaxvl (sms_mpax: SmsMod.map) :=
   forall index mpaxl mpaxh,
      get sms_mpax index = Some (mpaxl, mpaxh) -> 
      (nth_val (Z.to_nat ((Int.unsigned index) * 2))  sms_mpaxvl = Some (Vint32 mpaxl) /\
       nth_val (Z.to_nat ((Int.unsigned index) * 2 + 1)) sms_mpaxvl = Some (Vint32 mpaxh)).

Definition RLH_SMS_Mpax_P sms_mpaxvl (sms_mpax: SmsMod.map) :=
  (forall index mpaxl,
      nth_val (Z.to_nat ((Int.unsigned index) * 2))  sms_mpaxvl = Some (Vint32 mpaxl) ->
      exists mpaxh, get sms_mpax index = Some (mpaxl, mpaxh)) /\
  (forall index mpaxh,
      nth_val (Z.to_nat ((Int.unsigned index) * 2 + 1))  sms_mpaxvl = Some (Vint32 mpaxh) ->
      exists mpaxl, get sms_mpax index = Some (mpaxl, mpaxh)).

Definition R_SMS_Mpax_P sms_mpaxvl sms_mpax :=
  RHL_SMS_Mpax_P sms_mpaxvl sms_mpax /\ RLH_SMS_Mpax_P sms_mpaxvl sms_mpax.

Definition ASMSMpax sms_mpaxvl sms_mpax :=
    Asms_mpaxinfo sms_mpaxvl ** Hsms_mpax sms_mpax ** 
    [| RH_SMS_Mpax_P sms_mpax |] ** [| R_SMS_Mpax_P sms_mpaxvl sms_mpax |].

(* sesmpax *)
Notation Hses_mpax ses_mpax := (Aabsdata ses_mpaxid (osses_mpax ses_mpax)).

Definition Ases_mpaxinfo ses_mpaxvl:=
    Aarray ses_mpax_addr (Tarray Tint32 (nat_of_Z 16)) ses_mpaxvl  ** 
    [| array_type_vallist_match Tint32 ses_mpaxvl |].

Definition RH_SES_Mpax_P (ses_mpax: SesMod.map) :=
    (forall index, ~ (0 <= Int.unsigned index < 8) -> get ses_mpax index = None) /\ 
    (forall index, (0 <= Int.unsigned index < 8) -> exists mpaxl mpaxh, get ses_mpax index = Some (mpaxl, mpaxh)).

Definition RHL_SES_Mpax_P ses_mpaxvl (ses_mpax: SesMod.map) :=
   forall index mpaxl mpaxh,
      get ses_mpax index = Some (mpaxl, mpaxh) -> 
      (nth_val (Z.to_nat ((Int.unsigned index) * 2))  ses_mpaxvl = Some (Vint32 mpaxl) /\
       nth_val (Z.to_nat ((Int.unsigned index) * 2 + 1)) ses_mpaxvl = Some (Vint32 mpaxh)).

Definition RLH_SES_Mpax_P ses_mpaxvl (ses_mpax: SesMod.map) :=
  (forall index mpaxl,
      nth_val (Z.to_nat ((Int.unsigned index) * 2))  ses_mpaxvl = Some (Vint32 mpaxl) ->
      exists mpaxh, get ses_mpax index = Some (mpaxl, mpaxh)) /\
  (forall index mpaxh,
      nth_val (Z.to_nat ((Int.unsigned index) * 2 + 1))  ses_mpaxvl = Some (Vint32 mpaxh) ->
      exists mpaxl, get ses_mpax index = Some (mpaxl, mpaxh)).

Definition R_SES_Mpax_P ses_mpaxvl ses_mpax :=
  RHL_SES_Mpax_P ses_mpaxvl ses_mpax /\ RLH_SES_Mpax_P ses_mpaxvl ses_mpax.

Definition ASESMpax ses_mpaxvl (ses_mpax: SesMod.map) :=
    Ases_mpaxinfo ses_mpaxvl ** Hses_mpax ses_mpax ** 
    [| RH_SES_Mpax_P ses_mpax |] ** [| R_SES_Mpax_P ses_mpaxvl ses_mpax |].

(* xmpax *)
Notation Hxmpax xmpax := (Aabsdata xmpaxid (osxmpax xmpax)).

Definition Axmpaxinfo xmpaxvl:=
    Aarray xmpax_addr (Tarray Tint32 (nat_of_Z 32)) xmpaxvl  ** 
    [| array_type_vallist_match Tint32 xmpaxvl |].

Definition RH_XMpax_P (xmpax: XmcMod.map) :=
    (forall index, ~ (0 <= Int.unsigned index < 16) -> get xmpax index = None) /\ 
    (forall index, (0 <= Int.unsigned index < 16) -> exists mpaxl mpaxh, get xmpax index = Some (mpaxl, mpaxh)).

Definition RHL_XMpax_P xmpaxvl (xmpax: XmcMod.map) :=
   forall index mpaxl mpaxh,
      get xmpax index = Some (mpaxl, mpaxh) -> 
      (nth_val (Z.to_nat ((Int.unsigned index) * 2))  xmpaxvl = Some (Vint32 mpaxl) /\
       nth_val (Z.to_nat ((Int.unsigned index) * 2 + 1)) xmpaxvl = Some (Vint32 mpaxh)).

Definition RLH_XMpax_P xmpaxvl (xmpax: XmcMod.map) :=
  (forall index mpaxl,
      nth_val (Z.to_nat ((Int.unsigned index) * 2))  xmpaxvl = Some (Vint32 mpaxl) ->
      exists mpaxh, get xmpax index = Some (mpaxl, mpaxh)) /\
  (forall index mpaxh,
      nth_val (Z.to_nat ((Int.unsigned index) * 2 + 1))  xmpaxvl = Some (Vint32 mpaxh) ->
      exists mpaxl, get xmpax index = Some (mpaxl, mpaxh)).

Definition R_XMpax_P xmpaxvl xmpax :=
  RHL_XMpax_P xmpaxvl xmpax /\ RLH_XMpax_P xmpaxvl xmpax.

Definition AXMpax xmpaxvl xmpax :=
    Axmpaxinfo xmpaxvl ** Hxmpax xmpax ** 
    [| RH_XMpax_P xmpax |] ** [| R_XMpax_P xmpaxvl xmpax |].

Definition AMPAXs :=
EX sms_mpaxvl sms_mpax ses_mpaxvl ses_mpax xmpaxvl xmpax, 
                      ASMSMpax sms_mpaxvl sms_mpax **
                      ASESMpax ses_mpaxvl ses_mpax **
                      AXMpax xmpaxvl xmpax.

Notation Hxmpfar vfar := (Aabsdata xmpfarid (xmpfar vfar)).
Notation Hxmpfsr vfsr := (Aabsdata xmpfsrid (xmpfsr vfsr)).
Notation Hmdma verr := (Aabsdata mdmaerrid (mdmaerr verr)).

Definition AXMPFR :=
EX vfar vfsr,
       PV xmpfar_addr @ Tint32 |-> (Vint32 vfar) ** Hxmpfar vfar **
       PV xmpfsr_addr @ Tint32 |-> (Vint32 vfsr) ** Hxmpfsr vfsr.

Definition AMDMAER :=
EX verr, PV mdmaerr_addr @ Tint32 |-> (Vint32 verr) ** Hmdma verr.

(* content about ucos_conf_t *)

(* dschedule_conf_t vallist *)
Definition V_DSdomain     (vl:vallist) := nth_val 0 vl. 
Definition V_DSlength     (vl:vallist) := nth_val 1 vl. 
 
(* domain_conf_t vallist *)
Definition V_domain              (vl:vallist) := nth_val 0 vl.
Definition V_coreId              (vl:vallist) := nth_val 1 vl.
Definition V_ID                  (vl:vallist) := nth_val 2 vl.
Definition V_binAddress          (vl:vallist) := nth_val 3 vl.
Definition V_RootTaskPrio        (vl:vallist) := nth_val 4 vl.
Definition V_OSPartitionPeriod   (vl:vallist) := nth_val 5 vl.
Definition V_pAddress            (vl:vallist) := nth_val 6 vl.
Definition V_vAddress            (vl:vallist) := nth_val 7 vl.
Definition V_len                 (vl:vallist) := nth_val 8 vl.
Definition V_domsize             (vl:vallist) := nth_val 9 vl.
Definition V_status              (vl:vallist) := nth_val 10 vl.
Definition V_portRdyGrp          (vl:vallist) := nth_val 11 vl.
Definition V_DeviceNum           (vl:vallist) := nth_val 13 vl.

(* capconft vallist *)
Definition V_TaskEn              (vl:vallist) := nth_val 0 vl.
Definition V_PartitionEn         (vl:vallist) := nth_val 1 vl.
Definition V_InterCommEn         (vl:vallist) := nth_val 2 vl.
Definition V_IntraCommSemEn      (vl:vallist) := nth_val 3 vl.
Definition V_IntraCommMutexEn    (vl:vallist) := nth_val 4 vl.
Definition V_IntraCommQueueEn    (vl:vallist) := nth_val 5 vl.

(* areaconft vallist*)
Definition V_ACFpAddress     (vl:vallist) := nth_val 0 vl.
Definition V_ACFvAddress     (vl:vallist) := nth_val 1 vl.
Definition V_area_size       (vl:vallist) := nth_val 2 vl.
Definition V_ACFlen          (vl:vallist) := nth_val 3 vl.

(* cpus vallist *)
Definition V_CPUcore                    (vl:vallist) := nth_val 0 vl.
Definition V_CPUksDomScheduleLength     (vl:vallist) := nth_val 2 vl.
Definition V_CPUksDomainLength          (vl:vallist) := nth_val 3 vl.

(* ucoscontf vallist *)
Definition V_UCFmagicf          (vl:vallist) := nth_val 0 vl. 
Definition V_UCFfileVersion     (vl:vallist) := nth_val 1 vl.
Definition V_UCFcoreNums        (vl:vallist) := nth_val 2 vl.
Definition V_UCFnoPartitions    (vl:vallist) := nth_val 3 vl.
Definition V_UCFnoCommChannels  (vl:vallist) := nth_val 4 vl.
Definition V_UCFnoPorts         (vl:vallist) := nth_val 5 vl.
Definition V_UCFportRdyGrp      (vl:vallist) := nth_val 10 vl. 
Definition V_UCFmagicl          (vl:vallist) := nth_val 13 vl.  

(* channelconf vallist *)
Definition V_CHFcoreType      (vl:vallist) := nth_val 0 vl.
Definition V_CHFID            (vl:vallist) := nth_val 1 vl.
Definition V_CHFchannelType   (vl:vallist) := nth_val 2 vl.
Definition V_CHFsrcportID     (vl:vallist) := nth_val 3 vl.
Definition V_CHFdstGrp        (vl:vallist) := nth_val 4 vl.

(* portconft vallist *)
Definition V_PCFID              (vl:vallist) := nth_val 0 vl.
Definition V_PCFdirection       (vl:vallist) := nth_val 1 vl.
Definition V_PCFport_type       (vl:vallist) := nth_val 2 vl.
Definition V_PCFpartitionID     (vl:vallist) := nth_val 3 vl.
Definition V_PCFchannelID       (vl:vallist) := nth_val 4 vl.

Definition RLH_Dom2idx_P (dom2idx : vallist) (domls : Dom2IdxMod.map) :=
(forall kscurdomian,
        ~ (0 <= Int.unsigned kscurdomian < 8)%Z ->
        get domls kscurdomian = None) /\
( forall kscurdomian index,
        (0 <= Int.unsigned kscurdomian < 8)%Z ->
        nth_val (nat_of_Z (Int.unsigned kscurdomian)) dom2idx = Some (Vint32 index) ->
        get domls kscurdomian = Some index).

Definition RHL_Dom2idx_P (dom2idx : vallist) (domls : Dom2IdxMod.map) :=
(forall kscurdomian,
        get domls kscurdomian = None ->
        ~ (0 <= Int.unsigned kscurdomian < 8)%Z) /\
(forall kscurdomian index,
        get domls kscurdomian = Some index ->
        (0 <= Int.unsigned kscurdomian < 8)%Z /\
        nth_val (nat_of_Z (Int.unsigned kscurdomian)) dom2idx = Some (Vint32 index)).

Notation HDomain2index domls:= (Aabsdata dom2indexid (domindexlist domls)).

Definition Adomain2index' (vl:vallist) :=
  GAarray Domain2Index (Tarray (Tint8) (Z.to_nat DOMAIN_SIZE)) vl **
  [| array_type_vallist_match (Tint8) vl /\ length vl = (Z.to_nat DOMAIN_SIZE) |].

Definition Adomain2index (vl:vallist) (domls : Dom2IdxMod.map) :=
  Adomain2index' vl ** [|RLH_Dom2idx_P vl domls|] ** [|RHL_Dom2idx_P vl domls|] **
  HDomain2index domls.

(* Aucosconf start *)
Definition node_offt (v:val) (vl:vallist) (t:type) :=
  EX b i, [| v = Vptr (b,i) /\ struct_type_vallist_match t vl |] **
           Astruct (b,i) t vl.

Definition deviceIOConfVal := prod vallist vallist.

(* generate the memory assertions for an array of elements with type deviceio_conf_t, such that v represents the initial location of the array *)
Fixpoint ADeviceioTbl' (v: val) (val: list deviceIOConfVal) :=
  match val with
    nil => Aemp
  | (vl, vl') :: val' =>
    EX b i,
         [| v = Vptr (b, i) |] ** 
         Aarray (b, i) (Tarray Tint8 (nat_of_Z 10)) vl' ** 
         [| array_type_vallist_match Tint8 vl' |] **
         node_offt v vl deviceio_conf_t **
         ADeviceioTbl' (Vptr (b, i +ᵢ  $ Z.of_nat (typelen deviceio_conf_t))) val'
  end.

Definition dscheduleConfVal :=  vallist. 

Fixpoint AksDomSchedule' (v: val) (val: list dscheduleConfVal) :=
  match val with
    nil => Aemp
  | (vl) :: val' =>
    node_offt v vl dschedule_conf_t **  
    EX b i, [| v = Vptr (b, i) |] **
         AksDomSchedule' (Vptr (b, i +ᵢ  $ Z.of_nat (typelen dschedule_conf_t))) val' 
  end.

Definition domainConfVal :=
           prod (prod (prod vallist vallist) (list deviceIOConfVal)) vallist.

Definition CPU_ksDomain_prio_Good (dom_vl: vallist) := 
exists prio, V_RootTaskPrio dom_vl = Some (Vint32 prio) /\ 0 <= Int.unsigned prio < 64.

Fixpoint AksDomains' (v: val) (val: list domainConfVal) :=
  match val with
    nil => Aemp
  | (vl, vl', vl'', vl''') :: val' =>
    node_offt v vl domain_conf_t **
    [| CPU_ksDomain_prio_Good vl |] **
    EX b i, [| v = Vptr (b, i) |]  ** 
    (EX lprdytbl,
        Aarray lprdytbl (Tarray Tint8 (nat_of_Z 8)) vl' **
        [| id_addrval (b, i) portRdyTbl domain_conf_t = Some lprdytbl |] **
        [| array_type_vallist_match Tint8 vl' |] ) ** 
    (EX ldeviotbl,
        ADeviceioTbl' (Vptr ldeviotbl) vl'' ** 
        [| id_addrval (b, i) DeviceioTbl domain_conf_t = Some ldeviotbl |] **
        [| length vl'' = 3%nat |]) ** 
    (EX lcapentbl,
        node_offt (Vptr lcapentbl) vl''' cap_conf_t **
        [| id_addrval (b, i) CapEnTbl domain_conf_t = Some lcapentbl |]) ** 
    AksDomains' (Vptr (b, i +ᵢ  $ Z.of_nat (typelen domain_conf_t))) val' 
  end.

Definition channelConfVal := prod vallist vallist. 

Fixpoint AchannelTbl' (v: val) (val: list channelConfVal) :=
  match val with
    nil => Aemp
  | (vl, vl') :: val' =>
    node_offt v vl channel_conf_t **  
    EX b i l,
      [| v = Vptr (b, i) |] ** 
      [| id_addrval (b, i) dstTbl channel_conf_t = Some l |] **
      Aarray l (Tarray Tint8 (nat_of_Z 8)) vl' ** 
      [| array_type_vallist_match Tint8 vl' |] **
    AchannelTbl' (Vptr (b, i +ᵢ  $ Z.of_nat (typelen channel_conf_t))) val' 
  end.

Definition portConfVal := vallist. 
 
Fixpoint AportTbl' (v: val) (val: list portConfVal) :=
  match val with
    nil => Aemp
  | vl :: val' =>
    node_offt v vl port_conf_t **
    EX b i, [| v = Vptr (b, i) |] **
    AportTbl' (Vptr (b, i +ᵢ  $ Z.of_nat (typelen port_conf_t))) val' 
  end.

Definition cpuConfVal :=
           prod (prod (prod vallist vallist) (list dscheduleConfVal))
                (list domainConfVal).

Definition CPU_ksDomScLength_Good (cpu_vl: vallist) :=
  (exists x,
    V_CPUksDomScheduleLength cpu_vl = Some (Vint32 x) /\
     0 <= Int.unsigned x < DSCHEDULE_SIZE).

Definition CPU_ksDomSchdule_dom_Good (dscd_vll: list dscheduleConfVal) :=
  forall i, 0 <= i < DSCHEDULE_SIZE ->
      (exists x dscd_vl ,
      nth_error dscd_vll (nat_of_Z i) = Some dscd_vl  /\
      V_DSdomain dscd_vl = Some (Vint32 x) /\ 0 <= Int.unsigned x < DOMAIN_SIZE).

Definition CPU_ksDomSchdule_dom_NoDup (dscd_vll: list dscheduleConfVal) :=
  forall i j dscd_vl dscd_vl' x y,
      0 <= i < DSCHEDULE_SIZE ->
      0 <= j < DSCHEDULE_SIZE ->
      i <> j ->
      nth_error dscd_vll (nat_of_Z i) = Some dscd_vl ->
      nth_error dscd_vll (nat_of_Z j) = Some dscd_vl' ->
      V_DSdomain dscd_vl = Some (Vint32 x) ->
      V_DSdomain dscd_vl' = Some (Vint32 y) ->
      x <> y.

Definition CPU_ksDomSchdule_Good (dscd_vll: list dscheduleConfVal) :=
  CPU_ksDomSchdule_dom_Good dscd_vll /\
  CPU_ksDomSchdule_dom_NoDup dscd_vll.      

 Definition CPU_ksDomains_dom_Good (dom_vll: list domainConfVal) :=
  forall i, 0 <= i < CORENUM ->
      (exists x dom_vl prdy_vl devio_vll cap_vl,
        nth_error dom_vll (nat_of_Z i) = Some (dom_vl, prdy_vl, devio_vll, cap_vl) /\
        V_domain dom_vl = Some (Vint32 x) /\ 0 <= Int.unsigned x < DOMAIN_SIZE).

Definition CPU_ksDomains_dom_NoDup (dom_vll: list domainConfVal) :=
  forall i j dom_vl prdy_vl devio_vll cap_vl dom_vl' prdy_vl' devio_vll' cap_vl' x y,
      0 <= i < CORENUM ->
      0 <= j < CORENUM ->
      i <> j ->
      nth_error dom_vll (nat_of_Z i) = Some (dom_vl, prdy_vl, devio_vll, cap_vl) ->
      nth_error dom_vll (nat_of_Z j) = Some (dom_vl', prdy_vl', devio_vll', cap_vl') ->
      V_domain dom_vl = Some (Vint32 x) ->
      V_domain dom_vl' = Some (Vint32 y) ->
      x <> y.

Definition CPU_ksDomains_ID_NoDup (dom_vll: list domainConfVal) :=
  forall i j dom_vl prdy_vl devio_vll cap_vl dom_vl' prdy_vl' devio_vll' cap_vl' x y,
      0 <= i < CORENUM ->
      0 <= j < CORENUM ->
      i <> j ->
      nth_error dom_vll (nat_of_Z i) = Some (dom_vl, prdy_vl, devio_vll, cap_vl) ->
      nth_error dom_vll (nat_of_Z j) = Some (dom_vl', prdy_vl', devio_vll', cap_vl') ->
      V_ID dom_vl = Some (Vint32 x) ->
      V_ID dom_vl' = Some (Vint32 y) ->
      x <> y.

Definition CPU_ksDomain_ID_Good (dom_vll: list domainConfVal) :=
  forall i, 0 <= i < CORENUM ->
      (exists x dom_vl prdy_vl devio_vll cap_vl,
        nth_error dom_vll (nat_of_Z i) = Some (dom_vl, prdy_vl, devio_vll, cap_vl) /\
        V_ID dom_vl = Some (Vint32 x) /\ 0 <= Int.unsigned x < PARTITION_NUM).

Definition CPU_ksDomains_Good (dom_vll: list domainConfVal) :=
  CPU_ksDomains_dom_Good dom_vll /\
  CPU_ksDomains_dom_NoDup dom_vll /\
  CPU_ksDomain_ID_Good dom_vll /\
  CPU_ksDomains_ID_NoDup dom_vll.

Fixpoint Acpus' (v: val) (val: list cpuConfVal) :=
  match val with
    nil => Aemp
  | (vl, vl', vl'', vl''') :: val' =>
    node_offt v vl cpu_conf_t **
    [| CPU_ksDomScLength_Good vl |] **
    (EX b i, [| v = Vptr (b, i) |] ** 
             (EX ldomrtbl,
                 [| id_addrval (b, i) domainRdy cpu_conf_t = Some ldomrtbl |] ** 
                 Aarray ldomrtbl (Tarray Tint8 (nat_of_Z 2)) vl' ** 
                 [| array_type_vallist_match Tint8 vl' |]) ** 
             (EX lksdstbl,
                 AksDomSchedule' (Vptr lksdstbl) vl'' ** 
                 [| length vl'' = (nat_of_Z DSCHEDULE_SIZE) |] **
                 [| id_addrval (b, i) cpu_ksDomSchedule cpu_conf_t = Some lksdstbl |] **
                 [| CPU_ksDomSchdule_Good vl'' |]) **
             (EX lksdomtbl,
                 AksDomains' (Vptr lksdomtbl) vl''' ** 
                 [| length vl''' = ( nat_of_Z CORENUM) |] **
                 [| id_addrval (b, i) cpu_ksDomains cpu_conf_t = Some lksdomtbl |] **
                 [| CPU_ksDomains_Good vl'''|])**
             Acpus' (Vptr (b, i +ᵢ  $ Z.of_nat (typelen cpu_conf_t))) val')
  end.

Definition RHL_intrDomainMux_P (intrdomtbl:vallist) (intrdomls:IntrDomMod.map) :=
  (forall i,
          get intrdomls i = None ->
          ~ (0 <= Int.unsigned i < USER_INT_MAX_N)%Z) /\
  (forall i domindex,
          get intrdomls i = Some domindex ->
          ((0 <= Int.unsigned i < USER_INT_MAX_N)%Z /\
            nth_val (nat_of_Z (Int.unsigned i)) intrdomtbl = Some (Vint32 domindex))). 

Definition RHL_deviceId_P (devicetbl:vallist) (devicels:DevIDMod.map) :=
(forall i,
        get devicels i = None ->
        ~ (0 <= Int.unsigned i < 10)%Z) /\
(forall i IDindex,
        get devicels i = Some IDindex ->
        (0 <= Int.unsigned i < 10)%Z /\
        nth_val (nat_of_Z (Int.unsigned i)) devicetbl = Some (Vint32 IDindex)). 


Definition V_startAddr (vl:vallist) := nth_val 1  vl.
Definition V_size  (vl:vallist) := nth_val 2 vl.

Definition RHL_nodedeviceiocf_P  (nodedconftbl:vallist)
                                 (nodedeviceioconf: DcfstartAddr * Dcfdeviceio_size):=
  match nodedeviceioconf with
    |(so,m) =>
     V_startAddr nodedconftbl = Some (Vint32 m) /\  
     V_size      nodedconftbl = Some (Vint32 so) 
  end.

Definition RHL_deviceiocf_P  (dconftbl : deviceIOConfVal)
               (deviceioconf: DcfstartAddr * Dcfdeviceio_size * DevIDMod.map ):=
  match deviceioconf with
    |(nodedeviceioconf,absdevID) =>
     RHL_nodedeviceiocf_P (fst dconftbl) nodedeviceioconf/\
     RHL_deviceId_P       (snd dconftbl) absdevID 
  end.

Fixpoint deviceioArray_P (v: val) (l: list deviceIOConfVal) (devls: DevMod.map) : Prop :=
  match l with
  | nil =>  devls = emp
  | vl :: l' => (exists post devls' deviceioconf v',
                        v = Vint32 post /\
                        v' = Vint32 (Int.add post Int.one) /\
                        joinsig post deviceioconf devls' devls /\
                        RHL_deviceiocf_P vl deviceioconf /\
                        deviceioArray_P v' l' devls')
  end. 

Definition RHL_capconft_P (capcftbl:vallist) (capconftls:CapTblMod.map):=
forall capid tsen pen come comsen commen comqen,
  get capconftls capid = Some (tsen, pen, come, comsen, commen, comqen) ->
     V_TaskEn           capcftbl = Some (Vint32 tsen) /\
     V_PartitionEn      capcftbl = Some (Vint32 pen) /\
     V_InterCommEn      capcftbl = Some (Vint32 come) /\
     V_IntraCommSemEn   capcftbl = Some (Vint32 comsen) /\
     V_IntraCommMutexEn capcftbl = Some (Vint32 commen) /\
     V_IntraCommQueueEn capcftbl = Some (Vint32 comqen).

Definition RHL_portRdyTbl_P (portrdytbl : vallist) (portrdyls : PortRdyTblMod.map) :=
(forall i,
        get portrdyls i = None ->
        ~ (0 <= Int.unsigned i < 8)%Z) /\
(forall i portrdindex,
        get portrdyls i = Some portrdindex ->
        (0 <= Int.unsigned i < 8)%Z /\
        nth_val (nat_of_Z (Int.unsigned i)) portrdytbl = Some (Vint32 portrdindex)). 

Definition RHL_dstTbl_P (dsttbl : vallist) (dstls : DstTblMod.map) :=
(forall i,
        get dstls i = None ->
        ~ (0 <= Int.unsigned i < 8)%Z) /\
(forall i index,
        get dstls i = Some index ->
        (0 <= Int.unsigned i < 8)%Z /\
        nth_val (nat_of_Z (Int.unsigned i)) dsttbl = Some (Vint32 index)). 

Definition RHL_domainRdy_P (domrdytbl : vallist) (domrdyls : DomRdyMod.map) :=
(forall i,
        get domrdyls i = None ->
        ~ (0 <= Int.unsigned i < 2)%Z) /\
(forall i index,
        get domrdyls i = Some index ->
        ((0 <= Int.unsigned i < 2)%Z /\
        nth_val (nat_of_Z (Int.unsigned i)) domrdytbl = Some (Vint32 index))).

Definition RHL_nodedomainconf_p
           (nodedomconftbl : vallist)
           (domconft : Dcfdomain * DcfcoreId * DcfID * DcfbinAddress *
                       DcfRootTaskPrio * DcfOSPartitionPeriod * DcfpAddress *
                       DcfvAddress * Dcflen * Dcfdomain_size * Dcfstatus *
                       DcfportRdyGrp * DcfDeviceNum):=
 match domconft with
   |(dom,cor,id, bin, toot, ospar, pad, vad, le, sz, sta, prg , dnm   ) =>
     V_domain            nodedomconftbl = Some (Vint32 dom)  /\
     V_coreId            nodedomconftbl = Some (Vint32 cor)  /\
     V_ID                nodedomconftbl = Some (Vint32 id)   /\
     V_binAddress        nodedomconftbl = Some (Vint32 bin)  /\
     V_RootTaskPrio      nodedomconftbl = Some (Vint32 toot) /\
     V_OSPartitionPeriod nodedomconftbl = Some (Vint32 ospar)/\
     V_pAddress          nodedomconftbl = Some (Vint32 pad)  /\
     V_vAddress          nodedomconftbl = Some (Vint32 vad)  /\
     V_len               nodedomconftbl = Some (Vint32 le)   /\
     V_domsize           nodedomconftbl = Some (Vint32 sz)   /\
     V_status            nodedomconftbl = Some (Vint32 sta)  /\
     V_portRdyGrp        nodedomconftbl = Some (Vint32 prg)  /\
     V_DeviceNum         nodedomconftbl = Some (Vint32 dnm)
     end.

Definition RHL_domainconf_P
           (domconftbl : domainConfVal)
           (domainconft : Dcfdomain * DcfcoreId * DcfID * DcfbinAddress *
                          DcfRootTaskPrio * DcfOSPartitionPeriod * DcfpAddress *
                          DcfvAddress * Dcflen * Dcfdomain_size * Dcfstatus *
                          DcfportRdyGrp * DcfDeviceNum *
                          PortRdyTblMod.map * DevMod.map * CapTblMod.map) :=
 match domainconft with
    |( nodedomcon, portRdyT, deviceioconf, capconf ) =>
     RHL_nodedomainconf_p  (fst (fst (fst domconftbl)))  nodedomcon /\      
     RHL_portRdyTbl_P      (snd (fst (fst domconftbl))) portRdyT /\
     deviceioArray_P       (Vint32 Int.zero) (snd (fst domconftbl))  deviceioconf /\
     RHL_capconft_P        (snd domconftbl) capconf
     end.

Fixpoint domainconfArray_P
         (v: val) (l: list domainConfVal) (domcfls: DomCTMod.map) : Prop :=
  match l with
  | nil =>  domcfls = emp
  | vl :: l' => (exists domary domcfls' domaincon v',
                        v = Vint32 domary /\
                        v' = Vint32 (Int.add domary Int.one) /\
                        joinsig domary domaincon domcfls' domcfls /\
                        RHL_domainconf_P vl domaincon  /\
                        domainconfArray_P v' l' domcfls')
  end.

Definition RHL_dschedule_P  (dschdtbl : dscheduleConfVal) (dschels:DSdomain * DSlength):=
  match dschels with
  |(dom, len) =>
     V_DSdomain dschdtbl = Some (Vint32 dom) /\  
     V_DSlength dschdtbl = Some (Vint32 len)
  end.

Fixpoint dscheduleconfArray_P (v: val) (l: list dscheduleConfVal)
                              (devcfls: DSchMod.map) : Prop :=
  match l with
  | nil =>  devcfls = emp
  | vl :: l' => (exists dev devcfls' devcon v',
                        v = Vint32 dev /\
                        v' = Vint32 (Int.add dev Int.one) /\
                        joinsig dev devcon devcfls' devcfls /\
                        RHL_dschedule_P vl devcon  /\
                        dscheduleconfArray_P v' l' devcfls')
  end.

Definition RHL_areaconft_P  
           (areacftbl : vallist) 
           (areactls: AcfpAddress * AcfvAddress * area_size * Acflen):=
  match areactls with
  |(t, m, m', m'') =>
     V_ACFpAddress areacftbl = Some (Vint32 t) /\  
     V_ACFvAddress areacftbl = Some (Vint32 m) /\
     V_area_size   areacftbl = Some (Vint32 m') /\
     V_ACFlen      areacftbl = Some (Vint32 m'')
    end.

Definition RHL_nodecpuconft_P
           (nodecpusftbl : vallist)
           (nodecpuconft : CPUcore * CPUksDomScheduleLength * CPUksDomainLength) :=
 match nodecpuconft with
    | (cs, ksd, ksl) =>
     V_CPUcore                nodecpusftbl = Some (Vint32 cs)  /\  
     V_CPUksDomScheduleLength nodecpusftbl = Some (Vint32 ksd) /\ 
     V_CPUksDomainLength      nodecpusftbl = Some (Vint32 ksl)
     end.

Definition RHL_cpuconft_P 
           (cpusftbl : cpuConfVal) 
           (cpuconft : CPUcore * CPUksDomScheduleLength * CPUksDomainLength *
                       DomRdyMod.map * DSchMod.map * DomCTMod.map):=
 match cpuconft with
    | (nodecpuconft, absdomRdy, dscheduleconft, domainconft ) => 
     RHL_nodecpuconft_P   (fst (fst (fst cpusftbl))) nodecpuconft /\
     RHL_domainRdy_P      (snd (fst (fst cpusftbl))) absdomRdy /\ 
     dscheduleconfArray_P (Vint32 Int.zero)(snd (fst cpusftbl)) dscheduleconft /\  
     domainconfArray_P    (Vint32 Int.zero) (snd cpusftbl) domainconft
    end.

Definition ucosConfVal :=
           prod (prod (prod (prod (prod (prod vallist vallist) vallist) (list cpuConfVal)) (list channelConfVal)) vallist) (list portConfVal).

Fixpoint cpusconft_P (v: val) (l: list cpuConfVal) (cpusconfls: CPUsMod.map) : Prop :=
  match l with
  | nil =>  cpusconfls = emp
  | vl :: l' => (exists cpc cpusconfls' cpuscft v',
                        v = Vint32 cpc /\
                        v' = Vint32 (Int.add cpc Int.one) /\
                        joinsig cpc cpuscft cpusconfls' cpusconfls /\
                        RHL_cpuconft_P vl cpuscft /\
                        cpusconft_P v' l' cpusconfls')
  end.

Definition RHL_portconft_P
           (portconftbl : vallist) 
           (portconft: PcfID * Pcfdirection * Pcfport_type *
                       PcfpartitionID * PcfchannelID):=
  match portconft with
    |(did, dir, pty, pid, cid ) => 
     V_PCFID          portconftbl = Some (Vint32 did) /\  
     V_PCFdirection   portconftbl = Some (Vint32 dir) /\
     V_PCFport_type   portconftbl = Some (Vint32 pty) /\
     V_PCFpartitionID portconftbl = Some (Vint32 pid) /\
     V_PCFchannelID   portconftbl = Some (Vint32 cid) 
     end.

Fixpoint portconft_P (v: val) (l: list portConfVal) (portconfls: PortCFMod.map) : Prop :=
  match l with
  | nil =>  portconfls = emp
  | vl :: l' => (exists por portconfls' portcft v',
                        v = Vint32 por /\
                        v' = Vint32 (Int.add por Int.one) /\
                        joinsig por portcft portconfls' portconfls /\
                        RHL_portconft_P vl portcft /\
                        portconft_P v' l' portconfls')
  end.

Definition RHL_nodechannelconf_P 
           (nodechannelconftbl : vallist) 
           (nodechannelconft: ChfcoreType * ChfID * ChfchannelType *
                              ChfsrcportID * ChfdstGrp) :=
 match nodechannelconft with
    |(coty,cfid,chty,src,dstg) =>
     V_CHFcoreType     nodechannelconftbl = Some (Vint32 coty)  /\ 
     V_CHFID           nodechannelconftbl = Some (Vint32 cfid)  /\
     V_CHFchannelType  nodechannelconftbl = Some (Vint32 chty)  /\
     V_CHFsrcportID    nodechannelconftbl = Some (Vint32 src)  /\
     V_CHFdstGrp       nodechannelconftbl = Some (Vint32 dstg)
     end.

Definition RHL_channelconf_P
           (channelconftbl : channelConfVal)
           (channelconft: ChfcoreType * ChfID * ChfchannelType *
                          ChfsrcportID * ChfdstGrp * DstTblMod.map) :=
 match channelconft with
    |(nodechannelconft,absdstTbl) =>
     RHL_nodechannelconf_P (fst channelconftbl) nodechannelconft /\
     RHL_dstTbl_P          (snd channelconftbl) absdstTbl  
     end.

Fixpoint channelconf_P (v: val) (l: list channelConfVal) (chnncfls: ChanCFMod.map) : Prop :=
  match l with
  | nil =>  chnncfls = emp
  | vl :: l' => (exists chf chnncfls' chlconft v',
                        v = Vint32 chf /\
                        v' = Vint32 (Int.add chf Int.one) /\
                        joinsig chf chlconft chnncfls' chnncfls /\
                        RHL_channelconf_P vl chlconft /\
                        channelconf_P v' l' chnncfls')
  end.

Definition RHL_ucnodeosconft_P
           (nodeucosconftbl : vallist)
           (nodeabsucosconf : Ucfmagicf * UcffileVersion * UcfcoreNums *UcfnoPartitions *
            UcfnoCommChannels * UcfnoPorts * UcfportRdyGrp * Ucfmagicl) :=
 match nodeabsucosconf with
    |(mag,nop,cns, npt, ncc, npos,prgp,mcl) =>
     V_UCFmagicf           nodeucosconftbl = Some (Vint32 mag)  /\
     V_UCFfileVersion      nodeucosconftbl = Some (Vint32 nop)  /\
     V_UCFcoreNums         nodeucosconftbl = Some (Vint32 cns)  /\
     V_UCFnoPartitions     nodeucosconftbl = Some (Vint32 npt)  /\
     V_UCFnoCommChannels   nodeucosconftbl = Some (Vint32 ncc)  /\
     V_UCFnoPorts          nodeucosconftbl = Some (Vint32 npos) /\
     V_UCFportRdyGrp       nodeucosconftbl = Some (Vint32 prgp) /\
     V_UCFmagicl           nodeucosconftbl = Some (Vint32 mcl) 
    end.

Definition AIntrDomainMux l vl absintrdom :=
     (EX lintdtbl,
        [| id_addrval l IntrDomainMux ucos_conf_t = Some lintdtbl |] **
        Aarray lintdtbl (Tarray Tint8 (nat_of_Z USER_INT_MAX_N)) vl **
        [| array_type_vallist_match Tint8 vl |] **
        [| RHL_intrDomainMux_P vl absintrdom |]).

Definition AAllArea l vl areaconf := 
    (EX lalltbl,
         node_offt (Vptr lalltbl) vl area_conf_t **
         [| id_addrval l allArea ucos_conf_t = Some lalltbl |] **
         [| RHL_areaconft_P vl areaconf |]).

Fixpoint R_CPUs_DomLen_P (cpuc: list cpuConfVal ) :=
      match cpuc with
      | nil => True
      | (cpu_vl, _, _, _) :: vl' => 
        (exists ksdomlen,
        V_CPUksDomainLength cpu_vl = Some (Vint32 ksdomlen) /\
        1 <= Int.unsigned ksdomlen <= 8 /\
        1 <= Int.unsigned (Int.divu (Int.repr (Z.div OS_USER_MAX_EVENTS 3%Z)) ksdomlen)) /\
        R_CPUs_DomLen_P vl'
      end.

Definition ACPUs l vl cpus_ :=
    (EX lcpustbl,
          Acpus' (Vptr lcpustbl) vl **
          [| length vl = (nat_of_Z CORENUM) |]**
          [| id_addrval l cpus ucos_conf_t = Some lcpustbl |]** 
          [| cpusconft_P (Vint32 Int.zero) vl cpus_ |] **
          [| R_CPUs_DomLen_P vl |]).

Definition AChannelTbl l vl channels := 
    (EX lchantbl, 
         AchannelTbl' (Vptr lchantbl) vl **
         [| length vl = (nat_of_Z CHANNEL_NUMS) |]**
         [| id_addrval l channelTbl ucos_conf_t = Some lchantbl |]**
         [| channelconf_P (Vint32 Int.zero) vl channels |]).

(* Definition APortRdyTbl l vl prtrdytbl :=  *)
(*     (EX lprtbl,  *)
(*           [| id_addrval l portRdyTbl ucos_conf_t = Some lprtbl |] **  *)
(*              Aarray lprtbl (Tarray Tint8 (nat_of_Z 8)) vl **  *)
(*           [| array_type_vallist_match Tint8 vl |]**  *)
(*           [| RHL_portRdyTbl_P vl prtrdytbl |] ).  *)

Definition UCOS_portTbl_partitionID_Good (port_vll : list portConfVal) :=
forall i,
  0 <= i < PORT_NUMS ->
  (exists x port_vl,
        nth_vallist (nat_of_Z i) port_vll = Some port_vl /\
        V_PCFpartitionID port_vl = Some (Vint32 x) /\
        0 <= Int.unsigned x < PARTITION_NUM).

Definition UCOS_portTbl_ID_Good (port_vll : list portConfVal) :=
forall i,
  0 <= i < PORT_NUMS ->
  (exists x port_vl,
        nth_vallist (nat_of_Z i) port_vll = Some port_vl /\
        V_PCFID port_vl = Some (Vint32 x) /\
        0 <= Int.unsigned x < PORT_NUMS).

Definition UCOS_portTbl_partitionID_NoDup (port_vll : list portConfVal) :=
  forall i j port_vl port_vl' x y,
      0 <= i < PORT_NUMS ->
      0 <= j < PORT_NUMS ->
      i <> j ->
      nth_vallist (nat_of_Z i) port_vll = Some port_vl ->
      nth_vallist (nat_of_Z j) port_vll = Some port_vl' ->
      V_PCFpartitionID port_vl = Some (Vint32 x) ->
      V_PCFpartitionID port_vl' = Some (Vint32 y) ->
      x <> y.

Definition UCOS_portTbl_ID_NoDup (port_vll : list portConfVal) :=
  forall i j port_vl port_vl' x y,
      0 <= i < PORT_NUMS ->
      0 <= j < PORT_NUMS ->
      i <> j ->
      nth_vallist (nat_of_Z i) port_vll = Some port_vl ->
      nth_vallist (nat_of_Z j) port_vll = Some port_vl' ->
      V_PCFID port_vl = Some (Vint32 x) ->
      V_PCFID port_vl' = Some (Vint32 y) ->
      x <> y.

Definition UCOS_portTbl_Good (port_vll : list portConfVal) :=
  UCOS_portTbl_partitionID_Good port_vll /\
  UCOS_portTbl_partitionID_NoDup port_vll /\
  UCOS_portTbl_ID_Good port_vll /\
  UCOS_portTbl_ID_NoDup port_vll.

Definition APortTbl l svl prttbl := 
    (EX lportbl,
          AportTbl' (Vptr lportbl) svl ** 
          [| length svl = ( nat_of_Z PORT_NUMS) |]**
          [| id_addrval l portTbl ucos_conf_t = Some lportbl |]**
          [| UCOS_portTbl_Good svl |] **
          [| portconft_P (Vint32 Int.zero) svl prttbl |]).

Definition UCOS_noPorts_Good (ucos_vl : vallist) :=
  exists x, V_UCFnoPorts ucos_vl = Some (Vint32 x) /\
                  0 <= Int.unsigned x < PORT_NUMS.

Definition AucosConf (val: ucosConfVal) (ucosf :absucosconf) :=
  match val with
  | (vl, intrdom, areac, cpuc, channelc, portc, svl) => 
    match ucosf with
    |(mgf, fv, cnum, npart, ncomm, nport, 
      absintrdom, areaconf, cpuconf, channelconf,
      prgrp, prtrdytbl, portconf, mgl) =>
      node (Vptr BOOT_DATA_ADDRESS) vl ucos_conf_t **
      [| UCOS_noPorts_Good vl |] **
      [| RHL_ucnodeosconft_P vl (mgf, fv, cnum, npart, ncomm, nport, prgrp, mgl) |] **
      (EX b i, [| BOOT_DATA_ADDRESS = (b, i) |] **
               AIntrDomainMux (b, i) intrdom absintrdom ** 
               AAllArea (b, i) areac areaconf ** 
               ACPUs (b, i) cpuc cpuconf ** 
               AChannelTbl (b, i) channelc channelconf **  
               (* APortRdyTbl (b, i) vl''''' prtrdytbl **  *)
               APortTbl (b, i) svl portconf) 
     end
  end.

Notation Hucosconf ucosf := (Aabsdata uconfid (absuconf ucosf)).

(* Aucosconf end *)

Notation Hcorepartnum cpn := (Aabsdata cpartnumid (cpartnum cpn)).

Definition ACorepartnum' cpn :=
GV Core_partition_num @ Tint32 |-> (Vint32 cpn) **
[| 1 <= Int.unsigned cpn <= 8 |] **
[| 1 <= Int.unsigned (Int.divu (Int.repr (Z.div OS_USER_MAX_EVENTS 3%Z)) cpn) |].

Definition ACorepartnum cpn :=
ACorepartnum' cpn ** Hcorepartnum cpn.

Definition R_Cpartnum_Dom2idx_P cpn dom2index :=
forall kscurdomian index,
           0 <= Int.unsigned kscurdomian < 8 -> 
          nth_val (nat_of_Z (Int.unsigned kscurdomian)) dom2index = Some (Vint32 index) ->
          Int.unsigned index < Int.unsigned cpn.

Definition APortnumcur :=
EX pnc, GV Port_num_cur @ Tint8 |-> pnc **
[| rule_type_val_match Tint8 pnc = true |].

(* OSAll_Partition_Area vallist *)
Definition V_PApAddr  (vl:vallist) := nth_val 0 vl.
Definition V_PAvAddr  (vl:vallist) := nth_val 1 vl.
Definition V_PAsize       (vl:vallist) := nth_val 2 vl.

Notation HPartArea partarea := (Aabsdata allpartareaid (allpartarea partarea)).

Definition APartArea' partareavl :=
EX l, GV OSAll_Partition_Area @ Tptr area_t |-> (Vptr l) **
          node (Vptr l) partareavl area_t.

Definition R_PartArea_P partareavl (partarea: absarea_t) :=
match partarea with
| (paddr, vaddr, asize) =>
   V_PApAddr partareavl = Some (Vint32 paddr) /\
   V_PAvAddr partareavl = Some (Vint32 vaddr) /\
   V_PAsize partareavl = Some (Vint32 asize)
end.

Definition APartArea partareavl partarea:=
           APartArea' partareavl ** HPartArea partarea **
           [| R_PartArea_P partareavl partarea |] .

(* Definition APartID2Dom partid2domvl :=
EX l, GV partitionID2Domain @ Tptr Tint8 |-> (Vptr l) **
         Aarray l (Tarray Tint8 (nat_of_Z PARTITION_NUM)) partid2domvl **
         [| length partid2domvl = (nat_of_Z PARTITION_NUM) |] **
         [| array_type_vallist_match Tint8 partid2domvl |]. *)

Definition APartID2Dom (partid2domvl:vallist) :=
GAarray partitionID2Domain (Tarray (Tint8) (Z.to_nat PARTITION_NUM)) partid2domvl **
[| array_type_vallist_match (Tint8) partid2domvl /\ length partid2domvl = (Z.to_nat PARTITION_NUM) |].

(* content about domain_t*)

Definition V_Dtdomain                  (vl:vallist)  := nth_val 0 vl.
Definition V_dom_t_ID                    (vl:vallist)  := nth_val 1 vl.
Definition V_DtOSPartitionPeriod  (vl:vallist)  := nth_val 2 vl.
Definition V_dom_t_pAddress     (vl:vallist)  := nth_val 3 vl.
Definition V_dom_t_vAddress     (vl:vallist)  := nth_val 4 vl.
Definition V_dom_t_len                 (vl:vallist)  := nth_val 5 vl.
Definition V_dom_t_size                (vl:vallist)  := nth_val 6 vl.
Definition V_dom_t_status                (vl:vallist)  := nth_val 7 vl.

(* domainIntStatusTbl[USER_INT_MAX_N] *)

Definition RHL_domainIntStatusTbl_P (domIntsta : vallist) (domIntstals : DomIntStaMod.map) :=
  (forall umax,
        get domIntstals umax = None ->
        ~ (0<=Int.unsigned umax < USER_INT_MAX_N)) /\
  (forall umax index,
        get domIntstals umax = Some index ->
        ((0<=Int.unsigned umax < USER_INT_MAX_N) /\
           nth_val (nat_of_Z (Int.unsigned umax)) domIntsta = Some (Vint32 index))). 

Definition Doamin_t_val := prod vallist vallist. 

Definition RHL_nodedom_P
   (nodedomt : vallist) 
  ( nodeabsdomt : DDTdomain * Ddom_t_ID * DOSPartitionPeriod * Ddom_t_pAddress
                         * Ddom_t_vAddress * Ddom_t_len * Ddom_t_size * Ddom_t_status )
  :=
 match nodeabsdomt with
    |(ddom, did, dosp, dpa, dva, dlen, ddsize, dsta  ) =>
     V_Dtdomain                        nodedomt = Some (Vint32 ddom)    /\  
     V_dom_t_ID                         nodedomt = Some (Vint32 did)         /\ 
     V_DtOSPartitionPeriod   nodedomt = Some (Vint32 dosp)      /\ 
     V_dom_t_pAddress          nodedomt = Some (Vint32 dpa)        /\ 
     V_dom_t_vAddress          nodedomt = Some (Vint32 dva)         /\  
     V_dom_t_len                      nodedomt = Some (Vint32 dlen)        /\
     V_dom_t_size                     nodedomt = Some (Vint32 ddsize)   /\
     V_dom_t_status                nodedomt = Some (Vint32 dsta) 
     end.

Definition RHL_domain_P (domt : Doamin_t_val)
(domaint: DDTdomain * Ddom_t_ID * DOSPartitionPeriod * Ddom_t_pAddress
                         * Ddom_t_vAddress * Ddom_t_len * Ddom_t_size * Ddom_t_status * DomIntStaMod.map ) :=
 match domaint with
    |(nodeabsdomt,domainIntStatusTbl) =>
     RHL_nodedom_P (fst domt) nodeabsdomt /\
     RHL_domainIntStatusTbl_P (snd domt) domainIntStatusTbl  
     end.

 Definition KsDomains_dom_Good (dom_vll: list Doamin_t_val) :=
  forall i, 0 <= i < DOMAIN_SIZE ->
      (exists x dom_vl int_vl,
        nth_error dom_vll (nat_of_Z i) = Some (dom_vl, int_vl) /\
        V_Dtdomain dom_vl = Some (Vint32 x) /\ 0 <= Int.unsigned x < DOMAIN_SIZE).

Definition KsDomains_dom_NoDup (dom_vll: list Doamin_t_val) :=
  forall i j dom_vl int_vl dom_vl' int_vl' x y,
      0 <= i < DOMAIN_SIZE ->
      0 <= j < DOMAIN_SIZE ->
      i <> j ->
      nth_error dom_vll (nat_of_Z i) = Some (dom_vl, int_vl) ->
      nth_error dom_vll (nat_of_Z j) = Some (dom_vl', int_vl') ->
      V_Dtdomain dom_vl = Some (Vint32 x) ->
      V_Dtdomain dom_vl' = Some (Vint32 y) ->
      x <> y.

Definition KsDomains_ID_NoDup (dom_vll: list Doamin_t_val) :=
  forall i j dom_vl int_vl dom_vl' int_vl' x y,
      0 <= i < DOMAIN_SIZE ->
      0 <= j < DOMAIN_SIZE ->
      i <> j ->
      nth_error dom_vll (nat_of_Z i) = Some (dom_vl, int_vl) ->
      nth_error dom_vll (nat_of_Z j) = Some (dom_vl', int_vl') ->
      V_dom_t_ID dom_vl = Some (Vint32 x) ->
      V_dom_t_ID dom_vl' = Some (Vint32 y) ->
      x <> y.

Definition KsDomain_ID_Good (dom_vll: list Doamin_t_val) :=
  forall i, 0 <= i < DOMAIN_SIZE ->
      (exists x dom_vl int_vl,
        nth_error dom_vll (nat_of_Z i) = Some (dom_vl, int_vl) /\
        V_dom_t_ID dom_vl = Some (Vint32 x) /\
        0 <= Int.unsigned x < PARTITION_NUM).

Definition KsDomains_Good (dom_vll: list Doamin_t_val) :=
  KsDomains_dom_Good dom_vll /\
  KsDomains_dom_NoDup dom_vll /\
  KsDomain_ID_Good dom_vll /\
  KsDomains_ID_NoDup dom_vll.

Fixpoint AKsDomains' (v: val) (val: list Doamin_t_val) :=
  match val with
    nil => Aemp
  | (vl, vl') :: val' =>
    node_offt v vl domain_t **  
    EX b i l,
      [| v = Vptr (b, i) |] ** 
      [| id_addrval (b, i) domainIntStatusTbl domain_t = Some l |] **
      Aarray l (Tarray Tint8 (nat_of_Z USER_INT_MAX_N)) vl' ** 
      [| array_type_vallist_match Tint8 vl' /\ length vl' = (nat_of_Z USER_INT_MAX_N)|] **
         AKsDomains' (Vptr (b, i +ᵢ  $ Z.of_nat (typelen domain_t))) val' 
  end.

Fixpoint AKsDomains_P (v: val) (l: list Doamin_t_val) (domtls: KsDomsMod.map) 
 : Prop :=
  match l with
  | nil =>  domtls = emp
  | vl :: l' => (
                 exists dom domtls' domT v',
                     v = Vint32 dom /\
                     v' = Vint32 (Int.add dom Int.one) /\
                     joinsig dom domT domtls' domtls /\
                     RHL_domain_P vl domT /\
                     AKsDomains_P v' l' domtls'  )
  end.

Definition AKsDomains vl ksdomls := 
    (EX lksdomains, 
         GV ksDomains @ Tptr domain_t |-> Vptr lksdomains **
         AKsDomains' (Vptr lksdomains) vl **
         [| length vl = (nat_of_Z DOMAIN_SIZE) |]**
         [| KsDomains_Good vl |] **
         [| AKsDomains_P (Vint32 Int.zero) vl ksdomls |]).

 Notation HKsDomains ksdomls:= (Aabsdata ksdomsid (ksdoms  ksdomls)).

(* end of ksDomains *)

Definition AisCoreBoot iscor :=
           GV isCoreBoot @ Tint8 |-> Vint32 iscor**
           [| iscor = Int.zero \/ iscor = Int.one |].

Definition AsystemStck' systmstck :=
           EX l, GV systemStck @ Tptr Tint32 |-> Vptr l **
                 [| array_type_vallist_match Tint32 systmstck /\
                    length systmstck = (nat_of_Z (SYS_STK_SIZE))|] **
                 Aarray l (Tarray Tint32 (Z.to_nat SYS_STK_SIZE)) systmstck.

(* Notation "'REGISTERS'" := (Tint32) (at level 5) : code_scope . *)

Definition AOSSystemSP ossp :=
           GV OSSystemSP @ Tptr Tint32 |-> Vptr ossp.

Notation HKsDSchdidx ksdomscdidx := (Aabsdata ksdschedidxid (ksdschedidx ksdomscdidx)).
Notation HKsDSchdlen ksdomscdlen := (Aabsdata ksdschedlenid (ksdschedlen ksdomscdlen)).
Notation HKsCurDomain kscurd := (Aabsdata kscurdomid (kscurdom kscurd)).
Notation HKsLastDomain kslastd := (Aabsdata kslastdomid (kslastdom kslastd)).
Notation HKsDomainTime ksdomt := (Aabsdata ksdomtimeid (ksdomtime ksdomt)).
Notation HKsDomSchedule ksdscd := (Aabsdata ksdschedid (ksdsched ksdscd)).

Definition AisChangePartion iscp :=
           GV isChangePartion @ Tint8 |-> Vint32 iscp **
           [| iscp = Int.zero \/ iscp = Int.one |].

Definition AKsDSchdidx ksdomscdidx :=
           GV ksDomScheduleIdx @ Tint32 |-> Vint32 ksdomscdidx.

Definition AKsDSchdlen ksdomscdlen :=
           GV ksDomScheduleLength @ Tint8 |-> Vint32 ksdomscdlen **
           [| rule_type_val_match Tint8 (Vint32 ksdomscdlen) = true |].

Definition AKsCurDomain kscurd :=
           GV ksCurDomain @ Tint32 |-> Vint32 kscurd **
            [|(0 <= Int.unsigned kscurd < DOMAIN_SIZE)%Z \/ kscurd =  Int.mone|].

Definition AKsLastDomain kslastd :=
           GV ksLastDomain @ Tint32 |-> Vint32 kslastd.

Definition AKsDomainTime ksdomt :=
           GV ksDomainTime @ Tint32 |-> Vint32 ksdomt.

Definition V_dscd_domain vl := nth_val 0 vl.
Definition V_dscd_length vl := nth_val 1 vl.

Definition R_KsDomSchedule_P ksdsche :=
  forall  td vl dscd_dp ,  
             nth_vallist (nat_of_Z (Int.unsigned td)) ksdsche = Some vl ->
             V_dscd_domain vl = Some (Vint32 dscd_dp) ->
             ( (0 <= Int.unsigned dscd_dp < DOMAIN_SIZE)%Z \/ dscd_dp =  Int.mone) .

Definition AKsDomSchedule' ksdschedule :=
           EX l, GV ksDomSchedule @ Tptr dschedule_t |-> Vptr l **
                 [| new_array_type_vallist_match dschedule_t ksdschedule /\
                    length ksdschedule = (nat_of_Z (DSCHEDULE_SIZE))|] **
                 [| R_KsDomSchedule_P ksdschedule |] **
                 Aarray_new l (Tarray dschedule_t (Z.to_nat DSCHEDULE_SIZE)) ksdschedule.

Definition RLH_KsDomSchedule_P ksdschedule (ksdscd: KsDScdMod.map) :=
(forall i vl dscd_domain dscd_length,
           (0 <= Int.unsigned i < DSCHEDULE_SIZE)%Z ->
           nth_vallist (nat_of_Z (Int.unsigned i)) ksdschedule = Some vl ->
           V_dscd_domain vl = Some (Vint32 dscd_domain) ->
           V_dscd_length vl = Some (Vint32 dscd_length) ->
           KsDScdMod.get ksdscd i = Some (dscd_domain, dscd_length)) /\
(forall i,
           ~(0 <= Int.unsigned i < DSCHEDULE_SIZE)%Z ->
           KsDScdMod.get ksdscd i = None).

Definition RHL_KsDomSchedule_P ksdschedule (ksdscd: KsDScdMod.map) :=
(forall i dscd_domain dscd_length,
           KsDScdMod.get ksdscd i = Some (dscd_domain, dscd_length) ->
           exists vl,
           (0 <= Int.unsigned i < DSCHEDULE_SIZE)%Z /\
           nth_vallist (nat_of_Z (Int.unsigned i)) ksdschedule = Some vl /\
           V_dscd_domain vl = Some (Vint32 dscd_domain) /\
           V_dscd_length vl = Some (Vint32 dscd_length)) /\
(forall i,
           KsDScdMod.get ksdscd i = None ->
           ~(0 <= Int.unsigned i < DSCHEDULE_SIZE)%Z).

Definition AKsDomSchedule ksdschedule ksdscd:=
           AKsDomSchedule' ksdschedule ** HKsDomSchedule ksdscd **
           [| RLH_KsDomSchedule_P ksdschedule ksdscd |] **
           [| RHL_KsDomSchedule_P ksdschedule ksdscd |].


Notation HIntPartMux intpmux := (Aabsdata intpmuxid (intparmux intpmux)).

Definition AIntPartMux' intpmuxvl :=
           EX l, GV IntPartitionMux @ Tptr Tint8 |-> Vptr l **
                 [| array_type_vallist_match Tint8 intpmuxvl /\
                    length intpmuxvl = (nat_of_Z (USER_INT_MAX_N))|] **
                 Aarray l (Tarray Tint8 (Z.to_nat USER_INT_MAX_N)) intpmuxvl.

Definition RLH_IntPartMux_P intpmuxvl (intpmux: IntPMuxMod.map) :=
(forall i v,
           (0 <= Int.unsigned i < USER_INT_MAX_N)%Z ->
           nth_val (nat_of_Z (Int.unsigned i)) intpmuxvl = Some (Vint32 v) ->
           IntPMuxMod.get intpmux i = Some v) /\
(forall i,
           ~(0 <= Int.unsigned i < USER_INT_MAX_N)%Z ->
           IntPMuxMod.get intpmux i = None).

Definition RHL_IntPartMux_P intpmuxvl (intpmux: IntPMuxMod.map) :=
(forall i v,
           IntPMuxMod.get intpmux i = Some v ->
           (0 <= Int.unsigned i < USER_INT_MAX_N)%Z /\
           nth_val (nat_of_Z (Int.unsigned i)) intpmuxvl = Some (Vint32 v)) /\
(forall i,
           IntPMuxMod.get intpmux i = None ->
           ~(0 <= Int.unsigned i < USER_INT_MAX_N)%Z).

Definition AIntPartMux intpmuxvl intpmux:=
           AIntPartMux' intpmuxvl ** HIntPartMux intpmux **
           [| RLH_IntPartMux_P intpmuxvl intpmux |] **
           [| RHL_IntPartMux_P intpmuxvl intpmux |].

Definition AOSPortAttrTbl' portattrls :=
           EX l, GV OSPortAttrTbl @ Tptr port_attr_t |-> Vptr l **
                 [| new_array_type_vallist_match port_attr_t portattrls /\
                    length portattrls = (nat_of_Z (PORT_NUMS))|] **
                 Aarray_new l (Tarray port_attr_t (Z.to_nat PORT_NUMS)) portattrls.

(* predicate for Partition module *)
Definition PartitionInv (ecbls: EcbMod.map):= 
  EX  dportlptr dportl dportmsgll dportls1 dpptrl
      otherppl otherpl othermsgll dportls2 dportls
      kportvl kportl kportls kportfptr kportfl
      chanvl chanl chandstkportll chanls chanfptr chanfl cportlptr cportpl
      rtsk_vll absrtsk ucosf absucosf dom2index absdom2index ksdomscdidx ksdomscdlen kscurd kslastd
      ksdomt ksdschedule ksdscd iscp intpmuxvl intpmux ksdom absks iscb systm ossp
      cpn partareavl partarea partid2domvl portattrls,
        AOSDomainPortPtrList dportlptr dportl dportmsgll **
        Hdomainportl dportls ** 
        [| join dportls1 dportls2 dportls |] **
        [| RL_PortAttr dpptrl dportl |] **
        [| RLH_PortPtrINecb dportlptr dportl dpptrl ecbls |] **
        [| RLH_Domainportl dportlptr dportl dportmsgll dportls1|] **
        AOSKernelPortIDTbl kportvl kportl **
        Hkernelport kportls **
        [| RLH_Kernelport kportvl kportl kportls|] ** 
        AOSChannelIDTbl chanvl chanl chandstkportll**
        Hchannell chanls **
        [| RLH_Channel otherppl chanvl chanl chandstkportll chanls kportls dportls1 dportls2 |] **
        AOSKernelPortFreeList kportfptr kportfl **
        AOSChannelFreeList chanfptr chanfl **
        [| R_Kernelport_DomainPort kportvl kportl dportl dpptrl |] **
        [| R_KernelPortIDTbl_ChannelIDTbl kportvl kportl chanvl chanl chandstkportll kportls dportls1 dportls2 |] **
        OtherPortPtrList otherppl otherpl othermsgll **
        [| RLH_OtherPortPtrList otherppl otherpl othermsgll dportls2 |] **
        [| nodup_dport kportls |] **
        Hcoreportpl cportpl **
        AOSCorePortPtrList cportlptr cportpl dportls1 **
        ARootTaskStk rtsk_vll absrtsk **
        AMPAXs ** AXMPFR ** AMDMAER **
        AucosConf ucosf absucosf ** Hucosconf absucosf **
        Adomain2index dom2index absdom2index **
        AKsDSchdidx ksdomscdidx ** HKsDSchdidx ksdomscdidx **
        AKsDSchdlen ksdomscdlen ** HKsDSchdlen ksdomscdlen **
        AKsCurDomain kscurd ** HKsCurDomain kscurd **
        AKsLastDomain kslastd ** HKsLastDomain kslastd **
        AKsDomainTime ksdomt ** HKsDomainTime ksdomt **
        AKsDomSchedule ksdschedule ksdscd **
        AisChangePartion iscp **
        AIntPartMux intpmuxvl intpmux **
        AKsDomains ksdom absks ** HKsDomains absks **
        AisCoreBoot iscb **
        AsystemStck' systm **
        AOSSystemSP ossp **
        ACorepartnum cpn ** [| R_Cpartnum_Dom2idx_P cpn dom2index |] **
        APortnumcur **
        APartArea partareavl partarea **
        APartID2Dom partid2domvl ** AOSPortAttrTbl' portattrls.

(* Predicate for Capability module *)
Fixpoint nth_cspace_val (n: nat) (vl: list cspace_val_type) {struct vl}: option cspace_val_type :=
    match vl with
          | nil  => None
          | v :: vl'=> match n with
                  | 0%nat => Some v
                  | S n' => nth_cspace_val n' vl'
                end
  end.

(* Specifies that the map cspacels must contain the same information as
   the pair of lists plv and lv.

   plv and lv must have the same length. Each pair of corresponding elements
   must have the form (pv, Vptr v'), where get cspacels v' = Some pv. 
*)
Fixpoint RLH_cspace_pris_P (plv: list priority) (lv: list val) (cspacels: CSpaceptr2prioMod.map): Prop:=
  match plv, lv with
  | nil, nil => True
  | pv :: plv', v :: lv' =>
    match v with
    | Vptr v' =>
        get cspacels v' = Some pv /\ RLH_cspace_pris_P plv' lv' cspacels
    | _ => False
    end
  | _, _ => False
  end.

(* OSCSpaceObjectPointer is an array of length 64, with value type int32.

   TODO: add constraints that each elemen255t is in a certain range?
*)


Definition  objectpointer vl:=
  forall i x,
  (0 <= i < (length vl))%nat ->
  nth_val i vl = Some (Vint32 x) ->
  ((Z.to_nat OBJ_POSITION) <= Z.to_nat(Int.unsigned x) <= 255 )%nat.


Definition AOSCSpaceObjectPointer vl :=
  GAarray OSCSpaceObjectPointer (Tarray Tint32 64) vl 
  ** [|array_type_vallist_match Tint32 vl /\ length vl = 64%nat
  /\objectpointer vl|].

(* CapParent is an array of length 64, with value type int32.

   CapParent specifies the parent of each task in the capability
   information.

   TODO: specify the range of values of CapParent, also that it agrees with
   information in childs.
*)
Definition capparent vl :=
  forall i x,
  (0 <= i < (length vl))%nat ->
  nth_val i vl = Some (Vint32 x) ->
  (0 <= Z.to_nat(Int.unsigned x) <64 )%nat.


Definition AOSCSpaceCapParent vl:=
  GAarray CapParent (Tarray Tint32 64) vl
  ** [|array_type_vallist_match Tint32 vl /\ length vl = 64%nat
   /\ capparent vl|].

(* Global pointers for capability information.

   OSCSpaceCur: pointer to the current CSpace - not used!
   OSCSpaceList: pointer to the doubly-linked list of CSpaces - not used!
   OSCSpaceFreeList: pointer to the list of free CSpaces.
*)

(*The cspace free list*)
Definition CSpaceGVars :=
  EX p1, GV OSCSpaceCur @(Tptr CSPACE) |-> p1 **
  EX p2, GV OSCSpaceList @(Tptr CSPACE) |-> p2 **
  EX p, GV OSCSpaceFreeList @(Tptr CSPACE) |-> p.

(* Relationship between list of cspace_val_type and CSpaceMod.map
*)
Definition  RLH_cspace_parents_P prio parent pl :=
    nth_val' (nat_of_Z(Int.unsigned prio)) pl = Vint32 parent. 


Definition RLH_cspace_slots_P (vl: list cspace_val_type) (acspace: CSpaceMod.map)
                              (cspacels: CSpaceptr2prioMod.map) (pl: list val) : Prop :=
  (forall prio cspace,
    nth_cspace_val (nat_of_Z (Int.unsigned prio)) vl = Some cspace ->
    match cspace with
    | ((_, slots), _, lv, _, _) =>
       exists plv parent, (get acspace prio = Some (slots, plv, parent)) /\ RLH_cspace_pris_P plv lv cspacels
       /\RLH_cspace_parents_P prio parent pl
    end) /\
  (forall prio slots plv parent,
    get acspace prio = Some (slots, plv, parent) ->
    exists lv a b c d, (nth_cspace_val (nat_of_Z (Int.unsigned prio)) vl = Some ((a, slots), b, lv, c, d) /\
    RLH_cspace_pris_P plv lv cspacels /\ RLH_cspace_parents_P prio parent pl)).

Fixpoint Child_In_ChildList (x: int) (lv: list val) : Prop :=
  match lv with
    | nil => False
    | (Vint32 a)::lv' => if Int.eq x a then True else (Child_In_ChildList x lv')
    | _ => False
  end. 

Definition get_Childlist (cspace: cspace_val_type) :=
  match cspace with
    (a, b, c, d, e) => c
  end. 

(*If CapParent[i] = a and a is not -1, then i is in the childlist of a *)
Definition RL_Cap_Parent_Child (pl: list val) (vl: list cspace_val_type) : Prop :=
  (forall prio x cspace,
    nth_val (nat_of_Z (Int.unsigned prio)) pl = Some (Vint32 x) ->
    ((Int.eq x (Int.mone)) = false) ->  
    nth_cspace_val (nat_of_Z (Int.unsigned x)) vl = Some cspace ->
    Child_In_ChildList x (get_Childlist cspace)) /\
  (forall prio cspace,
    nth_cspace_val (nat_of_Z (Int.unsigned prio)) vl = Some cspace ->
    forall x, (Child_In_ChildList x (get_Childlist cspace) -> 
                nth_val (nat_of_Z (Int.unsigned x)) pl = Some (Vint32 prio))
  ).

Definition RLH_CapParent (pl: list val) (acspace: CSpaceMod.map) : Prop :=
  (forall prio x,
   nth_val (nat_of_Z (Int.unsigned prio)) pl = Some (Vint32 x) -> 
   exists slots plv, (get acspace prio = Some (slots, plv, x))) /\
  (forall prio slots plv parent,
   get acspace prio = Some (slots, plv, parent) ->
   nth_val (nat_of_Z (Int.unsigned prio)) pl = Some (Vint32 parent)  
  ).

Definition taskPrioProp (vl: list cspace_val_type):=
  forall prio a b c d prio',
  0 <= Int.unsigned prio < 64 ->  
  nth_cspace_val (nat_of_Z (Int.unsigned prio)) vl = Some(a, b, c, d, prio') ->
  prio = prio'.
(* Obtain the list of priority of child nodes of task i *)

Definition int32_inj (v: option int32):=
  match v with
  | Some v' => v' 
  | None => Int.zero
  end.


Fixpoint nth_cspace n (vl: list cspace_val_type):=
    match vl with 
    | nil => None
    | v :: vl' =>
        match n with 
        |0%nat => Some v 
        |S n' => nth_cspace n' vl' 
        end
    end.
Fixpoint reverse_map (map: CSpaceptr2prioMod.map) (pointvl: list val):=
  match pointvl with 
  |(Vptr v) :: pointvl' => int32_inj(get map v) :: reverse_map map pointvl'
  | _:: pointvl' => reverse_map map pointvl'  
  | nil => nil 
  end.

Definition child (i: int32) (ls: list cspace_val_type) (map: CSpaceptr2prioMod.map) :=
  match (nth_cspace (Z.to_nat (Int.unsigned i)) ls) with
  | Some (cnode, child_num, cspace, next, index)
    => reverse_map map cspace
  | None => nil 
  end.

Fixpoint contains (ls: list int32) (v: int32):=
  match ls with 
  |nil => false
  |h::ls' => 
    if Int.eq h v
    then true 
    else contains ls' v
  end.
      
Fixpoint intersection l1 l2:=
  match l1 with 
  | nil => false 
  | v1::l1' => (contains l2 v1)||(intersection l1' l2)
  end.  




(*child函数是输入cpsace的下标，求出其children的下标集合
contains是用来判断一个集合是否包含x
intersection是用来判断两个集合是否有交集*)

Inductive wellform_descendents:
  int32 -> list int32 -> list cspace_val_type -> CSpaceptr2prioMod.map -> Prop :=
| wellform_descendents_neqnull:
  forall map node ls descs, 
    wellform_descendents_list (child node ls map) descs ls map ->  
    (contains descs node = false) ->
    wellform_descendents node (node :: descs) ls map
with
  wellform_descendents_list:
  list int32 -> list int32 -> list cspace_val_type -> CSpaceptr2prioMod.map -> Prop :=
| wellform_descendents_list_leaf:
  forall ls map,
    wellform_descendents_list nil nil ls map
|wellform_descendents_list_cons:
  forall node desc1 rest desc2 ls map, 
    wellform_descendents node desc1 ls map-> 
    wellform_descendents_list rest desc2 ls map -> 
    intersection desc1 desc2 = false -> 
    wellform_descendents_list (node :: rest) (desc1 ++ desc2) ls map.

Definition Capability_wellform_descendents vl cspacels:=
  forall destTask_Prio ,
  0 <= Int.unsigned destTask_Prio < 64 ->
  exists childlist, wellform_descendents destTask_Prio childlist vl cspacels.


Definition CapabilityInv (acspace: CSpaceMod.map):=
  EX (l: addrval) (ptrvl: list val)
     (vl: list cspace_val_type) (cspacels: CSpaceptr2prioMod.map) (pl: list val) (objvl: list val),
    AOSCSpacePrioTbl l ptrvl vl cspacels **
    AOSCSpaceObjectPointer objvl ** 
    AOSCSpaceCapParent pl **
    [|RLH_CapParent pl acspace|] **
    [|RL_Cap_Parent_Child pl vl|] **
    CSpaceGVars **
    [| ptrvl_to_cspace_to_ptrvl ptrvl cspacels |] **
    [| RLH_cspace_slots_P vl acspace cspacels pl|] **
    [|CSPACEList_P ptrvl 0%nat  cspacels|] **
    Hcapspace acspace **
    [|taskPrioProp vl|] **
    [|Capability_wellform_descendents vl cspacels|].

Definition APthreadAttr pattrb :=
    HPthreadAttr pattrb.


Definition OldOSInvWL' ct lg:=
  EX ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp ecbls (tcbls:TcbMod.map) t vhold ptfree lfree ptls pattrb acspace
    scapl mcapl qcapl,
                   AOSMapTbl ** AOSUnMapTbl ** AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold ** 
                   AOSTCBList_old p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
                   AOSTCBFreeList ptfree lfree**
                   AOSRdyTblGrp rtbl rgrp **
                   AOSTime (Vint32 t) **(* tcblist & rdy table *)               


                   HTCBList tcbls ** HTime t ** HCurTCB ct **  AGVars **
                   APthreadAttr pattrb **
                   EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
                   
                   [| RH_TCBList_ECBList_P ecbls tcbls ct|] **
                   [| RH_CurTCB ct tcbls|] **
                   A_isr_is_prop **
                   IntInv **
                   TmrInv **
                   CoreCommuInv ecbls **
                   PartitionInv ecbls **
                   CapabilityInv acspace**
                   tcbdllflag p1 (tcbl1 ++ (tcbcur::tcbl2)) ** LINV OSLInv ct lg. 
                  
Definition OldOSInvWL ct lg:=
  EX ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp ecbls (tcbls:TcbMod.map) t vhold ptfree lfree ptls pattrb acspace
    scapl mcapl qcapl,
                   AOSMapTbl ** AOSUnMapTbl ** AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold ** 
                   AOSTCBList p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
                   AOSTCBFreeList ptfree lfree**
                   AOSRdyTblGrp rtbl rgrp ** AOSTime (Vint32 t) **(* tcblist & rdy table *)
                   HTCBList tcbls ** HTime t ** HCurTCB ct **  AGVars **
                   APthreadAttr pattrb **
                   EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
                   
                   [| RH_TCBList_ECBList_P ecbls tcbls ct|] **
                   [| RH_CurTCB ct tcbls|] **
                   A_isr_is_prop **
                   IntInv **
                   TmrInv **
                   CoreCommuInv ecbls **
                   PartitionInv ecbls**
                   CapabilityInv acspace**
                   tcbdllflag p1 (tcbl1 ++ (tcbcur::tcbl2)) ** p_local OSLInv ct lg.
                                 
(*                   PV (get_flag_addr ct) @ Tint8 |-r-> (V$ 1).
                   
*)
                   
Definition OSInv :=
  EX ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp ecbls tcbls t ct vhold ptfree lfree ptls pattrb acspace 
    scapl mcapl qcapl,
                   AOSMapTbl ** AOSUnMapTbl ** AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold ** 
                   AOSTCBList' p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls ptfree **
                   AOSTCBFreeList' ptfree lfree ct tcbls**
                   AOSRdyTblGrp rtbl rgrp ** AOSTime (Vint32 t) **(* tcblist & rdy table *)
                   HTCBList tcbls ** HTime t ** HCurTCB ct ** AGVars **
                   APthreadAttr pattrb **
                   EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
                   
                   [| RH_TCBList_ECBList_P ecbls tcbls ct|] **
                   (* [| RH_CurTCB ct tcbls|] ** *)
                   A_isr_is_prop **
                   IntInv **
                   TmrInv **
                   CoreCommuInv ecbls **
                   PartitionInv ecbls**
                   CapabilityInv acspace.
               
Definition atoy_inv':=(EX i, GV OSIntToyCount@ (Tint32) |-> Vint32 i) .
Definition atoy_inv:= atoy_inv'** A_isr_is_prop.

Definition aemp_isr_is:= Aemp ** A_isr_is_prop.

Fixpoint eq_dllflag l1 l2:=
  match l1,l2 with
    | nil,nil => True
    | vl1::l1',vl2::l2' =>
      V_OSTCBNext vl1 = V_OSTCBNext vl2 /\ V_OSTCBflag vl1 = V_OSTCBflag vl2 /\ eq_dllflag l1' l2'
    | _,_ => False
  end.

Lemma eq_dllflag_refl: forall l, eq_dllflag l l.
Proof.
  induction l.
  simpl;auto.
  simpl.
  splits;auto.
Qed.
Lemma tcbdllflag_hold_middle:
  forall l1 l2 node node',
    eq_dllflag (node::nil) (node'::nil) -> eq_dllflag (l1++node::l2) (l1++node'::l2).
Proof.
  induction l1.
  intros.
  simpl in H.
  simpl.
  destruct H.
  destruct H0.
  splits;auto.
  apply eq_dllflag_refl.
  intros.
  simpl.
  splits;auto.
Qed.

Lemma tcbdllflag_hold:
  forall l1 P head l2,
    eq_dllflag l1 l2 ->
    tcbdllflag head l1  ** P ==> tcbdllflag head l2  ** P.
Proof.
  unfold tcbdllflag.
  inductions l1.
  intros.
  simpl in H.
  unfold tcbdllflag in *.
  destruct l2; tryfalse.
  auto.
  intros.
  destruct l2.
  simpl in H; tryfalse.
  unfold dllsegflag in *; fold dllsegflag in *.
  simpl in H.
  simpljoin.
  sep normal in H0.
  sep normal.
  sep destruct H0.
  exists x x0.
  sep cancel 1%nat 1%nat.
  sep split in H0.
  sep split; auto.
  sep cancel 1%nat 1%nat.
  eapply IHl1; eauto.
  rewrite H in H3.
  auto.
Qed.

Lemma disj_split:
  forall s p q r, 
    (s |= (p \\// q) ** r <-> s |= (p ** r) \\// (q ** r)).
Proof.
  split.
  intros.
  simpl in H.
  simpljoin.
  destruct H3.
  left.
  do 6 eexists.
  splits; eauto.
  right.
  do 6 eexists.
  splits; eauto.
  intros.
  destruct H.
  sep cancel 2%nat 2%nat.
  left; auto.
  sep cancel 2%nat 2%nat.
  right; auto.
Qed.
(* ** ac: Locate PV_combine_ro_frm. *)
Import sep_combine_lemmas.

Lemma read_only_merge_all:
  forall s x t v1 v2 P,
    rule_type_val_match t v1 = true->
    rule_type_val_match t v2 = true->
    s |= (PV x @  t |-r->  v1) **
      (PV x @  t |-r->  v2) ** P  ->
    s |= PV x @  t |-> v1 ** P /\ v1 = v2.                                       
Proof.
  (* ** ac: Print rule_type_val_match. *)
  intros.
  (* ** ac: Check PV_combine_ro_frm. *)
  eapply PV_combine_ro_frm in H1.
  sep split in H1.
  split.
  auto.
  lets Hx : rule_type_val_match_encode_val_eq H H0 H2.
  auto.
Qed.

Lemma rule_type_val_match_encode_val_length_eq :
  forall t v1 v2 vl1 vl2,
    rule_type_val_match t v1 = true ->
    rule_type_val_match t v2 = true ->
    encode_val t v1 = vl1 ->
    encode_val t v2 = vl2 ->
    length vl1 = length vl2.
Proof.
  intros.
  destruct t, v1, v2;
    simpl in H, H0; tryfalse;
    simpl in H1, H2; try(destruct a); try (destruct a0); substs; auto.
Qed.

Lemma read_only_merge_vptr:
  forall s x t1 t2 v1 v2 P,
    s |= (GV x @ Tptr t1 |-r-> Vptr v1) **
      (GV x @ Tptr t2 |-r-> Vptr v2) ** P  ->
    s |= GV x @ Tptr t1 |-> Vptr v1 ** P /\ v1 = v2.                                       
Proof.

  intros.
  destruct_s s.
  simpl in H.
  simpljoin.
  unfold emposabst in *; substs.
  rewrite H13 in H22.
  inverts H22.

  unfold mapstoval in H14, H23.
  simpljoin.

  assert(length (encode_val (Tptr t1) (Vptr v2)) = length (encode_val (Tptr t1) (Vptr v1))).
  {
    eapply rule_type_val_match_encode_val_length_eq; eauto.
    simpl; auto.
    simpl; auto.
  }
  (* ** ac: Print ptomvallist. *)
  (* ** ac: Print encode_val. *)
  assert(x21 = x6).
  geat.
  assert(x14 = x0).
  geat.
  assert(x4 = o).
  geat.
  assert(x10 = x4).
  geat.
  substs.

  assert(exists xx, join x0 x6 xx).
  clear - H0 H5.
  geat.
  destruct H1.

  symmetry in H.
  (* ** ac: Locate ptomvallistr_join_vl_eq. *)
  (* ** ac: SearchAbout ptomvallist. *)
Lemma ptomvallist_false_sub_vl_eq :
  forall vl1 vl2 l m1 m2 m,
    ptomvallist l false vl1 m1 ->
    ptomvallist l false vl2 m2 ->
    length vl1 = length vl2 ->
    Maps.sub m1 m -> Maps.sub m2 m ->
    vl1 = vl2.
Proof.
  inductions vl1; intros.
  destruct vl2; auto.
  simpl in H1; inversion H1.
  
  destruct vl2.
  simpl in H1; inversion H1.

  simpl in H1; inverts H1.
  simpl in H; destruct l.

  do 3 destruct H; destruct H1.
  simpl in H0; do 3 destruct H0; destruct H6.

  unfold ptomval in H1, H6; substs.
  assert(a = m0).
  unfolds in H2; destruct H2.
  unfolds in H3; destruct H3.
  lets Hx1: HalfPermMap.map_join_assoc H H1.
  lets Hx2: HalfPermMap.map_join_assoc H0 H2.
  simpljoin.

  Require Import mem_join_lemmas.
  lets Hx: mem_join_sig_eq H6 H3; auto.
  substs.
  assert(vl1 = vl2).
  assert(Maps.sub x0 m).
  unfold Maps.sub.
  unfold Maps.sub in H2.
  geat.
  assert(Maps.sub x2 m).
  unfold Maps.sub.
  unfold Maps.sub in H3.
  geat.
  apply IHvl1 with (m1:=x0) (m2:=x2) (m:=m) (l:=(b,o+1)); auto.
  substs; auto.
Qed.
  
  assert ((encode_val (Tptr t1) (Vptr v1)) = (encode_val (Tptr t1) (Vptr v2))).
  {
    eapply ptomvallist_false_sub_vl_eq; eauto.
    instantiate (1:= x2).
    unfold Maps.sub.
    exists x6.
    auto.
    unfold Maps.sub.
    clear - H1.
    geat.
  } 

  assert(Vptr v1 = Vptr v2).
  {
    eapply rule_type_val_match_encode_val_eq; eauto.
    simpl; auto.
    simpl; auto.
  }
  inverts H8.

  simpl.
  split; auto.
  exists x2 x7 m empabst o o.
  splits; auto.
  jeauto2.
  clear - H5 H0 H1.
  geat.
  do 7 eexists.
  splits; auto.
  Focus 3.
  eexists.
  splits; auto.
  eauto.
  unfolds; auto.
  jeauto2.
  jeauto2.
  (* ** ac: Check os_inv.ptomvallistr_ptomvallist. *)
  unfolds.
  eexists.
  split; auto.
  eapply ptomvallistr_ptomvallist.
  exact H4.
  exact H3.
  eauto.
  unfolds; auto.
Qed.

Lemma tcbfreelist_disj_tcblist:
  forall pfree fls  ct x y l s P,
    s|= AOSTCBFreeList pfree fls ** tcbdllseg (Vptr ct) x y Vnull l ** P
    -> pfree <> (Vptr ct).
Proof.
  intros.
  intro; substs.

  destruct l.
  unfold tcbdllseg in H.
  simpl dllseg in H; sep split in H; tryfalse.

  destruct fls.
  unfold AOSTCBFreeList in H.
  unfold assertion.sll in H.
  simpl sllseg in H.
  sep split in H; tryfalse.

  unfold AOSTCBFreeList in H.
  unfold assertion.sll in H.
  unfold tcbdllseg in H.
  unfold sllseg in H; fold sllseg in H.
  unfold dllseg in H; fold dllseg in H.
  sep normal in H.
  do 2 destruct H.
  sep split in H.
  sep lifts (1::3::nil)%nat in H.
  apply node_OS_TCB_dup_false in H; tryfalse.
Qed.

Lemma flag_merege_false :
  forall a P s,
    s|= PV a @ Tint8 |-r-> (V$ 1)
     ** PV a @ Tint8 |-r-> (V$ 0) ** P -> False.
Proof.
  intros.
  destruct_s s.
  simpl in H.
  repeat (let a:= fresh in destruct H as [a H]).
  destruct H10; unfolds in H22.
  destruct H21; unfolds in H23.
  substs.
  unfolds in H10; destruct H10; destruct H2.
  unfolds in H21; destruct H21; destruct H5.
  apply map_join_comm in H7.
  apply map_join_comm in H18.

  pose proof map_join_assoc H18 H7.
  do 2 destruct H8.
  substs.
  simpl in H3.
  simpl in H6.
  destruct (addrval_to_addr a).
  destruct H6; destruct H2; destruct H2; destruct H5.
  destruct H3; destruct H3; destruct H3; destruct H13.
  substs.
  pose proof map_join_emp x.
  pose proof map_join_deter H2 H6; substs.
  pose proof map_join_emp x2.
  pose proof map_join_deter H3 H11; substs.
  clear H6 H18 H2 H11 H7 H3.
  
  lets Hx: ptomvalr_join_eq H5 H13 H10.
  inverts Hx.
Qed.

Lemma read_only_merge_vptreq:
  forall s x t v P,
      s |= (GV x @ Tptr t |-r-> Vptr v) **
        (GV x @ Tptr t |-r-> Vptr v) ** P  <->
      s |= GV x @ Tptr t |-> Vptr v ** P .                                       
Proof.
  intros.
  split; intros.
  lets Hx: read_only_merge_vptr H; destruct Hx; auto.
  apply read_only_split_vptr; auto.
Qed.

Require Import seplog_trm_tacs.

(* lg' contains logical values for the ghost variables *) 
Lemma inv_change':
  forall P t lg',
    OSInv ** p_local OSLInv t (logic_val (V$1) :: lg') ** P <==> OldOSInvWL' t (logic_val (V$1) :: lg')  ** P. 
Proof.
  intros.
  split.
  intros.
  sep cancel 3%nat 2%nat.
  unfold OldOSInvWL'.
  unfold OSInv in H.
  sep normal in H.
  sep destruct H.
  (* sep lift 8%nat in H. *)
  sep_lifts_trms_in H AOSTCBList'.
  unfold AOSTCBList' in H.
  apply disj_split in H.
  destruct H.
  sep normal in H.
  unfold p_local in H.
  unfold CurTid in H.
  unfold LINV in H.
  unfold OSLInv in H.
  unfold init_lg in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  destructs H0.
  inverts H0.
  destruct H1.
  subst x1.
  sep_lifts_skp_in H ((OSTCBCur, _N_ 1), (OSTCBCur, _N_ 0)).  
  apply read_only_merge_vptr in H.
  destruct H as (H & Ha).
  subst x10.
  unfold LINV.
  sep semiauto.
  Focus 2.
  {
    unfold1 TCBList_P in H4.
    simpljoin.
    unfolds.
    clear H.
    destruct x30 as [[[]]]. (* change *)
    unfold get, sig, join in *; simpl in *.
    unfold get, sig, join in *; simpl in *.
    do 4 eexists. (* change *)
    eapply TcbMod.join_get_r.
    eauto.
    eapply TcbMod.join_get_l.
    eauto.
    eapply TcbMod.get_a_sig_a.
    inverts H1.
    apply CltEnvMod.beq_refl.
  }
  Unfocus.

  unfold AOSTCBList_old.
  sep normal.
  sep eexists.
  sep semiauto.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  sep cancel tcbdllflag.
  sep cancel AOSTCBPrioTbl.
  sep cancel AOSRdyTblGrp.
  sep cancel EvtInv.

  unfold AOSTCBFreeList' in H.
  unfold AOSTCBFreeList.
  unfold OSLInv(* , init_lg *).
  sep auto.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  destruct H.
  unfold TCBFree_Not_Eq in H.
  sep auto.
  unfold TCBFree_Eq in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  destructs H1.
  tryfalse.
  splits; eauto. 
  eauto.
  eauto.
  auto.
  eauto.
  
  unfold p_local in H.
  unfold CurTid in H.
  unfold LINV in H.
  unfold OSLInv in H.
  unfold TCB_Not_In in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  inverts H0.
  destruct H1.
  destruct H1.
  subst x1.
  sep_lifts_skp_in H ((OSTCBCur, _N_ 1), (OSTCBCur, _N_ 0)).
  apply read_only_merge_vptr in H.
  destruct H as (H & Ha).
  subst t.
  sep lift 2%nat in H. (* PV get_off_addr (x26, Int.zero) flag_off @ ... *)
  inverts H6. (* logic_val ... = ... *)
  sep_lifts_trms_in H tcblist. 
  (* sep lift 3%nat in H. *)
  subst x12.
  unfold AOSTCBFreeList' in H.
  destruct H2.
  inverts H2.
  sep normal in H.
  (* sep lift 14%nat in H. *)
  sep_lifts_trms_in H Adisj.
  apply disj_split in H.
  destruct H.
  unfold TCBFree_Not_Eq in H.
  sep normal in H.
  sep split in H.
  tryfalse.
  unfold TCBFree_Eq in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  destruct H2.
  destruct H6;subst.
  sep_lifts_skp_in H ((flag_off, _N_ 1), (flag_off, _N_ 0)). 
  (* sep lift 2%nat in H. *)
  (* sep lift 5%nat in H. *)
  eapply flag_merege_false in H.
  tryfalse.
(****)
  intros.
  sep cancel 2%nat 3%nat.
  unfold OSInv, p_local, CurTid, LINV, OSLInv.
  unfold OldOSInvWL' in H.
  unfold AOSTCBList_old in H.
  
  unfold LINV, OSLInv, init_lg in H.
  sep semiauto.
  (* sep lift 10%nat. *)
  sep_lifts_trms AOSTCBList'.
  unfold AOSTCBList'.
  eapply disj_split.
  left.
  sep normal.
  subst x1.
  sep_lifts_skp_in H (AOSTCBFreeList, (tcbdllseg, _N_ 1)).
  (* sep lift 5%nat in H. *)
  (* sep lift 13%nat in H. *)
  lets Hxx : tcbfreelist_disj_tcblist H.

  sep normal in H.
  sep destruct H. 
  sep normal.
  sep semiauto.
  repeat (sep cancel 1%nat 1%nat).
  sep cancel AOSTCBPrioTbl.
  sep cancel AOSRdyTblGrp.  
  sep cancel 2%nat 4%nat.
  sep cancel OSTCBList. 
  sep cancel tcbdllflag.
  sep_lifts_trms_in H (OSTCBCur, AOSTCBFreeList).
  apply read_only_merge_vptreq in H.
  unfold AOSTCBFreeList in H.
  unfold AOSTCBFreeList'.
  sep_lifts_trms Adisj.
  eapply disj_split.
  left.
  unfold TCBFree_Not_Eq.

  sep auto.
  auto.
  eauto.
  eauto.
  eauto.
  auto.
  auto.
  splits; auto. 
Qed.

Lemma inv_change_old:
  forall P t lg,
    OldOSInvWL t lg ** P <==> OldOSInvWL' t lg  ** P.
Proof.
  intros.
  unfold OldOSInvWL in *.
  unfold OldOSInvWL' in *.
  split;intros.
  sep semiauto.
  unfold p_local in *.
  unfold CurTid in *.
  unfold AOSTCBList in *.
  unfold AOSTCBList_old in *.
  sep normal in H.
  sep destruct H.
  sep lift 4%nat in H.
  sep split in H.
  simpljoin.
  apply read_only_merge_vptr in H.
  destruct H.
  sep auto;eauto.
  sep semiauto.
  unfold p_local in *.
  unfold AOSTCBList in *.
  unfold AOSTCBList_old in *.
  sep normal in H.
  sep destruct H.
  sep lift 3%nat in H.
  sep split in H.
  simpljoin.
  apply read_only_merge_vptreq in H.
  unfold CurTid.
  sep auto;eauto.
Qed.

Lemma inv_change:
    forall P t lg',
      OSInv ** p_local OSLInv t (logic_val (V$1) :: lg') ** P <==> OldOSInvWL t (logic_val (V$1) :: lg')  ** P. 
Proof.
  intros.
  unfold OSInv,OldOSInvWL.
  unfold AOSTCBList.
  split;intros.
  apply inv_change' in H.
  apply inv_change_old;auto.
  apply inv_change'.
  apply inv_change_old;auto.
Qed.

(* Lemma inv_change: *)
(*     forall P t, *)
(*     OSInv ** p_local OSLInv t init_lg ** P <==> OldOSInvWL t init_lg  ** P. *)
(* Proof. *)
(*   intros. *)
(*   unfold OSInv,OldOSInvWL. *)
(*   unfold AOSTCBList. *)
(*   split;intros. *)
(*   apply inv_change' in H. *)
(*   apply inv_change_old;auto. *)
(*   apply inv_change'. *)
(*   apply inv_change_old;auto. *)
(* Qed. *)

Import DeprecatedTactic.
Lemma noabs_oslinv:
  NoAbs OSLInv.
Proof.
  unfolds.
  intros.
  unfold CurLINV in *.
  unfold LINV in *.
  unfold CurTid in *.
  unfold satp in *.
  intros.
  lets Hx:H aop.
  clear H.
  sep normal in Hx.
  sep destruct Hx.
  sep normal.
  exists x x0.
  simpl in Hx.
  simpl.
  mytac.
  do 6 eexists;splits;eauto.
  instantiate (2:=emp).
  clear.
  join auto.
  do 7 eexists;splits;eauto.
  join auto.
  eexists;splits;eauto.
  unfolds;auto.
  unfolds;auto.
  do 6 eexists;splits;eauto.
  instantiate (2:=emp).
  join auto.

  destruct t.
  simpl in *.
  exists x26. exists x27. exists x28. exists x29.
  exists x30. do 6 eexists. 
  splits; eauto.
  join auto.
  split. auto. join auto.
  exists x37. exists x38. eexists. 
  do 3 eexists.
  splits; eauto.
  join auto.
  split. auto. join auto.
  exists x43. exists x44. eexists.
  do 3 eexists.
  splits; eauto.
  join auto.
  split. auto. join auto.
  exists x49. exists x50.
  do 4 eexists.
  splits; auto. 
  join auto.
  split. auto. unfold emposabst. auto. 

  (* do 7 eexists;splits;eauto. *)
  (* join auto. *)
  (* split;auto. *)
  (* unfolds;auto. *)
  (* unfolds;auto. *)

  do 6 eexists;splits;eauto.
  join auto. split. auto. join auto. splits; auto. join auto.  
  
  do 6 eexists;splits;eauto.
  instantiate (1:= O').
  join auto.
  splits;auto.
  unfolds;auto.
Qed.

Close Scope int_scope.
Close Scope Z_scope.

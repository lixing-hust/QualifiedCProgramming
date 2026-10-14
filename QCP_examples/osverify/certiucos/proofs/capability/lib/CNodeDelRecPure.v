Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_int.
Require Import ios_cap_defs.
Require Import ios_cap.
Require Import include_frm.
Require Import sep_auto.
Require Import CapPure.
Require Import math_auto.
Require Import ACSpace_defs.
Require Import Lia.
Require Import CapSpec.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope code_scope.
Set Nested Proofs Allowed.

Lemma array_asrt_eq_frm:
  forall n vl b i v t m P,
  (m < n)%nat ->
    nth_val m vl = Some v ->
    Aarray' (b,i) n t vl ** P<==> 
    PV (b,Int.add i (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t))) (Int.repr (BinInt.Z.of_nat m)))) @ t |-> v ** (Aarray_rm (b,i) n t vl m) ** P. 
  Proof.
    intros.
    split. intros.
    sep pauto.
    eapply array_asrt_eq; eauto.
    intros. sep pauto.
    eapply array_asrt_eq; eauto.
  Qed.

Lemma LV_to_Rv_array:
  forall s  x tid decl id off P t lv b i0 n v idx,
  (0 <= idx < n)%nat ->
  field_offset id decl = Some off ->
  ftype id decl = Some (Tarray t n)->
  nth_val  idx lv = Some v ->
  rule_type_val_match t v  = true->
  s|= LV x @(Tptr (Tstruct tid decl)) |-> Vptr (b, i0) ** 
      LV i @ Tint32 |-> Vint32(Int.repr (Z.of_nat idx)) ** 
      Aarray (b, Int.add i0 off) (Tarray t n) lv ** P  ->
  s|= Rv earrayelem (efield (ederef(evar x)) id) (evar i) @t == v.
Proof.
  introv Hlen.
  intros.
  destruct_s s.
  eapply lv_mapsto_to_rv.
  2:{
    simpl.
    destruct H3. simpljoin.
    simpl in j, j0, s. simpljoin1.
    rewrite H7.
    rewrite H0.
    apply mapstoval_load in H8.
    lets Hload: load_local j H8.
    rewrite Int.unsigned_zero in Hload.
    rewrite Hload.
    unfold getoff. unfold evaltype.
    rewrite H7. rewrite H.
    rewrite Int.repr_unsigned.
    sep lift 2%nat in s0. destruct s0. simpljoin.
    simpl in H4, H6, H9. simpljoin1.
    unfold load at 1. simpl addr_to_addrval.
    rewrite Int.repr_unsigned.
    destruct H10. simpljoin.
    simpl in H5, H12, H11. simpljoin1.
    rewrite H15.
    apply mapstoval_load in H16.
    assert(exists xd, join x4 xd m).  join auto.
    destruct H3.
    lets Hload' : load_local H3 H16.
    rewrite Int.unsigned_zero in Hload'.
    rewrite Hload'.
    split; eauto.
    simpl. auto.
    simpl. auto.
  }
  auto.
  sep lift 3%nat in H3.
  eapply array_asrt_eq_frm with (m:= idx) in H3; eauto.
  destruct Hlen. auto.
Qed.

Lemma list_map_eq3:
forall t (l1 l2  l4 l5 : list t) (a1 a2 : t),
  length l1 = length l4 ->
  length l2 = length l5 ->
  l1 ++ a1 :: l2 = l4 ++ a2 :: l5 ->
  l1 = l4 /\ a1 = a2 /\ l2 = l5.
Proof.
  intros.
  assert(l1 = l4).
  eapply same_lenth_list_first_eq; eauto.
  subst l1.
  eapply app_inv_head in H1. inverts H1.
  splits; auto.
Qed.
Lemma while_statement_val: 
  forall s idx v'17 b i0 v'18 ls'' v'11 v'12 p b1, 
  length ls'' = 64%nat->
  (v'12 < 64)%nat ->
  length v'17 = v'12 ->
  length v'18 = (64 - (S v'12))%nat ->
  child_num_of (nth_cspace v'12 ls'') = Some b1 ->
  s|=  LV ios_cap_defs.i @ long|-> (V$ Z.of_nat idx) **
  ACSpaceAarrayTptr 64 (v'17 ++ Vptr (b ↝ {i0}) :: v'18) ls'' 
  v'11 ** LV dest_space @ CSPACE ∗
  |-> Vptr (b ↝ {i0}) ** p ->
  nth_val' v'12 (v'17 ++ Vptr(b, i0) :: v'18) <> Vnull ->
  s|= Rv dest_space′→ child_num >ₑios_cap_defs.i′ @
  long ==
  val_inj
   (bop_eval (V$ Z.of_nat idx)
      (Vint32 b1) long long olt).
Proof.
  intros.
  sep lift 2%nat in H4.
  eapply ACSpaceAarrayTptr_unfold_any_idx_frm with(idx:=v'12) in H4; eauto.
  sep normal in H4.
  sep destruct H4.
  sep split in H4.
  2: rewrite H; auto.
  2:{
      rewrite app_length.
      simpl.
      rewrite H1, H2.
      rewrite S_add_sub_S.
      lia.
      lia.
  }
  2: lia.
  unfold ACSpace in H4. 
  sep normal in H4.
  sep destruct H4.
  destruct x0.
  destruct p0.
  destruct p0.
  destruct p0.
  destruct x4.
  sep normal in H4.
  sep split in H4.
  eapply bop_rv.
  sep lift 8%nat in H4.
  eapply LV_to_Rv in H4.
  eapply inline_tactics.monoasrt_mono in H4. 
  exact H4.
  eapply inline_tactics.Rv_mono.
  auto. simpl. auto.
  eapply lv_mapsto_to_rv.
  2:{
      eapply local_val_struct_member_addr.
      sep lift 9%nat in H4.
      exact H4.
      unfold CSPACE.
      eauto. unfold field_offset. simpl.
      rewrite Int.add_zero. eauto.
      simpl. eauto.
  } 
  2:{
      simpl typelen in H4.
      sep lift 3%nat in H4.
      unfold Aptrmapsto in H4 at 1.
      destruct H8.
      assert(length v'17 = length x2).
      rewrite H1, e. auto.
      assert(length v'18 = length x3).
      rewrite H2, e0. auto.
      lets Hx: list_map_eq3 H8 H14 H6.
      destruct Hx. 
      destruct H16.
      inverts H16.
      exact H4.
  }   
  simpl. auto.
  2:{
      unfold val_inj, bop_eval. 
      unfold cmp_val. unfold cmpu.
      destruct ( Int.ltu($ Z.of_nat idx) b1); simpl; auto.
  }
  2: simpl; auto.
  assert(i1 = b1).
  subst ls''.
  clear -H3 H9.
  destruct H9.
  rewrite nth_cspace_length_imp in H3.
  simpl in H3. 
  inverts H3. auto. auto.
  subst i1. auto.
Qed.
 
Lemma array_type_match2rule_type_match: 
  forall l1 l2 a t,
  array_type_vallist_match t (l1 ++ a :: l2) ->
  rule_type_val_match t a = true.
  Proof.
      intros.
      induction l1.
      simpl in H. destruct H. auto.
      simpl in H. destruct H. eapply IHl1 in H0.
      auto.
  Qed.
Lemma nth_val'2nth_val_ptr:
  forall n rtbl x,
  nth_val' n rtbl = Vptr x ->
  nth_val n rtbl = Some (Vptr x).
  Proof.
  intros.
  inductions n;
  simpl in *;  destruct rtbl; simpl in *;tryfalse; try subst; auto.
Qed.

Lemma reverse_map_injection:
    forall l1 l3 n x  v l2  l4 a z,
    children_not_null (l1 ++ Vptr v :: l2) n ->
    (S(length l1) <= n)%nat ->
    length l1 = length l3 ->
    get x v = Some a ->
    reverse_map x (l1 ++ Vptr v :: l2) = l3 ++ z :: l4 ->
    a = z.
Proof.
    induction l1; destruct n; destruct l3;intros.
    simpl in H1. 
    simpl in H3. unfold int32_inj in H3.
    rewrite H2 in H3. inverts H3. auto. 
    simpl in H1. tryfalse.
    simpl in H3. unfold int32_inj in H3.
    rewrite H2 in H3. inverts H3. auto. 
    simpl in H1; tryfalse.
    simpl in H1. tryfalse. 
    simpl in H0. lia.
    simpl in H1. tryfalse. 
    assert(children_not_null (l1 ++ Vptr v:: l2) n).
    
    unfold children_not_null in *.
    splits; intros.
    destruct H. lets Hx: H (S i0).
    assert(0 <= S i0 < (S n))%nat by lia.
    eapply Hx in H6.
    simpl in H6. eauto. 
    assert((S n <= (S i0) <
    length ((a :: l1) ++ Vptr v :: l2))%nat).
    simpl. lia.
    destruct H. lets Hx: H6 (S i0) H5.
    simpl in Hx. eauto. 
    simpl in H0. 
    assert(S(length l1) <= n)%nat by lia.
    simpl in H1.
    assert(length l1 = length l3) by lia.
    simpl in H3. 
    destruct a; unfolds in H; simpljoin;
    pose proof H 0%nat; assert(Hlt: (0 <= 0 < S n)%nat) by lia;
    eapply H8 in Hlt; simpljoin; simpl in H9; tryfalse.
    inverts H3. 
    lets Hx: IHl1 H4 H5 H6 H2 H12.
    auto.
Qed.

Lemma seq_rule': 
forall  Spec sd  I r ri p p' p'' q  s1 s2 s3 pa t, 
  InfRules Spec sd pa I r ri p (s1 ) p' t ->
  InfRules Spec sd pa I r ri p' (s2 ) p'' t ->  
  InfRules Spec sd pa I r ri p'' s3 q t ->
  InfRules Spec sd pa I r ri p (sseq s1 (sseq s2 s3)) q t .
Proof.
  intros.
  eapply seq_rule; eauto.
  eapply seq_rule; eauto.
Qed.

Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_cap_defs.
Require Import ios_cap.
Require Import CapPure.
Require Import ACSpace_defs.
Require Import CapSpec.
Require Import include_frm.
Require Import os_inv.
Require Import abs_op.
Require Import sep_auto.
Require Import ucos_frmaop.
Require Import abs_step.
Require Import Lia.
Require Import sem_lab. 
Require Import abs_op_capability. 
(* Require Import userGrantCapPure. *)
(* Require Import hoare_forward_tac_ext. *)
Import DeprecatedTactic.

Open Scope list_scope.
Open Scope Z_scope.
Open Scope int_scope.
Open Scope code_scope.
Set Nested Proofs Allowed.
Set Keyed Unification.

Lemma expr_field_array_asrt_impl_frm_val:
  forall s p' b i t id e1 e2 decl  n' n sid off, 
    field_offset id decl = Some off ->
    nth_id n' decl = Some id ->
    ftype id decl = Some (Tarray t n) -> 
    s |=Lv e1 @ (Tstruct sid decl) == (b, i)  **p' ->
    s |= Lv earrayelem (efield e1 id) (′e2) @ t ==
    (b,
     Int.add (Int.add i off)
             (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                      (Int.repr (e2)))) ** p'.
Proof.
  sep pauto.
  destruct s as [[]].
  destruct t0 as [[[[[]]]]].
  simpl in *. simpljoin.
  rewrite H3.  
  rewrite H1. rewrite H2. 
  unfold getoff. 
  rewrite H3.  rewrite H. 
  unfold load. 
  unfold addr_to_addrval.
  unfold addrval_to_addr.
  rewrite Int.repr_unsigned. split.
  rewrite Int.repr_unsigned. auto. auto.
Qed.

Lemma A_dom_lenv_add:
  forall s l p,
  s |= A_dom_lenv l ** p ->
  s |= A_dom_lenv l ** A_dom_lenv l ** p. 
Proof.
  intros.
  sep split in H. 
  sep split; auto.
Qed.

Lemma field_array_struct_impl_g_char_t_g:
  forall  p' b i t id decl  n' gident lident sid off tp 
  idx b0 i0 lenv n s, 
  var_notin_dom gident lenv = true  ->
  var_notin_dom lident lenv = true ->
  field_offset id decl = Some off ->
  ftype id decl = Some t ->
  (Z.of_nat idx >= 0)%Z ->
  (Z.of_nat idx <= 255)%Z ->
  nth_id n' decl = Some id ->
  tp = Tptr(Tstruct sid decl) ->
  s |= G& gident @ (Tarray tp n) == (b, i)** GV lident @ char_t |-> Vint32(Int.repr (Z.of_nat idx))
  ** PV (b, i +ᵢ  Int.mul ($ Z.of_nat (typelen tp)) ($ Z.of_nat idx)) @ tp  |-> Vptr(b0, i0) ** 
  A_dom_lenv lenv ** p'->
  s |=  Lv (efield(ederef (gident ′ [lident ′]))id) @ t == (b0, Int.add i0 off) ** p'.
Proof.
    introv Hgnotin.
    introv Hlnotin.
    introv Hoff.
    introv Htype.
    introv Hinrange1.
    introv Hinrange2.
    intros.
    sep cancel p'.
    assert(s|=Lv (gident ′ [lident ′])@ tp == (b, i +ᵢ  Int.mul ($ Z.of_nat (typelen tp))($ (Z.of_nat idx)))
    ** PV (b, i +ᵢInt.mul ($ Z.of_nat (typelen tp))($ Z.of_nat idx)) @ tp
 |-> Vptr (b0 ,i0)).
    eapply arrayelem_asrt_impl_g'.
    instantiate(1:=char_t).
    auto.
    sep lift 4%nat in H1.
    eapply A_dom_lenv_add in H1.
    lets Hs: dom_lenv_imp_notin_lenv Hgnotin H1.
    sep normal.
    unfold Agvarenv' in Hs. 
    sep cancel 1%nat 1%nat. 
    sep cancel 2%nat 1%nat. 
    sep cancel 3%nat 2%nat.
    eapply gvar_rv; eauto.
    sep auto. 
    simpl. 
    rewrite Int.unsigned_repr.
    change Byte.max_unsigned with 255.
    assert(Z.of_nat idx <=? 255 = true).
    clear -Hinrange1 Hinrange2.
    int auto.
    rewrite H3.  auto.
    clear -Hinrange1 Hinrange2.
    int auto. 
    eapply field_ederef_asrt_impl'. eauto. 
    auto.
    rewrite H0 in H2.
    instantiate(2:=sid).
    instantiate(3:=b).
    instantiate(3:=i +ᵢInt.mul($ Z.of_nat (typelen tp))($ Z.of_nat idx)).
    sep auto.
Qed.

Lemma fold_AOSCSpacePrioTbl1:
  forall s b i ptrvl vl cspacels idx p q,
  length ptrvl = 64%nat ->
  length vl = 64%nat ->
  array_type_vallist_match CSPACE ∗ ptrvl ->
  nth_val idx ptrvl = Some (Vptr p) ->
  (idx < 64)%nat ->
  s |= G&OSCSpacePrioTbl @ Tarray CSPACE ∗ 64 ==(b, i)
  ** ACSpaceAarrayTptr  64%nat ptrvl vl cspacels
  ** PV (b, i +ᵢ $ Z.of_nat (idx * (typelen (Tptr CSPACE)))) @ (Tptr CSPACE) |-> Vptr p **
  Aarray_rm (b, i) 64%nat (Tptr CSPACE) ptrvl idx **q
  -> s |= AOSCSpacePrioTbl (b, i) ptrvl vl cspacels **q.
Proof.
  intros.
  unfold AOSCSpacePrioTbl.

  assert(Haddition: $ Z.of_nat (idx * typelen CSPACE ∗) = Int.mul ($ Z.of_nat (typelen CSPACE ∗))
    ($ Z.of_nat idx)).
    {
      rewrite Nat2Z.inj_mul.
      simpl typelen.
      mauto.
    }
  rewrite Haddition in H4.
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
  sep lifts (3::4::nil)%nat in H4.
  eapply array_asrt_eq_frm in H4; eauto.
  clear Haddition.
  sep auto.
Qed.

Lemma nth_cspace_eq_nth_cspace_val: 
forall vl x,
nth_cspace_val x vl = nth_cspace x vl.
Proof.
induction vl; destruct x; intros; simpl; auto.
Qed.
Lemma nth_slots_eq_nth_slots: 
forall vl x,
nth_slots x vl = ACSpace_defs.nth_slots x vl.
Proof.
induction vl; destruct x; intros; simpl; auto.
Qed.



Lemma update_nth_cspace_slots_cap_length_eq:
forall ls desc class v,
length ls = length (update_nth_cspace_slots_cap desc
class ls v).
Proof.
intros. 
unfold update_nth_cspace_slots_cap.
destruct (nth_cspace
desc ls) eqn: Heq.
destruct c, p, p, p, c, p. 
destruct (ACSpace_defs.nth_slots class l0).
destruct p, p, c, p.  

{
  remember (i0, i1,
  ACSpace_defs.update_nth_list slot_val_type
    class l0
    (i2, v), i, l, v0) as uval. 
  intros.
  rewrite update_nth_list_len_eq.
  auto. 
}
auto. auto.
Qed.

Lemma update_nth_cspace_slots_type_length_eq:
forall ls desc class v,
length ls = length (update_nth_cspace_slots_type desc
class ls v).
Proof.
intros. 
unfold update_nth_cspace_slots_type.
destruct (nth_cspace
desc ls) eqn: Heq.
destruct c, p, p, p, c, p. 
destruct (ACSpace_defs.nth_slots class l0).
destruct p, p, c, p.  

{
  remember (i1, i2,
  ACSpace_defs.update_nth_list
    slot_val_type class l0
    (v, (i4, (i5, i6, v1))), i0, l, v0, i) as uval. 
  intros.
  rewrite update_nth_list_len_eq.
  auto. 
}
auto. auto.
Qed.

Lemma add_isr_is_prop:
forall P, Aisr empisr ** Ais nil ** P ==> Aisr empisr ** Ais nil ** A_isr_is_prop ** P.
Proof.
  intros.
  unfold A_isr_is_prop.
  sep normal.
  sep auto.
  rewrite H0.
  rewrite H1.
  unfolds.
  intros.
  auto.
Qed.

Lemma aemp_isr_elim:
forall s P,
  s |= aemp_isr_is ** P -> s |= P.
Proof.
  introv Hsat.
  simpl in Hsat.
  simpljoin.
  destruct_s s. 
  simpl in *.
  assert (m=x0) by join auto.
  assert (o=x3) by join auto.
  subst.
  auto.
Qed.

Lemma update_nth_cspace_slots_cap_imply_exists:
forall x0 x y cspacevl v cspace,
  nth_cspace_val∘ (Int.unsigned x0)(update_nth_cspace_slots_cap
    x y cspacevl v) =
  Some cspace ->
  exists cspace', nth_cspace_val∘ (Int.unsigned x0) cspacevl = Some cspace'. 
Proof.
  intros.
  assert(∘ (Int.unsigned x0) < (length cspacevl))%nat. 
  assert(length cspacevl = length (update_nth_cspace_slots_cap x
  y cspacevl v)).
  eapply update_nth_cspace_slots_cap_length_eq.
  rewrite H0.
  lets Hc: nat_ltorge (∘ (Int.unsigned x0)) (length
  (update_nth_cspace_slots_cap x y
     cspacevl v)).
  destruct Hc. auto.
  rewrite nth_cspace_eq_nth_cspace_val in H. 
  rewrite nth_cspace_none in H; auto.
  tryfalse.
  rewrite nth_cspace_eq_nth_cspace_val.
  eapply nth_cspace_exists; auto.
Qed.

Lemma update_nth_cspace_slots_type_imply_exists:
forall x0 x y cspacevl v cspace,
  nth_cspace_val∘ (Int.unsigned x0)(update_nth_cspace_slots_type
    x y cspacevl v) =
  Some cspace ->
  exists cspace', nth_cspace_val∘ (Int.unsigned x0) cspacevl = Some cspace'. 
Proof.
  intros.
  assert(∘ (Int.unsigned x0) < (length cspacevl))%nat. 
  assert(length cspacevl = length (update_nth_cspace_slots_type x
  y cspacevl v)).
  eapply update_nth_cspace_slots_type_length_eq.
  rewrite H0.
  lets Hc: nat_ltorge (∘ (Int.unsigned x0)) (length
  (update_nth_cspace_slots_type x y
     cspacevl v)).
  destruct Hc. auto.
  rewrite nth_cspace_eq_nth_cspace_val in H. 
  rewrite nth_cspace_none in H; auto.
  tryfalse.
  rewrite nth_cspace_eq_nth_cspace_val.
  eapply nth_cspace_exists; auto.
Qed.

Lemma update_nth_cspace_slot_cap_child_similar:
  forall ls desc class v,
  child_similar ls (update_nth_cspace_slots_cap desc class ls v).
Proof.
  intros. 
  unfold update_nth_cspace_slots_cap.
  destruct (nth_cspace
  desc ls) eqn: Heq.
  destruct c, p, p, p, c, p. 
  destruct (ACSpace_defs.nth_slots class l0).
  destruct p, p, c, p.  

  {
    remember (i1, i2,
    ACSpace_defs.update_nth_list slot_val_type
      class l0
      (i3, v), i0, l, v0, i) as uval. 
    unfold child_similar.
    intros.
    lets Hc1: nat_ltorge (Z.to_nat(Int.unsigned node)) (length ls).
    lets Hc2: nat_ltorge (desc) (length ls).
    lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned node)) (desc).
    destruct Hc1; destruct Hc2; destruct Hc3.
    unfold child. 
    rewrite H1 in *.
    rewrite Heq.
    assert(nth_cspace desc
    (ACSpace_defs.update_nth_list cspace_val_type
       (desc) ls
       uval) = Some uval).
    eapply update_nth_cspace_eq; auto. 
    rewrite H2. subst uval. auto. 
    unfold child. 
    assert( nth_cspace
    (Z.to_nat (Int.unsigned node))
    (ACSpace_defs.update_nth_list cspace_val_type
       (desc)
       ls uval) = nth_cspace
       (Z.to_nat (Int.unsigned node)) ls).
    eapply update_nth_cspace_neqrev; auto.
    rewrite H2. auto.  
    eapply update_nth_cspace_remain with(v:= uval)in H0. 
    
    rewrite H0. auto. 
    eapply update_nth_cspace_remain with(v:= uval)in H0. 
    rewrite H0. auto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
  }
  unfold child_similar; intros. auto.
  unfold child_similar; intros. auto.
Qed.

Lemma update_nth_cspace_slot_type_child_similar:
  forall ls desc class v,
  child_similar ls (update_nth_cspace_slots_type desc class ls v).
Proof.
  intros. 
  unfold update_nth_cspace_slots_type.
  destruct (nth_cspace
  desc ls) eqn: Heq.
  destruct c, p, p, p, c, p. 
  destruct (ACSpace_defs.nth_slots class l0).
  destruct p, p, c, p.  

  {
    remember (i1, i2,
    ACSpace_defs.update_nth_list
      slot_val_type class l0
      (v, (i4, (i5, i6, v1))), i0, l, v0, i) as uval. 
    unfold child_similar.
    intros.
    lets Hc1: nat_ltorge (Z.to_nat(Int.unsigned node)) (length ls).
    lets Hc2: nat_ltorge (desc) (length ls).
    lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned node)) (desc).
    destruct Hc1; destruct Hc2; destruct Hc3.
    (* unfold child.  *)
    rewrite H1 in *.
    rewrite Heq.
    assert(nth_cspace desc
    (ACSpace_defs.update_nth_list cspace_val_type
       (desc) ls
       uval) = Some uval).
    eapply update_nth_cspace_eq; auto. 
    subst uval. rewrite H2. auto. 
    (* unfold child.  *)
    assert( nth_cspace
    (Z.to_nat (Int.unsigned node))
    (ACSpace_defs.update_nth_list cspace_val_type
       (desc)
       ls uval) = nth_cspace
       (Z.to_nat (Int.unsigned node)) ls).
    eapply update_nth_cspace_neqrev; auto.
    subst uval. rewrite H2. auto.  
    eapply update_nth_cspace_remain with(v:= uval)in H0. 
    
    subst uval. rewrite H0. auto. 
    eapply update_nth_cspace_remain with(v:= uval)in H0. 
    subst uval. rewrite H0. auto. 
    (* unfold child.  *)
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    (* unfold child.  *)
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    (* unfold child.  *)
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    (* unfold child.  *)
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
  }
  unfold child_similar; intros. auto.
  unfold child_similar; intros. auto.
Qed.

Lemma RL_Cap_Parent_Child_remain: 
  forall cspacevl vl x y  v,
  RL_Cap_Parent_Child vl cspacevl ->
  RL_Cap_Parent_Child vl (update_nth_cspace_slots_cap x y cspacevl v).
Proof.
  unfold RL_Cap_Parent_Child. intros.
  destruct H. 
  splits; intros.
  assert(H4_bak: nth_cspace_val
  ∘ (Int.unsigned x0)
  (update_nth_cspace_slots_cap
     x y cspacevl v) =
Some cspace) by auto.
  eapply update_nth_cspace_slots_cap_imply_exists in H3.
  destruct H3.
  lets Hx: H H1 H2 H3.
  assert(child_similar cspacevl (update_nth_cspace_slots_cap x y cspacevl v)).
  eapply update_nth_cspace_slot_cap_child_similar.
  unfold child_similar in H4.
  lets Hy: H4 x0. 
  destruct Hy.
  rewrite nth_cspace_eq_nth_cspace_val in H3.
  rewrite nth_cspace_eq_nth_cspace_val in H4_bak.
  rewrite H3, H4_bak in H6.
  assert(get_Childlist x1 = get_Childlist cspace).
  unfolds.
  destruct x1, p, p, p.
  destruct cspace, p, p, p.
  unfolds in H6. inverts H6. auto.
  rewrite <- H7. auto.
  auto.

  (*right*)
  assert(H2_bak: nth_cspace_val
  ∘ (Int.unsigned prio)
  (update_nth_cspace_slots_cap
     x y cspacevl v) =
Some cspace) by auto.
 eapply update_nth_cspace_slots_cap_imply_exists in H1.
 destruct H1.
 lets Hx: H0 H1.
 lets Hy: Hx x0.
 assert(get_Childlist x1 = get_Childlist cspace).
 {
  assert(child_similar cspacevl (update_nth_cspace_slots_cap x y cspacevl v)).
  eapply update_nth_cspace_slot_cap_child_similar.
  unfold child_similar in H3.
  lets Hz: H3 prio.
  destruct Hz.
  rewrite nth_cspace_eq_nth_cspace_val in H1, H2_bak.
  rewrite H1, H2_bak in H5.
  unfolds. destruct x1, p, p, p.
  destruct cspace, p, p, p.
  unfolds in H5. inverts H5. auto.
 }
 rewrite <- H3 in H2.
 eapply Hy. auto.
Qed.

Lemma RL_Cap_Parent_Child_update_slots_type_remain: 
  forall cspacevl vl x y  v,
  RL_Cap_Parent_Child vl cspacevl ->
  RL_Cap_Parent_Child vl (update_nth_cspace_slots_type x y cspacevl v).
Proof.
  unfold RL_Cap_Parent_Child. intros.
  destruct H. 
  splits; intros.
  assert(H4_bak: nth_cspace_val
    ∘ (Int.unsigned x0)
    (update_nth_cspace_slots_type
      x y cspacevl v) =
    Some cspace) by auto.
  eapply update_nth_cspace_slots_type_imply_exists in H3.
  destruct H3.
  lets Hx: H H1 H2 H3.
  assert(child_similar cspacevl (update_nth_cspace_slots_type x y cspacevl v)).
  eapply update_nth_cspace_slot_type_child_similar.
  unfold child_similar in H4.
  lets Hy: H4 x0. 
  destruct Hy.
  rewrite nth_cspace_eq_nth_cspace_val in H3.
  rewrite nth_cspace_eq_nth_cspace_val in H4_bak.
  rewrite H3, H4_bak in H6.
  assert(get_Childlist x1 = get_Childlist cspace).
  unfolds.
  destruct x1, p, p, p.
  destruct cspace, p, p, p.
  unfolds in H6. inverts H6. auto.
  rewrite <- H7. auto.
  (* auto. *)

  (*right*)
  assert(H2_bak: nth_cspace_val
      ∘ (Int.unsigned prio)
      (update_nth_cspace_slots_type
        x y cspacevl v) =
    Some cspace) by auto.
 eapply update_nth_cspace_slots_type_imply_exists in H1.
 destruct H1.
 lets Hx: H0 H1.
 lets Hy: Hx x0.
 assert(get_Childlist x1 = get_Childlist cspace).
 {
  assert(child_similar cspacevl (update_nth_cspace_slots_type x y cspacevl v)).
  eapply update_nth_cspace_slot_type_child_similar.
  unfold child_similar in H3.
  lets Hz: H3 prio.
  destruct Hz.
  rewrite nth_cspace_eq_nth_cspace_val in H1, H2_bak.
  rewrite H1, H2_bak in H5.
  unfolds. destruct x1, p, p, p.
  destruct cspace, p, p, p.
  unfolds in H5. inverts H5. auto.
 }
 rewrite <- H3 in H2.
 eapply Hy. auto.
Qed.

Lemma taskPrioProp_update_slots_type_remain: 
  forall cspacevl x y v,
  taskPrioProp cspacevl ->
  taskPrioProp (update_nth_cspace_slots_type x y cspacevl v).
Proof.
  unfold taskPrioProp.
  intros. 

  unfold update_nth_cspace_slots_type in H1.

  destruct (nth_cspace
  x cspacevl) eqn: Heq.
  destruct c0, p, p, p, c0, p. 
  destruct (ACSpace_defs.nth_slots y l0).
  destruct p, p, c0, p. 

  {
    remember(i1, i2,
    ACSpace_defs.update_nth_list slot_val_type y l0
      (v, (i4, (i5, i6, v1))), i0, l, v0, i) as uval. 

    rewrite nth_cspace_eq_nth_cspace_val in H1.
    unfold nat_of_Z in H1.

    lets Hc1: nat_ltorge (Z.to_nat(Int.unsigned prio)) (length cspacevl).
    lets Hc2: nat_ltorge (x) (length cspacevl).
    lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned prio)) (x).
    destruct Hc1; destruct Hc2; destruct Hc3.

    rewrite H4 in *.

    assert(nth_cspace x
    (ACSpace_defs.update_nth_list cspace_val_type
      (x) cspacevl
     uval) = Some uval).
    eapply update_nth_cspace_eq; auto.
    subst uval. rewrite H5 in H1.

    inverts H1. 
    eapply H.
    eauto.
    rewrite nth_cspace_eq_nth_cspace_val.
    unfold nat_of_Z.
    rewrite H4 in *.
    eauto.

    eapply H.
    eauto.
    rewrite nth_cspace_eq_nth_cspace_val.
    unfold nat_of_Z.
    assert( nth_cspace
    (Z.to_nat (Int.unsigned prio))
    (ACSpace_defs.update_nth_list cspace_val_type
      (x)
      cspacevl
            uval) = nth_cspace
      (Z.to_nat (Int.unsigned prio)) cspacevl).
    eapply update_nth_cspace_neqrev; auto.
    subst uval. rewrite H5 in H1. eauto.

    lia.

    eapply update_nth_cspace_remain with(v:= uval)in H3. 
    
    subst uval. rewrite H3 in H1. 
    eapply H.
    eauto.
    rewrite nth_cspace_eq_nth_cspace_val.
    unfold nat_of_Z. eauto.

    lia. 

    rewrite nth_cspace_none in H1; tryfalse.
    rewrite update_nth_list_len_eq; eauto. 
    rewrite nth_cspace_none in H1; tryfalse.
    rewrite update_nth_list_len_eq; eauto. 

    rewrite nth_cspace_none in H1; tryfalse.
    rewrite update_nth_list_len_eq; eauto. 
  }
  eauto.
  eauto.
Qed.

Lemma taskPrioProp_update_slots_cap_remain: 
  forall cspacevl x y v,
  taskPrioProp cspacevl ->
  taskPrioProp (update_nth_cspace_slots_cap x y cspacevl v).
Proof.
  unfold taskPrioProp.
  intros. 

  unfold update_nth_cspace_slots_cap in H1.

  destruct (nth_cspace
  x cspacevl) eqn: Heq.
  destruct c0, p, p, p, c0, p. 
  destruct (ACSpace_defs.nth_slots y l0).
  destruct p, p, c0, p. 

  {
    remember(i1, i2,
    ACSpace_defs.update_nth_list slot_val_type y l0
      (i3, v), i0, l, v0, i) as uval. 

    rewrite nth_cspace_eq_nth_cspace_val in H1.
    unfold nat_of_Z in H1.

    lets Hc1: nat_ltorge (Z.to_nat(Int.unsigned prio)) (length cspacevl).
    lets Hc2: nat_ltorge (x) (length cspacevl).
    lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned prio)) (x).
    destruct Hc1; destruct Hc2; destruct Hc3.

    rewrite H4 in *.

    assert(nth_cspace x
    (ACSpace_defs.update_nth_list cspace_val_type
      (x) cspacevl
      uval) = Some uval).
    eapply update_nth_cspace_eq; auto.
    rewrite H5 in H1. subst uval.

    inverts H1. 
    eapply H.
    eauto.
    rewrite nth_cspace_eq_nth_cspace_val.
    unfold nat_of_Z.
    rewrite H4 in *.
    eauto.

    eapply H.
    eauto.
    rewrite nth_cspace_eq_nth_cspace_val.
    unfold nat_of_Z.
    assert( nth_cspace
    (Z.to_nat (Int.unsigned prio))
    (ACSpace_defs.update_nth_list cspace_val_type
      (x)
      cspacevl
            uval) = nth_cspace
      (Z.to_nat (Int.unsigned prio)) cspacevl).
    eapply update_nth_cspace_neqrev; auto.
    rewrite H5 in H1. eauto.

    lia.

    eapply update_nth_cspace_remain with(v:= uval)in H3. 
    
    rewrite H3 in H1. 
    eapply H.
    eauto.
    rewrite nth_cspace_eq_nth_cspace_val.
    unfold nat_of_Z. eauto.

    lia. 

    rewrite nth_cspace_none in H1; tryfalse.
    rewrite update_nth_list_len_eq; eauto. 
    rewrite nth_cspace_none in H1; tryfalse.
    rewrite update_nth_list_len_eq; eauto. 

    rewrite nth_cspace_none in H1; tryfalse.
    rewrite update_nth_list_len_eq; eauto. 
  }
  eauto.
  eauto.
Qed.


Lemma update_nth_slots_length_imp: 
forall l1 l2 n v1 v2  ,
length l1 = n ->
update_nth_slots n (l1 ++ v1 :: l2) v2 = (l1 ++ v2 :: l2).
Proof.
induction l1; destruct n; intros; simpl; auto.
simpl in H. tryfalse.
simpl in H. tryfalse.
simpl in H. 
assert(length l1 = n) by lia.
eapply IHl1 with(l2:=l2)(v1:=v1)(v2:=v2) in H0.
rewrite H0. auto.
Qed.

Lemma update_nth_slots_eq_update_slots_type: 
forall y v p slots,
update_nth_slots y slots (v, p) = ACSpace_defs.update_nth_list slot_val_type y slots (v, p).
Proof.
  induction y; induction slots; simpl; eauto.
  rewrite IHy.
  eauto.
Qed.

Lemma update_nth_slots_eq_update_slots_type_NoA: 
forall y v p slots,
update_nth_slots y slots (v, p) = update_nth_list slot_val_type y slots (v, p).
Proof.
  induction y; induction slots; simpl; eauto.
  rewrite IHy.
  eauto.
Qed.

Lemma RLH_cspace_slots_P_update_slots_type_remain: 
forall cspacevl vl x y v p cspacels pl a b slots c d e f type x2 x3,
RLH_cspace_slots_P cspacevl vl cspacels pl->
nth_cspace (Z.to_nat(Int.unsigned x)) cspacevl = Some((a, b, slots), c, d, e, f) ->
ACSpace_defs.nth_slots y slots = Some(type, p) ->
get vl x = Some (slots, x2, x3) ->
RLH_cspace_slots_P (update_nth_cspace_slots_type (Z.to_nat(Int.unsigned x)) y cspacevl v)
(set vl x ((update_nth_slots y slots (v, p), x2, x3))) cspacels pl.
Proof.
  intros.
  unfold update_nth_cspace_slots_type.
  rewrite H0.
  destruct (ACSpace_defs.nth_slots y slots).
  destruct p0. 
  remember(a, b,
  ACSpace_defs.update_nth_list slot_val_type y slots
    (v, p0), c, d, e, f) as uval. 
    unfold RLH_cspace_slots_P in *. 
    destruct H. 
    splits; intros.
    lets Hc1: nat_ltorge (Z.to_nat(Int.unsigned prio)) (length cspacevl).
    lets Hc2: nat_ltorge (Z.to_nat(Int.unsigned x)) (length cspacevl).
    lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned prio)) (Z.to_nat(Int.unsigned x)).
    destruct Hc1;    destruct Hc2;    destruct Hc3.
  (* unfold RLH_cspace_slots_P in *. intros.
  destruct H.
  splits; intros. *)
  destruct cspace,p1,p1,p1,c0.
  rewrite nth_cspace_eq_nth_cspace_val in H4.
  unfold nat_of_Z in H4.
  rewrite H7 in *.

  assert(nth_cspace  (Z.to_nat(Int.unsigned x))
  (ACSpace_defs.update_nth_list cspace_val_type
  (Z.to_nat(Int.unsigned x)) cspacevl
   uval) = Some uval).
  eapply update_nth_cspace_eq; auto.
  subst uval.
  rewrite H8 in H4.
  inverts H1.
  inverts H4.

  rewrite <-H7 in H0.
  rewrite <-nth_cspace_eq_nth_cspace_val in H0.
  fold nat_of_Z in H0.
  (* inverts H6.
  inverts H8. *)
  lets Hx: H  H0.
  destruct Hx.   destruct H1. destruct H1.
  (* inverts H8. *)
  (* eexists. eexists. split. *)
  assert(prio = x).
  clear -H7.
  eapply Z2Nat.inj_iff in H7.
  apply unsigned_inj in H7.
  auto.
  int auto.
  int auto.
  rewrite H9 in *.
  rewrite H1 in H2.
  inverts H2.
  rewrite update_nth_slots_eq_update_slots_type.
  (* unfold update_nth_slots. simpl. *)
  eexists. eexists. split.
  eapply get_set_eq.
  eauto.

  destruct cspace,p1,p1,p1,c0.
  rewrite nth_cspace_eq_nth_cspace_val in H4.
    unfold nat_of_Z in H4.
    assert( nth_cspace
    (Z.to_nat (Int.unsigned prio))
    (ACSpace_defs.update_nth_list cspace_val_type
    (Z.to_nat(Int.unsigned x))
      cspacevl
            uval) = nth_cspace
      (Z.to_nat (Int.unsigned prio)) cspacevl).
    eapply update_nth_cspace_neqrev; auto.
    subst uval. rewrite H8 in H4.
    inverts H1.
    (* inverts H5. *)
  
    (* rewrite <-H8 in H0. *)
    rewrite <-nth_cspace_eq_nth_cspace_val in H4.
    fold nat_of_Z in H4.
    (* inverts H6.
    inverts H8. *)
    lets Hx: H H4.
    destruct Hx.   destruct H1. destruct H1.
    eexists. eexists. split.
    eapply get_set_neq.
    intro.
    rewrite H10 in H7. 
    tryfalse.
    eauto.
    eauto.

    lia.

    rewrite nth_cspace_none in H0; tryfalse.
     eauto.

     lia.

     rewrite nth_cspace_eq_nth_cspace_val in H4.
     unfold nat_of_Z in H4. 
     rewrite nth_cspace_none in H4; tryfalse.
     rewrite update_nth_list_len_eq; eauto.

     rewrite nth_cspace_none in H0; tryfalse.
     eauto.

     rewrite nth_cspace_none in H0; tryfalse.
     eauto.
     
     lets Hc1: nat_ltorge (Z.to_nat(Int.unsigned prio)) (length cspacevl).
     lets Hc2: nat_ltorge (Z.to_nat(Int.unsigned x)) (length cspacevl).
     lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned prio)) (Z.to_nat(Int.unsigned x)).
     destruct Hc1;    destruct Hc2;    destruct Hc3.

     rewrite nth_cspace_eq_nth_cspace_val.
     unfold nat_of_Z.
     rewrite H7 in *.
   
     assert(nth_cspace  (Z.to_nat(Int.unsigned x))
     (ACSpace_defs.update_nth_list cspace_val_type
     (Z.to_nat(Int.unsigned x)) cspacevl
      uval) = Some uval).
     eapply update_nth_cspace_eq; auto.
     subst uval. 
     (* rewrite update_nth_slots_eq_update_slots_type. *)
     rewrite update_nth_slots_eq_update_slots_type in H4.
     (* rewrite <-nth_cspace_eq_nth_cspace_val.
     fold nat_of_Z. *)
     rewrite H8.
     inverts H1.

     assert(prio = x).
     clear -H7.
     eapply Z2Nat.inj_iff in H7.
     apply unsigned_inj in H7.
     auto.
     int auto.
     int auto.
     rewrite H1 in H4.
     rewrite get_set_eq in H4.
     (* inverts H5. *)
     rewrite <-H1 in H2.

     lets Hx: H3  H2.
     destruct Hx. destruct H9. destruct H9. destruct H9. destruct H9.
     destruct H9.
     rewrite nth_cspace_eq_nth_cspace_val in H9.
     unfold nat_of_Z in H9.
     rewrite H7 in H9. 

     inverts H4.
     rewrite H9 in H0.
     inverts H0.
     (* rewrite H1 in H5. *)
     eexists.  eexists.  eexists.  eexists.  eexists.
     split.
     eauto.
     eauto.

     assert( nth_cspace
     (Z.to_nat (Int.unsigned prio))
     (ACSpace_defs.update_nth_list cspace_val_type
     (Z.to_nat(Int.unsigned x))
       cspacevl
             uval) = nth_cspace
       (Z.to_nat (Int.unsigned prio)) cspacevl).
     eapply update_nth_cspace_neqrev; auto.
     subst uval.
     rewrite nth_cspace_eq_nth_cspace_val.
     unfold nat_of_Z.
     rewrite H8.

     rewrite map_get_set' in H4; eauto.
  
     rewrite <-nth_cspace_eq_nth_cspace_val.
     fold nat_of_Z.
     eapply H3.
     eauto.
     lets Hx: Int.eq_dec x prio.
     destruct Hx. subst x. lia.
     auto.
     
     rewrite <- H7 in H6. lia.
     eapply nth_cspace_none in H6.
     
     lets Hx: H3 H2.
     simpljoin.
     rewrite nth_cspace_eq_nth_cspace_val in H8.
     unfold nat_of_Z in H8.
     rewrite H6 in H8. tryfalse.
     rewrite map_get_set' in H4; eauto.
     eapply nth_cspace_none in H5.
     lets Hx: H3 H4.
     simpljoin.
     rewrite nth_cspace_eq_nth_cspace_val in H8.
     unfold nat_of_Z in H8.
     rewrite H8 in H5. tryfalse.
     lets Hx: Int.eq_dec x prio.
     destruct Hx. subst x. lia. auto.
     rewrite map_get_set' in H4; eauto.
     eapply nth_cspace_none in H5.
     lets Hx: H3 H4.
     simpljoin.
     rewrite nth_cspace_eq_nth_cspace_val in H8.
     unfold nat_of_Z in H8.
     rewrite H8 in H5. tryfalse.
     lets Hx: Int.eq_dec x prio.
     destruct Hx. subst x. lia. auto.
     lets Hx: H3 H2.
     simpljoin.
     eapply nth_cspace_none in H6.
     unfold nat_of_Z in H8.
     rewrite nth_cspace_eq_nth_cspace_val in H8.
     rewrite H6 in H8. tryfalse.
     lets Hx: H3 H2.
     simpljoin.
     eapply nth_cspace_none in H6.
     unfold nat_of_Z in H8.
     rewrite nth_cspace_eq_nth_cspace_val in H8.
     rewrite H6 in H8. tryfalse.
     tryfalse.
Qed.

Lemma RLH_cspace_slots_P_update_slots_cap_remain: 
forall cspacevl vl x y v p cspacels pl a b slots c d e f type x2 x3,
RLH_cspace_slots_P cspacevl vl cspacels pl->
nth_cspace (Z.to_nat(Int.unsigned x)) cspacevl = Some((a, b, slots), c, d, e, f) ->
ACSpace_defs.nth_slots y slots = Some(type, p) ->
get vl x = Some (slots, x2, x3) ->
RLH_cspace_slots_P (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned x)) y cspacevl v)
(set vl x ((update_nth_slots y slots (type, v), x2, x3))) cspacels pl.
Proof.
intros.
unfold update_nth_cspace_slots_cap.
rewrite H0.
destruct (ACSpace_defs.nth_slots y slots).
destruct p0. 
remember(a, b,
ACSpace_defs.update_nth_list slot_val_type y slots
  (i, v), c, d, e, f) as uval. 
  unfold RLH_cspace_slots_P in *. 
  destruct H. 
  splits; intros.
  lets Hc1: nat_ltorge (Z.to_nat(Int.unsigned prio)) (length cspacevl).
  lets Hc2: nat_ltorge (Z.to_nat(Int.unsigned x)) (length cspacevl).
  lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned prio)) (Z.to_nat(Int.unsigned x)).
  destruct Hc1;    destruct Hc2;    destruct Hc3.
(* unfold RLH_cspace_slots_P in *. intros.
destruct H.
splits; intros. *)
destruct cspace,p1,p1,p1,c0.
rewrite nth_cspace_eq_nth_cspace_val in H4.
unfold nat_of_Z in H4.
rewrite H7 in *.

assert(nth_cspace  (Z.to_nat(Int.unsigned x))
(ACSpace_defs.update_nth_list cspace_val_type
(Z.to_nat(Int.unsigned x)) cspacevl
 uval) = Some uval).
eapply update_nth_cspace_eq; auto.
subst uval.
rewrite H8 in H4.
inverts H1.
inverts H4.

rewrite <-H7 in H0.
rewrite <-nth_cspace_eq_nth_cspace_val in H0.
fold nat_of_Z in H0.
(* inverts H6.
inverts H8. *)
lets Hx: H  H0.
destruct Hx.   destruct H1. destruct H1.
(* inverts H8. *)
(* eexists. eexists. split. *)
assert(prio = x).
clear -H7.
eapply Z2Nat.inj_iff in H7.
apply unsigned_inj in H7.
auto.
int auto.
int auto.
rewrite H9 in *.
rewrite H1 in H2.
inverts H2.
rewrite update_nth_slots_eq_update_slots_type.
(* unfold update_nth_slots. simpl. *)
eexists. eexists. split.
eapply get_set_eq.
eauto.

destruct cspace,p1,p1,p1,c0.
rewrite nth_cspace_eq_nth_cspace_val in H4.
  unfold nat_of_Z in H4.
  assert( nth_cspace
  (Z.to_nat (Int.unsigned prio))
  (ACSpace_defs.update_nth_list cspace_val_type
  (Z.to_nat(Int.unsigned x))
    cspacevl
          uval) = nth_cspace
    (Z.to_nat (Int.unsigned prio)) cspacevl).
  eapply update_nth_cspace_neqrev; auto.
  subst uval. rewrite H8 in H4.
  inverts H1.
  (* inverts H5. *)

  (* rewrite <-H8 in H0. *)
  rewrite <-nth_cspace_eq_nth_cspace_val in H4.
  fold nat_of_Z in H4.
  (* inverts H6.
  inverts H8. *)
  lets Hx: H H4.
  destruct Hx.   destruct H1. destruct H1.
  eexists. eexists. split.
  eapply get_set_neq.
  intro.
  rewrite H10 in H7. 
  tryfalse.
  eauto.
  eauto.

  lia.

  rewrite nth_cspace_none in H0; tryfalse.
   eauto.

   lia.

   rewrite nth_cspace_eq_nth_cspace_val in H4.
   unfold nat_of_Z in H4. 
   rewrite nth_cspace_none in H4; tryfalse.
   rewrite update_nth_list_len_eq; eauto.

   rewrite nth_cspace_none in H0; tryfalse.
   eauto.

   rewrite nth_cspace_none in H0; tryfalse.
   eauto.
   
   lets Hc1: nat_ltorge (Z.to_nat(Int.unsigned prio)) (length cspacevl).
   lets Hc2: nat_ltorge (Z.to_nat(Int.unsigned x)) (length cspacevl).
   lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned prio)) (Z.to_nat(Int.unsigned x)).
   destruct Hc1;    destruct Hc2;    destruct Hc3.

   rewrite nth_cspace_eq_nth_cspace_val.
   unfold nat_of_Z.
   rewrite H7 in *.
 
   assert(nth_cspace  (Z.to_nat(Int.unsigned x))
   (ACSpace_defs.update_nth_list cspace_val_type
   (Z.to_nat(Int.unsigned x)) cspacevl
    uval) = Some uval).
   eapply update_nth_cspace_eq; auto.
   subst uval. 
   (* rewrite update_nth_slots_eq_update_slots_type. *)
   rewrite update_nth_slots_eq_update_slots_type in H4.
   (* rewrite <-nth_cspace_eq_nth_cspace_val.
   fold nat_of_Z. *)
   rewrite H8.
   inverts H1.

   assert(prio = x).
   clear -H7.
   eapply Z2Nat.inj_iff in H7.
   apply unsigned_inj in H7.
   auto.
   int auto.
   int auto.
   rewrite H1 in H4.
   rewrite get_set_eq in H4.
   (* inverts H5. *)
   rewrite <-H1 in H2.

   lets Hx: H3  H2.
   destruct Hx. destruct H9. destruct H9. destruct H9. destruct H9.
   destruct H9.
   rewrite nth_cspace_eq_nth_cspace_val in H9.
   unfold nat_of_Z in H9.
   rewrite H7 in H9. 

   inverts H4.
   rewrite H9 in H0.
   inverts H0.
   (* rewrite H1 in H5. *)
   eexists.  eexists.  eexists.  eexists.  eexists.
   split.
   eauto.
   eauto.

   assert( nth_cspace
   (Z.to_nat (Int.unsigned prio))
   (ACSpace_defs.update_nth_list cspace_val_type
   (Z.to_nat(Int.unsigned x))
     cspacevl
           uval) = nth_cspace
     (Z.to_nat (Int.unsigned prio)) cspacevl).
   eapply update_nth_cspace_neqrev; auto.
   subst uval.
   rewrite nth_cspace_eq_nth_cspace_val.
   unfold nat_of_Z.
   rewrite H8.

   rewrite map_get_set' in H4; eauto.

   rewrite <-nth_cspace_eq_nth_cspace_val.
   fold nat_of_Z.
   eapply H3.
   eauto.
   lets Hx: Int.eq_dec x prio.
   destruct Hx. subst x. lia.
   auto.
   
   rewrite <- H7 in H6. lia.
   eapply nth_cspace_none in H6.
   
   lets Hx: H3 H2.
   simpljoin.
   rewrite nth_cspace_eq_nth_cspace_val in H8.
   unfold nat_of_Z in H8.
   rewrite H6 in H8. tryfalse.
   rewrite map_get_set' in H4; eauto.
   eapply nth_cspace_none in H5.
   lets Hx: H3 H4.
   simpljoin.
   rewrite nth_cspace_eq_nth_cspace_val in H8.
   unfold nat_of_Z in H8.
   rewrite H8 in H5. tryfalse.
   lets Hx: Int.eq_dec x prio.
   destruct Hx. subst x. lia. auto.
   rewrite map_get_set' in H4; eauto.
   eapply nth_cspace_none in H5.
   lets Hx: H3 H4.
   simpljoin.
   rewrite nth_cspace_eq_nth_cspace_val in H8.
   unfold nat_of_Z in H8.
   rewrite H8 in H5. tryfalse.
   lets Hx: Int.eq_dec x prio.
   destruct Hx. subst x. lia. auto.
   lets Hx: H3 H2.
   simpljoin.
   eapply nth_cspace_none in H6.
   unfold nat_of_Z in H8.
   rewrite nth_cspace_eq_nth_cspace_val in H8.
   rewrite H6 in H8. tryfalse.
   lets Hx: H3 H2.
   simpljoin.
   eapply nth_cspace_none in H6.
   unfold nat_of_Z in H8.
   rewrite nth_cspace_eq_nth_cspace_val in H8.
   rewrite H6 in H8. tryfalse.
   tryfalse.
Qed.





Lemma RLH_CapParent_update_slots_type_remain: 
forall cspacevl vl32 vl20 x y v p a b slots c d e f type x2 x3,
RLH_CapParent vl32 vl20 ->
nth_cspace (Z.to_nat(Int.unsigned x)) cspacevl = Some((a, b, slots), c, d, e, f) ->
ACSpace_defs.nth_slots y slots = Some(type, p) ->
get vl20 x = Some (slots, x2, x3) ->
RLH_CapParent vl32
(set vl20 x ((update_nth_slots y slots (v, p), x2, x3))).
Proof.
intros.
destruct (ACSpace_defs.nth_slots y slots).

{
  unfold RLH_CapParent in *. 
  destruct H. 
  splits; intros.
  lets Hc1: nat_ltorge (Z.to_nat(Int.unsigned prio)) (length cspacevl).
  lets Hc2: nat_ltorge (Z.to_nat(Int.unsigned x)) (length cspacevl).
  lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned prio)) (Z.to_nat(Int.unsigned x)).
  destruct Hc1;    destruct Hc2;    destruct Hc3.

  lets Hx: H H4.
  destruct Hx.   destruct H8.

  assert(prio = x).
  clear -H7.
  eapply Z2Nat.inj_iff in H7.
  apply unsigned_inj in H7.
  auto.
  int auto.
  int auto.
  rewrite H9 in *.
  rewrite H8 in H2.
  inverts H2.
  (* rewrite update_nth_slots_eq_update_slots_type. *)

  eexists. eexists. 
  eapply get_set_eq.
  eauto.


  lets Hx: H H4.
  destruct Hx.   destruct H8. 
  eexists. eexists. 
  eapply get_set_neq.
  intro.
  rewrite H9 in H7. 
  tryfalse.
  eauto.

  lia.

  rewrite nth_cspace_none in H0; tryfalse.
  eauto.

  lia.
  lets Hx: H H4.
  simpljoin. 
  do 2 eexists.
  rewrite map_get_set'; eauto. 
  lets Hx: Int.eq_dec x prio.
  destruct Hx. subst x. lia. auto. 
  eapply nth_cspace_none in H6.
  rewrite H0 in H6. tryfalse.
  eapply nth_cspace_none in H6.
  rewrite H0 in H6. tryfalse.

  lets Hc1: nat_ltorge (Z.to_nat(Int.unsigned prio)) (length cspacevl).
  lets Hc2: nat_ltorge (Z.to_nat(Int.unsigned x)) (length cspacevl).
  lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned prio)) (Z.to_nat(Int.unsigned x)).
  destruct Hc1;    destruct Hc2;    destruct Hc3.

  assert(prio = x).
  clear -H7.
  eapply Z2Nat.inj_iff in H7.
  apply unsigned_inj in H7.
  auto.
  int auto.
  int auto.
  rewrite H8 in H4.
  rewrite get_set_eq in H4.

  rewrite <-H8 in H2.

  lets Hx: H3 H2.

  inverts H4.
  eauto.

  eapply H3.
  eauto.
  instantiate(1:= plv).
  instantiate(1:= slots0).
  rewrite <- H4.
  eapply eq_sym.
  eapply CSpaceMod.map_get_set'.
  intro.
  rewrite H8 in H7. 
  tryfalse.

  lia.


  rewrite nth_cspace_none in H0. tryfalse.
  eauto.

  lia.
(*需要加上前提ength cspacevl = 64%nat*)
  rewrite map_get_set' in H4. 
  eapply H3; eauto. 
  lets Hx: Int.eq_dec x prio. destruct Hx;tryfalse; auto. 
  eapply nth_cspace_none in H6. 
  rewrite H0 in H6. tryfalse. 
  eapply nth_cspace_none in H6. 
  rewrite H0 in H6. tryfalse. 
  }
  tryfalse.
Qed.

Lemma RLH_CapParent_update_slots_cap_remain: 
forall cspacevl vl32 vl20 x y v p a b slots c d e f type x2 x3,
RLH_CapParent vl32 vl20 ->
nth_cspace (Z.to_nat(Int.unsigned x)) cspacevl = Some((a, b, slots), c, d, e, f) ->
ACSpace_defs.nth_slots y slots = Some(type, p) ->
get vl20 x = Some (slots, x2, x3) ->
RLH_CapParent vl32
(set vl20 x ((update_nth_slots y slots (type, v), x2, x3))).
Proof.
intros.
destruct (ACSpace_defs.nth_slots y slots).
{
  unfold RLH_CapParent in *. 
  destruct H. 
  splits; intros.
  lets Hc2: nat_ltorge (Z.to_nat(Int.unsigned x)) (length cspacevl).
  lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned prio)) (Z.to_nat(Int.unsigned x)).
  destruct Hc2;    destruct Hc3.

  lets Hx: H H4.
  destruct Hx.   destruct H7.

  assert(prio = x).
  clear -H6.
  eapply Z2Nat.inj_iff in H6.
  apply unsigned_inj in H6.
  auto.
  int auto.
  int auto.
  rewrite H8 in *.
  rewrite H7 in H2.
  inverts H2.

  eexists. eexists. 
  eapply get_set_eq.

  lets Hx: H H4.
  destruct Hx.   destruct H7. 
  eexists. eexists. 
  eapply get_set_neq.
  intro.
  rewrite H8 in H7. 
  tryfalse.
  eauto.
 
  
  rewrite nth_cspace_none in H0; tryfalse.
  lia.
  lets Hx: H H4.
  simpljoin. 
  do 2 eexists. rewrite map_get_set'; eauto. 
  lets Hx: Int.eq_dec x prio.
  destruct Hx. subst x. lia. auto. 

  lets Hc2: nat_ltorge (Z.to_nat(Int.unsigned x)) (length cspacevl).
  lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned prio)) (Z.to_nat(Int.unsigned x)).
  destruct Hc2;    destruct Hc3.

  assert(prio = x).
  clear -H6.
  eapply Z2Nat.inj_iff in H6.
  apply unsigned_inj in H6.
  auto.
  int auto.
  int auto.
  rewrite H7 in H4.
  rewrite get_set_eq in H4.

  rewrite <-H7 in H2.
  lets Hx: H3  H2.
  inverts H4.
  eauto.
  eapply H3.
  eauto.
  instantiate(1:= plv).
  instantiate(1:= slots0).
  rewrite <- H4.
  eapply eq_sym.
  eapply CSpaceMod.map_get_set'.
  intro.
  rewrite H7 in H6. 
  tryfalse.
  eapply Z2Nat.inj_iff in H6.
  apply unsigned_inj in H6. subst prio.
  rewrite get_set_eq in H4. 
  inverts H4. 
  eapply H3; eauto.
  int auto. int auto. 
  assert(prio <> x).
  lets Hx: Int.eq_dec prio x.
  destruct Hx. subst prio. lia.
  auto. 
  rewrite map_get_set' in H4; eauto. 
  }
  tryfalse.
Qed.


Lemma retpost_CheckCapTypeWeakPost:
  retpost Check_Cap_TypeWeakPost.
Proof.
  unfolds.
  intros.
  unfold getasrt in H.
  unfold Check_Cap_TypeWeakPost in H. 
  unfold Check_Cap_TypePost'' in H. 
  sep normal in H. sep destruct H. 
  sep lift 20%nat in H. 
  eapply disj_split in H. 
  destruct H. 
  sep split in H.
  rewrite H0. auto.
  sep split in H.
  simpljoin1. auto.
Qed.


Lemma Capability_wellform_descendents_update_type: 
  forall x y l v map,
  Capability_wellform_descendents l map ->
  Capability_wellform_descendents (update_nth_cspace_slots_type x y l v) map.
Proof.
  unfold Capability_wellform_descendents.
  intros.
  eapply H in H0.
  simpljoin.
  exists x0.
  assert(child_similar l (update_nth_cspace_slots_type x y l v)).
  intros. 

  unfold update_nth_cspace_slots_type.
  destruct (nth_cspace x l) eqn: Hxl.
  destruct c,p,p,p,c,p.
  destruct ( ACSpace_defs.nth_slots y l1 ) eqn: Hyl1.
  destruct p. 
  {
    remember ((i1, i2, ACSpace_defs.update_nth_list slot_val_type y l1 (v, p), i0, l0,
    v0, i)) as uval.
    unfold child_similar. 
    intros.
    lets Hc1: nat_ltorge (Z.to_nat(Int.unsigned node)) (length l).
    lets Hc2: nat_ltorge (x) (length l).
    lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned node)) (x).
    destruct Hc1; destruct Hc2; destruct Hc3.
    unfold child.
    rewrite H3 in *.
    rewrite Hxl.
    rewrite update_nth_cspace_eq; auto.
    subst uval. auto.
    rewrite update_nth_cspace_neqrev; eauto.
    eapply update_nth_cspace_remain with(v:= uval)in H2. 
    rewrite H2 in *; auto.
    eapply update_nth_cspace_remain with(v:= uval)in H2. 
    rewrite H2 in *; auto.
    rewrite nth_cspace_none; eauto.
    rewrite nth_cspace_none; eauto.
    rewrite update_nth_list_len_eq; auto.
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto.

    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto.
  }
  unfolds. intros. auto.
  unfolds. intros. auto.
  eapply wellform_descendents_child_similar; eauto.
Qed.

Lemma Capability_wellform_descendents_update_cap: 
  forall x y l v map,
  Capability_wellform_descendents l map ->
  Capability_wellform_descendents (update_nth_cspace_slots_cap x y l v) map.
Proof.
  unfold Capability_wellform_descendents.
  intros.
  eapply H in H0.
  simpljoin.
  exists x0.
  assert(child_similar l (update_nth_cspace_slots_cap x y l v)).
  intros. 

  unfold update_nth_cspace_slots_cap.
  destruct (nth_cspace x l) eqn: Hxl.
  destruct c,p,p,p,c,p.
  destruct ( ACSpace_defs.nth_slots y l1 ) eqn: Hyl1.
  destruct p. 
  {
    remember ((i1, i2, ACSpace_defs.update_nth_list slot_val_type y l1 (i3, v), i0, l0,
    v0, i)) as uval.
    unfold child_similar. 
    intros.
    lets Hc1: nat_ltorge (Z.to_nat(Int.unsigned node)) (length l).
    lets Hc2: nat_ltorge (x) (length l).
    lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned node)) (x).
    destruct Hc1; destruct Hc2; destruct Hc3.
    unfold child.
    rewrite H3 in *.
    rewrite Hxl.
    rewrite update_nth_cspace_eq; auto.
    subst uval. auto.
    rewrite update_nth_cspace_neqrev; eauto.
    eapply update_nth_cspace_remain with(v:= uval)in H2. 
    rewrite H2 in *; auto.
    eapply update_nth_cspace_remain with(v:= uval)in H2. 
    rewrite H2 in *; auto.
    rewrite nth_cspace_none; eauto.
    rewrite nth_cspace_none; eauto.
    rewrite update_nth_list_len_eq; auto.
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto.

    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto.
  }
  unfolds. intros. auto.
  unfolds. intros. auto.
  eapply wellform_descendents_child_similar; eauto.
Qed.



Scheme reset_descendents_cspace_slot_abs_mut :=
  Induction for reset_descendents_cspace_slot_abs Sort Prop
with
  reset_descendents_cspace_list_slot_abs_mut :=
  Induction for reset_descendents_cspace_list_slot_abs Sort Prop.

Scheme wellform_descendents_abs :=
  Induction for wellform_descendents_abs Sort Prop
with
  wellform_descendents_list_abs_mut :=
  Induction for wellform_descendents_list_abs Sort Prop.

(********************************分割线*************************)
Lemma  update_nth_list_same:
  forall type l x  a b,
  ACSpace_defs.update_nth_list type x (ACSpace_defs.update_nth_list type x l b) a =
  ACSpace_defs.update_nth_list type x l a. 
Proof.
    induction l; destruct x; intros.
    simpl. auto.
    simpl. auto.
    simpl. auto.
    simpl.
    lets Hx: IHl x a0 b. 
    rewrite Hx. auto.
Qed.



Lemma update_nth_cspace_slot_cap_type_trans: 
forall node ls ls1 i1 i2 (l0: list slot_val_type) i0 l v i n_class l0 i3 i4 i5 i6 v0 a b c d,
nth_cspace (Z.to_nat (Int.unsigned node)) ls =
      Some (i1, i2, l0, i0, l, v, i)->
ACSpace_defs.nth_slots n_class l0 =Some (i3, (i4, (i5, i6, v0))) ->
ACSpace_defs.update_nth_list
       cspace_val_type(Z.to_nat(Int.unsigned node)) ls
       (i1, i2,ACSpace_defs.update_nth_list
         slot_val_type n_class l0 ($ SLOT_NULL_CAP,(a,
         (b, c, d))),
i0, l, v, i) = ls1 ->
ls1 = update_nth_cspace_slots_type (Z.to_nat(Int.unsigned node)) n_class
(update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned node)) n_class  ls (a, (b, c, d)))($SLOT_NULL_CAP).
Proof.
  intros.
  lets Hx: nat_ltorge n_class (length l1).
  lets Hy: nat_ltorge (Z.to_nat (Int.unsigned node)) (length ls).
  destruct Hx; destruct Hy.
  unfold update_nth_cspace_slots_cap. 
  rewrite H. rewrite H0.
  unfold update_nth_cspace_slots_type.
  rewrite update_nth_cspace_eq; eauto.
  rewrite update_nth_slots_eq; eauto.
  auto.
  rewrite update_nth_list_same.
  rewrite update_nth_list_same.  auto.
  rewrite nth_cspace_none in H; auto.
  tryfalse.
  rewrite nth_slots_none in H0; auto. tryfalse.
  rewrite nth_cspace_none in H; auto.
  tryfalse.
Qed.

Lemma update_nth_list_eq_update_nth_slots: 
  forall l x  v, 
  update_nth_list slot_val_type x l v = update_nth_slots x l v.
Proof.
  induction l; destruct x; intros;simpl; auto.
  lets Hx: IHl x v.
  rewrite Hx. auto.
Qed.

Lemma nth_slots_exists:
  forall vl n,
  (n < (length vl))%nat ->
  exists v, nth_slots n vl = Some v.
Proof.
  induction vl; destruct n;intros.
  simpl in H. lia. 
  simpl in H. lia.
  eexists. simpl. eauto. 
  simpl in H. 
  assert(n < (length vl))%nat by lia.
  eapply IHvl in H0.
  destruct H0.
  exists x. 
  simpl. auto.
Qed. 



Lemma reset_nth_cspace_RLH_cspace_slots_P_keep: 
  forall node class ls ls1 map pl acspace acspace' n_class,
  reset_nth_cspace_slot_option node class n_class ls ls1 ->
  reset_nth_cspace_slot_ucos_option node (Int.repr (Z.of_nat class)) n_class acspace acspace' ->
  RLH_cspace_slots_P ls acspace map pl ->
  RLH_cspace_slots_P ls1 acspace' map pl.
Proof.
  intros.
  unfolds in H. 
  unfolds in H0.
  simpljoin.
  clear H0.
  unfolds in H.
  destruct H.
  subst n_class.
  assert((0 <=? Z.to_nat SLOT_NUM)%nat &&
  (Z.to_nat SLOT_NUM <?
  Z.to_nat SLOT_NUM)%nat = false).
  unfold SLOT_NUM. int auto. 
  rewrite H in H3, H2.
  subst acspace'. subst ls1.
  auto.
  assert((0 <=? n_class)%nat = true).
  clear -H. int auto.
  assert((n_class <? Z.to_nat SLOT_NUM)%nat = true).
  eapply Nat.ltb_lt. lia.
  rewrite H0, H4 in H3, H2.
  simpl in H2, H3.
  unfolds in H3.
  destruct (nth_cspace
  (Z.to_nat (Int.unsigned node)) ls) eqn: Hls.
  destruct c, p, p, p, c, p.
  assert(Hltnode: ((Z.to_nat (Int.unsigned node)) < length ls)%nat).
  {
    lets Hx: nat_ltorge ((Z.to_nat (Int.unsigned node))) (length ls).
    destruct Hx; auto.
    rewrite nth_cspace_none in Hls; tryfalse. auto.
  }
  destruct (ACSpace_defs.nth_slots n_class l0) eqn: Hslots.
  destruct p, p, c, p.
  assert(Hltn_class: (n_class < (length l0))%nat).
  {
    lets Hx: nat_ltorge (n_class) (length l0).
    destruct Hx; auto.
    rewrite nth_slots_none in Hslots; tryfalse.
    auto.
  }
  inversion H2.
  subst acspace'.
  unfolds in H1.
  destruct H1.
  rewrite <- nth_cspace_eq_nth_cspace_val in Hls.
  lets Hx: H1 Hls.
  simpljoin.
  unfold get in H10. simpl in H10.
  rewrite H5 in H10. tryfalse.
  subst acspace'.
  unfolds in H1.
  destruct H1.
  rewrite <- nth_cspace_eq_nth_cspace_val in Hls.
  lets Hx: H1 Hls.
  simpljoin.
  unfold get in H11. simpl in H11.
  rewrite H5 in H11. tryfalse.
  inverts H11. 
  rewrite Int.unsigned_repr in H6.
  rewrite Nat2Z.id in H6.
  eapply nth_slots_exists in Hltn_class.
  destruct Hltn_class. 
  rewrite H3 in H6. tryfalse.
  clear -H H14. unfold SLOT_NUM in *.
  rewrite max_unsigned_val. lia.
  assert(l0 = slots).
  clear -Hls H5 H1 Hltnode.
  rewrite <- nth_cspace_eq_nth_cspace_val in Hls.
  unfolds in H1. destruct H1.
  lets Hx: H Hls.
  simpljoin.
  unfold get in H1. simpl in H1.
  rewrite H1 in H5. inverts H5. auto.
  subst slots.
  rewrite Int.unsigned_repr in H6.
  rewrite Nat2Z.id in H6.
  rewrite <- nth_slots_eq_nth_slots in Hslots.
  rewrite Hslots in H6. inverts H6.
  2:{
    clear -H.
    unfold SLOT_NUM in H. rewrite max_unsigned_val. lia.
  }
  rewrite H7 in H3.
  eapply update_nth_cspace_slot_cap_type_trans in H3; eauto.
  subst ls1.
  
  subst cap.  subst acspace0.
  subst node.
  unfold Int.zero. 
  rewrite Int.unsigned_repr.
  rewrite Nat2Z.id.
  rewrite update_nth_list_eq_update_nth_slots.
  rewrite update_nth_list_eq_update_nth_slots.
  eapply RLH_cspace_slots_P_update_slots_type_remain; eauto.
  eapply RLH_cspace_slots_P_update_slots_cap_remain; eauto.
  unfold update_nth_cspace_slots_cap.
  rewrite Hls.
  rewrite nth_slots_eq_nth_slots in Hslots.
  rewrite Hslots.
  rewrite update_nth_cspace_eq.
  rewrite update_nth_slots_eq_update_slots_type.
  eauto.
  lia. 
  rewrite  update_nth_slots_eq_update_slots_type.
  rewrite update_nth_slots_eq; eauto.
  rewrite get_set_eq. eauto.
  unfold update_nth_cspace_slots_cap.
  clear -H. unfold SLOT_NUM in *. rewrite max_unsigned_val. lia.
  tryfalse.

  assert(l0 = slots).
  clear -Hls H5 H1 Hltnode.
  rewrite <- nth_cspace_eq_nth_cspace_val in Hls.
  unfolds in H1. destruct H1.
  lets Hx:  H Hls.
  simpljoin.
  unfold get in H1. simpl in H1.
  rewrite H1 in H5. inverts H5. auto.
  subst slots.
  rewrite Int.unsigned_repr in H6.
  rewrite Nat2Z.id in H6.
  rewrite <- nth_slots_eq_nth_slots in Hslots.
  rewrite Hslots in H6. inverts H6.
  2:{
    clear -H.
    unfold SLOT_NUM in H. rewrite max_unsigned_val. lia.
  }
  assert(Int.eq cap_type ($CAP_CATEGORY_TYPE) = false).
  clear -H7. unfold CAP_CATEGORY_TYPE.
  unfold CAP_OBJECT_TYPE in H7. int auto.
  rewrite H6, H7 in H3.
  eapply update_nth_cspace_slot_cap_type_trans in H3; eauto.
  subst ls1.
  
  subst cap.  subst acspace0.
  subst node.
  unfold Int.zero. 
  rewrite Int.unsigned_repr.
  rewrite Nat2Z.id.
  rewrite update_nth_list_eq_update_nth_slots.
  rewrite update_nth_list_eq_update_nth_slots.
  eapply RLH_cspace_slots_P_update_slots_type_remain; eauto.
  eapply RLH_cspace_slots_P_update_slots_cap_remain; eauto.
  unfold update_nth_cspace_slots_cap.
  rewrite Hls.
  rewrite nth_slots_eq_nth_slots in Hslots.
  rewrite Hslots.
  rewrite update_nth_cspace_eq.
  rewrite update_nth_slots_eq_update_slots_type.
  eauto.
  lia. 
  rewrite  update_nth_slots_eq_update_slots_type.
  rewrite update_nth_slots_eq; eauto.
  rewrite get_set_eq. eauto.
  unfold update_nth_cspace_slots_cap.
  clear -H. unfold SLOT_NUM in *. rewrite max_unsigned_val. lia.
  
  assert(l0 = slots).
  clear -Hls H5 H1 Hltnode.
  rewrite <- nth_cspace_eq_nth_cspace_val in Hls.
  unfolds in H1. destruct H1.
  lets Hx: H Hls.
  simpljoin.
  unfold get in H1. simpl in H1.
  rewrite H1 in H5. inverts H5. auto.
  subst l0.
  rewrite Int.unsigned_repr in H6.
  rewrite Nat2Z.id in H6.
  rewrite nth_slots_eq_nth_slots in H6.
  rewrite H6 in Hslots. inverts Hslots.
  rewrite H7, H8 in H3.
  eapply update_nth_cspace_slot_cap_type_trans in H3; eauto.
  subst ls1.
  rewrite Int.unsigned_repr.
  rewrite Nat2Z.id.
  rewrite <- update_nth_slots_eq_update_slots_type_NoA.
  rewrite <- update_nth_slots_eq_update_slots_type_NoA.
  eapply RLH_cspace_slots_P_update_slots_type_remain; eauto.
  eapply RLH_cspace_slots_P_update_slots_cap_remain; eauto.
  unfold update_nth_cspace_slots_cap.
  rewrite Hls.
  rewrite H6.
  rewrite update_nth_cspace_eq.
  rewrite update_nth_slots_eq_update_slots_type.
  eauto.
  lia. 
  rewrite  update_nth_slots_eq_update_slots_type.
  rewrite update_nth_slots_eq; eauto.
  rewrite get_set_eq. eauto.
  unfold update_nth_cspace_slots_cap.
  clear -H. unfold SLOT_NUM in *. rewrite max_unsigned_val. lia.
  clear -H. unfold SLOT_NUM in *. rewrite max_unsigned_val. lia.
  

  inversion H2.
  subst acspace'.
  unfolds in H1.
  destruct H1.
  rewrite <- nth_cspace_eq_nth_cspace_val in Hls.
  lets Hx: H1 Hls.
  simpljoin.
  unfold get in H10. simpl in H10.
  rewrite H5 in H10. tryfalse.
  subst acspace'. subst ls1.
  auto.
  unfolds in H1.
  destruct H1.
  rewrite <- nth_cspace_eq_nth_cspace_val in Hls.
  lets Hx: H1 Hls.
  simpljoin.
  unfold get in H13. simpl in H13.
  rewrite H5 in H13. inverts H13.
  rewrite Int.unsigned_repr in H6.
  rewrite Nat2Z.id in H6.
  rewrite nth_slots_eq_nth_slots in H6.
  rewrite Hslots in H6. tryfalse.
  clear -H H16.
  unfold SLOT_NUM in H16. rewrite max_unsigned_val. lia.
  unfolds in H1.
  destruct H1.
  rewrite <- nth_cspace_eq_nth_cspace_val in Hls.
  lets Hx: H1 Hls.
  simpljoin.
  unfold get in H13. simpl in H13.
  rewrite H5 in H13. inverts H13.
  rewrite Int.unsigned_repr in H6.
  rewrite Nat2Z.id in H6.
  rewrite nth_slots_eq_nth_slots in H6.
  rewrite Hslots in H6. tryfalse.
  clear -H H16.
  unfold SLOT_NUM in H16. rewrite max_unsigned_val. lia.
  unfolds in H1.
  destruct H1.
  rewrite <- nth_cspace_eq_nth_cspace_val in Hls.
  lets Hx: H1 Hls.
  simpljoin.
  unfold get in H14. simpl in H14.
  rewrite H5 in H14. inverts H14.
  rewrite Int.unsigned_repr in H6.
  rewrite Nat2Z.id in H6.
  rewrite nth_slots_eq_nth_slots in H6.
  rewrite Hslots in H6. tryfalse.
  clear -H H17.
  unfold SLOT_NUM in H17. rewrite max_unsigned_val. lia.
  subst ls1.
  
  assert(CSpaceMod.get acspace node = None).
  unfolds in H1.
  destruct H1.
  lets Hx: CSpaceMod.get_dec acspace node.
  destruct Hx.
  destruct e.
  destruct x. destruct p.
  eapply H3 in H5.
  do 5 destruct H5.
  destruct H5.
  rewrite nth_cspace_eq_nth_cspace_val in H5.
  clear -Hls H5.
  unfold nat_of_Z in H5.
  rewrite Hls in H5. tryfalse. auto.

  inversion H2. subst acspace'. auto. 
  subst acspace'. auto. 
  rewrite H3 in H5. tryfalse.
  rewrite H3 in H5. tryfalse.
  rewrite H3 in H5. tryfalse.
Qed.

(*low level to high level*)
Lemma reset_nth_cspace_slot_ucos_option_exists:
  forall node class n_class ls ls1 map pl acspace,
  reset_nth_cspace_slot_option node class n_class ls ls1 ->
  RLH_cspace_slots_P ls acspace map pl ->
  (exists acspace', reset_nth_cspace_slot_ucos_option node (Int.repr (Z.of_nat class)) n_class acspace
  acspace').
Proof.
  intros.
  unfolds in H.
  simpljoin.
  unfolds in H. destruct H.
  subst n_class.
  assert( (0 <=? Z.to_nat SLOT_NUM)%nat &&
  (Z.to_nat SLOT_NUM <?
   Z.to_nat SLOT_NUM)%nat = false). unfold SLOT_NUM.
  int auto.
  rewrite H in H1. subst ls1. 
  exists acspace. 
  unfold reset_nth_cspace_slot_ucos_option.
  splits. unfolds. eauto.
  rewrite H. auto.
  assert((0 <=? n_class)%nat = true). unfold SLOT_NUM in *.
  int auto.
  assert((n_class <? Z.to_nat SLOT_NUM)%nat = true).
  unfold SLOT_NUM in *. 
  eapply Nat.ltb_lt. lia. rewrite H2, H3 in H1.
  simpl in H1.
  unfolds in H1.
  destruct (nth_cspace(Z.to_nat(Int.unsigned node))
  ls) eqn: Hcspace.
  destruct c, p, p, p, c, p.
  lets Hcspace_bak: Hcspace.
  rewrite <- nth_cspace_eq_nth_cspace_val in Hcspace_bak.
  unfolds in H0. destruct H0.
  eapply H0 in Hcspace_bak.
  destruct Hcspace_bak. destruct H5.
  destruct H5. unfolds in H5. simpl in H5.
  destruct (ACSpace_defs.nth_slots
  n_class l0) eqn: Hslots.
  destruct p, p, c, p.
  
  destruct (Int.eq i4 ($ CAP_CATEGORY_TYPE)) eqn: Hcap.
  eexists. splits. unfolds. auto.
  rewrite H2, H3. simpl.
  eapply reset_nth_cspace_slot_ucos_category; eauto.
  rewrite Int.unsigned_repr. rewrite Nat2Z.id.
  eauto. clear -H.
  unfold SLOT_NUM in *. rewrite max_unsigned_val. lia.
  destruct (Int.eq i4 ($ CAP_OBJECT_TYPE)) eqn: Hobj.
  eexists. splits. unfolds. auto.
  rewrite H2, H3. simpl.
  eapply reset_nth_cspace_slot_ucos_object; eauto.
  rewrite Int.unsigned_repr. rewrite Nat2Z.id. eauto.
  clear -H. unfold SLOT_NUM in *. rewrite max_unsigned_val. lia.
  eexists. splits. unfolds. eauto.
  rewrite H2, H3. simpl.
  eapply reset_nth_cspace_slot_ucos_nocapobj; eauto.
  rewrite Int.unsigned_repr. rewrite Nat2Z.id. eauto.
  clear -H. unfold SLOT_NUM in *. rewrite max_unsigned_val. lia.
  eexists. split. eauto. unfolds. eauto.
  
  rewrite H2, H3. simpl.
  eapply reset_nth_cspace_slot_ucos_none_slots; eauto.
  rewrite Int.unsigned_repr. rewrite Nat2Z.id. 
  rewrite nth_slots_eq_nth_slots. eauto.
  clear -H. unfold SLOT_NUM in *. rewrite max_unsigned_val. lia.
  unfolds in H0.
  destruct H0.
  assert(CSpaceMod.get acspace node = None).
  lets Hx: CSpaceMod.get_dec acspace node.
  destruct Hx. destruct e. 
  destruct x. destruct p.
  eapply H4 in H5. simpljoin.
  unfold nat_of_Z in H5.
  rewrite nth_cspace_eq_nth_cspace_val in H5.
  rewrite Hcspace in H5.  tryfalse.
  auto.
  eexists. splits. unfolds; eauto.
  rewrite H2, H3.
  eapply reset_nth_cspace_slot_ucos_none_cspace; eauto.
Qed.

Lemma reset_nth_cspace_slot_option_RLH_cspace_slots_P:
  forall node class n_class ls ls1 map pl acspace,
  reset_nth_cspace_slot_option node class n_class ls ls1 ->
  RLH_cspace_slots_P ls acspace map pl->
  exists acspace', RLH_cspace_slots_P ls1 acspace' map pl/\
  reset_nth_cspace_slot_ucos_option node (Int.repr (Z.of_nat class)) n_class acspace
  acspace'.
Proof. 
  intros.
  lets Hx: reset_nth_cspace_slot_ucos_option_exists H H0.
  destruct Hx.
  eexists.
  splits.
  eapply reset_nth_cspace_RLH_cspace_slots_P_keep; eauto.
  auto.
Qed.
Lemma reset_descendents_cspace_slot_exists_acspace': 
  forall  dest cap cspacels  vl vl',
  reset_descendents_cspace_slot dest cap cspacels vl vl' ->
  forall acspace pl,
  RLH_cspace_slots_P vl acspace cspacels pl->
  (exists acspace', RLH_cspace_slots_P vl' acspace' cspacels pl).
Proof.

  apply (reset_descendents_cspace_slot_mut
  (fun dest cap cspacels vl vl' 
    (pf1: reset_descendents_cspace_slot dest cap cspacels vl vl') 
    => 
    forall acspace pl,
    RLH_cspace_slots_P vl acspace cspacels pl->
    exists acspace', RLH_cspace_slots_P vl' acspace' cspacels pl)
  (fun dest cap cspacels vl vl'  
    (pf2: 
    reset_descendents_cspace_list_slot dest cap cspacels vl vl') 
    => forall acspace pl,
    RLH_cspace_slots_P vl acspace cspacels pl->
    exists acspace', RLH_cspace_slots_P vl' acspace' cspacels pl)
  ).
  intros.
  destruct e. 
  lets Hx: reset_nth_cspace_slot_option_RLH_cspace_slots_P H1 H0.
  destruct Hx.
  destruct H2. 
  eapply H in H2.
  eauto. 
  intros. eauto.
  intros.
  eapply H in H1.
  destruct H1.
  eapply H0 in H1.
  eauto.
Qed.
Lemma reset_descendents_cspace_slot_exists_acspace: 
  forall  dest cap cspacels pl vl vl' acspace,
  reset_descendents_cspace_slot dest cap cspacels vl vl' ->
  RLH_cspace_slots_P vl acspace cspacels pl->
  (exists acspace', RLH_cspace_slots_P vl' acspace' cspacels pl).
Proof.
  intros.
  eapply reset_descendents_cspace_slot_exists_acspace'; eauto.
Qed.

Lemma reset_descendents_cspace_list_slots_exists_acspace': 
  forall  dests cap cspacels pl vl vl',
  reset_descendents_cspace_list_slot dests cap cspacels vl vl' ->
  forall acspace,
  RLH_cspace_slots_P vl acspace cspacels pl ->
  (exists acspace', RLH_cspace_slots_P vl' acspace' cspacels pl).
Proof.
  induction dests; intros.
  eapply reset_descdents_list_nil in H.
  substs. eauto.
  inversion H. substs. 
  lets Hx: reset_descendents_cspace_slot_exists_acspace H3 H0.
  destruct Hx.
  lets Hx: IHdests H8 H1.
  eauto.
Qed.
Lemma reset_descendents_cspace_list_slots_exists_acspace: 
  forall  dests cap cspacels pl vl vl' acspace,
  reset_descendents_cspace_list_slot dests cap cspacels vl vl' ->
  RLH_cspace_slots_P vl acspace cspacels pl ->
  (exists acspace', RLH_cspace_slots_P vl' acspace' cspacels pl).
Proof.
  intros.
  eapply reset_descendents_cspace_list_slots_exists_acspace'; eauto.
Qed.

Lemma reverse_map_nil:
  forall  map,
  reverse_map map nil = nil.
Proof.
  intros. simpl. auto. 
Qed.
Lemma reverse_map_RLH_cspace_pris:
  forall childs x map ,
  RLH_cspace_pris_P childs x map ->
  childs = reverse_map map x .
Proof.
  induction childs; destruct x; intros.
  rewrite reverse_map_nil. auto. 
  unfolds in H. tryfalse.
  unfolds in H. tryfalse.
  unfolds in H. destruct v; tryfalse.
  destruct H. fold RLH_cspace_pris_P in H0.
  eapply IHchilds in H0.
  simpl. rewrite H. unfold int32_inj.
  rewrite H0. auto.
Qed.


Lemma child_abs_LRH: 
  forall childs ls acspace node map pl,
  RLH_cspace_slots_P ls acspace map pl->
  child_abs node childs acspace ->
  childs = (child node ls map).
Proof.
  intros.
  inversion H0.
  substs. 
  unfolds in H. destruct H. 
  eapply H2 in H1.
  simpljoin.
  rewrite nth_cspace_eq_nth_cspace_val in H1.
  unfold nat_of_Z in H1.
  unfold child. 
  rewrite H1. 
  eapply reverse_map_RLH_cspace_pris; eauto.
  unfolds in H.
  destruct H.
  unfold child.
  destruct (nth_cspace
  (Z.to_nat (Int.unsigned node)) ls) eqn: Hcspace.
  destruct c. destruct p. destruct p. destruct p.
  rewrite <-nth_cspace_eq_nth_cspace_val in Hcspace.
  unfold nat_of_Z in H.
  eapply H in Hcspace.
  destruct c. 
  simpljoin.
  unfold get in H6. simpl in H6.
  rewrite H1 in H6. tryfalse.
  auto.
Qed.

Axiom check_cap_type_LRH_rel_same: 
forall x x0 ls ls1 node class acspace acspace1 map pl,
reset_nth_cspace_slot_option node class x0 ls ls1 ->
reset_nth_cspace_slot_ucos_option node ($ Z.of_nat class) x
       acspace acspace1 ->
RLH_cspace_slots_P ls acspace map pl->
x = x0.





Lemma reset_descendents_LRH_keep':
  forall node class cspacels  ls ls1 ,
  reset_descendents_cspace_slot node class cspacels ls ls1 ->
  forall  pl acspace acspace'  ,
  reset_descendents_cspace_slot_abs node (Int.repr (Z.of_nat class)) acspace acspace' ->
  RLH_cspace_slots_P ls acspace cspacels pl->
  RLH_cspace_slots_P ls1 acspace' cspacels pl.
Proof.
  apply (reset_descendents_cspace_slot_mut
  (fun node class cspacels ls ls1 
    (pf1: reset_descendents_cspace_slot node class cspacels ls ls1) 
    => 
    forall  pl acspace acspace'  ,
    reset_descendents_cspace_slot_abs node (Int.repr (Z.of_nat class)) acspace acspace' ->
    RLH_cspace_slots_P ls acspace cspacels pl ->
    RLH_cspace_slots_P ls1 acspace' cspacels pl)
  (fun node class cspacels ls ls1   
    (pf2: 
    reset_descendents_cspace_list_slot node class cspacels ls ls1) 
    =>forall  pl acspace acspace'  ,
    reset_descendents_cspace_list_slot_abs node (Int.repr (Z.of_nat class)) acspace acspace' ->
    RLH_cspace_slots_P ls acspace cspacels pl->
    RLH_cspace_slots_P ls1 acspace' cspacels pl)
  ).
  intros.
  inversion H0. 
  substs.
  destruct H3.
  destruct e. 
  assert(x = x0).
  {
    eapply check_cap_type_LRH_rel_same; eauto. 
  }
  subst x0.
  lets Hx: reset_nth_cspace_RLH_cspace_slots_P_keep H5 H3 H1.
  assert(childs0 = child node ls map).
  eapply child_abs_LRH; eauto. 
  subst childs0.
  eapply H; eauto.
  intros. 
  inversion H. substs. auto.
  intros.
  inversion H1. substs.
  lets Hx: H H5 H2.
  eapply H0; eauto.
Qed. 

Lemma reset_descendents_LRH_keep:
  forall node class cspacels ls ls1 pl acspace acspace' ,
  reset_descendents_cspace_slot node class cspacels ls ls1 ->
  reset_descendents_cspace_slot_abs node (Int.repr (Z.of_nat class)) acspace acspace' ->
  RLH_cspace_slots_P ls acspace cspacels pl->
  RLH_cspace_slots_P ls1 acspace' cspacels pl.
Proof.
  intros.
  eapply reset_descendents_LRH_keep'; eauto.
Qed.
Lemma reset_descendents_cspace_slot_LRH': 
  forall  dest cap cspacels vl vl',
  reset_descendents_cspace_slot dest cap cspacels vl vl' ->
  forall acspace pl,
  RLH_cspace_slots_P vl acspace cspacels pl->
  exists acspace', reset_descendents_cspace_slot_abs dest (Int.repr (Z.of_nat cap)) acspace acspace'
  /\ RLH_cspace_slots_P vl' acspace' cspacels pl.
Proof.
  apply (reset_descendents_cspace_slot_mut
  (fun dest cap cspacels vl vl' 
    (pf1: reset_descendents_cspace_slot dest cap cspacels vl vl') 
    => 
    forall acspace pl,
    RLH_cspace_slots_P vl acspace cspacels pl->
    exists acspace', reset_descendents_cspace_slot_abs dest (Int.repr (Z.of_nat cap)) acspace acspace'
    /\ RLH_cspace_slots_P vl' acspace' cspacels pl)
  (fun dest cap cspacels vl vl'  
    (pf2: 
    reset_descendents_cspace_list_slot dest cap cspacels vl vl') 
    => forall acspace pl,
    RLH_cspace_slots_P vl acspace cspacels pl->
    exists acspace', reset_descendents_cspace_list_slot_abs dest (Int.repr (Z.of_nat cap)) acspace acspace'
    /\ RLH_cspace_slots_P vl' acspace' cspacels pl)
  ).
  intros.
  destruct e. 
  lets Hx: reset_nth_cspace_slot_option_RLH_cspace_slots_P H1 H0.
  destruct Hx. destruct H2.
  lets H2_bak: H2. 
  eapply H in H2_bak.
  destruct H2_bak.
  assert(child_abs node (child node ls map) acspace).
  unfold child.
  destruct  (nth_cspace
  (Z.to_nat (Int.unsigned node)) ls) eqn: Hcspace.
  destruct c, p, p, p. 
  unfolds in H0. 
  destruct H0. 
  rewrite <- nth_cspace_eq_nth_cspace_val in Hcspace.
  eapply H0 in Hcspace.
  destruct c. 
  simpljoin.
  eapply reverse_map_RLH_cspace_pris in H7.
  rewrite <- H7.
  eapply child_abs_rule; eauto.
  unfolds in H0. destruct H0. 
  lets Hx: CSpaceMod.get_dec acspace node.
  destruct Hx. destruct e.
  destruct x2. destruct p.
  eapply H5 in H6.
  simpljoin.
  rewrite nth_cspace_eq_nth_cspace_val in H6. rewrite Hcspace in H6.
  tryfalse. 
  eapply child_abs_rule_none; eauto.
  eexists.
  lets Hx: reset_descendents_cspace_slot_abs_rule H5 H4; eauto.
  splits; eauto. 
  destruct H4. auto.
  intros.
  eexists.
  splits.
  eapply reset_descendents_cspace_list_slot_abs_nil.
  auto.
  intros. 
  
  lets H1_bak: H1.
  eapply H in H1_bak.
  destruct H1_bak.
  lets Hx: reset_descendents_LRH_keep r H2 H1.
  eapply H0 in Hx.
  destruct Hx.
  destruct H3. 
  destruct H2.
  eexists.
  splits.
  eapply reset_descendents_cspace_list_slot_abs_cons; eauto.
  auto.
Qed.

Lemma reset_descendents_cspace_slot_LRH: 
  forall  dest cap cspacels vl vl' pl acspace,
  reset_descendents_cspace_slot dest cap cspacels vl vl' ->
  RLH_cspace_slots_P vl acspace cspacels pl->
  exists acspace', reset_descendents_cspace_slot_abs dest (Int.repr (Z.of_nat cap)) acspace acspace'
  /\ RLH_cspace_slots_P vl' acspace' cspacels pl.
Proof.
  intros.
  eapply reset_descendents_cspace_slot_LRH'; eauto.
Qed.

(*Capability_wellform_descendents*)
Lemma reset_nth_cspace_slot_option_wellform:
  forall node class x ls ls1 map,
  reset_nth_cspace_slot_option node class x ls ls1 ->
  Capability_wellform_descendents ls map ->
  Capability_wellform_descendents ls1 map.
Proof.
  intros.
  unfolds in H. 
  simpljoin.
  unfolds in H. destruct H.
  subst x. 
  assert((0 <=? Z.to_nat SLOT_NUM)%nat &&
  (Z.to_nat SLOT_NUM <?
   Z.to_nat SLOT_NUM)%nat = false).
  unfold SLOT_NUM. int auto.
  rewrite H in H1.
  subst ls1. auto.
  assert((0 <=? x)%nat = true).
  clear -H. unfold SLOT_NUM in H.  int auto.
  assert((x <? Z.to_nat SLOT_NUM)%nat = true).
  clear -H. unfold SLOT_NUM in *. 
  eapply Nat.ltb_lt; eauto. lia.
  rewrite H2, H3 in H1.
  simpl in H1.
  unfolds in H1.
  destruct (nth_cspace
  (Z.to_nat (Int.unsigned node))
  ls) eqn: Hcspace.
  destruct c,p,p,p,c,p.
  destruct ( ACSpace_defs.nth_slots x l0) eqn: Hslots.
  destruct p, p, c, p.
  destruct (Int.eq i4 ($ CAP_CATEGORY_TYPE)).
  lets Hx: update_nth_cspace_slot_cap_type_trans Hcspace Hslots H1; eauto.
  subst ls1.
  rewrite Hx.
  eapply Capability_wellform_descendents_update_type; eauto.
  eapply Capability_wellform_descendents_update_cap; eauto.
  destruct (Int.eq i4 ($ CAP_OBJECT_TYPE)).
  lets Hx: update_nth_cspace_slot_cap_type_trans Hcspace Hslots H1; eauto.
  subst ls1.
  rewrite Hx.
  eapply Capability_wellform_descendents_update_type; eauto.
  eapply Capability_wellform_descendents_update_cap; eauto.
  lets Hx: update_nth_cspace_slot_cap_type_trans Hcspace Hslots H1; eauto.
  subst ls1.
  rewrite Hx.
  eapply Capability_wellform_descendents_update_type; eauto.
  eapply Capability_wellform_descendents_update_cap; eauto.
  subst ls1. auto. 
  subst ls1. auto.
Qed.

Lemma reset_descendents_cspace_slot_abs_Capability_wellform_descendents_keep': 
  forall  node class cspacels ls ls1,
  reset_descendents_cspace_slot node class cspacels ls ls1 ->
  forall acspace acspace' pl,
  RLH_cspace_slots_P ls acspace cspacels pl->
  RLH_cspace_slots_P ls1 acspace' cspacels pl->
  Capability_wellform_descendents ls cspacels ->
  Capability_wellform_descendents ls1 cspacels.
Proof.
  apply (reset_descendents_cspace_slot_mut
  (fun node class cspacels ls ls1
    (pf1: reset_descendents_cspace_slot node class cspacels ls ls1) 
    => 
    forall acspace acspace' pl,
    RLH_cspace_slots_P ls acspace cspacels pl->
    RLH_cspace_slots_P ls1 acspace' cspacels pl->
    Capability_wellform_descendents ls cspacels ->
    Capability_wellform_descendents ls1 cspacels)
  (fun node class cspacels ls ls1   
    (pf2: 
    reset_descendents_cspace_list_slot node class cspacels ls ls1) 
    => forall acspace acspace' pl,
    RLH_cspace_slots_P ls acspace cspacels pl->
    RLH_cspace_slots_P ls1 acspace' cspacels pl->
    Capability_wellform_descendents ls cspacels ->
    Capability_wellform_descendents ls1 cspacels)
  ).
  intros.
  destruct e. 
  lets Hx: reset_nth_cspace_slot_ucos_option_exists H3 H0.
  destruct Hx.
  lets Hy: reset_nth_cspace_RLH_cspace_slots_P_keep H3 H4 H0.
  eapply H; eauto.
  eapply reset_nth_cspace_slot_option_wellform; eauto.
  intros. auto.
  intros.
  lets Hx: reset_descendents_cspace_slot_LRH r H1.
  destruct Hx. 
  destruct H4.
  eapply H0; eauto.
Qed.
Lemma reset_descendents_cspace_slot_abs_Capability_wellform_descendents_keep: 
  forall  node class cspacels ls ls1 acspace acspace' pl,
  reset_descendents_cspace_slot node class cspacels ls ls1 ->
  RLH_cspace_slots_P ls acspace cspacels pl->
  RLH_cspace_slots_P ls1 acspace' cspacels pl->
  Capability_wellform_descendents ls cspacels ->
  Capability_wellform_descendents ls1 cspacels.
Proof.
  intros.
  eapply reset_descendents_cspace_slot_abs_Capability_wellform_descendents_keep'; eauto.
Qed.


(*taskPrioProp*)
Lemma reset_nth_cspace_slot_option_taskPrioProp:
  forall node class x ls ls1 ,
  reset_nth_cspace_slot_option node class x ls ls1 ->
  taskPrioProp ls ->
  taskPrioProp ls1.
Proof.
  intros.
  unfolds in H. 
  simpljoin.
  unfolds in H. destruct H.
  subst x. 
  assert((0 <=? Z.to_nat SLOT_NUM)%nat &&
  (Z.to_nat SLOT_NUM <?
   Z.to_nat SLOT_NUM)%nat = false).
  unfold SLOT_NUM. int auto.
  rewrite H in H1.
  subst ls1. auto.
  assert((0 <=? x)%nat = true).
  clear -H. unfold SLOT_NUM in H.  int auto.
  assert((x <? Z.to_nat SLOT_NUM)%nat = true).
  clear -H. unfold SLOT_NUM in *. 
  eapply Nat.ltb_lt; eauto. lia.
  rewrite H2, H3 in H1.
  simpl in H1.
  unfolds in H1.
  destruct (nth_cspace
  (Z.to_nat (Int.unsigned node))
  ls) eqn: Hcspace.
  destruct c,p,p,p,c,p.
  destruct ( ACSpace_defs.nth_slots x l0) eqn: Hslots.
  destruct p, p, c, p.
  destruct (Int.eq i4 ($ CAP_CATEGORY_TYPE)).
  lets Hx: update_nth_cspace_slot_cap_type_trans Hcspace Hslots H1; eauto.
  subst ls1.
  rewrite Hx.
  eapply taskPrioProp_update_slots_type_remain; eauto.
  eapply taskPrioProp_update_slots_cap_remain; eauto.
  destruct (Int.eq i4 ($ CAP_OBJECT_TYPE)).
  lets Hx: update_nth_cspace_slot_cap_type_trans Hcspace Hslots H1; eauto.
  subst ls1.
  rewrite Hx.
  eapply taskPrioProp_update_slots_type_remain; eauto.
  eapply taskPrioProp_update_slots_cap_remain; eauto.
  lets Hx: update_nth_cspace_slot_cap_type_trans Hcspace Hslots H1; eauto.
  subst ls1.
  rewrite Hx.
  eapply taskPrioProp_update_slots_type_remain; eauto.
  eapply taskPrioProp_update_slots_cap_remain; eauto.
  subst ls1. auto. 
  subst ls1. auto.
Qed.

Lemma reset_descendents_cspace_slot_abs_taskPrioProp_keep: 
  forall  node class cspacels ls ls1,
  reset_descendents_cspace_slot node class cspacels ls ls1 ->
  taskPrioProp ls  ->
  taskPrioProp ls1.
Proof.
  apply (reset_descendents_cspace_slot_mut
  (fun node class cspacels ls ls1
    (pf1: reset_descendents_cspace_slot node class cspacels ls ls1) 
    => 
    taskPrioProp ls ->
    taskPrioProp ls1)
  (fun node class cspacels ls ls1   
    (pf2: 
    reset_descendents_cspace_list_slot node class cspacels ls ls1) 
    => 
    taskPrioProp ls ->
    taskPrioProp ls1)
  ).
  intros.
  destruct e. 
  lets Hx: reset_nth_cspace_slot_option_taskPrioProp H1 H0.
  eapply H; eauto.
  intros. auto.
  intros.
  eapply H0; eauto.
Qed.

(*RL_Cap_Parent_Child*)
Lemma reset_nth_cspace_slot_option_RL_Cap_Parent_Child:
  forall node class x l ls ls1 ,
  reset_nth_cspace_slot_option node class x ls ls1 ->
  RL_Cap_Parent_Child l ls ->
  RL_Cap_Parent_Child l ls1.
Proof.
  intros.
  unfolds in H. 
  simpljoin.
  unfolds in H. destruct H.
  subst x. 
  assert((0 <=? Z.to_nat SLOT_NUM)%nat &&
  (Z.to_nat SLOT_NUM <?
   Z.to_nat SLOT_NUM)%nat = false).
  unfold SLOT_NUM. int auto.
  rewrite H in H1.
  subst ls1. auto.
  assert((0 <=? x)%nat = true).
  clear -H. unfold SLOT_NUM in H.  int auto.
  assert((x <? Z.to_nat SLOT_NUM)%nat = true).
  clear -H. unfold SLOT_NUM in *. 
  eapply Nat.ltb_lt; eauto. lia.
  rewrite H2, H3 in H1.
  simpl in H1.
  unfolds in H1.
  destruct (nth_cspace
  (Z.to_nat (Int.unsigned node))
  ls) eqn: Hcspace.
  destruct c,p,p,p,c,p.
  destruct ( ACSpace_defs.nth_slots x l1) eqn: Hslots.
  destruct p, p, c, p.
  destruct (Int.eq i4 ($ CAP_CATEGORY_TYPE)).
  lets Hx: update_nth_cspace_slot_cap_type_trans Hcspace Hslots H1; eauto.
  subst ls1.
  rewrite Hx.
  eapply RL_Cap_Parent_Child_update_slots_type_remain; eauto.
  eapply RL_Cap_Parent_Child_remain; eauto.
  destruct (Int.eq i4 ($ CAP_OBJECT_TYPE)).
  lets Hx: update_nth_cspace_slot_cap_type_trans Hcspace Hslots H1; eauto.
  subst ls1.
  rewrite Hx.
  eapply RL_Cap_Parent_Child_update_slots_type_remain; eauto.
  eapply RL_Cap_Parent_Child_remain; eauto.
  lets Hx: update_nth_cspace_slot_cap_type_trans Hcspace Hslots H1; eauto.
  subst ls1.
  rewrite Hx.
  eapply RL_Cap_Parent_Child_update_slots_type_remain; eauto.
  eapply RL_Cap_Parent_Child_remain; eauto.
  subst ls1. auto. 
  subst ls1. auto.
Qed.

Lemma reset_descendents_cspace_slot_abs_RL_Cap_Parent_Child_keep': 
  forall  node class cspacels  ls ls1,
  reset_descendents_cspace_slot node class cspacels ls ls1 ->
  forall l,
  RL_Cap_Parent_Child l ls  ->
  RL_Cap_Parent_Child l ls1.
Proof.
  apply (reset_descendents_cspace_slot_mut
  (fun node class cspacels ls ls1
    (pf1: reset_descendents_cspace_slot node class cspacels ls ls1) 
    => forall l,
    RL_Cap_Parent_Child l ls ->
    RL_Cap_Parent_Child l ls1)
  (fun node class cspacels ls ls1   
    (pf2: 
    reset_descendents_cspace_list_slot node class cspacels ls ls1) 
    => forall l,
    RL_Cap_Parent_Child l ls ->
    RL_Cap_Parent_Child l ls1)
  ).
  intros.
  destruct e. 
  lets Hx: reset_nth_cspace_slot_option_RL_Cap_Parent_Child H1 H0.
  eapply H; eauto.
  intros. auto.
  intros.
  eapply H0; eauto.
Qed.

Lemma RLH_cspace_pris_P_inj: 
  forall l x1 x  cspacels,
  RLH_cspace_pris_P x1 l cspacels ->
  RLH_cspace_pris_P x l cspacels ->
  x1 = x.
Proof.
  induction l; destruct x1; destruct x; intros; auto. 
  unfolds in H0. tryfalse.
  unfolds in H. tryfalse.
  unfolds in H. tryfalse.
  unfolds in H. tryfalse.
  unfolds in H0. tryfalse.
  simpl in H, H0.
  destruct a; tryfalse.
  simpljoin.
  rewrite H in H0. inverts H0.
  assert(x1 = x).
  eapply IHl; eauto. 
  subst x1. auto. 
Qed.



(*RLH_CapParent*)
Lemma RLH_cspace_slots_P_inj: 
forall vl acspace acspace' cspacels pl,
  RLH_cspace_slots_P vl acspace cspacels pl->
  RLH_cspace_slots_P vl acspace' cspacels pl->
  acspace = acspace'.
Proof.
  intros.
  apply CSpaceMod.map_eql.
  intros.
  unfold RLH_cspace_slots_P in H, H0. 
  simpljoin.
  destruct (nth_cspace_val
  ∘ (Int.unsigned t) vl) eqn: Hcspace.
  destruct c. destruct p. destruct p. 
  destruct p. 
  simpljoin.
  lets Hx: H Hcspace.
  lets Hy: H0 Hcspace.
  destruct c. 
  simpljoin.
  assert(x = x1).
  eapply RLH_cspace_pris_P_inj; eauto. 
  subst x1. 
  assert(x2 = x0).
  {
    unfold RLH_cspace_parents_P in *.
    rewrite H8 in H6.
    inverts H6. auto.
  }
  subst x2.
  rewrite <- H3 in H4. auto. 
  lets Hx: CSpaceMod.get_dec acspace t. 
  destruct Hx. destruct e. destruct x.
  destruct p. 
  eapply H2 in H3. 
  simpljoin. 
  rewrite Hcspace in H3. tryfalse.
  lets Hx: CSpaceMod.get_dec acspace' t. 
  destruct Hx. destruct e0. destruct x.
  destruct p. 
  eapply H1 in H3. 
  simpljoin. 
  rewrite Hcspace in H3. tryfalse.
  rewrite e, e0. auto. 
Qed.
Lemma reset_nth_cspace_slot_ucos_option_RLH_CapParent:
  forall node class x  vl vl' acspace acspace' cspacels pl,
  reset_nth_cspace_slot_option node class x vl vl' ->
  RLH_cspace_slots_P vl acspace cspacels pl ->
  RLH_cspace_slots_P vl' acspace' cspacels pl ->
  RLH_CapParent pl acspace ->
  RLH_CapParent pl acspace'.
Proof.
  intros.
  lets Hx: reset_nth_cspace_slot_option_RLH_cspace_slots_P H H0.
  unfolds in H. 
  simpljoin.
  unfolds in H. destruct H.
  subst x. 
  assert((0 <=? Z.to_nat SLOT_NUM)%nat &&
  (Z.to_nat SLOT_NUM <?
   Z.to_nat SLOT_NUM)%nat = false).
  unfold SLOT_NUM. int auto.
  rewrite H in H5.
  subst vl'.
  lets Hx: RLH_cspace_slots_P_inj H0 H1.
  subst acspace'. auto. 
  assert(x0 = acspace').
  { 
    eapply RLH_cspace_slots_P_inj; eauto.
  }
  subst x0.
  assert((0 <=? x)%nat = true).
  clear -H. unfold SLOT_NUM in H.  int auto.
  assert((x <? Z.to_nat SLOT_NUM)%nat = true).
  clear -H. unfold SLOT_NUM in *. 
  eapply Nat.ltb_lt; eauto. lia.
  rewrite H6, H7 in H5.
  simpl in H5. 
 
  inversion H4.
  rewrite H6, H7 in H9. simpl in H9.
  inversion H9. substs. auto.
  substs. auto.
 
  unfold RLH_CapParent.
  splits; intros.
  
  unfolds in H2.
  destruct H2.
  lets Hx: H2 H17.
  simpljoin. 
  lets Hx: Int.eq_dec prio0 node.
  destruct Hx. subst prio0.
  rewrite get_set_eq.
  assert(prio = x0).
  clear -H10 H19.
  unfolds in H19. simpl in H19.
  rewrite H10 in H19.
  inverts H19. auto.
  subst prio. eexists. eexists. eauto.
  eexists. eexists.
  eapply  get_set_neq; eauto.
  eapply  get_set_neq; eauto.
  lets Hx: Int.eq_dec prio0 node.
  destruct Hx.
  subst prio0.
  rewrite get_set_eq in H17.
  inverts H17. auto.
  clear -H2 H10.
  unfolds in H2. simpljoin.
  eapply H0; eauto.
  rewrite map_get_set' in H17; auto.
  rewrite map_get_set' in H17; auto.
  clear -H2 H17.
  unfolds in H2. simpljoin.
  eapply H0; eauto.

  unfold RLH_CapParent.
  splits; intros.
  
  unfolds in H2.
  destruct H2.
  lets Hx: H2 H17.
  simpljoin. 
  lets Hx: Int.eq_dec prio0 node.
  destruct Hx. subst prio0.
  rewrite get_set_eq.
  assert(prio = x0).
  clear -H10 H19.
  unfolds in H19. simpl in H19.
  rewrite H10 in H19.
  inverts H19. auto.
  subst prio. eexists. eexists. eauto.
  eexists. eexists.
  eapply  get_set_neq; eauto.
  eapply  get_set_neq; eauto.
  lets Hx: Int.eq_dec prio0 node.
  destruct Hx.
  subst prio0.
  rewrite get_set_eq in H17.
  inverts H17. auto.
  clear -H2 H10.
  unfolds in H2. simpljoin.
  eapply H0; eauto.
  rewrite map_get_set' in H17; auto.
  rewrite map_get_set' in H17; auto.
  clear -H2 H17.
  unfolds in H2. simpljoin.
  eapply H0; eauto.
  unfold RLH_CapParent.
  splits; intros.
  
  unfolds in H2.
  destruct H2.
  lets Hx: H2 H18.
  simpljoin. 
  lets Hx: Int.eq_dec prio0 node.
  destruct Hx. subst prio0.
  rewrite get_set_eq.
  assert(prio = x0).
  clear -H10 H20.
  unfolds in H20. simpl in H20.
  rewrite H10 in H20.
  inverts H20. auto.
  subst prio. eexists. eexists. eauto.
  eexists. eexists.
  eapply  get_set_neq; eauto.
  eapply  get_set_neq; eauto.
  lets Hx: Int.eq_dec prio0 node.
  destruct Hx.
  subst prio0.
  rewrite get_set_eq in H18.
  inverts H18. auto.
  clear -H2 H10.
  unfolds in H2. simpljoin.
  eapply H0; eauto.
  rewrite map_get_set' in H18; auto.
  rewrite map_get_set' in H18; auto.
  clear -H2 H18.
  unfolds in H2. simpljoin.
  eapply H0; eauto.
Qed.

Lemma reset_descendents_cspace_slot_RLH_CapParent_keep': 
  forall  node class cspacels ls ls1,
  reset_descendents_cspace_slot node class cspacels ls ls1 ->
  forall acspace acspace'  pl,
  RLH_cspace_slots_P ls acspace cspacels pl->
  RLH_cspace_slots_P ls1 acspace' cspacels pl->
  RLH_CapParent pl acspace ->
  RLH_CapParent pl acspace'.
Proof.
  apply (reset_descendents_cspace_slot_mut
  (fun node class cspacels ls ls1
    (pf1: reset_descendents_cspace_slot node class cspacels ls ls1) 
    => 
    forall acspace acspace' pl,
    RLH_cspace_slots_P ls acspace cspacels pl->
    RLH_cspace_slots_P ls1 acspace' cspacels pl->
    RLH_CapParent pl acspace ->
    RLH_CapParent pl acspace')
  (fun node class cspacels ls ls1   
    (pf2: 
    reset_descendents_cspace_list_slot node class cspacels ls ls1) 
    => forall acspace acspace' pl,
    RLH_cspace_slots_P ls acspace cspacels pl->
    RLH_cspace_slots_P ls1 acspace' cspacels pl->
    RLH_CapParent pl acspace ->
    RLH_CapParent pl acspace')
  ).
  intros.
  destruct e. 
  lets Hx: reset_nth_cspace_slot_ucos_option_exists H3 H0.
  destruct Hx.
  lets Hy: reset_nth_cspace_RLH_cspace_slots_P_keep H3 H4 H0.
  eapply H; eauto.
  eapply reset_nth_cspace_slot_ucos_option_RLH_CapParent; eauto.
  intros. auto.
  lets Hx: RLH_cspace_slots_P_inj H H0. subst acspace'. auto.
  intros.
  lets Hx: reset_descendents_cspace_slot_LRH r H1.
  destruct Hx. 
  destruct H4.
  eapply H0; eauto.
Qed.
Lemma reset_descendents_cspace_slot_RLH_CapParent_keep: 
  forall  node class cspacels ls ls1 pl acspace acspace',
  reset_descendents_cspace_slot node class cspacels ls ls1 ->
  RLH_cspace_slots_P ls acspace cspacels pl->
  RLH_cspace_slots_P ls1 acspace' cspacels pl->
  RLH_CapParent pl acspace ->
  RLH_CapParent pl acspace'.
Proof.
  intros.
  eapply reset_descendents_cspace_slot_RLH_CapParent_keep'; eauto.
Qed.

Lemma nth_slots_help_1: 
    forall  l1 l2 x a,
    nth_slots x l1 = Some a->
    nth_slots x (l1 ++ l2) = Some a. 
  Proof.
    induction l1; destruct x; intros.
    simpl in H. tryfalse.
    simpl in H.  tryfalse.
    simpl. simpl in H. auto.
    simpl in H.
    simpl.
    eapply IHl1. auto.
  Qed.

Lemma nth_slots_help_2: 
  forall  l1 l2 x  y,
  length l1 = x->
  nth_slots (x + y) (l1 ++ l2) = nth_slots y l2. 
Proof.
  induction l1; destruct x; intros.
  simpl in H. tryfalse.
  simpl in H.  tryfalse.
  simpl. simpl in H. auto.
  simpl in H. lia.
  simpl in H. lia.
  simpl. 
  assert(length l1 = x). simpl in H. lia.
  eapply IHl1; auto.
Qed.

Lemma nth_slots_length_ll:
  forall  l2 l1  l3 x a y,
  nth_slots x l2 = Some a ->
  length l1 = y ->
  nth_slots (x + y)(l1 ++ l2 ++ l3) = Some a.
Proof.
  induction l2; destruct l1; destruct l3; destruct x; destruct y; intros; simpl; auto;
  simpl in H; tryfalse. rewrite app_nil_r. rewrite Nat.add_0_r. auto.
  rewrite Nat.add_0_r. 
  eapply nth_slots_help_1; auto.
  assert(length l1 = y). simpl in H0. lia.
  rewrite app_nil_r.
  inverts H.
  eapply  nth_slots_length_imp; auto.
  rewrite app_nil_r. 
  rewrite Nat.add_comm.
  rewrite list_cons_assoc.
  rewrite nth_slots_help_2; auto.
  rewrite app_length. simpl. 
  simpl in H0. lia.
  inverts H. 
  eapply nth_slots_length_imp; eauto.
  rewrite list_cons_assoc.
  assert(length (l1 ++ a :: nil) = S y).
  rewrite app_length. simpl.  simpl in H0. lia.
  eapply IHl2; auto.
 Qed.

Lemma nth_slots_help_3:
forall  l1 l2 x a,
  (x < length l1)%nat ->
  nth_slots x (l1 ++ l2) = Some a->
  nth_slots x l1 = Some a. 
Proof.
  induction l1; destruct x; intros; simpl in H; try lia.
  simpl in H0. simpl. auto.
  simpl in H0. simpl. eapply IHl1; auto.
  lia. eauto.
Qed.

Lemma nth_slots_help_4:
  forall l x a,
  nth_slots x l = Some a ->
  exists l1  l2, l = l1 ++ a :: l2 
  /\ length l1 = x /\ length l2 = (length l - S x)%nat. 
Proof. 
  induction l; destruct x; intros; simpl in H; tryfalse.
  exists (nil: list slot_val_type).
  exists l.
  splits. rewrite app_nil_l. inverts H. auto.
  simpl. auto.   simpl. lia.
  eapply IHl in H. destruct H. destruct H.
  destruct H. destruct H0.
  subst l. 
  exists (a::x0). exists x1. 
  splits; auto.
  simpl. rewrite H0. auto.
Qed.
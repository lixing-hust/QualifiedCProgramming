Require Import base_tac.
Require Import hoare_forward.
Require Import math_auto.
Require Import sep_auto.
Require Import pure.
Require Import ucos_common.
Require Import ifun_spec.
Require Import inv_prop.
Require Import symbolic_lemmas.
Require Import ios_int.
Require Import lmachLib.
Require Import include_frm.
Require Import sep_auto.
Require Import ACSpace_defs.
Require Import math_auto.
Require Import ios_cap_defs.
Require Import pure_lib.
Import DeprecatedTactic.
Open Scope code_scope.
Open Scope list_scope.
Open Scope int_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Set Implicit Arguments.
Notation "E '..' I" := (efield E I) (at level 10)  : code_scope.

(*计算e.id的地址*)
Lemma field_asrt_impl_struct_aop: 
  forall s id e1 tid decl b i off tp p , 
    ftype id decl = Some tp ->
    field_offset id decl = Some off -> 
    s |= ((Lv e1 @ (Tstruct tid decl) ==  (b, i)) ** p) ->
    s |= (Lv (efield e1 id) @ tp == (b,Int.add i off)).
Proof.
  intros.
  unfold sat.
  destruct s as [[]].
  destruct t as [[[[[]]]]].
  unfold sat in H1;fold sat in H1;mytac.
  simpl in H5;mytac.
  simpl.
  simpl in H2.
  simpl in H4.
  assert(evaladdr e1 (e, e0, m) = Some (Vptr(b, i))).
  eapply evaladdr_mono; eauto.
  rewrite H1.
  unfold getoff.
  simpl in H7.
  simpl.
  assert(evaltype e1 (e, e0, m) = evaltype e1 (e, e0, x)).
  eapply evaltype_mono; eauto.
  rewrite H7 in H3.
  rewrite H3.
  rewrite H0.
  rewrite Int.repr_unsigned.
  auto.
  simpl;auto.
  simpl in H7. 
  assert(evaltype e1 (e, e0, m) = evaltype e1 (e, e0, x)).
  eapply evaltype_mono; eauto.
  rewrite H7 in H1.
  rewrite H1. auto.
Qed.

(*在后面加上一个后缀p'*)
Lemma field_asrt_impl_struct_aop': 
  forall s p id e1 tid decl b i off tp , 
    ftype id decl = Some tp ->
    field_offset id decl = Some off -> 
    s |= ((Lv e1 @ (Tstruct tid decl) ==  (b, i)) ** p) ->
    s|= (Lv (efield e1 id) @ tp == (b,Int.add i off) ** p).
Proof.
  intros.
  sep cancel p.
  unfold sat.
  destruct s as [[]].
  destruct t as [[[[[]]]]].
  unfold sat in H1;fold sat in H1;mytac.
  simpl.
  simpl in H2.
  simpl in H1.
  unfold getoff.
  rewrite H2. simpl.
  rewrite H1. rewrite H0.
  rewrite Int.repr_unsigned.
  auto.
  simpl;auto.
  simpl in H2. rewrite H2. auto.
Qed.


(*计算e.id的值*)
Lemma expr_struct_member_rv':
  forall s e t l vl tid decl n id t' v P,
    (forall ids dl, t' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
    (forall ids dl, t' <> Tunion ids dl) ->
    rule_type_val_match t' v =true->
    (*v<> Vundef ->*)
    good_decllist decl = true ->
    s |= Lv e @ t == l ->
    s |= Astruct l t vl ** P ->
    t = Tstruct tid decl ->
    nth_id n decl = Some id ->
    ftype id decl = Some t' ->
    nth_val n vl = Some v ->
    s |= Rv (efield e id) @ t' == v.
Proof.
  introv Hnstr.
  introv Hnarr.
  introv Hnunion.
  introv Htv.
  assert (v<> Vundef) as Hvn.
  eapply rule_type_val_match_nvundef;eauto.
  introv Hgooddecl.
  intros.
  destruct s as ((o&O)&aop).
  unfold sat in *;fold sat in *;mytac.
  unfold substmo in *.
  destruct o as [[[[[]]]]].
  unfold substaskst in *.
  unfold getsmem in *.
  unfold getmem in *.
  unfold get_smem in *.
  unfold get_mem in *.
  simpl in *;mytac.
  rewrite H.
  rewrite H10.
  unfold getoff.
  rewrite H3.
  lets Hoff: nth_id_exists_off H2.
  rewrite H10.
  destruct Hoff.
  rewrite H0.
  destruct l.
  rewrite struct_asrt_eq with (n:=n) in H8;eauto.
  unfold sat in H8;fold sat in H8;mytac.
  simpl in H12.
  rewrite Int.repr_unsigned.
  destruct H12.
  lets Hload: mapstoval_load H1. auto.
  simpl in H6.
  unfold addrval_to_addr.
  lets Hload': load_local H6 Hload.
  lets Hload'': load_local H5 Hload'.
  auto.
  destruct o as [[[[[]]]]].
  simpl in *;mytac.
  rewrite H10.
  auto.
  auto.
Qed.

Lemma field_asrt_impl_union_aop: 
  forall s id e1 tid decl b i tp p , 
    ftype id decl = Some tp ->
    s |= ((Lv e1 @ (Tunion tid decl) ==  (b, i)) ** p) ->
    s |= (Lv (efield e1 id) @ tp == (b,Int.add i (Int.repr 0))).
Proof.
  intros.
  unfold sat.
  destruct s as [[]].
  destruct t as [[[[[]]]]].
  unfold sat in H0;fold sat in H0;mytac.
  simpl in H4;mytac.
  simpl.
  simpl in H1.
  simpl in H3.
  assert(evaladdr e1 (e, e0, m) = Some (Vptr(b, i))).
  eapply evaladdr_mono; eauto.
  rewrite H0.
  unfold getoff.
  simpl in H6.
  simpl.
  assert(evaltype e1 (e, e0, m) = evaltype e1 (e, e0, x)).
  eapply evaltype_mono; eauto.
  rewrite H6 in H2.
  rewrite H2.
  rewrite Int.repr_unsigned.
  auto.
  rewrite Int.add_zero. auto.
  simpl getsmem.
  simpl.
  assert(evaltype e1 (e, e0, m) = evaltype e1 (e, e0, x)).
  eapply evaltype_mono; eauto.
  simpl in H6.
  rewrite H6 in H0.
  rewrite H0. auto.
Qed.


Lemma field_asrt_impl_union_aop': 
  forall s id e1 tid decl b i tp p , 
    ftype id decl = Some tp ->
    s |= ((Lv e1 @ (Tunion tid decl) ==  (b, i)) ** p) ->
    s |= (Lv (efield e1 id) @ tp == (b,Int.add i (Int.repr 0))) ** p.
Proof.
    intros.
    sep cancel p.
    destruct s as [[]].
    destruct t as [[[[[]]]]].
    unfold sat in H0;fold sat in H0;mytac.
    simpl in H0, H1.
    simpl.
    rewrite H0.
    unfold getoff.
    rewrite H1.
    split.
    rewrite Int.repr_unsigned. 
    rewrite Int.add_zero.
    auto.
    auto.
Qed.



Lemma star_eq_rep:
  forall q r q' A, (A <==> q ** r) -> (q <==> q') -> (A <==>  q' ** r).
Proof.
  intros.
  split;intros.
  destruct H with s.
  apply H2 in H1.
  sep_auto.
  destruct H0 with H4.
  apply H5;auto.
  destruct H with s.
  apply H3.
  sep_auto.
  destruct H0 with H4.
  apply H6;auto.
Qed.

(*对于expression e1, e2来说 e1.id = e2的赋值语句*)


Lemma assign_rule_struct_struct_aop:
  forall Spec I r ri p p' id e1 l1 e tid decl n vl vl' v1 v tp1 tp1' tp2 aop sc li ct,
  p ==> Lv e1 @ tp1 == l1->
  p <==> Astruct l1 tp1 vl ** p' ->
  tp1 = Tstruct tid decl ->
  good_decllist decl = true ->
  nth_id n decl = Some id ->
  ftype id decl = Some tp1' ->
  (forall ids dl, tp1' <> Tstruct ids dl) ->
  (forall (t'0 : type) (n0 : nat), tp1' <> Tarray t'0 n0) ->
  (forall ids dl, tp1' <> Tunion ids dl) ->
  p ==> Rv e @ tp2 == v ->
  assign_type_match tp1' tp2 ->
  (n < length vl)%nat ->
  nth_val n vl = Some v1 ->
  update_nth_val n vl v = vl'->
  Astruct l1 tp1 vl' ** p' ==>
  EX lg : list logicvar, p_local li ct lg ** Atrue ->
  {| Spec, sc, li, I, r, ri |} |-ct {{ <|| aop ||> ** p }} (sassign (efield (e1) id) e)  
                                  {{ <|| aop ||> **Astruct l1 tp1 vl' ** p' }}.
Proof.
  intros.
  unfold Astruct in H0. 
  rewrite H1 in H0.
  rewrite H1.
  simpl Astruct.
  lets Hoff: nth_id_exists_off H3.
  destruct Hoff as (off&Hoff).
  destruct l1 as (b&i).
  assert (Astruct' (b, i) decl vl <==> PV (b,Int.add i off) @ tp1' |-> v1 ** Astruct_rm (b,i) decl vl id).
  eapply struct_asrt_eq;eauto.
  lets Hrep:star_eq_rep H0 H14.

  assert(p ==> (Lv (efield e1 id) @ tp1' == (b,Int.add i off))).
  intros.
  apply H in H15.
  rewrite H1 in H15.
  apply astar_r_aemp_intro in H15.
  lets Hlv: field_asrt_impl_struct_aop H4 Hoff H15.
  auto.
  assert(p <==> PV (b, Int.add i off) @tp1' |-> v1 ** Astruct_rm (b, i) decl vl id ** p').
  eapply asrt_eq_trans;eauto.
  split;intros;sep auto.
  assert ({|Spec , sc, li, I, r, ri|}|-ct  {{p **  <|| aop ||> }}
                                           sassign (efield  e1 id) e
                                           {{PV (b, Int.add i off) @ tp1' |-> v ** (
                                                                                       Astruct_rm (b, i) decl vl id **
                                                                                       p') ** <|| aop ||> }}).
  
  eapply assign_rule'';eauto.
  intros.
  apply H13.
  sep auto.

  eapply struct_asrt_eq;eauto.

  eapply update_nth;eauto.
  sep auto.
  eapply struct_rm_update_eq;eauto.
  eapply forward_rule1.
  2: {
  hoare lifts (2::nil)%nat pre.
  eapply H17.
  }
  intros.
  sep auto.
  eapply struct_asrt_eq;eauto.
  eapply update_nth;eauto.
  sep auto.
  eapply struct_rm_update_eq;eauto.
Qed.
Require Import Lia.
Open Scope nat_scope.


Lemma assign_rule_aop :
  forall Spec I r ri  p p' e1 e2 l v1 v2 tp1 tp2 aop sc li tid,  
    assign_type_match tp1 tp2 ->  
    p ==> Lv e1 @ tp1 == l ->
    p <==>  PV l @ tp1|-> v1 ** p' ->
    p ==>  Rv e2 @ tp2 == v2 ->
    (*p ==>  EX lg, p_local li tid lg ** Atrue ->*)
    PV l @ tp1|-> v2 ** p' ==>  EX lg, p_local li tid lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-tid {{ <|| aop ||> ** p }} (sassign e1 e2) {{<|| aop ||> **  PV l @ tp1|-> v2 ** p' }}.
Proof.
  intros.
  eapply backward_rule1 with (p:= <||aop||> ** PV l @tp1|-> v1 ** p' ). 
  intros.
  sep cancel 1%nat 1%nat.
  apply H1 in H4;auto.
  eapply forward_rule1 with (<|| aop ||> ** PV l @ tp1|-> v2 ** p').
  intros;sep auto.
  eapply assign_rule';eauto.
  intros.
  split;auto.
  apply H0;apply H1;auto.
  apply H2;apply H1;auto.
  intros;apply H3;sep auto.
Qed.

(*辅助定理就是x'[e]的地址*)
Lemma arrayelem_asrt_impl_g': 
  forall n m p' b i te2 t e2 x s, 
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    s |= (A_notin_lenv x ** Agvarenv x (Tarray t n) (addrval_to_addr (b, i))) **
    Rv e2 @ te2 == Vint32 (Int.repr (BinInt.Z.of_nat m)) **  p' ->
    s |=
      (Lv (earrayelem (evar x) e2) @ t == (b,Int.add i (Int.mul (Int.repr (Z.of_nat (typelen t)))  (Int.repr (BinInt.Z.of_nat m))))) ** p'.
Proof.
  introv Ht.
  intros.
  sep cancel p'.
  destruct_s s.
  simpl in *;simpljoin. 
  apply EnvMod.nindom_get in H3.
  unfold get in *;simpl.
  simpl in H8.
  rewrite H8.
  rewrite H3.
  apply join_emp_eq in H0.
  subst x1.
  apply join_emp_eq in H5.
  subst x7.
  rewrite H9.
  rewrite <- Int.unsigned_zero in H19.
  apply hoare_assign.unsigned_zero in H19.
  subst i.
  simpl.
  split;auto.
  rewrite H10.
  destruct Ht;subst;auto.
  destruct H;subst;auto.
Qed.



(*e 的type是Tptr t,那么 *e的type就是t*)
Lemma eval_type_ederef_eq :
 forall e ge le m t, evaltype (e) (ge, le, m) = Some (Tptr t) 
    -> evaltype (ederef e) (ge, le, m) = Some t.
Proof.
  intros.
  simpl in *;destruct e;tryfalse;auto.
  destruct (evaltype v ′ (ge, le, m)); tryfalse.
  inversion H;auto.
    inversion H;auto.
  destruct (evaltype (eunop u e) (ge, le, m)); tryfalse.
  inversion H;auto.
  destruct (evaltype (ebinop b e1 e2) (ge, le, m));tryfalse.
  inversion H;auto.
  destruct (evaltype (∗ e) (ge, le, m));tryfalse.
  inversion H;auto.
  destruct (evaltype (&ₐ e) (ge, le, m));tryfalse.
  inversion H;auto.
  destruct (evaltype (efield e i) (ge, le, m));tryfalse.
  inversion H;auto.
  destruct (evaltype (〈 t0 〉 e) (ge, le, m));tryfalse.
  inversion H;auto.
  destruct (evaltype (e1 [e2]) (ge, le, m));tryfalse.
  inversion H;auto.
Qed.


(*计算 e->id的地址*)
Lemma field_ederef_asrt_impl': 
  forall p id e1 tid decl b i off tp b0 i0, 
    ftype id decl = Some tp ->
    field_offset id decl = Some off -> 
    ((Lv e1 @ (Tptr(Tstruct tid decl)) ==  (b, i)) ** PV (b, i)@ (Tptr(Tstruct tid decl)) |->Vptr(b0, i0) ** p) ==> (Lv (efield (ederef e1) id) @ tp == (b0,Int.add i0 off)).
Proof.
  intros.
  assert(s |= Rv e1 @(Tptr(Tstruct tid decl)) == Vptr (b0, i0)).
  eapply lv_mapsto_to_rv. auto. 
  assert(s |= Lv e1 @
  (STRUCT tid ­{ decl }­) ∗ ==
  (b ↝ {i})).
  {
    destruct_s s. 
    destruct H1. simpljoin. simpl in H2, H4, H5. simpljoin1.
    simpl.
    splits. eapply evaladdr_mono; eauto.
    assert(evaltype e1 ((e ↝ {e0}) ↝ {m}) = evaltype e1 ((e ↝ {e0}) ↝ {x})).
    eapply evaltype_mono; eauto.
    rewrite H5. auto.  
  }
  exact H2.
  sep lift 2%nat in H1.
  unfold Aptrmapsto in H1.
  exact H1.

  destruct_s s. 
  destruct H1. simpljoin. simpl in H3, H5, H6. simpljoin1.
  destruct H7. simpljoin. simpl in H7, H9, H10. simpljoin1.
  destruct H2.  simpljoin. simpl in H2, H8.

  simpl.
  rewrite H2.
  unfold getoff.
  assert(evaltype (∗ e1) ((e ↝ {e0}) ↝ {m}) = Some (STRUCT tid ­{ decl }­)).
  apply eval_type_ederef_eq. auto.
  rewrite H10.
  rewrite H0.
  splits.  rewrite Int.repr_unsigned. auto. 
  assert(evaltype e1 ((e ↝ {e0}) ↝ {m}) = evaltype e1 ((e ↝ {e0}) ↝ {x})).
  {
    eapply evaltype_mono. eauto.
  }
  rewrite H12. rewrite H4. auto.
Qed.

(*在原有版本上将GV换成了G&*)
Lemma field_array_struct_impl_g_char_t:
  forall  p' b i t id decl  n' gident lident sid off tp 
  idx b0 i0 lenv n s, 
  var_notin_dom gident lenv = true  ->
    field_offset id decl = Some off ->
    ftype id decl = Some t ->
    (Z.of_nat idx >= 0)%Z ->
    (Z.of_nat idx <= 255)%Z ->
    nth_id n' decl = Some id ->
    tp = Tptr(Tstruct sid decl) ->
    s |= G& gident @ (Tarray tp n) == (b, i)** LV lident @ char_t |-> Vint32(Int.repr (Z.of_nat idx))
    ** PV (b, i +ᵢ  Int.mul ($ Z.of_nat (typelen tp)) ($ Z.of_nat idx)) @ tp  |-> Vptr(b0, i0) ** 
    A_dom_lenv lenv ** p'->
    s |=  Lv (efield(ederef (gident ′ [lident ′]))id) @ t == (b0, Int.add i0 off) ** p'.
Proof.
    introv Hnotin.
    introv Hoff.
    introv Htype.
    introv Hinrange1.
    introv Hinrange2.
    intros.
    sep cancel p'.
    assert(s|=Lv (gident ′ [lident ′])@ tp == (b, i +ᵢ  Int.mul ($ Z.of_nat (typelen tp))($ (Z.of_nat idx)))
    ** PV b↝ {i +ᵢInt.mul ($ Z.of_nat (typelen tp))($ Z.of_nat idx)} @ tp
 |-> Vptr (b0 ↝ {i0})).
    eapply arrayelem_asrt_impl_g'.
    instantiate(1:=char_t).
    auto.
    sep lift 4%nat in H1.
    lets Hs: dom_lenv_imp_notin_lenv Hnotin H1.
    sep normal.
    unfold Agvarenv' in Hs. 
    sep cancel 1%nat 1%nat. 
    sep cancel 1%nat 1%nat. 
    sep cancel 2%nat 2%nat.
    {
      destruct_s H2. 
      simpl.
      clear -Hs Hinrange1 Hinrange2.
      simpl in Hs. simpljoin.
      rewrite H3.
      apply mapstoval_load in H4. 
      apply join_emp_eq in H0.
      subst x1.
      splits. auto.
      auto. auto. 
      unfold rule_type_val_match.
      assert((Int.unsigned ($ Z.of_nat idx) <=?
      Byte.max_unsigned)%Z = true).
      rewrite Int.unsigned_repr.
      rewrite byte_max_unsigned_val.
      apply Zle_is_le_bool. auto.
      rewrite max_unsigned_val. lia.
      rewrite H. auto.
    }
    eapply field_ederef_asrt_impl'. eauto. 
    auto.
    rewrite H0 in H2.
    instantiate(2:=sid).
    instantiate(3:=b).
    instantiate(3:=i +ᵢInt.mul($ Z.of_nat (typelen tp))($ Z.of_nat idx)).
    sep auto.
Qed.


(*计算 e1.id[e2]的地址*)
Lemma expr_field_array_asrt_impl:
  forall s p' b i t m id e1 e2 decl  n' n te2 sid off, 
    field_offset id decl = Some off ->
    nth_id n' decl = Some id ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    ftype id decl = Some (Tarray t n) -> 
    s |=Lv e1 @ (Tstruct sid decl) == (b, i) ** 
    Rv e2 @ te2 == Vint32 (Int.repr (BinInt.Z.of_nat m)) **p' ->
    s |= Lv earrayelem (efield e1 id) e2 @ t ==
    (b,
     Int.add (Int.add i off)
             (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                      (Int.repr (BinInt.Z.of_nat m)))).
Proof.
  introv Hoff.
  intros.
  destruct s as [[]].
  destruct t0 as [[[[[]]]]].
  simpl in *;simpljoin.
  assert(evaltype e1 ((e, e0), m0) = evaltype e1 ((e, e0), x)).
  eapply evaltype_mono; eauto. 
  rewrite H15 in H2.
  rewrite H2.
  rewrite H1.
  eapply evaladdr_mono in H6; eauto. 
  rewrite H6.
  unfold getoff.
  rewrite H2.
  rewrite Hoff.
  unfold load;unfold loadm.
  simpl addr_to_addrval.
  rewrite Int.repr_unsigned.
  lets Hval': evalval_mono H8 H11.
  apply map_join_comm in H3.
  rewrite H11 in Hval'.
  lets Hval'': evalval_mono  H3 Hval'.
  rewrite Hval' in Hval''.
  rewrite Hval''.
  rewrite Int.repr_unsigned.
  splits. auto.
  assert(evaltype e2((e, e0), x0) = evaltype e2((e, e0), x5)).
  eapply evaltype_mono; eauto. 
  assert(evaltype e2((e, e0), m0) = evaltype e2((e, e0), x0)).
  eapply evaltype_mono; eauto.
  rewrite H4 in H7.
  rewrite H13 in H7.
  rewrite H7.
  destruct H0; subst; auto.
  destruct H0; subst; auto.
Qed.


Lemma expr_field_array_asrt_impl_frm:
  forall s p' b i t m id e1 e2 decl  n' n te2 sid off, 
    field_offset id decl = Some off ->
    nth_id n' decl = Some id ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    ftype id decl = Some (Tarray t n) -> 
    s |=Lv e1 @ (Tstruct sid decl) == (b, i) ** 
    Rv e2 @ te2 == Vint32 (Int.repr (BinInt.Z.of_nat m)) **p' ->
    s |= Lv earrayelem (efield e1 id) e2 @ t ==
    (b,
     Int.add (Int.add i off)
             (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                      (Int.repr (BinInt.Z.of_nat m)))) ** p'.
Proof.
  intros.
  sep cancel p'.
  eapply expr_field_array_asrt_impl; eauto. 
  sep auto.
  sep cancel 1%nat 1%nat.
  exact H3.
Qed.

Lemma of_to_nat_unsignedv': 
  forall v',
  Z.of_nat (Z.to_nat (Int.unsigned v')) = Int.unsigned v'.
Proof.
  intros.
  rewrite ZifyInst.of_nat_to_nat_eq.
  assert(Int.unsigned v' >= 0)%Z. apply unsigned_ge0.
  rewrite Z.max_comm.
  assert(Z.max (Int.unsigned v') 0 = Int.unsigned v').
  eapply Zmax_left; eauto. auto. 
Qed.

Lemma GoodFrm_Aarray_rm: 
forall x n t vl m,
GoodFrm(Aarray_rm x n t vl m).
Proof.
  introv.
  gen n m  vl x t. 
  induction n; induction m; intros.
  destruct vl; simpl; destruct x; simpl; auto.
  destruct vl; simpl; destruct x; simpl; auto.
  destruct vl; simpl; destruct x; simpl; auto.
  go.
  destruct vl. simpl. destruct x. simpl. auto.
  simpl. destruct x.
  unfold GoodFrm; fold GoodFrm.
  splits; simpl; auto.
Qed.



Lemma nth_val_length_imp:
forall n vl1 a vl2,
  length vl1 = n ->
  nth_val n (vl1 ++ a :: vl2) = Some a.
Proof.
  induction n; induction vl1; intros.
  simpl. auto.
  simpl in H. tryfalse.
  simpl in H. tryfalse.
  simpl in H. 
  assert(length vl1 = n) by auto with arith.
  eapply IHn  with(a:=a)(vl2:=vl2) in H0 . 
  simpl.
  auto.
Qed.

Lemma nth_cspace_length_imp:
forall n vl1 a vl2,
  length vl1 = n ->
  nth_cspace n (vl1 ++ a :: vl2) = Some a.
Proof.
  induction n; induction vl1; intros.
  simpl. auto.
  simpl in H. tryfalse.
  simpl in H. tryfalse.
  simpl in H. 
  assert(length vl1 = n) by auto with arith.
  eapply IHn  with(a:=a)(vl2:=vl2) in H0 . 
  simpl.
  auto.
Qed.

Lemma nth_slots_length_imp:
forall n vl1 a vl2,
  length vl1 = n ->
  nth_slots n (vl1 ++ a :: vl2) = Some a.
Proof.
  induction n; induction vl1; intros.
  simpl. auto.
  simpl in H. tryfalse.
  simpl in H. tryfalse.
  simpl in H. 
  assert(length vl1 = n) by auto with arith.
  eapply IHn  with(a:=a)(vl2:=vl2) in H0 . 
  simpl.
  auto.
Qed.

Lemma get_capability_nth_mth_cspace_length_imp:
forall n m vl1 a vl2 vll1 b1 b2 vll2 c d e idx,
  length vl1 = n ->
  length vll1 = m ->
  get_capability n m (vl1 ++ ((((a, vll1 ++ (b1, b2) :: vll2),
  c), d), e, idx) :: vl2) = Some b2.
Proof.
    intros.
    remember(((((a ↝ {vll1 ++ (b1 ↝ {b2}) :: vll2}) ↝ {c}) ↝ {d}) ↝ {e})↝ {idx}) as X.
    assert(nth_cspace n (vl1 ++ X :: vl2) = Some X).
    eapply nth_cspace_length_imp; eauto.
    unfold get_capability.
    rewrite H1.
    subst X. destruct a.
    assert(nth_slots m (vll1 ++ (b1, b2) :: vll2) = Some (b1, b2)).
    eapply nth_slots_length_imp; eauto.
    rewrite H2. auto.
Qed.
Open Scope Z_scope.

Lemma update_nth_list_length_imp: 
    forall (t: Type)(l1: list t) 
    (v1 : t) (v2 : t) (l2: list t) 
    (n : nat),
    length l1 = n ->
    update_nth_list t n (l1++v1::l2) v2
    =(l1++v2::l2).
Proof.
  induction l1; destruct n; intros.
  simpl. auto.
  simpl in H. tryfalse.
  simpl in H. tryfalse.
  simpl.
  simpl in H. 
  assert(length l1 = n).
  inverts H. auto.
  eapply IHl1 with(l2:=l2)
  (n := n)(v1:=v1)(v2:=v2) in H0.
  rewrite H0. auto.    
Qed.

Lemma update_nth_list_len_eq:
forall t vl  x v,
  length (update_nth_list t x vl v ) = length vl. 
Proof.
  induction vl; intros.
  simpl. auto.
  simpl. destruct x.
  simpl. auto.
  simpl.
  assert(length(update_nth_list t x vl v) = length vl).
  auto.
  lia.
Qed.

Lemma calculate_rv_GAarray:
    forall s x t1 n b i lv ls p v v'9 ,
    s |= G& x @ (Tarray t1 n) == (b, i) ** LV lv @ char_t |-> Vint32 v 
    ** PV (b, i +ᵢ Int.mul($Z.of_nat(typelen t1)) v)@t1 |-> Vptr v'9
    **A_dom_lenv ls **  p ->
    rule_type_val_match t1 (Vptr v'9) = true ->
    ((Int.unsigned v) <= 255) ->
    var_notin_dom x ls = true ->
    s |= Rv x′[lv′]@t1 == (Vptr v'9).
Proof.
    intros.
    destruct_s s. simpl.
    rename H0 into Htype.
    rename H1 into Hrange.
    rename H2 into H0.
    sep lift 4%nat in H.
    lets H1: dom_lenv_imp_notin_lenv H0 H. 
    destruct H1. simpljoin.
    simpl in H2, H4, H5. simpljoin1.
    apply nindom_get in H1.
    rewrite H1.
    destruct H6. simpljoin.
    simpl in H3, H5, H6. simpljoin1.
    rewrite H2.
    destruct H7. simpljoin.
    simpl in H4, H7, H8. simpljoin1.
    rewrite H11.
    destruct H9. simpljoin.
    rewrite H6.
    apply mapstoval_load in H12.
    rewrite Int.unsigned_zero in H12.
    lets Hload: load_local H4 H12.
    rewrite Hload.
    simpl.
    destruct H9.
    simpl in H3, H5, H7, H8.
    rewrite <- Int.unsigned_zero in H6.
    apply hoare_assign.unsigned_zero in H6.
    subst i.
    apply mapstoval_load in H3.
    lets Hload': load_local H5 H3.
    apply map_join_comm in H4.
    lets Hload'': load_local H4 Hload'.
    splits; eauto.
    auto. simpl. 
    clear -Hrange.
    assert(Int.unsigned v <=? Byte.max_unsigned = true).
    rewrite byte_max_unsigned_val.
    apply Zle_is_le_bool. auto.
    rewrite H. auto.
Qed.
Require Import lmachLib.
(*计算Rv &a(expr..id的值)*)
Lemma calculate_rv_expr_id_addr:
  forall s e b i  id tid decl tp p off,
  ftype id decl = Some tp ->
  field_offset id decl = Some off -> 
  s |= Lv e @(Tstruct tid decl) == (b, i)  ** p
  -> s |= Rv &ₐ(e..id)@(Tptr tp) == Vptr(b, Int.add i off).
intros.
  destruct_s s. 
  simpl; simpljoin.
  destruct H1. simpljoin.
  simpl in H2, H4, H5. simpljoin1.
  assert(evaltype e((e0, e1), m ) = evaltype e((e0, e1), x)).
  eapply evaltype_mono; eauto.
  rewrite H3 in H5. rewrite H5.
  rewrite H.
  lets Haddr: evaladdr_mono H2 H1.
  rewrite Haddr.
  unfold getoff.
  rewrite H5.  rewrite H0.
  rewrite Int.repr_unsigned.
  splits; eauto.
Qed.


Lemma LV_to_Rv:
  forall s x tp v p, 
  v <> Vundef ->
  rule_type_val_match tp v = true ->
  s |= LV x @ tp |-> v ** p ->
  s |= Rv (evar x) @ tp == v ** p.
Proof.
  introv Hnotundef.
  introv Hmatch.
  intros.
  sep cancel p.
  destruct_s s.
  simpl in H. simpljoin.
  simpl. rewrite H3.
  rewrite Int.unsigned_zero in H4.
  apply mapstoval_load in H4.
  splits; eauto.
  apply join_emp_eq in H0.
  subst x2.
  auto.
  auto.
Qed.


Lemma  negation_rv:
forall s e v, 
  s |= Rv e @ long == Vint32 v ->
  s |= Rv ∼e @ long == Vint32(Int.not v).
Proof.
  intros.
  destruct_s s.
  destruct H. simpljoin.
  simpl in H, H0.
  simpl.
  rewrite H. 
  rewrite H0.
  simpl uop_type.
  simpl. splits; eauto.
Qed.
(*计算x -> id的地址*)
Lemma local_val_struct_member_addr:
  forall s x t1 b i  p id off t2 tid decl,
  s |= LV x @ (Tptr t1) |-> Vptr (b, i) ** p ->
  t1 = Tstruct tid decl ->
  field_offset id decl = Some off ->
  ftype id decl = Some t2 ->
  s |= Lv x′→id@t2 == (b, Int.add i off).
Proof.
  intros.
  destruct_s s.
  simpl.
  destruct H. simpljoin.
  simpl in H3, H6, H5. simpljoin1.
  rewrite H8.
  apply mapstoval_load in H9.
  rewrite Int.unsigned_zero in H9.
  lets Hload: load_local H3 H9.
  rewrite Hload.
  unfold getoff.
  assert(evaltype (∗ x ′)((e, e0), m)
  = Some STRUCT tid ­{ decl }­).
  eapply eval_type_ederef_eq .
  simpl.
  rewrite H8. auto.
  rewrite H.
  rewrite H1.
  rewrite Int.repr_unsigned.
  splits; auto.
  simpl. auto.
Qed.

Lemma local_val_struct_member_addr_frm:
  forall s x t1 b i  p id off t2 tid decl,
  t1 = Tstruct tid decl ->
  field_offset id decl = Some off ->
  ftype id decl = Some t2 ->
  s |= LV x @ (Tptr t1) |-> Vptr (b, i) ** p ->
  s |= Lv x′→id@t2 == (b, Int.add i off) ** p.
Proof.
  intros.
  sep cancel p. 
  destruct_s s.
  simpl in H2.  simpljoin.
  apply join_emp_eq in H3.
  subst x2.
  rewrite Int.unsigned_zero in H7.
  apply mapstoval_load in H7.
  simpl.
  rewrite H6.
  rewrite H7.
  unfold getoff.
  assert(evaltype (∗ x ′)((e, e0), m)
  = Some STRUCT tid ­{ decl }­).
  eapply eval_type_ederef_eq .
  simpl.
  rewrite H6. auto.
  rewrite H. 
  rewrite H0.
  rewrite Int.repr_unsigned.
  splits; eauto.
  auto.
Qed.
Open Scope Z_scope.

Lemma nthval'_has_value_Tint32 : 
  forall l len n, array_type_vallist_match Tint32 l ->
                  length l = len -> 
                  (n < len)%nat ->
                  exists x, nth_val' n l = Vint32 x /\ true = rule_type_val_match Tint32 (Vint32 x).
Proof.
  intro.
  induction l.
  intros.
  simpl in H0.
  rewrite <- H0 in H1.
  inversion H1.

  intros.
  induction n.
  inversion H.
  simpl in H2.
  destruct a; try inversion H2.
  exists i.
  split ; auto.
 
  apply (IHl (pred len)).
  inversion H;  auto.
  2:{
    simpl in H0.
    lia. 
  }
  simpl in H0. 
  rewrite <- H0. simpl. auto.
Qed.

Lemma addition_trans:
forall v'0 n,
  Z.of_nat (S n) <= 255 ->
  $ Z.of_nat (Z.to_nat (Int.unsigned v'0) * n) =
  Int.mul ($ Z.of_nat n) v'0.
Proof.
  intros.
  rewrite Nat2Z.inj_mul.
  rewrite of_to_nat_unsignedv'.
  mauto.
  rewrite Z.mul_comm.
  auto.
Qed.

Ltac val_help_H H:=
    simpl in H;
    try change (Int.ltu Int.zero Int.zero) with (false) in H;
    try change (Int.ltu Int.one Int.zero) with (false) in H;
    try change (Int.ltu Int.zero Int.one) with (true) in H;
    try change (Int.ltu Int.one Int.one) with (false) in H;
    try change (Int.eq Int.one Int.one) with (true) in H;
    try change (Int.eq Int.one Int.zero) with (false) in H;
    try change (Int.eq Int.zero Int.one) with (false) in H;
    try change (Int.eq Int.zero Int.zero) with (true) in H.

Ltac val_help:=
  try change (Int.ltu Int.zero Int.zero) with (false);
  try change (Int.ltu Int.one Int.zero) with (false);
  try change (Int.ltu Int.zero Int.one) with (true);
  try change (Int.ltu Int.one Int.one) with (false);
  try change (Int.eq Int.one Int.one) with (true);
  try change (Int.eq Int.one Int.zero) with (false);
  try change (Int.eq Int.zero Int.one) with (false);
  try change (Int.eq Int.zero Int.zero) with (true).
Lemma list_trans: 
forall t (l1 l2 l3 : list t) a b,
  l1 ++ (a :: l2) ++ (b :: l3) = l1 ++ (a :: (l2 ++ b :: l3)).
Proof.
  intros.
  simpl. auto.
Qed.

Lemma list_trans_1:
forall t (l1 l2 l3 : list t) a b,
l1 ++ (a :: l2) ++ (b :: l3) = (l1 ++ a :: l2) ++ b :: l3.
Proof.
intros.
simpl. auto.
rewrite app_assoc_reverse.
simpl. auto.
Qed.



Lemma list_trans_2:
  forall t (l1 l2 l3 : list t) a b,
  l1 ++ (a):: l2 ++ (b) :: l3 = (l1 ++ a :: l2) ++ b :: l3.
Proof.
  intros.
  simpl. auto.
  rewrite app_assoc_reverse.
  simpl. auto.
Qed.

Lemma func_capability_if_true_range:
forall v'2,
val_inj
      (bool_or
         (val_inj
            (if
              Int.ltu v'2
                ($ CAP_NULL_CLASS)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))
         (val_inj
            (if
              Int.ltu ($ CAP_CHANNEL_CLASS)
                v'2
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))) <>
    Vint32 Int.zero -> CAP_NULL_CLASS > Int.unsigned v'2 \/
    Int.unsigned v'2 > CAP_CHANNEL_CLASS.
Proof.
  intros.
  destruct (Int.ltu v'2
  ($ CAP_NULL_CLASS)) eqn: Hlt1;
  destruct (Int.ltu
  ($ CAP_CHANNEL_CLASS)
  v'2) eqn: Hlt2; val_help_H H; simpl in H; tryfalse.
  rewrite Intlt_true_is_Zlt in Hlt1.
  rewrite Int.unsigned_repr in Hlt1.
  lia. unfold CAP_NULL_CLASS. rewrite max_unsigned_val. lia.
  rewrite Intlt_true_is_Zlt in Hlt1.
  rewrite Int.unsigned_repr in Hlt1.
  lia. unfold CAP_NULL_CLASS. rewrite max_unsigned_val. lia.
  rewrite Intlt_true_is_Zlt in Hlt2.
  rewrite Int.unsigned_repr in Hlt2.
  lia. unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val.
  lia.
Qed.


Lemma func_capability_if_false_range:
forall v'2,
val_inj
(bool_or
   (val_inj
      (if
        Int.ltu v'2 ($ CAP_NULL_CLASS)
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)))
   (val_inj
      (if
        Int.ltu ($ CAP_CHANNEL_CLASS)
          v'2
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)))) =
Vint32 Int.zero \/
val_inj
(bool_or
   (val_inj
      (if
        Int.ltu v'2 ($ CAP_NULL_CLASS)
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)))
   (val_inj
      (if
        Int.ltu ($ CAP_CHANNEL_CLASS)
          v'2
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)))) =
Vnull ->CAP_NULL_CLASS <=Int.unsigned v'2 <= CAP_CHANNEL_CLASS .
Proof.
  intros.
  unfold val_inj, bool_or in H.
  destruct (Int.ltu v'2 ($ CAP_NULL_CLASS)) eqn: Hlt1;
  destruct (Int.ltu ($ CAP_CHANNEL_CLASS) v'2) eqn: Hlt2;
  val_help_H H; simpl in H;destruct H; tryfalse;
  try(rewrite Intlt_false_is_Zge in Hlt1);
  try(rewrite Intlt_false_is_Zge in Hlt2);
  try(rewrite Int.unsigned_repr in Hlt1);
  try(rewrite Int.unsigned_repr in Hlt2);
  try lia.
  unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val. lia.
  unfold CAP_NULL_CLASS. rewrite max_unsigned_val. lia.
  unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val. lia.
Qed.

Lemma S_add_sub_S_add:
    forall x y z,
    (S y <= x)%nat ->
    (S (x - S y + z) = x - y + z)%nat. 
Proof.
  induction z; intros.
  rewrite Nat.add_0_r.
  rewrite Nat.add_0_r.
  rewrite S_add_sub_S; auto.
  eapply IHz in H.
  rewrite Nat.add_succ_r.
  rewrite Nat.add_succ_r.
  rewrite H. auto.
Qed.

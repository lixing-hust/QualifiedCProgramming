Require Import include_frm.
Require Import os_code_defs.
Require Import code_notations.
Require Import seplog_trm_tacs.
Require Import os_ucos_h.
Require Import os_inv.
Require Import inv_prop.
Require Import frmaop_sol.
Require Import derived_rules.
Require Import math_auto.
Require Import sep_auto.
Require Import symbolic_lemmas.
Require Import symbolic_execution.
Require Import Aarray_new_common.
Require Import gjb_common.
Require Import hoare_assign_tac_ext.
Require Import pure_lib.
Require Import ucos_pauto.

Local Open Scope code_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Ltac hoare_enter_critical2 :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- {|_ , _, ?li , _, _, _|}|-_ {{?P}} (sprim encrit) {{_}} =>
        hoare_lifts_trms_pre (Aop, Aisr, Aier, Aie, Ais, Acs);
        eapply encrit2_rule';
        [ eauto
          | apply GoodI_I
          | good_frm_sovler;
            try (unfold GoodFrm; fold GoodFrm);
            do 3 try (splits; try intros; try tauto);
            try good_frm_sovler
          ]
  end.

Ltac hoare_exit_critical2 :=
  match goal with
    | |- {|_ , _, ?li , _, _, _|}|- _ {{?P}} (sprim excrit) {{_}} =>
          hoare_lifts_trms_pre (Aop, Aisr, Aier, Aie, Ais, Acs);
            eapply excrit2_rule';
            [ eauto
            | apply GoodI_I
            | good_frm_sovler;
            try (unfold GoodFrm; fold GoodFrm);
            do 3 try (splits; try intros; try tauto);
            try good_frm_sovler
            ]
  end.

Lemma pos_to_nat_8: Pos.to_nat 8 = 8%nat. 
auto with arith. Qed. 

Lemma ge_ne_lt_8:
  forall i, 
  Int.unsigned ($ 8) >= Int.unsigned i ->
    i <> $ 8 ->
    (Z.to_nat (Int.unsigned i) < 8)%nat. 
Proof.
  intros.
  assert (Int.unsigned i <> 8).
  { intro Hf. apply H0. destruct Hf. int auto. }
  asserts_rewrite (Int.unsigned ($8) = 8) in H. { int auto. } 
  auto with zarith.
Qed.

Lemma pos_to_nat_10: Pos.to_nat 10 = 10%nat. 
auto with arith. Qed.

Lemma nth_vallist_neq : 
 forall vll1 vl vl' vll2 curvl n,
  n <> length vll1 ->
  nth_vallist n (vll1 ++ vl::vll2) = Some curvl ->
  nth_vallist n (vll1 ++ vl'::vll2) = Some curvl.
Proof.
intros vll1 vl vl' vll2 curvl n H_neq H_eq.
generalize dependent n.
induction vll1 as [ | hd tl IH]; intros.
- simpl in *. destruct n; try congruence.
- simpl in *. destruct n; auto.
Qed.

Lemma nth_error_neq:
forall (A : Type) (vll1 : list A) (vl vl' : A) (vll2 : list A) (curvl : A) (n : nat),
       n <> length vll1 ->
       nth_error (vll1 ++ vl :: vll2) n = Some curvl ->
       nth_error (vll1 ++ vl' :: vll2) n= Some curvl.
Proof.
intros A vll1 vl vl' vll2 curvl n H_neq H_eq.
generalize dependent n.
induction vll1 as [ | hd tl IH]; intros.
- simpl in *. destruct n; try congruence.
   simpl in *. auto.
- simpl in *. destruct n; auto.
   simpl in *. eapply IH; eauto.
Qed.

Lemma nth_error_eq_nth_vallist :
forall vll n vl,
nth_error vll n = Some vl <->
nth_vallist n vll = Some vl.
Proof.
induction vll; intros.
rewrite nth_error_nil.
simpl.
tauto.
destruct n; simpl.
tauto.
rewrite IHvll; tauto.
Qed.

Lemma Int_repr_add :
forall x y,
   0 <= x ->
   0 <= y ->
    x + y <= Int.max_unsigned ->
   Int.repr (x + y) = Int.add(Int.repr x) (Int.repr y).
Proof.
intros.
int auto.
Qed.

Lemma pos_to_nat_usr_max_evts:
 Pos.to_nat (Z.to_pos (OS_USER_MAX_EVENTS / 3)) = Z.to_nat (OS_USER_MAX_EVENTS / 3).
Proof.
lets Hrgn : usr_max_evts_rgn; destruct Hrgn as (Hrgn1, Hrgn2).
rewrite <- Z2Nat.inj_pos.
rewrite Z2Pos.id; auto.
auto with zarith.
Qed.

Lemma ge_ne_lt_usr_max_evts:
  forall i, 
  Int.unsigned ($ (OS_USER_MAX_EVENTS / 3)) >= Int.unsigned i ->
    i <> $ (OS_USER_MAX_EVENTS / 3) ->
    (Z.to_nat (Int.unsigned i) < Z.to_nat (OS_USER_MAX_EVENTS / 3))%nat. 
Proof.
  intros.
  rewrite <- ZIntneq_is_Zneq in H0.
  lets Hrgn : usr_max_evts_rgn; destruct Hrgn as (Hrgn1, Hrgn2).
  rewrite Int.unsigned_repr in H, H0; try solve_usr_max_evts_rgn.
Qed.

Lemma ptrconst_rv: 
  forall (s : RstateOP) a, s |= Rv eptrconst a @ (Tptr Tint32) == Vptr a.
Proof.
  intros.
  simpl.
  destruct s as [[[[[[[]]]]]]].
  simpl.
  splits; auto.
Qed.

Theorem Tptr_bop_rv :
  forall s e1 e2 v1 t1 v2  v t ,
    s |= Rv e1 @  (Tptr t1) == v1 ->
    s |= Rv e2 @ Tint32 == v2 ->
    val_inj (bop_eval v1 v2 (Tptr t1) Tint32 obitand_ptr) = v ->
    v <> Vundef ->
   bop_type (Tptr t1) Tint32 obitand_ptr = Some t -> 
    s |= Rv (ebinop obitand_ptr e1 e2) @ (Tptr t1) == v.
Proof.
intros.
  destruct s as [ [ [ [ [ [ [  ] ] ] ] ] ] ]. 
  simpl in *; mytac; auto.
  rewrite H6.
  rewrite H4. 
 rewrite H3. 
 rewrite H.  
destruct v1; simpl in H2; tryfalse.  
rewrite H0.
destruct a0.
destruct v2; simpl in H2; tryfalse.
simpl; eauto.
Qed.

Lemma new_array_type_vallist_match_split2_gen
: forall (vll vll1 vll2 : list vallist) tp,
       new_array_type_vallist_match tp vll ->
       vll = vll1 ++ vll2 ->
       new_array_type_vallist_match tp vll1 /\
       new_array_type_vallist_match tp vll2.
Proof.
  inductions vll.
  -  intros.
     symmetry in H0.
     apply app_eq_nil in H0.
     destruct H0. subst vll1 vll2. 
     simpl. auto.
  - introv Hmt1 Hlst.
    destruct vll1.
    simpl in Hlst.
    destruct vll2; inverts Hlst.
    split; simpl; auto.
    rewrite <- app_comm_cons in Hlst.
    inverts Hlst.
    destruct tp;
    simpl new_array_type_vallist_match in *;
    destruct Hmt1 as (Ha & Hmt);
    eapply IHvll in Hmt; eauto;
    simpljoin;
    splits; auto.
Qed.

Lemma new_array_type_vallist_match_split1_gen
: forall (vll vll1 vll2 : list vallist) vl tp id decls,
       new_array_type_vallist_match tp vll ->
       vll = vll1 ++ (vl :: vll2) ->
       tp = Tstruct id decls ->
       new_array_type_vallist_match tp vll1 /\
       new_array_type_vallist_match tp vll2 /\
       struct_type_vallist_match tp vl.
Proof.
intros.
eapply new_array_type_vallist_match_split2_gen in H; eauto.
subst.
simpl new_array_type_vallist_match in *.
simpljoin.
splits; auto.
Qed.

Lemma nth_vallist_get_some:
  forall vll idx,
  (idx < length vll)%nat ->
  exists vl, nth_vallist idx vll = Some vl.
Proof.
induction vll; simpl length.
intros.
false. eapply Nat.nlt_0_r; eauto.
intros.
simpl.
destruct idx; eauto.
eapply lt_S_n in H.
eapply IHvll; eauto.
Qed.

Lemma eight_min_max:
 Int.min_signed <= 8 <= Int.max_signed.
Proof.
int auto.
Qed.

Lemma nth_error_middle {A: Type}:
  forall l1 l2 (a: A),
    nth_error (l1 ++ a :: l2) (length l1) = Some a.
Proof.
  intros.
  replace a with (nth (length l1) (l1 ++ a :: l2) a) at 2;
  [ |apply nth_middle].
  apply nth_error_nth'.
  rewrite app_length; simpl.
  auto with zarith.
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

Ltac destruct_absuconf v:= 
  destruct v as [[[[[[[[[[[[[]]]]]]]]]]]]].

Ltac unfold_bootaddr boot_b :=
   unfold BOOT_DATA_ADDRESS in *; remember (2147483648%positive) as boot_b.


Ltac conv_max_unsigned' :=
  try change Int.max_unsigned with 4294967295 in *;
  try change Int.max_signed with 2147483647 in *;
  try change Int.min_signed with (Z.opp 2147483648) in *.

Ltac unfold_part_defs :=
try unfold CORENUM in *;
try unfold DSCHEDULE_SIZE in *;
try unfold DOMAIN_SIZE in *;
try unfold PARTITION_NUM in *;
try unfold PORT_NUMS in *;
try unfold PTHREAD_STACK_MIN in *;
try change (Z.to_nat (2 * 4096 / 4)) with 2048%nat.

Ltac solve_part_int_rgn :=
conv_max_unsigned';
unfold_part_defs;
auto with zarith.

Lemma cnum_le:
forall cnum,
            Int.unsigned cnum < CORENUM ->
            Int.unsigned cnum <= Int.max_signed.
solve_part_int_rgn.
Qed.

Lemma cnum_le':
forall cnum,
            Z.of_nat cnum < CORENUM ->
            Z.of_nat cnum <= Int.max_signed.
solve_part_int_rgn.
Qed.

Lemma cpu_conf_t_min_max:
     (Int.min_signed <= 910 <= Int.max_signed)%Z.
solve_part_int_rgn.
Qed.

Lemma struct_array_member_rv':
  forall decls s e1 te1 e2 te2 b o t n m vl v k t' id sid P, 
    s |= Rv e1 @ te1 == Vptr (b, o) ->
    s |= Rv e2 @ te2 == Vint32 m ->
    (te1 = Tarray t n \/ te1 = t ∗) -> 
    (te2 = Int8u \/ te2 = Int16u \/ te2 = Int32u) ->
    s |= Astruct (b, o +ᵢ  $ Z.of_nat (Z.to_nat (Int.unsigned m) * typelen t)) t vl ** P -> 
    t = Tstruct sid decls -> 
    good_decllist decls = true -> 
    Int.ltu m Int.zero = false -> 
    Int.unsigned m <= Int.max_signed -> 
    Int.min_signed <= Z.of_nat (szstruct decls) <= Int.max_signed -> 
    struct_type_vallist_match t vl -> 
    ftype id decls = Some t' ->
    (~(exists t'' n, t' = Tarray t'' n) /\ ~(exists sid' ds', t' = Tstruct sid' ds')
    /\ ~(exists sid' ds', t' = Tunion sid' ds')) ->  
    (id_nth id decls) = Some k ->
    nth_val' k vl = v -> 
    s |= Rv efield (e1[e2]) id @ t' == v. 
Proof. 
  introv He1 He2 Hte1 Hte2 Hastruct Ht Hgdecls Hmgez. 
  introv Hmle Hszrgn.
  introv Hmt Hidtp Ht' Hoff Hv. 
  subst t.
  unfold Astruct in Hastruct.
  assert (Hnth: nth_id k decls = Some id).
  { apply id_nth_eq; auto. }
  pose proof (nth_id_exists_off _ _ Hnth).
  destruct H as (off & Hfdoff).
  gen Hv.
  destruct Hastruct. simpljoin1.
  introv Hv.
  rename H8 into Hastruct.
  erewrite struct_asrt_eq with (id:=id) (dls:=decls) (v:=v) (t:=t') (n:=k) in Hastruct;
    eauto.
  2: {
    subst v. apply nth_val_imp_nth_val'_2.
    assert (k < len_decllist decls)%nat.
    { eapply id_nth_lt_len; eauto. }
    erewrite <- astruct_dls_vl_len; eauto.
  }

  destruct s as [[[[[[[]]]]]]].
  destruct Hastruct. 
  gen Hv.
  simpljoin1. change_smo_hyps.
  destruct H11.
  simp_mem_abst.
  simpl in H.

  destruct He1.  destruct He2. mytac. intro Hv.
  simpl in H11. simpl in H13. simpl in H14. simpl in H15.

  assert (Hrtpvmt: rule_type_val_match t' v = true).
  { eapply struct_rule_type_vll_mt; eauto. }

  simpl_sat_goal.
  change (getsmem (e, e0, m0, i, i0, l, o0, a)) with (e, e0, m0).
  simpl.
  rewrite H13.

  destruct Hte1 as [Hte1' | Hte1']; subst te1; 
  rewrite H15; 
    destruct Hte2 as [Hte2' | [Hte2' | Hte2']]; subst te2;
    try (
        rewrite Hidtp; 
        rewrite H11; 
        rewrite H14; 
        unfold getoff;  
        simpl; rewrite H13; rewrite H15;
        rewrite Hfdoff; 
        splits; auto;
        [
          eapply mapstoval_load in H; auto;
          simpl; rewrite Int.repr_unsigned;
          rewrite <- mul_sz_decls; auto;
          assert (Hsub: Maps.sub x1 m0) by (join_to_sub; eapply sub_trans; eauto);
          eapply lmachLib.load_mem_mono; eauto
        |
          eapply rule_type_val_match_nvundef; eauto]).
Qed.

Lemma struct_array_member_rv_array:
  forall decls s e1 te1 e2 te2 b o t n m v t' id sid off t'' n', 
    s |= Rv e1 @ te1 == Vptr (b, o) ->
    s |= Rv e2 @ te2 == Vint32 m -> 
    (te1 = Tarray t n \/ te1 = t ∗) -> 
    (te2 = Int8u \/ te2 = Int16u \/ te2 = Int32u) ->
    t = Tstruct sid decls -> 
    good_decllist decls = true -> 
    Int.ltu m Int.zero = false -> 
    Int.unsigned m <= Int.max_signed -> 
    Int.min_signed <= Z.of_nat (szstruct decls) <= Int.max_signed -> 
    ftype id decls = Some t' ->
    field_offset id decls = Some off ->
    t' = Tarray t'' n' /\ (exists sid' ds', t'' = Tstruct sid' ds') ->
    v = Vptr (b, (o +ᵢ  $ Z.of_nat (Z.to_nat (Int.unsigned m) * typelen t)) +ᵢ off) ->
    s |= Rv efield (e1[e2]) id @ t' == v.
Proof.
 introv He1 He2 Hte1 Hte2 Ht Hgdecls Hmgez.
  introv Hmle Hszrgn.
  introv Hidtp Hoff Ht' Hv.
  destruct Ht' as (Ht' & (sid' & ds' & Ht'')).
  subst t. subst t' t''.
  destruct s as [[[[[[[]]]]]]].
  simpljoin1. change_smo_hyps.
  simp_mem_abst.
  destruct He1.  destruct He2. simpljoin.
  simpl in H1, H2, H3, H4.
  simpl_sat_goal.
  change (getsmem (e, e0, m0, i, i0, l, o0, a)) with (e, e0, m0) in *.
  simpl.
  rewrite H1, H2, H3, H4.
  destruct Hte1 as [Hte1' | Hte1']; subst te1;
  destruct Hte2 as [Hte2' | [Hte2' | Hte2']]; subst te2;
  rewrite Hidtp;
  unfold getoff;
  simpl;
  rewrite H2, H4;
  rewrite Hoff;
  unfold addrval_to_addr;
  unfold addr_to_addrval;
  splits; auto;
  do 2 rewrite Int.repr_unsigned;
  rewrite <- mul_sz_decls; auto.
Qed.

Lemma array_array_member_rv:
  forall s e1 te1 e2 te2 b o t n m v t' n', 
    s |= Rv e1 @ te1 == Vptr (b, o) ->
    s |= Rv e2 @ te2 == Vint32 m -> 
    (te1 = Tarray t n \/ te1 = t ∗) -> 
    (te2 = Int8u \/ te2 = Int16u \/ te2 = Int32u) ->
    t = Tarray t' n' ->
    Z.of_nat (typelen t' * n') <= Int.max_unsigned ->
    v = Vptr (b, (o +ᵢ  $ Z.of_nat (Z.to_nat (Int.unsigned m) * typelen t))) ->
    s |= Rv (e1[e2]) @ t == v.
Proof.
 introv He1 He2 Hte1 Hte2 Ht' Hrgn Hv.
  subst t.
  destruct s as [[[[[[[]]]]]]].
  simpljoin1. change_smo_hyps.
  simp_mem_abst.
  destruct He1.  destruct He2. simpljoin.
  simpl in H1, H2, H3, H4.
  simpl_sat_goal.
  change (getsmem (e, e0, m0, i, i0, l, o0, a)) with (e, e0, m0) in *.
  simpl.
  rewrite H, H0, H1, H2.
  destruct Hte1 as [Hte1' | Hte1']; subst te1;
  destruct Hte2 as [Hte2' | [Hte2' | Hte2']]; subst te2;
  simpl;
  splits; auto;
  rewrite Nat2Z.inj_mul with (m:= (typelen t' * n')%nat);
  rewrite Z2Nat.id; try solve [apply Int.unsigned_range_2];
  rewrite Int.repr_unsigned;
  rewrite Int.mul_commut;
  unfold Int.mul;
  rewrite Int.unsigned_repr; try split; auto with zarith.
Qed.

Ltac sep_get_rv_array_struct_conf :=
let Hsat := fresh in
let Hf := fresh in
let Heq := fresh in
match goal with
| |- ?P ==> Rv efield ((efield (ederef ?gident) ?id1)[?ident ′]) ?id2 @ ?tp1 == _ =>
      introv Hsat;
      eapply struct_array_member_rv';
      [ try symbolic_execution; eauto
      | try symbolic_execution
      | auto
      | auto
      | try (match goal with
                  Hsat: _ |= ?P' |- _ |= Astruct (?pb, ?pi) _ _ ** _ =>
                     match find_ptrstruct_by_block P' pb with
                       | some ?n => sep lifts (( n) :: nil) in Hsat
                       end
                  end);
         try sep cancel Astruct; eauto
      | match goal with
        | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
        end; auto
      | simpl; auto
      | try apply int_ltu_zero_eq_false
      | try (apply cnum_le; auto); try (apply cnum_le'; auto)
      | simpl; try apply cpu_conf_t_min_max
      | auto
      | simpl; auto
      | splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
      | unfold id_nth; simpl; auto
      | auto ]
| Hsat:?s |= ?P
  |- ?s |= Rv efield ((efield (ederef ?gident) ?id1)[?ident ′]) ?id2 @ ?tp1 == _ =>
              eapply struct_array_member_rv';
              [ try symbolic_execution; eauto
              | try symbolic_execution
              | auto
              | auto
              | try (match goal with
                          Hsat: _ |= ?P' |- _ |= Astruct (?pb, ?pi) _ _ ** _ =>
                             match find_ptrstruct_by_block P' pb with
                               | some ?n => sep lifts (( n) :: nil) in Hsat
                               end
                          end);
                 try sep cancel Astruct; eauto
              | match goal with
                | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
                end; auto
              | simpl; auto
              | try apply int_ltu_zero_eq_false
              | try (apply cnum_le; auto); try (apply cnum_le'; auto)
              | simpl; try apply cpu_conf_t_min_max
              | auto
              | simpl; auto
              | splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
              | unfold id_nth; simpl; auto
              | auto ]
end.

Ltac sep_get_rv_array_struct_array:=
let Hsat := fresh in
match goal with
| |- ?P ==> Rv (efield ((efield (ederef ?gident) ?id3) [?ident2′]) ?id2) @ ?tp2 == _ =>
       introv Hsat;
       eapply struct_array_member_rv_array;
       [ try symbolic_execution; eauto
         | try symbolic_execution
         | match goal with
           | |- ((?te = _) \/ _) =>
               match te with 
                 | Tarray ?tp _ => try unfold tp
                 | Tptr ?tp => try unfold tp
                 | _ => idtac
                 end
           end; auto
         | auto
         | match goal with
            | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
            end; auto
         | simpl; auto
         | try apply int_ltu_zero_eq_false
         | try solve_part_int_rgn
         | simpl; try solve_part_int_rgn
         | simpl; auto
         | unfold field_offset; simpl; auto
         | match goal with | |- (Tarray ?tp _ = _) /\ _ => try unfold tp end;eauto
         | auto ]
 | Hsat: _ |= _ |- _ |= Rv (efield ((efield (ederef ?gident) ?id3) [?ident2′]) ?id2) @ ?tp2 == _ =>
       eapply struct_array_member_rv_array;
       [ try symbolic_execution; eauto
         | try symbolic_execution
         | match goal with
           | |- ((?te = _) \/ _) =>
               match te with 
                 | Tarray ?tp _ => try unfold tp
                 | Tptr ?tp => try unfold tp
                 | _ => idtac
                 end
           end; auto
         | auto
         | match goal with
            | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
            end; auto
         | simpl; auto
         | try apply int_ltu_zero_eq_false
         | try solve_part_int_rgn
         | simpl; try solve_part_int_rgn
         | simpl; auto
         | unfold field_offset; simpl; auto
         | match goal with | |- (Tarray ?tp _ = _) /\ _ => try unfold tp end;eauto
         | auto ]
end.

Ltac sep_get_rv_array_struct_conf' :=
let Hsat := fresh in
let Hf := fresh in
let Heq := fresh in
match goal with
| |- ?P ==> Rv efield ( (efield ((efield (ederef ?gident) ?id3) [?ident2′]) ?id2) [?ident1′]) ?id1 @ ?tp1 == _ =>
      introv Hsat;
      eapply struct_array_member_rv';
      [ try sep_get_rv_array_struct_array
      | try symbolic_execution
      | auto
      | auto
      | try (match goal with
                  Hsat: _ |= ?P' |- _ |= Astruct (?pb, ?pi) _ _ ** _ =>
                     match find_ptrstruct_by_block P' pb with
                       | some ?n => sep lifts (( n) :: nil) in Hsat
                       end
                  end);
         try simpl typelen; try sep cancel Astruct; eauto
      | match goal with
        | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
        end; auto
      | simpl; auto
      | try apply int_ltu_zero_eq_false
      | try solve_part_int_rgn
      | simpl; try solve_part_int_rgn
      | auto
      | simpl; auto
      | splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
      | unfold id_nth; simpl; auto
      | auto ]
| Hsat:?s |= ?P
  |- ?s |= Rv efield ( (efield ((efield (ederef ?gident) ?id3) [?ident2′]) ?id2) [?ident1′]) ?id1 @ ?tp1 == _ =>
              eapply struct_array_member_rv';
              [ try sep_get_rv_array_struct_array
              | try symbolic_execution
              | auto
              | auto
              | try (match goal with
                          Hsat: _ |= ?P' |- _ |= Astruct (?pb, ?pi) _ _ ** _ =>
                             match find_ptrstruct_by_block P' pb with
                               | some ?n => sep lifts (( n) :: nil) in Hsat
                               end
                          end);
                 try simpl typelen; try sep cancel Astruct; eauto
              | match goal with
                | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
                end; auto
              | simpl; auto
              | try apply int_ltu_zero_eq_false
              | try solve_part_int_rgn
              | simpl; try solve_part_int_rgn
              | auto
              | simpl; auto
              | splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
              | unfold id_nth; simpl; auto
              | auto ]
end.

Theorem cast_rv_int32_to_ptr :
  forall s e v t,
    s |= Rv e @ (Tint32) == Vint32 v ->
    s |= Rv (ecast e (Tptr t)) @ (Tptr t) == Vptr (int32_to_ptr v).
Proof.
  intros.
  unfold sat;fold sat.
  destruct_s s.
  simpl in H.
  destructs H.
  simpl.
  rewrite H, H0.
  simpl.
  splits;auto.
Qed.

Theorem cast_rv_ptr_to_int32 :
  forall s e v t,
    s |= Rv e @ (Tptr t) == Vptr v ->
    s |= Rv (ecast e (Tint32)) @ (Tint32) == Vint32 (ptr_to_int32 v).
Proof.
  intros.
  unfold sat;fold sat.
  destruct_s s.
  simpl in H.
  destructs H.
  simpl.
  rewrite H, H0.
  simpl.
  splits;auto.
Qed.

Lemma struct_type_vallist_match_domain_conf_t:
forall vl, struct_type_vallist_match domain_conf_t vl ->
           exists v v0 v1 v2 v3 v4 v5 v6 v7 v8, exists v9 v10 v11 v12 v13 v14,
           vl = (v :: v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: v13 :: v14 :: nil).
Proof.
intros.
repeat try (destruct vl; simpl in *; tryfalse; simpljoin).
repeat eexists; eauto.
Qed.

Hint Resolve ucos_frmaop.GoodFrm_AOSCSpacePrioTbl : good_frm_lemmas.

Lemma ARootTaskStk'_len: 
  forall s vl, s |= ARootTaskStk' vl -> length vl = ∘ (PARTITION_NUM).
Proof.
  introv Hsat.
  unfold ARootTaskStk' in *.
  sep split in Hsat.
  simpljoin1.
  auto.
Qed.

Lemma ARootTaskStk'_len_frm:
  forall s vl P, s |= ARootTaskStk' vl ** P -> length vl = ∘ (PARTITION_NUM).
Proof.
  introv Hsat.
  unfold ARootTaskStk' in *.
  sep split in Hsat.
  simpljoin1.
  auto.
Qed.

Lemma ARootTaskStk'_unfold_any_idx: 
  forall s vll idx,
    s |= ARootTaskStk' vll ->
    (idx < length vll)%nat ->
    s |= EX vll1 vll2 b i vl type,
          [| RootTaskStk_head = (b, i) |] **
          [| type = (Tarray Tint32 (nat_of_Z (2 * PTHREAD_STACK_MIN/4 ))) |] **
          GV RootTaskStk @ (Tptr type) |-> (Vptr (b,i)) **
          Aarray_new (b, i) (Tarray type idx) vll1 **
          Aarray (b, i +ᵢ $ Z.of_nat (idx * (typelen type))) type vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen type))))
          (Tarray type (∘ (PARTITION_NUM - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match type vll |] **
          [| length vll = ∘ (PARTITION_NUM) |] **
          [| (forall n vl, nth_vallist n vll = Some vl -> length vl = (nat_of_Z (2 * PTHREAD_STACK_MIN/4 ))) |] **
          [| vll = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (PARTITION_NUM - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= PARTITION_NUM |].
Proof.
  introv Hsat Hlenle.
  remember (Tarray Tint32 (nat_of_Z (2 * PTHREAD_STACK_MIN/4 ))) as type.
  assert (Hlengt: Z.of_nat (length vll * typelen type) <= Int.max_unsigned). 
  { erewrite ARootTaskStk'_len; eauto. subst. unfold typelen. unfold nat_of_Z. solve_part_int_rgn.  }
  unfold ARootTaskStk' in Hsat.
  rewrite <- Heqtype in *.
  sep destruct Hsat.
  sep split in Hsat.
  rename H into Hmat; rename H0 into Hlen; rename H1 into Hlen_sub.
  destruct RootTaskStk_head.
  assert (Hlen_eq: (length vll = idx + (length vll - idx))%nat) 
    by auto with arith.
  lets Hsplit: (firstn_skipn idx vll).
  unfold nat_of_Z in *.
  rewrite <- Hlen in Hsat.
  rewrite Hlen_eq in Hsat.
  rewrite <- Hsplit in Hsat.
   assert (Hlens: length (firstn idx vll) = idx /\ length (skipn idx vll) = (length vll - idx)%nat).
  { rewrite Hsplit in *.
    split. 
    apply firstn_length_le. auto with arith.
    apply skipn_length.
  }
  sep lift 2%nat in Hsat.
  eapply Aarray_new_split_strong_frm in Hsat.
   assert (HlenS: (length vll - idx = S (length vll - (S idx)))%nat).
  {
    rewrite NPeano.Nat.sub_succ_r.
    rewrite Nat.lt_succ_pred with (z:=0%nat); auto.
    rewrite <- Nat.lt_add_lt_sub_r. simpl. auto.
  }
  rewrite Hsplit in Hsat.
  rewrite HlenS in Hsat.
  assert (Hln: (length (skipn idx vll) > 0)%nat).
  {
    rewrite skipn_length.  
    cut (0 < length vll - idx)%nat.
    auto with arith.
    rewrite <- NPeano.Nat.lt_add_lt_sub_l.
    rewrite Nat.add_0_r. auto.
  }
  apply length_exists in Hln.
  destruct Hln as (vh & vlt & Hlst). rewrite Hlst in *.
  sep pauto; eauto.
  sep cancel Aarray_new.
  eapply Aarray_new_succ_imp in Hsat.
  remember (Tarray long (Z.to_nat (2 * PTHREAD_STACK_MIN / 4))) as type.
  assert (Hsimp: $ Z.of_nat (idx * typelen type) +ᵢ  $ Z.of_nat (typelen type) =
                   $ Z.of_nat (S idx * typelen type)).
  {
    rewrite <- Nat.add_1_r.
    rewrite NPeano.Nat.mul_add_distr_r. 
    rewrite Nat2Z.inj_add.
    rewrite Nat.mul_1_l.
    subst.
    unfold typelen.
    rewrite Int.add_unsigned.
    rewrite Int.unsigned_repr; auto.
    rewrite Hlen in *.
    unfold typelen in *.
    clear -Hlenle Hlengt.
    solve_part_int_rgn.
  }
  rewrite Int.add_assoc in Hsat.
  rewrite Hsimp in Hsat.
  rewrite Z2Nat.inj_sub; auto with zarith.
  rewrite <- Hlen.
  rewrite Nat2Z.id.
  unfold Aarray_new at 1 in Hsat.
  subst.
  unfold Aarray_new' in Hsat.
  sep pauto.
  rewrite Hlen in *.
  auto with zarith.
  split; auto.
  eapply Nat.succ_inj.
  simpl length in *.
  rewrite H0.
  rewrite Hlen in *.
  auto with zarith.
  {
    apply Z.le_trans with (m:=Z.of_nat (length vll * typelen type));
      auto.
    apply inj_le. 
    apply NPeano.Nat.mul_le_mono_r; auto.
  }
  rewrite Hsplit.
  auto.
Qed.

Lemma ARootTaskStk'_unfold_any_idx_frm: 
  forall s vll idx P,
    s |= ARootTaskStk' vll ** P->
    (idx < length vll)%nat ->
    s |= (EX vll1 vll2 b i vl type,
          [| RootTaskStk_head = (b, i) |] **
          [| type = (Tarray Tint32 (nat_of_Z (2 * PTHREAD_STACK_MIN/4 ))) |] **
           GV RootTaskStk @ (Tptr type) |-> (Vptr (b,i)) **
          Aarray_new (b, i) (Tarray type idx) vll1 **
          Aarray (b, i +ᵢ $ Z.of_nat (idx * (typelen type))) type vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen type))))
          (Tarray type (∘ (PARTITION_NUM - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match type vll |] **
          [| length vll = ∘ (PARTITION_NUM) |] **
          [| (forall n vl, nth_vallist n vll = Some vl -> length vl = (nat_of_Z (2 * PTHREAD_STACK_MIN/4 ))) |] **
          [| vll = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (PARTITION_NUM - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= PARTITION_NUM |]) ** P.
Proof.
intros.
sep cancel P.
eapply ARootTaskStk'_unfold_any_idx; eauto.
Qed.

Lemma ARootTaskStk'_select_sn_strong :
  forall vll1 idx vll2 b i s vl type,
    Z.of_nat(S idx) <= PARTITION_NUM ->
    RootTaskStk_head = (b, i) ->
    type = (Tarray Tint32 (nat_of_Z (2 * PTHREAD_STACK_MIN/4 ))) ->
    s |=  GV RootTaskStk @ (Tptr type) |-> (Vptr (b,i)) **
            Aarray_new (b, i) (Tarray type idx) vll1 **
            Aarray (b, i +ᵢ $ Z.of_nat (idx * (typelen type))) type vl **
            Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen type))))
                                     (Tarray type (∘ (PARTITION_NUM - Z.of_nat (S idx)))) vll2  ->
    new_array_type_vallist_match type (vll1 ++ (vl::vll2)) ->
    length (vll1 ++ (vl::vll2)) = ∘ (PARTITION_NUM) ->
    (forall n vl', nth_vallist n (vll1 ++ (vl::vll2)) = Some vl' -> length vl' = (nat_of_Z (2 * PTHREAD_STACK_MIN/4 ))) ->
    s |= ARootTaskStk' (vll1 ++ (vl::vll2)).
Proof.
  intros.
  assert (Hrgn: Z.of_nat (S idx * typelen type) <= Int.max_unsigned).
  {
    remember (typelen type) as X.
    subst.
    unfold typelen.
    unfold nat_of_Z. solve_part_int_rgn.
  }
  unfold ARootTaskStk'.
  sep pauto.
  assert (Heq: ∘ (PARTITION_NUM) 
               =  Nat.add idx (S (∘ (PARTITION_NUM - Z.of_nat(S idx))) )).
  unfold nat_of_Z.
  assert (Heq1: Z.to_nat (PARTITION_NUM - Z.of_nat (S idx)) 
              = Nat.sub (Z.to_nat (PARTITION_NUM))  (Z.to_nat (Z.of_nat (S idx))) ).
  apply Z2Nat.inj_sub.
  eauto with zarith.
  rewrite Heq1.
  eauto with zarith.
  unfold nat_of_Z in *.
  rewrite Heq.
  rewrite H0.
  eapply Aarray_new_compose_strong; eauto.
  sep pauto.
  eapply Aarray_new_succ.
  rewrite Int.add_assoc.
  remember (Tarray long (Z.to_nat (2 * PTHREAD_STACK_MIN / 4))) as type.
  asserts_rewrite ($ Z.of_nat (idx * typelen type) +ᵢ  $ Z.of_nat (typelen type) 
                   = $ Z.of_nat (S idx * typelen type)).
  {  subst.
    unfold typelen.
    unfold nat_of_Z. solve_part_int_rgn.
     rewrite Nat.mul_succ_l  with (n:= idx).
     rewrite Nat2Z.inj_add.
     rewrite Int_repr_add; auto with zarith.
     solve_part_int_rgn. }
  sep pauto.
  unfold Aarray_new.
  unfold Aarray_new'.
  sep pauto.
  rewrite H0; auto.
Qed.

Lemma ARootTaskStk'_select_sn_strong_frm:
  forall s P vll,
     s |= EX idx vll1 vll2 b i vl type,
                    [| RootTaskStk_head = (b, i) |] **
                    [| type = (Tarray Tint32 (nat_of_Z (2 * PTHREAD_STACK_MIN/4 ))) |] **
                     GV RootTaskStk @ (Tptr type) |-> (Vptr (b,i)) **
                    Aarray_new (b, i) (Tarray type idx) vll1 **
                    Aarray (b, i +ᵢ $ Z.of_nat (idx * (typelen type))) type vl **
                    Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen type))))
                    (Tarray type (∘ (PARTITION_NUM - Z.of_nat (S idx)))) vll2 ** 
                    [| new_array_type_vallist_match type vll |] **
                    [| length vll = ∘ (PARTITION_NUM) |] **
                    [| (forall n vl, nth_vallist n vll = Some vl -> length vl = (nat_of_Z (2 * PTHREAD_STACK_MIN/4 ))) |] **
                    [| vll = vll1 ++ (vl::vll2) |] ** 
                    [| length vll1 = idx /\ length vll2 = ∘ (PARTITION_NUM - Z.of_nat (S idx)) |] **
                    [| Z.of_nat (S idx) <= PARTITION_NUM |] **
                    P ->
    s |= ARootTaskStk' vll ** P.
Proof.
  intros.
  sep destruct H.
  sep split in H.
  subst.
  sep cancel P.
  eapply ARootTaskStk'_select_sn_strong; eauto.
Qed.

(* lemmas about global array, ksDomSchedule[DSCHEDULE_SIZE] *)

Lemma AKsDomSchedule'_len: 
  forall s vl, s |= AKsDomSchedule' vl -> length vl = ∘ (DSCHEDULE_SIZE).
Proof.
  introv Hsat.
  destruct Hsat.
  simpl_sat H. simpljoin1.
  auto.
Qed.

Lemma AKsDomSchedule'_len_frm:
  forall s vl P, s |= AKsDomSchedule' vl ** P -> length vl = ∘ (DSCHEDULE_SIZE).
Proof.
  introv Hsat.
  unfold AKsDomSchedule' in *.
  simpl in Hsat.
  simpljoin1.
  auto.
Qed.

Lemma AKsDomSchedule'_unfold_any_idx: 
  forall s vll idx,
    s |= AKsDomSchedule' vll ->
    (idx < length vll)%nat ->
    s |= EX vll1 vll2 b i vl ,
        GV ksDomSchedule @ dschedule_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray dschedule_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen dschedule_t))) dschedule_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen dschedule_t))))
          (Tarray dschedule_t (∘ (DSCHEDULE_SIZE - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match dschedule_t vll |] **
          [| length vll = ∘ (DSCHEDULE_SIZE) |] **
          [| vll = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (DSCHEDULE_SIZE - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= DSCHEDULE_SIZE |] **
          [| R_KsDomSchedule_P vll |].
Proof.
  introv Hsat.
  assert (Hlengt: Z.of_nat (length vll * typelen dschedule_t) <= Int.max_unsigned). 
  { erewrite AKsDomSchedule'_len; eauto.  simpl. mauto. }
  introv Hlenle.
  unfold AKsDomSchedule' in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  destruct H as (Hmat & Hlen).
  destruct x.
  assert (Hlen_eq: (length vll = idx + (length vll - idx))%nat) 
    by auto with arith.
  lets Hsplit: (firstn_skipn idx vll).
  sep lift 2%nat in Hsat.
  unfold nat_of_Z in *.
  rewrite <- Hlen in Hsat.
  rewrite Hlen_eq in Hsat.
  rewrite <- Hsplit in Hsat.
   assert (Hlens: length (firstn idx vll) = idx /\ length (skipn idx vll) = (length vll - idx)%nat).
  { rewrite Hsplit in *.
    split. 
    apply firstn_length_le. auto with arith.
    apply skipn_length.
  }
  eapply Aarray_new_split_strong_frm in Hsat.
   assert (HlenS: (length vll - idx = S (length vll - (S idx)))%nat).
  {
    rewrite NPeano.Nat.sub_succ_r.
    rewrite Nat.lt_succ_pred with (z:=0%nat); auto.
    rewrite <- Nat.lt_add_lt_sub_r. simpl. auto.
  }
  rewrite Hsplit in Hsat.
  rewrite HlenS in Hsat.
  assert (Hln: (length (skipn idx vll) > 0)%nat).
  {
    rewrite skipn_length.  
    cut (0 < length vll - idx)%nat.
    auto with arith.
    rewrite <- NPeano.Nat.lt_add_lt_sub_l.
    rewrite Nat.add_0_r. auto.
  }
  apply length_exists in Hln.
  destruct Hln as (vh & vlt & Hlst). rewrite Hlst in *.
  sep pauto; eauto.
  sep cancel Aarray_new.
  eapply Aarray_new_succ_imp in Hsat.
  assert (Hsimp: $ Z.of_nat (idx * typelen dschedule_t) +ᵢ  $ Z.of_nat (typelen dschedule_t) =
                   $ Z.of_nat (S idx * typelen dschedule_t)).
  {
    rewrite <- Nat.add_1_r.
    rewrite NPeano.Nat.mul_add_distr_r. 
    rewrite Nat2Z.inj_add.
    change (1 * typelen dschedule_t)%nat with (typelen dschedule_t).
    simpl.
    rewrite Int.add_unsigned.
    rewrite Int.unsigned_repr; auto.
    rewrite Hlen in *.
    simpl typelen in *.
    clear -Hlenle Hlengt.
    unfold DSCHEDULE_SIZE in *.
    auto with zarith.
  }
  rewrite Int.add_assoc in Hsat.
  rewrite Hsimp in Hsat.
  rewrite Z2Nat.inj_sub; auto with zarith.
  rewrite <- Hlen.
  rewrite Nat2Z.id.
  unfold Aarray_new at 1 in Hsat.
  unfold dschedule_t in *.
  unfold Aarray_new' in Hsat.
  sep pauto.
  rewrite Hlen in *.
  auto with zarith.
  split; auto.
  eapply Nat.succ_inj.
  simpl length in *.
  rewrite H1.
  rewrite Hlen in *.
  auto with zarith.
  {
    apply Z.le_trans with (m:=Z.of_nat (length vll * typelen dschedule_t));
      auto.
    apply inj_le. 
    apply NPeano.Nat.mul_le_mono_r; auto.
  }
  rewrite Hsplit.
  auto.
Qed.

Lemma AKsDomSchedule'_unfold_any_idx_frm:
  forall s vll idx P,
    s |= AKsDomSchedule' vll ** P ->
    (idx < length vll)%nat ->
    s |= (EX vll1 vll2 b i vl ,
        GV ksDomSchedule @ dschedule_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray dschedule_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen dschedule_t))) dschedule_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen dschedule_t))))
          (Tarray dschedule_t (∘ (DSCHEDULE_SIZE - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match dschedule_t vll |] **
          [| length vll = ∘ (DSCHEDULE_SIZE) |] **
          [| vll = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (DSCHEDULE_SIZE - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= DSCHEDULE_SIZE |] **
          [| R_KsDomSchedule_P vll |]) ** P.
Proof. 
  introv Hsat Hlenle. 
  sep cancel 2%nat 2%nat.
  eapply AKsDomSchedule'_unfold_any_idx; eauto.
Qed.

Lemma AKsDomSchedule'_select_sn_strong :
  forall vll1 n vll2 b i s vl,
    Z.of_nat(S n) <= DSCHEDULE_SIZE ->
    s |= GV ksDomSchedule @ dschedule_t ∗ |-> Vptr (b,i) **
           Aarray_new (b, i) (Tarray dschedule_t n) vll1 **
           Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen dschedule_t)))) dschedule_t vl **
           Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen dschedule_t))))
                                (Tarray dschedule_t (∘ (DSCHEDULE_SIZE - Z.of_nat(S n)))) vll2 ->
    new_array_type_vallist_match dschedule_t (vll1 ++ (vl::vll2)) ->
    length (vll1 ++ (vl::vll2)) = ∘ (DSCHEDULE_SIZE) ->
    R_KsDomSchedule_P (vll1 ++ (vl::vll2)) ->
    s |= AKsDomSchedule' (vll1 ++ (vl::vll2)).
Proof.
  intros.
  rename H3 into Hr.
  assert (Hrgn: Z.of_nat (S n * typelen dschedule_t) <= Int.max_unsigned).
  {
    remember (typelen dschedule_t) as X. 
    unfold dschedule_t in HeqX. simpl in HeqX. 
    rewrite HeqX.
    unfold DSCHEDULE_SIZE in *.
    int auto.
  }
  unfold AKsDomSchedule'.
  sep pauto.
  assert (Heq: ∘ (DSCHEDULE_SIZE) 
               =  Nat.add n (S (∘ (DSCHEDULE_SIZE - Z.of_nat(S n))) )).
  unfold nat_of_Z.
  assert (Heq1: Z.to_nat (DSCHEDULE_SIZE - Z.of_nat (S n)) 
              = Nat.sub (Z.to_nat (DSCHEDULE_SIZE))  (Z.to_nat (Z.of_nat (S n))) ).
  apply Z2Nat.inj_sub.
  eauto with zarith.
  rewrite Heq1.
  eauto with zarith.
  unfold nat_of_Z in *.
  rewrite Heq.
  eapply Aarray_new_compose_strong; eauto.
  sep pauto.
  eapply Aarray_new_succ.
  rewrite Int.add_assoc.
  asserts_rewrite ($ Z.of_nat (n * typelen dschedule_t) +ᵢ  $ Z.of_nat (typelen dschedule_t) 
                   = $ Z.of_nat (S n * typelen dschedule_t)).
  { int auto. }
  sep pauto.
  unfold dschedule_t.
  unfold Aarray_new.
  unfold Aarray_new'.
  fold dschedule_t.
  sep pauto.
Qed.

Lemma AKsDomSchedule'_select_sn_strong_frm:
  forall s P vll,
     s |= EX n vll1 vll2 b i vl ,
             GV ksDomSchedule @ dschedule_t ∗ |-> Vptr (b,i) **
             Aarray_new (b, i) (Tarray dschedule_t n) vll1 **
             Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen dschedule_t)))) dschedule_t vl **
             Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen dschedule_t))))
                                (Tarray dschedule_t (∘ (DSCHEDULE_SIZE - Z.of_nat(S n)))) vll2 **
             [|  new_array_type_vallist_match dschedule_t (vll1 ++ (vl::vll2)) |] **
             [| length vll = ∘ (DSCHEDULE_SIZE) |] **
             [| vll = vll1 ++ (vl::vll2) |] ** 
             [| length vll1 = n /\ length vll2 = ∘ (DSCHEDULE_SIZE - Z.of_nat(S n)) |] **
             [| Z.of_nat(S n) <= DSCHEDULE_SIZE |] **
             [| R_KsDomSchedule_P vll |] **
              P ->
    s |= AKsDomSchedule' vll ** P.
Proof.
  intros.
  sep destruct H.
  sep split in H.
  subst.
  sep cancel P.
  eapply AKsDomSchedule'_select_sn_strong; eauto.
Qed.

Lemma dscd_size_eq:
forall idx : nat,
       Z.of_nat (S idx) <= DSCHEDULE_SIZE ->
       Int.unsigned ($ Z.of_nat idx) = Z.of_nat idx.
Proof.
unfold DSCHEDULE_SIZE.
int auto.
Qed.

Lemma dscd_size_le':
forall idx : nat,
       Z.of_nat (S idx) <= DSCHEDULE_SIZE -> Z.of_nat idx <= Int.max_signed.
Proof.
unfold DSCHEDULE_SIZE.
int auto.
Qed.

Lemma dscd_size_comp:
forall idx,
       Z.of_nat (S (Z.to_nat (Int.unsigned idx))) <= DSCHEDULE_SIZE -> Int.unsigned idx <= Int.max_signed.
Proof.
unfold DSCHEDULE_SIZE.
int auto.
Qed.

Lemma R_KsDomSchedule_P_updata:
forall vll1 vl vll2 v0 v1 ,
R_KsDomSchedule_P (vll1 ++ vl :: vll2) ->
0 <= Int.unsigned v0 < DOMAIN_SIZE ->
R_KsDomSchedule_P (vll1 ++ (Vint32 v0 :: Vint32 v1 :: nil) :: vll2).
Proof.
unfold R_KsDomSchedule_P in *.
introv Hr Hrgn Hnth Hv.
assert (Hc: ∘ (Int.unsigned td) = length vll1 \/ ∘ (Int.unsigned td) <> length vll1) by tauto.
destruct Hc as [Heq | Hneq].
rewrite Heq in Hnth.
rewrite <- nth_error_eq_nth_vallist in Hnth.
rewrite nth_error_app2 in Hnth; auto with zarith.
rewrite Nat.sub_diag in Hnth.
simpl in Hnth.
inverts Hnth.
inverts Hv.
auto.
eapply Hr; eauto.
eapply nth_vallist_neq; eauto.
Qed.

(* end lemmas about global array, ksDomSchedule[DSCHEDULE_SIZE] *)

(* lemmas about global array, ksDomains[DOMAIN_SIZE] *)

Lemma AKsDomains'_plus: 
   forall x idx s b i x1 x2 ,
   (length x < ∘ DOMAIN_SIZE)%nat ->
   (idx = length x)%nat ->
    s |=  AKsDomains' (Vptr (b,i)) x **
             node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t)))) x1 domain_t **
             (EX l,
                     [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t))) domainIntStatusTbl domain_t = Some l |] **
                     Aarray l (Tarray Tint8 (nat_of_Z USER_INT_MAX_N)) x2 ** 
                    [| array_type_vallist_match Tint8 x2 /\ length x2 = (nat_of_Z USER_INT_MAX_N)|])  ->
  s |= AKsDomains' (Vptr (b, i)) (x ++ (x1, x2) :: nil) .
Proof.
  induction x; introv Hlen Hidx Hsat; subst.
  simpl length in *.
  rewrite app_nil_l.
  unfold AKsDomains' in *.
  rewrite Nat.mul_0_l in Hsat.
  change ($ Z.of_nat 0) with Int.zero in *.
  rewrite Int.add_zero in *.
  sep pauto.
  change ((a :: x) ++ (x1, x2) :: nil) with (a :: (x ++ (x1, x2) :: nil)).
  destruct a as [].
  simpl length in *.
  unfold AKsDomains' in *. fold AKsDomains' in *.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  sep pauto; eauto.
  sep cancel 2%nat 1%nat.
  eapply IHx; auto with zarith.
  rewrite Int.add_assoc.
  rewrite Nat.mul_succ_l in *.
  rewrite Nat.add_comm in *.
  rewrite Nat2Z.inj_add in *.
  rewrite Int_repr_add in *; auto with zarith;
  try solve[simpl typelen;
              unfold DOMAIN_SIZE in *;
              unfold PARTITION_NUM in *;
              conv_max_unsigned;
              unfold nat_of_Z in *;
              auto with zarith].
  sep pauto; eauto.
Qed.

Lemma AKsDomains'_plus_frm: 
   forall x idx s b i x1 x2 P,
   (length x < ∘ DOMAIN_SIZE)%nat ->
   (idx = length x)%nat ->
    s |=  AKsDomains' (Vptr (b,i)) x **
             node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t)))) x1 domain_t **
             (EX l,
                     [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t))) domainIntStatusTbl domain_t = Some l |] **
                     Aarray l (Tarray Tint8 (nat_of_Z USER_INT_MAX_N)) x2 ** 
                    [| array_type_vallist_match Tint8 x2 /\ length x2 = (nat_of_Z USER_INT_MAX_N)|]) ** P  ->
  s |= AKsDomains' (Vptr (b, i)) (x ++ (x1, x2) :: nil) ** P.
Proof.
intros.
sep cancel P.
eapply AKsDomains'_plus; eauto.
Qed.

Lemma AKsDomains'_compose_strong:
 forall  vll1 vll2 s b i idx    ,
    ( length vll1 = idx)%nat -> 
    ( idx < ∘ (DOMAIN_SIZE))%nat ->
     s |= AKsDomains' (Vptr (b, i)) vll1 ** 
             AKsDomains'  (Vptr (b, (i+ᵢ  $ Z.of_nat ( idx* (typelen domain_t))))) vll2->
     s |= AKsDomains' (Vptr (b, i)) (vll1++vll2) .
Proof.
induction vll1; introv Hlen Hidx Hsat; subst.
rewrite app_nil_l.
simpl length in *.
unfold AKsDomains' in *. 
fold AKsDomains' in *.
rewrite Nat.mul_0_l in *.
change ($ Z.of_nat 0) with Int.zero in *.
rewrite Int.add_zero in *.
sep pauto.
change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)).
destruct a as [].
unfold AKsDomains' in *.
fold AKsDomains' in *.
simpl length in *.
sep normal in Hsat.
sep destruct Hsat.
sep split in Hsat.
match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
sep pauto; eauto.
sep cancel Aarray.
eapply IHvll1; eauto.
auto with zarith.
rewrite Int.add_assoc.
rewrite Nat.mul_succ_l in Hsat.
rewrite Nat.add_comm in Hsat.
rewrite Nat2Z.inj_add in Hsat.
rewrite Int_repr_add in Hsat; auto with zarith.
simpl typelen.
unfold DOMAIN_SIZE in *.
unfold PARTITION_NUM in *.
conv_max_unsigned.
unfold nat_of_Z in *.
auto with zarith.
Qed.

Lemma AKsDomains'_compose_strong_frm:
 forall  vll1 vll2 s b i idx P ,
    ( length vll1 = idx)%nat -> 
    ( idx < ∘ (DOMAIN_SIZE))%nat ->
     s |= AKsDomains' (Vptr (b, i)) vll1 ** 
             AKsDomains'  (Vptr (b, (i+ᵢ  $ Z.of_nat ( idx* (typelen domain_t))))) vll2 ** P->
     s |= AKsDomains' (Vptr (b, i)) (vll1++vll2) ** P.
Proof.
intros.
sep cancel P.
eapply AKsDomains'_compose_strong; eauto.
Qed.

Lemma AKsDomains'_select_sn_strong :
  forall idx s b i vll1 vll2 vl  vl' ,
     ( length vll1 = idx)%nat ->
     ( idx < ∘ (DOMAIN_SIZE))%nat ->
     s |=  AKsDomains' (Vptr (b,i)) vll1 **
              node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t)))) vl domain_t **
              (EX l ,
                     [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t))) domainIntStatusTbl domain_t = Some l  |] ** 
                     Aarray l (Tarray Tint8 (nat_of_Z USER_INT_MAX_N)) vl' ** 
                     [| array_type_vallist_match Tint8 vl' /\ length vl' = (nat_of_Z USER_INT_MAX_N)|]) **
              AKsDomains' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen domain_t))))) vll2->
      s |= AKsDomains'(Vptr (b, i)) (vll1 ++  ((vl, vl')::vll2)).
Proof.
  induction vll2; introv Hlen Hidx Hsat; subst;
  unfold AKsDomains' in *;
  fold AKsDomains'  in *.
  eapply AKsDomains'_plus ;eauto.
  sep pauto; eauto.
  eapply AKsDomains'_compose_strong; eauto.
  destruct a as [].
  unfold AKsDomains' in *.
  fold AKsDomains' in *.
  sep normal in Hsat; sep destruct Hsat.
  sep split in Hsat.
  remember (i +ᵢ  $ Z.of_nat (S (length vll1) * typelen domain_t)) as si.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  subst.
  rewrite Nat.mul_succ_l in *.
  rewrite Nat2Z.inj_add in *.
  rewrite Int_repr_add in *; auto with zarith;
  try solve [simpl typelen;
                      unfold DOMAIN_SIZE in *;
                      unfold PARTITION_NUM in *;
                      conv_max_unsigned;
                      unfold nat_of_Z in *;
                      auto with zarith].
  rewrite <- Int.add_assoc in *.
  sep pauto.
Qed.

Lemma AKsDomains'_select_sn_strong_frm :
  forall idx s b i P vll1 vll2 vl  vl' ,
     ( length vll1 = idx)%nat ->
     ( idx < ∘ (DOMAIN_SIZE))%nat ->
     s |=  AKsDomains' (Vptr (b,i)) vll1 **
              node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t)))) vl domain_t **
              (EX l ,
                     [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t))) domainIntStatusTbl domain_t = Some l  |] ** 
                     Aarray l (Tarray Tint8 (nat_of_Z USER_INT_MAX_N)) vl' ** 
                     [| array_type_vallist_match Tint8 vl' /\ length vl' = (nat_of_Z USER_INT_MAX_N)|]) **
              AKsDomains' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen domain_t))))) vll2 ** P->
      s |= AKsDomains'(Vptr (b, i)) (vll1 ++  ((vl, vl')::vll2)) ** P. 
Proof.
  intros.
  sep cancel P.
  eapply AKsDomains'_select_sn_strong; eauto.
Qed.

Lemma AKsDomains'_unfold_any_idx: 
   forall vll idx s b i ,
    s |= AKsDomains' (Vptr (b,i)) vll ->
     length vll= ∘ (DOMAIN_SIZE) ->
    (idx < length vll)%nat ->
    s |= (EX vll1 vll2 vl  vl',
                    AKsDomains' (Vptr (b,i)) vll1 **
                    node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t)))) vl domain_t **
                   (EX l ,
                          [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t))) domainIntStatusTbl domain_t = Some l |] **
                          Aarray l (Tarray Tint8 (nat_of_Z USER_INT_MAX_N)) vl' ** 
                          [| array_type_vallist_match Tint8 vl' /\ length vl' = (nat_of_Z USER_INT_MAX_N)|]) **
                   AKsDomains' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen domain_t))))) vll2**
                   [| vll = vll1 ++ ((vl, vl')::vll2) |] ** 
                   [| length vll1 = idx /\ length vll2 = ∘ (Z.of_nat(length vll) - Z.of_nat (S idx)) |] **
                   [| Z.of_nat (S idx) <= Z.of_nat(length vll) |]).
Proof.
induction idx; introv Hsat Hlen Hlt.
rewrite Nat.mul_0_l.
rewrite Nat.mul_1_l.
destruct vll; simpl length in *.
tryfalse.
destruct d as [].
unfold AKsDomains' in Hsat. fold AKsDomains' in Hsat.
change ($ Z.of_nat 0) with Int.zero.
rewrite Int.add_zero.
sep normal in Hsat;sep destruct Hsat.
sep split in Hsat.
match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
exists (nil: list Doamin_t_val) vll v v0.
simpl AKsDomains' at 1.
rewrite app_nil_l. 
sep pauto; eauto.
auto with zarith.
split; auto.
unfold nat_of_Z in *.
auto with zarith.
(* case: suc n *)
eapply IHidx in Hsat; eauto.
sep normal in Hsat; sep destruct Hsat.
sep split in Hsat.
destruct H2; subst idx.
destruct x0.
simpljoin.
rewrite last_length in Hlt.
false.
auto with zarith.
destruct d as [].
exists (x ++ (x1, x2) :: nil) x0 v v0.
eapply AKsDomains'_plus_frm; eauto.
auto with zarith.
unfold AKsDomains' in Hsat; fold AKsDomains' in Hsat.
sep normal in Hsat; sep destruct Hsat.
sep split in Hsat.
remember (i +ᵢ  $ Z.of_nat (S (length x) * typelen domain_t)) as si.
match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
simpljoin.
rewrite Int.add_assoc in Hsat.
rewrite Nat.mul_succ_l  with (n:= (S (length x))).
rewrite Nat2Z.inj_add.
rewrite Int_repr_add; auto with zarith.
rewrite <- list_cons_assoc.
sep pauto; eauto.
rewrite app_length in *.
simpl length in *.
auto with zarith.
rewrite last_length.
split; auto.
rewrite app_length in *.
simpl length in *.
unfold nat_of_Z in *.
auto with zarith.
simpl typelen.
unfold DOMAIN_SIZE in *.
unfold PARTITION_NUM in *.
conv_max_unsigned.
unfold nat_of_Z in *.
auto with zarith.
auto with zarith.
Qed.

Lemma AKsDomains'_unfold_any_idx_frm: 
   forall vll idx s b i P,
    s |= AKsDomains' (Vptr (b,i)) vll ** P ->
     length vll= ∘ (DOMAIN_SIZE) ->
    (idx < length vll)%nat ->
    s |= (EX vll1 vll2 vl  vl',
                    AKsDomains' (Vptr (b,i)) vll1 **
                    node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t)))) vl domain_t **
                   (EX l ,
                          [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t))) domainIntStatusTbl domain_t = Some l |] **
                          Aarray l (Tarray Tint8 (nat_of_Z USER_INT_MAX_N)) vl' ** 
                          [| array_type_vallist_match Tint8 vl' /\ length vl' = (nat_of_Z USER_INT_MAX_N)|]) **
                   AKsDomains' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen domain_t))))) vll2**
                   [| vll = vll1 ++ ((vl, vl')::vll2) |] ** 
                   [| length vll1 = idx /\ length vll2 = ∘ (Z.of_nat(length vll) - Z.of_nat (S idx)) |] **
                   [| Z.of_nat (S idx) <= Z.of_nat(length vll) |]) ** P.
Proof.
intros .
sep cancel P.
eapply AKsDomains'_unfold_any_idx; eauto.
Qed.

Lemma AKsDomains_P_split:
forall vll1 vll2 (abs: KsDomsMod.map) n,
  AKsDomains_P (Vint32 n) (vll1 ++ vll2) abs ->
  (length vll1 < ∘ DOMAIN_SIZE)%nat ->
  exists abs1 abs2 idx,
  idx = (length vll1)%nat /\
  AKsDomains_P (Vint32 n) vll1 abs1 /\
  AKsDomains_P (Vint32 (Int.add n (Int.repr (Z.of_nat idx )))) vll2 abs2 /\
  KsDomsMod.join abs1 abs2 abs.
Proof.
  induction vll1;
  introv Hksd Hlen.
  simpl in *.
  do 3 eexists.
  splits; eauto.
  change ($ Z.of_nat 0) with Int.zero.
  rewrite Int.add_zero.
  eauto.
  eapply KsDomsMod.map_join_emp.
  simpl in *.
  simpljoin.
  inverts H.
  eapply IHvll1 in H3; auto with zarith.
  simpljoin.
  assert (Heq: (x +ᵢ  $ Z.of_nat (S (length vll1))) = ((x +ᵢ  Int.one) +ᵢ  $ Z.of_nat (length vll1))).
   {
      rewrite Int.add_assoc.
      assert (Heq1: $ Z.of_nat (S (length vll1)) = (Int.one +ᵢ  $ Z.of_nat (length vll1))).
      { clear -Hlen.
        int auto.
       }
       rewrite Heq1. auto.
   }
  rewrite <- Heq in *.
  lets Hnew: KsDomsMod.join_assoc_r H4 H1.
  simpljoin.
  repeat eexists; eauto.
Qed.

Lemma AKsDomains_P_split':
forall vll1 vl vll2 (abs: KsDomsMod.map) n,
  AKsDomains_P (Vint32 n) (vll1 ++ (vl :: vll2)) abs ->
  (length vll1 < ∘ DOMAIN_SIZE) %nat ->
  exists abs1 abs2 abs0 abs' idx,
  idx = (length vll1)%nat /\
  AKsDomains_P (Vint32 n) vll1 abs1 /\
  AKsDomains_P (Vint32(Int.add n (Int.repr ((Z.of_nat idx) + 1)%Z))) vll2 abs2 /\
  AKsDomains_P (Vint32(Int.add n (Int.repr (Z.of_nat idx )))) (vl :: nil)
                                 (KsDomsMod.sig (Int.add n (Int.repr (Z.of_nat idx))) abs0) /\
  TcbJoin (Int.add n (Int.repr (Z.of_nat idx))) abs0 abs2 abs' /\
  KsDomsMod.join abs1 abs' abs.
Proof.
  intros.
  eapply AKsDomains_P_split in H; eauto.
  simpl in *.
  simpljoin.
  inverts H2.
 assert (Heq: (Vint32 ((n +ᵢ  $ Z.of_nat (length vll1)) +ᵢ  Int.one)) = (Vint32 (n +ᵢ  $ (Z.of_nat (length vll1) + 1)))).
   { rewrite Int.add_assoc.
      assert (Heq1: $ (Z.of_nat  (length vll1)+1) = ($ Z.of_nat (length vll1) +ᵢ  Int.one)).
      { clear -H0.
        int auto.
       }
       rewrite Heq1. auto.
   }
  rewrite Heq in *.
  repeat eexists; eauto.
  eapply KsDomsMod.map_join_emp.
Qed.

(* end lemmas about global array, ksDomains[DOMAIN_SIZE] *)

(* lemmas about variables in ucos_conf_t *)

Lemma  AksDomains'_plus:
  forall x s b i idx x1 x2 x3 x4  ,
     (length x < ∘ CORENUM)%nat ->
     (idx = length x)%nat ->
     s |= AksDomains' (Vptr (b, i)) x ** 
             node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen  domain_conf_t)))) x1  domain_conf_t **
             [| CPU_ksDomain_prio_Good x1 |] **
            ((EX  lprdytbl ,
              [|id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) portRdyTbl domain_conf_t = Some lprdytbl|] **
              Aarray lprdytbl (Tarray char_t ∘ 8) x2 **
              [|array_type_vallist_match char_t x2|]) **
           (EX ldeviotbl ,
             ADeviceioTbl' (Vptr ldeviotbl) x3 **
            [|length x3 =  3%nat|] **
            [|id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) DeviceioTbl domain_conf_t = Some ldeviotbl|]) **
            (EX lcapentbl ,
              node_offt (Vptr lcapentbl) x4 cap_conf_t **
              [|id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) CapEnTbl domain_conf_t = Some lcapentbl|])) ->
     s |= AksDomains' (Vptr (b, i)) (x ++ (x1, x2, x3, x4) :: nil).
Proof.
  induction x; introv Hlen Hidx Hsat.
  simpl length in *.
  rewrite app_nil_l.
  unfold AksDomains' in *.
  subst.
  rewrite Nat.mul_0_l in Hsat.
  change ($ Z.of_nat 0) with Int.zero in *.
  rewrite Int.add_zero in *.
  sep pauto.
  change ((a :: x) ++ (x1, x2, x3, x4) :: nil) with (a :: (x ++ (x1, x2, x3, x4) :: nil)).
  destruct a as [[[]]].
  simpl length in *.
  subst.
  unfold AksDomains' in *. fold AksDomains' in *.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  sep pauto; eauto.
  do 3 sep cancel 4%nat 1%nat.
  eapply IHx; auto with zarith.
  assert(Heq: x5 +ᵢ  $ Z.of_nat (S (length x) * typelen domain_conf_t) = (x5 +ᵢ  $ Z.of_nat (typelen domain_conf_t)) +ᵢ
        $ Z.of_nat (length x * typelen domain_conf_t)).
  {   rewrite Int.add_assoc.
      rewrite Nat.mul_succ_l.
      rewrite Nat.add_comm.
      rewrite Nat2Z.inj_add.
      simpl typelen.
      unfold CORENUM in Hlen.
      rewrite Int_repr_add; auto with zarith.
      conv_max_unsigned.
      unfold nat_of_Z in Hlen.
      auto with zarith.
    }
  rewrite <- Heq.
  sep pauto; eauto.
Qed.

Lemma  AksDomains'_plus_frm:
  forall x s b i idx x1 x2 x3 x4  P,
     (length x < ∘ CORENUM)%nat ->
     (idx = length x)%nat ->
     s |= AksDomains' (Vptr (b, i)) x ** 
             node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen  domain_conf_t)))) x1  domain_conf_t **
             [| CPU_ksDomain_prio_Good x1 |] **
            ((EX  lprdytbl ,
              [|id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) portRdyTbl domain_conf_t = Some lprdytbl|] **
              Aarray lprdytbl (Tarray char_t ∘ 8) x2 **
              [|array_type_vallist_match char_t x2|]) **
           (EX ldeviotbl ,
             ADeviceioTbl' (Vptr ldeviotbl) x3 **
            [|length x3 =  3%nat|] **
            [|id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) DeviceioTbl domain_conf_t = Some ldeviotbl|]) **
            (EX lcapentbl ,
              node_offt (Vptr lcapentbl) x4 cap_conf_t **
              [|id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) CapEnTbl domain_conf_t = Some lcapentbl|])) ** P ->
     s |= AksDomains' (Vptr (b, i)) (x ++ (x1, x2, x3, x4) :: nil) ** P.
Proof.
  intros .
  sep cancel P.
  eapply AksDomains'_plus; eauto.
Qed.

Lemma AksDomains'_compose_strong:
 forall  vll1 vll2 s b i idx    ,
    ( length vll1 = idx)%nat -> 
    ( idx < ∘ (CORENUM))%nat ->
     s |= AksDomains' (Vptr (b, i)) vll1 ** 
             AksDomains'  (Vptr (b, (i+ᵢ  $ Z.of_nat ( idx* (typelen domain_conf_t))))) vll2->
     s |= AksDomains' (Vptr (b, i)) (vll1++vll2) .
Proof.
  induction vll1; introv Hlen Hidx Hsat.
  rewrite app_nil_l.
  simpl length in *.
  subst.
  rewrite Nat.mul_0_l in Hsat.
  change ($ Z.of_nat 0) with Int.zero in *.
  rewrite Int.add_zero in Hsat.
  unfold AksDomains' in *. 
  fold AksDomains' in *.
  sep pauto.
   change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)).
   destruct a as [[[]]].
   unfold AksDomains' in *. fold AksDomains' in *.
   sep normal in Hsat.
   sep destruct Hsat.
   sep split in Hsat.
   match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
   sep pauto; eauto.
   do 3 sep cancel 1%nat 1%nat.
   simpl length in *.
   eapply IHvll1; eauto.
   auto with zarith.
   rewrite Int.add_assoc.
   rewrite Nat.mul_succ_l in Hsat.
   rewrite Nat.add_comm in Hsat.
   rewrite Nat2Z.inj_add in Hsat.
   rewrite Int_repr_add in Hsat; auto with zarith.
   simpl typelen.
   unfold CORENUM in *.
   conv_max_unsigned.
   unfold nat_of_Z in *.
   auto with zarith. 
Qed.

Lemma AksDomains'_compose_strong_frm:
 forall  vll1 vll2 s b i idx  P  ,
    ( length vll1 = idx)%nat -> 
    ( idx < ∘ (CORENUM))%nat ->
     s |= AksDomains' (Vptr (b, i)) vll1 ** 
             AksDomains'  (Vptr (b, (i+ᵢ  $ Z.of_nat ( idx* (typelen domain_conf_t))))) vll2 **P->
     s |= AksDomains' (Vptr (b, i)) (vll1++vll2) **P.
Proof.
 intros.
  sep cancel P.
  eapply AksDomains'_compose_strong; eauto.
Qed.

Lemma AksDomains'_select_sn_strong :
 forall idx s b i vll1 vll2 vl  vl' vl'' vl''',
    ( length vll1 = idx)%nat ->
    ( idx < ∘ (CORENUM))%nat ->
    s |=  AksDomains' (Vptr (b,i)) vll1 **
             node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t)))) vl domain_conf_t **
             [| CPU_ksDomain_prio_Good vl |] **
            (EX lprdytbl,
                     [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) portRdyTbl domain_conf_t = Some lprdytbl |] ** 
                     Aarray lprdytbl (Tarray char_t ∘ 8) vl' **
                    [| array_type_vallist_match char_t vl' |]) **
            (EX ldeviotbl, ADeviceioTbl' (Vptr ldeviotbl) vl'' **
                    [|length vl'' = 3%nat|]** 
                    [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) DeviceioTbl domain_conf_t = Some ldeviotbl |]) ** 
            (EX lcapentbl, 
                    node_offt (Vptr lcapentbl) vl''' cap_conf_t **
                    [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) CapEnTbl domain_conf_t = Some lcapentbl |])**
            AksDomains' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen domain_conf_t))))) vll2->
    s |= AksDomains'(Vptr (b, i)) (vll1 ++  ((vl, vl', vl'', vl''')::vll2)).
Proof.
introv Hlen Hidx Hsat; subst.
eapply AksDomains'_compose_strong; eauto.
unfold AksDomains'; fold AksDomains'.
sep pauto; eauto.
rewrite Int.add_assoc.
rewrite Nat.mul_succ_l in Hsat.
rewrite Nat2Z.inj_add in Hsat.
rewrite Int_repr_add in Hsat; auto with zarith.
simpl typelen.
unfold CORENUM in *.
conv_max_unsigned.
unfold nat_of_Z in *.
auto with zarith.
Qed.

Lemma AksDomains'_select_sn_strong_frm :
 forall idx s b i P vll1 vll2 vl  vl' vl'' vl''',
    ( length vll1 = idx)%nat ->
    ( idx < ∘ (CORENUM))%nat ->
    s |=  AksDomains' (Vptr (b,i)) vll1 **
             node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t)))) vl domain_conf_t **
             [| CPU_ksDomain_prio_Good vl |] **
            (EX lprdytbl,
                     [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) portRdyTbl domain_conf_t = Some lprdytbl |] ** 
                     Aarray lprdytbl (Tarray char_t ∘ 8) vl' **
                    [| array_type_vallist_match char_t vl' |]) **
            (EX ldeviotbl, ADeviceioTbl' (Vptr ldeviotbl) vl'' **
                    [|length vl'' = 3%nat|]** 
                    [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) DeviceioTbl domain_conf_t = Some ldeviotbl |]) ** 
            (EX lcapentbl, 
                    node_offt (Vptr lcapentbl) vl''' cap_conf_t **
                    [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) CapEnTbl domain_conf_t = Some lcapentbl |])**
            AksDomains' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen domain_conf_t))))) vll2 ** P->
    s |= AksDomains'(Vptr (b, i)) (vll1 ++  ((vl, vl', vl'', vl''')::vll2)) ** P.
Proof.
intros.
sep cancel P.
eapply AksDomains'_select_sn_strong; eauto.
Qed.

Lemma AksDomains'_unfold_any_idx: 
   forall vll idx s b i ,
    s |= AksDomains' (Vptr (b,i)) vll ->
     length vll= ∘ (CORENUM) ->
    (idx < length vll)%nat ->
    s |= (EX vll1 vll2 vl  vl' vl'' vl''',
             AksDomains' (Vptr (b,i)) vll1 **
             node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t)))) vl domain_conf_t **
             [| CPU_ksDomain_prio_Good vl |] **
            (EX lprdytbl,
              [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) portRdyTbl domain_conf_t = Some lprdytbl |] ** 
             Aarray lprdytbl (Tarray char_t ∘ 8) vl' ** 
             [| array_type_vallist_match char_t vl' |]) ** 
           (EX ldeviotbl, ADeviceioTbl' (Vptr ldeviotbl) vl''  **
            [|length vl'' = 3%nat|]** 
            [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) DeviceioTbl domain_conf_t = Some ldeviotbl |]) ** 
           (EX lcapentbl, 
            node_offt (Vptr lcapentbl) vl''' cap_conf_t **
            [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) CapEnTbl domain_conf_t = Some lcapentbl |]) **
            AksDomains' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen domain_conf_t))))) vll2 **
           [| vll = vll1 ++ ((vl, vl', vl'', vl''')::vll2) |] ** 
           [| length vll1 = idx /\ length vll2 = ∘ (Z.of_nat(length vll) - Z.of_nat (S idx)) |] **
           [| Z.of_nat (S idx) <= Z.of_nat(length vll) |]) . 
Proof.
induction idx; introv Hsat  Hlen  Hlt.
rewrite Nat.mul_0_l.
rewrite Nat.mul_1_l.
destruct vll; simpl length in *.
tryfalse.
destruct d as [[[]]].
unfold AksDomains' in Hsat. fold AksDomains' in Hsat.
change ($ Z.of_nat 0) with Int.zero.
rewrite Int.add_zero.
sep normal in Hsat;sep destruct Hsat.
sep split in Hsat.
inverts H4.
exists (nil: list domainConfVal) vll v v0 l v1.
simpl AksDomains' at 1.
rewrite app_nil_l. 
sep pauto; eauto.
auto with zarith.
split; auto.
unfold nat_of_Z in *.
auto with zarith.
(* case: suc n *)
eapply IHidx in Hsat; eauto.
sep normal in Hsat; sep destruct Hsat.
sep split in Hsat.
destruct H6; subst idx.
destruct x0.
simpljoin.
rewrite last_length in Hlt.
false.
auto with zarith.
destruct d as [[[]]].
exists ( (x ++ (x1, x2, x3, x4) :: nil) : list domainConfVal) x0 v v0 l v1.
eapply AksDomains'_plus_frm; eauto.
auto with zarith.
unfold AksDomains' in Hsat; fold AksDomains' in Hsat.
sep normal in Hsat; sep destruct Hsat.
sep split in Hsat.
remember (i +ᵢ  $ Z.of_nat (S (length x) * typelen domain_conf_t)) as si.
match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
simpljoin.
rewrite Int.add_assoc in Hsat.
rewrite Nat.mul_succ_l  with (n:= (S (length x))).
rewrite Nat2Z.inj_add.
rewrite Int_repr_add; auto with zarith.
rewrite <- list_cons_assoc.
sep pauto; eauto.
rewrite app_length in *.
simpl length in *.
auto with zarith.
rewrite last_length.
split; auto.
rewrite app_length in *.
simpl length in *.
unfold nat_of_Z in *.
auto with zarith.
simpl typelen.
unfold CORENUM in *.
conv_max_unsigned.
unfold nat_of_Z in *.
auto with zarith.
auto with zarith.
Qed.

Lemma AksDomains'_unfold_any_idx_frm: 
   forall idx s vll b i P,
    s |= AksDomains' (Vptr (b,i)) vll  ** P ->
    length vll= ∘ (CORENUM) ->
    (idx < length vll)%nat ->
    s |= (EX vll1 vll2 vl  vl' vl'' vl''',
             AksDomains' (Vptr (b,i)) vll1 **
             node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t)))) vl domain_conf_t  **
             [| CPU_ksDomain_prio_Good vl |] **
            (EX lprdytbl,
              [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) portRdyTbl domain_conf_t = Some lprdytbl |] ** 
              Aarray lprdytbl (Tarray char_t ∘ 8) vl' ** 
              [| array_type_vallist_match char_t vl' |]) ** 
            (EX ldeviotbl, ADeviceioTbl' (Vptr ldeviotbl) vl''  ** 
              [|length vl'' = 3%nat|]** 
             [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) DeviceioTbl domain_conf_t = Some ldeviotbl |]) ** 
           (EX lcapentbl, 
            node_offt (Vptr lcapentbl) vl''' cap_conf_t **
            [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_conf_t))) CapEnTbl domain_conf_t = Some lcapentbl |])**
            AksDomains' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen domain_conf_t))))) vll2 **
            [| vll = vll1 ++ ((vl, vl', vl'', vl''')::vll2) |] ** 
            [| length vll1 = idx /\ length vll2 = ∘ (Z.of_nat(length vll) - Z.of_nat (S idx)) |] **
            [| Z.of_nat (S idx) <= Z.of_nat(length vll) |])  ** P. 
Proof.
intros.
sep cancel P.
eapply AksDomains'_unfold_any_idx; eauto.
Qed.

Lemma AksDomSchedule'_plus: 
   forall vll idx s b i vl,
   (length vll < ∘ DSCHEDULE_SIZE)%nat ->
   (idx = length vll)%nat ->
   s |= AksDomSchedule' (Vptr (b,i)) vll **
           node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen dschedule_conf_t)))) vl dschedule_conf_t ->
   s |= AksDomSchedule' (Vptr (b,i)) (vll ++ vl::nil) .
Proof.
  induction vll; introv Hlen Hidx Hsat.
  simpl length in *.
  rewrite app_nil_l.
  unfold AksDomSchedule' in *.
  subst.
  rewrite Nat.mul_0_l in Hsat.
  change ($ Z.of_nat 0) with Int.zero in *.
  rewrite Int.add_zero in *.
  sep pauto.
  change ((a :: vll) ++ vl :: nil) with (a :: (vll ++ vl :: nil)).
  simpl length in *.
  subst.
  unfold AksDomSchedule' in *. fold AksDomSchedule' in *.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  sep pauto; eauto.
  eapply IHvll; auto with zarith.
  assert(Heq: x0 +ᵢ  $ Z.of_nat (S (length vll) * typelen dschedule_conf_t) = (x0 +ᵢ  $ Z.of_nat (typelen dschedule_conf_t)) +ᵢ
        $ Z.of_nat (length vll * typelen dschedule_conf_t)).
  {   rewrite Int.add_assoc.
      rewrite Nat.mul_succ_l.
      rewrite Nat.add_comm.
      rewrite Nat2Z.inj_add.
      simpl typelen.
      unfold DSCHEDULE_SIZE in Hlen.
      rewrite Int_repr_add; auto with zarith.
      conv_max_unsigned.
      unfold nat_of_Z in Hlen.
      auto with zarith.
    }
  rewrite <- Heq.
  sep pauto; eauto.
Qed.

Lemma AksDomSchedule'_plus_frm: 
   forall vll idx s b i vl P,
   (length vll < ∘ DSCHEDULE_SIZE)%nat ->
   (idx = length vll)%nat ->
    s |= AksDomSchedule' (Vptr (b,i)) vll **
            node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen dschedule_conf_t)))) vl dschedule_conf_t ** P ->
    s |= AksDomSchedule' (Vptr (b,i)) (vll ++ vl::nil) ** P.
Proof.
intros . 
sep cancel P.
eapply AksDomSchedule'_plus; eauto.
Qed.

Lemma AksDomSchedule'_compose_strong:
 forall  vll1 vll2 s b i idx    ,
    ( length vll1 = idx)%nat -> 
    ( idx < ∘ (DSCHEDULE_SIZE))%nat ->
    s |= AksDomSchedule' (Vptr (b, i)) vll1 ** 
            AksDomSchedule'  (Vptr (b, (i+ᵢ  $ Z.of_nat ( idx* (typelen dschedule_conf_t))))) vll2->
    s |= AksDomSchedule' (Vptr (b, i)) (vll1++vll2) .
Proof.
induction vll1; introv Hlen Hidx Hsat; subst.
rewrite app_nil_l.
simpl length in *.
unfold AksDomSchedule' in *. 
fold AksDomSchedule' in *.
rewrite Nat.mul_0_l in *.
change ($ Z.of_nat 0) with Int.zero in *.
rewrite Int.add_zero in *.
sep pauto.
change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)).
unfold AksDomSchedule' in *.
fold AksDomSchedule' in *.
simpl length in *.
sep normal in Hsat.
sep destruct Hsat.
sep split in Hsat.
match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
sep pauto; eauto.
eapply IHvll1; eauto.
auto with zarith.
rewrite Int.add_assoc.
rewrite Nat.mul_succ_l in Hsat.
rewrite Nat.add_comm in Hsat.
rewrite Nat2Z.inj_add in Hsat.
rewrite Int_repr_add in Hsat; auto with zarith.
simpl typelen.
unfold DSCHEDULE_SIZE in *.
conv_max_unsigned.
unfold nat_of_Z in *.
auto with zarith.
Qed.

Lemma AksDomSchedule'_compose_strong_frm:
 forall  vll1 vll2 s b i idx  P  ,
    ( length vll1 = idx)%nat -> 
    ( idx < ∘ (DSCHEDULE_SIZE))%nat ->
    s |= AksDomSchedule' (Vptr (b, i)) vll1 ** 
            AksDomSchedule'  (Vptr (b, (i+ᵢ  $ Z.of_nat ( idx* (typelen dschedule_conf_t))))) vll2 ** P->
    s |= AksDomSchedule' (Vptr (b, i)) (vll1++vll2) **P.
Proof.
  intros.
  sep cancel P.
  eapply AksDomSchedule'_compose_strong; eauto.
Qed.

Lemma AksDomSchedule'_select_sn_strong :
forall vll1 idx s b i vl vll2,
  ( length vll1 = idx)%nat ->
  ( idx < ∘ (DSCHEDULE_SIZE))%nat ->
  s |= AksDomSchedule' (Vptr (b,i)) vll1 ** 
          node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen dschedule_conf_t)))) vl dschedule_conf_t **
          AksDomSchedule' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen dschedule_conf_t))))) vll2 ->
  s |= AksDomSchedule'(Vptr (b, i)) (vll1 ++ (vl::vll2) ).
Proof.
  induction vll2; introv Hlen Hidx Hsat; subst;
  unfold AksDomSchedule' in *;
  fold AksDomSchedule'  in *.
  eapply AksDomSchedule'_plus ;eauto.
  sep pauto.
  eapply AksDomSchedule'_compose_strong; eauto.
  unfold AksDomSchedule' in *.
  fold AksDomSchedule' in *.
  sep pauto; eauto.
  remember (i +ᵢ  $ Z.of_nat (S (length vll1) * typelen dschedule_conf_t)) as si.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  subst.
  rewrite Int.add_assoc.
  rewrite Nat.mul_succ_l in Hsat.
  rewrite Nat2Z.inj_add in Hsat.
  rewrite Int_repr_add in Hsat; auto with zarith.
  do 2 try rewrite Int.add_assoc in *.
  sep pauto.
  simpl typelen.
  unfold DSCHEDULE_SIZE in *.
  conv_max_unsigned.
  unfold nat_of_Z in *.
  auto with zarith.
Qed.

Lemma AksDomSchedule'_select_sn_strong_frm :
forall vll1 idx s b i vl vll2 P,
  ( length vll1 = idx)%nat ->
  ( idx < ∘ (DSCHEDULE_SIZE))%nat ->
  s |= AksDomSchedule' (Vptr (b,i)) vll1 ** 
          node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen dschedule_conf_t)))) vl dschedule_conf_t **
          AksDomSchedule' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen dschedule_conf_t))))) vll2 ** P ->
  s |= AksDomSchedule'(Vptr (b, i)) (vll1 ++ (vl::vll2) ) ** P. 
Proof.
intros.
sep cancel P.
eapply AksDomSchedule'_select_sn_strong; eauto.
Qed.

Lemma AksDomSchedule'_unfold_any_idx: 
   forall vll idx s b i ,
    s |= AksDomSchedule' (Vptr (b,i)) vll ->
    length vll= ∘ (DSCHEDULE_SIZE) ->
    (idx < length vll)%nat ->
    s |= (EX vll1 vll2 vl ,
              AksDomSchedule' (Vptr (b,i)) vll1 **
              node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen dschedule_conf_t)))) vl dschedule_conf_t **
              AksDomSchedule' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen dschedule_conf_t))))) vll2 **
              [| vll = vll1 ++ (vl::vll2) |] ** 
              [| length vll1 = idx /\ length vll2 = ∘ (Z.of_nat(length vll) - Z.of_nat (S idx)) |] **
              [| Z.of_nat (S idx) <= Z.of_nat(length vll) |]) . 
Proof.
induction idx; introv Hsat  Hlen  Hlt.
rewrite Nat.mul_0_l.
rewrite Nat.mul_1_l.
destruct vll; simpl length in *.
tryfalse.
unfold AksDomSchedule' in Hsat. 
fold AksDomSchedule' in Hsat.
change ($ Z.of_nat 0) with Int.zero.
rewrite Int.add_zero.
sep normal in Hsat;sep destruct Hsat.
exists (nil: list dscheduleConfVal) vll d.
simpl AksDomSchedule' at 1.
sep split in Hsat. 
inverts H.
rewrite app_nil_l. 
simpl length.
sep pauto; eauto.
auto with zarith.
split; auto.
unfold nat_of_Z in *.
auto with zarith.
(* case: suc n *)
eapply IHidx in Hsat; eauto.
sep normal in Hsat; sep destruct Hsat.
sep split in Hsat.
destruct H0; subst idx.
destruct x0.
simpljoin.
rewrite last_length in Hlt.
false.
auto with zarith.
exists ( x ++ x1 :: nil) x0 d.
eapply AksDomSchedule'_plus_frm; eauto.
auto with zarith.
unfold AksDomSchedule' in Hsat; fold AksDomSchedule' in Hsat.
sep normal in Hsat; sep destruct Hsat.
sep split in Hsat.
remember (i +ᵢ  $ Z.of_nat (S (length x) * typelen dschedule_conf_t)) as si.
match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
simpljoin.
rewrite Int.add_assoc in Hsat.
rewrite Nat.mul_succ_l  with (n:= (S (length x))).
rewrite Nat2Z.inj_add.
rewrite Int_repr_add; auto with zarith.
rewrite <- list_cons_assoc.
sep pauto; eauto.
rewrite app_length in *.
simpl length in *.
auto with zarith.
rewrite last_length.
split; auto.
rewrite app_length in *.
simpl length in *.
unfold nat_of_Z in *.
auto with zarith.
simpl typelen.
unfold DSCHEDULE_SIZE in *.
conv_max_unsigned.
unfold nat_of_Z in *.
auto with zarith.
auto with zarith.
Qed.

Lemma AksDomSchedule'_unfold_any_idx_frm: 
   forall vll idx s b i P,
   s |= AksDomSchedule' (Vptr (b,i)) vll ** P ->
   length vll= ∘ (DSCHEDULE_SIZE) ->
   (idx < length vll)%nat ->
   s |= (EX vll1 vll2 vl ,
             AksDomSchedule' (Vptr (b,i)) vll1 **
             node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen dschedule_conf_t)))) vl dschedule_conf_t **
             AksDomSchedule' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen dschedule_conf_t))))) vll2 **
             [| vll = vll1 ++ (vl::vll2) |] ** 
             [| length vll1 = idx /\ length vll2 = ∘ (Z.of_nat(length vll) - Z.of_nat (S idx)) |] **
             [| Z.of_nat (S idx) <= Z.of_nat(length vll) |]) ** P . 
Proof.
intros.
sep cancel P.
eapply AksDomSchedule'_unfold_any_idx; eauto.
Qed.

Lemma  Acpus'_plus:
forall x s b i idx x1 x2 x3 x4    ,
   (length x < ∘ CORENUM)%nat ->
   (idx = length x)%nat ->
   s |= Acpus' (Vptr (b, i)) x ** 
           node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t)))) x1 cpu_conf_t **
           [|CPU_ksDomScLength_Good x1 |] ** 
          ((EX ldomrtbl ,
                    [|id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) domainRdy cpu_conf_t = Some ldomrtbl|] **
                    Aarray ldomrtbl (Tarray char_t ∘ 2) x2 **
                    [|array_type_vallist_match char_t x2|]) **
          (EX lksdstbl ,
                  AksDomSchedule' (Vptr lksdstbl) x3 **
                  [|length x3 = ∘ DSCHEDULE_SIZE|] **
                  [|id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) cpu_ksDomSchedule cpu_conf_t = Some lksdstbl|]) **
                  [| CPU_ksDomSchdule_Good x3 |] ** 
          (EX lksdomtbl ,
                  AksDomains' (Vptr lksdomtbl) x4 **
                  [|CPU_ksDomains_Good x4 |] **
                  [|length x4 = ∘ CORENUM|] **
                  [|id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) cpu_ksDomains cpu_conf_t = Some lksdomtbl|])) ->
   s |= Acpus' (Vptr (b, i)) (x ++ (x1, x2, x3, x4) :: nil).
Proof.
  induction x; introv Hlen Hidx Hsat; subst.
  simpl length in *.
  rewrite app_nil_l.
  unfold Acpus' in *.
  rewrite Nat.mul_0_l in Hsat.
  change ($ Z.of_nat 0) with Int.zero in *.
  rewrite Int.add_zero in *.
  sep pauto.
  change ((a :: x) ++ (x1, x2, x3, x4) :: nil) with (a :: (x ++ (x1, x2, x3, x4) :: nil)).
  simpl length in *.
  destruct a as [[[]]].
  unfold Acpus' in *. fold Acpus' in *.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  sep pauto; eauto.
  do 3 sep cancel 4%nat 1%nat.
  eapply IHx; auto with zarith.
  rewrite Int.add_assoc.
  rewrite Nat.mul_succ_l in *.
  rewrite Nat.add_comm in *.
  rewrite Nat2Z.inj_add in *.
  rewrite Int_repr_add in *; auto with zarith;
  sep pauto; eauto;
  try solve [simpl typelen;
                      unfold CORENUM in *;
                      conv_max_unsigned;
                      unfold nat_of_Z in *;
                      auto with zarith].
Qed.

Lemma  Acpus'_plus_frm:
forall x s b i idx x1 x2 x3 x4  P  ,
   (length x < ∘ CORENUM)%nat ->
   (idx = length x)%nat ->
   s |= Acpus' (Vptr (b, i)) x ** 
           node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t)))) x1 cpu_conf_t **
           [|CPU_ksDomScLength_Good x1 |] ** 
          ((EX ldomrtbl ,
                    [|id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) domainRdy cpu_conf_t = Some ldomrtbl|] **
                    Aarray ldomrtbl (Tarray char_t ∘ 2) x2 **
                    [|array_type_vallist_match char_t x2|]) **
          (EX lksdstbl ,
                  AksDomSchedule' (Vptr lksdstbl) x3 **
                  [|length x3 = ∘ DSCHEDULE_SIZE|] **
                  [|id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) cpu_ksDomSchedule cpu_conf_t = Some lksdstbl|]) **
                  [| CPU_ksDomSchdule_Good x3 |] ** 
          (EX lksdomtbl ,
                  AksDomains' (Vptr lksdomtbl) x4 **
                  [|CPU_ksDomains_Good x4 |] **
                  [|length x4 = ∘ CORENUM|] **
                  [|id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) cpu_ksDomains cpu_conf_t = Some lksdomtbl|])) ** P ->
   s |= Acpus' (Vptr (b, i)) (x ++ (x1, x2, x3, x4) :: nil) ** P.
Proof.
intros .
sep cancel P.
eapply Acpus'_plus; eauto.
Qed.

Lemma Acpus'_compose_strong:
 forall  vll1 vll2 s b i idx    ,
    ( length vll1 = idx)%nat -> 
    ( idx < ∘ (CORENUM))%nat ->
     s |= Acpus' (Vptr (b, i)) vll1 ** 
             Acpus'  (Vptr (b, (i+ᵢ  $ Z.of_nat ( idx* (typelen cpu_conf_t))))) vll2->
     s |= Acpus' (Vptr (b, i)) (vll1++vll2) .
Proof.
induction vll1; introv Hlen Hidx Hsat; subst.
rewrite app_nil_l.
simpl length in *.
unfold Acpus' in *. 
fold Acpus' in *.
rewrite Nat.mul_0_l in *.
change ($ Z.of_nat 0) with Int.zero in *.
rewrite Int.add_zero in *.
sep pauto.
change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)).
destruct a as [[[]]].
unfold Acpus' in *.
fold Acpus' in *.
simpl length in *.
sep normal in Hsat.
sep destruct Hsat.
sep split in Hsat.
match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
sep pauto; eauto.
do 3 sep cancel 1%nat 1%nat.
eapply IHvll1; eauto.
auto with zarith.
rewrite Int.add_assoc.
rewrite Nat.mul_succ_l in Hsat.
rewrite Nat.add_comm in Hsat.
rewrite Nat2Z.inj_add in Hsat.
rewrite Int_repr_add in Hsat; auto with zarith.
simpl typelen.
unfold CORENUM in *.
conv_max_unsigned.
unfold nat_of_Z in *.
auto with zarith.
Qed.

Lemma Acpus'_compose_strong_frm:
 forall  vll1 vll2 s b i idx  P  ,
    ( length vll1 = idx)%nat -> 
    ( idx < ∘ (CORENUM))%nat ->
     s |= Acpus' (Vptr (b, i)) vll1 ** 
             Acpus'  (Vptr (b, (i+ᵢ  $ Z.of_nat ( idx* (typelen cpu_conf_t))))) vll2 **P->
     s |= Acpus' (Vptr (b, i)) (vll1++vll2) **P.
Proof.
intros.
sep cancel P.
eapply Acpus'_compose_strong; eauto.
Qed.

Lemma Acpus'_select_sn_strong :
 forall idx s b i vll1 vll2 vl  vl' vl'' vl''',
    ( length vll1 = idx)%nat ->
    ( idx < ∘ (CORENUM))%nat -> 
    s |=  Acpus' (Vptr (b,i)) vll1 **
             node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t)))) vl cpu_conf_t **
             [| CPU_ksDomScLength_Good vl |] ** 
             (EX ldomrtbl,
                     [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) domainRdy cpu_conf_t = Some ldomrtbl |] ** 
                     Aarray ldomrtbl (Tarray Tint8 (nat_of_Z 2)) vl' ** 
                     [| array_type_vallist_match Tint8 vl' |]) ** 
             (EX lksdstbl, AksDomSchedule' (Vptr lksdstbl) vl'' ** 
                     [| length vl'' = (nat_of_Z DSCHEDULE_SIZE) |] **
                     [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) cpu_ksDomSchedule cpu_conf_t = Some lksdstbl |]) **
                     [| CPU_ksDomSchdule_Good vl'' |] **   
             (EX lksdomtbl, AksDomains' (Vptr lksdomtbl) vl''' **
                     [| CPU_ksDomains_Good vl''' |] **
                     [| length vl''' = ( nat_of_Z CORENUM) |] **
                     [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) cpu_ksDomains cpu_conf_t = Some lksdomtbl |]) **
              Acpus' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen cpu_conf_t))))) vll2->
     s |= Acpus'(Vptr (b, i)) (vll1 ++  ((vl, vl', vl'', vl''')::vll2)).
Proof.
  induction vll2; introv Hlen Hidx Hsat; subst;
  unfold Acpus' in *;
  fold Acpus'  in *.
  eapply Acpus'_plus ;eauto.
  sep pauto; eauto.
  eapply Acpus'_compose_strong; eauto.
  destruct a as [[[]]].
  unfold Acpus' in *.
  fold Acpus' in *.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  remember (i +ᵢ  $ Z.of_nat (S (length vll1) * typelen cpu_conf_t)) as si.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  subst.
  sep normal; sep eexists.
  do 2 sep cancel AksDomains'.
  do 2 sep cancel AksDomSchedule'.
  do 2 sep cancel Aarray.
  do 2 sep cancel Acpus'.
  rewrite Nat.mul_succ_l in Hsat.
  rewrite Nat2Z.inj_add in Hsat.
  rewrite Int_repr_add in Hsat; auto with zarith.
  rewrite <- Int.add_assoc in Hsat.
  sep cancel vl.
  sep pauto.
  rewrite Nat.mul_succ_l.
  rewrite Nat2Z.inj_add.
  rewrite Int_repr_add; auto with zarith.
  rewrite  Int.add_assoc.
  auto.
  simpl typelen.
  unfold CORENUM in *.
  conv_max_unsigned.
  unfold nat_of_Z in *.
  auto with zarith.
  simpl typelen.
  unfold CORENUM in *.
  conv_max_unsigned.
  unfold nat_of_Z in *.
  auto with zarith.
Qed.

Lemma Acpus'_select_sn_strong_frm :
 forall idx s b i P vll1 vll2 vl  vl' vl'' vl''',
    ( length vll1 = idx)%nat ->
    ( idx < ∘ (CORENUM))%nat -> 
    s |=  Acpus' (Vptr (b,i)) vll1 **
             node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t)))) vl cpu_conf_t **
             [| CPU_ksDomScLength_Good vl |] ** 
             (EX ldomrtbl,
                     [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) domainRdy cpu_conf_t = Some ldomrtbl |] ** 
                     Aarray ldomrtbl (Tarray Tint8 (nat_of_Z 2)) vl' ** 
                     [| array_type_vallist_match Tint8 vl' |]) ** 
             (EX lksdstbl, AksDomSchedule' (Vptr lksdstbl) vl'' ** 
                     [| length vl'' = (nat_of_Z DSCHEDULE_SIZE) |] **
                     [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) cpu_ksDomSchedule cpu_conf_t = Some lksdstbl |]) **
                     [| CPU_ksDomSchdule_Good vl'' |] **   
             (EX lksdomtbl, AksDomains' (Vptr lksdomtbl) vl''' **
                     [| CPU_ksDomains_Good vl''' |] **
                     [| length vl''' = ( nat_of_Z CORENUM) |] **
                     [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) cpu_ksDomains cpu_conf_t = Some lksdomtbl |]) **
              Acpus' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen cpu_conf_t))))) vll2 ** P->
     s |= Acpus'(Vptr (b, i)) (vll1 ++  ((vl, vl', vl'', vl''')::vll2)) ** P. 
Proof.
intros.
sep cancel P.
eapply Acpus'_select_sn_strong; eauto.
Qed.

Lemma Acpus'_unfold_any_idx: 
 forall idx s vll b i ,
  s |= Acpus' (Vptr (b,i)) vll ->
  length vll= ∘ (CORENUM) ->
  (idx < length vll)%nat ->
  s |= (EX vll1 vll2 vl  vl' vl'' vl''',
                  Acpus' (Vptr (b,i)) vll1 **
                  node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t)))) vl cpu_conf_t **
                  [| CPU_ksDomScLength_Good vl |] ** 
                  (EX ldomrtbl,
                          [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) domainRdy cpu_conf_t = Some ldomrtbl |] ** 
                          Aarray ldomrtbl (Tarray Tint8 (nat_of_Z 2)) vl' ** 
                          [| array_type_vallist_match Tint8 vl' |]) ** 
                  (EX lksdstbl,
                           AksDomSchedule' (Vptr lksdstbl) vl'' ** 
                          [| length vl'' = (nat_of_Z DSCHEDULE_SIZE) |] **
                          [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) cpu_ksDomSchedule cpu_conf_t = Some lksdstbl |]) ** 
                          [| CPU_ksDomSchdule_Good vl'' |] **  
                  (EX lksdomtbl,
                          AksDomains' (Vptr lksdomtbl) vl''' **
                          [| CPU_ksDomains_Good vl''' |] **
                          [| length vl''' = ( nat_of_Z CORENUM) |]**
                          [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) cpu_ksDomains cpu_conf_t = Some lksdomtbl |])**
                  Acpus' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen cpu_conf_t))))) vll2 **
                  [| vll = vll1 ++ ((vl, vl', vl'', vl''')::vll2) |] ** 
                  [| length vll1 = idx /\ length vll2 = ∘ (Z.of_nat(length vll) - Z.of_nat (S idx)) |] **
                  [| Z.of_nat (S idx) <= Z.of_nat(length vll) |]).
Proof.
induction idx; introv Hsat  Hlen  Hlt.
rewrite Nat.mul_0_l.
rewrite Nat.mul_1_l.
destruct vll; simpl length in *.
tryfalse.
destruct c as [[[]]].
unfold Acpus' in Hsat. 
fold Acpus' in Hsat.
change ($ Z.of_nat 0) with Int.zero.
rewrite Int.add_zero.
sep normal in Hsat;sep destruct Hsat.
exists (nil: list cpuConfVal) vll v v0 l l0.
simpl Acpus' at 1.
sep split in Hsat.
match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
rewrite app_nil_l.
simpl length.
sep pauto; eauto.
auto with zarith.
split; auto.
unfold nat_of_Z in *.
auto with zarith.
(* case: suc n *)
eapply IHidx in Hsat; eauto.
sep normal in Hsat; sep destruct Hsat.
sep split in Hsat.
destruct H9; subst idx.
destruct x0.
simpljoin.
rewrite last_length in Hlt.
false.
auto with zarith.
destruct c as [[[]]].
exists ( x ++ (x1, x2, x3, x4) :: nil) x0 v v0 l l0.
eapply Acpus'_plus_frm; eauto.
auto with zarith.
unfold Acpus' in Hsat; fold Acpus' in Hsat.
sep normal in Hsat; sep destruct Hsat.
sep split in Hsat.
remember (i +ᵢ  $ Z.of_nat (S (length x) * typelen cpu_conf_t)) as si.
match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
simpljoin.
rewrite Int.add_assoc in Hsat.
rewrite Nat.mul_succ_l  with (n:= (S (length x))).
rewrite Nat2Z.inj_add.
rewrite Int_repr_add; auto with zarith.
rewrite <- list_cons_assoc.
sep pauto; eauto.
rewrite app_length in *.
simpl length in *.
auto with zarith.
rewrite last_length.
split; auto.
rewrite app_length in *.
simpl length in *.
unfold nat_of_Z in *.
auto with zarith.
simpl typelen.
unfold CORENUM in *.
conv_max_unsigned.
unfold nat_of_Z in *.
auto with zarith.
auto with zarith.
Qed.

Lemma Acpus'_unfold_any_idx_frm:
 forall idx s vll b i P,
  s |= Acpus' (Vptr (b,i)) vll ** P->
  length vll= ∘ (CORENUM) ->
  (idx < length vll)%nat ->
  s |= (EX vll1 vll2 vl  vl' vl'' vl''',
                  Acpus' (Vptr (b,i)) vll1 **
                  node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t)))) vl cpu_conf_t **
                  [| CPU_ksDomScLength_Good vl |] ** 
                  (EX ldomrtbl,
                          [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) domainRdy cpu_conf_t = Some ldomrtbl |] ** 
                          Aarray ldomrtbl (Tarray Tint8 (nat_of_Z 2)) vl' ** 
                          [| array_type_vallist_match Tint8 vl' |]) ** 
                  (EX lksdstbl,
                           AksDomSchedule' (Vptr lksdstbl) vl'' ** 
                          [| length vl'' = (nat_of_Z DSCHEDULE_SIZE) |] **
                          [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) cpu_ksDomSchedule cpu_conf_t = Some lksdstbl |]) ** 
                          [| CPU_ksDomSchdule_Good vl'' |] **  
                  (EX lksdomtbl,
                          AksDomains' (Vptr lksdomtbl) vl''' **
                          [| CPU_ksDomains_Good vl''' |] **
                          [| length vl''' = ( nat_of_Z CORENUM) |]**
                          [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen cpu_conf_t))) cpu_ksDomains cpu_conf_t = Some lksdomtbl |])**
                  Acpus' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen cpu_conf_t))))) vll2 **
                  [| vll = vll1 ++ ((vl, vl', vl'', vl''')::vll2) |] ** 
                  [| length vll1 = idx /\ length vll2 = ∘ (Z.of_nat(length vll) - Z.of_nat (S idx)) |] **
                  [| Z.of_nat (S idx) <= Z.of_nat(length vll) |]) ** P.
Proof.
intros.
sep cancel P.
eapply Acpus'_unfold_any_idx; eauto.
Qed.

Lemma AportTbl'_plus:
   forall vll idx s b i vl,
   (length vll < ∘ PORT_NUMS)%nat ->
   (idx = length vll)%nat ->
    s |= AportTbl' (Vptr (b,i)) vll **
            node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen port_conf_t)))) vl port_conf_t ->
    s |= AportTbl' (Vptr (b,i)) (vll ++ vl::nil) .
Proof.
  induction vll; introv Hlen Hidx Hsat; subst.
  simpl length in *.
  rewrite app_nil_l.
  unfold AportTbl' in *.
  rewrite Nat.mul_0_l in Hsat.
  change ($ Z.of_nat 0) with Int.zero in *.
  rewrite Int.add_zero in *.
  sep pauto.
  change ((a :: vll) ++ vl :: nil) with (a :: (vll ++ vl :: nil)).
  simpl length in *.
  unfold AportTbl' in *. fold AportTbl' in *.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  sep pauto; eauto.
  eapply IHvll; auto with zarith.
  rewrite Int.add_assoc.
  rewrite Nat.mul_succ_l in *.
  rewrite Nat.add_comm in *.
  rewrite Nat2Z.inj_add in *.
  rewrite Int_repr_add in *; auto with zarith;
  sep pauto; eauto;
  try solve [simpl typelen;
                      unfold PORT_NUMS in *;
                      conv_max_unsigned;
                      unfold nat_of_Z in *;
                      auto with zarith].
Qed.

Lemma AportTbl'_plus_frm:
   forall vll idx s b i vl P,
   (length vll < ∘ PORT_NUMS)%nat ->
   (idx = length vll)%nat ->
    s |= AportTbl' (Vptr (b,i)) vll **
            node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen port_conf_t)))) vl port_conf_t ** P->
    s |= AportTbl' (Vptr (b,i)) (vll ++ vl::nil) ** P.
Proof.
intros .
sep cancel P.
eapply AportTbl'_plus; eauto.
Qed.

Lemma AportTbl'_compose_strong:
 forall  vll1 vll2 s b i idx    ,
    ( length vll1 = idx)%nat -> 
    ( idx < ∘ (PORT_NUMS))%nat ->
     s |= AportTbl' (Vptr (b, i)) vll1 ** 
             AportTbl'  (Vptr (b, (i+ᵢ  $ Z.of_nat ( idx* (typelen port_conf_t))))) vll2->
     s |= AportTbl' (Vptr (b, i)) (vll1++vll2) .
Proof.
induction vll1; introv Hlen Hidx Hsat; subst.
rewrite app_nil_l.
simpl length in *.
unfold AportTbl' in *. 
fold AportTbl' in *.
rewrite Nat.mul_0_l in *.
change ($ Z.of_nat 0) with Int.zero in *.
rewrite Int.add_zero in *.
sep pauto.
change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)).
unfold AportTbl' in *.
fold AportTbl' in *.
simpl length in *.
sep normal in Hsat.
sep destruct Hsat.
sep split in Hsat.
match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
sep pauto; eauto.
eapply IHvll1; eauto.
auto with zarith.
rewrite Int.add_assoc.
rewrite Nat.mul_succ_l in Hsat.
rewrite Nat.add_comm in Hsat.
rewrite Nat2Z.inj_add in Hsat.
rewrite Int_repr_add in Hsat; auto with zarith.
simpl typelen.
unfold PORT_NUMS in *.
conv_max_unsigned.
unfold nat_of_Z in *.
auto with zarith.
Qed.

Lemma AportTbl'_compose_strong_frm:
 forall  vll1 vll2 s b i idx P,
    ( length vll1 = idx)%nat -> 
    ( idx < ∘ (PORT_NUMS))%nat ->
     s |= AportTbl' (Vptr (b, i)) vll1 ** 
             AportTbl'  (Vptr (b, (i+ᵢ  $ Z.of_nat ( idx* (typelen port_conf_t))))) vll2 ** P ->
     s |= AportTbl' (Vptr (b, i)) (vll1++vll2) ** P.
Proof.
intros.
sep cancel P.
eapply AportTbl'_compose_strong; eauto.
Qed.

Lemma AportTbl'_select_sn_strong :
forall vll1 idx s b i vl vll2,
  ( length vll1 = idx)%nat ->
  ( idx < ∘ (PORT_NUMS))%nat ->
  s |= AportTbl' (Vptr (b,i)) vll1 ** 
          node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen port_conf_t)))) vl port_conf_t **
          AportTbl' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen port_conf_t))))) vll2->
  s |= AportTbl'(Vptr (b, i)) (vll1 ++ (vl::vll2) ).
Proof.
induction vll2; introv Hlen Hidx Hsat; subst;
unfold AportTbl' in *;
fold AportTbl'  in *.
eapply AportTbl'_plus ;eauto.
sep pauto.
eapply AportTbl'_compose_strong; eauto.
unfold AportTbl' in *.
fold AportTbl' in *.
sep pauto; eauto.
remember (i +ᵢ  $ Z.of_nat (S (length vll1) * typelen port_conf_t)) as si.
match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
subst.
rewrite Int.add_assoc.
rewrite Nat.mul_succ_l in Hsat.
rewrite Nat2Z.inj_add in Hsat.
rewrite Int_repr_add in Hsat; auto with zarith.
do 2 try rewrite Int.add_assoc in *.
sep pauto.
simpl typelen.
unfold PORT_NUMS in *.
conv_max_unsigned.
unfold nat_of_Z in *.
auto with zarith.
Qed.

Lemma AportTbl'_select_sn_strong_frm :
forall vll1 idx s b i vl vll2 P,
  ( length vll1 = idx)%nat ->
  ( idx < ∘ (PORT_NUMS))%nat ->
  s |= AportTbl' (Vptr (b,i)) vll1 ** 
          node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen port_conf_t)))) vl port_conf_t **
          AportTbl' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen port_conf_t))))) vll2 ** P->
  s |= AportTbl'(Vptr (b, i)) (vll1 ++ (vl::vll2) ) ** P.
Proof.
intros.
sep cancel P.
eapply AportTbl'_select_sn_strong; eauto.
Qed.

Lemma AportTbl'_unfold_any_idx: 
   forall vll idx s b i ,
    s |= AportTbl' (Vptr (b,i)) vll ->
    length vll= ∘ (PORT_NUMS) ->
    (idx < length vll)%nat ->
    s |= (EX vll1 vll2 vl ,
                    AportTbl' (Vptr (b,i)) vll1 **
                    node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen port_conf_t)))) vl port_conf_t **
                    AportTbl' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen port_conf_t))))) vll2 **
                    [| vll = vll1 ++ (vl::vll2) |] ** 
                    [| length vll1 = idx /\ length vll2 = ∘ (Z.of_nat(length vll) - Z.of_nat (S idx)) |] **
                    [| Z.of_nat (S idx) <= Z.of_nat(length vll) |]) .
Proof.
induction idx; introv Hsat  Hlen  Hlt.
rewrite Nat.mul_0_l.
rewrite Nat.mul_1_l.
destruct vll; simpl length in *.
tryfalse.
unfold AportTbl' in Hsat. 
fold AportTbl' in Hsat.
change ($ Z.of_nat 0) with Int.zero.
rewrite Int.add_zero.
sep normal in Hsat;sep destruct Hsat.
sep split in Hsat.
match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
exists (nil: list portConfVal) vll p.
simpl AportTbl' at 1.
rewrite app_nil_l.
simpl length.
sep pauto; eauto.
auto with zarith.
split; auto.
unfold nat_of_Z in *.
auto with zarith.
(* case: suc n *)
eapply IHidx in Hsat; eauto.
sep normal in Hsat; sep destruct Hsat.
sep split in Hsat.
destruct H0; subst idx.
destruct x0.
simpljoin.
rewrite last_length in Hlt.
false.
auto with zarith.
exists ( x ++ x1 :: nil) x0 p.
eapply AportTbl'_plus_frm; eauto.
auto with zarith.
unfold AportTbl' in Hsat; fold AportTbl' in Hsat.
sep normal in Hsat; sep destruct Hsat.
sep split in Hsat.
remember (i +ᵢ  $ Z.of_nat (S (length x) * typelen port_conf_t)) as si.
match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
simpljoin.
rewrite Int.add_assoc in Hsat.
rewrite Nat.mul_succ_l  with (n:= (S (length x))).
rewrite Nat2Z.inj_add.
rewrite Int_repr_add; auto with zarith.
rewrite <- list_cons_assoc.
sep pauto; eauto.
rewrite app_length in *.
simpl length in *.
auto with zarith.
rewrite last_length.
split; auto.
rewrite app_length in *.
simpl length in *.
unfold nat_of_Z in *.
auto with zarith.
simpl typelen.
unfold PORT_NUMS in *.
conv_max_unsigned.
unfold nat_of_Z in *.
auto with zarith.
auto with zarith.
Qed.

Lemma AportTbl'_unfold_any_idx_frm:
   forall vll idx s b i P,
    s |= AportTbl' (Vptr (b,i)) vll ** P ->
    length vll= ∘ (PORT_NUMS) ->
    (idx < length vll)%nat ->
    s |= (EX vll1 vll2 vl ,
                    AportTbl' (Vptr (b,i)) vll1 **
                    node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen port_conf_t)))) vl port_conf_t **
                    AportTbl' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen port_conf_t))))) vll2 **
                    [| vll = vll1 ++ (vl::vll2) |] ** 
                    [| length vll1 = idx /\ length vll2 = ∘ (Z.of_nat(length vll) - Z.of_nat (S idx)) |] **
                    [| Z.of_nat (S idx) <= Z.of_nat(length vll) |]) ** P.
Proof.
intros.
sep cancel P.
eapply AportTbl'_unfold_any_idx; eauto.
Qed.

(* end lemma about variables in ucos_conf_t *)


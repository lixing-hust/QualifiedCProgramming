Require Import include_frm.
Require Import os_code_defs.
Require Import code_notations.
Require Import seplog_trm_tacs.
Require Import os_ucos_h.
Require Import os_inv.
Require Import inv_prop.
Require Import math_auto.
Require Import gjb_common.
Require Import Aarray_new_common.
Require Import pure_lib.
Require Import Lia.
Require Import symbolic_lemmas.
Require Import symbolic_execution.
Require Import partition_common.
Require Import hoare_assign_tac_ext.

Local Open Scope code_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Lemma eq_7add1 :  $ 7+ᵢ ($ 1) = $ 8.
Proof.
  repeat int auto.
Qed.

Lemma new_array_type_vallist_match_split_domsch: 
  forall domschvl vll1 vll2 vl, 
    new_array_type_vallist_match dschedule_t domschvl ->
    domschvl = vll1 ++ (vl::vll2) ->
    new_array_type_vallist_match dschedule_t vll1 /\
      new_array_type_vallist_match dschedule_t vll2 /\ 
      struct_type_vallist_match dschedule_t vl.   
Proof.
  introv Hmatch Hlst.
  lets Hsp2 : new_array_type_vallist_match_split2 Hmatch Hlst.
  destruct Hsp2.
  split; auto.
  simpl in H0.
  destruct H0.
  split; auto.
Qed.
(* OSPortAttrTbl 值表的展开与合并 *)
Lemma portattr_len: 
forall s vl, s |= AOSPortAttrTbl' vl -> length vl = ∘ (PORT_NUMS).
Proof.  
  introv Hsat.
  destruct Hsat.
  sep split in H. 
  destruct H0.
  eauto.
Qed. 

Lemma pos_to_nat_64: Pos.to_nat 64 = 64%nat. 
auto with arith. Qed. 

Lemma OSportattr_unfold_any_idx: 
  forall s portvl idx,
    s |= AOSPortAttrTbl' portvl ->
    (idx < length portvl)%nat ->
    s |= EX vll1 vll2 b i vl ,
      GV OSPortAttrTbl @ Tptr port_attr_t |-> Vptr (b,i)**
          Aarray_new (b, i) (Tarray port_attr_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen port_attr_t))) port_attr_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen port_attr_t))))
          (Tarray port_attr_t (∘ ( PORT_NUMS - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match port_attr_t portvl |] **
          [| length portvl = ∘ (PORT_NUMS) |] **
          [| portvl = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (PORT_NUMS - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= PORT_NUMS |].  
Proof. 
introv Hsat.
assert (Hlengt: Z.of_nat (length portvl * typelen port_attr_t) <= Int.max_unsigned). 
{ erewrite portattr_len; eauto.  simpl. mauto. }
introv Hlenle. 
unfold AOSPortAttrTbl' in Hsat.
unfold sat in Hsat.

simpljoin1.
unfold nat_of_Z in *.
rewrite <- H11 in *.
assert (Hlen: (length portvl = idx + (length portvl - idx))%nat) 
  by auto with arith.
lets Hsplit: (firstn_skipn idx portvl). 
rewrite <- Hsplit in H9 at 2.
rewrite Hlen in H9. 
destruct x.

lets Harrs0: Aarray_new_split_strong H9.
assert (HSidx: (S idx <= length portvl)%nat) by auto with arith.
assert (Harith: Z.of_nat (S idx * typelen port_attr_t) <= Int.max_unsigned ). 
{
  apply Z.le_trans with (m:=Z.of_nat (length portvl * typelen port_attr_t));
    auto.
  apply inj_le. 
  apply NPeano.Nat.mul_le_mono_r; auto.
}
lets Harrs00: Harrs0 Harith.
clear Harrs0.
assert (Hlens: length (firstn idx portvl) = idx /\ length (skipn idx portvl) = (length portvl - idx)%nat).
{
  split. 
  apply firstn_length_le. auto with arith.
  apply skipn_length.
}
lets Harrs: Harrs00 Hlens.
clear Harrs00.
destruct Harrs.
simpljoin1.
destruct s as [[[[[[[]]]]]]].
change_smo H12.
change_smo H13.
change_smo H3.

assert (HlenS: (length portvl - idx = S (length portvl - (S idx)))%nat).
{
  rewrite NPeano.Nat.sub_succ_r.
  rewrite Nat.lt_succ_pred with (z:=0%nat); auto.
  rewrite <- Nat.lt_add_lt_sub_r. simpl. auto.
}
rewrite HlenS in H13.
assert (Hln: (length (skipn idx portvl) > 0)%nat).
{
  rewrite skipn_length.  
  cut (0 < length portvl - idx)%nat.
  auto with arith.
  rewrite <- NPeano.Nat.lt_add_lt_sub_l.
  rewrite Nat.add_0_r. auto.
}
apply length_exists in Hln.
destruct Hln as (vh & vlt & Hlst). rewrite Hlst in H13.
apply Aarray_new'_succ_imp in H13.
assert (Hsimp: $ Z.of_nat (idx * typelen port_attr_t) +ᵢ  $ Z.of_nat (typelen port_attr_t) =
                  $ Z.of_nat (S idx * typelen port_attr_t)).
{
  rewrite <- Nat.add_1_r.
  rewrite NPeano.Nat.mul_add_distr_r. 
  rewrite Nat2Z.inj_add.
  change (1 * typelen port_attr_t)%nat with (typelen port_attr_t).
  simpl. 
  assert (Ha: Z.of_nat (idx * 6) = Int.unsigned ($ (Z.of_nat (idx * 6)))). 
  {
    rewrite int_usign_eq; auto. auto with zarith.
    rewrite H11 in Hlen.
    simpl in H11.
    rewrite pos_to_nat_64 in H11. 
    rewrite H11 in Hlengt.
    apply lt_imply_le.
    apply Z.lt_le_trans with (m:=1920). auto. 
    mauto. mauto.
  }
  assert (Hb: 6 = Int.unsigned ($6)) by auto.
  rewrite Ha at 2. rewrite Hb at 2.
  rewrite <- Int.add_unsigned. auto.
}
rewrite Int.add_assoc in H13. rewrite Hsimp in H13.
assert (Hc: (Z.to_nat (PORT_NUMS - Z.of_nat (S idx)) = length portvl - S idx)%nat).
{
  rewrite H11.
  rewrite sub_Z_nat; auto. 
  unfold nat_of_Z in *.
  rewrite <- H11. 
  auto.
}
rewrite Hc. 
destruct H13.
simpljoin1.
change_smo H17.
change_smo H18.
unfold Aarray_new' in H17. unfold port_attr_t in H17. fold port_attr_t in H17.
apply step_prop.StarEmpER in H17.

simpl_sat_goal.

exists (firstn idx portvl). exists vlt. exists b. exists i.
exists vh. exists x0. exists x1. exists m. exists x3. eexists. exists o.
splits; eauto.

simpl in H10. simpl in H5. 
destruct H10 as (Hx7emp & Hx10emp).
subst x6. unfold emposabst in Hx10emp. subst x9. 
assert (x7 = x1). { apply map_join_emp'' in H5. auto. }
subst x7.
simpl in H7. simpl in H2.
assert (x10 = x4). { apply map_join_emp'' in H7. auto. }
subst x10.
simpl in H6. 
simpl in H1.

exists x.  do 5 eexists. splits; eauto.
eexists x5. do 2 eexists. exists x14. do 2 eexists. 
splits; eauto.

unfold Aarray_new.
exists x12. do 2 eexists. exists x15. do 2 eexists.
splits; eauto.
instantiate (1:=empenv). join auto.
instantiate (1:=emp). join auto.

do 6 eexists. splits; eauto.
join auto. join auto.
split; auto. simpl. split; auto. unfolds. auto.

do 6 eexists. splits; eauto. 
join auto. join auto.
split; auto. simpl. split; auto. unfolds. eauto.

do 6 eexists. splits; eauto.
join auto. join auto.
split. 
rewrite <- Hsplit at 1. rewrite Hlst. auto.
simpl. split; auto. unfolds. auto.

do 6 eexists. splits; eauto.
join auto. join auto.
split. split; auto.
rewrite Hlst in H15. simpl in H15. 
eapply sub_eq_succ; eauto.
simpl. split; auto. unfolds. auto.
rewrite H11 in HSidx.
apply inj_le in HSidx. simpl in HSidx.
simpl. 
change PORT_NUMS with 64. { auto. }
auto.
simpl. split; auto. unfolds. auto.
Qed. 

Lemma OSportattr_unfold_any_idx_frm: 
forall s portvl idx P,
s |= AOSPortAttrTbl' portvl ** P ->
(idx < length portvl)%nat ->
s |= (EX vll1 vll2 b i vl ,
  GV OSPortAttrTbl @ Tptr port_attr_t |-> Vptr (b,i)**
      Aarray_new (b, i) (Tarray port_attr_t idx) vll1 **
      Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen port_attr_t))) port_attr_t vl **
      Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen port_attr_t))))
      (Tarray port_attr_t (∘ ( PORT_NUMS - Z.of_nat (S idx)))) vll2 ** 
      [| new_array_type_vallist_match port_attr_t portvl |] **
      [| length portvl = ∘ (PORT_NUMS) |] **
      [| portvl = vll1 ++ (vl::vll2) |] ** 
      [| length vll1 = idx /\ length vll2 = ∘ (PORT_NUMS - Z.of_nat (S idx)) |] **
      [| Z.of_nat (S idx) <= PORT_NUMS |]) ** P.  
Proof. 
introv Hsat Hlenle. 
sep cancel 2%nat 2%nat.
eapply OSportattr_unfold_any_idx; eauto.
Qed.

Lemma OSportattr_select_sn_strong :
  forall vll1 n vll2 b i s vl P, 
    Z.of_nat(S n) <= PORT_NUMS ->
    s |= GV OSPortAttrTbl @ Tptr port_attr_t |-> Vptr (b,i)**
      Aarray_new (b, i) (Tarray port_attr_t n) vll1 **
      Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen port_attr_t)))) port_attr_t vl **
      Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen port_attr_t))))
        (Tarray port_attr_t (∘ (PORT_NUMS - Z.of_nat(S n)))) vll2 ** P ->
    new_array_type_vallist_match port_attr_t (vll1 ++ (vl::vll2)) ->
    length (vll1 ++ (vl::vll2)) = ∘ (PORT_NUMS) ->
    s |= AOSPortAttrTbl' (vll1 ++ (vl::vll2)) ** P.
Proof.
  intros.
  assert (Hrgn: Z.of_nat (S n * typelen port_attr_t) <= Int.max_unsigned).
  {
    remember (typelen port_attr_t) as X. 
    unfold port_attr_t in HeqX. simpl in HeqX. 
    rewrite HeqX.
    simpl in H.
    change PORT_NUMS with 64 in H. 
    int auto.
  }
  unfold AOSPortAttrTbl'.
  sep pauto.
  assert (Heq: ∘ (PORT_NUMS) 
               =  Nat.add n (S (∘ (PORT_NUMS - Z.of_nat(S n))) )).
  unfold nat_of_Z.
  assert (Heq1: Z.to_nat (PORT_NUMS - Z.of_nat (S n)) 
              = Nat.sub (Z.to_nat (PORT_NUMS))  (Z.to_nat (Z.of_nat (S n))) ).
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
  asserts_rewrite ($ Z.of_nat (n * typelen port_attr_t) +ᵢ  $ Z.of_nat (typelen port_attr_t) 
                   = $ Z.of_nat (S n * typelen port_attr_t)).
  { int auto. }
  sep pauto.
  unfold port_attr_t.
  unfold Aarray_new.
  unfold Aarray_new'.
  fold port_attr_t.
  sep pauto.
Qed.

Lemma OSportattr_select_sn_ex_strong:
  forall s P semvl,
     s |= EX vll1 n vll2 b i vl ,
       GV OSPortAttrTbl @ Tptr port_attr_t |-> Vptr (b,i)**
             Aarray_new (b, i) (Tarray port_attr_t n) vll1 **
             Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen port_attr_t)))) port_attr_t vl **
             Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen port_attr_t))))
               (Tarray port_attr_t (∘ (PORT_NUMS - Z.of_nat(S n)))) vll2 **
             [| new_array_type_vallist_match port_attr_t semvl |] **
             [| length semvl = ∘ (PORT_NUMS) |] **
             [| semvl = vll1 ++ (vl::vll2) |] ** 
             [| length vll1 = n /\ length vll2 = ∘ (PORT_NUMS - Z.of_nat(S n)) |] **
             [| Z.of_nat(S n) <= PORT_NUMS |] **
              P ->
    s |= AOSPortAttrTbl' semvl ** P.
Proof.
  intros.
  do 6 destruct H.
  sep split in H.
  subst.
  eapply OSportattr_select_sn_strong.
  eauto.
  eauto.
  sep pauto.
  eauto.
Qed.


(* OSPortAttrTbl 值表的展开与合并 end *)
Fixpoint update_nth_vallist (n : nat) (vl :list vallist) (v : vallist) :=
  match vl with
    | nil => nil
    | v'::vl' => match n with
                  | O => v::vl'
                  | S n' => v'::(update_nth_vallist n' vl' v)
                end
  end.

Lemma updata_nth_lvallist:
forall (vll1 vll2: list vallist)  (vl1 vl2 : vallist),
  update_nth_vallist ( length vll1) (vll1 ++ vl1::vll2) vl2 = (vll1 ++ vl2::vll2).
Proof.
Proof.
  intros vll1 vll2 vl1 vl2.
  induction vll1 as [ |v' vll1 IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma nth_upd_neqrev_vll:
  forall (vl :list vallist) (n m : nat) (x y : vallist),
    n <> m ->
    nth_vallist n vl = Some y ->
    nth_vallist n (update_nth_vallist m vl x) = Some y.
Proof.
  inductions vl.
  intros.
  simpl in *. 
  tryfalse.
  intros; simpl in *.
  destruct n.
  simpl.
  destruct m.
  tryfalse.
  simpl ; auto.
  destruct m.
  simpl.
  auto.
  eapply IHvl.
  auto with zarith.
  auto.
Qed.

Ltac sep_get_rv' :=
  match goal with
    | |- _ |= Rv (ebinop ?bop ?e1 ?e2) @ _ == _ =>
      eapply bop_rv;
        [ sep_get_rv'
        | sep_get_rv'
        | simpl; auto
        | auto
        | simpl; auto ]

    | |- _ |= Rv (eunop ?uop ?e) @ _ == _ =>
      eapply uop_rv;
        [ sep_get_rv'
        | simpl; auto
        | auto
        | simpl; auto ]

    | |- _ |= Rv (ecast _ (Tptr _)) @ _ == _ =>
      eapply cast_rv_ptr ; [sep_get_rv'| simpl; eauto; tryfalse| intuition (try eexists; auto 1) ..]
      (* first [ eapply cast_rv_tptr ; [ sep_get_rv | simpl;eauto;tryfalse ]
       *       | eapply cast_rv_tnull; [ sep_get_rv | simpl;eauto;tryfalse ]
       *       | eapply cast_rv_struct_tptr; [ sep_get_rv | simpl;eauto;tryfalse ] ] *)
            
    | |- _ |= Rv (ecast _ (Tint8)) @ _ == _ =>
      eapply cast_rv_tint32_tint8 ; [ sep_get_rv' | simpl;auto ]
                                      
    | |- _ |= Rv (ecast _ (Tint16)) @ _ == _ =>
              eapply cast_rv_tint8_tint16 ; [ sep_get_rv' | simpl;auto ]

    | |- _ |= Rv (ederef _) @ _ == _ =>
      first [ eapply deref_rv;
              [ sep_get_rv'
              | match goal with
                  | H : ?s |= ?P |- ?s |= PV ?l @ _ |=> _  @ _ ** _ =>
                    match find_ptrmapsto P l with
                      | (some ?n) => sep lift n in H; try exact H
                    end
                end 
              | simpl; auto ]
            | eapply deref_ptr_of_array_member_rv;
              [ sep_get_rv'
              | match goal with
                  | H : ?s |= ?P |- ?s |= Aarray (?b, _) _ _ ** _ =>
                    match find_ptrarray_by_block P b with
                      | some ?n => sep lift n in H; try exact H
                    end
                end
              | match goal with |- ?t = Tarray _ _ => try unfold t; simpl; auto end
              | simpl; try lia
              | simpl; try lia
              | simpl; try lia
              | try lia
              | (*unfold Z.div; simpl;*) try (simpl typelen;simpl Z.of_nat); auto
              | try (simpl typelen;simpl Z.of_nat);try lia
              | simpl;try lia
              | try lia
              | auto
              | simpl; auto ] ]

    | H: ?s |= ?P |- ?s |= Rv (evar ?x) @ _ == _ =>
      match find_lvarmapsto P x with
        | some ?m =>
          eapply lvar_rv;
            [ sep lift m in H; exact H
            (*| auto*)
            | simpl; auto ]
        | none _ =>
          match find_dom_lenv P with
            | (none _, _) => fail 1
            | (some ?m, Some ?l) =>
              (* let ret1 := constr:(var_notin_dom x l) in
              let ret2 := (eval compute in ret1) in
              match ret2 with
                | true => *)
                  match find_gvarmapsto P x with
                    | none _ => fail 2
                    | some ?n =>
                      eapply gvar_rv;
                        [ sep lifts (m::n::nil)%list in H; exact H
                        | simpl; auto
                        (*| auto*)
                        | simpl; auto ]
                  end
                (* | false => fail 3
              end *)
          end
      end
        
    | H: ?s |= ?P |- ?s |= Rv (efield (ederef (evar ?x)) _) @ _ == _ =>
      match find_lvarmapsto P x with
        | some ?m =>
          sep lift m in H;
            match type of H with
              | _ |= LV x @ Tptr _ |=> Vptr ?l @ _ ** ?P' =>
                (* match find_ptrstruct P' l with
                  | none _ => fail 1
                  | some ?n =>
                    sep lifts (1::(S n)::nil)%list in H; *)
                      eapply struct_member_rv_general_typeneq;
                      [ exact H
                      | (match goal with|- ?t' = Tstruct _ _ => try unfold t' end); auto
                      | (match goal with|- ?t' = Tstruct _ _ => try unfold t' end); auto
                      | simpl; auto
                      | simpl; auto
                      | simpl; auto
                      | unfold isarray_type;intros;mytac;
                        tryfalse;eexists;splits;auto
                      | unfold isarray_type;
                        let X:=fresh in intro X;
                                       try solve [ (destruct X;do 2 eexists;eauto) ]; 
                                       try
                                         (  
                                           eexists;splits;
                                           [ intros;auto 
                                           | unfold id_nth; simpl; auto 
                                           | simpl; try lia 
                                           | auto 
                                           | simpl;auto]
                                         )
                      | auto
                      ]
                (* end *)
            end
        | none _ =>
          match find_dom_lenv P with
            | (none _, _) => fail 2
            | (some ?m, Some ?ls) =>
              let ret1 := constr:(var_notin_dom x ls) in
              let ret2 := (eval compute in ret1) in
              match ret2 with
                | true =>
                  match find_gvarmapsto P x with
                    | none _ => fail 3
                    | some ?n =>
                      sep lifts (m::n::nil)%list in H;
                        match type of H with
                          | _ |= A_dom_lenv _ ** GV x @ Tptr _ |=> Vptr ?l @ _ ** ?P' =>
                            match find_ptrstruct P' l with
                              | none _ => fail 4
                              | some ?o =>
                                sep lifts (1::2::(S (S o))::nil)%list in H;
                                  eapply struct_member_rv_g_general_typeneq;
                                  [ exact H
                                  | simpl; auto
                                  | match goal with
                                    | |- ?t' = Tstruct _ _ =>
                                          try unfold t'
                                    end; eauto
                                  | match goal with
                                    | |- ?t' = Tstruct _ _  =>
                                          try unfold t'
                                    end; eauto
                                  | simpl; auto
                                  | simpl; auto
                                  | simpl; auto
                                  | unfold symbolic_lemmas.isarray_type;
                                     intros; DeprecatedTactic.mytac; tryfalse;
                                     eexists; splits; 
                                     auto
                                  | unfold symbolic_lemmas.isarray_type;
                                     (let X := fresh in
                                      intro X;
                                       try (solve
                                        [ destruct X; do 2 eexists; eauto   ]);
                                       try
                                        (eexists; splits;
                                         [ let Hx:=fresh in introv Hx; inversion Hx
                                          | unfold id_nth; simpl; auto
                                          | simpl; try lia
                                          | idtac  
                                          | simpl; auto ]))
                                  | auto
                                  ]
                            end
                        end
                  end
                | false => fail 5
              end
          end
      end

    | H: ?s |= ?P |- ?s |= Rv (earrayelem (evar ?x) _) @ _ == _ =>
      match find_lvararray P x with
        | some ?m =>
          sep lift m in H;
            eapply array_member_rv;
            [ exact H
            | auto
            | sep_get_rv'
            | intuition auto
            | simpl; try lia
            | simpl; try lia
            | simpl; try lia
            | auto
            | simpl; auto ]
        | none _ =>
          match find_dom_lenv P with
            | (none _, _) => fail 1
            | (some ?m, Some ?ls) =>
              let ret1 := constr:(var_notin_dom x ls) in
              let ret2 := (eval compute in ret1) in
              match ret2 with
                | true =>
                  match find_gvararray P x with
                    | none _ => fail 2
                    | some ?n =>
                      sep lifts (m::n::nil)%list in H;
                        eapply array_member_rv_g;
                        [ exact H
                        | simpl; auto
                        | auto
                        | sep_get_rv'
                        | intuition auto
                        | intuition auto
                        | simpl; try Lia.lia
                        | simpl; try Lia.lia
                        | simpl; try Lia.lia
                        | auto
                        | simpl; auto ]
                  end
                | false => fail 3
              end
          end
      end

    | |- _ |= Rv (earrayelem _ _) @ _ == _ =>
            eapply expr_array_member_rv;
            [ 
              sep_get_rv';try solve [eauto;simpl;auto]
            | match goal with
                  | H : ?s |= ?P |- ?s |= Aarray ?l _ _ ** _ =>
                    match find_ptrarray P l with
                      | (some ?n) => sep lift n in H; try exact H
                      | _ => fail 4
                    end
                end 
            | sep_get_rv'
            | intuition auto
            | intuition auto
            | simpl; try Lia.lia
            | simpl; try Lia.lia
            | simpl; try Lia.lia
            | auto
            | simpl; auto ]
              
    | |- _ |= Rv (eaddrof (ederef ?e)) @ _ == _ =>
      eapply addrof_deref_rv; sep_get_rv'

    | |- _ |= Rv (eaddrof (earrayelem ?e1 ?e2)) @ _ == _ =>
      eapply addrof_array_elem_rv; 
        [ sep_get_rv' 
        | sep_get_rv'
        | intuition auto 
        | intuition auto ]
    | |- _ |= Rv enull @ _ == _ =>
      apply null_rv
    | |- _ |= Rv econst32 _ @ _ == _ =>
      apply const_rv
 end.

 Ltac sep_get_rv_array_struct_array1:=
  let Hsat := fresh in
  match goal with
  | |- ?P ==> Rv (efield ((efield (ederef ?gident) ?id3) [?ident2′]) ?id2) @ ?tp2 == _ =>
         introv Hsat;
         eapply struct_array_member_rv_array;
         [ try sep_get_rv'; eauto
           | try sep_get_rv'
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
         [ try sep_get_rv'; eauto
           | try sep_get_rv'
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


 Ltac sep_get_rv_array_struct_conf'' :=
  let Hsat := fresh in
  let Hf := fresh in
  let Heq := fresh in
  match goal with
  | |- ?P ==> Rv efield ( (efield ((efield (ederef ?gident) ?id3) [?ident2′]) ?id2) [?ident1′]) ?id1 @ ?tp1 == _ =>
        introv Hsat;
        eapply struct_array_member_rv';
        [ try sep_get_rv_array_struct_array1
        | try sep_get_rv'
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
                [ try sep_get_rv_array_struct_array1
                | try sep_get_rv'
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

Ltac sep_get_rv_array_struct_conf1 :=
  let Hsat := fresh in
  let Hf := fresh in
  let Heq := fresh in
  match goal with
  | |- ?P ==> Rv efield ((efield (ederef ?gident) ?id1)[?ident ′]) ?id2 @ ?tp1 == _ =>
        introv Hsat;
        eapply struct_array_member_rv';
        [ try sep_get_rv'; eauto
        | try sep_get_rv'
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
                [ try sep_get_rv'; eauto
                | try sep_get_rv'
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

(* 修改版  end*)

Lemma nth_val'2nth_val_dom:
forall n rtbl x,
  nth_val' n rtbl = Vint32 x ->
  nth_val n rtbl = Some (Vint32 x).
Proof.
intros.
inductions n;
  simpl in *;  destruct rtbl; simpl in *;tryfalse; try subst; auto.
Qed.

Ltac get_hsat Hs := 
match goal with
  H: _ |= _ |- _ => rename H into Hs
end.
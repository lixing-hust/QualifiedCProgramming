Require Import code_notations.


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
Require Import ios_cap_defs.
Require Import ios_cap.
Require Import include_frm.
Require Import sep_auto.
Require Import math_auto.
Require Import memory.
Require Import ios_cap_defs.
Open Scope Z_scope.
Open Scope int_scope.

(*由于这个是union结构，所以是二选一，里面都有两个变量，所以直接统一写*)

Lemma nth_val'_length_imp:
forall n vl1 a vl2,
  length vl1 = n ->
  nth_val' n (vl1 ++ a :: vl2) = a.
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





Set Nested Proofs Allowed.

Lemma ACSpaceAarrayTptr_unfold_any_idx:
  forall s ptrvl priotbl cspacels n idx,
  s |= ACSpaceAarrayTptr n ptrvl priotbl cspacels ->
  (idx < length priotbl)%nat ->
  (n = length priotbl) ->
  (n = length ptrvl) ->
  ((length priotbl) < 1000)%nat->  (*设置一个很大的数*)
  nth_val' idx ptrvl <> Vnull ->
  s |= EX vll1 v vll2 ptrvl1 ptrvl2 p ,
  ACSpaceAarrayTptr idx ptrvl1 vll1 cspacels**
  ACSpace p v cspacels**
  ACSpaceAarrayTptr(n - (S idx))%nat  ptrvl2 vll2 cspacels**
  [|ptrvl = ptrvl1 ++ ((Vptr p) :: ptrvl2)|] **
  [|priotbl = vll1 ++ (v :: vll2)|] ** 
  [|length ptrvl1 = idx /\ length ptrvl2 = (n - S idx)%nat|] **
  [|length vll1 = idx /\ length vll2 = (n - S idx)%nat|].
Proof.
  intros.
  rename H4 into Hnotnull.
  subst n. 
  assert (Hlen: (length priotbl = idx + (length priotbl - idx))%nat) 
  by auto with arith.
  lets Hsplit1: (firstn_skipn idx ptrvl).
  lets Hsplit2: (firstn_skipn idx priotbl). 
  rewrite <- Hsplit1 in H.
  rewrite <- Hsplit2 in H at 2.
  rewrite Hlen in H.

  lets Harrs0: ACSpaceAarrayTptr_split_strong H.
  assert (HSidx: (S idx <= length priotbl)%nat) by auto with arith.
  assert (Harith: Z.of_nat (S idx * typelen (Tptr CSPACE)) <= Int.max_unsigned). 
  {
    apply Z.le_trans with (m:=Z.of_nat (length priotbl * typelen (Tptr CSPACE))).
    2:{
      apply Z.le_trans with (m:=Z.of_nat (1000 * typelen (Tptr CSPACE))).
      apply inj_le. 
      apply NPeano.Nat.mul_le_mono_r; auto.
      Require Import Lia. 
      lia.
      simpl. rewrite max_unsigned_val. lia.
    }

    apply inj_le. 
    apply NPeano.Nat.mul_le_mono_r; auto.
  }
  lets Harrs00: Harrs0 Harith.
  clear Harrs0.
  assert (Hlensptr: length (firstn idx ptrvl) = idx /\ length (skipn idx ptrvl) = (length ptrvl - idx)%nat).
  {
    split. 
    apply firstn_length_le. auto with arith.
    rewrite <- H2. auto with arith.
    apply skipn_length.
  }
  rewrite <- H2 in Hlensptr.
  lets Harrs000: Harrs00 Hlensptr.
  assert (Hlensprio: length (firstn idx priotbl) = idx /\ length (skipn idx priotbl) = (length priotbl - idx)%nat).
  {
    split. 
    apply firstn_length_le. auto with arith.
    apply skipn_length.
  }
  lets Harrs: Harrs000 Hlensprio.
  clear Harrs000.
  assert (Hlnptr: (length (skipn idx ptrvl) > 0)%nat).
  {
    rewrite skipn_length.  
    cut (0 < length ptrvl - idx)%nat.
    auto with arith.
    rewrite <- NPeano.Nat.lt_add_lt_sub_l.
    rewrite Nat.add_0_r. auto.
    rewrite <- H2. auto.
  }
  assert (Hlnprio: (length (skipn idx priotbl) > 0)%nat).
  {
    rewrite skipn_length.  
    cut (0 < length priotbl - idx)%nat.
    auto with arith.
    rewrite <- NPeano.Nat.lt_add_lt_sub_l.
    rewrite Nat.add_0_r. auto.
  }
  apply length_exists in Hlnptr.
  apply length_exists in Hlnprio.
  destruct Hlnptr as (vptrh & vptrlt & Hlstptr).
  destruct Hlnprio as (vprioh & vpriolt & Hlstprio).
  rewrite Hlstptr, Hlstprio in Harrs.
  sep lift 2%nat in Harrs.
  assert((length priotbl - idx)%nat = S(length priotbl - (S idx))).
    {
      rewrite NPeano.Nat.sub_succ_r.
      rewrite Nat.lt_succ_pred with (z:=0%nat); auto.
      rewrite <- Nat.lt_add_lt_sub_r. simpl. auto.
    }
  rewrite H1 in Harrs.
  apply ACSpaceAarrayTptr_succ_imp_frm in Harrs.
  assert(nth_val' idx ptrvl = vptrh).
  rewrite <- Hsplit1.
  rewrite Hlstptr. 
  rewrite nth_val'_length_imp; eauto.
  destruct Hlensptr. auto. 
  rewrite H4 in Hnotnull.
  clear H4. 
  simpl ACSpaceAarrayTptr in Harrs.
  destruct vptrh;  try(eapply astar_l_afalse_elim in Harrs;  simpl in Harrs;
  tryfalse). tryfalse.
  sep normal in Harrs.
  sep auto.
  1:{
    splits.
    apply firstn_length_le. auto with arith.
    assert(length(skipn idx priotbl)=(length priotbl - idx)%nat).
    apply skipn_length. 
    rewrite Hlstprio in H4.
    simpl in H4. lia.
  }
  1:{
    splits.
    apply firstn_length_le. auto with arith.
    rewrite <- H2. lia. 
    assert(length(skipn idx ptrvl)=(length ptrvl - idx)%nat).
    apply skipn_length. 
    rewrite Hlstptr in H4. 
    simpl in H4. lia.
  }
  rewrite <- Hlstprio.
  auto.
  rewrite <- Hlstptr.
  auto.
Qed.
  
Lemma ACSpaceAarrayTptr_unfold_any_idx_frm:
  forall s ptrvl priotbl cspacels n idx P,
  s |= ACSpaceAarrayTptr n ptrvl priotbl cspacels ** P ->
  (idx < length priotbl)%nat ->
  (n = length priotbl) ->
  (n = length ptrvl) ->
  ((length priotbl) < 1000)%nat->  (*设置一个很大的数*)
  nth_val' idx ptrvl <> Vnull ->
  s |= (EX vll1 v vll2 ptrvl1 ptrvl2 p ,
  ACSpaceAarrayTptr idx ptrvl1 vll1 cspacels**
  ACSpace p v cspacels**
  ACSpaceAarrayTptr(n - (S idx))%nat  ptrvl2 vll2 cspacels**
  [|ptrvl = ptrvl1 ++ ((Vptr p) :: ptrvl2)|] **
  [|priotbl = vll1 ++ (v :: vll2)|] ** 
  [|length ptrvl1 = idx /\ length ptrvl2 = (n - S idx)%nat|] **
  [|length vll1 = idx /\ length vll2 = (n - S idx)%nat|]) ** P.
Proof.
    intros.
    sep cancel P.
    eapply ACSpaceAarrayTptr_unfold_any_idx; eauto.
Qed.


Lemma Astar4_sat_split:
  forall s a b c d ,
  s |= a ** b ** c ** [|d|] ->
  exists M1 M2 M o1 o2 o,
    M = getmem s /\
    join M1 M2 M /\
    o = getabst s /\
    join o1 o2 o /\
    substmo s M1 o1 |= a /\
    (exists M3 M4 M0 o3 o4 o0,
     M0 = getmem (substmo s M2 o2) /\
     join M3 M4 M0 /\
     o0 = getabst (substmo s M2 o2) /\
     join o3 o4 o0 /\
     substmo (substmo s M2 o2) M3 o3 |= b /\
     (exists M5 M6 M7 o5 o6 o7,
      M7 = getmem (substmo (substmo s M2 o2) M4 o4) /\
      join M5 M6 M7 /\
      o7 = getabst (substmo (substmo s M2 o2) M4 o4) /\
      join o5 o6 o7 /\
      substmo (substmo (substmo s M2 o2) M4 o4) M5 o5 |= c /\
      d /\ empst (substmo (substmo (substmo s M2 o2) M4 o4) M6 o6)))
.
Proof.
  intros.
  unfold sat in H. fold sat in H.
  auto.
Qed.




Lemma AOSCSpacePrioTbl_unfold_any_idx: 
    forall s priotbl idx ptrvl b i cspacels, 
    s |= AOSCSpacePrioTbl (b, i)ptrvl priotbl cspacels->
    (idx < length priotbl)%nat ->
    nth_val' idx ptrvl <> Vnull ->
    s |= EX vll1 v vll2 ptrvl1 ptrvl2 p ,
        G& OSCSpacePrioTbl @ (Tarray (Tptr CSPACE) 64) == (b, i) **
        PV (b, i +ᵢ $ Z.of_nat (idx * (typelen (Tptr CSPACE)))) @ (Tptr CSPACE) |-> Vptr p **
        Aarray_rm (b, i) 64%nat (Tptr CSPACE) ptrvl idx **
        ACSpaceAarrayTptr idx ptrvl1 vll1 cspacels**
        ACSpace p v cspacels**
        ACSpaceAarrayTptr(64 - (S idx))%nat  ptrvl2 vll2 cspacels**
        [|ptrvl = ptrvl1 ++ ((Vptr p) :: ptrvl2)|] **
        [|priotbl = vll1 ++ (v :: vll2)|] ** 
        [|length ptrvl1 = idx /\ length ptrvl2 = (64 - S idx)%nat|] **
        [|length vll1 = idx /\ length vll2 = (64 - S idx)%nat|].
Proof.
    intros.
    rename H1 into Hnotnull.
    unfold AOSCSpacePrioTbl in H.
    eapply Astar4_sat_split in H. 
    simpl substmo in H; simpl getmem in H; simpl getabst in H; simpl empst in H.

    simpljoin1.
    rewrite <- H17 in *.
    assert (Hlen: (length priotbl = idx + (length priotbl - idx))%nat) 
    by auto with arith.
    lets Hsplit1: (firstn_skipn idx ptrvl).
    lets Hsplit2: (firstn_skipn idx priotbl). 
    rewrite <- Hsplit1 in H14.
    rewrite <- Hsplit2 in H14 at 2.
    rewrite Hlen in H14.

    lets Harrs0: ACSpaceAarrayTptr_split_strong H14.
    assert (HSidx: (S idx <= length priotbl)%nat) by auto with arith.
    assert (Harith: Z.of_nat (S idx * typelen (Tptr CSPACE)) <= Int.max_unsigned). 
    {
      apply Z.le_trans with (m:=Z.of_nat (length priotbl * typelen (Tptr CSPACE))).
      2:{
        Require Import Lia.
        rewrite H17.  simpl.   rewrite max_unsigned_val.
        lia.
      }

      apply inj_le. 
      apply NPeano.Nat.mul_le_mono_r; auto.
    }
    lets Harrs00: Harrs0 Harith.
    clear Harrs0.
    assert (Hlensptr: length (firstn idx ptrvl) = idx /\ length (skipn idx ptrvl) = (length ptrvl - idx)%nat).
  {
    split. 
    apply firstn_length_le. auto with arith.
    rewrite H15. auto with arith.
    apply skipn_length.
  }
  rewrite H15 in Hlensptr.
  lets Harrs000: Harrs00 Hlensptr.
  assert (Hlensprio: length (firstn idx priotbl) = idx /\ length (skipn idx priotbl) = (length priotbl - idx)%nat).
  {
    split. 
    apply firstn_length_le. auto with arith.
    apply skipn_length.
  }
  lets Harrs: Harrs000 Hlensprio.
  clear Harrs000.
  destruct Harrs.
  simpljoin1.
  destruct_s s.
  simpl in H2, H7, H10, H12.
  assert (HlenS: (length priotbl - idx = S (length priotbl - (S idx)))%nat).
  {
    rewrite NPeano.Nat.sub_succ_r.
    rewrite Nat.lt_succ_pred with (z:=0%nat); auto.
    rewrite <- Nat.lt_add_lt_sub_r. simpl. auto.
  }
  rewrite HlenS in H12.
  assert (Hlnptr: (length (skipn idx ptrvl) > 0)%nat).
  {
    rewrite skipn_length.  
    cut (0 < length ptrvl - idx)%nat.
    auto with arith.
    rewrite <- NPeano.Nat.lt_add_lt_sub_l.
    rewrite Nat.add_0_r. auto.
    rewrite H15. auto.
  }
  assert (Hlnprio: (length (skipn idx priotbl) > 0)%nat).
  {
    rewrite skipn_length.  
    cut (0 < length priotbl - idx)%nat.
    auto with arith.
    rewrite <- NPeano.Nat.lt_add_lt_sub_l.
    rewrite Nat.add_0_r. auto.
  }
  apply length_exists in Hlnptr.
  apply length_exists in Hlnprio.
  destruct Hlnptr as (vptrh & vptrlt & Hlstptr).
  destruct Hlnprio as (vprioh & vpriolt & Hlstprio).
  rewrite Hlstptr, Hlstprio in H12.
  apply ACSpaceAarrayTptr_succ_imp in H12.



  destruct H12. simpljoin1.
  simpl in H5, H23.
  simpl substmo in H24, H25.
  unfold ACSpaceAarrayTptr in H24.
  assert(nth_val' idx ptrvl = vptrh).
  rewrite <- Hsplit1.
  rewrite Hlstptr.
  rewrite nth_val'_length_imp; eauto. 
  rewrite H in Hnotnull.
  clear H. 
  destruct vptrh. simpl in H24. tryfalse.
  tryfalse.
  simpl in H24. tryfalse.

  simpl_sat_goal.
  simpl Aarray in *. 
  eapply array_asrt_eq with(m:=idx) 
  (v :=Vptr a0)in H9.
  simpl in H1, H3, H6, H8, H11, H13.
  simpl substmo in H4, H9, H14.
  destruct H9. simpljoin1.
  simpl in H9, H26.
  simpl substmo in H27, H28.
  exists (firstn idx priotbl) vprioh.
  exists vpriolt.
  exists (firstn idx ptrvl).
  exists vptrlt.
  exists a0.
  simpl substmo in H4.
  simpl in H1, H3, H6, H8.
  simpl substmo in H9.
  assert(Haddition: $ Z.of_nat (idx * typelen CSPACE ∗) = Int.mul ($ Z.of_nat (typelen CSPACE ∗))
  ($ Z.of_nat idx)).
  {
      rewrite Nat2Z.inj_mul.
      simpl typelen.
      mauto.
      rewrite Z.mul_comm. 
      auto.
  }
  simpl in H16.
  destruct H16 as (Hx7emp & Hx16emp).
  simpl in H11, H13.
  subst x12. unfold emposabst in Hx16emp. subst x15.
  assert(x11 = x6).
  {
    apply map_join_emp' in H11. auto.
  }
  subst x11.
  assert (x14 = x9). { apply map_join_emp' in H13. auto. }
  subst x14.

  exists x x0 m x2 x3 o. splits; eauto.
  exists x17. do 2 eexists. eexists x22. do 2 eexists.
  splits; eauto. 
  
  3:{
    
    rewrite Haddition. auto.
  }
  3:{
    eexists x20. do 2 eexists. exists x23. do 2 eexists. 
    splits; eauto.
    
    3:{
      exists x1. do 2 eexists. exists x10. do 2 eexists.
      splits; eauto.
      1:{
          exists x7. do 2 eexists. exists x18. do 2 eexists.
          splits; eauto.
          eapply astar_r_aemp_elim in H24.
          auto.
          exists x16. do 2 eexists. exists x19. do 2 eexists.
          splits; eauto.
          instantiate (1:=empenv). join auto.
          instantiate(1:=emp). join auto.
          do 6 eexists. splits; eauto.
          join auto. join auto. 
          split.  rewrite <- Hlstptr.
          rewrite Hsplit1. auto.
          simpl. splits; unfolds. auto. auto.
          rewrite <- Hlstprio. rewrite Hsplit2. auto.
          do 6 eexists.
          splits; eauto. join auto. join auto.
          splits; simpl. eauto. 
          splits; unfolds; eauto.
          do 6 eexists.
          splits; eauto. join auto. join auto.
          splits; eauto.
          splits. auto.
          rewrite H17.
          eapply sub_eq_succ. lia.
          rewrite Hlstptr in H22.
          simpl in H22. rewrite H17 in H22. auto.
          simpl. splits; unfolds; auto.
          splits.
          rewrite H19. auto.
          eapply sub_eq_succ. lia.
          rewrite Hlstprio in H20.
          simpl in H19. auto.
          simpl. splits; unfolds; auto.
      }
    }
    join auto.
    join auto.
  }
  join auto. join auto.
  auto.

  clear -Hlstptr.
  Lemma nth_firstn_val: 
    forall idx ptrvl  a0 vptrlt,
    skipn idx ptrvl = Vptr a0 :: vptrlt
    -> nth_val idx ptrvl = Some (Vptr a0).
      Proof.
        induction idx; destruct ptrvl; intros.
        simpl in H. tryfalse.
        simpl in H. inverts H. simpl. auto.
        simpl in H. tryfalse.
        simpl in H.  apply IHidx in H.
        simpl.  auto.
      Qed.
  eapply nth_firstn_val. eauto.
Qed.






Lemma AOSCSpacePrioTbl_unfold_any_idx_frm: 
forall s priotbl idx ptrvl P b i cspacels, 
s |= AOSCSpacePrioTbl (b, i)ptrvl priotbl cspacels ** P ->
(idx < length priotbl)%nat ->
nth_val' idx ptrvl <> Vnull ->
s |= (EX vll1 v vll2 ptrvl1 ptrvl2 p ,
  G& OSCSpacePrioTbl @ (Tarray (Tptr CSPACE) 64) == (b, i) **
  PV (b, i +ᵢ $ Z.of_nat (idx * (typelen (Tptr CSPACE)))) @ (Tptr CSPACE) |-> Vptr p **
  Aarray_rm (b, i) 64%nat (Tptr CSPACE) ptrvl idx **
  ACSpaceAarrayTptr idx ptrvl1 vll1 cspacels**
  ACSpace p v cspacels**
  ACSpaceAarrayTptr(64 - (S idx))%nat  ptrvl2 vll2 cspacels**
  [|ptrvl = ptrvl1 ++ ((Vptr p) :: ptrvl2)|] **
  [|priotbl = vll1 ++ (v :: vll2)|] ** 
  [|length ptrvl1 = idx /\ length ptrvl2 = (64 - S idx)%nat|] **
  [|length vll1 = idx /\ length vll2 = (64 - S idx)%nat|]) ** P.
Proof.
    intros.
    sep cancel P.
    eapply AOSCSpacePrioTbl_unfold_any_idx; eauto.
Qed.

Lemma Aarray'_succ_imp :
  forall s n  p vl b i t, 
  s |= Aarray' (b, i) (S n) t (p :: vl)->
    s |= Aarray' (b, i)  1%nat t (p::nil) ** Aarray' (b, i+ᵢInt.repr(Z.of_nat(typelen t)))  n t vl.
Proof.
    intros.
    sep pauto.
    simpl Aarray' in *.
    sep normal.
    sep auto.
Qed.

Lemma Aarray'_succ_imp_frm :
  forall s n  p vl b i t P, 
  s |= Aarray' (b, i) (S n) t (p :: vl) ** P->
    s |= Aarray' (b, i)  1%nat t (p::nil) ** Aarray' (b, i+ᵢInt.repr(Z.of_nat(typelen t)))  n t vl ** P.
Proof.
  sep pauto.
  eapply Aarray'_succ_imp; eauto.
Qed.


Lemma Aarray'_split_strong:
  forall  vll1 vll2  t b i n m s,
  s |= Aarray' (b, i) (n + m) t (vll1 ++ vll2)->
  Z.of_nat (n * typelen (t)) <= Int.max_unsigned -> 
  Z.of_nat(typelen t) <= Int.max_unsigned ->
  length vll1 = n /\ length vll2 = m ->
  s |= Aarray' (b, i) n t vll1
  ** Aarray' (b, i +ᵢ $ Z.of_nat (n * (typelen t))%nat) m t vll2.
Proof.
  induction vll1; induction n; intros.

  simpl Aarray' in *.
  eapply astar_l_aemp_intro.
  auto.
  rewrite Int.add_zero. auto. 
  simpl in H2. destruct H2. tryfalse.
  simpl in H2. destruct H2. tryfalse.
  change ((a::vll1)++vll2) with (a::(vll1++vll2)) in H.
  rewrite Nat.add_succ_l in H.
  eapply Aarray'_succ_imp in H.
  simpl Aarray' in *.
  sep normal in H. sep auto.
  assert (i +ᵢ
  $ Z.of_nat (typelen t + n * typelen t) = (i +ᵢ
  $ Z.of_nat (typelen t)) +ᵢ $ Z.of_nat(n * typelen t)). 
  rewrite Int.add_assoc.
  rewrite Nat2Z.inj_add.
  assert($ Z.of_nat (typelen t) +ᵢ
  $ Z.of_nat (n * typelen t) = $
  (Z.of_nat (typelen t) + Z.of_nat (n * typelen t))).
  rewrite Int.add_unsigned. rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr. auto. lia. lia. 
  rewrite H3. auto.
  rewrite H3. 
  remember (i +ᵢ  $ Z.of_nat (typelen t)) as I.
  apply IHvll1 with (i:=I); auto.
  lia.  simpl in H2. destruct H2.
  split; lia. 
Qed.


Lemma Aarray'_unfold_any_idx:
  forall s t n b i idx lv,
  s |= Aarray' (b, i) n   t lv ->
  (idx < n)%nat ->
  (length lv = n)%nat ->
  Z.of_nat (n * typelen (t)) <= Int.max_unsigned -> 
  Z.of_nat(typelen (t)) <= Int.max_unsigned ->
  s |= EX vll1 vll2 p,
      Aarray' (b, i) idx (t) vll1 **
      PV (b, i+ᵢ $ Z.of_nat (idx * (typelen t))) @ (t) |-> p **
      Aarray' (b, i+ᵢ $ Z.of_nat ((S idx) * (typelen t))) (n - (S idx))%nat (t) vll2 **
      [|lv = vll1++(p::vll2)|]**
      [|length vll1 = idx /\ length vll2 = (n - (S idx))%nat|].
Proof.
  intros.
  assert (Hlen: (length lv = idx + (length lv - idx))%nat).
  lia. 
  lets Hsplit: (firstn_skipn idx lv).
  rewrite <- Hsplit in H.
  rewrite H1 in Hlen.
  rewrite Hlen in H.

  eapply Aarray'_split_strong in H; eauto.
  2: lia. 
  2:{
    splits.
    apply firstn_length_le. auto with arith.
    rewrite H1. lia. 
    rewrite <- H1.
    apply skipn_length.
  }
  assert (Hln: (length (skipn idx lv) > 0)%nat).
    {
      rewrite skipn_length.  
      cut (0 < length lv - idx)%nat.
      auto with arith.
      rewrite <- NPeano.Nat.lt_add_lt_sub_l.
      rewrite Nat.add_0_r. auto.
      rewrite H1.
      auto.
    }
    apply length_exists in Hln.
    destruct Hln as (vh & vt & Hht).
    rewrite Hht in H. 
    sep lift 2%nat in H.
    assert((n - idx)%nat = S(n - (S idx))).
    {
      rewrite NPeano.Nat.sub_succ_r.
      rewrite Nat.lt_succ_pred with (z:=0%nat); auto.
      rewrite <- Nat.lt_add_lt_sub_r. simpl. auto.
    }
    rewrite H4 in H.
    eapply Aarray'_succ_imp_frm in H.
    simpl Aarray' in H.  sep normal in H. sep auto.
    assert($ Z.of_nat (idx * typelen t)+ᵢ$ Z.of_nat (typelen t) 
     = $Z.of_nat (S idx * typelen t)).
    rewrite Int.add_unsigned. rewrite Int.unsigned_repr.
    rewrite Int.unsigned_repr.
    2:lia. 
    2:lia. 
    assert(Z.of_nat (idx*typelen t) + Z.of_nat(typelen t) = Z.of_nat(S idx * typelen t)). lia. 
    rewrite H1. auto.
    rewrite Int.add_assoc in H. 
    rewrite H1 in H.
    sep auto.
    1:{
      splits.
      apply firstn_length_le. auto with arith.
      assert(length(skipn idx lv) = (length lv - idx)%nat).
      apply skipn_length. 
      rewrite Hht in H1.
      simpl in H1. lia.
    }
    1:{
      rewrite <- Hht.  rewrite Hsplit. auto.
    }
Qed.



Lemma Aarray'_unfold_any_idx_frm:
  forall s t n b i idx lv P,
  s |= Aarray' (b, i) n  t lv ** P->
  (idx < n)%nat ->
  (length lv = n)%nat ->
  Z.of_nat (n * typelen (t)) <= Int.max_unsigned -> 
  Z.of_nat(typelen t) <= Int.max_unsigned ->
  s |= (EX vll1 vll2 p,
      Aarray' (b, i) idx t vll1 **
      PV (b, i+ᵢ $ Z.of_nat (idx * (typelen t))) @ t |-> p **
      Aarray' (b, i+ᵢ $ Z.of_nat ((S idx) * (typelen t))) (n - (S idx))%nat t vll2 **
      [|lv = vll1++(p::vll2)|]**
      [|length vll1 = idx /\ length vll2 = (n - (S idx))%nat|]) ** P.
Proof.
  intros.
  sep cancel P. 
  eapply Aarray'_unfold_any_idx; eauto.
Qed.





Lemma same_lenth_list_first_eq:
forall (t:Type)(x1 x3 x2 x4 l: list t),
  l = x1 ++ x2 ->
  l = x3 ++ x4->
  (length x1 = length x3)%nat ->
  x1 = x3.
Proof.
  induction x1; induction x3; intros.
  simpl in *. subst l.  split; auto.
  simpl in H1. tryfalse.
  simpl in H1. tryfalse.
  rewrite H in H0. inverts H0.
  assert(x1 = x3).
  simpl in H1. assert(length x1 = length x3) by lia. 
  lets Heq: IHx1 H4. eauto.
  eapply Heq. auto.
  rewrite H0. auto.
Qed.


Lemma same_lenth_list_last_eq:
forall (t:Type) (x1 x3 x2 x4 l: list t),
  l = x1 ++ x2 ->
  l = x3 ++ x4->
  (length x1 = length x3)%nat ->
  x2 = x4.
Proof.
  induction x1; induction x3; intros.
  simpl in *. subst l.  auto.
  simpl in H1. tryfalse.
  simpl in H1. tryfalse.
  rewrite H in H0. inverts H0.
  assert(x2 = x4).
  simpl in H1. assert(length x1 = length x3) by lia. 
  lets Heq: IHx1 H4. eauto.
  eapply Heq. auto.
  rewrite H0. auto.
Qed.

Lemma same_list_eq3:
  forall (t: Type) (l x1 x2  x3 x4: list t) a b,
  l = x1 ++ a :: x2 ->
  l = x3 ++ b :: x4 ->
  (length x1 = length x3) ->
  x1 = x3 /\ a = b /\ x2 =x4.
Proof.
  intros.
  rewrite list_cons_assoc in H, H0.
  rewrite app_assoc_reverse in H, H0.
  split. 
  lets Hsame: same_lenth_list_first_eq H H0 H1.
  auto.
  split. 
  lets Hsamelast: same_lenth_list_last_eq H H0 H1.
  inverts Hsamelast. auto.
  rewrite app_assoc in H, H0.
  lets Hsamelast: same_lenth_list_last_eq H H0.
  assert(length (x1 ++ a :: nil) =length (x3 ++ b :: nil)).
  rewrite app_length. rewrite app_length. simpl. lia.
  eapply Hsamelast in H2. auto.
Qed.


Lemma list_get_two_elements:
  forall l1 l2 idx,
  (idx < length l1)%nat ->
  nth_val' idx l1 = nth_val' idx (l1 ++ l2).
Proof. 
  induction l1; destruct idx; intros.
  simpl in H. lia. 
  simpl in H. lia. 
  simpl. auto. 
  simpl. 
  simpl in H. 
  assert(idx < length l1)%nat by lia.
  eapply IHl1 in H0; eauto. 
Qed.

Lemma AOSCSpacePrioTbl_unfold_any_two_idx: 
    forall s priotbl idx1 idx2 ptrvl b i cspacels, 
    s |= AOSCSpacePrioTbl (b, i)ptrvl priotbl cspacels->
    (idx1 < length priotbl)%nat -> 
    (idx2 < idx1)%nat ->
    nth_val' idx1 ptrvl <> Vnull ->
    nth_val' idx2 ptrvl <> Vnull ->
    s |= EX vll11 v1 v2 vll12 vll2 ptrvl11 ptrvl12 ptrvl2 p1 p2 ,
        G& OSCSpacePrioTbl @ (Tarray (Tptr CSPACE) 64) == (b, i) **
        PV (b, i +ᵢ $ Z.of_nat (idx2 * (typelen (Tptr CSPACE)))) @ (Tptr CSPACE) |-> Vptr p1 **
        PV (b, i +ᵢ $ Z.of_nat (idx1 * (typelen (Tptr CSPACE)))) @ (Tptr CSPACE) |-> Vptr p2 **
        Aarray' (b, i) idx2 (Tptr CSPACE) ptrvl11 **
        Aarray' (b, i+ᵢ $ Z.of_nat (S idx2 * (typelen (Tptr CSPACE)))) (idx1 - (S idx2)) (Tptr CSPACE) ptrvl12 **
        Aarray' (b, i+ᵢ $ Z.of_nat (S idx1 * (typelen (Tptr CSPACE)))) (64%nat - (S idx1)) (Tptr CSPACE) ptrvl2 **
        ACSpaceAarrayTptr idx2 ptrvl11 vll11 cspacels**
        ACSpace p1 v1 cspacels**
        ACSpaceAarrayTptr(idx1 - (S idx2))%nat  ptrvl12 vll12 cspacels**
        ACSpace p2 v2 cspacels **
        ACSpaceAarrayTptr (64%nat - (S idx1))  ptrvl2 vll2 cspacels **
        [|ptrvl = ptrvl11 ++ ((Vptr p1)::ptrvl12) ++ ((Vptr p2) :: ptrvl2) |] **
        [|priotbl = vll11 ++ (v1 :: vll12) ++ (v2 :: vll2)|] ** 
        [|length ptrvl11 = idx2 /\ length ptrvl12 = (idx1 - (S idx2))%nat /\ length ptrvl2 = (64 - (S idx1))%nat|] **
        [|length vll11 = idx2 /\ length vll12 = (idx1 - (S idx2))%nat /\ length vll2 = (64 - (S idx1))%nat|].
Proof.
    intros.
    rename H2 into Hnotnull1.
    rename H3 into Hnotnull2.
    unfold AOSCSpacePrioTbl in H.
    unfold Aarray in *.
    
    sep lift 3%nat in H.
    eapply ACSpaceAarrayTptr_unfold_any_idx_frm with(idx:=idx1) in H; eauto.
    2:{
      sep split in H. 
      simpljoin. auto.
    }
    2:{
      sep split in H. 
      simpljoin. auto.
    }
    2:{
      sep split in H. 
      simpljoin. lia.
    }
    sep normal in H. sep destruct H.
    simpljoin.
    sep split in H.
    destruct H4. destruct H5.
    sep lift 2%nat in H. 
    
    sep lift 5%nat in H. 
    eapply Aarray'_unfold_any_idx_frm with(idx:=idx1) in H; eauto.
    2:{
      simpljoin.  rewrite <- H9.
      auto.
    }
    2:{
      simpljoin. auto.
    }
    2:{
      simpl. rewrite max_unsigned_val. lia.
    }
    2:{
      simpl. rewrite max_unsigned_val. lia. 
    }
    sep normal in H. sep destruct H.
    sep split in H. 
    destruct H10. rewrite <- H10 in H4.
    lets Hsame: same_list_eq3 H2 H9 H4.
    destruct Hsame. destruct H13.
    subst x7.
    sep lift 5%nat in H. 
    eapply ACSpaceAarrayTptr_unfold_any_idx_frm with(idx:=idx2) in H; eauto.
    2:{
      lia. 
    }
    2:{
      rewrite H10 in H4. auto.
    }
    2: lia. 
    sep normal in H. sep destruct H.
    sep split in H. 
    sep lift 4%nat in H. 
    eapply Aarray'_unfold_any_idx_frm with(idx:=idx2) in H; eauto.
    2:{
      simpl typelen. 
      destruct H6.
      destruct H18.
      rewrite H18 in H0.
      clear -H0. int auto.
    }
    2: simpl;rewrite max_unsigned_val; lia. 
    sep normal in H. sep destruct H. 
    sep split in H.  
    rewrite <- H12 in H18.
    destruct H16, H19.
    rewrite <- H19 in H16.
    lets Hsame: same_list_eq3 H13 H18 H16.
    destruct Hsame. destruct H23. subst x15.
    sep normal. sep eexists.
    sep cancel OSCSpacePrioTbl.
    sep cancel 2%nat 1%nat. 
    sep cancel 6%nat 1%nat. 
    sep cancel 1%nat 1%nat. 
    sep cancel 1%nat 1%nat. 
    sep auto.
    2:{
      rewrite app_assoc. auto.
    }
    2:{
      rewrite app_assoc.
      auto.
    }
    split. destruct H17. auto.
    split. destruct H17. auto. auto.
    assert(nth_val' idx2 x2 = nth_val' idx2 ptrvl).
    subst ptrvl.
    eapply list_get_two_elements; eauto.
    rewrite H4. rewrite H10.
    lia.
    rewrite H13. auto.
Qed.
    

Lemma AOSCSpacePrioTbl_unfold_any_two_idx_frm: 
    forall s priotbl idx1 idx2 ptrvl b i cspacels P, 
    s |= AOSCSpacePrioTbl (b, i)ptrvl priotbl cspacels ** P->
    (idx1 < length priotbl)%nat -> 
    (idx2 < idx1)%nat ->
    nth_val' idx1 ptrvl <> Vnull ->
    nth_val' idx2 ptrvl <> Vnull ->
    s |= (EX vll11 v1 v2 vll12 vll2 ptrvl11 ptrvl12 ptrvl2 p1 p2 ,
        G& OSCSpacePrioTbl @ (Tarray (Tptr CSPACE) 64) == (b, i) **
        PV (b, i +ᵢ $ Z.of_nat (idx2 * (typelen (Tptr CSPACE)))) @ (Tptr CSPACE) |-> Vptr p1 **
        PV (b, i +ᵢ $ Z.of_nat (idx1 * (typelen (Tptr CSPACE)))) @ (Tptr CSPACE) |-> Vptr p2 **
        Aarray' (b, i) idx2 (Tptr CSPACE) ptrvl11 **
        Aarray' (b, i+ᵢ $ Z.of_nat (S idx2 * (typelen (Tptr CSPACE)))) (idx1 - (S idx2)) (Tptr CSPACE) ptrvl12 **
        Aarray' (b, i+ᵢ $ Z.of_nat (S idx1 * (typelen (Tptr CSPACE)))) (64%nat - (S idx1)) (Tptr CSPACE) ptrvl2 **
        ACSpaceAarrayTptr idx2 ptrvl11 vll11 cspacels**
        ACSpace p1 v1 cspacels**
        ACSpaceAarrayTptr(idx1 - (S idx2))%nat  ptrvl12 vll12 cspacels**
        ACSpace p2 v2 cspacels **
        ACSpaceAarrayTptr (64%nat - (S idx1))  ptrvl2 vll2 cspacels **
        [|ptrvl = ptrvl11 ++ ((Vptr p1)::ptrvl12) ++ ((Vptr p2) :: ptrvl2) |] **
        [|priotbl = vll11 ++ (v1 :: vll12) ++ (v2 :: vll2)|] ** 
        [|length ptrvl11 = idx2 /\ length ptrvl12 = (idx1 - (S idx2))%nat /\ length ptrvl2 = (64 - (S idx1))%nat|] **
        [|length vll11 = idx2 /\ length vll12 = (idx1 - (S idx2))%nat /\ length vll2 = (64 - (S idx1))%nat|]) ** P.
Proof.
  intros.
  sep cancel P.
  eapply AOSCSpacePrioTbl_unfold_any_two_idx; eauto.
Qed.


Lemma ASlots_succ_alt :
  forall s a vll n b i P, 
    s |= ASlots (b,i) 1  (a::nil) ** ASlots (b,i +ᵢ  $ Z.of_nat  (typelen Slot)) n vll ** P -> 
    s |= ASlots (b,i) (S n) (a :: vll) ** P.
Proof.
    intros.
    sep pauto.
    simpl ASlots in *.
    destruct a.
    sep normal in H.
    sep auto.
Qed.



Lemma ASlots_succ_imp :
  forall s a vll n b i, 
  s |= ASlots (b,i) (S n)(a :: vll) ->
  s |= ASlots(b,i) 1 (a::nil) ** ASlots (b,i +ᵢ  $ Z.of_nat  (typelen Slot)) n vll .
    
Proof.
    intros.
    sep pauto.
    simpl ASlots in *.
    destruct a. 
    sep auto.
Qed.

Lemma ASlots_split_strong :
  forall  n  m b i s vll1 vll2, 
    s |= ASlots (b,i) (n + m)  (vll1 ++ vll2) ->
    Z.of_nat (S n * typelen (Slot)) <= Int.max_unsigned -> 
    (* 0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned -> *)
    length vll1 = n /\ length vll2 = m ->
    s |= ASlots (b, i) n vll1 ** ASlots (b, i +ᵢ $ Z.of_nat (n * (typelen (Slot)))) m  vll2.
Proof.
  induction n; destruct vll1; intros.
  simpl ASlots in *.
  simpl in H.
  rewrite Int.add_zero.
  eapply astar_l_aemp_intro.
  auto.
  destruct H1.
  tryfalse.
  destruct H1. tryfalse.
  eapply ASlots_succ_alt.
  change ((p :: vll1) ++ vll2) with (p :: (vll1 ++ vll2)) in H.

  rewrite Nat.add_succ_l in H.
  eapply ASlots_succ_imp in H.
  sep pauto.
  cut ($ Z.of_nat (S n * typelen (Slot )) = $ Z.of_nat (typelen (Slot)) +ᵢ $ Z.of_nat (n * typelen (Slot))).
  {
    intro.
    rewrite H3.
    rewrite <- Int.add_assoc.
    eapply IHn.

    sep pauto.
    auto with zarith.
    inverts H1. auto.
  }
  int auto.
Qed.

Lemma ASlots_split_strong_frm: 
forall  n  m b i s vll1 vll2 P , 
  s |= ASlots (b,i) (n + m)  (vll1 ++ vll2) ** P ->
  Z.of_nat (S n * typelen (Slot)) <= Int.max_unsigned -> 
  (* 0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned -> *)
  length vll1 = n /\ length vll2 = m ->
  s |= ASlots (b, i) n vll1 ** ASlots (b, i +ᵢ $ Z.of_nat (n * (typelen (Slot)))) m  vll2 ** P.
Proof.
  intros. sep pauto.
  eapply ASlots_split_strong; eauto.
Qed.



Fixpoint nth_slots n (vl: list (int32 * (int32* cap_content_type))):=
    match vl with 
    |nil => None 
    |v :: vl' =>
        match n with 
        | 0%nat => Some v 
        | S n' => nth_slots n' vl' 
        end 
    end.
Lemma  ASlots_unfold_any_idx:
forall s b i n slotsvl idx, 
s |= ASlots (b, i) n slotsvl ->
(idx < n)%nat ->
n = Z.to_nat SLOT_NUM ->
length slotsvl = n ->
s |= EX vll1 vll2 slot_type slot_cap,
    ASlots (b, i) idx vll1**
    PV (b, i +ᵢ $ Z.of_nat (idx * (typelen Slot))) @ Int32 |-> Vint32 slot_type ** 
    ACap (b, i +ᵢ $ Z.of_nat (idx * (typelen Slot)) +ᵢ (Int.repr 4)) slot_cap
    ** ASlots (b, i +ᵢ $ Z.of_nat ((S idx) * (typelen Slot))) (n - (S idx)) vll2
    ** [|slotsvl = vll1 ++ (slot_type, slot_cap):: vll2|] **
    [|length vll1 = idx /\ length vll2 = (n - (S idx))%nat|] **
    [|nth_slots idx slotsvl = Some (slot_type, slot_cap)|].
Proof.
    introv Hsat.
    introv Hlenle.
    introv Hn.
    introv Hslotslen.
    assert (Hlen: (n = idx + (n - idx))%nat) by auto with arith.
    lets Hsplit: firstn_skipn idx slotsvl.
    rewrite <- Hsplit in Hsat.
    rewrite Hlen in Hsat.
    lets Harrs0: ASlots_split_strong Hsat.
    assert(HSidx: (S idx <= n)%nat) by auto with arith.
    assert(Harith: (Z.of_nat (S idx * typelen Slot) <=
    Int.max_unsigned)).
    {
        simpl typelen.
        apply Z.le_trans with (m:=Z.of_nat (255 * typelen Slot)).
        apply inj_le. 
        simpl typelen. apply NPeano.Nat.mul_le_mono_r; auto.
        rewrite Hn in HSidx. unfold SLOT_NUM in HSidx.
        auto.
        simpl typelen.
        rewrite max_unsigned_val.
        lia. 
    }
    lets Harrs00: Harrs0 Harith.
    clear Harrs0.
    assert(Hlens: length (firstn idx slotsvl) = idx /\
    length (skipn idx slotsvl) = (n - idx)%nat).
    {
        splits.
        apply firstn_length_le. auto with arith.
        rewrite Hslotslen. auto with arith.
        rewrite <- Hslotslen.
        apply skipn_length.
    }
    lets Harrs: Harrs00 Hlens.
    clear Harrs00.
    destruct_s s. 
    destruct Harrs.
    simpljoin1.
    simpl substmo in H3, H4.
    simpl in H0, H2.
    assert (HlenS: (length slotsvl - idx = S (length slotsvl - (S idx)))%nat).
    {
      rewrite NPeano.Nat.sub_succ_r.
      rewrite Nat.lt_succ_pred with (z:=0%nat); auto.
      rewrite <- Nat.lt_add_lt_sub_r. simpl. auto.
      rewrite Hslotslen.
      auto with arith.
    }
    rewrite <- Hslotslen in H4.
    rewrite HlenS in H4.
    assert (Hln: (length (skipn idx slotsvl) > 0)%nat).
    {
      rewrite skipn_length.  
      cut (0 < length slotsvl - idx)%nat.
      auto with arith.
      rewrite <- NPeano.Nat.lt_add_lt_sub_l.
      rewrite Nat.add_0_r. auto.
      rewrite Hslotslen.
      auto.
    }
    apply length_exists in Hln.
    destruct Hln as (vh & vlt & Hlst).
    rewrite Hlst in H4.
    eapply ASlots_succ_imp in H4.

    assert (Hsimp: $ Z.of_nat (idx * typelen (Slot)) +ᵢ  $ Z.of_nat (typelen (Slot)) =
                   $ Z.of_nat (S idx * typelen (Slot))).
  {
    rewrite <- Nat.add_1_r.
    rewrite NPeano.Nat.mul_add_distr_r. 
    rewrite Nat2Z.inj_add.
    change (1 * typelen (Slot))%nat with (typelen (Slot)).
    simpl. 
    assert (Ha: Z.of_nat (idx * 20) = Int.unsigned ($ (Z.of_nat (idx * 20)))). 
    {
      rewrite int_usign_eq; auto. auto with zarith.
      apply lt_imply_le.
      clear -Hlenle.
      rewrite max_unsigned_val. 
      apply Z.lt_le_trans with (m:=255 * 20).
      mauto. mauto.
    }
    assert (Hb: 20 = Int.unsigned ($20)) by auto.
    rewrite Ha at 2. rewrite Hb at 2.
    rewrite <- Int.add_unsigned. auto.
  }
  assert(typelen Slot = 20%nat) by auto.
  rewrite Int.add_assoc in H4.
  rewrite Hsimp in H4.


  destruct H4. simpljoin1.
  simpl in H4, H8.
  simpl substmo in H9, H10.
  unfold ASlots in H9.
  destruct vh.
  sep lift 3%nat in H9.
  eapply astar_l_aemp_elim in H9.

  simpl_sat_goal.
  destruct H9. simpljoin1.
  simpl in H7, H11.
  simpl substmo in H12, H13.

  exists (firstn idx slotsvl) vlt.
  exists i4 p.
  exists x x0 m x2 x3 o.
  splits; eauto.
  exists x5. do 2 eexists.
  exists x10. do 2 eexists.
  splits; eauto.
  3:{
    exists x8. do 2 eexists. exists x11. do 2 eexists.
    splits; eauto.
    
    3:{
        rewrite <- Hslotslen.
        exists x4. do 2 eexists. exists x7. do 2 eexists.
        splits; eauto.
        instantiate(1:=x4).
        instantiate (1:=empenv). join auto.
        instantiate (1:=x7).
        instantiate(1:=emp). join auto.
        do 6 eexists. splits; eauto.
        join auto. join auto.
        split.  rewrite <- Hlst.
        rewrite Hsplit. auto.
        simpl. split; auto. unfolds. auto.
        do 6 eexists. splits; eauto.
        join auto. join auto.
        splits; eauto.
        splits. auto. 
        eapply sub_eq_succ; eauto.
        rewrite Hslotslen. lia. 
        rewrite Hslotslen. rewrite <- H6.
        rewrite Hlst.
        simpl. auto.
        splits; simpl; unfolds; auto.
        clear -Hlst.
        Lemma nth_skipn_slot: 
            forall idx slotsvl  i4 c0 vlt,
            skipn idx slotsvl = (i4, c0) :: vlt
            -> nth_slots idx slotsvl = Some (i4, c0).
        Proof.
            induction idx; destruct slotsvl; intros.
            simpl in H. tryfalse.
            simpl in H. inverts H. simpl. auto.
            simpl in H. tryfalse.
            simpl in H.  apply IHidx in H.
            simpl.  auto.
        Qed.
        
        eapply nth_skipn_slot. eauto.
        simpl. split; unfolds; auto.
     }
    join auto.
    join auto.
  }
  join auto.
  join auto.
Qed. 

Lemma  ASlots_unfold_any_idx_frm:
forall s b i n slotsvl idx P, 
  s |= ASlots (b, i) n slotsvl ** P->
  (idx < n)%nat ->
  n = Z.to_nat SLOT_NUM ->
  length slotsvl = n ->
  s |= (EX vll1 vll2 slot_type slot_cap,
  ASlots (b, i) idx vll1**
  PV (b, i +ᵢ $ Z.of_nat (idx * (typelen Slot))) @ Int32 |-> Vint32 slot_type ** 
  ACap (b, i +ᵢ $ Z.of_nat (idx * (typelen Slot)) +ᵢ (Int.repr 4)) slot_cap
  ** ASlots (b, i +ᵢ $ Z.of_nat ((S idx) * (typelen Slot))) (n - (S idx)) vll2
  ** [|slotsvl = vll1 ++ (slot_type, slot_cap):: vll2|] **
  [|length vll1 = idx /\ length vll2 = (n - (S idx))%nat|] **
  [|nth_slots idx slotsvl = Some (slot_type, slot_cap)|]) ** P.
Proof.
  intros.
  sep cancel P.
  eapply ASlots_unfold_any_idx; eauto.
Qed.

Lemma ASlots_succ_imp_alt :
  forall s a vll n b i P, 
  s |= ASlots (b,i) (S n) (a :: vll) ** P ->
  s |= ASlots (b,i) 1  (a::nil) ** ASlots (b,i +ᵢ  $ Z.of_nat  (typelen Slot)) n vll ** P.
Proof.
    intros.
    sep pauto.
    simpl ASlots in *.
    destruct a. 
    sep auto.
Qed.


Lemma ASlots_fold_strong :
forall vll1 n vll2 m b i s , 
  Z.of_nat (S n * typelen (Slot)) <= Int.max_unsigned -> 
  (* 0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned -> *)
  length vll1 = n /\ length vll2 = m ->
  s |= ASlots (b, i) n vll1 ** ASlots (b, i +ᵢ $ Z.of_nat (n * (typelen (Slot)))) m  vll2 ->
  s |= ASlots (b,i) (n + m)  (vll1 ++ vll2) .
Proof.
  induction vll1; induction n; intros.
  simpl ASlots in H1. 
  sep auto. rewrite Int.add_zero in H1.
  rewrite Nat.add_0_l. simpl. auto.
  simpl in H0. destruct H0. tryfalse.
  simpl in H0. destruct H0. tryfalse.
  eapply ASlots_succ_imp_alt in H1.
  change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)).
  rewrite Nat.add_succ_l.
  assert(s |= ASlots (b ↝ {i}) (S (n + m)) (a :: vll1 ++ vll2) ** Aemp).
  eapply ASlots_succ_alt.
  sep pauto.
  eapply IHvll1 with (i:=i +ᵢ  $ Z.of_nat (typelen Slot)); eauto.
  auto with zarith.
  rewrite Int.add_assoc.
  assert (Heq:
           $ Z.of_nat (S n * typelen Slot) = ($ Z.of_nat (typelen Slot) +ᵢ  $ Z.of_nat (n * typelen Slot))).
  { int auto. }
  rewrite <- Heq.
  auto.
  sep auto.
Qed.


Lemma ASlots_fold_strong_frm :
forall vll1 n vll2 m b i s p, 
  Z.of_nat (S n * typelen (Slot)) <= Int.max_unsigned -> 
  (* 0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned -> *)
  length vll1 = n /\ length vll2 = m ->
  s |= ASlots (b, i) n vll1 ** ASlots (b, i +ᵢ $ Z.of_nat (n * (typelen (Slot)))) m  vll2 ** p ->
  s |= ASlots (b,i) (n + m)  (vll1 ++ vll2) **p .
Proof.
  intros.
  sep pauto.
  eapply ASlots_fold_strong; eauto.
Qed.

Lemma  ASlots_fold_any_idx:
  forall s b i n slotsvl idx vll1 vll2 slot_type slot_cap, 
  (idx < n)%nat ->
  n = Z.to_nat SLOT_NUM ->
  length slotsvl = n ->
  length vll1 = idx ->
  length vll2 = (n - S idx)%nat ->
  slotsvl = vll1 ++ (slot_type, slot_cap):: vll2 ->
  s |=ASlots (b, i) idx vll1**
      PV (b, i +ᵢ $ Z.of_nat (idx * (typelen Slot))) @ Int32 |-> Vint32 slot_type ** 
      ACap (b, i +ᵢ $ Z.of_nat (idx * (typelen Slot)) +ᵢ (Int.repr 4)) slot_cap 
      ** ASlots (b, i +ᵢ $ Z.of_nat ((S idx) * (typelen Slot))) (n - (S idx)) vll2 ->
  s |= ASlots (b, i) n slotsvl.
Proof.
  intros.
  sep split in H4.
  assert(s |= ASlots (b, i) idx vll1 **
  ASlots (b, i +ᵢ$ Z.of_nat (idx * typelen Slot)) 1 ((slot_type, slot_cap)::nil)
  **  ASlots (b , (i +ᵢ  $ Z.of_nat (S idx * typelen Slot)))(n - S idx) vll2).
  unfold ASlots at 2.
  sep auto.
  eapply ASlots_fold_strong_frm in H6.
  rewrite Nat.add_1_r in H6.
  eapply ASlots_fold_strong in H6.
  assert(((vll1 ++ (slot_type, slot_cap) :: nil) ++ vll2) = vll1 ++ (slot_type, slot_cap) :: vll2).
  rewrite app_assoc_reverse.
  rewrite list_prop1. auto.
  rewrite H7 in H6.
  rewrite <- H4 in H6.
  assert(S idx + (n - S idx) = n)%nat by auto with arith.
  rewrite H8 in H6.
  auto.
  2:{
    splits.
    rewrite app_length.
    simpl.
    rewrite H2.
    rewrite Nat.add_1_r. auto.
    auto.
  }
  assert(S (S idx) <= n + 1)%nat. 
  lia.
  rewrite Nat2Z.inj_mul.
  rewrite H0 in H7. unfold SLOT_NUM in H7. simpl in H7.
  simpl typelen.
  eapply Z.le_trans with(m := (256 * 20)).
  lia. rewrite max_unsigned_val. lia.
  assert((S idx) <= n)%nat. 
  lia.
  rewrite Nat2Z.inj_mul.
  rewrite H0 in H7. unfold SLOT_NUM in H7. simpl in H7.
  simpl typelen.
  eapply Z.le_trans with(m := (255 * 20)).
  lia. rewrite max_unsigned_val. lia.
  splits; eauto.
Qed.

Lemma  ASlots_fold_any_idx_frm:
  forall s b i n slotsvl idx vll1 vll2 p slot_type slot_cap, 
  (idx < n)%nat ->
  n = Z.to_nat SLOT_NUM ->
  length slotsvl = n ->
  length vll1 = idx ->
  length vll2 = (n - S idx)%nat ->
  slotsvl = vll1 ++ (slot_type, slot_cap):: vll2 ->
  s |= ASlots (b, i) idx vll1**
      PV (b, i +ᵢ $ Z.of_nat (idx * (typelen Slot))) @ Int32 |-> Vint32 slot_type ** 
      ACap (b, i +ᵢ $ Z.of_nat (idx * (typelen Slot)) +ᵢ (Int.repr 4)) slot_cap
      
      ** ASlots (b, i +ᵢ $ Z.of_nat ((S idx) * (typelen Slot))) (n - (S idx)) vll2
      ** p->
  s |= ASlots (b, i) n slotsvl ** p.
Proof.
  intros.
  sep cancel p.
  eapply ASlots_fold_any_idx; eauto.
Qed.

Lemma ACSpaceAarrayTptr_succ_imp_alt :
  forall s a ptrvl c vll n P cspacels, 
  s |= ACSpaceAarrayTptr (S n) (a::ptrvl) (c :: vll) cspacels ** P ->
  s |= ACSpaceAarrayTptr 1 (a::nil) (c::nil) cspacels  ** ACSpaceAarrayTptr n ptrvl vll cspacels ** P.
Proof.
    intros.
    sep pauto.
    simpl ACSpaceAarrayTptr in *.
    destruct a. 
    simpl in H. tryfalse.
    sep auto. 
    simpl in H. tryfalse.
    sep auto.
Qed.


Lemma ACSpaceAarrayTptr_fold_strong :
forall vll1 n vll2 m  s ptrvl1 ptrvl2 cspacels, 
  Z.of_nat (S n * typelen (CSPACE ∗)) <= Int.max_unsigned -> 
  (* 0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned -> *)
  length vll1 = n /\ length vll2 = m ->
  length ptrvl1 = n /\ length ptrvl2 = m ->
  s |= ACSpaceAarrayTptr n  ptrvl1 vll1 cspacels** ACSpaceAarrayTptr m ptrvl2 vll2 cspacels->
  s |= ACSpaceAarrayTptr (n + m) (ptrvl1 ++ ptrvl2) (vll1 ++ vll2) cspacels.
Proof.
  induction vll1; induction n; induction ptrvl1;intros.
  simpl ACSpaceAarrayTptr in H2. 
  sep auto. 
  rewrite Nat.add_0_l. simpl. auto.
  simpl in H1. destruct H1. tryfalse.
  simpl in H1. destruct H1. tryfalse.
  simpl in H0. destruct H0. tryfalse.
  simpl in H0. destruct H0. tryfalse.
  simpl in H0. destruct H0. tryfalse.
  simpl in H1. destruct H1. tryfalse.
  eapply ACSpaceAarrayTptr_succ_imp_alt in H2.
  change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)).
  change (((a0 :: ptrvl1) ++ ptrvl2)) with (a0 :: (ptrvl1 ++ ptrvl2)).
  rewrite Nat.add_succ_l.
  assert(s |= ACSpaceAarrayTptr  (S (n + m))(a0 :: ptrvl1 ++ ptrvl2) (a :: vll1 ++ vll2) cspacels** Aemp).
  eapply ACSpaceAarrayTptr_succ_alt.
  sep pauto.
  eapply IHvll1 ; eauto.
  auto with zarith.
  sep auto.
Qed.

Lemma ACSpaceAarrayTptr_fold_strong_frm :
forall vll1 n vll2 m cspacels s ptrvl1 ptrvl2 P, 
  Z.of_nat (S n * typelen (CSPACE ∗)) <= Int.max_unsigned -> 
  (* 0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned -> *)
  length vll1 = n /\ length vll2 = m ->
  length ptrvl1 = n /\ length ptrvl2 = m ->
  s |= ACSpaceAarrayTptr  n  ptrvl1 vll1 cspacels ** ACSpaceAarrayTptr  m ptrvl2 vll2 cspacels ** P ->
  s |= ACSpaceAarrayTptr (n + m) (ptrvl1 ++ ptrvl2) (vll1 ++ vll2) cspacels** P.
Proof.
  sep pauto.
  eapply ACSpaceAarrayTptr_fold_strong; eauto.
Qed.
Lemma Aarray'_succ_alt :
  forall s n  p vl b i t, 
  s |= Aarray' (b, i)  1%nat t (p::nil) ** Aarray' (b, i+ᵢInt.repr(Z.of_nat(typelen t)))  n t vl ->
  s |= Aarray' (b, i) (S n) t (p :: vl).
Proof.
    intros.
    sep pauto.
    simpl Aarray' in *.
    sep normal.
    sep auto.
Qed.


Lemma Aarray'_fold_strong:
  forall  vll1 vll2  t b i n m s,
  Z.of_nat (n * typelen (t)) <= Int.max_unsigned -> 
  Z.of_nat(typelen t) <= Int.max_unsigned ->
  length vll1 = n /\ length vll2 = m ->
  s |= Aarray' (b, i) n t vll1
  ** Aarray' (b, i +ᵢ $ Z.of_nat (n * (typelen t))%nat) m t vll2 ->
  s |= Aarray' (b, i) (n + m) t (vll1 ++ vll2).
Proof.

  induction vll1; induction n; intros.
  simpl Aarray' in *. 
  rewrite Int.add_zero in H2. sep auto.
  simpl in H1. destruct H1. tryfalse.
  simpl in H1. destruct H1. tryfalse.
  eapply Aarray'_succ_imp_frm in H2.
  change ((a :: vll1) ++ vll2) with (a::(vll1++vll2)).
  rewrite Nat.add_succ_l.
  eapply Aarray'_succ_alt.
  sep pauto. 
  eapply IHvll1; eauto.
  lia. 
  sep auto.
  assert($ Z.of_nat (S n * typelen t) =  $ Z.of_nat (typelen t)+ᵢ
  $ Z.of_nat (n * typelen t)). int auto.
  rewrite Int.add_assoc.
  rewrite <- H3. sep auto.
Qed.
  
Lemma Aarray'_fold_strong_frm:
  forall  vll1 vll2  t b i n m s P,
  Z.of_nat (n * typelen (t)) <= Int.max_unsigned -> 
  Z.of_nat(typelen t) <= Int.max_unsigned ->
  length vll1 = n /\ length vll2 = m ->
  s |= Aarray' (b, i) n t vll1
  ** Aarray' (b, i +ᵢ $ Z.of_nat (n * (typelen t))%nat) m t vll2 ** P->
  s |= Aarray' (b, i) (n + m) t (vll1 ++ vll2) ** P.
Proof.
  intros.
  sep pauto.
  eapply Aarray'_fold_strong; eauto.
Qed.

Lemma Aarray'_fold_any_idx: 
  forall s b i n idx t vll1 vll2 lv a,
  (idx < n)%nat ->
  lv = vll1 ++ a::vll2 ->
  Z.of_nat (n * typelen (t)) <= Int.max_unsigned -> 
  Z.of_nat(typelen (t)) <= Int.max_unsigned ->
  length vll1 = idx /\ length vll2 = (n - S idx)%nat ->
  s |= Aarray' (b, i) idx (t) vll1 **
  PV (b, i+ᵢ $ Z.of_nat (idx * (typelen t))) @ (t) |-> a **
  Aarray' (b, i+ᵢ $ Z.of_nat ((S idx) * (typelen t))) (n - (S idx))%nat (t) vll2 ->
  s |= Aarray' (b, i) n t lv .
Proof.
    intros.
    assert(s |= Aarray' (b, i) idx (t) vll1 **
    Aarray'(b, i+ᵢ $ Z.of_nat (( idx) * (typelen t))) 1%nat t (a::nil)**
    Aarray' (b, i+ᵢ $ Z.of_nat ((S idx) * (typelen t))) (n - (S idx))%nat (t) vll2).
    unfold Aarray' at 2. sep auto.
    eapply Aarray'_fold_strong_frm in H5; eauto.
    2:{
      clear -H H1.
      apply Z.le_trans with (m:=Z.of_nat( n * typelen t)).
      2: auto.
      rewrite Nat2Z.inj_mul. 
      rewrite Nat2Z.inj_mul. 
      eapply Zmult_le_compat_r.
      lia. lia. 
    }
    2:{
      destruct H3. split. auto.
      simpl. auto.
    }
    rewrite Nat.add_1_r in H5.
    eapply Aarray'_fold_strong in H5; eauto.
    rewrite app_assoc_reverse in H5.
    rewrite list_prop1 in H5. 
    rewrite <- H0 in H5. 
    assert(S idx + (n - S idx) = n)%nat. lia. 
    rewrite H6 in H5. sep auto.
    clear -H H1.
    apply Z.le_trans with (m:=Z.of_nat( n * typelen t)).
    2: auto.
    rewrite Nat2Z.inj_mul. 
    rewrite Nat2Z.inj_mul. 
    eapply Zmult_le_compat_r.
    lia. lia. 
    destruct H3.  split. rewrite app_length.
    simpl. rewrite H3. lia. 
    auto.
Qed.


Lemma Aarray'_fold_any_idx_frm: 
  forall s b i n idx t vll1 vll2 lv a P,
  (idx < n)%nat ->
  lv = vll1 ++ a::vll2 ->
  Z.of_nat (n * typelen (t)) <= Int.max_unsigned -> 
  Z.of_nat(typelen (t)) <= Int.max_unsigned ->
  length vll1 = idx /\ length vll2 = (n - S idx)%nat ->
  s |= Aarray' (b, i) idx (t) vll1 **
  PV (b, i+ᵢ $ Z.of_nat (idx * (typelen t))) @ (t) |-> a **
  Aarray' (b, i+ᵢ $ Z.of_nat ((S idx) * (typelen t))) (n - (S idx))%nat (t) vll2 **P ->
  s |= Aarray' (b, i) n t lv ** P.
Proof.
  intros.
  sep pauto.
  eapply Aarray'_fold_any_idx; eauto.
Qed.


Lemma  ACSpaceAarray_fold_any_idx:
  forall s cspacels n cspacevl idx ptrvl1 ptrvl2 ptrvl vll1 vll2 p v, 
  (n < 1000)%nat ->  (*设置一个很大的数*)
  (idx < n)%nat ->
  length cspacevl = n ->
  length vll1 = idx ->
  length vll2 = (n - S idx)%nat ->
  length ptrvl1 = idx ->
  length ptrvl2 = (n - S idx)%nat ->
  cspacevl = vll1 ++ v:: vll2 ->
  ptrvl = ptrvl1 ++ (Vptr p) :: ptrvl2 ->
  s |= ACSpaceAarrayTptr idx ptrvl1 vll1 cspacels**
    ACSpace p v cspacels**
    ACSpaceAarrayTptr (n - (S idx))%nat  ptrvl2 vll2 cspacels ->
  s |= ACSpaceAarrayTptr n%nat ptrvl cspacevl cspacels.
Proof.
  introv Hnlt.
  intros.
  assert(s |= ACSpaceAarrayTptr  idx ptrvl1 vll1 cspacels**
  ACSpaceAarrayTptr 1%nat (Vptr p :: nil) (v::nil) cspacels ** 
  ACSpaceAarrayTptr (n - S idx) ptrvl2 vll2 cspacels).
  unfold ACSpaceAarrayTptr at 2. sep auto.
  eapply ACSpaceAarrayTptr_fold_strong_frm in H8; eauto.
  rewrite Nat.add_1_r in H8.
  eapply ACSpaceAarrayTptr_fold_strong in H8; eauto.
  assert(((ptrvl1 ++ Vptr p :: nil) ++ ptrvl2) = ptrvl1 ++ Vptr p :: ptrvl2).
  rewrite app_assoc_reverse.
  rewrite list_prop1. auto.

  rewrite H9 in H8.
  rewrite <- H6 in H8.
  assert((vll1 ++ v :: nil) ++ vll2 = vll1 ++ v :: vll2).
  rewrite app_assoc_reverse.
  rewrite list_prop1. auto.
  rewrite H10 in H8.
  rewrite <- H5 in H8.
  assert(S idx + (n - S idx) = n)%nat.
  lia.
  rewrite H11 in H8.
  auto.
  2:{
    splits; eauto.
    rewrite app_length.
    simpl. rewrite H1. rewrite Nat.add_1_r. auto.
  }
  2:{
    splits; eauto.
    rewrite app_length.
    simpl. rewrite H3. rewrite Nat.add_1_r. auto.
  }
  assert(S(S idx) <= n + 1)%nat by lia.
  rewrite Nat2Z.inj_mul.
  simpl typelen.
  eapply Z.le_trans with(m := (1001 * 4)).
  lia. rewrite max_unsigned_val. lia.
  assert((S idx) <= n )%nat by lia.
  rewrite Nat2Z.inj_mul.
  simpl typelen.
  eapply Z.le_trans with(m := (1001 * 4)).
  lia. rewrite max_unsigned_val. lia.
Qed.


Lemma  ACSpaceAarray_fold_any_idx_frm:
  forall s cspacels n cspacevl idx ptrvl1 ptrvl2 ptrvl vll1 vll2 p v P, 
  (n < 1000)%nat ->  (*设置一个很大的数*)
  (idx < n)%nat ->
  length cspacevl = n ->
  length vll1 = idx ->
  length vll2 = (n - S idx)%nat ->
  length ptrvl1 = idx ->
  length ptrvl2 = (n - S idx)%nat ->
  cspacevl = vll1 ++ v:: vll2 ->
  ptrvl = ptrvl1 ++ (Vptr p) :: ptrvl2 ->
  s |= ACSpaceAarrayTptr idx ptrvl1 vll1 cspacels**
    ACSpace p v cspacels**
    ACSpaceAarrayTptr (n - (S idx))%nat  ptrvl2 vll2 cspacels ** P->
  s |= ACSpaceAarrayTptr n%nat ptrvl cspacevl cspacels ** P.
Proof.
  sep pauto.
  eapply ACSpaceAarray_fold_any_idx; eauto.
Qed.

Lemma fold_Cap:
    forall s b i p x y z a,
    s |= PV (b, i) @ Tint32 |-> Vint32 x**
         PV (b, i +ᵢ  $ Z.of_nat 4) @ Tint32 |-> Vint32 y ** 
         PV (b, i +ᵢ  $ Z.of_nat 8) @ Tint32 |-> Vint32 z **
         PV (b, i +ᵢ  $ Z.of_nat 12) @ Tptr Tvoid |-> a  ** 
          p ->
    isptr a ->
     s |= ACap (b, i)(x, (y ,z, a)) ** p.
Proof.
  intros.
  unfold ACap.
  sep auto.
Qed.





Lemma S_add_sub_S:
  forall a b,
    (S b <= a)%nat ->
    S (a - S b) = (a - b)%nat. 
  intros.
  eapply minus_Sn_m in H.
  rewrite H.
  auto with arith.
Qed.

Lemma fold_Acnode:
  forall s p b i guide_num slot_num slots,
  length slots =  (Z.to_nat SLOT_NUM) ->
  s |= PV (b, i)@ Tint32 |-> Vint32 guide_num **
  PV (b, i +ᵢ $ 4)@ Tint32 |-> Vint32 slot_num **
  ASlots (b, i +ᵢ $ 8) (Z.to_nat SLOT_NUM) slots ** p 
  -> s |= Acnode (b, i)(guide_num, slot_num, slots) ** p.
Proof.
  intros.
  unfold Acnode.
  sep auto.
Qed.

Lemma fold_ACSpace: 
  forall s c i l v idx p b i2 cspacels,
  Int.unsigned i <= 64 /\ Int.unsigned idx < OS_LOWEST_PRIO-> 
  ptrlv_in_cspace_ls l cspacels ->
  array_type_vallist_match (Tcom_ptr cspace) l->
  children_not_null l (Z.to_nat (Int.unsigned i)) ->
  s |= Acnode (b, i2) c ** 
  PV (b ,i2 +ᵢ  $ Z.of_nat (typelen Cte)) @
    long |-> Vint32 i **
    Aarray
      (b,(i2 +ᵢ  $ Z.of_nat (typelen Cte))
          +ᵢ  $ 4) (Tarray (Tcom_ptr cspace) (Z.to_nat MaxChildNum)) l **
    PV (b, ((i2 +ᵢ  $ Z.of_nat (typelen Cte))
           +ᵢ  $ 4) +ᵢ
          Int.mul ($ MaxChildNum)
            ($ Z.of_nat (typelen (Tcom_ptr cspace)))) @
    CSPACE ∗ |-> v ** 
    PV (b, ((i2 +ᵢ  $ Z.of_nat (typelen Cte))
    +ᵢ  $ 4) +ᵢ
   Int.mul ($ MaxChildNum)
     ($ Z.of_nat (typelen (Tcom_ptr cspace))) +ᵢ Int.repr (Z.of_nat (typelen Tint32))) @ Tint32|-> Vint32 idx ** p 
    -> s |= ACSpace (b, i2) (c, i, l, v, idx) cspacels** p.
Proof.
  intros.
  unfold ACSpace.
  sep auto.
Qed.

Lemma fold_AOSCSpacePrioTbl:
  forall s b i ptrvl vl cspacels idx p,
  length ptrvl = 64%nat ->
  length vl = 64%nat ->
  array_type_vallist_match CSPACE ∗ ptrvl ->
  nth_val idx ptrvl = Some (Vptr p) ->
  (idx < 64)%nat ->
  s |= G&OSCSpacePrioTbl @ Tarray CSPACE ∗ 64 ==(b, i)
  ** ACSpaceAarrayTptr  64%nat ptrvl vl cspacels
  ** PV (b, i +ᵢ $ Z.of_nat (idx * (typelen (Tptr CSPACE)))) @ (Tptr CSPACE) |-> Vptr p **
  Aarray_rm (b, i) 64%nat (Tptr CSPACE) ptrvl idx
  -> s |= AOSCSpacePrioTbl (b, i) ptrvl vl cspacels.
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







Definition get_capability prio class vl :=
  match nth_cspace prio vl with
  | Some (cnode, _, _, _, _) =>
    match cnode with 
    |(_, _, slotvl) =>
      match nth_slots class slotvl with 
      |Some (a, b) => Some b 
      |None => None 
      end 
    end 
  | None => None 
  end.

Fixpoint update_nth_list (t: Type) (n : nat) (vl : list t) (v : t){struct vl} :=
  match vl with
    | nil => nil
    | v'::vl' => match n with
                  | 0%nat => v::vl'
                  | S n' => v'::(update_nth_list t n' vl' v)
                end
  end.
  
Definition update_nth_cspace_slots_cap prio class vl v:=
  match nth_cspace prio vl with
  | Some (cnode, c, d, e, idx) =>
    match cnode with 
    |(f, g, slotvl) =>
      match nth_slots class slotvl with 
      |Some (a, b) => 
      (update_nth_list cspace_val_type prio vl
      ((f, g, (update_nth_list slot_val_type class slotvl (a, v))), c, d, e, idx))
      |None => vl
      end 
    end 
  | None => vl
  end.
  (*a, f, g等一些变量表示的就是update之后的list相比于原来的list不变的部分*)
Definition update_nth_cspace_slots_type prio class vl v:=
  match nth_cspace prio vl with
  | Some (cnode, c, d, e, idx) =>
    match cnode with 
    |(f, g, slotvl) =>
      match nth_slots class slotvl with 
      |Some (a, b) => 
      (update_nth_list cspace_val_type prio vl
      ((f, g, (update_nth_list slot_val_type class slotvl (v, b))), c, d, e, idx))
      |None => vl
      end 
    end 
  | None => vl
  end.

Definition update_nth_cspace_slots prio class vl v:=
  match nth_cspace prio vl with
  | Some (cnode, c, d, e, idx) =>
    match cnode with 
    |(f, g, slotvl) =>
      match nth_slots class slotvl with 
      |Some (a, b) => 
      (update_nth_list cspace_val_type prio vl
      ((f, g, (update_nth_list slot_val_type class slotvl v)), c, d, e, idx))
      |None => vl
      end 
    end 
  | None => vl
  end.
Lemma  ASlots_unfold_any_idx_strong:
forall s b i n slotsvl idx, 
s |= ASlots (b, i) n slotsvl ->
(idx < n)%nat ->
(n < Z.to_nat SLOT_NUM)%nat ->
length slotsvl = n ->
s |= EX vll1 vll2 slot_type slot_cap,
    ASlots (b, i) idx vll1**
    PV (b, i +ᵢ $ Z.of_nat (idx * (typelen Slot))) @ Int32 |-> Vint32 slot_type ** 
    ACap (b, i +ᵢ $ Z.of_nat (idx * (typelen Slot)) +ᵢ (Int.repr 4)) slot_cap
    ** ASlots (b, i +ᵢ $ Z.of_nat ((S idx) * (typelen Slot))) (n - (S idx)) vll2
    ** [|slotsvl = vll1 ++ (slot_type, slot_cap):: vll2|] **
    [|length vll1 = idx /\ length vll2 = (n - (S idx))%nat|] **
    [|nth_slots idx slotsvl = Some (slot_type, slot_cap)|].
Proof.
    introv Hsat.
    introv Hlenle.
    introv Hn.
    introv Hslotslen.
    assert (Hlen: (n = idx + (n - idx))%nat) by auto with arith.
    lets Hsplit: firstn_skipn idx slotsvl.
    rewrite <- Hsplit in Hsat.
    rewrite Hlen in Hsat.
    lets Harrs0: ASlots_split_strong Hsat.
    assert(HSidx: (S idx <= n)%nat) by auto with arith.
    assert(Harith: (Z.of_nat (S idx * typelen Slot) <=
    Int.max_unsigned)).
    {
        simpl typelen.
        apply Z.le_trans with (m:=Z.of_nat (255 * typelen Slot)).
        apply inj_le. 
        simpl typelen. apply NPeano.Nat.mul_le_mono_r; auto.
        unfold SLOT_NUM in Hn. lia.
        simpl typelen.
        rewrite max_unsigned_val.
        lia. 
    }
    lets Harrs00: Harrs0 Harith.
    clear Harrs0.
    assert(Hlens: length (firstn idx slotsvl) = idx /\
    length (skipn idx slotsvl) = (n - idx)%nat).
    {
        splits.
        apply firstn_length_le. auto with arith.
        rewrite Hslotslen. auto with arith.
        rewrite <- Hslotslen.
        apply skipn_length.
    }
    lets Harrs: Harrs00 Hlens.
    clear Harrs00.
    destruct_s s. 
    destruct Harrs.
    simpljoin1.
    simpl substmo in H3, H4.
    simpl in H0, H2.
    assert (HlenS: (length slotsvl - idx = S (length slotsvl - (S idx)))%nat).
    {
      rewrite NPeano.Nat.sub_succ_r.
      rewrite Nat.lt_succ_pred with (z:=0%nat); auto.
      rewrite <- Nat.lt_add_lt_sub_r. simpl. auto.
    }
    rewrite HlenS in H4.
    assert (Hln: (length (skipn idx slotsvl) > 0)%nat).
    {
      rewrite skipn_length.  
      cut (0 < length slotsvl - idx)%nat.
      auto with arith.
      rewrite <- NPeano.Nat.lt_add_lt_sub_l.
      rewrite Nat.add_0_r. auto.
    }
    apply length_exists in Hln.
    destruct Hln as (vh & vlt & Hlst).
    rewrite Hlst in H4.
    eapply ASlots_succ_imp in H4.

    assert (Hsimp: $ Z.of_nat (idx * typelen (Slot)) +ᵢ  $ Z.of_nat (typelen (Slot)) =
                    $ Z.of_nat (S idx * typelen (Slot))).
  {
    rewrite <- Nat.add_1_r.
    rewrite NPeano.Nat.mul_add_distr_r. 
    rewrite Nat2Z.inj_add.
    change (1 * typelen (Slot))%nat with (typelen (Slot)).
    simpl. 
    assert (Ha: Z.of_nat (idx * 20) = Int.unsigned ($ (Z.of_nat (idx * 20)))). 
    {
      rewrite int_usign_eq; auto. auto with zarith.
      apply lt_imply_le.
      clear -Hlenle Hn.
      unfold SLOT_NUM in *.
      rewrite max_unsigned_val. 
      apply Z.lt_le_trans with (m:=255 * 20).
      mauto. mauto.
    }
    assert (Hb: 20 = Int.unsigned ($20)) by auto.
    rewrite Ha at 2. rewrite Hb at 2.
    rewrite <- Int.add_unsigned. auto.
  }
  assert(typelen Slot = 20%nat) by auto.
  rewrite Int.add_assoc in H4.
  rewrite Hsimp in H4.


  destruct H4. simpljoin1.
  simpl in H4, H8.
  simpl substmo in H9, H10.
  unfold ASlots in H9.
  destruct vh.
  sep lift 3%nat in H9.
  eapply astar_l_aemp_elim in H9.

  simpl_sat_goal.
  destruct H9. simpljoin1.
  simpl in H7, H11.
  simpl substmo in H12, H13.

  exists (firstn idx slotsvl) vlt.
  exists i4 p.
  exists x x0 m x2 x3 o.
  splits; eauto.
  exists x5. do 2 eexists.
  exists x10. do 2 eexists.
  splits; eauto.
  3:{
    exists x8. do 2 eexists. exists x11. do 2 eexists.
    splits; eauto.
    3:{
        exists x4. do 2 eexists. exists x7. do 2 eexists.
        splits; eauto.
        instantiate(1:=x4).
        instantiate (1:=empenv). join auto.
        instantiate (1:=x7).
        instantiate(1:=emp). join auto.
        do 6 eexists. splits; eauto.
        join auto. join auto. 
        split.  rewrite <- Hlst.
        rewrite Hsplit. auto.
        simpl. split; auto. unfolds. auto.
        do 6 eexists. splits; eauto.
        join auto. join auto.
        splits; eauto.
        splits. auto. 
        eapply sub_eq_succ; eauto.
        rewrite <- H6.
        rewrite Hlst.
        simpl. auto.
        splits; simpl; unfolds; auto.
        clear -Hlst.
        
        eapply nth_skipn_slot. eauto.
        simpl. split; unfolds; auto.
      }
    join auto.
    join auto.
  }
  join auto.
  join auto.
Qed. 


Lemma  ASlots_unfold_any_idx_strong_frm:
forall s b i n slotsvl idx p, 
s |= ASlots (b, i) n slotsvl ** p ->
(idx < n)%nat ->
(n < Z.to_nat SLOT_NUM)%nat ->
length slotsvl = n ->
s |= (EX vll1 vll2 slot_type slot_cap,
    ASlots (b, i) idx vll1**
    PV (b, i +ᵢ $ Z.of_nat (idx * (typelen Slot))) @ Int32 |-> Vint32 slot_type ** 
    ACap (b, i +ᵢ $ Z.of_nat (idx * (typelen Slot)) +ᵢ (Int.repr 4)) slot_cap
    ** ASlots (b, i +ᵢ $ Z.of_nat ((S idx) * (typelen Slot))) (n - (S idx)) vll2
    ** [|slotsvl = vll1 ++ (slot_type, slot_cap):: vll2|] **
    [|length vll1 = idx /\ length vll2 = (n - (S idx))%nat|] **
    [|nth_slots idx slotsvl = Some (slot_type, slot_cap)|]) ** p.
Proof.
  intros.
  sep cancel p.
  eapply ASlots_unfold_any_idx_strong; eauto.
Qed.


Lemma  ASlots_fold_any_idx_strong:
  forall s b i n slotsvl idx vll1 vll2 slot_type slot_cap, 
  (idx < n)%nat ->
  (n <= Z.to_nat SLOT_NUM)%nat ->
  length slotsvl = n ->
  length vll1 = idx ->
  length vll2 = (n - S idx)%nat ->
  slotsvl = vll1 ++ (slot_type, slot_cap):: vll2 ->
  s |=ASlots (b, i) idx vll1**
      PV (b, i +ᵢ $ Z.of_nat (idx * (typelen Slot))) @ Int32 |-> Vint32 slot_type ** 
      ACap (b, i +ᵢ $ Z.of_nat (idx * (typelen Slot)) +ᵢ (Int.repr 4)) slot_cap
      ** ASlots (b, i +ᵢ $ Z.of_nat ((S idx) * (typelen Slot))) (n - (S idx)) vll2 ->
  s |= ASlots (b, i) n slotsvl.
Proof.
  intros.
  sep split in H4.
  assert(s |= ASlots (b, i) idx vll1 **
  ASlots (b, i +ᵢ$ Z.of_nat (idx * typelen Slot)) 1 ((slot_type, slot_cap)::nil)
  **  ASlots (b , (i +ᵢ  $ Z.of_nat (S idx * typelen Slot)))(n - S idx) vll2).
  unfold ASlots at 2.
  sep auto.
  eapply ASlots_fold_strong_frm in H6.
  rewrite Nat.add_1_r in H6.
  eapply ASlots_fold_strong in H6.
  assert(((vll1 ++ (slot_type, slot_cap) :: nil) ++ vll2) = vll1 ++ (slot_type, slot_cap) :: vll2).
  rewrite app_assoc_reverse.
  rewrite list_prop1. auto.
  rewrite H7 in H6.
  rewrite <- H4 in H6.
  assert(S idx + (n - S idx) = n)%nat by auto with arith.
  rewrite H8 in H6.
  auto.
  2:{
    splits.
    rewrite app_length.
    simpl.
    rewrite H2.
    rewrite Nat.add_1_r. auto.
    auto.
  }
  assert(S (S idx) <= n + 1)%nat. 
  lia.
  rewrite Nat2Z.inj_mul.
  clear -H0 H7. unfold SLOT_NUM in H0.
  simpl typelen.
  eapply Z.le_trans with(m := (256 * 20)).
  lia. rewrite max_unsigned_val. lia.
  assert((S idx) <= n)%nat. 
  lia.
  rewrite Nat2Z.inj_mul.
  clear -H0 H7. unfold SLOT_NUM in H0. simpl in H7.
  simpl typelen.
  eapply Z.le_trans with(m := (255 * 20)).
  lia. rewrite max_unsigned_val. lia.
  splits; eauto.
Qed.

Lemma  ASlots_fold_any_idx_strong_frm:
  forall s b i n slotsvl idx vll1 vll2 slot_type slot_cap p, 
  (idx < n)%nat ->
  (n <= Z.to_nat SLOT_NUM)%nat ->
  length slotsvl = n ->
  length vll1 = idx ->
  length vll2 = (n - S idx)%nat ->
  slotsvl = vll1 ++ (slot_type, slot_cap):: vll2 ->
  s |=ASlots (b, i) idx vll1**
      PV (b, i +ᵢ $ Z.of_nat (idx * (typelen Slot))) @ Int32 |-> Vint32 slot_type ** 
      ACap (b, i +ᵢ $ Z.of_nat (idx * (typelen Slot)) +ᵢ (Int.repr 4)) slot_cap
      ** ASlots (b, i +ᵢ $ Z.of_nat ((S idx) * (typelen Slot))) (n - (S idx)) vll2 ** p ->
  s |= ASlots (b, i) n slotsvl ** p.
Proof.
  intros.
  sep cancel p.
  eapply ASlots_fold_any_idx_strong; eauto.
Qed.





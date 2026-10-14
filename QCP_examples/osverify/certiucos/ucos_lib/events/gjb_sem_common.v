Require Import ucos_include.
Require Import os_ucos_h.
Require Import symbolic_lemmas.
Require Import evt_spec_defs.
Require Import seplog_trm_tacs.
Require Import Aarray_new_common.
Require Import gjb_common.

Open Scope code_scope.
Open Scope int_scope.
Open Scope Z_scope.

(* Definition Seminfo_full_P semvl :=
forall i vl1, (0 <= i /\ i < Z.of_nat (length semvl)) ->
                        nth_vallist (nat_of_Z i) semvl = Some vl1 ->
                        ~(V_OSSINFOPevent vl1 = Some Vnull).

Definition nth_Seminfo_free_P i semvl :=
exists vl1, 0 <= i /\ i < Z.of_nat (length semvl) /\ 
                      nth_vallist (nat_of_Z i) semvl = Some vl1 /\
                      V_OSSINFOPevent vl1 = Some Vnull. *)

(* Lemma aseminfo_len: 
  forall s vl, s |= ASeminfo vl -> length vl = ∘ (OS_USER_MAX_EVENTS / 3).
Proof.  
  introv Hsat.
  destruct Hsat.
  simpl_sat H. simpljoin1.
  auto.
Qed.  *)

(* Lemma ASeminfo_unfold_any_idx: 
  forall s semvl idx,
    s |= ASeminfo semvl ->
    (idx < length semvl)%nat ->
    s |= EX vll1 vll2 b i vl ,
        GV Sem_info @ sem_info_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray sem_info_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen sem_info_t))) sem_info_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen sem_info_t))))
          (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match sem_info_t semvl |] **
          [| length semvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
          [| semvl = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 |].  
Proof. 
  introv Hsat.
  assert (Hlengt: Z.of_nat (length semvl * typelen sem_info_t) <= Int.max_unsigned). 
  { erewrite aseminfo_len; eauto.  simpl. mauto. }
  introv Hlenle. 
  unfold ASeminfo in Hsat.
  simpl_sat Hsat. 
  simpljoin1.
  rewrite <- H11 in *.
  assert (Hlen: (length semvl = idx + (length semvl - idx))%nat) 
    by auto with arith.
  lets Hsplit: (firstn_skipn idx semvl). 
  rewrite <- Hsplit in H8 at 2.
  rewrite Hlen in H8. 
  destruct x.
  lets Harrs0: Aarray_new_split_strong H8.
  assert (HSidx: (S idx <= length semvl)%nat) by auto with arith.
  assert (Harith: Z.of_nat (S idx * typelen sem_info_t) <= Int.max_unsigned). 
  {
    apply Z.le_trans with (m:=Z.of_nat (length semvl * typelen sem_info_t));
      auto.
    apply inj_le. 
    apply NPeano.Nat.mul_le_mono_r; auto.
  }
  lets Harrs00: Harrs0 Harith.
  clear Harrs0.
  assert (Hlens: length (firstn idx semvl) = idx /\ length (skipn idx semvl) = (length semvl - idx)%nat).
  {
    split. 
    apply firstn_length_le. auto with arith.
    apply skipn_length.
  }
  lets Harrs: Harrs00 Hlens.
  clear Harrs00.
  destruct Harrs.
  simpljoin1.
  destruct s as [[[[[[]]]]]].
  change_smo H12.
  change_smo H13.
  change_smo H3.

  assert (HlenS: (length semvl - idx = S (length semvl - (S idx)))%nat).
  {
    rewrite NPeano.Nat.sub_succ_r.
    rewrite Nat.lt_succ_pred with (z:=0%nat); auto.
    rewrite <- Nat.lt_add_lt_sub_r. simpl. auto.
  }
  rewrite HlenS in H13.
  assert (Hln: (length (skipn idx semvl) > 0)%nat).
  {
    rewrite skipn_length.  
    cut (0 < length semvl - idx)%nat.
    auto with arith.
    rewrite <- NPeano.Nat.lt_add_lt_sub_l.
    rewrite Nat.add_0_r. auto.
  }
  apply length_exists in Hln.
  destruct Hln as (vh & vlt & Hlst). rewrite Hlst in H13.
  apply Aarray_new'_succ_imp in H13.
  assert (Hsimp: $ Z.of_nat (idx * typelen sem_info_t) +ᵢ  $ Z.of_nat (typelen sem_info_t) =
                   $ Z.of_nat (S idx * typelen sem_info_t)).
  {
    rewrite <- Nat.add_1_r.
    rewrite NPeano.Nat.mul_add_distr_r. 
    rewrite Nat2Z.inj_add.
    change (1 * typelen sem_info_t)%nat with (typelen sem_info_t).
    simpl. 
    assert (Ha: Z.of_nat (idx * 32) = Int.unsigned ($ (Z.of_nat (idx * 32)))). 
    {
      rewrite int_usign_eq; auto. auto with zarith.
      rewrite H11 in Hlen. unfold_usr_max_evts_in H11.
      simpl in H11.
      rewrite pos_to_nat_6 in H11. 
      rewrite H11 in Hlengt.
      apply lt_imply_le.
      apply Z.lt_le_trans with (m:=192). auto. 
      mauto. mauto.
    }
    assert (Hb: 32 = Int.unsigned ($32)) by auto.
    rewrite Ha at 2. rewrite Hb at 2.
    rewrite <- Int.add_unsigned. auto.
  }
  rewrite Int.add_assoc in H13. rewrite Hsimp in H13.
  assert (Hc: (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) = length semvl - S idx)%nat).
  {
    rewrite H11.
    rewrite sub_Z_nat; auto. 
    rewrite <- H11. 
    auto.
  }
  rewrite Hc. 
  destruct H13.
  simpljoin1.
  change_smo H17.
  change_smo H18.
  unfold Aarray_new' in H17. unfold sem_info_t in H17. fold sem_info_t in H17.
  apply step_prop.StarEmpER in H17.

  simpl_sat_goal.

  exists (firstn idx semvl). exists vlt. exists b. exists i.
  exists vh. exists x0. exists x1. exists m. exists x3. eexists. exists o.
  splits; eauto.
  
  simpl in H10. simpl in H5. 
  destruct H10 as (Hx7emp & Hx10emp).
  subst x7. unfold emposabst in Hx10emp. subst x10. 
  assert (x6 = x1). { apply map_join_emp' in H5. auto. }
  subst x6.
  simpl in H7. simpl in H2.
  assert (x9 = x4). { apply map_join_emp' in H7. auto. }
  subst x9.
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
  unfold_usr_max_evts. simpl. 
  asserts_rewrite (20/3 = 6). { auto. }
  auto.
  simpl. split; auto. unfolds. auto.

Qed.  *)

(* Lemma ASeminfo_unfold_any_idx_frm: 
  forall s semvl idx P,
    s |= ASeminfo semvl ** P ->
    (idx < length semvl)%nat ->
    s |= (EX vll1 vll2 b i vl ,
        GV Sem_info @ sem_info_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray sem_info_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen sem_info_t))) sem_info_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen sem_info_t))))
            (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match sem_info_t semvl |] **
          [| length semvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
          [| semvl = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 |]) ** P.   
Proof. 
  introv Hsat Hlenle. 
  sep cancel 2%nat 2%nat.
  eapply ASeminfo_unfold_any_idx; eauto.
Qed. *)

(* Lemma ASeminfo_select_sn_strong :
  forall vll1 n vll2 b i s vl P, 
    Z.of_nat(S n) <= OS_USER_MAX_EVENTS / 3 ->
    (* 0 <= Int.unsigned i + (OS_USER_MAX_EVENTS / 3) * (Z.of_nat (typelen sem_info_t)) <= Int.max_unsigned -> *)
    s |= GV Sem_info @ sem_info_t ∗ |-> Vptr (b,i) **
      Aarray_new (b, i) (Tarray sem_info_t n) vll1 **
      Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen sem_info_t)))) sem_info_t vl **
      Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen sem_info_t))))
        (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)))) vll2 ** P ->
    new_array_type_vallist_match sem_info_t (vll1 ++ (vl::vll2)) ->
    length (vll1 ++ (vl::vll2)) = ∘ (OS_USER_MAX_EVENTS / 3) ->
    s |= ASeminfo (vll1 ++ (vl::vll2)) ** P.
Proof.
  intros.
  assert (Hrgn: Z.of_nat (S n * typelen sem_info_t) <= Int.max_unsigned).
  {
    remember (typelen sem_info_t) as X. 
    unfold sem_info_t in HeqX. simpl in HeqX. 
    rewrite HeqX.
    unfold_usr_max_evts_in H.
    simpl in H.
    asserts_rewrite (20 / 3 = 6)  in H. { auto with zarith. } 
    int auto.
  }
  unfold ASeminfo.
  sep pauto.
  assert (Heq: ∘ (OS_USER_MAX_EVENTS / 3) 
               =  Nat.add n (S (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n))) )).
  unfold nat_of_Z.
  assert (Heq1: Z.to_nat (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S n)) 
              = Nat.sub (Z.to_nat (OS_USER_MAX_EVENTS / 3))  (Z.to_nat (Z.of_nat (S n))) ).
  apply Z2Nat.inj_sub.
  eauto with zarith.
  rewrite Heq1.
  eauto with zarith.
  rewrite Heq.
  eapply Aarray_new_compose_strong; eauto.

  sep pauto.
  eapply Aarray_new_succ.
  rewrite Int.add_assoc.
  asserts_rewrite ($ Z.of_nat (n * typelen sem_info_t) +ᵢ  $ Z.of_nat (typelen sem_info_t) 
                   = $ Z.of_nat (S n * typelen sem_info_t)).
  { int auto. }
  sep pauto.
  unfold sem_info_t.
  unfold Aarray_new.
  unfold Aarray_new'.
  fold sem_info_t.
  sep pauto.
Qed. *)

(* Lemma ASeminfo_select_sn_ex_strong:
  forall s P semvl,
     s |= EX vll1 n vll2 b i vl ,
             GV Sem_info @ sem_info_t ∗ |-> Vptr (b,i) **
             Aarray_new (b, i) (Tarray sem_info_t n) vll1 **
             Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen sem_info_t)))) sem_info_t vl **
             Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen sem_info_t))))
               (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)))) vll2 **
             [| new_array_type_vallist_match sem_info_t semvl |] **
             [| length semvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
             [| semvl = vll1 ++ (vl::vll2) |] ** 
             [| length vll1 = n /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)) |] **
             [| Z.of_nat(S n) <= OS_USER_MAX_EVENTS / 3 |] **
             (* [| 0 <= Int.unsigned i + (OS_USER_MAX_EVENTS / 3) * (Z.of_nat (typelen sem_info_t)) <= Int.max_unsigned |] ** *)
              P ->
    s |= ASeminfo semvl ** P.
Proof.
  intros.
  do 6 destruct H.
  sep split in H.
  subst.
  eapply ASeminfo_select_sn_strong.
  eauto.
  eauto.
  sep pauto.
  eauto.
Qed. *)

Lemma semb_corr': 
  forall vl vll1 vll2 embls hld v i, 
    EIBArray_P v (vll1 ++ vl :: vll2) embls hld ->
    Int.ltu i Int.zero = false -> 
    length vll1 = Z.to_nat (Int.unsigned i) -> 
    (forall j, v = Vint32 j ->
               Int.ltu j Int.zero = false /\ Int.unsigned j + Int.unsigned i <= Int.max_unsigned) ->  
    exists j eid_opt tp sc,
      v = Vint32 j /\
      get embls (j +ᵢ i) = Some (eid_opt, tp, sc) /\
          V_OSSINFOType vl = Some (Vint32 tp) /\
           ((exists eid, eid_opt = infotid eid /\ V_OSSINFOPevent vl = Some (Vptr eid) /\ eid <> hld) \/
           (eid_opt = infohold /\ V_OSSINFOPevent vl = Some (Vptr hld)) \/
              (eid_opt = infonull /\ V_OSSINFOPevent vl = Some Vnull)).
Proof.
  inductions vll1.

  introv Harrp Hi Hlen Hsumrgn.
  simpl in Harrp.
  assert (Hiz: i = Int.zero).
  { 
    simpl in Hlen. destruct (Int.unsigned i) eqn: E.
    apply Int.unsigned_eq_zero; auto.
    int auto. int auto.
  }
  destruct Harrp as (pos & embls' & absemb & v' & Hv & Hv' & Hjo & HP & H').
  unfold RHL_EINFO_P in HP.
  destruct absemb as ((eo & kd) & sc).
  (* destruct absemb as [eo kd]. *)
  specialize (HP eo kd sc (eq_refl _)).
  destruct v eqn: E; try inverts Hv.
  exists pos.
  exists eo kd sc.
  splits; auto.
  assert (Heq: pos +ᵢ  i = pos). { rewrite Hiz. int auto. }
  rewrite Heq.
  eapply join_sig_get; eauto.
  destructs HP.
  auto. 
  destructs HP. auto.
  
  introv Harrp Hi Hlen Hsumrgn.
  simpl in Harrp.
  simpl in Hlen.
  assert (Hige: Int.unsigned i >= 1). { auto with zarith. }
  destruct Harrp as (pos & embls' & absemb & v' & Hv & Hv' & Hjo & HP & H').
  eapply IHvll1 with (embls:=embls') (i:=Int.sub i ($1)) in H'; eauto.
  destruct H' as (j & eo & kd & sc & H').
  exists pos eo kd sc.
  simpljoin1. splits; auto.
  inverts H.
  rewrite pos_add_sub_one in H0; auto.
  eapply join_lib.map_join_get_none' with (m2:=embls'); eauto.
  apply get_a_sig_a'.
  specialize (Hsumrgn pos (eq_refl _)). 
  destruct Hsumrgn. apply pos_add_i_neq; auto.
  specialize (Hsumrgn pos (eq_refl _)).
  mytac.
  specialize (Hsumrgn pos (eq_refl _)).
  mytac.
  apply i_ge1_i_sub1_ge0. auto.
  int auto. int auto. 
  introv H_v'.
  subst v. subst v'. inverts H_v'.
  specialize (Hsumrgn pos (eq_refl _)).
  destruct Hsumrgn as (Hpos & Hadd).
  split. int auto. int auto.
  int auto. int auto. int auto.
Qed.

Lemma semb_corr: 
  forall vl vll1 vll2 embls hld i, 
    EIBArray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls hld ->
    length vll1 = Z.to_nat (Int.unsigned i) -> 
    Int.ltu i Int.zero = false -> 
    Int.unsigned i <= Int.max_unsigned ->  
    exists eid_opt tp sc,
      get embls i = Some (eid_opt, tp, sc) /\
          V_OSSINFOType vl = Some (Vint32 tp)
      /\
        ((exists eid, eid_opt = infotid eid /\ V_OSSINFOPevent vl = Some (Vptr eid) /\ eid <> hld) 
         \/ (eid_opt = infohold /\ V_OSSINFOPevent vl = Some (Vptr hld)) 
         \/ (eid_opt = infonull /\ V_OSSINFOPevent vl = Some Vnull)).
Proof.
  introv HP Hvll1 Hlt Hle.
  eapply semb_corr' with (i:=i) in HP; eauto.
  2: {
    introv Hj0. 
    split. inv Hj0. int auto. inverts Hj0. int auto.
  }
  rewrite <- (Int.add_zero_l i).
  simpljoin1.
  do 3 eexists. splits; eauto.
  inverts H.
  instantiate (1:= x2).
  auto.
Qed.

Lemma Seminfo_full_imp_no_free
: forall semvl,
    Seminfo_full_P semvl ->
    ~(exists i, nth_Seminfo_free_P i semvl).
Proof.
unfold nth_Seminfo_free_P.
unfold Seminfo_full_P.
intros.
do 2 (eapply Classical_Pred_Type.all_not_not_ex; intros).
pure_auto.
Qed.

Lemma Seminfo_free_imp_no_full
: forall semvl,
    (exists i, nth_Seminfo_free_P i semvl) ->
     ~(Seminfo_full_P semvl).
Proof.
unfold nth_Seminfo_free_P.
unfold Seminfo_full_P.
intros.
pure_auto.
do 3 destruct H.
destruct H1.
destruct H2.
eapply H0; eauto.
Qed.


Lemma Seminfo_free_dec
: forall semvl,
    (exists i, nth_Seminfo_free_P i semvl) \/ Seminfo_full_P semvl.
Proof.
intros.
assert (Ht: (Seminfo_full_P semvl) \/ ~(Seminfo_full_P semvl)) by tauto.
destruct Ht. pure_auto.
left.
unfold nth_Seminfo_free_P in *.
unfold Seminfo_full_P in *.
eapply Classical_Pred_Type.not_all_ex_not in H.
destruct H.
eapply Classical_Pred_Type.not_all_ex_not in H.
destruct H.
eapply Classical_Prop.imply_to_and in H; destruct H.
eapply Classical_Prop.imply_to_and in H0; destruct H0.
destruct H.
repeat eexists; eauto.
tauto.
Qed.

Lemma ASeminfo_select_sn_ex_strong_frm:
  forall s b i semvl,
     s |= EX vll1 n vll2 (* b i *) vl ,
             GV Sem_info @ sem_info_t ∗ |-> Vptr (b,i) **
             Aarray_new (b, i) (Tarray sem_info_t n) vll1 **
             Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen sem_info_t)))) sem_info_t vl **
             Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen sem_info_t))))
               (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)))) vll2 **
             [| new_array_type_vallist_match sem_info_t semvl |] **
             [| length semvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
             [| semvl = vll1 ++ (vl::vll2) |] ** 
             [| length vll1 = n /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)) |] **
             [| Z.of_nat(S n) <= OS_USER_MAX_EVENTS / 3 |] ->
    s |= ASeminfo (b,i) semvl.
Proof.
  intros. 
  apply astar_r_aemp_elim.
  eapply ASeminfo_select_sn_ex_strong.
  sep auto.
Qed.

Lemma Seminfo_full_P_nil :
Seminfo_full_P nil.
Proof.
unfold Seminfo_full_P.
simpl. auto with zarith.
Qed.

Lemma Seminfo_full_P_succ :
forall a vl, Seminfo_full_P (a :: vl) <-> (Seminfo_full_P (a::nil) /\ Seminfo_full_P vl).
Proof.
unfold Seminfo_full_P.
split; intros.
simpl in *.
split; intros.
eapply H. instantiate (1:= i). int auto.
destruct (∘ i); tryfalse. auto.
eapply H. instantiate (1:= (i + 1)). int auto.
assert (Hi: (∘ (i + 1)) = ((∘ i) + (∘ 1))%nat).
eapply nat_of_Z_plus; auto with zarith.
rewrite Hi.
change (∘ 1) with 1%nat.
assert (Hi': (∘ i + 1)%nat = S (∘ i)).
auto with zarith.
rewrite Hi'. auto.
destruct H.
destruct H0.
assert (Hi: i= 0 \/ i <> 0) by tauto.
destruct Hi.
eapply H. simpl in *. eauto with zarith. subst i. auto.
eapply H2. instantiate (1:= i - 1). simpl in *. eauto with zarith.
assert (Hsub: i = i - 1 +1).
rewrite Z.sub_add. auto.
rewrite Hsub in H1.
assert (Hi: ∘ (i - 1 + 1) = ((∘ (i - 1)) + (∘ 1))%nat).
eapply nat_of_Z_plus; auto with zarith.
rewrite Hi in H1.
change (∘ 1) with 1%nat in H1.
assert (Hi': (∘ (i - 1) + 1)%nat = S (∘ (i - 1))) by auto with zarith.
rewrite Hi' in H1.
simpl in H1. auto.
Qed.

Lemma Seminfo_full_P_split:
forall vl1 vl2, (Seminfo_full_P vl1 /\ Seminfo_full_P vl2)  <-> Seminfo_full_P (vl1 ++ vl2).
Proof.
induction vl1; intros.
simpl. split; try pure_auto. apply Seminfo_full_P_nil.
simpl.
rewrite Seminfo_full_P_succ.
rewrite Seminfo_full_P_succ with (vl:= vl1 ++ vl2).
rewrite <- IHvl1.
tauto.
Qed.

Lemma ASeminfo_split: 
  forall s b i vll1 vl vll2,
    s |= ASeminfo (b, i) (vll1 ++ (vl :: vll2)) ->
    s |= EX idx (* b i *),
           GV Sem_info @ sem_info_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray sem_info_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen sem_info_t))) sem_info_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen sem_info_t))))
          (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match sem_info_t (vll1 ++ (vl :: vll2)) |] **
          [| length (vll1 ++ (vl :: vll2)) = ∘ (OS_USER_MAX_EVENTS / 3) |] **
          [| length vll1 = idx /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 |].  
Proof.
intros.
unfold ASeminfo in H.
(* destruct H. *)
(* destruct x. *)
sep lift 2%nat in H.
sep split in H.
destruct H0.
lets Hl: H1.
rewrite app_length in Hl.
rewrite <- Hl in H.
assert ((length vll1 < ∘ (OS_USER_MAX_EVENTS / 3))%nat).
rewrite <- Hl. simpl.
auto with zarith.
assert (Hl2: length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S (length vll1)))).
{
  unfold nat_of_Z in *.
  assert (Z.to_nat (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S (length vll1))) =
                  (Z.to_nat (OS_USER_MAX_EVENTS / 3) - Z.to_nat(Z.of_nat (S (length vll1))))%nat).
  eapply Z2Nat.inj_sub; auto with zarith.
  rewrite H3.
  rewrite <- Hl.
  rewrite Nat2Z.id.
  simpl.
  auto with zarith.
}
eapply Aarray_new_split_strong_frm in H; try (split; auto).
2: { unfold sem_info_t. simpl typelen.
     (* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in H2. *)
     lets Hrgn: usr_max_evts_rgn.
     destruct Hrgn as (Hrgn3 & Hrgn4).
     clear -H2 Hrgn3 Hrgn4.
     unfold nat_of_Z in H2.
     int auto. }
sep pauto.
sep cancel 1%nat 1%nat.
change (length (vl :: vll2)) with (S (length vll2)) in H.
eapply Aarray_new_succ_imp in H.
rewrite Int.add_assoc in H.
assert (Hsuc: ($ Z.of_nat (length vll1 * typelen sem_info_t) +ᵢ
          $ Z.of_nat (typelen sem_info_t)) =
     $ Z.of_nat (S (length vll1) * typelen sem_info_t) ).
{
  clear -Hl H2.
  unfold sem_info_t. simpl typelen.
  assert ((S (length vll1) * 60)%nat = ((((length vll1) * 60)%nat + 60)%nat)).
  auto with zarith.
  rewrite H.
  rewrite Nat2Z.inj_add.
  (* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in H2. *)
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  clear -H2 Hrgn3 Hrgn4.
  unfold nat_of_Z in H2.
  int auto.
}
rewrite Hsuc in H.
rewrite <- Hl2.
sep cancel 2%nat 2%nat.
unfold Aarray_new in H.
unfold Aarray_new' in H. unfold sem_info_t in H.
fold sem_info_t in H.
sep pauto.
(* change (∘ (OS_USER_MAX_EVENTS / 3)) with 6%nat in H2. *)
(* change (OS_USER_MAX_EVENTS / 3) with 6. *)
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
clear -H2 Hrgn3 Hrgn4.
unfold nat_of_Z in H2.
auto with zarith.
Qed.

Lemma ASeminfo_split_frm: 
  forall s b i vll1 vl vll2 P,
    s |= ASeminfo (b, i) (vll1 ++ (vl :: vll2)) ** P ->
    s |= EX idx (* b i *),
           GV Sem_info @ sem_info_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray sem_info_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen sem_info_t))) sem_info_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen sem_info_t))))
          (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match sem_info_t (vll1 ++ (vl :: vll2)) |] **
          [| length (vll1 ++ (vl :: vll2)) = ∘ (OS_USER_MAX_EVENTS / 3) |] **
          [| length vll1 = idx /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 |] ** P.  
Proof.
intros.
unfold ASeminfo in H.
sep normal in H.
(* destruct H. *)
(* destruct x. *)
sep lift 2%nat in H.
sep split in H.
destruct H0.
lets Hl: H1.
rewrite app_length in Hl.
rewrite <- Hl in H.
assert ((length vll1 < ∘ (OS_USER_MAX_EVENTS / 3))%nat).
rewrite <- Hl. simpl.
auto with zarith.
assert (Hl2: length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S (length vll1)))).
{
  unfold nat_of_Z in *.
  assert (Z.to_nat (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S (length vll1))) =
                  (Z.to_nat (OS_USER_MAX_EVENTS / 3) - Z.to_nat(Z.of_nat (S (length vll1))))%nat).
  eapply Z2Nat.inj_sub; auto with zarith.
  rewrite H3.
  rewrite <- Hl.
  rewrite Nat2Z.id.
  simpl.
  auto with zarith.
}
eapply Aarray_new_split_strong_frm in H; try (split; auto).
2: { unfold sem_info_t. simpl typelen.
     (* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in H2. *)
     lets Hrgn: usr_max_evts_rgn.
     destruct Hrgn as (Hrgn3 & Hrgn4).
     clear -H2 Hrgn3 Hrgn4.
     unfold nat_of_Z in H2.
     int auto. }
sep pauto.
sep cancel 1%nat 1%nat.
change (length (vl :: vll2)) with (S (length vll2)) in H.
eapply Aarray_new_succ_imp in H.
rewrite Int.add_assoc in H.
assert (Hsuc: ($ Z.of_nat (length vll1 * typelen sem_info_t) +ᵢ
          $ Z.of_nat (typelen sem_info_t)) =
     $ Z.of_nat (S (length vll1) * typelen sem_info_t) ).
{
  clear -Hl H2.
  unfold sem_info_t. simpl typelen.
  assert ((S (length vll1) * 60)%nat = ((((length vll1) * 60)%nat + 60)%nat)).
  auto with zarith.
  rewrite H.
  rewrite Nat2Z.inj_add.
  (* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in H2. *)
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  clear -H2 Hrgn3 Hrgn4.
  unfold nat_of_Z in H2.
  int auto.
}
rewrite Hsuc in H.
rewrite <- Hl2.
sep cancel 2%nat 2%nat.
unfold Aarray_new in H.
unfold Aarray_new' in H. unfold sem_info_t in H.
fold sem_info_t in H.
sep pauto.
(* change (∘ (OS_USER_MAX_EVENTS / 3)) with 6%nat in H2.
change (OS_USER_MAX_EVENTS / 3) with 6. *)
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
clear -H2 Hrgn3 Hrgn4.
unfold nat_of_Z in H2.
auto with zarith.
Qed.

Lemma new_array_type_vallist_match_sem_getp:
forall vll1 vl vll2,
new_array_type_vallist_match sem_info_t (vll1 ++ (vl :: vll2)) ->
exists v, V_OSSINFOPevent vl = Some v /\ isptr v.
Proof.
intros.
eapply new_array_type_vallist_match_split in H; eauto.
destruct H as (_ & _ & Hsp).
lets Hvl: struct_type_vallist_match_elim_9 Hsp.
destruct Hvl. do 8 destruct H.
subst vl.
simpl in Hsp.
destruct Hsp as (_ & _ & _ & _ & _ & _ & _ & Hk & _).
exists x3.
unfold V_OSSINFOPevent. unfold isptr.
simpl. split; auto.
destruct x3; tryfalse; pure_auto.
Qed.

Lemma aseminfo_len_frm: 
  forall s l vl P, s |= ASeminfo l vl ** P -> length vl = ∘ (OS_USER_MAX_EVENTS / 3).
Proof.  
  introv Hsat.
  destruct Hsat.
  simpl_sat H. simpljoin1.
  destruct H3.
  simpl_sat H. simpljoin1.
  auto.
Qed.

Lemma length_vll_asemeibs_sinfo:
  forall s P sinfol scapl semeibs ecbls vhold, 
    s |= ASemEIBs sinfol scapl semeibs ecbls vhold ** P ->
    length sinfol = ∘ (OS_USER_MAX_EVENTS / 3).  
Proof.
  intros.
  unfold ASemEIBs in H.
  sep normal in H.
  destruct H.
  eapply aseminfo_len_frm with (s := s); eauto.
Qed.

Lemma nth_Seminfo_free_P_range: 
  forall s l vl P i, s |= ASeminfo l vl ** P -> nth_Seminfo_free_P i vl -> 0 <= i < OS_USER_MAX_EVENTS / 3.
Proof. 
  intros.
  funfold H0.
  apply aseminfo_len_frm in H.
  rewrite H in *.
  unfold nat_of_Z in *.
  auto with zarith.
Qed.

Lemma semb_getnull:
  forall vl vll1 vll2 embls hld i,
    EIBArray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls hld ->
    nth_Seminfo_free_P i (vll1 ++ vl :: vll2) ->
    length vll1 = Z.to_nat i ->
    length (vll1 ++ vl :: vll2) = ∘ (OS_USER_MAX_EVENTS / 3) ->
    exists tp sc,
      get embls (Int.repr i) = Some (infonull, tp, sc) /\
      V_OSSINFOPevent vl = Some Vnull.
Proof.
  introv He Hf Hl1 Hl2.
  funfold Hf.
  rewrite Hl2 in H0.
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  unfold nat_of_Z in H0.
  assert (Z.of_nat (Z.to_nat (OS_USER_MAX_EVENTS / 3)) = (OS_USER_MAX_EVENTS / 3)).
  apply Z2Nat.id.
  int auto.
  rewrite H3 in H0.
  assert (Hi_ran: Int.ltu ($ i) Int.zero = false /\ Int.unsigned ($ i) <= Int.max_unsigned).
  (* change (OS_USER_MAX_EVENTS / 3) with 6 in H0. *)
  int auto.
  destruct Hi_ran as (Hi1 & Hi2).
  assert (Hi: Int.unsigned (Int.repr i) = i).
  eapply int_usign_eq; auto.
  (* change (OS_USER_MAX_EVENTS / 3) with 6 in H0. *)
  int auto.
  unfold nat_of_Z in H1.
  rewrite <- Hl1 in H1.
  rewrite nth_vallist_get_idx in H1.
  inverts H1.
  rewrite <- Hi in Hl1.
  lets Hsem: semb_corr He Hl1 Hi1 Hi2.
  mytac.
  unfold V_OSSINFOPevent in *.
  rewrite Hi in Hl1.
  rewrite H2 in H5.
  do 2 destruct H5; mytac; tryfalse.
  repeat eexists.
  apply H1.
  auto.
Qed.

Lemma EIBArray_P_nth_vallist:
forall semvl posv embls hld i,
        EIBArray_P posv semvl embls hld ->
        0 <= i < Z.of_nat (length semvl)  ->
        exists vl, nth_vallist ∘ i semvl = Some vl.
Proof.
induction semvl;intros.
simpl in *.
false.
auto with zarith.
simpl in H.
mytac.
destruct (∘ i ) eqn: eq1.
simpl.
exists a. auto.
lets Hi: nat_of_Z_eq_succ eq1.
simpl.
rewrite Hi.
eapply IHsemvl in H5.
instantiate (1:= (i - 1)) in H5.
auto.
lets eq2: nat_of_Z_eq eq1 H0.
unfold nat_of_Z in eq1.
subst i.
simpl length in H1.
split.
auto with zarith.
auto with zarith.
Qed.

Lemma semb_corr_alt: 
  forall i semvl embls hld, 
    EIBArray_P (Vint32 Int.zero) semvl embls hld ->
    (i < (length semvl))%nat ->
    length semvl = ∘ (OS_USER_MAX_EVENTS / 3) ->
    exists vl eid_opt tp sc, 
      nth_vallist i semvl = Some vl /\
        get embls ($ (Z.of_nat i)) = Some (eid_opt, tp, sc) /\
        V_OSSINFOType vl = Some (Vint32 tp) /\ 
        ((exists eid, eid_opt = infotid eid /\ 
                      V_OSSINFOPevent vl = Some (Vptr eid) /\ eid <> hld) \/
                      (eid_opt = infohold /\ V_OSSINFOPevent vl = Some (Vptr hld)) \/
                      (eid_opt = infonull /\ V_OSSINFOPevent vl = Some Vnull)). 
Proof.
introv He Hi Hl.
destruct semvl.
simpl in *. false.
auto with zarith.
assert (v :: semvl <> nil ) by eauto.
lets Hsp: list_vallist_split_idx Hi H.
destruct Hsp. do 3 destruct H0.
rewrite H0 in *.
eapply semb_corr in He.
instantiate (1:= ($ Z.of_nat i)) in He.
destruct He. destruct H2. destruct H2.
do 4 eexists. 
splits; pauto. 
subst i.
rewrite nth_vallist_get_idx. auto.
subst i.
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
(* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in Hl. *)
rewrite Hl in Hi.
unfold nat_of_Z in Hi.
int auto.
rewrite int_ltu_zero_eq_false; auto.
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
(* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in Hl. *)
rewrite Hl in Hi.
unfold nat_of_Z in Hi.
int auto.
Qed.

Lemma semb_corr_alt': 
  forall i semvl embls hld, 
    EIBArray_P (Vint32 Int.zero) semvl embls hld ->
    (Int.unsigned i) < Z.of_nat (length semvl) ->
    length semvl = ∘ (OS_USER_MAX_EVENTS / 3) ->
    exists vl eid_opt tp sc, 
      nth_vallist ∘ (Int.unsigned i) semvl = Some vl /\
        get embls i = Some (eid_opt, tp, sc) /\
        V_OSSINFOType vl = Some (Vint32 tp) /\
        ((exists eid, eid_opt = infotid eid /\  
                      V_OSSINFOPevent vl = Some (Vptr eid) /\ eid <> hld) \/
                      (eid_opt = infohold /\ V_OSSINFOPevent vl = Some (Vptr hld)) \/
                      (eid_opt = infonull /\ V_OSSINFOPevent vl = Some Vnull)). 
Proof.
introv He Hi Hl.
eapply semb_corr_alt in He.
instantiate (1:= ∘ (Int.unsigned i)) in He.
assert (($ Z.of_nat ∘ (Int.unsigned i)) = i).
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
(* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in Hl. *)
rewrite Hl in Hi.
unfold nat_of_Z in *.
assert (Z.of_nat (Z.to_nat (Int.unsigned i)) = Int.unsigned i).
apply Z2Nat.id.
int auto.
rewrite H.
apply Int.repr_unsigned.
rewrite H in He.
auto.
unfold nat_of_Z in *.
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
(* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in Hl. *)
rewrite Hl in *.
int auto.
auto.
Qed.

Lemma semb_get_not_null: 
  forall semvl embls hld, 
    EIBArray_P (Vint32 Int.zero) semvl embls hld ->
    Seminfo_full_P semvl ->
    length semvl = ∘ (OS_USER_MAX_EVENTS / 3) ->
    ~(exists i tp sc,
          get embls i = Some (infonull, tp, sc) /\ 0 <= (Int.unsigned i) < Z.of_nat (length semvl)).
Proof.
introv He Hf Hl.
funfold Hf.
introv H. 
do 3 destruct H.
eapply semb_corr_alt' in He; eauto.
instantiate (1:= x) in He.
destruct He. destruct H0. destruct H0. destruct H0.
destruct H. destructs H0.
unfold get in H, H2.
unfold EmbMap in H, H2.
rewrite H2 in H. inverts H. 
destruct H4.
destruct H. destruct H. tryfalse. 
destruct H. destruct H. tryfalse.
destruct H.
eapply Hf; eauto.
destruct H. destruct H0. 
auto.
Qed.

Lemma struct_type_vallist_match_get_sem_type:
  forall x15 x14 x8 x9 x10 x11 x12 x13,
    struct_type_vallist_match sem_info_t (x15 :: x14 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: nil) ->
    exists tp, x15 = Vint32 tp.
Proof.
simpl.
intros.
destruct H as (H & _).
destruct x15; tryfalse.
eauto.
Qed.

Lemma RH_SEM_EINFO_ECB_P_set_to_hold:
  forall els embls pos tp sc,
    RH_SEM_EINFO_ECB_P els embls ->
    RH_SEM_EINFO_ECB_P els (set embls pos (infohold, tp, sc)). 
Proof.
  unfold RH_SEM_EINFO_ECB_P.
  intros.
  rewrite EmbMod.set_sem in H0.
  destruct (idxspec.beq pos pos0) eqn: eq1; tryfalse.
  eapply H in H0; eauto.
Qed.

(* RHL_EINFO_P change ****************************************************************)

Lemma RHL_EINFO_P_set_to_hold:
forall vl vhold v t sc,
V_OSSINFOPevent vl = Some v ->
V_OSSINFOType vl = Some (Vint32 t) -> 
RHL_EINFO_P (update_nth_val 7 vl (Vptr vhold)) (infohold,t,sc) vhold.
Proof.
unfold RHL_EINFO_P.
intros.
inverts H1.
unfold V_OSSINFOType in *.
splits; auto.
eapply nth_upd_neqrev; auto.

right. left.
unfold V_OSSINFOPevent in *.
splits; auto.
eapply update_nth. eauto.
Qed.

Lemma RHL_EINFO_P_set_to_null:
forall vl vhold v t sc,
V_OSSINFOPevent vl = Some v ->
V_OSSINFOType vl = Some (Vint32 t) -> 
RHL_EINFO_P (update_nth_val 7 vl Vnull) (infonull,t,sc) vhold.
Proof.
unfold RHL_EINFO_P.
intros.
inverts H1.
splits.
eapply nth_upd_neqrev; auto.
right. right.
unfold V_OSSINFOPevent in *.
splits; auto.
eapply update_nth. eauto.
Qed.

Lemma RHL_EINFO_P_set_to_tid:
forall vl vhold v pid t sc,
  V_OSSINFOPevent vl = Some v ->
  V_OSSINFOType vl = Some (Vint32 t) -> 
  pid <> vhold ->
  RHL_EINFO_P (update_nth_val 7 vl (Vptr pid)) (infotid pid,t,sc) vhold.
Proof.
unfold RHL_EINFO_P.
intros.
inverts H2.
splits.
eapply nth_upd_neqrev; auto.

left.
unfold V_OSSINFOType in *.
unfold V_OSSINFOPevent in *.
eexists.
splits; auto.
eapply update_nth. eauto.
Qed.

Lemma RHL_EINFO_P_set_type:
forall vl vhold tp sc tp' sc' eop,
RHL_EINFO_P vl (eop,tp,sc) vhold ->
RHL_EINFO_P (update_nth_val 0 vl (Vint32 tp')) (eop,tp',sc') vhold.
Proof.
unfold RHL_EINFO_P.
intros.
inverts H0.
unfold V_OSSINFOType in *;
unfold V_OSSINFOPevent in *.
(* assert ((eid_opt, tp, eflag0) = (eid_opt, tp, eflag0)) by auto. *)
specialize (H _ _ _ (eq_refl _)).
destructs H.
splits; (try (eapply nth_upd_neqrev; auto; fail)).
eapply update_nth. eauto.

destruct H0 as [H' | [H' | H']]; mytac; [left | right; left | do 2 right].

eexists.
splits; eauto.
eapply nth_upd_neqrev; eauto.
splits; eauto.
eapply nth_upd_neqrev; eauto.
splits; eauto.
eapply nth_upd_neqrev; eauto.
Qed.

Lemma RHL_EINFO_P_update_hold:
forall vl vhold x v n,
n <> 7%nat ->
n <> 0%nat ->
RHL_EINFO_P vl x vhold ->
RHL_EINFO_P (update_nth_val n vl v) x vhold.
Proof.
unfold RHL_EINFO_P.
introv Hn1 Hn2.
intros.
subst x.
(* assert ((eid_opt, tp, eflag) = (eid_opt, tp, eflag)) by auto. *)
specialize (H _ _ _ (eq_refl _)).
destructs H. 
unfold V_OSSINFOType in *.
unfold V_OSSINFOPevent in *.
splits; (try (eapply nth_upd_neqrev; auto; fail)).

destruct H0 as [H' | [H' | H']]; mytac;
[left | right; left | do 2 right].

eexists.
splits; eauto.
eapply nth_upd_neqrev; eauto.
splits; eauto.
eapply nth_upd_neqrev; eauto.
splits; eauto.
eapply nth_upd_neqrev; eauto.
Qed.

(* EIBArray_P change ********************************************************************)

Lemma EIBArray_P_hold_for_update_to_hold:
forall vll1 vl vll2 embls vhold pos j t sc,
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
(* isptr eflag -> *)
V_OSSINFOType vl = Some (Vint32 t) -> 
EIBArray_P (Vint32 j) (vll1 ++ vl :: vll2) embls vhold ->
EIBArray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 7 vl (Vptr vhold)) :: vll2)
                        (set embls (Int.add pos j) (infohold,t,sc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H3.
do 4 eexists.
destruct x1 as [eop' sc'].
destruct eop' as [eop' tp'].
lets Hcp: H6.
eapply RHL_EINFO_P_get_pevent in Hcp.
destruct Hcp.
splits; eauto.
change ($ 0) with Int.zero.
instantiate (1:= (infohold,t,sc)).
2: { eapply RHL_EINFO_P_set_to_hold; eauto.  }
rewrite Int.add_zero_l.
eapply EmbMod_get_join_sig_set; eauto.
eapply EmbMod_join_get_none_r; [idtac | eauto].
eapply EmbMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H3. simpl.
mytac.
inverts H3.
do 4 eexists.
splits; eauto.
instantiate (1:= set x0 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x) (infohold, t, sc)).
eapply EmbMod.join_comm.
eapply EmbMod.map_join_set_none.
eapply EmbMod.join_comm. auto.
eapply EmbMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x + Z.of_nat (S (length vll1)) = (Int.unsigned x + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x + 1).
pose proof (Int.unsigned_range_2 x).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x +ᵢ  Int.one) = Int.unsigned x + 1).
int auto;simpl length in *; auto with zarith.
rewrite H4. rewrite Heq2. auto.
Qed.

Lemma EIBArray_P_hold_for_update_to_null:
forall vll1 vl vll2 embls vhold pos j t sc,
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
V_OSSINFOType vl = Some (Vint32 t) -> 
EIBArray_P (Vint32 j) (vll1 ++ vl :: vll2) embls vhold ->
EIBArray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 7 vl Vnull) :: vll2)
                        (set embls (Int.add pos j) (infonull,t,sc)) vhold. 
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H3.
do 4 eexists.
destruct x1 as [eop' sc'].
destruct eop' as [eop' tp'].
lets Hcp: H6.
eapply RHL_EINFO_P_get_pevent in Hcp.
destruct Hcp.
splits; eauto.
change ($ 0) with Int.zero.
instantiate (1:= (infonull,t,sc)).
2: { eapply RHL_EINFO_P_set_to_null; eauto. }
rewrite Int.add_zero_l.
eapply EmbMod_get_join_sig_set; eauto.
eapply EmbMod_join_get_none_r; [idtac | eauto].
eapply EmbMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H3. simpl.
mytac.
inverts H3.
do 4 eexists.
splits; eauto.
instantiate (1:= set x0 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x) (infonull,t,sc)).
eapply EmbMod.join_comm.
eapply EmbMod.map_join_set_none.
eapply EmbMod.join_comm. auto.
eapply EmbMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x + Z.of_nat (S (length vll1)) = (Int.unsigned x + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x + 1).
pose proof (Int.unsigned_range_2 x).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x +ᵢ  Int.one) = Int.unsigned x + 1).
int auto;simpl length in *; auto with zarith.
rewrite H4. rewrite Heq2. auto.
Qed.

Lemma EIBArray_P_hold_for_update_to_hold':
forall vll1 vl vll2 embls vhold pos t sc,
length vll1 = Z.to_nat pos ->
0 <= pos <= Int.max_unsigned ->
(* isptr eflag -> *)
V_OSSINFOType vl = Some (Vint32 t) -> 
EIBArray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold ->
EIBArray_P (Vint32 Int.zero) 
                        (vll1 ++ (update_nth_val 7 vl (Vptr vhold)) :: vll2)
                        (set embls (Int.repr pos) (infohold,t,sc)) vhold.
Proof.
intros.
lets Hr: Int.unsigned_repr H0.
destruct H0.
eapply EIBArray_P_hold_for_update_to_hold in H2.
rewrite Int.add_zero in H2.
eauto.
eapply Z2Nat.id in H0.
rewrite <- H0.  rewrite H. auto.
eapply Z2Nat.id in H0.
rewrite H.  rewrite H0. auto.
rewrite Int.unsigned_zero. 
auto with zarith.
auto.
Qed.

Lemma EIBArray_P_hold_for_update_to_null':
forall vll1 vl vll2 embls vhold pos t sc,
length vll1 = Z.to_nat pos ->
0 <= pos <= Int.max_unsigned ->
V_OSSINFOType vl = Some (Vint32 t) -> 
EIBArray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold ->
EIBArray_P (Vint32 Int.zero) 
                        (vll1 ++ (update_nth_val 7 vl Vnull) :: vll2)
                        (set embls (Int.repr pos) (infonull,t,sc)) vhold.
Proof.
intros.
lets Hr: Int.unsigned_repr H0.
destruct H0.
eapply EIBArray_P_hold_for_update_to_null in H1.
rewrite Int.add_zero in H1.
eauto.
eapply Z2Nat.id in H0.
rewrite <- H0.  rewrite H. auto.
eapply Z2Nat.id in H0.
rewrite H.  rewrite H0. auto.
rewrite Int.unsigned_zero. 
auto with zarith.
auto.
Qed.

Lemma EIBArray_P_hold_for_update_to_tid:
forall vll1 vl vll2 embls vhold pos j pid t sc,
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
(* eflag = Vnull \/ eflag = Vptr pid -> *)
V_OSSINFOType vl = Some (Vint32 t) -> 
pid <> vhold ->
EIBArray_P (Vint32 j) (vll1 ++ vl :: vll2) embls vhold ->
EIBArray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 7 vl (Vptr pid)) :: vll2)
                        (set embls (Int.add pos j) (infotid pid,t,sc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H4.
do 4 eexists.
destruct x1 as [eop' sc'].
destruct eop' as [eop' tp'].
lets Hcp: H7.
eapply RHL_EINFO_P_get_pevent in Hcp.
destruct Hcp.
splits; eauto.
change ($ 0) with Int.zero.
instantiate (1:= (infotid pid,t,sc)).
2: { eapply RHL_EINFO_P_set_to_tid; eauto. }
rewrite Int.add_zero_l.
eapply EmbMod_get_join_sig_set; eauto.
eapply EmbMod_join_get_none_r; [idtac | eauto].
eapply EmbMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H4. simpl.
mytac.
inverts H4.
do 4 eexists.
splits; eauto.
instantiate (1:= set x0 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x) (infotid pid, t, sc)).
eapply EmbMod.join_comm.
eapply EmbMod.map_join_set_none.
eapply EmbMod.join_comm. auto.
eapply EmbMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x + Z.of_nat (S (length vll1)) = (Int.unsigned x + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x + 1).
pose proof (Int.unsigned_range_2 x).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x +ᵢ  Int.one) = Int.unsigned x + 1).
int auto;simpl length in *; auto with zarith.
rewrite H5. rewrite Heq2. auto.
Qed.

Lemma EIBArray_P_hold_for_update_to_tid':
forall vll1 vl vll2 embls vhold pos pid t sc,
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned pos <= Int.max_unsigned ->
(* eflag = Vnull \/ eflag = Vptr pid -> *)
V_OSSINFOType vl = Some (Vint32 t) ->
pid <> vhold ->
EIBArray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold ->
EIBArray_P (Vint32 Int.zero) 
                        (vll1 ++ (update_nth_val 7 vl (Vptr pid)) :: vll2)
                        (set embls pos (infotid pid,t,sc)) vhold.
Proof.
intros.
lets Hnew: EIBArray_P_hold_for_update_to_tid H H0.
instantiate (5:= Int.zero) in Hnew.
change (Int.unsigned Int.zero) with 0 in Hnew.
rewrite Int.add_commut in Hnew.
rewrite Int.add_zero_l in Hnew.
rewrite Z.add_0_l in Hnew.
eapply Hnew;eauto.
Qed.

Lemma EIBArray_P_hold_for_update_type:
forall vll1 vl vll2 embls vhold tp sc pos j tp' sc' eop,
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
EmbMod.get embls (Int.add pos j) = Some (eop,tp,sc) ->
V_OSSINFOType vl = Some (Vint32 tp) ->
EIBArray_P (Vint32 j) (vll1 ++ vl :: vll2) embls vhold ->
EIBArray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 0 vl (Vint32 tp')) :: vll2)
                        (set embls (Int.add pos j) (eop,tp',sc')) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H4.
do 4 eexists.
destruct x1 as [eop0 sc0].
destruct eop0 as [eop0 tp0].
lets Hget: EmbMod.join_sig_get H6.
change ($ 0) with Int.zero in *.
rewrite Int.add_zero_l in H2.
rewrite H2 in Hget.
inverts Hget.
lets Hcp: H7.
eapply RHL_EINFO_P_get_pevent in Hcp.
destruct Hcp.
splits; eauto.
(* change ($ 0) with Int.zero. *)
instantiate (1:= (eop, tp',sc')).
2: { eapply RHL_EINFO_P_set_type; eauto. }
rewrite Int.add_zero_l.
eapply EmbMod_get_join_sig_set; eauto.
eapply EmbMod_join_get_none_r; [idtac | eauto].
eapply EmbMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H4. simpl.
mytac.
inverts H4.
do 4 eexists.
splits; eauto.
instantiate (1:= set x0 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x) (eop, tp', sc')).
eapply EmbMod.join_comm.
eapply EmbMod.map_join_set_none.
eapply EmbMod.join_comm. auto.
eapply EmbMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x + Z.of_nat (S (length vll1)) = (Int.unsigned x + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x + 1).
pose proof (Int.unsigned_range_2 x).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x +ᵢ  Int.one) = Int.unsigned x + 1).
int auto;simpl length in *; auto with zarith.
rewrite H5. rewrite Heq2. auto.
eapply EmbMod.map_join_get_none in H6.
erewrite H2 in H6.
rewrite H6.
rewrite Heq. auto. 
eapply EmbMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
Qed.

Lemma EIBArray_P_hold_for_update_type':
forall vll1 vl vll2 embls vhold tp sc pos tp' sc' eop,
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned pos <= Int.max_unsigned ->
EmbMod.get embls pos = Some (eop,tp,sc) ->
V_OSSINFOType vl = Some (Vint32 tp) ->
EIBArray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold ->
EIBArray_P (Vint32 Int.zero) 
                        (vll1 ++ (update_nth_val 0 vl (Vint32 tp')) :: vll2)
                        (set embls pos (eop,tp',sc')) vhold.
Proof.
intros.
lets Hnew: EIBArray_P_hold_for_update_type H H0.
instantiate (5:= Int.zero) in Hnew.
change (Int.unsigned Int.zero) with 0 in Hnew.
rewrite Int.add_commut in Hnew.
rewrite Int.add_zero_l in Hnew.
rewrite Z.add_0_l in Hnew.
eapply Hnew;eauto.
Qed.

Lemma EIBArray_P_hold_for_update_same:
forall vll1 vl vll2 embls vhold pos j v n,
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
n <> 7%nat ->
n <> 0%nat ->
EIBArray_P (Vint32 j) (vll1 ++ vl :: vll2) embls vhold ->
EIBArray_P (Vint32 j) (vll1 ++ (update_nth_val n vl v) :: vll2) embls vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H4.
do 4 eexists.
splits;eauto.
eapply RHL_EINFO_P_update_hold; eauto.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H4. simpl.
mytac.
inverts H4.
do 4 eexists.
splits; eauto.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x + Z.of_nat (S (length vll1)) = (Int.unsigned x + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x + 1).
pose proof (Int.unsigned_range_2 x).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x +ᵢ  Int.one) = Int.unsigned x + 1).
int auto;simpl length in *; auto with zarith.
rewrite H5. rewrite Heq2. auto.
Qed.

Lemma EIBArray_P_hold_for_update_same':
forall vll1 vl vll2 embls vhold pos v n,
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned pos <= Int.max_unsigned ->
n <> 7%nat ->
n <> 0%nat ->
EIBArray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold ->
EIBArray_P (Vint32 Int.zero) (vll1 ++ (update_nth_val n vl v) :: vll2) embls vhold.
Proof.
intros.
eapply EIBArray_P_hold_for_update_same; eauto.
Qed.

Lemma RH_SEM_EINFO_ECB_P_set_minus_one : 
  forall els sid n wls embls,
    EcbMod.get els sid = Some (abssem n, wls) ->
    RH_SEM_EINFO_ECB_P els embls ->
    RH_SEM_EINFO_ECB_P (set els sid (abssem (n -ᵢ Int.one), wls)) embls.
Proof.
  unfold RH_SEM_EINFO_ECB_P.
  intros.
  assert (Hi: eid = sid \/ eid <> sid) by tauto.
  destruct Hi.
  subst.
  exists (n -ᵢ Int.one) wls.
  eapply EcbMod.set_a_get_a.
  eapply tidspec.eq_beq_true.
  auto.
  assert (Hg: get (set els sid (abssem (n -ᵢ Int.one), wls)) eid = get els eid).
  eapply EcbMod.set_a_get_a'.
  eapply tidspec.neq_beq_false.
  eauto.
  rewrite Hg.
  eauto.
Qed.

Lemma RH_MUX_EIB_ECB_P_sem_minus_one_preserve:
  forall muxeibs els n sid wls, 
    RH_ECBlk_EIBlk_Mux_P muxeibs els ->
    get els sid = Some (abssem n, wls) ->
    RH_ECBlk_EIBlk_Mux_P muxeibs (set els sid (abssem (n -ᵢ Int.one), wls)). 
Proof.
  introv Hrh Hget.
  unfold RH_ECBlk_EIBlk_Mux_P in *.
  introv Hget' Htpeq.
  subst eid_tp.
  casetac sid eid Ht Hf.
  -
    subst.
    lets H00: Hrh Hget'.
    specialize (H00 (eq_refl _)).
    simpljoin1.
    rewrite Hget in H.
    inverts H.
  -
    rewrite set_a_get_a'; eauto.
Qed.

Lemma AMuxEIBs_sem_minus_one_preserve:
  forall minfol mcapl muxeibs els sid n wls s P,
    s |= AMuxEIBs minfol mcapl muxeibs els vhold_addr ** P ->
    get els sid = Some (abssem n, wls) ->
    s |= AMuxEIBs minfol mcapl muxeibs (set els sid (abssem (n -ᵢ Int.one), wls)) vhold_addr ** P.
Proof. 
  introv Hsat Hget.
  unfold AMuxEIBs in *.
  sep pauto.
  eapply RH_MUX_EIB_ECB_P_sem_minus_one_preserve; eauto. 
Qed.

Lemma RH_EIB_ECB_Q_P_sem_minus_one_preserve: 
  forall els qeibs sid n wls, 
    RH_EIBlk_ECBlk_Q_P els qeibs -> 
    get els sid = Some (abssem n, wls) ->
    RH_EIBlk_ECBlk_Q_P (set els sid (abssem (n -ᵢ Int.one), wls)) qeibs. 
Proof.
  introv Hrh Hget.
  unfold RH_EIBlk_ECBlk_Q_P in *.
  introv Hget'.
  casetac sid eid Ht Hf.
  - subst.
    lets H00: Hrh Hget'.
    simpljoin1.
    rewrite Hget in H.
    inverts H.
  - rewrite set_a_get_a'; eauto. 
Qed.

Lemma AMqEIBs_sem_minus_one_preserve: 
  forall qattrl qcapl qeibs els sid n wls s P, 
    s |= AMqEIBs qattrl qcapl qeibs els vhold_addr ** P ->
    get els sid = Some (abssem n, wls) -> 
    s |= AMqEIBs qattrl qcapl qeibs (set els sid (abssem (n -ᵢ Int.one), wls)) vhold_addr ** P.  
Proof.
  introv Hsat Hget.
  unfold AMqEIBs in *.
  sep pauto.
  eapply RH_EIB_ECB_Q_P_sem_minus_one_preserve; eauto. 
Qed.


Lemma RH_SEM_EINFO_ECB_P_set_wls': 
  forall els sid n wls embls wls',
    EcbMod.get els sid = Some (abssem n, wls) ->
    RH_SEM_EINFO_ECB_P els embls ->
    RH_SEM_EINFO_ECB_P (set els sid (abssem n, wls')) embls.
Proof.
  unfold RH_SEM_EINFO_ECB_P.
  intros.
  assert (Hi: eid = sid \/ eid <> sid) by tauto.
  destruct Hi.
  subst.
  repeat eexists.
  eapply EcbMod.set_a_get_a.
  eapply tidspec.eq_beq_true.
  auto.
  assert (Hg: get (set els sid (abssem n, wls')) eid = get els eid).
  eapply EcbMod.set_a_get_a'.
  eapply tidspec.neq_beq_false.
  eauto.
  rewrite Hg.
  eauto.
Qed.

Lemma ASemEIBs_sem_set_wls'_preserve: 
  forall els sid n wls embls wls' infol scapl vhold s P,
    EcbMod.get els sid = Some (abssem n, wls) ->
    s |= ASemEIBs infol scapl embls els vhold ** P -> 
    s |= ASemEIBs infol scapl embls (set els sid (abssem n, wls')) vhold ** P.  
Proof. 
  introv Hsat Hget.
  unfold ASemEIBs in *.
  sep pauto.
  eapply RH_SEM_EINFO_ECB_P_set_wls'; eauto. 
Qed. 

Lemma RH_MUX_EIB_ECB_P_sem_set_wls'_preserve:
  forall muxeibs els n sid wls wls', 
    RH_ECBlk_EIBlk_Mux_P muxeibs els ->
    get els sid = Some (abssem n, wls) ->
    RH_ECBlk_EIBlk_Mux_P muxeibs (set els sid (abssem n, wls')). 
Proof.
  introv Hrh Hget.
  unfold RH_ECBlk_EIBlk_Mux_P in *.
  introv Hget' Htpeq.
  subst eid_tp.
  casetac sid eid Ht Hf.
  -
    subst.
    lets H00: Hrh Hget'.
    specialize (H00 (eq_refl _)).
    simpljoin1.
    rewrite Hget in H.
    inverts H.
  -
    rewrite set_a_get_a'; eauto.
Qed. 

Lemma AMuxEIBs_sem_set_wls'_preserve:
  forall minfol mcapl muxeibs els sid n wls wls' s P, 
    s |= AMuxEIBs minfol mcapl muxeibs els vhold_addr ** P ->
    get els sid = Some (abssem n, wls) ->
    s |= AMuxEIBs minfol mcapl muxeibs (set els sid (abssem n, wls')) vhold_addr ** P.
Proof. 
  introv Hsat Hget.
  unfold AMuxEIBs in *.
  sep pauto.
  eapply RH_MUX_EIB_ECB_P_sem_set_wls'_preserve; eauto. 
Qed.

Lemma RH_EIB_ECB_Q_P_sem_set_wls'_preserve: 
  forall els qeibs sid n wls wls', 
    RH_EIBlk_ECBlk_Q_P els qeibs -> 
    get els sid = Some (abssem n, wls) ->
    RH_EIBlk_ECBlk_Q_P (set els sid (abssem n, wls')) qeibs. 
Proof.
  introv Hrh Hget.
  unfold RH_EIBlk_ECBlk_Q_P in *.
  introv Hget'.
  casetac sid eid Ht Hf.
  - subst.
    lets H00: Hrh Hget'.
    simpljoin1.
    rewrite Hget in H.
    inverts H.
  - rewrite set_a_get_a'; eauto. 
Qed.

Lemma AMqEIBs_sem_set_wls'_preserve: 
  forall qattrl qcapl qeibs els sid n wls wls' s P,  
    s |= AMqEIBs qattrl qcapl qeibs els vhold_addr ** P ->
    get els sid = Some (abssem n, wls) -> 
    s |= AMqEIBs qattrl qcapl qeibs (set els sid (abssem n, wls')) vhold_addr ** P.  
Proof.
  introv Hsat Hget.
  unfold AMqEIBs in *.
  sep pauto.
  eapply RH_EIB_ECB_Q_P_sem_set_wls'_preserve; eauto.  
Qed.



Lemma RH_SEM_EINFO_ECB_P_sem_inc : 
  forall els sid n wls embls,
    EcbMod.get els sid = Some (abssem n, wls) ->
    RH_SEM_EINFO_ECB_P els embls ->
    RH_SEM_EINFO_ECB_P (set els sid (abssem (n +ᵢ Int.one), wls)) embls.
Proof.
  unfold RH_SEM_EINFO_ECB_P.
  intros.
  assert (Hi: eid = sid \/ eid <> sid) by tauto.
  destruct Hi.
  subst.
  exists (n +ᵢ Int.one) wls.
  eapply EcbMod.set_a_get_a.
  eapply tidspec.eq_beq_true.
  auto.
  assert (Hg: get (set els sid (abssem (n +ᵢ Int.one), wls)) eid = get els eid).
  eapply EcbMod.set_a_get_a'.
  eapply tidspec.neq_beq_false.
  eauto.
  rewrite Hg.
  eauto.
Qed.

Lemma RH_MUX_EIB_ECB_P_sem_inc_preserve:
  forall muxeibs els n sid wls, 
    RH_ECBlk_EIBlk_Mux_P muxeibs els ->
    get els sid = Some (abssem n, wls) ->
    RH_ECBlk_EIBlk_Mux_P muxeibs (set els sid (abssem (n +ᵢ Int.one), wls)). 
Proof.
  introv Hrh Hget.
  unfold RH_ECBlk_EIBlk_Mux_P in *.
  introv Hget' Htpeq.
  subst eid_tp.
  casetac sid eid Ht Hf.
  -
    subst.
    lets H00: Hrh Hget'.
    specialize (H00 (eq_refl _)).
    simpljoin1.
    rewrite Hget in H.
    inverts H.
  -
    rewrite set_a_get_a'; eauto.
Qed. 

Lemma AMuxEIBs_sem_inc_preserve:
  forall minfol mcapl muxeibs els sid n wls s P,
    s |= AMuxEIBs minfol mcapl muxeibs els vhold_addr ** P ->
    get els sid = Some (abssem n, wls) ->
    s |= AMuxEIBs minfol mcapl muxeibs (set els sid (abssem (n +ᵢ Int.one), wls)) vhold_addr ** P.
Proof. 
  introv Hsat Hget.
  unfold AMuxEIBs in *.
  sep pauto.
  eapply RH_MUX_EIB_ECB_P_sem_inc_preserve; eauto. 
Qed.

Lemma RH_EIB_ECB_Q_P_sem_inc_preserve: 
  forall els qeibs sid n wls, 
    RH_EIBlk_ECBlk_Q_P els qeibs -> 
    get els sid = Some (abssem n, wls) ->
    RH_EIBlk_ECBlk_Q_P (set els sid (abssem (n +ᵢ Int.one), wls)) qeibs. 
Proof.
  introv Hrh Hget.
  unfold RH_EIBlk_ECBlk_Q_P in *.
  introv Hget'.
  casetac sid eid Ht Hf.
  - subst.
    lets H00: Hrh Hget'.
    simpljoin1.
    rewrite Hget in H.
    inverts H.
  - rewrite set_a_get_a'; eauto. 
Qed.

Lemma AMqEIBs_sem_inc_preserve: 
  forall qattrl qcapl qeibs els sid n wls s P, 
    s |= AMqEIBs qattrl qcapl qeibs els vhold_addr ** P ->
    get els sid = Some (abssem n, wls) -> 
    s |= AMqEIBs qattrl qcapl qeibs (set els sid (abssem (n +ᵢInt.one), wls)) vhold_addr ** P.   
Proof.
  introv Hsat Hget.
  unfold AMqEIBs in *.
  sep pauto.
  eapply RH_EIB_ECB_Q_P_sem_inc_preserve; eauto. 
Qed.

(* used for sem init *)

Lemma RH_SEM_EINFO_ECB_P_set_type_preserve: 
  forall ecbls semeibs pos e tp sc tp', 
    RH_SEM_EINFO_ECB_P ecbls semeibs ->
    get semeibs pos = Some (e, tp, sc) -> 
    RH_SEM_EINFO_ECB_P ecbls (set semeibs pos (e, tp', sc)). 
Proof.
  introv Hrh Hget.
  unfold RH_SEM_EINFO_ECB_P in *.
  introv Hget'.
  casetac pos pos0 Heq Hneq.
  subst.
  rewrite set_a_get_a in Hget'.
  inverts Hget'.
  eapply Hrh; eauto.
  rewrite set_a_get_a' in Hget'; eauto.
Qed.

Lemma RH_SEM_EINFO_ECB_P_null_preserve:
  forall ecbls semeibs pos tp sc, 
    RH_SEM_EINFO_ECB_P ecbls semeibs ->
    RH_SEM_EINFO_ECB_P ecbls (set semeibs pos (infonull, tp, sc)). 
Proof.
  intros.
  unfold RH_SEM_EINFO_ECB_P in *.
  introv Hget.
  casetac pos pos0 Ht Hf.
  subst.
  rewrite set_a_get_a in Hget. inverts Hget.
  rewrite set_a_get_a' in Hget; eauto. 
Qed.

Lemma RH_SEM_EINFO_ECB_P_ptr_preserve: 
  forall ecbls semeibs pos tp sc eid, 
    RH_SEM_EINFO_ECB_P ecbls semeibs ->
    is_sem ecbls eid -> 
    RH_SEM_EINFO_ECB_P ecbls (set semeibs pos (infotid eid, tp, sc)). 
Proof.
  introv Hrh Hsem.
  unfold RH_SEM_EINFO_ECB_P in *.
  introv Hget.
  casetac pos pos0 Heq Hne.
  subst.
  rewrite set_a_get_a in Hget. inverts Hget.
  unfold is_sem in Hsem. eauto.
  rewrite set_a_get_a' in Hget; eauto.
Qed.

(* used for sem destroy *)

Lemma mux_eib_ecb_delsem_preserve: 
  forall muxeibs ecbls i1 ecbls' eid, 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls ->
    join ecbls' (sig eid (abssem i1, nil)) ecbls ->
    ~muxeib_ref muxeibs eid ->
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls'. 
Proof.
  introv Heibecb Hjo Hnref.
  unfold RH_ECBlk_EIBlk_Mux_P in *.
  introv Hgetpos Htp.
  casetac eid0 eid Heq Hneq.
  subst.
  unfold muxeib_ref in Hnref.
  false. apply Hnref. repeat eexists. eauto.
  lets H00: Heibecb Hgetpos Htp. clear Heibecb.
  simpljoin1.
  exists x x0 x1.
  assert (join (sig eid (abssem i1, nil)) ecbls' ecbls).
  join auto.
  eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
Qed.

Lemma amuxeibs_delsem_preserve: 
  forall s ecbls ecbls' eid i1 minfol mcapl muxeibs vhold P, 
    s |= AMuxEIBs minfol mcapl muxeibs ecbls vhold ** P -> 
    join ecbls' (sig eid (abssem i1, nil)) ecbls ->
    ~muxeib_ref muxeibs eid ->
    s |= AMuxEIBs minfol mcapl muxeibs ecbls' vhold ** P.  
Proof.
  introv Hsat Hjo Hnref.
  unfold AMuxEIBs in *.
  sep pauto.
  eapply mux_eib_ecb_delsem_preserve; eauto.
Qed.

Lemma mq_eib_ecb_delsem_preserve:
  forall mqeibs ecbls i1 ecbls' eid, 
    RH_EIBlk_ECBlk_Q_P ecbls mqeibs -> 
    join ecbls' (sig eid (abssem i1, nil)) ecbls ->
    ~mqeib_ref mqeibs eid ->
    RH_EIBlk_ECBlk_Q_P ecbls' mqeibs.
Proof.
  introv Heibecb Hjo Hnref.
  unfold RH_EIBlk_ECBlk_Q_P in *. 
  introv Hgetpos. 
  casetac eid0 eid Heq Hneq.
  subst.
  unfold mqeib_ref in Hnref.
  false. apply Hnref. repeat eexists. eauto.
  lets H00: Heibecb Hgetpos. clear Heibecb.
  simpljoin1.
  exists x x0 x1 x2. (* add x2 *)
  assert (join (sig eid (abssem i1, nil)) ecbls' ecbls).
  join auto.
  eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
Qed. 

Lemma mqeibaarray_delsem_preserve: 
  forall s qattrl qcapl mqeibs ecbls ecbls' vhold eid i1 P, 
    s |= AMqEIBs qattrl qcapl mqeibs ecbls vhold ** P ->  
    join ecbls' (sig eid (abssem i1, nil)) ecbls ->
    ~mqeib_ref mqeibs eid ->
    s |= AMqEIBs qattrl qcapl  mqeibs ecbls' vhold ** P. 
Proof.
  introv Hsat Hjo Hnref.
  unfold AMqEIBs in *.
  sep pauto.
  eapply mq_eib_ecb_delsem_preserve; eauto.
Qed. 

Lemma sem_einfo_ecb_delsem_preserve: 
  forall els semeibs muxeibs mqeibs els' i1 eid pos tp sc, 
    RH_SEM_EINFO_ECB_P els semeibs ->
    eibref_distinct semeibs muxeibs mqeibs ->
    join els' (sig eid (abssem i1, nil)) els ->
    get semeibs pos = Some (infotid eid, tp, sc) -> 
    RH_SEM_EINFO_ECB_P els' (set semeibs pos (infonull, tp, sc)). 
Proof.
  introv Heibecb Hd Hjo Heib.
  unfold RH_SEM_EINFO_ECB_P in *.
  introv Hget.
  casetac pos pos0 Heq Hneq.
  subst.
  rewrite set_a_get_a in Hget. inverts Hget.
  rewrite set_a_get_a' in Hget; eauto.
  lets H00: Heibecb Hget. clear Heibecb.
  simpljoin1.
  casetac eid0 eid Ht Hf.
  subst.
  unfold eibref_distinct in Hd.
  specialize (Hd eid).
  simpljoin1.
  unfold semref_distinct in H1.
  lets H00: H1 Heib Hget.
  apply Hneq in H00. tryfalse.
  exists x x0.
  assert (join (sig eid (abssem i1, nil)) els' els).
  join auto.
  eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
Qed.




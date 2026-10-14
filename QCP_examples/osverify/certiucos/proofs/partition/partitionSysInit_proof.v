(* new in partitionSysInitProof.v *)

Require Import seplog_lemmas.
Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import os_ucos_h.
(* Require Import abs_infer_abt. *)

Require Import partition.
Require Import abs_op_partition_ext.
Require Import Aarray_new_common.

Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Require Import Lia.
Require Import partition_common.

Local Open Scope code_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Lemma AKsDomSchedule'_len: 
  forall s vl, s |= AKsDomSchedule' vl -> length vl = ∘ (DSCHEDULE_SIZE).
Proof.
  introv Hsat.
  destruct Hsat.
  simpl_sat H. simpljoin1.
  auto.
Qed.

Lemma absimp_partitionSysInit_succ:
  forall P s sch idx  ld kscd dom kscd_len dom' kscd_len',
    can_change_aop P ->
    KsDScdMod.get kscd Int.zero = Some (dom', kscd_len') ->
    absinfer sch
             ( <|| partitionSys (nil) ;; s ||> ** HKsDSchdidx idx ** 
                                                               HKsCurDomain dom ** HKsLastDomain ld ** 
                                                               HKsDomainTime kscd_len **
                                                               HKsDomSchedule kscd ** P
                                                             
                                                               ) 
             ( <|| s ||> ** HKsDSchdidx Int.zero **
                                    HKsCurDomain dom' ** HKsLastDomain Int.mone ** 
                                    HKsDomainTime kscd_len' **
                                    HKsDomSchedule kscd ** P
                                  
                                     ). 
Proof.
  intros.
  subst. 
  infer_solver 0%nat.
  do 4 (eapply tidsame_trans; [idtac | eapply tidsame_set;eauto]).
  apply eqtid_same.
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
          [| R_KsDomSchedule_P vll |] **
          [| vll = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (DSCHEDULE_SIZE - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= DSCHEDULE_SIZE |].  
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
          [| R_KsDomSchedule_P vll |] **
          [| vll = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (DSCHEDULE_SIZE - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= DSCHEDULE_SIZE |]) ** P.
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
      R_KsDomSchedule_P (vll1 ++ (vl::vll2))  ->
    new_array_type_vallist_match dschedule_t (vll1 ++ (vl::vll2)) ->
    length (vll1 ++ (vl::vll2)) = ∘ (DSCHEDULE_SIZE) ->
    s |= AKsDomSchedule' (vll1 ++ (vl::vll2)).
Proof.
  intros.
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
     s |= EX vll1 n vll2 b i vl ,
             GV ksDomSchedule @ dschedule_t ∗ |-> Vptr (b,i) **
             Aarray_new (b, i) (Tarray dschedule_t n) vll1 **
             Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen dschedule_t)))) dschedule_t vl **
             Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen dschedule_t))))
                                (Tarray dschedule_t (∘ (DSCHEDULE_SIZE - Z.of_nat(S n)))) vll2 **
             [|  new_array_type_vallist_match dschedule_t (vll1 ++ (vl::vll2)) |] **
             [| R_KsDomSchedule_P (vll1 ++ (vl::vll2)) |] **
             [| length vll = ∘ (DSCHEDULE_SIZE) |] **
             [| vll = vll1 ++ (vl::vll2) |] ** 
             [| length vll1 = n /\ length vll2 = ∘ (DSCHEDULE_SIZE - Z.of_nat(S n)) |] **
             [| Z.of_nat(S n) <= DSCHEDULE_SIZE |] **
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



Lemma good_frm_p_local:
forall ct lg,
  GoodFrm (p_local OSLInv ct lg).
Proof.
  intros.
  unfold p_local.
  unfold LINV,CurTid.
  unfold OSLInv.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_p_local : good_frm_lemmas.

Theorem good_frm_AisCoreBoot :
  forall x1  ,
GoodFrm (AisCoreBoot x1 ).
Proof.
unfold AisCoreBoot in *. intros.
  good_frm_sovler.
Qed.
Hint Resolve good_frm_AisCoreBoot : good_frm_lemmas.

Theorem good_frm_AsystemStck' :
  forall x1 ,
GoodFrm (AsystemStck' x1).
Proof.
unfold AsystemStck' in *. intros.
  good_frm_sovler.
Qed.
Hint Resolve good_frm_AsystemStck' : good_frm_lemmas.

Theorem good_frm_AOSSystemSP :
  forall x1 ,
GoodFrm (AOSSystemSP x1).
Proof.
unfold AOSSystemSP in *. intros.
  good_frm_sovler.
Qed.
Hint Resolve good_frm_AOSSystemSP : good_frm_lemmas.

Theorem can_change_aop_AisCoreBoot :
  forall x1 ,
can_change_aop (AisCoreBoot x1 ).
Proof.
unfold AisCoreBoot in *. intros.
can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_AisCoreBoot : can_change_aop.

Theorem can_change_aop_AsystemStck' :
  forall x1 ,
can_change_aop (AsystemStck' x1 ).
Proof.
unfold AsystemStck' in *. intros.
can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_AsystemStck' : can_change_aop.


Theorem can_change_aop_AOSSystemSP :
  forall x1 ,
can_change_aop (AOSSystemSP x1 ).
Proof.
unfold AOSSystemSP in *. intros.
can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_AOSSystemSP : can_change_aop.


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


Theorem Tptr_bop_rv :
  forall s e1 e2 v1 t1 (* t2 *) v2  v t ,
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




Lemma partitionSysInit_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal partitionSysInit vl logicl partitionSysInitPre ct->
      Some r =
      BuildRetI os_internal partitionSysInit vl logicl partitionSysInitPost ct->
      exists t d1 d2 s,
        os_internal partitionSysInit = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
init spec.
subst.
unfold AKsDSchdidx, AisCoreBoot, AsystemStck', AKsCurDomain, AKsLastDomain,
             AKsDomainTime, AKsDomSchedule, AisChangePartion.
hoare unfold.
hoare forward.
hoare_enter_critical2.
hoare forward.
hoare forward.


(* hoare forward. *)
hoare_lifts_trms_pre AKsDomSchedule'.

eapply backward_rule1.
introv Hsat.
unfold AKsDomSchedule' in Hsat.
eapply AKsDomSchedule'_unfold_any_idx_frm with (idx:= Z.to_nat(Int.unsigned Int.zero)); eauto.
sep normal in Hsat. destruct Hsat. sep split in H8. 
destruct H9.
rewrite H18.
change DSCHEDULE_SIZE with (10).
unfold nat_of_Z.  rewrite Int.unsigned_zero. mauto.


hoare unfold.
lets Hnth: gjb_common.nth_vallist_get_idx v'16 v'20  v'17.
rewrite H12 in Hnth.
lets Hsp: H8.
eapply new_array_type_vallist_match_split1_gen in Hsp; eauto; try solve [unfolds; eauto].
destruct Hsp as (_ & _ & Hsp).
lets Hsp': Hsp. lets Hsp'': Hsp.
eapply struct_type_vallist_match_elim_2 in Hsp'.
destruct Hsp' as (dscd_dom & dscd_len & Heq).
subst.
simpl in Hsp''.
destruct dscd_dom; destruct dscd_len; simpl in Hsp''; simpljoin; tryfalse.
remember (Int.zero) as idx'.
rename i into dscd_dom; rename i0 into dscd_len.


rename v'10 into kscd_abs.
assert (Hget: KsDScdMod.get kscd_abs idx' = Some (dscd_dom, dscd_len)).
{
   eapply H2; eauto.
   split; auto with zarith.
   apply Int.unsigned_range_2.
}
subst.
(* ksCurDomain ′ =ₑ efield (ksDomSchedule ′[ksDomScheduleIdx ′]) dscd_domain;ₛ *)
hoare_lifts_trms_pre (Aop).
hoare forward.
eapply assign_rule_gvar.
split; introv Hsat. sep cancel (Agvarmapsto ksDomainTime).
sep cancel A_dom_lenv; eauto.
sep auto.
simpl; auto.
Ltac sep_get_rv_array_struct_gen :=
  let Hsat := fresh in
  let Hf := fresh in
  let Heq := fresh in
  match goal with
  | |- ?P ==> Rv efield (?gident ′ [?ident ′]) ?id @ ?tp1 == _ =>
        introv Hsat;
        eapply struct_array_member_rv';
                [ try symbolic_execution
                | try symbolic_execution
                | match goal with
                  | |- ((?te = _) \/ _) =>
                        match te with
                         | Tarray ?tp _ => try unfold tp
                         | Tptr ?tp => try unfold tp
                         | _ => idtac
                         end
                  end;auto
                | auto
                | try  match goal with
                            | Hsat:_ |= ?P'
                              |- _ |= Astruct (?pb, ?pi) _ _ ** _ =>
                                  match find_ptrstruct_by_block P' pb with
                                  | some ?n => sep lifts (n :: nil) in Hsat
                                  end
                            end; try simpl typelen; try sep cancel Astruct; eauto
                | match goal with
                  | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
                  end; eauto
                | simpl; auto
                | try apply gjb_common.int_ltu_zero_eq_false
                | try solve_part_int_rgn
                | simpl; try solve_part_int_rgn
                | auto
                | simpl; auto
                | splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
                | unfold id_nth; simpl; auto
                | simpl nth_val'; auto ]
  | Hsat:?s |= ?P
    |- ?s |= Rv efield (?gident ′ [?ident ′]) ?id @ ?tp1 == _ =>
       eapply struct_array_member_rv';
                [ try symbolic_execution
                | try symbolic_execution
                | match goal with
                  | |- ((?te = _) \/ _) =>
                        match te with
                         | Tarray ?tp _ => try unfold tp
                         | Tptr ?tp => try unfold tp
                         | _ => idtac
                         end
                  end;auto
                | auto
                | try  match goal with
                            | Hsat:_ |= ?P'
                              |- _ |= Astruct (?pb, ?pi) _ _ ** _ =>
                                  match find_ptrstruct_by_block P' pb with
                                  | some ?n => sep lifts (n :: nil) in Hsat
                                  end
                            end; try simpl typelen; try sep cancel Astruct; eauto
                | match goal with
                  | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
                  end; eauto
                | simpl; auto
                | try apply gjb_common.int_ltu_zero_eq_false
                | try solve_part_int_rgn
                | simpl; try solve_part_int_rgn
                | auto
                | simpl; auto
                | splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
                | unfold id_nth; simpl; auto
                | simpl nth_val'; auto ]
  end.

sep_get_rv_array_struct_gen.
eapply eq_int; tauto.
intros. eexists. sep cancel p_local. simpl; eauto.


hoare forward.
hoare forward.

(* ksDomainTime ′ =ₑ efield (ksDomSchedule ′[ksDomScheduleIdx ′]) dscd_length;ₛ *)
hoare_lifts_trms_pre (Aop).
hoare forward.
eapply assign_rule_gvar.
split; introv Hsat. sep cancel (Agvarmapsto ksCurDomain).
sep cancel A_dom_lenv; eauto.
sep auto.
simpl; auto.
sep_get_rv_array_struct_gen.
eapply eq_int; tauto.
intros. eexists. sep cancel p_local. simpl; eauto.

(* hoare forward. *)
remember (Int.zero) as idx'.
eapply backward_rule1.
introv Hsat.
eapply AKsDomSchedule'_select_sn_strong_frm.
exists v'16 (Z.to_nat (Int.unsigned idx')) v'17 v'18 v'19 (Vint32 dscd_dom :: Vint32 dscd_len :: nil).
sep pauto. subst.

(* hoare_lifts_trms_pre (Aop).
eapply assign_rule_general.
 *)
(* ksd ′ =ₑ 〈 long 〉 (&ₐ systemStck ′ [′ 511]);ₛ *)
destruct v'15. hoare forward.  

unfold AOSSystemSP.
hoare_lifts_trms_pre (Aop). 
hoare forward.   

hoare_lifts_trms_pre (Aop, ksdschedidxid,  kscurdomid, kslastdomid, ksdomtimeid, ksdschedid).
eapply abscsq_rule.
apply noabs_oslinv.
eapply absimp_partitionSysInit_succ; eauto.
can_change_aop_solver.
eapply absinfer_eq.
simpl nth_val'.
hoare forward.
hoare_exit_critical2.
subst.
hoare forward.


unfold AKsDomSchedule' in *.  
unfold R_KsDomSchedule_P in *. sep pauto.
sep split in H11.
destruct H3.  
eapply H3 in Hget. destruct Hget.
destruct H16 as (Hrgn & Hnth' & Hvdom & Hvlen). 
eapply H10 in Hvdom; eauto.



Unshelve. eauto.
exact O. exact O.
Qed.


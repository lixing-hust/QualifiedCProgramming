
(* Require Import include_frm.
Require Import ifun_spec.
Require Export os_inv.
Require Import List.
Require Import Maps.  *)

(* new in getFreePosProof.v *)

Require Import seplog_lemmas.

Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import os_ucos_h.
Require Import Aarray_new_common.
Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.

Require Import os_code_defs.
Require Import ifun_spec.
Require Import gjb_common.
Require Import gjb_sem_common.
Require Import gjb_q_common.
Require Import gjb_mutex_common.
Require Import evt_spec_defs.
Require Import partition_common.

Local Open Scope code_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Lemma Seminfo_full_P'_left_start: 
forall vll idx cpn,
  length vll = Z.to_nat (OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned idx) ->
  Seminfo_full_P' vll idx cpn.
Proof.
unfold Seminfo_full_P'.
intros.
rewrite H in *.
rewrite Z2Nat.id in *.
false.
auto with zarith.
eapply Ztac.mul_le; try apply Int.unsigned_range_2.
assert (Hc: Int.unsigned cpn = 0 \/ Int.unsigned cpn <> 0) by tauto.
destruct Hc as [Hc | Hc].
rewrite Hc.
rewrite Zdiv_0_r; auto with zarith.
eapply Z.div_pos.
pose proof usr_max_evts_rgn.
auto with zarith.
pose proof (Int.unsigned_range_2 cpn).
auto with zarith.
Qed.

Lemma PthreadMutex_full_P'_left_start: 
forall vll idx cpn,
  length vll = Z.to_nat (OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned idx) ->
  PthreadMutex_full_P' vll idx cpn.
Proof.
unfold PthreadMutex_full_P'.
intros.
rewrite H in *.
rewrite Z2Nat.id in *.
false.
auto with zarith.
eapply Ztac.mul_le; try apply Int.unsigned_range_2.
assert (Hc: Int.unsigned cpn = 0 \/ Int.unsigned cpn <> 0) by tauto.
destruct Hc as [Hc | Hc].
rewrite Hc.
rewrite Zdiv_0_r; auto with zarith.
eapply Z.div_pos.
pose proof usr_max_evts_rgn.
auto with zarith.
pose proof (Int.unsigned_range_2 cpn).
auto with zarith.
Qed.

Lemma Qattr_full_P'_left_start: 
forall vll idx cpn,
  length vll = Z.to_nat (OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned idx) ->
  Qattr_full_P' vll idx cpn.
Proof.
unfold Qattr_full_P'.
intros.
rewrite H in *.
rewrite Z2Nat.id in *.
false.
auto with zarith.
eapply Ztac.mul_le; try apply Int.unsigned_range_2.
assert (Hc: Int.unsigned cpn = 0 \/ Int.unsigned cpn <> 0) by tauto.
destruct Hc as [Hc | Hc].
rewrite Hc.
rewrite Zdiv_0_r; auto with zarith.
eapply Z.div_pos.
pose proof usr_max_evts_rgn.
auto with zarith.
pose proof (Int.unsigned_range_2 cpn).
auto with zarith.
Qed.

Lemma Seminfo_full_P'_split:
forall vl1 vl2 idx cpn,
  1 <= OS_USER_MAX_EVENTS / 3 / (Int.unsigned cpn) ->
  Seminfo_full_P' vl1 idx cpn ->
  V_OSSINFOPevent vl2 <> Some Vnull  ->
 Seminfo_full_P' (vl1 ++ vl2::nil) idx cpn.
Proof.
introv Hcpn Hfull Hvp.
lets Hnth: nth_vallist_get_idx vl1 vl2 (nil:list vallist).
unfold Seminfo_full_P' in *.
introv Hi Hnthi.
destruct Hi as (Hli & Hlr).
rewrite last_length in Hlr.
rewrite Nat2Z.inj_succ in Hlr.
eapply Zlt_succ_le in Hlr.
eapply Zle_lt_or_eq in Hlr.
rewrite <- nth_error_eq_nth_vallist in *.
assert (Hi: 0 <= i).
{
   eapply Z.le_trans; eauto.
   eapply Ztac.mul_le; auto with zarith.
   apply Int.unsigned_range_2.
}
destruct Hlr as [Hlr | Hlr].
eapply Hfull; eauto.
rewrite <- nth_error_eq_nth_vallist.
rewrite nth_error_app1 in Hnthi; auto with zarith.
unfold nat_of_Z.
auto with zarith.
subst.
unfold nat_of_Z in *.
rewrite Nat2Z.id in Hnthi.
rewrite Hnth in Hnthi; inverts Hnthi.
auto.
Qed.

Lemma PthreadMutex_full_P'_split:
forall vl1 vl2 idx cpn,
  1 <= OS_USER_MAX_EVENTS / 3 / (Int.unsigned cpn) ->
  PthreadMutex_full_P' vl1 idx cpn ->
  V_OSMUXINFOPevent vl2 <> Some Vnull  ->
 PthreadMutex_full_P' (vl1 ++ vl2::nil) idx cpn.
Proof.
introv Hcpn Hfull Hvp.
lets Hnth: nth_vallist_get_idx vl1 vl2 (nil:list vallist).
unfold PthreadMutex_full_P' in *.
introv Hi Hnthi.
destruct Hi as (Hli & Hlr).
rewrite last_length in Hlr.
rewrite Nat2Z.inj_succ in Hlr.
eapply Zlt_succ_le in Hlr.
eapply Zle_lt_or_eq in Hlr.
rewrite <- nth_error_eq_nth_vallist in *.
assert (Hi: 0 <= i).
{
   eapply Z.le_trans; eauto.
   eapply Ztac.mul_le; auto with zarith.
   apply Int.unsigned_range_2.
}
destruct Hlr as [Hlr | Hlr].
eapply Hfull; eauto.
rewrite <- nth_error_eq_nth_vallist.
rewrite nth_error_app1 in Hnthi; auto with zarith.
unfold nat_of_Z.
auto with zarith.
subst.
unfold nat_of_Z in *.
rewrite Nat2Z.id in Hnthi.
rewrite Hnth in Hnthi; inverts Hnthi.
auto.
Qed.

Lemma Qattr_full_P'_split:
forall vl1 vl2 idx cpn,
  1 <= OS_USER_MAX_EVENTS / 3 / (Int.unsigned cpn) ->
  Qattr_full_P' vl1 idx cpn ->
  V_QATTRpevent vl2 <> Some Vnull  ->
 Qattr_full_P' (vl1 ++ vl2::nil) idx cpn.
Proof.
introv Hcpn Hfull Hvp.
lets Hnth: nth_vallist_get_idx vl1 vl2 (nil:list vallist).
unfold Qattr_full_P' in *.
introv Hi Hnthi.
destruct Hi as (Hli & Hlr).
rewrite last_length in Hlr.
rewrite Nat2Z.inj_succ in Hlr.
eapply Zlt_succ_le in Hlr.
eapply Zle_lt_or_eq in Hlr.
rewrite <- nth_error_eq_nth_vallist in *.
assert (Hi: 0 <= i).
{
   eapply Z.le_trans; eauto.
   eapply Ztac.mul_le; auto with zarith.
   apply Int.unsigned_range_2.
}
destruct Hlr as [Hlr | Hlr].
eapply Hfull; eauto.
rewrite <- nth_error_eq_nth_vallist.
rewrite nth_error_app1 in Hnthi; auto with zarith.
unfold nat_of_Z.
auto with zarith.
subst.
unfold nat_of_Z in *.
rewrite Nat2Z.id in Hnthi.
rewrite Hnth in Hnthi; inverts Hnthi.
auto.
Qed.

Lemma getFreePos_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal getFreePos vl logicl getFreePosPre ct->
      Some r =
      BuildRetI os_internal getFreePos vl logicl getFreePosPost ct->
      exists t d1 d2 s,
        os_internal getFreePos = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
init spec.
inverts H2.
subst logicl.
rename v' into vi.
rename v'0 into tp.
rename v'2 into semvl.
rename v'3 into muxvl.
rename v'4 into mqvl.
rename v'5 into lg'.
rename v'6 into ier.
rename v'7 into domvl.
rename v'8 into domls.
rename v'9 into kcurd.
rename v'10 into cpn.
rename v'11 into lsem.
rename v'12 into lmux.
rename v'13 into lmq.
destruct H as (Hcd_pos & Hcd_lt).
rename H0 into Hrcpn.

assert (Heqf: Int.eq ($ OS_USER_MAX_EVENTS) ($ Int.min_signed) = false).
eapply int_min_neq_maxevents.
assert (Hdiveq: (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3) = $ (OS_USER_MAX_EVENTS / 3))).
  {  clear. lets Hrgn': usr_max_evts_rgn'.
      unfold Int.divs in *.
      rewrite zdiv_equiv in *; int auto.
  }
assert (Heqf': Int.eq ($ OS_USER_MAX_EVENTS / 3) ($ Int.min_signed) = false).
{ clear. lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  unfold nat_of_Z in *.
  unfold Int.eq.
  rewrite Int.unsigned_repr.
  2:{ split; solve_usr_max_evts_rgn. }
  destruct (zeq (OS_USER_MAX_EVENTS / 3) (Int.unsigned ($ Int.min_signed))); auto.
  change (Int.unsigned ($ Int.min_signed)) with 2147483648  in *.
  rewrite e in Hrgn4.
  false. auto with zarith.
}
assert (Hchg: Int.eq ($ 3) Int.zero ||
                Int.eq ($ OS_USER_MAX_EVENTS) ($ Int.min_signed) && 
                Int.eq ($ 3) Int.mone = false).
  { rewrite Heqf.
     change (Int.eq ($ 3) Int.zero || false && Int.eq ($ 3) Int.mone) with false.
     auto.
  }

hoare forward. (* assign i *)
assert (Hif_cond: tp = Int.zero \/ tp = Int.one \/ tp = ($ 2) \/
                                     ~(tp = Int.zero \/ tp = Int.one \/ tp = ($ 2))).
tauto.
destruct Hif_cond as [Htp_eq | [Htp_eq | [Htp_eq | Hif_false]]];
try subst tp.
(* ~(tp = Int.zero \/ tp = Int.one \/ tp = ($ 2)) *)
4 : { assert (Htp_range: tp <> Int.zero /\ tp <> Int.one /\ tp <> ($ 2)).
         { tauto. }
         destruct Htp_range as (Hif1 & Hif2 & Hif3).
         lets Heq1: Int.eq_false Hif1.
         lets Heq2: Int.eq_false Hif2.
         lets Heq3: Int.eq_false Hif3.
         hoare forward.
         pure_auto.
         change ($ 0) with Int.zero.
         rewrite Heq1.
         simpl val_inj.
         hoare unfold; tryfalse.
         eapply hoare_disj_afalseP_l_pre.
         hoare unfold.
         hoare forward.
         pure_auto.
         change ($ 1) with Int.one.
         rewrite Heq2.
         simpl val_inj.
         hoare unfold; tryfalse.
         eapply hoare_disj_afalseP_l_pre.
         hoare unfold.
         hoare forward.
         pure_auto.
         rewrite Heq3.
         simpl val_inj.
         hoare unfold; tryfalse.
         eapply hoare_disj_afalseP_l_pre.
         hoare unfold.
         mytac_getret 7%nat.
         hoare forward.
}
(*type = 0 *)
hoare forward.
2: {
(* instantiate (1:= Afalse). *)
eapply hoare_disj_afalseP_l_pre.
hoare unfold.
change (Int.eq Int.zero ($ 0)) with true in H.
simpl in H. destruct H; tryfalse.
}
change (Int.eq Int.zero ($ 0)) with true.
hoare unfold.

(* i ′ =ₑ ebinop odiv (ebinop odiv ′ OS_USER_MAX_EVENTS ′ 3)  ′ Core_partition_num × Domain2Index ′ [ksCurDomain ′];ₛ *)
unfold Adomain2index.
unfold Adomain2index'.
unfold ACorepartnum, ACorepartnum'.
unfold AKsCurDomain.
hoare unfold.

match goal with
 H: length domvl = ?len |- _ =>
 rename H into Hlen;
 assert (Hle_len: (Z.to_nat (Int.unsigned kcurd) < len)%nat)
 by auto with zarith end.
lets Hnth: Hle_len.
eapply pure_lib.nthval'_has_value in Hnth; eauto.
destruct Hnth as (rv_dom & Hnth & Hmat).

assert (Hif_cpn: Int.eq cpn Int.zero || Int.eq ($ OS_USER_MAX_EVENTS / 3) ($ Int.min_signed) &&
                                Int.eq cpn Int.mone = false).
  { rewrite Heqf'.
     destruct (Int.eq cpn Int.zero) eqn: eq1; try tauto.
     eapply sem_lab.semacc_int_eq_true in eq1; subst.
     change (Int.unsigned Int.zero) with 0 in *.
     false; auto with zarith.
  }

assert (Hdiv_rgn1: 1 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn
                                      <= 79).
{ eapply user_max_evts_div_cpn_rgn; eauto. }
assert (Hdom_lt: Int.unsigned rv_dom < Int.unsigned cpn).
{ eapply Hrcpn; eauto.
   eapply inline_bittblfunctions.nth_val'2nth_val; eauto.
}
assert (Hdom_lt': Int.unsigned rv_dom < 8).
{ auto with zarith. }
assert (Hdiv_rgn2: 0 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn
                                                * Int.unsigned rv_dom <= Int.max_unsigned).
{ conv_max_unsigned.
   split.
   eapply Ztac.mul_le; auto with zarith.
   apply Int.unsigned_range_2.
   eapply Z.le_trans with (m:= 79 * Int.unsigned rv_dom).
   eapply Zmult_le_compat_r; auto with zarith.
   apply Int.unsigned_range_2.
   auto with zarith.
}
assert (Hdiv_rgn2': 0 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn
                                                * Int.unsigned rv_dom <= 79).
{
   split.
   eapply Ztac.mul_le; auto with zarith.
   eapply Z.le_trans with (m:= OS_USER_MAX_EVENTS / 3).
   eapply Z.lt_le_incl.
   eapply Z_div_mul_lt; auto with zarith.
   solve_usr_max_evts_rgn.
}

assert (Heqi: (Int.unsigned (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn) rv_dom)) 
                           = OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned rv_dom).
{ rewrite <- Int_divu_eq_divs'; auto with zarith.
   unfold Int.mul, Int.divu in *.
   repeat rewrite Int.unsigned_repr; auto;
   try solve_usr_max_evts_rgn; try conv_max_unsigned.
   rewrite Int.unsigned_repr; auto; try solve_usr_max_evts_rgn.
}
assert (Heqi_suc: Int.unsigned
  (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn) (rv_dom +ᵢ  Int.one)) = 
  OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned rv_dom + 1)).
{ rewrite <- Int_divu_eq_divs'; auto with zarith.
   unfold Int.mul, Int.divu, Int.add in *.
   change (Int.unsigned Int.one) with 1.
   repeat rewrite Int.unsigned_repr; auto;
   try solve_usr_max_evts_rgn; try conv_max_unsigned.
   rewrite Int.unsigned_repr; auto; try solve_usr_max_evts_rgn.
}
assert (Hsuc_rgn: 0 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned rv_dom + 1) <=
Int.max_unsigned).
{  try solve_usr_max_evts_rgn. }
assert (Hsuc_rgn': 1 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned rv_dom + 1)
                                       <=  OS_USER_MAX_EVENTS / 3).
{ eapply user_max_evts_part_succ_rgn; eauto with zarith. }

hoare forward.
rewrite Hchg; simpl val_inj; pure_auto.
rewrite Hchg; simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hchg; simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
rewrite Hchg; simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.

(*WHILE (ebinop odiv (ebinop odiv ′ OS_USER_MAX_EVENTS ′ 3)
         Core_partition_num ′ × (Domain2Index ′ [ksCurDomain ′] +ₑ ′ 1) *)

(*1: remember irrelevant sep-conjunctions*)
hoare_lifts_trms_pre (ASeminfo, Alvarmapsto i, Domain2Index, ksCurDomain, Core_partition_num).
hoare remember (1 :: 2 :: 3 :: 4 :: 5 :: nil)%nat pre.

  (*2: get the while loop inv into the pre-condition,
    so the pre-condition after the while statement
    can be correctly instantiated
   *)

destruct lsem as (lsem_b & lsem_i).

eapply backward_rule1 with (p := (*below is the loop inv*)
     (EX i p vl vll1 vll2 (* lsem_b lsem_i *),
      LV os_code_defs.i @ Int32u |-> (V$ (Z.of_nat i)) **
      GAarray Domain2Index (Tarray char_t (Z.to_nat DOMAIN_SIZE)) domvl **
      GV ksCurDomain @ long |-> Vint32 kcurd **
      GV Core_partition_num @ long |-> Vint32 cpn **
      GV Sem_info @ sem_info_t ∗ |-> Vptr (lsem_b, lsem_i) **
      Aarray_new (lsem_b, lsem_i) (Tarray sem_info_t i) vll1 **
      Astruct (lsem_b,(lsem_i+ᵢ  $ Z.of_nat (i * (typelen sem_info_t)))) sem_info_t vl **
      Aarray_new (lsem_b, (lsem_i+ᵢ  $ Z.of_nat ( (S i) * (typelen sem_info_t))))
                            (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S i)))) vll2 **
      [| new_array_type_vallist_match sem_info_t semvl |] **
      [| length semvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
      [| semvl = vll1 ++ (vl::vll2) |] ** 
      [| length vll1 = i /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S i)) |] **
      [| Z.of_nat(S i) <= (OS_USER_MAX_EVENTS / 3) |] **
      [| Z.of_nat(S i) <= (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) *
                                        (Int.unsigned rv_dom + 1)) |] **
      [| (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) *
                                        (Int.unsigned rv_dom)) <= Z.of_nat i |] **
      [| Seminfo_full_P' vll1 rv_dom cpn |] ** (* use for get out of the while loop *)
      [| V_OSSINFOPevent vl = Some p /\ isptr p |] **
      H9) \\//
    (  EX vll1 vll2,
        LV os_code_defs.i @ Int32u |-> 
              Vint32 (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn) 
                                              (Int.add rv_dom Int.one)) **
        GAarray Domain2Index (Tarray char_t (Z.to_nat DOMAIN_SIZE)) domvl **
        GV ksCurDomain @ long |-> Vint32 kcurd **
        GV Core_partition_num @ long |-> Vint32 cpn **
        ASeminfo (lsem_b, lsem_i) semvl **
        [|vll1 ++ vll2 = semvl|] **
        [|length vll1 = ∘ (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) *
                                        (Int.unsigned rv_dom + 1))|] **
        [| Seminfo_full_P' vll1 rv_dom cpn  |] ** H9
      )
    ).
introv Hsat.
left.
eapply ASeminfo_unfold_any_idx_frm
   with (idx:= Z.to_nat (Int.unsigned 
                                             (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn) rv_dom))) in Hsat.
sep normal in Hsat.
sep destruct Hsat.
sep split in Hsat.
subst semvl.
match goal with H: new_array_type_vallist_match sem_info_t _ |- _ =>
lets Hgetp: new_array_type_vallist_match_sem_getp H end.
destruct Hgetp as (p & Hvp & Hptr).
sep pauto; eauto.
rewrite Z2Nat.id.
rewrite Int.repr_unsigned; auto.
apply Int.unsigned_range_2.
eapply Seminfo_full_P'_left_start; eauto.
rewrite <- Heqi; auto.
rewrite Heqi; auto with zarith.
rewrite Z.mul_add_distr_l.
rewrite Heqi.
rewrite <- Z2Nat.inj_succ; auto with zarith.
unfold ASeminfo in Hsat.
sep normal in Hsat.
sep destruct Hsat.
sep split in Hsat.
match goal with
 H: new_array_type_vallist_match sem_info_t _ /\ _ |- _ =>
 destruct H as (_ & Hlen_vl); rewrite Hlen_vl end.
eapply OSMutex_common.intlt2nat.
rewrite Heqi.
eapply Z_div_mul_lt; auto with zarith.


 (*3: apply the 'seq_rule' to get the while statement
    off the remaining statements, then apply the 'while_rule'
   *)
eapply seq_rule.

(*4: prove the condition expression of while is legal *)
eapply while_rule with (tp := Int32u).
(*prove the condition expression of while is legal *)
introv Hsat.
(*2 cases*)
destruct Hsat as [Hsat | Hsat].
symbolic_execution; try rewrite Hchg.
simpl val_inj; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hnth; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.
pure_auto.
symbolic_execution; try rewrite Hchg.
simpl val_inj; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hnth; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.
pure_auto.
(*Aistrue (ebinop odiv (ebinop odiv ′ OS_USER_MAX_EVENTS ′ 3)
         Core_partition_num ′ × (Domain2Index ′ [ksCurDomain ′] +ₑ ′ 1 >ₑ os_code_defs.i ′)*)

(*5: the cond-expr of while hold implies the left part
    of the loop-inv*)
  eapply backward_rule1 with ( p:= (
     EX i p vl vll1 vll2 (* lsem_b lsem_i *),
      LV os_code_defs.i @ Int32u |-> (V$ (Z.of_nat i)) **
      GAarray Domain2Index (Tarray char_t (Z.to_nat DOMAIN_SIZE)) domvl **
      GV ksCurDomain @ long |-> Vint32 kcurd **
      GV Core_partition_num @ long |-> Vint32 cpn **
      GV Sem_info @ sem_info_t ∗ |-> Vptr (lsem_b, lsem_i) **
      Aarray_new (lsem_b, lsem_i) (Tarray sem_info_t i) vll1 **
      Astruct (lsem_b,(lsem_i+ᵢ  $ Z.of_nat (i * (typelen sem_info_t)))) sem_info_t vl **
      Aarray_new (lsem_b, (lsem_i+ᵢ  $ Z.of_nat ( (S i) * (typelen sem_info_t))))
                            (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S i)))) vll2 **
      [| new_array_type_vallist_match sem_info_t semvl |] **
      [| length semvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
      [| semvl = vll1 ++ (vl::vll2) |] ** 
      [| length vll1 = i /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S i)) |] **
      [| Z.of_nat(S i) <= (OS_USER_MAX_EVENTS / 3) |] **
      [| Z.of_nat(S i) <= (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) *
                                        (Int.unsigned rv_dom + 1)) |] **
      [| (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) *
                                        (Int.unsigned rv_dom)) <= Z.of_nat i |] **
      [| Seminfo_full_P' vll1 rv_dom cpn |] ** (* use for get out of the while loop *)
      [| V_OSSINFOPevent vl = Some p /\ isptr p |] **
      H9
)).
introv Hsat.
destruct Hsat as (Hsat & Histrue).
destruct Hsat as [Hsat | Hsat]. (*2 cases*)
(*case 1*)
sep destruct Hsat.
sep eexists.
sep cancel 1%nat 1%nat.
(*case 2*)
sep destruct Hsat.
lets Hcp: aconj_intro Hsat Histrue;
eapply sep_aconj_r_aistrue_to_astar in Hcp; eauto.
2:{ 
clear Hsat Hcp. 
introv Hsat. subst.
sep get rv; try rewrite Hchg.
simpl val_inj; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hnth; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.
pure_auto.
}
rewrite Hchg in Hcp; simpl val_inj in Hcp.
rewrite Hnth in Hcp.
rewrite Hdiveq in Hcp; rewrite Hif_cpn in Hcp; simpl val_inj in Hcp.
clear -Hcp.
sep_lifts_trms_in Hcp (val_inj).
eapply sep_pure_split in Hcp.
destruct Hcp as (Hf & Hcp).
change ($ 1) with Int.one in Hf.
rewrite sem_common.sempend_ltu_ass1 in Hf.
simpl in Hf.
destruct Hf; tryfalse.

(*If ((Sem_info ′ [os_code_defs.i ′]) → pevent ==ₑ ′ 0)*)
hoare_split_pure_all.
match goal with
H : Seminfo_full_P' _ _ _, 
H' : V_OSSINFOPevent _ = Some _ /\ isptr _ |- _ =>
rename H into Hfull; destruct H' as (Hvp & Hptr)
end.
match goal with
| |- {| _, _, _, _, _, _ |} |- _ {{ ?P }} _ {{ _ }} =>
assert (Hgetp: P
       ==> Rv (efield (Sem_info ′ [i ′]) pevent) ==ₑ NULL @ Int32 == val_inj(val_eq v'0 Vnull))
end.
{
  introv Hsat.
  eapply bop_rv.
  { sep_get_rv_array_struct.
    eapply new_array_type_vallist_match_split; eauto.
  }
  sep get rv.
  unfold bop_eval.
  unfold V_OSSINFOPevent in Hvp. eapply nth_val_nth_val'_some_eq in Hvp.
  rewrite Hvp.
  auto.
  destruct Hptr as [Hvnull | ((pb & pi) & Hp)]; simpljoin; pure_auto.
  simpl. auto.
}

(* actual start if *)
hoare forward.
eapply ift_rule_general.
intros.
eexists.
eapply Hgetp.
sep pauto.
sep pauto.

(* if true *)
eapply backward_rule1.
introv Hsat.
eapply sep_aconj_r_aistrue_to_astar in Hsat; eauto.

mytac_getret 1%nat.
instantiate (1:= Afalse).
clear Hgetp.
hoare unfold.
change ($ 0) with Int.zero.
hoare forward. (*RETURN i*)
sep cancel p_local.
sep cancel APthreadMutex.
sep cancel AMqAttr.
eapply ASeminfo_select_sn_ex_strong_frm.
sep auto.
pure_auto.
2:{ rewrite Hnth; eauto. }
rewrite <- Byte.unsigned_repr_eq.
match goal with
H: Z.of_nat (S (length _)) <= _ ,
H':  Z.of_nat (S (length _)) <= _,
H'': _ <= Z.of_nat (length _) |- _ =>
rename H into Hslen; rename H' into Hslen';
rename H'' into Hlen_ge end.
assert (Hieq: (Int.unsigned ($ Z.of_nat (length v'3))) = Z.of_nat (length v'3)).
{ rewrite Int.unsigned_repr; auto with zarith.
  (*  split; auto with zarith.
   solve_usr_max_evts_rgn. *)
}
rewrite Hieq.
assert (Hv: (Byte.unsigned (Byte.repr (Z.of_nat (length v'3)))) = Z.of_nat (length v'3)).
{
  eapply Byte.unsigned_repr.
  change Byte.max_unsigned with 255.
  split; try solve_usr_max_evts_rgn.
}
rewrite Hv.
unfold nth_Seminfo_free_P'.
exists v'2.
splits.
split; auto with zarith.
unfold nat_of_Z in *.
rewrite nat_of_Z_of_nat.
apply nth_vallist_get_idx.
rewrite Hvp.
match goal with H: val_inj (val_eq _ Vnull) <> Vint32 Int.zero |- _ => rename H into Hif end.
destruct Hptr as [Hvnull | ((pb & pi) & Hp)]; simpljoin; simpl in Hif; tryfalse.

(* if false *)
hoare forward.
eapply backward_rule1.
introv Hsat.
eapply sep_aconj_r_aisfalse_to_astar in Hsat; eauto.
(* ++ i ′ *)
clear Hgetp.
hoare_lifts_trms_pre val_inj.
eapply pure_split_rule'; introv Hval_inj.
destruct Hptr as [Hvnull | ((pb & pi) & Hp)]; subst v'0; simpl in Hval_inj; destruct Hval_inj; tryfalse.
match goal with
H: Z.of_nat (S _) <= _ ,
H':  Z.of_nat (S _) <= _,
H'': _ <= Z.of_nat _ |- _ =>
rename H into Hslen; rename H' into Hslen';
rename H'' into Hlen_ge end.
assert (Hsuc: ($ Z.of_nat v' +ᵢ  $ 1) = ($ (Z.of_nat (S v')))).
{ simpljoin.
   clear -Hslen.
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  int auto.
}
lets Hcond: z_split Hslen'.
destruct Hcond as [Hc1 | Hc2].
(* case 1*)
eapply backward_rule1.
introv Hsat.
eapply ASeminfo_select_sn_ex_strong.
sep eexists.
sep split; eauto.
sep pauto.
subst.
hoare forward.
rewrite Hsuc in *; rewrite Hc1 in *.
eapply adisj_intro.
right.
exists (v'3 ++ (v'2 :: nil)) v'4.
rewrite <- list_cons_assoc.
sep pauto.
match goal with | |- Vint32 ?v1 = Vint32 ?v2 => assert (Heqv: v1 = v2) end.
eapply unsigned_inj.
rewrite Int.unsigned_repr.
rewrite Heqi_suc; auto.
auto.
rewrite Heqv; auto.
eapply Seminfo_full_P'_split; eauto.
rewrite Hvp; auto.
rewrite last_length.
rewrite <- Hc1.
unfold nat_of_Z; rewrite Nat2Z.id; auto.
(* case 2 *)
destruct v'4.
{
  false.
  match goal with H: length _ = _ /\ length _ = _ |- _ => destruct H as (Hlen_vl1 & Hlen_vl2) end.
  subst semvl.
  clear -Hlen_vl2 Hc2 Hsuc_rgn'.
  change (length nil) with 0%nat in Hlen_vl2.
  unfold nat_of_Z in Hlen_vl2.
  assert (Z.to_nat (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S v')) 
                  = (Z.to_nat (OS_USER_MAX_EVENTS / 3) - Z.to_nat (Z.of_nat (S v')))%nat).
  eapply Z2Nat.inj_sub; apply Nat2Z.is_nonneg.
  rewrite H in Hlen_vl2. clear H.
  rewrite Nat.eq_sym_iff in Hlen_vl2.
  rewrite NPeano.Nat.sub_0_le in Hlen_vl2.
  auto with zarith.
}
eapply backward_rule1.
introv Hsat.
eapply ASeminfo_select_sn_ex_strong.
sep eexists.
sep split; eauto.
sep pauto.
subst.
hoare forward.
rewrite Hsuc in *.
eapply adisj_intro.
left.
assert (Hvl: v'3 ++ v'2 :: v :: v'4 = (v'3 ++ (v'2 :: nil)) ++ (v :: v'4)).
{
simpl; rewrite app_assoc_reverse.
simpl. auto.
}
rewrite Hvl in *.
match goal with H: _ |= _ |- _ => rename H into Hsat; sep_lifts_trms_in Hsat ASeminfo end.
eapply ASeminfo_split_frm in Hsat.
sep destruct Hsat.
sep_lifts_trms_in Hsat (_N_ 5 , _N_ 6, _N_ 7).
eapply sep_pure_split in Hsat; destruct Hsat as (Hmat_suc & Hsat).
eapply sep_pure_split in Hsat; destruct Hsat as (Hlen_all & Hsat).
eapply sep_pure_split in Hsat; destruct Hsat as (Hlen_suc & Hsat).
destruct Hlen_suc as (Hlen_l & Hlen_r).
rewrite last_length in Hlen_l.
subst.
lets Hgetp: new_array_type_vallist_match_sem_getp Hmat_suc.
destruct Hgetp as (p' & Hvp' & Hptr').
do 3 eexists.
exists (v'3 ++ (v'2 :: nil)) v'4.
sep eexists.
sep cancel Aarray_new.
sep cancel Astruct.
sep cancel Aarray_new.
sep auto.
rewrite Hvp'; eauto.
eapply Seminfo_full_P'_split; eauto.
rewrite Hvp; auto.
eapply Z.le_trans; eauto.
rewrite <- Nat2Z.inj_le; auto with zarith.
clear -Hc2.
eapply Zlt_le_succ in Hc2.
eapply Z.le_trans; eauto.
rewrite <- Nat2Z.inj_succ; auto with zarith.
rewrite last_length; auto.
(* end of while Aistrue*)
(* start of while Aisfalse *)
mytac_getret 2%nat.
eapply backward_rule1.
introv Hsat.
destruct Hsat as (Hsat & Hisfalse).
destruct Hsat as [Hsat | Hsat].
(* false case *)
false.
sep destruct Hsat.
lets Hcp: aconj_intro Hsat Hisfalse;
eapply sep_aconj_r_aisfalse_to_astar in Hcp; eauto.
2:{
clear Hsat Hcp. 
introv Hsat. subst.
sep get rv; try rewrite Hchg.
simpl val_inj; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hnth; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.
pure_auto.
}
rewrite Hchg in Hcp; simpl val_inj in Hcp.
rewrite Hnth in Hcp.
rewrite Hdiveq in Hcp; rewrite Hif_cpn in Hcp; simpl val_inj in Hcp.
clear -Hcp Heqi_suc.
sep_lifts_trms_in Hcp (val_inj).
eapply sep_pure_split in Hcp.
destruct Hcp as (Hf & Hcp).
change ($ 1) with Int.one in Hf.
destruct (Int.ltu ($ Z.of_nat x)
           (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn)
              (rv_dom +ᵢ  Int.one))) eqn: eq1;
simpl in Hf; destruct Hf; tryfalse.
rewrite Intlt_false_is_Zge in eq1.
rewrite Heqi_suc in eq1.
sep split in Hcp.
simpljoin.
rewrite Int.unsigned_repr in eq1; auto with zarith.
split; try solve_usr_max_evts_rgn.
(* actual Aisfalse *)
lets Hcp: aconj_intro Hsat Hisfalse;
eapply sep_aconj_r_aisfalse_to_astar in Hcp; eauto.
{
clear Hsat Hcp. 
introv Hsat.
sep destruct Hsat.
subst.
sep get rv; try rewrite Hchg.
simpl val_inj; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hnth; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.
pure_auto.
}
hoare unfold.
hoare forward. (* RETURN ′ 255 *)
eauto.
eauto.
eauto.

(*type = 1 *)
assert (Hif_false: Int.eq Int.one ($ 0) = false).
{ clear.  int auto. }
hoare forward.
pure_auto.
rewrite Hif_false.
simpl val_inj.
hoare unfold; tryfalse.
eapply hoare_disj_afalseP_l_pre.
hoare unfold.
clear H.
hoare forward.
2: {
instantiate (1:= Afalse).
eapply hoare_disj_afalseP_l_pre.
hoare unfold.
change (Int.eq Int.one ($ 2)) with false in H.
simpl in H. destruct H; tryfalse.
}
change (Int.eq Int.one ($ 1)) with true.
hoare unfold.

(* i ′ =ₑ ebinop odiv (ebinop odiv ′ OS_USER_MAX_EVENTS ′ 3)  ′ Core_partition_num × Domain2Index ′ [ksCurDomain ′];ₛ *)
unfold Adomain2index.
unfold Adomain2index'.
unfold ACorepartnum, ACorepartnum'.
unfold AKsCurDomain.
hoare unfold.

match goal with
 H: length domvl = ?len |- _ =>
 rename H into Hlen;
 assert (Hle_len: (Z.to_nat (Int.unsigned kcurd) < len)%nat)
 by auto with zarith end.
lets Hnth: Hle_len.
eapply pure_lib.nthval'_has_value in Hnth; eauto.
destruct Hnth as (rv_dom & Hnth & Hmat).

assert (Hif_cpn: Int.eq cpn Int.zero || Int.eq ($ OS_USER_MAX_EVENTS / 3) ($ Int.min_signed) &&
                                Int.eq cpn Int.mone = false).
  { rewrite Heqf'.
     destruct (Int.eq cpn Int.zero) eqn: eq1; try tauto.
     eapply sem_lab.semacc_int_eq_true in eq1; subst.
     change (Int.unsigned Int.zero) with 0 in *.
     false; auto with zarith.
  }

assert (Hdiv_rgn1: 1 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn
                                      <= 79).
{ eapply user_max_evts_div_cpn_rgn; eauto. }
assert (Hdom_lt: Int.unsigned rv_dom < Int.unsigned cpn).
{ eapply Hrcpn; eauto.
   eapply inline_bittblfunctions.nth_val'2nth_val; eauto.
}
assert (Hdom_lt': Int.unsigned rv_dom < 8).
{ auto with zarith. }
assert (Hdiv_rgn2: 0 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn
                                                * Int.unsigned rv_dom <= Int.max_unsigned).
{ conv_max_unsigned.
   split.
   eapply Ztac.mul_le; auto with zarith.
   apply Int.unsigned_range_2.
   eapply Z.le_trans with (m:= 79 * Int.unsigned rv_dom).
   eapply Zmult_le_compat_r; auto with zarith.
   apply Int.unsigned_range_2.
   auto with zarith.
}
assert (Hdiv_rgn2': 0 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn
                                                * Int.unsigned rv_dom <= 79).
{
   split.
   eapply Ztac.mul_le; auto with zarith.
   eapply Z.le_trans with (m:= OS_USER_MAX_EVENTS / 3).
   eapply Z.lt_le_incl.
   eapply Z_div_mul_lt; auto with zarith.
   solve_usr_max_evts_rgn.
}

assert (Heqi: (Int.unsigned (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn) rv_dom)) 
                           = OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned rv_dom).
{ rewrite <- Int_divu_eq_divs'; auto with zarith.
   unfold Int.mul, Int.divu in *.
   repeat rewrite Int.unsigned_repr; auto;
   try solve_usr_max_evts_rgn; try conv_max_unsigned.
   rewrite Int.unsigned_repr; auto; try solve_usr_max_evts_rgn.
}
assert (Heqi_suc: Int.unsigned
  (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn) (rv_dom +ᵢ  Int.one)) = 
  OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned rv_dom + 1)).
{ rewrite <- Int_divu_eq_divs'; auto with zarith.
   unfold Int.mul, Int.divu, Int.add in *.
   change (Int.unsigned Int.one) with 1.
   repeat rewrite Int.unsigned_repr; auto;
   try solve_usr_max_evts_rgn; try conv_max_unsigned.
   rewrite Int.unsigned_repr; auto; try solve_usr_max_evts_rgn.
}
assert (Hsuc_rgn: 0 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned rv_dom + 1) <=
Int.max_unsigned).
{  try solve_usr_max_evts_rgn. }
assert (Hsuc_rgn': 1 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned rv_dom + 1)
                                       <=  OS_USER_MAX_EVENTS / 3).
{ eapply user_max_evts_part_succ_rgn; eauto with zarith. }

hoare forward.
rewrite Hchg; simpl val_inj; pure_auto.
rewrite Hchg; simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hchg; simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
rewrite Hchg; simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.

(*WHILE (ebinop odiv (ebinop odiv ′ OS_USER_MAX_EVENTS ′ 3)
         Core_partition_num ′ × (Domain2Index ′ [ksCurDomain ′] +ₑ ′ 1) *)

(*1: remember irrelevant sep-conjunctions*)
hoare_lifts_trms_pre (APthreadMutex, Alvarmapsto i, Domain2Index, ksCurDomain, Core_partition_num).
hoare remember (1 :: 2 :: 3 :: 4 :: 5 :: nil)%nat pre.

  (*2: get the while loop inv into the pre-condition,
    so the pre-condition after the while statement
    can be correctly instantiated
   *)

destruct lmux as (lmux_b & lmux_i).

eapply backward_rule1 with (p := (*below is the loop inv*)
     (EX i p vl vll1 vll2 (* lmux_b lmux_i *),
      LV os_code_defs.i @ Int32u |-> (V$ (Z.of_nat i)) **
      GAarray Domain2Index (Tarray char_t (Z.to_nat DOMAIN_SIZE)) domvl **
      GV ksCurDomain @ long |-> Vint32 kcurd **
      GV Core_partition_num @ long |-> Vint32 cpn **
      GV Pthread_Mutex @ pthread_mutex_info_t ∗ |-> Vptr (lmux_b, lmux_i) **
      Aarray_new (lmux_b, lmux_i) (Tarray pthread_mutex_info_t i) vll1 **
      Astruct (lmux_b,(lmux_i+ᵢ  $ Z.of_nat (i * (typelen pthread_mutex_info_t)))) pthread_mutex_info_t vl **
      Aarray_new (lmux_b, (lmux_i+ᵢ  $ Z.of_nat ( (S i) * (typelen pthread_mutex_info_t)))) (Tarray pthread_mutex_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S i)))) vll2 **
      [| new_array_type_vallist_match pthread_mutex_info_t muxvl |] **
      [| length muxvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
      [| muxvl = vll1 ++ (vl::vll2) |] ** 
      [| length vll1 = i /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S i)) |] **
      [| Z.of_nat(S i) <= OS_USER_MAX_EVENTS / 3 |] **
      [| Z.of_nat(S i) <= (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) *
                                        (Int.unsigned rv_dom + 1)) |] **
      [| (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) *
                                        (Int.unsigned rv_dom)) <= Z.of_nat i |] **
      [| PthreadMutex_full_P' vll1 rv_dom cpn |] ** (* use for get out of the while loop *)
      [| V_OSMUXINFOPevent vl = Some p /\ isptr p |] **
      H9) \\//
    (  EX vll1 vll2,
        LV os_code_defs.i @ Int32u |-> 
              Vint32 (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn) 
                                              (Int.add rv_dom Int.one)) **
        GAarray Domain2Index (Tarray char_t (Z.to_nat DOMAIN_SIZE)) domvl **
        GV ksCurDomain @ long |-> Vint32 kcurd **
        GV Core_partition_num @ long |-> Vint32 cpn **
        APthreadMutex (lmux_b, lmux_i) muxvl **
        [|vll1 ++ vll2 = muxvl|] **
        [|length vll1 = ∘ (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) *
                                        (Int.unsigned rv_dom + 1))|] **
        [| PthreadMutex_full_P' vll1 rv_dom cpn  |] ** H9
      )
    ).
introv Hsat.
left.
eapply APthreadMutex_unfold_any_idx_frm
   with (idx:= Z.to_nat (Int.unsigned 
                                             (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn) rv_dom))) in Hsat.
sep normal in Hsat.
sep destruct Hsat.
sep split in Hsat.
subst muxvl.
match goal with H: new_array_type_vallist_match pthread_mutex_info_t _ |- _ =>
lets Hgetp: new_array_type_vallist_match_mux_getp H end.
destruct Hgetp as (p & Hvp & Hptr).
sep pauto; eauto.
rewrite Z2Nat.id.
rewrite Int.repr_unsigned; auto.
apply Int.unsigned_range_2.
eapply PthreadMutex_full_P'_left_start; eauto.
rewrite <- Heqi; auto.
rewrite Heqi; auto with zarith.
rewrite Z.mul_add_distr_l.
rewrite Heqi.
rewrite <- Z2Nat.inj_succ; auto with zarith.
unfold APthreadMutex in Hsat.
sep normal in Hsat.
sep destruct Hsat.
sep split in Hsat.
match goal with
 H: new_array_type_vallist_match pthread_mutex_info_t _ /\ _ |- _ =>
 destruct H as (_ & Hlen_vl); rewrite Hlen_vl end.
eapply OSMutex_common.intlt2nat.
rewrite Heqi.
eapply Z_div_mul_lt; auto with zarith.


 (*3: apply the 'seq_rule' to get the while statement
    off the remaining statements, then apply the 'while_rule'
   *)
eapply seq_rule.

(*4: prove the condition expression of while is legal *)
eapply while_rule with (tp := Int32u).
(*prove the condition expression of while is legal *)
introv Hsat.
(*2 cases*)
destruct Hsat as [Hsat | Hsat].
symbolic_execution; try rewrite Hchg.
simpl val_inj; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hnth; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.
pure_auto.
symbolic_execution; try rewrite Hchg.
simpl val_inj; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hnth; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.
pure_auto.
(*Aistrue (ebinop odiv (ebinop odiv ′ OS_USER_MAX_EVENTS ′ 3)
         Core_partition_num ′ × (Domain2Index ′ [ksCurDomain ′] +ₑ ′ 1 >ₑ os_code_defs.i ′)*)

(*5: the cond-expr of while hold implies the left part
    of the loop-inv*)
  eapply backward_rule1 with ( p:= (
     EX i p vl vll1 vll2(*  lmux_b lmux_i *),
      LV os_code_defs.i @ Int32u |-> (V$ (Z.of_nat i)) **
      GAarray Domain2Index (Tarray char_t (Z.to_nat DOMAIN_SIZE)) domvl **
      GV ksCurDomain @ long |-> Vint32 kcurd **
      GV Core_partition_num @ long |-> Vint32 cpn **
      GV Pthread_Mutex @ pthread_mutex_info_t ∗ |-> Vptr (lmux_b, lmux_i) **
      Aarray_new (lmux_b, lmux_i) (Tarray pthread_mutex_info_t i) vll1 **
      Astruct (lmux_b,(lmux_i+ᵢ  $ Z.of_nat (i * (typelen pthread_mutex_info_t)))) pthread_mutex_info_t vl **
      Aarray_new (lmux_b, (lmux_i+ᵢ  $ Z.of_nat ( (S i) * (typelen pthread_mutex_info_t)))) (Tarray pthread_mutex_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S i)))) vll2 **
      [| new_array_type_vallist_match pthread_mutex_info_t muxvl |] **
      [| length muxvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
      [| muxvl = vll1 ++ (vl::vll2) |] ** 
      [| length vll1 = i /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S i)) |] **
      [| Z.of_nat(S i) <= OS_USER_MAX_EVENTS / 3 |] **
      [| Z.of_nat(S i) <= (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) *
                                        (Int.unsigned rv_dom + 1)) |] **
      [| (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) *
                                        (Int.unsigned rv_dom)) <= Z.of_nat i |] **
      [| PthreadMutex_full_P' vll1 rv_dom cpn |] ** (* use for get out of the while loop *)
      [| V_OSMUXINFOPevent vl = Some p /\ isptr p |] **
      H9
)).
introv Hsat.
destruct Hsat as (Hsat & Histrue).
destruct Hsat as [Hsat | Hsat]. (*2 cases*)
(*case 1*)
sep destruct Hsat.
sep eexists.
sep cancel 1%nat 1%nat.
(*case 2*)
sep destruct Hsat.
lets Hcp: aconj_intro Hsat Histrue;
eapply sep_aconj_r_aistrue_to_astar in Hcp; eauto.
2:{ 
clear Hsat Hcp. 
introv Hsat. subst.
sep get rv; try rewrite Hchg.
simpl val_inj; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hnth; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.
pure_auto.
}
rewrite Hchg in Hcp; simpl val_inj in Hcp.
rewrite Hnth in Hcp.
rewrite Hdiveq in Hcp; rewrite Hif_cpn in Hcp; simpl val_inj in Hcp.
clear -Hcp.
sep_lifts_trms_in Hcp (val_inj).
eapply sep_pure_split in Hcp.
destruct Hcp as (Hf & Hcp).
change ($ 1) with Int.one in Hf.
rewrite sem_common.sempend_ltu_ass1 in Hf.
simpl in Hf.
destruct Hf; tryfalse.

(*If ((Pthread_Mutex ′ [os_code_defs.i ′]) → pevent ==ₑ ′ 0)*)
hoare_split_pure_all.
match goal with
H : PthreadMutex_full_P' _ _ _, 
H' : V_OSMUXINFOPevent _ = Some _ /\ isptr _ |- _ =>
rename H into Hfull; destruct H' as (Hvp & Hptr)
end.
match goal with
| |- {| _, _, _, _, _, _ |} |- _ {{ ?P }} _ {{ _ }} =>
assert (Hgetp: P
       ==> Rv (efield (Pthread_Mutex ′ [i ′]) pevent) ==ₑ NULL @ Int32 == val_inj(val_eq v'0 Vnull))
end.
{
  introv Hsat.
  eapply bop_rv.
  { sep_get_rv_array_struct.
    eapply new_array_type_vallist_match_split1; eauto.
  }
  sep get rv.
  unfold bop_eval.
  unfold V_OSMUXINFOPevent in Hvp. eapply nth_val_nth_val'_some_eq in Hvp.
  rewrite Hvp.
  auto.
  destruct Hptr as [Hvnull | ((pb & pi) & Hp)]; simpljoin; pure_auto.
  simpl. auto.
}

(* actual start if *)
hoare forward.
eapply ift_rule_general.
intros.
eexists.
eapply Hgetp.
sep pauto.
sep pauto.

(* if true *)
eapply backward_rule1.
introv Hsat.
eapply sep_aconj_r_aistrue_to_astar in Hsat; eauto.

mytac_getret 3%nat.
instantiate (1:= Afalse).
clear Hgetp.
hoare unfold.
change ($ 0) with Int.zero.
hoare forward. (*RETURN i*)
sep cancel p_local.
sep cancel ASeminfo.
sep cancel AMqAttr.
eapply APthreadMutex_select_sn_ex_strong_frm.
sep auto.
pure_auto.
2:{ rewrite Hnth; eauto. }
rewrite <- Byte.unsigned_repr_eq.
match goal with
H: Z.of_nat (S (length _)) <= _ ,
H':  Z.of_nat (S (length _)) <= _,
H'': _ <= Z.of_nat (length _) |- _ =>
rename H into Hslen; rename H' into Hslen';
rename H'' into Hlen_ge end.
assert (Hieq: (Int.unsigned ($ Z.of_nat (length v'3))) = Z.of_nat (length v'3)).
{ rewrite Int.unsigned_repr; auto with zarith.
}
rewrite Hieq.
assert (Hv: (Byte.unsigned (Byte.repr (Z.of_nat (length v'3)))) = Z.of_nat (length v'3)).
{
  eapply Byte.unsigned_repr.
  change Byte.max_unsigned with 255.
  split; try solve_usr_max_evts_rgn.
}
rewrite Hv.
unfold nth_PthreadMutex_free_P'.
exists v'2.
splits.
split; auto with zarith.
unfold nat_of_Z in *.
rewrite nat_of_Z_of_nat.
apply nth_vallist_get_idx.
rewrite Hvp.
match goal with H: val_inj (val_eq _ Vnull) <> Vint32 Int.zero |- _ => rename H into Hif end.
destruct Hptr as [Hvnull | ((pb & pi) & Hp)]; simpljoin; simpl in Hif; tryfalse.

(* if false *)
hoare forward.
eapply backward_rule1.
introv Hsat.
eapply sep_aconj_r_aisfalse_to_astar in Hsat; eauto.
(* ++ i ′ *)
clear Hgetp.
hoare_lifts_trms_pre val_inj.
eapply pure_split_rule'; introv Hval_inj.
destruct Hptr as [Hvnull | ((pb & pi) & Hp)]; subst v'0; simpl in Hval_inj; destruct Hval_inj; tryfalse.
match goal with
H: Z.of_nat (S _) <= _ ,
H':  Z.of_nat (S _) <= _,
H'': _ <= Z.of_nat _ |- _ =>
rename H into Hslen; rename H' into Hslen';
rename H'' into Hlen_ge end.
assert (Hsuc: ($ Z.of_nat v' +ᵢ  $ 1) = ($ (Z.of_nat (S v')))).
{ simpljoin.
   clear -Hslen.
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  int auto.
}
lets Hcond: z_split Hslen'.
destruct Hcond as [Hc1 | Hc2].
(* case 1*)
eapply backward_rule1.
introv Hsat.
eapply APthreadMutex_select_sn_ex_strong.
sep eexists.
sep split; eauto.
sep pauto.
subst.
hoare forward.
rewrite Hsuc in *; rewrite Hc1 in *.
eapply adisj_intro.
right.
exists (v'3 ++ (v'2 :: nil)) v'4.
rewrite <- list_cons_assoc.
sep pauto.
match goal with | |- Vint32 ?v1 = Vint32 ?v2 => assert (Heqv: v1 = v2) end.
eapply unsigned_inj.
rewrite Int.unsigned_repr.
rewrite Heqi_suc; auto.
auto.
rewrite Heqv; auto.
eapply PthreadMutex_full_P'_split; eauto.
rewrite Hvp; auto.
rewrite last_length.
rewrite <- Hc1.
unfold nat_of_Z; rewrite Nat2Z.id; auto.
(* case 2 *)
destruct v'4.
{
  false.
  match goal with H: length _ = _ /\ length _ = _ |- _ => destruct H as (Hlen_vl1 & Hlen_vl2) end.
  subst muxvl.
  clear -Hlen_vl2 Hc2 Hsuc_rgn'.
  change (length nil) with 0%nat in Hlen_vl2.
  unfold nat_of_Z in Hlen_vl2.
  assert (Z.to_nat (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S v')) 
                  = (Z.to_nat (OS_USER_MAX_EVENTS / 3) - Z.to_nat (Z.of_nat (S v')))%nat).
  eapply Z2Nat.inj_sub; apply Nat2Z.is_nonneg.
  rewrite H in Hlen_vl2. clear H.
  rewrite Nat.eq_sym_iff in Hlen_vl2.
  rewrite NPeano.Nat.sub_0_le in Hlen_vl2.
  auto with zarith.
}
eapply backward_rule1.
introv Hsat.
eapply APthreadMutex_select_sn_ex_strong.
sep eexists.
sep split; eauto.
sep pauto.
subst.
hoare forward.
rewrite Hsuc in *.
eapply adisj_intro.
left.
assert (Hvl: v'3 ++ v'2 :: v :: v'4 = (v'3 ++ (v'2 :: nil)) ++ (v :: v'4)).
{
simpl; rewrite app_assoc_reverse.
simpl. auto.
}
rewrite Hvl in *.
match goal with H: _ |= _ |- _ => rename H into Hsat; sep_lifts_trms_in Hsat APthreadMutex end.
eapply APthreadMutex_split_frm in Hsat.
sep destruct Hsat.
sep_lifts_trms_in Hsat (_N_ 5 , _N_ 6, _N_ 7).
eapply sep_pure_split in Hsat; destruct Hsat as (Hmat_suc & Hsat).
eapply sep_pure_split in Hsat; destruct Hsat as (Hlen_all & Hsat).
eapply sep_pure_split in Hsat; destruct Hsat as (Hlen_suc & Hsat).
destruct Hlen_suc as (Hlen_l & Hlen_r).
rewrite last_length in Hlen_l.
subst.
lets Hgetp: new_array_type_vallist_match_mux_getp Hmat_suc.
destruct Hgetp as (p' & Hvp' & Hptr').
do 3 eexists.
exists (v'3 ++ (v'2 :: nil)) v'4.
sep eexists.
sep cancel Aarray_new.
sep cancel Astruct.
sep cancel Aarray_new.
sep auto.
rewrite Hvp'; eauto.
eapply PthreadMutex_full_P'_split; eauto.
rewrite Hvp; auto.
eapply Z.le_trans; eauto.
rewrite <- Nat2Z.inj_le; auto with zarith.
clear -Hc2.
eapply Zlt_le_succ in Hc2.
eapply Z.le_trans; eauto.
rewrite <- Nat2Z.inj_succ; auto with zarith.
rewrite last_length; auto.
(* end of while Aistrue*)
(* start of while Aisfalse *)
mytac_getret 4%nat.
eapply backward_rule1.
introv Hsat.
destruct Hsat as (Hsat & Hisfalse).
destruct Hsat as [Hsat | Hsat].
(* false case *)
false.
sep destruct Hsat.
lets Hcp: aconj_intro Hsat Hisfalse;
eapply sep_aconj_r_aisfalse_to_astar in Hcp; eauto.
2:{
clear Hsat Hcp. 
introv Hsat. subst.
sep get rv; try rewrite Hchg.
simpl val_inj; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hnth; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.
pure_auto.
}
rewrite Hchg in Hcp; simpl val_inj in Hcp.
rewrite Hnth in Hcp.
rewrite Hdiveq in Hcp; rewrite Hif_cpn in Hcp; simpl val_inj in Hcp.
clear -Hcp Heqi_suc.
sep_lifts_trms_in Hcp (val_inj).
eapply sep_pure_split in Hcp.
destruct Hcp as (Hf & Hcp).
change ($ 1) with Int.one in Hf.
destruct (Int.ltu ($ Z.of_nat x)
           (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn)
              (rv_dom +ᵢ  Int.one))) eqn: eq1;
simpl in Hf; destruct Hf; tryfalse.
rewrite Intlt_false_is_Zge in eq1.
rewrite Heqi_suc in eq1.
sep split in Hcp.
simpljoin.
rewrite Int.unsigned_repr in eq1; auto with zarith.
split; try solve_usr_max_evts_rgn.
(* actual Aisfalse *)
lets Hcp: aconj_intro Hsat Hisfalse;
eapply sep_aconj_r_aisfalse_to_astar in Hcp; eauto.
{
clear Hsat Hcp. 
introv Hsat.
sep destruct Hsat.
subst.
sep get rv; try rewrite Hchg.
simpl val_inj; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hnth; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.
pure_auto.
}
hoare unfold.
hoare forward. (* RETURN ′ 255 *)
sep pauto.
eauto.
eauto.
eauto.

(*type = 2 *) 
assert (Hif_false: Int.eq ($ 2) ($ 0) = false).
{ clear. int auto. }
hoare forward.
pure_auto.
rewrite Hif_false.
simpl val_inj.
hoare unfold; tryfalse.
eapply hoare_disj_afalseP_l_pre.
hoare unfold.
clear H Hif_false.
assert (Hif_false: Int.eq ($ 2) ($ 1) = false).
{ clear. int auto. }
hoare forward.
pure_auto.
rewrite Hif_false.
simpl val_inj.
hoare unfold; tryfalse.
eapply hoare_disj_afalseP_l_pre.
hoare unfold.
clear H Hif_false.
  hoare forward.
  2: {
    instantiate (1:= Afalse).
    eapply hoare_disj_afalseP_l_pre.
    hoare unfold.
    change (Int.eq ($2) ($ 2)) with true in H.
    simpl in H. destruct H; tryfalse.
  }
  change (Int.eq ($2) ($ 2)) with true. 
  hoare unfold.

(* i ′ =ₑ ebinop odiv (ebinop odiv ′ OS_USER_MAX_EVENTS ′ 3)  ′ Core_partition_num × Domain2Index ′ [ksCurDomain ′];ₛ *)
unfold Adomain2index.
unfold Adomain2index'.
unfold ACorepartnum, ACorepartnum'.
unfold AKsCurDomain.
hoare unfold.

match goal with
 H: length domvl = ?len |- _ =>
 rename H into Hlen;
 assert (Hle_len: (Z.to_nat (Int.unsigned kcurd) < len)%nat)
 by auto with zarith end.
lets Hnth: Hle_len.
eapply pure_lib.nthval'_has_value in Hnth; eauto.
destruct Hnth as (rv_dom & Hnth & Hmat).

assert (Hif_cpn: Int.eq cpn Int.zero || Int.eq ($ OS_USER_MAX_EVENTS / 3) ($ Int.min_signed) &&
                                Int.eq cpn Int.mone = false).
  { rewrite Heqf'.
     destruct (Int.eq cpn Int.zero) eqn: eq1; try tauto.
     eapply sem_lab.semacc_int_eq_true in eq1; subst.
     change (Int.unsigned Int.zero) with 0 in *.
     false; auto with zarith.
  }

assert (Hdiv_rgn1: 1 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn
                                      <= 79).
{ eapply user_max_evts_div_cpn_rgn; eauto. }
assert (Hdom_lt: Int.unsigned rv_dom < Int.unsigned cpn).
{ eapply Hrcpn; eauto.
   eapply inline_bittblfunctions.nth_val'2nth_val; eauto.
}
assert (Hdom_lt': Int.unsigned rv_dom < 8).
{ auto with zarith. }
assert (Hdiv_rgn2: 0 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn
                                                * Int.unsigned rv_dom <= Int.max_unsigned).
{ conv_max_unsigned.
   split.
   eapply Ztac.mul_le; auto with zarith.
   apply Int.unsigned_range_2.
   eapply Z.le_trans with (m:= 79 * Int.unsigned rv_dom).
   eapply Zmult_le_compat_r; auto with zarith.
   apply Int.unsigned_range_2.
   auto with zarith.
}
assert (Hdiv_rgn2': 0 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn
                                                * Int.unsigned rv_dom <= 79).
{
   split.
   eapply Ztac.mul_le; auto with zarith.
   eapply Z.le_trans with (m:= OS_USER_MAX_EVENTS / 3).
   eapply Z.lt_le_incl.
   eapply Z_div_mul_lt; auto with zarith.
   solve_usr_max_evts_rgn.
}

assert (Heqi: (Int.unsigned (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn) rv_dom)) 
                           = OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned rv_dom).
{ rewrite <- Int_divu_eq_divs'; auto with zarith.
   unfold Int.mul, Int.divu in *.
   repeat rewrite Int.unsigned_repr; auto;
   try solve_usr_max_evts_rgn; try conv_max_unsigned.
   rewrite Int.unsigned_repr; auto; try solve_usr_max_evts_rgn.
}
assert (Heqi_suc: Int.unsigned
  (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn) (rv_dom +ᵢ  Int.one)) = 
  OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned rv_dom + 1)).
{ rewrite <- Int_divu_eq_divs'; auto with zarith.
   unfold Int.mul, Int.divu, Int.add in *.
   change (Int.unsigned Int.one) with 1.
   repeat rewrite Int.unsigned_repr; auto;
   try solve_usr_max_evts_rgn; try conv_max_unsigned.
   rewrite Int.unsigned_repr; auto; try solve_usr_max_evts_rgn.
}
assert (Hsuc_rgn: 0 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned rv_dom + 1) <=
Int.max_unsigned).
{  try solve_usr_max_evts_rgn. }
assert (Hsuc_rgn': 1 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned rv_dom + 1)
                                       <=  OS_USER_MAX_EVENTS / 3).
{ eapply user_max_evts_part_succ_rgn; eauto with zarith. }

hoare forward.
rewrite Hchg; simpl val_inj; pure_auto.
rewrite Hchg; simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hchg; simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
rewrite Hchg; simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.

(*WHILE (ebinop odiv (ebinop odiv ′ OS_USER_MAX_EVENTS ′ 3)
         Core_partition_num ′ × (Domain2Index ′ [ksCurDomain ′] +ₑ ′ 1) *)

(*1: remember irrelevant sep-conjunctions*)
hoare_lifts_trms_pre (AMqAttr, Alvarmapsto i, Domain2Index, ksCurDomain, Core_partition_num).
hoare remember (1 :: 2 :: 3 :: 4 :: 5 :: nil)%nat pre.

  (*2: get the while loop inv into the pre-condition,
    so the pre-condition after the while statement
    can be correctly instantiated
   *)
destruct lmq as (lq_b & lq_i).

eapply backward_rule1 with (p := (*below is the loop inv*)
     (EX i p vl vll1 vll2 (* lq_b lq_i *),
      LV os_code_defs.i @ Int32u |-> (V$ (Z.of_nat i)) **
      GAarray Domain2Index (Tarray char_t (Z.to_nat DOMAIN_SIZE)) domvl **
      GV ksCurDomain @ long |-> Vint32 kcurd **
      GV Core_partition_num @ long |-> Vint32 cpn **
      GV Mq_Attr @ mq_attr_t ∗ |-> Vptr (lq_b, lq_i) **
      Aarray_new (lq_b, lq_i) (Tarray mq_attr_t i) vll1 **
      Astruct (lq_b,(lq_i+ᵢ  $ Z.of_nat (i * (typelen mq_attr_t)))) mq_attr_t vl ** 
      Aarray_new (lq_b, (lq_i+ᵢ  $ Z.of_nat ( (S i) * (typelen mq_attr_t)))) 
      (Tarray mq_attr_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S i)))) vll2 **
      [| new_array_type_vallist_match mq_attr_t mqvl |] **
      [| length mqvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
      [| mqvl = vll1 ++ (vl::vll2) |] **
      [| length vll1 = i /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S i)) |] **
      [| Z.of_nat(S i) <= OS_USER_MAX_EVENTS / 3 |] **
      [| Z.of_nat(S i) <= (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) *
                                        (Int.unsigned rv_dom + 1)) |] **
      [| (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) *
                                        (Int.unsigned rv_dom)) <= Z.of_nat i |] **
      [| Qattr_full_P' vll1 rv_dom cpn |] ** (* use for get out of the while loop *)
      [| V_QATTRpevent vl = Some p /\ isptr p |] **
      H9) \\//
    (  EX vll1 vll2,
        LV os_code_defs.i @ Int32u |-> 
              Vint32 (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn) 
                                              (Int.add rv_dom Int.one)) **
        GAarray Domain2Index (Tarray char_t (Z.to_nat DOMAIN_SIZE)) domvl **
        GV ksCurDomain @ long |-> Vint32 kcurd **
        GV Core_partition_num @ long |-> Vint32 cpn **
        AMqAttr (lq_b, lq_i) mqvl **
        [|vll1 ++ vll2 = mqvl|] **
        [|length vll1 = ∘ (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) *
                                        (Int.unsigned rv_dom + 1))|] **
        [| Qattr_full_P' vll1 rv_dom cpn  |] ** H9
      )
    ).
introv Hsat.
left.
eapply AMqAttr_unfold_any_idx_frm
   with (idx:= Z.to_nat (Int.unsigned 
                                             (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn) rv_dom))) in Hsat.
sep normal in Hsat.
sep destruct Hsat.
sep split in Hsat.
subst mqvl.
match goal with H: new_array_type_vallist_match mq_attr_t _ |- _ =>
lets Hgetp: new_array_type_vallist_match_que_getp H end.
destruct Hgetp as (p & Hvp & Hptr).
sep pauto; eauto.
rewrite Z2Nat.id.
rewrite Int.repr_unsigned; auto.
apply Int.unsigned_range_2.
eapply Qattr_full_P'_left_start; eauto.
rewrite <- Heqi; auto.
rewrite Heqi; auto with zarith.
rewrite Z.mul_add_distr_l.
rewrite Heqi.
rewrite <- Z2Nat.inj_succ; auto with zarith.
unfold AMqAttr in Hsat.
sep normal in Hsat.
sep destruct Hsat.
sep split in Hsat.
match goal with
 H: new_array_type_vallist_match mq_attr_t _ /\ _ |- _ =>
 destruct H as (_ & Hlen_vl); rewrite Hlen_vl end.
eapply OSMutex_common.intlt2nat.
rewrite Heqi.
eapply Z_div_mul_lt; auto with zarith.


 (*3: apply the 'seq_rule' to get the while statement
    off the remaining statements, then apply the 'while_rule'
   *)
eapply seq_rule.

(*4: prove the condition expression of while is legal *)
eapply while_rule with (tp := Int32u).
(*prove the condition expression of while is legal *)
introv Hsat.
(*2 cases*)
destruct Hsat as [Hsat | Hsat].
symbolic_execution; try rewrite Hchg.
simpl val_inj; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hnth; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.
pure_auto.
symbolic_execution; try rewrite Hchg.
simpl val_inj; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hnth; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.
pure_auto.
(*Aistrue (ebinop odiv (ebinop odiv ′ OS_USER_MAX_EVENTS ′ 3)
         Core_partition_num ′ × (Domain2Index ′ [ksCurDomain ′] +ₑ ′ 1 >ₑ os_code_defs.i ′)*)

(*5: the cond-expr of while hold implies the left part
    of the loop-inv*)
  eapply backward_rule1 with ( p:= (
     EX i p vl vll1 vll2 (* lq_b lq_i *),
      LV os_code_defs.i @ Int32u |-> (V$ (Z.of_nat i)) **
      GAarray Domain2Index (Tarray char_t (Z.to_nat DOMAIN_SIZE)) domvl **
      GV ksCurDomain @ long |-> Vint32 kcurd **
      GV Core_partition_num @ long |-> Vint32 cpn **
      GV Mq_Attr @ mq_attr_t ∗ |-> Vptr (lq_b, lq_i) **
      Aarray_new (lq_b, lq_i) (Tarray mq_attr_t i) vll1 **
      Astruct (lq_b,(lq_i+ᵢ  $ Z.of_nat (i * (typelen mq_attr_t)))) mq_attr_t vl ** 
      Aarray_new (lq_b, (lq_i+ᵢ  $ Z.of_nat ( (S i) * (typelen mq_attr_t)))) 
      (Tarray mq_attr_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S i)))) vll2 **
      [| new_array_type_vallist_match mq_attr_t mqvl |] **
      [| length mqvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
      [| mqvl = vll1 ++ (vl::vll2) |] **
      [| length vll1 = i /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S i)) |] **
      [| Z.of_nat(S i) <= OS_USER_MAX_EVENTS / 3 |] **
      [| Z.of_nat(S i) <= (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) *
                                        (Int.unsigned rv_dom + 1)) |] **
      [| (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) *
                                        (Int.unsigned rv_dom)) <= Z.of_nat i |] **
      [| Qattr_full_P' vll1 rv_dom cpn |] ** (* use for get out of the while loop *)
      [| V_QATTRpevent vl = Some p /\ isptr p |] **
      H9
)).
introv Hsat.
destruct Hsat as (Hsat & Histrue).
destruct Hsat as [Hsat | Hsat]. (*2 cases*)
(*case 1*)
sep destruct Hsat.
sep eexists.
sep cancel 1%nat 1%nat.
(*case 2*)
sep destruct Hsat.
lets Hcp: aconj_intro Hsat Histrue;
eapply sep_aconj_r_aistrue_to_astar in Hcp; eauto.
2:{ 
clear Hsat Hcp. 
introv Hsat. subst.
sep get rv; try rewrite Hchg.
simpl val_inj; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hnth; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.
pure_auto.
}
rewrite Hchg in Hcp; simpl val_inj in Hcp.
rewrite Hnth in Hcp.
rewrite Hdiveq in Hcp; rewrite Hif_cpn in Hcp; simpl val_inj in Hcp.
clear -Hcp.
sep_lifts_trms_in Hcp (val_inj).
eapply sep_pure_split in Hcp.
destruct Hcp as (Hf & Hcp).
change ($ 1) with Int.one in Hf.
rewrite sem_common.sempend_ltu_ass1 in Hf.
simpl in Hf.
destruct Hf; tryfalse.

(*If ((Mq_Attr ′ [os_code_defs.i ′]) → pevent ==ₑ ′ 0)*)
hoare_split_pure_all.
match goal with
H : Qattr_full_P' _ _ _, 
H' : V_QATTRpevent _ = Some _ /\ isptr _ |- _ =>
rename H into Hfull; destruct H' as (Hvp & Hptr)
end.
match goal with
| |- {| _, _, _, _, _, _ |} |- _ {{ ?P }} _ {{ _ }} =>
assert (Hgetp: P
       ==> Rv (efield (Mq_Attr ′ [i ′]) pevent) ==ₑ NULL @ Int32 == val_inj(val_eq v'0 Vnull))
end.
{
  introv Hsat.
  eapply bop_rv.
  { sep_get_rv_array_struct.
    eapply new_array_type_vallist_match_split'; eauto.
  }
  sep get rv.
  unfold bop_eval.
  unfold V_QATTRpevent in Hvp. eapply nth_val_nth_val'_some_eq in Hvp.
  rewrite Hvp.
  auto.
  destruct Hptr as [Hvnull | ((pb & pi) & Hp)]; simpljoin; pure_auto.
  simpl. auto.
}

(* actual start if *)
hoare forward.
eapply ift_rule_general.
intros.
eexists.
eapply Hgetp.
sep pauto.
sep pauto.

(* if true *)
eapply backward_rule1.
introv Hsat.
eapply sep_aconj_r_aistrue_to_astar in Hsat; eauto.

mytac_getret 5%nat.
instantiate (1:= Afalse).
clear Hgetp.
hoare unfold.
change ($ 0) with Int.zero.
hoare forward. (*RETURN i*)
sep cancel p_local.
sep cancel ASeminfo.
sep_lifts_trms AMqAttr.
eapply AMqAttr_select_sn_ex_strong.
sep eexists.
sep cancel APthreadMutex.
sep auto.
pure_auto.
2:{ rewrite Hnth; eauto. }
rewrite <- Byte.unsigned_repr_eq.
match goal with
H: Z.of_nat (S (length _)) <= _ ,
H':  Z.of_nat (S (length _)) <= _,
H'': _ <= Z.of_nat (length _) |- _ =>
rename H into Hslen; rename H' into Hslen';
rename H'' into Hlen_ge end.
assert (Hieq: (Int.unsigned ($ Z.of_nat (length v'3))) = Z.of_nat (length v'3)).
{ rewrite Int.unsigned_repr; auto with zarith.
}
rewrite Hieq.
assert (Hv: (Byte.unsigned (Byte.repr (Z.of_nat (length v'3)))) = Z.of_nat (length v'3)).
{
  eapply Byte.unsigned_repr.
  change Byte.max_unsigned with 255.
  split; try solve_usr_max_evts_rgn.
}
rewrite Hv.
unfold nth_Qattr_free_P'.
exists v'2.
splits.
split; auto with zarith.
unfold nat_of_Z in *.
rewrite nat_of_Z_of_nat.
apply nth_vallist_get_idx.
rewrite Hvp.
match goal with H: val_inj (val_eq _ Vnull) <> Vint32 Int.zero |- _ => rename H into Hif end.
destruct Hptr as [Hvnull | ((pb & pi) & Hp)]; simpljoin; simpl in Hif; tryfalse.

(* if false *)
hoare forward.
eapply backward_rule1.
introv Hsat.
eapply sep_aconj_r_aisfalse_to_astar in Hsat; eauto.
(* ++ i ′ *)
clear Hgetp.
hoare_lifts_trms_pre val_inj.
eapply pure_split_rule'; introv Hval_inj.
destruct Hptr as [Hvnull | ((pb & pi) & Hp)]; subst v'0; simpl in Hval_inj; destruct Hval_inj; tryfalse.
match goal with
H: Z.of_nat (S _) <= _ ,
H':  Z.of_nat (S _) <= _,
H'': _ <= Z.of_nat _ |- _ =>
rename H into Hslen; rename H' into Hslen';
rename H'' into Hlen_ge end.
assert (Hsuc: ($ Z.of_nat v' +ᵢ  $ 1) = ($ (Z.of_nat (S v')))).
{ simpljoin.
   clear -Hslen.
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  int auto.
}
lets Hcond: z_split Hslen'.
destruct Hcond as [Hc1 | Hc2].
(* case 1*)
eapply backward_rule1.
introv Hsat.
eapply AMqAttr_select_sn_ex_strong.
sep eexists.
sep split; eauto.
sep pauto.
subst.
hoare forward.
rewrite Hsuc in *; rewrite Hc1 in *.
eapply adisj_intro.
right.
exists (v'3 ++ (v'2 :: nil)) v'4.
rewrite <- list_cons_assoc.
sep pauto.
match goal with | |- Vint32 ?v1 = Vint32 ?v2 => assert (Heqv: v1 = v2) end.
eapply unsigned_inj.
rewrite Int.unsigned_repr.
rewrite Heqi_suc; auto.
auto.
rewrite Heqv; auto.
eapply Qattr_full_P'_split; eauto.
rewrite Hvp; auto.
rewrite last_length.
rewrite <- Hc1.
unfold nat_of_Z; rewrite Nat2Z.id; auto.
(* case 2 *)
destruct v'4.
{
  false.
  match goal with H: length _ = _ /\ length _ = _ |- _ => destruct H as (Hlen_vl1 & Hlen_vl2) end.
  subst mqvl.
  clear -Hlen_vl2 Hc2 Hsuc_rgn'.
  change (length nil) with 0%nat in Hlen_vl2.
  unfold nat_of_Z in Hlen_vl2.
  assert (Z.to_nat (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S v')) 
                  = (Z.to_nat (OS_USER_MAX_EVENTS / 3) - Z.to_nat (Z.of_nat (S v')))%nat).
  eapply Z2Nat.inj_sub; apply Nat2Z.is_nonneg.
  rewrite H in Hlen_vl2. clear H.
  rewrite Nat.eq_sym_iff in Hlen_vl2.
  rewrite NPeano.Nat.sub_0_le in Hlen_vl2.
  auto with zarith.
}
eapply backward_rule1.
introv Hsat.
eapply AMqAttr_select_sn_ex_strong.
sep eexists.
sep split; eauto.
sep pauto.
subst.
hoare forward.
rewrite Hsuc in *.
eapply adisj_intro.
left.
assert (Hvl: v'3 ++ v'2 :: v :: v'4 = (v'3 ++ (v'2 :: nil)) ++ (v :: v'4)).
{
simpl; rewrite app_assoc_reverse.
simpl. auto.
}
rewrite Hvl in *.
match goal with H: _ |= _ |- _ => rename H into Hsat; sep_lifts_trms_in Hsat AMqAttr end.
eapply AMqAttr_split_frm in Hsat.
sep destruct Hsat.
sep_lifts_trms_in Hsat (_N_ 5 , _N_ 6, _N_ 7).
eapply sep_pure_split in Hsat; destruct Hsat as (Hmat_suc & Hsat).
eapply sep_pure_split in Hsat; destruct Hsat as (Hlen_all & Hsat).
eapply sep_pure_split in Hsat; destruct Hsat as (Hlen_suc & Hsat).
destruct Hlen_suc as (Hlen_l & Hlen_r).
rewrite last_length in Hlen_l.
subst.
lets Hgetp: new_array_type_vallist_match_que_getp Hmat_suc.
destruct Hgetp as (p' & Hvp' & Hptr').
do 3 eexists.
exists (v'3 ++ (v'2 :: nil)) v'4.
sep eexists.
sep cancel Aarray_new.
sep cancel Astruct.
sep cancel Aarray_new.
sep auto.
rewrite Hvp'; eauto.
eapply Qattr_full_P'_split; eauto.
rewrite Hvp; auto.
eapply Z.le_trans; eauto.
rewrite <- Nat2Z.inj_le; auto with zarith.
clear -Hc2.
eapply Zlt_le_succ in Hc2.
eapply Z.le_trans; eauto.
rewrite <- Nat2Z.inj_succ; auto with zarith.
rewrite last_length; auto.
(* end of while Aistrue*)
(* start of while Aisfalse *)
mytac_getret 6%nat.
eapply backward_rule1.
introv Hsat.
destruct Hsat as (Hsat & Hisfalse).
destruct Hsat as [Hsat | Hsat].
(* false case *)
false.
sep destruct Hsat.
lets Hcp: aconj_intro Hsat Hisfalse;
eapply sep_aconj_r_aisfalse_to_astar in Hcp; eauto.
2:{
clear Hsat Hcp. 
introv Hsat. subst.
sep get rv; try rewrite Hchg.
simpl val_inj; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hnth; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.
pure_auto.
}
rewrite Hchg in Hcp; simpl val_inj in Hcp.
rewrite Hnth in Hcp.
rewrite Hdiveq in Hcp; rewrite Hif_cpn in Hcp; simpl val_inj in Hcp.
clear -Hcp Heqi_suc.
sep_lifts_trms_in Hcp (val_inj).
eapply sep_pure_split in Hcp.
destruct Hcp as (Hf & Hcp).
change ($ 1) with Int.one in Hf.
destruct (Int.ltu ($ Z.of_nat x)
           (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) cpn)
              (rv_dom +ᵢ  Int.one))) eqn: eq1;
simpl in Hf; destruct Hf; tryfalse.
rewrite Intlt_false_is_Zge in eq1.
rewrite Heqi_suc in eq1.
sep split in Hcp.
simpljoin.
rewrite Int.unsigned_repr in eq1; auto with zarith.
split; try solve_usr_max_evts_rgn.
(* actual Aisfalse *)
lets Hcp: aconj_intro Hsat Hisfalse;
eapply sep_aconj_r_aisfalse_to_astar in Hcp; eauto.
{
clear Hsat Hcp. 
introv Hsat.
sep destruct Hsat.
subst.
sep get rv; try rewrite Hchg.
simpl val_inj; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; simpl; pure_auto.
unfold DOMAIN_SIZE; unfold PARTITION_NUM; auto with zarith.
rewrite Hnth; auto.
rewrite Hnth; pure_auto.
simpl val_inj.
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth; simpl; pure_auto.
simpl val_inj;
rewrite Hdiveq; rewrite Hif_cpn; rewrite Hnth.
simpl val_inj.
pure_auto.
}
hoare unfold.
hoare forward. (* RETURN ′ 255 *)
sep pauto.
eauto.
eauto.
eauto.

Unshelve.
exact 0%nat.
exact 0%nat.
exact 0%nat.
Qed.


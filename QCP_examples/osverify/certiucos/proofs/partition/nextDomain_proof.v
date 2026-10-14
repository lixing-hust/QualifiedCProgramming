(* new in nextDomainProof.v *)

Require Import seplog_lemmas.
Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import os_ucos_h.
(* Require Import abs_infer_abt. *)

Require Import abs_op_partition_ext.
Require Import Aarray_new_common.

Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.
Require Import partition_common.

Local Open Scope code_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Lemma absimp_nextDomain_succ:
  forall P s sch idx len cd ld dt kscd dom kscd_len idx',
    can_change_aop P ->
    idx' = (if Int.ltu (idx +ᵢ  Int.one) len then idx +ᵢ  Int.one else Int.zero) ->
    KsDScdMod.get kscd idx' = Some (dom, kscd_len) ->
    absinfer sch
             ( <|| nextdom (nil) ;; s ||> ** HKsDSchdidx idx ** HKsDSchdlen len **
                                                               HKsCurDomain cd ** HKsLastDomain ld ** HKsDomainTime dt **
                                                               HKsDomSchedule kscd ** P ) 
             ( <|| s ||> ** HKsDSchdidx idx' **
                                  HKsDSchdlen len ** HKsCurDomain dom ** HKsLastDomain cd ** HKsDomainTime kscd_len **
                                  HKsDomSchedule kscd ** P ). 
Proof.
  intros.
  subst.
  infer_solver 0%nat.
  do 4 (eapply tidsame_trans; [idtac | eapply tidsame_set;eauto]).
  apply eqtid_same.
Qed.

Ltac sep_get_rv_array_struct_gvar :=
  let Hsat := fresh in
  let Hf := fresh in
  let Heq := fresh in
  match goal with
  | |- ?P ==> Rv efield (?gident ′ [?ident ′]) ?id @ ?tp1 == _ =>
        introv Hsat; sep_lifts_trms_in Hsat (Agvarmapsto gident, Agvarmapsto ident);
         match goal with
         | Hsat:?s
                |= GV gident @ ?tp ∗ |-> Vptr (?b, ?i) **
                   GV ident @ _ |-> Vint32 ?idx ** ?P'
           |- ?s |= Rv efield (?gident ′ [?ident ′]) ?id @ ?tp1 == _ =>
               match find_ptrstruct_by_block P' b with
               | some ?n => sep lifts (S (S n) :: nil) in Hsat
               end; sep_lifts_trms_in Hsat (Agvarmapsto gident, Agvarmapsto ident);
                eapply gjb_common.struct_array_member_rv;
                [ try symbolic_execution
                | try symbolic_execution
                | try sep lift 3%nat in Hsat;
                   match idx with
                   | $ Z.of_nat ?idx0 =>
                       assert (Heq : Int.unsigned ($ Z.of_nat idx0) = Z.of_nat idx0);
                        [ try apply dscd_size_eq;
                           try auto with zarith
                        |  ]
                   | _ => idtac
                   end; try rewrite Heq; try rewrite Nat2Z.id; eauto
                | match goal with
                  | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
                  end; auto
                | simpl; auto
                | auto
                | auto
                | try apply gjb_common.int_ltu_zero_eq_false
                | match idx with
                  | $ Z.of_nat ?idx0 =>
                      assert (Heq : Int.unsigned ($ Z.of_nat idx0) = Z.of_nat idx0);
                       [ try apply dscd_size_eq;
                          try auto with zarith
                       |  ]
                  | _ => idtac
                  end; try rewrite Heq;
                   try (apply dscd_size_le'; auto);
                   try (apply dscd_size_comp; auto)
                | simpl; try apply eight_min_max
                | auto
                | simpl; auto
                | splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
                | unfold id_nth; simpl; auto
                | auto ]
         end
   | Hsat:?s |= ?P
    |- ?s |= Rv efield (?gident ′ [?ident ′]) ?id @ ?tp1 == _ =>
        sep_lifts_trms_in Hsat (Agvarmapsto gident, Agvarmapsto ident);
         match goal with
         | Hsat:?s
                |= GV gident @ ?tp ∗ |-> Vptr (?b, ?i) **
                   GV ident @ _ |-> Vint32 ?idx ** ?P'
           |- ?s |= Rv efield (?gident ′ [?ident ′]) ?id @ ?tp1 == _ =>
               match find_ptrstruct_by_block P' b with
               | some ?n => sep lifts (S (S n) :: nil) in Hsat
               end; sep_lifts_trms_in Hsat (Agvarmapsto gident, Agvarmapsto ident);
                eapply gjb_common.struct_array_member_rv;
                [ try symbolic_execution
                | try symbolic_execution
                | try sep lift 3%nat in Hsat;
                   match idx with
                   | $ Z.of_nat ?idx0 =>
                       assert (Heq : Int.unsigned ($ Z.of_nat idx0) = Z.of_nat idx0);
                        [ try apply dscd_size_eq;
                           try auto with zarith
                        |  ]
                   | _ => idtac
                   end; try rewrite Heq; try rewrite Nat2Z.id; eauto
                | match goal with
                  | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
                  end; auto
                | simpl; auto
                | auto
                | auto
                | try apply gjb_common.int_ltu_zero_eq_false
                | match idx with
                  | $ Z.of_nat ?idx0 =>
                      assert (Heq : Int.unsigned ($ Z.of_nat idx0) = Z.of_nat idx0);
                       [ try apply dscd_size_eq;
                          try auto with zarith
                       |  ]
                  | _ => idtac
                  end; try rewrite Heq;
                   try (apply dscd_size_le'; auto);
                   try (apply dscd_size_comp; auto)
                | simpl; try apply eight_min_max
                | auto
                | simpl; auto
                | splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
                | unfold id_nth; simpl; auto
                | auto ]
         end
  end.

(* Lemma good_frm_p_local:
forall ct lg,
  GoodFrm (p_local OSLInv ct lg).
Proof.
  intros.
  unfold p_local.
  unfold LINV,CurTid.
  unfold OSLInv.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_p_local : good_frm_lemmas. *)


Lemma nextDomain_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal nextDomain vl logicl nextDomainPre ct->
      Some r =
      BuildRetI os_internal nextDomain vl logicl nextDomainPost ct->
      exists t d1 d2 s,
        os_internal nextDomain = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
init spec.
subst.
rename v'5 into idx.
rename v'6 into len.
rename v'7 into cd.
rename v'8 into ld.
rename v'9 into dt.
rename v'10 into kscd_vl.
rename v'11 into kscd_abs.
rename v'12 into icp.
unfold AKsDSchdidx, AKsDSchdlen, AKsCurDomain, AKsLastDomain,
             AKsDomainTime, AKsDomSchedule, AisChangePartion.
hoare unfold.
hoare forward.
hoare_enter_critical2.
hoare forward.
hoare_lifts_trms_pre (Aop, ksDomScheduleIdx, ksDomScheduleLength).
hoare remember (1 :: 2 :: 3 :: nil)%nat pre.
eapply seq_rule.
instantiate (1:= <|| nextdom nil;; v' ||>  **
  GV ksDomScheduleIdx @ long |-> Vint32 (if (Int.ltu (Int.add idx Int.one) len) then (Int.add idx Int.one) else Int.zero) **
  GV ksDomScheduleLength @ char_t |-> Vint32 len ** H5).
subst.
hoare forward; try change ($ 1) with Int.one in *.
pure_auto.
pure_auto.
pure_auto.
hoare forward.
destruct H5 as [Hsat | Hsat];
sep pauto.
assert (Hcond: Int.ltu (idx +ᵢ  Int.one) len = false).
{
   rewrite Intlt_false_is_Zge.
  destruct (Int.ltu len (idx +ᵢ  Int.one)) eqn: eq1;
  try lets Hf: ltu_eq_false eq1;
  destruct ( Int.eq (idx +ᵢ  Int.one) len) eqn: eq2;
  simpl val_inj in *;
  try change (Int.ltu Int.zero Int.one) with true in *;
  try change (Int.ltu Int.zero Int.zero) with false in *;
  simpl val_inj in *; simpljoin; tryfalse.
  eapply sem_lab.semacc_int_eq_false in eq2.
  eapply Intlt_true_is_Zlt in eq1.
  auto with zarith.
  eapply sem_lab.semacc_int_eq_true in eq2; subst.
  auto with zarith.
}
rewrite Hcond.
change ($ 0) with Int.zero; auto.
assert (Hcond: Int.ltu (idx +ᵢ  Int.one) len = true).
{ rewrite Intlt_true_is_Zlt.
  destruct (Int.ltu len (idx +ᵢ  Int.one)) eqn: eq1;
  try lets Hf: ltu_eq_false eq1;
  destruct ( Int.eq (idx +ᵢ  Int.one) len) eqn: eq2;
  simpl val_inj in *;
  try change (Int.ltu Int.zero Int.one) with true in *;
  try change (Int.ltu Int.zero Int.zero) with false in *;
  simpl val_inj in *; destruct H5; tryfalse.
  eapply sem_lab.semacc_int_eq_false in eq2.
  eapply Intlt_false_is_Zge in eq1.
  rewrite <- ZIntneq_is_Zneq in eq2.
  auto with zarith.
}
rewrite Hcond.
auto.
subst.
hoare forward.
remember (if Int.ltu (idx +ᵢ  Int.one) len then idx +ᵢ  Int.one else Int.zero) as idx'.
hoare_lifts_trms_pre AKsDomSchedule'.
hoare_assert_pure (length kscd_vl = ∘ DSCHEDULE_SIZE).
{ eapply AKsDomSchedule'_len_frm with (s:= s0); eauto. }
eapply pure_split_rule'; introv Hlen.
assert (Hidx'_lt: (Z.to_nat (Int.unsigned idx') < length kscd_vl)%nat).
{ rewrite Hlen.
   unfold DSCHEDULE_SIZE in *.
   unfold nat_of_Z.
   eapply Z2Nat.inj_lt; auto with zarith.
   apply Int.unsigned_range_2.
   destruct (Int.ltu (idx +ᵢ  Int.one) len) eqn: eq1.
  rewrite Intlt_true_is_Zlt in eq1.
  subst.
  auto with zarith.
  subst.
  rewrite Int.unsigned_zero.
  auto with zarith.
}
eapply backward_rule1.
introv Hsat.
eapply AKsDomSchedule'_unfold_any_idx_frm with (idx:= Z.to_nat(Int.unsigned idx')); eauto.
hoare unfold.
lets Hnth: gjb_common.nth_vallist_get_idx v'5 v'9 v'6.
rewrite H8 in Hnth.
lets Hsp: H5.
eapply new_array_type_vallist_match_split1_gen in Hsp; eauto; try solve [unfolds; eauto].
destruct Hsp as (_ & _ & Hsp).
lets Hsp': Hsp. lets Hsp'': Hsp.
eapply struct_type_vallist_match_elim_2 in Hsp'.
destruct Hsp' as (dscd_dom & dscd_len & Heq).
subst.
simpl in Hsp''.
destruct dscd_dom; destruct dscd_len; simpl in Hsp''; simpljoin; tryfalse.
remember (if Int.ltu (idx +ᵢ  Int.one) len then idx +ᵢ  Int.one else Int.zero) as idx'.
rename i into dscd_dom; rename i0 into dscd_len.
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
split; introv Hsat. sep cancel (Agvarmapsto ksCurDomain).
sep cancel A_dom_lenv; eauto.
sep auto.
simpl; auto.
sep_get_rv_array_struct_gvar.
eapply eq_int; tauto.
intros. eexists. sep cancel p_local. simpl; eauto.
(* ksDomainTime ′ =ₑ efield (ksDomSchedule ′[ksDomScheduleIdx ′]) dscd_length;ₛ *)
hoare_lifts_trms_pre (Aop).
hoare forward.
eapply assign_rule_gvar.
split; introv Hsat. sep cancel (Agvarmapsto ksDomainTime).
sep cancel A_dom_lenv; eauto.
sep auto.
simpl; auto.
sep_get_rv_array_struct_gvar.
eapply eq_int; tauto.
intros. eexists. sep cancel p_local. simpl; eauto.
(* isChangePartion ′ =ₑ ′ 1;ₛ *)
hoare forward.
remember (if Int.ltu (idx +ᵢ  Int.one) len then idx +ᵢ  Int.one else Int.zero) as idx'.
eapply backward_rule1.
introv Hsat.
eapply AKsDomSchedule'_select_sn_strong_frm.
exists (Z.to_nat (Int.unsigned idx')) v'5 v'6 v'7 v'8 (Vint32 dscd_dom :: Vint32 dscd_len :: nil).
sep pauto.
hoare_lifts_trms_pre (Aop, ksdschedidxid, ksdschedlenid, kscurdomid, kslastdomid, ksdomtimeid, ksdschedid).
eapply abscsq_rule.
apply noabs_oslinv.
eapply absimp_nextDomain_succ; eauto.
can_change_aop_solver.
eapply absinfer_eq.
simpl nth_val'.
hoare forward.
hoare_exit_critical2.
subst.
hoare forward.
eauto.
Unshelve.
exact O. exact O.
Qed.


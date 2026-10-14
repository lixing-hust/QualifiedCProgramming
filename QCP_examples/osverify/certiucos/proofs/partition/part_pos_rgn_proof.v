Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import ifun_spec.
Require Import abs_op.
Require Import inv_prop.

Require Import abs_infer_step.
Require Import abs_infer_abt. 
Require Import ucos_frmaop.
Require Import part_pos_rgn_spec.

(* absimp lemmas *)
Require Import hoare_tactics.
Require Import pure_auto.
Require Import ucos_pauto.
Require Import sep_auto.
Require Import symbolic_execution.
Require Import seplog_tactics.
Require Import seplog_lemmas.
Require Import sep_cancel_ext.
Require Import derived_rules.
Require Import hoare_conseq.
Require Import ucos_forward.
Require Import hoare_assign.
Require Import math_auto.
Require Import tv_match.
Require Import symbolic_lemmas.
Require Import Aarray_new_common.
Require Import gjb_common.
Require Import partition_common.

(* Require Import ev_aux_code. *)
Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Local Open Scope code_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Lemma absinfer_kscurdom_ext :
forall sch P s curd,
       can_change_aop P ->
       curd <> Int.mone ->
         absinfer sch
      (<|| kscurdom_ext (| nil |) ;; s||> ** HKsCurDomain curd ** P)
      (<|| s ||> **  HKsCurDomain curd ** P).
Proof.
infer_solver 0%nat.
Qed.

Lemma absinfer_kscurdom_ext_abt :
forall sch P s curd,
       can_change_aop P ->
       curd = Int.mone ->
         absinfer sch
      (<|| kscurdom_ext (| nil |) ;; s ||> ** HKsCurDomain curd ** P)
      (<|| ABORT ||> **  HKsCurDomain curd ** P).
Proof.
intros.
eapply absinfer_trans; try (eapply absinfer_seq_abt; [ | | eauto ]; try can_change_aop_solver).
eapply absinfer_seq; try can_change_aop_solver.
eapply absinfer_abt; try can_change_aop_solver.
absimp_abt_solver; try can_change_aop_solver.
Qed.

Lemma absinfer_get_temp_dom_succ :
forall sch P s curd domls rv_dom idx,
       can_change_aop P ->
       get domls curd = Some idx ->
       rv_dom = Vint32 idx ->
         absinfer sch
      (<|| get_temp_dom (| rv_dom :: nil |) ;; s||> ** HKsCurDomain curd ** HDomain2index domls ** P)
      (<|| s ||> **  HKsCurDomain curd ** HDomain2index domls  ** P).
Proof.
infer_solver 0%nat.
Qed.

Lemma absinfer_get_temp_dom_abt :
forall sch P s curd domls rv_dom idx,
       can_change_aop P ->
       get domls curd = Some idx ->
       rv_dom <> Vint32 idx ->
         absinfer sch
      (<|| get_temp_dom (| rv_dom :: nil |) ;; s||> ** HKsCurDomain curd ** HDomain2index domls ** P)
      (<|| ABORT ||> **  HKsCurDomain curd ** HDomain2index domls  ** P).
Proof.
intros.
eapply absinfer_trans; try (eapply absinfer_seq_abt; [ | | eauto ]; try can_change_aop_solver).
eapply absinfer_seq; try can_change_aop_solver.
eapply absinfer_abt; try can_change_aop_solver.
absimp_abt_solver; try can_change_aop_solver.
instantiate (3:= s0).
instantiate (2:= get_temp_dom (|rv_dom :: nil|)).
sep pauto.
Qed.

Lemma absinfer_get_temp_num_succ :
forall sch P s rv_num cpn,
       can_change_aop P ->
       rv_num = Vint32 cpn ->
         absinfer sch
      (<|| get_temp_num (| rv_num :: nil |) ;; s||> ** Hcorepartnum cpn ** P)
      (<|| s ||> **  Hcorepartnum cpn  ** P).
Proof.
infer_solver 0%nat.
Qed.

Lemma absinfer_get_temp_num_abt :
forall sch P s rv_num cpn,
       can_change_aop P ->
       rv_num <> Vint32 cpn ->
         absinfer sch
      (<|| get_temp_num (| rv_num :: nil |) ;; s||> ** Hcorepartnum cpn ** P)
      (<|| ABORT ||> **  Hcorepartnum cpn  ** P).
Proof.
intros.
eapply absinfer_trans; try (eapply absinfer_seq_abt; [ | | eauto ]; try can_change_aop_solver).
eapply absinfer_seq; try can_change_aop_solver.
eapply absinfer_abt; try can_change_aop_solver.
absimp_abt_solver; try can_change_aop_solver.
Qed.

Lemma absinfer_pos_lt_rgn_err:
forall sch P s2 rv_dom rv_num evt pos,
       can_change_aop P ->
       evt = $ OS_USER_MAX_EVENTS / 3 ->
       Int.ltu pos (Int.mul (Int.divs evt rv_num) rv_dom) = true ->
       absinfer sch
      (<|| pos_lt_rgn_err (| Vint32 pos ::  Vint32 rv_dom :: Vint32 rv_num :: nil |) ?? s2 ||> ** P)
      (<|| END (Some (Vint32 Int.mone)) ||> **  P).
Proof.
infer_solver 0%nat.
Qed.

Lemma absinfer_pos_ge_rgn_err:
forall sch P s2 rv_dom rv_num evt pos,
       can_change_aop P ->
       evt = $ OS_USER_MAX_EVENTS / 3 ->
       Int.ltu pos (Int.mul (Int.divs evt rv_num) (Int.add rv_dom Int.one)) = false ->
       absinfer sch
      (<|| (pos_ge_rgn_err (| Vint32 pos ::  Vint32 rv_dom :: Vint32 rv_num :: nil |)) ?? s2 ||> ** P)
      (<|| END (Some (Vint32 Int.mone)) ||> **  P).
Proof.
infer_solver 0%nat.
Qed.

Lemma absinfer_pos_rgn_choice2_cons:
forall sch P s1 s2,
    can_change_aop P ->
    absinfer sch (<||  s1 ?? s2 ||> ** P) (<|| s2 ||> **  P).
Proof.
intros.
eapply absinfer_choice2; eauto.
Qed.

Lemma absinfer_pos_rgn_seq_cons:
forall sch P s,
    can_change_aop P ->
    absinfer sch (<||  END None ;; s ||> ** P) (<|| s ||> **  P).
Proof.
intros.
eapply absinfer_seq_end; eauto.
Qed.

Lemma absinfer_partition_pos_out_of_rgn_err :
forall sch P a curd pbls posv domls idx evt cpn,
       can_change_aop P ->
       cmpaddr Clt userAddrStart a = true ->
       cmpaddr Cle a userAddrEnd = true ->
       get pbls a = Some posv ->
       get domls curd = Some idx ->
      evt = (Int.repr (OS_USER_MAX_EVENTS / 3)) ->
      (Int.ltu posv (Int.mul (Int.divs evt cpn) idx) = true \/
        Int.ltu posv (Int.mul (Int.divs evt cpn) (Int.add idx Int.one)) = false) ->
         absinfer sch
      (<|| partition_pos_out_of_rgn_err (| Vptr a :: nil |) ||> **
        Hpbls pbls ** HKsCurDomain curd ** HDomain2index domls ** Hcorepartnum cpn ** P)
      (<|| END (Some (Vint32 Int.mone)) ||> **  Hpbls pbls ** HKsCurDomain curd ** HDomain2index domls ** Hcorepartnum cpn ** P).
Proof.
infer_solver 0%nat.
Qed.

Lemma mund_int_a2:
  forall i,
    Int.unsigned i <= 255 ->
    (if Int.unsigned i <=? Byte.max_unsigned then true else false) = true.
  intros.
  apply leb_bytemax_true_intro in H.
  rewrite H.
  auto.
Qed.

Lemma part_pos_rgn_proof:
forall lident r tid posv vr_temp_dom vr_temp_num vr_temp_dom' vr_temp_num' (* rv *) vdom vnum
            er lenv (ks: stmts) P s,
   (<|| END (Some (Vint32 Int.mone)) ||>  **
     LV lident @ Int32u |-> Vint32 posv **
    (EX vdom, LV temp_dom @ Int8s |-> vdom) **
    (EX vnum, LV temp_num @ Int8u |-> vnum) **
    Aisr empisr **
    Aie true **
    Ais nil **
    Acs nil **
    Aier er **
    p_local OSLInv tid init_lg **
    A_dom_lenv lenv ** P ==> r (Some (Vint32 Int.mone))) ->
GoodFrm P ->
can_change_aop P ->
var_notin_dom Domain2Index lenv = true ->
var_notin_dom ksCurDomain lenv = true ->
var_notin_dom Core_partition_num lenv = true ->
{|OS_spec, GetHPrio, OSLInv, I, r , Afalse|}
  |- tid
{{ <|| s ||>  **
     LV lident @ Int32u |-> Vint32 posv **
    (EX vdom, LV temp_dom @ Int8s |-> vdom) **
    (EX vnum, LV temp_num @ Int8u |-> vnum) **
    Aisr empisr **
    Aie true **
    Ais nil **
    Acs nil **
    Aier er **
    p_local OSLInv tid init_lg **
    A_dom_lenv lenv ** P}}
ks
{{ Afalse}}  ->
{|OS_spec, GetHPrio, OSLInv, I, r , Afalse|}
  |- tid
{{ <|| partition_pos_rgn (Vint32 posv :: vr_temp_dom :: vr_temp_num ::
                                                  vr_temp_dom' :: vr_temp_num' :: (* rv :: *) nil) s ||>  **
    LV lident @ Int32u |-> Vint32 posv **
    LV temp_dom @ Int8s |-> vdom **
    LV temp_num @ Int8u |-> vnum **
    Aisr empisr **
    Aie true **
    Ais nil **
    Acs nil **
    Aier er **
    p_local OSLInv tid init_lg **
    A_dom_lenv lenv ** P}}
ENTER_CRITICAL;ₛ
temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
EXIT_CRITICAL;ₛ
ENTER_CRITICAL;ₛ
temp_num′ =ₑ Core_partition_num′;ₛ
EXIT_CRITICAL;ₛ
If (lident′ <ₑ ((ebinop odiv (ebinop odiv (′OS_USER_MAX_EVENTS) (′3)) (temp_num′)) ×  temp_dom′)){
RETURN  ′-1
};ₛ
ENTER_CRITICAL;ₛ
temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
EXIT_CRITICAL;ₛ
ENTER_CRITICAL;ₛ
temp_num′ =ₑ Core_partition_num′;ₛ
EXIT_CRITICAL;ₛ
If (lident′ ≥ ((ebinop odiv (ebinop odiv (′OS_USER_MAX_EVENTS) (′3)) (temp_num′)) ×  (temp_dom′+ₑ ′1))){
RETURN  ′-1
};ₛ ks
{{ Afalse}}.
Proof.
introv Hr Hfrm Haop Hnin_dom1 Hnin_dom2 Hnin_dom3 Hpre.
eapply seq_rule.
hoare_enter_critical.
hoare unfold.
unfold PartitionInv.
unfold Adomain2index.
unfold Adomain2index'.
unfold AKsCurDomain.
hoare unfold.
hoare_lifts_trms_pre (Aop, kscurdom).
match goal with
| H: length ?vl = ?len
  |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** HKsCurDomain ?idx ** _ }} _ {{ _ }} =>
   rename idx into vcurd
end.
assert(Hvcurd : vcurd = Int.mone \/ vcurd <> Int.mone) by tauto.
destruct Hvcurd as [Habt | Hvcurd].
eapply abscsq_rule.
apply noabs_oslinv.
eapply absinfer_kscurdom_ext_abt; eauto.
can_change_aop_solver.
eapply absinfer_eq.
apply absabort_rule.
eapply abscsq_rule.
apply noabs_oslinv.
eapply absinfer_kscurdom_ext; eauto.
can_change_aop_solver.
eapply absinfer_eq.
match goal with H: _ \/ vcurd = Int.mone |- _ => destruct H as [Hcd_rgn | Hf]; try subst; tryfalse end.
destruct Hcd_rgn as (Hcd_pos & Hcd_lt).

hoare_lifts_trms_pre (Aop, Domain2Index, ksCurDomain).
match goal with
| H: length ?vl = ?len
  |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** _ Domain2Index _ ?vl ** GV ksCurDomain @ _ |-> Vint32 ?idx ** _ }} _ {{ _ }} =>
   rename H into Hlen; assert (Hle_len: (Z.to_nat (Int.unsigned idx) < len)%nat)
end.
solve_part_int_rgn.
lets Hnth: Hle_len.
eapply pure_lib.nthval'_has_value in Hnth; eauto.
destruct Hnth as (rv_dom & Hnth & Hmat).
eapply seq_rule.
eapply assign_rule_lvar;
                [ intro s_; split; intro Hsat; try sep pauto
                | idtac
                | apply assign_type_match_true; simpl; auto | li_sepauto li].
introv Hsat.
sep_lifts_trms_in Hsat (A_dom_lenv, Domain2Index).
eapply array_member_rv_g; [eauto | eauto | eauto | try sep get rv | .. | ]; eauto.
solve_part_int_rgn.
solve_part_int_rgn.
simpl; auto.

hoare_lifts_trms_pre (Aop, kscurdom, domindexlist).
match goal with
  H: RLH_Dom2idx_P _ _ |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** _ ** HDomain2index ?absdomls ** _ }} _ {{ _ }} =>
   rename absdomls into domls; rename H into Hlh_dom
end.
assert (Hget_dom:get domls  vcurd = Some rv_dom).
eapply Hlh_dom; eauto.
eapply inline_bittblfunctions.nth_val'2nth_val; eauto.

assert (Hrv_dom: vr_temp_dom <> Vint32 rv_dom \/ vr_temp_dom = Vint32 rv_dom) by tauto.
destruct Hrv_dom as [Habt | Hrv_dom].
eapply abscsq_rule.
apply noabs_oslinv.
eapply absinfer_get_temp_dom_abt; eauto.
can_change_aop_solver.
eapply absinfer_eq.
apply absabort_rule.
eapply abscsq_rule.
apply noabs_oslinv.
eapply absinfer_get_temp_dom_succ; eauto.
can_change_aop_solver.
eapply absinfer_eq.

hoare_lifts_trms_pre Aop.
eapply seq_rule.
eapply excrit1_rule'_ISnil_ISRemp''.
intros; try unfold OSInv; sep pauto; trycancel.
sep cancel Aier.
sep cancel p_local.
unfold PartitionInv.
unfold Adomain2index.
unfold Adomain2index'.
unfold AKsCurDomain.
sep pauto; eauto.
repeat try (sep cancel 2%nat 1%nat; eauto).
auto.
pure_auto.

eapply seq_rule.
hoare_enter_critical.
hoare unfold.
unfold PartitionInv.
unfold ACorepartnum.
unfold ACorepartnum'.
hoare unfold.
hoare forward.
hoare_lifts_trms_pre (Aop, cpartnum).
match goal with
  | |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** Hcorepartnum ?cpn ** _ }} _ {{ _ }} =>
   rename cpn into rv_cpn
end.
assert (Hrv_num: vr_temp_num <> Vint32 rv_cpn \/ vr_temp_num = Vint32 rv_cpn) by tauto.
destruct Hrv_num as [Habt | Hrv_num].
eapply abscsq_rule.
apply noabs_oslinv.
eapply absinfer_get_temp_num_abt; eauto.
can_change_aop_solver.
eapply absinfer_eq.
apply absabort_rule.
eapply abscsq_rule.
apply noabs_oslinv.
eapply absinfer_get_temp_num_succ; eauto.
can_change_aop_solver.
eapply absinfer_eq.
subst.

hoare_lifts_trms_pre Aop.
eapply seq_rule.
eapply excrit1_rule'_ISnil_ISRemp''.
intros; try unfold OSInv; sep pauto; trycancel.
sep cancel Aier.
sep cancel p_local.
unfold PartitionInv.
unfold ACorepartnum.
unfold ACorepartnum'.
sep pauto; eauto.
repeat try (sep cancel 2%nat 1%nat; eauto).
auto.
pure_auto.

(* If (ebinop odiv (ebinop odiv ′ OS_USER_MAX_EVENTS ′ 3) temp_num ′ × temp_dom ′ >ₑ
    lident ′){RETURN ′ (-1)};ₛ *)
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
assert (Hif_cpu: Int.eq rv_cpn Int.zero || Int.eq ($ OS_USER_MAX_EVENTS / 3) ($ Int.min_signed) &&
                                Int.eq rv_cpn Int.mone = false).
{ rewrite Heqf'.
   destruct (Int.eq rv_cpn Int.zero) eqn: eq1; try tauto.
   eapply sem_lab.semacc_int_eq_true in eq1; subst.
   change (Int.unsigned Int.zero) with 0 in *.
   false; auto with zarith.
}

(* lets Hrgn': usr_max_evts_rgn'.
  destruct Hrgn' as (Hrgn5 & Hrgn6).
  assert (Hsieq : (Int.signed ($ OS_USER_MAX_EVENTS) / Int.signed ($ 3)) = (OS_USER_MAX_EVENTS / 3)).
  clear -Hrgn5 Hrgn6.
  int auto. *)
hoare forward; try rewrite Hdiveq; try rewrite Heqf;
try change (Int.eq ($ 3) Int.zero || false && Int.eq ($ 3) Int.mone) with false.
simpl val_inj; pure_auto.
eapply mund_int_a2; solve_part_int_rgn.
simpl val_inj; pure_auto.
simpl val_inj; pure_auto.
simpl val_inj; pure_auto.
simpl val_inj; pure_auto.
rewrite Hif_cpu; simpl val_inj.

hoare_lifts_trms_pre val_inj.
eapply pure_split_rule'; introv Hpos_lt.
destruct (Int.ltu posv (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) rv_cpn) rv_dom)) eqn: eq1;
simpl in Hpos_lt; destruct Hpos_lt as (Hpos_lt & _ ); tryfalse.

eapply abscsq_rule.
apply noabs_oslinv.
eapply absinfer_pos_lt_rgn_err; eauto.
can_change_aop_solver.
rewrite Hdiveq; auto.
eapply absinfer_eq.
instantiate (1:= Afalse).
eapply rete_rule.
introv Hsat.
split; [ | sep get rv].
change ($ 1) with Int.mone.
eapply Hr; eauto.
sep auto.

hoare forward.
simpl val_inj.
rewrite Hif_cpu; simpl val_inj.
hoare unfold.

eapply abscsq_rule.
apply noabs_oslinv.
eapply absinfer_pos_rgn_choice2_cons; eauto.
can_change_aop_solver.
eapply absinfer_eq.

clear - Hr Hfrm Haop Hnin_dom1 Hnin_dom2 Hnin_dom3 Hpre Heqf Hdiveq Heqf'.

eapply seq_rule.
hoare_enter_critical.
hoare unfold.
unfold PartitionInv.
unfold Adomain2index.
unfold Adomain2index'.
unfold AKsCurDomain.
hoare unfold.
hoare_lifts_trms_pre (Aop, kscurdom).
match goal with
| H: length ?vl = ?len
  |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** HKsCurDomain ?idx ** _ }} _ {{ _ }} =>
   rename idx into vcurd
end.
assert(Hvcurd : vcurd = Int.mone \/ vcurd <> Int.mone) by tauto.
destruct Hvcurd as [Habt | Hvcurd].
eapply abscsq_rule.
apply noabs_oslinv.
eapply absinfer_kscurdom_ext_abt; eauto.
can_change_aop_solver.
eapply absinfer_eq.
apply absabort_rule.
eapply abscsq_rule.
apply noabs_oslinv.
eapply absinfer_kscurdom_ext; eauto.
can_change_aop_solver.
eapply absinfer_eq.
match goal with H: _ \/ vcurd = Int.mone |- _ => destruct H as [Hcd_rgn | Hf]; try subst; tryfalse end.
destruct Hcd_rgn as (Hcd_pos & Hcd_lt).

hoare_lifts_trms_pre (Aop, Domain2Index, ksCurDomain).
match goal with
| H: length ?vl = ?len
  |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** _ Domain2Index _ ?vl ** GV ksCurDomain @ _ |-> Vint32 ?idx ** _ }} _ {{ _ }} =>
   rename H into Hlen; assert (Hle_len: (Z.to_nat (Int.unsigned idx) < len)%nat)
end.
solve_part_int_rgn.
lets Hnth: Hle_len.
eapply pure_lib.nthval'_has_value in Hnth; eauto.
destruct Hnth as (rv_dom' & Hnth & Hmat).
eapply seq_rule.
eapply assign_rule_lvar;
                [ intro s_; split; intro Hsat; try sep pauto
                | idtac
                | apply assign_type_match_true; simpl; auto | li_sepauto li].
introv Hsat.
sep_lifts_trms_in Hsat (A_dom_lenv, Domain2Index).
eapply array_member_rv_g; [eauto | eauto | eauto | try sep get rv | .. | ]; eauto.
solve_part_int_rgn.
solve_part_int_rgn.
simpl; auto.

hoare_lifts_trms_pre (Aop, kscurdom, domindexlist).
match goal with
  H: RLH_Dom2idx_P _ _ |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** _ ** HDomain2index ?absdomls ** _ }} _ {{ _ }} =>
   rename absdomls into domls; rename H into Hlh_dom
end.
assert (Hget_dom:get domls  vcurd = Some rv_dom').
eapply Hlh_dom; eauto.
eapply inline_bittblfunctions.nth_val'2nth_val; eauto.

assert (Hrv_dom': vr_temp_dom' <> Vint32 rv_dom' \/ vr_temp_dom' = Vint32 rv_dom') by tauto.
destruct Hrv_dom' as [Habt | Hrv_dom'].
eapply abscsq_rule.
apply noabs_oslinv.
eapply absinfer_get_temp_dom_abt; eauto.
can_change_aop_solver.
eapply absinfer_eq.
apply absabort_rule.
eapply abscsq_rule.
apply noabs_oslinv.
eapply absinfer_get_temp_dom_succ; eauto.
can_change_aop_solver.
eapply absinfer_eq.

hoare_lifts_trms_pre Aop.
eapply seq_rule.
eapply excrit1_rule'_ISnil_ISRemp''.
intros; try unfold OSInv; sep pauto; trycancel.
sep cancel Aier.
sep cancel p_local.
unfold PartitionInv.
unfold Adomain2index.
unfold Adomain2index'.
unfold AKsCurDomain.
sep pauto; eauto.
repeat try (sep cancel 2%nat 1%nat; eauto).
auto.
pure_auto.

eapply seq_rule.
hoare_enter_critical.
hoare unfold.
unfold PartitionInv.
unfold ACorepartnum.
unfold ACorepartnum'.
hoare unfold.
hoare forward.
hoare_lifts_trms_pre (Aop, cpartnum).
match goal with
  | |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** Hcorepartnum ?cpn ** _ }} _ {{ _ }} =>
   rename cpn into rv_cpn'
end.
assert (Hrv_num': vr_temp_num' <> Vint32 rv_cpn' \/ vr_temp_num' = Vint32 rv_cpn') by tauto.
destruct Hrv_num' as [Habt | Hrv_num'].
eapply abscsq_rule.
apply noabs_oslinv.
eapply absinfer_get_temp_num_abt; eauto.
can_change_aop_solver.
eapply absinfer_eq.
apply absabort_rule.
eapply abscsq_rule.
apply noabs_oslinv.
eapply absinfer_get_temp_num_succ; eauto.
can_change_aop_solver.
eapply absinfer_eq.
subst.

hoare_lifts_trms_pre Aop.
eapply seq_rule.
eapply excrit1_rule'_ISnil_ISRemp''.
intros; try unfold OSInv; sep pauto; trycancel.
sep cancel Aier.
sep cancel p_local.
unfold PartitionInv.
unfold ACorepartnum.
unfold ACorepartnum'.
sep pauto; eauto.
repeat try (sep cancel 2%nat 1%nat; eauto).
auto.
pure_auto.

(* If (lident ′
    ≥ ebinop odiv (ebinop odiv ′ OS_USER_MAX_EVENTS ′ 3) temp_num ′
      × (temp_dom ′ +ₑ ′ 1)){RETURN ′ (-1)};ₛ *)

assert (Hif_cpn': Int.eq rv_cpn' Int.zero || Int.eq ($ OS_USER_MAX_EVENTS / 3) ($ Int.min_signed) &&
                                Int.eq rv_cpn' Int.mone = false).
{ rewrite Heqf'.
   destruct (Int.eq rv_cpn' Int.zero) eqn: eq1; try tauto.
   eapply sem_lab.semacc_int_eq_true in eq1; subst.
   change (Int.unsigned Int.zero) with 0 in *.
   false; auto with zarith.
}

hoare forward; try rewrite Hdiveq; try rewrite Heqf;
try change (Int.eq ($ 3) Int.zero || false && Int.eq ($ 3) Int.mone) with false.
simpl val_inj; pure_auto.
eapply mund_int_a2; solve_part_int_rgn.
simpl val_inj; pure_auto.
simpl val_inj; pure_auto.
simpl val_inj; pure_auto.
simpl val_inj; pure_auto.
eapply mund_int_a2; solve_part_int_rgn.
simpl val_inj; pure_auto.
simpl val_inj; pure_auto.
simpl val_inj; pure_auto.
simpl val_inj; pure_auto.
simpl val_inj.
rewrite Hif_cpn'; simpl val_inj.

hoare_lifts_trms_pre val_inj.
eapply pure_split_rule'; introv Hpos_ge.

assert (Hpos_ge': Int.ltu posv (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) rv_cpn') (rv_dom' +ᵢ  Int.one)) = false).
{ clear - Hpos_ge.
  rewrite Intlt_false_is_Zge.
destruct (Int.ltu  (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) rv_cpn')  (rv_dom' +ᵢ  $ 1)) posv) eqn: eq1;
destruct (Int.eq posv (Int.mul (Int.divs ($ OS_USER_MAX_EVENTS / 3) rv_cpn')  (rv_dom' +ᵢ  $ 1))) eqn: eq2;
simpl in Hpos_ge; destruct Hpos_ge as (Hpos_ge & _ ); simpl val_inj in Hpos_ge; 
repeat (try change (Int.ltu Int.zero Int.zero) with false in *; 
                  try change (Int.ltu Int.zero Int.one) with true in *; simpl in *);
tryfalse;
try (eapply sem_lab.semacc_int_eq_true in eq2; subst);
try eapply sem_lab.semacc_int_eq_false in eq2;
try rewrite Intlt_false_is_Zge in eq1; 
try rewrite Intlt_true_is_Zlt in eq1;
auto with zarith.
eapply Z.le_ge.
eapply Z.lt_le_incl; eauto.
}

eapply abscsq_rule.
apply noabs_oslinv.
eapply absinfer_pos_ge_rgn_err; eauto.
can_change_aop_solver.
rewrite Hdiveq; auto.
eapply absinfer_eq.
instantiate (1:= Afalse).
eapply rete_rule.
introv Hsat.
split; [ | sep get rv].
change ($ 1) with Int.mone.
eapply Hr; eauto.
sep auto.

hoare forward.
simpl val_inj.
rewrite Hif_cpn'; simpl val_inj.
hoare unfold.

eapply abscsq_rule.
apply noabs_oslinv.
eapply absinfer_pos_rgn_choice2_cons; eauto.
can_change_aop_solver.
eapply absinfer_eq.
eapply backward_rule1; [ | eauto].
introv Hsat; sep auto.
Qed.

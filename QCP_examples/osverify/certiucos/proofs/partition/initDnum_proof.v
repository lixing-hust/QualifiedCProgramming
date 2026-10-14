Require Import ucos_include.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

(* Require Import os_program. *)
(* Require Import ifun_spec. *)
Require Import abs_op.
Require Import inv_prop.
Require Import symbolic_lemmas.
Require Import protect.
Require Import sem_lab.
Require Import cast_int_ptr_pure.
Require Import partition_xml_init.
Require Import abs_op_partition_ext.
Require Import ifun_spec.
Require Import partition_common.
Require Import Lia.
Require Import gjb_common.
Require Import tv_match.
Require Import Aarray_new_common.
Require Import symbolic_lemmas.
Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.
Require Import CapPure.
Require Import sem_common.
Require Import InitDNUM_pure.
Open Scope code_scope.
Open Scope int_scope.
Open Scope Z_scope.
Open Scope list_scope.
Open Scope int_scope.

Lemma initDnum_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal InitDNUM vl logicl initDnumPre ct->
      Some r =
      BuildRetI os_internal InitDNUM vl logicl initDnumPost ct->
      exists t d1 d2 s,
        os_internal InitDNUM = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
init spec.
subst logicl.
simpl in H0.
inverts H0.
simpl in H4.
inverts H4.

hoare forward. 
hoare forward. 

hoare_split_pure_all.
hoare_lifts_trms_pre (Alvarmapsto ios_cap_defs.i,Alvarmapsto j,AucosConf
,Alvarmapsto to1,Alvarmapsto tox1,Alvarmapsto coreNum, Adomain2index' ).
hoare remember (1::2::3::4::5::6::7::nil)%nat pre.

eapply backward_rule1 with ( p :=
(EX i0 j0 a1 vl b1,
  LV ios_cap_defs.i @ Int32u |-> (Vint32 i0) **
  LV j @ Int32u |-> (Vint32 j0) **
  [|Int.unsigned i0 < DOMAIN_SIZE |] ** 
 [|Int.unsigned j0 <= Int.unsigned i0 |] ** 
 [| ksDomain_P v'21 i0 (Z.to_nat (Int.unsigned v'24)) vl j0 v'23|] **
 AucosConf  v'21 v'22 **
 Adomain2index' vl **
 LV coreNum @ char_t |-> Vint32 v'24 ** 
 LV tox1 @ long |-> b1 **
 LV to1 @ char_t |-> a1 **  H) \\//
( 
  EX j0 vl a1 b1,
  LV j @ Int32u |-> (Vint32 j0) **
  LV ios_cap_defs.i @ Int32u |-> (V$ DOMAIN_SIZE) **
  [| ksDomain_P v'21  ($ DOMAIN_SIZE) (Z.to_nat (Int.unsigned v'24)) vl j0 v'23|] **
  LV coreNum @ char_t |-> Vint32 v'24 ** 
  [|Int.unsigned j0 <= DOMAIN_SIZE |] ** 
  AucosConf  v'21 v'22 ** 
  Adomain2index' vl **
  LV tox1 @ long |-> b1 **
  LV to1 @ char_t |-> a1 **  H )
).
intros.
left.
eexists (Int.repr 0) ,(Int.repr 0) ,v'3 ,v'23,v'11.
sep pauto.
2: int auto.
2: int auto.
unfold ksDomain_P .
unfold AucosConf in H0.

destruct v'21.
do 5 destruct p .
destruct v'22.
do 12 destruct p .
unfold ACPUs in H0.
sep normal in H0.
do 3 destruct H0.
sep split in H0.
simpl in H6.
eapply TmrMod.option2val in H6. 
inverts H6.
eapply Acpus'_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned v'24)) in H0. 
sep normal in H0.
sep destruct H0.
sep split in H0.

destruct H23 as (Hx1 & Hx1').
split.
intros. 
change ($ 0) with Int.zero in H23. 
rewrite unsigned_zero in H23. lia.

(* [0,8) *)
intros.
do 21 eexists. 
intros.
eauto.

eauto.
rewrite H5.
clear -H4. 
change CORENUM with 8. 
mauto.

eapply seq_rule.
eapply while_rule with (tp := Int32u).
intros.
destruct H0.
symbolic_execution.
pure_auto.
symbolic_execution.

eapply backward_rule1 with ( p:= 
  (EX i0 j0 a1 vl b1,
  LV ios_cap_defs.i @ Int32u |-> (Vint32 i0) **
  LV j @ Int32u |-> (Vint32 j0) **
  [|Int.unsigned i0 < DOMAIN_SIZE |] ** 
 [|Int.unsigned j0 <= Int.unsigned i0 |] ** 
 [| ksDomain_P v'21 i0 (Z.to_nat (Int.unsigned v'24)) vl j0 v'23|] **
 AucosConf v'21 v'22 **
 Adomain2index' vl **
 LV coreNum @ char_t |-> Vint32 v'24 ** 
 LV tox1 @ long |-> b1 **
 LV to1 @ char_t |-> a1 **  H) 
). 
intros.
destruct H0. 
destruct H0.
sep destruct H0.
do 5 eexists.
sep cancel 1%nat 1%nat.

sep destruct H0.
sep remember (2::nil)%nat in H0.
false.
destruct_s s.
simpl in H0; simpljoin1.
simpl in H4.
rewrite H15 in H4.
unfold cmp_int_type in H4.
unfold cmp_val in H4.
unfold cmpu in H4.
apply mapstoval_load in H16; auto.
destruct (load Int32u m (x16, 0)) eqn : eq1.
pose proof (load_mono Int32u (x16, Int.unsigned Int.zero) H7 H16).
rewrite H16 in H.
change (Int.unsigned Int.zero) with 0 in H.
rewrite H in eq1.
inverts eq1.
change (if Int.ltu ($ DOMAIN_SIZE) ($ DOMAIN_SIZE)
then Some (Vint32 Int.one)
else Some (Vint32 Int.zero)) with (Some (Vint32 Int.zero)) in H4.
destruct H4.
destruct H0.
inverts H0.
simpl in H4.
tryfalse.
destruct H4.
destruct H.
inverts H.

destruct v'21 as [[[[[[]]]]]].
destruct_absuconf v'22.
simpl AucosConf .
unfold node.
unfold ACPUs.
hoare unfold.
match goal with H: Int.unsigned i4 <= 255  |- _ => rename H into Hgi4 end.
match goal with H: Int.unsigned i3 <= 255  |- _ => rename H into Hgi3 end.
match goal with H: Int.unsigned i2 <= 255  |- _ => rename H into Hgi2 end.
match goal with H: Int.unsigned i1 <= 255  |- _ => rename H into Hgi1 end.
match goal with H: Int.unsigned i <= 255   |- _ => rename H into Hgi end.
unfold_bootaddr boot_b.

protect Heqboot_b.
inversion H8.
subst v'37.
subst.
destruct v'39 as (cpu_b, cpu_i).

match goal with H: length l = _ |- _ => rename H into Hlen_cpu end.

eapply backward_rule1.
introv Hsat.
sep_lifts_trms_in Hsat Acpus'.
eapply Acpus'_unfold_any_idx_frm with (idx:= Z.to_nat (Int.unsigned v'24)); eauto.
rewrite Hlen_cpu.
unfold CORENUM in *; unfold nat_of_Z; auto with zarith.
unfold node_offt.
hoare unfold.
match goal with H: id_addrval (boot_b, Int.zero) cpus ucos_conf_t = Some (?cb, ?cpu_i) |- _ => rename cb into cpu_b end.
rename H34 into H35.
rename H33 into H34.
rename H32 into H33.
rename H31 into H32.
rename H29 into H30.
rename H28 into H29.
rename H26 into H27.
rename H25 into H26.
rename H24 into H25.
rename H22 into H24.
remember (Vint32 i7
:: Vint32 i6
   :: Vint32 i4
      :: Vint32 i3
         :: Vint32 i2
            :: Vint32 i1
               :: x6
                  :: x5
                     :: x
                        :: x0
                           :: Vint32 i
                              :: x2 :: x3 :: Vint32 i5 :: nil) as v.
rename Heqv into H22.                             

destruct v'46 as (dom_b & dom_i).
hoare_lifts_trms_pre AksDomains'.
eapply backward_rule1.
introv Hsat.
sep_lifts_trms_in Hsat AksDomains'.
eapply AksDomains'_unfold_any_idx_frm with (idx:= Z.to_nat (Int.unsigned v'21)); eauto.
rewrite H0.
unfold nat_of_Z in *.
solve_part_int_rgn.
unfold node_offt.
hoare normal pre.
repeat (apply ex_intro_rule; intro).
hoare_split_pure_all.
destruct H8 as (Hptr & Hcap_mat); inverts Hptr.
destruct H39 as (Hptr & Hdom_mat); inverts Hptr.
inverts H9.
lets Hdom_mat': Hdom_mat.
lets Hdom_vl: struct_type_vallist_match_domain_conf_t Hdom_mat.
simpljoin.
simpl in Hdom_mat'.
simpljoin.
repeat try(match goal with
   H: match ?x with
         | Vint32 _ => _
         | _ => _
        end = true |- _ =>
   destruct x; tryfalse end).
   hoare forward.
   hoare_lifts_trms_pre ( Aop).
   eapply assign_rule_lvar.
   intros; split; intro Hsat.
   sep cancel tox1; eauto.
   sep auto.
  Optimize Proof.
  Optimize Heap.
   {
    introv Hsat .
    sep lift 16%nat in Hsat.
    sep_get_rv_array_struct_conf''.
    rewrite leb_bytemax_true_intro;eauto.
   }
   eapply eq_int; eauto.
   split;eauto.
   introv Hsat; eexists; sep cancel p_local; simpl; auto.

   change (LV tox1 @ long
   |-> nth_val' 3
         (Vint32 i23
         :: Vint32 i22
            :: Vint32 i21
               :: Vint32 i20
                  :: Vint32 i19
                     :: Vint32 i18
                        :: Vint32 i17
                           :: Vint32 i16
                              :: Vint32 i15
                                 :: Vint32 i14
                                    :: Vint32 i13
                                       :: Vint32 i12
                                          :: x20
                                             :: Vint32 i11
                                                :: 
                                                x22 :: x23 :: nil))
with  (LV tox1 @ long |-> Vint32 i20).

assert (Hor: (i20 = ($ 0) ) \/ 
(i20 <> ($ 0))) by tauto.
inversion Hor. 
hoare forward.
hoare unfold.
change (Int.eq ($ 0) ($ 0)) with true in H54.
simpl in H54.
change (Int.notbool Int.one) with Int.zero in H54.
tryfalse.
instantiate (1:= Afalse).
eapply hoare_disj_afalseP_l_pre.
hoare unfold.  
change (Int.eq ($ 0) ($ 0)) with true in H54. 
destruct H54. 
tryfalse.
2:{
simpl in H53.
change (Int.notbool Int.one) with Int.zero in H53. 
tryfalse.
}
unfold val_inj  in H53. unfold notint in H53. simpl in H53.
change CORENUM with 8 in *.
rewrite H0 in H43.
assert(Hcond: Z.of_nat (S (Z.to_nat (Int.unsigned v'21))) < Z.of_nat ∘ 8 \/
Z.of_nat (S (Z.to_nat (Int.unsigned v'21))) = Z.of_nat ∘ 8
).
{
  clear -H43.
  int auto.
}
assert(Heq: (S (Z.to_nat (Int.unsigned v'21))) =( Z.to_nat (Int.unsigned (v'21 +ᵢ  $ 1)))).
{
  clear -H43.
  int auto. 
  rewrite <- Z2Nat.inj_succ.
  mauto.
  eapply Int.unsigned_range_2.
  int auto.
  rewrite Z2Nat.id in H43.
  int auto.
  mauto.
}
destruct Hcond as [Hc1|Hc2].
(* case 1*)
hoare forward.
left.
do 5 eexists.
sep pauto.

2:  splits;eauto.
5: eauto.
eapply Acpus'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned v'24));eauto.
clear -H23.
change CORENUM with 8.
unfold nat_of_Z.
int_auto.
sep pauto.
2: eauto.
2: eauto.
2: {
  simpl.
  eauto.
}
5:{
  split;eauto.
  simpl.
  eapply leb_bytemax_true_intro in Hgi4,Hgi3,Hgi2,Hgi1,Hgi.
  simpl.
  rewrite Hgi4,Hgi3,Hgi2,Hgi1,Hgi.
  splits;eauto.
}
5:eauto.
eapply AksDomains'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned v'21));eauto.
clear -H10.
change CORENUM with 8.
change DOMAIN_SIZE with 8 in *.
unfold nat_of_Z.
int_auto.
sep pauto.
unfold node_offt.
sep pauto.
sep cancel 6%nat 1%nat.
sep cancel 2%nat 2%nat.
sep auto.
split;eauto.
eapply leb_bytemax_true_intro in H42,H45,H46,H47,H48,H50.
simpl.
rewrite H42,H45,H46,H47,H48,H50.
splits;eauto.
simpl (typelen cpu_conf_t).
split;eauto.
simpl;splits;eauto.
eauto.
eauto.
eauto.
2: {
  clear -H11 H10.
change DOMAIN_SIZE with 8 in H10.
  int auto.
  mauto.
}
2: 
{
  clear -Hc1 Heq.
  rewrite Heq in Hc1.
  rewrite Z2Nat.id in Hc1;eauto.
  eapply Int.unsigned_range_2.
}
assert(Hi: (Int.unsigned (v'21 +ᵢ  $ 1) - 1) = (Int.unsigned v'21)).
{
  clear -H10.
  change DOMAIN_SIZE with 8 in *.
  int auto.
  splits.
  eapply Z.add_nonneg_nonneg.
  eapply Int.unsigned_range_2.
  eapply Int.unsigned_range_2.
  int auto.
}
destruct v'42.
{
  false.
  rewrite H0 in H39.
  rewrite Heq in H39.
  rewrite Heq in Hc1.
  clear -H39 Hc1 .
  change (length nil) with 0%nat in H39.
  rewrite Z2Nat.id in H39.
  rewrite Z2Nat.id in H39.
  unfold nat_of_Z in H39. 

  assert (Z.to_nat (8 - Int.unsigned (v'21 +ᵢ  $ 1)) =
  (Z.to_nat 8 - Z.to_nat (Int.unsigned (v'21 +ᵢ  $ 1)))%nat
  ).
  eapply Z2Nat.inj_sub. 
  eapply Int.unsigned_range_2.
  rewrite H in H39.
  clear H. 
  rewrite Nat.eq_sym_iff in H39.
  rewrite NPeano.Nat.sub_0_le in H39.
  rewrite Z2Nat.id in Hc1;eauto.
  rewrite Z2Nat.id in Hc1;eauto.
  auto with zarith.
  mauto.
  eapply Int.unsigned_range_2.
  eapply Int.unsigned_range_2.
  mauto.
}

(* ksDomain_P *)
{
change DOMAIN_SIZE with 8 in *.
unfold ksDomain_P.
split.
intros.
assert (Hcond: 0 <= k < Int.unsigned v'21  \/ k = Int.unsigned v'21).
clear -H10 H56.

int auto.
  Optimize Proof.
  Optimize Heap.
mauto.
destruct Hcond as [Hca1 | Hca2].
lets Hcnew: Hca1.
eapply H12 in Hca1.
destruct Hca1.
simpljoin.
do 20 eexists.
splits;eauto.
splits;eauto.
intros.
assert(Hi_1:Int.unsigned (v'21 +ᵢ  $ 1) - 1 = Int.unsigned v'21).
{
clear -H10.
int auto.
splits.
eapply Z.add_nonneg_nonneg.
eapply Int.unsigned_range_2.
eapply Int.unsigned_range_2.
int auto.
}
rewrite Hi_1 in H57.
lia. 
2:{
  (* [0,8) *)
  unfold ksDomain_P in H12.
  destruct H12.
  eauto.
}
(* k= i *)
rewrite Hca2 .
do 20 eexists.
splits.
eauto.
rewrite <-H32.
rewrite nth_error_middle;eauto.
eauto.
unfold nat_of_Z.
rewrite <-H9.
rewrite nth_error_middle;eauto.
eauto.
simpl;eauto.
simpl;eauto.
splits;eauto.
2:{
  eexists.
  intros.
  tryfalse.
}
assert(Hi_eq: Int.unsigned v'21 = 0 \/ Int.unsigned v'21 > 0).
clear -H10 Hca2 H56.
int auto.
mauto.
destruct Hi_eq.
assert(Hj'_v : v'22 = ($ 0)).
{
clear -H11 H10 H57.
rewrite H57 in H11.
assert(0<=Int.unsigned v'22).
eapply Int.unsigned_range_2.
clear -H H11.
mauto. 
}
inverts Hj'_v.
rewrite H57 in *.
eapply length_zero_nil in H9.
rewrite H9.
change (0 + 1) with 1.
simpl.
rewrite Int.eq_true;eauto.
(* v'21>0 *)
destruct H12.
lets Hi_2 : H12 (Int.unsigned v'21 - 1).
destruct Hi_2.
clear -H57.
int auto.
simpljoin.
destruct H68.
eauto.
assert(Hv21: Int.unsigned v'21 - 1 + 1 = Int.unsigned v'21).
{
  clear.
  int auto.
}
rewrite Hv21 in H67.
assert(∘ (Int.unsigned v'21 + 1) = S ∘ (Int.unsigned v'21)).
{
  clear -H57 H10.
  unfold nat_of_Z.
  int auto.
}
destruct ∘ (Int.unsigned v'21 + 1).
tryfalse.
inverts H59.
simpl.
unfold nat_of_Z.
rewrite <-H9 at 1.
rewrite nth_error_middle.
rewrite <-H32 in H60.
rewrite nth_error_middle in H60.
inverts H60.
eapply H67.
}

(* case 2 *)
hoare forward.
rewrite Heq in Hc2.
rewrite Z2Nat.id in Hc2;eauto.
rewrite Z2Nat.id in Hc2;eauto.
assert(Heq1: (v'21 +ᵢ  $ 1) = $ 8).
{
  clear -Hc2 H10.
  change DOMAIN_SIZE with 8 in *.
  int auto.
  mauto.
}
rewrite Heq1 in H54.
eapply adisj_intro.
right.
sep pauto.
eapply Acpus'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned v'24));eauto.
clear -H23.
change CORENUM with 8.
unfold nat_of_Z.
int_auto.
sep pauto.
2: eauto.
2: eauto.
2: {
  simpl.
  eauto.
}
5:{
split;eauto.
eapply leb_bytemax_true_intro in Hgi4,Hgi3,Hgi2,Hgi1,Hgi.
simpl.
rewrite Hgi4,Hgi3,Hgi2,Hgi1,Hgi.
splits;eauto.
}
5:eauto.
eapply AksDomains'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned v'21));eauto.
clear -H10.
change CORENUM with 8.
change DOMAIN_SIZE with 8 in *.
unfold nat_of_Z.
int_auto.
sep pauto.
unfold node_offt.
sep pauto.
sep cancel 6%nat 1%nat.
sep cancel 2%nat 2%nat.
sep auto.
split;eauto.
eapply leb_bytemax_true_intro in H50,H48,H47,H46,H45,H42.
simpl.
rewrite H50,H48,H47,H46,H45,H42.
splits;eauto.
simpl (typelen cpu_conf_t).
split;eauto.
simpl;splits;eauto.
eauto.
eauto.
eauto.
splits;eauto.
clear -H11 H10.
change DOMAIN_SIZE with 8 in *.
int auto.

2: clear;int_auto.
2: eapply Int.unsigned_range_2.

(* ksDomain_P *)
change DOMAIN_SIZE with 8 in *.
assert(Hi: (Int.unsigned (v'21 +ᵢ  $ 1) - 1) = (Int.unsigned v'21)).
{
  clear -H10.
  int auto.
  splits.
  eapply Z.add_nonneg_nonneg.
  eapply Int.unsigned_range_2.
  eapply Int.unsigned_range_2.
  int auto.
  Optimize Proof.
  Optimize Heap.
}
rewrite <-Hc2.
rewrite Int.repr_unsigned.
{
unfold ksDomain_P.
split.
intros.
assert (Hcond: 0 <= k < Int.unsigned v'21  \/ k = Int.unsigned v'21).
clear -H10 H56.
int auto.
mauto.
destruct Hcond as [Hca1 | Hca2].
lets Hcnew: Hca1.
eapply H12 in Hca1.
destruct Hca1.
simpljoin.
do 20 eexists.
splits;eauto.
splits;eauto.
intros.
assert(Hi_1:Int.unsigned (v'21 +ᵢ  $ 1) - 1 = Int.unsigned v'21).
{
clear -H10.
int auto.
splits.
eapply Z.add_nonneg_nonneg.
eapply Int.unsigned_range_2.
eapply Int.unsigned_range_2.
int auto.
}
rewrite Hi_1 in H57.
lia. 
2:{
  (* [0,8) *)
  unfold ksDomain_P in H12.
  destruct H12.
  eauto.
}
(* k= i *)
rewrite Hca2 .
do 20 eexists.
splits.
eauto.
rewrite <-H32.
rewrite nth_error_middle;eauto.
eauto.
unfold nat_of_Z.
rewrite <-H9.
rewrite nth_error_middle;eauto.
eauto.
simpl;eauto.
simpl;eauto.
splits;eauto.
2:{
  eexists.
  intros.
  tryfalse.
}
assert(Hi_eq: Int.unsigned v'21 = 0 \/ Int.unsigned v'21 > 0).
clear -H10 Hca2 H56.
int auto.
mauto.
destruct Hi_eq.
assert(Hj'_v : v'22 = ($ 0)).
{
clear -H11 H10 H57.
rewrite H57 in H11.
assert(0<=Int.unsigned v'22).
eapply Int.unsigned_range_2.
clear -H H11.
mauto. 
}
inverts Hj'_v.
rewrite H57 in *.
eapply length_zero_nil in H9.
rewrite H9.
change (0 + 1) with 1.
simpl.
rewrite Int.eq_true;eauto.
(* v'21>0 *)
destruct H12.
lets Hi_2 : H12 (Int.unsigned v'21 - 1).
destruct Hi_2.
clear -H57.
int auto.
simpljoin.
destruct H68.
eauto.
assert(Hv22: Int.unsigned v'21 - 1 + 1 = Int.unsigned v'21).
{
  clear.
  int auto.
}
rewrite Hv22 in H67.
assert(∘ (Int.unsigned v'21 + 1) = S ∘ (Int.unsigned v'21)).
{
  clear -H57 H10.
  unfold nat_of_Z.
  int auto.
}
destruct ∘ (Int.unsigned v'21 + 1).
tryfalse.
inverts H59.
simpl.
unfold nat_of_Z.
rewrite <-H9 at 1.
rewrite nth_error_middle.
rewrite <-H32 in H60.
rewrite nth_error_middle in H60.
inverts H60.
eapply H67.
}

unfold Adomain2index' at 2.
hoare unfold.
assert (Hdomg: 0<= Int.unsigned v'21 < DOMAIN_SIZE).
{
  clear -H10.
  int auto.
}
change DOMAIN_SIZE with 8 in Hdomg.
lets HCPUg: H.
unfold CPU_ksDomains_Good in H.
destruct H as (Hdom_idx & _ & _).
eapply Hdom_idx in Hdomg.
simpljoin.
unfold nat_of_Z in H.
rewrite <-H9 in H.
rewrite nth_error_middle in H.
inverts H.
unfolds in H57.
simpl in H57.
inverts H57.

(* to1′ =ₑ  ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..domain;ₛ  *)
hoare forward.
pure_auto.
pure_auto.
hoare forward.
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel to1; eauto.
sep auto.
{
 introv Hsat .
 sep lift 17%nat in Hsat. 
 sep_get_rv_array_struct_conf''.
 rewrite leb_bytemax_true_intro;eauto.
}
eapply eq_int; eauto.
introv Hsat; eexists; sep cancel p_local; simpl; auto.
change (LV to1 @ char_t
|-> nth_val' 0
      (Vint32 x1
      :: Vint32 i22
         :: Vint32 i21
            :: Vint32 i20
               :: Vint32 i19
                  :: Vint32 i18
                     :: Vint32 i17
                        :: Vint32 i16
                           :: Vint32 i15
                              :: Vint32 i14
                                 :: Vint32 i13
                                    :: Vint32 i12
                                       :: x20
                                          :: Vint32 i11
                                             :: 
                                             x22 :: x23 :: nil))
with (LV to1 @ char_t |-> Vint32 x1).
(* Domain2Index′[ to1′ ] =ₑ j′;ₛ  *)
hoare forward.
(* ++j *)
hoare forward.
(* 将两种情况分开 *)
hoare forward.
2:{
  hoare unfold.
  destruct  (Int.eq i20 ($ 0)) eqn:Hi12.
  eapply semacc_int_eq_true in Hi12.
  tryfalse.
  unfold val_inj in H.
  unfold notint in H. 
  destruct H; inverts H.
}
hoare_split_pure_all.
clear H H57.
change CORENUM with 8 in H0.
rewrite H0 in H43. 
assert(Hcond: Z.of_nat (S (Z.to_nat (Int.unsigned v'21))) < Z.of_nat ∘ 8 \/
Z.of_nat (S (Z.to_nat (Int.unsigned v'21))) = Z.of_nat ∘ 8
).
{
clear -H43.
int auto.
  Optimize Proof.
  Optimize Heap.
}
assert(Heq: (S (Z.to_nat (Int.unsigned v'21))) =( Z.to_nat (Int.unsigned (v'21 +ᵢ  $ 1)))).
{
  clear -H43.
  int auto. 
  rewrite <- Z2Nat.inj_succ.
  mauto.
  eapply Int.unsigned_range_2.
  int auto.
  rewrite Z2Nat.id in H43.
  int auto.
  mauto.
}
destruct Hcond as [Hc1|Hc2].
(* case 1*)
hoare forward.
left.
do 5 eexists.
sep auto.
2:  splits;eauto.
5: eauto.
5:{
split;eauto.
eapply leb_bytemax_true_intro in Hgi4,Hgi3,Hgi2,Hgi1,Hgi.
simpl.
rewrite Hgi4,Hgi3,Hgi2,Hgi1,Hgi.
splits;eauto.
}
5:eauto.
eapply Acpus'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned v'24));eauto.
clear -H23.
change CORENUM with 8.
unfold nat_of_Z.
int_auto.
sep pauto.
2: eauto.
2: eauto.
2: {
  simpl.
  eauto.
}
eapply AksDomains'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned v'21));eauto.
clear -H10.
change CORENUM with 8.
change DOMAIN_SIZE with 8 in *.
unfold nat_of_Z.
int_auto.
sep pauto.
unfold node_offt.
sep pauto.
sep cancel 6%nat 1%nat.
sep cancel 2%nat 2%nat.
simpl (typelen domain_conf_t).
unfold Adomain2index'.
sep auto.
split;eauto.
eapply array_type_vallist_match_hold;eauto.
rewrite H56.
clear - H59.
change DOMAIN_SIZE with 8 in *.
int_auto.
assert (Hv23: Int.unsigned v'22 < DOMAIN_SIZE).
{
  clear -H10 H11.
  int_auto.
}
simpl.
rewrite leb_bytemax_true_intro;eauto.
clear -Hv23.
change DOMAIN_SIZE with 8 in *.
int_auto.
rewrite <-H56.
eapply update_nth_val_len_eq.
split;eauto.
eapply leb_bytemax_true_intro in H50,H48,H47,H46,H45,H42.
simpl.
rewrite H50,H48,H47,H46,H45,H42.
splits;eauto.
simpl (typelen cpu_conf_t).
split;eauto.
simpl;splits;eauto.
eauto.
eauto.
eauto.
2: {
  clear -H11 H10.
  change DOMAIN_SIZE with 8 in H10.
  int auto.
  int_auto.
  mauto.
}
2:
{
rewrite Heq in Hc1.
clear -Hc1.
change DOMAIN_SIZE with 8.
unfold nat_of_Z in *.
rewrite Z2Nat.id in Hc1;eauto.
eapply Int.unsigned_range_2.
}
assert(Hi: (Int.unsigned (v'21 +ᵢ  $ 1) - 1) = (Int.unsigned v'21)).
{
  clear -H10.
  int auto.
  splits.
  eapply Z.add_nonneg_nonneg.
  eapply Int.unsigned_range_2.
  eapply Int.unsigned_range_2.
  change DOMAIN_SIZE with 8 in H10.
  int auto.
}
destruct v'42.
{
  false.
  rewrite H0 in H39.
  rewrite Heq in H39.
  rewrite Heq in Hc1.
  clear -H39 Hc1 .
  change (length nil) with 0%nat in H39.
  rewrite Z2Nat.id in H39.
  rewrite Z2Nat.id in H39.
  unfold nat_of_Z in H39. 

  assert (Z.to_nat (8 - Int.unsigned (v'21 +ᵢ  $ 1)) =
  (Z.to_nat 8 - Z.to_nat (Int.unsigned (v'21 +ᵢ  $ 1)))%nat
  ).
  eapply Z2Nat.inj_sub. 
  eapply Int.unsigned_range_2.
  rewrite H in H39.
  clear H. 
  rewrite Nat.eq_sym_iff in H39.
  rewrite NPeano.Nat.sub_0_le in H39.
  rewrite Z2Nat.id in Hc1;eauto.
  rewrite Z2Nat.id in Hc1;eauto.
  auto with zarith.
  mauto.
  eapply Int.unsigned_range_2.
  eapply Int.unsigned_range_2.
  mauto.
}
(* ksDomain_P  yes *)
change DOMAIN_SIZE with 8 in *.
unfold ksDomain_P.
split.
intros.
assert (Hcond: 0 <= k < Int.unsigned v'21  \/ k = Int.unsigned v'21).
clear -H10 H57.
int auto.
mauto.
destruct Hcond as [Hca1 | Hca2].
lets Hcnew: Hca1.
eapply H12 in Hca1.
simpljoin.
do 20 eexists.
splits;eauto.
splits;eauto.
intros. 
assert(Hi_1:Int.unsigned (v'21 +ᵢ  $ 1) - 1 = Int.unsigned v'21).
{
clear -H10.
int auto.
splits.
eapply Z.add_nonneg_nonneg.
eapply Int.unsigned_range_2.
eapply Int.unsigned_range_2.
int auto.
}
rewrite Hi_1 in H61.
lia. 
eexists.
intros.
destruct H72.
eauto.
splits;eauto.
eapply nth_upd_neqrev;eauto.
lets Hcpug1: HCPUg.
destruct HCPUg as (_ & Hdxnop & _ & _).
unfolds in Hdxnop.
lets Hnew: Hdxnop k (Int.unsigned v'21). 
specializes Hnew.
clear -H63 H62 H10.
change CORENUM with 8 .
int_auto.
clear -H10.
change CORENUM with 8 in *.
int_auto.
clear -H63.
lia.
  Optimize Proof.
  Optimize Heap.
rewrite <-H32 in H64.
rewrite nth_error_middle in H64.
inverts H64.
eapply H66.
unfold nat_of_Z.
rewrite <-H9.
eapply nth_error_middle ;eauto.
eauto.
unfold V_domain.
simpl;eauto.
intro.
eapply Hnew.
eapply inline_bittblfunctions.z2n_int_eq in H72.
eauto.
2:{
  destruct H12.
  intros.
  lets Hnew_j : H57 k'.
  destruct Hnew_j.
  eauto.
  do 20 destruct H62.
  do 21 eexists.
  intros.
  eauto. }

(* k = i *)
rewrite Hca2.
assert(Hi_eq: Int.unsigned v'21 = 0 \/ Int.unsigned v'21 > 0).
 clear -H10 Hca2 H57.
 int auto.
 mauto.
 destruct Hi_eq.
 assert(Hj'_v : v'22 = ($ 0)).
 {
 clear -H61 H10 H11.
 rewrite H61 in H11.
 assert(0<=Int.unsigned v'22).
 eapply Int.unsigned_range_2.
 clear -H H11.
 mauto. 
 }  
 inverts Hj'_v.
 do 20 eexists.
 splits.
 eauto.
 rewrite <-H32.
 eapply nth_error_middle ;eauto.
 eauto.
 unfold nat_of_Z.
 rewrite <-H9.
 eapply nth_error_middle ;eauto.
 eauto.
 simpl;eauto.
 simpl;eauto.
 splits;eauto.
 rewrite H61 in *.
 eapply length_zero_nil in H9.
rewrite H9.
 change (0 + 1) with 1.
 simpl.
 eapply Int.eq_false in H53.
 rewrite H53.
 clear .
 int_auto.
 int_auto.
 eexists.
 intros.
 splits;eauto.

 eapply nth_val'2nth_val_dom.
 eapply len_lt_update_get_eq.
 rewrite H56.
 clear -H59.
 int_auto.
  (* i>0 *)
  do 20 eexists.
  splits.
  eauto.
  rewrite <-H32.
  eapply nth_error_middle ;eauto.
  eauto.
  unfold nat_of_Z.
  rewrite <-H9.
  eapply nth_error_middle ;eauto.
  eauto.
  simpl;eauto.
  simpl;eauto.
  splits;eauto.
  unfold ksDomain_P in H12.
  destruct H12.
  lets Hi_2 : H12 (Int.unsigned v'21 - 1).
  destruct Hi_2.
  clear -H61.
  int auto.
  simpljoin.
  assert(Hvi : Int.unsigned v'21 - 1 + 1 = Int.unsigned v'21).
{
  clear.
  int auto.
}
rewrite Hvi in H70.
destruct H71.
clear.
int auto.
assert(∘ (Int.unsigned v'21 + 1) = S ∘ (Int.unsigned v'21)).
{
unfold nat_of_Z.
clear -H10 H61.
int auto.
}
destruct ∘ (Int.unsigned v'21 + 1).
tryfalse.
inverts H63.
unfold nat_of_Z in *.
simpl.
rewrite <-H9 at 1 .
rewrite nth_error_middle;eauto.
simpl.
eapply Int.eq_false in H53.
rewrite H53.
rewrite <-H32 in H64.
rewrite nth_error_middle in H64.
inverts H64.
rewrite H70.
{
  clear -H11 H10 H61.
  int_auto.
  rewrite <-Z2Nat.inj_succ.
  int_auto.
  int_auto.
  int_auto.
}
 (* 值表更新 *)
 eexists.
 intros.
 splits;eauto.
 assert((v'22 +ᵢ  $ 1) -ᵢ $ 1 = v'22).
clear -H62 H10 H11.
assert(0<=Int.unsigned v'22).
eapply Int.unsigned_range_2.
int auto.
rewrite H63. 
eapply nth_val'2nth_val_dom.
eapply len_lt_update_get_eq.
rewrite H56.
clear -H59.
int_auto.
(* case 2 *)
hoare forward.
rewrite Heq in Hc2.
rewrite Z2Nat.id in Hc2;eauto.
rewrite Z2Nat.id in Hc2;eauto.
assert(Heq1: (v'21 +ᵢ  $ 1) = $ 8).
{
  clear -Hc2 H10.
  int auto.
  change DOMAIN_SIZE with 8 in H10.
  mauto.
}
rewrite Heq1 in H.
eapply adisj_intro.
right.
sep pauto.
eapply Acpus'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned v'24));eauto.
clear -H23.
change CORENUM with 8.
unfold nat_of_Z.
int_auto.
sep pauto.
2: eauto.
2: eauto.
2: {
  simpl.
  eauto.
}
5:{
  split;eauto.
  eapply leb_bytemax_true_intro in Hgi4,Hgi3,Hgi2,Hgi1,Hgi.
  simpl.
  rewrite Hgi4,Hgi3,Hgi2,Hgi1,Hgi.
  splits;eauto.
  }
eapply AksDomains'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned v'21));eauto.
clear -H10.
change CORENUM with 8.
change DOMAIN_SIZE with 8 in *.
unfold nat_of_Z.
int_auto.
sep pauto.
unfold node_offt.
sep pauto.
sep cancel 8%nat 1%nat.
sep cancel 7%nat 1%nat.
unfold Adomain2index'.
sep auto.
  Optimize Proof.
  Optimize Heap.
split;eauto.
eapply array_type_vallist_match_hold;eauto.
rewrite H56.
clear - H59.
change DOMAIN_SIZE with 8 in *.
int_auto.
assert (Hv23: Int.unsigned v'22 < DOMAIN_SIZE).
{
  clear -H10 H11.
  int_auto.
}
simpl.
rewrite leb_bytemax_true_intro;eauto.
clear -Hv23.
change DOMAIN_SIZE with 8 in *.
int_auto.
rewrite <-H56.
eapply update_nth_val_len_eq.
split;eauto.
eapply leb_bytemax_true_intro in H50,H48,H47,H46,H45,H42.
simpl.
rewrite H50,H48,H47,H46,H45,H42.
splits;eauto.
simpl (typelen cpu_conf_t).
split;eauto.
simpl;splits;eauto.
eauto.
eauto.
eauto.
splits;eauto.
assert (Hv23: Int.unsigned v'22 < DOMAIN_SIZE).
{
  clear -H10 H11.
  int_auto.
}
clear -Hv23.
change DOMAIN_SIZE with 8 in *.
int_auto.
int_auto.
2: simpl; eauto.
2: clear ; int_auto.
2: eapply Int.unsigned_range_2.

assert(Heq7: v'21 = $ 7).
clear - Heq1 H10.
change DOMAIN_SIZE with 8.
rewrite <-eq_7add1 in Heq1.
assert(v'21 +ᵢ  $ 1 -ᵢ  $ 1= $ 7 +ᵢ  $ 1 -ᵢ  $ 1).
rewrite Heq1.
eauto.
assert((v'21 +ᵢ  $ 1) -ᵢ $ 1 = v'21).
clear -H10.
int auto. 
change DOMAIN_SIZE with 8 in H10. 
int_auto.
assert(($ 7 +ᵢ  $ 1) -ᵢ $ 1 = $ 7).
clear. 
int_auto.
rewrite H0 in H.
rewrite H1 in H.
eauto.
change DOMAIN_SIZE with 8.
rewrite <-Heq1.

(* ksDomain_P  yes *)
unfold ksDomain_P.
split.
intros.
assert (Hcond: 0 <= k < Int.unsigned v'21  \/ k = Int.unsigned v'21).
clear -H10 H57.
int auto.
mauto.
destruct Hcond as [Hca1 | Hca2].
lets Hcnew: Hca1.
eapply H12 in Hca1.
simpljoin.
do 20 eexists.
splits;eauto.
splits;eauto.
intros. 
assert(Hi_1:Int.unsigned ($ 7 +ᵢ  $ 1) - 1 = Int.unsigned ($ 7)).
{
clear .
rewrite eq_7add1.
int auto.
}
rewrite Hi_1 in H61.
lia. 
eexists.
intros.
destruct H72.
eauto.
splits;eauto.
eapply nth_upd_neqrev;eauto.
lets Hcpug1: HCPUg.
destruct HCPUg as (_ & Hdxnop & _ & _).
unfolds in Hdxnop.
lets Hnew: Hdxnop k (Int.unsigned ($ 7)). 
specializes Hnew.
clear -H63 H62 H10.
change CORENUM with 8 .
int_auto.
clear -H10.
change CORENUM with 8 in *.
int_auto.
clear -H63.
lia.
rewrite <-H32 in H64.
rewrite nth_error_middle in H64.
inverts H64.
eapply H66.
unfold nat_of_Z.
rewrite <-H9.
eapply nth_error_middle ;eauto.
eauto.
unfold V_domain.
simpl;eauto.
intro.
eapply Hnew.
eapply inline_bittblfunctions.z2n_int_eq in H72.
eauto.
2:{
  destruct H12.
  intros.
  lets Hnew_j : H57 k'.
  destruct Hnew_j.
  eauto.
  do 20 destruct H62.
  do 21 eexists.
  intros.
  eauto. }

(* k = i *)
rewrite Hca2.
assert( Int.unsigned v'21 > 0).
rewrite Heq7.
 clear .
 int auto.

  (* i>0 *)
  do 20 eexists.
  splits.
  eauto.
  rewrite <-H32.
  eapply nth_error_middle ;eauto.
  eauto.
  unfold nat_of_Z.
  rewrite <-H9.
  eapply nth_error_middle ;eauto.
  eauto.
  simpl;eauto.
  simpl;eauto.
  splits;eauto.
  unfold ksDomain_P in H12.
  destruct H12.
  lets Hi_2 : H12 (Int.unsigned v'21 - 1).
  destruct Hi_2.
  clear -H61.
  int auto.
  simpljoin.
  assert(Hvi : Int.unsigned ($ 7) - 1 + 1 = Int.unsigned ($ 7)).
{
  clear.
  int auto.
}
rewrite Hvi in H70.
destruct H71.
clear.
int auto.
assert(∘ (Int.unsigned ($ 7) + 1) = S ∘ (Int.unsigned ($ 7))).
{
unfold nat_of_Z.
clear .
int auto.
}
destruct ∘ (Int.unsigned ($ 7) + 1).
tryfalse.
inverts H63.
unfold nat_of_Z in *.
simpl.
rewrite <-H9 at 1 .
rewrite nth_error_middle;eauto.
simpl.
eapply Int.eq_false in H53.
rewrite H53.
rewrite <-H32 in H64.
rewrite nth_error_middle in H64.
inverts H64.
rewrite H70.
{
  clear -H11 H10 H61.
  int_auto.
  rewrite <-Z2Nat.inj_succ.
  int_auto.
  int_auto.
  int_auto.
}
 (* 值表更新 *)
 eexists.
 intros.
 splits;eauto.
 assert((v'22 +ᵢ  $ 1) -ᵢ $ 1 = v'22).
clear -H61 H10 H11.
assert(0<=Int.unsigned v'22).
eapply Int.unsigned_range_2.
change DOMAIN_SIZE with 8 in *.
int auto.
  Optimize Proof.
  Optimize Heap.
rewrite H63. 
eapply nth_val'2nth_val_dom.
eapply len_lt_update_get_eq.
rewrite H56.
clear -H59.
int_auto. 

(* Afalse *)
eapply backward_rule1 with (p := 
(
  (EX j0 vl a1 b1,
  LV j @ Int32u |-> (Vint32 j0) **
  LV ios_cap_defs.i @ Int32u |-> (V$ DOMAIN_SIZE) **
  [| ksDomain_P v'21  ($ DOMAIN_SIZE) (Z.to_nat (Int.unsigned v'24)) vl j0 v'23|] **
  LV coreNum @ char_t |-> Vint32 v'24 ** 
  [|Int.unsigned j0 <= DOMAIN_SIZE |] ** 
  AucosConf v'21 v'22 ** 
  Adomain2index' vl **
  LV tox1 @ long |-> b1 **
  LV to1 @ char_t |-> a1 **  H ) **
     [| Vint32 Int.zero = Vint32 Int.zero \/ Vint32 Int.zero = Vnull |]
)).
intros.
destruct H0.
destruct H0.
lets Hnew: aconj_intro H0 H4.
clear H0 H4.
eapply sep_aconj_r_aisfalse_to_astar in Hnew.
2 : {
intros.
sep destruct H0.
sep get rv. 
sep split in H0.
assert (Int.ltu x ($ DOMAIN_SIZE) = true).
{
clear -H4.
change DOMAIN_SIZE with 8 in *.
int auto.
}
rewrite H8.
eauto.
eauto.
}
sep normal in Hnew.
destruct Hnew. 
sep destruct H0.
sep split in H0.
destruct H8; tryfalse.
lets Hnew: aconj_intro H0 H4.
clear H0 H4.
eapply sep_aconj_r_aisfalse_to_astar in Hnew.
2 : {
intros.
sep destruct H0.
sep get rv.
}
assert (Int.ltu ($ DOMAIN_SIZE) ($ DOMAIN_SIZE) = false).
clear .
change DOMAIN_SIZE with 8.
int auto.
rewrite H0 in Hnew.
sep split in Hnew.
simpl in H4.
sep pauto.
(* end for *)

destruct v'21 as [[[[[[]]]]]].
destruct_absuconf v'22.
simpl AucosConf .
unfold node.
unfold ACPUs.
hoare unfold.
clear H14.
unfold_bootaddr boot_b.
protect Heqboot_b.
match goal with H: Int.unsigned i4 <= 255  |- _ => rename H into Hgi4 end.
match goal with H: Int.unsigned i3 <= 255  |- _ => rename H into Hgi3 end.
match goal with H: Int.unsigned i2 <= 255  |- _ => rename H into Hgi2 end.
match goal with H: Int.unsigned i1 <= 255  |- _ => rename H into Hgi1 end.
match goal with H: Int.unsigned i <= 255   |- _ => rename H into Hgi end.

inversion H8.
subst v'37.
subst.
destruct v'38 as (cpu_b, cpu_i).
match goal with H: length l = _ |- _ => rename H into Hlen_cpu end.
eapply backward_rule1.
introv Hsat.
sep_lifts_trms_in Hsat Acpus'.
eapply Acpus'_unfold_any_idx_frm with (idx:= Z.to_nat (Int.unsigned v'24)); eauto.
rewrite Hlen_cpu.
unfold CORENUM in *; unfold nat_of_Z; auto with zarith.
unfold node_offt.
hoare unfold.
eapply leb_bytemax_true_intro in Hgi4,Hgi3,Hgi2,Hgi1,Hgi.

(* len′ =ₑ ((uconf′→ cpus)[coreNum′])..cpu_ksDomScheduleLength ;ₛ  *)
hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel len; eauto.
sep auto.
{
introv Hsat .
sep lift 11%nat in Hsat. 
sep_get_rv_array_struct_conf1.
rewrite leb_bytemax_true_intro;eauto.
simpl;splits;eauto.
}
eapply eq_int; eauto.
split;eauto.
introv Hsat; eexists; sep cancel p_local; simpl; auto.
change (LV len @ long |-> nth_val' 2 (Vint32 i10 :: x4 :: Vint32 i9 :: Vint32 i8 :: x9 :: x10 :: nil))
with (LV len @ long |-> Vint32 i9).

(* Core_partition_num ′ =ₑ ((uconf ′ → cpus) [coreNum ′]) .. ksDomainLength;ₛ *)
unfold ACorepartnum'.
hoare unfold.
hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_gvar.
intros; split; intro Hsat.
sep cancel  A_dom_lenv.
sep cancel Core_partition_num; eauto.
sep auto.
simpl;eauto.
{
introv Hsat .
sep lift 12%nat in Hsat. 
sep_get_rv_array_struct_conf1.
rewrite leb_bytemax_true_intro;eauto.
simpl;splits;eauto.
}
eapply eq_int; eauto.
split;eauto.
introv Hsat; eexists; sep cancel p_local; simpl; auto.
(* Port_num_cur ′ =ₑ ′ 0;ₛ *)
unfold APortnumcur.
hoare forward.
unfold AAllArea.
hoare unfold.
unfold node_offt.
hoare unfold.
(* tox1 ′ =ₑ (uconf ′ → allArea) .. pAddress;ₛ *)
hoare forward.
hoare_lifts_trms_pre ( Aop ).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel (Alvarmapsto tox1); eauto.
sep auto.
introv Hsat .

eapply expr_struct_member_rv' with ( t' := long ) ;eauto.
instantiate (1:= (Vint32 i15)).
simpl;eauto.
3:{
  unfold area_conf_t.
  eauto.
}
go. 
2:{
  instantiate (1:= 0%nat).
  simpl;eauto.
}
2: go.
2: simpl;eauto.
2: {
  eapply eq_int.
  splits ; eauto.
}
simpl in H34.
inverts H34.
sep_lifts_trms_in Hsat (Alvarmapsto uconf).
eapply local_val_struct_member_addr;eauto.
unfolds;eauto.
go. 
go.
introv Hsat; eexists; sep cancel p_local; simpl; auto.
(* tox2 ′ =ₑ (uconf ′ → allArea) .. vAddress;ₛ *)
hoare unfold.
hoare forward.
hoare_lifts_trms_pre ( Aop ).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel (Alvarmapsto tox2); eauto.
sep auto.
  Optimize Proof.
  Optimize Heap.
introv Hsat .
unfold ucos_conf_t at 1 in Hsat.
eapply expr_struct_member_rv' with ( t' := long ).
go. 
go. 
go. 
4:{
  sep cancel 2%nat 1%nat.
  eauto.
}
4: unfolds;eauto.
6:{
  instantiate (2:= 1%nat).
  simpl;eauto.
}
simpl;eauto.
simpl;eauto.
2: simpl;eauto.
2: go. 
2:{
  eapply eq_int.
  splits ; eauto.
}
simpl in H34.
inverts H34.
sep_lifts_trms_in Hsat (Alvarmapsto uconf).
eapply local_val_struct_member_addr;eauto.
unfolds;eauto.
go. 
go.
introv Hsat; eexists; sep cancel p_local; simpl; auto.
(* tox3 ′ =ₑ (uconf ′ → allArea) .. size;ₛ *)
hoare unfold.
hoare forward.
hoare_lifts_trms_pre ( Aop ).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel (Alvarmapsto tox3); eauto.
sep auto.
introv Hsat .
unfold ucos_conf_t at 1 in Hsat.
eapply expr_struct_member_rv' with ( t' := long ).
go. 
go. 
go. 
4:{
  sep cancel 3%nat 1%nat.
  eauto.
}
4: unfolds;eauto.
6:{
  instantiate (2:= 2%nat).
  simpl;eauto.
}
simpl;eauto.
simpl;eauto.
2: simpl;eauto.
2: go. 
2:{
  eapply eq_int.
  splits ; eauto.
}
simpl in H34.
inverts H34.
sep_lifts_trms_in Hsat (Alvarmapsto uconf).
eapply local_val_struct_member_addr;eauto.
unfolds;eauto.
go. 
go.
introv Hsat; eexists; sep cancel p_local; simpl; auto.

(* OSAll_Partition_Area ′ .. areat_pAddress =ₑ tox1 ′;ₛ *)
unfold APartArea' at 2.  
unfold node.
hoare unfold.
hoare forward.
hoare forward.
hoare forward.
hoare forward.
hoare_split_pure_all.
hoare_lifts_trms_pre (Alvarmapsto ios_cap_defs.i,Alvarmapsto j,Alvarmapsto len,AksDomains'
,AksDomSchedule', AKsDomain,APartID2Dom,Alvarmapsto to1,Alvarmapsto to2
,Alvarmapsto to3,Alvarmapsto tox1,Alvarmapsto tox2,Alvarmapsto tox3
,Alvarmapsto tox4 ).
hoare remember (1::2::3::4::5::6::7::8::9::10::11::12::13::14::nil)%nat pre.
assert(0 <= Int.unsigned i9).
eapply Int.unsigned_range_2.
eapply backward_rule1 with ( p :=
(EX i0 j0 vlksd vpid a1 a2 a3 b1 b2 b3 ,
   EX b4 ,
  LV ios_cap_defs.i @ Int32u |-> (Vint32 i0) **
  LV j @ Int32u |-> (Vint32 j0) **
 
 [|(Int.unsigned i0) < (Int.unsigned i9)|] ** 
 [| Domainslen_P (Int.unsigned i0) v'41 vlksd v'40 vpid |] **

 AksDomains' (Vptr v'46) v'41 **
 AksDomSchedule' (Vptr v'45) v'40 **
 AKsDomain vlksd **
 APartID2Dom vpid **
 LV len @ long |-> Vint32 i9 **
 LV to1 @ char_t |-> a1 **
 LV to2 @ char_t |-> a2 **
 LV to3 @ char_t |-> a3 **
 LV tox1 @ long |-> b1 **
 LV tox2 @ long |-> b2 **
 LV tox3 @ long |-> b3 ** 
 LV tox4 @ long |-> b4 ** H37) 
 \\//
( EX j0 vlksd vpid a1 a2 a3 b1 b2 b3 b4,
LV ios_cap_defs.i @ Int32u |-> (Vint32 i9) **
LV j @ Int32u |-> (Vint32 j0) **

[| Domainslen_P (Int.unsigned i9) v'41 vlksd v'40 vpid |] **
AksDomains' (Vptr v'46) v'41 **
AksDomSchedule' (Vptr v'45) v'40 **
AKsDomain vlksd **
APartID2Dom vpid **
LV len @ long |-> Vint32 i9 **
LV to1 @ char_t |-> a1 **
LV to2 @ char_t |-> a2 **
LV to3 @ char_t |-> a3 **
LV tox1 @ long |-> b1 **
LV tox2 @ long |-> b2 **
LV tox3 @ long |-> b3 ** 
LV tox4 @ long |-> b4 ** H37)
).
assert(0 < Int.unsigned i9 \/ 0 = Int.unsigned i9).
clear -H38.
int_auto.
destruct H39.
intros.
left.
2:{
  right.
  sep pauto.
  rewrite H39.
  rewrite Int.repr_unsigned.
  eauto.
  unfold Domainslen_P.
  intros.
  rewrite <-H39 in H37.
  lia.
}
eexists (Int.repr 0),v'21 ,v'25.
do 8 eexists.
sep pauto.
unfold Domainslen_P.
intros.
change ($ 0) with Int.zero in H37. 
rewrite unsigned_zero in H37. 
lia.

eapply seq_rule.
eapply while_rule with (tp := Int32u).
intros.
destruct H39.
symbolic_execution.
pure_auto.
symbolic_execution.
pure_auto.
eapply backward_rule1 with ( p :=
(EX i0 j0 vlksd vpid a1 a2 a3 b1 b2 b3 ,
   EX b4 ,
  LV ios_cap_defs.i @ Int32u |-> (Vint32 i0) **
  LV j @ Int32u |-> (Vint32 j0) **
 
 [|(Int.unsigned i0) < (Int.unsigned i9)|] ** 
 [| Domainslen_P (Int.unsigned i0) v'41 vlksd v'40 vpid |] **

 AksDomains' (Vptr v'46) v'41 **
 AksDomSchedule' (Vptr v'45) v'40 **
 AKsDomain vlksd **
 APartID2Dom vpid **
 LV len @ long |-> Vint32 i9 **
 LV to1 @ char_t |-> a1 **
 LV to2 @ char_t |-> a2 **
 LV to3 @ char_t |-> a3 **
 LV tox1 @ long |-> b1 **
 LV tox2 @ long |-> b2 **
 LV tox3 @ long |-> b3 ** 
 LV tox4 @ long |-> b4 ** H37) 
).
intros.
destruct H39. 
destruct H39.
sep destruct H39.
sep eexists.
sep cancel 1%nat 1%nat.

sep destruct H39.
lets Halen: H38.
sep split in H39.
sep remember (1::7::nil)%nat in H39.
false. 
destruct_s s.
simpl in H39; simpljoin1.
simpl in H40.

rewrite H65 in H40.
rewrite H56 in H40.
unfold cmp_int_type in H40.
unfold cmp_val in H40.
unfold cmpu in H40.
apply mapstoval_load in H57; auto.
apply mapstoval_load in H66; auto.
destruct (load Int32u m4 (x45, 0)) eqn : eq1.
pose proof (load_mono Int32u (x45, Int.unsigned Int.zero) H43 H66).
rewrite H66 in H37.
change (Int.unsigned Int.zero) with 0 in H37.
rewrite H37 in eq1.
inverts eq1.
2:{
  destruct H40.
  destruct H37.
  tryfalse.
}
eapply join_comm in H43.
lets Hx2:load_local H48 H57.
lets Hm:load_local H43 Hx2. 
change (Int.unsigned Int.zero) with 0 in Hm.
rewrite Hm in H40. 
rewrite sem_common.sempend_ltu_ass1 in H40. 
destruct H40.
destruct H39. 
inverts H39. 
simpl in H40.
change (Int.eq Int.zero Int.zero) with true in H40. 
simpl in H40. 
tryfalse.

hoare unfold.
simpl in H22.
inverts H22.
assert (Hlen: Int.unsigned i9 < DSCHEDULE_SIZE).
{
  clear -H27.
  unfolds in H27.
  simpljoin.
  unfolds in H.
  simpl in H.
  inverts H.
  eauto.
}
eapply backward_rule1.
introv Hsat.
sep_lifts_trms_in Hsat AksDomSchedule'.
eapply AksDomSchedule'_unfold_any_idx_frm with (idx:= Z.to_nat (Int.unsigned v'27)); eauto.
rewrite H14.
unfold DSCHEDULE_SIZE in *.
unfold nat_of_Z in *.
auto with zarith.
unfold node_offt.
hoare unfold.
hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel j; eauto.
sep auto.
  Optimize Proof.
  Optimize Heap.
{
  introv Hsat .
  sep lift 30%nat in Hsat. 
  sep_get_rv_array_struct_conf''.
  rewrite leb_bytemax_true_intro;eauto.
  simpl;splits;eauto.
 }
 eapply eq_int; eauto.
 split;eauto.
 introv Hsat; eexists; sep cancel p_local; simpl; auto.
change (LV j @ long |-> nth_val' 0 (Vint32 i20 :: Vint32 i19 :: nil) )
with (LV j @ long |-> Vint32 i20).
assert(Hj : Int.unsigned i20 < 8).
{
  clear - H28 H41 H39 Hlen.
  destruct H28 as (H28 & _).
  unfolds in H28.
  specialize (H28 (Int.unsigned v'27)).
  destruct H28.
  change DSCHEDULE_SIZE with 10 in *.
  split.
  int_auto.
  auto with zarith.
  simpljoin.
  change DOMAIN_SIZE with 8 in *.
  unfold nat_of_Z in *.
  rewrite <-H41 in H.
  rewrite nth_error_middle in H.
  inverts H.
  unfolds in H0.
  simpl in H0.
  inverts H0.
  eauto.
}
simpl in H9.
inverts H9.
hoare_lifts_trms_pre AksDomains'.
eapply backward_rule1.
introv Hsat.
sep_lifts_trms_in Hsat AksDomains'.
eapply AksDomains'_unfold_any_idx_frm with (idx:= Z.to_nat (Int.unsigned i20)); eauto.
rewrite H0.
unfold nat_of_Z in *.
change CORENUM with 8 in *.
auto with zarith.
unfold node_offt at 1.
hoare unfold.
eapply leb_bytemax_true_intro in H48,H53,H54,H56,H61,H63,H64.

hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel to1; eauto.
sep auto.
{
  introv Hsat .
  sep lift 35%nat in Hsat.
  sep_get_rv_array_struct_conf''.
  rewrite leb_bytemax_true_intro;eauto.
  simpl.
  rewrite H48,H53,H54,H56,H61,H63,H64.
  splits;eauto.
  splits;eauto.
 }
 eapply eq_int; eauto.
 introv Hsat; eexists; sep cancel p_local; simpl; auto.
change (LV to1 @ char_t
|-> nth_val' 2
      (Vint32 i27
      :: Vint32 i26
         :: Vint32 i25
            :: Vint32 i33
               :: Vint32 i24
                  :: Vint32 i32
                     :: Vint32 i31
                        :: Vint32 i30
                           :: Vint32 i29
                              :: Vint32 i23
                                 :: Vint32 i28
                                    :: Vint32 i22
                                       :: x8
                                          :: Vint32 i21
                                             :: 
                                             x12 :: x13 :: nil) )
with (LV to1 @ char_t |-> Vint32 i25).
hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel to2; eauto.
sep auto.
{
  introv Hsat .
  sep lift 35%nat in Hsat. 
  sep_get_rv_array_struct_conf''.
  rewrite leb_bytemax_true_intro;eauto.
  simpl.
  rewrite H48,H53,H54,H56,H61,H63,H64.
  splits;eauto.
  splits;eauto.
 }
 eapply eq_int; eauto.
 introv Hsat; eexists; sep cancel p_local; simpl; auto.
change (LV to2 @ char_t
|-> nth_val' 0
      (Vint32 i27
      :: Vint32 i26
         :: Vint32 i25
            :: Vint32 i33
               :: Vint32 i24
                  :: Vint32 i32
                     :: Vint32 i31
                        :: Vint32 i30
                           :: Vint32 i29
                              :: Vint32 i23
                                 :: Vint32 i28
                                    :: Vint32 i22
                                       :: x8
                                          :: Vint32 i21
                                             :: 
                                             x12 :: x13 :: nil) )
with (LV to2 @ char_t |-> Vint32 i27).
hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel tox1; eauto.
sep auto.
{
  introv Hsat .
  sep lift 35%nat in Hsat. 
  sep_get_rv_array_struct_conf''.
  rewrite leb_bytemax_true_intro;eauto.  
  simpl.
  rewrite H48,H53,H54,H56,H61,H63,H64.
  splits;eauto.
  splits;eauto.
 }
 eapply eq_int;splits; eauto.
 introv Hsat; eexists; sep cancel p_local; simpl; auto.
change (LV tox1 @ long
|-> nth_val' 5
      (Vint32 i27
      :: Vint32 i26
         :: Vint32 i25
            :: Vint32 i33
               :: Vint32 i24
                  :: Vint32 i32
                     :: Vint32 i31
                        :: Vint32 i30
                           :: Vint32 i29
                              :: Vint32 i23
                                 :: Vint32 i28
                                    :: Vint32 i22
                                       :: x8
                                          :: Vint32 i21
                                             :: 
                                             x12 :: x13 :: nil) )
with (LV tox1 @ long |-> Vint32 i32).
hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel tox2; eauto.
sep auto.
{
  introv Hsat .
  sep lift 35%nat in Hsat. 
  sep_get_rv_array_struct_conf''.
  rewrite leb_bytemax_true_intro;eauto.
  simpl.
  rewrite H48,H53,H54,H56,H61,H63,H64.
  splits;eauto.
  splits;eauto.
 }
 eapply eq_int;splits; eauto.
 introv Hsat; eexists; sep cancel p_local; simpl; auto.
change (LV tox2 @ long
|-> nth_val' 6
      (Vint32 i27
      :: Vint32 i26
         :: Vint32 i25
            :: Vint32 i33
               :: Vint32 i24
                  :: Vint32 i32
                     :: Vint32 i31
                        :: Vint32 i30
                           :: Vint32 i29
                              :: Vint32 i23
                                 :: Vint32 i28
                                    :: Vint32 i22
                                       :: x8
                                          :: Vint32 i21
                                             :: 
                                             x12 :: x13 :: nil) )
with (LV tox2 @ long |-> Vint32 i31).
hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel tox3; eauto.
sep auto.
  Optimize Proof.
  Optimize Heap.
{
  introv Hsat .
  sep lift 35%nat in Hsat. 
  sep_get_rv_array_struct_conf''.
  rewrite leb_bytemax_true_intro;eauto.
  simpl.
  rewrite H48,H53,H54,H56,H61,H63,H64.
  splits;eauto.
  splits;eauto.
 }
 eapply eq_int;splits; eauto.
 introv Hsat; eexists; sep cancel p_local; simpl; auto.
change (LV tox3 @ long
|-> nth_val' 7
      (Vint32 i27
      :: Vint32 i26
         :: Vint32 i25
            :: Vint32 i33
               :: Vint32 i24
                  :: Vint32 i32
                     :: Vint32 i31
                        :: Vint32 i30
                           :: Vint32 i29
                              :: Vint32 i23
                                 :: Vint32 i28
                                    :: Vint32 i22
                                       :: x8
                                          :: Vint32 i21
                                             :: 
                                             x12 :: x13 :: nil) )
with (LV tox3 @ long |-> Vint32 i30).
hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel tox4; eauto.
sep auto.
{
  introv Hsat .
  sep lift 35%nat in Hsat. 
  sep_get_rv_array_struct_conf''.
  rewrite leb_bytemax_true_intro;eauto.
  simpl.
  rewrite H48,H53,H54,H56,H61,H63,H64.
  splits;eauto.
  splits;eauto.
 }
 eapply eq_int;splits; eauto.
 introv Hsat; eexists; sep cancel p_local; simpl; auto.
change (LV tox4 @ long
|-> nth_val' 8
      (Vint32 i27
      :: Vint32 i26
         :: Vint32 i25
            :: Vint32 i33
               :: Vint32 i24
                  :: Vint32 i32
                     :: Vint32 i31
                        :: Vint32 i30
                           :: Vint32 i29
                              :: Vint32 i23
                                 :: Vint32 i28
                                    :: Vint32 i22
                                       :: x8
                                          :: Vint32 i21
                                             :: 
                                             x12 :: x13 :: nil) )
with (LV tox4 @ long |-> Vint32 i29).
hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel to3; eauto.
sep auto.
{
  introv Hsat .
  sep lift 35%nat in Hsat. 
  sep_get_rv_array_struct_conf''.
  rewrite leb_bytemax_true_intro;eauto.
  simpl.
  rewrite H48,H53,H54,H56,H61,H63,H64.
  splits;eauto.
  splits;eauto.
 }
 eapply eq_int; eauto.
 introv Hsat; eexists; sep cancel p_local; simpl; auto.
change (LV to3 @ char_t
|-> nth_val' 9
      (Vint32 i27
      :: Vint32 i26
         :: Vint32 i25
            :: Vint32 i33
               :: Vint32 i24
                  :: Vint32 i32
                     :: Vint32 i31
                        :: Vint32 i30
                           :: Vint32 i29
                              :: Vint32 i23
                                 :: Vint32 i28
                                    :: Vint32 i22
                                       :: x8
                                          :: Vint32 i21
                                             :: 
                                             x12 :: x13 :: nil) )
with (LV to3 @ char_t |-> Vint32 i23).

(* (ksDomains ′ [j ′]) .. dom_t_ID =ₑ to1 ′;ₛ *)
unfold AKsDomain at 2.
hoare_split_pure_all.
inverts H55.
eapply backward_rule1.
introv Hsat.
sep_lifts_trms_in Hsat AKsDomains'.
eapply AKsDomains'_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned i20)).
sep cancel AKsDomains';eauto.
eauto.
rewrite H46.
unfold nat_of_Z.
change DOMAIN_SIZE with 8 in *.
auto with zarith.
unfold node_offt at 1.
hoare unfold.
assert(Hij: Vint32 i20 = V$ (Int.unsigned i20)).
{
  rewrite Int.repr_unsigned.
  eauto.
}
(* (ksDomains ′ [j ′]) .. dom_t_ID =ₑ to1 ′;ₛ *)
hoare forward.
hoare_lifts_trms_pre Aop.
eapply assign_rule_array_struct_aop_general.
split; intros.
sep cancel 5%nat 1%nat.
rewrite Hij in H57 at 1.
sep cancel (Alvarmapsto j).
sep cancel A_dom_lenv.
simpl (typelen domain_t).
sep pauto.
sep pauto.
simpl (typelen domain_t) in H57.
sep cancel Astruct.
sep cancel A_dom_lenv.
eauto.
unfolds;eauto.
go. 
go. 
go.
go. 
go.
go. 
go.  
simpl;auto with zarith.
simpl ;eauto.
simpl ;eauto.
2:{
  intros. 
  get_hsat Hsat.  
  sep_lifts_trms_in Hsat (Agvarmapsto ksDomains, Alvarmapsto j, A_dom_lenv).
  rewrite Hij in Hsat at 1.
  eapply Info_get_lv_general in Hsat; eauto. 
  unfold domain_t ; eauto.
  simpl; eauto.
  unfold field_offset.
  unfold field_offsetfld.
  simpl; eauto.
  clear. int_auto.
  clear -Hj.
  int_auto.
  simpl (typelen domain_t).
  clear;int_auto.
  simpl (typelen domain_t).
  clear;int_auto.
}
2: {
  intros.
  symbolic_execution.
  rewrite H54;eauto.
}
eapply eq_int;eauto.
intros.
sep pauto. 
sep cancel p_local. 
sep pauto.
(* (ksDomains ′ [j ′]) .. DTdomain =ₑ to2 ′;ₛ *)
hoare forward.
hoare_lifts_trms_pre Aop.
eapply assign_rule_array_struct_aop_general.
split; intros.
rewrite Hij in H57 at 1.
sep pauto.
sep pauto.
rewrite Hij ;eauto.
unfolds;eauto.
go. 
go. 
go.
go. 
go.
go. 
go.  
simpl;auto with zarith.
simpl ;eauto.
simpl ;eauto.
2:{
  intros. 
  get_hsat Hsat.  
  sep_lifts_trms_in Hsat (Agvarmapsto ksDomains, Alvarmapsto j, A_dom_lenv).
  rewrite Hij in Hsat at 1.
  eapply Info_get_lv_general in Hsat; eauto. 
  unfold domain_t ; eauto.
  simpl; eauto.
  unfold field_offset.
  unfold field_offsetfld.
  simpl; eauto.
  clear. int_auto.
  clear -Hj.
  int_auto.
  simpl (typelen domain_t).
  clear;int_auto.
  simpl (typelen domain_t).
  clear;int_auto.
}
2: {
  intros.
  symbolic_execution.
  rewrite H48;eauto.
}
eapply eq_int;eauto.
intros.
sep pauto. 
sep cancel p_local. 
sep pauto.
(* (ksDomains ′ [j ′]) .. dom_t_OSPartitionPeriod =ₑ tox1 ′;ₛ *)
hoare forward.
hoare_lifts_trms_pre Aop.
eapply assign_rule_array_struct_aop_general.
split; intros.
sep pauto.
sep pauto.
unfolds;eauto.
go. 
go. 
go.
go. 
go.
go. 
go.  
simpl;auto with zarith.
simpl ;eauto.
simpl ;eauto.
2:{
  intros. 
  get_hsat Hsat.  
  sep_lifts_trms_in Hsat (Agvarmapsto ksDomains, Alvarmapsto j, A_dom_lenv).
  eapply Info_get_lv_general in Hsat; eauto. 
  unfold domain_t ; eauto.
  simpl; eauto.
  go. 
  clear;int_auto.
  clear -Hj.
  int_auto.
  simpl (typelen domain_t).
  clear;int_auto.
  simpl (typelen domain_t).
  clear;int_auto.
}
2: {
  intros.
  symbolic_execution.  
}
eapply eq_int;splits; eauto.
intros.
sep pauto. 
sep cancel p_local. 
sep pauto.
hoare forward.
hoare_lifts_trms_pre Aop.
eapply assign_rule_array_struct_aop_general.
split; intros.
sep pauto.
sep pauto.
unfolds;eauto.
go. 
go. 
go.
go. 
go.
go. 
go.  
simpl;auto with zarith.
simpl ;eauto.
simpl ;eauto.
2:{
  intros. 
  get_hsat Hsat.  
  sep_lifts_trms_in Hsat (Agvarmapsto ksDomains, Alvarmapsto j, A_dom_lenv).
  eapply Info_get_lv_general in Hsat; eauto. 
  unfold domain_t ; eauto.
  simpl; eauto.
  go. 
  clear;int_auto.
  clear -Hj.
  int_auto.
  simpl (typelen domain_t).
  clear;int_auto.
  simpl (typelen domain_t).
  clear;int_auto.
}
2: {
  intros.
  symbolic_execution.
}
eapply eq_int;splits; eauto.
intros.
sep pauto. 
sep cancel p_local. 
sep pauto.
hoare forward.
eapply assign_rule_array_struct_aop_general.
split; intros.
sep pauto.
sep pauto.
unfolds;eauto.
go. 
go. 
go.
go. 
go.
go. 
go.  
simpl;auto with zarith.
simpl ;eauto.
simpl ;eauto.
2:{
  intros. 
  get_hsat Hsat.  
  sep_lifts_trms_in Hsat (Agvarmapsto ksDomains, Alvarmapsto j, A_dom_lenv).
  eapply Info_get_lv_general in Hsat; eauto. 
  unfold domain_t ; eauto.
  simpl; eauto.
  go. 
  clear;int_auto.
  clear -Hj.
  int_auto.
  simpl (typelen domain_t).
  clear;int_auto.
  simpl (typelen domain_t).
  clear;int_auto.
}
2: {
  intros.
  symbolic_execution.
}
eapply eq_int;splits; eauto.
intros.
sep pauto. 
sep cancel p_local. 
sep pauto.
hoare forward.
eapply assign_rule_array_struct_aop_general.
split; intros.
sep pauto.
sep pauto.
unfolds;eauto.
go. 
go. 
go.
go. 
go.
go. 
go.  
simpl;auto with zarith.
simpl ;eauto.
simpl ;eauto.
2:{
  intros. 
  get_hsat Hsat.  
  sep_lifts_trms_in Hsat (Agvarmapsto ksDomains, Alvarmapsto j, A_dom_lenv).
  eapply Info_get_lv_general in Hsat; eauto. 
  unfold domain_t ; eauto.
  simpl; eauto.
  go. 
  clear;int_auto.
  clear -Hj.
  int_auto.
  simpl (typelen domain_t).
  clear;int_auto.
  simpl (typelen domain_t).
  clear;int_auto.
}
2: {
  intros.
  symbolic_execution.
}
eapply eq_int;splits; eauto.
intros.
sep pauto. 
sep cancel p_local. 
sep pauto.
hoare forward.
eapply assign_rule_array_struct_aop_general.
split; intros.
sep pauto.
sep pauto.
unfolds;eauto.
go. 
go. 
go.
go. 
go.
go. 
go.  
simpl;auto with zarith.
simpl ;eauto.
simpl ;eauto.
2:{
  intros. 
  get_hsat Hsat.  
  sep_lifts_trms_in Hsat (Agvarmapsto ksDomains, Alvarmapsto j, A_dom_lenv).
  eapply Info_get_lv_general in Hsat; eauto. 
  unfold domain_t ; eauto.
  simpl; eauto.
  go. 
  clear;int_auto.
  clear -Hj.
  int_auto.
  simpl (typelen domain_t).
  clear;int_auto.
  simpl (typelen domain_t).
  clear;int_auto.
}
2: {
  intros.
  symbolic_execution.
  rewrite H61;eauto.
}
eapply eq_int;splits; eauto.
intros.
sep pauto. 
sep cancel p_local. 
sep pauto.
(* partitionID2Domain ′ [to1 ′] =ₑ to2 ′;ₛ *)
assert(Hpidx: Int.unsigned i25 < 8).
{
  destruct H as (_ & _ & Hid & _).
  unfolds in Hid.
  specialize (Hid (Int.unsigned i20)).
  destruct Hid.
  change CORENUM with 8 in *.
  clear -Hj.
  int_auto.
  simpljoin.
  unfold nat_of_Z in H.
  rewrite <-H49 in H.
  rewrite nth_error_middle in H.
  inverts H.
  unfolds in H57.
  simpl in H57.
  inverts H57.
  change PARTITION_NUM with 8 in *.
  eauto.
}
unfold APartID2Dom.
hoare unfold.
hoare forward.

rewrite H48;eauto.
rewrite H54;eauto.
change PARTITION_NUM with 8 .
auto with zarith.
rewrite H59.
change PARTITION_NUM with 8 .
auto with zarith.

(* ++ ios_cap_defs.i ′ *)
assert(Hcond: ( (Int.unsigned v'27) + 1 = Int.unsigned i9 \/
  (Int.unsigned v'27) + 1 < Int.unsigned i9  ) ).
{
clear -H39.
int auto.
  Optimize Proof.
  Optimize Heap.
}
assert (Hsuc: (v'27 +ᵢ $ 1) = ($ ((Int.unsigned v'27) + 1))).
{
 clear -Hcond.
 int auto.
}
destruct Hcond as [Hc1 | Hc2].
(* case 1 *)
hoare forward.
rewrite Hsuc in H68.
assert(Hv'27: $ (Int.unsigned v'27 + 1) = i9).
{
  clear -Hc1.
  rewrite <-Int.repr_unsigned.
  rewrite Hc1.
  eauto.
}
rewrite <-Hv'27 in H68 at 1.
eapply adisj_intro.
right.
sep auto.
eapply AksDomains'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned i20));eauto.
unfold nat_of_Z.
change CORENUM with 8.
auto with zarith.
unfold node_offt at 1.
sep pauto.
2:{
  split;eauto.
  simpl.
  rewrite H48,H53,H54,H56,H61,H63,H64.
  splits;eauto.
  splits;eauto.
}
2:eauto.
2:eauto.
2:eauto.
rewrite Int.repr_unsigned in H68.
simpl (typelen domain_conf_t).
simpl (typelen domain_conf_t) in H68.
sep pauto.
eapply AksDomSchedule'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned v'27));eauto.
unfold nat_of_Z.
clear -Hlen H39 .
change DSCHEDULE_SIZE with 10 in *.
auto with zarith.
unfold node_offt.
unfold AKsDomain.
sep pauto.
eapply AKsDomains'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned i20));eauto.
unfold nat_of_Z.
change DOMAIN_SIZE with 8.
auto with zarith.
unfold node_offt.
sep pauto.
sep cancel 2%nat 1%nat.
sep cancel 1%nat 1%nat.
sep cancel 1%nat 1%nat.
sep cancel 1%nat 1%nat.
eauto.
split;eauto.
simpl.
rewrite H54,H61.
rewrite leb_bytemax_true_intro;eauto.
splits;eauto.
split;eauto.
eauto.
split;eauto.
simpl;splits;eauto.
rewrite app_length.
simpl.
rewrite app_length in H46.
simpl in H46.
eauto.
split;eauto.
eapply array_type_vallist_match_hold.
eauto.
rewrite H59.
change PARTITION_NUM with 8.
auto with zarith.
simpl; rewrite H48; eauto.
rewrite <-H59.
eapply update_nth_val_len_eq.
(* Domainslen_P *)
unfold Domainslen_P.
intros.
rewrite <-Hc1 in H71.
assert (Hcond: 0 <= i9 < Int.unsigned v'27 \/ i9 = Int.unsigned v'27).
{
   clear -H71.
   int_auto.
}
destruct Hcond as [Hcc1 | Hcc2].
lets Hlt: Hcc1.
assert(Hjlen: Z.to_nat (Int.unsigned j) = length v'41 \/ Z.to_nat (Int.unsigned j) <> length v'41 ) by tauto.
destruct Hjlen.
unfold nat_of_Z in *.
rewrite H95 in *.
rewrite nth_error_middle in H77.
inverts H77.
rewrite <-H62 in H49.
rewrite <-H49 in H78.
rewrite nth_error_middle in H78.
inverts H78.
inverts H77.
simpl in H88,H87,H86,H85,H84,H83,H82,H81,H80,H93,H92,H91,H90,H89.
rewrite <-H88,<-H87,<-H86,<-H85,<-H84,<-H83,<-H82,<-H81,<-H80,<-H93,<-H92,<-H91,<-H90,<-H89.
splits;eauto.
eapply TmrMod.option2val in H88.
inverts H88.
eapply nth_upd_eq in H94.
rewrite H94;eauto.
(* 2 *)
eapply H40 in Hcc1.
rewrite Int.repr_unsigned in H75.
eapply Hcc1;eauto.
unfold nat_of_Z in *.
eapply nth_error_neq;eauto.
unfold nat_of_Z in H94.
eapply nth_upd_neq in H94. eauto.

(* 0<=j<8 *)
lets Hcpudomseg: H28.
destruct H28 as (Hdomg & Hnopg).
unfold CPU_ksDomSchdule_dom_Good in Hdomg.
lets j_i10: Hdomg i9.
destruct j_i10.
rewrite <-Hc1 in Hlen.
clear -Hlen H71.
auto with zarith.
do 2 destruct H28.
destruct H96.
unfold nat_of_Z in *.
rewrite H75 in H28.
inverts H28.
unfolds in H96.
rewrite H76 in H96.
inverts H96.

destruct H as (_ & _ & _ & Hnop).
unfolds in Hnop.
lets Hnewnop: Hnop (Int.unsigned x1) (Z.of_nat (length v'40)).
specializes Hnewnop.
unfold_part_defs.
auto with zarith.
rewrite H49.
unfold_part_defs.
auto with zarith.
rewrite H49.
rewrite <-H62.
intro.
rewrite H in H95.
rewrite nat_of_Z_of_nat in H95.
tryfalse.
unfold nat_of_Z in *.
eauto.
assert(Heqlen: length v'41 = length v'40).
rewrite H62.
rewrite H49;eauto.
rewrite Heqlen in H95.
rewrite H79 in H78.
eapply nth_error_neq;eauto.
rewrite nat_of_Z_of_nat .
eapply nth_error_middle.
unfolds;eauto.
unfolds;simpl;eauto.
intro.
eapply inline_bittblfunctions.z2n_int_eq in H.
rewrite H in Hnewnop;tryfalse.
inverts Hcc2.
unfold nat_of_Z in H75.
rewrite <-H41 in H75.
rewrite nth_error_middle in H75.
inverts H75.
simpl in H76.
rewrite Int.repr_unsigned in H76.
inverts H76.
unfold nat_of_Z in H77.
rewrite <-H62 in H77.
rewrite nth_error_middle in H77.
inverts H77.
simpl in H80,H81,H86,H85,H84,H83,H82.
unfold nat_of_Z in H78.
rewrite <-H49 in H78.
rewrite nth_error_middle in H78.
rewrite H79 in H78.
inverts H78.
simpl in H88,H87,H93,H92,H91,H90,H89.
rewrite H86 in H93.
rewrite H85 in H92.
rewrite H84 in H91.
rewrite H83 in H90.
rewrite H82 in H89.
rewrite H81 in H88.
rewrite H80 in H87.
splits;eauto.
rewrite H88 in H81.
inverts H81.
unfold nat_of_Z in H94.
eapply nth_upd_eq in H94.
rewrite H94 in H80.
apply H80.
(* case 2  *)
hoare forward.
rewrite Hsuc in H68.
eapply adisj_intro.
left.
sep auto.
  Optimize Proof.
  Optimize Heap.
eapply AksDomains'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned i20));eauto.
unfold nat_of_Z.
change CORENUM with 8.
auto with zarith.
unfold node_offt at 1.
sep pauto.
2:{
  split;eauto.
  simpl.
  rewrite H48,H53,H54,H56,H61,H63,H64.
  splits;eauto.
  splits;eauto.
}
2:eauto.
2:eauto.
2:eauto.
rewrite Int.repr_unsigned in H68.
simpl (typelen domain_conf_t).
simpl (typelen domain_conf_t) in H68.
sep pauto.
eapply AksDomSchedule'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned v'27));eauto.
unfold nat_of_Z.
clear -Hlen H39 .
change DSCHEDULE_SIZE with 10 in *.
auto with zarith.
unfold node_offt.
unfold AKsDomain.
sep pauto.
eapply AKsDomains'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned i20));eauto.
unfold nat_of_Z.
change DOMAIN_SIZE with 8.
auto with zarith.
unfold node_offt.
sep pauto.
sep cancel 2%nat 1%nat.
sep cancel 1%nat 1%nat.
sep cancel 1%nat 1%nat.
sep cancel 1%nat 1%nat.
eauto.
split;eauto.
simpl; rewrite H54, H61;splits;eauto.
rewrite leb_bytemax_true_intro;eauto.
split;eauto.
eauto.
split;eauto.
simpl;splits;eauto.
rewrite app_length.
simpl.
rewrite app_length in H46.
simpl in H46.
eauto.
split;eauto.
eapply array_type_vallist_match_hold.
eauto.
rewrite H59.
change PARTITION_NUM with 8.
auto with zarith.
simpl;rewrite H48; eauto.
rewrite <-H59.
eapply update_nth_val_len_eq.
2:{
  rewrite int_usign_eq;eauto.
  clear;int_auto.
  clear -Hlen Hc2.
  unfold_part_defs.
  int_auto.
}
(* Domainslen_P *)
assert(Hv'27 : Int.unsigned v'27 + 1 < 10).
{
  clear -Hlen Hc2.
  unfold_part_defs.
  int_auto.
}
unfold Domainslen_P.
intros.
unfold nat_of_Z in *.
assert (Hcond: 0 <= i42 < Int.unsigned v'27 \/ i42 = Int.unsigned v'27).
{
   clear -H71 Hv'27.
   int_auto.
   clear H0.
   int_auto.
}
destruct Hcond as [Hcc1 | Hcc2].
lets Hlt: Hcc1.
assert(Hjlen: Z.to_nat (Int.unsigned j) = length v'41 \/ Z.to_nat (Int.unsigned j) <> length v'41 ) by tauto.
destruct Hjlen.
rewrite H95 in *.
rewrite nth_error_middle in H77.
inverts H77.
rewrite <-H62 in H49.
rewrite <-H49 in H78.
rewrite nth_error_middle in H78.
inverts H78.
inverts H77.
simpl in H88,H87,H86,H85,H84,H83,H82,H81,H80,H93,H92,H91,H90,H89.
rewrite <-H88,<-H87,<-H86,<-H85,<-H84,<-H83,<-H82,<-H80,<-H81,<-H93,<-H92,<-H91,<-H90,<-H89.
splits;eauto.
eapply TmrMod.option2val in H88.
inverts H88.
eapply nth_upd_eq in H94.
rewrite H94;eauto.
(* 2 *)
eapply H40 in Hcc1.
rewrite Int.repr_unsigned in H75.
eapply Hcc1;eauto.
unfold nat_of_Z in *.
eapply nth_error_neq;eauto.
unfold nat_of_Z in H94.
eapply nth_upd_neq in H94. eauto.
(* 0<=j<8 *)
lets Hcpudomseg: H28.
destruct H28 as (Hdomg & Hnopg).
unfold CPU_ksDomSchdule_dom_Good in Hdomg.
lets j_i10: Hdomg i42.
destruct j_i10.
clear -Hv'27 Hlt.
change DSCHEDULE_SIZE with 10 in *.
int_auto.
do 2 destruct H28.
destruct H96.
unfold nat_of_Z in *.
rewrite H75 in H28.
inverts H28.
unfolds in H96.
rewrite H76 in H96.
inverts H96.
destruct H as (_ & _ & _ & Hnop).
unfolds in Hnop.
lets Hnewnop: Hnop (Int.unsigned x1) (Z.of_nat (length v'40)).
specializes Hnewnop.
unfold_part_defs.
auto with zarith.
rewrite H49.
unfold_part_defs.
auto with zarith.
rewrite H49.
rewrite <-H62.
intro.
rewrite H in H95.
rewrite nat_of_Z_of_nat in H95.
tryfalse.
unfold nat_of_Z in *.
eauto.
assert(Heqlen: length v'41 = length v'40).
rewrite H62.
rewrite H49;eauto.
rewrite Heqlen in H95.
rewrite H79 in H78.
eapply nth_error_neq;eauto.
rewrite nat_of_Z_of_nat .
eapply nth_error_middle.
unfolds;eauto.
unfolds;simpl;eauto.
intro.
eapply inline_bittblfunctions.z2n_int_eq in H.
rewrite H in Hnewnop;tryfalse.
inverts Hcc2.
unfold nat_of_Z in H75.
rewrite <-H41 in H75.
rewrite nth_error_middle in H75.
inverts H75.
simpl in H76.
rewrite Int.repr_unsigned in H76.
inverts H76.
unfold nat_of_Z in H77.
rewrite <-H62 in H77.
rewrite nth_error_middle in H77.
inverts H77.
simpl in H80,H81,H86,H85,H84,H83,H82.
unfold nat_of_Z in H78.
rewrite <-H49 in H78.
rewrite nth_error_middle in H78.
rewrite H79 in H78.
inverts H78.
simpl in H88,H87,H93,H92,H91,H90,H89.
rewrite H86 in H93.
rewrite H85 in H92.
rewrite H84 in H91.
rewrite H83 in H90.
rewrite H82 in H89.
rewrite H81 in H88.
rewrite H80 in H87.
splits;eauto.
rewrite H88 in H81.
inverts H81.
unfold nat_of_Z in H94.
eapply nth_upd_eq in H94.
rewrite H94 in H80.
apply H80.

(* Afalse *)
eapply backward_rule1 with ( p :=(
(EX j0 vlksd vpid a1 a2 a3 b1 b2 b3 b4,
LV ios_cap_defs.i @ Int32u |-> (Vint32 i9) **
LV j @ Int32u |-> (Vint32 j0) **

[| Domainslen_P (Int.unsigned i9) v'41 vlksd v'40 vpid |] **
AksDomains' (Vptr v'46) v'41 **
AksDomSchedule' (Vptr v'45) v'40 **
AKsDomain vlksd **
APartID2Dom vpid **
LV len @ long |-> Vint32 i9 **
LV to1 @ char_t |-> a1 **
LV to2 @ char_t |-> a2 **
LV to3 @ char_t |-> a3 **
LV tox1 @ long |-> b1 **
LV tox2 @ long |-> b2 **
LV tox3 @ long |-> b3 ** 
LV tox4 @ long |-> b4 ** H37) 
     **  [| Vint32 Int.zero = Vint32 Int.zero \/ Vint32 Int.zero = Vnull |]
)).
intros.
destruct H39.
destruct H39.
lets Hnew: aconj_intro H39 H40.
clear H39 H40.
eapply sep_aconj_r_aisfalse_to_astar in Hnew.
2 : {
intros.
sep destruct H39.
sep get rv. 
sep split in H39.
assert (Int.ltu x1 i9 = true).
{
clear -H40.
int auto.
  Optimize Proof.
  Optimize Heap.
}
rewrite H42.
eauto.
eauto.
}
sep normal in Hnew.
destruct Hnew. 
sep destruct H39.
sep split in H39.
destruct H42; tryfalse.
lets Hnew: aconj_intro H39 H40.
clear H39 H40.
eapply sep_aconj_r_aisfalse_to_astar in Hnew.
2 : {
intros.
sep destruct H39.
sep get rv.
pure_auto.
}
assert (Int.ltu i9 i9 = false).
clear .
int auto.
rewrite H39 in Hnew.
sep split in Hnew.
simpl in H40.
sep pauto.
(* end while *)
hoare unfold.
(* len ′ =ₑ ((uconf ′ → cpus) [coreNum ′]) .. cpu_ksDomScheduleLength;ₛ *)
hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel len; eauto.
sep auto.
{
introv Hsat .
sep lift 28%nat in Hsat.
sep_get_rv_array_struct_conf1.
rewrite leb_bytemax_true_intro;eauto.
simpl;splits;eauto.
}
eapply eq_int; eauto.
split;eauto.
introv Hsat; eexists; sep cancel p_local; simpl; auto.
change (LV len @ long |-> nth_val' 2 (Vint32 i10 :: x4 :: Vint32 i9 :: Vint32 i8 :: x9 :: x10 :: nil))
with (LV len @ long |-> Vint32 i9).
(* ksDomScheduleLength′=ₑ 〈Int8u〉len′;ₛ *)
hoare_lifts_trms_pre AKsDSchdlen. 
unfold AKsDSchdlen at 2.
hoare unfold.
hoare forward.
(* ios_cap_defs.i ′ =ₑ ′ 0;ₛ*)
hoare forward.
(* while *)
hoare_split_pure_all. 
hoare_lifts_trms_pre (Alvarmapsto ios_cap_defs.i,AksDomSchedule', AKsDomSchedule',
Alvarmapsto tox1,Alvarmapsto tox2,Alvarmapsto len).
hoare remember (1::2::3::4::5::6::nil)%nat pre.
eapply backward_rule1 with ( p :=
(EX i0 a1 a2 vldomsch,
 LV ios_cap_defs.i @ Int32u |-> (Vint32 i0) **
 [|(Int.unsigned i0) < (Int.unsigned i9)|] ** 
 [| ksDomSchedule_P (Int.unsigned i0) vldomsch v'40 |] **
 AksDomSchedule' (Vptr v'45) v'40 **
 AKsDomSchedule' vldomsch **
 LV tox1 @ long |-> a1 **
 LV tox2 @ long |-> a2 **
 LV len @ long |-> Vint32 i9 ** H41 ) 
 \\//
( EX a1 a2 vldomsch,
LV ios_cap_defs.i @ Int32u |-> (Vint32 i9) **
[| ksDomSchedule_P (Int.unsigned i9) vldomsch v'40 |] **
AksDomSchedule' (Vptr v'45) v'40 **
AKsDomSchedule' vldomsch **
LV tox1 @ long |-> a1 **
LV tox2 @ long |-> a2 **
LV len @ long |-> Vint32 i9 ** H41)
).
assert(Hlen: 0 < Int.unsigned i9 \/ 0 = Int.unsigned i9).
clear -H38.
int_auto.
destruct Hlen.
intros.
left.
2:{
  right.
  sep pauto.
  rewrite H42.
  rewrite Int.repr_unsigned.
  eauto.
  unfold ksDomSchedule_P.
  intros.
  rewrite <-H42 in H41.
  lia.
}
eexists (Int.repr 0).
sep pauto.
unfold ksDomSchedule_P.
intros.
change ($ 0) with Int.zero in H41. 
rewrite unsigned_zero in H41. 
lia.
eapply seq_rule.
eapply while_rule with (tp := Int32u).
intros.
destruct H42.
symbolic_execution.
pure_auto.
symbolic_execution.
pure_auto.
eapply backward_rule1 with ( p :=
(EX i0 a1 a2 vldomsch,
LV ios_cap_defs.i @ Int32u |-> (Vint32 i0) **
[|(Int.unsigned i0) < (Int.unsigned i9)|] ** 
[| ksDomSchedule_P (Int.unsigned i0) vldomsch v'40 |] **
AksDomSchedule' (Vptr v'45) v'40 **
AKsDomSchedule' vldomsch **
LV tox1 @ long |-> a1 **
LV tox2 @ long |-> a2 **
LV len @ long |-> Vint32 i9 ** H41)
).
intros.
destruct H42.
destruct H42.
sep destruct H42.
sep eexists.
sep cancel 1%nat 1%nat.
sep destruct H42.
lets Hnew39: H38.
sep split in H42.
sep remember (1::6::nil)%nat in H42.
false. 
destruct_s s.
simpl in H42; simpljoin1.
simpl in H43.
rewrite H68 in H43.
rewrite H59 in H43.
unfold cmp_int_type in H43.
unfold cmp_val in H43.
unfold cmpu in H43.
apply mapstoval_load in H60; auto.
apply mapstoval_load in H69; auto.
destruct (load Int32u m4 (x38, 0)) eqn : eq1.
pose proof (load_mono Int32u (x38, Int.unsigned Int.zero) H46 H69).
rewrite H69 in H41.
change (Int.unsigned Int.zero) with 0 in H41.
rewrite H41 in eq1.
inverts eq1.
2:{
  destruct H43.
  destruct H41.
  tryfalse.
}
eapply join_comm in H46.
lets Hx2:load_local H51 H60.
lets Hm:load_local H46 Hx2. 
change (Int.unsigned Int.zero) with 0 in Hm.
rewrite Hm in H43. 
rewrite sem_common.sempend_ltu_ass1 in H43. 
destruct H43.
destruct H42. 
inverts H42. 
simpl in H43.
change (Int.eq Int.zero Int.zero) with true in H43. 
simpl in H43. 
tryfalse.

(* tox1′  =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomSchedule)[i′])..ds_domain ;ₛ *)
hoare unfold.
simpl in H22.
inverts H22.
assert (Hlen: Int.unsigned i9 < DSCHEDULE_SIZE).
{
  clear -H27.
  unfolds in H27.
  simpljoin.
  unfolds in H.
  simpl in H.
  inverts H.
  eauto.
}
eapply backward_rule1.
introv Hsat.
sep_lifts_trms_in Hsat AksDomSchedule'.
eapply AksDomSchedule'_unfold_any_idx_frm with (idx:= Z.to_nat (Int.unsigned v'57)); eauto.
rewrite H14.
unfold DSCHEDULE_SIZE in *.
unfold nat_of_Z in *.
auto with zarith.
unfold node_offt.
hoare unfold.
hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel tox1; eauto.
sep auto.
  Optimize Proof.
  Optimize Heap.
{
  introv Hsat .
  sep lift 32%nat in Hsat.
  sep_get_rv_array_struct_conf''.
  rewrite leb_bytemax_true_intro;eauto.
  simpl;splits;eauto.
 }
 eapply eq_int; eauto.
 split;eauto.
 introv Hsat; eexists; sep cancel p_local; simpl; auto.
change (LV  tox1  @ long |-> nth_val' 0 (Vint32 i20 :: Vint32 i19 :: nil) )
with (LV  tox1  @ long |-> Vint32 i20).
hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel tox2; eauto.
sep auto.
{
  introv Hsat .
  sep lift 32%nat in Hsat.
  sep_get_rv_array_struct_conf''.
  rewrite leb_bytemax_true_intro;eauto.
  simpl;splits;eauto.
 }
 eapply eq_int; splits;eauto.
 introv Hsat; eexists; sep cancel p_local; simpl; auto.
change (LV  tox2  @ long |-> nth_val' 1 (Vint32 i20 :: Vint32 i19 :: nil) )
with (LV  tox2  @ long |-> Vint32 i19).
eapply backward_rule1.
introv Hsat.
sep lift 8%nat in Hsat.
eapply AKsDomSchedule'_unfold_any_idx_frm in Hsat.
instantiate (1:=  (Z.to_nat (Int.unsigned v'57))) in Hsat. 
eauto.
unfold AKsDomSchedule' in Hsat.
sep normal in Hsat.
destruct Hsat.
sep split in H22. 
destruct H41.
rewrite H55.
clear -H42 Hlen.
unfold nat_of_Z in *.
unfold_part_defs.
auto with zarith.
hoare unfold.
lets Hsplit : H22.  
eapply new_array_type_vallist_match_split_domsch in Hsplit; eauto.
destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
lets Hvl: struct_type_vallist_match_elim_2 Hsp.
destruct Hvl. 
destruct H47. 
subst v'65. 
(* efield (ksDomSchedule′[i′]) dscd_domain =ₑ tkdsd′ ;ₛ  *)
hoare forward.
hoare_lifts_trms_pre Aop.
eapply assign_rule_array_struct_aop_general.
split; intros.
sep cancel Agvarmapsto ksDomSchedule.
sep_lifts_trms_in H47 (Alvarmapsto ios_cap_defs.i).
instantiate(3:= Int.unsigned v'57).
rewrite Int.repr_unsigned. 
sep cancel (Alvarmapsto ios_cap_defs.i).
sep cancel A_dom_lenv.  
sep cancel Astruct.
eauto.
sep pauto.
rewrite Int.repr_unsigned;eauto. 
unfolds;eauto.
go. 
go. 
go. 
go. 
go. 
go. 
go.
simpl; auto.
simpl; eauto.
simpl; eauto.
2:{
  intros. 
  get_hsat Hsat.  
  sep_lifts_trms_in Hsat (Agvarmapsto ksDomSchedule, Alvarmapsto ios_cap_defs.i, A_dom_lenv).
  assert (Hv13: $ Z.of_nat (Z.to_nat (Int.unsigned v'57)) =  v'57).
  rewrite <-Int.repr_unsigned.
  rewrite Z2Nat.id;eauto. 
  eapply Int.unsigned_range_2.
  rewrite <-Hv13 in Hsat at 1.
  rewrite Z2Nat.id in Hsat;eauto.
  2:{
    clear.
    int_auto.
  }
  eapply Info_get_lv_general in Hsat; eauto. 
  unfolds;eauto.
  simpl;eauto.
  simpl;eauto.
  clear. int_auto.
  clear -H42 Hlen.
  unfold_part_defs.
  int_auto.
  simpl (typelen dschedule_t).
  clear.
  int_auto.
  simpl (typelen dschedule_t).
  clear.
  int_auto.
}
2: {
  intros.
  symbolic_execution.
}
eapply eq_int.
splits;eauto.
intros.
sep pauto. 
sep cancel p_local. 
sep pauto.
hoare forward.
hoare_lifts_trms_pre Aop.
eapply assign_rule_array_struct_aop_general.
split; intros.
sep cancel Agvarmapsto ksDomSchedule.
sep_lifts_trms_in H47 (Alvarmapsto ios_cap_defs.i).
instantiate(3:= Int.unsigned v'57).
sep cancel (Alvarmapsto ios_cap_defs.i).
sep cancel A_dom_lenv.  
sep cancel Astruct.
eauto.
sep pauto.
unfolds;eauto.
go. 
go. 
go. 
go. 
go. 
go. 
go.
simpl; auto.
simpl; eauto.
simpl; eauto.
2:{
  intros. 
  get_hsat Hsat.  
  sep_lifts_trms_in Hsat (Agvarmapsto ksDomSchedule, Alvarmapsto ios_cap_defs.i, A_dom_lenv).
  eapply Info_get_lv_general in Hsat; eauto. 
  unfolds;eauto.
  simpl;eauto.
  simpl;eauto.
  clear. int_auto.
  clear -H42 Hlen.
  unfold_part_defs.
  int_auto.
  simpl (typelen dschedule_t).
  clear.
  int_auto.
  simpl (typelen dschedule_t).
  clear.
  int_auto.
}
2: {
  intros.
  symbolic_execution.
}
eapply eq_int;splits;eauto.
intros.
sep pauto. 
sep cancel p_local. 
sep pauto.
assert (Hv13: V$ Int.unsigned v'57 = Vint32 v'57).
{
  rewrite Int.repr_unsigned.
  eauto.
}
 rewrite Hv13 in *. 
(* ++ ios_cap_defs.i ′ *)
assert(Hcond: ( (Int.unsigned v'57) + 1 = Int.unsigned i9 \/
  (Int.unsigned v'57) + 1 < Int.unsigned i9) ).
{
clear -H42.
int auto.
  Optimize Proof.
  Optimize Heap.
}
assert (Hsuc: (v'57 +ᵢ $ 1) = ($ ((Int.unsigned v'57) + 1))).
{
 clear -Hcond.
 int auto.
}
destruct Hcond as [Hc1 | Hc2].
(* case 1 *)
hoare forward.
rewrite Hsuc in H47.
assert(Hv'65: $ (Int.unsigned v'57 + 1) = i9).
{
  clear -Hc1.
  rewrite <-Int.repr_unsigned.
  rewrite Hc1.
  eauto.
}
rewrite <-Hv'65 in H47 at 1.
eapply adisj_intro.
right.
sep auto.
(* 拆分AksDomSchedule' *)
eapply AksDomSchedule'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned v'57));eauto.
{
  rewrite <-Hc1 in Hlen.
  clear -Hlen.
  unfold_part_defs.
  unfold nat_of_Z.
  int_auto.
}
unfold node_offt at 1.
sep pauto.
sep cancel 5%nat 1%nat.
2:{
  split;eauto.
  simpl.
  splits;eauto.
}
eapply AKsDomSchedule'_select_sn_strong with (n:= Z.to_nat (Int.unsigned v'57)).
eauto.
sep cancel 1%nat 1%nat.
sep pauto.
eapply new_array_type_vallist_match_compose_struct;eauto.
simpl;splits;eauto.
simpl.
rewrite app_length.
simpl.
rewrite app_length in H41.
simpl in H41.
eauto.
{
  assert (Hi12 : 0 <= Int.unsigned i20 < DOMAIN_SIZE).
  destruct H28 as (Hdes & _).
  unfolds in Hdes.
  lets Hauxi: Hdes ( (Int.unsigned v'57)).
  destruct Hauxi.
  clear -H49.
  unfold_part_defs.
  int_auto.
  do 2 destruct H28.
  unfold nat_of_Z in *.
  rewrite <-H44 in H28.
  rewrite nth_error_middle in H28.
  inverts H28.
  destruct H54.
  unfolds in H28.
  simpl in H28.
  inverts H28.
  eauto.

clear -H50 Hi12.
unfold R_KsDomSchedule_P in *.
unfold nat_of_Z in *.
intros.
assert(((Z.to_nat (Int.unsigned td)) = length v'40) \/((Z.to_nat (Int.unsigned td)) <> length v'40) ) by tauto.
destruct H1.
rewrite H1 in *.
rewrite nth_vallist_get_idx in H.
inverts H. 
unfolds in H0.
simpl in H0.
inverts H0.
left.
eauto.
specializes H50.
instantiate (1:= vl).
instantiate (1:= td).
eapply nth_vallist_neq;eauto.
eauto.
eauto.
}
(* ksDomSchedule_P *)
unfold ksDomSchedule_P.
intros.
rewrite <-Hc1 in H52.
assert (Hcond: 0 <= i9 < Int.unsigned v'57 \/ i9 = Int.unsigned v'57).
{
   clear -H52.
   int_auto.
}
destruct Hcond as [Hcc1 | Hcc2].
lets Hcc1': Hcc1.
eapply H43 in Hcc1.
destruct Hcc1;eauto.
eapply nth_vallist_neq;eauto.
rewrite H48.
clear -Hcc1'.
unfold nat_of_Z.
int_auto.
(* 2 *)
inverts Hcc2.
unfold nat_of_Z in *.
rewrite <-H48 in H57.
rewrite <-H44 in H54.
rewrite nth_vallist_get_idx in H57.
rewrite nth_error_middle in H54.
inverts H54.
inverts H57.
rewrite H56 in H59.
rewrite H55 in H58.
inverts H59.
inverts H58.
split;eauto.
(* case 2 *)
hoare forward.
rewrite Hsuc in H47.
eapply adisj_intro.
left.
sep auto.
(* 拆分AksDomSchedule' *)
eapply AksDomSchedule'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned v'57));eauto.
{
  clear -Hlen Hc2.
  unfold_part_defs.
  unfold nat_of_Z.
  int_auto.
}
unfold node_offt at 1.
sep pauto.
sep cancel 5%nat 1%nat.
2:{
  split;eauto.
  simpl.
  splits;eauto.
}
eapply AKsDomSchedule'_select_sn_strong with (n:= Z.to_nat (Int.unsigned v'57)).
eauto.
sep cancel 1%nat 1%nat.
sep pauto.
eapply new_array_type_vallist_match_compose_struct;eauto.
simpl;splits;eauto.
simpl.
rewrite app_length.
simpl.
rewrite app_length in H41.
simpl in H41.
eauto.
{
  assert (Hi12 : 0 <= Int.unsigned i20 < DOMAIN_SIZE).
  destruct H28 as (Hdes & _).
  unfolds in Hdes.
  lets Hauxi: Hdes ( (Int.unsigned v'57)).
  destruct Hauxi.
  clear -H49.
  unfold_part_defs.
  int_auto.
  do 2 destruct H28.
  unfold nat_of_Z in *.
  rewrite <-H44 in H28.
  rewrite nth_error_middle in H28.
  inverts H28.
  destruct H54.
  unfolds in H28.
  simpl in H28.
  inverts H28.
  eauto.

clear -H50 Hi12.
unfold R_KsDomSchedule_P in *.
unfold nat_of_Z in *.
intros.
assert(((Z.to_nat (Int.unsigned td)) = length v'40) \/((Z.to_nat (Int.unsigned td)) <> length v'40) ) by tauto.
destruct H1.
rewrite H1 in *.
rewrite nth_vallist_get_idx in H.
inverts H. 
unfolds in H0.
simpl in H0.
inverts H0.
left.
eauto.
specializes H50.
instantiate (1:= vl).
instantiate (1:= td).
eapply nth_vallist_neq;eauto.
eauto.
eauto.
}
2:{
  clear -Hc2 Hlen.
  rewrite int_usign_eq;eauto.
  clear ;int_auto.
  unfold_part_defs.
  int_auto.
}
(* ksDomSchedule_P *)
unfold ksDomSchedule_P.
intros.
rewrite int_usign_eq in H52.
2: clear;int_auto.
2:{
  clear -Hlen Hc2.
  unfold_part_defs.
  int_auto.
}
assert (Hcond: 0 <= i21 < Int.unsigned v'57 \/ i21 = Int.unsigned v'57).
{
   clear -H52.
   int_auto.
}
destruct Hcond as [Hcc1 | Hcc2].
lets Hcc1': Hcc1.
eapply H43 in Hcc1.
destruct Hcc1;eauto.
eapply nth_vallist_neq;eauto.
rewrite H48.
clear -Hcc1'.
unfold nat_of_Z.
int_auto.
(* 2 *)
inverts Hcc2.
unfold nat_of_Z in *.
rewrite <-H48 in H57.
rewrite <-H44 in H54.
rewrite nth_vallist_get_idx in H57.
rewrite nth_error_middle in H54.
inverts H54.
inverts H57.
rewrite H56 in H59.
rewrite H55 in H58.
inverts H59.
inverts H58.
split;eauto.

(* Adfalse *)
eapply backward_rule1 with ( p :=(
( EX a1 a2 vldomsch,
LV ios_cap_defs.i @ Int32u |-> (Vint32 i9) **
[| ksDomSchedule_P (Int.unsigned i9) vldomsch v'40 |] **
AksDomSchedule' (Vptr v'45) v'40 **
AKsDomSchedule' vldomsch **
LV tox1 @ long |-> a1 **
LV tox2 @ long |-> a2 **
LV len @ long |-> Vint32 i9 ** H41)
** [| Vint32 Int.zero = Vint32 Int.zero \/ Vint32 Int.zero = Vnull |]
)).
intros.
destruct H42.
destruct H42.
lets Hnew: aconj_intro H42 H43.
clear H43 H42.
eapply sep_aconj_r_aisfalse_to_astar in Hnew.
2 : {
intros.
sep destruct H42.
sep get rv.
sep split in H42.
assert (Int.ltu x1 i9 = true).
{
clear -H43.
int auto.
  Optimize Proof.
  Optimize Heap.
}
rewrite H45.
eauto.
eauto.
}
sep normal in Hnew.
destruct Hnew. 
sep destruct H42.
sep split in H42.
destruct H45; tryfalse.
lets Hnew: aconj_intro H42 H43.
clear H43 H42.
eapply sep_aconj_r_aisfalse_to_astar in Hnew.
2 : {
intros.
sep destruct H42.
sep get rv.
pure_auto.
}
assert (Int.ltu i9 i9 = false).
clear .
int auto.
rewrite H42 in Hnew.
sep split in Hnew.
sep pauto.
(* end while *)
hoare unfold.
clear H43.
(* i=0 *)
hoare forward.

hoare forward.
hoare_lifts_trms_pre (Aop ,(Alvarmapsto to1)).
eapply assign_rule_lvar. 
intros; split; intro Hsat.
sep cancel to1; eauto.
sep auto.
intros.
2:{
    instantiate (1:= char_t ).
    eapply eq_int.
    splits;eauto.
  }
eapply struct_member_rv' with (v:=Vint32 i1) ;eauto. 
simpl; rewrite Hgi1 ;eauto.
2:{
  sep pauto.
  sep lift 30%nat in H41. 
  fold ucos_conf_t.
  sep cancel Astruct.
  eauto.
}
simpl;eauto.
2: simpl;eauto.
instantiate(1:= 5%nat).
simpl.
eauto.
eauto.
introv Hsat; eexists; sep cancel p_local; simpl; auto.
(* while  *)
hoare_split_pure_all.
hoare_lifts_trms_pre (Alvarmapsto ios_cap_defs.i,Alvarmapsto j,
Alvarmapsto len,APortTbl,AKsDomain,
AKsDomSchedule',AOSPortAttrTbl', Agvarmapsto Port_num_cur,Alvarmapsto flag,
Alvarmapsto to1,Alvarmapsto to2,Alvarmapsto to3,Alvarmapsto to4,
Alvarmapsto to5,Alvarmapsto to6,Alvarmapsto to7,
Alvarmapsto to8,Alvarmapsto tox2,APartID2Dom
).
hoare remember (1::2::3::4::5::6::7::8::9::10::11::12::13::14::15::16 ::17::18::19::nil)%nat pre.
assert(Htnoport: 0 <= Int.unsigned i1).
eapply Int.unsigned_range_2.
eapply backward_rule1 with ( p :=
(EX i0 j0 tf portattrvl portnumc a2 a3 a4 a5, 
  EX a6 a7 a8 b2 ,
  LV ios_cap_defs.i @ Int32u |-> (Vint32 i0) **
  LV j @ Int32u |-> (Vint32 j0) **
  LV flag @ Int32u |-> tf ** 
 [|(Int.unsigned i0) < (Int.unsigned i1)|] ** 
 [| Cfnoport_P (Int.unsigned i0) (Int.unsigned i9) l1 v'43 v'59 portattrvl v'49 |] **
 [|(Int.unsigned portnumc) <= (Int.unsigned i0)|] ** 

 LV len @ long |-> Vint32 i9 **
 APortTbl (v'36, Int.zero) l1 m3 **
 AKsDomain v'43 **
 AKsDomSchedule' v'59 **
 AOSPortAttrTbl' portattrvl **
 GV Port_num_cur @ char_t |-> (Vint32 portnumc) **
 LV to1 @ char_t |-> Vint32 i1 **
 LV to2 @ char_t |-> a2 **
 LV to3 @ char_t |-> a3 **
 LV to4 @ char_t |-> a4 **
 LV to5 @ char_t |-> a5 **
 LV to6 @ char_t |-> a6 **
 LV to7 @ char_t |-> a7 **
 LV to8 @ char_t |-> a8 **
 LV tox2 @ long |-> b2 ** 
 APartID2Dom v'49 ** H41) 
 \\//
(EX j0 tf portattrvl portnumc a2 a3 a4 a5, 
EX a6 a7 a8 b2,
LV ios_cap_defs.i @ Int32u |-> (Vint32 i1) **
LV j @ Int32u |-> (Vint32 j0) **
LV flag @ Int32u |-> tf ** 
[| Cfnoport_P (Int.unsigned i1) (Int.unsigned i9) l1 v'43 v'59 portattrvl v'49 |] **
[|(Int.unsigned portnumc) <= (Int.unsigned i1)|] ** 

LV len @ long |-> Vint32 i9 **
APortTbl (v'36, Int.zero) l1 m3 **
AKsDomain v'43 **
AKsDomSchedule' v'59 **
AOSPortAttrTbl' portattrvl **
GV Port_num_cur @ char_t |-> (Vint32 portnumc) **
LV to1 @ char_t |-> Vint32 i1 **
LV to2 @ char_t |-> a2 **
LV to3 @ char_t |-> a3 **
LV to4 @ char_t |-> a4 **
LV to5 @ char_t |-> a5 **
LV to6 @ char_t |-> a6 **
LV to7 @ char_t |-> a7 **
LV to8 @ char_t |-> a8 **
LV tox2 @ long |-> b2 ** 
APartID2Dom v'49 ** H41)
). 
assert(Hcond_port: 0 < Int.unsigned i1 \/ 0 = Int.unsigned i1).
clear -Htnoport.
int_auto.
destruct Hcond_port as [Hport1 | Hport2].
intros.
left.
2:{
  right.
  sep pauto.
  rewrite Hport2.
  rewrite Int.repr_unsigned.
  eauto.
  unfold Cfnoport_P.
  intros.
  rewrite <-Hport2 in H41.
  lia.
}
sep pauto.
clear;int_auto.
unfold Cfnoport_P.
intros.
change ($ 0) with Int.zero in H41. 
rewrite unsigned_zero in H41. 
lia.
eapply seq_rule.
eapply while_rule with (tp := Int32u).
intros.
destruct H43.
symbolic_execution.
rewrite Hgi1;eauto.
pure_auto.
symbolic_execution.
rewrite Hgi1;eauto.
pure_auto.
eapply backward_rule1 with ( p :=
(EX i0 j0 tf portattrvl portnumc a2 a3 a4 a5, 
EX a6 a7 a8 b2 ,
LV ios_cap_defs.i @ Int32u |-> (Vint32 i0) **
LV j @ Int32u |-> (Vint32 j0) **
LV flag @ Int32u |-> tf ** 
[|(Int.unsigned i0) < (Int.unsigned i1)|] ** 
[| Cfnoport_P (Int.unsigned i0) (Int.unsigned i9) l1 v'43 v'59 portattrvl v'49 |] **
[|(Int.unsigned portnumc) <= (Int.unsigned i0)|] ** 

LV len @ long |-> Vint32 i9 **
APortTbl (v'36, Int.zero) l1 m3 **
AKsDomain v'43 **
AKsDomSchedule' v'59 **
AOSPortAttrTbl' portattrvl **
GV Port_num_cur @ char_t |-> (Vint32 portnumc) **
LV to1 @ char_t |-> Vint32 i1 **
LV to2 @ char_t |-> a2 **
LV to3 @ char_t |-> a3 **
LV to4 @ char_t |-> a4 **
LV to5 @ char_t |-> a5 **
LV to6 @ char_t |-> a6 **
LV to7 @ char_t |-> a7 **
LV to8 @ char_t |-> a8 **
LV tox2 @ long |-> b2 ** 
APartID2Dom v'49 ** H41)
). 
intros.
destruct H43. 
destruct H43.
sep destruct H43.
sep eexists.
sep cancel 1%nat 1%nat.

sep destruct H43.
lets Htnoport1: Htnoport.
sep split in H43.
rename H46 into Hpnum.
sep remember (1::10::nil)%nat in H43.
false. 
destruct_s s.
simpl in H43; simpljoin1.
simpl in H44.
rewrite H69 in H44.
rewrite H60 in H44.
unfold cmp_int_type in H44.
unfold cmp_val in H44.
unfold cmpu in H44.
apply mapstoval_load in H70; auto.
apply mapstoval_load in H61; auto.
destruct (load Int32u m4 (x47, 0)) eqn : eq1.
pose proof (load_mono Int32u (x47, Int.unsigned Int.zero) H47 H70).
rewrite H70 in H41.
change (Int.unsigned Int.zero) with 0 in H41.
rewrite H41 in eq1.
inverts eq1.
2:{
  destruct H44.
  destruct H41.
  tryfalse.
}
2: simpl; rewrite Hgi1 ;eauto.
eapply join_comm in H47.
lets Hx2:load_local H52 H61.
lets Hm:load_local H47 Hx2. 
change (Int.unsigned Int.zero) with 0 in Hm.
rewrite Hm in H44. 
rewrite sem_common.sempend_ltu_ass1 in H44. 
destruct H44.
destruct H43. 
inverts H43. 
change (Int.eq Int.zero Int.zero) with true in H44. 
simpl in H44. 
tryfalse.
(* j=0 *)
hoare unfold.
hoare forward.
(* flag ′ =ₑ ′ 1;ₛ *)
hoare forward.
(* while  *)
hoare_lifts_trms_pre (Alvarmapsto ios_cap_defs.i,Alvarmapsto j,
Alvarmapsto len,APortTbl,AKsDomain,
AKsDomSchedule',AOSPortAttrTbl', Agvarmapsto Port_num_cur,Alvarmapsto flag,
Alvarmapsto to1,Alvarmapsto to2,Alvarmapsto to3,Alvarmapsto to4,
Alvarmapsto to5,Alvarmapsto to6,Alvarmapsto to7,
Alvarmapsto to8,Alvarmapsto tox2,APartID2Dom
).
hoare remember (1::2::3::4::5::6::7::8::9::10::11::12::13::14::15::16 ::17::18::19::nil)%nat pre.

eapply backward_rule1 with ( p :=
(EX j0 tf portnumc a2 a3 a4 a5, 
  EX a6 a7 a8 b2 ,
  LV ios_cap_defs.i @ Int32u |-> (Vint32 v'60) **
  LV j @ Int32u |-> (Vint32 j0) **
  LV flag @ Int32u |-> tf ** 
 [|(Int.unsigned j0) < (Int.unsigned i9)|] ** 
 [|tf = (V$ 1)|] ** 
 [| PortAttr_P1 (Int.unsigned v'60) (Int.unsigned j0) tf l1 v'43 v'59|] **
 [|portnumc = v'64 |] ** 

 LV len @ long |-> Vint32 i9 **
 APortTbl (v'36, Int.zero) l1 m3 **
 AKsDomain v'43 **
 AKsDomSchedule' v'59 **
 AOSPortAttrTbl' v'63 **
 GV Port_num_cur @ char_t |-> (Vint32 portnumc) **
 LV to1 @ char_t |-> Vint32 i1 **
 LV to2 @ char_t |-> a2 **
 LV to3 @ char_t |-> a3 **
 LV to4 @ char_t |-> a4 **
 LV to5 @ char_t |-> a5 **
 LV to6 @ char_t |-> a6 **
 LV to7 @ char_t |-> a7 **
 LV to8 @ char_t |-> a8 **
 LV tox2 @ long |-> b2 ** 
 APartID2Dom v'49 ** H41) 
 \\//
(EX j0 tf portattrvl portnumc a2 a3 a4 a5, 
EX a6 a7 a8 b2 curcfport,
LV ios_cap_defs.i @ Int32u |-> (Vint32 v'60) **
LV j @ Int32u |-> (Vint32 j0) **
LV flag @ Int32u |-> tf ** 
[|(Int.unsigned j0) < (Int.unsigned i9)|] **  
[|tf = (V$ 0)|] ** 
[| PortAttr_P (Z.to_nat (Int.unsigned v'60)) (Z.to_nat (Int.unsigned j0)) (Int.unsigned i9) tf l1 portattrvl v'49  |] **
[|portattrvl = update_nth_vallist (Z.to_nat (Int.unsigned a4)) v'63 ((V$ 1):: a3 :: a8 :: a5 :: a6 :: a7 :: nil)|] ** 
[|portnumc = Int.repr ((Int.unsigned v'64) + 1) |] ** 
[| nth_vallist (Z.to_nat (Int.unsigned v'60)) l1 = Some curcfport /\
   nth_val 0 curcfport =Some (Vint32 a4)
|] ** 

LV len @ long |-> Vint32 i9 **
APortTbl (v'36, Int.zero) l1 m3 **
AKsDomain v'43 **
AKsDomSchedule' v'59 **
AOSPortAttrTbl' portattrvl **
GV Port_num_cur @ char_t |-> (Vint32 portnumc) **
LV to1 @ char_t |-> Vint32 i1 **
LV to2 @ char_t |-> a2 **
LV to3 @ char_t |-> a3 **
LV to4 @ char_t |-> Vint32 a4 **
LV to5 @ char_t |-> a5 **
LV to6 @ char_t |-> a6 **
LV to7 @ char_t |-> a7 **
LV to8 @ char_t |-> a8 **
LV tox2 @ long |-> b2 ** 
APartID2Dom v'49 ** H41)
\\//
(EX j0 tf portnumc a2 a3 a4 a5, 
EX a6 a7 a8 b2,
LV ios_cap_defs.i @ Int32u |-> (Vint32 v'60) **
LV j @ Int32u |-> (Vint32 j0) **
LV flag @ Int32u |-> tf ** 
[|(Int.unsigned j0) = (Int.unsigned i9)|] **  
[|tf = (V$ 1)|] ** 
[| PortAttr_P1 (Int.unsigned v'60) (Int.unsigned j0) tf l1 v'43 v'59|] **
[|portnumc = v'64 |] ** 

LV len @ long |-> Vint32 i9 **
APortTbl (v'36, Int.zero) l1 m3 **
AKsDomain v'43 **
AKsDomSchedule' v'59 **
AOSPortAttrTbl' v'63 **
GV Port_num_cur @ char_t |-> (Vint32 portnumc) **
LV to1 @ char_t |-> Vint32 i1 **
LV to2 @ char_t |-> a2 **
LV to3 @ char_t |-> a3 **
LV to4 @ char_t |-> a4 **
LV to5 @ char_t |-> a5 **
LV to6 @ char_t |-> a6 **
LV to7 @ char_t |-> a7 **
LV to8 @ char_t |-> a8 **
LV tox2 @ long |-> b2 ** 
APartID2Dom v'49 ** H41)
). 
rename H45 into Hpnum.
assert(Hlen:0 < Int.unsigned i9 \/ 0 = Int.unsigned i9).
clear -H38.
int_auto.
destruct Hlen.
intros.
left.
2:{
  right.
  right.
  sep pauto.
  unfold PortAttr_P1.
  intros.
  destruct H41.
  rewrite unsigned_repr_0 in H48.
  lia.
  Optimize Proof.
  Optimize Heap.
}
eapply aexists_intro. 
exists ($ 0).
sep pauto.
unfold PortAttr_P1.
intros.
destruct H41.
rewrite unsigned_repr_0 in H48.
lia.
rename H45 into Hpnum.
eapply seq_rule.
eapply while_rule (* with (tp := Int32u) *).
intros.
destruct H45.
sep normal in H45.
sep destruct H45.
ssplit_apure_in H45.
sep normal;sep eexists.       
sep get rv. 
pure_auto.
rewrite H47.
eauto.
rewrite H47. 
pure_auto.
destruct H45.
sep normal in H45.
sep destruct H45.
ssplit_apure_in H45.
sep normal;sep eexists.       
sep get rv. 
pure_auto.
rewrite H47.
eauto.
rewrite H47. 
pure_auto.
sep normal in H45.
sep destruct H45.
ssplit_apure_in H45.
sep normal;sep eexists.       
sep get rv. 
pure_auto.
rewrite H47.
eauto.
rewrite H47. 
pure_auto.
eapply backward_rule1 with ( p :=
(EX j0 tf portnumc a2 a3 a4 a5, 
EX a6 a7 a8 b2 ,
LV ios_cap_defs.i @ Int32u |-> (Vint32 v'60) **
LV j @ Int32u |-> (Vint32 j0) **
LV flag @ Int32u |-> tf ** 
[|(Int.unsigned j0) < (Int.unsigned i9)|] ** 
[|tf = (V$ 1)|] ** 
[| PortAttr_P1 (Int.unsigned v'60) (Int.unsigned j0) tf l1 v'43 v'59|] **
[|portnumc = v'64 |] ** 
LV len @ long |-> Vint32 i9 **
APortTbl (v'36, Int.zero) l1 m3 **
AKsDomain v'43 **
AKsDomSchedule' v'59 **
AOSPortAttrTbl' v'63 **
GV Port_num_cur @ char_t |-> (Vint32 portnumc) **
LV to1 @ char_t |-> Vint32 i1 **
LV to2 @ char_t |-> a2 **
LV to3 @ char_t |-> a3 **
LV to4 @ char_t |-> a4 **
LV to5 @ char_t |-> a5 **
LV to6 @ char_t |-> a6 **
LV to7 @ char_t |-> a7 **
LV to8 @ char_t |-> a8 **
LV tox2 @ long |-> b2 ** 
APartID2Dom v'49 ** H41)).
intros.
destruct H45.
destruct H45.
sep destruct H45.
sep eexists.
sep cancel 1%nat 1%nat.
destruct H45.
sep destruct H45.
sep split in H45.
rename H51 into Hnumadd.
rename H52 into Hxv.

sep remember (2::3::4::nil)%nat in H45.
false.
destruct_s s.
simpl in H45; simpljoin1.
simpl in H46.
rewrite H88,H79,H70 in H46.
unfold cmp_int_type in H46.
unfold bop_int_type in H46.
unfold cmp_val in H46.
unfold cmpu in H46.
apply mapstoval_load in H89,H80,H71; auto.
destruct (load long m4 (x62, 0%Z)) eqn : eq1.
pose proof (load_mono long (x62, Int.unsigned Int.zero) H52 H89).
rewrite H89 in H41.
change (Int.unsigned Int.zero) with 0%Z in H41.
rewrite H41 in eq1.
inverts eq1.
2:{
  destruct H46.
  destruct H41.
  tryfalse.
}
eapply join_comm in H57.
lets Hx2:load_local H62 H71.
lets Hm:load_local H57 Hx2. 
eapply join_comm in H52.
lets Hm1:load_local H52 Hm.
change (Int.unsigned Int.zero) with 0%Z in Hm1.
rewrite Hm1 in H46.
assert(Hltlen: (Int.ltu x1 i9 = true)).
clear -H47.
int_auto.
rewrite Hltlen in H46.
eapply join_comm in H57.
lets Hs2: load_local H57 H80.
lets Hs3: load_local H52 Hs2.
change (Int.unsigned Int.zero) with 0%Z in Hs3.
rewrite Hs3 in H46.
unfold bool_and in H46.
change (if Int.ltu Int.zero Int.one && Int.ltu Int.zero ($ 0)
then Some (Vint32 Int.one)
else Some (Vint32 Int.zero)) with (Some (Vint32 Int.zero)) in H46.
destruct H46.
destruct H45.
inverts H45.
inverts H46.
sep destruct H45.
sep split in H45.
rename H50 into Hnum1.
sep remember (2::3::4::nil)%nat in H45.
false.
destruct_s s.
simpl in H45; simpljoin1.
simpl in H46.
rewrite H87,H78,H69 in H46.
unfold cmp_int_type in H46.
unfold bop_int_type in H46.
unfold cmp_val in H46.
unfold cmpu in H46.
apply mapstoval_load in H88,H79,H70; auto.
destruct (load long m4 (x60, 0%Z)) eqn : eq1.
pose proof (load_mono long (x60, Int.unsigned Int.zero) H51 H88).
rewrite H88 in H41.
change (Int.unsigned Int.zero) with 0%Z in H41.
rewrite H41 in eq1.
inverts eq1.
2:{
  destruct H46.
  destruct H41.
  tryfalse.
}
eapply join_comm in H56.
lets Hx2:load_local H61 H70.
lets Hm:load_local H56 Hx2. 
eapply join_comm in H51.
lets Hm1:load_local H51 Hm.
change (Int.unsigned Int.zero) with 0%Z in Hm1.
rewrite Hm1 in H46.
assert(Hltlen: (Int.ltu x1 i9 = false)).
clear -H47.
int_auto.
rewrite Hltlen in H46.
eapply join_comm in H56.
lets Hs2: load_local H56 H79.
lets Hs3: load_local H51 Hs2.
change (Int.unsigned Int.zero) with 0%Z in Hs3.
rewrite Hs3 in H46.
unfold bool_and in H46.
change (if Int.ltu Int.zero Int.zero && Int.ltu Int.zero ($ 1)
then Some (Vint32 Int.one)
else Some (Vint32 Int.zero)) with (Some (Vint32 Int.zero)) in H46.
destruct H46.
destruct H45.
inverts H45.
inverts H46.

do 2 destruct H27.
unfolds in H27.
simpl in H27.
inverts H27.
do 2 destruct H12.
unfolds in H12.
simpl in H12.
inverts H12.
assert(Hport: Int.unsigned v'60 < PORT_NUMS).
clear -H43 H27.
unfold_part_defs.
int_auto.
hoare unfold.
assert(Hlenj: Int.unsigned v'73 < DSCHEDULE_SIZE ).
clear -H12 H49.
unfold_part_defs. 
int_auto.
(* to2′ =ₑ ((uconf′→ portTbl)[i′])..partitionID ;ₛ  *)
unfold APortTbl.
hoare unfold.
simpl in H46.
inverts H46.
eapply backward_rule1.
introv Hsat.
sep_lifts_trms_in Hsat AportTbl'.
eapply AportTbl'_unfold_any_idx_frm with (idx:= Z.to_nat (Int.unsigned v'60)); eauto.
rewrite H41.
unfold_part_defs ; unfold nat_of_Z; auto with zarith.
unfold node_offt.
hoare unfold.
(* len′ =ₑ ((uconf′→ cpus)[coreNum′])..cpu_ksDomScheduleLength ;ₛ  *)
hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel to2; eauto.
sep auto.
  Optimize Proof.
  Optimize Heap.
{
introv Hsat .
sep_lifts_trms_in Hsat (Astruct (v'85, Int.zero) ucos_conf_t).
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
| try (apply Hport; auto); try (apply Hport; auto)
| simpl; try apply cpu_conf_t_min_max
| auto
| simpl; auto
| splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
| unfold id_nth; simpl; auto
| auto ].
simpl;eauto.
simpl (typelen port_conf_t).
sep cancel 2%nat 1%nat;eauto.
clear -Hport.
unfold_part_defs.
int_auto.
eapply leb_bytemax_true_intro in H57,H52,H56,H58,H59;eauto.
simpl.
rewrite H57,H52,H56,H58,H59.
splits;eauto.
}
eapply eq_int; eauto.
introv Hsat; eexists; sep cancel p_local; simpl; auto.
change ( LV to2 @ char_t
|-> nth_val' 3
      (Vint32 i21
      :: Vint32 i20 :: Vint32 i19 :: Vint32 i9 :: Vint32 i1 :: nil))
with (LV to2 @ char_t |-> Vint32 i9).
(* tox2′ =ₑ (efield (ksDomSchedule′[j′]) dscd_domain);ₛ *)
eapply backward_rule1.
intros.
eapply AKsDomSchedule'_unfold_any_idx_frm with (idx:= Z.to_nat(Int.unsigned v'73)); eauto.
sep_lifts_trms_in H46 (AKsDomSchedule').
sep pauto.
unfold AKsDomSchedule' in H46.
sep normal in H46.
destruct H46.
sep split in H46.
destruct H60.
rewrite H69.
clear -Hlenj.
unfold_part_defs.
unfold nat_of_Z.
int_auto.
hoare unfold.
clear H40.
lets Hsplit : H46.  
eapply new_array_type_vallist_match_split_domsch in Hsplit; eauto.
destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
lets Hvl: struct_type_vallist_match_elim_2 Hsp.
destruct Hvl. destruct H40. subst v'88. 

hoare_lifts_trms_pre (Aop).
hoare forward.
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel tox2; eauto.
sep auto.
2:{
  instantiate (1:= long ).
  eapply eq_int;  splits;eauto.
}
2: {
  pure_auto. 
  sep auto.
  }
pure_auto.
eapply struct_array_member_rv; try eauto.
symbolic_execution.
symbolic_execution.
sep cancel Astruct.
eauto.
simpl; auto.
eapply gjb_common.int_ltu_zero_eq_false.
clear -Hlenj.
unfold_part_defs.
int_auto.
simpl.
clear. int_auto.
clear -H60.
split; pure_auto; do 2 destruct H; tryfalse.
unfold id_nth. simpl; auto.
change (LV tox2 @ long |-> nth_val' 0 (x8 :: x11 :: nil))
with (LV tox2 @ long |-> x8).
destruct Hsp.
destruct x8;tryfalse.
destruct H61.
destruct x11;tryfalse.
(* 求ksdomain[]下标合法，去掉-1 ，打开之前的AksDomSchedule' *)
eapply backward_rule1.
introv Hsat.
simpl in H22.
inverts H22.
sep_lifts_trms_in Hsat AksDomSchedule'.
eapply AksDomSchedule'_unfold_any_idx_frm with (idx:= Z.to_nat (Int.unsigned v'73)); eauto.
rewrite H14.
unfold DSCHEDULE_SIZE in *.
unfold nat_of_Z in *.
auto with zarith.
unfold node_offt.
hoare unfold.

assert(Hgx2: 0 <= Int.unsigned i22 < 8).
unfolds in H42.
specialize (H42 (Int.unsigned v'73)).
specializes H42.
clear -H12.
int_auto.
unfold nat_of_Z.
rewrite <-H69.
eapply nth_error_middle.
simpl;eauto.
simpl;eauto.
unfold nat_of_Z.
rewrite <-H62.
eapply nth_vallist_get_idx.
simpl;eauto.
simpl;eauto.
destruct H42.
subst i25.
subst i24.
destruct H28.
unfolds in H28.
specialize (H28 (Int.unsigned v'73)).
destruct H28.
unfold_part_defs.
clear -Hlenj.
int_auto.
destruct H28.
destruct H28.
unfold nat_of_Z in *.
rewrite <-H69 in H28.
rewrite nth_error_middle in H28.
inverts H28.
destruct H67.
unfolds in H28.
simpl in H28;inverts H28.
unfold_part_defs.
eauto.

eapply backward_rule1.
introv Hsat.
eapply AksDomSchedule'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned v'73)); eauto.
unfold DSCHEDULE_SIZE in *.
unfold nat_of_Z in *.
clear -Hlenj.
int_auto.
unfold node_offt.
sep pauto.
simpl (typelen dschedule_conf_t).
split;eauto.
simpl;splits;eauto.

(* to3′  =ₑ (ksDomains′ [ tox2′ ])..dom_t_ID  ;ₛ  *)
unfold AKsDomain.
hoare unfold.
eapply backward_rule1.
intros.
eapply AKsDomains'_unfold_any_idx_frm with (idx:= Z.to_nat(Int.unsigned i22)); eauto.
sep cancel 2%nat 1%nat;eauto.
rewrite H67.
unfold_part_defs.
unfold nat_of_Z.
clear -H72 H73.
int_auto.
unfold node_offt.
hoare unfold.

hoare_lifts_trms_pre (Aop,ksDomains).
hoare forward.
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel to3; eauto.
sep auto.
  Optimize Proof.
  Optimize Heap.
2:{
  instantiate (1:= char_t ).
  eapply eq_int;  eauto.
}
2: {
  pure_auto. 
  sep auto.
  }
pure_auto.
eapply struct_array_member_rv with (t := (domain_t ) ); try eauto.
symbolic_execution.
symbolic_execution.
sep cancel Astruct.
eauto.
unfolds;eauto.
simpl; auto.
eapply gjb_common.int_ltu_zero_eq_false.
clear -H73.
int_auto.
simpl.
clear; int_auto.
simpl.
change 255 with Byte.max_unsigned in H81,H87,H88.
rewrite H81,H87,H88.
splits;eauto.
go. 
clear -H60.
split; pure_auto; do 2 destruct H; tryfalse.
go.
change (LV to3 @ char_t
|-> nth_val' 1
      (Vint32 i33
      :: Vint32 i28
         :: Vint32 i32
            :: Vint32 i31
               :: Vint32 i30
                  :: Vint32 i29
                     :: Vint32 i27 :: Vint32 i26 :: x15 :: nil))
                      with (LV to3 @ char_t
                      |-> Vint32 i28).

(* if *)
assert(Hor : ( i9 =  i28) \/ ( i9 <> i28)) by tauto.
destruct Hor as [Hif | Hnif].
(* 进if *)
hoare forward.
rewrite leb_bytemax_true_intro;eauto.
rewrite leb_bytemax_true_intro;eauto.
pure_auto.
2:{
  hoare unfold.
  assert(Int.eq i28 i28 = true).
  eapply Int.eq_true.
  destruct H75.
  rewrite H76 in H75.
  simpl in H75.
  tryfalse.
  rewrite H76 in H75.
  simpl in H75.
  tryfalse.
}
2:{
  destruct H75.
  sep split in H75.
  sep pauto.
  sep split in H75.
  sep pauto.
}
(* 进入之后 *)
assert (Hv60: $ Z.of_nat (Z.to_nat (Int.unsigned v'60)) =  v'60).
rewrite <-Int.repr_unsigned.
rewrite Z2Nat.id;eauto. 
eapply Int.unsigned_range_2.
inverts Hv60.
assert(Hv60': Int.mul ($ Z.of_nat (Z.to_nat (Int.unsigned v'60))) ($ 5)
   =  $ Z.of_nat (Z.to_nat (Int.unsigned v'60) * 5)).
   rewrite H75.
   clear -Hport.
   change PORT_NUMS with 64 in *.
   int auto. mauto.
hoare unfold.
hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel to4; eauto.
sep auto.
{
introv Hsat .
sep_lifts_trms_in Hsat (Astruct (v'85, Int.zero) ucos_conf_t).
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
| try (apply Hport; auto); try (apply Hport; auto)
| simpl; try apply cpu_conf_t_min_max
| auto
| simpl; auto
| splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
| unfold id_nth; simpl; auto
| auto ].
simpl;eauto.
simpl (typelen port_conf_t).
sep cancel 15%nat 1%nat;eauto.
clear -Hport.
unfold_part_defs.
int_auto.
eapply leb_bytemax_true_intro in H52,H56,H57,H58,H59;eauto.
simpl.
rewrite H52,H56,H57,H58,H59.
splits;eauto.
}
eapply eq_int; eauto.
introv Hsat; eexists; sep cancel p_local; simpl; auto.
change ( LV to4 @ char_t
|-> nth_val' 0
      (Vint32 i21
      :: Vint32 i20 :: Vint32 i19 :: Vint32 i28 :: Vint32 i1 :: nil))
with (LV to4 @ char_t |-> Vint32 i21).
hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel to5; eauto.
sep auto.
{
introv Hsat .
sep_lifts_trms_in Hsat (Astruct (v'85, Int.zero) ucos_conf_t).
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
| try (apply Hport; auto); try (apply Hport; auto)
| simpl; try apply cpu_conf_t_min_max
| auto
| simpl; auto
| splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
| unfold id_nth; simpl; auto
| auto ].
simpl;eauto.
simpl (typelen port_conf_t).
sep cancel 16%nat 1%nat;eauto.
clear -Hport.
unfold_part_defs.
int_auto.
eapply leb_bytemax_true_intro in H52,H56,H57,H58,H59;eauto.
simpl.
rewrite H52,H56,H57,H58,H59.
splits;eauto.
}
eapply eq_int; eauto.
introv Hsat; eexists; sep cancel p_local; simpl; auto.
change ( LV to5 @ char_t
|-> nth_val' 1
      (Vint32 i21
      :: Vint32 i20 :: Vint32 i19 :: Vint32 i28 :: Vint32 i1 :: nil))
with (LV to5 @ char_t |-> Vint32 i20).
hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel to6; eauto.
sep auto.
  Optimize Proof.
  Optimize Heap.
{
introv Hsat .
sep_lifts_trms_in Hsat (Astruct (v'85, Int.zero) ucos_conf_t).
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
| try (apply Hport; auto); try (apply Hport; auto)
| simpl; try apply cpu_conf_t_min_max
| auto
| simpl; auto
| splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
| unfold id_nth; simpl; auto
| auto ].
simpl;eauto.
simpl (typelen port_conf_t).
sep cancel 17%nat 1%nat;eauto.
clear -Hport.
unfold_part_defs.
int_auto.
eapply leb_bytemax_true_intro in H52,H56,H57,H58,H59;eauto.
simpl.
rewrite H52,H56,H57,H58,H59.
splits;eauto.
}
eapply eq_int; eauto.
introv Hsat; eexists; sep cancel p_local; simpl; auto.
change ( LV to6 @ char_t
|-> nth_val' 2
      (Vint32 i21
      :: Vint32 i20 :: Vint32 i19 :: Vint32 i28 :: Vint32 i1 :: nil))
with (LV to6 @ char_t |-> Vint32 i19).
hoare forward.
hoare_lifts_trms_pre ( Aop).
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel to7; eauto.
sep auto.
{
introv Hsat .
sep_lifts_trms_in Hsat (Astruct (v'85, Int.zero) ucos_conf_t).
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
| try (apply Hport; auto); try (apply Hport; auto)
| simpl; try apply cpu_conf_t_min_max
| auto
| simpl; auto
| splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
| unfold id_nth; simpl; auto
| auto ].
simpl;eauto.
simpl (typelen port_conf_t).
sep cancel 18%nat 1%nat;eauto.
clear -Hport.
unfold_part_defs.
int_auto.
eapply leb_bytemax_true_intro in H52,H56,H57,H58,H59;eauto.
simpl.
rewrite H52,H56,H57,H58,H59.
splits;eauto.
}
eapply eq_int; eauto.
introv Hsat; eexists; sep cancel p_local; simpl; auto.
change ( LV to7 @ char_t
|-> nth_val' 4
      (Vint32 i21
      :: Vint32 i20 :: Vint32 i19 :: Vint32 i28 :: Vint32 i1 :: nil))
with (LV to7 @ char_t |-> Vint32 i1 ).
(* to8′ =ₑ partitionID2Domain′[to2′]  ;ₛ *)
unfold APartID2Dom at 2.
hoare unfold.
assert(Hi26:Int.unsigned i28 < 8).
{
  destruct H48 as (HportidG & _).
  lets HportID : HportidG (Int.unsigned v'60).
  destruct HportID.
  clear -Hport.
  change PORT_NUMS with 64 in *.
  int_auto.
  do 2 destruct H48.
  unfold nat_of_Z in H48.
  rewrite <-H53 in H48.
  rewrite nth_vallist_get_idx in H48.
  inverts H48.
  destruct H89.
  unfolds in H48.
  simpl in H48.
  inverts H48.
  clear -H89.
  unfold_part_defs.
  int_auto.
}
hoare forward.
rewrite leb_bytemax_true_intro;eauto.
rewrite H86.
clear -Hi26.
change PARTITION_NUM with 8.
int_auto.
eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
rewrite H86.
clear -Hi26.
change PARTITION_NUM with 8.
int_auto.
(* 拆分OSPortAttrTbl的值表 *)
eapply backward_rule1.
introv Hsat.
sep_lifts_trms_in Hsat (AOSPortAttrTbl').
eapply OSportattr_unfold_any_idx_frm in Hsat.
instantiate (1:=  (Z.to_nat (Int.unsigned i21))) in Hsat. 
eauto.
assert(Hi19:Int.unsigned i21 < PORT_NUMS).
{
  destruct H48 as (_ & _ & portvlG & _).
  lets HportID : portvlG (Int.unsigned v'60).
  destruct HportID.
  clear -Hport.
  change PORT_NUMS with 64 in *.
  int_auto.
  do 2 destruct H48.
  unfold nat_of_Z in H48.
  rewrite <-H53 in H48.
  rewrite nth_vallist_get_idx in H48.
  inverts H48.
  destruct H89.
  unfolds in H48.
  simpl in H48.
  inverts H48.
  clear -H89.
  change PORT_NUMS with 64.
  int_auto.
}
unfold AOSPortAttrTbl' in Hsat.
sep normal in Hsat.
destruct Hsat.
sep split in H89.
destruct H90.
rewrite H98.
unfold nat_of_Z.
clear -Hi19.
change PORT_NUMS with 64 in *.
int_auto.
hoare unfold.
lets Hsplit : H89.  
remember((v'42 ++ v'97 :: v'43)).
eapply new_array_type_vallist_match_split2 in Hsplit; eauto.
destruct Hsplit.
simpl in H95.
destruct H95.
unfold struct_type_vallist_match' in H95.
destruct v'97. tryfalse.
destruct H95.
destruct v'97. tryfalse.
destruct H97.
destruct v'97. tryfalse.
destruct H98.
destruct v'97. tryfalse.
destruct H99.
destruct v'97. tryfalse.
destruct H100.
destruct v'97. tryfalse.
destruct H101.
destruct v'97. 
2:tryfalse.
(* efield (OSPortAttrTbl′[to4′]) portat_partitionID =ₑ to2′ ;ₛ *)
hoare forward.
hoare_lifts_trms_pre Aop.

eapply assign_rule_array_struct_aop_general' with (tp' := char_t).
(* ;eauto. *)
right.
right.
eauto.
split; intros.
sep cancel Agvarmapsto OSPortAttrTbl.
sep_lifts_trms_in H103 (Alvarmapsto to4).
instantiate(3:= Int.unsigned i21).
rewrite Int.repr_unsigned. 
sep cancel (Alvarmapsto to4).
sep cancel A_dom_lenv.  
sep cancel Astruct.
eauto.
sep pauto.
rewrite Int.repr_unsigned;eauto. 
unfolds;eauto.
go. 
go.
go. 
go.
go. 
go.
go. 
simpl; auto with zarith.
simpl;eauto.
simpl;eauto.
2:{
  intros. 
  get_hsat Hsat.  
  sep_lifts_trms_in Hsat (Agvarmapsto OSPortAttrTbl, Alvarmapsto to4, A_dom_lenv).
  assert (Hvi19: $ Z.of_nat (Z.to_nat (Int.unsigned i21)) =  i21).
  rewrite <-Int.repr_unsigned.
  rewrite Z2Nat.id;eauto. 
  eapply Int.unsigned_range_2.
  rewrite <-Hvi19 in Hsat at 1.
  rewrite Z2Nat.id in Hsat;eauto.
  2: clear; int_auto.
  eapply Info_get_lv_general_int8 in Hsat; eauto. 
  unfolds;eauto.
  simpl;eauto.
  simpl;eauto.
  clear; int_auto.
  simpl (typelen port_attr_t).
  clear. lets H: Byte.min_signed_neg.
  int_auto.
  simpl (typelen port_attr_t).
  clear. change Byte.max_unsigned with 255.
  int_auto.
  }
  2: {
    intros.
    symbolic_execution.
    rewrite leb_bytemax_true_intro;eauto.
  }
  eapply eq_int;eauto.
  introv Hsat; eexists; sep cancel p_local; simpl; auto.
  hoare forward.
hoare_lifts_trms_pre Aop.
eapply assign_rule_array_struct_aop_general' with (tp' := char_t).
right.
right.
eauto.
split; intros.
sep cancel Agvarmapsto OSPortAttrTbl.
sep_lifts_trms_in H103 (Alvarmapsto to4).
instantiate(3:= Int.unsigned i21).
sep cancel (Alvarmapsto to4).
sep cancel A_dom_lenv.  
sep cancel Astruct.
eauto.
sep pauto.
unfolds;eauto.
go. 
go.
go. 
go.
go. 
go.
go. 
simpl; auto with zarith.
simpl;eauto.
simpl;eauto.
2:{
  intros. 
  get_hsat Hsat.  
  sep_lifts_trms_in Hsat (Agvarmapsto OSPortAttrTbl, Alvarmapsto to4, A_dom_lenv).
  eapply Info_get_lv_general_int8 in Hsat; eauto. 
  unfolds;eauto.
  simpl;eauto.
  simpl;eauto.
  clear; int_auto.
  simpl (typelen port_attr_t).
  clear. lets H: Byte.min_signed_neg.
  int_auto.
  simpl (typelen port_attr_t).
  clear. change Byte.max_unsigned with 255.
  int_auto.
  }
  2: {
    intros.
    symbolic_execution.
    assert(Hnth: rule_type_val_match char_t (nth_val' (Z.to_nat (Int.unsigned i28)) v'49) = true).
    {
     eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
   rewrite H86.
   change PARTITION_NUM with 8.
   clear -Hi26.
   int_auto.
    }
    simpl in Hnth.
    eauto.
  }
  eapply eq_int;eauto.
  introv Hsat; eexists; sep cancel p_local; simpl; auto.

  hoare forward.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_array_struct_aop_general' with (tp' := char_t).
  right.
  right.
  eauto.
  split; intros.
  sep cancel Agvarmapsto OSPortAttrTbl.
  sep_lifts_trms_in H103 (Alvarmapsto to4).
  instantiate(3:= Int.unsigned i21).
  sep cancel (Alvarmapsto to4).
  sep cancel A_dom_lenv.  
  sep cancel Astruct.
  eauto.
  sep pauto.
  unfolds;eauto.
  go. 
  go.
  go. 
  go.
  go. 
  go.
  go. 
  simpl; auto with zarith.
  simpl;eauto.
  simpl;eauto.
  2:{
    intros. 
    get_hsat Hsat.  
    sep_lifts_trms_in Hsat (Agvarmapsto OSPortAttrTbl, Alvarmapsto to4, A_dom_lenv).
    eapply Info_get_lv_general_int8 in Hsat; eauto. 
    unfolds;eauto.
    simpl;eauto.
    simpl;eauto.
    clear; int_auto.
    simpl (typelen port_attr_t).
    clear. lets H: Byte.min_signed_neg.
    int_auto.
    simpl (typelen port_attr_t).
    clear. change Byte.max_unsigned with 255.
    int_auto.
    }
  2: {
    intros.
    symbolic_execution.
    rewrite leb_bytemax_true_intro;eauto.
    }
  eapply eq_int;eauto.
  introv Hsat; eexists; sep cancel p_local; simpl; auto.

  hoare forward.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_array_struct_aop_general' with (tp' := char_t).
  right.
  right.
  eauto.
  split; intros.
  sep cancel Agvarmapsto OSPortAttrTbl.
  sep_lifts_trms_in H103 (Alvarmapsto to4).
  instantiate(3:= Int.unsigned i21).
  sep cancel (Alvarmapsto to4).
  sep cancel A_dom_lenv.  
  sep cancel Astruct.
  eauto.
  sep pauto.
  unfolds;eauto.
  go. 
  go.
  go. 
  go.
  go. 
  go.
  go. 
  simpl; auto with zarith.
  simpl;eauto.
  simpl;eauto.
  2:{
    intros. 
    get_hsat Hsat.  
    sep_lifts_trms_in Hsat (Agvarmapsto OSPortAttrTbl, Alvarmapsto to4, A_dom_lenv).
    eapply Info_get_lv_general_int8 in Hsat; eauto. 
    unfolds;eauto.
    simpl;eauto.
    simpl;eauto.
    clear; int_auto.
    simpl (typelen port_attr_t).
    clear. lets H: Byte.min_signed_neg.
    int_auto.
    simpl (typelen port_attr_t).
    clear. change Byte.max_unsigned with 255.
    int_auto.
    }
    2: {
      intros.
      symbolic_execution.
      rewrite leb_bytemax_true_intro;eauto.
      }
    eapply eq_int;eauto.
    introv Hsat; eexists; sep cancel p_local; simpl; auto.

  hoare forward.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_array_struct_aop_general' with (tp' := char_t).
  right.
  right.
  eauto.
  split; intros.
  sep cancel Agvarmapsto OSPortAttrTbl.
  sep_lifts_trms_in H103 (Alvarmapsto to4).
  instantiate(3:= Int.unsigned i21).
  sep cancel (Alvarmapsto to4).
  sep cancel A_dom_lenv.  
  sep cancel Astruct.
  eauto.
  sep pauto.
  unfolds;eauto.
  go. 
  go.
  go. 
  go.
  go. 
  go.
  go. 
  simpl; auto with zarith.
  simpl;eauto.
  simpl;eauto.
  2:{
    intros. 
    get_hsat Hsat.  
    sep_lifts_trms_in Hsat (Agvarmapsto OSPortAttrTbl, Alvarmapsto to4, A_dom_lenv).
    eapply Info_get_lv_general_int8 in Hsat; eauto. 
    unfolds;eauto.
    simpl;eauto.
    simpl;eauto.
    clear; int_auto.
    simpl (typelen port_attr_t).
    clear. lets H: Byte.min_signed_neg.
    int_auto.
    simpl (typelen port_attr_t).
    clear. change Byte.max_unsigned with 255.
    int_auto.
    }
    2: {
      intros.
      symbolic_execution.
      rewrite leb_bytemax_true_intro;eauto.
      }
    eapply eq_int;eauto.
    introv Hsat; eexists; sep cancel p_local; simpl; auto.

  hoare forward.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_array_struct_aop_general' with (tp' := char_t).
  right.
  right.
  eauto.
  split; intros.
  sep cancel Agvarmapsto OSPortAttrTbl.
  sep_lifts_trms_in H103 (Alvarmapsto to4).
  instantiate(3:= Int.unsigned i21).
  sep cancel (Alvarmapsto to4).
  sep cancel A_dom_lenv.  
  sep cancel Astruct.
  eauto.
  sep pauto.
  unfolds;eauto.
  go. 
  go.
  go. 
  go.
  go. 
  go.
  go. 
  simpl; auto with zarith.
  simpl;eauto.
  simpl;eauto.
  2:{
    intros. 
    get_hsat Hsat.  
    sep_lifts_trms_in Hsat (Agvarmapsto OSPortAttrTbl, Alvarmapsto to4, A_dom_lenv).
    eapply Info_get_lv_general_int8 in Hsat; eauto. 
    unfolds;eauto.
    simpl;eauto.
    simpl;eauto.
    clear; int_auto.
    simpl (typelen port_attr_t).
    clear. lets H: Byte.min_signed_neg.
    int_auto.
    simpl (typelen port_attr_t).
    clear. change Byte.max_unsigned with 255.
    int_auto.
    }
    2: {
      intros.
      symbolic_execution.
      }
    eapply eq_int;eauto.
    introv Hsat; eexists; sep cancel p_local; simpl; auto.
(* ++ Port_num_cur ′;ₛ *)
hoare forward.
rewrite leb_bytemax_true_intro;eauto.
clear -Hpnum Hport.
unfold_part_defs.
int_auto.
(* flag ′ =ₑ ′ 0 *)
hoare forward.
(* end assign *)
(* 进if，j<len *)
assert(Heqv60:(Z.to_nat (Int.unsigned v'60)) = (Z.to_nat (Int.unsigned
($ Z.of_nat (Z.to_nat (Int.unsigned v'60))))) ).
{
  rewrite Z2Nat.id;eauto.
  2:{ clear. int_auto. }
  rewrite Int.repr_unsigned;eauto.
}
assert(Hnth: rule_type_val_match char_t (nth_val' (Z.to_nat (Int.unsigned i28)) v'49) = true).
{
 eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
rewrite H86.
change PARTITION_NUM with 8.
clear -Hi26.
int_auto.
}
eapply adisj_intro.
right.
eapply adisj_intro.
left.
sep pauto.
sep cancel Aop.
sep cancel A_dom_lenv.
2:{
  rewrite <-Heqv60.
  rewrite <-H53.
  split.
  eapply nth_vallist_get_idx.
  simpl;eauto.
  rewrite Int.repr_unsigned;eauto.
}
3: simpl;eauto.
(* AKsDomains' *)
eapply AKsDomains'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned i22));eauto.
clear -H73.
unfold nat_of_Z.
unfold_part_defs.
int_auto.
unfold node_offt at 1.
sep normal.
do 3 eexists.
sep pauto.
sep cancel Aarray.
sep cancel 5%nat 1%nat.
2:{
  simpl.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  splits;eauto.
}
2:eauto.
(* APortTbl *)
eapply AportTbl'_select_sn_strong_frm with  (idx:= Z.to_nat (Int.unsigned v'60));eauto.
clear -Hport.
unfold nat_of_Z.
change PORT_NUMS with 64 in *.
int_auto.
unfold node_offt at 1.
sep normal.
do 2 eexists.
sep pauto.
sep cancel 10%nat 1%nat.
rewrite Heqv60.
sep cancel AportTbl'.
2:{
  rewrite Heqv60 at 1.
  split;eauto.
  simpl.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  splits;eauto.
}
(* AKsDomSchedule' *)
eapply AKsDomSchedule'_select_sn_strong_frm;eauto .
eexists (Z.to_nat (Int.unsigned v'73)).
sep pauto.
sep cancel 6%nat 1%nat.
sep cancel 6%nat 1%nat.
rewrite Int.repr_unsigned.
rewrite <-H92.
rewrite updata_nth_lvallist.
eapply OSportattr_select_sn_strong with (n:= Z.to_nat (Int.unsigned i21)).
eauto.
fold port_attr_t in H103.
sep auto.
  Optimize Proof.
  Optimize Heap.

unfold APartID2Dom.
simpl in H22.
inverts H22.
sep pauto.
eapply new_array_type_vallist_match_compose_struct;eauto.
simpl.
rewrite leb_bytemax_true_intro;eauto.
rewrite leb_bytemax_true_intro;eauto.
rewrite leb_bytemax_true_intro;eauto.
rewrite leb_bytemax_true_intro;eauto.
rewrite leb_bytemax_true_intro;eauto.
simpl in Hnth.
rewrite Hnth.
splits;eauto.
clear.
int_auto.
rewrite app_length.
simpl.
rewrite app_length in H90.
simpl in H90.
apply H90.
split;eauto.
rewrite Int.repr_unsigned.
rewrite <-H92.
rewrite updata_nth_lvallist.
(* PortAttr_P *)
unfold PortAttr_P.
do 4 eexists.
intros.
rewrite <-Heqv60.
splits.
rewrite <-H53.
rewrite nth_vallist_get_idx.
eauto.
simpl.
eauto.
simpl.
eauto.
rewrite <-H92.
rewrite nth_vallist_get_idx.
eauto.
simpl;eauto.
simpl;eauto.
rewrite nth_val_imp_nth_val'_2;eauto.
rewrite H86.
clear -Hi26.
change PARTITION_NUM with 8 in *.
int_auto.
simpl;eauto.
simpl;splits;eauto.
(* end 进if *)
assert(Heqv60:(Z.to_nat (Int.unsigned v'60)) = (Z.to_nat (Int.unsigned
($ Z.of_nat (Z.to_nat (Int.unsigned v'60))))) ).
{
  rewrite Z2Nat.id;eauto.
  2:{ clear. int_auto. }
  rewrite Int.repr_unsigned;eauto.
}
 (* 不进if *)
 hoare forward.
 rewrite leb_bytemax_true_intro;eauto.
 rewrite leb_bytemax_true_intro;eauto.
 pure_auto.

hoare unfold.
eapply Int.eq_false in Hnif.
rewrite Hnif in H75.
simpl in H75.
tryfalse.
2:{
 destruct H75.
 sep split in H75.
 sep pauto.
 sep split in H75.
 sep pauto.
}
(* 处理不进if *)
hoare unfold.
clear H75.
assert(Hcond: ( (Int.unsigned v'73) + 1 = Int.unsigned x1 \/
  (Int.unsigned v'73) + 1 < Int.unsigned x1 ) ).
{
clear -H12.
int auto.
}
assert (Hv98_add: (v'73 +ᵢ $ 1) = ($ ((Int.unsigned v'73) + 1))).
{
 clear -Hcond.
 int auto.
}
destruct Hcond as [Hc1 | Hc2].
(* case 1 *)
hoare forward.
rewrite Hv98_add in H75.
assert(Hv'98: $ (Int.unsigned v'73 + 1) = x1).
{
  clear -Hc1.
  rewrite <-Int.repr_unsigned.
  rewrite Hc1.
  eauto.
}
rewrite <-Hv'98 in H75 at 1.
eapply adisj_intro.
right.
right.
sep auto.
3: simpl;eauto.
(* AKsDomains' *)
eapply AKsDomains'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned i22));eauto.
clear -H73.
unfold nat_of_Z.
unfold_part_defs.
int_auto.
unfold node_offt at 1.
sep normal.
do 3 eexists.
sep pauto.
sep cancel Aarray.
sep cancel 1%nat 1%nat.
2:{
  simpl.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  splits;eauto.
}
2:eauto.
(* APortTbl *)
eapply AportTbl'_select_sn_strong_frm with  (idx:= Z.to_nat (Int.unsigned v'60));eauto.
clear -Hport.
unfold nat_of_Z.
change PORT_NUMS with 64 in *.
int_auto.
unfold node_offt at 1.
sep normal.
do 2 eexists.
sep pauto.
sep cancel 6%nat 1%nat.
2:{
  split;eauto.
  simpl.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  splits;eauto.
}
(* AKsDomSchedule' *)
eapply AKsDomSchedule'_select_sn_strong_frm;eauto .
eexists (Z.to_nat (Int.unsigned v'73)).
sep pauto.
sep cancel 2%nat 1%nat.
sep cancel 2%nat 1%nat.
simpl in H22.
inverts H22.
eauto.
split;eauto.
(* ---------------------- *)
unfold PortAttr_P1.
intros.
rewrite <-Hc1 in H76.
destruct H76.
assert (Hcond: 0 <= Z.of_nat k < Int.unsigned v'73 \/ Z.of_nat k = Int.unsigned v'73).
{
   clear -H84.
   int_auto.
}
destruct Hcond as [Hcc1 | Hcc2].
assert(H1': V$ 1 = V$ 1 /\  0 <= Z.of_nat k < Int.unsigned v'73).
split;eauto.
eapply H47 in H1';eauto.
assert(k = Z.to_nat (Int.unsigned v'73)).
{
  rewrite <-Hcc2.
  rewrite nat_of_Z_of_nat;eauto.
}
rewrite H85.
do 7 eexists.
splits.
rewrite <-H53.
rewrite nth_vallist_get_idx;eauto.
simpl;eauto.
rewrite <-H62.
rewrite nth_vallist_get_idx;eauto.
simpl;eauto.
rewrite <-H77.
rewrite nth_error_middle ;eauto.
simpl;eauto.
clear -Hnif.
intro.
int_auto.
(* case 2 *)
hoare forward.
rewrite Hv98_add in H75.
eapply adisj_intro.
left.
sep auto.
  Optimize Proof.
  Optimize Heap.
4: simpl;eauto.
(* AKsDomains' *)
eapply AKsDomains'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned i22));eauto.
clear -H73.
unfold nat_of_Z.
unfold_part_defs.
int_auto.
unfold node_offt at 1.
sep normal.
do 3 eexists.
sep pauto.
sep cancel Aarray.
sep cancel 1%nat 1%nat.
2:{
  simpl.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  splits;eauto.
}
2:eauto.
(* APortTbl *)
eapply AportTbl'_select_sn_strong_frm with  (idx:= Z.to_nat (Int.unsigned v'60));eauto.
clear -Hport.
unfold nat_of_Z.
change PORT_NUMS with 64 in *.
int_auto.
unfold node_offt at 1.
sep normal.
do 2 eexists.
sep pauto.
sep cancel 6%nat 1%nat.
2:{
  split;eauto.
  simpl.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  rewrite leb_bytemax_true_intro;eauto.
  splits;eauto.
}
(* AKsDomSchedule' *)
eapply AKsDomSchedule'_select_sn_strong_frm;eauto .
eexists (Z.to_nat (Int.unsigned v'73)).
sep pauto.
sep cancel 2%nat 1%nat.
sep cancel 2%nat 1%nat.
simpl in H22.
inverts H22.
eauto.
split;eauto.
(* ---------------------- *)
unfold PortAttr_P1.
intros.
rewrite int_usign_eq in H76.
2:clear;int_auto.
2:{
  clear -Hc2 H49.
  unfold_part_defs.
  int_auto.
}
destruct H76.
assert (Hcond: 0 <= Z.of_nat k < Int.unsigned v'73 \/ Z.of_nat k = Int.unsigned v'73).
{
   clear -H84.
   int_auto.
}
destruct Hcond as [Hcc1 | Hcc2].
assert(H1': V$ 1 = V$ 1 /\  0 <= Z.of_nat k < Int.unsigned v'73).
split;eauto.
eapply H47 in H1';eauto.
assert(k = Z.to_nat (Int.unsigned v'73)).
{
  rewrite <-Hcc2.
  rewrite nat_of_Z_of_nat;eauto.
}
rewrite H85.
do 7 eexists.
splits.
rewrite <-H53.
rewrite nth_vallist_get_idx;eauto.
simpl;eauto.
rewrite <-H62.
rewrite nth_vallist_get_idx;eauto.
simpl;eauto.
rewrite <-H77.
rewrite nth_error_middle ;eauto.
simpl;eauto.
clear -Hnif.
intro.
int_auto.
clear -H49 Hc2.
rewrite int_usign_eq.
unfold_part_defs.
int_auto.
int_auto.
unfold_part_defs.
int_auto.

(* Afalse *)
eapply backward_rule1 with ( p :=
(EX j0 tf portattrvl portnumc a2 a3 a4 a5, 
EX a6 a7 a8 b2 curcfport,
LV ios_cap_defs.i @ Int32u |-> (Vint32 v'60) **
LV j @ Int32u |-> (Vint32 j0) **
LV flag @ Int32u |-> tf ** 
[|(Int.unsigned j0) < (Int.unsigned i9)|] **  
[|tf = (V$ 0)|] ** 
[| PortAttr_P (Z.to_nat (Int.unsigned v'60)) (Z.to_nat (Int.unsigned j0)) (Int.unsigned i9) tf l1 portattrvl v'49  |] **
[|portattrvl = update_nth_vallist (Z.to_nat (Int.unsigned a4)) v'63 ((V$ 1):: a3 :: a8 :: a5 :: a6 :: a7 :: nil)|] ** 
[|portnumc = Int.repr ((Int.unsigned v'64) + 1) |] ** 
[| nth_vallist (Z.to_nat (Int.unsigned v'60)) l1 = Some curcfport /\
   nth_val 0 curcfport =Some (Vint32 a4)
|] ** 
LV len @ long |-> Vint32 i9 **
APortTbl (v'36, Int.zero) l1 m3 **
AKsDomain v'43 **
AKsDomSchedule' v'59 **
AOSPortAttrTbl' portattrvl **
GV Port_num_cur @ char_t |-> (Vint32 portnumc) **
LV to1 @ char_t |-> Vint32 i1 **
LV to2 @ char_t |-> a2 **
LV to3 @ char_t |-> a3 **
LV to4 @ char_t |-> Vint32 a4 **
LV to5 @ char_t |-> a5 **
LV to6 @ char_t |-> a6 **
LV to7 @ char_t |-> a7 **
LV to8 @ char_t |-> a8 **
LV tox2 @ long |-> b2 ** 
APartID2Dom v'49 ** H41)
\\//
(EX j0 tf portnumc a2 a3 a4 a5, 
EX a6 a7 a8 b2,
LV ios_cap_defs.i @ Int32u |-> (Vint32 v'60) **
LV j @ Int32u |-> (Vint32 j0) **
LV flag @ Int32u |-> tf ** 
[|(Int.unsigned j0) = (Int.unsigned i9)|] **  
[|tf = (V$ 1)|] ** 
[| PortAttr_P1 (Int.unsigned v'60) (Int.unsigned j0) tf l1 v'43 v'59|] **
[|portnumc = v'64 |] ** 

LV len @ long |-> Vint32 i9 **
APortTbl (v'36, Int.zero) l1 m3 **
AKsDomain v'43 **
AKsDomSchedule' v'59 **
AOSPortAttrTbl' v'63 **
GV Port_num_cur @ char_t |-> (Vint32 portnumc) **
LV to1 @ char_t |-> Vint32 i1 **
LV to2 @ char_t |-> a2 **
LV to3 @ char_t |-> a3 **
LV to4 @ char_t |-> a4 **
LV to5 @ char_t |-> a5 **
LV to6 @ char_t |-> a6 **
LV to7 @ char_t |-> a7 **
LV to8 @ char_t |-> a8 **
LV tox2 @ long |-> b2 ** 
APartID2Dom v'49 ** H41)
). 
intros.
destruct H45.
destruct H45.
lets Hnew: aconj_intro H45 H46.
clear H45 H46.
eapply sep_aconj_r_aisfalse_to_astar in Hnew.
2 : {
  intros.
  sep destruct H45.
  sep split in H45.
  eapply bop_rv.
  sep get rv.
  destruct (Int.ltu x1 i9);simpl; auto.
  sep get rv. rewrite H47. eauto.
  assert(Hlt: Int.ltu x1 i9 = true).
  clear -H46.
  int auto.
  rewrite Hlt.
  subst x7.
  simpl.
  change (if Int.ltu Int.zero Int.one && Int.ltu Int.zero ($ 1)
  then Some (Vint32 Int.one)
  else Some (Vint32 Int.zero))  with (Some (Vint32 Int.one)).
  simpl; eauto.
  auto.
  Optimize Proof.
  Optimize Heap.
  simpl; eauto. }
  sep normal in Hnew.
  destruct Hnew. 
  sep destruct H45.
  sep split in H45.
  destruct H50; tryfalse.
  destruct H45.
lets Hnew: aconj_intro H45 H46.
clear  H45 H46.
eapply sep_aconj_r_aisfalse_to_astar in Hnew.
2 : {
  intros.
  sep destruct H45.
  sep split in H45.
  eapply bop_rv.
  sep get rv.
  destruct (Int.ltu x1 i9);simpl; auto.
  sep get rv. rewrite H47. eauto.
  assert(Hlt: Int.ltu x1 i9 = true).
  clear -H46.
  int auto.
  rewrite Hlt.
  subst x7.
  simpl.
  simpl; eauto.
  auto.
  simpl; eauto. }
  sep normal in Hnew.
  destruct Hnew.
  sep destruct H45.
  left.
  sep pauto.
  split;eauto.

lets Hnew: aconj_intro H45 H46.
clear H45 H46.
eapply sep_aconj_r_aisfalse_to_astar in Hnew.
2 : {
  intros.
  sep destruct H45.
  sep split in H45.
  eapply bop_rv.
  sep get rv.
  destruct (Int.ltu x1 i9);simpl; auto.
  sep get rv. rewrite H47. eauto.
  assert(Hlt: Int.ltu x1 i9 = false).
  clear -H46.
  int auto.
  rewrite Hlt.
  subst x7.
  simpl.
  change (if Int.ltu Int.zero Int.zero && Int.ltu Int.zero ($ 1)
   then Some (Vint32 Int.one)
   else Some (Vint32 Int.zero)) with (Some (Vint32 Int.zero)).
  simpl; eauto.
  auto.
  simpl; eauto. }
  sep normal in Hnew.
  destruct Hnew. 
  sep destruct H45.
  right.
  sep pauto.

(* i++ *)
assert(Hi6: (Int.unsigned i1) <= PORT_NUMS ).
do 2 destruct H12.
unfolds in H12.
simpl in H12. 
inverts H12. 
change PORT_NUMS with 64 in *.
auto with zarith.
assert(Hcond: ( (Int.unsigned v'60) + 1 = Int.unsigned i1 \/
  (Int.unsigned v'60) + 1 < Int.unsigned i1 ) ).
{
clear -H43.
int auto.
}
assert (Hsuc: (v'60 +ᵢ $ 1) = ($ ((Int.unsigned v'60) + 1))).
{
 clear -Hcond.
 int auto.
}
hoare forward.
hoare forward prim.
hoare unfold.
rename H50 into Hauxx1.
rename H51 into Hauxx2.
destruct Hcond as [Hc1 | Hc2].
(* case 1 *)
hoare forward.
assert(Hv'83: $ (Int.unsigned v'60 + 1) = i1).
{
  clear -Hc1.
  rewrite <-Int.repr_unsigned.
  rewrite Hc1.
  eauto.
}
rewrite <-Hv'83 in H41 at 1.
eapply adisj_intro.
right.
sep auto.
rewrite <-Hc1 in Hi6.
clear -Hpnum Hi6.
unfold_part_defs.
int_auto;int_auto.
destruct H47.
unfold Cfnoport_P.
intros.
rewrite <-Hc1 in H47.
assert (Hcond: 0 <= i1 < Int.unsigned v'60 \/ i1 = Int.unsigned v'60).
{
   clear -H47.
   int_auto.
}
destruct Hcond as [Hcc1 | Hcc2].
lets Hcc1': Hcc1.
eapply H44 in Hcc1.
destruct Hcc1.
do 6 destruct H49.
do 7 eexists.
intros.
destruct H49. eauto.
do 2 destruct H49.
destruct H51.
destruct H52.
destruct H53.
destruct H54.
destruct H55.
destruct H56.
do 4 destruct H46.
split;eauto.
clear -H45.
int_auto.
eexists x16,x17.
splits;eauto.
destruct H58 as (Hv48 &Hv49 &Hv50 &Hv51 &Hv52 &Hv53 &Hv54 &Hv55 &Hv56) .
unfold APortTbl in H41.
sep normal in H41.
destruct H41.
sep split in H41.
destruct H60 as (_ & _ & _ & Hidnop).
eapply nth_upd_neqrev_vll;eauto.
rewrite <-Hc1 in Hi6.
change PORT_NUMS with 64 in Hi6.
assert(Hgl3:  Int.unsigned v'60 < 64).
{
  clear -Hi6.
  int_auto.
}
unfolds in Hidnop.
lets Hneq: Hidnop (i1) (Int.unsigned v'60).
specializes Hneq.
clear -Hcc1' Hgl3.
unfold_part_defs.
int_auto.
clear - Hgl3.
unfold_part_defs.
int_auto.
clear -Hcc1'.
int_auto.
simpljoin.
unfold nat_of_Z.
eauto.
unfold nat_of_Z.
eauto.
unfolds.
eauto.
unfolds.
eauto.
rewrite Hauxx1 in H46.
inverts H46.
rewrite Hauxx2 in Hv49.
inverts Hv49.
intro.
eapply inline_bittblfunctions.z2n_int_eq in H46.
tryfalse.

do 4 destruct H46.
split;eauto.
clear -H45.
rewrite Z2Nat.id;int_auto.
do 7 eexists.
intros.
do 2 eexists.
destruct H49;eauto.
change PORT_NUMS with 64 in Hi6.
assert(H86: Int.unsigned v'60 + 1 < 64).
{
  clear -Hc2 Hi6.
  int_auto.
}
hoare forward.
eapply adisj_intro.
left.
rewrite Hsuc in *.
sep auto.
  Optimize Proof.
  Optimize Heap.
clear -Hpnum H43 Hi6.
int_auto;int_auto.
2:{
  rewrite int_usign_eq.
  2:clear;int_auto.
  2:{
    clear -H86.
    int_auto.
  }
eauto.
}
destruct H47.
unfold Cfnoport_P.
intros.
assert(Heq83: Int.unsigned ($ (Int.unsigned v'60 + 1)) = Int.unsigned v'60 + 1 ).
{
  rewrite int_usign_eq;eauto.
  clear;int_auto.
  clear -H86.
  int_auto.
}
rewrite Heq83 in H47.
assert (Hcond: 0 <= i19 < Int.unsigned v'60 \/ i19 = Int.unsigned v'60).
{
   clear -H47.
   int_auto.
}
destruct Hcond as [Hcc1 | Hcc2].
lets Hcc1': Hcc1.
eapply H44 in Hcc1.
destruct Hcc1.
do 6 destruct H49.
do 7 eexists.
intros.
destruct H49. eauto.
do 2 destruct H49.
destruct H51.
destruct H52.
destruct H53.
destruct H54.
destruct H55.
destruct H56.
do 4 destruct H46.
split;eauto.
clear -H45.
int_auto.
eexists x16,x17.
splits;eauto.
destruct H58 as (Hv48 &Hv49 &Hv50 &Hv51 &Hv52 &Hv53 &Hv54 &Hv55 &Hv56) .
unfold APortTbl in H41.
sep normal in H41.
destruct H41.
sep split in H41.
destruct H60 as (_ & _ & _ & Hidnop).
eapply nth_upd_neqrev_vll;eauto.
assert(Hgl3:  Int.unsigned v'60 < 64).
{
  clear -Hi6 H43.
  int_auto.
}
unfolds in Hidnop.
lets Hneq: Hidnop (i19) (Int.unsigned v'60).
specializes Hneq.
clear -Hcc1' Hgl3.
unfold_part_defs.
int_auto.
clear - Hgl3.
unfold_part_defs.
int_auto.
clear -Hcc1'.
int_auto.
simpljoin.
unfold nat_of_Z.
eauto.
unfold nat_of_Z.
eauto.
unfolds.
eauto.
unfolds.
eauto.
rewrite Hauxx1 in H46.
inverts H46.
rewrite Hauxx2 in Hv49.
inverts Hv49.
intro.
eapply inline_bittblfunctions.z2n_int_eq in H46.
tryfalse.

do 4 destruct H46.
split;eauto.
clear -H45.
rewrite Z2Nat.id;int_auto.
do 7 eexists.
intros.
do 2 eexists.
destruct H49;eauto.
(* 无变化 *)
destruct Hcond as [Hc1 | Hc2].
(* case 1 *)
hoare unfold.
hoare forward.
assert(Hv'83: $ (Int.unsigned v'60 + 1) = i1).
{
  clear -Hc1.
  rewrite <-Int.repr_unsigned.
  rewrite Hc1.
  eauto.
}
rewrite <-Hv'83 in H41 at 1.
eapply adisj_intro.
right.
sep auto.
rewrite <-Hc1 in Hi6.
clear -Hpnum Hi6.
unfold_part_defs.
int_auto;int_auto.
unfold Cfnoport_P.
intros.
assert (Hcond: 0 <= i1 < Int.unsigned v'60 \/ i1 = Int.unsigned v'60).
{
  rewrite <-Hc1 in H46.
   clear -H46.
   int_auto.
}
destruct Hcond as [Hcc1 | Hcc2].
lets Hcc1': Hcc1.
eapply H44 in Hcc1.
destruct Hcc1.
do 6 destruct H49.
do 7 eexists.
intros.
destruct H49. eauto.
do 2 destruct H49.
destruct H51 as (Hv42 & Hv43 & Hv44 & Hv45 & Hv46 & Hv47 & Hv48).

eexists x15,x16.
splits;eauto.
(* ///////////////////////// *)
unfold PortAttr_P1 in H47.
do 7 eexists.
intros.
destruct H49 as (Hv41 & Hv42 & Hv43 & Hv48 & Hv49 & Hv44 & Hv45).
assert(Hhy:V$ 1 = V$ 1 /\ 0 <= Z.of_nat j < Int.unsigned v'73).
{
  split.
  auto.
  rewrite H45.
  apply Hv41.
}
eapply H47 in Hhy.
destruct Hhy.
do 7 destruct H49.
destruct H50.
destruct H51.
destruct H52.
destruct H53.
destruct H54.
rewrite Hcc2 in Hv42.
rewrite H49 in Hv42.
inverts Hv42.
rewrite H51 in Hv48.
inverts Hv48.
rewrite H52 in Hv49.
inverts Hv49.
rewrite H50 in Hv43.
inverts Hv43.
rewrite H53 in Hv44.
inverts Hv44.
destruct Hv45.
rewrite H54 in H56.
inverts H56.
tryfalse.
(* case 1 *)
hoare unfold.
hoare forward.
assert(Heq83: Int.unsigned ($ (Int.unsigned v'60 + 1)) = Int.unsigned v'60 + 1 ).
{
  rewrite int_usign_eq;eauto.
  clear;int_auto.
  clear -Hc2 Hi6.
  change PORT_NUMS with 64 in *.
  int_auto.
}
rewrite Hsuc in *.
eapply adisj_intro.
left.
sep auto.
  Optimize Proof.
  Optimize Heap.
clear -Hc2 H43 Hpnum Hi6. 
unfold_part_defs.
int_auto;int_auto.
2:{
  rewrite Heq83 .
  apply Hc2.
}
rewrite Heq83.
unfold Cfnoport_P.
intros.
assert (Hcond: 0 <= i19 < Int.unsigned v'60 \/ i19 = Int.unsigned v'60).
{
   clear -H46.
   int_auto.
}
destruct Hcond as [Hcc1 | Hcc2].
lets Hcc1': Hcc1.
eapply H44 in Hcc1.
destruct Hcc1.
do 6 destruct H49.
do 7 eexists.
intros.
destruct H49. eauto.
do 2 destruct H49.
destruct H51 as (Hv42 & Hv43 & Hv44 & Hv45 & Hv46 & Hv47 & Hv48).
eexists x15,x16.
splits;eauto.
unfold PortAttr_P1 in H47.
do 7 eexists.
intros.
destruct H49 as (Hv41 & Hv42 & Hv43 & Hv48 & Hv49 & Hv44 & Hv45).
assert(Hhy:V$ 1 = V$ 1 /\ 0 <= Z.of_nat j < Int.unsigned v'73).
{
  split.
  auto.
  rewrite H45.
  apply Hv41.
}
eapply H47 in Hhy.
destruct Hhy.
do 7 destruct H49.
destruct H50 as (Hv47 & Hv50 & Hv51 & Hv52 & Hv53 & Hv54).
rewrite Hcc2 in Hv42.
rewrite H49 in Hv42.
inverts Hv42.
rewrite Hv47 in Hv43.
inverts Hv43.
rewrite Hv50 in Hv48.
inverts Hv48.
rewrite Hv51 in Hv49.
inverts Hv49.
rewrite Hv52 in Hv44.
inverts Hv44.
destruct Hv45.
rewrite H50 in Hv53.
inverts Hv53.
tryfalse.
(* Afalse *)
eapply backward_rule1 with ( p :=
(EX j0 tf portattrvl portnumc a2 a3 a4 a5, 
EX a6 a7 a8 b2,
LV ios_cap_defs.i @ Int32u |-> (Vint32 i1) **
LV j @ Int32u |-> (Vint32 j0) **
LV flag @ Int32u |-> tf ** 
[| Cfnoport_P (Int.unsigned i1) (Int.unsigned i9) l1 v'43 v'59 portattrvl v'49 |] **
[|(Int.unsigned portnumc) <= (Int.unsigned i1)|] ** 

LV len @ long |-> Vint32 i9 **
APortTbl (v'36, Int.zero) l1 m3 **
AKsDomain v'43 **
AKsDomSchedule' v'59 **
AOSPortAttrTbl' portattrvl **
GV Port_num_cur @ char_t |-> (Vint32 portnumc) **
LV to1 @ char_t |-> Vint32 i1 **
LV to2 @ char_t |-> a2 **
LV to3 @ char_t |-> a3 **
LV to4 @ char_t |-> a4 **
LV to5 @ char_t |-> a5 **
LV to6 @ char_t |-> a6 **
LV to7 @ char_t |-> a7 **
LV to8 @ char_t |-> a8 **
LV tox2 @ long |-> b2 ** 
APartID2Dom v'49 ** H41)
**  [| Vint32 Int.zero = Vint32 Int.zero \/ Vint32 Int.zero = Vnull |]
). 
intros.
destruct H43.
destruct H43.
lets Hnew: aconj_intro H43 H44.
clear H43 H44.
eapply sep_aconj_r_aisfalse_to_astar in Hnew.
2 : {
intros.
sep destruct H43.
sep get rv.
rewrite Hgi1;eauto.
sep split in H43.
assert (Hlt:Int.ltu x1 i1 = true).
{
clear -H44.
int auto.
}
rewrite Hlt.
eauto.
eauto.
}
sep normal in Hnew.
destruct Hnew. 
sep destruct H43.
sep split in H43.
destruct H47; tryfalse.

lets Hnew: aconj_intro H43 H44.
clear H43 H44.
eapply sep_aconj_r_aisfalse_to_astar in Hnew.
2 : {
intros.
sep destruct H43.
sep get rv.
pure_auto.
pure_auto.
}
sep pauto.
(* end while *)
hoare unfold.
clear H45.
hoare forward.
unfold_part_defs.
2:simpl;eauto.
2:{
  unfolds in H7.
  clear -H7 .
  induction v'35.
  simpl in H7.
  simpljoin.
  unfolds in H. 
  simpl in H. 
  inverts H. 
  eauto.
  simpl in H7.
  destruct a.
  do 2 destruct p.
  simpljoin.
  eapply IHv'35 in H0.
  eauto.
}
2:{
  unfolds in H7.
  clear -H7 .
  induction v'35.
  simpl in H7.
  simpljoin.
  unfolds in H. 
  simpl in H. 
  inverts H. 
  eauto.
  simpl in H7.
  destruct a.
  do 2 destruct p.
  simpljoin.
  eapply IHv'35 in H0.
  eauto.
}
2:eauto.
3:eauto.
3:eauto.
5:eauto.
4:{
  splits;eauto.
  rewrite <-H30.
  eapply nth_error_middle.
  simpl;eauto.
}
2: simpl;eauto.
2: simpl;eauto.
2:{
  go.
  rewrite leb_bytemax_true_intro;eauto.
  eapply leb_bytemax_true_elim in Hgi1.
  clear -Hgi1 H44.
  int_auto.
}
change (nth_val' 0
(Vint32 i15 :: Vint32 i14 :: Vint32 i13 :: Vint32 i12 :: nil)
:: nth_val' 1
   (Vint32 i15 :: Vint32 i14 :: Vint32 i13 :: Vint32 i12 :: nil)
 :: nth_val' 2
      (Vint32 i15 :: Vint32 i14 :: Vint32 i13 :: Vint32 i12 :: nil)
    :: nil)
    with (Vint32 i15 :: Vint32 i14 :: Vint32 i13 :: nil).
sep cancel p_local.
instantiate (1:= (u, u0, u1, u2, u3, u4, m, a, m0, m1, u5, m2, m3, u6)).
unfold AucosConf.
unfold BOOT_DATA_ADDRESS.
sep pauto.
2:{
  unfolds;splits ;eauto.
}
unfolds in Heqboot_b.
subst v'36.
unfold AAllArea.
unfold node.
sep pauto.
2:simpl;eauto.
2:{
  split;eauto.
  simpl;eauto.
  rewrite Hgi4 ,Hgi3, Hgi2 , Hgi1,Hgi.
  splits;eauto.
}
unfold APartArea'.
unfold node_offt.
unfold AKsDSchdlen.
unfold ACPUs.
unfold node.
sep pauto.
sep cancel 3%nat 1%nat.
eapply Acpus'_select_sn_strong_frm with (idx:=Z.to_nat (Int.unsigned v'24));eauto. 
clear -H23.
change CORENUM with 8.
unfold nat_of_Z.
int_auto.
sep pauto.
sep cancel 2%nat 1%nat.
sep cancel 1%nat 1%nat.
sep cancel 2%nat 1%nat.
unfold node_offt.
sep auto.
  Optimize Proof.
  Optimize Heap.
split;eauto.
simpl;eauto.
eauto.
eauto.
eauto.
clear -H27.
unfolds in H27.
simpljoin.
unfolds in H;simpl in H;inverts H. 
unfold_part_defs.
rewrite inline_bittblfunctions.mutexpost_intlemma1;eauto.
int_auto.
simpl.
clear -H27.
unfolds in H27.
simpljoin.
unfolds in H;simpl in H;inverts H. 
unfold_part_defs.
assert(H:Int.unsigned x <= 255).
int_auto.
eapply leb_bytemax_true_intro in H.
rewrite H;eauto.
split;eauto.
simpl;splits;eauto.
eauto.
split;eauto.
simpl;splits;eauto.
Unshelve.
all : auto.
destruct x6;tryfalse.
exact d.
destruct l1;tryfalse.
exact c.
exact 0%nat.
exact 0%nat.
Qed.

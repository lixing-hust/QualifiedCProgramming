Require Import sound_include.
Require Import Lia.
Require Import symbolic_lemmas.
Require Import math_sol.
Require Import join_lib.
Require Import memory_prop.
Require Import perm_map_lemmas_part1.
Require Import perm_map_lemmas_part3.
Require Import int_auto.

Lemma ptomvallist_unique:
forall vl l b m1 m2,
 ptomvallist l b vl m1 ->
 ptomvallist l b vl m2 ->
 m1 = m2.
Proof.
induction vl.
simpl in *; intros. subst. auto.
simpl.
intros.
destruct l.
simpljoin.
assert(Heq: x = x1).
unfold ptomval in *.
subst. auto.
assert (x0 = x2).
eapply IHvl; eauto.
subst.
eapply map_join_merge' in H, H0; subst.
auto.
Qed.


Lemma mapstoval_unique:
forall l t b v m1 m2,
 mapstoval l t b v m1 ->
 mapstoval l t b v m2 ->
 m1 = m2.
Proof.
unfold mapstoval.
intros.
simpljoin.
lets Heq: ptomvallist_unique H2 H1; auto.
Qed.

Lemma ptomval_minus_eq_emp:
forall v1 v2 b l m1 m2,
 ptomval l b v1 m1 ->
 ptomval l b v2 m2 ->
 minus m1 m2 = emp.
Proof.
 unfold ptomval.
 intros.
 subst.
 unfold minus,sig,emp.
simpl.
unfold HalfPermMap.minus,HalfPermMap.sig, HalfPermMap.emp.
eapply HalfPermMap.extensionality.
intros.
unfold HalfPermMap.set, HalfPermMap.rminus.
destruct (HalfPermMap.dec_A x l) eqn: eq1; auto.
destruct b; auto.
Qed.

Lemma ptomval_minus_eq_emp':
forall v1 v2 b l m1 m2,
 ptomval l b v1 m1 ->
 ptomval l b v2 m2 ->
 minus m1 m2 = emp /\ 
(forall x, (m1 x = Some (b, v1) /\ m2 x = Some (b, v2)) \/
           (m1 x = None /\ m2 x = None)).
Proof.
intros.
split.
eapply ptomval_minus_eq_emp; eauto.
unfold ptomval in *.
substs.
intros.
unfold sig in *.
simpl in *.
unfold HalfPermMap.sig, HalfPermMap.set, HalfPermMap.emp in *.
destruct (HalfPermMap.dec_A x l);
tryfalse; eauto.
Qed.

Lemma ptomvallist_minus_eq_emp:
forall vl1 vl2 l m1 m2,
 ptomvallist l true vl1 m1 ->
 ptomvallist l true vl2 m2 ->
 length vl1 = length vl2 ->
 minus m1 m2 = emp.
Proof.
induction vl1.
simpl in *; intros. subst. auto.
induction vl2.
simpl.
intros.
tryfalse.
simpl.
intros.
destruct l.
simpljoin.
eapply Nat.succ_inj in H1.
lets Heq: IHvl1 H5 H3 H1.
lets Heq2: ptomval_minus_eq_emp H4 H2.
unfold ptomval in *.
simpljoin.
eapply join_merge in H,H0; subst.
unfold merge,minus,sig, emp in *.
simpl in *.
unfold HalfPermMap.merge,HalfPermMap.minus,HalfPermMap.sig in *.
eapply HalfPermMap.extensionality.
intros.
eapply FunctionalExtensionality.equal_f in Heq,Heq2.
instantiate (1:= x) in Heq.
instantiate (1:= x) in Heq2.
unfold HalfPermMap.set, HalfPermMap.rjoin, HalfPermMap.rminus, HalfPermMap.emp in *.
destruct (HalfPermMap.dec_A x (b, o)) eqn: eq1;
try destruct (x0 x) eqn: eq2;
try destruct (x2 x) eqn: eq3;
try destruct (b) eqn: eq4;
try destruct (b1) eqn: eq5;
try destruct (b2) eqn: eq6;
try destruct (b3) eqn: eq7;
try destruct (b4) eqn: eq8;
try destruct (HalfPermMap.dec_C a c0) eqn: eq9;
try destruct (HalfPermMap.dec_C a0 c) eqn: eq10;
try destruct (HalfPermMap.dec_C a a0) eqn: eq11;
subst; tryfalse; auto.
Qed.

Lemma ptomvallist_minus_eq_emp':
forall vl1 vl2 l m1 m2,
 ptomvallist l true vl1 m1 ->
 ptomvallist l true vl2 m2 ->
 length vl1 = length vl2 ->
 minus m1 m2 = emp /\
(forall x, (exists v1 v2, (m1 x = Some (true, v1) /\ m2 x = Some (true, v2))) \/
           (m1 x = None /\ m2 x = None)).
Proof.
induction vl1.
simpl in *; intros. subst.
eapply eq_sym in H1.
eapply length_zero_iff_nil in H1.
subst.
simpl in *. subst. eauto.
induction vl2.
intros.
simpl in *. tryfalse.
intros.
destruct l.
simpl in *.
simpljoin.
eapply Nat.succ_inj in H1.
lets Heq: IHvl1 H5 H3 H1.
lets Heq2: ptomval_minus_eq_emp H4 H2.
destruct Heq as (Heq & Hf1).
unfold ptomval in *.
simpljoin.
eapply join_merge in H,H0; subst.
split.
unfold merge,minus,sig, emp in *.
simpl in *.
unfold HalfPermMap.merge,HalfPermMap.minus,HalfPermMap.sig in *.
eapply HalfPermMap.extensionality.
intros.
eapply FunctionalExtensionality.equal_f in Heq,Heq2.
instantiate (1:= x) in Heq.
instantiate (1:= x) in Heq2.
unfold HalfPermMap.set, HalfPermMap.rjoin, HalfPermMap.rminus, HalfPermMap.emp in *.
destruct (HalfPermMap.dec_A x (b, o)) eqn: eq1;
try destruct (x0 x) eqn: eq2;
try destruct (x2 x) eqn: eq3;
try destruct (b) eqn: eq4;
try destruct (b1) eqn: eq5;
try destruct (b2) eqn: eq6;
try destruct (b3) eqn: eq7;
try destruct (b4) eqn: eq8;
try destruct (HalfPermMap.dec_C a c0) eqn: eq9;
try destruct (HalfPermMap.dec_C a0 c) eqn: eq10;
try destruct (HalfPermMap.dec_C a a0) eqn: eq11;
subst; tryfalse; auto.
(*subgoal2*)
intros.
clear -Heq Hf1 Heq2.
specialize Hf1 with (x:= x).
unfold sig, minus, emp, merge in *.
simpl in *.
eapply FunctionalExtensionality.equal_f in Heq,Heq2.
instantiate (1:= x) in Heq.
instantiate (1:= x) in Heq2.
unfold HalfPermMap.minus, HalfPermMap.sig, HalfPermMap.merge in *.
unfold HalfPermMap.rminus, HalfPermMap.set, HalfPermMap.rjoin,HalfPermMap.emp in *.
try destruct (HalfPermMap.dec_A x (b, o)) eqn: eq1;
try destruct (x0 x) eqn: eq2;
try destruct (x2 x) eqn: eq3;
try destruct (b0) eqn: eq4;
try destruct (b1) eqn: eq5;
try destruct (b2) eqn: eq6;
try destruct (b3) eqn: eq7;
subst; tryfalse; eauto.
Qed.

Lemma mapstoval_minus_eq_emp:
forall l t v1 v2 m1 m2,
 mapstoval l t true v1 m1 ->
 mapstoval l t true v2 m2 ->
 length (encode_val t v1) = length (encode_val t v2) ->
 minus m1 m2 = emp.
Proof.
unfold mapstoval.
intros.
simpljoin.
eapply ptomvallist_minus_eq_emp; eauto.
Qed.

Lemma mapstoval_minus_eq_emp_alt:
forall l t v1 v2 m1 m2,
 mapstoval l t true v1 m1 ->
 mapstoval l t true v2 m2 ->
 length (encode_val t v1) = length (encode_val t v2) ->
 minus m1 m2 = emp /\ 
 (forall x, (exists v1 v2, m1 x = Some (true, v1) /\ m2 x = Some (true, v2)) \/
           (m1 x = None /\ m2 x = None)).
Proof.
intros.
unfold mapstoval in *.
simpljoin.
eapply ptomvallist_minus_eq_emp'; eauto.
Qed.

Lemma minus_imp_disjoint:
forall M M': mem,
minus M M' = M -> disjoint M M'.
Proof.
intros.
unfold minus, disjoint in *.
unfold join.
simpl in *.
unfold HalfPermMap.minus, HalfPermMap.join in *.
exists (HalfPermMap.merge M M').
unfold HalfPermMap.disjoint, HalfPermMap.merge.
unfold HalfPermMap.rminus, HalfPermMap.rjoin in *.
split; auto.
intros.
eapply FunctionalExtensionality.equal_f in H.
instantiate (1:= x) in H.
destruct (M x) eqn: eq1; try destruct b;
destruct (M' x) eqn: eq2; try destruct b0;
try destruct b eqn: Heq1;
try destruct b0 eqn: Heq2;
try destruct (HalfPermMap.dec_C c c0) eqn: Hc0;
tryfalse; auto.
Qed.
 

Lemma minus_merge_left:
forall M M1 M2: mem,
minus M1 M = M1 ->
minus M2 M = M2 ->
minus (merge M1 M2) M = (merge M1 M2).
Proof.
intros.
unfold minus, merge in *.
simpl in *.
unfold HalfPermMap.minus, HalfPermMap.merge in *.
eapply HalfPermMap.extensionality.
intros.
eapply FunctionalExtensionality.equal_f in H,H0.
instantiate (1:= x) in H.
instantiate (1:= x) in H0.
unfold HalfPermMap.rminus, HalfPermMap.rjoin in *.
destruct (M x) eqn: eq1; try destruct b;
destruct (M1 x) eqn: eq2; try destruct b0;
destruct (M2 x) eqn: eq3; try destruct b1;
try destruct b eqn: Heq1;
try destruct b0 eqn: Heq2;
try destruct b1 eqn: Heq3;
try destruct b2 eqn: Heq4;
tryfalse; auto;
try solve [
try destruct (HalfPermMap.dec_C c c0) eqn: Hc0;
substs;
tryfalse; auto].
Qed.


Lemma minus_same_emp:
forall M m1 (m2:mem),
(forall x, (exists v1 v2, m1 x = Some (true, v1) /\ m2 x = Some (true, v2)) \/
           (m1 x = None /\ m2 x = None)) ->
Maps.sub m2 M ->
Maps.sub m1 M ->
minus m1 m2 = emp ->  
minus M m1 = minus M m2.
Proof.
intros.
unfold minus, empenv, Maps.sub in *.
simpl in *. 
simpljoin.
rename x0 into x'.
unfold join in *.
simpl in *. 
unfold HalfPermMap.minus, HalfPermMap.emp, HalfPermMap.join in *.
unfold HalfPermMap.rminus, HalfPermMap.disjoint, HalfPermMap.merge, HalfPermMap.rjoin in *.
simpljoin.
eapply HalfPermMap.extensionality.
intros.
eapply FunctionalExtensionality.equal_f in H3.
eapply FunctionalExtensionality.equal_f in H2.
instantiate (1:= x0) in H3.
instantiate (1:= x0) in H2.
specialize H0 with (x:= x0).
specialize H1 with (x:= x0).
specialize H with (x:= x0).
try destruct (m1 x0) eqn: eq1;
try destruct (x x0) eqn: eq2;
try destruct (x' x0) eqn: eq2';
try destruct (m2 x0) eqn: eq3;
try destruct p eqn: eq4;
try destruct p0 eqn: eq5;
try destruct b eqn: eq6;
try destruct b0 eqn: eq7;
try destruct b1 eqn: eq8;
try destruct b2 eqn: eq9;
try destruct b3 eqn: eq9';
try destruct b4 eqn: eq9'';
try destruct (HalfPermMap.dec_C c c0) eqn: eq11;
try destruct (HalfPermMap.dec_C c c) eqn: eq12;
try destruct (HalfPermMap.dec_C c c1) eqn:eq10;
try destruct (HalfPermMap.dec_C v1 c) eqn: eq13;
try destruct (HalfPermMap.dec_C v1 c1) eqn: eq14;
subst;
try rewrite eq10 in *;
try rewrite eq11 in *;
tryfalse; auto;
try solve [destruct H as [(v1 & v2 & Hf1 & Hf2) | (Hf1 & Hf2)];
           tryfalse].
Qed.

Lemma minus_same_emp':
forall M m1 (m2:mem),
(forall x, (exists v1 v2, m1 x = Some (true, v1) /\ m2 x = Some (true, v2)) \/
           (m1 x = None /\ m2 x = None)) ->
minus m1 m2 = emp ->  
minus M m1 = minus M m2.
Proof.
intros.
unfold minus, empenv in *.
simpl in *.
unfold HalfPermMap.minus, HalfPermMap.emp in *.
unfold HalfPermMap.rminus in *.
eapply HalfPermMap.extensionality.
intros.
eapply FunctionalExtensionality.equal_f in H0.
instantiate (1:= x) in H0.
specialize H with (x:= x).
try destruct (M x) eqn: eq1;
try destruct (m1 x) eqn: eq2;
try destruct (m2 x) eqn: eq3;
try destruct p eqn: eq4;
try destruct p0 eqn: eq5;
try destruct b eqn: eq6;
try destruct b0 eqn: eq7;
try destruct b1 eqn: eq8;
try destruct b2 eqn: eq9;
try destruct (HalfPermMap.dec_C c c1) eqn:eq10;
try destruct (HalfPermMap.dec_C c c0) eqn:eq11;
try destruct (HalfPermMap.dec_C c0 c1) eqn:eq12;
try destruct (HalfPermMap.dec_C c1 c0) eqn:eq13;
subst;
tryfalse; auto;
try solve [destruct H as [(v1 & v2 & Hf1 & Hf2) | (Hf1 & Hf2)];
           tryfalse].
Qed.

Lemma clearl_left_eq:
forall i v,
(0 <= i <= 31)%nat ->
clearl v i = Int.zero_ext (32 - (Z.of_nat i)) v.
Proof.
unfold clearl.
induction i; introv Hrgn; intros.
change (Int.repr (Z.of_nat 0)) with Int.zero.
rewrite Int.shl_zero.
rewrite two_power_nat_O.
rewrite Z.div_1_r.
change (32 - Z.of_nat 0) with 32.
rewrite Int.zero_ext_above.
rewrite Int.repr_unsigned; auto.
change Int.zwordsize with 32.
auto with zarith.
change 32 with Int.zwordsize.
lets Hi: Nat.lt_ge_cases i 31%nat.
destruct Hi as [Hok | Hout].
rewrite Int.zero_ext_shru_shl; change Int.zwordsize with 32.
2:{ auto with zarith. }
assert (Heq: (32 - (32 - Z.of_nat (S i))) = (Z.of_nat (S i))).
{ auto with zarith. }
rewrite Heq.
assert(Heq1: two_power_nat (S i) = two_p (Int.unsigned (Int.repr(Z.of_nat (S i))))).
{ clear Hrgn. mauto. }
rewrite Heq1.
rewrite <- Int.shru_div_two_p.
auto.
false.
auto with zarith.
Qed.


Lemma clearl_left_range:
forall i v,
(0 < i <= 31)%nat ->
(0 <= Int.unsigned (clearl v i) < two_power_nat (32 - i))%Z.
Proof.
intros.
rewrite clearl_left_eq; eauto.
assert(Heq: two_power_nat (32 - i) = two_p (32 - (Z.of_nat i))).
{ mauto. }
rewrite Heq.
eapply Int.zero_ext_range.
change Int.zwordsize with 32.
auto with zarith.
auto with zarith.
Qed.

Lemma get_mpax_smsl_sr:
forall mpaxl,
(Int.unsigned (get_mpax mpaxl smsl_sr) <= Byte.max_unsigned)%Z.
Proof.
intros. 
simpl.
unfold get_part.
unfold clearr.
lets Hr: clearl_left_range 26%nat mpaxl.
destruct Hr; auto with zarith.
change (two_power_nat (32 - 26)) with 64 in *.
change Byte.max_unsigned with 255.
unfold Int.shru.
change (Int.unsigned (Int.repr (Z.of_nat 5))) with 5.
rewrite Int.unsigned_repr;
rewrite Int.Zshiftr_div_two_p; auto with zarith;
change (two_p 5) with 32.
int auto.
eapply Z.div_le_upper_bound; auto with zarith.
auto with zarith.
split.
eapply Z.div_pos; auto with zarith.
eapply Z.div_le_upper_bound; auto with zarith.
auto with zarith.
int auto.
Qed.

Lemma get_mpax_perm:
forall id mpax,
~(id = smsl_raddr \/ id = smsh_baddr \/ id = smsh_segsize
  \/ id = sesl_raddr \/ id = sesh_baddr \/ id = sesh_segsize
  \/ id = xmc_raddr \/ id = xmc_baddr \/ id = xmc_segsize) ->
(Int.unsigned (get_mpax mpax id) <= Byte.max_unsigned)%Z.
Proof.
destruct id; intros;
try solve [ false; eapply H; tauto];
simpl; unfold get_part, clearr;
try solve [
lets Hr1: clearl_left_range 26%nat mpax;
lets Hr2: clearl_left_range 27%nat mpax;
lets Hr3: clearl_left_range 28%nat mpax;
lets Hr4: clearl_left_range 29%nat mpax;
lets Hr5: clearl_left_range 30%nat mpax;
lets Hr6: clearl_left_range 31%nat mpax;
destruct Hr1; destruct Hr2; destruct Hr3;
destruct Hr4; destruct Hr5; destruct Hr6;
auto with zarith;
try change (two_power_nat (32 - 26)) with 64 in *;
try change (two_power_nat (32 - 27)) with 32 in *;
try change (two_power_nat (32 - 28)) with 16 in *;
try change (two_power_nat (32 - 29)) with 8 in *;
try change (two_power_nat (32 - 30)) with 4 in *;
try change (two_power_nat (32 - 31)) with 2 in *;
change Byte.max_unsigned with 255;
unfold Int.shru;
try change (Int.unsigned (Int.repr (Z.of_nat 5))) with 5;
try change (Int.unsigned (Int.repr (Z.of_nat 4))) with 4;
try change (Int.unsigned (Int.repr (Z.of_nat 3))) with 3;
try change (Int.unsigned (Int.repr (Z.of_nat 2))) with 2;
try change (Int.unsigned (Int.repr (Z.of_nat 1))) with 1;
try change (Int.unsigned (Int.repr (Z.of_nat 0))) with 0;
rewrite Int.unsigned_repr;
rewrite Int.Zshiftr_div_two_p; auto with zarith;
try change (two_p 5) with 32;
try change (two_p 4) with 16;
try change (two_p 3) with 8;
try change (two_p 2) with 4;
try change (two_p 1) with 2;
try change (two_p 0) with 1;
auto with zarith;
try solve [
try split;
try change Int.max_unsigned with 4294967295;
try eapply Z.div_pos;
try eapply Z.div_le_upper_bound; auto with zarith]].
Qed.

Lemma true_if_else_true: 
  forall x, x =true -> (if x then true else false) = true.
Proof.
  intros.
  rewrite H.
  auto.
Qed.

Lemma get_mpax_struct_smsmpaxl_match:
forall mpaxl,
struct_type_vallist_match MSMC_SMSMPAXL
  (get_mpax_struct mpaxl 
      (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: 
       smsl_ur :: smsl_uw :: smsl_ux :: nil)).
Proof.
intros.
unfold get_mpax_struct.
unfold struct_type_vallist_match.
unfold struct_type_vallist_match'.
unfold rule_type_val_match.
splits; auto;
eapply true_if_else_true;
eapply Zle_imp_le_bool;
eapply get_mpax_perm;
introv H;
repeat (try destruct H; tryfalse).
Qed.

Lemma get_mpax_struct_sesmpaxl_match:
forall mpaxl,
struct_type_vallist_match MSMC_SESMPAXL
  (get_mpax_struct mpaxl 
      (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: 
       sesl_ur :: sesl_uw :: sesl_ux :: nil)).
Proof.
intros.
unfold get_mpax_struct.
unfold struct_type_vallist_match.
unfold struct_type_vallist_match'.
unfold rule_type_val_match.
splits; auto;
eapply true_if_else_true;
eapply Zle_imp_le_bool;
eapply get_mpax_perm;
introv H;
repeat (try destruct H; tryfalse).
Qed.

Lemma get_mpax_struct_xmpaxl_match:
forall mpaxl,
struct_type_vallist_match XMC_XMPAXL
  (get_mpax_struct mpaxl 
      (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: 
       xmc_ur :: xmc_uw :: xmc_ux :: nil)).
Proof.
intros.
unfold get_mpax_struct.
unfold struct_type_vallist_match.
unfold struct_type_vallist_match'.
unfold rule_type_val_match.
splits; auto;
eapply true_if_else_true;
eapply Zle_imp_le_bool;
eapply get_mpax_perm;
introv H;
repeat (try destruct H; tryfalse).
Qed.


Lemma get_join_none:
forall o o1 o2 id v,
 join o o1 o2 ->
OSAbstMod.get o id = Some v ->
 OSAbstMod.get o1 id = None.
Proof.
unfold join.
simpl.
unfold OSAbstMod.join.
intros.
specialize H with (a:= id).
rewrite H0 in *.
destruct (OSAbstMod.get o1 id) eqn: eq1; auto.
tryfalse.
Qed.

Lemma disjoint_merge_imp:
forall Mf Ms x: mem,
disjoint Mf x ->
disjoint Ms x ->
disjoint Ms Mf ->
(forall a b v, x a = Some (b, v) -> b = true)->
disjoint (merge Mf Ms) x.
Proof.
unfold disjoint, merge,join.
simpl.
intros.
simpljoin.
exists ( HalfPermMap.merge (HalfPermMap.merge Mf Ms) x).
unfold HalfPermMap.join, HalfPermMap.merge in *.
unfold HalfPermMap.disjoint, HalfPermMap.rjoin in *.
simpljoin.
splits; eauto.
intros.
specialize H with (x:= x0).
specialize H0 with (x:= x0).
specialize H1 with (x:= x0).
specialize H2 with (a:= x0).
try destruct (Mf x0) eqn: eq1;
try destruct (Ms x0) eqn: eq2;
try destruct (x x0) eqn: eq3;
try destruct b eqn: eq6;
try destruct b0 eqn: eq7;
try destruct b1 eqn: eq8;
try destruct b2 eqn: eq9;
try destruct b3 eqn: eq10;
try destruct b4 eqn: eq12;
try destruct (HalfPermMap.dec_C c c0) eqn:eq11;
subst;
tryfalse; auto.
specialize (H2 _ _ (eq_refl _)).
tryfalse.
Qed.

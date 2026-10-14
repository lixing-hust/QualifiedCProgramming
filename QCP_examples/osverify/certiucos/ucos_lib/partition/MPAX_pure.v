Require Import include_frm.
Require Import os_code_defs.
Require Import code_notations.
Require Import csl_mpax_pure.
Require Import int_auto.
Require Import Integers.
Require Import math_auto.
Require Import os_inv.
Require Import pure_lib.
Require Import inline_bittblfunctions.
Require Import ucos_common.

Open Scope Z_scope.
Open Scope int_scope.
Open Scope code_scope.
Local Open Scope list_scope.

Lemma get_mpax_smsh_segsize:
forall v,
(Int.unsigned (get_mpax v smsh_segsize) <= 4096 (* Byte.max_unsigned *))%Z.
Proof.
intros.
simpl.
unfold get_part.
unfold clearr.
lets Hr: clearl_left_range 20%nat v.
destruct Hr; auto with zarith.
change (two_power_nat (32 - 20)) with 4096 in *.
(* change Byte.max_unsigned with 255. *)
unfold Int.shru.
change (Int.unsigned (Int.repr (Z.of_nat 0))) with 0.
rewrite Int.unsigned_repr;
rewrite Int.Zshiftr_div_two_p; auto with zarith;
change (two_p 0) with 1.
eapply Z.div_le_upper_bound; auto with zarith.
split.
eapply Z.div_pos; auto with zarith.
eapply Z.div_le_upper_bound; auto with zarith.
int auto.
Qed.

Lemma get_mpax_segsize:
forall id mpax,
(id = smsh_segsize \/ id = sesh_segsize  \/ id = xmc_segsize) ->
(Int.unsigned (get_mpax mpax id) <= 4096 (* Byte.max_unsigned *))%Z.
Proof.
intros;
destruct H as [ | [ | ]]; subst;
simpl; unfold get_part, clearr;
try solve [
lets Hr1: clearl_left_range 20%nat mpax;
destruct Hr1;
auto with zarith;
try change (two_power_nat (32 - 20)) with 4096 in *;
change Byte.max_unsigned with 255;
unfold Int.shru;
try change (Int.unsigned (Int.repr (Z.of_nat 0))) with 0;
rewrite Int.unsigned_repr;
rewrite Int.Zshiftr_div_two_p; auto with zarith;
try change (two_p 0) with 1;
auto with zarith;
try solve [
try split;
try change Int.max_unsigned with 4294967295;
try eapply Z.div_pos;
try eapply Z.div_le_upper_bound; auto with zarith]].
Qed.

Lemma get_mpax_struct_smsmpaxh_match:
forall v,
Int.unsigned (get_mpax v smsh_segsize) <= Byte.max_unsigned ->
struct_type_vallist_match MSMC_SMSMPAXH
  (get_mpax_struct v (smsh_baddr :: smsh_segsize :: nil)).
Proof.
intros.
unfold get_mpax_struct.
unfold struct_type_vallist_match.
unfold struct_type_vallist_match'.
unfold rule_type_val_match.
splits; auto;
eapply true_if_else_true;
eapply Zle_imp_le_bool.
(* eapply get_mpax_segsize; *) eauto.
Qed.

Lemma get_mpax_struct_sesmpaxh_match:
forall v,
Int.unsigned (get_mpax v sesh_segsize) <= Byte.max_unsigned ->
struct_type_vallist_match MSMC_SESMPAXH
  (get_mpax_struct v (sesh_baddr :: sesh_segsize :: nil)).
Proof.
intros.
unfold get_mpax_struct.
unfold struct_type_vallist_match.
unfold struct_type_vallist_match'.
unfold rule_type_val_match.
splits; auto;
eapply true_if_else_true;
eapply Zle_imp_le_bool.
(* eapply get_mpax_segsize; *) eauto.
Qed.

Lemma get_mpax_struct_xmpaxh_match:
forall v,
Int.unsigned (get_mpax v xmc_segsize) <= Byte.max_unsigned ->
struct_type_vallist_match XMC_XMPAXH
  (get_mpax_struct v (xmc_baddr :: xmc_segsize :: nil)).
Proof.
intros.
unfold get_mpax_struct.
unfold struct_type_vallist_match.
unfold struct_type_vallist_match'.
unfold rule_type_val_match.
splits; auto;
eapply true_if_else_true;
eapply Zle_imp_le_bool.
(* eapply get_mpax_segsize; *) eauto.
Qed.

Lemma clearr_right_eq:
forall i v,
(0 <= i <= 31)%nat ->
clearr v i = Int.repr (Int.unsigned v / (two_p (Z.of_nat i))).
Proof.
unfold clearr.
intros.
int auto.
rewrite Int.shru_div_two_p.
rewrite Int.unsigned_repr.
auto.
int auto.
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

Lemma get_part_eq:
forall x l r,
 (0 <= Nat.add l r <= 31)%nat ->
 get_part x l r = Int.repr (Int.unsigned (Int.zero_ext (32 - Z.of_nat l) x) / (two_p (Z.of_nat r))).
Proof.
unfold get_part.
intros.
rewrite clearr_right_eq.
rewrite clearl_left_eq.
auto.
auto with zarith.
auto with zarith.
Qed.

Lemma bits_low:
  forall x i, i < 0 -> Int.testbit x i = false.
Proof.
  intros. apply Z.testbit_neg_r; auto.
Qed.

Lemma set_part_testbit:
forall n l r x i,
(0 <= n <= 31) ->
(0 <= l + r <= 31)%nat ->
(forall d, ((31 - Z.of_nat (l + r)) < d <= 31) -> Int.testbit i d = false) ->
((Z.of_nat (31 - l) < n <= 31) \/ (0 <= n < Z.of_nat r)-> Int.testbit (set_part x l r i) n = Int.testbit x n)
/\
((Z.of_nat r <= n <= Z.of_nat (31 -l)) -> Int.testbit (set_part x l r i) n = Int.testbit i (n - Z.of_nat r))
.
Proof.
introv Hn Hlr Hi.
split.
introv Hc.
destruct Hc as [Hhigh | Hlow].
unfold set_part.
unfold clear_part.
unfold get_part.
rewrite clearl_left_eq.
unfold clearr.
rewrite Int.bits_or.
rewrite Int.bits_xor.
rewrite Int.bits_shl.
rewrite Int.bits_shl.
rewrite Int.bits_shru.
rewrite Int.unsigned_repr.
destruct (zlt n (Z.of_nat r)) eqn: eq1.
rewrite xorb_false_r.
rewrite orb_false_r; auto.
unfold zlt in eq1.
destruct Z_lt_dec; tryfalse.
inverts eq1.

unfold zlt.
destruct Z_lt_dec.
rewrite <- Z.add_sub_swap.
rewrite Z.add_simpl_r.

2: { 
    rewrite <- Z.add_sub_swap in n1.
    rewrite Z.add_simpl_r in n1.
    unfold Int.zwordsize in *.
    unfold Int.wordsize in *.
    unfold Wordsize_32.wordsize in *.
    int auto.
   }

rewrite Int.bits_zero_ext.
unfold zlt.
destruct Z_lt_dec.
false.
auto with zarith.
rewrite xorb_false_r.
rewrite Hi.
rewrite orb_false_r.
auto.
(* left. *)
split.
auto with zarith.
auto with zarith.
int auto.
split.
int auto.
change (Int.zwordsize) with (Z.of_nat 32); int auto.
change (Int.zwordsize) with (Z.of_nat 32); int auto.
change (Int.zwordsize) with (Z.of_nat 32); int auto.
change (Int.zwordsize) with (Z.of_nat 32); int auto.
change (Int.zwordsize) with (Z.of_nat 32); int auto.
change (Int.zwordsize) with (Z.of_nat 32); int auto.
int auto.

unfold set_part.
unfold clear_part.
unfold get_part.
rewrite clearl_left_eq.
unfold clearr.
rewrite Int.bits_or.
rewrite Int.bits_xor.
rewrite Int.bits_shl.
rewrite Int.bits_shl.
(* rewrite Int.bits_shr. *)
rewrite Int.unsigned_repr.
destruct (zlt n (Z.of_nat r)) eqn: eq1.
rewrite xorb_false_r.
rewrite orb_false_r; auto.
unfold zlt in eq1.
destruct Z_lt_dec; tryfalse.
inverts eq1.

rewrite bits_low with (i := (n - Z.of_nat r)).
rewrite xorb_false_r.
rewrite bits_low with (i := (n - Z.of_nat r)).
rewrite orb_false_r; auto.
int auto.
int auto.
int auto.
change (Int.zwordsize) with (Z.of_nat 32); int auto.
change (Int.zwordsize) with (Z.of_nat 32); int auto.
change (Int.zwordsize) with (Z.of_nat 32); int auto.
change (Int.zwordsize) with (Z.of_nat 32); int auto.
int auto.

(* (r <= n <= 31 - l)%nat ->
Int.testbit (set_part x l r i) (Z.of_nat n) =
Int.testbit i (Z.of_nat (n - r)) *)
introv Hc.
unfold set_part.
unfold clear_part.
unfold get_part.
rewrite clearl_left_eq.
unfold clearr.
rewrite Int.bits_or.
rewrite Int.bits_xor.
rewrite Int.bits_shl.
rewrite Int.bits_shl.
rewrite Int.bits_shru.
rewrite Int.unsigned_repr.
destruct (zlt n (Z.of_nat r)) eqn: eq1.
false.
auto with zarith.
unfold zlt in eq1.
destruct Z_lt_dec; tryfalse.
inverts eq1.

unfold zlt.
destruct Z_lt_dec.
rewrite <- Z.add_sub_swap.
rewrite Z.add_simpl_r.

2: { 
    rewrite <- Z.add_sub_swap in n1.
    rewrite Z.add_simpl_r in n1.
    unfold Int.zwordsize in *.
    unfold Int.wordsize in *.
    unfold Wordsize_32.wordsize in *.
    int auto.
   }

rewrite Int.bits_zero_ext.
unfold zlt.
destruct Z_lt_dec.
rewrite xorb_nilpotent.
rewrite orb_false_l; auto.
int auto.
auto with zarith.

int auto.
int auto.
change (Int.zwordsize) with (Z.of_nat 32); int auto.
change (Int.zwordsize) with (Z.of_nat 32); int auto.
change (Int.zwordsize) with (Z.of_nat 32); int auto.
change (Int.zwordsize) with (Z.of_nat 32); int auto.
change (Int.zwordsize) with (Z.of_nat 32); int auto.
int auto.
Qed.

Lemma get_part_testbit_eq:
forall n l r x,
 (0 <= n <= 31) ->
 (0 <= l + r <= 31)%nat ->
 ((0 <= n <= Z.of_nat (31- l -r)) -> 
 Int.testbit (get_part x l r) n =  
 Int.testbit x (n + Z.of_nat r)) /\
 ((Z.of_nat (31 - l - r) < n <= 31) -> 
  Int.testbit (get_part x l r) n = 
  false).
Proof.
introv Hn Hlr.
split.
introv Hc.
unfold get_part.
rewrite clearl_left_eq.
unfold clearr.
rewrite Int.bits_shru.
rewrite Int.unsigned_repr.
destruct (zlt (n + Z.of_nat r) Int.zwordsize) eqn: eq1.
unfold zlt in eq1.
destruct Z_lt_dec.
inverts eq1.

rewrite Int.bits_zero_ext.
unfold zlt.
destruct Z_lt_dec.
int auto.
int auto.
int auto.
tryfalse.

change (Int.zwordsize) with (Z.of_nat 32) in *.
false.
auto with zarith.
int auto.
change (Int.zwordsize) with (Z.of_nat 32); int auto.
int auto.

introv Hc.
unfold get_part.
rewrite clearl_left_eq.
unfold clearr.
rewrite Int.bits_shru.
rewrite Int.unsigned_repr.

unfold zlt.
destruct Z_lt_dec.
(* Z.of_nat n + Z.of_nat r < Int.zwordsize *)
rewrite Int.bits_zero_ext.
unfold zlt.
destruct Z_lt_dec; auto.
false.
auto with zarith.
int auto.

auto.
int auto.
change (Int.zwordsize) with (Z.of_nat 32); int auto.
int auto.
Qed.


(*-------------neq--------------*)
Lemma get_set_smsl_raddr_neq:
forall t x i,
  t = smsl_sr \/ t = smsl_sw \/ t = smsl_sx \/
  t = smsl_ur \/ t = smsl_uw \/ t = smsl_ux ->
  (forall d, ((31 - Z.of_nat (0 + 8)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x smsl_raddr i) t = get_mpax x t.
Proof.
intros.
destruct H.
(* ------ t = smsl_sr ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 26 + 5 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = smsl_sw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 27 + 4 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = smsl_sx ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 28 + 3 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = smsl_ur ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 29 + 2 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = smsl_uw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
(* ------ t = smsl_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_smsl_sr_neq:
forall t x i,
  t = smsl_sw \/ t = smsl_sx \/  t = smsl_ur \/ 
  t = smsl_uw \/ t = smsl_ux ->
  (forall d, ((31 - Z.of_nat (26 + 5)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x smsl_sr i) t = get_mpax x t.
Proof.
intros.
destruct H.
(* ------ t = smsl_sw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 27 + 4 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = smsl_sx ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 28 + 3 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = smsl_ur ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 29 + 2 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = smsl_uw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
(* ------ t = smsl_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_smsl_sw_neq:
forall t x i,
  t = smsl_sx \/  t = smsl_ur \/ 
  t = smsl_uw \/ t = smsl_ux ->
  (forall d, ((31 - Z.of_nat (27 + 4)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x smsl_sw i) t = get_mpax x t.
Proof.
intros.
destruct H.
(* ------ t = smsl_sx ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 28 + 3 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = smsl_ur ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 29 + 2 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = smsl_uw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
(* ------ t = smsl_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_smsl_sx_neq:
forall t x i,
  t = smsl_ur \/ t = smsl_uw \/ t = smsl_ux ->
  (forall d, ((31 - Z.of_nat (28 + 3)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x smsl_sx i) t = get_mpax x t.
Proof.
intros.
destruct H.
(* ------ t = smsl_ur ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 29 + 2 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = smsl_uw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
(* ------ t = smsl_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_smsl_ur_neq:
forall t x i,
  t = smsl_uw \/ t = smsl_ux ->
  (forall d, ((31 - Z.of_nat (29 + 2)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x smsl_ur i) t = get_mpax x t.
Proof.
intros.
destruct H.
(* ------ t = smsl_uw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
(* ------ t = smsl_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_smsl_uw_neq:
forall t x i,
  t = smsl_ux ->
  (forall d, ((31 - Z.of_nat (30 + 1)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x smsl_uw i) t = get_mpax x t.
Proof.
intros.
(* ------ t = smsl_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_sesl_raddr_neq:
forall t x i,
  t = sesl_sr \/ t = sesl_sw \/ t = sesl_sx \/
  t = sesl_ur \/ t = sesl_uw \/ t = sesl_ux ->
  (forall d, ((31 - Z.of_nat (0 + 8)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x sesl_raddr i) t = get_mpax x t.
Proof.
intros.
destruct H.
(* ------ t = sesl_sr ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 26 + 5 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = sesl_sw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 27 + 4 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = sesl_sx ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 28 + 3 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = sesl_ur ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 29 + 2 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = sesl_uw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
(* ------ t = sesl_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_sesl_sr_neq:
forall t x i,
  t = sesl_sw \/ t = sesl_sx \/  t = sesl_ur \/ 
  t = sesl_uw \/ t = sesl_ux ->
  (forall d, ((31 - Z.of_nat (26 + 5)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x sesl_sr i) t = get_mpax x t.
Proof.
intros.
destruct H.
(* ------ t = sesl_sw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 27 + 4 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = sesl_sx ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 28 + 3 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = sesl_ur ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 29 + 2 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = sesl_uw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
(* ------ t = sesl_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_sesl_sw_neq:
forall t x i,
  t = sesl_sx \/  t = sesl_ur \/ 
  t = sesl_uw \/ t = sesl_ux ->
  (forall d, ((31 - Z.of_nat (27 + 4)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x sesl_sw i) t = get_mpax x t.
Proof.
intros.
destruct H.
(* ------ t = sesl_sx ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 28 + 3 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = sesl_ur ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 29 + 2 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = sesl_uw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
(* ------ t = sesl_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_sesl_sx_neq:
forall t x i,
  t = sesl_ur \/ t = sesl_uw \/ t = sesl_ux ->
  (forall d, ((31 - Z.of_nat (28 + 3)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x sesl_sx i) t = get_mpax x t.
Proof.
intros.
destruct H.
(* ------ t = sesl_ur ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 29 + 2 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = sesl_uw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
(* ------ t = sesl_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_sesl_ur_neq:
forall t x i,
  t = sesl_uw \/ t = sesl_ux ->
  (forall d, ((31 - Z.of_nat (29 + 2)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x sesl_ur i) t = get_mpax x t.
Proof.
intros.
destruct H.
(* ------ t = sesl_uw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
(* ------ t = sesl_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_sesl_uw_neq:
forall t x i,
  t = sesl_ux ->
  (forall d, ((31 - Z.of_nat (30 + 1)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x sesl_uw i) t = get_mpax x t.
Proof.
intros.
(* ------ t = sesl_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_xmc_raddr_neq:
forall t x i,
  t = xmc_sr \/ t = xmc_sw \/ t = xmc_sx \/
  t = xmc_ur \/ t = xmc_uw \/ t = xmc_ux ->
  (forall d, ((31 - Z.of_nat (0 + 8)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x xmc_raddr i) t = get_mpax x t.
Proof.
intros.
destruct H.
(* ------ t = xmc_sr ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 26 + 5 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = xmc_sw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 27 + 4 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = xmc_sx ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 28 + 3 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = xmc_ur ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 29 + 2 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = xmc_uw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
(* ------ t = xmc_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_xmc_sr_neq:
forall t x i,
  t = xmc_sw \/ t = xmc_sx \/  t = xmc_ur \/ 
  t = xmc_uw \/ t = xmc_ux ->
  (forall d, ((31 - Z.of_nat (26 + 5)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x xmc_sr i) t = get_mpax x t.
Proof.
intros.
destruct H.
(* ------ t = xmc_sw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 27 + 4 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = xmc_sx ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 28 + 3 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = xmc_ur ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 29 + 2 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = xmc_uw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
(* ------ t = xmc_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_xmc_sw_neq:
forall t x i,
  t = xmc_sx \/  t = xmc_ur \/ 
  t = xmc_uw \/ t = xmc_ux ->
  (forall d, ((31 - Z.of_nat (27 + 4)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x xmc_sw i) t = get_mpax x t.
Proof.
intros.
destruct H.
(* ------ t = xmc_sx ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 28 + 3 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = xmc_ur ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 29 + 2 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = xmc_uw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
(* ------ t = xmc_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_xmc_sx_neq:
forall t x i,
  t = xmc_ur \/ t = xmc_uw \/ t = xmc_ux ->
  (forall d, ((31 - Z.of_nat (28 + 3)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x xmc_sx i) t = get_mpax x t.
Proof.
intros.
destruct H.
(* ------ t = xmc_ur ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 29 + 2 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
destruct H.
(* ------ t = xmc_uw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
(* ------ t = xmc_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_xmc_ur_neq:
forall t x i,
  t = xmc_uw \/ t = xmc_ux ->
  (forall d, ((31 - Z.of_nat (29 + 2)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x xmc_ur i) t = get_mpax x t.
Proof.
intros.
destruct H.
(* ------ t = xmc_uw ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
(* ------ t = xmc_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_xmc_uw_neq:
forall t x i,
  t = xmc_ux ->
  (forall d, ((31 - Z.of_nat (30 + 1)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x xmc_uw i) t = get_mpax x t.
Proof.
intros.
(* ------ t = xmc_ux ------ *)
subst.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_smsh_neq:
forall x i,
  (forall d, ((31 - Z.of_nat (0 + 12)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x smsh_baddr i) smsh_segsize = get_mpax x smsh_segsize.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 20 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_sesh_neq:
forall x i,
  (forall d, ((31 - Z.of_nat (0 + 12)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x sesh_baddr i) sesh_segsize = get_mpax x sesh_segsize.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 20 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

Lemma get_set_xmc_neq:
forall x i,
  (forall d, ((31 - Z.of_nat (0 + 12)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x xmc_baddr i) xmc_segsize = get_mpax x xmc_segsize.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq; eauto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 20 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply get_part_testbit_eq with (n:= i0) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
erewrite Heq1'; auto with zarith.
eapply set_part_testbit; auto with zarith.
symmetry.
eapply get_part_testbit_eq with (n:= i0); auto with zarith.
Qed.

(*-------------end of neq--------------*)

(*--------------eq-----------------*)

Lemma get_set_smsl_raddr_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (0 + 8)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x smsl_raddr i) smsl_raddr = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 0 + 8 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 8) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_smsl_sr_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (26 + 5)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x smsl_sr i) smsl_sr = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 26 + 5 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 5) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_smsl_sw_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (27 + 4)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x smsl_sw i) smsl_sw = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 27 + 4 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 4) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_smsl_sx_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (28 + 3)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x smsl_sx i) smsl_sx = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 28 + 3 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 3) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_smsl_ur_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (29 + 2)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x smsl_ur i) smsl_ur = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 29 + 2 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 2) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_smsl_uw_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (30 + 1)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x smsl_uw i) smsl_uw = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 1) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_smsl_ux_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (31 + 0)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x smsl_ux i) smsl_ux = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 0) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_sesl_raddr_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (0 + 8)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x sesl_raddr i) sesl_raddr = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 0 + 8 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 8) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_sesl_sr_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (26 + 5)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x sesl_sr i) sesl_sr = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 26 + 5 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 5) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_sesl_sw_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (27 + 4)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x sesl_sw i) sesl_sw = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 27 + 4 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 4) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_sesl_sx_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (28 + 3)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x sesl_sx i) sesl_sx = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 28 + 3 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 3) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_sesl_ur_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (29 + 2)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x sesl_ur i) sesl_ur = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 29 + 2 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 2) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_sesl_uw_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (30 + 1)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x sesl_uw i) sesl_uw = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 1) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_sesl_ux_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (31 + 0)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x sesl_ux i) sesl_ux = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 0) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_xmc_raddr_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (0 + 8)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x xmc_raddr i) xmc_raddr = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 0 + 8 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 8) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_xmc_sr_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (26 + 5)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x xmc_sr i) xmc_sr = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 26 + 5 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 5) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_xmc_sw_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (27 + 4)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x xmc_sw i) xmc_sw = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 27 + 4 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 4) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_xmc_sx_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (28 + 3)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x xmc_sx i) xmc_sx = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 28 + 3 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 3) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_xmc_ur_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (29 + 2)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x xmc_ur i) xmc_ur = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 29 + 2 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 2) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_xmc_uw_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (30 + 1)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x xmc_uw i) xmc_uw = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 30 + 1 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 1) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_xmc_ux_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (31 + 0)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x xmc_ux i) xmc_ux = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 31 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 0) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_smsh_baddr_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (0 + 12)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x smsh_baddr i) smsh_baddr = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 0 + 12 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 12) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_segsize_eq:
forall x i id,
  (forall d, ((31 - Z.of_nat (20 + 0)) < d <= 31) -> Int.testbit i d = false) ->
  (id = smsh_segsize \/ id = sesh_segsize  \/ id = xmc_segsize) ->
  get_mpax (set_mpax x id i) id = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
rename H0 into Hid.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 20 + 0 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hid as [ | [ | ]]; subst id; simpl.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 0) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 0) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 0) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_sesh_baddr_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (0 + 12)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x sesh_baddr i) sesh_baddr = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 0 + 12 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 12) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.

Lemma get_set_xmc_baddr_eq:
forall x i,
  (forall d, ((31 - Z.of_nat (0 + 12)) < d <= 31) -> Int.testbit i d = false) ->
  get_mpax (set_mpax x xmc_baddr i) xmc_baddr = i.
Proof.
intros.
simpl.
erewrite <- Int.same_bits_eq ; auto.
intros.
change (Int.zwordsize) with 32 in*.
assert (Heq: (0 <= 0 + 12 <= 31)%nat) by auto with zarith.
lets Heq': Heq.
eapply get_part_testbit_eq with (n:= i0) in Heq; auto with zarith.
destruct Heq as (Heq1 & Heq2).
match goal with
 H1: ?p1 -> Int.testbit _ _ = Int.testbit _ _,
 H2: ?p2 -> Int.testbit _ _ = false
|- _ => assert(Hc: p1 \/ p2)
end.
mauto.
destruct Hc; [ erewrite Heq1 | erewrite Heq2]; auto.
eapply set_part_testbit with (n:= (i0 + Z.of_nat 12) ) in Heq'; auto with zarith.
destruct Heq' as (Heq1' & Heq2').
rewrite Z.add_simpl_r in Heq2'.
eapply Heq2'; auto with zarith.
symmetry.
eapply H; auto with zarith.
Qed.


(*--------------end of eq-----------------*)

Lemma get_mpax_struct_smsl:
forall tpvl x v vl,
(forall d, ((31 - Z.of_nat (0 + 8)) < d <= 31) -> Int.testbit v d = false) ->
tpvl = (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil) ->
vl = (Vint32 v :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil) ->
get_mpax_struct (set_mpax_struct x tpvl vl) tpvl = vl.
Proof.
intros.
simpljoin.
assert (Hlem: forall d, 0 < d <= 31 -> Int.testbit Int.one d = false).
{ intros.
   eapply Int.bits_size_2.
   change (Int.size Int.one) with 1.
   auto with zarith.
}
unfold get_mpax_struct, set_mpax_struct;
try rewrite get_set_smsl_raddr_eq;
repeat try rewrite get_set_smsl_raddr_neq in *; try solve [ tauto];
try rewrite get_set_smsl_sr_eq;
repeat try rewrite get_set_smsl_sr_neq in *; try solve [ tauto];
try rewrite get_set_smsl_sw_eq;
repeat try rewrite get_set_smsl_sw_neq in *; try solve [ tauto];
try rewrite get_set_smsl_sx_eq;
repeat try rewrite get_set_smsl_sx_neq in *; try solve [ tauto];
try rewrite get_set_smsl_ur_eq;
repeat try rewrite get_set_smsl_ur_neq in *; try solve [ tauto];
try rewrite get_set_smsl_uw_eq;
repeat try rewrite get_set_smsl_uw_neq in *; try solve [ tauto];
try rewrite get_set_smsl_ux_eq;
auto;
try change ($ 0) with Int.zero;
try change ($ 1) with Int.one;
try solve [ intros; eapply Hlem; auto with zarith];
try solve [intros; rewrite Int.bits_zero; auto].
Qed.

Lemma get_mpax_struct_sesl:
forall tpvl x v vl,
(forall d, ((31 - Z.of_nat (0 + 8)) < d <= 31) -> Int.testbit v d = false) ->
tpvl = (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil) ->
vl = (Vint32 v :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil) ->
get_mpax_struct (set_mpax_struct x tpvl vl) tpvl = vl.
Proof.
intros.
simpljoin.
assert (Hlem: forall d, 0 < d <= 31 -> Int.testbit Int.one d = false).
{ intros.
   eapply Int.bits_size_2.
   change (Int.size Int.one) with 1.
   auto with zarith.
}
unfold get_mpax_struct, set_mpax_struct;
try rewrite get_set_sesl_raddr_eq;
repeat try rewrite get_set_sesl_raddr_neq in *; try solve [ tauto];
try rewrite get_set_sesl_sr_eq;
repeat try rewrite get_set_sesl_sr_neq in *; try solve [ tauto];
try rewrite get_set_sesl_sw_eq;
repeat try rewrite get_set_sesl_sw_neq in *; try solve [ tauto];
try rewrite get_set_sesl_sx_eq;
repeat try rewrite get_set_sesl_sx_neq in *; try solve [ tauto];
try rewrite get_set_sesl_ur_eq;
repeat try rewrite get_set_sesl_ur_neq in *; try solve [ tauto];
try rewrite get_set_sesl_uw_eq;
repeat try rewrite get_set_sesl_uw_neq in *; try solve [ tauto];
try rewrite get_set_sesl_ux_eq;
auto;
try change ($ 0) with Int.zero;
try change ($ 1) with Int.one;
try solve [ intros; eapply Hlem; auto with zarith];
try solve [intros; rewrite Int.bits_zero; auto].
Qed.

Lemma get_mpax_struct_xmc:
forall tpvl x v vl,
(forall d, ((31 - Z.of_nat (0 + 8)) < d <= 31) -> Int.testbit v d = false) ->
tpvl = (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil) ->
vl = (Vint32 v :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil) ->
get_mpax_struct (set_mpax_struct x tpvl vl) tpvl = vl.
Proof.
intros.
simpljoin.
assert (Hlem: forall d, 0 < d <= 31 -> Int.testbit Int.one d = false).
{ intros.
   eapply Int.bits_size_2.
   change (Int.size Int.one) with 1.
   auto with zarith.
}
unfold get_mpax_struct, set_mpax_struct;
try rewrite get_set_xmc_raddr_eq;
repeat try rewrite get_set_xmc_raddr_neq in *; try solve [ tauto];
try rewrite get_set_xmc_sr_eq;
repeat try rewrite get_set_xmc_sr_neq in *; try solve [ tauto];
try rewrite get_set_xmc_sw_eq;
repeat try rewrite get_set_xmc_sw_neq in *; try solve [ tauto];
try rewrite get_set_xmc_sx_eq;
repeat try rewrite get_set_xmc_sx_neq in *; try solve [ tauto];
try rewrite get_set_xmc_ur_eq;
repeat try rewrite get_set_xmc_ur_neq in *; try solve [ tauto];
try rewrite get_set_xmc_uw_eq;
repeat try rewrite get_set_xmc_uw_neq in *; try solve [ tauto];
try rewrite get_set_xmc_ux_eq;
auto;
try change ($ 0) with Int.zero;
try change ($ 1) with Int.one;
try solve [ intros; eapply Hlem; auto with zarith];
try solve [intros; rewrite Int.bits_zero; auto].
Qed.

Lemma get_mpax_struct_smsl_gen:
forall tpvl x v v1 v2 v3 v4 v5 v6 vl,
(forall d, ((31 - Z.of_nat (0 + 8)) < d <= 31) -> Int.testbit v d = false) ->
tpvl = (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil) ->
vl = (Vint32 v :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: nil) ->
isflag v1 /\ isflag v2 /\ isflag v3 /\ isflag v4 /\ isflag v5 /\ isflag v6 ->
get_mpax_struct (set_mpax_struct x tpvl vl) tpvl = vl.
Proof.
intros.
simpljoin.
assert (Hlem: forall d, 0 < d <= 31 -> Int.testbit Int.one d = false).
{ intros.
   eapply Int.bits_size_2.
   change (Int.size Int.one) with 1.
   auto with zarith.
}
repeat try (match goal with H: isflag ?v |- _ => destruct H; subst end);
unfold get_mpax_struct, set_mpax_struct;
try rewrite get_set_smsl_raddr_eq;
repeat try rewrite get_set_smsl_raddr_neq in *; try solve [ tauto];
try rewrite get_set_smsl_sr_eq;
repeat try rewrite get_set_smsl_sr_neq in *; try solve [ tauto];
try rewrite get_set_smsl_sw_eq;
repeat try rewrite get_set_smsl_sw_neq in *; try solve [ tauto];
try rewrite get_set_smsl_sx_eq;
repeat try rewrite get_set_smsl_sx_neq in *; try solve [ tauto];
try rewrite get_set_smsl_ur_eq;
repeat try rewrite get_set_smsl_ur_neq in *; try solve [ tauto];
try rewrite get_set_smsl_uw_eq;
repeat try rewrite get_set_smsl_uw_neq in *; try solve [ tauto];
try rewrite get_set_smsl_ux_eq;
auto;
try change ($ 0) with Int.zero;
try change ($ 1) with Int.one;
try solve [ intros; eapply Hlem; auto with zarith];
try solve [intros; rewrite Int.bits_zero; auto].
Qed.

Lemma get_mpax_struct_sesl_gen:
forall tpvl x v v1 v2 v3 v4 v5 v6 vl,
(forall d, ((31 - Z.of_nat (0 + 8)) < d <= 31) -> Int.testbit v d = false) ->
tpvl = (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil) ->
vl = (Vint32 v :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: nil) ->
isflag v1 /\ isflag v2 /\ isflag v3 /\ isflag v4 /\ isflag v5 /\ isflag v6 ->
get_mpax_struct (set_mpax_struct x tpvl vl) tpvl = vl.
Proof.
intros.
simpljoin.
assert (Hlem: forall d, 0 < d <= 31 -> Int.testbit Int.one d = false).
{ intros.
   eapply Int.bits_size_2.
   change (Int.size Int.one) with 1.
   auto with zarith.
}
repeat try (match goal with H: isflag ?v |- _ => destruct H; subst end);
unfold get_mpax_struct, set_mpax_struct;
try rewrite get_set_sesl_raddr_eq;
repeat try rewrite get_set_sesl_raddr_neq in *; try solve [ tauto];
try rewrite get_set_sesl_sr_eq;
repeat try rewrite get_set_sesl_sr_neq in *; try solve [ tauto];
try rewrite get_set_sesl_sw_eq;
repeat try rewrite get_set_sesl_sw_neq in *; try solve [ tauto];
try rewrite get_set_sesl_sx_eq;
repeat try rewrite get_set_sesl_sx_neq in *; try solve [ tauto];
try rewrite get_set_sesl_ur_eq;
repeat try rewrite get_set_sesl_ur_neq in *; try solve [ tauto];
try rewrite get_set_sesl_uw_eq;
repeat try rewrite get_set_sesl_uw_neq in *; try solve [ tauto];
try rewrite get_set_sesl_ux_eq;
auto;
try change ($ 0) with Int.zero;
try change ($ 1) with Int.one;
try solve [ intros; eapply Hlem; auto with zarith];
try solve [intros; rewrite Int.bits_zero; auto].
Qed.

Lemma get_mpax_struct_xmcl_gen:
forall tpvl x v v1 v2 v3 v4 v5 v6 vl,
(forall d, ((31 - Z.of_nat (0 + 8)) < d <= 31) -> Int.testbit v d = false) ->
tpvl = (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil) ->
vl = (Vint32 v :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: nil) ->
isflag v1 /\ isflag v2 /\ isflag v3 /\ isflag v4 /\ isflag v5 /\ isflag v6 ->
get_mpax_struct (set_mpax_struct x tpvl vl) tpvl = vl.
Proof.
intros.
simpljoin.
assert (Hlem: forall d, 0 < d <= 31 -> Int.testbit Int.one d = false).
{ intros.
   eapply Int.bits_size_2.
   change (Int.size Int.one) with 1.
   auto with zarith.
}
repeat try (match goal with H: isflag ?v |- _ => destruct H; subst end);
unfold get_mpax_struct, set_mpax_struct;
try rewrite get_set_xmc_raddr_eq;
repeat try rewrite get_set_xmc_raddr_neq in *; try solve [ tauto];
try rewrite get_set_xmc_sr_eq;
repeat try rewrite get_set_xmc_sr_neq in *; try solve [ tauto];
try rewrite get_set_xmc_sw_eq;
repeat try rewrite get_set_xmc_sw_neq in *; try solve [ tauto];
try rewrite get_set_xmc_sx_eq;
repeat try rewrite get_set_xmc_sx_neq in *; try solve [ tauto];
try rewrite get_set_xmc_ur_eq;
repeat try rewrite get_set_xmc_ur_neq in *; try solve [ tauto];
try rewrite get_set_xmc_uw_eq;
repeat try rewrite get_set_xmc_uw_neq in *; try solve [ tauto];
try rewrite get_set_xmc_ux_eq;
auto;
try change ($ 0) with Int.zero;
try change ($ 1) with Int.one;
try solve [ intros; eapply Hlem; auto with zarith];
try solve [intros; rewrite Int.bits_zero; auto].
Qed.

Lemma get_mpax_struct_smsh_gen:
forall tpvl x v v1 vl,
(forall d, ((31 - Z.of_nat (12 + 0)) < d <= 31) -> Int.testbit v d = false) ->
  (forall d, ((31 - Z.of_nat (20)) < d <= 31) -> Int.testbit v1 d = false) ->
tpvl = (smsh_baddr :: smsh_segsize :: nil) ->
vl = (Vint32 v :: Vint32 v1 :: nil) ->
get_mpax_struct (set_mpax_struct x tpvl vl) tpvl = vl.
Proof.
intros.
simpljoin.
unfold get_mpax_struct, set_mpax_struct.
rewrite get_set_smsh_baddr_eq; auto with zarith.
rewrite get_set_smsh_neq; auto with zarith.
rewrite get_set_segsize_eq; auto with zarith.
Qed.

Lemma get_mpax_struct_sesh_gen:
forall tpvl x v v1 vl,
(forall d, ((31 - Z.of_nat (12 + 0)) < d <= 31) -> Int.testbit v d = false) ->
  (forall d, ((31 - Z.of_nat (20)) < d <= 31) -> Int.testbit v1 d = false) ->
tpvl = (sesh_baddr :: sesh_segsize :: nil) ->
vl = (Vint32 v :: Vint32 v1 :: nil) ->
get_mpax_struct (set_mpax_struct x tpvl vl) tpvl = vl.
Proof.
intros.
simpljoin.
unfold get_mpax_struct, set_mpax_struct.
rewrite get_set_sesh_baddr_eq; auto with zarith.
rewrite get_set_sesh_neq; auto with zarith.
rewrite get_set_segsize_eq; auto with zarith.
Qed.

Lemma get_mpax_struct_xmch_gen:
forall tpvl x v v1 vl,
(forall d, ((31 - Z.of_nat (12 + 0)) < d <= 31) -> Int.testbit v d = false) ->
  (forall d, ((31 - Z.of_nat (20)) < d <= 31) -> Int.testbit v1 d = false) ->
tpvl = (xmc_baddr :: xmc_segsize :: nil) ->
vl = (Vint32 v :: Vint32 v1 :: nil) ->
get_mpax_struct (set_mpax_struct x tpvl vl) tpvl = vl.
Proof.
intros.
simpljoin.
unfold get_mpax_struct, set_mpax_struct.
rewrite get_set_xmc_baddr_eq; auto with zarith.
rewrite get_set_xmc_neq; auto with zarith.
rewrite get_set_segsize_eq; auto with zarith.
Qed.

Lemma R_SES_Mpax_P_update_hold_comm:
forall v v' (n: Z) vl l ses_mpax,
  0 <= n <= Int.max_unsigned ->
  nth_val (Z.to_nat(n*2)) vl = Some (Vint32 v) ->
  nth_val (Z.to_nat(n*2 + 1)) vl = Some (Vint32 l) ->
  R_SES_Mpax_P vl ses_mpax ->
  R_SES_Mpax_P
    (update_nth_val (Z.to_nat (n*2)) vl (Vint32 v'))
    (SesMod.set ses_mpax ($ n) (v', l)).
Proof.
  introv Hrgn Hnth1 Hnth2 Hrp.
  unfold R_SES_Mpax_P in *.
  destruct Hrp as (Hhl & Hlh).
  split.
  unfold RHL_SES_Mpax_P.
  intros.
  assert (Hc:(index = Int.repr n) \/ (index <> Int.repr n)) by tauto.
  destruct Hc.
  subst index.
  rewrite SesMod.map_get_set in H; inverts H.
  rewrite Int.unsigned_repr; auto with zarith.
  erewrite update_nth; eauto.
  erewrite nth_upd_neqrev; auto with zarith.
  rewrite SesMod.map_get_set' in H; auto.
  eapply Hhl in H; eauto.
  destruct H as (H & H').
  do 2 try erewrite nth_upd_neqrev; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  int auto.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  eapply Z.mul_reg_r in Hf; subst.
  rewrite Int.repr_unsigned in *; tryfalse.
  auto with zarith.
  int auto.
  unfold RLH_SES_Mpax_P.
  lets Hnth1': Hnth1; lets Hnth2' : Hnth2.
  splits; intros;
  assert (Hc:(Int.unsigned index = n) \/ (Int.unsigned index <> n)) by tauto;
  destruct Hc;
  try (subst n;
  eapply Hlh in Hnth1, Hnth2; eauto;
  destruct Hnth1 as (? & Hnth1); destruct Hnth2 as (? & Hnth2);
  unfolds in Hnth1; unfolds in Hnth2; simpl in Hnth1, Hnth2;
  rewrite Hnth1 in Hnth2; inverts Hnth2);
  try (eapply nth_upd_eq in H; inverts H);
  try rewrite Int.repr_unsigned in *; auto with zarith;
  try rewrite SesMod.map_get_set; eauto;
  try eapply nth_upd_neq in H; try rewrite Hnth1' in H; try rewrite Hnth2' in H; inverts H;
  try rewrite SesMod.map_get_set'; eauto;
  try eapply Hlh; eauto.
  introv Hf; subst.
  try rewrite Int.unsigned_repr in *; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  int auto.
  auto with zarith.
  introv Hf; subst.
  try rewrite Int.unsigned_repr in *; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  int auto.
Qed.

Lemma R_SES_Mpax_P_update_hold_comm':
forall v v' (n: Z) vl l ses_mpax,
  0 <= n <= Int.max_unsigned ->
  nth_val (Z.to_nat(n*2)) vl = Some (Vint32 l) ->
  nth_val (Z.to_nat(n*2 + 1)) vl = Some (Vint32 v) ->
  R_SES_Mpax_P vl ses_mpax ->
  R_SES_Mpax_P
    (update_nth_val (Z.to_nat (n*2 + 1)) vl (Vint32 v'))
    (SesMod.set ses_mpax ($ n) (l, v')).
Proof.
  introv Hrgn Hnth1 Hnth2 Hrp.
  unfold R_SES_Mpax_P in *.
  destruct Hrp as (Hhl & Hlh).
  split.
  unfold RHL_SES_Mpax_P.
  intros.
  assert (Hc:(index = Int.repr n) \/ (index <> Int.repr n)) by tauto.
  destruct Hc.
  subst index.
  rewrite SesMod.map_get_set in H; inverts H.
  rewrite Int.unsigned_repr; auto with zarith.
  erewrite update_nth; eauto.
  erewrite nth_upd_neqrev; auto with zarith.
  rewrite SesMod.map_get_set' in H; auto.
  eapply Hhl in H; eauto.
  destruct H as (H & H').
  do 2 try erewrite nth_upd_neqrev; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  rewrite Z.add_cancel_r in Hf.
  eapply Z.mul_reg_r in Hf; subst.
  rewrite Int.repr_unsigned in *; tryfalse.
  auto with zarith.
  unfold RLH_SES_Mpax_P.
  lets Hnth1': Hnth1; lets Hnth2' : Hnth2.
  splits; intros;
  assert (Hc:(Int.unsigned index = n) \/ (Int.unsigned index <> n)) by tauto;
  destruct Hc;
  try (subst n;
  eapply Hlh in Hnth1, Hnth2; eauto;
  destruct Hnth1 as (? & Hnth1); destruct Hnth2 as (? & Hnth2);
  unfolds in Hnth1; unfolds in Hnth2; simpl in Hnth1, Hnth2;
  rewrite Hnth1 in Hnth2; inverts Hnth2);
  try (eapply nth_upd_eq in H; inverts H);
  try rewrite Int.repr_unsigned in *; auto with zarith;
  try rewrite SesMod.map_get_set; eauto;
  try eapply nth_upd_neq in H; try rewrite Hnth1' in H; try rewrite Hnth2' in H; inverts H;
  try rewrite SesMod.map_get_set'; eauto;
  try eapply Hlh; eauto.
  introv Hf; subst.
  try rewrite Int.unsigned_repr in *; auto with zarith.
  introv Hf; subst.
  try rewrite Int.unsigned_repr in *; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  introv Hf; subst.
  try rewrite Int.unsigned_repr in *; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
Qed.

Lemma R_SMS_Mpax_P_update_hold_comm:
forall v v' (n: Z) vl l sms_mpax,
  0 <= n <= Int.max_unsigned ->
  nth_val (Z.to_nat(n*2)) vl = Some (Vint32 v) ->
  nth_val (Z.to_nat(n*2 + 1)) vl = Some (Vint32 l) ->
  R_SMS_Mpax_P vl sms_mpax ->
  R_SMS_Mpax_P
    (update_nth_val (Z.to_nat (n*2)) vl (Vint32 v'))
    (SmsMod.set sms_mpax ($ n) (v', l)).
Proof.
  introv Hrgn Hnth1 Hnth2 Hrp.
  unfold R_SMS_Mpax_P in *.
  destruct Hrp as (Hhl & Hlh).
  split.
  unfold RHL_SMS_Mpax_P.
  intros.
  assert (Hc:(index = Int.repr n) \/ (index <> Int.repr n)) by tauto.
  destruct Hc.
  subst index.
  rewrite SmsMod.map_get_set in H; inverts H.
  rewrite Int.unsigned_repr; auto with zarith.
  erewrite update_nth; eauto.
  erewrite nth_upd_neqrev; auto with zarith.
  rewrite SmsMod.map_get_set' in H; auto.
  eapply Hhl in H; eauto.
  destruct H as (H & H').
  do 2 try erewrite nth_upd_neqrev; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  int auto.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  eapply Z.mul_reg_r in Hf; subst.
  rewrite Int.repr_unsigned in *; tryfalse.
  auto with zarith.
  int auto.
  unfold RLH_SMS_Mpax_P.
  lets Hnth1': Hnth1; lets Hnth2' : Hnth2.
  splits; intros;
  assert (Hc:(Int.unsigned index = n) \/ (Int.unsigned index <> n)) by tauto;
  destruct Hc;
  try (subst n;
  eapply Hlh in Hnth1, Hnth2; eauto;
  destruct Hnth1 as (? & Hnth1); destruct Hnth2 as (? & Hnth2);
  unfolds in Hnth1; unfolds in Hnth2; simpl in Hnth1, Hnth2;
  rewrite Hnth1 in Hnth2; inverts Hnth2);
  try (eapply nth_upd_eq in H; inverts H);
  try rewrite Int.repr_unsigned in *; auto with zarith;
  try rewrite SmsMod.map_get_set; eauto;
  try eapply nth_upd_neq in H; try rewrite Hnth1' in H; try rewrite Hnth2' in H; inverts H;
  try rewrite SmsMod.map_get_set'; eauto;
  try eapply Hlh; eauto.
  introv Hf; subst.
  try rewrite Int.unsigned_repr in *; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  int auto.
  auto with zarith.
  introv Hf; subst.
  try rewrite Int.unsigned_repr in *; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  int auto.
Qed.

Lemma R_SMS_Mpax_P_update_hold_comm':
forall v v' (n: Z) vl l sms_mpax,
  0 <= n <= Int.max_unsigned ->
  nth_val (Z.to_nat(n*2)) vl = Some (Vint32 l) ->
  nth_val (Z.to_nat(n*2 + 1)) vl = Some (Vint32 v) ->
  R_SMS_Mpax_P vl sms_mpax ->
  R_SMS_Mpax_P
    (update_nth_val (Z.to_nat (n*2 + 1)) vl (Vint32 v'))
    (SmsMod.set sms_mpax ($ n) (l, v')).
Proof.
  introv Hrgn Hnth1 Hnth2 Hrp.
  unfold R_SMS_Mpax_P in *.
  destruct Hrp as (Hhl & Hlh).
  split.
  unfold RHL_SMS_Mpax_P.
  intros.
  assert (Hc:(index = Int.repr n) \/ (index <> Int.repr n)) by tauto.
  destruct Hc.
  subst index.
  rewrite SmsMod.map_get_set in H; inverts H.
  rewrite Int.unsigned_repr; auto with zarith.
  erewrite update_nth; eauto.
  erewrite nth_upd_neqrev; auto with zarith.
  rewrite SmsMod.map_get_set' in H; auto.
  eapply Hhl in H; eauto.
  destruct H as (H & H').
  do 2 try erewrite nth_upd_neqrev; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  rewrite Z.add_cancel_r in Hf.
  eapply Z.mul_reg_r in Hf; subst.
  rewrite Int.repr_unsigned in *; tryfalse.
  auto with zarith.
  unfold RLH_SMS_Mpax_P.
  lets Hnth1': Hnth1; lets Hnth2' : Hnth2.
  splits; intros;
  assert (Hc:(Int.unsigned index = n) \/ (Int.unsigned index <> n)) by tauto;
  destruct Hc;
  try (subst n;
  eapply Hlh in Hnth1, Hnth2; eauto;
  destruct Hnth1 as (? & Hnth1); destruct Hnth2 as (? & Hnth2);
  unfolds in Hnth1; unfolds in Hnth2; simpl in Hnth1, Hnth2;
  rewrite Hnth1 in Hnth2; inverts Hnth2);
  try (eapply nth_upd_eq in H; inverts H);
  try rewrite Int.repr_unsigned in *; auto with zarith;
  try rewrite SmsMod.map_get_set; eauto;
  try eapply nth_upd_neq in H; try rewrite Hnth1' in H; try rewrite Hnth2' in H; inverts H;
  try rewrite SmsMod.map_get_set'; eauto;
  try eapply Hlh; eauto.
  introv Hf; subst.
  try rewrite Int.unsigned_repr in *; auto with zarith.
  introv Hf; subst.
  try rewrite Int.unsigned_repr in *; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  introv Hf; subst.
  try rewrite Int.unsigned_repr in *; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
Qed.

Lemma R_XMC_Mpax_P_update_hold_comm:
forall v v' (n: Z) vl l xmpax,
  0 <= n <= Int.max_unsigned ->
  nth_val (Z.to_nat(n*2)) vl = Some (Vint32 v) ->
  nth_val (Z.to_nat(n*2 + 1)) vl = Some (Vint32 l) ->
  R_XMpax_P vl xmpax ->
  R_XMpax_P
    (update_nth_val (Z.to_nat (n*2)) vl (Vint32 v'))
    (XmcMod.set xmpax ($ n) (v', l)).
Proof.
 introv Hrgn Hnth1 Hnth2 Hrp.
  unfold R_XMpax_P in *.
  destruct Hrp as (Hhl & Hlh).
  split.
  unfold RHL_XMpax_P.
  intros.
  assert (Hc:(index = Int.repr n) \/ (index <> Int.repr n)) by tauto.
  destruct Hc.
  subst index.
  rewrite XmcMod.map_get_set in H; inverts H.
  rewrite Int.unsigned_repr; auto with zarith.
  erewrite update_nth; eauto.
  erewrite nth_upd_neqrev; auto with zarith.
  rewrite XmcMod.map_get_set' in H; auto.
  eapply Hhl in H; eauto.
  destruct H as (H & H').
  do 2 try erewrite nth_upd_neqrev; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  int auto.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  eapply Z.mul_reg_r in Hf; subst.
  rewrite Int.repr_unsigned in *; tryfalse.
  auto with zarith.
  int auto.
  unfold RLH_XMpax_P.
  lets Hnth1': Hnth1; lets Hnth2' : Hnth2.
  splits; intros;
  assert (Hc:(Int.unsigned index = n) \/ (Int.unsigned index <> n)) by tauto;
  destruct Hc;
  try (subst n;
  eapply Hlh in Hnth1, Hnth2; eauto;
  destruct Hnth1 as (? & Hnth1); destruct Hnth2 as (? & Hnth2);
  unfolds in Hnth1; unfolds in Hnth2; simpl in Hnth1, Hnth2;
  rewrite Hnth1 in Hnth2; inverts Hnth2);
  try (eapply nth_upd_eq in H; inverts H);
  try rewrite Int.repr_unsigned in *; auto with zarith;
  try rewrite XmcMod.map_get_set; eauto;
  try eapply nth_upd_neq in H; try rewrite Hnth1' in H; try rewrite Hnth2' in H; inverts H;
  try rewrite XmcMod.map_get_set'; eauto;
  try eapply Hlh; eauto.
  introv Hf; subst.
  try rewrite Int.unsigned_repr in *; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  int auto.
  auto with zarith.
  introv Hf; subst.
  try rewrite Int.unsigned_repr in *; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  int auto.
Qed.

Lemma R_XMC_Mpax_P_update_hold_comm':
forall v v' (n: Z) vl l xmpax,
  0 <= n <= Int.max_unsigned ->
  nth_val (Z.to_nat(n*2)) vl = Some (Vint32 l) ->
  nth_val (Z.to_nat(n*2 + 1)) vl = Some (Vint32 v) ->
  R_XMpax_P vl xmpax ->
  R_XMpax_P
    (update_nth_val (Z.to_nat (n*2 + 1)) vl (Vint32 v'))
    (XmcMod.set xmpax ($ n) (l, v')).
Proof.
  introv Hrgn Hnth1 Hnth2 Hrp.
  unfold R_XMpax_P in *.
  destruct Hrp as (Hhl & Hlh).
  split.
  unfold RHL_XMpax_P.
  intros.
  assert (Hc:(index = Int.repr n) \/ (index <> Int.repr n)) by tauto.
  destruct Hc.
  subst index.
  rewrite XmcMod.map_get_set in H; inverts H.
  rewrite Int.unsigned_repr; auto with zarith.
  erewrite update_nth; eauto.
  erewrite nth_upd_neqrev; auto with zarith.
  rewrite XmcMod.map_get_set' in H; auto.
  eapply Hhl in H; eauto.
  destruct H as (H & H').
  do 2 try erewrite nth_upd_neqrev; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  rewrite Z.add_cancel_r in Hf.
  eapply Z.mul_reg_r in Hf; subst.
  rewrite Int.repr_unsigned in *; tryfalse.
  auto with zarith.
  unfold RLH_XMpax_P.
  lets Hnth1': Hnth1; lets Hnth2' : Hnth2.
  splits; intros;
  assert (Hc:(Int.unsigned index = n) \/ (Int.unsigned index <> n)) by tauto;
  destruct Hc;
  try (subst n;
  eapply Hlh in Hnth1, Hnth2; eauto;
  destruct Hnth1 as (? & Hnth1); destruct Hnth2 as (? & Hnth2);
  unfolds in Hnth1; unfolds in Hnth2; simpl in Hnth1, Hnth2;
  rewrite Hnth1 in Hnth2; inverts Hnth2);
  try (eapply nth_upd_eq in H; inverts H);
  try rewrite Int.repr_unsigned in *; auto with zarith;
  try rewrite XmcMod.map_get_set; eauto;
  try eapply nth_upd_neq in H; try rewrite Hnth1' in H; try rewrite Hnth2' in H; inverts H;
  try rewrite XmcMod.map_get_set'; eauto;
  try eapply Hlh; eauto.
  introv Hf; subst.
  try rewrite Int.unsigned_repr in *; auto with zarith.
  introv Hf; subst.
  try rewrite Int.unsigned_repr in *; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
  introv Hf; subst.
  try rewrite Int.unsigned_repr in *; auto with zarith.
  introv Hf.
  eapply Z2Nat.inj in Hf; auto with zarith.
Qed.

Lemma RH_SES_Mpax_P_update_hold_comm:
forall v' l n ses_mpax, 
  0 <= n < 8 ->
  RH_SES_Mpax_P ses_mpax ->
  RH_SES_Mpax_P (SesMod.set ses_mpax ($ n) (v', l)).
Proof.
  introv Hrgn Hrp.
  unfold RH_SES_Mpax_P in *.
  destruct Hrp as (Hnone & Hsome).
  split; introv Hidx;lets Hidx': Hidx; try eapply Hnone in Hidx; try eapply Hsome in Hidx;
  assert (Hc:(index = Int.repr n) \/ (index <> Int.repr n)) by tauto;
  destruct Hc;
  try subst index;
  try rewrite Int.unsigned_repr in Hidx';
  try change Int.max_unsigned with 4294967295 in *; auto with zarith.
  false.
  auto with zarith.
  rewrite SesMod.map_get_set'; auto.
  rewrite SesMod.map_get_set; eauto.
  rewrite SesMod.map_get_set'; auto.
Qed.

Lemma RH_SMS_Mpax_P_update_hold_comm:
forall v' l n sms_mpax, 
  0 <= n < 8 ->
  RH_SMS_Mpax_P sms_mpax ->
  RH_SMS_Mpax_P (SmsMod.set sms_mpax ($ n) (v', l)).
Proof.
  introv Hrgn Hrp.
  unfold RH_SMS_Mpax_P in *.
  destruct Hrp as (Hnone & Hsome).
  split; introv Hidx;lets Hidx': Hidx; try eapply Hnone in Hidx; try eapply Hsome in Hidx;
  assert (Hc:(index = Int.repr n) \/ (index <> Int.repr n)) by tauto;
  destruct Hc;
  try subst index;
  try rewrite Int.unsigned_repr in Hidx';
  try change Int.max_unsigned with 4294967295 in *; auto with zarith.
  false.
  auto with zarith.
  rewrite SmsMod.map_get_set'; auto.
  rewrite SmsMod.map_get_set; eauto.
  rewrite SmsMod.map_get_set'; auto.
Qed.

Lemma RH_XMpax_P_update_hold_comm:
forall v' l n xmpax, 
  0 <= n < 8 ->
  RH_XMpax_P xmpax ->
  RH_XMpax_P (XmcMod.set xmpax ($ n) (v', l)).
Proof.
  introv Hrgn Hrp.
  unfold RH_XMpax_P in *.
  destruct Hrp as (Hnone & Hsome).
  split; introv Hidx;lets Hidx': Hidx; try eapply Hnone in Hidx; try eapply Hsome in Hidx;
  assert (Hc:(index = Int.repr n) \/ (index <> Int.repr n)) by tauto;
  destruct Hc;
  try subst index;
  try rewrite Int.unsigned_repr in Hidx';
  try change Int.max_unsigned with 4294967295 in *; auto with zarith.
  false.
  auto with zarith.
  rewrite XmcMod.map_get_set'; auto.
  rewrite XmcMod.map_get_set; eauto.
  rewrite XmcMod.map_get_set'; auto.
Qed.

Lemma Int_testbit_paddress_eq:
forall (d : Z) d2,
31 - Z.of_nat (0 + 8) < d <= 31 ->
Int.testbit
  (if Int.ltu d2 ($ 2147483648)
   then d2 >>ᵢ $ 12
   else Int.or ((d2 -ᵢ $ 2147483648) >>ᵢ $ 12) ($ 8388608)) d = false.
Proof.
intros.
destruct (Int.ltu d2 ($ 2147483648)) eqn: eq1.
rewrite Int.bits_shru;
change (Int.zwordsize) with 32; auto with zarith.
change (Int.unsigned ($ 12)) with 12.
destruct (zlt (d + 12) 32) eqn: eq2; auto.
eapply Int.bits_size_2.
eapply Z.ge_le.
eapply Int.size_interval_2; auto with zarith.
rewrite Int.bits_or;
try rewrite Int.bits_shru;
change (Int.zwordsize) with 32; auto with zarith.
change (Int.unsigned ($ 12)) with 12.
destruct (zlt (d + 12) 32) eqn: eq2.
eapply orb_false_intro.
eapply Int.bits_size_2.
eapply Z.ge_le.
eapply Int.size_interval_2; auto with zarith.
eapply Int.bits_size_2.
eapply Z.ge_le.
eapply Int.size_interval_2; auto with zarith.
eapply orb_false_intro; auto.
eapply Int.bits_size_2.
eapply Z.ge_le.
eapply Int.size_interval_2; auto with zarith.
int auto.
change 8388608 with (two_p 23).
eapply two_p_monotone_strict ; eauto.
split; auto with zarith.
Qed.

Lemma Int_testbit_baddress_eq:
forall d3 (d0 : Z),
31 - Z.of_nat (12 + 0) < d0 <= 31 -> Int.testbit (d3 >>ᵢ $ 12) d0 = false.
Proof.
intros.
rewrite Int.bits_shru;
change (Int.zwordsize) with 32; auto with zarith.
change (Int.unsigned ($ 12)) with 12.
destruct (zlt (d0 + 12) 32) eqn: eq1; auto.
eapply Int.bits_size_2.
eapply Z.ge_le.
eapply Int.size_interval_2; auto with zarith.
Qed.

Lemma Int_testbit_segsize_eq:
forall rv_vsize (d0 : Z),
  (if Int.unsigned rv_vsize <=? Byte.max_unsigned then true else false) = true ->
  31 - Z.of_nat 20 < d0 <= 31 ->
  Int.testbit rv_vsize d0 = false.
Proof.
intros.
eapply Int.bits_size_2.
eapply Z.ge_le.
eapply Int.size_interval_2; auto with zarith.
eapply int_true_le255 in H.
split. apply Int.unsigned_range_2.
change (31 - Z.of_nat 20) with 11 in *.
eapply Z.le_lt_trans; eauto.
change 255 with ((two_p 8) - 1).
eapply Z.le_lt_trans with (m:= (two_p 8)); eauto.
auto with zarith.
eapply two_p_monotone_strict; auto with zarith.
Qed.

Lemma get_mpax_ses_segsize_set_rgn:
forall v d3 rv_vsize,
  (if Int.unsigned rv_vsize <=? Byte.max_unsigned then true else false) = true ->
Int.unsigned (get_mpax
                                (set_mpax_struct v (sesh_baddr :: sesh_segsize :: nil)
                                                                       (Vint32 (d3 >>ᵢ $ 12) :: Vint32 rv_vsize :: nil))
                                 sesh_segsize) <= Byte.max_unsigned.
Proof.
intros.
unfold set_mpax_struct.
rewrite get_set_sesh_neq.
lets Hrgn: int_true_le255 H.
rewrite get_set_segsize_eq; auto.
intros; eapply Int_testbit_segsize_eq; eauto.
intros; eapply Int_testbit_baddress_eq; eauto.
Qed.

Lemma get_mpax_sms_segsize_set_rgn:
forall v d3 rv_vsize,
  (if Int.unsigned rv_vsize <=? Byte.max_unsigned then true else false) = true ->
Int.unsigned (get_mpax
                                (set_mpax_struct v (smsh_baddr :: smsh_segsize :: nil)
                                                                       (Vint32 (d3 >>ᵢ $ 12) :: Vint32 rv_vsize :: nil))
                                 smsh_segsize) <= Byte.max_unsigned.
Proof.
intros.
unfold set_mpax_struct.
rewrite get_set_smsh_neq.
lets Hrgn: int_true_le255 H.
rewrite get_set_segsize_eq; auto.
intros; eapply Int_testbit_segsize_eq; eauto.
intros; eapply Int_testbit_baddress_eq; eauto.
Qed.

Lemma get_mpax_xmc_segsize_set_rgn:
forall v d3 rv_vsize,
  (if Int.unsigned rv_vsize <=? Byte.max_unsigned then true else false) = true ->
Int.unsigned (get_mpax
                                (set_mpax_struct v (xmc_baddr :: xmc_segsize :: nil)
                                                                       (Vint32 (d3 >>ᵢ $ 12) :: Vint32 rv_vsize :: nil))
                                 xmc_segsize) <= Byte.max_unsigned.
Proof.
intros.
unfold set_mpax_struct.
rewrite get_set_xmc_neq.
lets Hrgn: int_true_le255 H.
rewrite get_set_segsize_eq; auto.
intros; eapply Int_testbit_segsize_eq; eauto.
intros; eapply Int_testbit_baddress_eq; eauto.
Qed.

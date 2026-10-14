Require Import include_frm.
Require Import int_auto.
Require Import math_rewrite.

Open Scope code_scope.
Open Scope int_scope.
Open Scope Z_scope.

(* Parameter block_bit : Z.
Parameter block_bit_range :  Z.lt 0 block_bit /\ Z.lt block_bit Int.zwordsize.

Definition offset_bit:= Int.zwordsize - block_bit.
(* all block and offset, at least one bit *)

Definition int32_to_ptr (v: int32) :addrval :=
( Z.to_pos (Int.unsigned (Int.shru v (Int.repr offset_bit))), Int.zero_ext offset_bit v).

Definition ptr_to_int32 (adr: addrval) : int32:=
match adr with (b,i) => Int.or (Int.shl (Int.repr (Z.pos b)) (Int.repr offset_bit) ) (Int.zero_ext offset_bit i)  end.
 *)

Lemma offset_bit_range:
0 < offset_bit < Int.zwordsize.
Proof.
pose proof block_bit_range.
unfold offset_bit.
simpljoin. 
auto with zarith.
Qed.

Lemma offset_bit_rgn:
0 <= offset_bit <= Int.max_unsigned.
Proof.
pose proof block_bit_range.
unfold offset_bit.
simpljoin.
change (Int.max_unsigned) with 4294967295 in *;
change (Int.zwordsize) with 32 in *; 
auto with zarith.
Qed.

Lemma block_bit_two_p_rgn:
2 <= two_p block_bit <= Int.half_modulus.
Proof.
pose proof block_bit_range.
simpljoin.
split.
change 2 with (two_p 1).
eapply two_p_monotone; auto with zarith.
rewrite Int.half_modulus_power.
eapply two_p_monotone; auto with zarith.
Qed.

Lemma block_bit_two_p_rgn':
0 <= two_p block_bit <= Int.max_unsigned.
Proof.
pose proof block_bit_two_p_rgn.
unfold Int.max_unsigned.
rewrite Int.half_modulus_modulus.
simpljoin.
split; auto with zarith.
Qed.

Lemma offset_bit_two_p_rgn:
2 <= two_p offset_bit <= Int.half_modulus.
Proof.
pose proof offset_bit_range.
simpljoin.
split.
change 2 with (two_p 1).
eapply two_p_monotone; auto with zarith.
rewrite Int.half_modulus_power.
eapply two_p_monotone; auto with zarith.
Qed.

Lemma offset_bit_two_p_rgn':
0 <= two_p offset_bit <= Int.max_unsigned.
Proof.
pose proof offset_bit_two_p_rgn.
unfold Int.max_unsigned.
rewrite Int.half_modulus_modulus.
simpljoin.
split; auto with zarith.
Qed.

Lemma Int_shru_eq_zero :
forall x, Int.shru Int.zero x = Int.zero.
Proof.
intros.
rewrite Int.shru_div_two_p.
rewrite Int.unsigned_zero.
rewrite Zdiv_0_l.
rewrite int_auto.repr_zero.
auto.
Qed.

Lemma Int_zero_ext_eq_zero :
forall n, 0 <= n -> Int.zero_ext n Int.zero = Int.zero.
Proof.
intros.
rewrite Int.zero_ext_and; auto.
Qed.

Lemma int32_to_ptr_zero:
int32_to_ptr Int.zero = (1%positive, Int.zero).
Proof.
unfolds.
rewrite Int_shru_eq_zero.
rewrite Int_zero_ext_eq_zero; auto.
unfold offset_bit.
pose proof block_bit_range.
auto with zarith.
Qed.

Lemma Int_shru_lt_zero:
forall v x,
two_p (Int.unsigned x) <= Int.unsigned v ->
Int.unsigned x < Int.zwordsize ->
Int.ltu Int.zero (Int.shru v x) = true.
Proof.
intros.
rewrite Int.shru_div_two_p.
rewrite math_rewrite.Intlt_true_is_Zlt.
rewrite Int.unsigned_zero.
pose proof (Int.unsigned_range_2 v).
assert (Hrgn: 0 < two_p (Int.unsigned x)).
{ eapply Z.gt_lt.
   eapply two_p_gt_ZERO.
   apply Int.unsigned_range_2.
}
assert (Hlt: 0 < Int.unsigned v / two_p (Int.unsigned x)).
{
eapply Z.div_str_pos.
split; auto.
}
rewrite Int.unsigned_repr; auto.
split; auto with zarith.
eapply Z.div_le_upper_bound; auto.
simpljoin.
eapply Z.le_trans; eauto.
lets Hle: Zmult_le_compat_r 1  (two_p (Int.unsigned x)) Int.max_unsigned.
auto with zarith.
Qed.

Lemma int32_eq_ptr :
forall v,
two_p (offset_bit) <= Int.unsigned v ->
ptr_to_int32 (int32_to_ptr v) = v.
Proof.
introv Hle.
unfold int32_to_ptr, ptr_to_int32.
pose proof block_bit_range.
pose proof offset_bit_rgn.
unfold offset_bit in *.
rewrite Z2Pos.id.
2:{
       simpljoin.
       rewrite <- Int.unsigned_zero.
       eapply Int.ltu_inv.
       eapply Int_shru_lt_zero; rewrite Int.unsigned_repr;
       change (Int.max_unsigned) with 4294967295 in *;
       change (Int.zwordsize) with 32 in *; 
      auto with zarith.
}
rewrite Int.repr_unsigned.
rewrite Int.zero_ext_idem; auto with zarith.
eapply Int.same_bits_eq.
intros.
simpljoin.
rewrite Int.bits_or; auto.
rewrite Int.bits_zero_ext; auto.
rewrite Int.bits_shl; auto.
rewrite Int.unsigned_repr; auto.
destruct (zlt i (Int.zwordsize - block_bit)) eqn: eq1.
rewrite orb_false_l; auto.
rewrite Int.bits_shru;auto with zarith.
rewrite Int.unsigned_repr; auto.
rewrite Z.sub_add.
destruct (zlt i Int.zwordsize) eqn: eq2.
rewrite orb_false_r; auto.
false.
Qed.

Lemma Int_same_bits_eq':
  forall x y : int32,
  (forall i : Z, 0 <= i < Int.zwordsize -> Int.testbit x i = Int.testbit y i) <->
  x = y.
Proof.
intros.
split.
eapply Int.same_bits_eq; eauto.
intros. subst; auto.
Qed.

Lemma ptr_eq_int32 :
forall  b i,
0 < Z.pos b < two_p (block_bit) ->
0 <= Int.unsigned i < two_p offset_bit ->
int32_to_ptr (ptr_to_int32 (b,i)) = (b,i).
Proof.
unfold int32_to_ptr, ptr_to_int32.
introv Hrgnb Hrgni.
lets Hrgn_blk: block_bit_range.
lets Hrgn_off: offset_bit_rgn.
assert (Hrgnb': 0 <= Z.pos b <= Int.max_unsigned).
{
  split; auto with zarith.
  eapply Z.le_trans with (m:= two_p block_bit); auto with zarith.
  apply block_bit_two_p_rgn'.
}
assert (Hsize: Int.size ($ Z.pos b) <= block_bit).
{ rewrite <- Z.ge_le_iff.
   eapply Int.size_interval_2.
   simpljoin; auto with zarith.
   rewrite Int.unsigned_repr; auto with zarith.
}
assert (Hbit_eq: forall i, block_bit <= i -> Int.testbit ($ Z.pos b) i = false).
{
   intros.
   eapply Int.bits_size_2.
   auto with zarith.
}

assert (Heqb: Int.or ($ Z.pos b<<ᵢ$ offset_bit) (Int.zero_ext offset_bit i) >>ᵢ $ offset_bit = $ Z.pos b).
{
eapply Int.same_bits_eq.
intros.
rewrite Int.bits_shru; auto.
rewrite Int.unsigned_repr; auto.
destruct (zlt (i0 + offset_bit) Int.zwordsize) eqn: eq1.
rewrite Int.bits_or; try split; auto with zarith.
rewrite Int.bits_zero_ext; auto with zarith.
rewrite Int.bits_shl; auto with zarith.
rewrite Int.unsigned_repr; auto.
destruct (zlt (i0 + offset_bit) offset_bit) eqn: eq2.
false. auto with zarith.
rewrite Z.add_simpl_r.
rewrite orb_false_r; auto.
symmetry.
eapply Hbit_eq.
eapply Zplus_le_reg_l with (p := offset_bit).
unfold offset_bit.
rewrite Z.sub_add.
fold offset_bit.
auto with zarith.
}
rewrite Heqb.
erewrite pair_equal_spec with (A:= positive) (B:= int32).
split.
rewrite Int.unsigned_repr; auto.
eapply Int.same_bits_eq.
intros.
rewrite Int.bits_zero_ext; auto with zarith.
destruct (zlt i0 offset_bit) eqn: eq1.
rewrite Int.bits_or; try split; auto with zarith.
rewrite Int.bits_zero_ext; auto with zarith.
rewrite Int.bits_shl; auto with zarith.
rewrite Int.unsigned_repr; auto.
rewrite eq1.
rewrite orb_false_l; auto.
symmetry.
eapply Int.bits_size_2.
rewrite <- Z.ge_le_iff.
eapply Int.size_interval_2; auto with zarith.
simpljoin.
split; auto with zarith.
eapply Z.lt_le_trans; eauto.
eapply two_p_monotone; auto with zarith.
Qed.

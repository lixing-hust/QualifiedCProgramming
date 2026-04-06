
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Lists.List Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Load "../spec/131".

Definition problem_131_pre_z (n : Z) : Prop := problem_131_pre (Z.to_nat n).
Definition problem_131_spec_z (n r : Z) : Prop := problem_131_spec (Z.to_nat n) (Z.to_nat r).

Definition tail_odd_prod_nat (n : nat) : nat :=
	product (filter Nat.odd (get_digits n)).

Definition tail_odd_prod_z (n : Z) : Z :=
	Z.of_nat (tail_odd_prod_nat (Z.to_nat n)).

Definition digits_state_z (n prod has : Z) : Z :=
	if Z.eqb has 0 then Z.of_nat (digits_impl (Z.to_nat n))
	else prod * tail_odd_prod_z n.

Lemma div10_le_pred_nat : forall n, n >= 1 -> n / 10 <= n - 1.
Proof.
	intros n Hn.
	enough (n / 10 < n) by lia.
	apply Nat.div_lt; lia.
Qed.

Lemma get_digits_helper_fuel_sufficient : forall n fuel1 fuel2,
	fuel1 >= n -> fuel2 >= n ->
	get_digits_helper n fuel1 = get_digits_helper n fuel2.
Proof.
	induction n as [n IH] using lt_wf_ind.
	intros fuel1 fuel2 Hf1 Hf2.
	destruct n as [|n'].
	- destruct fuel1; destruct fuel2; reflexivity.
	- destruct fuel1 as [|f1']; [lia|].
		destruct fuel2 as [|f2']; [lia|].
		set (q := S n' / 10).
		assert (Hlt : q < S n') by (unfold q; apply Nat.div_lt; lia).
		assert (H1 : f1' >= q) by (pose proof (div10_le_pred_nat (S n') ltac:(lia)); unfold q; lia).
		assert (H2 : f2' >= q) by (pose proof (div10_le_pred_nat (S n') ltac:(lia)); unfold q; lia).
		cbn [get_digits_helper].
		f_equal.
		apply IH; assumption.
Qed.

Lemma get_digits_step : forall n,
	n >= 1 ->
	get_digits n = (n mod 10) :: get_digits (n / 10).
Proof.
	intros n Hn.
	destruct n as [|n']; [lia|].
	unfold get_digits at 1.
	cbn [get_digits_helper].
	set (q := S n' / 10).
	assert (Hq : n' >= q).
	{ unfold q. pose proof (div10_le_pred_nat (S n') ltac:(lia)). lia. }
	rewrite (get_digits_helper_fuel_sufficient q n' q) by lia.
	reflexivity.
Qed.

Lemma odd_true_ge_1 : forall d, Nat.odd d = true -> d >= 1.
Proof.
	intros d Hodd.
	apply Nat.odd_spec in Hodd.
	destruct Hodd as [k Hk].
	rewrite Hk; lia.
Qed.

Lemma product_filter_odd_ge_1 : forall l,
	product (filter Nat.odd l) >= 1.
Proof.
	induction l as [|a l IH]; simpl.
	- lia.
	- destruct (Nat.odd a) eqn:Hodd; simpl.
		+ assert (a >= 1) by (apply odd_true_ge_1; exact Hodd).
			nia.
		+ exact IH.
Qed.

Lemma tail_odd_prod_nat_ge_1 : forall n,
	tail_odd_prod_nat n >= 1.
Proof.
	intros n.
	unfold tail_odd_prod_nat.
	apply product_filter_odd_ge_1.
Qed.

Lemma tail_step_odd : forall n,
	n >= 1 -> Nat.odd (n mod 10) = true ->
	tail_odd_prod_nat n = (n mod 10) * tail_odd_prod_nat (n / 10).
Proof.
	intros n Hn Hodd.
	unfold tail_odd_prod_nat.
	set (d := n mod 10).
	set (q := n / 10).
	assert (Hstep : get_digits n = d :: get_digits q).
	{ subst d q. apply get_digits_step. exact Hn. }
	rewrite Hstep.
	cbn [filter product].
	assert (Hdodd : Nat.odd d = true) by (subst d; exact Hodd).
	rewrite Hdodd. simpl. subst d q. reflexivity.
Qed.

Lemma tail_step_even : forall n,
	n >= 1 -> Nat.odd (n mod 10) = false ->
	tail_odd_prod_nat n = tail_odd_prod_nat (n / 10).
Proof.
	intros n Hn Heven.
	unfold tail_odd_prod_nat.
	set (d := n mod 10).
	set (q := n / 10).
	assert (Hstep : get_digits n = d :: get_digits q).
	{ subst d q. apply get_digits_step. exact Hn. }
	rewrite Hstep.
	cbn [filter product].
	assert (Hdeven : Nat.odd d = false) by (subst d; exact Heven).
	rewrite Hdeven. simpl. subst d q. reflexivity.
Qed.

Lemma digits_impl_step_odd : forall n,
	n >= 1 -> Nat.odd (n mod 10) = true ->
	digits_impl n = (n mod 10) * tail_odd_prod_nat (n / 10).
Proof.
	intros n Hn Hodd.
	unfold digits_impl.
	set (d := n mod 10).
	set (q := n / 10).
	assert (Hstep : get_digits n = d :: get_digits q).
	{ subst d q. apply get_digits_step. exact Hn. }
	rewrite Hstep.
	cbn [filter product].
	assert (Hdodd : Nat.odd d = true) by (subst d; exact Hodd).
	rewrite Hdodd. simpl. subst d q. reflexivity.
Qed.

Lemma digits_impl_step_even : forall n,
	n >= 1 -> Nat.odd (n mod 10) = false ->
	digits_impl n = digits_impl (n / 10).
Proof.
	intros n Hn Heven.
	unfold digits_impl.
	set (d := n mod 10).
	set (q := n / 10).
	assert (Hstep : get_digits n = d :: get_digits q).
	{ subst d q. apply get_digits_step. exact Hn. }
	rewrite Hstep.
	cbn [filter product].
	assert (Hdeven : Nat.odd d = false) by (subst d; exact Heven).
	rewrite Hdeven. simpl. subst d q. reflexivity.
Qed.

Local Open Scope Z_scope.

Lemma Z2Nat_div10 : forall (n : Z), 0 <= n ->
	Z.to_nat (n / 10) = (Z.to_nat n / 10)%nat.
Proof.
	intros n Hn.
	rewrite Z2Nat.inj_div by lia.
	reflexivity.
Qed.

Lemma Z2Nat_mod10 : forall (n : Z), 0 <= n ->
	Z.to_nat (n mod 10) = (Z.to_nat n mod 10)%nat.
Proof.
	intros n Hn.
	rewrite Z2Nat.inj_mod by lia.
	reflexivity.
Qed.

Lemma Zquot_eq_Zdiv_pos : forall a b, 0 <= a -> 0 < b -> Z.quot a b = a / b.
Proof.
	intros a b Ha Hb.
	apply Zquot_Zdiv_pos; lia.
Qed.

Lemma rem_rem10_eq_mod2 : forall n,
	0 <= n ->
	Z.rem (Z.rem n 10) 2 = (n mod 10) mod 2.
Proof.
	intros n Hn.
	rewrite (Z.rem_mod_nonneg n 10) by lia.
	assert (Hm : 0 <= n mod 10) by (apply Z.mod_pos_bound; lia).
	rewrite (Z.rem_mod_nonneg (n mod 10) 2) by lia.
	reflexivity.
Qed.

Lemma cstyle_odd_to_nat_odd : forall n,
	n > 0 -> Z.rem (Z.rem n 10) 2 = 1 ->
	Nat.odd (Z.to_nat n mod 10)%nat = true.
Proof.
	intros n Hn Hodd.
	remember (n mod 10) as m eqn:Hm.
	assert (Hmrange : 0 <= m < 10).
	{ rewrite Hm. apply Z.mod_pos_bound; lia. }
	assert (Hmod : m mod 2 = 1).
	{
		rewrite Hm.
		rewrite <- rem_rem10_eq_mod2 by lia.
		exact Hodd.
	}
	rewrite <- Z2Nat_mod10 by lia.
	rewrite <- Hm.
	assert (Hcases : m = 0 \/ m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7 \/ m = 8 \/ m = 9) by lia.
	destruct Hcases as [Hm0|Hcases].
	{ rewrite Hm0 in Hmod. vm_compute in Hmod. discriminate. }
	destruct Hcases as [Hm1|Hcases]. { rewrite Hm1. reflexivity. }
	destruct Hcases as [Hm2|Hcases].
	{ rewrite Hm2 in Hmod. vm_compute in Hmod. discriminate. }
	destruct Hcases as [Hm3|Hcases]. { rewrite Hm3. reflexivity. }
	destruct Hcases as [Hm4|Hcases].
	{ rewrite Hm4 in Hmod. vm_compute in Hmod. discriminate. }
	destruct Hcases as [Hm5|Hcases]. { rewrite Hm5. reflexivity. }
	destruct Hcases as [Hm6|Hcases].
	{ rewrite Hm6 in Hmod. vm_compute in Hmod. discriminate. }
	destruct Hcases as [Hm7|Hcases]. { rewrite Hm7. reflexivity. }
	destruct Hcases as [Hm8|Hm9].
	{ rewrite Hm8 in Hmod. vm_compute in Hmod. discriminate. }
	rewrite Hm9. reflexivity.
Qed.

Lemma cstyle_even_to_nat_even : forall n,
	n > 0 -> Z.rem (Z.rem n 10) 2 <> 1 ->
	Nat.odd (Z.to_nat n mod 10)%nat = false.
Proof.
	intros n Hn Heven.
	remember (n mod 10) as m eqn:Hm.
	assert (Hmrange : 0 <= m < 10).
	{ rewrite Hm. apply Z.mod_pos_bound; lia. }
	assert (Hmodne : m mod 2 <> 1).
	{
		intro Hm1.
		apply Heven.
		rewrite Hm in Hm1.
		rewrite rem_rem10_eq_mod2 by lia.
		exact Hm1.
	}
	rewrite <- Z2Nat_mod10 by lia.
	rewrite <- Hm.
	assert (Hcases : m = 0 \/ m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7 \/ m = 8 \/ m = 9) by lia.
	destruct Hcases as [Hm0|Hcases]. { rewrite Hm0. reflexivity. }
	destruct Hcases as [Hm1|Hcases].
	{ exfalso. apply Hmodne. rewrite Hm1. reflexivity. }
	destruct Hcases as [Hm2|Hcases]. { rewrite Hm2. reflexivity. }
	destruct Hcases as [Hm3|Hcases].
	{ exfalso. apply Hmodne. rewrite Hm3. reflexivity. }
	destruct Hcases as [Hm4|Hcases]. { rewrite Hm4. reflexivity. }
	destruct Hcases as [Hm5|Hcases].
	{ exfalso. apply Hmodne. rewrite Hm5. reflexivity. }
	destruct Hcases as [Hm6|Hcases]. { rewrite Hm6. reflexivity. }
	destruct Hcases as [Hm7|Hcases].
	{ exfalso. apply Hmodne. rewrite Hm7. reflexivity. }
	destruct Hcases as [Hm8|Hm9]. { rewrite Hm8. reflexivity. }
	exfalso. apply Hmodne. rewrite Hm9. reflexivity.
Qed.

Lemma tail_step_odd_cstyle : forall n,
	n > 0 -> Z.rem (Z.rem n 10) 2 = 1 ->
	tail_odd_prod_z n = Z.rem n 10 * tail_odd_prod_z (Z.quot n 10).
Proof.
	intros n Hn Hodd.
	unfold tail_odd_prod_z.
	rewrite Zquot_eq_Zdiv_pos by lia.
	rewrite Z.rem_mod_nonneg by lia.
	rewrite Z2Nat_div10 by lia.
	assert (Hnat : (Z.to_nat n >= 1)%nat) by lia.
	assert (Hoddnat : Nat.odd (Z.to_nat n mod 10)%nat = true).
	{ apply cstyle_odd_to_nat_odd; assumption. }
	rewrite (tail_step_odd (Z.to_nat n) Hnat Hoddnat).
	rewrite Nat2Z.inj_mul.
	rewrite Nat2Z.inj_mod.
	rewrite Z2Nat.id by lia.
	replace (Z.of_nat (Z.to_nat n mod 10)) with (Z.of_nat (Z.to_nat (n mod 10))).
	2:{ rewrite Z2Nat_mod10 by lia. reflexivity. }
	replace (Z.of_nat (Z.to_nat (n mod 10))) with (n mod 10).
	2:{ symmetry. apply Z2Nat.id. apply Z.mod_pos_bound; lia. }
	reflexivity.
Qed.

Lemma tail_step_even_cstyle : forall n,
	n > 0 -> Z.rem (Z.rem n 10) 2 <> 1 ->
	tail_odd_prod_z n = tail_odd_prod_z (Z.quot n 10).
Proof.
	intros n Hn Heven.
	unfold tail_odd_prod_z.
	rewrite Zquot_eq_Zdiv_pos by lia.
	rewrite Z2Nat_div10 by lia.
	assert (Hnat : (Z.to_nat n >= 1)%nat) by lia.
	assert (Heven_nat : Nat.odd (Z.to_nat n mod 10)%nat = false).
	{ apply cstyle_even_to_nat_even; assumption. }
	rewrite (tail_step_even (Z.to_nat n) Hnat Heven_nat).
	reflexivity.
Qed.

Lemma digits_impl_step_odd_cstyle : forall n,
	n > 0 -> Z.rem (Z.rem n 10) 2 = 1 ->
	Z.of_nat (digits_impl (Z.to_nat n)) =
	Z.rem n 10 * tail_odd_prod_z (Z.quot n 10).
Proof.
	intros n Hn Hodd.
	rewrite Zquot_eq_Zdiv_pos by lia.
	rewrite Z.rem_mod_nonneg by lia.
	assert (Hnat : (Z.to_nat n >= 1)%nat) by lia.
	assert (Hoddnat : Nat.odd (Z.to_nat n mod 10)%nat = true).
	{ apply cstyle_odd_to_nat_odd; assumption. }
	rewrite (digits_impl_step_odd (Z.to_nat n) Hnat Hoddnat).
	unfold tail_odd_prod_z.
	rewrite Z2Nat_div10 by lia.
	rewrite Nat2Z.inj_mul.
	rewrite Nat2Z.inj_mod.
	rewrite Z2Nat.id by lia.
	replace (Z.of_nat (Z.to_nat n mod 10)) with (Z.of_nat (Z.to_nat (n mod 10))).
	2:{ rewrite Z2Nat_mod10 by lia. reflexivity. }
	replace (Z.of_nat (Z.to_nat (n mod 10))) with (n mod 10).
	2:{ symmetry. apply Z2Nat.id. apply Z.mod_pos_bound; lia. }
	reflexivity.
Qed.

Lemma digits_impl_step_even_cstyle : forall n,
	n > 0 -> Z.rem (Z.rem n 10) 2 <> 1 ->
	Z.of_nat (digits_impl (Z.to_nat n)) =
	Z.of_nat (digits_impl (Z.to_nat (Z.quot n 10))).
Proof.
	intros n Hn Heven.
	rewrite Zquot_eq_Zdiv_pos by lia.
	rewrite Z2Nat_div10 by lia.
	assert (Hnat : (Z.to_nat n >= 1)%nat) by lia.
	assert (Heven_nat : Nat.odd (Z.to_nat n mod 10)%nat = false).
	{ apply cstyle_even_to_nat_even; assumption. }
	rewrite (digits_impl_step_even (Z.to_nat n) Hnat Heven_nat).
	reflexivity.
Qed.

Lemma tail_odd_prod_z_ge_rem_digit : forall n,
	n > 0 -> Z.rem (Z.rem n 10) 2 = 1 ->
	Z.rem n 10 <= tail_odd_prod_z n.
Proof.
	intros n Hn Hodd.
	rewrite tail_step_odd_cstyle by assumption.
	assert (Htail_ge_1 : tail_odd_prod_z (Z.quot n 10) >= 1).
	{
		unfold tail_odd_prod_z.
		pose proof (tail_odd_prod_nat_ge_1 (Z.to_nat (Z.quot n 10))).
		lia.
	}
	assert (Hrem_nonneg : 0 <= Z.rem n 10).
	{
		rewrite Z.rem_mod_nonneg by lia.
		apply Z.mod_pos_bound; lia.
	}
	nia.
Qed.

Lemma digits_state_init_spec : forall n,
	0 <= n -> problem_131_spec_z n (digits_state_z n 1 0).
Proof.
	intros n Hn.
	unfold problem_131_spec_z, problem_131_spec, digits_state_z.
	rewrite Z.eqb_refl.
	rewrite Nat2Z.id.
	reflexivity.
Qed.

Lemma digits_state_step_odd_preserve : forall n prod has,
	n > 0 -> 0 <= has <= 1 -> (has = 0 -> prod = 1) ->
	Z.rem (Z.rem n 10) 2 = 1 ->
	digits_state_z n prod has =
	digits_state_z (Z.quot n 10) (prod * Z.rem n 10) 1.
Proof.
	intros n prod has Hn Hhas Hhprod Hodd.
	unfold digits_state_z.
	destruct (Z.eqb has 0) eqn:H0.
	- apply Z.eqb_eq in H0. subst has.
		assert (prod = 1) by (apply Hhprod; reflexivity).
		subst prod.
		rewrite digits_impl_step_odd_cstyle by assumption.
		simpl.
		destruct (Z.rem n 10); reflexivity.
	- apply Z.eqb_neq in H0.
		rewrite tail_step_odd_cstyle by assumption.
		simpl.
		ring.
Qed.

Lemma digits_state_step_even_preserve : forall n prod has,
	n > 0 -> 0 <= has <= 1 -> (has = 0 -> prod = 1) ->
	Z.rem (Z.rem n 10) 2 <> 1 ->
	digits_state_z n prod has =
	digits_state_z (Z.quot n 10) prod has.
Proof.
	intros n prod has Hn Hhas Hhprod Heven.
	unfold digits_state_z.
	destruct (Z.eqb has 0) eqn:H0.
	- apply Z.eqb_eq in H0. subst has.
		rewrite digits_impl_step_even_cstyle by assumption.
		simpl.
		reflexivity.
	- apply Z.eqb_neq in H0.
		rewrite tail_step_even_cstyle by assumption.
		simpl.
		reflexivity.
Qed.


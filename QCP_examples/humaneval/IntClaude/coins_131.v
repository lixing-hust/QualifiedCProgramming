Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Lists.List Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Wf_nat.
Import ListNotations.

Load "../../../../Coins/spec/human/input/131".

Definition problem_131_pre_z (n : Z) : Prop := problem_131_pre (Z.to_nat n).
Definition problem_131_spec_z (n r : Z) : Prop := problem_131_spec (Z.to_nat n) (Z.to_nat r).

(* ================================================================ *)
(* Helper: model of the C loop computation                          *)
(* digits_loop_nat fuel n acc has = final result of the C function  *)
(*   given remaining digits in n, accumulated product acc,          *)
(*   and whether an odd digit has been seen (has)                   *)
(* ================================================================ *)

Fixpoint digits_loop_nat (fuel n : nat) (acc : nat) (has : bool) : nat :=
  match fuel with
  | 0 => if has then acc else 0
  | S f' =>
    match n with
    | 0 => if has then acc else 0
    | _ =>
      let d := n mod 10 in
      if Nat.odd d
      then digits_loop_nat f' (n / 10) (acc * d) true
      else digits_loop_nat f' (n / 10) acc has
    end
  end.

(* Product of odd digits, returning 1 when there are none *)
Fixpoint raw_odd_prod_nat (fuel n : nat) : nat :=
  match fuel with
  | 0 => 1
  | S f' =>
    match n with
    | 0 => 1
    | _ =>
      let d := n mod 10 in
      let rest := raw_odd_prod_nat f' (n / 10) in
      if Nat.odd d then d * rest else rest
    end
  end.

(* Z-level wrappers *)
Definition digits_loop_z (n acc has : Z) : Z :=
  Z.of_nat (digits_loop_nat (Z.to_nat n) (Z.to_nat n) (Z.to_nat acc) (Z.eqb has 1)).

Definition raw_odd_prod_z (n : Z) : Z :=
  Z.of_nat (raw_odd_prod_nat (Z.to_nat n) (Z.to_nat n)).

(* ================================================================ *)
(* Fuel sufficiency lemmas                                          *)
(* ================================================================ *)

Lemma div10_lt : forall n, n >= 1 -> n / 10 < n.
Proof. intros. apply Nat.div_lt; lia. Qed.

Lemma div10_le_pred : forall n, n >= 1 -> n / 10 <= n - 1.
Proof.
  intros.
  enough (n / 10 < n) by lia.
  apply Nat.div_lt; lia.
Qed.

Lemma digits_loop_fuel_sufficient : forall n fuel1 fuel2 acc has,
  fuel1 >= n -> fuel2 >= n ->
  digits_loop_nat fuel1 n acc has = digits_loop_nat fuel2 n acc has.
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros fuel1 fuel2 acc has Hf1 Hf2.
  destruct n as [|n'].
  - destruct fuel1; destruct fuel2; simpl; reflexivity.
  - destruct fuel1 as [|f1']; [lia|].
    destruct fuel2 as [|f2']; [lia|].
    set (d := S n' mod 10). set (q := S n' / 10).
    assert (Hlt : q < S n') by (unfold q; apply div10_lt; lia).
    assert (Hle1 : f1' >= q) by (pose proof (div10_le_pred (S n') ltac:(lia)); unfold q; lia).
    assert (Hle2 : f2' >= q) by (pose proof (div10_le_pred (S n') ltac:(lia)); unfold q; lia).
    cbn [digits_loop_nat]. fold d. fold q.
    destruct (Nat.odd d); apply IH; assumption.
Qed.

Lemma raw_odd_prod_fuel_sufficient : forall n fuel1 fuel2,
  fuel1 >= n -> fuel2 >= n ->
  raw_odd_prod_nat fuel1 n = raw_odd_prod_nat fuel2 n.
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros fuel1 fuel2 Hf1 Hf2.
  destruct n as [|n'].
  - destruct fuel1; destruct fuel2; simpl; reflexivity.
  - destruct fuel1 as [|f1']; [lia|].
    destruct fuel2 as [|f2']; [lia|].
    set (d := S n' mod 10). set (q := S n' / 10).
    assert (Hlt : q < S n') by (unfold q; apply div10_lt; lia).
    assert (Hle1 : f1' >= q) by (pose proof (div10_le_pred (S n') ltac:(lia)); unfold q; lia).
    assert (Hle2 : f2' >= q) by (pose proof (div10_le_pred (S n') ltac:(lia)); unfold q; lia).
    cbn [raw_odd_prod_nat]. fold d. fold q.
    destruct (Nat.odd d); [f_equal|]; apply IH; assumption.
Qed.

Lemma get_digits_helper_fuel_sufficient : forall n fuel1 fuel2,
  fuel1 >= n -> fuel2 >= n ->
  get_digits_helper n fuel1 = get_digits_helper n fuel2.
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros fuel1 fuel2 Hf1 Hf2.
  destruct n as [|n'].
  - destruct fuel1; destruct fuel2; simpl; reflexivity.
  - destruct fuel1 as [|f1']; [lia|].
    destruct fuel2 as [|f2']; [lia|].
    set (d := S n' mod 10). set (q := S n' / 10).
    assert (Hlt : q < S n') by (unfold q; apply div10_lt; lia).
    assert (Hle1 : f1' >= q) by (pose proof (div10_le_pred (S n') ltac:(lia)); unfold q; lia).
    assert (Hle2 : f2' >= q) by (pose proof (div10_le_pred (S n') ltac:(lia)); unfold q; lia).
    cbn [get_digits_helper]. fold d. fold q.
    f_equal. apply IH; assumption.
Qed.

(* ================================================================ *)
(* Step / base lemmas (nat level)                                   *)
(* ================================================================ *)

Lemma digits_loop_nat_zero : forall fuel acc has,
  digits_loop_nat fuel 0 acc has = if has then acc else 0.
Proof. destruct fuel; reflexivity. Qed.

Lemma digits_loop_nat_step : forall n acc has,
  n >= 1 ->
  digits_loop_nat n n acc has =
    let d := n mod 10 in
    if Nat.odd d
    then digits_loop_nat (n / 10) (n / 10) (acc * d) true
    else digits_loop_nat (n / 10) (n / 10) acc has.
Proof.
  intros n acc has Hn.
  destruct n as [|n']; [lia|].
  set (d := S n' mod 10). set (q := S n' / 10).
  cbn [digits_loop_nat]. fold d. fold q.
  destruct (Nat.odd d);
  apply digits_loop_fuel_sufficient;
  pose proof (div10_le_pred (S n') ltac:(lia)); unfold q; lia.
Qed.

Lemma raw_odd_prod_nat_zero : forall fuel,
  raw_odd_prod_nat fuel 0 = 1.
Proof. destruct fuel; reflexivity. Qed.

Lemma raw_odd_prod_nat_step : forall n,
  n >= 1 ->
  raw_odd_prod_nat n n =
    let d := n mod 10 in
    let rest := raw_odd_prod_nat (n / 10) (n / 10) in
    if Nat.odd d then d * rest else rest.
Proof.
  intros n Hn. destruct n as [|n']; [lia|].
  set (d := S n' mod 10). set (q := S n' / 10).
  cbn [raw_odd_prod_nat]. fold d. fold q.
  destruct (Nat.odd d); [f_equal|];
  apply raw_odd_prod_fuel_sufficient;
  pose proof (div10_le_pred (S n') ltac:(lia)); unfold q; lia.
Qed.

(* raw_odd_prod_nat equals product of odd digits via get_digits *)
Lemma raw_odd_prod_is_product_filter : forall n,
  raw_odd_prod_nat n n = product (filter Nat.odd (get_digits n)).
Proof.
  induction n as [n IH] using lt_wf_ind.
  destruct n as [|n'].
  - simpl. reflexivity.
  - rewrite raw_odd_prod_nat_step by lia.
    unfold get_digits.
    set (d := S n' mod 10). set (q := S n' / 10).
    assert (Hlt : q < S n') by (unfold q; apply div10_lt; lia).
    cbn [get_digits_helper]. fold d. fold q.
    (* normalize fuel and apply IH *)
    assert (Hfuel : get_digits_helper q n' = get_digits_helper q q).
    { apply get_digits_helper_fuel_sufficient; unfold q; lia. }
    specialize (IH q Hlt). unfold get_digits in IH.
    rewrite Hfuel. rewrite IH.
    destruct (Nat.odd d) eqn:Hodd; simpl; rewrite Hodd; simpl; ring.
Qed.

(* ================================================================ *)
(* Equivalence: digits_loop_nat n n 1 false = digits_impl n        *)
(* ================================================================ *)

Lemma digits_loop_general : forall n acc has,
  digits_loop_nat n n acc has =
    let odds := filter Nat.odd (get_digits n) in
    if (has || negb (Nat.eqb (length odds) 0))%bool
    then acc * product odds
    else 0.
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros acc has.
  destruct n as [|n'].
  - (* n = 0 *)
    simpl. destruct has; simpl; [lia|reflexivity].
  - (* n = S n' *)
    rewrite digits_loop_nat_step by lia.
    set (d := S n' mod 10).
    set (rest_n := S n' / 10).
    assert (Hlt : rest_n < S n') by (unfold rest_n; apply div10_lt; lia).
    unfold get_digits.
    cbn [get_digits_helper]. fold d. fold rest_n.
    assert (Hfuel : get_digits_helper rest_n n' = get_digits_helper rest_n rest_n).
    { apply get_digits_helper_fuel_sufficient; unfold rest_n; lia. }
    rewrite Hfuel.
    set (odds_rest := filter Nat.odd (get_digits_helper rest_n rest_n)).
    specialize (IH rest_n Hlt).
    unfold get_digits in IH. fold odds_rest in IH.
    (* Normalize IH: eliminate the let binding *)
    assert (IH' : forall a h, digits_loop_nat rest_n rest_n a h =
      if (h || negb (Nat.eqb (length odds_rest) 0))%bool
      then a * product odds_rest else 0).
    { intros a h. specialize (IH a h). cbn beta in IH. exact IH. }
    clear IH.
    rewrite IH', IH'.
    destruct (Nat.odd d) eqn:Hodd.
    + (* d is odd *)
      unfold odds_rest. cbn [filter]. rewrite Hodd.
      cbn [length Nat.eqb Bool.negb Bool.orb filter product].
      ring.
    + (* d is even *)
      unfold odds_rest. cbn [filter]. rewrite Hodd.
      destruct (Nat.eqb (length (filter Nat.odd (get_digits_helper rest_n rest_n))) 0) eqn:Hlen;
      simpl; reflexivity.
Qed.

Lemma digits_loop_equiv : forall n,
  digits_loop_nat n n 1 false = digits_impl n.
Proof.
  intros n.
  rewrite digits_loop_general.
  unfold digits_impl.
  set (odds := filter Nat.odd (get_digits n)).
  destruct odds as [|h t]; simpl; lia.
Qed.

(* ================================================================ *)
(* raw_odd_prod properties                                          *)
(* ================================================================ *)

Lemma raw_odd_prod_nat_ge_1 : forall n,
  raw_odd_prod_nat n n >= 1.
Proof.
  induction n as [n IH] using lt_wf_ind.
  destruct n as [|n']; [simpl; lia|].
  rewrite raw_odd_prod_nat_step by lia.
  set (rest_n := S n' / 10).
  assert (Hlt : rest_n < S n') by (unfold rest_n; apply div10_lt; lia).
  specialize (IH rest_n Hlt).
  destruct (Nat.odd (S n' mod 10)).
  - assert (S n' mod 10 >= 1) by (apply Nat.mod_bound_pos; lia). lia.
  - lia.
Qed.

Lemma raw_odd_prod_nat_step_odd : forall n,
  n >= 1 -> Nat.odd (n mod 10) = true ->
  raw_odd_prod_nat n n = (n mod 10) * raw_odd_prod_nat (n / 10) (n / 10).
Proof.
  intros. rewrite raw_odd_prod_nat_step by lia.
  rewrite H0. reflexivity.
Qed.

Lemma raw_odd_prod_nat_step_even : forall n,
  n >= 1 -> Nat.odd (n mod 10) = false ->
  raw_odd_prod_nat n n = raw_odd_prod_nat (n / 10) (n / 10).
Proof.
  intros. rewrite raw_odd_prod_nat_step by lia.
  rewrite H0. reflexivity.
Qed.

(* ================================================================ *)
(* Z-level lemmas for use in manual proofs                          *)
(* ================================================================ *)

Lemma Z2Nat_div10 : forall n, 0 <= n ->
  Z.to_nat (n / 10) = Z.to_nat n / 10.
Proof.
  intros. rewrite Z2Nat.inj_div by lia. reflexivity.
Qed.

Lemma Z2Nat_mod10 : forall n, 0 <= n ->
  Z.to_nat (n mod 10) = Z.to_nat n mod 10.
Proof.
  intros. rewrite Z2Nat.inj_mod by lia. reflexivity.
Qed.

(* Key: Nat.odd and Z.odd correspondence for mod 10 results *)
Lemma odd_mod10_nat_Z : forall n, 0 <= n ->
  Nat.odd (Z.to_nat n mod 10) = Z.odd (n mod 10).
Proof.
  intros.
  rewrite <- Z2Nat_mod10 by lia.
  rewrite Nat2Z.inj_odd.
  f_equal. rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia).
  reflexivity.
Qed.

(* Z.rem and Z.modulo for positive arguments *)
Lemma Zrem_Zmod_pos : forall a b, 0 <= a -> 0 < b ->
  Z.rem a b = Z.modulo a b.
Proof.
  intros. rewrite Z.rem_mod_nonneg; lia.
Qed.

(* Step lemma for digits_loop_z: odd digit *)
Lemma digits_loop_z_step_odd : forall n acc has,
  n > 0 -> acc >= 0 -> 0 <= has <= 1 ->
  Z.odd (n mod 10) = true ->
  digits_loop_z n acc has = digits_loop_z (n / 10) (acc * (n mod 10)) 1.
Proof.
  intros n acc has Hn Hacc Hhas Hodd.
  unfold digits_loop_z.
  rewrite Z2Nat_div10 by lia.
  replace (Z.eqb 1 1) with true by reflexivity.
  assert (Hnat : Z.to_nat n >= 1) by lia.
  rewrite digits_loop_nat_step by lia.
  rewrite <- odd_mod10_nat_Z by lia. rewrite Hodd.
  (* Convert acc * (n mod 10) *)
  rewrite Z2Nat.inj_mul by (try lia; apply Z.mod_pos_bound; lia).
  rewrite Z2Nat_mod10 by lia.
  (* fuel sufficiency *)
  apply f_equal.
  apply digits_loop_fuel_sufficient; lia.
Qed.

(* Step lemma for digits_loop_z: even digit *)
Lemma digits_loop_z_step_even : forall n acc has,
  n > 0 -> acc >= 0 -> 0 <= has <= 1 ->
  Z.odd (n mod 10) = false ->
  digits_loop_z n acc has = digits_loop_z (n / 10) acc has.
Proof.
  intros n acc has Hn Hacc Hhas Heven.
  unfold digits_loop_z.
  rewrite Z2Nat_div10 by lia.
  assert (Hnat : Z.to_nat n >= 1) by lia.
  rewrite digits_loop_nat_step by lia.
  rewrite <- odd_mod10_nat_Z by lia. rewrite Heven.
  apply f_equal.
  assert (Z.eqb has 1 = Z.eqb has 1) by reflexivity.
  apply digits_loop_fuel_sufficient; lia.
Qed.

(* Base lemma: digits_loop_z at n=0 *)
Lemma digits_loop_z_zero_false : forall acc,
  acc >= 0 -> digits_loop_z 0 acc 0 = 0.
Proof.
  intros. unfold digits_loop_z. simpl. reflexivity.
Qed.

Lemma digits_loop_z_zero_true : forall acc,
  acc >= 0 -> digits_loop_z 0 acc 1 = acc.
Proof.
  intros. unfold digits_loop_z. simpl.
  rewrite Nat2Z.id. reflexivity.
Qed.

(* Initialization: digits_loop_z establishes the spec *)
Lemma digits_loop_z_init : forall n,
  0 <= n ->
  Z.to_nat (digits_loop_z n 1 0) = digits_impl (Z.to_nat n).
Proof.
  intros. unfold digits_loop_z. simpl.
  rewrite Nat2Z.id.
  rewrite digits_loop_equiv. reflexivity.
Qed.

(* Step lemma for raw_odd_prod_z: odd digit *)
Lemma raw_odd_prod_z_step_odd : forall n,
  n > 0 -> Z.odd (n mod 10) = true ->
  raw_odd_prod_z n = (n mod 10) * raw_odd_prod_z (n / 10).
Proof.
  intros n Hn Hodd.
  unfold raw_odd_prod_z.
  rewrite Z2Nat_div10 by lia.
  assert (Hnat : Z.to_nat n >= 1) by lia.
  rewrite raw_odd_prod_nat_step_odd by
    (try lia; rewrite <- odd_mod10_nat_Z by lia; exact Hodd).
  rewrite Nat2Z.inj_mul.
  rewrite Z2Nat_mod10 by lia.
  f_equal; [|f_equal]; try lia.
  - rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). reflexivity.
  - apply raw_odd_prod_fuel_sufficient; lia.
Qed.

(* Step lemma for raw_odd_prod_z: even digit *)
Lemma raw_odd_prod_z_step_even : forall n,
  n > 0 -> Z.odd (n mod 10) = false ->
  raw_odd_prod_z n = raw_odd_prod_z (n / 10).
Proof.
  intros n Hn Heven.
  unfold raw_odd_prod_z.
  rewrite Z2Nat_div10 by lia.
  assert (Hnat : Z.to_nat n >= 1) by lia.
  rewrite raw_odd_prod_nat_step_even by
    (try lia; rewrite <- odd_mod10_nat_Z by lia; exact Heven).
  f_equal. apply raw_odd_prod_fuel_sufficient; lia.
Qed.

(* raw_odd_prod_z is at least 1 *)
Lemma raw_odd_prod_z_ge_1 : forall n,
  0 <= n -> raw_odd_prod_z n >= 1.
Proof.
  intros. unfold raw_odd_prod_z.
  pose proof (raw_odd_prod_nat_ge_1 (Z.to_nat n)). lia.
Qed.

(* When n > 0 and n%10 is odd, n%10 <= raw_odd_prod_z n *)
Lemma raw_odd_prod_z_ge_digit : forall n,
  n > 0 -> Z.odd (n mod 10) = true ->
  n mod 10 <= raw_odd_prod_z n.
Proof.
  intros.
  rewrite raw_odd_prod_z_step_odd by assumption.
  pose proof (raw_odd_prod_z_ge_1 (n / 10) ltac:(lia)).
  pose proof (Z.mod_pos_bound n 10 ltac:(lia)).
  nia.
Qed.

(* ================================================================ *)
(* C-style (Z.rem/Z.quot) helper lemmas for use in manual proofs    *)
(* ================================================================ *)

(* Z.quot equals Z.div for non-negative numerator and positive denominator *)
Lemma Zquot_eq_Zdiv_pos : forall a b, 0 <= a -> 0 < b -> a ÷ b = a / b.
Proof.
  intros. apply Zquot_Zdiv_pos; lia.
Qed.

(* Convert C-style oddness check to Z.odd *)
Lemma rem_digit_odd : forall n, 0 < n ->
  Z.rem (Z.rem n 10) 2 = 1 <-> Z.odd (n mod 10) = true.
Proof.
  intros n Hn.
  rewrite Z.odd_spec.
  rewrite <- (Zrem_Zmod_pos (n mod 10) 2) by (apply Z.mod_pos_bound; lia).
  rewrite <- (Zrem_Zmod_pos n 10) by lia.
  tauto.
Qed.

(* C-style: n rem 10 <= raw_odd_prod_z n when digit is odd *)
Lemma raw_odd_prod_z_ge_rem_digit : forall n,
  n > 0 -> Z.rem (Z.rem n 10) 2 = 1 ->
  Z.rem n 10 <= raw_odd_prod_z n.
Proof.
  intros n Hn Hodd.
  rewrite Zrem_Zmod_pos by lia.
  apply raw_odd_prod_z_ge_digit; [lia|].
  rewrite <- rem_digit_odd by lia. exact Hodd.
Qed.

(* C-style step for raw_odd_prod_z when digit is odd *)
Lemma raw_odd_prod_z_step_odd_cstyle : forall n,
  n > 0 -> Z.rem (Z.rem n 10) 2 = 1 ->
  raw_odd_prod_z n = Z.rem n 10 * raw_odd_prod_z (n ÷ 10).
Proof.
  intros n Hn Hodd.
  rewrite Zquot_eq_Zdiv_pos by lia.
  rewrite Zrem_Zmod_pos by lia.
  apply raw_odd_prod_z_step_odd; [lia|].
  rewrite <- rem_digit_odd by lia. exact Hodd.
Qed.

(* C-style step for raw_odd_prod_z when digit is even *)
Lemma raw_odd_prod_z_step_even_cstyle : forall n,
  n > 0 -> Z.rem (Z.rem n 10) 2 <> 1 ->
  raw_odd_prod_z n = raw_odd_prod_z (n ÷ 10).
Proof.
  intros n Hn Heven.
  rewrite Zquot_eq_Zdiv_pos by lia.
  apply raw_odd_prod_z_step_even; [lia|].
  destruct (Z.odd (n mod 10)) eqn:E; [|reflexivity].
  exfalso. apply Heven. rewrite rem_digit_odd by lia. exact E.
Qed.

(* C-style step for digits_loop_z when digit is odd *)
Lemma digits_loop_z_step_odd_cstyle : forall n acc has,
  n > 0 -> acc >= 0 -> 0 <= has <= 1 ->
  Z.rem (Z.rem n 10) 2 = 1 ->
  digits_loop_z n acc has = digits_loop_z (n ÷ 10) (acc * Z.rem n 10) 1.
Proof.
  intros n acc has Hn Hacc Hhas Hodd.
  rewrite Zquot_eq_Zdiv_pos by lia.
  rewrite Zrem_Zmod_pos by lia.
  apply digits_loop_z_step_odd; [lia | lia | lia |].
  rewrite <- rem_digit_odd by lia. exact Hodd.
Qed.

(* C-style step for digits_loop_z when digit is even *)
Lemma digits_loop_z_step_even_cstyle : forall n acc has,
  n > 0 -> acc >= 0 -> 0 <= has <= 1 ->
  Z.rem (Z.rem n 10) 2 <> 1 ->
  digits_loop_z n acc has = digits_loop_z (n ÷ 10) acc has.
Proof.
  intros n acc has Hn Hacc Hhas Heven.
  rewrite Zquot_eq_Zdiv_pos by lia.
  apply digits_loop_z_step_even; [lia | lia | lia |].
  destruct (Z.odd (n mod 10)) eqn:E; [|reflexivity].
  exfalso. apply Heven. rewrite rem_digit_odd by lia. exact E.
Qed.

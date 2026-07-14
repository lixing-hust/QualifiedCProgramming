Load "../spec/155".

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Logic.LogicGenerator.demo932.Interface.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition Zabs_155 (x : Z) : Z := Z.abs x.

Definition problem_155_pre_z (num : Z) : Prop :=
  problem_155_pre num.

Definition problem_155_spec_z (num : Z) (output : list Z) : Prop :=
  exists even odd,
    output = [Z.of_nat even; Z.of_nat odd] /\
    problem_155_spec num (even, odd).

Fixpoint count_digits_155 (digits : list Z) (even odd : Z) : Z * Z :=
  match digits with
  | [] => (even, odd)
  | d :: rest =>
      if Z.eqb (Z.rem d 2) 1
      then count_digits_155 rest even (odd + 1)
      else count_digits_155 rest (even + 1) odd
  end.

Fixpoint c_digits_fuel_155 (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if n =? 0
      then []
      else Z.rem n 10 :: c_digits_fuel_155 fuel' (Z.quot n 10)
  end.

Definition c_digits_155 (num : Z) : list Z :=
  let n := Z.abs num in
  if n =? 0
  then [0]
  else c_digits_fuel_155 (Z.to_nat n + 1)%nat n.

Definition count_result_155 (num : Z) : Z * Z :=
  count_digits_155 (c_digits_155 num) 0 0.

Definition digit_count_state_155 (num w even odd : Z) : Prop :=
  0 <= w /\
  0 <= even /\
  0 <= odd /\
  exists fuel,
    (w = 0 \/ w < Z.of_nat fuel) /\
    count_digits_155 (c_digits_fuel_155 fuel w) even odd =
      count_result_155 num /\
    even + odd + Zlength (c_digits_fuel_155 fuel w) <= Z.abs num + 1.

Definition even_odd_safe_155 (num : Z) : Prop :=
  INT_MIN < num <= INT_MAX /\
  let '(even, odd) := count_result_155 num in
  0 <= even <= INT_MAX /\ 0 <= odd <= INT_MAX.

Lemma c_digits_fuel_length_le_155 : forall fuel n,
  Zlength (c_digits_fuel_155 fuel n) <= Z.of_nat fuel.
Proof.
  induction fuel as [|fuel IH]; intros n.
  - cbn. lia.
  - cbn.
    destruct (n =? 0) eqn:Hn0.
    + rewrite Zlength_correct. cbn.
      change (Z.pos (Pos.of_succ_nat fuel)) with (Z.of_nat (S fuel)).
      rewrite Nat2Z.inj_succ. lia.
    + rewrite !Zlength_correct. cbn.
      change (Z.pos (Pos.of_succ_nat fuel)) with (Z.of_nat (S fuel)).
      rewrite Nat2Z.inj_succ.
      specialize (IH (Z.quot n 10)).
      rewrite Zlength_correct in IH.
      lia.
Qed.

Lemma digit_count_state_init_nonzero_155 : forall num,
  0 < Z.abs num ->
  digit_count_state_155 num (Z.abs num) 0 0.
Proof.
  intros num Habs.
  unfold digit_count_state_155, count_result_155, c_digits_155.
  destruct (Z.abs num =? 0) eqn:Habs0.
  { apply Z.eqb_eq in Habs0. lia. }
  repeat split; try lia.
  exists (Z.to_nat (Z.abs num) + 1)%nat.
  split.
  - right.
    replace (Z.of_nat (Z.to_nat (Z.abs num) + 1)) with (Z.abs num + 1) by lia.
    lia.
  - split.
    + reflexivity.
    + pose proof (c_digits_fuel_length_le_155 (Z.to_nat (Z.abs num) + 1) (Z.abs num)).
      lia.
Qed.

Lemma digit_count_state_init_zero_155 : forall num,
  Z.abs num = 0 ->
  digit_count_state_155 num 0 1 0.
Proof.
  intros num Habs.
  unfold digit_count_state_155, count_result_155, c_digits_155.
  rewrite Habs.
  cbn.
  repeat split; try lia.
  exists 1%nat.
  split; [left; reflexivity|].
  split; [reflexivity|cbn; lia].
Qed.

Lemma digit_count_state_step_odd_155 : forall num w even odd d,
  digit_count_state_155 num w even odd ->
  0 < w ->
  d = Z.rem w 10 ->
  Z.rem d 2 = 1 ->
  digit_count_state_155 num (Z.quot w 10) even (odd + 1).
Proof.
  intros num w even odd d Hstate Hw Hd Hodd.
  unfold digit_count_state_155 in *.
  destruct Hstate as [Hw_nonneg [Heven [Hodd_nonneg [fuel [Hfuel [Hcount Hbound]]]]]].
  destruct fuel as [|fuel']; [destruct Hfuel as [Hzero|Hlt]; lia|].
  simpl in Hcount, Hbound.
  assert (Hw0 : (w =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hw0 in Hcount, Hbound.
  rewrite <- Hd in Hcount.
  rewrite Zlength_cons in Hbound.
  assert (Hcount' :
    count_digits_155 (c_digits_fuel_155 fuel' (Z.quot w 10)) even (odd + 1) =
    count_result_155 num).
  {
    rewrite <- Hcount.
    cbn.
    rewrite Hodd.
    reflexivity.
  }
  repeat split.
  - rewrite Z.quot_div_nonneg by lia.
    apply Z.div_pos; lia.
  - lia.
  - lia.
  - exists fuel'.
    repeat split.
    + destruct (Z.quot w 10 =? 0) eqn:Hq.
      * left. apply Z.eqb_eq; assumption.
      * right.
        destruct Hfuel as [Hzero|Hlt]; [lia|].
        assert (Z.quot w 10 < w).
        { rewrite Z.quot_div_nonneg by lia.
          apply Z.div_lt; lia. }
        lia.
    + exact Hcount'.
    + lia.
Qed.

Lemma digit_count_state_step_even_155 : forall num w even odd d,
  digit_count_state_155 num w even odd ->
  0 < w ->
  d = Z.rem w 10 ->
  Z.rem d 2 <> 1 ->
  digit_count_state_155 num (Z.quot w 10) (even + 1) odd.
Proof.
  intros num w even odd d Hstate Hw Hd Heven_case.
  unfold digit_count_state_155 in *.
  destruct Hstate as [Hw_nonneg [Heven [Hodd_nonneg [fuel [Hfuel [Hcount Hbound]]]]]].
  destruct fuel as [|fuel']; [destruct Hfuel as [Hzero|Hlt]; lia|].
  simpl in Hcount, Hbound.
  assert (Hw0 : (w =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hw0 in Hcount, Hbound.
  rewrite <- Hd in Hcount.
  rewrite Zlength_cons in Hbound.
  destruct (Z.rem d 2 =? 1) eqn:Hcase.
  - apply Z.eqb_eq in Hcase. contradiction.
  - assert (Hcount' :
      count_digits_155 (c_digits_fuel_155 fuel' (Z.quot w 10)) (even + 1) odd =
      count_result_155 num).
    {
      rewrite <- Hcount.
      cbn.
      rewrite Hcase.
      reflexivity.
    }
    repeat split.
    + rewrite Z.quot_div_nonneg by lia.
      apply Z.div_pos; lia.
    + lia.
    + lia.
    + exists fuel'.
      repeat split.
      * destruct (Z.quot w 10 =? 0) eqn:Hq.
        -- left. apply Z.eqb_eq; assumption.
        -- right.
           destruct Hfuel as [Hzero|Hlt]; [lia|].
           assert (Z.quot w 10 < w).
           { rewrite Z.quot_div_nonneg by lia.
             apply Z.div_lt; lia. }
           lia.
      * exact Hcount'.
      * lia.
Qed.

Lemma c_digits_fuel_nonnegative_155 : forall fuel n d,
  0 <= n ->
  In d (c_digits_fuel_155 fuel n) ->
  0 <= d.
Proof.
  induction fuel as [|fuel IH]; intros n d Hn Hin; cbn in Hin; [contradiction|].
  destruct (n =? 0) eqn:Hn0; [contradiction|].
  cbn in Hin.
  destruct Hin as [Hd|Hin].
  - subst d.
    rewrite Z.rem_mod_nonneg by lia.
    apply Z.mod_pos_bound; lia.
  - eapply IH; [|eassumption].
    rewrite Z.quot_div_nonneg by lia.
    apply Z.div_pos; lia.
Qed.

Lemma count_digits_155_nonnegative : forall digits even odd,
  0 <= even ->
  0 <= odd ->
  (forall d, In d digits -> 0 <= d) ->
  let '(e, o) := count_digits_155 digits even odd in
  0 <= e /\ 0 <= o.
Proof.
  induction digits as [|d rest IH]; intros even odd He Ho Hnonneg; cbn.
  - lia.
  - assert (Hd_nonneg : 0 <= d) by (apply Hnonneg; cbn; auto).
    rewrite Z.rem_mod_nonneg by lia.
    destruct (Z.modulo d 2 =? 1); cbn.
    + apply IH; try lia.
      intros x Hx. apply Hnonneg. cbn. auto.
    + apply IH; try lia.
      intros x Hx. apply Hnonneg. cbn. auto.
Qed.

Lemma even_odd_safe_counts_155 : forall num,
  even_odd_safe_155 num ->
  let '(even, odd) := count_result_155 num in
  0 <= even <= INT_MAX /\ 0 <= odd <= INT_MAX.
Proof.
  intros num Hsafe.
  unfold even_odd_safe_155 in Hsafe.
  destruct (count_result_155 num) as [even odd].
  tauto.
Qed.

Lemma count_digits_155_acc_le_result : forall digits even odd final_even final_odd,
  count_digits_155 digits even odd = (final_even, final_odd) ->
  even <= final_even /\ odd <= final_odd.
Proof.
  induction digits as [|d rest IH]; intros even odd final_even final_odd Hcount; cbn in Hcount.
  - inversion Hcount; lia.
  - destruct (Z.rem d 2 =? 1) eqn:Hcase.
    + specialize (IH even (odd + 1) final_even final_odd Hcount).
      lia.
    + specialize (IH (even + 1) odd final_even final_odd Hcount).
      lia.
Qed.

Lemma digit_count_state_acc_bounds_155 : forall num w even odd,
  digit_count_state_155 num w even odd ->
  even_odd_safe_155 num ->
  0 <= even <= INT_MAX /\ 0 <= odd <= INT_MAX.
Proof.
  intros num w even odd Hstate Hsafe.
  unfold digit_count_state_155 in Hstate.
  destruct Hstate as [_ [Heven_nonneg [Hodd_nonneg [fuel [_ [Hcount _]]]]]].
  destruct (count_result_155 num) as [final_even final_odd] eqn:Hresult.
  unfold even_odd_safe_155 in Hsafe.
  rewrite Hresult in Hsafe.
  destruct Hsafe as [_ [[Hfinal_even_nonneg Hfinal_even_int]
                        [Hfinal_odd_nonneg Hfinal_odd_int]]].
  pose proof (count_digits_155_acc_le_result
    (c_digits_fuel_155 fuel w) even odd final_even final_odd Hcount) as Hle.
  destruct Hle as [Heven_le Hodd_le].
  lia.
Qed.

Lemma digit_count_state_step_even_safe_155 : forall num w even odd,
  digit_count_state_155 num w even odd ->
  even_odd_safe_155 num ->
  0 < w ->
  Z.rem (Z.rem w 10) 2 <> 1 ->
  0 <= even + 1 <= INT_MAX.
Proof.
  intros num w even odd Hstate Hsafe Hw Heven.
  pose proof (digit_count_state_step_even_155
    num w even odd (Z.rem w 10) Hstate Hw eq_refl Heven) as Hnext.
  pose proof (digit_count_state_acc_bounds_155 num (Z.quot w 10) (even + 1) odd Hnext Hsafe).
  lia.
Qed.

Lemma digit_count_state_step_odd_safe_155 : forall num w even odd,
  digit_count_state_155 num w even odd ->
  even_odd_safe_155 num ->
  0 < w ->
  Z.rem (Z.rem w 10) 2 = 1 ->
  0 <= odd + 1 <= INT_MAX.
Proof.
  intros num w even odd Hstate Hsafe Hw Hodd.
  pose proof (digit_count_state_step_odd_155
    num w even odd (Z.rem w 10) Hstate Hw eq_refl Hodd) as Hnext.
  pose proof (digit_count_state_acc_bounds_155 num (Z.quot w 10) even (odd + 1) Hnext Hsafe).
  lia.
Qed.

Lemma count_digits_155_nat_acc_lengths : forall digits e0 o0 e o,
  (forall d, In d digits -> 0 <= d) ->
  count_digits_155 digits (Z.of_nat e0) (Z.of_nat o0) =
    (Z.of_nat e, Z.of_nat o) ->
  e = (e0 + length (filter Z.even digits))%nat /\
  o = (o0 + length (filter (fun d => negb (Z.even d)) digits))%nat.
Proof.
  induction digits as [|d rest IH]; intros e0 o0 e o Hnonneg Hcount.
  - cbn in Hcount.
    inversion Hcount; subst.
    cbn.
    split; lia.
  - cbn in Hcount.
    assert (Hd_nonneg : 0 <= d) by (apply Hnonneg; cbn; auto).
    rewrite Z.rem_mod_nonneg in Hcount by lia.
    rewrite Zmod_odd in Hcount.
    rewrite <- Z.negb_even in Hcount.
    destruct (Z.even d) eqn:Hdeven.
    + cbn in Hcount.
      replace (Z.of_nat e0 + 1) with (Z.of_nat (S e0)) in Hcount by lia.
      specialize (IH (S e0) o0 e o).
      destruct IH as [He Ho].
      * intros x Hx. apply Hnonneg. cbn. auto.
      * exact Hcount.
      * cbn. rewrite Hdeven. rewrite He, Ho.
        split.
        -- rewrite Nat.add_succ_comm. reflexivity.
        -- reflexivity.
    + cbn in Hcount.
      replace (Z.of_nat o0 + 1) with (Z.of_nat (S o0)) in Hcount by lia.
      specialize (IH e0 (S o0) e o).
      destruct IH as [He Ho].
      * intros x Hx. apply Hnonneg. cbn. auto.
      * exact Hcount.
      * cbn. rewrite Hdeven. cbn. rewrite He, Ho.
        split.
        -- reflexivity.
        -- rewrite Nat.add_succ_comm. reflexivity.
Qed.

Lemma count_digits_155_from_zero_lengths : forall digits even odd,
  (forall d, In d digits -> 0 <= d) ->
  count_digits_155 digits 0 0 = (Z.of_nat even, Z.of_nat odd) ->
  even_odd_digit_counts digits even odd.
Proof.
  intros digits even odd Hnonneg Hcount.
  change 0 with (Z.of_nat 0) in Hcount.
  destruct (count_digits_155_nat_acc_lengths digits 0 0 even odd Hnonneg Hcount)
    as [He Ho].
  unfold even_odd_digit_counts.
  split; lia.
Qed.

Lemma digit_count_state_final_counts_155 : forall num even odd,
  digit_count_state_155 num 0 even odd ->
  count_result_155 num = (even, odd).
Proof.
  intros num even odd Hstate.
  unfold digit_count_state_155 in Hstate.
  destruct Hstate as [_ [_ [_ [fuel [_ [Hcount _]]]]]].
  destruct fuel; cbn in Hcount; inversion Hcount; reflexivity.
Qed.

Lemma c_digits_fuel_zero_155 : forall fuel,
  c_digits_fuel_155 fuel 0 = [].
Proof.
  destruct fuel; reflexivity.
Qed.

Lemma c_digits_fuel_decimal_pos_155 : forall fuel n,
  0 < n ->
  n < Z.of_nat fuel ->
  list_within_bound 10 (c_digits_fuel_155 fuel n) /\
  list_to_Z 10 (c_digits_fuel_155 fuel n) = n /\
  c_digits_fuel_155 fuel n <> [] /\
  last (c_digits_fuel_155 fuel n) 0 <> 0.
Proof.
  induction fuel as [|fuel IH]; intros n Hn Hfuel.
  - cbn in Hfuel. lia.
  - cbn.
    assert (Hn0 : (n =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite Hn0.
    set (d := Z.rem n 10).
    set (q := Z.quot n 10).
    assert (Hd_bounds : 0 <= d < 10).
    { unfold d. rewrite Z.rem_mod_nonneg by lia. apply Z.mod_pos_bound; lia. }
    assert (Hdecomp : n = q * 10 + d).
    {
      unfold q, d.
      rewrite Z.quot_div_nonneg by lia.
      rewrite Z.rem_mod_nonneg by lia.
      pose proof (Z.div_mod n 10 ltac:(lia)).
      lia.
    }
    destruct (Z.eq_dec q 0) as [Hq0|Hqne].
    + assert (Hquot0 : Z.quot n 10 = 0) by (fold q; exact Hq0).
      assert (d = n) by lia.
      subst q.
      subst d.
      replace (c_digits_fuel_155 fuel (Z.quot n 10)) with (@nil Z)
        by (rewrite Hquot0; symmetry; apply c_digits_fuel_zero_155).
      split.
      * cbn.
        split; [lia|].
        change (list_within_bound 10 []) with True.
        exact I.
      * split.
        -- change (list_to_Z 10 [n % 10] = n).
           rewrite list_to_Z_single.
           lia.
        -- split.
           ++ discriminate.
           ++ cbn. lia.
    + assert (Hq_pos : 0 < q).
      {
        unfold q in Hqne |- *.
        rewrite Z.quot_div_nonneg in Hqne |- * by lia.
        pose proof (Z.div_pos n 10 ltac:(lia) ltac:(lia)).
        lia.
      }
      assert (Hq_lt_fuel : q < Z.of_nat fuel).
      {
        assert (q < n).
        {
          unfold q.
          rewrite Z.quot_div_nonneg by lia.
          apply Z.div_lt; lia.
        }
        replace (Z.of_nat (S fuel)) with (Z.of_nat fuel + 1) in Hfuel by lia.
        lia.
      }
      destruct (IH q Hq_pos Hq_lt_fuel) as [Hbound [Hval [Hnonempty Hlast]]].
      repeat split; try lia; try assumption.
      * change (list_to_Z 10 (d :: c_digits_fuel_155 fuel q) = n).
        rewrite list_to_Z_cons.
        rewrite Hval.
        lia.
      * discriminate.
      * destruct (c_digits_fuel_155 fuel q) as [|r rs] eqn:Hrest.
        -- contradiction.
        -- cbn.
           exact Hlast.
Qed.

Lemma c_digits_decimal_digits_155 : forall num,
  decimal_digits num (c_digits_155 num).
Proof.
  intro num.
  unfold decimal_digits, c_digits_155.
  destruct (Z.abs num =? 0) eqn:Habs0.
  - apply Z.eqb_eq in Habs0.
    repeat split.
    + cbn. lia.
    + rewrite list_to_Z_single. lia.
    + left.
      split.
      * destruct num; cbn in Habs0; lia.
      * reflexivity.
  - apply Z.eqb_neq in Habs0.
    assert (Habs_pos : 0 < Z.abs num) by (pose proof (Z.abs_nonneg num); lia).
    destruct (c_digits_fuel_decimal_pos_155
      (Z.to_nat (Z.abs num) + 1)%nat (Z.abs num)) as
      [Hbound [Hval [Hnonempty Hlast]]].
    + exact Habs_pos.
    + replace (Z.of_nat (Z.to_nat (Z.abs num) + 1)) with (Z.abs num + 1) by lia.
      lia.
    + repeat split.
      * exact Hbound.
      * exact Hval.
      * right.
        split.
        -- intro Hnum0. rewrite Hnum0, Z.abs_0 in Habs0. contradiction.
        -- split; assumption.
Qed.

Lemma digit_count_state_final_spec_155 : forall num even odd,
  digit_count_state_155 num 0 even odd ->
  even_odd_safe_155 num ->
  problem_155_spec_z num [even; odd].
Proof.
  intros num even_z odd_z Hstate Hsafe.
  pose proof (digit_count_state_final_counts_155 num even_z odd_z Hstate) as Hcount_z.
  pose proof (even_odd_safe_counts_155 num Hsafe) as Hbounds.
  rewrite Hcount_z in Hbounds.
  destruct Hbounds as [[He_nonneg He_int] [Ho_nonneg Ho_int]].
  pose (even := Z.to_nat even_z).
  pose (odd := Z.to_nat odd_z).
  assert (Heq_even : even_z = Z.of_nat even) by (unfold even; lia).
  assert (Heq_odd : odd_z = Z.of_nat odd) by (unfold odd; lia).
  unfold problem_155_spec_z.
  exists even, odd.
  split.
  - rewrite Heq_even, Heq_odd.
    reflexivity.
  - unfold problem_155_spec.
    exists (c_digits_155 num).
    split.
    + apply c_digits_decimal_digits_155.
    + assert (Hnonneg_digits : forall d, In d (c_digits_155 num) -> 0 <= d).
      {
        intros d Hd.
        unfold c_digits_155 in Hd.
        destruct (Z.abs num =? 0) eqn:Hzero.
        - cbn in Hd. destruct Hd as [Hd | []]. rewrite <- Hd. lia.
        - eapply c_digits_fuel_nonnegative_155; [apply Z.abs_nonneg|eassumption].
      }
      assert (Hcount_nat :
        count_digits_155 (c_digits_155 num) 0 0 = (Z.of_nat even, Z.of_nat odd)).
      {
        unfold count_result_155 in Hcount_z.
        rewrite Hcount_z.
        rewrite Heq_even, Heq_odd.
        reflexivity.
      }
      exact (count_digits_155_from_zero_lengths
        (c_digits_155 num) even odd Hnonneg_digits Hcount_nat).
Qed.

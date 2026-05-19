Load "../spec/68".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition list_Z_to_nat (l : list Z) : list nat :=
  map Z.to_nat l.

Definition list_nonnegative (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0.

Definition output_Z_to_option (l : list Z) : option (nat * nat) :=
  match l with
  | [] => None
  | value :: index :: [] => Some (Z.to_nat value, Z.to_nat index)
  | _ => None
  end.

Definition problem_68_pre_z (arr : list Z) : Prop :=
  problem_68_pre (list_Z_to_nat arr).

Definition problem_68_spec_z (arr output : list Z) : Prop :=
  list_nonnegative arr /\
  problem_68_spec (list_Z_to_nat arr) (output_Z_to_option output).

Definition pluck_update (x i : Z) (best : list Z) : list Z :=
  if Z.eqb (Z.rem x 2) 0 then
    match best with
    | [] => [x; i]
    | value :: _ =>
        if Z.ltb x value then [x; i] else best
    end
  else best.

Fixpoint pluck_scan_from (i : Z) (arr best : list Z) : list Z :=
  match arr with
  | [] => best
  | x :: xs => pluck_scan_from (i + 1) xs (pluck_update x i best)
  end.

Definition pluck_prefix_result (arr : list Z) (i : Z) : list Z :=
  pluck_scan_from 0 (sublist 0 i arr) [].

Definition pluck_loop_state (arr : list Z) (i : Z) (output : list Z) : Prop :=
  0 <= i <= Zlength arr /\
  output = pluck_prefix_result arr i.

Lemma pluck_scan_from_app : forall l1 l2 i best,
  pluck_scan_from i (l1 ++ l2) best =
  pluck_scan_from (i + Zlength l1) l2 (pluck_scan_from i l1 best).
Proof.
  induction l1 as [|x xs IH]; intros l2 i best; simpl.
  - change (Zlength (@nil Z)) with 0.
    replace (i + 0) with i by lia.
    reflexivity.
  - rewrite IH.
    rewrite Zlength_cons.
    replace (i + Z.succ (Zlength xs)) with (i + 1 + Zlength xs) by lia.
    reflexivity.
Qed.

Lemma pluck_prefix_result_0 : forall arr,
  pluck_loop_state arr 0 [].
Proof.
  intros arr.
  unfold pluck_loop_state, pluck_prefix_result.
  rewrite sublist_nil by lia.
  simpl.
  rewrite Zlength_correct.
  split; [lia | reflexivity].
Qed.

Lemma pluck_prefix_result_step : forall arr i,
  0 <= i < Zlength arr ->
  pluck_prefix_result arr (i + 1) =
  pluck_update (Znth i arr 0) i (pluck_prefix_result arr i).
Proof.
  intros arr i Hi.
  destruct Hi as [Hi0 Hilt].
  rewrite Zlength_correct in Hilt.
  unfold pluck_prefix_result.
  assert (Hsplit: sublist 0 (i + 1) arr = sublist 0 i arr ++ sublist i (i + 1) arr).
  { eapply (@sublist_split Z); lia. }
  rewrite Hsplit.
  rewrite pluck_scan_from_app.
  rewrite Zlength_sublist by (rewrite Zlength_correct; split; lia).
  rewrite (sublist_single i arr 0) by lia.
  simpl.
  replace (0 + i) with i by lia.
  replace (i - 0) with i by lia.
  reflexivity.
Qed.

Lemma replace_Znth_two : forall a b l,
  Zlength l = 2 ->
  @replace_Znth Z 1 b (@replace_Znth Z 0 a l) = [a; b].
Proof.
  intros a b l Hlen.
  rewrite Zlength_correct in Hlen.
  destruct l as [|x [|y [|z zs]]]; simpl in Hlen; try lia.
  reflexivity.
Qed.

Lemma pluck_loop_state_update_empty : forall arr i output,
  0 <= i < Zlength arr ->
  pluck_loop_state arr i output ->
  output = [] ->
  Z.rem (Znth i arr 0) 2 = 0 ->
  pluck_loop_state arr (i + 1) [Znth i arr 0; i].
Proof.
  intros arr i output Hi [Hrange Hstate] Hout Heven.
  unfold pluck_loop_state.
  split; [lia |].
  rewrite pluck_prefix_result_step by lia.
  rewrite <- Hstate.
  unfold pluck_update.
  apply Z.eqb_eq in Heven.
  rewrite Heven.
  rewrite Hout.
  reflexivity.
Qed.

Lemma pluck_loop_state_update_less : forall arr i output value index,
  0 <= i < Zlength arr ->
  pluck_loop_state arr i output ->
  output = [value; index] ->
  Z.rem (Znth i arr 0) 2 = 0 ->
  Znth i arr 0 < Znth 0 output 0 ->
  pluck_loop_state arr (i + 1) [Znth i arr 0; i].
Proof.
  intros arr i output value index Hi [Hrange Hstate] Hout Heven Hlt.
  unfold pluck_loop_state.
  split; [lia |].
  rewrite pluck_prefix_result_step by lia.
  rewrite <- Hstate.
  unfold pluck_update.
  apply Z.eqb_eq in Heven.
  rewrite Heven.
  rewrite Hout.
  rewrite Hout in Hlt.
  change (Znth 0 [value; index] 0) with value in Hlt.
  simpl in Hlt.
  apply Z.ltb_lt in Hlt.
  rewrite Hlt.
  reflexivity.
Qed.

Lemma pluck_loop_state_skip_odd : forall arr i output,
  0 <= i < Zlength arr ->
  pluck_loop_state arr i output ->
  Z.rem (Znth i arr 0) 2 <> 0 ->
  pluck_loop_state arr (i + 1) output.
Proof.
  intros arr i output Hi [Hrange Hstate] Hodd.
  unfold pluck_loop_state.
  split; [lia |].
  rewrite pluck_prefix_result_step by lia.
  rewrite <- Hstate.
  unfold pluck_update.
  apply Z.eqb_neq in Hodd.
  rewrite Hodd.
  reflexivity.
Qed.

Lemma pluck_loop_state_skip_ge : forall arr i output value index,
  0 <= i < Zlength arr ->
  pluck_loop_state arr i output ->
  output = [value; index] ->
  Z.rem (Znth i arr 0) 2 = 0 ->
  Znth i arr 0 >= Znth 0 output 0 ->
  pluck_loop_state arr (i + 1) output.
Proof.
  intros arr i output value index Hi [Hrange Hstate] Hout Heven Hge.
  unfold pluck_loop_state.
  split; [lia |].
  rewrite pluck_prefix_result_step by lia.
  rewrite <- Hstate.
  unfold pluck_update.
  apply Z.eqb_eq in Heven.
  rewrite Heven.
  rewrite Hout.
  rewrite Hout in Hge.
  change (Znth 0 [value; index] 0) with value in Hge.
  simpl in Hge.
  assert (Hge' : value <= Znth i arr 0) by lia.
  apply Z.ltb_ge in Hge'.
  rewrite Hge'.
  reflexivity.
Qed.

Definition pluck_best_spec_z (base : Z) (processed best : list Z) : Prop :=
  match best with
  | [] =>
      forall x, In x processed -> Z.rem x 2 <> 0
  | value :: index :: [] =>
      exists idx : nat,
        index = base + Z.of_nat idx /\
        nth_error processed idx = Some value /\
        Z.rem value 2 = 0 /\
        (forall x, In x processed -> Z.rem x 2 = 0 -> value <= x) /\
        (forall j : nat, (j < idx)%nat -> nth j processed 0 <> value)
  | _ => False
  end.

Lemma Z_rem_0_nat_even : forall z,
  0 <= z ->
  (Z.rem z 2 = 0 <-> Nat.even (Z.to_nat z) = true).
Proof.
  intros z Hz.
  rewrite Nat.even_spec.
  split.
  - intros Hrem.
    apply Z.rem_divide in Hrem; [|lia].
    destruct Hrem as [q Hq].
    exists (Z.to_nat q).
    apply Nat2Z.inj.
    rewrite Nat2Z.inj_mul.
    rewrite Z2Nat.id by lia.
    rewrite Z2Nat.id.
    + lia.
    + subst z. nia.
  - intros [m Hm].
    rewrite <- (Z2Nat.id z) by lia.
    rewrite Hm.
    rewrite Nat2Z.inj_mul.
    change (Z.of_nat 2) with 2.
    replace (2 * Z.of_nat m) with (Z.of_nat m * 2) by lia.
    rewrite Z.rem_mul by lia.
    reflexivity.
Qed.

Lemma Z_rem_nonzero_nat_even_false : forall z,
  0 <= z ->
  Z.rem z 2 <> 0 ->
  Nat.even (Z.to_nat z) = false.
Proof.
  intros z Hz Hrem.
  destruct (Nat.even (Z.to_nat z)) eqn:Heven; [|reflexivity].
  apply Z_rem_0_nat_even in Heven; lia.
Qed.

Lemma list_nonnegative_In : forall l x,
  list_nonnegative l ->
  In x l ->
  0 <= x.
Proof.
  induction l as [|a l IH]; intros x Hnonneg Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + specialize (Hnonneg 0).
      rewrite Znth0_cons in Hnonneg.
      apply Hnonneg.
      rewrite Zlength_cons.
      pose proof (Zlength_nonneg l). lia.
    + apply IH; [|exact Hin].
      intros i Hi.
      specialize (Hnonneg (i + 1)).
      rewrite Znth_cons in Hnonneg by lia.
      replace (i + 1 - 1) with i in Hnonneg by lia.
      apply Hnonneg.
      rewrite Zlength_cons.
      pose proof (Zlength_nonneg l). lia.
Qed.

Lemma list_nonnegative_nth_error : forall l n x,
  list_nonnegative l ->
  nth_error l n = Some x ->
  0 <= x.
Proof.
  intros l n x Hnonneg Hnth.
  apply (list_nonnegative_In l x Hnonneg).
  apply nth_error_In with (n := n). exact Hnth.
Qed.

Lemma list_nonnegative_nth : forall l n,
  (n < length l)%nat ->
  list_nonnegative l ->
  0 <= nth n l 0.
Proof.
  intros l n Hn Hnonneg.
  apply (list_nonnegative_In l (nth n l 0) Hnonneg).
  apply nth_In. exact Hn.
Qed.

Lemma pluck_best_spec_update : forall base processed best x,
  pluck_best_spec_z base processed best ->
  pluck_best_spec_z base (processed ++ [x])
    (pluck_update x (base + Zlength processed) best).
Proof.
  intros base processed best x Hbest.
  unfold pluck_update.
  destruct (Z.eqb (Z.rem x 2) 0) eqn:Heven.
  - apply Z.eqb_eq in Heven.
    destruct best as [|value [|index [|extra rest]]]; simpl in Hbest; try contradiction.
    + simpl.
      exists (length processed).
      repeat split.
      * rewrite Zlength_correct. lia.
      * rewrite nth_error_app2 by lia.
        replace (length processed - length processed)%nat with 0%nat by lia.
        reflexivity.
      * exact Heven.
      * intros y Hy Hy_even.
        apply in_app_or in Hy.
        destruct Hy as [Hy | [Hy | []]].
        -- exfalso. apply (Hbest y Hy Hy_even).
        -- subst y. lia.
      * intros j Hj.
        rewrite app_nth1 by lia.
        intro Hnth.
        apply Hbest with (x := nth j processed 0).
        -- apply nth_In. lia.
        -- rewrite Hnth. exact Heven.
    + destruct (Z.ltb x value) eqn:Hlt.
      * apply Z.ltb_lt in Hlt.
        destruct Hbest as [idx [Hindex [Hnth [Hvalue_even [Hmin Hfirst]]]]].
        simpl.
        exists (length processed).
        repeat split.
        -- rewrite Zlength_correct. lia.
        -- rewrite nth_error_app2 by lia.
           replace (length processed - length processed)%nat with 0%nat by lia.
           reflexivity.
        -- exact Heven.
        -- intros y Hy Hy_even.
           apply in_app_or in Hy.
           destruct Hy as [Hy | [Hy | []]].
           ++ specialize (Hmin y Hy Hy_even). lia.
           ++ subst y. lia.
        -- intros j Hj.
           rewrite app_nth1 by lia.
           intro Hnth_j.
           destruct (Z.eq_dec (Z.rem (nth j processed 0) 2) 0) as [Hj_even | Hj_odd].
           ++ assert (Hin_j : In (nth j processed 0) processed).
              { apply nth_In. exact Hj. }
              specialize (Hmin (nth j processed 0) Hin_j Hj_even).
              lia.
           ++ rewrite Hnth_j in Hj_odd. contradiction.
      * apply Z.ltb_ge in Hlt.
        destruct Hbest as [idx [Hindex [Hnth [Hvalue_even [Hmin Hfirst]]]]].
        simpl.
        exists idx.
        repeat split.
        -- exact Hindex.
        -- rewrite nth_error_app1; [exact Hnth |].
           apply nth_error_Some.
           rewrite Hnth. discriminate.
        -- exact Hvalue_even.
        -- intros y Hy Hy_even.
           apply in_app_or in Hy.
           destruct Hy as [Hy | [Hy | []]].
           ++ apply Hmin; auto.
           ++ subst y. lia.
        -- intros j Hj.
           rewrite app_nth1.
           ++ apply Hfirst. exact Hj.
           ++ apply nth_error_Some.
              destruct (nth_error processed j) eqn:Hnth_j; [discriminate |].
              assert (Hj_len : (length processed <= j)%nat).
              { apply nth_error_None. exact Hnth_j. }
              assert (Hidx_len : (idx < length processed)%nat).
              { apply nth_error_Some. rewrite Hnth. discriminate. }
              lia.
  - apply Z.eqb_neq in Heven.
    destruct best as [|value [|index [|extra rest]]]; simpl in Hbest; try contradiction.
    + simpl.
      intros y Hy.
      apply in_app_or in Hy.
      destruct Hy as [Hy | [Hy | []]]; subst; auto.
    + destruct Hbest as [idx [Hindex [Hnth [Hvalue_even [Hmin Hfirst]]]]].
      simpl.
      exists idx.
      repeat split.
      * exact Hindex.
      * rewrite nth_error_app1; [exact Hnth |].
        apply nth_error_Some.
        rewrite Hnth. discriminate.
      * exact Hvalue_even.
      * intros y Hy Hy_even.
        apply in_app_or in Hy.
        destruct Hy as [Hy | [Hy | []]].
        -- apply Hmin; auto.
        -- subst y. contradiction.
      * intros j Hj.
        rewrite app_nth1.
        -- apply Hfirst. exact Hj.
        -- apply nth_error_Some.
           destruct (nth_error processed j) eqn:Hnth_j; [discriminate |].
           assert (Hj_len : (length processed <= j)%nat).
           { apply nth_error_None. exact Hnth_j. }
           assert (Hidx_len : (idx < length processed)%nat).
           { apply nth_error_Some. rewrite Hnth. discriminate. }
           lia.
Qed.

Lemma pluck_scan_from_best_spec : forall rest base processed best,
  pluck_best_spec_z base processed best ->
  pluck_best_spec_z base (processed ++ rest)
    (pluck_scan_from (base + Zlength processed) rest best).
Proof.
  induction rest as [|x xs IH]; intros base processed best Hbest; simpl.
  - rewrite app_nil_r. exact Hbest.
  - replace (base + Zlength processed + 1)
      with (base + Zlength (processed ++ [x])) by
        (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    replace (processed ++ x :: xs) with ((processed ++ [x]) ++ xs)
      by (rewrite <- app_assoc; reflexivity).
    apply IH.
    apply pluck_best_spec_update.
    exact Hbest.
Qed.

Lemma pluck_prefix_result_best_spec : forall arr,
  pluck_best_spec_z 0 arr (pluck_prefix_result arr (Zlength arr)).
Proof.
  intros arr.
  unfold pluck_prefix_result.
  rewrite (sublist_self arr (Zlength arr)) by lia.
  replace 0 with (0 + Zlength (@nil Z)) by reflexivity.
  change arr with (@nil Z ++ arr) at 1.
  apply pluck_scan_from_best_spec.
  simpl.
  intros x H; contradiction.
Qed.

Lemma pluck_best_spec_to_original : forall arr output,
  list_nonnegative arr ->
  pluck_best_spec_z 0 arr output ->
  problem_68_spec (list_Z_to_nat arr) (output_Z_to_option output).
Proof.
  intros arr output Hnonneg Hbest.
  destruct output as [|value [|index [|extra rest]]]; simpl in Hbest; try contradiction; simpl.
  - intros val Hval.
    unfold list_Z_to_nat in Hval.
    apply in_map_iff in Hval.
    destruct Hval as [x [Hxval Hx]].
    subst val.
    apply Z_rem_nonzero_nat_even_false.
    + destruct (In_nth_error _ _ Hx) as [n Hnth].
      eapply list_nonnegative_nth_error; eauto.
    + apply Hbest. exact Hx.
  - destruct Hbest as [idx [Hindex [Hnth [Hvalue_even [Hmin Hfirst]]]]].
    assert (Hidx_len : (idx < length arr)%nat).
    { apply nth_error_Some. rewrite Hnth. discriminate. }
    assert (Hvalue_nonneg : 0 <= value).
    { eapply list_nonnegative_nth_error; eauto. }
    replace (Z.to_nat index) with idx by lia.
    repeat split.
    + unfold list_Z_to_nat. rewrite length_map. exact Hidx_len.
    + unfold list_Z_to_nat.
      change 1%nat with (Z.to_nat 1).
      rewrite map_nth.
      rewrite (nth_error_nth arr idx 1 Hnth).
      reflexivity.
    + apply Z_rem_0_nat_even; auto.
    + intros val Hval Hval_even.
      unfold list_Z_to_nat in Hval.
      apply in_map_iff in Hval.
      destruct Hval as [x [Hxval Hx]].
      subst val.
      assert (Hx_nonneg : 0 <= x).
      { destruct (In_nth_error _ _ Hx) as [n Hnth_x].
        eapply list_nonnegative_nth_error; eauto. }
      apply Nat2Z.inj_le.
      rewrite !Z2Nat.id by lia.
      apply Hmin; auto.
      apply Z_rem_0_nat_even; auto.
    + intros j Hj Hnth_eq.
      assert (Hj_len : (j < length arr)%nat) by lia.
      unfold list_Z_to_nat in Hnth_eq.
      replace (nth j (map Z.to_nat arr) 1%nat)
        with (nth j (map Z.to_nat arr) (Z.to_nat 0)) in Hnth_eq.
      rewrite map_nth in Hnth_eq.
      assert (Hnth_nonneg : 0 <= nth j arr 0).
      { apply list_nonnegative_nth; auto. }
      assert (nth j arr 0 = value).
      { apply Z2Nat.inj; lia. }
      apply (Hfirst j Hj). exact H.
      apply nth_indep.
      rewrite length_map. exact Hj_len.
Qed.

Lemma pluck_loop_state_full_spec : forall arr i output,
  list_nonnegative arr ->
  i >= Zlength arr ->
  pluck_loop_state arr i output ->
  problem_68_spec_z arr output.
Proof.
  intros arr i output Hnonneg Hi [Hrange Hstate].
  unfold problem_68_spec_z.
  split; [exact Hnonneg |].
  replace i with (Zlength arr) in Hstate by lia.
  rewrite Hstate.
  apply pluck_best_spec_to_original; auto.
  apply pluck_prefix_result_best_spec.
Qed.

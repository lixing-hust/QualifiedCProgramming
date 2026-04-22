Load "../spec/68".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
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

Definition problem_68_spec_z (arr output : list Z) : Prop :=
  output = pluck_prefix_result arr (Zlength arr).

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

Lemma pluck_loop_state_full_spec : forall arr i output,
  i >= Zlength arr ->
  pluck_loop_state arr i output ->
  problem_68_spec_z arr output.
Proof.
  intros arr i output Hi [Hrange Hstate].
  unfold problem_68_spec_z.
  replace i with (Zlength arr) in Hstate by lia.
  exact Hstate.
Qed.

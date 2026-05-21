Load "../spec/67".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition int_min_z : Z := -2147483648.
Definition int_max_z : Z := 2147483647.
Definition int_cur_mul10_bound_z : Z := 214748363.

Fixpoint list_ascii_of_string_z (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string_z s'
  end.

Definition char_list_string (l : list Z) (s : string) : Prop :=
  list_ascii_of_string_z s = map (fun z => ascii_of_nat (Z.to_nat z)) l.

Definition ascii_of_z (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z c) (string_of_list_z rest)
  end.

Definition ascii_range_z (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 < 256.

Definition is_digit_z (c : Z) : Prop :=
  48 <= c <= 57.

Definition digit_value_z (c : Z) : Z :=
  c - 48.

Definition fruit_commit_num1_z (num1 cur : Z) : Z :=
  if num1 <? 0 then cur else num1.

Definition fruit_commit_num2_z (num1 num2 cur : Z) : Z :=
  if num1 <? 0 then num2 else if num2 <? 0 then cur else num2.

Definition fruit_step_z (st : Z * Z * Z) (c : Z) : Z * Z * Z :=
  let '(num1, num2, cur) := st in
  if (48 <=? c) && (c <=? 57) then
    let cur0 := if cur <? 0 then 0 else cur in
    (num1, num2, cur0 * 10 + digit_value_z c)
  else if 0 <=? cur then
    (fruit_commit_num1_z num1 cur,
     fruit_commit_num2_z num1 num2 cur,
     -1)
  else st.

Fixpoint fruit_state_after_nat (k : nat) (s : list Z) : Z * Z * Z :=
  match k with
  | O => (-1, -1, -1)
  | S k' => fruit_step_z (fruit_state_after_nat k' s) (Znth (Z.of_nat k') s 0)
  end.

Definition fruit_num1_prefix_z (i : Z) (s : list Z) : Z :=
  let '(num1, _, _) := fruit_state_after_nat (Z.to_nat i) s in num1.

Definition fruit_num2_prefix_z (i : Z) (s : list Z) : Z :=
  let '(_, num2, _) := fruit_state_after_nat (Z.to_nat i) s in num2.

Definition fruit_cur_prefix_z (i : Z) (s : list Z) : Z :=
  let '(_, _, cur) := fruit_state_after_nat (Z.to_nat i) s in cur.

Definition fruit_flush_num1_z (s : list Z) : Z :=
  let num1 := fruit_num1_prefix_z (Zlength s) s in
  let cur := fruit_cur_prefix_z (Zlength s) s in
  if 0 <=? cur then fruit_commit_num1_z num1 cur else num1.

Definition fruit_flush_num2_z (s : list Z) : Z :=
  let num1 := fruit_num1_prefix_z (Zlength s) s in
  let num2 := fruit_num2_prefix_z (Zlength s) s in
  let cur := fruit_cur_prefix_z (Zlength s) s in
  if 0 <=? cur then fruit_commit_num2_z num1 num2 cur else num2.

Definition fruit_final_num1_z (s : list Z) : Z :=
  let num1 := fruit_flush_num1_z s in
  if num1 <? 0 then 0 else num1.

Definition fruit_final_num2_z (s : list Z) : Z :=
  let num2 := fruit_flush_num2_z s in
  if num2 <? 0 then 0 else num2.

Definition fruit_output_z (s : list Z) (total : Z) : Z :=
  total - fruit_final_num1_z s - fruit_final_num2_z s.

Definition fruit_state_range_at_z (i : Z) (s : list Z) : Prop :=
  -1 <= fruit_num1_prefix_z i s <= int_max_z /\
  -1 <= fruit_num2_prefix_z i s <= int_max_z /\
  -1 <= fruit_cur_prefix_z i s <= int_max_z.

Definition fruit_digit_update_safe_z (i : Z) (s : list Z) : Prop :=
  is_digit_z (Znth i s 0) ->
  fruit_cur_prefix_z i s < 0 \/
  0 <= fruit_cur_prefix_z i s <= int_cur_mul10_bound_z.

Definition fruit_state_safe_z (s : list Z) : Prop :=
  (forall i, 0 <= i <= Zlength s -> fruit_state_range_at_z i s) /\
  (forall i, 0 <= i < Zlength s -> fruit_digit_update_safe_z i s).

Definition fruit_output_safe_z (s : list Z) (total : Z) : Prop :=
  int_min_z <= total - fruit_final_num1_z s <= int_max_z /\
  int_min_z <= fruit_output_z s total <= int_max_z.

Definition problem_67_pre_z (s : list Z) (total : Z) : Prop :=
  problem_67_pre (string_of_list_z s) (Z.to_nat total).

Definition problem_67_spec_z (s : list Z) (total output : Z) : Prop :=
  problem_67_spec (string_of_list_z s) (Z.to_nat total) (Z.to_nat output).

Lemma fruit_state_after_step : forall i s st,
  0 <= i ->
  fruit_state_after_nat (Z.to_nat i) s = st ->
  fruit_state_after_nat (Z.to_nat (i + 1)) s =
  fruit_step_z st (Znth i s 0).
Proof.
  intros i s st Hi Hst.
  rewrite Z2Nat.inj_add by lia.
  change (Z.to_nat 1) with 1%nat.
  rewrite Nat.add_1_r.
  simpl.
  rewrite Z2Nat.id by lia.
  rewrite Hst.
  reflexivity.
Qed.

Lemma fruit_prefix_step : forall i s,
  0 <= i ->
  (fruit_num1_prefix_z (i + 1) s,
   fruit_num2_prefix_z (i + 1) s,
   fruit_cur_prefix_z (i + 1) s) =
  fruit_step_z
    (fruit_num1_prefix_z i s, fruit_num2_prefix_z i s, fruit_cur_prefix_z i s)
    (Znth i s 0).
Proof.
  intros i s Hi.
  unfold fruit_num1_prefix_z, fruit_num2_prefix_z, fruit_cur_prefix_z.
  destruct (fruit_state_after_nat (Z.to_nat i) s) as [[num1 num2] cur] eqn:Hst.
  rewrite (fruit_state_after_step i s (num1, num2, cur) Hi Hst).
  destruct (fruit_step_z (num1, num2, cur) (Znth i s 0)) as [[num1' num2'] cur'].
  reflexivity.
Qed.

Lemma fruit_state_range_from_safe : forall s i,
  fruit_state_safe_z s ->
  0 <= i <= Zlength s ->
  fruit_state_range_at_z i s.
Proof.
  intros s i [Hrange _] Hi.
  apply Hrange; lia.
Qed.

Lemma fruit_digit_update_safe_from_safe : forall s i,
  fruit_state_safe_z s ->
  0 <= i < Zlength s ->
  fruit_digit_update_safe_z i s.
Proof.
  intros s i [_ Hsafe] Hi.
  apply Hsafe; lia.
Qed.

Lemma fruit_output_safe_from_safe : forall s total,
  fruit_output_safe_z s total ->
  fruit_output_safe_z s total.
Proof.
  auto.
Qed.

Definition spec67_digit_z (c : ascii) : Z :=
  (Z.of_nat (nat_of_ascii c) - 48)%Z.

Definition spec67_commit_num1 (num1 cur : Z) : Z :=
  if Z.ltb num1 0 then cur else num1.

Definition spec67_commit_num2 (num1 num2 cur : Z) : Z :=
  if Z.ltb num1 0 then num2 else if Z.ltb num2 0 then cur else num2.

Definition spec67_scan_step (st : Z * Z * Z) (c : ascii) : Z * Z * Z :=
  let '(num1, num2, cur) := st in
  let z := Z.of_nat (nat_of_ascii c) in
  if andb (Z.leb 48 z) (Z.leb z 57) then
    let cur0 := if Z.ltb cur 0 then 0%Z else cur in
    (num1, num2, (cur0 * 10 + spec67_digit_z c)%Z)
  else if Z.leb 0 cur then
    (spec67_commit_num1 num1 cur,
     spec67_commit_num2 num1 num2 cur,
     (-1)%Z)
  else st.

Fixpoint spec67_scan_state_left (st : Z * Z * Z) (l : list ascii) : Z * Z * Z :=
  match l with
  | [] => st
  | c :: rest => spec67_scan_state_left (spec67_scan_step st c) rest
  end.

Definition spec67_scan_state_full (l : list ascii) : Z * Z * Z :=
  spec67_scan_state_left ((-1)%Z, (-1)%Z, (-1)%Z) l.

Definition spec67_flush_num1 (st : Z * Z * Z) : Z :=
  let '(num1, _, cur) := st in
  if Z.leb 0 cur then spec67_commit_num1 num1 cur else num1.

Definition spec67_flush_num2 (st : Z * Z * Z) : Z :=
  let '(num1, num2, cur) := st in
  if Z.leb 0 cur then spec67_commit_num2 num1 num2 cur else num2.

Definition spec67_final_num1 (st : Z * Z * Z) : Z :=
  let n1 := spec67_flush_num1 st in
  if Z.ltb n1 0 then 0%Z else n1.

Definition spec67_final_num2 (st : Z * Z * Z) : Z :=
  let n2 := spec67_flush_num2 st in
  if Z.ltb n2 0 then 0%Z else n2.

Definition spec67_scan_output_z (s : string) (n : nat) : Z :=
  let st := spec67_scan_state_full (list_ascii_of_string s) in
  (Z.of_nat n - spec67_final_num1 st - spec67_final_num2 st)%Z.

Lemma nat_of_ascii_ascii_of_z_67 : forall z,
  0 <= z < 256 ->
  nat_of_ascii (ascii_of_z z) = Z.to_nat z.
Proof.
  intros z Hz.
  unfold ascii_of_z.
  rewrite nat_ascii_embedding by lia.
  reflexivity.
Qed.

Lemma spec67_scan_step_ascii_of_z : forall st c,
  0 <= c < 256 ->
  fruit_step_z st c = spec67_scan_step st (ascii_of_z c).
Proof.
  intros [[num1 num2] cur] c Hc.
  unfold fruit_step_z, spec67_scan_step, digit_value_z, spec67_digit_z,
         fruit_commit_num1_z, fruit_commit_num2_z,
         spec67_commit_num1, spec67_commit_num2.
  rewrite nat_of_ascii_ascii_of_z_67 by exact Hc.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma list_ascii_of_string_string_of_list_z_67 : forall l,
  list_ascii_of_string (string_of_list_z l) = map ascii_of_z l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma spec67_scan_state_left_app : forall l1 l2 st,
  spec67_scan_state_left st (l1 ++ l2) =
  spec67_scan_state_left (spec67_scan_state_left st l1) l2.
Proof.
  induction l1 as [| c rest IH]; intros l2 st; simpl; auto.
Qed.

Lemma firstn_succ_nth_67 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = (firstn n l ++ [nth n l d])%list.
Proof.
  induction n as [| n IH]; intros l d Hlen.
  - destruct l; simpl in *; try lia; reflexivity.
  - destruct l; simpl in *; try lia.
    f_equal.
    apply IH.
    lia.
Qed.

Lemma spec67_scan_state_left_prefix_ascii : forall k l,
  ascii_range_z l ->
  (k <= List.length l)%nat ->
  spec67_scan_state_left ((-1)%Z, (-1)%Z, (-1)%Z)
    (firstn k (map ascii_of_z l)) =
  fruit_state_after_nat k l.
Proof.
  induction k as [| k IH]; intros l Hrange Hk.
  - reflexivity.
  - rewrite (firstn_succ_nth_67 k (map ascii_of_z l) (ascii_of_z 0%Z))
      by (rewrite map_length; lia).
    rewrite spec67_scan_state_left_app.
    rewrite IH by (assumption || lia).
    rewrite map_nth with (d := 0%Z) by lia.
    simpl.
    unfold Znth.
    rewrite Nat2Z.id.
    rewrite spec67_scan_step_ascii_of_z.
    + reflexivity.
    + specialize (Hrange (Z.of_nat k)).
      unfold Znth in Hrange.
      rewrite Nat2Z.id in Hrange.
      apply Hrange.
      rewrite Zlength_correct.
      lia.
Qed.

Lemma spec67_scan_state_full_ascii_of_z : forall l,
  ascii_range_z l ->
  spec67_scan_state_full (map ascii_of_z l) =
  fruit_state_after_nat (List.length l) l.
Proof.
  intros l Hrange.
  unfold spec67_scan_state_full.
  replace (map ascii_of_z l) with
    (firstn (List.length l) (map ascii_of_z l)) at 1.
  - apply spec67_scan_state_left_prefix_ascii.
    + exact Hrange.
    + lia.
  - replace (List.length l) with (List.length (map ascii_of_z l))
      by (rewrite map_length; reflexivity).
    exact (firstn_all (map ascii_of_z l)).
Qed.

Lemma fruit_output_spec67_scan_output_z : forall s total,
  ascii_range_z s ->
  0 <= total ->
  spec67_scan_output_z (string_of_list_z s) (Z.to_nat total) =
  fruit_output_z s total.
Proof.
  intros s total Hrange Htotal.
  unfold spec67_scan_output_z, fruit_output_z.
  rewrite list_ascii_of_string_string_of_list_z_67.
  rewrite spec67_scan_state_full_ascii_of_z by exact Hrange.
  rewrite Z2Nat.id by lia.
  unfold fruit_final_num1_z, fruit_final_num2_z,
         fruit_flush_num1_z, fruit_flush_num2_z,
         fruit_num1_prefix_z, fruit_num2_prefix_z, fruit_cur_prefix_z.
  replace (Z.to_nat (Zlength s)) with (List.length s).
  - destruct (fruit_state_after_nat (List.length s) s) as [[num1 num2] cur].
    reflexivity.
  - rewrite Zlength_correct.
    lia.
Qed.

Lemma list_ascii_of_string_app_67 : forall a b,
  list_ascii_of_string (a ++ b) =
  (list_ascii_of_string a ++ list_ascii_of_string b)%list.
Proof.
  induction a; intros b; simpl; auto.
  rewrite IHa; reflexivity.
Qed.

Lemma spec67_digit_z_nat : forall c,
  (48 <= nat_of_ascii c <= 57)%nat ->
  spec67_digit_z c = Z.of_nat (char_to_digit c).
Proof.
  intros c Hc.
  unfold spec67_digit_z, char_to_digit.
  change (nat_of_ascii "0"%char) with 48%nat.
  rewrite Nat2Z.inj_sub by lia.
  lia.
Qed.

Lemma spec67_scan_digits_acc : forall s n1 n2 acc,
  (forall c, In c (list_ascii_of_string s) ->
    (48 <= nat_of_ascii c <= 57)%nat) ->
  spec67_scan_state_left (n1, n2, Z.of_nat acc) (list_ascii_of_string s) =
    (n1, n2, Z.of_nat (string_to_nat_aux s acc)).
Proof.
  induction s as [| c rest IH]; intros n1 n2 acc Hdigits.
  - reflexivity.
  - simpl in Hdigits |- *.
    assert (Hc : (48 <= nat_of_ascii c <= 57)%nat) by
      (apply Hdigits; left; reflexivity).
    assert (Hrest : forall x, In x (list_ascii_of_string rest) ->
      (48 <= nat_of_ascii x <= 57)%nat) by
      (intros x Hx; apply Hdigits; right; exact Hx).
    unfold spec67_scan_step.
    replace (andb (Z.leb 48 (Z.of_nat (nat_of_ascii c)))
                  (Z.leb (Z.of_nat (nat_of_ascii c)) 57)) with true
      by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    replace (Z.ltb (Z.of_nat acc) 0) with false
      by (symmetry; apply Z.ltb_ge; lia).
    rewrite spec67_digit_z_nat by exact Hc.
    replace ((Z.of_nat acc * 10 + Z.of_nat (char_to_digit c))%Z)
      with (Z.of_nat (acc * 10 + char_to_digit c)) by lia.
    apply IH.
    exact Hrest.
Qed.

Lemma spec67_scan_digits_first : forall s n1 n2,
  s <> EmptyString ->
  (forall c, In c (list_ascii_of_string s) ->
    (48 <= nat_of_ascii c <= 57)%nat) ->
  spec67_scan_state_left (n1, n2, (-1)%Z) (list_ascii_of_string s) =
    (n1, n2, Z.of_nat (string_to_nat s)).
Proof.
  destruct s as [| c rest]; intros n1 n2 Hnonempty Hdigits; [contradiction|].
  simpl in Hdigits |- *.
  assert (Hc : (48 <= nat_of_ascii c <= 57)%nat) by
    (apply Hdigits; left; reflexivity).
  assert (Hrest : forall x, In x (list_ascii_of_string rest) ->
    (48 <= nat_of_ascii x <= 57)%nat) by
    (intros x Hx; apply Hdigits; right; exact Hx).
  unfold spec67_scan_step.
  replace (andb (Z.leb 48 (Z.of_nat (nat_of_ascii c)))
                (Z.leb (Z.of_nat (nat_of_ascii c)) 57)) with true
    by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
  replace (Z.ltb (-1) 0) with true by reflexivity.
  rewrite spec67_digit_z_nat by exact Hc.
  change (if true then 0%Z else (-1)%Z) with 0%Z.
  change (string_to_nat (String c rest)) with
    (string_to_nat_aux rest (char_to_digit c)).
  replace ((0 * 10 + Z.of_nat (char_to_digit c))%Z)
    with (Z.of_nat (char_to_digit c)) by lia.
  apply spec67_scan_digits_acc.
  exact Hrest.
Qed.

Lemma spec67_scan_step_non_digit_no_cur : forall n1 n2 c,
  (Z.of_nat (nat_of_ascii c) < 48 \/
   57 < Z.of_nat (nat_of_ascii c))%Z ->
  spec67_scan_step (n1, n2, (-1)%Z) c = (n1, n2, (-1)%Z).
Proof.
  intros n1 n2 c Hnot.
  unfold spec67_scan_step.
  replace (andb (Z.leb 48 (Z.of_nat (nat_of_ascii c)))
                (Z.leb (Z.of_nat (nat_of_ascii c)) 57)) with false.
  - reflexivity.
  - symmetry.
    apply andb_false_iff.
    destruct Hnot as [Hlt | Hgt].
    + left. apply Z.leb_gt. lia.
    + right. apply Z.leb_gt. lia.
Qed.

Lemma spec67_scan_step_non_digit_commit : forall n1 n2 cur c,
  0 <= cur ->
  (Z.of_nat (nat_of_ascii c) < 48 \/
   57 < Z.of_nat (nat_of_ascii c))%Z ->
  spec67_scan_step (n1, n2, cur) c =
    (spec67_commit_num1 n1 cur,
     spec67_commit_num2 n1 n2 cur,
     (-1)%Z).
Proof.
  intros n1 n2 cur c Hcur Hnot.
  unfold spec67_scan_step.
  replace (andb (Z.leb 48 (Z.of_nat (nat_of_ascii c)))
                (Z.leb (Z.of_nat (nat_of_ascii c)) 57)) with false.
  - replace (Z.leb 0 cur) with true by (symmetry; apply Z.leb_le; lia).
    reflexivity.
  - symmetry.
    apply andb_false_iff.
    destruct Hnot as [Hlt | Hgt].
    + left. apply Z.leb_gt. lia.
    + right. apply Z.leb_gt. lia.
Qed.

Ltac solve_ascii_non_digit :=
  first [left; vm_compute; lia | right; vm_compute; lia].

Lemma spec67_scan_apples_sep : forall apples,
  spec67_scan_state_left ((-1)%Z, (-1)%Z, Z.of_nat apples)
    (list_ascii_of_string " apples and ") =
    (Z.of_nat apples, (-1)%Z, (-1)%Z).
Proof.
  intros apples.
  cbn [list_ascii_of_string spec67_scan_state_left].
  pose proof (spec67_scan_step_non_digit_commit
    (-1)%Z (-1)%Z (Z.of_nat apples) " "%char
    ltac:(lia)
    ltac:(left; change (Z.of_nat (nat_of_ascii " "%char)) with 32%Z; lia)) as Hstep.
  rewrite Hstep; clear Hstep.
  unfold spec67_commit_num1, spec67_commit_num2.
  replace (Z.ltb (Z.of_nat apples) 0) with false
    by (symmetry; apply Z.ltb_ge; lia).
  replace (Z.ltb (-1) 0) with true by reflexivity.
  cbn.
  repeat rewrite spec67_scan_step_non_digit_no_cur by solve_ascii_non_digit.
  reflexivity.
Qed.

Lemma spec67_scan_oranges_sep : forall apples oranges,
  spec67_scan_state_left (Z.of_nat apples, (-1)%Z, Z.of_nat oranges)
    (list_ascii_of_string " oranges") =
    (Z.of_nat apples, Z.of_nat oranges, (-1)%Z).
Proof.
  intros apples oranges.
  cbn [list_ascii_of_string spec67_scan_state_left].
  pose proof (spec67_scan_step_non_digit_commit
    (Z.of_nat apples) (-1)%Z (Z.of_nat oranges) " "%char
    ltac:(lia)
    ltac:(left; change (Z.of_nat (nat_of_ascii " "%char)) with 32%Z; lia)) as Hstep.
  rewrite Hstep; clear Hstep.
  unfold spec67_commit_num1, spec67_commit_num2.
  replace (Z.ltb (Z.of_nat apples) 0) with false
    by (symmetry; apply Z.ltb_ge; lia).
  replace (Z.ltb (-1) 0) with true by reflexivity.
  cbn.
  repeat rewrite spec67_scan_step_non_digit_no_cur by solve_ascii_non_digit.
  reflexivity.
Qed.

Lemma Z_to_nat_sub_two : forall n a b,
  Z.to_nat (Z.of_nat n - Z.of_nat a - Z.of_nat b) =
  (n - (a + b))%nat.
Proof.
  intros n a b.
  replace (Z.of_nat n - Z.of_nat a - Z.of_nat b)%Z
    with (Z.of_nat n - Z.of_nat (a + b))%Z by lia.
  destruct (le_gt_dec (a + b) n) as [Hle | Hgt].
  - apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite Nat2Z.inj_sub by lia.
    lia.
  - replace (n - (a + b))%nat with 0%nat by lia.
    destruct (Z.of_nat n - Z.of_nat (a + b))%Z eqn:Hz; try reflexivity;
      exfalso; lia.
Qed.

Lemma spec67_scan_output_z_format : forall s_apples s_oranges n,
  s_apples <> EmptyString ->
  s_oranges <> EmptyString ->
  (forall c, In c (list_ascii_of_string s_apples) ->
    (48 <= nat_of_ascii c <= 57)%nat) ->
  (forall c, In c (list_ascii_of_string s_oranges) ->
    (48 <= nat_of_ascii c <= 57)%nat) ->
  spec67_scan_output_z
    (s_apples ++ " apples and " ++ s_oranges ++ " oranges") n =
  (Z.of_nat n - Z.of_nat (string_to_nat s_apples) -
   Z.of_nat (string_to_nat s_oranges))%Z.
Proof.
  intros s_apples s_oranges n Happles_nonempty Horanges_nonempty
    Happles_digits Horanges_digits.
  unfold spec67_scan_output_z, spec67_scan_state_full.
  repeat rewrite list_ascii_of_string_app_67.
  repeat rewrite spec67_scan_state_left_app.
  rewrite spec67_scan_digits_first by assumption.
  rewrite spec67_scan_apples_sep.
  rewrite spec67_scan_digits_first by assumption.
  rewrite spec67_scan_oranges_sep.
  unfold spec67_final_num1, spec67_final_num2,
         spec67_flush_num1, spec67_flush_num2,
         spec67_commit_num1, spec67_commit_num2.
  cbn.
  replace (Z.ltb (Z.of_nat (string_to_nat s_apples)) 0) with false
    by (symmetry; apply Z.ltb_ge; lia).
  replace (Z.ltb (Z.of_nat (string_to_nat s_oranges)) 0) with false
    by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

Lemma problem_67_spec_z_intro : forall s total output,
  problem_67_pre_z s total ->
  ascii_range_z s ->
  0 <= total ->
  output = fruit_output_z s total ->
  problem_67_spec_z s total output.
Proof.
  intros s total output Hpre Hrange Htotal Hout.
  unfold problem_67_spec_z.
  unfold problem_67_pre_z, problem_67_pre in Hpre.
  destruct Hpre as [s_apples [s_oranges
    [Happles_nonempty [Horanges_nonempty [Happles_digits [Horanges_digits Hs]]]]]].
  unfold problem_67_spec.
  exists (string_to_nat s_apples), (string_to_nat s_oranges).
  split.
  - unfold parse_fruit_string.
    exists s_apples, s_oranges.
    repeat split; assumption.
  - rewrite Hout.
    rewrite <- fruit_output_spec67_scan_output_z by auto.
    rewrite Hs.
    rewrite spec67_scan_output_z_format by assumption.
    apply Z_to_nat_sub_two.
Qed.

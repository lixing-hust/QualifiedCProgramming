Load "../spec/44".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.
Require Import Recdef.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
From SimpleC.EE Require Import string_bridge.
Import ListNotations.

Local Open Scope Z_scope.

Definition SingleSome {A : Type} (l : list (option A)) (n : Z) (a : A) : Prop :=
  Znth n l None = Some a /\
  forall m, 0 <= m < Zlength l -> m <> n -> Znth m l None = None.

Definition repeat_Z {A: Type} (a: A) (n: Z): list A :=
  repeat a (Z.to_nat n).

Lemma repeat_Z_tail : forall {A: Type} (a: A) n,
  0 <= n ->
  repeat_Z a (n + 1) = repeat_Z a n ++ [a].
Proof.
  intros A a n Hn.
  unfold repeat_Z.
  replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  rewrite <- repeat_cons.
  reflexivity.
Qed.

Lemma Zlength_repeat_Z : forall {A: Type} (a: A) n,
  0 <= n ->
  Zlength (repeat_Z a n) = n.
Proof.
  intros A a n Hn.
  unfold repeat_Z.
  rewrite Zlength_correct, repeat_length.
  lia.
Qed.

Function base_digits_z (n base : Z) {measure Z.to_nat n} : list Z :=
  if Z.leb base 1 then [48]
  else if Z.leb n 0 then [48]
  else if Z.ltb n base then [48 + n]
  else base_digits_z (n / base) base ++ [48 + (n mod base)].
Proof.
  intros n base Hbase Hnpos Hnotlt.
  apply Z.leb_gt in Hbase.
  apply Z.leb_gt in Hnpos.
  apply Z.ltb_ge in Hnotlt.
  apply Z2Nat.inj_lt.
  - apply Z.div_pos; lia.
  - lia.
  - apply Z.div_lt; lia.
Defined.

Definition base_digits_pos_z (n base : Z) : list Z :=
  if Z.leb n 0 then [] else base_digits_z n base.

Definition problem_44_pre_z (x base : Z) : Prop :=
  problem_44_pre (Z.to_nat x) (Z.to_nat base).

Definition problem_44_spec_z (x base : Z) (output : list Z) : Prop :=
  problem_44_spec (Z.to_nat x) (Z.to_nat base) (map ascii_of_z output).

Definition digit_value_z (c : Z) : Z := c - 48.

Fixpoint digits_value_z (base : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | c :: rest => digits_value_z base rest + digit_value_z c * Z.pow base (Zlength rest)
  end.

Definition base_count_state_z (orig base t digits : Z) : Prop :=
  0 <= t /\
  0 <= digits /\
  digits + Zlength (base_digits_pos_z t base) =
    Zlength (base_digits_pos_z orig base).

Definition base_fill_state_z
  (orig base x digits : Z) (suffix : list Z) : Prop :=
  0 <= x /\
  0 <= digits /\
  digits = Zlength (base_digits_pos_z x base) /\
  base_digits_z orig base = base_digits_pos_z x base ++ suffix.

Definition base_fill_full_state_z
  (orig base x digits : Z) (out_l : list Z) : Prop :=
  exists suffix,
    base_fill_state_z orig base x digits suffix /\
    out_l = repeat_Z 0 digits ++ suffix.

Lemma base_digits_z_zero : forall base,
  2 <= base ->
  base_digits_z 0 base = [48].
Proof.
  intros base Hbase.
  rewrite base_digits_z_equation.
  replace (base <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
  replace (0 <=? 0) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma base_digits_z_small : forall n base,
  0 < n < base ->
  2 <= base ->
  base_digits_z n base = [48 + n].
Proof.
  intros n base Hn Hbase.
  rewrite base_digits_z_equation.
  replace (base <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
  replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  replace (n <? base) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma base_digits_z_step : forall n base,
  0 < n ->
  2 <= base ->
  base <= n ->
  base_digits_z n base =
    base_digits_z (n / base) base ++ [48 + n mod base].
Proof.
  intros n base Hn Hbase Hle.
  rewrite base_digits_z_equation.
  replace (base <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
  replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  replace (n <? base) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

Lemma base_digits_z_length_pos_le : forall n base,
  0 < n ->
  2 <= base ->
  Zlength (base_digits_z n base) <= n.
Proof.
  intros n base Hn Hbase.
  functional induction (base_digits_z n base).
  - lia.
  - apply Z.leb_le in e0. lia.
  - rewrite Zlength_cons, Zlength_nil.
    lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    assert (0 < n / base).
    { assert (1 <= n / base) by (apply Z.div_le_lower_bound; lia). lia. }
    pose proof (IHl ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt n base ltac:(lia) ltac:(lia)).
    lia.
Qed.

Lemma base_digits_z_nonempty : forall n base,
  base_digits_z n base <> [].
Proof.
  intros n base.
  functional induction (base_digits_z n base); simpl; try discriminate.
  intro H.
  apply app_eq_nil in H.
  destruct H as [_ Hnil].
  discriminate Hnil.
Qed.

Lemma base_digits_pos_step : forall n base,
  0 < n ->
  2 <= base ->
  base_digits_pos_z n base =
    base_digits_pos_z (n / base) base ++ [48 + n mod base].
Proof.
  intros n base Hn Hbase.
  unfold base_digits_pos_z at 1.
  replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (Z.ltb_spec n base) as [Hlt | Hge].
  - rewrite base_digits_z_small by lia.
    unfold base_digits_pos_z.
    replace (n / base <=? 0) with true.
    + rewrite app_nil_l. rewrite Z.mod_small by lia. reflexivity.
    + symmetry. apply Z.leb_le.
      rewrite Z.div_small by lia. lia.
  - rewrite base_digits_z_step by lia.
    unfold base_digits_pos_z at 1.
    assert (0 < n / base).
    { assert (1 <= n / base) by (apply Z.div_le_lower_bound; lia).
      lia. }
    replace (n / base <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
    reflexivity.
Qed.

Lemma base_count_state_init : forall x base,
  0 < x ->
  base_count_state_z x base x 0.
Proof.
  intros x base Hx.
  unfold base_count_state_z.
  lia.
Qed.

Lemma base_count_state_step : forall orig base t digits,
  0 < t ->
  2 <= base ->
  base_count_state_z orig base t digits ->
  base_count_state_z orig base (t / base) (digits + 1).
Proof.
  intros orig base t digits Ht Hbase [Ht0 [Hd Hlen]].
  unfold base_count_state_z.
  split; [apply Z.div_pos; lia | split; [lia |]].
  rewrite (base_digits_pos_step t base) in Hlen by lia.
  rewrite Zlength_app in Hlen.
  change (Zlength [48 + t mod base]) with 1 in Hlen.
  lia.
Qed.

Lemma base_count_state_done : forall orig base digits,
  0 < orig ->
  base_count_state_z orig base 0 digits ->
  digits = Zlength (base_digits_z orig base).
Proof.
  intros orig base digits Horig [_ [Hd Hlen]].
  unfold base_digits_pos_z in Hlen.
  replace (0 <=? 0) with true in Hlen by (symmetry; apply Z.leb_le; lia).
  replace (orig <=? 0) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
  change (Zlength (@nil Z)) with 0 in Hlen.
  lia.
Qed.

Lemma base_fill_state_init : forall orig base,
  0 < orig ->
  base_fill_state_z orig base orig (Zlength (base_digits_z orig base)) [].
Proof.
  intros orig base Horig.
  unfold base_fill_state_z, base_digits_pos_z.
  replace (orig <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  repeat split; try lia.
  - apply Zlength_nonneg.
  - rewrite app_nil_r. reflexivity.
Qed.

Lemma base_fill_state_step : forall orig base x digits suffix,
  0 < x ->
  2 <= base ->
  base_fill_state_z orig base x digits suffix ->
  base_fill_state_z orig base (x / base) (digits - 1)
    ((48 + x mod base) :: suffix).
Proof.
  intros orig base x digits suffix Hx Hbase [Hx0 [Hd [Hdigits Hsplit]]].
  unfold base_fill_state_z.
  rewrite (base_digits_pos_step x base) in Hsplit by lia.
  rewrite (base_digits_pos_step x base) in Hdigits by lia.
  rewrite Zlength_app in Hdigits.
  change (Zlength [48 + x mod base]) with 1 in Hdigits.
  assert (Hdiv_nonneg : 0 <= x / base) by (apply Z.div_pos; lia).
  assert (Hprefix_len : 0 <= Zlength (base_digits_pos_z (x / base) base))
    by apply Zlength_nonneg.
  split; [exact Hdiv_nonneg | split; [lia | split; [|]]].
  - rewrite Hdigits. lia.
  - rewrite Hsplit.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma base_fill_state_done : forall orig base suffix,
  base_fill_state_z orig base 0 0 suffix ->
  suffix = base_digits_z orig base.
Proof.
  intros orig base suffix [_ [_ [_ Hsplit]]].
  unfold base_digits_pos_z in Hsplit.
  replace (0 <=? 0) with true in Hsplit by (symmetry; apply Z.leb_le; lia).
  simpl in Hsplit.
  symmetry. exact Hsplit.
Qed.

Lemma base_fill_full_state_init : forall orig base,
  0 < orig ->
  base_fill_full_state_z orig base orig
    (Zlength (base_digits_z orig base))
    (repeat_Z 0 (Zlength (base_digits_z orig base))).
Proof.
  intros orig base Horig.
  exists [].
  split.
  - apply base_fill_state_init. exact Horig.
  - rewrite app_nil_r. reflexivity.
Qed.

Lemma base_fill_full_state_done : forall orig base out_l,
  base_fill_full_state_z orig base 0 0 out_l ->
  out_l = base_digits_z orig base.
Proof.
  intros orig base out_l [suffix [Hstate Hout]].
  pose proof (base_fill_state_done _ _ _ Hstate) as Hsuffix.
  subst suffix.
  rewrite Hout.
  unfold repeat_Z. simpl. reflexivity.
Qed.

Lemma replace_Znth_boundary_app : forall {A: Type} (prefix tail : list A) x y,
  replace_Znth (Zlength prefix) x (prefix ++ y :: tail) =
  prefix ++ x :: tail.
Proof.
  intros A prefix.
  induction prefix as [|a prefix IH]; intros tail x y.
  - reflexivity.
  - rewrite Zlength_cons.
    change (replace_Znth (Z.succ (Zlength prefix)) x
              (a :: (prefix ++ y :: tail)) =
            a :: prefix ++ x :: tail).
    unfold replace_Znth at 1.
    simpl.
    replace (Z.to_nat (Z.succ (Zlength prefix))) with
      (S (Z.to_nat (Zlength prefix))) by (rewrite Zlength_correct; lia).
    simpl.
    fold (@replace_Znth A (Zlength prefix) x (prefix ++ y :: tail)).
    rewrite (IH tail x y).
    reflexivity.
Qed.

Lemma Zlength_replace_Znth_44 : forall {A: Type} (l : list A) n (v : A),
  0 <= n < Zlength l ->
  Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v Hrange.
  revert n Hrange.
  induction l as [|a l IH]; intros n Hrange; simpl.
  - rewrite Zlength_nil in Hrange. lia.
  - unfold replace_Znth in *.
    destruct (Z.to_nat n) eqn:Hn; simpl.
    + repeat rewrite Zlength_cons. reflexivity.
    + repeat rewrite Zlength_cons.
      specialize (IH (Z.of_nat n0)).
      unfold replace_Znth in IH.
      rewrite Nat2Z.id in IH.
      rewrite IH by (rewrite Zlength_cons in Hrange; lia).
      reflexivity.
Qed.

Lemma replace_Znth_repeat_suffix : forall d suffix v,
  0 <= d ->
  replace_Znth d v (repeat_Z 0 (d + 1) ++ suffix) =
  repeat_Z 0 d ++ v :: suffix.
Proof.
  intros d suffix v Hd.
  rewrite repeat_Z_tail by lia.
  rewrite <- app_assoc.
  change ([0] ++ suffix) with (0 :: suffix).
  assert (Hlen : Zlength (repeat_Z 0 d) = d)
    by (rewrite Zlength_repeat_Z; lia).
  rewrite <- Hlen at 1.
  rewrite replace_Znth_boundary_app.
  reflexivity.
Qed.

Lemma base_fill_full_state_step : forall orig base x digits out_l,
  0 < x ->
  2 <= base ->
  0 <= digits ->
  base < 10 ->
  base_fill_full_state_z orig base x (digits + 1) out_l ->
  base_fill_full_state_z orig base (x / base) digits
    (replace_Znth digits (signed_last_nbits (48 + x mod base) 8) out_l).
Proof.
  intros orig base x digits out_l Hx Hbase Hdigits Hbase10
    [suffix [Hstate Hout]].
  exists ((48 + x mod base) :: suffix).
  split.
  - pose proof (base_fill_state_step orig base x (digits + 1) suffix
      Hx Hbase Hstate) as Hstep.
    replace (digits + 1 - 1) with digits in Hstep by lia.
    exact Hstep.
  - rewrite Hout.
    rewrite (signed_last_nbits_eq (48 + x mod base) 8)
      by (pose proof (Z.mod_pos_bound x base ltac:(lia)); lia).
    apply replace_Znth_repeat_suffix. lia.
Qed.

Lemma base_fill_full_state_positive_digits : forall orig base x digits out_l,
  0 < x ->
  2 <= base ->
  base_fill_full_state_z orig base x digits out_l ->
  1 <= digits.
Proof.
  intros orig base x digits out_l Hx Hbase [suffix [[_ [_ [Hdigits _]]] _]].
  rewrite Hdigits.
  unfold base_digits_pos_z.
  replace (x <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (base_digits_z x base) eqn:Hbd.
  - exfalso. apply (base_digits_z_nonempty x base). exact Hbd.
  - rewrite Zlength_cons.
    pose proof (Zlength_nonneg l). lia.
Qed.

Lemma base_digits_z_digit_range : forall n base c,
  0 <= n ->
  2 <= base < 10 ->
  In c (base_digits_z n base) ->
  48 <= c <= 57 /\ c - 48 < base.
Proof.
  intros n base c Hn Hbase.
  functional induction (base_digits_z n base); intros Hin; simpl in Hin.
  - destruct Hin as [<- | []]; lia.
  - destruct Hin as [<- | []]; lia.
  - destruct Hin as [<- | []].
    apply Z.leb_gt in e0.
    apply Z.ltb_lt in e1.
    change (48 <= 48 + n <= 57 /\ 48 + n - 48 < base).
    lia.
  - apply in_app_or in Hin.
    destruct Hin as [Hin | [<- | []]].
    + apply IHl.
      * apply Z.div_pos; lia.
      * lia.
      * exact Hin.
    + change (48 <= 48 + n mod base <= 57 /\
              48 + n mod base - 48 < base).
      split.
      * pose proof (Z.mod_pos_bound n base ltac:(lia)).
        lia.
      * pose proof (Z.mod_pos_bound n base ltac:(lia)).
        lia.
Qed.

Lemma digits_value_z_app : forall base l1 l2,
  digits_value_z base (l1 ++ l2) =
  digits_value_z base l2 +
  digits_value_z base l1 * Z.pow base (Zlength l2).
Proof.
  induction l1 as [|c rest IH]; intros l2; simpl.
  - lia.
  - rewrite IH.
    rewrite Zlength_app.
    simpl.
    rewrite Z.pow_add_r by (apply Zlength_nonneg || lia).
    ring.
Qed.

Lemma base_digits_z_value : forall n base,
  0 <= n ->
  2 <= base < 10 ->
  digits_value_z base (base_digits_z n base) = n.
Proof.
  intros n base Hn Hbase.
  functional induction (base_digits_z n base).
  - lia.
  - apply Z.leb_le in e0. simpl. lia.
  - simpl. apply Z.leb_gt in e0. apply Z.ltb_lt in e1.
    unfold digit_value_z.
    change ((48 + n - 48) * 1 = n). lia.
  - rewrite digits_value_z_app.
    simpl.
    rewrite IHl by (try lia; apply Z.div_pos; lia).
    replace (Z.pow base 1) with base by (simpl; lia).
    replace (Z.pow_pos base 1) with (base * 1) by reflexivity.
    change (digit_value_z (48 + n mod base) * 1 + n / base * (base * 1) = n).
    replace (digit_value_z (48 + n mod base)) with (n mod base)
      by (unfold digit_value_z; lia).
    pose proof (Z.div_mod n base ltac:(lia)).
    nia.
Qed.

Lemma fold_left_digit_value_z : forall l base acc,
  0 <= acc ->
  0 <= base ->
  (forall c, In c l -> 0 <= digit_value_z c) ->
  fold_left (fun acc d => (acc * Z.to_nat base + d)%nat)
    (map Z.to_nat (map digit_value_z l)) (Z.to_nat acc) =
  Z.to_nat (acc * Z.pow base (Zlength l) + digits_value_z base l).
Proof.
  induction l as [|c rest IH]; intros base acc Hacc Hbase Hdigits; simpl.
  - replace (Zlength (@nil Z)) with 0 by reflexivity.
    rewrite Z.mul_1_r.
    rewrite Z.add_0_r.
    reflexivity.
  - replace (Z.to_nat acc * Z.to_nat base + Z.to_nat (digit_value_z c))%nat
      with (Z.to_nat (acc * base + digit_value_z c)).
    2:{
      rewrite Z2Nat.inj_add.
      - rewrite Z2Nat.inj_mul by lia. reflexivity.
      - apply Z.mul_nonneg_nonneg; lia.
      - apply Hdigits. left. reflexivity.
    }
    rewrite IH.
    2:{ pose proof (Hdigits c (or_introl eq_refl)); nia. }
    2:{ exact Hbase. }
    2:{ intros d Hd. apply Hdigits. right. exact Hd. }
    f_equal.
    rewrite Zlength_cons.
    replace (Z.succ (Zlength rest)) with (Zlength rest + 1) by lia.
    rewrite Z.pow_add_r by (lia || apply Zlength_nonneg).
    simpl.
    replace (Z.pow_pos base 1) with (base * 1) by reflexivity.
    ring.
Qed.

Lemma nat_of_digit_ascii_of_z : forall z,
  48 <= z <= 57 ->
  nat_of_digit (ascii_of_z z) = Z.to_nat (z - 48).
Proof.
  intros z Hz.
  unfold nat_of_digit.
  rewrite nat_of_ascii_ascii_of_z by lia.
  cbn.
  replace (Pos.to_nat 48) with (Z.to_nat 48) by reflexivity.
  rewrite <- Z2Nat.inj_sub by lia.
  reflexivity.
Qed.

Lemma map_nat_of_digit_base_digits : forall n base,
  0 <= n ->
  2 <= base < 10 ->
  map nat_of_digit (map ascii_of_z (base_digits_z n base)) =
  map Z.to_nat (map digit_value_z (base_digits_z n base)).
Proof.
  intros n base Hn Hbase.
  repeat rewrite map_map.
  apply map_ext_in.
  intros c Hin.
  pose proof (base_digits_z_digit_range n base c Hn Hbase Hin) as [Hc _].
  apply nat_of_digit_ascii_of_z; lia.
Qed.

Lemma problem_44_spec_z_intro : forall x base out_l,
  0 <= x ->
  2 <= base < 10 ->
  out_l = base_digits_z x base ->
  problem_44_spec_z x base out_l.
Proof.
  intros x base out_l Hx Hbase Hout.
  subst out_l.
  unfold problem_44_spec_z, problem_44_spec.
  split.
  - rewrite Forall_forall.
    intros d Hd.
    rewrite in_map_iff in Hd.
    destruct Hd as [a [<- Ha]].
    rewrite in_map_iff in Ha.
    destruct Ha as [c [<- Hin]].
    rewrite nat_of_digit_ascii_of_z.
    + pose proof (base_digits_z_digit_range x base c Hx Hbase Hin) as [Hc Hlt].
      apply Z2Nat.inj_lt; lia.
    + pose proof (base_digits_z_digit_range x base c Hx Hbase Hin) as [Hc _].
      lia.
  - rewrite map_nat_of_digit_base_digits by lia.
    change 0%nat with (Z.to_nat 0).
    rewrite fold_left_digit_value_z.
    2-4: try lia.
    2:{ intros c Hin.
        pose proof (base_digits_z_digit_range x base c Hx Hbase Hin) as [Hc _].
        unfold digit_value_z; lia. }
    rewrite base_digits_z_value by lia.
    lia.
Qed.

Lemma problem_44_spec_z_zero : forall base,
  2 <= base < 10 ->
  problem_44_spec_z 0 base [48].
Proof.
  intros base Hbase.
  apply problem_44_spec_z_intro; try lia.
  rewrite base_digits_z_zero by lia.
  reflexivity.
Qed.

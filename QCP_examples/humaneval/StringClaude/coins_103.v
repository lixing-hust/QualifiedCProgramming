Load "../spec/103".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
From SimpleC.EE Require Import string_bridge coins_44.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition problem_103_pre_z (n m : Z) : Prop :=
  problem_103_pre n m.

Definition problem_103_spec_z (n m : Z) (output : list Z) : Prop :=
  problem_103_spec n m (string_of_list_z output).

Definition avg_103 (n m : Z) : Z := (n + m) / 2.

Definition binary_digits_z (n : Z) : list Z :=
  base_digits_z n 2.

Definition binary_count_state_z (orig t digits : Z) : Prop :=
  base_count_state_z orig 2 t digits.

Definition binary_fill_full_state_z
  (orig x digits : Z) (out_l : list Z) : Prop :=
  base_fill_full_state_z orig 2 x digits out_l.

Lemma string_of_list_z_app : forall a b,
  string_of_list_z (a ++ b) = string_of_list_z a ++ string_of_list_z b.
Proof.
  induction a; simpl; intros; congruence.
Qed.

Lemma string_append_assoc : forall a b c,
  (a ++ b) ++ c = a ++ (b ++ c).
Proof.
  induction a; simpl; intros; congruence.
Qed.

Lemma ascii_of_z_48 : ascii_of_z 48 = "0"%char.
Proof. reflexivity. Qed.

Lemma ascii_of_z_49 : ascii_of_z 49 = "1"%char.
Proof. reflexivity. Qed.

Lemma ascii_of_z_45 : ascii_of_z 45 = "-"%char.
Proof. reflexivity. Qed.

Lemma string_of_list_z_0 : string_of_list_z [48] = "0".
Proof. reflexivity. Qed.

Lemma string_of_list_z_neg1 : string_of_list_z [45; 49] = "-1".
Proof. reflexivity. Qed.

Lemma zpos_xO_div2 : forall p,
  Z.pos (xO p) / 2 = Z.pos p.
Proof.
  intros p.
  rewrite Pos2Z.inj_xO.
  rewrite Z.mul_comm.
  apply Z.div_mul; lia.
Qed.

Lemma zpos_xO_mod2 : forall p,
  Z.pos (xO p) mod 2 = 0.
Proof.
  intros p.
  rewrite Pos2Z.inj_xO.
  rewrite Z.mul_comm.
  apply Z.mod_mul; lia.
Qed.

Lemma zpos_xI_div2 : forall p,
  Z.pos (xI p) / 2 = Z.pos p.
Proof.
  intros p.
  rewrite Pos2Z.inj_xI.
  replace (2 * Z.pos p + 1) with (Z.pos p * 2 + 1) by lia.
  rewrite Z.div_add_l by lia.
  rewrite Z.div_small; lia.
Qed.

Lemma zpos_xI_mod2 : forall p,
  Z.pos (xI p) mod 2 = 1.
Proof.
  intros p.
  rewrite Pos2Z.inj_xI.
  replace (2 * Z.pos p + 1) with (Z.pos p * 2 + 1) by lia.
  rewrite Z.add_comm.
  rewrite Z_mod_plus_full.
  reflexivity.
Qed.

Lemma base_digits_z_two_to_binary : forall n,
  0 <= n ->
  string_of_list_z (base_digits_z n 2) = to_binary n.
Proof.
  intros n Hn.
  destruct n as [| p | p]; try lia.
  - rewrite base_digits_z_zero by lia. reflexivity.
  - induction p.
    + rewrite base_digits_z_step by (try lia; vm_compute; lia).
      rewrite zpos_xI_div2, zpos_xI_mod2.
      rewrite string_of_list_z_app, IHp by lia.
      simpl.
      rewrite ascii_of_z_49.
      reflexivity.
    + destruct p.
      * rewrite base_digits_z_step by (try lia; vm_compute; lia).
        rewrite zpos_xO_div2, zpos_xO_mod2.
        rewrite string_of_list_z_app, IHp by lia.
        simpl.
        rewrite ascii_of_z_48.
        reflexivity.
      * rewrite base_digits_z_step by (try lia; vm_compute; lia).
        rewrite zpos_xO_div2, zpos_xO_mod2.
        rewrite string_of_list_z_app, IHp by lia.
        simpl.
        rewrite ascii_of_z_48.
        reflexivity.
      * rewrite base_digits_z_step by (try lia; vm_compute; lia).
        rewrite zpos_xO_div2, zpos_xO_mod2.
        rewrite base_digits_z_small by lia.
        reflexivity.
    + rewrite base_digits_z_small by lia.
      reflexivity.
Qed.

Lemma binary_digits_z_length_pos_le : forall n,
  0 < n ->
  Zlength (binary_digits_z n) <= n.
Proof.
  intros n Hn.
  unfold binary_digits_z.
  apply base_digits_z_length_pos_le; lia.
Qed.

Lemma binary_digits_z_nonempty : forall n,
  binary_digits_z n <> [].
Proof.
  intros n.
  unfold binary_digits_z.
  apply base_digits_z_nonempty.
Qed.

Lemma binary_count_state_init : forall orig,
  0 < orig ->
  binary_count_state_z orig orig 0.
Proof.
  intros orig Horig.
  unfold binary_count_state_z.
  apply base_count_state_init; lia.
Qed.

Lemma binary_count_state_step : forall orig t digits,
  0 < t ->
  binary_count_state_z orig t digits ->
  binary_count_state_z orig (t / 2) (digits + 1).
Proof.
  intros orig t digits Ht Hstate.
  unfold binary_count_state_z in *.
  apply base_count_state_step; lia || exact Hstate.
Qed.

Lemma binary_count_state_done : forall orig digits,
  0 < orig ->
  binary_count_state_z orig 0 digits ->
  digits = Zlength (binary_digits_z orig).
Proof.
  intros orig digits Horig Hstate.
  unfold binary_count_state_z, binary_digits_z in *.
  apply base_count_state_done; lia || exact Hstate.
Qed.

Lemma binary_count_state_step_safe : forall orig t digits,
  0 < orig ->
  orig < INT_MAX ->
  0 < t ->
  binary_count_state_z orig t digits ->
  digits + 1 < INT_MAX.
Proof.
  intros orig t digits Horig Hbound Ht [_ [Hdigits Hlen]].
  unfold binary_digits_z.
  unfold base_digits_pos_z in Hlen.
  replace (Z.leb t 0) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
  replace (Z.leb orig 0) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
  destruct (base_digits_z t 2) eqn:Hbd.
  - exfalso. apply (base_digits_z_nonempty t 2). exact Hbd.
  - rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg l).
    pose proof (base_digits_z_length_pos_le orig 2 Horig ltac:(lia)).
    lia.
Qed.

Lemma binary_fill_full_state_init : forall orig,
  0 < orig ->
  binary_fill_full_state_z orig orig (Zlength (binary_digits_z orig))
    (repeat_Z 0 (Zlength (binary_digits_z orig))).
Proof.
  intros orig Horig.
  unfold binary_fill_full_state_z, binary_digits_z.
  apply base_fill_full_state_init; lia.
Qed.

Lemma binary_fill_full_state_step : forall orig x digits out_l,
  0 < x ->
  0 <= digits ->
  binary_fill_full_state_z orig x (digits + 1) out_l ->
  binary_fill_full_state_z orig (x / 2) digits
    (replace_Znth digits (signed_last_nbits (48 + x mod 2) 8) out_l).
Proof.
  intros orig x digits out_l Hx Hdigits Hstate.
  unfold binary_fill_full_state_z in *.
  apply base_fill_full_state_step; lia || exact Hstate.
Qed.

Lemma binary_fill_full_state_done : forall orig out_l,
  binary_fill_full_state_z orig 0 0 out_l ->
  out_l = binary_digits_z orig.
Proof.
  intros orig out_l Hstate.
  unfold binary_fill_full_state_z, binary_digits_z in *.
  apply base_fill_full_state_done; exact Hstate.
Qed.

Lemma problem_103_spec_z_neg : forall n m,
  n > m ->
  problem_103_spec_z n m [45; 49].
Proof.
  intros n m Hgt.
  unfold problem_103_spec_z, problem_103_spec, rounded_avg_impl.
  rewrite string_of_list_z_neg1.
  replace (n >? m) with true by (symmetry; apply Z.gtb_gt; lia).
  reflexivity.
Qed.

Lemma problem_103_spec_z_binary : forall n m out_l,
  n <= m ->
  0 <= avg_103 n m ->
  out_l = binary_digits_z (avg_103 n m) ->
  problem_103_spec_z n m out_l.
Proof.
  intros n m out_l Hle Havg Hout.
  subst out_l.
  unfold avg_103 in Havg.
  unfold problem_103_spec_z, problem_103_spec, rounded_avg_impl, avg_103.
  destruct (Z.gtb_spec n m) as [Hgt | Hngt]; [lia | simpl].
  unfold binary_digits_z.
  apply base_digits_z_two_to_binary.
  lia.
Qed.

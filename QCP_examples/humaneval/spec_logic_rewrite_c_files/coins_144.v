Load "../spec/144".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition ascii_of_z_144 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_144 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_144 c) (string_of_list_z_144 rest)
  end.

Definition bool_of_z_144 (z : Z) : bool :=
  Z.eqb z 1.

Definition problem_144_pre_z (x n : list Z) : Prop :=
  problem_144_pre (string_of_list_z_144 x) (string_of_list_z_144 n).

Definition problem_144_spec_z (x n : list Z) (output : Z) : Prop :=
  problem_144_spec
    (string_of_list_z_144 x) (string_of_list_z_144 n)
    (bool_of_z_144 output).

Definition digit_code_z_144 (c : Z) : Prop :=
  48 <= c <= 57.

Definition digit_value_z_144 (c : Z) : Z :=
  c - 48.

Definition parse_digits_z_144 (l : list Z) : Z :=
  fold_left (fun acc c => acc * 10 + digit_value_z_144 c) l 0.

Definition fraction_parts_z_144
    (l : list Z) (slash num den : Z) : Prop :=
  0 < slash < Zlength l /\
  Znth slash l 0 = 47 /\
  (forall k, 0 <= k < slash -> digit_code_z_144 (Znth k l 0)) /\
  (forall k, slash < k < Zlength l -> digit_code_z_144 (Znth k l 0)) /\
  num = parse_digits_z_144 (sublist 0 slash l) /\
  den = parse_digits_z_144 (sublist (slash + 1) (Zlength l) l) /\
  (forall i, 0 <= i <= slash ->
     0 <= parse_digits_z_144 (sublist 0 i l) <= num) /\
  (forall i, slash + 1 <= i <= Zlength l ->
     0 <= parse_digits_z_144 (sublist (slash + 1) i l) <= den) /\
  Parse_Fraction
    (list_ascii_of_string (string_of_list_z_144 l))
    (Z.to_nat num) (Z.to_nat den) /\
  0 < num /\ 0 < den.

Definition fraction_scan_state_144
    (l : list Z) (slash full_num i seen num den : Z) : Prop :=
  0 <= i <= Zlength l /\
  ((i <= slash /\ seen = 0 /\
    num = parse_digits_z_144 (sublist 0 i l) /\ den = 0) \/
   (slash < i /\ seen = 1 /\ num = full_num /\
    den = parse_digits_z_144 (sublist (slash + 1) i l))).

Lemma valid_string_c_string_inside_144 : forall l i,
  valid_string l ->
  0 <= i < string_length l ->
  0 <= Znth i (c_string l) 0 <= 127.
Proof.
  intros l i [Hascii _] Hi.
  rewrite c_string_Znth_inside by exact Hi.
  apply Hascii.
  exact Hi.
Qed.

Lemma parse_digits_z_144_empty :
  parse_digits_z_144 [] = 0.
Proof. reflexivity. Qed.

Lemma parse_digits_z_144_snoc : forall l c,
  parse_digits_z_144 (l ++ [c]) =
  parse_digits_z_144 l * 10 + digit_value_z_144 c.
Proof.
  intros l c.
  unfold parse_digits_z_144.
  rewrite fold_left_app.
  reflexivity.
Qed.

Lemma sublist_snoc_z_144 : forall l lo i,
  0 <= lo <= i ->
  i < Zlength l ->
  sublist lo (i + 1) l = sublist lo i l ++ [Znth i l 0].
Proof.
  intros l lo i Hlo Hi.
  rewrite (sublist_split lo (i + 1) i l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  reflexivity.
Qed.

Lemma sublist_same_z_144 : forall (l : list Z) i,
  sublist i i l = [].
Proof.
  intros l i.
  unfold sublist.
  apply skipn_all2.
  rewrite firstn_length.
  lia.
Qed.

Lemma fraction_scan_state_144_init : forall l slash num den,
  fraction_parts_z_144 l slash num den ->
  fraction_scan_state_144 l slash num 0 0 0 0.
Proof.
  intros l slash num den Hparts.
  unfold fraction_parts_z_144 in Hparts.
  unfold fraction_scan_state_144.
  destruct Hparts as (Hslash & _).
  split; [lia|].
  left.
  repeat split; try lia.
Qed.

Lemma fraction_scan_state_144_finish : forall l slash num den seen a b,
  fraction_parts_z_144 l slash num den ->
  fraction_scan_state_144 l slash num (Zlength l) seen a b ->
  seen = 1 /\ a = num /\ b = den.
Proof.
  intros l slash num den seen a b Hparts Hscan.
  unfold fraction_parts_z_144 in Hparts.
  destruct Hparts as (Hslash & _ & _ & _ & Hnum & Hden & _).
  unfold fraction_scan_state_144 in Hscan.
  destruct Hscan as [_ [Hbefore | Hafter]].
  - destruct Hbefore as [Hle _]. lia.
  - destruct Hafter as (_ & Hseen & Ha & Hb).
    repeat split; try assumption.
    now rewrite <- Hden in Hb.
Qed.

Lemma fraction_scan_state_144_num_step : forall l slash full_num full_den i a b,
  fraction_parts_z_144 l slash full_num full_den ->
  fraction_scan_state_144 l slash full_num i 0 a b ->
  i < Zlength l ->
  Znth i l 0 <> 47 ->
  fraction_scan_state_144 l slash full_num (i + 1) 0
    (a * 10 + digit_value_z_144 (Znth i l 0)) b.
Proof.
  intros l slash full_num full_den i a b Hparts Hscan Hi Hnot.
  unfold fraction_parts_z_144 in Hparts.
  destruct Hparts as
    (Hslash & Hslash_char & Hnum_digits & Hden_digits & Hnum & Hden &
     Hnum_bounds & Hden_bounds & Hparse & Hnum_pos & Hden_pos).
  unfold fraction_scan_state_144 in Hscan |- *.
  destruct Hscan as (Hirange & [Hbefore | Hafter]).
  - destruct Hbefore as (His & Hseen & Ha & Hb).
    assert (Hi_lt : i < slash).
    { destruct (Z.eq_dec i slash) as [-> | Hne]; [contradiction|lia]. }
    split; [lia|].
    left; repeat split; try lia; try assumption.
    rewrite (sublist_snoc_z_144 l 0 i) by lia.
    rewrite parse_digits_z_144_snoc.
    now rewrite Ha.
  - destruct Hafter as (_ & Hseen & _).
    discriminate.
Qed.

Lemma fraction_scan_state_144_den_step : forall l slash full_num full_den i a b,
  fraction_parts_z_144 l slash full_num full_den ->
  fraction_scan_state_144 l slash full_num i 1 a b ->
  i < Zlength l ->
  Znth i l 0 <> 47 ->
  fraction_scan_state_144 l slash full_num (i + 1) 1 a
    (b * 10 + digit_value_z_144 (Znth i l 0)).
Proof.
  intros l slash full_num full_den i a b Hparts Hscan Hi Hnot.
  unfold fraction_parts_z_144 in Hparts.
  destruct Hparts as
    (Hslash & Hslash_char & Hnum_digits & Hden_digits & Hnum & Hden &
     Hnum_bounds & Hden_bounds & Hparse & Hnum_pos & Hden_pos).
  unfold fraction_scan_state_144 in Hscan |- *.
  destruct Hscan as (Hirange & [Hbefore | Hafter]).
  - destruct Hbefore as (_ & Hseen & _).
    discriminate.
  - destruct Hafter as (His & Hseen & Ha & Hb).
    split; [lia|].
    right; repeat split; try lia; try assumption.
    rewrite (sublist_snoc_z_144 l (slash + 1) i) by lia.
    rewrite parse_digits_z_144_snoc.
    now rewrite Hb.
Qed.

Lemma fraction_scan_state_144_slash_step : forall l slash full_num full_den i seen a b,
  fraction_parts_z_144 l slash full_num full_den ->
  fraction_scan_state_144 l slash full_num i seen a b ->
  i < Zlength l ->
  Znth i l 0 = 47 ->
  fraction_scan_state_144 l slash full_num (i + 1) 1 a b.
Proof.
  intros l slash full_num full_den i seen a b Hparts Hscan Hi Hchar.
  unfold fraction_parts_z_144 in Hparts.
  destruct Hparts as
    (Hslash & Hslash_char & Hnum_digits & Hden_digits & Hnum & Hden &
     Hnum_bounds & Hden_bounds & Hparse & Hnum_pos & Hden_pos).
  unfold fraction_scan_state_144 in Hscan |- *.
  destruct Hscan as (Hirange & [Hbefore | Hafter]).
  - destruct Hbefore as (His & Hseen & Ha & Hb).
    assert (Heq : i = slash).
    { destruct (Z_lt_ge_dec i slash) as [Hlt | Hge].
      - specialize (Hnum_digits i ltac:(lia)).
        unfold digit_code_z_144 in Hnum_digits.
        rewrite Hchar in Hnum_digits; lia.
      - lia. }
    subst i.
    split; [lia|].
    right; repeat split; try lia; try assumption.
    rewrite Hb.
    rewrite sublist_same_z_144.
    reflexivity.
  - destruct Hafter as (His & Hseen & Ha & Hb).
    specialize (Hden_digits i ltac:(lia)).
    unfold digit_code_z_144 in Hden_digits.
    rewrite Hchar in Hden_digits; lia.
Qed.

Lemma fraction_scan_state_144_bounds : forall l slash full_num full_den i seen a b,
  fraction_parts_z_144 l slash full_num full_den ->
  fraction_scan_state_144 l slash full_num i seen a b ->
  0 <= a <= full_num /\ 0 <= b <= full_den.
Proof.
  intros l slash full_num full_den i seen a b Hparts Hscan.
  unfold fraction_parts_z_144 in Hparts.
  destruct Hparts as
    (Hslash & Hslash_char & Hnum_digits & Hden_digits & Hnum & Hden &
     Hnum_bounds & Hden_bounds & Hparse & Hnum_pos & Hden_pos).
  unfold fraction_scan_state_144 in Hscan.
  destruct Hscan as (Hirange & [Hbefore | Hafter]).
  - destruct Hbefore as (His & Hseen & Ha & Hb).
    specialize (Hnum_bounds i ltac:(lia)).
    rewrite Ha, Hb; lia.
  - destruct Hafter as (His & Hseen & Ha & Hb).
    specialize (Hden_bounds i ltac:(lia)).
    rewrite Ha, Hb; lia.
Qed.

Lemma problem_144_spec_z_from_parts : forall x n sx sy a b c d output,
  fraction_parts_z_144 x sx a b ->
  fraction_parts_z_144 n sy c d ->
  output = (if Z.eqb (Z.rem (a * c) (b * d)) 0 then 1 else 0) ->
  problem_144_spec_z x n output.
Proof.
  intros x n sx sy a b c d output Hx Hn Hout.
  unfold fraction_parts_z_144 in Hx, Hn.
  destruct Hx as (_ & _ & _ & _ & _ & _ & _ & _ & Hpx & Ha & Hb).
  destruct Hn as (_ & _ & _ & _ & _ & _ & _ & _ & Hpn & Hc & Hd).
  unfold problem_144_spec_z, problem_144_spec, bool_of_z_144.
  exists (Z.to_nat a), (Z.to_nat b), (Z.to_nat c), (Z.to_nat d).
  repeat split; try assumption; try lia.
  rewrite Hout.
  destruct (Z.eqb_spec (Z.rem (a * c) (b * d)) 0) as [Hrem | Hrem].
  - cbn.
    symmetry.
    apply Nat.eqb_eq.
    apply Nat2Z.inj.
    rewrite Nat2Z.inj_mod by nia.
    rewrite !Nat2Z.inj_mul.
    rewrite !Z2Nat.id by lia.
    rewrite <- Z.rem_mod_nonneg by nia.
    exact Hrem.
  - cbn.
    symmetry.
    apply Nat.eqb_neq.
    intro Hnat.
    apply Hrem.
    apply (f_equal Z.of_nat) in Hnat.
    rewrite Nat2Z.inj_mod in Hnat by nia.
    rewrite !Nat2Z.inj_mul in Hnat.
    rewrite !Z2Nat.id in Hnat by lia.
    rewrite <- Z.rem_mod_nonneg in Hnat by nia.
    exact Hnat.
Qed.

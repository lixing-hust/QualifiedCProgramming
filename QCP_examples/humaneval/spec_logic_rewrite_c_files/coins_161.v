Load "../spec/161".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Classical_Prop.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.
Require Import SimpleC.StdLib.string_lib.
Load "../StringClaude/string_bridge".
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition problem_161_pre_z (input : list Z) : Prop :=
  problem_161_pre (string_of_list_z input).

Definition problem_161_spec_z (input output : list Z) : Prop :=
  problem_161_spec (string_of_list_z input) (string_of_list_z output).

Definition lower_z_161 (c : Z) : Prop := 97 <= c <= 122.
Definition upper_z_161 (c : Z) : Prop := 65 <= c <= 90.
Definition letter_z_161 (c : Z) : Prop :=
  lower_z_161 c \/ upper_z_161 c.

Definition lower_zb_161 (c : Z) : bool :=
  (97 <=? c) && (c <=? 122).

Definition upper_zb_161 (c : Z) : bool :=
  (65 <=? c) && (c <=? 90).

Definition letter_zb_161 (c : Z) : bool :=
  lower_zb_161 c || upper_zb_161 c.

Definition nonletter_zb_161 (c : Z) : bool :=
  negb (letter_zb_161 c).

Definition flip_char_z_161 (c : Z) : Z :=
  if upper_zb_161 c then c + 32
  else if lower_zb_161 c then c - 32
  else c.

Definition nonletter_count_prefix_z_161
    (input : list Z) (i : Z) : Z :=
  Zlength
    (filter nonletter_zb_161 (sublist 0 i input)).

Definition flip_scan_state_z_161
    (input output : list Z) (i nonletters : Z) : Prop :=
  0 <= i <= Zlength input /\
  0 <= nonletters <= i /\
  output = map flip_char_z_161 (sublist 0 i input) /\
  nonletters = nonletter_count_prefix_z_161 input i.

Definition reverse_scan_state_z_161
    (input output : list Z) (i : Z) : Prop :=
  0 <= i <= Zlength input /\
  output = sublist 0 i (rev input).

Definition has_letter_z_161 (input : list Z) : Prop :=
  exists c, In c input /\ letter_z_161 c.

Definition no_letter_z_161 (input : list Z) : Prop :=
  Forall (fun c => ~ letter_z_161 c) input.

Definition flip_output_z_161 (input output : list Z) : Prop :=
  output = map flip_char_z_161 input.

Definition reverse_output_z_161 (input output : list Z) : Prop :=
  output = rev input.

Lemma c_string_inside_eq_161 : forall input i,
  0 <= i < Zlength input ->
  Znth i (c_string input) 0 = Znth i input 0.
Proof.
  intros input i Hi. apply c_string_Znth_inside. exact Hi.
Qed.

Lemma signed_last_nbits_8_eq_161 : forall c,
  0 <= c <= 127 -> signed_last_nbits c 8 = c.
Proof.
  intros c Hc. apply signed_last_nbits_eq; lia.
Qed.

Lemma Zlength_c_string_161 : forall input,
  Zlength (c_string input) = Zlength input + 1.
Proof.
  intros input.
  unfold c_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma flip_output_z_161_length : forall input output,
  flip_output_z_161 input output ->
  Zlength output = Zlength input.
Proof.
  intros input output Hout.
  unfold flip_output_z_161 in Hout. subst output.
  rewrite !Zlength_correct, map_length. reflexivity.
Qed.

Lemma reverse_output_z_161_length : forall input output,
  reverse_output_z_161 input output ->
  Zlength output = Zlength input.
Proof.
  intros input output Hout.
  unfold reverse_output_z_161 in Hout. subst output.
  rewrite !Zlength_correct, List.rev_length. reflexivity.
Qed.

Lemma lower_zb_161_true : forall c,
  lower_zb_161 c = true <-> lower_z_161 c.
Proof.
  intros c.
  unfold lower_zb_161, lower_z_161.
  rewrite andb_true_iff, !Z.leb_le.
  tauto.
Qed.

Lemma upper_zb_161_true : forall c,
  upper_zb_161 c = true <-> upper_z_161 c.
Proof.
  intros c.
  unfold upper_zb_161, upper_z_161.
  rewrite andb_true_iff, !Z.leb_le.
  tauto.
Qed.

Lemma letter_zb_161_true : forall c,
  letter_zb_161 c = true <-> letter_z_161 c.
Proof.
  intros c.
  unfold letter_zb_161, letter_z_161.
  rewrite orb_true_iff, lower_zb_161_true, upper_zb_161_true.
  tauto.
Qed.

Lemma nonletter_zb_161_true : forall c,
  nonletter_zb_161 c = true <-> ~ letter_z_161 c.
Proof.
  intros c.
  unfold nonletter_zb_161.
  split.
  - intros Hneg Hletter.
    apply negb_true_iff in Hneg.
    apply letter_zb_161_true in Hletter.
    congruence.
  - intros Hnot.
    apply negb_true_iff.
    destruct (letter_zb_161 c) eqn:Hletter; [|reflexivity].
    exfalso. apply Hnot. now apply letter_zb_161_true.
Qed.

Lemma sublist_snoc_161 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  reflexivity.
Qed.

Lemma flip_scan_state_z_161_init : forall input,
  flip_scan_state_z_161 input [] 0 0.
Proof.
  intros input.
  unfold flip_scan_state_z_161, nonletter_count_prefix_z_161.
  replace (sublist 0 0 input) with (@nil Z)
    by (symmetry; apply sublist_nil; lia).
  rewrite Zlength_nil.
  repeat split; try lia; try reflexivity; apply Zlength_nonneg.
Qed.

Lemma flip_char_z_161_upper : forall c,
  upper_z_161 c -> flip_char_z_161 c = c + 32.
Proof.
  intros c Hupper.
  unfold flip_char_z_161.
  rewrite (proj2 (upper_zb_161_true c) Hupper).
  reflexivity.
Qed.

Lemma flip_char_z_161_lower : forall c,
  ~ upper_z_161 c -> lower_z_161 c ->
  flip_char_z_161 c = c - 32.
Proof.
  intros c Hnot Hlower.
  unfold flip_char_z_161.
  assert (upper_zb_161 c = false) as Hu.
  { destruct (upper_zb_161 c) eqn:Hu; [|reflexivity].
    exfalso. apply Hnot. now apply upper_zb_161_true. }
  rewrite Hu, (proj2 (lower_zb_161_true c) Hlower).
  reflexivity.
Qed.

Lemma flip_char_z_161_nonletter : forall c,
  ~ upper_z_161 c -> ~ lower_z_161 c ->
  flip_char_z_161 c = c.
Proof.
  intros c Hupper Hlower.
  unfold flip_char_z_161.
  destruct (upper_zb_161 c) eqn:Hu.
  - exfalso. apply Hupper. now apply upper_zb_161_true.
  - destruct (lower_zb_161 c) eqn:Hl.
    + exfalso. apply Hlower. now apply lower_zb_161_true.
    + reflexivity.
Qed.

Lemma flip_scan_state_z_161_step_upper : forall input output i count c,
  flip_scan_state_z_161 input output i count ->
  0 <= i < Zlength input ->
  c = Znth i input 0 ->
  upper_z_161 c ->
  flip_scan_state_z_161 input (output ++ [c + 32]) (i + 1) count.
Proof.
  intros input output i count c Hstate Hi -> Hupper.
  unfold flip_scan_state_z_161 in *.
  destruct Hstate as [Hib [Hcount [Hout Hcountdef]]].
  repeat split; try lia.
  - rewrite sublist_snoc_161 by lia.
    rewrite map_app; simpl.
    rewrite Hout, flip_char_z_161_upper by exact Hupper.
    reflexivity.
  - unfold nonletter_count_prefix_z_161 in *.
    rewrite sublist_snoc_161 by lia.
    rewrite filter_app, Zlength_app.
    assert (nonletter_zb_161 (Znth i input 0) = false) as Hnon.
    { unfold nonletter_zb_161.
      rewrite (proj2 (letter_zb_161_true _) (or_intror Hupper)).
      reflexivity. }
    rewrite <- Hcountdef.
    change (count = count +
      Zlength (if nonletter_zb_161 (Znth i input 0)
               then [Znth i input 0] else [])).
    rewrite Hnon, Zlength_nil. lia.
Qed.

Lemma flip_scan_state_z_161_step_lower : forall input output i count c,
  flip_scan_state_z_161 input output i count ->
  0 <= i < Zlength input ->
  c = Znth i input 0 ->
  ~ upper_z_161 c ->
  lower_z_161 c ->
  flip_scan_state_z_161 input (output ++ [c - 32]) (i + 1) count.
Proof.
  intros input output i count c Hstate Hi -> Hnotupper Hlower.
  unfold flip_scan_state_z_161 in *.
  destruct Hstate as [Hib [Hcount [Hout Hcountdef]]].
  repeat split; try lia.
  - rewrite sublist_snoc_161 by lia.
    rewrite map_app; simpl.
    rewrite Hout, flip_char_z_161_lower by assumption.
    reflexivity.
  - unfold nonletter_count_prefix_z_161 in *.
    rewrite sublist_snoc_161 by lia.
    rewrite filter_app, Zlength_app.
    assert (nonletter_zb_161 (Znth i input 0) = false) as Hnon.
    { unfold nonletter_zb_161.
      rewrite (proj2 (letter_zb_161_true _) (or_introl Hlower)).
      reflexivity. }
    rewrite <- Hcountdef.
    change (count = count +
      Zlength (if nonletter_zb_161 (Znth i input 0)
               then [Znth i input 0] else [])).
    rewrite Hnon, Zlength_nil. lia.
Qed.

Lemma flip_scan_state_z_161_step_nonletter : forall input output i count c,
  flip_scan_state_z_161 input output i count ->
  0 <= i < Zlength input ->
  c = Znth i input 0 ->
  ~ upper_z_161 c ->
  ~ lower_z_161 c ->
  flip_scan_state_z_161 input (output ++ [c]) (i + 1) (count + 1).
Proof.
  intros input output i count c Hstate Hi -> Hupper Hlower.
  unfold flip_scan_state_z_161 in *.
  destruct Hstate as [Hib [Hcount [Hout Hcountdef]]].
  repeat split; try lia.
  - rewrite sublist_snoc_161 by lia.
    rewrite map_app; simpl.
    rewrite Hout, flip_char_z_161_nonletter by assumption.
    reflexivity.
  - unfold nonletter_count_prefix_z_161 in *.
    rewrite sublist_snoc_161 by lia.
    rewrite filter_app, Zlength_app.
    assert (nonletter_zb_161 (Znth i input 0) = true) as Hnon.
    { apply nonletter_zb_161_true.
      unfold letter_z_161. tauto. }
    rewrite <- Hcountdef.
    change (count + 1 = count +
      Zlength (if nonletter_zb_161 (Znth i input 0)
               then [Znth i input 0] else [])).
    rewrite Hnon, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma reverse_scan_state_z_161_init : forall input,
  reverse_scan_state_z_161 input [] 0.
Proof.
  intros input.
  unfold reverse_scan_state_z_161.
  replace (sublist 0 0 (rev input)) with (@nil Z)
    by (symmetry; apply sublist_nil; lia).
  split.
  - split; [lia | apply Zlength_nonneg].
  - reflexivity.
Qed.

Lemma Zlength_rev_161 : forall {A : Type} (l : list A),
  Zlength (rev l) = Zlength l.
Proof.
  intros A l.
  rewrite !Zlength_correct, List.rev_length.
  reflexivity.
Qed.

Lemma Znth_rev_161 : forall {A : Type} (l : list A) i d,
  0 <= i < Zlength l ->
  Znth i (rev l) d = Znth (Zlength l - 1 - i) l d.
Proof.
  intros A l i d Hi.
  unfold Znth.
  rewrite rev_nth by (rewrite Zlength_correct in Hi; lia).
  replace (Datatypes.length l - S (Z.to_nat i))%nat
    with (Z.to_nat (Zlength l - 1 - i)).
  - reflexivity.
  - rewrite Zlength_correct. lia.
Qed.

Lemma reverse_scan_state_z_161_step : forall input output i c,
  reverse_scan_state_z_161 input output i ->
  0 <= i < Zlength input ->
  c = Znth (Zlength input - 1 - i) input 0 ->
  reverse_scan_state_z_161 input (output ++ [c]) (i + 1).
Proof.
  intros input output i c Hstate Hi ->.
  unfold reverse_scan_state_z_161 in *.
  destruct Hstate as [Hib Hout].
  split; [lia |].
  rewrite sublist_snoc_161.
  - rewrite Hout, Znth_rev_161 by lia. reflexivity.
  - rewrite Zlength_rev_161. lia.
Qed.

Lemma filter_length_eq_all_true_161 : forall {A} (f : A -> bool) l,
  List.length (filter f l) = List.length l ->
  Forall (fun x => f x = true) l.
Proof.
  intros A f l.
  induction l as [|x xs IH]; intros Hlen; simpl in *.
  - constructor.
  - destruct (f x) eqn:Hx; simpl in Hlen.
    + constructor; [exact Hx |]. apply IH. lia.
    + pose proof (@filter_length_le A f xs). lia.
Qed.

Lemma filter_all_true_eq_161 : forall {A} (f : A -> bool) l,
  Forall (fun x => f x = true) l -> filter f l = l.
Proof.
  intros A f l H.
  induction H; simpl; [reflexivity |].
  rewrite H, IHForall. reflexivity.
Qed.

Lemma flip_scan_state_z_161_finish_no_letter : forall input output n,
  n = Zlength input ->
  flip_scan_state_z_161 input output n n ->
  no_letter_z_161 input /\ output = map flip_char_z_161 input.
Proof.
  intros input output n -> Hstate.
  unfold flip_scan_state_z_161 in Hstate.
  destruct Hstate as [_ [_ [Hout Hcount]]].
  assert (Hsub : sublist 0 (Zlength input) input = input).
  { apply sublist_self. reflexivity. }
  split.
  - unfold no_letter_z_161.
    unfold nonletter_count_prefix_z_161 in Hcount.
    rewrite Hsub in Hcount.
    apply Forall_impl
      with (P := fun c => nonletter_zb_161 c = true).
    + intros c Hc. now apply nonletter_zb_161_true.
    + apply filter_length_eq_all_true_161.
      apply Nat2Z.inj.
      rewrite <- !Zlength_correct.
      symmetry. exact Hcount.
  - now rewrite Hsub in Hout.
Qed.

Lemma flip_scan_state_z_161_finish_has_letter : forall input output n count,
  n = Zlength input ->
  count <> n ->
  flip_scan_state_z_161 input output n count ->
  has_letter_z_161 input /\ output = map flip_char_z_161 input.
Proof.
  intros input output n count -> Hneq Hstate.
  unfold flip_scan_state_z_161 in Hstate.
  destruct Hstate as [_ [_ [Hout Hcount]]].
  assert (Hsub : sublist 0 (Zlength input) input = input).
  { apply sublist_self. reflexivity. }
  split.
  - unfold has_letter_z_161.
    destruct (classic (exists c, In c input /\ letter_z_161 c)) as [H | H].
    + exact H.
    + exfalso. apply Hneq.
      unfold nonletter_count_prefix_z_161 in Hcount.
      rewrite Hsub in Hcount.
      rewrite filter_all_true_eq_161 in Hcount.
      * exact Hcount.
      * apply Forall_forall. intros c Hin.
        apply nonletter_zb_161_true.
        intro Hletter. apply H. now exists c.
  - now rewrite Hsub in Hout.
Qed.

Lemma reverse_scan_state_z_161_finish : forall input output n,
  n = Zlength input ->
  reverse_scan_state_z_161 input output n ->
  output = rev input.
Proof.
  intros input output n -> Hstate.
  unfold reverse_scan_state_z_161 in Hstate.
  destruct Hstate as [_ Hout].
  rewrite sublist_self in Hout by (rewrite Zlength_rev_161; reflexivity).
  exact Hout.
Qed.

Lemma In_Znth_exists_161 : forall (x : Z) l,
  In x l ->
  exists i, 0 <= i < Zlength l /\ Znth i l 0 = x.
Proof.
  intros x l Hin.
  apply In_nth_error in Hin.
  destruct Hin as [n Hn].
  exists (Z.of_nat n).
  split.
  - assert ((n < List.length l)%nat) as Hlt.
    { apply nth_error_Some. rewrite Hn. discriminate. }
    rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id.
    apply nth_error_nth with (d := 0) in Hn.
    exact Hn.
Qed.

Lemma ascii_range_z_161_Forall : forall input,
  ascii_range_z input ->
  Forall (fun c => 0 <= c < 256) input.
Proof.
  intros input Hrange.
  apply Forall_forall.
  intros c Hin.
  destruct (In_Znth_exists_161 c input Hin) as [i [Hi <-]].
  apply Hrange. exact Hi.
Qed.

Lemma letter_z_161_ascii : forall c,
  0 <= c < 256 ->
  letter_z_161 c <-> letter (ascii_of_z c).
Proof.
  intros c Hrange.
  unfold letter_z_161, lower_z_161, upper_z_161,
         letter, lower_alpha, upper_alpha.
  rewrite nat_of_ascii_ascii_of_z by exact Hrange.
  lia.
Qed.

Lemma case_flip_ascii_of_z_161 : forall c,
  0 <= c < 256 ->
  case_flip (ascii_of_z c) (ascii_of_z (flip_char_z_161 c)).
Proof.
  intros c Hrange.
  destruct (Z_le_gt_dec 65 c) as [H65 | H65];
  destruct (Z_le_gt_dec c 90) as [H90 | H90].
  - right; left. split.
    + unfold upper_alpha. rewrite nat_of_ascii_ascii_of_z by exact Hrange. lia.
    + rewrite flip_char_z_161_upper by (unfold upper_z_161; lia).
      rewrite nat_of_ascii_ascii_of_z by exact Hrange.
      unfold ascii_of_z.
      f_equal. lia.
  - destruct (Z_le_gt_dec 97 c) as [H97 | H97];
    destruct (Z_le_gt_dec c 122) as [H122 | H122].
    + left. split.
      * unfold lower_alpha. rewrite nat_of_ascii_ascii_of_z by exact Hrange. lia.
      * rewrite flip_char_z_161_lower.
        -- rewrite nat_of_ascii_ascii_of_z by exact Hrange.
           unfold ascii_of_z.
           f_equal. lia.
        -- unfold upper_z_161. lia.
        -- unfold lower_z_161. lia.
    + right; right. split.
      * intro Hletter. apply (proj2 (letter_z_161_ascii c Hrange)) in Hletter.
        unfold letter_z_161, lower_z_161, upper_z_161 in Hletter. lia.
      * rewrite flip_char_z_161_nonletter.
        -- reflexivity.
        -- unfold upper_z_161; lia.
        -- unfold lower_z_161; lia.
    + right; right. split.
      * intro Hletter. apply (proj2 (letter_z_161_ascii c Hrange)) in Hletter.
        unfold letter_z_161, lower_z_161, upper_z_161 in Hletter. lia.
      * rewrite flip_char_z_161_nonletter.
        -- reflexivity.
        -- unfold upper_z_161; lia.
        -- unfold lower_z_161; lia.
    + right; right. split.
      * intro Hletter. apply (proj2 (letter_z_161_ascii c Hrange)) in Hletter.
        unfold letter_z_161, lower_z_161, upper_z_161 in Hletter. lia.
      * rewrite flip_char_z_161_nonletter.
        -- reflexivity.
        -- unfold upper_z_161; lia.
        -- unfold lower_z_161; lia.
  - right; right. split.
    + intro Hletter. apply (proj2 (letter_z_161_ascii c Hrange)) in Hletter.
      unfold letter_z_161, lower_z_161, upper_z_161 in Hletter. lia.
    + rewrite flip_char_z_161_nonletter.
      * reflexivity.
      * unfold upper_z_161; lia.
      * unfold lower_z_161; lia.
  - right; right. split.
    + intro Hletter. apply (proj2 (letter_z_161_ascii c Hrange)) in Hletter.
      unfold letter_z_161, lower_z_161, upper_z_161 in Hletter. lia.
    + rewrite flip_char_z_161_nonletter.
      * reflexivity.
      * unfold upper_z_161; lia.
      * unfold lower_z_161; lia.
Qed.

Lemma map_flip_case_rel_161 : forall input,
  ascii_range_z input ->
  Forall2 case_flip
    (map ascii_of_z input)
    (map ascii_of_z (map flip_char_z_161 input)).
Proof.
  intros input Hrange.
  pose proof (ascii_range_z_161_Forall input Hrange) as Hall.
  clear Hrange.
  induction Hall; simpl.
  - constructor.
  - constructor.
    + now apply case_flip_ascii_of_z_161.
    + exact IHHall.
Qed.

Lemma Znth_map_161 : forall {A B : Type}
    (f : A -> B) (l : list A) i da db,
  0 <= i < Zlength l ->
  Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l i da db Hi.
  unfold Znth.
  transitivity (nth (Z.to_nat i) (map f l) (f da)).
  - apply nth_indep.
    rewrite map_length.
    rewrite Zlength_correct in Hi. lia.
  - rewrite (@map_nth A B f l da (Z.to_nat i)). reflexivity.
Qed.

Lemma Zlength_map_161 : forall {A B : Type} (f : A -> B) l,
  Zlength (map f l) = Zlength l.
Proof.
  intros A B f l.
  rewrite !Zlength_correct, map_length. reflexivity.
Qed.

Lemma flip_char_z_161_range : forall c,
  0 <= c <= 127 -> 0 <= flip_char_z_161 c <= 127.
Proof.
  intros c Hrange.
  unfold flip_char_z_161.
  destruct (upper_zb_161 c) eqn:Hu.
  - apply upper_zb_161_true in Hu. unfold upper_z_161 in Hu. lia.
  - destruct (lower_zb_161 c) eqn:Hl.
    + apply lower_zb_161_true in Hl. unfold lower_z_161 in Hl. lia.
    + lia.
Qed.

Lemma flip_char_z_161_nonzero : forall c,
  0 <= c <= 127 -> c <> 0 -> flip_char_z_161 c <> 0.
Proof.
  intros c Hrange Hnonzero.
  unfold flip_char_z_161.
  destruct (upper_zb_161 c) eqn:Hu.
  - apply upper_zb_161_true in Hu. unfold upper_z_161 in Hu. lia.
  - destruct (lower_zb_161 c) eqn:Hl.
    + apply lower_zb_161_true in Hl. unfold lower_z_161 in Hl. lia.
    + exact Hnonzero.
Qed.

Lemma flip_output_valid_161 : forall input,
  valid_string input -> valid_string (map flip_char_z_161 input).
Proof.
  intros input [Hascii Hnonzero].
  split; intros i Hi.
  - rewrite (Znth_map_161 flip_char_z_161 input i 0 0)
      by (rewrite Zlength_map_161 in Hi; lia).
    apply flip_char_z_161_range. apply Hascii.
    rewrite Zlength_map_161 in Hi. exact Hi.
  - rewrite (Znth_map_161 flip_char_z_161 input i 0 0)
      by (rewrite Zlength_map_161 in Hi; lia).
    apply flip_char_z_161_nonzero.
    + apply Hascii. rewrite Zlength_map_161 in Hi. exact Hi.
    + apply Hnonzero. rewrite Zlength_map_161 in Hi. exact Hi.
Qed.

Lemma rev_valid_161 : forall input,
  valid_string input -> valid_string (rev input).
Proof.
  intros input [Hascii Hnonzero].
  split; intros i Hi.
  - rewrite Zlength_rev_161 in Hi.
    rewrite Znth_rev_161 by exact Hi.
    apply Hascii. lia.
  - rewrite Zlength_rev_161 in Hi.
    rewrite Znth_rev_161 by exact Hi.
    apply Hnonzero. lia.
Qed.

Lemma problem_161_spec_z_intro_flip : forall input output,
  ascii_range_z input ->
  has_letter_z_161 input ->
  output = map flip_char_z_161 input ->
  problem_161_spec_z input output.
Proof.
  intros input output Hrange [c [Hin Hletter]] ->.
  unfold problem_161_spec_z, problem_161_spec.
  rewrite !list_ascii_of_string_string_of_list_z.
  left. split.
  - apply Exists_exists. exists (ascii_of_z c). split.
    + apply in_map. exact Hin.
    + assert (Hcrange : 0 <= c < 256).
      { pose proof (ascii_range_z_161_Forall input Hrange) as Hall.
        apply Forall_forall with (x := c) in Hall; assumption. }
      apply (proj1 (letter_z_161_ascii c Hcrange)). exact Hletter.
  - apply map_flip_case_rel_161. exact Hrange.
Qed.

Lemma no_letter_ascii_161 : forall input,
  ascii_range_z input ->
  no_letter_z_161 input ->
  Forall (fun c => ~ letter c) (map ascii_of_z input).
Proof.
  intros input Hrange Hnone.
  pose proof (ascii_range_z_161_Forall input Hrange) as Hall.
  clear Hrange.
  induction Hnone; inversion Hall; subst; simpl.
  - constructor.
  - constructor.
    + intro Hletter.
      apply H.
      apply (proj2 (letter_z_161_ascii x H2)). exact Hletter.
    + apply IHHnone. exact H3.
Qed.

Lemma problem_161_spec_z_intro_rev : forall input output,
  ascii_range_z input ->
  no_letter_z_161 input ->
  output = rev input ->
  problem_161_spec_z input output.
Proof.
  intros input output Hrange Hnone ->.
  unfold problem_161_spec_z, problem_161_spec.
  rewrite !list_ascii_of_string_string_of_list_z.
  right. split.
  - apply no_letter_ascii_161; assumption.
  - rewrite map_rev. reflexivity.
Qed.

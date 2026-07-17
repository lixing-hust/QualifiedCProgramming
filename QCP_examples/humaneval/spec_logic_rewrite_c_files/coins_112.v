Load "../spec/112".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition ascii_of_z_112 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_112 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | x :: xs => String (ascii_of_z_112 x) (string_of_list_z_112 xs)
  end.

Definition bool_of_z_112 (z : Z) : bool :=
  negb (Z.eqb z 0).

Definition problem_112_pre_z (s c : list Z) : Prop :=
  problem_112_pre (string_of_list_z_112 s) (string_of_list_z_112 c).

Definition problem_112_spec_z
    (s c filtered : list Z) (pal : Z) : Prop :=
  problem_112_spec
    (string_of_list_z_112 s)
    (string_of_list_z_112 c)
    (string_of_list_z_112 filtered, bool_of_z_112 pal).

Fixpoint char_in_zb_112 (x : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | y :: ys => if Z.eqb x y then true else char_in_zb_112 x ys
  end.

Fixpoint filter_not_in_z_112 (s c : list Z) : list Z :=
  match s with
  | [] => []
  | x :: xs =>
      if char_in_zb_112 x c
      then filter_not_in_z_112 xs c
      else x :: filter_not_in_z_112 xs c
  end.

Definition filter_prefix_state_112
    (s c : list Z) (i : Z) (out : list Z) : Prop :=
  0 <= i <= Zlength s /\
  out = filter_not_in_z_112 (sublist 0 i s) c.

Definition mirror_prefix_112 (s : list Z) (i : Z) : Prop :=
  forall j,
    0 <= j < i ->
    Znth j s 0 = Znth (Zlength s - 1 - j) s 0.

Definition mirror_mismatch_prefix_112 (s : list Z) (i : Z) : Prop :=
  exists j,
    0 <= j < i /\
    Znth j s 0 <> Znth (Zlength s - 1 - j) s 0.

Definition palindrome_scan_state_112
    (s : list Z) (i pal : Z) : Prop :=
  0 <= i <= Zlength s ÷ 2 /\
  (pal = 1 -> mirror_prefix_112 s i) /\
  (pal = 0 -> mirror_mismatch_prefix_112 s i) /\
  (pal = 0 \/ pal = 1).

Definition palindrome_result_112 (s : list Z) (pal : Z) : Prop :=
  pal = 1 <-> s = rev s.

Definition flag_payload_112 (pal : Z) : list Z :=
  if Z.eqb pal 0
  then [70; 97; 108; 115; 101]
  else [84; 114; 117; 101].

Lemma filter_not_in_z_112_length_le : forall s c,
  Zlength (filter_not_in_z_112 s c) <= Zlength s.
Proof.
  induction s as [| x xs IH]; intros c; simpl.
  - lia.
  - specialize (IH c).
    destruct (char_in_zb_112 x c); simpl; rewrite ?Zlength_cons in *; lia.
Qed.

Lemma palindrome_index_bounds_112 : forall m i,
  0 <= m ->
  0 <= i < m ÷ 2 ->
  0 <= m - 1 - i < m.
Proof.
  intros m i Hm Hi.
  pose proof (BinInt.Z.mul_quot_le m 2 Hm ltac:(lia)) as [_ Hquot].
  lia.
Qed.

Lemma filter_prefix_state_112_zero : forall s c,
  filter_prefix_state_112 s c 0 [].
Proof.
  intros s c; unfold filter_prefix_state_112.
  change (sublist 0 0 s) with (@nil Z).
  simpl; split.
  - split; [lia | apply Zlength_nonneg].
  - reflexivity.
Qed.

Lemma char_in_zb_112_true_iff : forall x l,
  char_in_zb_112 x l = true <-> In x l.
Proof.
  intros x l; induction l as [| y ys IH]; simpl.
  - split.
    + intro H; discriminate.
    + intro H; contradiction.
  - destruct (Z.eqb x y) eqn:Heq.
    + apply Z.eqb_eq in Heq; subst; split; intro; [now left | reflexivity].
    + rewrite IH; apply Z.eqb_neq in Heq; split.
      * intro H; now right.
      * intros [Hy | Hin]; [exfalso; apply Heq; now symmetry | exact Hin].
Qed.

Lemma char_in_zb_112_false_iff : forall x l,
  char_in_zb_112 x l = false <-> ~ In x l.
Proof.
  intros x l; split.
  - intros Hfalse Hin.
    apply char_in_zb_112_true_iff in Hin; congruence.
  - intros Hnot.
    destruct (char_in_zb_112 x l) eqn:Hb; [|reflexivity].
    exfalso; apply Hnot; now apply char_in_zb_112_true_iff.
Qed.

Lemma filter_not_in_z_112_snoc : forall s c x,
  filter_not_in_z_112 (s ++ [x]) c =
  filter_not_in_z_112 s c ++
    if char_in_zb_112 x c then [] else [x].
Proof.
  induction s as [| y ys IH]; intros c x; simpl.
  - destruct (char_in_zb_112 x c); reflexivity.
  - destruct (char_in_zb_112 y c); simpl; rewrite IH; reflexivity.
Qed.

Lemma Znth_In_112 : forall (l : list Z) i d,
  0 <= i < Zlength l -> In (Znth i l d) l.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite <- (Nat2Z.id (List.length l)).
  apply (proj1 (Z2Nat.inj_lt i (Z.of_nat (List.length l)) ltac:(lia) ltac:(lia))).
  rewrite <- Zlength_correct; exact (proj2 Hi).
Qed.

Lemma In_as_Znth_112 : forall (l : list Z) x,
  In x l -> exists i, 0 <= i < Zlength l /\ Znth i l 0 = x.
Proof.
  intros l x Hin.
  apply In_nth with (d := 0) in Hin.
  destruct Hin as [n [Hn Hnth]].
  exists (Z.of_nat n); split.
  - rewrite Zlength_correct; lia.
  - unfold Znth; rewrite Nat2Z.id; exact Hnth.
Qed.

Lemma strchr_result_zero_not_in_112 : forall l ch ret base,
  ch <> 0 -> ret = 0 -> strchr_result l ch ret base -> ~ In ch l.
Proof.
  intros l ch ret base Hch Hret Hres Hin.
  destruct Hres as [[i [Hi [Heq [_ [_ Hnz]]]]] | [Hnone Htail]].
  - congruence.
  - destruct Htail as [[Hz _] | [_ _]]; [congruence|].
    destruct (In_as_Znth_112 l ch Hin) as [i [Hi Heq]].
    specialize (Hnone i Hi); congruence.
Qed.

Lemma strchr_result_nonzero_in_112 : forall l ch ret base,
  ch <> 0 -> ret <> 0 -> strchr_result l ch ret base -> In ch l.
Proof.
  intros l ch ret base Hch Hret Hres.
  destruct Hres as [[i [Hi [Heq _]]] | [_ [[Hcz _] | [_ Hzero]]]].
  - rewrite <- Heq; apply Znth_In_112; exact Hi.
  - contradiction.
  - congruence.
Qed.

Lemma filter_prefix_state_112_step_keep : forall s c i out ch,
  0 <= i < Zlength s ->
  ch = Znth i (c_string s) 0 ->
  ~ In ch c ->
  filter_prefix_state_112 s c i out ->
  filter_prefix_state_112 s c (i + 1) (out ++ [ch]).
Proof.
  intros s c i out ch Hi Hch Hnot [Hrange Hout].
  unfold filter_prefix_state_112; split; [lia|].
  rewrite (helper_sublist_snoc_Z s i 0) by exact Hi.
  rewrite filter_not_in_z_112_snoc, <- Hout.
  rewrite c_string_Znth_inside in Hch by (unfold string_length; exact Hi).
  subst ch.
  apply char_in_zb_112_false_iff in Hnot; rewrite Hnot; reflexivity.
Qed.

Lemma filter_prefix_state_112_step_drop : forall s c i out ch,
  0 <= i < Zlength s ->
  ch = Znth i (c_string s) 0 ->
  In ch c ->
  filter_prefix_state_112 s c i out ->
  filter_prefix_state_112 s c (i + 1) out.
Proof.
  intros s c i out ch Hi Hch Hin [Hrange Hout].
  unfold filter_prefix_state_112; split; [lia|].
  rewrite (helper_sublist_snoc_Z s i 0) by exact Hi.
  rewrite filter_not_in_z_112_snoc, <- Hout.
  rewrite c_string_Znth_inside in Hch by (unfold string_length; exact Hi).
  subst ch.
  apply char_in_zb_112_true_iff in Hin; rewrite Hin.
  now rewrite app_nil_r.
Qed.

Lemma filter_prefix_state_112_done : forall s c i out,
  i = Zlength s ->
  filter_prefix_state_112 s c i out ->
  out = filter_not_in_z_112 s c.
Proof.
  intros s c i out -> [_ Hout].
  rewrite sublist_self in Hout by lia; exact Hout.
Qed.

Lemma c_string_inside_nonzero_112 : forall s i,
  valid_string s ->
  0 <= i < string_length s ->
  Znth i (c_string s) 0 <> 0.
Proof.
  intros s i [_ Hno] Hi.
  rewrite c_string_Znth_inside by exact Hi.
  apply Hno; exact Hi.
Qed.

Lemma Znth_rev_112 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  Znth i (rev l) d = Znth (Zlength l - 1 - i) l d.
Proof.
  intros l i d Hi.
  unfold Znth.
  rewrite rev_nth.
  - f_equal.
    apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite Nat2Z.inj_sub by (rewrite Zlength_correct in Hi; lia).
    rewrite Zlength_correct, Nat2Z.inj_succ, Z2Nat.id by lia.
    lia.
  - rewrite <- (Nat2Z.id (List.length l)).
    apply (proj1 (Z2Nat.inj_lt i (Z.of_nat (List.length l)) ltac:(lia) ltac:(lia))).
    rewrite <- Zlength_correct; exact (proj2 Hi).
Qed.

Lemma list_eq_by_Znth_112 : forall (l1 l2 : list Z) d,
  Zlength l1 = Zlength l2 ->
  (forall i, 0 <= i < Zlength l1 -> Znth i l1 d = Znth i l2 d) ->
  l1 = l2.
Proof.
  intros l1 l2 d Hlen Heq.
  apply nth_ext with (d := d) (d' := d).
  - rewrite !Zlength_correct in Hlen; lia.
  - intros n Hn1.
    specialize (Heq (Z.of_nat n)).
    unfold Znth in Heq; rewrite Nat2Z.id in Heq.
    apply Heq; rewrite Zlength_correct; lia.
Qed.

Lemma mirror_prefix_half_palindrome_112 : forall s,
  mirror_prefix_112 s (Zlength s ÷ 2) -> s = rev s.
Proof.
  intros s Hmirror.
  apply list_eq_by_Znth_112 with (d := 0).
  - rewrite !Zlength_correct, rev_length; reflexivity.
  - intros idx Hidx.
    rewrite Znth_rev_112 by exact Hidx.
    destruct Hidx as [Hidx0 HidxL].
    destruct (Z_lt_ge_dec idx (Zlength s ÷ 2)) as [Hleft | Hright].
    + apply Hmirror; lia.
    + set (j := Zlength s - 1 - idx).
      pose proof (Z.rem_bound_pos (Zlength s) 2 (Zlength_nonneg s) ltac:(lia)) as Hmod.
      pose proof (Z.quot_rem (Zlength s) 2 ltac:(lia)) as Hdiv.
      assert (Hrem : Z.rem (Zlength s) 2 = 0 \/ Z.rem (Zlength s) 2 = 1) by lia.
      assert (Hcases : j < Zlength s ÷ 2 \/ j = idx).
      { destruct Hrem as [Hrem | Hrem].
        - rewrite Hrem, Z.add_0_r in Hdiv.
          assert (Hform : Zlength s = 2 * (Zlength s ÷ 2)) by exact Hdiv.
          assert (Hqle : Zlength s ÷ 2 <= idx) by lia.
          left; unfold j; lia.
        - rewrite Hrem in Hdiv.
          assert (Hform : Zlength s = 2 * (Zlength s ÷ 2) + 1) by exact Hdiv.
          assert (Hqle : Zlength s ÷ 2 <= idx) by lia.
          destruct (Z.eq_dec idx (Zlength s ÷ 2)).
          + right; unfold j; lia.
          + left; unfold j; lia. }
      destruct Hcases as [Hj | ->]; [|reflexivity].
      assert (Hjr : 0 <= j < Zlength s ÷ 2) by (unfold j; lia).
      specialize (Hmirror j Hjr).
      replace (Zlength s - 1 - j) with idx in Hmirror by (unfold j; lia).
      symmetry; exact Hmirror.
Qed.

Lemma palindrome_scan_state_112_init : forall s,
  palindrome_scan_state_112 s 0 1.
Proof.
  intros s; unfold palindrome_scan_state_112, mirror_prefix_112.
  repeat split.
  - lia.
  - apply Z.quot_pos; [apply Zlength_nonneg | lia].
  - intros _ j Hj; lia.
  - intro H; discriminate.
  - right; reflexivity.
Qed.

Lemma palindrome_scan_state_112_mismatch : forall s i pal,
  0 <= i < Zlength s ÷ 2 ->
  palindrome_scan_state_112 s i pal ->
  Znth i (c_string s) 0 <>
    Znth (Zlength s - 1 - i) (c_string s) 0 ->
  palindrome_scan_state_112 s (i + 1) 0.
Proof.
  intros s i pal Hi Hstate Hneq.
  pose proof (Zlength_nonneg s) as Hlen.
  pose proof (palindrome_index_bounds_112 (Zlength s) i Hlen Hi) as Hmirroridx.
  rewrite !c_string_Znth_inside in Hneq by (unfold string_length; lia).
  unfold palindrome_scan_state_112; repeat split; try lia; try congruence.
  - intros _; exists i; split; [lia | exact Hneq].
Qed.

Lemma palindrome_scan_state_112_equal_one : forall s i,
  0 <= i < Zlength s ÷ 2 ->
  palindrome_scan_state_112 s i 1 ->
  Znth i (c_string s) 0 =
    Znth (Zlength s - 1 - i) (c_string s) 0 ->
  palindrome_scan_state_112 s (i + 1) 1.
Proof.
  intros s i Hi Hstate Heq.
  pose proof (Zlength_nonneg s) as Hlen.
  pose proof (palindrome_index_bounds_112 (Zlength s) i Hlen Hi) as Hmirroridx.
  rewrite !c_string_Znth_inside in Heq by (unfold string_length; lia).
  destruct Hstate as [Hrange [Hone [Hzero Hflag]]].
  unfold palindrome_scan_state_112; repeat split; try lia; try congruence.
  - intros _ j Hj.
    destruct (Z_lt_ge_dec j i); [apply Hone; lia |].
    assert (j = i) by lia; subst; exact Heq.
Qed.

Lemma palindrome_scan_state_112_equal_zero : forall s i,
  0 <= i < Zlength s ÷ 2 ->
  palindrome_scan_state_112 s i 0 ->
  palindrome_scan_state_112 s (i + 1) 0.
Proof.
  intros s i Hi [Hrange [Hone [Hzero Hflag]]].
  unfold palindrome_scan_state_112; repeat split; try lia; try congruence.
  - intros _.
    destruct (Hzero eq_refl) as [j [Hj Hneq]].
    exists j; split; [lia | exact Hneq].
Qed.

Lemma palindrome_result_112_false : forall s i,
  palindrome_scan_state_112 s i 0 -> palindrome_result_112 s 0.
Proof.
  intros s i [Hrange [_ [Hzero _]]].
  unfold palindrome_result_112; split; [congruence |].
  intro Hpal; exfalso.
  destruct (Hzero eq_refl) as [j [Hj Hneq]].
  pose proof (Zlength_nonneg s) as Hlen.
  pose proof (BinInt.Z.mul_quot_le (Zlength s) 2 Hlen ltac:(lia)) as [_ Hquot].
  apply Hneq.
  rewrite Hpal at 1.
  rewrite Znth_rev_112 by (destruct Hj; lia).
  reflexivity.
Qed.

Lemma palindrome_result_112_true : forall s,
  palindrome_scan_state_112 s (Zlength s ÷ 2) 1 ->
  palindrome_result_112 s 1.
Proof.
  intros s [_ [Hone _]].
  unfold palindrome_result_112; split; intro.
  - apply mirror_prefix_half_palindrome_112; now apply Hone.
  - reflexivity.
Qed.

Fixpoint delete_ascii_112 (source removed : list ascii) : list ascii :=
  match source with
  | [] => []
  | x :: xs =>
      if in_dec ascii_dec x removed
      then delete_ascii_112 xs removed
      else x :: delete_ascii_112 xs removed
  end.

Fixpoint kept_indices_ascii_112 (source removed : list ascii) : list nat :=
  match source with
  | [] => []
  | x :: xs =>
      if in_dec ascii_dec x removed
      then map S (kept_indices_ascii_112 xs removed)
      else 0%nat :: map S (kept_indices_ascii_112 xs removed)
  end.

Lemma strictly_increasing_map_S_112 : forall indices,
  strictly_increasing indices -> strictly_increasing (map S indices).
Proof.
  induction indices as [| a [| b rest] IH]; intros H.
  - unfold strictly_increasing; simpl; constructor.
  - unfold strictly_increasing; simpl; constructor.
  - unfold strictly_increasing in H |- *; simpl in H |- *.
    inversion H as [| ? ? Hab Htail]; subst.
    simpl in Hab.
    constructor; [now apply (proj1 (Nat.succ_lt_mono a b)) |].
    apply IH; exact Htail.
Qed.

Lemma strictly_increasing_zero_shift_112 : forall indices,
  strictly_increasing indices ->
  strictly_increasing (0%nat :: map S indices).
Proof.
  intros [| a rest] H; [simpl; constructor |].
  unfold strictly_increasing; simpl.
  constructor; [simpl; lia |].
  pose proof (strictly_increasing_map_S_112 (a :: rest) H) as Hmap.
  unfold strictly_increasing in Hmap; simpl in Hmap; exact Hmap.
Qed.

Lemma Forall2_shift_source_112 : forall
    (source removed : list ascii) (indices : list nat)
    (result : list ascii) (x : ascii),
  Forall2
    (fun index ch => nth_error source index = Some ch /\ ~ In ch removed)
    indices result ->
  Forall2
    (fun index ch => nth_error (x :: source) index = Some ch /\ ~ In ch removed)
    (map S indices) result.
Proof.
  intros source removed indices result x H.
  induction H; simpl; constructor; auto.
Qed.

Lemma In_map_S_112 : forall n indices,
  In (S n) (map S indices) <-> In n indices.
Proof.
  intros n indices; split.
  - intros Hin; apply in_map_iff in Hin.
    destruct Hin as [m [Heq Hin]]; injection Heq; intro; subst; exact Hin.
  - intro Hin; now apply in_map.
Qed.

Lemma zero_not_In_map_S_112 : forall indices,
  ~ In 0%nat (map S indices).
Proof.
  intros indices Hin; apply in_map_iff in Hin.
  destruct Hin as [n [H _]]; discriminate.
Qed.

Lemma delete_ascii_112_rel : forall source removed,
  delete_chars_rel source removed (delete_ascii_112 source removed).
Proof.
  induction source as [| x xs IH]; intros removed.
  - exists []; split.
    + unfold strictly_increasing; simpl; constructor.
    + split; [constructor |].
    intros idx z Hnth; destruct idx; discriminate.
  - destruct (IH removed) as [indices [Hinc [Hpairs Hcover]]].
    simpl; destruct (in_dec ascii_dec x removed) as [Hin | Hnot].
    + exists (map S indices); split.
      * now apply strictly_increasing_map_S_112.
      * split; [now apply Forall2_shift_source_112 |].
        intros idx z Hnth; destruct idx as [| n].
        -- simpl in Hnth; injection Hnth; intro; subst.
           split.
           ++ intro Hzero; exfalso; now apply (zero_not_In_map_S_112 indices).
           ++ intro Hcontra; contradiction.
        -- simpl in Hnth.
           rewrite In_map_S_112; now apply Hcover.
    + exists (0%nat :: map S indices); split.
      * now apply strictly_increasing_zero_shift_112.
      * split.
        -- constructor; [split; [reflexivity | exact Hnot] |].
           now apply Forall2_shift_source_112.
        -- intros idx z Hnth; destruct idx as [| n].
           ++ simpl in Hnth; injection Hnth; intro; subst; simpl; tauto.
           ++ simpl in Hnth; simpl.
              split.
              ** intros [Heq | Hin]; [discriminate |].
                 exact ((proj1 (Hcover n z Hnth))
                   ((proj1 (In_map_S_112 n indices)) Hin)).
              ** intro Hkeep; right.
                 apply (proj2 (In_map_S_112 n indices)).
                 exact ((proj2 (Hcover n z Hnth)) Hkeep).
Qed.

Lemma list_ascii_string_of_list_z_112 : forall l,
  list_ascii_of_string (string_of_list_z_112 l) = map ascii_of_z_112 l.
Proof.
  induction l as [| x xs IH]; simpl; now rewrite ?IH.
Qed.

Lemma valid_string_Forall_bounds_112 : forall l,
  valid_string l -> Forall (fun z => 0 <= z <= 127) l.
Proof.
  intros l [Hbounds _].
  apply Forall_forall; intros z Hin.
  destruct (In_as_Znth_112 l z Hin) as [i [Hi Hiz]].
  rewrite <- Hiz; apply Hbounds; exact Hi.
Qed.

Lemma ascii_of_z_112_inj_bound : forall x y,
  0 <= x <= 127 -> 0 <= y <= 127 ->
  ascii_of_z_112 x = ascii_of_z_112 y -> x = y.
Proof.
  intros x y Hx Hy Heq.
  apply (f_equal nat_of_ascii) in Heq.
  unfold ascii_of_z_112 in Heq.
  assert (Hxnat : (Z.to_nat x < 256)%nat).
  { change (Z.to_nat x < Z.to_nat 256)%nat.
    apply (proj1 (Z2Nat.inj_lt x 256 ltac:(lia) ltac:(lia))); lia. }
  assert (Hynat : (Z.to_nat y < 256)%nat).
  { change (Z.to_nat y < Z.to_nat 256)%nat.
    apply (proj1 (Z2Nat.inj_lt y 256 ltac:(lia) ltac:(lia))); lia. }
  rewrite !nat_ascii_embedding in Heq by assumption.
  apply (f_equal Z.of_nat) in Heq.
  rewrite !Z2Nat.id in Heq by lia; exact Heq.
Qed.

Lemma In_ascii_map_iff_112 : forall x l,
  0 <= x <= 127 ->
  Forall (fun z => 0 <= z <= 127) l ->
  (In (ascii_of_z_112 x) (map ascii_of_z_112 l) <-> In x l).
Proof.
  intros x l Hx Hall; split.
  - intros Hin; apply in_map_iff in Hin.
    destruct Hin as [y [Heq Hin]].
    apply Forall_forall with (x := y) in Hall; [|exact Hin].
    assert (x = y) by (apply ascii_of_z_112_inj_bound; auto; now symmetry).
    now subst.
  - intro Hin; now apply in_map.
Qed.

Lemma map_filter_not_in_z_112 : forall source removed,
  Forall (fun z => 0 <= z <= 127) source ->
  Forall (fun z => 0 <= z <= 127) removed ->
  map ascii_of_z_112 (filter_not_in_z_112 source removed) =
    delete_ascii_112 (map ascii_of_z_112 source) (map ascii_of_z_112 removed).
Proof.
  induction source as [| x xs IH]; intros removed Hsource Hremoved; simpl.
  - reflexivity.
  - inversion Hsource as [| ? ? Hx Hxs]; subst.
    specialize (IH removed Hxs Hremoved).
    destruct (char_in_zb_112 x removed) eqn:Hz.
    + apply char_in_zb_112_true_iff in Hz.
      destruct (in_dec ascii_dec (ascii_of_z_112 x)
        (map ascii_of_z_112 removed)) as [Hascii | Hcontra].
      * exact IH.
      * exfalso; apply Hcontra; apply In_ascii_map_iff_112; assumption.
    + apply char_in_zb_112_false_iff in Hz.
      destruct (in_dec ascii_dec (ascii_of_z_112 x)
        (map ascii_of_z_112 removed)) as [Hcontra | Hascii].
      * exfalso; apply Hz; apply In_ascii_map_iff_112 in Hcontra; assumption.
      * simpl; now rewrite IH.
Qed.

Lemma map_ascii_injective_bounds_112 : forall l1 l2,
  Forall (fun z => 0 <= z <= 127) l1 ->
  Forall (fun z => 0 <= z <= 127) l2 ->
  map ascii_of_z_112 l1 = map ascii_of_z_112 l2 -> l1 = l2.
Proof.
  induction l1 as [| x xs IH]; intros [| y ys] H1 H2 Heq; simpl in Heq;
    try discriminate; try reflexivity.
  inversion H1; inversion H2; injection Heq; intros Hmaps Hxy.
  f_equal.
  - now apply ascii_of_z_112_inj_bound.
  - now apply IH.
Qed.

Lemma filter_not_in_z_112_bounds : forall source removed,
  Forall (fun z => 0 <= z <= 127) source ->
  Forall (fun z => 0 <= z <= 127) (filter_not_in_z_112 source removed).
Proof.
  induction source as [| x xs IH]; intros removed H; simpl; [constructor|].
  inversion H; destruct (char_in_zb_112 x removed); auto.
Qed.

Lemma problem_112_spec_z_bridge : forall input removed pal,
  valid_string input -> valid_string removed ->
  palindrome_result_112 (filter_not_in_z_112 input removed) pal ->
  (pal = 0 \/ pal = 1) ->
  problem_112_spec_z input removed (filter_not_in_z_112 input removed) pal.
Proof.
  intros input removed pal Hinput Hremoved Hpal Hflag.
  pose proof (valid_string_Forall_bounds_112 input Hinput) as Hib.
  pose proof (valid_string_Forall_bounds_112 removed Hremoved) as Hrb.
  pose proof (filter_not_in_z_112_bounds input removed Hib) as Hfb.
  unfold problem_112_spec_z, problem_112_spec; simpl.
  rewrite !list_ascii_string_of_list_z_112.
  split.
  - rewrite map_filter_not_in_z_112 by assumption.
    apply delete_ascii_112_rel.
  - unfold palindrome_flag, bool_of_z_112.
    destruct Hflag as [-> | ->]; simpl.
    + split; [discriminate | intro Hmap].
      exfalso.
      assert (Hraw : filter_not_in_z_112 input removed =
          rev (filter_not_in_z_112 input removed)).
      { apply map_ascii_injective_bounds_112.
        - exact Hfb.
        - apply Forall_rev; exact Hfb.
        - now rewrite map_rev. }
      pose proof ((proj2 Hpal) Hraw) as Hbad; discriminate.
    + split; intro H.
      * pose proof ((proj1 Hpal) eq_refl) as Hraw.
        apply (f_equal (map ascii_of_z_112)) in Hraw.
        now rewrite map_rev in Hraw.
      * reflexivity.
Qed.

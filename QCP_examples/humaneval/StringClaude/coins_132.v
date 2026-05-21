Load "../spec/132".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition bracket_char_z (c : Z) : Prop :=
  c = 91 \/ c = 93.

Definition problem_132_pre_z (s : list Z) : Prop :=
  problem_132_pre (string_of_list_z s).

Definition problem_132_spec_z (s : list Z) (output : Z) : Prop :=
  problem_132_spec (string_of_list_z s) (bool_of_z output).

Lemma Znth_In_range_132 : forall (l : list Z) k d,
  0 <= k < Zlength l ->
  In (Znth k l d) l.
Proof.
  intros l k d Hk.
  unfold Znth.
  apply nth_In.
  rewrite <- z_to_nat_Zlength.
  lia.
Qed.

Definition subseq_step_z (state c : Z) : Z :=
  if Z.eqb state 0 then
    if Z.eqb c 91 then 1 else 0
  else if Z.eqb state 1 then
    if Z.eqb c 91 then 2 else 1
  else if Z.eqb state 2 then
    if Z.eqb c 93 then 3 else 2
  else if Z.eqb state 3 then
    if Z.eqb c 93 then 4 else 3
  else 4.

Fixpoint subseq_state_list_z (state : Z) (s : list Z) : Z :=
  match s with
  | [] => state
  | c :: rest => subseq_state_list_z (subseq_step_z state c) rest
  end.

Definition subseq_state_prefix_z (i : Z) (s : list Z) : Z :=
  subseq_state_list_z 0 (firstn (Z.to_nat i) s).

Lemma subseq_state_list_z_app : forall a b st,
  subseq_state_list_z st (List.app a b) =
  subseq_state_list_z (subseq_state_list_z st a) b.
Proof.
  induction a as [| c rest IH]; intros b st; simpl; auto.
Qed.

Lemma firstn_succ_nth_132 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n as [| n IH]; intros l d Hlen.
  - destruct l as [| x xs]; simpl in *; try lia; reflexivity.
  - destruct l as [| x xs]; simpl in *; try lia.
    f_equal.
    apply IH.
    lia.
Qed.

Lemma firstn_succ_Znth_132 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  List.app (firstn (Z.to_nat i) l) [Znth i l d].
Proof.
  intros l i d Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite (firstn_succ_nth_132 (Z.to_nat i) l d).
  - unfold Znth.
    reflexivity.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
Qed.

Lemma subseq_state_prefix_step : forall s i,
  0 <= i < Zlength s ->
  subseq_state_prefix_z (i + 1) s =
  subseq_step_z (subseq_state_prefix_z i s) (Znth i s 0).
Proof.
  intros s i Hi.
  unfold subseq_state_prefix_z.
  rewrite (firstn_succ_Znth_132 s i 0) by exact Hi.
  rewrite subseq_state_list_z_app.
  reflexivity.
Qed.

Lemma subseq_step_range : forall state c,
  0 <= state <= 4 ->
  0 <= subseq_step_z state c <= 4.
Proof.
  intros state c Hstate.
  unfold subseq_step_z.
  repeat match goal with
  | |- context[Z.eqb ?a ?b] => destruct (Z.eqb_spec a b); subst
  end; lia.
Qed.

Lemma subseq_state_list_z_range : forall l state,
  0 <= state <= 4 ->
  0 <= subseq_state_list_z state l <= 4.
Proof.
  induction l as [| c rest IH]; intros state Hstate; simpl.
  - exact Hstate.
  - apply IH.
    apply subseq_step_range.
    exact Hstate.
Qed.

Lemma subseq_state_prefix_range : forall s i,
  0 <= subseq_state_prefix_z i s <= 4.
Proof.
  intros s i.
  unfold subseq_state_prefix_z.
  apply subseq_state_list_z_range.
  lia.
Qed.

Definition subseq_step_ascii (state : Z) (c : ascii) : Z :=
  if Z.eqb state 0 then
    if Ascii.ascii_dec c "["%char then 1 else 0
  else if Z.eqb state 1 then
    if Ascii.ascii_dec c "["%char then 2 else 1
  else if Z.eqb state 2 then
    if Ascii.ascii_dec c "]"%char then 3 else 2
  else if Z.eqb state 3 then
    if Ascii.ascii_dec c "]"%char then 4 else 3
  else 4.

Fixpoint subseq_state_list_ascii (state : Z) (s : list ascii) : Z :=
  match s with
  | [] => state
  | c :: rest => subseq_state_list_ascii (subseq_step_ascii state c) rest
  end.

Definition target_of_state (state : Z) : list ascii :=
  if Z.eqb state 0 then ["["%char; "["%char; "]"%char; "]"%char]
  else if Z.eqb state 1 then ["["%char; "]"%char; "]"%char]
  else if Z.eqb state 2 then ["]"%char; "]"%char]
  else if Z.eqb state 3 then ["]"%char]
  else [].

Lemma subseq_state_list_ascii_4 : forall l,
  subseq_state_list_ascii 4 l = 4.
Proof.
  induction l as [| c rest IH]; simpl; auto.
Qed.

Lemma contains_subseq_state_ascii : forall l state,
  state = 0 \/ state = 1 \/ state = 2 \/ state = 3 \/ state = 4 ->
  (contains_subseq l (target_of_state state) = true <->
   subseq_state_list_ascii state l = 4).
Proof.
  induction l as [| c rest IH]; intros state Hstate.
  - destruct Hstate as [-> | [-> | [-> | [-> | ->]]]]; simpl; split; intros H; try discriminate; auto.
  - destruct Hstate as [-> | [-> | [-> | [-> | ->]]]].
    + simpl. destruct (Ascii.ascii_dec c "["%char) as [-> | Hneq]; simpl.
      * change (contains_subseq rest (target_of_state 1) = true <->
                subseq_state_list_ascii 1 rest = 4).
        apply IH. auto.
      * replace (subseq_step_ascii 0 c) with 0
          by (unfold subseq_step_ascii; destruct (Ascii.ascii_dec c "["%char); [contradiction | reflexivity]).
        change (contains_subseq rest (target_of_state 0) = true <->
                subseq_state_list_ascii 0 rest = 4).
        apply IH. auto.
    + simpl. destruct (Ascii.ascii_dec c "["%char) as [-> | Hneq]; simpl.
      * change (contains_subseq rest (target_of_state 2) = true <->
                subseq_state_list_ascii 2 rest = 4).
        apply IH. auto.
      * replace (subseq_step_ascii 1 c) with 1
          by (unfold subseq_step_ascii; destruct (Z.eqb_spec 1 0); try lia;
              destruct (Z.eqb_spec 1 1); try lia;
              destruct (Ascii.ascii_dec c "["%char); [contradiction | reflexivity]).
        change (contains_subseq rest (target_of_state 1) = true <->
                subseq_state_list_ascii 1 rest = 4).
        apply IH. auto.
    + simpl. destruct (Ascii.ascii_dec c "]"%char) as [-> | Hneq]; simpl.
      * change (contains_subseq rest (target_of_state 3) = true <->
                subseq_state_list_ascii 3 rest = 4).
        apply IH. auto.
      * replace (subseq_step_ascii 2 c) with 2
          by (unfold subseq_step_ascii; destruct (Z.eqb_spec 2 0); try lia;
              destruct (Z.eqb_spec 2 1); try lia;
              destruct (Z.eqb_spec 2 2); try lia;
              destruct (Ascii.ascii_dec c "]"%char); [contradiction | reflexivity]).
        change (contains_subseq rest (target_of_state 2) = true <->
                subseq_state_list_ascii 2 rest = 4).
        apply IH. auto.
    + simpl. destruct (Ascii.ascii_dec c "]"%char) as [-> | Hneq]; simpl.
      * change (contains_subseq rest (target_of_state 4) = true <->
                subseq_state_list_ascii 4 rest = 4).
        apply IH. auto.
      * replace (subseq_step_ascii 3 c) with 3
          by (unfold subseq_step_ascii; destruct (Z.eqb_spec 3 0); try lia;
              destruct (Z.eqb_spec 3 1); try lia;
              destruct (Z.eqb_spec 3 2); try lia;
              destruct (Z.eqb_spec 3 3); try lia;
              destruct (Ascii.ascii_dec c "]"%char); [contradiction | reflexivity]).
        change (contains_subseq rest (target_of_state 3) = true <->
                subseq_state_list_ascii 3 rest = 4).
        apply IH. auto.
    + rewrite subseq_state_list_ascii_4. split; auto.
Qed.

Lemma ascii_of_z_open_132 : forall z,
  0 <= z < 256 ->
  (ascii_of_z z = "["%char <-> z = 91).
Proof.
  intros z Hz.
  split; intro H.
  - apply (f_equal nat_of_ascii) in H.
    rewrite nat_of_ascii_ascii_of_z in H by exact Hz.
    change (nat_of_ascii "["%char) with 91%nat in H.
    lia.
  - subst. reflexivity.
Qed.

Lemma ascii_of_z_close_132 : forall z,
  0 <= z < 256 ->
  (ascii_of_z z = "]"%char <-> z = 93).
Proof.
  intros z Hz.
  split; intro H.
  - apply (f_equal nat_of_ascii) in H.
    rewrite nat_of_ascii_ascii_of_z in H by exact Hz.
    change (nat_of_ascii "]"%char) with 93%nat in H.
    lia.
  - subst. reflexivity.
Qed.

Lemma subseq_step_z_ascii : forall state z,
  0 <= z < 256 ->
  subseq_step_z state z = subseq_step_ascii state (ascii_of_z z).
Proof.
  intros state z Hz.
  unfold subseq_step_z, subseq_step_ascii.
  destruct (Z.eqb_spec state 0); subst.
  - destruct (Z.eqb_spec z 91); subst.
    + destruct (Ascii.ascii_dec (ascii_of_z 91) "["%char) as [Hopen | Hopen];
      [reflexivity | contradiction Hopen; reflexivity].
    + destruct (Ascii.ascii_dec (ascii_of_z z) "["%char) as [Hopen | Hopen].
      * apply ascii_of_z_open_132 in Hopen; lia.
      * reflexivity.
  - destruct (Z.eqb_spec state 1); subst.
    + destruct (Z.eqb_spec z 91); subst.
      * destruct (Ascii.ascii_dec (ascii_of_z 91) "["%char) as [Hopen | Hopen];
        [reflexivity | contradiction Hopen; reflexivity].
      * destruct (Ascii.ascii_dec (ascii_of_z z) "["%char) as [Hopen | Hopen].
        -- apply ascii_of_z_open_132 in Hopen; lia.
        -- reflexivity.
    + destruct (Z.eqb_spec state 2); subst.
      * destruct (Z.eqb_spec z 93); subst.
        -- destruct (Ascii.ascii_dec (ascii_of_z 93) "]"%char) as [Hclose | Hclose];
           [reflexivity | contradiction Hclose; reflexivity].
        -- destruct (Ascii.ascii_dec (ascii_of_z z) "]"%char) as [Hclose | Hclose].
           ++ apply ascii_of_z_close_132 in Hclose; lia.
           ++ reflexivity.
      * destruct (Z.eqb_spec state 3); subst.
        -- destruct (Z.eqb_spec z 93); subst.
           ++ destruct (Ascii.ascii_dec (ascii_of_z 93) "]"%char) as [Hclose | Hclose];
              [reflexivity | contradiction Hclose; reflexivity].
           ++ destruct (Ascii.ascii_dec (ascii_of_z z) "]"%char) as [Hclose | Hclose].
              ** apply ascii_of_z_close_132 in Hclose; lia.
              ** reflexivity.
        -- reflexivity.
Qed.

Lemma ascii_range_z_tail_132 : forall c rest,
  ascii_range_z (c :: rest) ->
  ascii_range_z rest.
Proof.
  unfold ascii_range_z.
  intros c rest Hrange i Hi.
  specialize (Hrange (i + 1)).
  rewrite Zlength_cons in Hrange.
  rewrite Znth_cons in Hrange by lia.
  replace (i + 1 - 1) with i in Hrange by lia.
  apply Hrange.
  lia.
Qed.

Lemma ascii_range_z_head_132 : forall c rest,
  ascii_range_z (c :: rest) ->
  0 <= c < 256.
Proof.
  unfold ascii_range_z.
  intros c rest Hrange.
  specialize (Hrange 0).
  rewrite Zlength_cons in Hrange.
  change (Znth 0 (c :: rest) 0) with c in Hrange.
  apply Hrange.
  pose proof (Zlength_nonneg rest).
  lia.
Qed.

Lemma subseq_state_list_z_ascii : forall l state,
  ascii_range_z l ->
  subseq_state_list_z state l =
  subseq_state_list_ascii state (map ascii_of_z l).
Proof.
  induction l as [| c rest IH]; intros state Hrange; simpl.
  - reflexivity.
  - rewrite subseq_step_z_ascii by (apply ascii_range_z_head_132 with (rest := rest); exact Hrange).
    apply IH.
    apply ascii_range_z_tail_132 with (c := c).
    exact Hrange.
Qed.

Lemma subseq_state_prefix_full : forall s,
  subseq_state_prefix_z (Zlength s) s = subseq_state_list_z 0 s.
Proof.
  intros s.
  unfold subseq_state_prefix_z.
  rewrite z_to_nat_Zlength.
  rewrite firstn_all.
  reflexivity.
Qed.

Lemma problem_132_spec_z_true : forall s,
  ascii_range_z s ->
  subseq_state_prefix_z (Zlength s) s = 4 ->
  problem_132_spec_z s 1.
Proof.
  intros s Hrange Hstate.
  unfold problem_132_spec_z, problem_132_spec, bool_of_z, is_nested.
  simpl.
  rewrite list_ascii_of_string_string_of_list_z.
  symmetry.
  apply (proj2 (contains_subseq_state_ascii (map ascii_of_z s) 0 ltac:(auto))).
  rewrite <- subseq_state_list_z_ascii by exact Hrange.
  rewrite <- subseq_state_prefix_full.
  exact Hstate.
Qed.

Lemma problem_132_spec_z_false : forall s,
  ascii_range_z s ->
  subseq_state_prefix_z (Zlength s) s <> 4 ->
  problem_132_spec_z s 0.
Proof.
  intros s Hrange Hstate.
  unfold problem_132_spec_z, problem_132_spec, bool_of_z, is_nested.
  simpl.
  rewrite list_ascii_of_string_string_of_list_z.
  destruct (contains_subseq (map ascii_of_z s) [open_bracket; open_bracket; close_bracket; close_bracket]) eqn:Hcontains.
  - exfalso.
    apply Hstate.
    rewrite subseq_state_prefix_full.
    rewrite subseq_state_list_z_ascii by exact Hrange.
    apply (proj1 (contains_subseq_state_ascii (map ascii_of_z s) 0 ltac:(auto))).
    exact Hcontains.
  - reflexivity.
Qed.

Lemma problem_132_pre_z_char : forall s i,
  problem_132_pre_z s ->
  ascii_range_z s ->
  0 <= i < Zlength s ->
  bracket_char_z (Znth i s 0).
Proof.
  intros s i Hpre Hrange Hi.
  unfold problem_132_pre_z, problem_132_pre in Hpre.
  rewrite list_ascii_of_string_string_of_list_z in Hpre.
  apply Forall_forall with (x := ascii_of_z (Znth i s 0)) in Hpre.
  - destruct Hpre as [Hopen | Hclose].
    + left.
      apply ascii_of_z_open_132; [apply Hrange; exact Hi | exact Hopen].
    + right.
      apply ascii_of_z_close_132; [apply Hrange; exact Hi | exact Hclose].
  - rewrite in_map_iff.
    exists (Znth i s 0).
    split; [reflexivity |].
    apply Znth_In_range_132.
    exact Hi.
Qed.

Load "../spec/86".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_86_pre_z (s : list Z) : Prop :=
  problem_86_pre (string_of_list_z s).

Definition problem_86_spec_z (s output : list Z) : Prop :=
  problem_86_spec (string_of_list_z s) (string_of_list_z output).

Definition empty_z_list : list Z := [].

Definition is_space_z (c : Z) : bool :=
  Z.eqb c 32.

Definition ascii_le_z (a b : Z) : bool :=
  Nat.leb (nat_of_ascii (ascii_of_z a)) (nat_of_ascii (ascii_of_z b)).

Fixpoint insert_char_z (c : Z) (l : list Z) : list Z :=
  match l with
  | [] => [c]
  | h :: t =>
      if ascii_le_z c h then c :: l else h :: insert_char_z c t
  end.

Fixpoint sort_chars_forward_z (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => insert_char_z h (sort_chars_forward_z t)
  end.

Definition sort_chars_z (l : list Z) : list Z :=
  sort_chars_forward_z (rev l).

Definition anti_step_state_z (st : list Z * list Z) (c : Z) : list Z * list Z :=
  let '(out_l, cur_l) := st in
  if is_space_z c then
    (out_l ++ sort_chars_z cur_l ++ [32], [])
  else
    (out_l, cur_l ++ [c]).

Fixpoint anti_state_nat (n : nat) (l : list Z) : list Z * list Z :=
  match n with
  | O => ([], [])
  | S n' => anti_step_state_z (anti_state_nat n' l) (Znth (Z.of_nat n') l 0)
  end.

Definition anti_out_prefix_z (i : Z) (l : list Z) : list Z :=
  fst (anti_state_nat (Z.to_nat i) l).

Definition anti_cur_prefix_z (i : Z) (l : list Z) : list Z :=
  snd (anti_state_nat (Z.to_nat i) l).

Definition anti_shuffle_output_z (l : list Z) : list Z :=
  anti_out_prefix_z (Zlength l) l ++ sort_chars_z (anti_cur_prefix_z (Zlength l) l).

Fixpoint anti_process_z (l cur : list Z) : list Z :=
  match l with
  | [] => sort_chars_z cur
  | c :: rest =>
      if is_space_z c then
        sort_chars_z cur ++ [32] ++ anti_process_z rest []
      else
        anti_process_z rest (cur ++ [c])
  end.

Lemma Zlength_insert_char_z : forall c l,
  Zlength (insert_char_z c l) = Zlength l + 1.
Proof.
  intros c l.
  induction l as [| h t IH]; simpl.
  - rewrite Zlength_cons, Zlength_nil. lia.
  - unfold ascii_le_z.
    destruct (Nat.leb _ _); simpl.
    + repeat rewrite Zlength_cons. lia.
    + repeat rewrite Zlength_cons. lia.
Qed.

Lemma Zlength_sort_chars_forward_z : forall l,
  Zlength (sort_chars_forward_z l) = Zlength l.
Proof.
  induction l as [| h t IH]; simpl.
  - reflexivity.
  - rewrite Zlength_insert_char_z, IH.
    rewrite Zlength_cons. lia.
Qed.

Lemma Zlength_rev_86 : forall (l : list Z),
  Zlength (rev l) = Zlength l.
Proof.
  intros l.
  rewrite !Zlength_correct, List.rev_length.
  reflexivity.
Qed.

Lemma Zlength_sort_chars_z : forall l,
  Zlength (sort_chars_z l) = Zlength l.
Proof.
  intros l.
  unfold sort_chars_z.
  rewrite Zlength_sort_chars_forward_z.
  rewrite Zlength_rev_86.
  reflexivity.
Qed.

Lemma anti_state_nat_out_cur_len : forall n l,
  (Z.of_nat n <= Zlength l)%Z ->
  Zlength (fst (anti_state_nat n l)) + Zlength (snd (anti_state_nat n l)) =
  Z.of_nat n.
Proof.
  induction n as [| n IH]; intros l Hn; simpl.
  - reflexivity.
  - specialize (IH l ltac:(lia)).
    destruct (anti_state_nat n l) as [out_l cur_l].
    simpl in *.
    unfold anti_step_state_z.
    destruct (is_space_z (Znth (Z.of_nat n) l 0)) eqn:Hspace; simpl.
    + rewrite !Zlength_app, Zlength_sort_chars_z.
      rewrite !Zlength_cons, !Zlength_nil.
      lia.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
Qed.

Lemma anti_prefix_lengths : forall i l,
  0 <= i <= Zlength l ->
  Zlength (anti_out_prefix_z i l) + Zlength (anti_cur_prefix_z i l) = i.
Proof.
  intros i l Hi.
  unfold anti_out_prefix_z, anti_cur_prefix_z.
  pose proof (anti_state_nat_out_cur_len (Z.to_nat i) l ltac:(lia)).
  lia.
Qed.

Lemma Znth_app_l_0_86 : forall l i,
  0 <= i < Zlength l ->
  Znth i (l ++ [0]) 0 = Znth i l 0.
Proof.
  intros l i Hi.
  rewrite app_Znth1 by lia.
  reflexivity.
Qed.

Lemma anti_state_nat_step_86 : forall i l,
  0 <= i ->
  anti_state_nat (Z.to_nat (i + 1)) l =
  anti_step_state_z (anti_state_nat (Z.to_nat i) l) (Znth i l 0).
Proof.
  intros i l Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma anti_prefix_step_nonspace_86 : forall i l,
  0 <= i ->
  is_space_z (Znth i l 0) = false ->
  anti_out_prefix_z (i + 1) l = anti_out_prefix_z i l /\
  anti_cur_prefix_z (i + 1) l = anti_cur_prefix_z i l ++ [Znth i l 0].
Proof.
  intros i l Hi Hspace.
  unfold anti_out_prefix_z, anti_cur_prefix_z.
  rewrite anti_state_nat_step_86 by lia.
  destruct (anti_state_nat (Z.to_nat i) l) as [out_l cur_l].
  unfold anti_step_state_z.
  rewrite Hspace.
  split; reflexivity.
Qed.

Lemma anti_prefix_step_space_86 : forall i l,
  0 <= i ->
  is_space_z (Znth i l 0) = true ->
  anti_out_prefix_z (i + 1) l =
    anti_out_prefix_z i l ++ sort_chars_z (anti_cur_prefix_z i l) ++ [32] /\
  anti_cur_prefix_z (i + 1) l = [].
Proof.
  intros i l Hi Hspace.
  unfold anti_out_prefix_z, anti_cur_prefix_z.
  rewrite anti_state_nat_step_86 by lia.
  destruct (anti_state_nat (Z.to_nat i) l) as [out_l cur_l].
  unfold anti_step_state_z.
  rewrite Hspace.
  split; reflexivity.
Qed.

Lemma is_space_z_eq_true_86 : forall c,
  c = 32 ->
  is_space_z c = true.
Proof.
  intros c ->.
  unfold is_space_z.
  rewrite Z.eqb_refl.
  reflexivity.
Qed.

Lemma is_space_z_eq_false_86 : forall c,
  c <> 32 ->
  is_space_z c = false.
Proof.
  intros c Hneq.
  unfold is_space_z.
  apply Z.eqb_neq.
  exact Hneq.
Qed.

Lemma anti_shuffle_output_z_length_86 : forall l,
  Zlength (anti_shuffle_output_z l) = Zlength l.
Proof.
  intros l.
  unfold anti_shuffle_output_z.
  rewrite Zlength_app, Zlength_sort_chars_z.
  pose proof (Zlength_nonneg l) as Hlen_nonneg.
  pose proof (anti_prefix_lengths (Zlength l) l ltac:(lia)).
  lia.
Qed.

Lemma string_of_list_z_app_86 : forall l1 l2,
  string_of_list_z (l1 ++ l2) =
  String.append (string_of_list_z l1) (string_of_list_z l2).
Proof.
  induction l1 as [| c rest IH]; intros l2; simpl.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma ascii_of_z_space_86 : ascii_of_z 32 = " "%char.
Proof.
  reflexivity.
Qed.

Lemma ascii_of_z_eq_space_to_z_86 : forall x,
  0 <= x < 256 ->
  ascii_of_z x = " "%char ->
  x = 32.
Proof.
  intros x Hrange Hspace.
  apply (f_equal nat_of_ascii) in Hspace.
  rewrite nat_of_ascii_ascii_of_z in Hspace by exact Hrange.
  change (nat_of_ascii " "%char) with 32%nat in Hspace.
  lia.
Qed.

Lemma is_space_bool_ascii_of_z_86 : forall c,
  0 <= c < 256 ->
  is_space_bool (ascii_of_z c) = is_space_z c.
Proof.
  intros c Hrange.
  unfold is_space_bool, is_space_z.
  destruct (ascii_dec (ascii_of_z c) " "%char) as [Hspace | Hspace].
  - apply ascii_of_z_eq_space_to_z_86 in Hspace; try assumption.
    subst c.
    rewrite Z.eqb_refl.
    reflexivity.
  - destruct (Z.eqb_spec c 32) as [Heq | Hneq].
    + subst c.
      exfalso.
      apply Hspace.
      apply ascii_of_z_space_86.
    + reflexivity.
Qed.

Lemma ascii_range_z_cons_inv_86 : forall c rest,
  ascii_range_z (c :: rest) ->
  0 <= c < 256 /\ ascii_range_z rest.
Proof.
  intros c rest Hrange.
  split.
  - assert (Hidx : 0 <= 0 < Zlength (c :: rest)).
    { rewrite Zlength_cons.
      pose proof (Zlength_nonneg rest).
      lia. }
    specialize (Hrange 0 Hidx).
    unfold Znth in Hrange.
    simpl in Hrange.
    exact Hrange.
  - unfold ascii_range_z in *.
    intros i Hi.
    assert (Hidx : 0 <= i + 1 < Zlength (c :: rest)).
    { rewrite Zlength_cons in *.
      lia. }
    specialize (Hrange (i + 1) Hidx).
    unfold Znth in *.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in Hrange by lia.
    simpl in Hrange.
    exact Hrange.
Qed.

Lemma string_of_list_z_insert_char_z_86 : forall c l,
  string_of_list_z (insert_char_z c l) =
  insert_char (ascii_of_z c) (string_of_list_z l).
Proof.
  induction l as [| h t IH]; simpl.
  - reflexivity.
  - unfold ascii_le_z.
    destruct (Nat.leb _ _); simpl.
    + reflexivity.
    + rewrite IH.
      reflexivity.
Qed.

Lemma string_of_list_z_sort_chars_forward_z_86 : forall l,
  string_of_list_z (sort_chars_forward_z l) =
  sort_chars (string_of_list_z l).
Proof.
  induction l as [| h t IH]; simpl.
  - reflexivity.
  - rewrite string_of_list_z_insert_char_z_86.
    rewrite IH.
    reflexivity.
Qed.

Lemma string_of_list_z_sort_chars_z_86 : forall l,
  string_of_list_z (sort_chars_z l) =
  sort_chars (string_of_list_z (rev l)).
Proof.
  intros l.
  unfold sort_chars_z.
  apply string_of_list_z_sort_chars_forward_z_86.
Qed.

Lemma string_of_list_z_rev_snoc_86 : forall cur c,
  string_of_list_z (rev (cur ++ [c])) =
  String (ascii_of_z c) (string_of_list_z (rev cur)).
Proof.
  intros cur c.
  rewrite rev_app_distr.
  simpl.
  reflexivity.
Qed.

Lemma Znth_of_nat_nth_86 : forall {A : Type} n (l : list A) d,
  Znth (Z.of_nat n) l d = nth n l d.
Proof.
  intros A n l d.
  unfold Znth.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

Lemma skipn_n_cons_86 : forall {A : Type} n (l : list A) d,
  (n < Datatypes.length l)%nat ->
  skipn n l = nth n l d :: skipn (S n) l.
Proof.
  intros A n.
  induction n as [| n IH]; intros l d Hlen.
  - destruct l as [| c rest]; simpl in *; try lia.
    reflexivity.
  - destruct l as [| c rest]; simpl in *; try lia.
    apply IH.
    lia.
Qed.

Lemma app_space_tail_86 : forall a b rest,
  (a ++ b ++ [32]) ++ rest = a ++ b ++ 32 :: rest.
Proof.
  intros a b rest.
  repeat rewrite <- List.app_assoc.
  reflexivity.
Qed.

Lemma anti_state_nat_process_86 : forall n l,
  (n <= Datatypes.length l)%nat ->
  fst (anti_state_nat n l) ++
    anti_process_z (skipn n l) (snd (anti_state_nat n l)) =
  anti_process_z l [].
Proof.
  induction n as [| n IH]; intros l Hlen.
  - simpl.
    reflexivity.
  - assert (Hn_le : (n <= Datatypes.length l)%nat) by lia.
    assert (Hn_lt : (n < Datatypes.length l)%nat) by lia.
    pose proof (IH l Hn_le) as Hprev.
    rewrite <- Hprev.
    simpl anti_state_nat.
    rewrite (skipn_n_cons_86 n l 0 Hn_lt).
    rewrite Znth_of_nat_nth_86.
    destruct (anti_state_nat n l) as [out_l cur_l].
    simpl.
    unfold anti_step_state_z.
    destruct (is_space_z (nth n l 0)) eqn:Hspace; simpl.
    + rewrite app_space_tail_86.
      reflexivity.
    + reflexivity.
Qed.

Lemma anti_shuffle_output_z_eq_process_86 : forall l,
  anti_shuffle_output_z l = anti_process_z l [].
Proof.
  intros l.
  unfold anti_shuffle_output_z, anti_out_prefix_z, anti_cur_prefix_z.
  pose proof (anti_state_nat_process_86 (Datatypes.length l) l ltac:(lia)) as Hprocess.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  rewrite skipn_all in Hprocess.
  simpl in Hprocess.
  exact Hprocess.
Qed.

Lemma anti_process_z_correct_86 : forall l cur,
  ascii_range_z l ->
  string_of_list_z (anti_process_z l cur) =
  anti_shuffle_aux (string_of_list_z l) (string_of_list_z (rev cur)).
Proof.
  induction l as [| c rest IH]; intros cur Hrange.
  - simpl.
    apply string_of_list_z_sort_chars_z_86.
  - destruct (ascii_range_z_cons_inv_86 c rest Hrange) as [Hc Hrest].
    simpl.
    rewrite is_space_bool_ascii_of_z_86 by exact Hc.
    unfold is_space_z.
    destruct (Z.eqb_spec c 32) as [Hspace | Hnonspace].
    + subst c.
      simpl.
      rewrite !string_of_list_z_app_86.
      simpl.
      rewrite string_of_list_z_sort_chars_z_86.
      rewrite IH by exact Hrest.
      rewrite ascii_of_z_space_86.
      reflexivity.
    + rewrite IH by exact Hrest.
      rewrite string_of_list_z_rev_snoc_86.
      reflexivity.
Qed.

Lemma problem_86_spec_z_anti_shuffle_output_86 : forall l,
  ascii_range_z l ->
  problem_86_spec_z l (anti_shuffle_output_z l).
Proof.
  intros l Hrange.
  unfold problem_86_spec_z, problem_86_spec, anti_shuffle_impl.
  rewrite anti_shuffle_output_z_eq_process_86.
  apply anti_process_z_correct_86.
  exact Hrange.
Qed.

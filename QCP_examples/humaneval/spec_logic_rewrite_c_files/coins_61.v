Load "../spec/61".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition ascii_of_z_61 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_61 c) (string_of_list_z rest)
  end.

Definition string_length (s : list Z) : Z :=
  Zlength s.

Definition problem_61_pre_z (brackets : list Z) : Prop :=
  problem_61_pre (string_of_list_z brackets).

Definition problem_61_spec_z (brackets : list Z) (output : bool) : Prop :=
  problem_61_spec (string_of_list_z brackets) output.

Definition paren_delta_61 (c : Z) : Z :=
  if Z.eqb c 40 then 1 else -1.

Fixpoint paren_level_nat_61 (n : nat) (s : list Z) : Z :=
  match n with
  | O => 0
  | S n' => paren_level_nat_61 n' s + paren_delta_61 (Znth (Z.of_nat n') s 0)
  end.

Definition paren_level_61 (s : list Z) (i : Z) : Z :=
  paren_level_nat_61 (Z.to_nat i) s.

Definition paren_prefix_nonnegative_61 (s : list Z) (i : Z) : Prop :=
  forall k, 0 <= k < i -> 0 <= paren_level_61 s (k + 1).

Definition bracket_state_61 (s : list Z) (i level : Z) : Prop :=
  0 <= i <= string_length s /\
  level = paren_level_61 s i /\
  paren_prefix_nonnegative_61 s i.

Definition bracket_safe_input_61 (s : list Z) : Prop :=
  (forall i,
      0 <= i < Zlength s ->
      Znth i s 0 = 40 \/ Znth i s 0 = 41) /\
  bracket_state_61 s 0 0 /\
  (forall i level,
      bracket_state_61 s i level ->
      i < Zlength s ->
      Znth i s 0 = 40 ->
      bracket_state_61 s (i + 1) (level + 1)) /\
  (forall i level,
      bracket_state_61 s i level ->
      i < Zlength s ->
      Znth i s 0 = 41 ->
      0 < level ->
      bracket_state_61 s (i + 1) (level - 1)) /\
  (forall i,
      bracket_state_61 s i 0 ->
      i < Zlength s ->
      Znth i s 0 = 41 ->
      problem_61_spec_z s false) /\
  (forall level,
      bracket_state_61 s (Zlength s) level ->
      level = 0 ->
      problem_61_spec_z s true) /\
  (forall level,
      bracket_state_61 s (Zlength s) level ->
      level <> 0 ->
      problem_61_spec_z s false).

Lemma bracket_safe_char_61 : forall s i,
  bracket_safe_input_61 s ->
  0 <= i < Zlength s ->
  Znth i s 0 = 40 \/ Znth i s 0 = 41.
Proof.
  intros s i Hsafe Hi.
  unfold bracket_safe_input_61 in Hsafe.
  destruct Hsafe as [Hchar _].
  apply Hchar; exact Hi.
Qed.

Lemma bracket_safe_initial_61 : forall s,
  bracket_safe_input_61 s ->
  bracket_state_61 s 0 0.
Proof.
  intros s Hsafe.
  unfold bracket_safe_input_61 in Hsafe.
  destruct Hsafe as [_ [Hinit _]].
  exact Hinit.
Qed.

Lemma bracket_safe_open_61 : forall s i level,
  bracket_safe_input_61 s ->
  bracket_state_61 s i level ->
  i < Zlength s ->
  Znth i s 0 = 40 ->
  bracket_state_61 s (i + 1) (level + 1).
Proof.
  intros s i level Hsafe.
  unfold bracket_safe_input_61 in Hsafe.
  destruct Hsafe as [_ [_ [Hopen _]]].
  eauto.
Qed.

Lemma bracket_safe_close_continue_61 : forall s i level,
  bracket_safe_input_61 s ->
  bracket_state_61 s i level ->
  i < Zlength s ->
  Znth i s 0 = 41 ->
  0 < level ->
  bracket_state_61 s (i + 1) (level - 1).
Proof.
  intros s i level Hsafe.
  unfold bracket_safe_input_61 in Hsafe.
  destruct Hsafe as [_ [_ [_ [Hclose _]]]].
  eauto.
Qed.

Lemma bracket_safe_close_negative_61 : forall s i,
  bracket_safe_input_61 s ->
  bracket_state_61 s i 0 ->
  i < Zlength s ->
  Znth i s 0 = 41 ->
  problem_61_spec_z s false.
Proof.
  intros s i Hsafe.
  unfold bracket_safe_input_61 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [Hneg _]]]]].
  eauto.
Qed.

Lemma bracket_safe_final_true_61 : forall s level,
  bracket_safe_input_61 s ->
  bracket_state_61 s (Zlength s) level ->
  level = 0 ->
  problem_61_spec_z s true.
Proof.
  intros s level Hsafe.
  unfold bracket_safe_input_61 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [Htrue _]]]]]].
  eauto.
Qed.

Lemma bracket_safe_final_false_61 : forall s level,
  bracket_safe_input_61 s ->
  bracket_state_61 s (Zlength s) level ->
  level <> 0 ->
  problem_61_spec_z s false.
Proof.
  intros s level Hsafe.
  unfold bracket_safe_input_61 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ Hfalse]]]]]].
  eauto.
Qed.

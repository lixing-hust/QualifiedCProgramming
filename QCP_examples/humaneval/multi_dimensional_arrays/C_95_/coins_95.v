Load "QCP_examples/humaneval/spec/95".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition ascii_of_z (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z c) (string_of_list_z rest)
  end.

Definition bool_of_z (z : Z) : bool :=
  Z.eqb z 1.

Definition row_payload_z (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition rows_to_dictionary_z (rows : list (list Z)) : dictionary :=
  map (fun row => (KeyString (string_of_list_z (row_payload_z row)), EmptyString)) rows.

Definition problem_95_pre_z (rows : list (list Z)) : Prop :=
  problem_95_pre (rows_to_dictionary_z rows).

Definition problem_95_spec_z (rows : list (list Z)) (ret : Z) : Prop :=
  problem_95_spec (rows_to_dictionary_z rows) (bool_of_z ret).

Definition lower_char_z (c : Z) : Prop :=
  97 <= c <= 122.

Definition upper_char_z (c : Z) : Prop :=
  65 <= c <= 90.

Definition letter_char_z (c : Z) : Prop :=
  upper_char_z c \/ lower_char_z c.

Definition row_payload_bound (row : list Z) (i : Z) : Prop :=
  0 <= i < Zlength row - 1.

Definition row_all_lower_z (row : list Z) : Prop :=
  forall i, row_payload_bound row i -> lower_char_z (Znth i row 0).

Definition row_all_upper_z (row : list Z) : Prop :=
  forall i, row_payload_bound row i -> upper_char_z (Znth i row 0).

Definition row_all_letters_z (row : list Z) : Prop :=
  forall i, row_payload_bound row i -> letter_char_z (Znth i row 0).

Definition rows_all_lower_z (rows : list (list Z)) : Prop :=
  forall k, 0 <= k < Zlength rows -> row_all_lower_z (Znth k rows nil).

Definition rows_all_upper_z (rows : list (list Z)) : Prop :=
  forall k, 0 <= k < Zlength rows -> row_all_upper_z (Znth k rows nil).

Definition rows_all_letters_z (rows : list (list Z)) : Prop :=
  forall k, 0 <= k < Zlength rows -> row_all_letters_z (Znth k rows nil).

Definition rows_have_case_z (rows : list (list Z)) : Prop :=
  rows_all_lower_z rows \/ rows_all_upper_z rows.

Definition processed_position_z (k i r j : Z) : Prop :=
  (0 <= r < k /\ 0 <= j) \/ (r = k /\ 0 <= j < i).

Definition processed_char_bound_z
  (k i : Z) (rows : list (list Z)) (r j : Z) : Prop :=
  0 <= r < Zlength rows /\
  processed_position_z k i r j /\
  j < Zlength (Znth r rows nil) - 1.

Definition processed_all_letters_z (k i : Z) (rows : list (list Z)) : Prop :=
  forall r j,
    processed_char_bound_z k i rows r j ->
    letter_char_z (Znth j (Znth r rows nil) 0).

Definition processed_has_lower_z (k i : Z) (rows : list (list Z)) : Prop :=
  exists r j,
    processed_char_bound_z k i rows r j /\
    lower_char_z (Znth j (Znth r rows nil) 0).

Definition processed_has_upper_z (k i : Z) (rows : list (list Z)) : Prop :=
  exists r j,
    processed_char_bound_z k i rows r j /\
    upper_char_z (Znth j (Znth r rows nil) 0).

Definition dict_case_state_z
  (k i : Z) (rows : list (list Z)) (islower isupper : Z) : Prop :=
  processed_all_letters_z k i rows /\
  (islower = 1 <-> processed_has_lower_z k i rows) /\
  (isupper = 1 <-> processed_has_upper_z k i rows) /\
  0 <= islower <= 1 /\
  0 <= isupper <= 1 /\
  islower + isupper <= 1.

Definition rows_well_formed_z (rows : list (list Z)) (dict_size : Z) : Prop :=
  Zlength rows = dict_size /\
  forall k,
    0 <= k < dict_size ->
    0 < Zlength (Znth k rows nil) <= 101 /\
    Znth (Zlength (Znth k rows nil) - 1) (Znth k rows nil) 0 = 0 /\
    forall i, row_payload_bound (Znth k rows nil) i ->
      Znth i (Znth k rows nil) 0 <> 0.

Lemma problem_95_pre_z_rows : forall rows,
  problem_95_pre_z rows.
Proof.
  intros rows.
  unfold problem_95_pre_z, problem_95_pre.
  exact I.
Qed.

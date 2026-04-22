Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Definition replace_char (x old_c new_c : Z) : Z :=
  if Z.eq_dec x old_c then new_c else x.

Fixpoint string_replace_char_spec (l : list Z) (old_c new_c : Z) : list Z :=
  match l with
  | nil => nil
  | x :: xs => replace_char x old_c new_c :: string_replace_char_spec xs old_c new_c
  end.

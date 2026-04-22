Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Definition lower_ascii_char (x : Z) : Z :=
  if Z_le_dec 65 x then
    if Z_le_dec x 90 then x - 65 + 97 else x
  else x.

Fixpoint string_to_lower_ascii_spec (l : list Z) : list Z :=
  match l with
  | nil => nil
  | x :: xs => lower_ascii_char x :: string_to_lower_ascii_spec xs
  end.

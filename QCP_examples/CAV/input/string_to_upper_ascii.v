Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Definition upper_ascii_char (x : Z) : Z :=
  if Z_le_dec 97 x then
    if Z_le_dec x 122 then x - 97 + 65 else x
  else x.

Fixpoint string_to_upper_ascii_spec (l : list Z) : list Z :=
  match l with
  | nil => nil
  | x :: xs => upper_ascii_char x :: string_to_upper_ascii_spec xs
  end.

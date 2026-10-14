From Coq Require Import ZArith.
Local Open Scope Z_scope.

Definition grant_input_widths (d c r : Z) : Prop :=
  0 <= d <= 255 /\ 0 <= c <= 4294967295 /\
  0 <= r <= 4294967295.

Definition grant_early_failure (d c : Z) : Prop :=
  16 < c \/ 64 <= d.

Definition grant_selected (d c : Z) : Prop :=
  0 <= c <= 16 /\ 0 <= d < 64.

Definition grant_rights (old_right supplied : Z) : Z :=
  Z.lor (Z.land old_right 4095) supplied.

Definition grant_success_fields
  (c old_right supplied ret new_type new_content new_right : Z) : Prop :=
  ret = 0 /\ new_type = 1 /\ new_content = c /\
  new_right = grant_rights old_right supplied.

Definition grant_return (d c selected_ptr ret : Z) : Prop :=
  (grant_early_failure d c /\ ret = 11) \/
  (grant_selected d c /\ selected_ptr = 0 /\ ret = 11) \/
  (grant_selected d c /\ selected_ptr <> 0 /\ ret = 0).

From SimpleC.SL Require Import SeparationLogic.

Load "../spec/157".

Lemma fp32_ge_not_lt_157 :
  forall x y,
    fp32_ge x y ->
    ~ fp32_lt x y.
Proof.
  intros x y Hge.
  unfold fp32_ge in Hge.
  unfold fp32_lt.
  destruct (fp32_compare x y) as [comparison|] eqn:Hcmp.
  - destruct comparison.
    + discriminate.
    + contradiction.
    + discriminate.
  - contradiction.
Qed.

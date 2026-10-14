Require Import include_frm2.
Require Import sep_auto2.
Require Import derived_rules2.
Require Import symbolic_execution2.

Ltac hoare_if :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- {| _ , _, _, _, _, _ |}|-?ct {{ _ }} (sif _ _ _) {{ _ }} =>
      eapply if_rule2';
        [ symbolic execution
        | idtac 
        | idtac ]
    | |- {| _ , _, _, _, _, _ |}|-?ct {{ _ }} (sifthen _ _) {{ _ }} =>
      eapply ift_rule'';
        [ symbolic execution
        | idtac ]
  end.

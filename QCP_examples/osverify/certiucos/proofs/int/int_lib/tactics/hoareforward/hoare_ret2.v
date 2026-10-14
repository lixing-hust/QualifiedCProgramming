Require Import include_frm2.
Require Import sep_auto2.
Require Import derived_rules2.
Require Import symbolic_execution2.
Set Implicit Arguments.

Ltac hoare_ret :=
  match goal with
  | |- {| _, _, _, _, _, _ |} |-?ct {{ _ }} sret {{ _ }} =>
    apply ret_rule'; sep semiauto
  | |- {| _, _, _, _, _, _|} |-?ct {{ _ }} (sprim exint) {{ _ }} =>
    apply iret_rule';sep semiauto
  | |- {| ?spec, _, _, _, _, _|} |-?ct {{ _ }} (srete _) {{ _ }} =>
    eapply rete_rule';
      [symbolic execution
          | sep semiauto
      ]     
end.

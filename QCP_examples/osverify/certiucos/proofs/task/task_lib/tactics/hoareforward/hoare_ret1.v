Require Import include_frm1.
Require Import sep_auto1.
Require Import derived_rules1.
Require Import symbolic_execution1.
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

Require Import include_frm.
Require Import sep_auto.
Require Import hoare_tactics.
Require Import ucos_forward.
Require Import hoare_conseq.
Require Import derived_rules.
Require Import hoare_call.
Require Import hoare_assign.
Require Import hoare_if.
Require Import hoare_ret.
Require Import symbolic_execution.
Require Import hoare_assign_tac_ext.

Open Scope code_scope.

Ltac sep_cancel_iers :=
try sep cancel Aop;
try sep cancel Aisr;
try sep cancel Ais;
try sep cancel Aie;
try sep cancel Acs;
try sep cancel Aier.

    Ltac hoare_call :=
  match goal with
    | |- {| _, _, ?li, _, _, _ |} |- ?ct {{ ?P }} scall _ ?el {{ _ }} =>
      match find_aop P with 
        | some ?n =>  
              hoare lifts (n::nil)%nat pre; 
                eapply call_rule';
                [intuition eauto | 
                 intros; 
                    do 5 try (apply rvl_elim;[ try (eapply symbolic_lemmas.cast_rv_tnull; [sep get rv |  simpl; auto]); symbolic_execution | ]);
                     first [apply rvl_nil | simpl;auto] |
                 intros;  unfold_spec; sep normal; sep eexists; sep_cancel_iers; sep pauto | (* origin: intros;  unfold_spec; sep pauto *)
                 idtac |
                 sep_unfold_funpost |
                 sep_unfold_funpre |
                 simpl;eauto
                ] 
        | none _ => idtac
      end
  end.

Ltac hoare_calle_lvar :=
  match goal with
    | |- {| _, _, ?li, _, _, _ |} |-?ct {{ ?P }} scalle (evar ?x) _ ?el {{ _ }} =>
      match find_aop P with 
        | some ?n =>  
          hoare lifts (n::nil)%nat pre; 
            eapply calle_rule_lvar'; 
            [ intuition eauto  | 
              intros; do 5 try 
                         (apply rvl_elim;[ symbolic_execution | ]);
              first [apply rvl_nil | simpl;auto] | 
              intros;  unfold_spec; sep normal; sep eexists; sep_cancel_iers; sep pauto | (* origin: intros;  unfold_spec; sep pauto *)
              idtac |
              idtac |
              simpl;eauto | 
              sep_unfold_funpost |
              sep_unfold_funpre 
              ]
        | none _ => idtac
      end
  end.

Ltac hoare_forward_first :=
  first [ hoare_assign
        | hoare_assign_array_struct (* new add *)
        | hoare_assign_evaux (* new add *)
        | hoare_if
        | hoare_ret
        | hoare_call
        | hoare_calle_lvar
        | idtac ].

Ltac hoare_forward_stmts' :=
  let s := fresh in
  let H := fresh in
  match goal with
  | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} (sseq _ _) {{ _ }} =>
    eapply seq_rule; [ hoare_forward_stmts'
                     | idtac ]
  | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
    eapply forward_rule2; [ hoare_forward_first
                          | try sep_unfold_funpost;
                            first [ intros s H; exact H
                                  | sep pauto ] ]
  end.

Ltac hoare_forward_stmts :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ Afalse \\// _ }} _ {{ _ }} =>
      apply hoare_disj_afalse_l_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// Afalse }} _ {{ _ }} =>
      apply hoare_disj_afalse_r_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ Afalse ** ?P \\// _ }} _ {{ _ }} =>
      apply hoare_disj_afalseP_l_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// Afalse **?P }} _ {{ _ }} =>
      apply hoare_disj_afalseP_r_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// _ }} _ {{ _ }} =>
      eapply disj_rule
    | _ => hoare normal pre; hoare_ex_intro;  hoare_forward_stmts'
  end.

Tactic Notation "hoare" "forward" := hoare_forward_stmts.

Ltac hoare_enter_critical :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- {|_ , _, ?li , _, _, _|}|-_ {{?P}} (sprim encrit) {{_}} =>
      match find_aop P with 
        | none _ => idtac 1 "no absop in the pre condition"; fail 1
        | some ?a =>
          match find_aisr P with
            | none _ => idtac 2 "no isr in the pre condition"; fail 2
            | some ?b =>
              match find_aie P with
                | none _ => idtac 3 "no ie in the pre condition"; fail 3
                | some ?c =>
                  match find_ais P with
                    | none _ => idtac 4 "no is in the pre condition"; fail 4
                    | some ?d =>
                      match find_acs P with
                        | none _ => idtac 5 "no cs in the pre condition"; fail 5
                        | some ?e =>
                          match find_aier P with 
                            | none _ => idtac 6 "no ier in the pre condition"; fail 6
                            | some ?f =>
                              hoare lifts (a::b::c::d::e::nil) pre;
                                eapply encrit1_rule'_ISnil_ISRemp;
                                [ try (intros s H; sep_cancel_iers; exact H) (* origin: intros s H; exact H*)
                                | try (good_frm_sovler;simpl;tauto) (* origin: good_frm_sovler;simpl;tauto *)
                                ]
                          end
                      end
                  end
              end
          end
      end
  end.

Ltac hoare_forward_prim_first :=
  first [ hoare_enter_critical
        | hoare_exit_critical
        | idtac ].

Ltac hoare_forward_prim' :=
  let s := fresh in
  let H := fresh in
  match goal with
  | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} (sseq _ _) {{ _ }} =>
    eapply seq_rule; [ hoare_forward_prim'
                     | try hoare_invchange ]
  | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
    eapply forward_rule2; [ hoare_forward_prim_first
                          | first [ intros s H; exact H
                                  | sep pauto ] ]
  end.

Ltac hoare_forward_prim :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ Afalse \\// _ }} _ {{ _ }} =>
      apply hoare_disj_afalse_l_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// Afalse }} _ {{ _ }} =>
      apply hoare_disj_afalse_r_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ Afalse ** ?P \\// _ }} _ {{ _ }} =>
      apply hoare_disj_afalseP_l_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// Afalse **?P }} _ {{ _ }} =>
      apply hoare_disj_afalseP_r_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// _ }} _ {{ _ }} =>
      eapply disj_rule
    | _ => hoare normal pre; hoare_ex_intro;  hoare_forward_prim'
  end.

Tactic Notation "hoare" "forward" "prim":= hoare_forward_prim.

Close Scope code_scope.
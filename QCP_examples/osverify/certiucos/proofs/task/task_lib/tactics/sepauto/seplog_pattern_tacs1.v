
Require Import include_frm1.
Require Import sep_auto1.
Require Import join_lib1. 
Require Import hoare_conseq1. 
Require Import derived_rules1.

Require Import List. 

Ltac sep_lift_context_in H trm :=
  match type of H with
    | _ |= ?P =>
      match find_match_context P trm with
         | none _ => idtac 1 "no such term in the Hsat"; fail 1
         | some ?a => sep lifts (a::nil)%nat in H
      end
  end.

Ltac sep_lift_context trm :=
  match goal with
    | |- _ |= ?P =>
      match find_match_context P trm with
         | none _ => idtac 1 "no such term in the Hsat"; fail 1
         | some ?a => sep lifts (a::nil)%nat 
      end
  end.

Inductive _num_ := _N_ (n:nat). 

Ltac trms_to_idxs trms :=
  match trms with
    (?trms', ?trm) =>
    let l := (trms_to_idxs trms') in 
    match trm with 
      _N_ ?n => constr: (n :: l)
    | _ => 
      match goal with
      | |- _ |= ?P =>
        match find_match_context P trm with
        | none _ => l 
        | some ?a => constr: (a :: l) 
        end
      end
    end
  | pnil => constr: (@nil nat)
  | ?trm =>
    match trm with
      _N_ ?n => constr: (n :: (@nil nat)) 
    | _ => 
      match goal with
      | |- _ |= ?P =>
        match find_match_context P trm with
        | none _ => constr: (@nil nat) 
        | some ?a => constr: (a :: (@nil nat))
        end
      end
    end
  end.

Ltac trms_to_idxs_in H trms :=
  match trms with
    (?trms', ?trm) =>
    let l := (trms_to_idxs_in H trms') in
    match trm with
      _N_ ?n => constr: (n :: l)
    | _ => 
      match type of H with 
      | _ |= ?P =>
        match find_match_context P trm with
        | none _ => l 
        | some ?a => constr: (a :: l)
        end 
      end
    end
  | pnil => constr: (@nil nat)
  | ?trm =>
    match trm with
      _N_ ?n => constr: (n :: (@nil nat))
    | _ => 
      match type of H with
      | _ |= ?P =>
        match find_match_context P trm with
        | none _ => constr: (@nil nat) 
        | some ?a => constr: (a :: (@nil nat))
        end
      end
    end
  end.  

Ltac sep_rmb_trms trms :=
  let l := trms_to_idxs trms in sep_remember (List.rev l).

Ltac sep_rmb_trms_in H trms :=
  let l := trms_to_idxs_in H trms in sep_remember_in H (List.rev l).

Ltac sep_lifts_trms trms :=
  let l := trms_to_idxs trms in sep lifts (List.rev l).

Ltac sep_lifts_trms_in H trms :=
  let l := trms_to_idxs_in H trms in sep lifts (List.rev l) in H.

Ltac hoare_lifts_trms_pre trms :=
  match goal with
    | |-  {| _, _, _, _, _, _ |} |- _  {{ _ //\\ _ }} _ {{ _ //\\ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply backward_rule3;
       [ intros s H; let l := (trms_to_idxs_in H trms) in sep lifts (List.rev l) in H; exact H | idtac ]
    | |-  {| _, _, _, _, _,_ |} |- _ {{ _ }} _ {{ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply backward_rule1;
       [ intros s H; let l := (trms_to_idxs_in H trms) in sep lifts (List.rev l) in H; exact H | idtac ]
  end.


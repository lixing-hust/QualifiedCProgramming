
Require Import memory. 
Require Import sem_language.

Require Import sem_sys. 

(* generate the syntactical successors of cd that are neither "END _" nor "ABORT" *)
Fixpoint get_all_succs_aux (cd: spec_code) : (list spec_code) :=
  match cd with
    spec_prim _ vl step => nil
  | sched _ => nil
  | spec_done _ => nil
  | spec_seq cd1 cd2 =>
      let cds := get_all_succs_aux cd1 in
      (List.map (fun cd => (cd;; cd2)) cds) ++ (cd2::nil) ++ (get_all_succs_aux cd2)
  | spec_choice cd1 cd2 => 
      (cd1::nil) ++ (get_all_succs_aux cd1) ++ (cd2::nil) ++ (get_all_succs_aux cd2)
  | spec_assume asrt _ => nil
  | spec_assert _ => nil
  | spec_set_pt _ => nil
  | spec_atm cd => nil
  | spec_abort => nil
  end.

Definition get_all_succs (cd: spec_code) : (list spec_code) :=
  (cd::nil)++(get_all_succs_aux cd).

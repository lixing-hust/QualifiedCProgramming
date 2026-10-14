
Require Import memory. 
Require Import if_language.
Require Import mq_apispecs. 

(* generate the syntactical successors of cd that are neither "END _" nor "ABORT" *)
Fixpoint get_all_succs_aux (cd: spec_code) : (list spec_code) :=
  match cd with
    spec_prim asrt vl step => nil
  | sched asrt => nil
  | spec_done _ => nil
  | spec_seq cd1 cd2 =>
      let cds := get_all_succs_aux cd1 in
      (List.map (fun cd => (cd;; cd2)) cds) ++ (cd2::nil) ++ (get_all_succs_aux cd2)
  | spec_ifelse _ b cd1 cd2 =>
      (get_all_succs_aux cd1) ++ (get_all_succs_aux cd2)
  | spec_if_else_  _ b cd1 cd2 =>
      (cd1::nil) ++ (get_all_succs_aux cd1) ++ (cd2::nil) ++ (get_all_succs_aux cd2)
  | spec_assume _ _ => nil
  | spec_assert _ _ => nil
  | getsem _ _ | postsem _ _ | coreint _ _ _ | clearipc _ _ _
  | cslsemacc _ _ _ | cslsemrel _ _ => nil
  | spec_abort => nil
  end.


Definition get_all_succs (cd: spec_code) : (list spec_code) :=
  (cd::nil)++(get_all_succs_aux cd).


Definition mqsend1 :=
  mqsend (Vint32 (Int.one)
  :: Vptr (xH, Int.zero)
  :: Vint32 Int.one
  :: Vint32 Int.zero
  :: Vint32 (Int.one)
  :: Vptr (xH, Int.one)
  :: Vptr (xH, Int.one)
  :: Vint32 (Int.zero)
  :: Vint32 (Int.zero)
  :: Vint32 (Int.mone) :: Vint32 (Int.zero) :: nil). 


Set Printing Depth 1000.
Set Printing Width 200. 
Goal exists x, get_all_succs mqsend1= x.
  eexists. unfold mqsend1. unfold mqsend. unfold get_all_succs. simpl.
  eauto. 
Qed. 

Ltac eval_succ :=
  eexists; unfold mqsend1; unfold mqsend; simpl. 

Goal exists x, List.nth_error (get_all_succs mqsend1) 20 = x.
  eval_succ. 
  eauto. 
Qed. 

Goal exists x, List.nth_error (get_all_succs mqsend1) 21 = x.
  eval_succ. 
  eauto. 
Qed. 

